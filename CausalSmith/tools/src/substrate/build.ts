// CausalSmith/tools/src/substrate/build.ts
import { readFileSync } from "node:fs";
import path from "node:path";
import { withLakeBuildLock } from "../shared/build_mutex.js";
import { spawnWithInactivityTimeout } from "../workers/spawn.js";
import type { BuildDiagnostics } from "./types.js";

const LEAN_MODULE_RE = /^[A-Za-z_][A-Za-z0-9_']*(\.[A-Za-z_][A-Za-z0-9_']*)*$/;

export function parseBuildDiagnostics(log: string, files: string[]): BuildDiagnostics {
  const perFile: Record<string, { sorries: number; errors: number }> = {};
  for (const f of files) perFile[f] = { sorries: 0, errors: 0 };
  const attribute = (line: string, kind: "sorries" | "errors"): boolean => {
    const hit = files.find((f) => line.includes(f));
    if (hit) perFile[hit][kind] += 1;
    return hit !== undefined;
  };
  const errors: string[] = [];
  let sorryCount = 0;
  for (const line of log.split(/\r?\n/)) {
    if (/declaration uses 'sorry'|warning:.*\bsorry\b/.test(line)) {
      // Only count sorries attributable to a TARGET file. `lake build <module>`
      // replays the FULL transitive dependency closure and re-emits every dep's
      // cached warnings — including any pre-existing `sorry` in a dependency
      // (e.g. `Clt/Prokhorov.lean`). Those must NOT fail the substrate gate, or a
      // single upstream sorry permanently blocks every substrate whose closure
      // touches it. A sorry in the substrate's OWN files is still counted.
      if (attribute(line, "sorries")) sorryCount += 1;
    } else if (/(^|\s)error:/.test(line)) {
      // Same scoping for errors; a hard build failure is still caught by the
      // non-zero exit code in `buildTargets`, independent of this attribution.
      if (attribute(line, "errors")) errors.push(line.trim());
    }
  }
  return { ok: errors.length === 0, errors, sorryCount, perFile };
}

/**
 * Strip Lean comments — line `--` and nested block `/- … -/` (which also covers
 * `/-- … -/` docstrings and `/-! … -/` section comments) — so a keyword that
 * appears only in prose (e.g. a proof-strategy note discussing "axiomatize") is
 * not mistaken for a real declaration. Over-stripping (e.g. inside a string
 * literal) only loses coverage; it never creates a false positive.
 */
export function stripLeanComments(src: string): string {
  let out = "";
  let depth = 0;
  for (let i = 0; i < src.length; ) {
    if (depth > 0) {
      if (src[i] === "/" && src[i + 1] === "-") { depth++; i += 2; }
      else if (src[i] === "-" && src[i + 1] === "/") { depth--; i += 2; }
      else i++;
      continue;
    }
    if (src[i] === "/" && src[i + 1] === "-") { depth++; i += 2; continue; }
    if (src[i] === "-" && src[i + 1] === "-") {
      while (i < src.length && src[i] !== "\n") i++;
      continue;
    }
    out += src[i];
    i++;
  }
  return out;
}

/**
 * Detect a non-proof discharge a filler might use to make a file compile clean
 * while NOT actually proving the statement — chiefly a new `axiom` declaration,
 * which emits no `sorry` warning and so slips past `parseBuildDiagnostics`, and
 * `native_decide` (closes a goal via the `Lean.ofReduceBool` axiom). Scans the
 * substrate's OWN source with comments stripped; returns one message per hit.
 * A new axiom is never a legitimate autonomous substrate output — a genuine
 * axiomatization is a deliberate human decision, not a filler's shortcut.
 */
export function scanSourceForNonProofDischarge(file: string, source: string): string[] {
  const code = stripLeanComments(source);
  const checks: Array<[RegExp, string]> = [
    [/\baxiom\b/, "introduces an 'axiom'"],
    [/\bnative_decide\b/, "uses 'native_decide'"],
  ];
  const out: string[] = [];
  for (const [re, what] of checks) {
    if (re.test(code)) {
      out.push(
        `${file}: ${what} — non-proof discharge forbidden; prove the statement or leave an honest \`sorry\``,
      );
    }
  }
  return out;
}

export async function buildTargets(repoRoot: string, modules: string[]): Promise<BuildDiagnostics> {
  for (const mod of modules) {
    // why: module names become argv to lake; reject anything that is not a Lean module path.
    if (!LEAN_MODULE_RE.test(mod)) throw new Error(`invalid Lean module target: ${mod}`);
  }
  // Target file paths (relative to repoRoot) derived from the module names, so
  // sorry/error attribution scopes to the substrate's OWN files and ignores
  // dependency-replay warnings. Module `A.B.C` ↦ file `A/B/C.lean`.
  const files: string[] = modules.map((m) => `${m.replace(/\./g, "/")}.lean`);
  return withLakeBuildLock(repoRoot, async () => {
    const result = await spawnWithInactivityTimeout("lake", ["build", ...modules], {
      cwd: repoRoot,
      env: process.env,
      inactivityTimeoutMs: 20 * 60 * 1000,
    });
    const log = [result.stdout, result.stderr].filter(Boolean).join("\n");
    const diag = parseBuildDiagnostics(log, files);
    // Axiom-laundering guard: a filler must never discharge a `sorry` with a new
    // `axiom` (or `native_decide`). That compiles clean, emits no sorry warning,
    // and would otherwise pass the gate and promote an unproven assumption into
    // Causalean. Scan the substrate's OWN target files and treat any hit as a
    // build error, routing the scaffolder back to a genuine proof.
    const laundering: string[] = [];
    for (const rel of files) {
      let src: string;
      try {
        src = readFileSync(path.join(repoRoot, rel), "utf8");
      } catch {
        continue; // file may not exist yet this round; nothing to scan
      }
      const hits = scanSourceForNonProofDischarge(rel, src);
      if (hits.length > 0) {
        laundering.push(...hits);
        if (diag.perFile[rel]) diag.perFile[rel].errors += hits.length;
      }
    }
    // Also fail on a non-zero/null exit code, even if no error: line matched.
    const exitCode = result.exitCode ?? 1;
    if (exitCode !== 0) {
      const base = diag.errors.length > 0 ? diag.errors : [`lake build exited with code ${exitCode}`];
      return { ...diag, ok: false, errors: [...base, ...laundering] };
    }
    if (laundering.length > 0) {
      return { ...diag, ok: false, errors: [...diag.errors, ...laundering] };
    }
    return diag;
  });
}
