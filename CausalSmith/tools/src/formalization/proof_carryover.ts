// Stage 2 proof carry-over (rewind proof-preservation).
//
// When F2 re-scaffolds on a rewind, every declaration is rewritten `:= by sorry`,
// which ERASES proofs a prior Stage 3 had already filled — the most expensive
// artifact in the pipeline. The .md-instructed carry-over (stage2_scaffold.txt)
// is unreliable (prompt-only) and is SKIPPED whenever the spec changed, so a deep
// rewind loses all proofs outright.
//
// This module makes carry-over CODE-ENFORCED and gated on a SIGNATURE MATCH. After
// the producer writes a new scaffold, every new `sorry` declaration whose
// normalized signature is byte-identical to a prior real proof receives that
// proof in a structured carry-over comment. Cold-mode flows may keep the comment
// until F2.5 passes; revise-mode flows reactivate it immediately, so an F2 rewind
// cannot downgrade an unchanged working declaration to `sorry` even if the model
// follows a stale cold-start instruction.
//
// Signature-match is the whole safety story: a proof is only re-attached to the
// SAME statement, so an unrelated, unchanged decl keeps its proof while the decl
// actually being fixed (signature changed) gets nothing and is re-proven.

import { existsSync } from "node:fs";
import { readFile, readdir, writeFile } from "node:fs/promises";
import path from "node:path";
import { isPaperTmpPath } from "../paths.js";

interface DeclSigBody {
  name: string;
  normSig: string; // normalized decl header through ":= by"
  body: string; // raw text after ":= by" to decl end (the tactic block)
  isSorry: boolean; // body is just `sorry` (after stripping comments)
  headerLineIdx: number;
  endLineIdx: number; // last line index of the decl (insertion point = endLineIdx+1)
}

const CARRYOVER_TAG = "PRIOR PROOF (carry-over: auto";

function normWs(s: string): string {
  return s.replace(/\s+/g, " ").trim();
}

function stripComments(s: string): string {
  return s.replace(/\/-[\s\S]*?-\//g, " ").replace(/--[^\n]*/g, " ");
}

/**
 * Parse top-level theorem/lemma decls, splitting signature vs body at the first
 * top-level `:= by` (robust against `let x := …` in the conclusion, which has no
 * `by`). Comment-aware: a header/boundary keyword inside `/- … -/` or after `--`
 * is prose, not a declaration. Term-mode decls (no `:= by`) are skipped.
 */
function parseDecls(fileText: string): DeclSigBody[] {
  const lines = fileText.split(/\r?\n/);
  let depth = 0;
  const code = lines.map((ln) => {
    const start = depth;
    for (const tok of ln.match(/\/-|-\//g) ?? []) depth += tok === "/-" ? 1 : -1;
    if (depth < 0) depth = 0;
    return start === 0 && !/^\s*--/.test(ln);
  });
  const headerRe =
    /^\s*(?:noncomputable\s+|private\s+|protected\s+|scoped\s+)*(theorem|lemma)\s+([A-Za-z0-9_'.]+)/;
  const topLevelRe =
    /^\s*@\[|^\s*\/--|^\s*(?:noncomputable\s+|private\s+|protected\s+|scoped\s+)*(?:theorem|lemma|def|abbrev|structure|class|instance|section|namespace|end)\b/;
  const out: DeclSigBody[] = [];
  let i = 0;
  while (i < lines.length) {
    const m = code[i] ? lines[i].match(headerRe) : null;
    if (!m) {
      i++;
      continue;
    }
    const headerLineIdx = i;
    const declLines = [lines[i]];
    let j = i + 1;
    for (; j < lines.length; j++) {
      if (code[j] && (topLevelRe.test(lines[j]) || /^#{1,3}\s/.test(lines[j]))) break; // why: next decl docstrings are top-level boundaries for carryover snapshots.
      declLines.push(lines[j]);
    }
    const declText = declLines.join("\n");
    const by = declText.match(/:=\s*by\b/);
    if (by && by.index !== undefined) {
      const cut = by.index + by[0].length;
      out.push({
        name: m[2],
        normSig: normWs(declText.slice(0, cut)),
        body: declText.slice(cut).replace(/^\r?\n/, ""),
        isSorry: /^\s*sorry\b/.test(stripComments(declText.slice(cut)).trim()),
        headerLineIdx,
        endLineIdx: j - 1,
      });
    }
    i = j;
  }
  return out;
}

/**
 * Snapshot the real (non-`sorry`, non-`BLOCKER`) proof bodies currently on disk,
 * keyed by normalized signature. Call BEFORE the producer overwrites the files.
 * Bodies containing a bare `-/` are skipped (they would prematurely close the
 * `/-! … -/` carry-over comment).
 */
export async function snapshotPriorProofs(
  leanDir: string,
): Promise<Map<string, { name: string; body: string }>> {
  const out = new Map<string, { name: string; body: string }>();
  if (!existsSync(leanDir)) return out;
  const files = (await readdir(leanDir, { recursive: true }))
    .map(String)
    .filter((f) => f.endsWith(".lean") && !isPaperTmpPath(f));
  for (const f of files) {
    const text = await readFile(path.join(leanDir, f), "utf8");
    for (const d of parseDecls(text)) {
      if (d.isSorry) continue;
      if (/\bBLOCKER\b/.test(d.body)) continue;
      if (d.body.includes("-/")) continue; // comment-nesting hazard
      out.set(d.normSig, { name: d.name, body: d.body });
    }
  }
  return out;
}

/**
 * Re-attach prior proofs (as inert comments) for new `sorry` decls whose
 * signature matches a snapshot entry. Call AFTER the producer wrote the new
 * scaffold. Idempotent: a decl already carrying an auto carry-over is skipped.
 * Returns the names re-attached.
 */
export async function injectCarryoverComments(
  leanDir: string,
  prior: Map<string, { name: string; body: string }>,
): Promise<{ count: number; names: string[] }> {
  if (prior.size === 0 || !existsSync(leanDir)) return { count: 0, names: [] };
  const names: string[] = [];
  const files = (await readdir(leanDir, { recursive: true }))
    .map(String)
    .filter((f) => f.endsWith(".lean") && !isPaperTmpPath(f));
  for (const f of files) {
    const full = path.join(leanDir, f);
    const text = await readFile(full, "utf8");
    const lines = text.split(/\r?\n/);
    const decls = parseDecls(text);
    // Only NEW sorry decls that match a prior real proof and aren't already tagged.
    const toInject = decls.filter((d) => {
      if (!d.isSorry || !prior.has(d.normSig)) return false;
      const window = lines.slice(Math.max(0, d.headerLineIdx - 4), d.endLineIdx + 4).join("\n");
      return !window.includes(CARRYOVER_TAG);
    });
    if (toInject.length === 0) continue;
    // Insert AFTER each decl (bottom-up so line indices stay valid). Inserting
    // after — not above — avoids detaching a `/-- … -/` docstring from its decl.
    toInject.sort((a, b) => b.endLineIdx - a.endLineIdx);
    for (const d of toInject) {
      const p = prior.get(d.normSig)!;
      const comment = [
        `/-! ${CARRYOVER_TAG}; signature-unchanged \`${p.name}\`). Stage 3: replace the`,
        `   \`:= by sorry\` above with this body, run \`lean_diagnostic_messages\`, patch failures only.`,
        `   := by${p.body}`,
        `-/`,
      ].join("\n");
      lines.splice(d.endLineIdx + 1, 0, comment);
      names.push(d.name);
    }
    await writeFile(full, lines.join("\n"), "utf8");
  }
  return { count: names.length, names };
}

/**
 * Reactivate code-enforced carry-over comments after F2.5 has accepted the new
 * statement scaffold. The injector already gated every comment on an identical
 * normalized signature, so this is a mechanical undo of F2's temporary
 * sorry-only form, not a proof search. F3 then spends effort only on changed or
 * genuinely new declarations.
 */
export async function restoreCarryoverProofs(
  leanDir: string,
): Promise<{ count: number; names: string[] }> {
  if (!existsSync(leanDir)) return { count: 0, names: [] };
  const names: string[] = [];
  const files = (await readdir(leanDir, { recursive: true }))
    .map(String)
    .filter((f) => f.endsWith(".lean") && !isPaperTmpPath(f));
  for (const f of files) {
    const full = path.join(leanDir, f);
    const lines = (await readFile(full, "utf8")).split(/\r?\n/);
    const starts = lines
      .map((line, index) => line.includes(CARRYOVER_TAG) ? index : -1)
      .filter((index) => index >= 0)
      .sort((a, b) => b - a);
    let changed = false;
    for (const start of starts) {
      const end = lines.findIndex((line, index) => index > start && /^\s*-\/\s*$/.test(line));
      if (end < 0) continue;
      const marker = lines.findIndex(
        (line, index) => index > start && index < end && /^\s*:=\s*by\b/.test(line),
      );
      if (marker < 0) continue;

      let sorry = start - 1;
      while (sorry >= 0 && lines[sorry].trim() === "") sorry--;
      if (sorry < 0) continue;
      const bareSorry = /^\s*sorry\s*$/.test(lines[sorry]);
      // A single-line decl tail (`… := by sorry`) is snapshot/injected by the carry-over pass
      // too (its body still parses as `sorry`); without this branch such a decl kept its inert
      // comment forever and F3 re-proved it from scratch.
      const inlineSorry = !bareSorry && /:=\s*by\s+sorry\s*$/.test(lines[sorry]);
      if (!bareSorry && !inlineSorry) continue;

      const markerOffset = lines[marker].indexOf(":= by") + ":= by".length;
      const body = [lines[marker].slice(markerOffset), ...lines.slice(marker + 1, end)];
      if (body.every((line) => line.trim() === "")) continue;

      const name = lines[start].match(/signature-unchanged `([^`]+)`/)?.[1] ?? path.basename(f);
      if (bareSorry) {
        lines.splice(sorry, end - sorry + 1, ...body);
      } else {
        const head = lines[sorry].replace(/\bsorry\s*$/, "").replace(/\s+$/, "");
        const first = body[0].trim() === "" ? head : `${head} ${body[0].trimStart()}`;
        lines.splice(sorry, end - sorry + 1, first, ...body.slice(1));
      }
      names.push(name);
      changed = true;
    }
    if (changed) await writeFile(full, lines.join("\n"), "utf8");
  }
  return { count: names.length, names };
}
