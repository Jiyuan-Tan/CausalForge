// CausalSmith/tools/src/substrate/coordinate.ts
//
// The `coordinate` phase — intelligent successor of the mechanical `promote`.
//
// On reviewer PASS, a codex COORDINATOR agent decides how the proven substrate
// integrates into Causalean: which existing topical module it belongs in
// (merge-first, so repeated `--study` runs follow the library's subject
// hierarchy), what existing decls it should reuse
// instead of reinventing, and how it is documented per the docstring-canonical
// workflow (per-decl docstrings, module docstring, `headline_theorems` sidecar,
// `doc/API.md` GEN markers).
//
// The intelligence is codex's; SAFETY is deterministic TS. The coordinator emits
// a structured MANIFEST (never free-form edits); this module applies it under
// snapshot / verify / rollback. Crucially, edits to EXISTING Lean files are
// INSERT-ONLY (a merge cannot modify or delete a proven decl — asserted by
// byte-preservation), and codex never self-certifies the build: the same
// integration gate promote used (`lake build` → `library_index` → `embed` →
// `lint:embeddings` → `doc:gen` → `doc:check`) runs deterministically, rolling
// back everything on any failure.
//
// Manifest content is carried inline (full bodies / insert patches as strings).
// For the typical substrate run (1–3 files) this stays well within codex output
// limits and keeps the apply layer deterministic and unit-testable; if large
// runs prove truncation-prone, switch to a codex-writes-staging-dir handoff.
import { mkdir, readFile, writeFile, unlink, rmdir, rm, readdir } from "node:fs/promises";
import { existsSync } from "node:fs";
import path from "node:path";
import { withLakeBuildLock } from "../shared/build_mutex.js";
import { spawnWithInactivityTimeout } from "../workers/spawn.js";
import { runCodex as realRunCodex } from "../shared/codex.js";
import { expectStringJsonOutput, persistCodexRaw } from "../shared/codex_json.js";
import { causaleanRoot } from "./paths.js";
import { logAgentCall } from "./log.js";
import { buildCoordinatorPrompt } from "./prompts.js";
import { parseCoordinationManifest, type CoordinationManifest } from "./types.js";

// --- The coordinator agent (codex → manifest) ---------------------------------

export interface CoordinatorArgs {
  repoRoot: string;
  runDir: string;
  round: number;
  slug: string;
  requirement: string;
  leanDir: string;
  modulePrefix: string;
  leanFiles: string[];
  /** Directory where the coordinator WRITES file bodies / insert patches; the
   *  manifest references them by `from`. Keeps large content out of the JSON. */
  stagingDir: string;
  /** Failing integration-gate log from the previous coordinate attempt, fed back
   *  so codex can fix placement / imports / a dedup that broke the build. */
  lastFailureLog: string | null;
}
export interface CoordinatorDeps {
  runCodex: typeof realRunCodex;
}

export async function runCoordinator(
  args: CoordinatorArgs,
  deps: CoordinatorDeps = { runCodex: realRunCodex },
): Promise<CoordinationManifest> {
  const prompt = buildCoordinatorPrompt(args);
  // why: retries must not see staged bodies from an earlier coordinate attempt.
  await rm(args.stagingDir, { recursive: true, force: true });
  await mkdir(args.stagingDir, { recursive: true });
  const t0 = Date.now();
  let stdout = "";
  let parsed: CoordinationManifest | undefined;
  let parseError: string | undefined;
  try {
    // cwd = the Causalean root so codex sees BOTH the staging substrate (under
    // CausalSmith/) and the Causalean tree it integrates into, and lean-lsp
    // targets the Causalean lake project.
    const res = await deps.runCodex({ prompt, cwd: causaleanRoot(args.repoRoot) });
    stdout = res.stdout;
    // Persist raw stdout BEFORE parsing, so a parse failure leaves a forensic
    // trail (the #1 historical breakdown cause) in the run dir.
    await persistCodexRaw(args.runDir, "coordinator", stdout);
    parsed = parseCoordinationManifest(expectStringJsonOutput(stdout));
    await assertManifestFromFilesExist(args.stagingDir, parsed);
    return parsed;
  } catch (err) {
    parseError = err instanceof Error ? err.message : String(err);
    throw err;
  } finally {
    await logAgentCall(args.runDir, {
      agent: "coordinator", round: args.round, callId: "main", model: "codex",
      prompt, promptBytes: Buffer.byteLength(prompt), rawOutput: stdout,
      parsed, parseError, ok: parseError === undefined, durationMs: Date.now() - t0,
    });
  }
}

// --- Deterministic manifest apply (snapshot / verify / rollback) ---------------

export interface CoordinateApplyDeps {
  /** `timedOut` is set when the command was watchdog-killed (inactivity/liveness)
   *  rather than exiting on its own. A kill is NOT proof the step failed, so the
   *  caller escalates instead of rolling back proven work. */
  run: (cmd: string, cwd: string) => Promise<{ code: number; log: string; timedOut?: boolean }>;
  readFile: (p: string) => Promise<string>;
  writeFile: (p: string, text: string) => Promise<void>;
  removeFile: (p: string) => Promise<void>;
  removeDir?: (p: string) => Promise<void>;
  exists: (p: string) => Promise<boolean>;
}

const realApplyDeps: CoordinateApplyDeps = {
  run: async (cmd, cwd) =>
    withLakeBuildLock(cwd, async () => {
      // Drop any inherited isolated TMPDIR: the nested `doc:gen` / `embed:library`
      // tsx subcommands open an IPC pipe under TMPDIR and would collide on a
      // per-run TMPDIR (see promote.ts for the same fix).
      const env = { ...process.env };
      delete env.TMPDIR;
      // Inactivity bounds a SILENT hang; the wall-clock backstop bounds a step
      // that spins forever while EMITTING output (which would keep `lastOutput`
      // fresh and never trip inactivity), so a runaway verify can never hold the
      // promotion lock indefinitely. Generous (> inactivity); `CAUSALSMITH_VERIFY_MAX_MS=0`
      // disables it. Both kinds surface as `timedOut` → escalate (preserve).
      const maxTotalMs = Number(process.env.CAUSALSMITH_VERIFY_MAX_MS ?? 60 * 60 * 1000);
      const r = await spawnWithInactivityTimeout("bash", ["-lc", cmd], {
        cwd, env, inactivityTimeoutMs: 30 * 60 * 1000, maxTotalMs,
      });
      const log = [r.stdout, r.stderr].filter(Boolean).join("\n");
      const timedOut =
        r.killedDueToInactivity || r.killedDueToLiveness != null || r.killedDueToTotalTimeout === true;
      const code = (r.exitCode ?? 1) !== 0 ? 1 : 0;
      return { code, log, timedOut };
    }),
  readFile: (p) => readFile(p, "utf8"),
  writeFile: async (p, text) => { await mkdir(path.dirname(p), { recursive: true }); await writeFile(p, text, "utf8"); },
  removeFile: async (p) => { await unlink(p).catch(() => {}); },
  removeDir: async (p) => { await rmdir(p).catch(() => {}); },
  exists: async (p) => existsSync(p),
};

/** Resolve `rel` against the Causalean root, refusing any path that escapes it. */
function resolveInside(cRoot: string, rel: string): string {
  const abs = path.resolve(cRoot, rel);
  const back = path.relative(cRoot, abs);
  if (back === "" || back.startsWith("..") || path.isAbsolute(back)) {
    throw new Error(`manifest op path escapes the Causalean root: ${rel}`);
  }
  return abs;
}

async function listStagedFiles(root: string, dir = root): Promise<Set<string>> {
  const out = new Set<string>();
  const entries = await readdir(dir, { withFileTypes: true }).catch(() => []);
  for (const entry of entries) {
    const abs = path.join(dir, entry.name);
    if (entry.isDirectory()) {
      for (const nested of await listStagedFiles(root, abs)) out.add(nested);
    } else if (entry.isFile()) {
      out.add(path.relative(root, abs));
    }
  }
  return out;
}

async function assertManifestFromFilesExist(stagingDir: string, manifest: CoordinationManifest): Promise<void> {
  const staged = await listStagedFiles(stagingDir);
  for (const op of manifest.ops) {
    const abs = resolveInside(stagingDir, op.from);
    const rel = path.relative(stagingDir, abs);
    // why: the staging dir was cleared for this attempt, so membership proves this round wrote it.
    if (!staged.has(rel)) throw new Error(`manifest references unstaged from file: ${op.from}`);
  }
}

function isLeanWriteTarget(target: string): boolean {
  const normalized = target.replace(/\\/g, "/");
  return normalized === "Causalean.lean" || normalized.endsWith(".lean");
}

/** Add one root import in deterministic sorted order. */
export function insertImportSorted(rootFileText: string, importLine: string): string {
  const lines = rootFileText.split(/\r?\n/);
  if (lines.includes(importLine)) return rootFileText;
  const imports = lines.filter((line) => line.startsWith("import "));
  const rest = lines.filter((line) => !line.startsWith("import "));
  imports.push(importLine);
  imports.sort();
  const trailingNewline = rootFileText.endsWith("\n");
  const out = [...imports, ...rest.filter((line) => line.length > 0)].join("\n");
  return trailingNewline ? `${out}\n` : out;
}

function leanCodeOnly(content: string): string {
  let out = "";
  let blockDepth = 0;
  let inString = false;
  let escaped = false;
  for (let i = 0; i < content.length; i++) {
    const c = content[i];
    const next = content[i + 1] ?? "";
    if (blockDepth > 0) {
      if (c === "/" && next === "-") { blockDepth++; out += "  "; i++; }
      else if (c === "-" && next === "/") { blockDepth--; out += "  "; i++; }
      else out += c === "\n" ? "\n" : " ";
      continue;
    }
    if (inString) {
      out += c === "\n" ? "\n" : " ";
      if (escaped) escaped = false;
      else if (c === "\\") escaped = true;
      else if (c === '"') inString = false;
      continue;
    }
    if (c === "-" && next === "-") {
      while (i < content.length && content[i] !== "\n") { out += " "; i++; }
      if (i < content.length) out += "\n";
      continue;
    }
    if (c === "/" && next === "-") { blockDepth = 1; out += "  "; i++; continue; }
    if (c === '"') { inString = true; out += " "; continue; }
    out += c;
  }
  return out;
}

function assertLibraryOnlyLeanContent(content: string, target: string): void {
  if (/\bCausalSmith\b/.test(leanCodeOnly(content))) {
    throw new Error(`final Lean content retains a CausalSmith dependency: ${target}`);
  }
}

function isCausaleanLeanPath(target: string): boolean {
  const parts = target.replace(/\\/g, "/").split("/");
  return parts[0] === "Causalean" && parts.length >= 3 && parts.at(-1)?.endsWith(".lean") === true;
}

function isAllowedRecordPath(target: string): boolean {
  const normalized = target.replace(/\\/g, "/");
  return normalized === "doc/API.md" || /^doc\/library_review\/[A-Za-z0-9_-]+\.json$/.test(normalized);
}

async function assertOperationTarget(
  cRoot: string,
  op: CoordinationManifest["ops"][number],
  abs: string,
  d: CoordinateApplyDeps,
): Promise<void> {
  if (op.kind === "merge_lean") {
    if (!isCausaleanLeanPath(op.target) || !(await d.exists(abs))) {
      throw new Error(`merge_lean target must be an existing Causalean subject file: ${op.target}`);
    }
    return;
  }
  if (op.kind === "write_file") {
    if (!isAllowedRecordPath(op.target)) {
      throw new Error(`write_file target is outside the coordinator record allowlist: ${op.target}`);
    }
    return;
  }
  if (!isLeanWriteTarget(op.target) && !isAllowedRecordPath(op.target)) {
    throw new Error(`non-Lean create_file target is outside the coordinator record allowlist: ${op.target}`);
  }
  if (isLeanWriteTarget(op.target) && !isCausaleanLeanPath(op.target)) {
    throw new Error(`create_file Lean target must be inside a Causalean subject area: ${op.target}`);
  }
  void cRoot;
}

async function assertCreatePlacement(
  cRoot: string,
  target: string,
  newModule: string | undefined,
  d: CoordinateApplyDeps,
): Promise<void> {
  const normalized = target.replace(/\\/g, "/");
  if (!normalized.endsWith(".lean")) return;
  const parts = normalized.split("/");
  if (parts[0] !== "Causalean" || parts.length < 3) {
    throw new Error(`new Lean module must live inside an existing Causalean subject area: ${target}`);
  }
  const subjectRoot = path.join(cRoot, "Causalean", parts[1]);
  if (!(await d.exists(subjectRoot))) {
    throw new Error(`new Lean module names a non-existing Causalean subject area: ${parts[1]}`);
  }
  const expectedModule = normalized.slice(0, -".lean".length).replaceAll("/", ".");
  if (!newModule || newModule !== expectedModule) {
    throw new Error(`create_file newModule must match target (${expectedModule}): ${newModule ?? "(missing)"}`);
  }
}

/**
 * Insert `insert` into `orig` after the first line containing `anchor` (empty
 * anchor → append at end of file). Returns the merged text plus the exact
 * inserted segment and its offset, so the caller can assert byte-preservation.
 */
export function applyInsertOnly(
  orig: string,
  anchor: string,
  insert: string,
): { merged: string; at: number; segment: string } {
  const block = insert.endsWith("\n") ? insert : `${insert}\n`;
  if (anchor.trim() === "") {
    const lead = orig.length === 0 || orig.endsWith("\n") ? "\n" : "\n\n";
    const segment = `${lead}${block}`;
    return { merged: orig + segment, at: orig.length, segment };
  }
  const lines = orig.split("\n");
  const idx = lines.findIndex((l) => l.includes(anchor));
  if (idx < 0) throw new Error(`merge_lean anchor not found: ${JSON.stringify(anchor)}`);
  // Char offset of the start of line idx+1 (i.e. just after line idx's newline).
  let at = 0;
  for (let i = 0; i <= idx; i++) at += lines[i].length + 1;
  if (at > orig.length) at = orig.length; // last line had no trailing newline
  const segment = `${block}\n`;
  const merged = orig.slice(0, at) + segment + orig.slice(at);
  return { merged, at, segment };
}

/** A merge must leave every pre-existing byte intact: removing the inserted
 *  segment at its offset must reproduce the original exactly. */
function assertInsertOnly(orig: string, merged: string, at: number, segment: string): void {
  const without = merged.slice(0, at) + merged.slice(at + segment.length);
  if (without !== orig) {
    throw new Error("insert-only invariant violated: a merge would change existing bytes");
  }
}

export interface ApplyManifestArgs {
  cRoot: string;
  repoRoot: string;
  /** Root the manifest's `from` paths resolve against (where codex staged the
   *  file bodies / insert patches). */
  stagingDir: string;
  leanFiles: string[];
  manifest: CoordinationManifest;
}

export async function applyManifest(
  args: ApplyManifestArgs,
  d: CoordinateApplyDeps = realApplyDeps,
): Promise<{ ok: boolean; log: string; timedOut?: boolean }> {
  const { cRoot, repoRoot, stagingDir, leanFiles, manifest } = args;
  const rootPath = path.join(cRoot, "Causalean.lean");
  const logs: string[] = [];
  // abs path → original content (null = file did not exist, so rollback deletes).
  const snapshots = new Map<string, string | null>();
  const snap = async (abs: string) => {
    if (!snapshots.has(abs)) snapshots.set(abs, (await d.exists(abs)) ? await d.readFile(abs) : null);
  };
  const rollback = async () => {
    for (const [abs, orig] of snapshots) {
      if (orig === null) await d.removeFile(abs);
      else await d.writeFile(abs, orig);
    }
  };
  const newModules: string[] = [];
  try {
    await snap(rootPath);
    for (const op of manifest.ops) {
      const abs = resolveInside(cRoot, op.target);
      await assertOperationTarget(cRoot, op, abs, d);
      if (op.kind === "create_file") {
        // The op body lives in a staged file; read it (never inline in the JSON).
        const content = await d.readFile(resolveInside(stagingDir, op.from));
        await assertCreatePlacement(cRoot, op.target, op.newModule, d);
        if (isLeanWriteTarget(op.target)) assertLibraryOnlyLeanContent(content, op.target);
        if (await d.exists(abs)) throw new Error(`create_file target already exists (use merge_lean): ${op.target}`);
        await snap(abs);
        await d.writeFile(abs, content);
        if (op.newModule) newModules.push(op.newModule);
      } else if (op.kind === "merge_lean") {
        const content = await d.readFile(resolveInside(stagingDir, op.from));
        assertLibraryOnlyLeanContent(content, op.target);
        if (!(await d.exists(abs))) throw new Error(`merge_lean target does not exist: ${op.target}`);
        await snap(abs);
        const orig = await d.readFile(abs);
        const { merged, at, segment } = applyInsertOnly(orig, op.anchor, content);
        assertInsertOnly(orig, merged, at, segment);
        await d.writeFile(abs, merged);
      } else {
        // write_file (non-Lean record surface)
        // why: Lean edits must go through create_file/merge_lean so existing bytes stay insert-only.
        if (isLeanWriteTarget(op.target)) throw new Error(`write_file cannot target Lean files: ${op.target}`);
        const content = await d.readFile(resolveInside(stagingDir, op.from));
        await snap(abs);
        await d.writeFile(abs, content);
      }
    }
    // Root-wire every new module into Causalean.lean.
    if (newModules.length > 0) {
      let rootText = (snapshots.get(rootPath) as string | null) ?? (await d.readFile(rootPath));
      for (const m of newModules) rootText = insertImportSorted(rootText, `import ${m}`);
      await d.writeFile(rootPath, rootText);
    }
    // Integration gate — any failure rolls back. Same chain promote used, plus a
    // doc:check freshness guard after doc:gen.
    const toolsDir = path.join(repoRoot, "tools");
    const steps: Array<{ cmd: string; cwd: string }> = [
      { cmd: "lake build", cwd: cRoot },
      { cmd: "lake exe library_index", cwd: cRoot },
      { cmd: "npm run embed:library", cwd: toolsDir },
      { cmd: "npm run lint:embeddings", cwd: toolsDir },
      { cmd: "npm run doc:gen", cwd: toolsDir },
      { cmd: "npm run doc:check", cwd: toolsDir },
    ];
    for (const s of steps) {
      const r = await d.run(s.cmd, s.cwd);
      logs.push(`$ (${s.cwd}) ${s.cmd}\n${r.log}`);
      if (r.timedOut) {
        // A watchdog kill means the step went silent for the FULL timeout without
        // exiting — it may be genuinely stuck (deadlocked lake) OR was mid-flight
        // when killed. Either way a kill is NOT a compile error, and the files are
        // already promoted into Causalean, so rolling back destroys proven,
        // expensive work while a rollback of a mid-flight build is itself unsafe.
        // PRESERVE everything (no rollback, no source deletion) and escalate to a
        // human — who verifies the tree and keeps or reverts. The promotion is
        // UNVERIFIED until they do.
        return {
          ok: false,
          timedOut: true,
          log: `${logs.join("\n\n")}\n\n[coordinate] verify step '${s.cmd}' was watchdog-killed after going silent (unverified); files left in place for human verification (NOT rolled back).`,
        };
      }
      if (r.code !== 0) {
        await rollback();
        return { ok: false, log: logs.join("\n\n") };
      }
    }
    // Success — the substrate content now lives in Causalean; delete the staging
    // sources and clean up the now-empty Substrate dirs (best-effort).
    for (const f of leanFiles) await d.removeFile(f);
    if (d.removeDir) {
      const dirs = Array.from(new Set(leanFiles.map((f) => path.dirname(f))));
      for (const dir of dirs) {
        await d.removeDir(dir);
        await d.removeDir(path.dirname(dir));
      }
    }
    return { ok: true, log: `${logs.join("\n\n")}\n\n[coordinate] applied ${manifest.ops.length} op(s).${manifest.notes ? `\nnotes: ${manifest.notes}` : ""}` };
  } catch (err) {
    await rollback();
    const msg = err instanceof Error ? err.message : String(err);
    return { ok: false, log: `${logs.join("\n\n")}\n\n[coordinate] apply error: ${msg}` };
  }
}

// --- Orchestrator (one coordinate attempt: agent → apply) ----------------------

export interface CoordinateArgs {
  repoRoot: string;
  slug: string;
  leanDir: string;
  requirement: string;
  modulePrefix: string;
  runDir: string;
  leanFiles: string[];
  round: number;
  lastFailureLog: string | null;
}
export interface CoordinateDeps {
  runCoordinator: typeof runCoordinator;
  apply: typeof applyManifest;
  applyDeps?: CoordinateApplyDeps;
}

const realCoordinateDeps: CoordinateDeps = { runCoordinator, apply: applyManifest };

/**
 * One coordinate attempt: ask the coordinator for a manifest, then apply it
 * deterministically. Returns `{ ok, log }`; the pipeline owns the bounded retry
 * (feeding a failure log back on `ok === false`).
 */
export async function coordinate(
  args: CoordinateArgs,
  deps: CoordinateDeps = realCoordinateDeps,
): Promise<{ ok: boolean; log: string; timedOut?: boolean }> {
  const stagingDir = path.join(args.runDir, "coordinate_staging", `round_${args.round}`);
  let manifest: CoordinationManifest;
  try {
    manifest = await deps.runCoordinator({
      repoRoot: args.repoRoot, runDir: args.runDir, round: args.round, slug: args.slug,
      requirement: args.requirement, leanDir: args.leanDir, modulePrefix: args.modulePrefix,
      leanFiles: args.leanFiles, stagingDir, lastFailureLog: args.lastFailureLog,
    });
  } catch (err) {
    const msg = err instanceof Error ? err.message : String(err);
    // A parse/agent failure is retryable: the pipeline feeds this back so codex
    // re-emits (the prompt already tells it to keep the JSON tiny + stage bodies).
    return { ok: false, log: `[coordinate] coordinator agent/parse failed: ${msg}` };
  }
  return deps.apply(
    { cRoot: causaleanRoot(args.repoRoot), repoRoot: args.repoRoot, stagingDir, leanFiles: args.leanFiles, manifest },
    deps.applyDeps ?? realApplyDeps,
  );
}
