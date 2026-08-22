import { existsSync, readFileSync, readdirSync, cpSync, mkdtempSync, rmSync, statSync } from "node:fs";
import { resolve, join, relative } from "node:path";
import { tmpdir } from "node:os";

/**
 * The real CausalSmith package root (parent of tools/), for integration tests
 * that read actual bank artifacts. Throws if the layout is unexpected.
 */
export function causalSmithRoot(): string {
  const root = resolve(import.meta.dirname, "..", "..");
  const lakefile = join(root, "lakefile.toml");
  if (!existsSync(lakefile) || !/name\s*=\s*"CausalSmith"/.test(readFileSync(lakefile, "utf8"))) {
    throw new Error(`expected CausalSmith package root at ${root}`);
  }
  return root;
}

/**
 * The first accepted bank entry currently on disk, as `{qid, spec}`. Integration tests that load a
 * real banked paper use this instead of a hardcoded qid, so they track whatever paper is banked now
 * and never go stale when the bank is re-curated (a banked paper is removed/renamed). Throws if no
 * accepted entry exists. An accepted entry is a `<qid>_<spec>` directory carrying its state file
 * (the bare `state.json`, or the legacy `<qid>_<spec>_state.json` for un-migrated entries).
 */
export function acceptedBankEntry(): { qid: string; spec: string } {
  const dir = join(causalSmithRoot(), "doc", "research", "_bank", "accepted");
  for (const name of readdirSync(dir).sort()) {
    const m = name.match(/^(.+)_(v\d+)$/);
    if (!m) continue;
    const hasState =
      existsSync(join(dir, name, "state.json")) ||
      existsSync(join(dir, name, `${name}_state.json`));
    if (hasState) return { qid: m[1], spec: m[2] };
  }
  throw new Error(`no accepted bank entry under ${dir}`);
}

/** Every file under `dir`, as paths relative to it. */
function filesUnder(dir: string): string[] {
  const out: string[] = [];
  const walk = (d: string): void => {
    for (const name of readdirSync(d)) {
      const p = join(d, name);
      if (statSync(p).isDirectory()) walk(p);
      else out.push(relative(dir, p));
    }
  };
  walk(dir);
  return out;
}

/**
 * Snapshot the accepted bank entry `<qid>_<spec>` and return a restore function.
 *
 * The presentation pipeline persists into the REAL bank: the P1 statement audit freezes every
 * faithful body onto `graph.json` (`--refresh-frozen-bodies` releases them), promotion rewrites
 * it, and P5 appends to `README.md`. Integration tests run that pipeline against the real
 * `repoRoot` with STUBBED models, so without this guard a test run commits stub statement bodies
 * into a tracked bank record — observed 2026-08-21, when 23 nodes of exp_bipartite_minimax_design_v1
 * were rewritten to "Touched statement body." / "Stub Title".
 *
 * Call at module scope (before any pipeline run) and register the result in `afterAll`. Restore
 * overwrites in place and deletes files the run added; it never removes the entry directory, so a
 * crash mid-restore cannot leave the bank without its record.
 */
export function guardBankEntry(qid: string, spec: string): () => void {
  const dir = join(causalSmithRoot(), "doc", "research", "_bank", "accepted", `${qid}_${spec}`);
  const snapshot = join(mkdtempSync(join(tmpdir(), "causalsmith-bank-guard-")), "entry");
  cpSync(dir, snapshot, { recursive: true });
  const original = new Set(filesUnder(snapshot));
  return () => {
    cpSync(snapshot, dir, { recursive: true, force: true });
    for (const rel of filesUnder(dir)) if (!original.has(rel)) rmSync(join(dir, rel), { force: true });
    rmSync(resolve(snapshot, ".."), { recursive: true, force: true });
  };
}
