import { readFile, writeFile, rename, mkdir } from "node:fs/promises";
import { join } from "node:path";
import { PaperState } from "./types.js";

const stateFile = (dir: string, qid: string, spec: string) =>
  join(dir, `${qid}_${spec}_paper_state.json`);

export function freshPaperState(qid: string, spec: string): PaperState {
  return {
    qid,
    spec,
    stage_completed: null,
    checkpoint_pending: null,
    pinned_commit: null,
    revision_round: 0,
    p5_revision_passes: 0,
    p5_last_fingerprints: [],
    hard_gate_failures: [],
    notes: [],
  };
}

export async function loadPaperState(
  dir: string,
  qid: string,
  spec: string,
): Promise<PaperState | null> {
  try {
    return PaperState.parse(JSON.parse(await readFile(stateFile(dir, qid, spec), "utf8")));
  } catch (e: unknown) {
    if ((e as NodeJS.ErrnoException)?.code === "ENOENT") return null;
    throw e;
  }
}

/**
 * Atomic write (temp + rename), mirroring src/state.ts.
 *
 * `notes` is append-only and every `--from` re-entry re-appends the same deterministic
 * lines, so it grew to 215 entries / 105 unique / 89 KB in one run, burying real signal
 * (P0 bib caveats, a failed docstring pass) under 17 copies of the same bib note.
 * De-duplicate on save, preserving first-occurrence order.
 */
export async function savePaperState(dir: string, s: PaperState): Promise<void> {
  s.notes = [...new Set(s.notes)];
  await mkdir(dir, { recursive: true });
  const target = stateFile(dir, s.qid, s.spec);
  const tmp = `${target}.tmp`;
  await writeFile(tmp, JSON.stringify(s, null, 2) + "\n", "utf8");
  await rename(tmp, target);
}
