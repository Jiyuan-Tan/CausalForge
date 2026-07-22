/**
 * Phase 4 — glue: invoke propose_next, render CHECKPOINT_NEXT.md, persist it.
 *
 * Called from:
 *   - `pipeline.ts::runPostStage5CloseHook` after research Stage 5 closes
 *     cleanly (and the OpenQuestion was minted to a BankedTheorem).
 *   - `study/stageS2.ts::run` after the S2 commit + index rebuild succeed.
 *
 * Contract: every callable here is wrapped in a top-level try/catch at the
 * call site so a writer failure logs a warning but never blocks the run from
 * completing (spec §R5).
 */

import path from "node:path";
import { mkdir, rename, writeFile } from "node:fs/promises";
import { proposeNext, type CodexRunner } from "./propose_next.js";
import { renderCheckpointNext } from "./checkpoint_next.js";

export interface CheckpointNextWriterInput {
  loop: "research" | "study";
  run_id: string;
  /** Absolute path to the run's directory. CHECKPOINT_NEXT.md is written here. */
  run_dir: string;
  /** Absolute path to `<package>/doc/study`. */
  graph_root: string;
  /** Plain-English summary of what just completed. */
  run_summary: string;
  /** Optional method id used to scope OQ filtering. */
  method_id?: string | null;
  /** Optional lineage metadata; depth defaults to 0 when absent. */
  lineage_depth?: number;
  lineage_origin?: string;
  /** Override the codex dispatcher (tests inject a stub). */
  runCodex?: CodexRunner;
}

export interface CheckpointNextWriterResult {
  path: string;
  fallback: boolean;
}

export async function writeCheckpointNext(
  input: CheckpointNextWriterInput,
): Promise<CheckpointNextWriterResult> {
  const result = await proposeNext(
    {
      loop: input.loop,
      run_id: input.run_id,
      text: input.run_summary,
      method_id: input.method_id ?? null,
    },
    {
      graphRoot: input.graph_root,
      runCodex: input.runCodex,
      cwd: path.dirname(input.graph_root),
    },
  );

  const md = renderCheckpointNext({
    run_id: input.run_id,
    loop: input.loop,
    what_just_finished: input.run_summary,
    options: result.options,
    lineage_depth: input.lineage_depth ?? 0,
    lineage_origin: input.lineage_origin,
    fallback: result.fallback,
  });

  await mkdir(input.run_dir, { recursive: true });
  const finalPath = path.join(input.run_dir, "CHECKPOINT_NEXT.md");
  const tmpPath = `${finalPath}.new`;
  await writeFile(tmpPath, md, "utf8");
  await rename(tmpPath, finalPath);
  return { path: finalPath, fallback: result.fallback };
}
