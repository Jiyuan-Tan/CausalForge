import { readFile } from "node:fs/promises";
import { STAGE_ORDER } from "../constants.js";
import { pipelineLogPath } from "../paths.js";
import type { PipelineContext, Stage, StateJson } from "../types.js";

function isLaterStage(candidate: unknown, target: Stage): boolean {
  if (typeof candidate !== "string") return false;
  const candidateIndex = STAGE_ORDER.indexOf(candidate as Stage);
  const targetIndex = STAGE_ORDER.indexOf(target);
  return candidateIndex > targetIndex;
}

/**
 * True when durable run history shows that a stage after `target` has ever run.
 *
 * `--from-stage` deliberately leaves `state.stage_completed` at the old cursor
 * until the re-entered stage finishes, so the current state catches the common
 * post-F5 rewind. Programmatic rewinds can lower that cursor, however; the
 * append-only pipeline log is the durable fallback that prevents a later
 * resume from being misclassified as a cold first pass.
 */
export async function laterStageEverRan(
  ctx: PipelineContext,
  state: StateJson,
  target: Stage,
): Promise<boolean> {
  if (isLaterStage(state.stage_completed, target)) return true;
  if (state.theorems?.some((entry) => isLaterStage(entry.stage_completed, target))) return true;

  let raw: string;
  try {
    raw = await readFile(pipelineLogPath(ctx.repoRoot, ctx.qid, ctx.specialization), "utf8");
  } catch {
    return false;
  }
  for (const line of raw.split("\n")) {
    if (!line.trim()) continue;
    try {
      const event = JSON.parse(line) as { stage?: unknown };
      if (isLaterStage(event.stage, target)) return true;
    } catch {
      // A partial final JSONL line must not erase earlier valid history.
    }
  }
  return false;
}
