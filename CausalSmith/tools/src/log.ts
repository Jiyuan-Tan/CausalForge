import { mkdir, appendFile } from "node:fs/promises";
import path from "node:path";
import { pipelineLogPath, reviewsLogPath } from "./paths.js";
import type { PipelineContext, PipelineLogEntry } from "./types.js";
import type { Intervention, ReviewResult } from "./judgment.js";

export async function appendPipelineLog(
  ctx: Pick<PipelineContext, "repoRoot" | "qid" | "specialization">,
  entry: Omit<PipelineLogEntry, "timestamp">,
): Promise<void> {
  const file = pipelineLogPath(ctx.repoRoot, ctx.qid, ctx.specialization);
  await mkdir(path.dirname(file), { recursive: true });
  const line = JSON.stringify({ timestamp: new Date().toISOString(), ...entry });
  await appendFile(file, `${line}\n`, "utf8");
}

export type ReviewLogEntry =
  | {
      timestamp: string;
      stage: string;
      kind: "review";
      attempt: number;
      status: ReviewResult["status"];
      classification?: string;
      report_summary?: string;
      review?: ReviewResult;
    }
  | {
      timestamp: string;
      stage: string;
      kind: "intervention";
      attempt?: number;
      route: Intervention["route"];
      reason: string;
      proposed_action?: string;
      cite?: string;
      intervention: Intervention;
    };

export async function appendReviewLog(
  ctx: PipelineContext,
  entry: Omit<ReviewLogEntry, "timestamp">,
): Promise<void> {
  const file = reviewsLogPath(ctx.repoRoot, ctx.qid, ctx.specialization);
  await mkdir(path.dirname(file), { recursive: true });
  const line = JSON.stringify({ timestamp: new Date().toISOString(), ...entry });
  await appendFile(file, `${line}\n`, "utf8");
}
