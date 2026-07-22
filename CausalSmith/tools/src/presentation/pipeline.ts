import { loadBankEntry, type BankEntry } from "./bank.js";
import type { ClaudeModel } from "../models.js";
import type { Lookup } from "./citations.js";
import { loadPaperState, savePaperState, freshPaperState } from "./state.js";
import { writeFile } from "node:fs/promises";
import { join } from "node:path";
import { presentationDir } from "./paths.js";
import { type PaperStage, type PaperState } from "./types.js";
import { stageP0 } from "./stages/p0_literature.js";
import { stageP1 } from "./stages/p1_plan.js";
import { stageP2 } from "./stages/p2_draft.js";
import { stageP3 } from "./stages/p3_gates.js";
import { stageP4 } from "./stages/p4_emit.js";
import { stageP5 } from "./stages/p5_review.js";
import { stageP5HolisticRevision } from "./stages/p5_holistic_revision.js";
import { loadPriorReview } from "./revision_brief.js";
import {
  MAX_P5_REVISION_PASSES,
  findingFingerprint,
  partitionFindings,
  renderRoutingPlan,
} from "./revision_routing.js";

/** Injected model runners (matches src/workers/claude.ts and src/shared/codex.ts). */
export interface PaperDeps {
  /** Resolved default model for model-sensitive presentation caches/logging. */
  codexModel?: string;
  runClaude: (args: {
    prompt: string;
    model: ClaudeModel;
    cwd: string;
    allowedTools?: string[];
  }) => Promise<string>;
  runCodex: (args: {
    prompt: string;
    cwd: string;
    reasoningEffort?: "minimal" | "low" | "medium" | "high" | "xhigh";
    leanLsp?: boolean;
    /** codex model id override (present mode defaults to MODELS.codexPresentation). */
    model?: string;
    /** Codex native sub-agents — default-off (opt-in); set true only for a lone low-concurrency call whose prompt uses spawn_agent (see CodexRunInput.multiAgent). */
    multiAgent?: boolean;
  }) => Promise<{ stdout: string; stderr: string }>;
  /** Citation metadata lookup; defaults to live Crossref/arXiv (citations.defaultLookup). */
  lookup?: Lookup;
  dryRun: boolean;
}

export interface PaperCtx {
  repoRoot: string;
  qid: string;
  spec: string;
  deps: PaperDeps;
  resume?: boolean;
  /** Approve the P1/P2 human checkpoints automatically. Hard gates and terminal
   * holistic-revision halts are unchanged. */
  auto?: boolean;
  stopAfter?: PaperStage;
  /** Maximum number of P5 referee passes in this invocation, counting the
   * initial review. Useful for an explicitly bounded presentation run. */
  maxP5Reviews?: number;
  /** Re-enter the pipeline at this stage (e.g. `--from P4` to re-emit + re-review
   * after the orchestrator edits paper.tex per the P5 referee report). Loads
   * prior state and runs forward from here, ignoring stage_completed. */
  from?: PaperStage;
  /** Output dir override (tests MUST set this — the default is the live run dir). */
  outDir?: string;
  /** Internal cost mode used by P3's independent rubric review. */
  p3ReviewMode?: "intermediate" | "final";
}

export interface StageIO {
  ctx: PaperCtx;
  state: PaperState;
  bank: BankEntry;
  outDir: string;
}

export type StageFn = (io: StageIO) => Promise<void>;

const ORDER: { stage: PaperStage; fn: StageFn; checkpointAfter?: "outline" | "draft" }[] = [
  { stage: "P0", fn: stageP0 },
  { stage: "P1", fn: stageP1, checkpointAfter: "outline" },
  { stage: "P2", fn: stageP2, checkpointAfter: "draft" },
  { stage: "P3", fn: stageP3 },
  { stage: "P4", fn: stageP4 },
  { stage: "P5", fn: stageP5 },
];

export async function runPaperPipeline(ctx: PaperCtx): Promise<{ halt: string }> {
  const outDir = ctx.outDir ?? presentationDir(ctx.repoRoot, ctx.qid, ctx.spec);
  const bank = await loadBankEntry(ctx.repoRoot, ctx.qid, ctx.spec);
  const prior = ctx.resume || ctx.from || ctx.auto ? await loadPaperState(outDir, ctx.qid, ctx.spec) : null;
  const state = prior ?? freshPaperState(ctx.qid, ctx.spec);
  if (state.checkpoint_pending && ctx.resume) state.checkpoint_pending = null; // resume = checkpoint approved
  if (state.checkpoint_pending && ctx.auto) state.checkpoint_pending = null; // auto = checkpoint approved
  let startIdx: number;
  let p5ReviewsRun = 0;
  if (ctx.from) {
    startIdx = ORDER.findIndex((s) => s.stage === ctx.from);
    if (startIdx < 0) throw new Error(`unknown --from stage: ${ctx.from}`);
    state.checkpoint_pending = null; // explicit re-entry overrides any pending checkpoint
    // An explicit re-entry is a NEW revision budget. Without this the persisted
    // counter stays latched at MAX_P5_REVISION_PASSES forever, so every later
    // `--from P4` re-pays a full P3+P4+P5 (incl. a ~140k-char referee call) and
    // then halts `p5:iteration-cap` without ever invoking the reviser.
    state.p5_revision_passes = 0;
    state.p5_last_fingerprints = [];
  } else {
    startIdx = state.stage_completed
      ? ORDER.findIndex((s) => s.stage === state.stage_completed) + 1
      : 0;
  }
  for (let i = startIdx; i < ORDER.length; i++) {
    const { stage, fn, checkpointAfter } = ORDER[i];
    await fn({ ctx, state, bank, outDir });
    state.stage_completed = stage;
    if (checkpointAfter && !ctx.auto) state.checkpoint_pending = checkpointAfter;
    await savePaperState(outDir, state);
    if (stage === "P5") {
      p5ReviewsRun += 1;
      if (ctx.maxP5Reviews !== undefined && p5ReviewsRun >= ctx.maxP5Reviews) {
        return { halt: "p5:review-cap" };
      }
    }
    if (ctx.stopAfter === stage) return { halt: `stopped:${stage}` };
    if (checkpointAfter && !ctx.auto) return { halt: `checkpoint:${checkpointAfter}` };
  }
  // P5 revision: one holistic manuscript reviser may make at most two passes.
  // Initial P1/P2 drafting remains stage-structured, but referee-driven repair no
  // longer rewinds through independent outline/section/proof writers. The reviser
  // may reframe the whole paper while the verification contract freezes the math.
  if (!ctx.deps.dryRun && ctx.stopAfter === undefined) {
    while (true) {
      const review = await loadPriorReview(outDir);
      if (!review) break;
      if (review.recommendation === "accept" && review.findings.length === 0) break;
      const { repairable, blocked } = partitionFindings(review.findings);
      await writeFile(join(outDir, "p5_revision_routing.md"), renderRoutingPlan(review), "utf8");
      if (repairable.length === 0) {
        const researchMajor = blocked.filter((f) => f.severity === "major" && f.remedy && f.remedy !== "rewrite");
        state.notes.push(researchMajor.length > 0
          ? `P5 holistic revision halted: ${researchMajor.length} major finding(s) require new research/source work.`
          : `P5 holistic revision halted: ${blocked.length} finding(s) require adjudication.`);
        await savePaperState(outDir, state);
        return { halt: researchMajor.length > 0 ? "p5:research-required" : "p5:adjudication" };
      }
      // Non-convergence guard: if this pass would attack exactly the same finding
      // set as the last one, the reviser has already tried and failed on it. Halt
      // rather than re-paying a reviser + P3 + P4 + referee cycle for a repeat.
      const fingerprints = repairable.map(findingFingerprint).sort();
      if (
        state.p5_last_fingerprints.length > 0 &&
        fingerprints.length === state.p5_last_fingerprints.length &&
        fingerprints.every((f, i) => f === state.p5_last_fingerprints[i])
      ) {
        state.notes.push(
          `P5 holistic revision halted: pass ${state.p5_revision_passes} left the same ${fingerprints.length} finding(s) unrepaired (${fingerprints.join(", ")}).`,
        );
        await savePaperState(outDir, state);
        return { halt: "p5:non-converging" };
      }
      if (state.p5_revision_passes >= MAX_P5_REVISION_PASSES) {
        state.notes.push(`P5 holistic revision reached the ${MAX_P5_REVISION_PASSES}-pass cap.`);
        await savePaperState(outDir, state);
        return { halt: "p5:iteration-cap" };
      }
      const revised = await stageP5HolisticRevision({ ctx, state, bank, outDir }, review, repairable);
      if (!revised.changed) {
        state.notes.push("P5 holistic revision halted: the reviser produced no authored-source change.");
        await savePaperState(outDir, state);
        return { halt: "p5:stalled" };
      }
      state.p5_last_fingerprints = revised.fingerprints;
      state.p5_revision_passes += 1;
      state.revision_round += 1;
      state.notes.push(`P5 holistic revision pass ${state.p5_revision_passes}/${MAX_P5_REVISION_PASSES}.`);
      await savePaperState(outDir, state);
      const priorReviewMode = ctx.p3ReviewMode;
      ctx.p3ReviewMode = "final";
      try {
        for (const stage of ["P3", "P4", "P5"] as const) {
          const { fn } = ORDER.find((entry) => entry.stage === stage)!;
          await fn({ ctx, state, bank, outDir });
          state.stage_completed = stage;
          await savePaperState(outDir, state);
          if (stage === "P5") {
            p5ReviewsRun += 1;
            if (ctx.maxP5Reviews !== undefined && p5ReviewsRun >= ctx.maxP5Reviews) {
              return { halt: "p5:review-cap" };
            }
          }
        }
      } finally {
        ctx.p3ReviewMode = priorReviewMode;
      }
    }
    const residual = await loadPriorReview(outDir);
    if (residual && !(residual.recommendation === "accept" && residual.findings.length === 0)) {
      await writeFile(join(outDir, "p5_revision_routing.md"), renderRoutingPlan(residual), "utf8");
      state.notes.push(`P5 holistic revision reached the ${MAX_P5_REVISION_PASSES}-pass cap.`);
      await savePaperState(outDir, state);
      return { halt: "p5:iteration-cap" };
    }
  }
  return { halt: "done" };
}
