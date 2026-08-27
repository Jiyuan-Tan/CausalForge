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
import { assertP2AssemblyFresh } from "./assembly_freshness.js";
import { PROMOTION_ESCALATION_MARKER, PROOF_AUDIT_FAILURE_MARKER, runPromotionRound } from "./promotion.js";
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
    /** See ClaudeRunInput.onResolvedModel — surfaces the id an alias like "opus" resolved to. */
    onResolvedModel?: (modelId: string) => void;
  }) => Promise<string>;
  runCodex: (args: {
    prompt: string;
    cwd: string;
    reasoningEffort?: "minimal" | "low" | "medium" | "high" | "xhigh";
    leanLsp?: boolean;
    webSearch?: boolean;
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
  /** On a P2 render-key miss, keep an existing proof file as an unaudited
   * candidate and send it through the normal proof audit/refinement gate. */
  reuseExistingProofsForAudit?: boolean;
  /** With `--from P2`: run P2 in reassemble mode (rebuild paper.tex from the
   * on-disk authored sources, no drafting) — the manual-revision re-entry after
   * hand-edits to front_matter.tex / sections/ / proofs/. */
  reassembleP2?: boolean;
  /** With `--from P1`: release every audit-frozen body (`nl.frozen_body`) before planning, so the
   * render prompts are applied afresh to the whole layer. Every body then re-renders and re-audits
   * (the audit re-freezes what passes). The deliberate knob for pushing a render-prompt
   * improvement into a paper whose bodies are otherwise locked against prompt churn. */
  refreshFrozenBodies?: boolean;
  /**
   * Grant one further P2 promotion round. The orchestrator sets this after reading the audit
   * findings on a `P2 promotion decision required` halt and judging that the failing proofs lack
   * a citable step rather than being mis-rendered.
   */
  promoteAgain?: boolean;
  /** P6 only: regenerate slides.md even over hand edits (which are otherwise kept). */
  refreshSlides?: boolean;
}

export interface StageIO {
  ctx: PaperCtx;
  state: PaperState;
  bank: BankEntry;
  outDir: string;
  /** P2 only, revision cycle: reassemble paper.tex from the on-disk authored
   * sources (which the P5 reviser just edited) — never re-draft; a missing or
   * contract-violating source is an error, not a redraft trigger. */
  reassemble?: boolean;
  /** Revision entry (P5 cycle or `--from P2 --reassemble`): P3 runs hard gates
   * only and skips the rubric — the P5 referee is the holistic judge of a
   * revision, so re-scoring it here duplicates full-paper calls per cycle. */
  revisionCycle?: boolean;
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
  let bank = await loadBankEntry(ctx.repoRoot, ctx.qid, ctx.spec);
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
  let promotionUsed = false;
  for (let i = startIdx; i < ORDER.length; i++) {
    const { stage, fn, checkpointAfter } = ORDER[i];
    const io = { ctx, state, bank, outDir, reassemble: stage === "P2" && ctx.reassembleP2 === true, revisionCycle: ctx.reassembleP2 === true };
    // Persist state BEFORE re-throwing a stage failure: stages push notes and set
    // hard_gate_failures while running, and state otherwise reaches disk only on stage
    // success — so every failure exit silently discarded its own diagnosis (P3 grew a
    // local workaround, failP3; every other stage lost its notes — audit, 2026-08-26).
    // Best-effort: a save failure must never mask the stage's real error.
    const failStage = async (err: unknown): Promise<never> => {
      try {
        await savePaperState(outDir, state);
      } catch { /* keep the original error */ }
      throw err;
    };
    try {
      await fn(io);
    } catch (err) {
      // PROMOTION ROUND (once per invocation): a P2 proof-audit failure usually means the
      // failing steps' content needs to become citable auxiliary lemmas. Author them
      // (agent call), re-run P1 as a cheap delta (only new statements render/audit),
      // and retry P2 once. Anything else — or a second failure — propagates as before.
      const msg = err instanceof Error ? err.message : String(err);
      // Never in a reassemble/revision re-entry: new formal environments are forbidden
      // there (no draft checkpoint would review them, and a promoted lemma has no
      // rendered proof for the reassemble guard to reuse).
      if (stage !== "P2" || promotionUsed || ctx.reassembleP2 === true || !msg.includes(PROOF_AUDIT_FAILURE_MARKER)) await failStage(err);
      // Bounded across the whole bundle, not just this invocation: `promotionUsed` caps rounds
      // per process, so re-entering P2 repeatedly grants a fresh round each time and the chain
      // grows without limit. The persisted budget is what actually terminates it; at the cap the
      // run halts for adjudication rather than promoting again.
      if (state.promotion_rounds > 0 && ctx.promoteAgain !== true) {
        state.notes.push(
          `P2 promotion decision required after ${state.promotion_rounds} round(s): the orchestrator decides ` +
            `whether another round closes a gap or the proofs need adjudicating.`,
        );
        await savePaperState(outDir, state);
        throw new Error(
          `${PROMOTION_ESCALATION_MARKER}: ${state.promotion_rounds} promotion round(s) already ran and proofs ` +
            `still fail the audit. Read the findings below and decide. A further round helps only when a proof ` +
            `lacks a CITABLE STEP; it cannot fix a rendering defect (leaked conventions, mis-attribution, an ` +
            `omitted conjunct, symbol shadowing), which needs the proof or the statement adjudicated instead. ` +
            `To grant another round, re-run with --promote-again.\n\n${msg}`,
        );
      }
      promotionUsed = true;
      // Record the round BEFORE the agent mutates graph.json: a crash between the graph edit and
      // this save would otherwise hand the next process a fresh automatic round over an
      // already-grown graph, which is the cascade this guards. The trade-off is that a crashed
      // or refused promotion still consumes the automatic round — recoverable, since the
      // orchestrator can grant another with --promote-again, and loud either way.
      state.promotion_rounds += 1;
      await savePaperState(outDir, state);
      const added = await runPromotionRound(io, msg);
      state.notes.push(
        `P2 promotion round ${state.promotion_rounds}: added ${added} — review at the draft checkpoint.`,
      );
      await savePaperState(outDir, state);
      // The promotion agent edited graph.json ON DISK; the loaded bank (graph, crosswalk,
      // lean pointers) is stale. Reload so the P1 re-run, the P2 retry, and every later
      // stage see the new nodes.
      bank = await loadBankEntry(ctx.repoRoot, ctx.qid, ctx.spec);
      const retryIo = { ...io, bank };
      try {
        await stageP1({ ...retryIo, reassemble: false });
        await fn(retryIo);
      } catch (retryErr) {
        await failStage(retryErr); // the retry's notes must survive its failure too
      }
    }
    state.stage_completed = stage;
    // A reassemble re-entry is a revision of an already-reviewed draft, not a first
    // draft awaiting approval — do not halt it at the P2 draft checkpoint.
    const skipCheckpoint = ctx.auto || (stage === "P2" && ctx.reassembleP2 === true);
    if (checkpointAfter && !skipCheckpoint) state.checkpoint_pending = checkpointAfter;
    await savePaperState(outDir, state);
    if (stage === "P5") {
      p5ReviewsRun += 1;
      if (ctx.maxP5Reviews !== undefined && p5ReviewsRun >= ctx.maxP5Reviews) {
        return { halt: "p5:review-cap" };
      }
    }
    if (ctx.stopAfter === stage) return { halt: `stopped:${stage}` };
    if (checkpointAfter && !skipCheckpoint) return { halt: `checkpoint:${checkpointAfter}` };
  }
  // P5 revision: one holistic manuscript reviser may make at most two passes.
  // Initial P1/P2 drafting remains stage-structured, but referee-driven repair no
  // longer rewinds through independent outline/section/proof writers. The reviser
  // may reframe the whole paper while the verification contract freezes the math.
  if (!ctx.deps.dryRun && ctx.stopAfter === undefined) {
    while (true) {
      // Stale-source guard: if the authored sources are newer than the recorded
      // assembly (a prior pass's reviser succeeded but the P2→P5 re-gate died, or
      // the operator hand-edited sources before --resume), finish the re-gate FIRST.
      // Without this, the loop would re-dispatch the reviser against the old review
      // and misroute to p5:non-converging on identical fingerprints.
      const assemblyStale = await assertP2AssemblyFresh(outDir).then(() => false, () => true);
      if (assemblyStale) {
        for (const stage of ["P2", "P3", "P4", "P5"] as const) {
          const { fn } = ORDER.find((entry) => entry.stage === stage)!;
          await fn({ ctx, state, bank, outDir, reassemble: stage === "P2", revisionCycle: true });
          state.stage_completed = stage;
          await savePaperState(outDir, state);
          if (stage === "P5") {
            p5ReviewsRun += 1;
            if (ctx.maxP5Reviews !== undefined && p5ReviewsRun >= ctx.maxP5Reviews) {
              return { halt: "p5:review-cap" };
            }
          }
        }
        continue;
      }
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
      // P2 runs in reassemble mode: the reviser edited the authored sources
      // (front_matter/sections/proofs), so P2 rebuilds paper.tex from disk with
      // no drafting; P3 then re-gates the revised text and P4 re-emits.
      for (const stage of ["P2", "P3", "P4", "P5"] as const) {
        const { fn } = ORDER.find((entry) => entry.stage === stage)!;
        await fn({ ctx, state, bank, outDir, reassemble: stage === "P2", revisionCycle: true });
        state.stage_completed = stage;
        await savePaperState(outDir, state);
        if (stage === "P5") {
          p5ReviewsRun += 1;
          if (ctx.maxP5Reviews !== undefined && p5ReviewsRun >= ctx.maxP5Reviews) {
            return { halt: "p5:review-cap" };
          }
        }
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
