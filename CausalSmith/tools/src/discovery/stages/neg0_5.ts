// Discovery Stage -0.5 (proposal reviewer + angle/revise/pivot loop).
// Extracted from pipeline_stages.ts in Step 2.2 of the three-submodules refactor.

import path from "node:path";
import { mkdir, readdir, readFile, writeFile } from "node:fs/promises";
import { existsSync } from "node:fs";
import { MODEL_PLAN } from "../../constants.js";
import { extractJsonObject } from "../../judgment.js";
import { formalizationDir, resolveInDir, templatePath } from "../../paths.js";
import { saveState } from "../../state.js";
import type { PipelineContext, StageResult, StateJson } from "../../types.js";
import {
  artifactPaths,
  cleanupRenderedTemplate,
  readIfExists,
  readPrompt,
  type StageDeps,
} from "../../pipeline_support.js";
import { meetsNoveltyFloor, tierFloorBlock } from "../../pipeline_stages.js";
import type { NoveltyTarget } from "../../novelty.js";
import {
  runStageNeg1_2,
  logNeg1Review,
  buildDrafterHandoff,
  NEG1_NONFLAGSHIP_KILL_VERSION,
  NEG1_PIVOT_BUDGET,
  NEG1_REVISE_CAP,
  NEG1_ENV_FAILURE_RETRY_BUDGET,
} from "./neg1_2.js";
import { protoCoreJsonPath } from "./neg1_2_author.js";
import {
  collectFlagCodes,
  decideRejectEscape,
  decideReviseOutcome,
  decideTierSaturationPromote,
  normalizeReviewVerdict,
} from "./neg0_5_decision.js";
import { renderRefereeTemplate, runReferee, stripTemplateScaffolding } from "../framework/referee.js";
import { parseRepairedModelJson } from "../core/core_io.js";

/**
 * Dual-producer retarget block for the D-0.5 reviewer (D0_CORE_REDESIGN.md §12.5).
 *
 * Once D-1.2 emits a `proto_core.json`, the reviewer judges that ONE artifact:
 * the typed proto_core (the authoritative formal content and prose). This returns
 * the core inlined, or "" when no proto_core exists yet (the legacy monolithic
 * `.tex` path is unchanged — the block is simply absent). Safe in both regimes.
 */
export async function buildProtoCoreReviewBlock(ctx: PipelineContext): Promise<string> {
  const src = await readIfExists(protoCoreJsonPath(ctx));
  if (!src) return "";
  // Validate AND canonicalize before inlining. The proto core is written by the
  // AGENT (no atomic wrapper), and the resume guard only checks `existsSync` while
  // this function only checked non-empty — so a torn file was inlined verbatim and
  // a full reviewer dispatch was paid to review garbage, with the real failure
  // surfacing much later in D0-SOLVE. Reading through the three-layer escape
  // defense additionally rescues an under-escaped agent-raw core (`\alpha`) and a
  // legacy `\texttt`→tab corruption instead of inlining it for the reviewer.
  let canonical: string;
  try {
    canonical = JSON.stringify(parseRepairedModelJson(src, protoCoreJsonPath(ctx)), null, 2);
  } catch (err) {
    throw new Error(
      `D-0.5 cannot review: proto_core.json at ${protoCoreJsonPath(ctx)} is not valid JSON ` +
        `(${err instanceof Error ? err.message : String(err)}). This is a torn/partial producer write ` +
        `or unrecoverable escape corruption, NOT a review verdict — re-run the D-1.2 producer before ` +
        `the review boundary.`,
    );
  }
  // No adapter: the single-artifact rubric (stage_neg1_review_core.txt) is itself
  // retargeted at the typed core, so we only need to inline the core.
  return ["=== PROPOSAL CORE (the artifact under review — typed source of truth) ===", canonical, "=== END PROPOSAL CORE ==="].join("\n");
}

/** Resolve the artifact D-0.5 must record and hand to the reviewer.
 *
 * Proto-core runs are deliberately single-artifact: `proposal.tex` may be a
 * legacy file from an earlier producer version and therefore MUST NOT remain
 * the reviewer path once the typed core exists. Keeping this decision in one
 * helper prevents the template, prompt, and checkpoint receipts from drifting.
 */
export function neg1ReviewArtifactPath(ctx: PipelineContext, legacyProposalTexPath: string): string {
  const corePath = protoCoreJsonPath(ctx);
  return existsSync(corePath) ? corePath : legacyProposalTexPath;
}

/**
 * Inspect a Stage -0.5 reviewer JSON and, when REJECTed for a localized
 * failure mode this angle hasn't yet rescued from, mutate `pf` to dispatch
 * the producer in the appropriate escape mode (kernel-replace > draft-rebuild),
 * record the angle in the corresponding used-angles array, and invoke
 * `runStageNeg1_2`. Returns true iff an escape was dispatched (caller should
 * `continue` the loop). Returns false when no escape applies, the angle has
 * already used the relevant escape, or the flag pattern doesn't match — in
 * which case the caller falls through to the pivot path.
 */
async function dispatchRejectEscape(args: {
  angle: number;
  reviewJson: Record<string, unknown>;
  pf: NonNullable<StateJson["proposed_from"]>;
  iterations: NonNullable<NonNullable<StateJson["proposed_from"]>["iterations"]>;
  ctx: PipelineContext;
  deps: StageDeps;
  state: StateJson;
  persistState: () => Promise<void>;
}): Promise<boolean> {
  const kernelUsed = args.pf.kernel_replace_used_angles ?? [];
  const draftUsed = args.pf.draft_rebuild_used_angles ?? [];
  const escapeMode = decideRejectEscape({
    codes: collectFlagCodes(args.reviewJson),
    angle: args.angle,
    kernelReplaceUsedAngles: kernelUsed,
    draftRebuildUsedAngles: draftUsed,
  });
  if (!escapeMode) return false;
  if (escapeMode === "kernel-replace") args.pf.kernel_replace_used_angles = [...kernelUsed, args.angle];
  else args.pf.draft_rebuild_used_angles = [...draftUsed, args.angle];

  args.pf.current_mode = escapeMode;
  // Keep current_version as-is; the producer increments it on entry. The
  // angle's iteration history is preserved so the producer's revise-style
  // head prompt can read the prior REJECT verdict.
  args.pf.iterations = args.iterations;
  await args.persistState();
  await runStageNeg1_2({ ctx: args.ctx, state: args.state, deps: args.deps });
  await args.persistState();
  return true;
}

/**
 * Stage -0.5 reviewer: review the current `proposal.tex` and own the
 * angle / revise / pivot loop. On REVISE / REJECT / cap-exhausted, calls the
 * Stage -1.2 producer as a callback to draft the next version. Exits with
 * ACCEPT (advance forward) or NO-PASS (checkpoint).
 */
export async function runStageNeg0_5(args: {
  ctx: PipelineContext;
  state: StateJson;
  deps: StageDeps;
}): Promise<StageResult> {
  // Stage -0.5 runs whenever the state carries a `proposed_from` record,
  // regardless of whether --propose was passed on this invocation. This makes
  // resumes after a programmatic rewind (e.g. Stage 0.5 boundary routing back
  // to "-1.2") correctly re-enter the proposal-review loop instead of skipping
  // ahead to Stage 0. Cold-start without --propose still skips: in that case
  // no proposed_from has been written by Stage -1.2 and we have nothing to review.
  if (!args.ctx.proposeTopic && !args.state.proposed_from) {
    return { stage: "-0.5", status: "skipped", message: "proposal review skipped" };
  }
  const pf = args.state.proposed_from;
  if (!pf) {
    return {
      stage: "-0.5",
      status: "blocked",
      advance: false,
      message: "Stage -0.5 has no proposed_from; run Stage -1.2 producer first",
    };
  }
  const paths = artifactPaths(args.ctx, args.state);
  const currentProposalArtifact = (): string => neg1ReviewArtifactPath(args.ctx, paths.proposalTex);
  // The flagship rubric (regime axes (a)–(j), soft tier-movers, hard caps) is
  // a single shared block injected into BOTH the -0.5 and 0.5 reviewers so the
  // two stages key off the same definitions (prevents the proposal/derivation
  // calibration drift). The review prompt keeps only its stage-specific routing.
  // Single-artifact path: when a proposal core exists, use the self-contained
  // core reviewer rubric (retargeted at the typed core; no .tex-structure / SC10
  // machinery). Otherwise the legacy monolithic-.tex rubric. The flagship rubric
  // is shared by both.
  // Resolved PER REVIEW ATTEMPT, not once per stage entry. `buildProtoCoreReviewBlock`
  // re-reads proto_core.json inside the loop, so hoisting this pinned the rubric to
  // whatever existed at stage entry: if the proto core first appears mid-loop, the
  // reviewer was handed the legacy .tex rubric while the prompt inlined a typed core —
  // mismatched rubric and artifact, and every finding it produces is suspect.
  const rubricCache = new Map<boolean, string>();
  const resolveReviewPrompt = async (): Promise<string> => {
    const hasCore = (await readIfExists(protoCoreJsonPath(args.ctx))).length > 0;
    const cached = rubricCache.get(hasCore);
    if (cached !== undefined) return cached;
    const [neg1ReviewBody, flagshipRubric] = await Promise.all([
      readPrompt(args.ctx, hasCore ? "stage_neg1_review_core.txt" : "stage_neg1_review.txt"),
      readPrompt(args.ctx, "stage_flagship_rubric.txt"),
    ]);
    const prompt = `${neg1ReviewBody}\n\n${flagshipRubric}`;
    rubricCache.set(hasCore, prompt);
    return prompt;
  };

  // Stage 0.5 rejection context (load-bearing on resume after rewound_from_stage0).
  // Built once per Stage -0.5 entry so each reviewer attempt sees the same evidence.
  const stage0_5RejectionBlock = await buildStage0_5RejectionContext({
    ctx: args.ctx,
    state: args.state,
  });

  // Phase 3 — method-scoped novelty corpus. When the run was launched via
  // `--from-question <oq_id>`, Stage -1.2 cached the seed Method id on
  // state.method_id. Walk the graph for BankedTheorems instantiating that
  // Method and render a compact block the reviewer uses INSTEAD of the
  // full-bank scan. Empty string under legacy (full-bank) invocations.
  let methodScopedNoveltyBlock = "";
  if (args.state.from_question_oq_id && args.state.method_id) {
    try {
      const { loadGraph, bankedTheoremsForMethod } = await import("../../shared/graph.js");
      const graph = await loadGraph(path.join(args.ctx.repoRoot, "doc", "study"));
      const allBts = bankedTheoremsForMethod(graph, args.state.method_id, Number.MAX_SAFE_INTEGER);
      const limit = 10;
      const shown = allBts.slice(0, limit);
      const truncated = allBts.length > limit;
      const lines: string[] = [
        "=== METHOD_SCOPED_BANKED_PRECEDENTS (load-bearing — see method-scoped novelty corpus directive in base prompt) ===",
        `method_id: ${args.state.method_id}`,
      ];
      if (shown.length === 0) {
        lines.push("_(none — this method has no banked precedents in the graph)_");
      } else {
        for (const bt of shown) {
          const inst = (bt.instantiates ?? []).join(", ") || "—";
          const uses = (bt.uses ?? []).join(", ") || "—";
          lines.push(`- ${bt.bt_id}: instantiates [${inst}], uses [${uses}]`);
        }
        if (truncated) {
          lines.push(`_(showing top ${limit} of ${allBts.length}; older entries omitted)_`);
        }
      }
      lines.push("=== END METHOD_SCOPED_BANKED_PRECEDENTS ===");
      methodScopedNoveltyBlock = lines.join("\n");
    } catch (err) {
      // Failure here just leaves the reviewer in legacy full-bank mode.
      const msg = err instanceof Error ? err.message : String(err);
      // eslint-disable-next-line no-console
      console.warn(
        `[stage -0.5] method-scoped novelty corpus unavailable (${msg}); falling back to full-bank reviewer scan.`,
      );
    }
  }

  const iterations = pf.iterations ?? [];
  const archivedProposals = pf.archived_proposals ?? [];
  const exhaustedAngles = pf.exhausted_angles ?? [];
  // The run's ambition floor. Both the tier-saturation auto-promote and the
  // early angle-kill below gate on "reached this floor tier" rather than the
  // literal "flagship", so a nonflagship target gets the full revise runway
  // and can converge to ACCEPT via clean revises. Default mirrors the
  // proposal-stage default novelty target (`field`).
  const noveltyTarget = pf.novelty_target ?? "field";

  const persistState = (): Promise<void> =>
    saveState(args.ctx.repoRoot, args.ctx.qid, args.ctx.specialization, args.state);

  const reviseCapForAngle = (angle: number): number =>
    pf.revision_cap_by_angle?.[String(angle)] ?? NEG1_REVISE_CAP;

  const checkpointAngle = async (checkpoint: NonNullable<typeof pf.angle_checkpoint>): Promise<StageResult> => {
    pf.angle_checkpoint = checkpoint;
    pf.iterations = iterations;
    pf.archived_proposals = archivedProposals;
    pf.exhausted_angles = exhaustedAngles;
    await persistState();
    const actions = checkpoint.kind === "revise"
      ? "continue"
      : "switch | retry --extra-revisions N | give-up";
    return {
      stage: "-0.5",
      status: "checkpoint",
      advance: false,
      message:
        `D-0.5 ${checkpoint.kind} checkpoint on angle ${checkpoint.angle} v${checkpoint.version}: ` +
        `${checkpoint.reason}. Resolve atomically with ` +
        `\`causalsmith research --angle-action ${actions} <qid> <spec> ` +
        `[--angle-directive <text|->] --auto\`. No next proposer has started.`,
      artifacts: [currentProposalArtifact()],
    };
  };

  // Counts environment-failure retries across the whole loop. An env failure
  // (codex sandbox could not start) is not a statement about the angle, so it
  // must NOT pivot; we retry the same draft up to the budget, then abort.
  // CARRIED across resumes. This was a process-local counter, so the abort below left
  // `last_draft_status === "env-failure"` in state, every resume re-entered the branch with
  // the counter at 0, and re-dispatched the producer a full budget of times — unbounded and
  // unaudited, with no cap gate.
  let envFailureRetries = args.state.flags.neg1_env_failure_retries ?? 0;

  while ((pf.current_angle_index ?? 0) < NEG1_PIVOT_BUDGET) {
    const angle = pf.current_angle_index ?? 0;
    const version = pf.current_version ?? 1;
    const mode = pf.current_mode ?? "cold-start";

    // Environment failure (sandbox/FS could not start) — distinct from a
    // mathematical judgment about the angle. Do NOT burn the angle: retry the
    // SAME draft a bounded number of times, then abort WITHOUT pivot so the
    // angle is preserved for `--resume` once the sandbox is repaired. (Observed:
    // angle 0 REVISE@field abandoned to a spurious pivot on a single
    // `spawn setup refresh`.)
    if (pf.last_draft_status === "env-failure") {
      envFailureRetries += 1;
      args.state.flags.neg1_env_failure_retries = envFailureRetries;
      if (envFailureRetries > NEG1_ENV_FAILURE_RETRY_BUDGET) {
        iterations.push({ angle, version, mode, verdict: "env-failure-abort" });
        pf.iterations = iterations;
        // Raise the cap gate, or the abort is UNRECOVERABLE by the resume it prescribes:
        // the over-budget counter persists with `last_draft_status` still "env-failure",
        // so a plain `--resume` re-enters this branch, increments again and re-aborts
        // forever — a healthy angle permanently presents as dead. `stage_neg1_fallback`
        // is the designed escape: its CapGate.clear resets `neg1_env_failure_retries`.
        args.state.flags.stage_neg1_fallback =
          `D-0.5 producer environment failure (sandbox could not start) ${envFailureRetries}× on angle ${angle}`;
        await persistState();
        return {
          stage: "-0.5",
          status: "blocked",
          advance: false,
          message:
            `Stage -1.2 producer hit a non-recoverable environment failure ` +
            `(codex sandbox could not start — e.g. 'spawn setup refresh') ` +
            `${envFailureRetries}× on angle ${angle} v${version} (${mode}). ` +
            `Aborting WITHOUT pivot so the angle is preserved. Repair the codex ` +
            `write sandbox (apply_patch), then resume with ` +
            `\`--clear-gate stage_neg1_fallback\` to retry this draft (a plain ` +
            `--resume cannot clear the exhausted retry counter).`,
          artifacts: [currentProposalArtifact()],
        };
      }
      // eslint-disable-next-line no-console
      console.warn(
        `[stage -0.5] env-failure on angle ${angle} v${version} (${mode}); ` +
          `retry ${envFailureRetries}/${NEG1_ENV_FAILURE_RETRY_BUDGET} (NOT pivoting).`,
      );
      // Re-attempt the same mode/angle. runStageNeg1_2 re-dispatches the
      // producer; on success last_draft_status flips to "completed" and the
      // loop proceeds to review.
      await runStageNeg1_2({ ctx: args.ctx, state: args.state, deps: args.deps });
      await persistState();
      continue;
    }

    // Producer-side failure (invalid-draft / needs-pivot) → angle is dead.
    if (pf.last_draft_status && pf.last_draft_status !== "completed") {
      iterations.push({ angle, version, mode, verdict: pf.last_draft_status });
      pf.iterations = iterations;
      await persistState();
      return checkpointAngle({
        kind: "angle-boundary",
        angle,
        version,
        verdict: pf.last_draft_status,
        reason: `producer returned ${pf.last_draft_status}`,
        revise_cap: reviseCapForAngle(angle),
        ...(angle < NEG1_PIVOT_BUDGET - 1 ? { next_angle: angle + 1 } : {}),
      });
    }

    // Resume-aware producer-first guard. If we are entering -0.5 in
    // revise/pivot mode with no fresh draft handoff, drive the producer once
    // before reviewing — otherwise we would either (a) burn a Codex call
    // re-reviewing the already-judged proposal, or (b) push an iteration row
    // with version=0 (cross-stage pivot path, where intervention_routing
    // wipes last_reviewer_verdict and resets current_version=0 expecting
    // stageNeg1_2 to bump it before the next review).
    const hasFreshDraft =
      typeof pf.last_draft_handoff === "string" && pf.last_draft_handoff.length > 0;
    if (!hasFreshDraft && (mode === "revise" || mode === "pivot")) {
      await runStageNeg1_2({ ctx: args.ctx, state: args.state, deps: args.deps });
      // The next operation is another remote reviewer call. Persist the newly
      // authored version/handoff first so a reviewer crash resumes from review
      // instead of silently re-running and overwriting the proposer output.
      await persistState();
      continue;
    }

    let draftJson: Record<string, unknown> = {};
    if (typeof pf.last_draft_handoff === "string" && pf.last_draft_handoff.length > 0) {
      try {
        // Three-layer defense: the handoff is a persisted model stdout receipt and
        // can carry under-escaped TeX (comparator claims, checklist lines).
        draftJson = parseRepairedModelJson(
          pf.last_draft_handoff,
          "stage -0.5 producer handoff",
        ) as Record<string, unknown>;
      } catch (err) {
        // An unparseable handoff silently blanks the drafter context (comparator
        // table, upgrade_mode, checklist), which the reviewer then reads as genuine
        // omissions — spurious findings, each costing a revise round.
        console.warn(
          `[stage -0.5] producer handoff is unparseable (${err instanceof Error ? err.message : String(err)}); ` +
            `the reviewer will see EMPTY drafter context and may report spurious omissions this round.`,
        );
        draftJson = {};
      }
    }
    // Resolve this per attempt: a proto core can first appear during the loop.
    // In single-artifact mode every reviewer-facing path must name the core,
    // never a possibly stale legacy proposal.tex.
    const proposalReviewPath = currentProposalArtifact();
    await renderNeg1ReviewOutputTemplate({
      ctx: args.ctx,
      targetPath: paths.proposalReviewOutputJson,
      proposalPath: proposalReviewPath,
    });
    const reviewOut = await runNeg1Review({
      ctx: args.ctx,
      deps: args.deps,
      promptText: await resolveReviewPrompt(),
      proposalPath: proposalReviewPath,
      reviewOutputJsonPath: paths.proposalReviewOutputJson,
      draftJson,
      noveltyTarget: pf.novelty_target,
      stage0_5RejectionBlock,
      methodScopedNoveltyBlock,
    });
    // A reviewer whose output could not be parsed has NOT reviewed anything. Halt on
    // it rather than letting the `?? "REVISE"` default below burn a revise round (cap
    // 5) plus a full producer re-author on a parsing artifact.
    if (reviewOut.parseError !== null) {
      await persistState();
      return {
        stage: "-0.5",
        status: "checkpoint",
        advance: false,
        message:
          `Stage -0.5 reviewer output was UNPARSEABLE on angle ${pf.current_angle_index ?? 0} ` +
          `v${pf.current_version ?? 0} (parseError=${reviewOut.parseError}). This is a PLUMBING fault, not a ` +
          `review verdict — no revise round was consumed and the proposal is untouched. Inspect the reviewer ` +
          `transcript in logs/stages/, then --resume to re-run the same review.`,
      };
    }
    pf.last_reviewer_verdict = reviewOut.raw;
    // Reviewer returned successfully — its rendered output template is now dead
    // scratch (the verdict lives in reviewOut.raw / reviews.jsonl). Drop it;
    // it is re-rendered on the next revise/pivot iteration.
    await cleanupRenderedTemplate(paths.proposalReviewOutputJson);
    // Same fail-loud contract as the parse-error checkpoint above, one layer deeper:
    // parseable JSON whose `verdict` is missing or junk is a SHAPE fault, not a review.
    // The old `?? "REVISE"` default burned a revise round + producer re-author on it.
    const normalizedVerdict = normalizeReviewVerdict(reviewOut.verdict);
    if (normalizedVerdict === null) {
      await persistState();
      return {
        stage: "-0.5",
        status: "checkpoint",
        advance: false,
        message:
          `Stage -0.5 reviewer JSON parsed but carried no usable verdict on angle ${pf.current_angle_index ?? 0} ` +
          `v${pf.current_version ?? 0} (verdict=${JSON.stringify(reviewOut.verdict)}; expected ACCEPT/REJECT/REVISE). ` +
          `This is a PLUMBING fault, not a review verdict — no revise round was consumed and the proposal is ` +
          `untouched. Inspect the reviewer transcript in logs/stages/, then --resume to re-run the same review.`,
      };
    }
    let verdict: string = normalizedVerdict;
    // Tier-saturation extras: tier_at_proposal + a boolean "clean_substance"
    // = no N-* flags AND no C-* flags (structure flags are OK). These feed
    // the auto-promote rule below; harmless when absent.
    const reviewJson = reviewOut.json as Record<string, unknown>;
    const tierStr =
      typeof reviewJson.publishability_tier === "string"
        ? reviewJson.publishability_tier
        : undefined;
    const novelArr = Array.isArray(reviewJson.novelty_flags) ? reviewJson.novelty_flags : [];
    const soundArr = Array.isArray(reviewJson.soundness_flags) ? reviewJson.soundness_flags : [];
    const cleanSubstance = novelArr.length === 0 && soundArr.length === 0;
    // Persist accepted scope caveats so the downstream Stage 0.5 derivation
    // reviewer treats them as settled (does not relitigate "assumed not proved").
    // Validate the shape (the field rides outside the zod ReviewResult via
    // .passthrough()); a mis-keyed object would otherwise render as
    // `undefined → undefined` in the D0.5 injection and silently un-suppress
    // relitigation. Keep only well-formed entries; log if any were dropped.
    if (Array.isArray(reviewJson.accepted_scope_caveats)) {
      const raw = reviewJson.accepted_scope_caveats;
      const valid = raw.filter(
        (c): c is { label: string; caveat: string; bound_claim: string } =>
          !!c &&
          typeof c === "object" &&
          typeof (c as { label?: unknown }).label === "string" &&
          typeof (c as { caveat?: unknown }).caveat === "string" &&
          typeof (c as { bound_claim?: unknown }).bound_claim === "string",
      );
      if (valid.length < raw.length) {
        console.warn(
          `[causalsmith] Stage -0.5: dropped ${raw.length - valid.length} malformed accepted_scope_caveats entry(ies) (need string label/caveat/bound_claim).`,
        );
      }
      pf.accepted_scope_caveats = valid;
    }
    iterations.push({ angle, version, mode, verdict, tier: tierStr, clean_substance: cleanSubstance });

    // Stage -0.5 tier-saturation auto-promote (safe here because Stage -0.5
    // never verifies proofs — Conjectures are intentionally open and math
    // correctness is checked downstream at Stage 0.5). If the last 3
    // consecutive REVISEs on the CURRENT angle held at-or-above the run's
    // novelty floor tier with empty N-* and C-* flag arrays (only S-* /
    // prose-level flags left), promote to ACCEPT. Prevents the cap-bound trap
    // observed in Runs 4, 5, 7 where well-posedness nits dominate at the cap.
    // Gated on the run's floor (not the literal "flagship") so nonflagship
    // targets can converge to ACCEPT the same way.
    // NOT replicated at Stage 0.5 — there C-wellposed flags can be
    // load-bearing and must escalate to a user checkpoint instead.
    if (
      decideTierSaturationPromote({
        verdict,
        tier: tierStr,
        cleanSubstance,
        iterations,
        angle,
        noveltyTarget,
      })
    ) {
      verdict = "ACCEPT";
      // Patch the last iteration entry to record the auto-promote reason.
      iterations[iterations.length - 1] = {
        ...iterations[iterations.length - 1],
        verdict,
      };
      pf.last_reviewer_verdict =
        (pf.last_reviewer_verdict ?? "") +
        `\n[orchestrator note] Stage -0.5 tier-saturation auto-promote: 3 consecutive REVISE at-or-above the ${noveltyTarget} novelty floor with empty N-* and C-* flags; auto-set ACCEPT.`;
    }

    await logNeg1Review({
      ctx: args.ctx,
      angle,
      version,
      verdict,
      json: reviewOut.json,
    });
    pf.iterations = iterations;
    await persistState();

    if (verdict === "ACCEPT") {
      pf.iterations = iterations;
      pf.archived_proposals = archivedProposals;
      pf.exhausted_angles = exhaustedAngles;
      pf.final_verdict = "ACCEPT";
      pf.pivot_budget_used = angle;
      // Recomputed at accept time (was a stage-entry snapshot): a proto core that
      // appeared mid-loop must not be recorded as a legacy .tex accept path.
      const acceptedProposalPath = currentProposalArtifact();
      pf.proposal_path = acceptedProposalPath; // why: single-artifact proto-core runs must not resume against the stale legacy .tex path.
      await persistState();
      return {
        stage: "-0.5",
        status: "completed",
        message: `Stage -0.5 ACCEPT on angle ${angle} v${version}`,
        artifacts: [acceptedProposalPath],
      };
    }

    if (verdict === "REJECT") {
      // REJECT-escape dispatcher (May 2026). Before pivoting to a new angle,
      // give the producer a single rescue attempt on the current angle when the
      // reviewer's flag pattern points at a localized failure mode:
      //   - kernel-replace: kernel claim is structurally a definitional unfold
      //     / unbounded epsilon / unnamed focal object; swap the kernel but
      //     keep the angle's seeds + literature anchor.
      //   - draft-rebuild: kernel is OK but the draft execution is broken
      //     (witness self-refuting, exhibit unhydrated, arithmetic wrong);
      //     rewrite the draft on top of the same kernel.
      // Each escape fires at most once per angle. Kernel-replace takes priority
      // over draft-rebuild when both flag patterns are present. If the angle
      // already burned the relevant escape, fall through to the pivot below.
      const escapeDispatched = await dispatchRejectEscape({
        angle,
        reviewJson: reviewOut.json as Record<string, unknown>,
        pf,
        iterations,
        ctx: args.ctx,
        deps: args.deps,
        state: args.state,
        persistState,
      });
      if (escapeDispatched) continue;
      return checkpointAngle({
        kind: "angle-boundary",
        angle,
        version,
        verdict,
        reason: "reviewer REJECT after same-angle rescue paths were unavailable or exhausted",
        revise_cap: reviseCapForAngle(angle),
        ...(angle < NEG1_PIVOT_BUDGET - 1 ? { next_angle: angle + 1 } : {}),
      });
    }

    // REVISE — tier-gated early-stop vs cap vs another round; see
    // decideReviseOutcome for the rationale (below-floor kill preserves the
    // full revise runway for angles whose problem is substance, not ceiling).
    const reviseCap = reviseCapForAngle(angle);
    const reviseOutcome = decideReviseOutcome({
      version,
      iterations,
      angle,
      noveltyTarget,
      reviseCap,
      killVersion: NEG1_NONFLAGSHIP_KILL_VERSION,
    });
    if (reviseOutcome !== "revise") {
      iterations.push({ angle, version, mode: "revise", verdict: reviseOutcome });
      pf.iterations = iterations;
      await persistState();
      return checkpointAngle({
        kind: "angle-boundary",
        angle,
        version,
        verdict: reviseOutcome,
        reason:
          reviseOutcome === "below-floor-kill"
            ? `angle never reached the ${noveltyTarget} novelty floor by v${version}`
            : `revision cap ${reviseCap} exhausted after reviewer REVISE`,
        revise_cap: reviseCap,
        ...(angle < NEG1_PIVOT_BUDGET - 1 ? { next_angle: angle + 1 } : {}),
      });
    }
    pf.current_mode = "revise";
    pf.iterations = iterations;
    pf.archived_proposals = archivedProposals;
    pf.exhausted_angles = exhaustedAngles;
    return checkpointAngle({
      kind: "revise",
      angle,
      version,
      verdict,
      reason: "reviewer requested revision; D-orchestrator may inject a directive before continuing",
      revise_cap: reviseCap,
    });
  }

  pf.iterations = iterations;
  pf.archived_proposals = archivedProposals;
  pf.exhausted_angles = exhaustedAngles;
  pf.final_verdict = "NO-PASS";
  pf.pivot_budget_used = NEG1_PIVOT_BUDGET - 1;
  pf.proposal_path = currentProposalArtifact();
  await persistState();
  // advance:false keeps stage_completed at "-1.2" so `--resume` re-enters -0.5
  // (the reviewer-loop) once the user has reset/extended the iteration cursor
  // in state.proposed_from. Without this, nextStage would jump to "0".
  return {
    stage: "-0.5",
    status: "checkpoint",
    advance: false,
    message: `Stage -0.5 NO-PASS — pivot budget exhausted (${NEG1_PIVOT_BUDGET} angles tried)`,
    artifacts: [currentProposalArtifact(), ...archivedProposals],
  };
}

/**
 * Render the Stage -0.5 reviewer's stdout-JSON template into the qid folder.
 * Pre-fills `proposal_path_read` with the one artifact the reviewer will read
 * (typed core in single-artifact mode, `.tex` in legacy mode) and lets the agent
 * fill the verdict and finding slots. Re-rendered on
 * every invocation so a fresh template is always next to the proposal.
 */
async function renderNeg1ReviewOutputTemplate(args: {
  ctx: PipelineContext;
  targetPath: string;
  proposalPath: string;
}): Promise<void> {
  await renderRefereeTemplate({
    ctx: args.ctx,
    templateName: "stage_neg1_review_output_template.json",
    targetPath: args.targetPath,
    prefill: (tmpl) => {
      tmpl.proposal_path_read = args.proposalPath;
    },
  });
}

const SOURCE_RECEIPT_REQUIRED_CODES = new Set([
  "N-mischar",
  "N-pub",
  "C-assumption-nonstandard",
]);

/** Fail closed when a source-dependent adverse finding has no inspectable
 * primary-source receipt. A review that cannot show its source must not burn a
 * proposal revision or trigger a mathematical rewrite. */
export function sourceReceiptValidationError(json: Record<string, unknown>): string | null {
  const required = new Set<string>();
  for (const key of ["novelty_flags", "soundness_flags"] as const) {
    const flags = Array.isArray(json[key]) ? json[key] : [];
    for (const flag of flags) {
      if (!flag || typeof flag !== "object") continue;
      const code = (flag as { code?: unknown }).code;
      if (typeof code === "string" && SOURCE_RECEIPT_REQUIRED_CODES.has(code)) required.add(code);
    }
  }
  if (required.size === 0) return null;

  const covered = new Set<string>();
  const receipts = Array.isArray(json.source_verification_receipts)
    ? json.source_verification_receipts
    : [];
  for (const receipt of receipts) {
    if (!receipt || typeof receipt !== "object") continue;
    const row = receipt as Record<string, unknown>;
    const wellFormed =
      typeof row.bibkey === "string" && row.bibkey.trim().length > 0 &&
      typeof row.source_url === "string" && /^https?:\/\//.test(row.source_url) &&
      typeof row.version === "string" && row.version.trim().length > 0 &&
      typeof row.locator === "string" && row.locator.trim().length > 0 &&
      typeof row.verified_claim === "string" && row.verified_claim.trim().length > 0;
    if (!wellFormed || !Array.isArray(row.supports_flag_codes)) continue;
    for (const code of row.supports_flag_codes) {
      if (typeof code === "string") covered.add(code);
    }
  }
  const missing = [...required].filter((code) => !covered.has(code));
  return missing.length > 0
    ? `source-dependent reviewer flag(s) lack a complete primary-source receipt: ${missing.join(", ")}`
    : null;
}

export async function runNeg1Review(args: {
  ctx: PipelineContext;
  deps: StageDeps;
  promptText: string;
  proposalPath: string;
  reviewOutputJsonPath: string;
  draftJson: Record<string, unknown>;
  noveltyTarget: NoveltyTarget;
  stage0_5RejectionBlock?: string;
  methodScopedNoveltyBlock?: string;
}): Promise<{ raw: string; verdict: string | null; json: Record<string, unknown>; parseError: string | null }> {
  // Fail-closed on the proposal source. `readIfExists` returns "" for a missing file,
  // which would send the reviewer a prompt with an empty proposal body and let it
  // render a verdict on nothing — the same class of fault that fabricated a novelty
  // tier at D0.5.G.
  if (!existsSync(args.proposalPath)) {
    throw new Error(
      `D-0.5 cannot review: the proposal is absent at ${args.proposalPath}. This is a plumbing failure, ` +
        `not a review verdict — re-run the D-1.2 producer before the review boundary.`,
    );
  }
  const proposalSrc = await readIfExists(args.proposalPath);
  if (proposalSrc.trim().length === 0) {
    throw new Error(`D-0.5 cannot review: the proposal at ${args.proposalPath} is empty (0 non-whitespace chars).`);
  }
  // Proto path: the SC6 comparator table lives in `proto_core.json` as
  // `comparator_promises`; the proto producer's stdout handoff only carries
  // {status, message, artifacts, literature_checklist} (see
  // stage_neg1_2_proto_core.ts), so buildDrafterHandoff would always render the
  // table as <MISSING> and the reviewer would fire N-comparator-drift every
  // round. Surface the core's comparator_promises into the handoff object.
  const draftForHandoff: Record<string, unknown> = { ...args.draftJson };
  if (
    draftForHandoff.comparator_promise_table == null &&
    draftForHandoff.comparator_promises == null
  ) {
    try {
      const coreRaw = await readIfExists(protoCoreJsonPath(args.ctx));
      if (coreRaw) {
        // Three-layer defense: comparator claims are verbatim TeX-bearing
        // summaries from a (possibly agent-raw / legacy) proto core.
        const core = parseRepairedModelJson(
          coreRaw,
          protoCoreJsonPath(args.ctx),
        ) as Record<string, unknown>;
        // The producer may store the table under either name (canonical proto
        // field `comparator_promises`, or `comparator_promise_table` when it
        // self-aligns to the reviewer's wording). Accept either.
        const coreTable =
          core.comparator_promise_table ?? core.comparator_promises;
        if (Array.isArray(coreTable) && coreTable.length > 0) {
          draftForHandoff.comparator_promise_table = coreTable;
        }
      }
    } catch (err) {
      // Do NOT fail silently. The comment 25 lines above explains that a missing
      // comparator table makes the reviewer fire N-comparator-drift EVERY round —
      // i.e. this catch converts a proto_core read/parse error into a recurring
      // fabricated review finding, and each one costs a revise round.
      console.warn(
        `[stage -0.5] comparator table unavailable from proto_core (${err instanceof Error ? err.message : String(err)}); ` +
          `the handoff will render <MISSING> and the reviewer is LIKELY to fire a spurious N-comparator-drift. ` +
          `Treat any comparator finding this round as suspect.`,
      );
    }
  }
  const handoff = buildDrafterHandoff(draftForHandoff);
  const upgradeMode = args.draftJson.upgrade_mode === true;
  const upgradeDirective = upgradeMode
    ? await readPrompt(args.ctx, "stage_neg1_review_upgrade_directive.txt")
    : "";
  const parts: string[] = [args.promptText, ""];
  if (upgradeDirective) {
    parts.push(upgradeDirective, "");
  }
  // Single-artifact retarget: when a proto_core exists, use the core rubric and
  // inline the authoritative artifact. Empty (no-op) under the legacy monolithic
  // `.tex` path.
  const protoCoreBlock = await buildProtoCoreReviewBlock(args.ctx);
  if (protoCoreBlock) {
    parts.push(protoCoreBlock, "");
  }
  parts.push(
    "=== ORCHESTRATOR-PROVIDED INPUTS ===",
    `proposal_path: ${args.proposalPath}`,
    `Output JSON template (READ THIS, fill TODOs, emit on stdout): ${args.reviewOutputJsonPath}`,
    `novelty_target: ${args.noveltyTarget}`,
    "Return ONLY the JSON object obtained by filling the output template.",
    "",
    tierFloorBlock(args.noveltyTarget),
    "=== DRAFTER HANDOFF (load-bearing — this is the named literature checklist the reviewer prompt expects) ===",
    handoff,
    "=== END DRAFTER HANDOFF ===",
  );
  // Single-artifact path: the core is already inlined above (protoCoreBlock) and
  // the .tex is just its deterministic render — do not double-feed it. Legacy
  // monolithic path: inline the proposal .tex (the artifact under review).
  if (!protoCoreBlock) {
    parts.push("", "=== PROPOSAL .TEX (verbatim) ===", proposalSrc, "=== END PROPOSAL .TEX ===");
  }
  if (args.stage0_5RejectionBlock && args.stage0_5RejectionBlock.length > 0) {
    parts.push("", args.stage0_5RejectionBlock);
  }
  if (args.methodScopedNoveltyBlock && args.methodScopedNoveltyBlock.length > 0) {
    parts.push("", args.methodScopedNoveltyBlock);
  }
  const prompt = parts.join("\n");
  // Referee harness: dispatch + parse + scaffolding-strip + verdict extraction.
  // A parse failure surfaces as parseError and must never masquerade as a
  // review verdict (the caller's `?? "REVISE"` default would otherwise turn it
  // into a PHANTOM REVISE consuming one of only five revise rounds). The
  // source-receipt validation runs as the harness's validate hook.
  const result = await runReferee({
    ctx: args.ctx,
    deps: args.deps,
    stage: "-0.5",
    label: "D-0.5 proposal review",
    prompt,
    promptSources: [
      "stage_neg1_review(_core).txt + stage_flagship_rubric.txt",
      args.proposalPath,
    ],
    model: MODEL_PLAN.stageNeg0_5_review.model,
    reasoningEffort: MODEL_PLAN.stageNeg0_5_review.effort,
    inactivityTimeoutMs: 40 * 60 * 1000,
    validate: sourceReceiptValidationError,
  });
  return { raw: result.raw, verdict: result.verdict, json: result.json, parseError: result.parseError };
}

/**
 * Build the Stage 0.5 rejection context block injected into Stage -1.2 / -0.5
 * prompts on resume after a `rewound_from_stage0` event. Returns "" when no
 * such rewind is on file (i.e. cold-start or fresh post-pivot Stage -0.5
 * entries should see no block).
 *
 * Contents (when present): verbatim rewind reason from the intervention judge,
 * the auto-granted Bucket A assumption(s) recorded against the rewind, and the
 * most recent `stage_0.5_to_0_attempt*.json` review so the producer/reviewer
 * can decide whether the kernel novelty critique requires a real revise/pivot
 * or whether the new Bucket A patch already addressed the gap.
 */
export async function buildStage0_5RejectionContext(args: {
  ctx: PipelineContext;
  state: StateJson;
}): Promise<string> {
  const rewind = args.state.flags.rewound_from_stage0;
  if (!rewind) return "";
  const correction = args.state.flags.statement_correction_directive;
  const approved = args.state.added_assumptions.filter((a) => a.user_approved === true);
  let latestReview = "";
  try {
    const reviewsDir = resolveInDir(formalizationDir(args.ctx.repoRoot, args.ctx.qid), "reviews", [
      `${args.ctx.qid}_${args.ctx.specialization}_reviews`,
    ]);
    const names = await readdir(reviewsDir).catch(() => [] as string[]);
    const candidates = names
      .filter((n) => n.startsWith("stage_0.5_to_0_attempt") && n.endsWith(".json"))
      .sort();
    const latest = candidates[candidates.length - 1];
    if (latest) {
      latestReview = await readFile(path.join(reviewsDir, latest), "utf8").catch(() => "");
    }
  } catch {
    // ignore — block still surfaces the rewind reason even without the JSON.
  }
  if (correction) {
    // Statement-correction rewind: the headline OBJECT was over-precise (e.g.
    // claimed pointwise extremum attainment / exactness where the standard true
    // statement is the closure / inf-sup / a.e. form). This is NOT a novelty
    // failure and NOT a regime restriction — do not pivot, do not demote to a
    // conjecture, do not add an assumption. Restate the SAME object in the
    // corrected standard form below; it then holds unconditionally.
    const cLines: string[] = [
      "=== STAGE 0.5 STATEMENT-CORRECTION DIRECTIVE (load-bearing — this OVERRIDES the generic revise/pivot framing) ===",
      "Stage 0.5 found the derivation could not close ONLY because the headline",
      "statement is OVER-PRECISE relative to the standard true form of the SAME",
      "focal object (the intervention judge classified this as an over-precision",
      "artifact, NOT a regime-defining gap). The fix is a faithful RESTATEMENT,",
      "not a revise/pivot/reject and not a theorem-split:",
      "",
      "- Restate the affected theorem's focal object in the corrected standard",
      "  form given below. Keep the SAME object and the SAME §3/§4 novelty pitch.",
      "- Do NOT demote the claim to a Conjecture, do NOT add a new Assumption,",
      "  and do NOT pivot to a different angle. The corrected statement holds",
      "  UNCONDITIONALLY under the existing §6/§7 assumptions.",
      "- If — and only if — you find the corrected standard form is already",
      "  established by a named §4 comparator (novelty collapses), THEN this is not",
      "  a correction: emit REJECT so the loop pivots. Otherwise apply the",
      "  restatement and keep the contribution.",
      "",
      "Corrected statement (verbatim from the intervention judge):",
      correction,
      "",
    ];
    if (latestReview) {
      cLines.push(
        "Most recent Stage 0.5 review (verbatim JSON — for the precise step that",
        "failed; the corrected statement above is the intended fix):",
        latestReview,
        "",
      );
    }
    cLines.push("=== END STAGE 0.5 STATEMENT-CORRECTION DIRECTIVE ===");
    return cLines.join("\n");
  }
  const lines: string[] = [
    "=== STAGE 0.5 REJECTION CONTEXT (load-bearing — read before any revise/accept/pivot decision) ===",
    "This proposal previously passed Stage -0.5 and reached Stage 0 derivation,",
    "but Stage 0.5 (post-derivation novelty/structure/correctness boundary review)",
    "routed it back to the proposal loop because the derivation did not clear the",
    "novelty floor or otherwise failed at the kernel level. Treat this as a",
    "directive that the *prior accept may have been over-optimistic*: revise the",
    "kernel, pivot to a different surviving seed, or — if the angle is provably",
    "blocked — emit REJECT so the next loop pivots.",
    "",
    "Stage 0.5 rewind directive (verbatim from the intervention judge):",
    rewind,
    "",
  ];
  if (approved.length > 0) {
    lines.push(
      "Auto-granted Bucket A assumption(s) — already added to §7 of the .tex.",
      "These patch a specific local proof step flagged by the Stage 0.5 reviewer.",
      "They do NOT by themselves answer the kernel-novelty critique unless that",
      "critique was a pure caveat-class assumption gap:",
    );
    for (const a of approved) {
      lines.push(`- [${a.label}] ${a.statement}`);
      if (a.source) lines.push(`  source: ${a.source}`);
    }
    lines.push("");
  }
  if (latestReview) {
    lines.push(
      "Most recent Stage 0.5 review (verbatim JSON — the per-item structure/",
      "novelty/correctness verdicts and the verbatim_critique field are the",
      "authoritative reading of what failed):",
      latestReview,
      "",
    );
  }
  lines.push("=== END STAGE 0.5 REJECTION CONTEXT ===");
  return lines.join("\n");
}
