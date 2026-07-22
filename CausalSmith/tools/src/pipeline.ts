import { existsSync } from "node:fs";
import { readdir, readFile } from "node:fs/promises";
import path from "node:path";
import { performance } from "node:perf_hooks";
import { formatStageLabel, STAGE_ORDER } from "./constants.js";
import { CAP_GATES, clearCapGate } from "./cap_gates.js";
import { appendPipelineLog } from "./log.js";
import { checkpointGuidance } from "./checkpoint_playbook.js";
import { statePath } from "./paths.js";
import { createInitialState, loadState, saveState } from "./state.js";
import { dryRunStageHandler, liveStageHandler, type StageHandler } from "./pipeline_stages.js";
import { PaperHasNoCompletedTheorems } from "./shared/close_open_question.js";
import { withRunHeartbeat } from "./shared/run_heartbeat.js";
import { loadWorkingState, readEscalationLog } from "./discovery/stages/d0_working.js";
import type { PipelineContext, Stage, StateJson } from "./types.js";

export function nextStage(stage: Stage): Stage | null {
  const index = STAGE_ORDER.indexOf(stage);
  if (index === -1) throw new Error(`Unknown stage: ${formatStageLabel(stage)}`);
  return STAGE_ORDER[index + 1] ?? null;
}

/** A D0 directive is a durable request to rerun D0, not merely context for the
 * next stage that plain resume would otherwise choose. This guard prevents a
 * resume from D0/D0.5 from repeatedly reviewing stale core/prose while queued
 * corrections remain beyond the working cursor. */
async function hasPendingD0Directive(ctx: PipelineContext): Promise<boolean> {
  const [working, entries] = await Promise.all([
    loadWorkingState(ctx),
    readEscalationLog(ctx),
  ]);
  // Only an ACTIONABLE directive should pull a resume back to D0. A provenance-only
  // entry (a paid verdict recorded so a resume does not re-buy it) carries no targets,
  // so routing on it would re-enter D0 and force the whole paper open.
  const unconsumed = entries.slice(working?.escalation_entries_consumed ?? 0);
  return unconsumed.some((entry) => entry.provenance_only !== true);
}

export interface RunPipelineOptions {
  startStage?: Stage;
  stopAfterStage?: Stage;
  /**
   * Resume-time cap-gate clears (CLI: `--clear-gate <flag>`, repeatable). Applied
   * after state load, only on `--resume`, so the orchestrator clears a resume-blocking
   * flag through the CLI instead of hand-editing `state.json`. Each name must be a
   * `CAP_GATES` flag; an unknown name throws.
   */
  clearGates?: string[];
}

/**
 * Reconciles per-theorem status in a paper-scoped run. Returns counts of
 * theorems by status. Paper-wide or legacy single-theorem runs return all zeros.
 *
 * Does not halt the pipeline — stuck/failed entries are allowed to flow through
 * subsequent stages and are filtered at Stage 5 (banking) and study-pipeline S5
 * (reconciliation).
 */
export function reconcilePaperStatus(state: StateJson): {
  completed: number;
  in_progress: number;
  pending: number;
  stuck: number;
  failed: number;
} {
  const counts = { completed: 0, in_progress: 0, pending: 0, stuck: 0, failed: 0 };
  if (!state.theorems || state.theorems.length === 0) return counts;
  for (const entry of state.theorems) {
    counts[entry.status] += 1;
  }
  return counts;
}

export async function initializeOrLoadState(ctx: PipelineContext): Promise<StateJson> {
  // Per-qid concurrency is enforced by `withRunHeartbeat` in `runPipeline`.
  // This helper only handles state-file lifecycle.
  const currentStatePath = statePath(ctx.repoRoot, ctx.qid, ctx.specialization);

  if (ctx.resume) return loadState(ctx.repoRoot, ctx.qid, ctx.specialization);

  if (existsSync(currentStatePath)) {
    throw new Error(`state already exists for ${ctx.qid}_${ctx.specialization}; use --resume`);
  }

  const state = createInitialState(ctx.qid);
  // Phase 3: persist the --from-question flag on the run's state so Stage -1.2,
  // Stage -0.5, and the post-Stage-5 close hook can see it without re-parsing
  // the CLI args. `method_id` is filled in lazily by the Stage -1.2 driver
  // once the bundle is resolved.
  if (ctx.fromQuestionOqId) {
    state.from_question_oq_id = ctx.fromQuestionOqId;
  }
  await saveState(ctx.repoRoot, ctx.qid, ctx.specialization, state);
  await appendPipelineLog(ctx, {
    stage: "init",
    status: "created",
    duration_ms: 0,
    message: `created state for ${ctx.qid}_${ctx.specialization}`,
  });
  return state;
}

export async function runPipeline(
  ctx: PipelineContext,
  handler: StageHandler = ctx.dryRun ? dryRunStageHandler : liveStageHandler,
  options: RunPipelineOptions = {},
): Promise<StateJson> {
  return withRunHeartbeat(ctx.repoRoot, ctx.qid, ctx.specialization, () =>
    runPipelineInner(ctx, handler, options),
  );
}

async function runPipelineInner(
  ctx: PipelineContext,
  handler: StageHandler,
  options: RunPipelineOptions,
): Promise<StateJson> {
  // Resolve and validate upgrade lineage before creating any run state. The
  // target may be any novelty tier, but it must be STRICTLY above the parent's
  // achieved banked tier. Loading here also makes the resolved bank bucket
  // available to D-1.1 instead of carrying the CLI's placeholder `accepted`.
  if (ctx.upgradeFrom) {
    const { assertUpgradeNoveltyTarget, loadParentEntry } = await import("./upgrade.js");
    const parent = await loadParentEntry(ctx.repoRoot, {
      parent_qid: ctx.upgradeFrom.parent_qid,
      parent_spec: ctx.upgradeFrom.parent_spec,
    });
    assertUpgradeNoveltyTarget(ctx.noveltyTarget, parent);
    ctx.upgradeFrom.parent_tier = parent.tier;
    if (!ctx.proposeTopic) {
      (ctx as { proposeTopic?: string }).proposeTopic = parent.topic;
    }
  }

  const state = await initializeOrLoadState(ctx);

  // Persist `--auto` onto state so a run stays autonomous across resumes even if
  // a later `--resume` omits the flag. Latching: `--auto` turns it on; it is
  // never auto-cleared here (start a fresh run to drop autonomy).
  if (ctx.auto) state.auto_mode = true;

  // Resume-time cap-gate clears (`--clear-gate <flag>`). Apply BEFORE the resume
  // gate below, so clearing a blocking flag opens the gate in the same command.
  // Only on `--resume` (a cold start has no persisted flags to clear); an unknown
  // gate name throws out of `clearCapGate`. This replaces the old "hand-edit
  // state.flags then --resume" instruction — the flip is atomic + schema-valid.
  if (ctx.resume && options.clearGates?.length) {
    for (const name of options.clearGates) {
      clearCapGate(state.flags, name);
      console.warn(`[causalsmith] cleared cap gate flags.${name} before resume.`);
    }
  }

  // Resume without --novelty: recover the original novelty_target from
  // state.proposed_from so downstream tier-floor enforcement (Stage -0.5
  // and Stage 0.5 reviewers) sees the same floor it had on cold-start.
  // Without this, a `--resume` of a flagship cold-start lost the floor
  // and reviewers happily ACCEPT'd at subfield/field tiers.
  if (!ctx.noveltyTarget && state.proposed_from?.novelty_target) {
    (ctx as { noveltyTarget?: PipelineContext["noveltyTarget"] }).noveltyTarget =
      state.proposed_from.novelty_target;
  }

  // A deliberate D-1.1 re-entry means the operator wants a fresh literature
  // scout result (typically after fixing the scout prompt or changing its
  // routing policy). `--from-stage` already overrides the stage pointer, but
  // Stage -1.1 also has a persisted `state.gaps` cache; leaving it populated
  // makes the handler immediately report "already complete" and feeds the
  // stale gaps into D-1.2. Invalidate the whole proposal-side derivative state
  // here so the fresh scout is followed by a genuinely cold D-1.2 draft.
  let resetProposalForDNeg11 = false;
  if (ctx.resume && options.startStage === "-1.1") {
    const persistedProposal = state.proposed_from;
    const topic = ctx.proposeTopic ?? persistedProposal?.topic;
    if (topic) {
      // A normal resume does not repeat `--propose <topic>`. Rehydrate the
      // scout input (and upgrade lineage) before deleting the derivative
      // proposal cache, otherwise explicit D-1.1 re-entry silently skips.
      if (!ctx.proposeTopic) {
        (ctx as { proposeTopic?: string }).proposeTopic = topic;
      }
      if (!ctx.upgradeFrom && persistedProposal?.upgrade_from) {
        (ctx as { upgradeFrom?: PipelineContext["upgradeFrom"] }).upgradeFrom =
          persistedProposal.upgrade_from;
      }
      resetProposalForDNeg11 = true;
    }
  }

  // Protect an authored-but-unreviewed proposal from accidental overwrite.
  // At this boundary plain --resume advances to D-0.5 and reviews the existing
  // draft; --from-stage D-1.2 explicitly reruns the producer. The latter is
  // almost always an orchestration mistake after SIGINT, and previously
  // silently replaced v1 with an unreviewed cold-start v2.
  if (ctx.resume && options.startStage === "-1.2") {
    const pf = state.proposed_from;
    const angle = pf?.current_angle_index ?? 0;
    const version = pf?.current_version ?? 0;
    const currentDraftReviewed = (pf?.iterations ?? []).some(
      (it) => it.angle === angle && it.version === version,
    );
    if (version > 0 && pf?.last_draft_status === "completed" && !pf.angle_checkpoint && !currentDraftReviewed) {
      throw new Error(
        `refusing --from-stage D-1.2: angle ${angle} v${version} is authored but unreviewed; ` +
        `use plain --resume to review it at D-0.5, or run reset_proposal_cursor.ts ` +
        `<qid> <spec> --angle ${angle} --fresh-angle before intentionally discarding it`,
      );
    }
  }

  const resumeGate = await resolveResumeGates(ctx, state);
  if (!resumeGate.open) {
    await appendPipelineLog(ctx, {
      stage: "resume",
      status: "blocked",
      duration_ms: 0,
      message: resumeGate.message,
    });
    await saveState(ctx.repoRoot, ctx.qid, ctx.specialization, state);
    return state;
  }

  // Commit resume preflight mutations before dispatching another stage. A live
  // handler may crash after making external calls; if `--auto`, `--clear-gate`,
  // the D-1.1 cache invalidation, or a satisfied missing-architecture gate only
  // lived in memory until that handler returned, the next resume resurrected
  // stale state and repeated already-authorized work.
  await saveState(ctx.repoRoot, ctx.qid, ctx.specialization, state);

  // Invalidate the D-1.1 derivatives only after the durable preflight snapshot.
  // If the scout process crashes, the old proposal/topic remains resumable on
  // disk; once the handler returns, the normal post-stage save commits this
  // invalidation together with the new scout result.
  if (resetProposalForDNeg11) {
    delete state.gaps;
    delete state.proposed_from;
    console.warn("[causalsmith] D-1.1 re-entry: cleared cached gaps and proposal state.");
  }

  // An explicit `--from-stage` re-entry OVERRIDES the "already complete" short-circuit: the operator
  // is deliberately re-running a stage on a finished run (e.g. to re-review after a reviewer fix), so
  // fall through to the stage dispatch below instead of returning "already complete".
  if (state.stage_completed === "5" && !options.startStage) {
    // Repair path: a `--from-question` run that finished Stage 5 before the
    // close hook ran (or whose hook failed) still has its OQ `in_progress`.
    // Re-fire the hook here; it is gated on `closed_oq` so a successfully
    // closed run is a no-op. Paper-scoped (no-OQ) minting is NOT retried here
    // to avoid double-minting BankedTheorems.
    if (state.from_question_oq_id && !state.closed_oq) {
      await runPostStage5CloseHook(ctx, state);
      await saveState(ctx.repoRoot, ctx.qid, ctx.specialization, state);
    }
    await appendPipelineLog(ctx, {
      stage: "resume",
      status: "complete",
      duration_ms: 0,
      message: "Pipeline already complete",
    });
    return state;
  }

  // Cold-start ordering for propose mode: Stage -1.1 (literature scout) runs
  // FIRST to mine open problems from web + prior proposals, then Stage -1.2
  // (the producer) consumes the resulting `gaps.json`. Both gates pivot on the
  // pristine initial sentinel `stage_completed === "-1.2"` (set by
  // `createInitialState`) and on whether the relevant downstream artifact
  // (`state.gaps`, `state.proposed_from`) has already been populated by a
  // prior turn through the loop. Without --propose we fall through to the
  // ordinary advance so non-propose runs skip both stages.
  //
  // Stage -0.5 owns the review/revise/pivot loop. On NO-PASS it returns
  // `advance: false` so `stage_completed` stays at "-1.2"; that way `--resume`
  // jumps back to -0.5 via `nextStage("-1.2")` (rather than skipping ahead to
  // Stage 0) once the orchestrator has reset/extended the iteration cursor in
  // `state.proposed_from`.
  let stage: Stage | null;
  const inProposeColdStart = !!ctx.proposeTopic && state.stage_completed === "-1.2";
  // Resume safety: if Stage -1.2 was last completed but the drafter never
  // actually wrote a proposal to disk (e.g. crashed mid-draft on a pivot),
  // re-enter -1.2 instead of advancing into the Stage -0.5 reviewer with a
  // missing or stale .tex. The reviewer would otherwise fall back to reading
  // the archived `_angle{N-1}_rejected.tex` and emit a confusing v0 review
  // for the new angle.
  const proposalPathFromState = state.proposed_from?.proposal_path;
  const draftIncomplete =
    state.stage_completed === "-1.2" &&
    !!proposalPathFromState &&
    !existsSync(proposalPathFromState);
  const pendingD0Directive =
    ctx.resume &&
    (state.stage_completed === "0" || state.stage_completed === "0.5") &&
    await hasPendingD0Directive(ctx);
  if (
    pendingD0Directive &&
    options.startStage &&
    STAGE_ORDER.indexOf(options.startStage) > STAGE_ORDER.indexOf("0")
  ) {
    throw new Error(
      `refusing --from-stage ${formatStageLabel(options.startStage)}: unconsumed D0 escalation entries exist; ` +
        `re-enter D0 so the frozen core/prose is repaired before downstream review`,
    );
  }
  if (inProposeColdStart && !state.gaps) {
    stage = "-1.1";
  } else if (inProposeColdStart && !state.proposed_from) {
    stage = "-1.2";
  } else if (draftIncomplete) {
    stage = "-1.2";
  } else if (pendingD0Directive) {
    stage = "0";
    console.warn("[causalsmith] pending D0 escalation entries detected; plain resume re-enters D0 before downstream review.");
  } else {
    stage = nextStage(state.stage_completed);
  }
  if (options.startStage) {
    stage = options.startStage;
  }
  const MAX_STAGE_ITERATIONS = 100;
  let stageIters = 0;
  while (stage && stageIters++ < MAX_STAGE_ITERATIONS) {
    // Re-check at every transition, not just process startup. A D-stage action
    // can append a directive while this process is alive; D0.5 must never review
    // a core whose durable repair request is still beyond the working cursor.
    if (stage === "0.5" && await hasPendingD0Directive(ctx)) {
      stage = "0";
      console.warn("[causalsmith] unconsumed D0 escalation detected before D0.5; re-entering D0 fail-closed.");
    }
    const started = performance.now();
    let result;
    try {
      result = await handler({ ctx, state, stage });
    } catch (error) {
      const duration_ms = Math.round(performance.now() - started);
      const message = error instanceof Error ? error.message : String(error);
      // A handler exception is still a pipeline event. Previously it escaped before
      // any journal append, so event-trigger monitors saw neither progress nor failure
      // and waited the full window while the process had already exited.
      try {
        await appendPipelineLog(ctx, { stage, status: "failed", duration_ms, message });
      } catch (logError) {
        // Preserve the original stage failure; a secondary journal failure must not
        // replace the actionable exception that stopped the pipeline.
        console.error(`[causalsmith] failed to journal stage ${stage} exception: ${logError instanceof Error ? logError.message : String(logError)}`);
      }
      throw error;
    }
    const duration_ms = Math.round(performance.now() - started);
    // A combined handler may enter in one slot but complete through a later logical stage. The
    // F2.5 proof-review handler, for example, owns proof fill, lint, and dual convergence and returns
    // `completedStage: "4"`. Log that successful aggregate completion as F4. Combined handlers
    // can also report a later logical stage for a checkpoint (for example an F3 escalation while
    // entered via F2.5), so prefer their returned stage over the physical entry slot.
    const loggedStage = result.status === "completed" && result.completedStage
      ? result.completedStage
      : result.stage;
    // On a halt, re-surface the orchestrator playbook (it drifts out of
    // attention over a long run) — both on the checkpoint line it reads and on
    // the console it sees after `--resume`.
    const guidance = checkpointGuidance(stage, result.status, state.flags, state.auto_mode, result.message);
    await appendPipelineLog(ctx, {
      stage: loggedStage,
      status: result.status,
      duration_ms,
      message: result.message,
      ...(guidance ? { next_step_guidance: guidance } : {}),
    });
    if (guidance) {
      console.warn(
        `\n[causalsmith] halt at ${formatStageLabel(stage)} (${result.status}). NEXT STEPS:\n${guidance}\n`,
      );
    }

    if (result.status === "blocked") {
      await saveState(ctx.repoRoot, ctx.qid, ctx.specialization, state);
      break;
    }

    if (result.advance !== false) {
      state.stage_completed = result.completedStage ?? stage;
    }
    await saveState(ctx.repoRoot, ctx.qid, ctx.specialization, state);

    // Paper-scoped run status reconciliation hook: log per-theorem progress
    // after each successful stage. Does not halt the pipeline.
    if (result.status === "completed") {
      const summary = reconcilePaperStatus(state);
      if (state.theorems && state.theorems.length > 0) {
        const parts: string[] = [];
        if (summary.completed) parts.push(`${summary.completed} completed`);
        if (summary.in_progress) parts.push(`${summary.in_progress} in_progress`);
        if (summary.pending) parts.push(`${summary.pending} pending`);
        if (summary.stuck) parts.push(`${summary.stuck} stuck`);
        if (summary.failed) parts.push(`${summary.failed} failed`);
        console.warn(`[paper] stage ${formatStageLabel(stage)}: ${parts.join(", ")}`);
      }
    }

    if (stage === "5" && result.advance !== false) {
      // Phase 3: post-Stage-5 close-OpenQuestion hook. Skip on dry-run (the
      // mock Stage 5 does not produce a real bank entry). Skip when the run
      // was not launched via `--from-question`. On hook failure: log + leave
      // the bank intact + emit the next-step message; the user runs
      // `tools/bin/close_oq.ts` to repair (spec §9 row 8).
      // Must run BEFORE the generic checkpoint break: live Stage 5 returns
      // status "checkpoint" (CKPT 2), which previously short-circuited this
      // hook on every real run (it only fired on dry-run "completed").
      await runPostStage5CloseHook(ctx, state);
      break;
    }
    if (result.status === "checkpoint") {
      break;
    }
    const logicalCompletedStage = result.completedStage ?? stage;
    if (result.status === "completed" && options.stopAfterStage === logicalCompletedStage) break;
    // STOP_AFTER fires only when the stage actually completed. A rewound stage
    // has not produced a settled artifact at `stage`, so the pipeline must keep
    // running until the rewound chain re-completes the stage (or hits a real
    // checkpoint).
    if (result.status !== "rewound" && process.env.CAUSALSMITH_STOP_AFTER === logicalCompletedStage) break;
    // Rewound stages reset `state.stage_completed` to an earlier marker; the
    // next iteration must advance from that marker, not from the local `stage`
    // variable which still points at the stage whose handler just rewound.
    stage =
      result.status === "rewound"
        ? nextStage(state.stage_completed)
        // Combined handlers may complete several logical stages at once. Advance from the stage
        // actually completed so their already-logged phases do not reappear as legacy skip rows.
        : nextStage(result.completedStage ?? stage);
  }
  if (stageIters > MAX_STAGE_ITERATIONS) {
    throw new Error(
      `Pipeline exceeded ${MAX_STAGE_ITERATIONS} stage iterations — possible infinite rewind loop`,
    );
  }

  return state;
}

async function resolveResumeGates(
  ctx: PipelineContext,
  state: StateJson,
): Promise<{ open: true } | { open: false; message: string }> {
  const angleCheckpoint = state.proposed_from?.angle_checkpoint;
  if (angleCheckpoint) {
    const actions = angleCheckpoint.kind === "revise"
      ? "continue"
      : "switch, retry, or give-up";
    return {
      open: false,
      message:
        `D-0.5 ANGLE CHECKPOINT BLOCKED: ${angleCheckpoint.kind} on angle ` +
        `${angleCheckpoint.angle} v${angleCheckpoint.version} (${angleCheckpoint.reason}). ` +
        `Resolve with \`causalsmith research --angle-action <${actions}> <qid> <spec>\`` +
        `; add \`--angle-directive <text|->\` to persist the D-orchestrator repair atomically.`,
    };
  }
  // Gate: pivot-budget-exhausted fallback. When intervention_routing decides
  // to route a D0.5 reject to D-1 (pivot to new angle) but the pivot budget
  // is already spent, it sets `flags.stage_neg1_fallback` with the full
  // reviewer reason and returns control. The current `stage_completed`
  // still points at the producing stage (e.g. "0"), so a naive `--resume`
  // would otherwise re-enter D0.5 and reproduce the same reject indefinitely.
  // Refuse to resume until the operator either banks the run or hand-clears
  // the flag (i.e. acknowledges the pivot-exhaustion verdict).
  // Gates: cap-hit / halt flags. These were previously WRITE-ONLY — a naive
  // `--resume` re-ran the full producer+reviewer+judge cycle (hours of codex),
  // hit the same persisted cap, and checkpointed again with no exit
  // instructions. Refuse up front with the reason + the deliberate clear step.
  // The set + clear semantics live in `CAP_GATES` (cap_gates.ts), shared with the
  // `--clear-gate <flag>` CLI so the orchestrator clears them via the CLI, never a
  // hand-edit of state.json.
  const flagsRec = state.flags as unknown as Record<string, unknown>;
  for (const gate of CAP_GATES) {
    const value = flagsRec[gate.flag];
    if (value) {
      return {
        open: false,
        message: `${gate.flag.toUpperCase()} BLOCKED: ${value}\nResolve: ${gate.guidance}.`,
      };
    }
  }
  if (!state.flags.missing_architecture) return { open: true };
  const items = state.flags.missing_architecture_items ?? [];
  const unresolved = [];
  for (const item of items) {
    const found = await declarationExists(ctx.repoRoot, item.name_suggestion, item.suggested_location);
    if (!found) unresolved.push(item);
  }
  if (unresolved.length > 0) {
    return {
      open: false,
      message: `MISSING ARCHITECTURE BLOCKED: ${unresolved
        .map((item) => item.name_suggestion)
        .join(", ")}`,
    };
  }
  state.flags.missing_architecture = false;
  delete state.flags.missing_architecture_items;
  return { open: true };
}

async function declarationExists(
  repoRoot: string,
  name: string,
  suggestedLocation: string | undefined,
): Promise<boolean> {
  const causalSmithRoot = path.join(repoRoot, "CausalSmith");
  const causaleanRoot = path.join(repoRoot, "..", "Causalean");
  const legacyCausaleanRoot = path.join(repoRoot, "Causalean");
  const suggestedRoot = suggestedLocation
    ? suggestedLocation.split(/[\\/]/)[0] === "Causalean"
      ? path.join(repoRoot, "..", suggestedLocation) // why: Causalean is a sibling package after the split.
      : path.join(repoRoot, suggestedLocation)
    : undefined;
  const roots = suggestedLocation
    ? [suggestedRoot!, causalSmithRoot, causaleanRoot, legacyCausaleanRoot]
    : [causalSmithRoot, causaleanRoot, legacyCausaleanRoot];
  for (const root of roots) {
    if (await fileOrTreeContains(root, name)) return true;
  }
  return false;
}

async function fileOrTreeContains(target: string, needle: string): Promise<boolean> {
  if (!existsSync(target)) return false;
  const statEntries = await readdir(target, { withFileTypes: true }).catch(async () => []);
  if (statEntries.length === 0 && target.endsWith(".lean")) {
    return (await readFile(target, "utf8").catch(() => "")).includes(needle);
  }
  for (const entry of statEntries) {
    const full = path.join(target, entry.name);
    if (entry.isDirectory() && (await fileOrTreeContains(full, needle))) return true;
    if (entry.isFile() && entry.name.endsWith(".lean")) {
      const text = await readFile(full, "utf8").catch(() => "");
      if (text.includes(needle)) return true;
    }
  }
  return false;
}

/**
 * Phase 3 — post-Stage-5 close hook (spec §13 Phase 3 exit criterion).
 *
 * Fires when Stage 5 completes cleanly and the run was launched via
 * `--from-question`. Mints a BankedTheorem node, adds the `closes` edge,
 * flips the OpenQuestion to `closed_by:<bt_id>`. On dry-run we emit a log
 * line instead — the mock Stage 5 produces no real bank entry.
 *
 * On hook failure: the bank entry stays intact, the OQ remains
 * `in_progress`, and the user is told to retry via
 * `tools/bin/close_oq.ts <qid> <spec> <oq_id>` (spec §9 row 8).
 */
async function runPostStage5CloseHook(
  ctx: PipelineContext,
  state: StateJson,
): Promise<void> {
  const oq_id = state.from_question_oq_id;
  if (state.loop && state.loop !== "research") return;
  if (!oq_id) {
    // No --from-question. Two cases:
    //   (a) Paper-scoped study-mode dispatch (study-pipeline S4 → paper_dispatcher):
    //       state.theorems is populated and state.context.from_insight_id is
    //       a string. Mint one BankedTheorem per completed theorem entry via
    //       the no-OQ minter so study-pipeline S5 can reconcile.
    //   (b) Generic research run: nothing to bank from the close hook.
    const passthroughCtx = (state as unknown as { context?: { from_insight_id?: unknown } }).context;
    const fromInsight =
      typeof passthroughCtx?.from_insight_id === "string"
        ? (passthroughCtx.from_insight_id as string)
        : null;
    const hasPaperTheorems = !!(state.theorems && state.theorems.length > 0);
    if (fromInsight && hasPaperTheorems) {
      await runPaperScopedNoOqCloseHook(ctx, state, fromInsight);
    }
    await tryWriteResearchCheckpointNext(ctx, state, null);
    return;
  }
  if (ctx.dryRun) {
    await appendPipelineLog(ctx, {
      stage: "5",
      status: "dry-run-skip",
      duration_ms: 0,
      message: `[dry-run] would close OpenQuestion ${oq_id} via close_open_question.ts`,
    });
    await tryWriteResearchCheckpointNext(ctx, state, oq_id);
    return;
  }

  try {
    const { closeOpenQuestion } = await import("./shared/close_open_question.js");
    const graphRoot = path.join(ctx.repoRoot, "doc", "study");

    // Paper-scoped mode: pass state.theorems so closeOpenQuestion writes N
    // BankedTheorems. Legacy single-theorem runs omit this field.
    const paperTheorems = (state.theorems && state.theorems.length > 0)
      ? state.theorems.map((t) => ({
          local_id: t.theorem_local_id,
          lean_decl_name: t.lean_decl_name,
          statement: t.statement,
          status: t.status,
        }))
      : undefined;

    const result = await closeOpenQuestion(
      {
        qid: ctx.qid,
        spec: ctx.specialization,
        oq_id,
        bankMetadata: {
          // Phase 3: leave both empty — the user/operator fills these in by
          // editing the BankedTheorem JSON (Phase 4 may auto-populate from
          // proposal §7 Assumptions). The `derived_from` + `closes` edge is
          // what matters for the graph wiring.
          instantiates: state.method_id ? [state.method_id] : [],
          uses: [],
        },
        ...(paperTheorems ? { theorems: paperTheorems } : {}),
      },
      { graphRoot },
    );

    // For paper-scoped runs, write bt_id back onto each completed theorems[k]
    // entry so readPostRunOutcomes / study-pipeline S5 can find it.
    if (paperTheorems && state.theorems && result.all_bt_ids.length > 0) {
      for (const entry of state.theorems) {
        if (entry.status === "completed") {
          const derivedBtId = `${ctx.qid}_${entry.theorem_local_id}_${ctx.specialization}`;
          if (result.all_bt_ids.includes(derivedBtId)) {
            entry.bt_id = derivedBtId;
          }
        }
      }
    }

    state.closed_oq = { oq_id, bt_id: result.bt_id };
    await saveState(ctx.repoRoot, ctx.qid, ctx.specialization, state);
    await appendPipelineLog(ctx, {
      stage: "5",
      status: "closed_oq",
      duration_ms: 0,
      message: `closed OpenQuestion ${oq_id} via BankedTheorem(s) ${result.all_bt_ids.length > 0 ? result.all_bt_ids.join(", ") : result.bt_id}`,
    });
  } catch (err: unknown) {
    if (err instanceof PaperHasNoCompletedTheorems) {
      // All theorems stuck/failed — OQ stays in_progress for Stage 7 reroute
      // or manual retry. Do NOT set state.closed_oq; log a warning instead.
      await appendPipelineLog(ctx, {
        stage: "5",
        status: "close_oq_failed",
        duration_ms: 0,
        message:
          `paper-scoped run for ${ctx.qid} has no completed theorems — ` +
          `OQ ${oq_id} left in_progress. study-pipeline S5 will mint failure-Notes. ` +
          `Use S7 reroute or manual retry to attempt again.`,
      });
    } else {
      const msg = err instanceof Error ? err.message : String(err);
      await appendPipelineLog(ctx, {
        stage: "5",
        status: "close_oq_failed",
        duration_ms: 0,
        message: `close hook failed for ${oq_id}: ${msg}. Run \`npx tsx tools/bin/close_oq.ts ${ctx.qid} ${ctx.specialization} ${oq_id}\` to retry manually.`,
      });
    }
  }
  await tryWriteResearchCheckpointNext(ctx, state, oq_id);
}

/**
 * Paper-scoped no-OQ banking variant: mints one BankedTheorem per completed
 * theorem entry without touching an OpenQuestion. Used when study-pipeline S4
 * dispatched the run via paper_dispatcher (so `from_question_oq_id` is null
 * and the banking target is the parent Insight, not a graph OQ).
 *
 * Dry-run is honored upstream (the outer hook is skipped on `--from-question`
 * dry-runs; paper_dispatcher itself sets `dryRun=false`).
 */
async function runPaperScopedNoOqCloseHook(
  ctx: PipelineContext,
  state: StateJson,
  insight_id: string,
): Promise<void> {
  if (ctx.dryRun) {
    await appendPipelineLog(ctx, {
      stage: "5",
      status: "dry-run-skip",
      duration_ms: 0,
      message: `[dry-run] would mint BankedTheorem(s) for paper-scoped run (insight=${insight_id})`,
    });
    return;
  }
  try {
    const { mintPaperScopedBankedTheoremsNoOq } = await import(
      "./shared/close_open_question.js"
    );
    const graphRoot = path.join(ctx.repoRoot, "doc", "study");
    const paperTheorems = (state.theorems ?? []).map((t) => ({
      local_id: t.theorem_local_id,
      lean_decl_name: t.lean_decl_name,
      statement: t.statement,
      status: t.status,
    }));
    const result = await mintPaperScopedBankedTheoremsNoOq(
      {
        qid: ctx.qid,
        spec: ctx.specialization,
        derived_from_insight_id: insight_id,
        bankMetadata: {
          instantiates: state.method_id ? [state.method_id] : [],
          uses: [],
        },
        theorems: paperTheorems,
      },
      { graphRoot },
    );

    if (state.theorems) {
      for (const entry of state.theorems) {
        if (entry.status === "completed") {
          const derivedBtId = `${ctx.qid}_${entry.theorem_local_id}_${ctx.specialization}`;
          if (result.bt_ids.includes(derivedBtId)) {
            entry.bt_id = derivedBtId;
          }
        }
      }
      await saveState(ctx.repoRoot, ctx.qid, ctx.specialization, state);
    }
    await appendPipelineLog(ctx, {
      stage: "5",
      status: "minted_bts",
      duration_ms: 0,
      message: `paper-scoped no-OQ mint: wrote BankedTheorem(s) ${result.bt_ids.join(", ")}`,
    });
  } catch (err: unknown) {
    if (err instanceof PaperHasNoCompletedTheorems) {
      await appendPipelineLog(ctx, {
        stage: "5",
        status: "close_oq_skipped",
        duration_ms: 0,
        message:
          `paper-scoped run for ${ctx.qid} has no completed theorems — no BT minted. ` +
          `study-pipeline S5 will mint failure-Notes.`,
      });
    } else {
      const msg = err instanceof Error ? err.message : String(err);
      await appendPipelineLog(ctx, {
        stage: "5",
        status: "close_oq_failed",
        duration_ms: 0,
        message: `paper-scoped no-OQ mint failed: ${msg}`,
      });
    }
  }
}

/**
 * Phase 4 — best-effort CHECKPOINT_NEXT.md writer for the research loop.
 * Wrapped in try/catch so any writer failure logs but never blocks Stage 5
 * completion (spec §R5).
 *
 * In dry-run mode, codex is bypassed via `dry-run-skip` propose so the
 * fallback template is written.
 */
async function tryWriteResearchCheckpointNext(
  ctx: PipelineContext,
  state: StateJson,
  oq_id: string | null,
): Promise<void> {
  try {
    const { writeCheckpointNext } = await import("./shared/checkpoint_next_writer.js");
    const { formalizationDir } = await import("./paths.js");
    const runDir = formalizationDir(ctx.repoRoot, ctx.qid);
    const graph_root = path.join(ctx.repoRoot, "doc", "study");
    const summaryParts: string[] = [
      `Research run ${ctx.qid}_${ctx.specialization} reached F5 cleanly.`,
    ];
    if (state.closed_oq) {
      summaryParts.push(`Closed OpenQuestion ${state.closed_oq.oq_id} via BankedTheorem ${state.closed_oq.bt_id}.`);
    } else if (oq_id) {
      summaryParts.push(`(dry-run) Would close OpenQuestion ${oq_id}.`);
    }
    const lineageDepth = (state.lineage?.parent_run_id ? 1 : 0);
    // Bypass real codex in dry-run or vitest mode; the writer's fallback path
    // emits a deterministic "no automatic suggestions" template. Live runs
    // use the default codex dispatcher.
    const bypassCodex = ctx.dryRun || !!process.env.VITEST || !!process.env.CAUSALSMITH_BYPASS_CODEX;
    const runCodex = bypassCodex
      ? async () => { throw new Error("test/dry-run: codex bypassed for propose_next"); }
      : undefined;
    const res = await writeCheckpointNext({
      loop: "research",
      run_id: `${ctx.qid}_${ctx.specialization}`,
      run_dir: runDir,
      graph_root,
      run_summary: summaryParts.join(" "),
      method_id: state.method_id,
      lineage_depth: lineageDepth,
      lineage_origin: oq_id ?? state.lineage?.parent_run_id,
      runCodex,
    });
    state.next_action = "pending_checkpoint";
    await saveState(ctx.repoRoot, ctx.qid, ctx.specialization, state);
    await appendPipelineLog(ctx, {
      stage: "5",
      status: res.fallback ? "checkpoint_next_fallback" : "checkpoint_next_written",
      duration_ms: 0,
      message: `CHECKPOINT_NEXT written: ${res.path}${res.fallback ? " (fallback template)" : ""}`,
    });
  } catch (err: unknown) {
    const msg = err instanceof Error ? err.message : String(err);
    await appendPipelineLog(ctx, {
      stage: "5",
      status: "checkpoint_next_failed",
      duration_ms: 0,
      message: `CHECKPOINT_NEXT writer failed (non-fatal): ${msg}`,
    });
  }
}
