/**
 * CLI-owned decisions for the D-0.5 proposal checkpoint.
 *
 * The reviewer loop deliberately halts before dispatching another proposer.
 * This writer persists an optional D-orchestrator directive and then performs
 * exactly one schema-valid action: continue a revision, switch angles, grant a
 * bounded same-angle retry, or give up. No caller edits `state.json` directly.
 */
import type { PipelineContext, StateJson } from "../types.js";
import { loadState, saveState } from "../state.js";
import { proposalTexPath } from "../paths.js";
import { archiveProposalForPivot, NEG1_PIVOT_BUDGET } from "./stages/neg1_2.js";
import { appendNeg1EscalationLog } from "./stageNeg1_directive.js";

export type ProposalAngleAction = "continue" | "switch" | "retry" | "give-up";

export interface ApplyProposalAngleActionOptions {
  repoRoot: string;
  qid: string;
  specialization: string;
  action: ProposalAngleAction;
  extraRevisions?: number;
  directive?: string;
  directiveNote?: string;
}

export interface ProposalAngleActionResult {
  action: ProposalAngleAction;
  angle: number;
  version: number;
  nextAngle?: number;
  reviseCap?: number;
  directivePersisted: boolean;
  resume: boolean;
}

function resetForProducer(state: StateJson): void {
  const pf = state.proposed_from!;
  pf.last_draft_status = "completed";
  pf.last_draft_handoff = undefined;
  pf.last_reviewer_verdict = "";
  pf.final_verdict = "pending";
  pf.angle_checkpoint = undefined;
}

export async function applyProposalAngleAction(
  options: ApplyProposalAngleActionOptions,
): Promise<ProposalAngleActionResult> {
  const state = await loadState(options.repoRoot, options.qid, options.specialization);
  const pf = state.proposed_from;
  if (!pf) throw new Error("--angle-action requires an existing --propose run");
  const checkpoint = pf.angle_checkpoint;
  if (!checkpoint) {
    throw new Error(
      "--angle-action requires a pending D-0.5 angle checkpoint; the run has none",
    );
  }

  const directive = options.directive?.trim();
  if (options.directive !== undefined && !directive) {
    throw new Error("--angle-directive must not be empty");
  }

  // Validate the complete action before appending its directive. Previously an
  // invalid action (for example `continue` at an angle boundary) threw only
  // after journaling the directive, so a later valid action unexpectedly fed a
  // repair that was never actually committed.
  if (options.action === "continue") {
    if (checkpoint.kind !== "revise") {
      throw new Error(
        `--angle-action continue requires a revise checkpoint; found ${checkpoint.kind}`,
      );
    }
  } else {
    if (checkpoint.kind !== "angle-boundary") {
      throw new Error(
        `--angle-action ${options.action} requires an angle-boundary checkpoint; found ${checkpoint.kind}`,
      );
    }
    if (options.action === "retry") {
      if (options.extraRevisions === undefined) {
        throw new Error("--angle-action retry requires --extra-revisions <positive-integer>");
      }
      if (!Number.isInteger(options.extraRevisions) || options.extraRevisions <= 0) {
        throw new Error("--extra-revisions must be a positive integer");
      }
      if (!directive) {
        throw new Error("--angle-action retry requires a non-empty --angle-directive <text|->");
      }
    }
    if (options.action === "switch" && checkpoint.angle >= NEG1_PIVOT_BUDGET - 1) {
      throw new Error(
        `cannot switch beyond angle ${checkpoint.angle}: pivot budget ${NEG1_PIVOT_BUDGET} is exhausted; use retry or give-up`,
      );
    }
  }

  if (directive) {
    const ctx: PipelineContext = {
      repoRoot: options.repoRoot,
      qid: options.qid,
      specialization: options.specialization,
      dryRun: false,
      resume: true,
    };
    await appendNeg1EscalationLog(ctx, {
      version: checkpoint.version,
      directive,
      note: options.directiveNote ?? `angle-action:${options.action}`,
    });
  }

  const angle = checkpoint.angle;
  const version = checkpoint.version;
  if (options.action === "continue") {
    pf.current_angle_index = angle;
    pf.current_version = version;
    pf.current_mode = "revise";
    resetForProducer(state);
    await saveState(options.repoRoot, options.qid, options.specialization, state);
    return { action: options.action, angle, version, directivePersisted: !!directive, resume: true };
  }

  if (options.action === "retry") {
    const extra = options.extraRevisions!;
    const caps = pf.revision_cap_by_angle ?? {};
    const base = Math.max(checkpoint.revise_cap, version, caps[String(angle)] ?? 0);
    const reviseCap = base + extra;
    caps[String(angle)] = reviseCap;
    pf.revision_cap_by_angle = caps;
    pf.exhausted_angles = (pf.exhausted_angles ?? []).filter((a) => a !== angle);
    pf.current_angle_index = angle;
    pf.current_version = version;
    pf.current_mode = "revise";
    resetForProducer(state);
    await saveState(options.repoRoot, options.qid, options.specialization, state);
    return {
      action: options.action,
      angle,
      version,
      reviseCap,
      directivePersisted: !!directive,
      resume: true,
    };
  }

  const exhausted = pf.exhausted_angles ?? [];
  if (!exhausted.includes(angle)) exhausted.push(angle);
  pf.exhausted_angles = exhausted;

  if (options.action === "give-up") {
    pf.angle_checkpoint = undefined;
    pf.final_verdict = "NO-PASS";
    pf.pivot_budget_used = angle;
    state.flags.stage_neg1_fallback =
      `D-0.5 angle ${angle} ended by explicit --angle-action give-up: ${checkpoint.reason}`;
    await saveState(options.repoRoot, options.qid, options.specialization, state);
    return { action: options.action, angle, version, directivePersisted: !!directive, resume: false };
  }

  const archived = await archiveProposalForPivot(
    proposalTexPath(options.repoRoot, options.qid, options.specialization),
    angle,
  );
  if (archived && !(pf.archived_proposals ?? []).includes(archived)) {
    pf.archived_proposals = [...(pf.archived_proposals ?? []), archived];
  }
  const nextAngle = angle + 1;
  pf.current_angle_index = nextAngle;
  pf.current_version = 0;
  pf.current_mode = "pivot";
  pf.pivot_budget_used = nextAngle;
  resetForProducer(state);
  await saveState(options.repoRoot, options.qid, options.specialization, state);
  return {
    action: options.action,
    angle,
    version,
    nextAngle,
    directivePersisted: !!directive,
    resume: true,
  };
}
