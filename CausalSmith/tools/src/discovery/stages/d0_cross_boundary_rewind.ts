/** Typed, fail-closed completion of F→D0 rewind intents. */
import { createHash } from "node:crypto";
import { readFile } from "node:fs/promises";
import type { PipelineContext, StateJson } from "../../types.js";
import { coreNodeIds } from "../core/schema.js";
import { readTypedCore } from "../core/core_io.js";
import { coreJsonPath } from "./d0_core.js";
import { commitD0StoreReplacement } from "./d0_apply.js";
import { prepareD0ExtensionRebase } from "./d0_rebase_baseline.js";
import { protoCoreJsonPath } from "./neg1_2_author.js";
import {
  appendEscalationLog,
  loadWorkingState,
  proposalRevision,
  readEscalationLog,
} from "./d0_working.js";

const sha256 = (text: string): string => createHash("sha256").update(text).digest("hex");

/**
 * Detect a pre-fix F→D state already parked at D-1.2. The old receipt records
 * only that `stage_0` was requested, not whether it meant repair, extension, or
 * replacement, so no conversion is logically justified. Stop before D-0.5 can
 * review the stale proto and require the operator to classify the intent.
 */
export function legacyCrossBoundaryRewindGuard(state: StateJson): string | null {
  if (
    state.stage_completed !== "-1.2" ||
    state.flags.rewound_from_stage0 === undefined ||
    state.flags.rewound_from_stage0 === null ||
    state.flags.d0_cross_boundary_rewind
  ) return null;
  const message =
    "legacy cross-boundary stage_0 rewind has no typed intent; refusing to review/edit the pre-D0 proto. " +
    "Classify it explicitly as incremental_repair, extension, or replacement before resuming.";
  state.flags.stage0_rewind_intent_required = message;
  return message;
}

/** Seal the accepted source before the extension author sees it. Idempotent on resume. */
export async function sealPendingExtensionSource(args: {
  ctx: PipelineContext;
  state: StateJson;
}): Promise<void> {
  const receipt = args.state.flags.d0_cross_boundary_rewind;
  if (!receipt || receipt.intent !== "extension" || receipt.status !== "pending") return;
  const revision = proposalRevision(args.state);
  if (revision !== receipt.source_revision) return; // already authored at least once
  const coreBytes = await readFile(coreJsonPath(args.ctx), "utf8");
  const core = await readTypedCore(coreJsonPath(args.ctx));
  const ids = [...coreNodeIds(core)].sort();
  if (receipt.source_core_sha256 && receipt.source_core_sha256 !== sha256(coreBytes)) {
    throw new Error("extension rewind source core changed after it was sealed");
  }
  if (receipt.source_ids && JSON.stringify(receipt.source_ids) !== JSON.stringify(ids)) {
    throw new Error("extension rewind source node set changed after it was sealed");
  }
  receipt.source_core_sha256 = sha256(coreBytes);
  receipt.source_ids = ids;
}

/**
 * Pick D-1.2's edit base. The first extension draft edits the accepted D0 core,
 * never the stale pre-D0 proto; later revise rounds edit their immediately prior
 * extension proposal.
 */
export function extensionEditBasePath(args: {
  ctx: PipelineContext;
  state: StateJson;
  ordinaryProtoPath: string;
}): string {
  const receipt = args.state.flags.d0_cross_boundary_rewind;
  return receipt?.intent === "extension" &&
      receipt.status === "pending" &&
      proposalRevision(args.state) === receipt.source_revision
    ? coreJsonPath(args.ctx)
    : args.ordinaryProtoPath;
}

/** Consume an incremental repair as a D0 directive without touching proto/cursor. */
export async function consumePendingIncrementalRewind(args: {
  ctx: PipelineContext;
  state: StateJson;
}): Promise<void> {
  const receipt = args.state.flags.d0_cross_boundary_rewind;
  if (!receipt || receipt.intent !== "incremental_repair" || receipt.status !== "pending") return;
  if (proposalRevision(args.state) !== receipt.source_revision) {
    throw new Error("incremental D0 rewind refuses a changed proposal revision");
  }
  const marker = `[CROSS-BOUNDARY D0 INCREMENTAL ${sha256(JSON.stringify(receipt)).slice(0, 16)}]`;
  const journal = await readEscalationLog(args.ctx);
  if (!journal.some((entry) => entry.directive?.includes(marker))) {
    const working = await loadWorkingState(args.ctx);
    if (!working || working.proposal_revision !== receipt.source_revision) {
      throw new Error("incremental D0 rewind requires the accepted working cursor at its source revision");
    }
    await appendEscalationLog(args.ctx, {
      round: working.round,
      changed: [],
      directive:
        `${marker} Repair the accepted D0 paper in place. Preserve its proto and working cursor; ` +
        `do not replace the accepted claim catalogue. Root-cause directive: ${receipt.reason}`,
    });
  }
  delete args.state.flags.d0_cross_boundary_rewind;
  // The journal entry above is now the durable provenance. The old routing
  // marker must not survive without its typed receipt: a later legitimate
  // angle pivot would otherwise be mistaken for a pre-fix ambiguous rewind.
  args.state.flags.rewound_from_stage0 = null;
}

/**
 * Before the first D0 solve of an extension, atomically carry every accepted
 * proof onto the new additive proposal revision. Omission or mutation of any
 * accepted node aborts before either authoritative store is changed.
 */
export async function finalizePendingExtensionRebase(args: {
  ctx: PipelineContext;
  state: StateJson;
}): Promise<void> {
  const receipt = args.state.flags.d0_cross_boundary_rewind;
  if (!receipt || receipt.intent !== "extension" || receipt.status !== "pending") return;
  const extensionRevision = proposalRevision(args.state);
  if (!extensionRevision || extensionRevision === receipt.source_revision) {
    throw new Error("extension D0 rewind reached solve before an extension proposal revision was authored");
  }
  const sourceCoreBytes = await readFile(coreJsonPath(args.ctx), "utf8");
  if (!receipt.source_core_sha256 || sha256(sourceCoreBytes) !== receipt.source_core_sha256) {
    throw new Error("extension D0 rewind accepted-core basis changed; refusing rebase");
  }
  const sourceCore = await readTypedCore(coreJsonPath(args.ctx));
  const sourceIds = [...coreNodeIds(sourceCore)].sort();
  if (!receipt.source_ids || JSON.stringify(sourceIds) !== JSON.stringify(receipt.source_ids)) {
    throw new Error("extension D0 rewind accepted node set changed; refusing rebase");
  }
  const sourceWorking = await loadWorkingState(args.ctx);
  if (!sourceWorking) throw new Error("extension D0 rewind has no accepted working cursor");
  const protoPath = protoCoreJsonPath(args.ctx);
  const protoBytes = await readFile(protoPath, "utf8");
  const extensionProto = await readTypedCore(protoPath);
  const journal = await readEscalationLog(args.ctx);
  const consumed = sourceWorking.escalation_entries_consumed ?? 0;
  if (consumed > journal.length) {
    throw new Error("extension D0 rewind cursor is ahead of its escalation journal");
  }
  const actionableTail = journal.slice(consumed).filter((entry) =>
    entry.provenance_only !== true &&
    (entry.changed.length > 0 || !!entry.directive || !!entry.require_core_changes ||
      (entry.required_core_targets ?? []).length > 0 ||
      (entry.required_core_edits ?? []).length > 0 ||
      (entry.required_core_edit_mandates ?? []).length > 0 ||
      (entry.cancelled_core_edit_mandates ?? []).length > 0 ||
      !!entry.cancel_require_core_changes ||
      (entry.cancelled_core_targets ?? []).length > 0));
  if (actionableTail.length > 0) {
    throw new Error(
      `extension D0 rewind has ${actionableTail.length} unconsumed actionable directive(s); ` +
      `repair/adjudicate them before rebasing`,
    );
  }
  const plan = prepareD0ExtensionRebase({
    sourceCore,
    sourceWorking,
    extensionProto,
    sourceRevision: receipt.source_revision,
    extensionRevision,
    escalationEntries: journal.length,
  });
  const stateAfter = structuredClone(args.state);
  delete stateAfter.flags.d0_cross_boundary_rewind;
  stateAfter.flags.rewound_from_stage0 = null;
  const transactionId = await commitD0StoreReplacement({
    ctx: args.ctx,
    expectedProtoBytes: protoBytes,
    protoAfter: plan.proto,
    workingAfter: plan.working,
    stateAfter,
    note:
      `CROSS-BOUNDARY EXTENSION REBASE: preserved ${plan.preservedIds.length} accepted node(s); ` +
      `opened ${plan.addedIds.length} additive node(s); directive=${receipt.reason}`,
  });
  delete args.state.flags.d0_cross_boundary_rewind;
  args.state.flags.rewound_from_stage0 = null;
  console.warn(
    `[D0] completed extension rebase ${transactionId}: preserved ${plan.preservedIds.length}, ` +
      `added ${plan.addedIds.length}`,
  );
}
