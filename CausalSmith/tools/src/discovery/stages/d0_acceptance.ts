/** Exact-artifact receipt for a complete typed D0.5 pass.
 *
 * Proposal review (D-0.5) and typed core review (D0.5) are different gates. A
 * sanctioned D0 baseline rebase does not manufacture a new D-0.5 iteration,
 * so F-entry must use an authority emitted by D0.5 itself. Every full D0.5
 * pass writes this receipt, whether or not D0.R edited the core. F-entry binds
 * the authority to the proposal revision and exact proto/working/core bytes.
 */
import { createHash } from "node:crypto";
import { readFile } from "node:fs/promises";
import path from "node:path";
import type { PipelineContext, StateJson } from "../../types.js";
import { writeJsonAtomic } from "../../shared/json_atomic.js";
import { coreJsonPath } from "./d0_core.js";
import { loadWorkingState, proposalRevision, workingPath } from "./d0_working.js";
import { protoCoreJsonPath } from "./neg1_2_author.js";

interface D05AcceptanceReceipt {
  schema_version: 1;
  kind: "accepted-d05-store";
  proposal_revision: string;
  proto_sha256: string;
  working_sha256: string;
  core_sha256: string;
}

export function d05AcceptanceReceiptPath(ctx: PipelineContext): string {
  return path.join(path.dirname(coreJsonPath(ctx)), "d05_acceptance_receipt.json");
}

async function sha256File(filePath: string): Promise<string> {
  return createHash("sha256").update(await readFile(filePath)).digest("hex");
}

async function currentReceipt(ctx: PipelineContext, state: StateJson): Promise<D05AcceptanceReceipt | null> {
  const revision = proposalRevision(state);
  // Legacy/non-propose fixtures have no proposal cursor and are outside the
  // revision-coherence guard. Do not make their otherwise-valid D0.5 pass fail.
  if (!revision) return null;
  const working = await loadWorkingState(ctx);
  // Never bless a split store merely because a reviewer happened to read its
  // core. The receipt is authority only for a coherent current revision.
  if (!working || working.proposal_revision !== revision) return null;
  const [proto_sha256, working_sha256, core_sha256] = await Promise.all([
    sha256File(protoCoreJsonPath(ctx)),
    sha256File(workingPath(ctx)),
    sha256File(coreJsonPath(ctx)),
  ]);
  return {
    schema_version: 1,
    kind: "accepted-d05-store",
    proposal_revision: revision,
    proto_sha256,
    working_sha256,
    core_sha256,
  };
}

/** Called only after the complete typed D0.5 panel and novelty gate pass. */
export async function writeD05AcceptanceReceipt(ctx: PipelineContext, state: StateJson): Promise<void> {
  const receipt = await currentReceipt(ctx, state);
  if (receipt) {
    await writeJsonAtomic(d05AcceptanceReceiptPath(ctx), receipt);
    return;
  }
  if (proposalRevision(state)) {
    throw new Error("refusing to record typed D0.5 acceptance for an absent or split D store");
  }
}

/** Exact-byte validation; malformed/stale receipts are simply not authority. */
export async function hasValidD05AcceptanceReceipt(
  ctx: PipelineContext,
  state: StateJson,
): Promise<boolean> {
  try {
    const recorded = JSON.parse(await readFile(d05AcceptanceReceiptPath(ctx), "utf8")) as D05AcceptanceReceipt;
    const current = await currentReceipt(ctx, state);
    if (!current) return false;
    return recorded.schema_version === 1 && recorded.kind === "accepted-d05-store" &&
      recorded.proposal_revision === current.proposal_revision &&
      recorded.proto_sha256 === current.proto_sha256 &&
      recorded.working_sha256 === current.working_sha256 &&
      recorded.core_sha256 === current.core_sha256;
  } catch {
    return false;
  }
}
