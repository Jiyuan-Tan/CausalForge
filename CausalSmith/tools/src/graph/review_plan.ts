import { objIdToNodeId } from "./from_note.js";
import type { GraphSkeletonRow } from "./skeleton.js";
import type { FormalizationGraph, ReviewStatus } from "./types.js";

/** crosswalk obj_id → graph node id (AUX-<decl> hidden-defs → aux_<decl>). */
function rowNodeId(objId: string): string {
  return objId.startsWith("AUX-") ? `aux_${objId.slice(4)}` : objIdToNodeId(objId);
}

export interface GateReviewPlan {
  /** Rows whose node is dirty (changed since last review, or a dependent of one):
   *  send these to the reviewer. */
  reaudit: GraphSkeletonRow[];
  /** Non-dirty, already-reviewed rows: reuse their `node.review.status` without
   *  re-auditing. `matched`/`derived` is a frozen pass; `drift` stays blocking. */
  carried: Array<{ obj_id: string; status: ReviewStatus }>;
}

/**
 * The graph-native replacement for `splitCrosswalkByCache` + the freeze floor:
 * partition the skeleton into the dirty frontier (re-audit) and the carried
 * verdicts (everything else, reusing `node.review.status`). `dirty` is the node-id
 * frontier from `dirtyFrontier` (hash-changed nodes + their dependents).
 */
export function gateReviewPlan(
  graph: FormalizationGraph,
  skeleton: GraphSkeletonRow[],
  dirty: string[],
): GateReviewPlan {
  const dirtySet = new Set(dirty);
  const statusById = new Map(graph.nodes.map((n) => [n.id, n.review.status] as const));
  const reaudit: GraphSkeletonRow[] = [];
  const carried: GateReviewPlan["carried"] = [];
  for (const row of skeleton) {
    const nid = rowNodeId(row.obj_id);
    if (dirtySet.has(nid)) reaudit.push(row);
    else carried.push({ obj_id: row.obj_id, status: statusById.get(nid) ?? "unreviewed" });
  }
  return { reaudit, carried };
}
