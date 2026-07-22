// Node-addressable review verdicts for the D0.5 panel (D0_CORE_REDESIGN.md §6).
//
// The referees receive the full deterministic paper plus its typed CORE and emit
// findings keyed by core node id. This module defines
// the verdict shape, the combiner, and a mechanical check that a referee never
// cites a nonexistent node.
import { z } from "zod";
import { coreNodeIds, type Core } from "./schema.js";

export const REVIEW_VERDICTS = ["pass", "revise", "fail"] as const;
export const REFEREE_ROLES = ["math", "general", "decision"] as const;
export const CITED_CHECK_STATUSES = [
  "cited-verified",
  "cited-verified-attested",
  "cited-mismatch",
  "cited-underspecified",
  "cited-source-unverifiable",
] as const;

export const D0CitedCheckSchema = z.object({
  node_id: z.string(),
  check_status: z.enum(CITED_CHECK_STATUSES),
  note: z.string().min(1),
});

export const ReviewFindingSchema = z.object({
  node_id: z.string().optional(), // a core node id; omitted only for note-global findings
  code: z.string().optional(),
  one_line: z.string(),
});

export const ReviewVerdictSchema = z.object({
  referee: z.enum(REFEREE_ROLES),
  verdict: z.enum(REVIEW_VERDICTS),
  findings: z.array(ReviewFindingSchema).default([]),
  // Owned by the math referee. The D0.5 controller requires exactly one fresh
  // row per status:"cited" core node and validates the status against the
  // resolver mode; a broad `pass` cannot silently omit citation verification.
  cited_checks: z.array(D0CitedCheckSchema).default([]),
});

export type ReviewFinding = z.infer<typeof ReviewFindingSchema>;
export type ReviewVerdict = z.infer<typeof ReviewVerdictSchema>;
export type D0CitedCheck = z.infer<typeof D0CitedCheckSchema>;

/** Worst-of combine: fail dominates revise dominates pass. Math correctness is
 * load-bearing, but a math fail already forces overall fail under this rule. */
export function combineVerdicts(vs: ReviewVerdict[]): (typeof REVIEW_VERDICTS)[number] {
  // An empty panel is not a pass. Falling through to "pass" here would let a review
  // stage that produced NO verdicts advance the paper — a fail-open guarded only by
  // an invariant held in another module (`REFEREES` being a non-empty const).
  if (vs.length === 0) {
    throw new Error("combineVerdicts received no verdicts — a review that produced nothing cannot resolve to a pass.");
  }
  if (vs.some((v) => v.verdict === "fail")) return "fail";
  if (vs.some((v) => v.verdict === "revise")) return "revise";
  return "pass";
}

/** Finding node_ids that do not resolve to a real core node — a referee citing a
 * nonexistent node is itself a review defect (caught mechanically, like \coreref). */
export function unresolvedFindingNodes(core: Core, vs: ReviewVerdict[]): string[] {
  const ids = coreNodeIds(core);
  const bad: string[] = [];
  for (const v of vs) {
    for (const f of v.findings) {
      if (f.node_id && !ids.has(f.node_id)) bad.push(f.node_id);
    }
  }
  return bad;
}
