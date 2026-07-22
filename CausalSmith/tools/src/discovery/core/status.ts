// One rule for "what status does a node with a proof carry?".
//
// Written three times — twice in `stage0_solve` (as a local `solvedStatus`) and twice
// more in `bin/d0_rebuild_review_packet`, whose two copies do not even agree with each
// other. `cited` must survive: a node whose result is imported from the literature is
// not something this paper proved, and overwriting its status to `proved` is a
// provenance claim the run cannot support.

import type { CoreStatement } from "./schema.js";

/**
 * The status a node takes once a proof has been attached to it.
 *
 * `cited` is preserved; everything else becomes `proved`.
 *
 * WARNING PATH: callers can reach this with an EMPTY proof, which would publish
 * `status: "proved"` over nothing. That has never been observed in a real run, so this
 * preserves the long-standing behaviour rather than silently changing it — but it says
 * so, because the alternative is an unearned `proved` in a rendered paper. The recovery
 * tool independently chose the stricter rule (keep the prior status when the proof is
 * empty); if this warning ever fires, that is the rule to adopt.
 */
export function solvedStatus(
  s: { status?: CoreStatement["status"]; id?: string; proof_tex?: string },
): CoreStatement["status"] {
  if (s.status === "cited") return "cited";
  if (s.proof_tex !== undefined && s.proof_tex.trim().length === 0) {
    console.warn(
      `[D0] status: marking '${s.id ?? "<unknown>"}' proved with an EMPTY proof — ` +
        "the node will render as established with nothing behind it. Inspect before trusting this round.",
    );
  }
  return "proved";
}

/** Is a CARRIED working record unfinished — i.e. must it be reopened rather than
 *  republished as a settled result?
 *
 *  `partial` takes precedence over everything: it means the record was invalidated and
 *  must be re-derived, which is as true of a cited node as any other. The `cited`
 *  exemption applies only to the EMPTINESS test — a cited node's justification is its
 *  citation, so it legitimately carries no proof, and marking it unfinished on that basis
 *  rewrote it to `to-prove` while it still held `source`, producing a node the schema
 *  rejects (cited <=> source).
 *
 *  Lives here, not inline at the call site, so it can be tested against the real
 *  implementation instead of a copy that cannot fail when the source changes. */
export function isUnfinishedCarriedRecord(rec: {
  partial?: boolean;
  proof_tex?: string;
  node?: { status?: CoreStatement["status"] };
}): boolean {
  if (rec.partial === true) return true;
  if (rec.node?.status === "cited") return false;
  return (rec.proof_tex ?? "").trim().length === 0;
}
