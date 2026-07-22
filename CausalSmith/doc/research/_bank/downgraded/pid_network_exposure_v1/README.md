---
qid: pid_network_exposure
spec: v1
topic: "Partial identification of average direct treatment effects under partially-misspecified network exposure mappings, when interference structure is only locally known"
novelty_target: field
tier_at_proposal: ACCEPT
tier_at_derivation: ACCEPT
reusable_artifacts:
  # TODO: list LP setup / operator / witness / literature_map /
  # counterexample paths inside this directory that future runs should
  # lift rather than re-derive.
seeds_burned: []
banked_novelty_tier: subfield
proposal_promise_gap: "tier_genuinely_below"
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "The LP sharpness theorem is routine, but Theorem 2 proves the nonsharpness conjecture on an open finite design and gives the finite-polyhedral certificate reduction, which is enough for a field-level contribution under the requested floor."
  - "D-0.5 per-theorem log grades Theorem 1's published prior art overall_verdict: incremental (against Manski 1990)."
  - "does not claim that odd-set and lifted-cover inequalities by themselves form a universal small certificate list (the facet characterization / separation oracle is gestured at and dropped)."
  - "The causal contribution is not a new polyhedral theorem."
  - "RETIER 2026-07-18: 'under the requested floor' is the defect in three words — the reviewer graded TO the --novelty target instead of clearing a bar against it, inverting principle #14. Thm 1 is Manski's bounded-outcome LP with a finite union bolted on; Thm 2's containment is immediate (it is a relaxation) and the strict-gap half is the 'drop a constraint -> looser bound' direction principle #10 disqualifies. No nameable consumer at all: a full-text grep for consumer/empirical/applied/practitioner/software returns one hit, the journal name in the bibliography."
proof_attempt_summary: |
  Attempted sharp joint-completion LP bounds for exposure-conditional average direct effects under
  a partially-observed network, plus a strict-nonsharpness separation against the cellwise
  relaxation. Theorem 1 is definitional bookkeeping (finite union of compacta); Theorem 2's witness
  is a correct 3-unit one-hidden-edge degree-cap pigeonhole with gap min(d1,d2)/3 — one
  counterexample, not a characterization of when the gap opens or how large it is. The certificate
  half proves a one-line convexity fact and explicitly disclaims the hard object. No algorithm
  beyond enumerating all completions (exponential; complexity never stated) and no estimation rung.
banked_on: "2026-05-14"
retiered_on: 2026-07-18
retiered_from: candidates
---

# pid_network_exposure / v1 — Downgraded

**Topic.** Partial identification of average direct treatment effects under partially-misspecified network exposure mappings, when interference structure is only locally known

**Novelty target.** field

**D-0.5 verdict.** ACCEPT

**D0.5 verdict.** ACCEPT

**Banking reason.** D-0.5 ACCEPT angle 0 v4 tier=field; D0.5 ACCEPT tier=field — sharp joint-completion LP bounds for network-exposure ADEs with strict cellwise-relaxation nonsharpness.

Re-tiered from `candidates` to `downgraded` on 2026-07-18. The `candidates` tier has been retired from the bank and the pipeline.

This entry was banked `field` on a D0.5 ACCEPT. An independent per-entry re-grade on 2026-07-18 assessed it **subfield**, in agreement with the objections already recorded in this entry's own review log before the accepting round reversed them (see `gap_reasons`). The math is sound; the novelty framing was too high — which is what `downgraded` means. `reraise_status: re-raise`: do not treat this direction as refuted. Re-anchor at the corrected tier, or pivot to the adjacent hard kernel recorded under **Re-anchor path** below.


## Re-anchor path (recorded before the seed burn)

Promote the disclaimed object to BE the kernel: characterize the facet family (or give a
separation oracle with proven complexity) for the projected degree-capped exposure-demand
polytope, and add the estimation rung — a computable relaxation of the completion union with a
proven approximation ratio plus inference over the identified set, mirroring exp_bipartite's
alpha-certificate. Plausibly field, but largely a combinatorial-optimization theorem with thin
causal delta, and the consumer gap would still need closing independently.

## Key files

- `pid_network_exposure_v1_state.json` — pipeline state at banking (`banked: true`).
- `pid_network_exposure_v1_proposal.tex` — final proposal version.
- `pid_network_exposure_v1.tex` — derivation note (if D0 ran).
- `pid_network_exposure_v1_reviews.jsonl` — per-round reviewer log (D-0.5 and D0.5).
- `pid_network_exposure_v1_reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
