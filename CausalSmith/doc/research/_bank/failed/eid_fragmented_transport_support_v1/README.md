---
qid: eid_fragmented_transport_support
spec: v1
topic: "Flagship new topic: support-fragmented causal transport across multiple source trials. Characterize sharp identification of a target-population ATE when no single source trial satisfies positivity on the target covariate support, but the collection of source trials jointly covers the target. The proposed kernel is a finite-support Hall-type if-and-only-if certificate: target ATE is identified exactly when every target support atom can be assigned to a source trial with experimental treatment support and invariant conditional potential-outcome law; below the certificate give a sharp partial-ID interval and explicit two-source witness. This should be positioned against Pearl-Bareinboim multi-transportability and Dahabreh-style multiple-trial transport as a finite positivity/support-fragmentation frontier, not an upgrade of any banked topic."
novelty_target: flagship
tier_at_proposal: REVISE
tier_at_derivation: NA
proposal_promise_gap: "tier_genuinely_below"
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "Conjecture 1: N-mischar -- Dahabreh et al. 2023 Section 3.4/Theorem 3 already treats fragmented trial support via weaker overlap over the collection."
  - "Theorem 2: N-pub -- the sharp interval is a direct bounded-outcome Manski/Robins rectangle bound applied atomwise to missing potential-outcome means."
  - "Theorem 2: N-thin-survey -- the closest published prior for the interval is classical Manski/Robins bounded-outcome bounds, absent from the checklist."
  - "Conjecture 1: N-thin-anchor -- flagship comparison needs a location-level anchor to Dahabreh et al. 2023 Section 3.4/Theorem 3 and an exact statement of what remains beyond A4/A5."
  - "Proposal: N-no-named-focal-object -- atom-cover certificate is named, but current contribution is a finite diagnostic/specialization rather than a flagship frontier."
  - "Theorem 2: C-definitional-unfold -- proof route is definition unfold plus rectangularity and linear optimization over bounded missing means."
reusable_artifacts:
  - path: "eid_fragmented_transport_support_v1_gaps.json"
    kind: literature_map
    one_line: "Useful multi-trial transport map: Dahabreh 2020/2023, Cole-Stuart 2010, Westreich 2017, Hotz-Imbens-Mortimer 2005, Kline-Tamer 2018, Zivich et al. 2025, Bareinboim et al. 2013."
  - path: "eid_fragmented_transport_support_v1_reviews/angle0_v1.json"
    kind: counterexample
    one_line: "Reviewer diagnosis showing why the atom-cover idea is already covered or field-tier."
  - path: "eid_fragmented_transport_support_v1_proposal.tex"
    kind: other
    one_line: "Reusable mainly as a warning: finite source-support coverage plus missing-cell bounds is not flagship unless a regime beyond Dahabreh 2023 is isolated."
seeds_burned: []
proof_attempt_summary: |
  Attempted a fresh ExactID topic on support-fragmented causal transport across multiple source trials. The reviewer found a genuine practical issue but not a flagship gap: the proposed atom-cover certificate is close to existing multi-trial transport overlap results, especially Dahabreh et al. 2023, and the failed-certificate interval collapses to classical bounded-outcome missing-cell bounds. This was stopped early after one review by design; the failure is topic choice, not pipeline behavior or reviewer over-strictness.
banked_on: "2026-05-24"
---

# eid_fragmented_transport_support / v1 â€” Failed

**Topic.** Flagship new topic: support-fragmented causal transport across multiple source trials. Characterize sharp identification of a target-population ATE when no single source trial satisfies positivity on the target covariate support, but the collection of source trials jointly covers the target. The proposed kernel is a finite-support Hall-type if-and-only-if certificate: target ATE is identified exactly when every target support atom can be assigned to a source trial with experimental treatment support and invariant conditional potential-outcome law; below the certificate give a sharp partial-ID interval and explicit two-source witness. This should be positioned against Pearl-Bareinboim multi-transportability and Dahabreh-style multiple-trial transport as a finite positivity/support-fragmentation frontier, not an upgrade of any banked topic.

**Novelty target.** flagship

**Stage -0.5 verdict.** REVISE

**Stage 0.5 verdict.** NA

**Banking reason.** Stopped early after Stage -0.5 angle0 v1 REVISE at field tier: Dahabreh et al. 2023 already treats fragmented trial support under weaker collection-level overlap, and the proposed below-frontier interval reduces to classical Manski/Robins bounded-outcome missing-cell bounds.

## Key files

- `eid_fragmented_transport_support_v1_state.json` â€” pipeline state at banking (`banked: true`).
- `eid_fragmented_transport_support_v1_proposal.tex` â€” final proposal version.
- `eid_fragmented_transport_support_v1.tex` â€” derivation note (if Stage 0 ran).
- `eid_fragmented_transport_support_v1_reviews.jsonl` â€” per-round reviewer log (Stage -0.5 and Stage 0.5).
- `eid_fragmented_transport_support_v1_reviews/` â€” per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
