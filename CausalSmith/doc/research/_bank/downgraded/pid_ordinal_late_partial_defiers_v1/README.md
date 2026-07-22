---
qid: pid_ordinal_late_partial_defiers
spec: v1
topic: "Sharp partial identification of the LATE with an ordinal instrument under bounded per-rung defier proportions, extending Imbens-Angrist monotonicity to a calibrated partial-defiance regime where the share of defiers is observably restricted on each adjacent IV-rung pair"
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
  - "Its scope is narrower than a top-field flagship contribution"
  - "The current derivation is field-tier but not broad enough to oversell as a flagship general identification theory"
  - "proves a field-tier ordinal compatibility result above the enforced novelty floor"
  - "this note does not prove that stronger existence claim (Prop. 4, in its own body)"
  - "The cap-ray result is appropriately stated as regularity only, not as the unproved first-kink conjecture."
  - "RETIER 2026-07-18: graded above the 'enforced novelty floor' rather than against the ladder. Substantially overlaps downgraded pid_iv_bounded_defier_envelope_v1 — same Balke-Pearl latent-table LP with bounded-mass caps, one rung wider; that entry delivered MORE (closed-form scalar envelope, attempted facet taxonomy) and was graded subfield. The tier-justifying object (the criterion characterizing when per-rung sensitivity can be calibrated locally) is exactly what was not proved. Instance of Mogstad-Santos-Torgovitsky 2018, computable in ivmte today."
proof_attempt_summary: |
  Attempted sharp weighted-complier LATE bounds for an ordinal instrument under bounded per-rung
  defier caps over the 2^(J+1) response-path polytope, with a zig-zag pairwise-strictness witness
  (d=(1/5,2/5,4/5), m=(3/5,1/5,2/5), eta=(3/5,2/5): global upper endpoint 1/9 vs pairwise pasting
  1/5). Props 1-2 are conceded routine finite response-type algebra; Prop 3's inclusion is the
  trivial relaxation direction; Prop 4 delivers only textbook parametric-LP regularity. No endpoint
  estimator and no inference — the note states outright that this instance has no regression
  estimator. gap_reasons had never been filled before this re-tier.
banked_on: "2026-05-15"
retiered_on: 2026-07-18
retiered_from: candidates
---

# pid_ordinal_late_partial_defiers / v1 — Downgraded

**Topic.** Sharp partial identification of the LATE with an ordinal instrument under bounded per-rung defier proportions, extending Imbens-Angrist monotonicity to a calibrated partial-defiance regime where the share of defiers is observably restricted on each adjacent IV-rung pair

**Novelty target.** field

**D-0.5 verdict.** ACCEPT

**D0.5 verdict.** ACCEPT

**Banking reason.** D-0.5 ACCEPT angle 0 v3 tier=field; D0.5 ACCEPT tier=field — sharp finite response-path LATE bounds for an ordinal instrument under bounded per-rung defier proportions, with zig-zag pairwise strictness witness.

Re-tiered from `candidates` to `downgraded` on 2026-07-18. The `candidates` tier has been retired from the bank and the pipeline.

This entry was banked `field` on a D0.5 ACCEPT. An independent per-entry re-grade on 2026-07-18 assessed it **subfield**, in agreement with the objections already recorded in this entry's own review log before the accepting round reversed them (see `gap_reasons`). The math is sound; the novelty framing was too high — which is what `downgraded` means. `reraise_status: re-raise`: do not treat this direction as refuted. Re-anchor at the corrected tier, or pivot to the adjacent hard kernel recorded under **Re-anchor path** below.


## Re-anchor path (recorded before the seed burn)

Necessary-and-sufficient conditions on (P, eta) under which pairwise pasting is exact — a testable
local-calibration criterion — plus an estimator and inference for the endpoints. A #15 kernel
pivot and a new run. Account for this entry and pid_ordinal_principal_strata_v1 as ONE template
in slate-diversity terms.

## Key files

- `pid_ordinal_late_partial_defiers_v1_state.json` — pipeline state at banking (`banked: true`).
- `pid_ordinal_late_partial_defiers_v1_proposal.tex` — final proposal version.
- `pid_ordinal_late_partial_defiers_v1.tex` — derivation note (if D0 ran).
- `pid_ordinal_late_partial_defiers_v1_reviews.jsonl` — per-round reviewer log (D-0.5 and D0.5).
- `pid_ordinal_late_partial_defiers_v1_reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
