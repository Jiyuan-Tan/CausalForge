---
qid: pid_dynamic_iv_compliance
spec: v2
topic: "Partial identification of dynamic treatment effects under non-Markov assignments and imperfect compliance"
novelty_target: field
tier_at_proposal: ACCEPT
tier_at_derivation: ACCEPT
reusable_artifacts:
  # Pre-filled at banking: the Stage -1 literature_map is auto-loaded from
  # state.json::proposed_from.literature_map; the proposal/derivation .tex
  # files are listed as pointers. Hand-edit to add lp_setup / witness /
  # counterexample entries after curating the v2 .tex.
  - path: pid_dynamic_iv_compliance_v2_proposal.tex
    kind: literature_map
    one_line: "Stage -1 literature map covering Balke-Pearl 1997, Manski 1990, Manski-Pepper 2000, Swanson-Hernan-Miller-Robins-Richardson 2018, MichaelCuiLorchTchetgen 2024, SojitraSyrgkanis 2024, BugniGaoObradovicVelez 2024, Han 2023 etc. — dynamic-IV / sequential-compliance frontier."
  - path: pid_dynamic_iv_compliance_v2_proposal.tex
    kind: other
    one_line: "Final accepted proposal (Stage -0.5 ACCEPT, angle 1) — full §1–§7 + tier justification for the non-Markov second-stage assignment direction."
  - path: pid_dynamic_iv_compliance_v2.tex
    kind: other
    one_line: "Stage 0 derivation note — Sharp memory-retaining dynamic IV bounds as LP projections; marginal mixture subtraction is only an outer relaxation."
seeds_burned: []
banked_novelty_tier: subfield
proposal_promise_gap: "tier_genuinely_below"
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "the positive result is a standard finite latent-response LP sharp-set/projection statement plus monotonicity under dropping equations... below novelty_target=field because it does not prove a regime-opening PartialID theorem or a new strictly tighter analytic bound beyond generic Balke-Pearl/Autobounds-style machinery."
  - "a narrow two-stage one-sided IV specialization of standard finite latent-response sharp-bound machinery, yielding assessed tier=subfield below novelty_target=field"
  - "To meet the field floor, the note would need a genuinely broader compatibility characterization, a general memory-gain theorem, or a nontrivial class of dynamic IV designs for which the response-contribution reduction opens a regime not already implicit in Balke-Pearl/Autobounds-style sharp-bound machinery. (None of the three repairs was made.)"
  - "Note self-disclaims field twice: 'does not replace that machinery with a general bound algorithm or a field-level characterization of dynamic IV bounds' and 'Its role is a compatibility diagnostic for this proposed closed form, rather than a field-level identification theorem'."
  - "RETIER 2026-07-18: two D0.5 rounds graded subfield with explicit repair conditions; round 3 accepted at field after the note NARROWED ITS OWN CLAIMS, with no gain in mathematical content. Nothing mathematical distinguishes v2 from downgraded siblings v1 and v3 — their objections apply verbatim. Theorem 2 refutes the pipeline's own Stage -1 conjecture, not a published estimator (the same defect that capped v3)."
proof_attempt_summary: |
  Attempted sharp memory-retaining dynamic IV bounds for a two-stage encouragement design with
  one-sided second-stage noncompliance: identify the never-taker branch, subtract it from the
  mixed branch, let unidentified nonresponder mass range over [0,1]. Reduces exactly to the
  Balke-Pearl system at a single X cell, as the note states. The memory-refinement clause is
  feasible-set monotonicity under adding equations; the negative result (marginal mixture
  subtraction is only an outer relaxation) refutes the pipeline's own conjecture. No estimation
  rung; an unresolved correctness item survives in the strict-aggregation proposition
  (compressed semicontinuity argument without a stated parametric LP continuity lemma).
banked_on: "2026-05-14"
retiered_on: 2026-07-18
retiered_from: candidates
---

# pid_dynamic_iv_compliance / v2 — Downgraded

**Topic.** Partial identification of dynamic treatment effects under non-Markov assignments and imperfect compliance

**Novelty target.** field

**D-0.5 verdict.** ACCEPT

**D0.5 verdict.** ACCEPT

**Banking reason.** D0.5 ACCEPT (field tier, 2026-05-14) parked pending tournament — generate sibling or cross-topic alternatives before advancing any one of them to F1.

Re-tiered from `candidates` to `downgraded` on 2026-07-18. The `candidates` tier has been retired from the bank and the pipeline.

This entry was banked `field` on a D0.5 ACCEPT. An independent per-entry re-grade on 2026-07-18 assessed it **subfield**, in agreement with the objections already recorded in this entry's own review log before the accepting round reversed them (see `gap_reasons`). The math is sound; the novelty framing was too high — which is what `downgraded` means. `reraise_status: re-raise`: do not treat this direction as refuted. Re-anchor at the corrected tier, or pivot to the adjacent hard kernel recorded under **Re-anchor path** below.


## Re-anchor path (recorded before the seed burn)

None recommended. Siblings v1 and v3 are already downgraded on the same objections; the
direction has now failed three times on the same axis (a specialization of Balke-Pearl /
Autobounds machinery with no named published open question closed). Treat as burned.

## Key files

- `pid_dynamic_iv_compliance_v2_state.json` — pipeline state at banking (`banked: true`).
- `pid_dynamic_iv_compliance_v2_proposal.tex` — final proposal version.
- `pid_dynamic_iv_compliance_v2.tex` — derivation note (if D0 ran).
- `pid_dynamic_iv_compliance_v2_reviews.jsonl` — per-round reviewer log (D-0.5 and D0.5).
- `pid_dynamic_iv_compliance_v2_reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
