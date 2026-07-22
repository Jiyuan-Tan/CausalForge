---
qid: pid_ordinal_principal_facet_phase
spec: v1
topic: "Flagship upgrade of ordinal principal-strata partial identification: derive an explicit K=3 compatibility-facet certificate and phase threshold for strict nonrectangularity beyond pairwise adjacent-stratum bounds. Pre-anchor check: closest banked result is pid_ordinal_principal_strata_v1, accepted only at field tier with an adjacent-chain posterior LP; closest published anchors are Frangakis-Rubin principal stratification and ordinal principal-score / principal-ignorability work. Why non-trivial? The target is not a new-domain LP dual or another Manski interval: require a named facet normal, a minimal K=3 witness law, and a proof that the shared middle stratum creates strict containment of the common-law feasible polytope inside all pairwise relaxations, with an endpoint-attaining certificate. Why promising? The nonroutine object is the hand-derived compatibility facet and strict-containment witness. If the delta reduces to LP duality, support coverage, or definition-unfold frontier algebra, reject or downgrade."
novelty_target: flagship
supersedes:
  parent_qid: "pid_ordinal_principal_strata"
  parent_spec: "v1"
  parent_tier: "candidates"  # tier retired 2026-07-18; parent re-tiered to _bank/downgraded/
  upgrade_axis: "mechanism"
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "tier_genuinely_below"
reusable: not_reusable
reraise_status: re-raise
gap_reasons:
  - "D0.5 attempt 2: the derivation delivered a correct-looking finite K=3 active-constraint calculation and one-cell pairwise-relaxation witness, but not a flagship-level theorem."
  - "The relative-open phase was not derived from primitive inequalities; it was imported through Assumption phase-neighborhood."
  - "The only extension beyond the exact symmetric cell was an assumption that active bases persist under perturbation, so the phase statement was conditional on a conclusion-shaped nondegeneracy premise."
  - "Theorem middle-facet omitted the witness-cell and finite Gamma > 1 assumptions in the theorem statement."
  - "The closest comparison remained the in-repository parent result rather than a strictly wider published-class sharp bound or new identification target."
reusable_artifacts:
  - "pid_ordinal_principal_facet_phase_v1_gaps.json: literature map and parent-upgrade open problems."
  - "pid_ordinal_principal_facet_phase_v1_proposal.tex: final D-0.5 accepted flagship proposal; useful as a negative example of proposal-stage overrating."
  - "pid_ordinal_principal_facet_phase_setup.json: finite K=3 witness-cell setup with assumptions, target functional, C_mid, T_mid, T_pair, and Delta_mid_sym."
  - "pid_ordinal_principal_facet_phase_conj_1_fragment.tex: hand derivation of q_b^0 >= 1/(2 Gamma + 1), endpoint attainment, and middle-facet certificate."
  - "pid_ordinal_principal_facet_phase_conj_2_fragment.tex: pairwise-relaxation endpoint and Delta_mid_sym algebra."
  - "pid_ordinal_principal_facet_phase_v1_reviews.jsonl: D0.5 reviewer critique identifying the missing generic-class/open-neighborhood certificate."
seeds_burned:
  - index: 0
    one_liner: "Parent has qualitative nonrectangularity; this upgrade delivers a named K=3 middle-facet certificate C_mid with normal e_b^1 and endpoint-attaining rational law."
    reason: "Angle 0 reached D-0.5 flagship acceptance but D0.5 rejected it as below the flagship floor; future retries need a derived generic-class facet/phase certificate, not this symmetric-cell upgrade."
proof_attempt_summary: |
  The run upgraded the field-tier ordinal principal-strata parent by isolating a K=3 shared-middle witness, naming C_mid and n_mid, and deriving coherent versus pairwise endpoints T_mid and T_pair with Delta_mid_sym(Gamma) > 0. The finite symmetric-cell algebra survived review, but the flagship claim collapsed because the open-neighborhood phase was assumed rather than proved and the result did not become a generic-class facet theorem or strict extension of a published comparator class. Future work should not retry this exact upgrade unless it brings a primitive perturbation certificate or a genuinely wider theorem beyond the symmetric cell.
banked_on: "2026-05-25"
---

# pid_ordinal_principal_facet_phase / v1 — Failed

**Topic.** Flagship upgrade of ordinal principal-strata partial identification: derive an explicit K=3 compatibility-facet certificate and phase threshold for strict nonrectangularity beyond pairwise adjacent-stratum bounds. Pre-anchor check: closest banked result is pid_ordinal_principal_strata_v1, accepted only at field tier with an adjacent-chain posterior LP; closest published anchors are Frangakis-Rubin principal stratification and ordinal principal-score / principal-ignorability work. Why non-trivial? The target is not a new-domain LP dual or another Manski interval: require a named facet normal, a minimal K=3 witness law, and a proof that the shared middle stratum creates strict containment of the common-law feasible polytope inside all pairwise relaxations, with an endpoint-attaining certificate. Why promising? The nonroutine object is the hand-derived compatibility facet and strict-containment witness. If the delta reduces to LP duality, support coverage, or definition-unfold frontier algebra, reject or downgrade.

**Novelty target.** flagship

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** D0.5 rejected the flagship upgrade on novelty: the K=3 middle-facet algebra was coherent, but the contribution remained a symmetric finite-cell LP endpoint calculation and imported the open-neighborhood phase through an assumption rather than deriving a generic-class theorem.

**Supersedes.** pid_ordinal_principal_strata_v1 (tier=candidates, upgrade_axis=mechanism). The parent now lives in `_bank/downgraded/` (the `candidates` tier was retired 2026-07-18 and the parent re-graded subfield) and remains an independent reference; this entry is the flagship upgrade.

## Key files

- `pid_ordinal_principal_facet_phase_v1_state.json` — pipeline state at banking (`banked: true`).
- `pid_ordinal_principal_facet_phase_v1_proposal.tex` — final proposal version.
- `pid_ordinal_principal_facet_phase_v1.tex` — derivation note (if Stage 0 ran).
- `pid_ordinal_principal_facet_phase_v1_reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `pid_ordinal_principal_facet_phase_v1_reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
