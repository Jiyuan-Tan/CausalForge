---
qid: pid_late_bounded_defiers
spec: one_sided_compliance
topic: "Sharp partial identification of the Local Average Treatment Effect under one-sided non-compliance with bounded covariate-dependent defier mass: closed-form sharp bounds and the phase transition to point identification. The kernel question: when monotonicity (Imbens-Angrist 1994) is relaxed to allow a covariate-dependent defier subpopulation of bounded mass eta(X) <= eta_bar, characterize the sharp identified set for E[Y(1)-Y(0) | complier] in closed form, and identify the threshold on eta_bar at which the bounds collapse to point identification under additional shape restrictions."
novelty_target: relative-to-literature
tier_at_proposal: REJECT
tier_at_derivation: NA
proposal_promise_gap: "assumption_omitted"
reusable: unknown
reraise_status: retry
gap_reasons:
  - 'Conjecture 1: C-wellposed — The claimed sharp set ranges over models matching P(Y,D|Z=z,X) but the formula only uses the Z=0,D=0 mixture and omits the Z=1,D=0 observed cell, which constrains the never-taker/defier untreated mixture and can tighten the bound.'
  - 'Conjecture 2: C-sanity — The zero-threshold claim fails in the eta=0, pi_N>0 corner: Z=1,D=0 identifies the never-taker untreated mean, so the Z=0,D=0 mixture identifies mu_C0 and theta_C even when 0<m00<1.'
  - 'Theorem 1: N-pub — The observable principal-stratum mass decomposition is standard AIR/Imbens-Angrist principal-strata algebra, not a novel theorem.'
  - 'Conjecture 1: N-thin-survey — The literature comparison misses Huber2014, Economics Letters, ''Sensitivity checks for the local average treatment effect'', a directly relevant published monotonicity-sensitivity paper.'
reusable_artifacts:
  # TODO: list LP setup / operator / witness / literature_map /
  # counterexample paths inside this directory that future runs should
  # lift rather than re-derive.
seeds_burned: []
proof_attempt_summary: |
  The proposal attempted to derive closed-form sharp complier-LATE bounds under a no-always-takers, bounded-defier IV design and to prove a zero-threshold point-identification phase transition. Conjecture 1 (sharp bounds) was flagged as ill-posed because the formula omitted the Z=1,D=0 observable cell, which constrains the never-taker/defier untreated mixture and can tighten the bound. Conjecture 2 (zero-threshold phase transition) was directly refuted: in the eta=0, pi_N>0 corner the Z=1,D=0 cell identifies the never-taker untreated mean and the Z=0,D=0 mixture then point-identifies mu_C0, contradicting the claimed failure of standard non-endpoint restrictions. The proposal was rejected at Stage -1 after one cold-start iteration and never advanced to derivation.
banked_on: "2026-05-14"
---

# pid_late_bounded_defiers / one_sided_compliance — Failed

**Topic.** Sharp partial identification of the Local Average Treatment Effect under one-sided non-compliance with bounded covariate-dependent defier mass: closed-form sharp bounds and the phase transition to point identification. The kernel question: when monotonicity (Imbens-Angrist 1994) is relaxed to allow a covariate-dependent defier subpopulation of bounded mass eta(X) <= eta_bar, characterize the sharp identified set for E[Y(1)-Y(0) | complier] in closed form, and identify the threshold on eta_bar at which the bounds collapse to point identification under additional shape restrictions.

**Novelty target.** relative-to-literature

**D-0.5 verdict.** REJECT

**D0.5 verdict.** NA

**Banking reason.** D-0.5 final_verdict=pending after 1 iteration (cold-start REJECT). Never advanced past proposal stage; no derivation produced.

## Key files

- `pid_late_bounded_defiers_one_sided_compliance_state.json` — pipeline state at banking (`banked: true`).
- `pid_late_bounded_defiers_one_sided_compliance_proposal.tex` — final proposal version.
- `pid_late_bounded_defiers_one_sided_compliance.tex` — derivation note (if D0 ran).
- `pid_late_bounded_defiers_one_sided_compliance_reviews.jsonl` — per-round reviewer log (D-0.5 and D0.5).
- `pid_late_bounded_defiers_one_sided_compliance_reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
