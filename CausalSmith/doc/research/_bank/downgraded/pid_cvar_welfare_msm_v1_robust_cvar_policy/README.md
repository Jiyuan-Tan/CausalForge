---
qid: pid_cvar_welfare_msm_v1
spec: robust_cvar_policy
topic: "Sharp MSM partial identification of the CVaR / rank-dependent welfare of a policy under unobserved confounding. Extend Schroder-Frauen-Feuerriegel (2025, arXiv:2502.13022) confounding-robust off-policy bounds from the MEAN welfare V(pi)=E[sum_a pi(a|X) Y(a)] to the lower-tail welfare W_tau(pi)=CVaR_tau(Y(pi)) (Y lower=better; the policy minimizes worst-case tail risk). Central proposition: the worst-case MSM tilt does NOT commute with the CVaR quantile, so the sharp lower endpoint is the nested-quantile object CVaR_lower_tau(pi)=inf_eta{ eta + (1/tau) E_X[ worst-case-tilted E[(Y-eta)+ | X, pi] ] } with the inner tilt at the Dorn-Frauen level alpha=Gamma/(1+Gamma); prove it is STRICTLY tighter than CVaR applied to the pointwise average-potential-outcome band (the non-commutation gap is the named scalar). Computation: 1-D convex line search in eta, each step a closed-form tilted truncated mean. Estimation rung: efficient influence function for CVaR_lower_tau(pi) (nuisances eta(P), per-cell MSM quantile cutoffs, truncated outcome regressions), cross-fit one-step estimator with asymptotic normality and an Imbens-Manski interval over the partially-identified CVaR."
novelty_target: field
tier_at_proposal: ACCEPT
tier_at_derivation: ACCEPT
reusable_artifacts:
  - pid_cvar_welfare_msm_v1_robust_cvar_policy.tex
  - pid_cvar_welfare_msm_v1_robust_cvar_policy_d0r_ledger.json
  - pid_cvar_welfare_msm_v1_conj_2_salvage.json
  - pid_cvar_welfare_msm_v1_robust_cvar_policy_reviews.jsonl
seeds_burned: []
banked_novelty_tier: subfield
proposal_promise_gap: "tier_genuinely_below"
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "the current contribution is more field-level than flagship because the positive kernel is a corrected taxonomy and subclass program."
  - "The proof uses the missing condition Y(a) in [y_L,y_U] Q-a.s. for every action a. Assumption ass:tail only states support of the observed conditional law ... so theta_U^{full} need not upper-bound sup Theta_I(P)."
  - "the one-step proof consumes a unique active LP threshold lambda_{eta,a}(x), but Assumptions iid-overlap--nuisance give no explicit uniqueness or canonical differentiable selection condition near eta_* ... the asymptotic linear expansion is not justified under the stated assumptions."
  - "The original claim that the two-action, three-outcome, one-cell class has Delta_nc>0 was refuted by the common upper-tail MSM vertex q-star."
  - "RETIER 2026-07-18: both tier-carrying claims (full-class sharpness, strict non-commutation gap) were refuted during review; the round-4 ACCEPT re-graded the residue one notch down from the flagship pitch instead of re-deriving the tier. Residue is Rockafellar-Uryasev CVaR wrapped around a Dorn-Guo MSM LP, giving a non-sharp OUTER bound."
proof_attempt_summary: |
  Pitched a sharp CVaR-welfare endpoint under a marginal sensitivity model with a strictly
  positive band-vs-separate non-commutation gap. Full-class sharpness collapsed (sup Theta_I =
  +infinity without a nonfactual-outcome support restriction) and the strict gap was refuted by
  an explicit common upper-tail vertex making Delta_nc = 0 on the very class proposed as witness.
  What survives is a corrected taxonomy plus a computable outer bound for a conditionally
  exchangeable subclass, with a one-step limit law resting on four hand-added regularity
  assumptions. No estimation rung for the sharp object; consumer line does not survive the
  refutation.
banked_on: "2026-07-12"
retiered_on: 2026-07-18
retiered_from: candidates
---

# pid_cvar_welfare_msm_v1 / robust_cvar_policy — Downgraded

**Topic.** Sharp MSM partial identification of the CVaR / rank-dependent welfare of a policy under unobserved confounding. Extend Schroder-Frauen-Feuerriegel (2025, arXiv:2502.13022) confounding-robust off-policy bounds from the MEAN welfare V(pi)=E[sum_a pi(a|X) Y(a)] to the lower-tail welfare W_tau(pi)=CVaR_tau(Y(pi)) (Y lower=better; the policy minimizes worst-case tail risk). Central proposition: the worst-case MSM tilt does NOT commute with the CVaR quantile, so the sharp lower endpoint is the nested-quantile object CVaR_lower_tau(pi)=inf_eta{ eta + (1/tau) E_X[ worst-case-tilted E[(Y-eta)+ | X, pi] ] } with the inner tilt at the Dorn-Frauen level alpha=Gamma/(1+Gamma); prove it is STRICTLY tighter than CVaR applied to the pointwise average-potential-outcome band (the non-commutation gap is the named scalar). Computation: 1-D convex line search in eta, each step a closed-form tilted truncated mean. Estimation rung: efficient influence function for CVaR_lower_tau(pi) (nuisances eta(P), per-cell MSM quantile cutoffs, truncated outcome regressions), cross-fit one-step estimator with asymptotic normality and an Imbens-Manski interval over the partially-identified CVaR.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** ACCEPT

**Banking reason.** Field-tier D0.5 accepted; legacy pre-F run archived during stale live-folder cleanup.

Re-tiered from `candidates` to `downgraded` on 2026-07-18. The `candidates` tier has been retired from the bank and the pipeline.

This entry was banked `field` on a D0.5 ACCEPT. An independent per-entry re-grade on 2026-07-18 assessed it **subfield**, in agreement with the objections already recorded in this entry's own review log before the accepting round reversed them (see `gap_reasons`). The math is sound; the novelty framing was too high — which is what `downgraded` means. `reraise_status: re-raise`: do not treat this direction as refuted. Re-anchor at the corrected tier, or pivot to the adjacent hard kernel recorded under **Re-anchor path** below.


## Re-anchor path (recorded before the seed burn)

Sharp characterization of the joint-compatible endpoint theta_U^jnt (currently only an outer
bound, with no differentiability theory) together with its limit law. This is the adjacent hard
kernel the note itself names as open — a genuine #15 pivot, and new D0 work rather than a re-grade.

## Key files

- `pid_cvar_welfare_msm_v1_robust_cvar_policy_state.json` — pipeline state at banking (`banked: true`).
- `pid_cvar_welfare_msm_v1_robust_cvar_policy_proposal.tex` — final proposal version.
- `pid_cvar_welfare_msm_v1_robust_cvar_policy.tex` — derivation note (if Stage 0 ran).
- `pid_cvar_welfare_msm_v1_robust_cvar_policy_reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `pid_cvar_welfare_msm_v1_robust_cvar_policy_reviews/` — per-version reviewer JSON files (if present).

## Notes

This directory was recovered from a legacy live-folder snapshot accidentally
reintroduced by commit `b6ed6a30`. It is intentionally a candidate rather than
an active run. A future promotion should first migrate the prefixed legacy file
layout to the current canonical `discovery/`, `reviews/`, and `state.json`
layout, then enter at F1; D0 does not need to be repeated.
