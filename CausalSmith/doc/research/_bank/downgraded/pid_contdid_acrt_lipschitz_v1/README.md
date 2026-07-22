---
qid: pid_contdid_acrt_lipschitz
spec: v1
topic: "Sharp partial identification of the average causal response on the treated ACRT(d) in continuous-treatment difference-in-differences, when the cross-dose selection bias is constrained by a STRUCTURAL cross-dose regularity rather than pointwise: the group-conditional dose-l treatment effect ATT(l|d) (effect of dose l on the group whose actual dose is d) is L-Lipschitz (or monotone) in the conditioning group d. This couples the unidentified selection-bias terms ATT(l|h)-ATT(l|l) -- left unbounded by Callaway-Goodman-Bacon-Sant'Anna (arXiv:2107.02637, Thm 3, with the zero-sum TWFE level-weights of Thm 5) -- into a joint Lipschitz/isotonic nuisance set, so the sharp bounds on ACRT(d) are the image of that convex set under the linear identification map: a finite-grid LP / support-function envelope [L_L(d),U_L(d)], NOT the trivial observed-contrast +/- L*gap. Deliver the sharp envelope, the critical Lipschitz constant L* at which 0 first enters the ACRT(d) interval (dose-response sign undetermined; TWFE-implied sign unidentified), a nonseparability witness showing the joint constraints strictly sharpen the local bounds, and a plug-in estimator of the envelope endpoints with inference over the identified set."
novelty_target: relative-to-literature
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "tier_genuinely_below"
reusable: not_reusable
reraise_status: re-raise
gap_reasons:
  # Source: D0.5.G cold referee under field floor (pid_contdid_acrt_lipschitz_v1_reviews/stage_0.5_to_0_attempt1.json, field-retest).
  - "law-sharp: shallow sharpness — the main sharpness step 'becomes a direct two-point mean-completion construction once the missing inequalities are added', i.e. a definitional unfold, not a new sharpness principle."
  - "law-sharp: narrow causal content — 'the advertised law-sharp interval is sharp only for a very permissive completion class with arbitrary off-arm product kernels, so the causal content is much narrower than the continuous-treatment DiD headline suggests'."
  - "critical-l: 'standard parametric LP basis sensitivity' — not a new threshold object."
  - "plugin-inference: 'conservative pointwise outer coverage by enlarging the feasible set with diverging padding rather than a sharp or broadly usable inference theory'."
  - "overall: 'a real but specialized algebraic partial-identification note, not a field-level contribution' — tier=subfield < field floor, not salvageable within scope."
reusable_artifacts:
  # No liftable Lean artifact (reusable: not_reusable). Math reference only:
  - "pid_contdid_acrt_lipschitz_v1.tex — finite-grid LP / support-function envelope formulation for continuous-treatment DiD ACRT partial-ID; a math reference for a re-anchored, deeper field-tier kernel (tighter causal completion class + sharp inference + non-standard threshold)."
seeds_burned: []
proof_attempt_summary: |
  Discovery completed and ACCEPTed at the lenient relative-to-literature target
  (D-0.5 ACCEPT; D0.5 stamped tier_at_derivation=field). A manual field-floor
  retest (set novelty_target=field, re-ran D0.5) surfaced the D0.5.G cold
  referee's true verdict: tier=subfield, not salvageable within scope. No
  correctness defect — the math is sound; downgraded purely on novelty tier.
  Formalization (F1 NL plan + F2 Lean scaffold) was discarded; discovery
  artifacts retained for a possible re-raise at a corrected/sharper framing.
banked_on: "2026-06-10"
---

# pid_contdid_acrt_lipschitz / v1 — Downgraded

**Topic.** Sharp partial identification of the average causal response on the treated ACRT(d) in continuous-treatment difference-in-differences, when the cross-dose selection bias is constrained by a STRUCTURAL cross-dose regularity rather than pointwise: the group-conditional dose-l treatment effect ATT(l|d) (effect of dose l on the group whose actual dose is d) is L-Lipschitz (or monotone) in the conditioning group d. This couples the unidentified selection-bias terms ATT(l|h)-ATT(l|l) -- left unbounded by Callaway-Goodman-Bacon-Sant'Anna (arXiv:2107.02637, Thm 3, with the zero-sum TWFE level-weights of Thm 5) -- into a joint Lipschitz/isotonic nuisance set, so the sharp bounds on ACRT(d) are the image of that convex set under the linear identification map: a finite-grid LP / support-function envelope [L_L(d),U_L(d)], NOT the trivial observed-contrast +/- L*gap. Deliver the sharp envelope, the critical Lipschitz constant L* at which 0 first enters the ACRT(d) interval (dose-response sign undetermined; TWFE-implied sign unidentified), a nonseparability witness showing the joint constraints strictly sharpen the local bounds, and a plug-in estimator of the envelope endpoints with inference over the identified set.

**Novelty target.** relative-to-literature

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** D0.5.G cold referee under field floor: tier=subfield, not salvageable within scope — shallow two-point mean-completion sharpness, permissive completion class with narrow causal content, standard parametric-LP critical-L, and conservative padded inference; a real but specialized algebraic partial-ID note, not field-level.

## Key files

- `pid_contdid_acrt_lipschitz_v1_state.json` — pipeline state at banking (`banked: true`).
- `pid_contdid_acrt_lipschitz_v1_proposal.tex` — final proposal version.
- `pid_contdid_acrt_lipschitz_v1.tex` — derivation note (if Stage 0 ran).
- `pid_contdid_acrt_lipschitz_v1_reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `pid_contdid_acrt_lipschitz_v1_reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
