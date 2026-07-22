---
qid: stat_sa_cate_pointwise
spec: v1
topic: Structure-agnostic minimax rate for pointwise CATE at x0 under black-box nuisance rates (matched achievability + Le Cam converse)
novelty_target: field
tier_at_proposal: ACCEPT          # original D-0.5; REVISE under corrected reviewer (well-definedness gate, 2026-06-04)
tier_at_derivation: ACCEPT        # original D0.5 ACCEPT@field; this was the reviewer MISS — see gap_reasons
downgrade_reason: reviewer_recalibration   # not a derivation defect; the field pass was a now-fixed D-0.5 gap
gap_reasons:
  - "C-wellposed (corrected D-0.5, angle0_v2.json): the at-a-point target tau_P(x0)=E[Y(1)-Y(0)|X=x0] is NOT a well-defined functional of the observed law without an explicit version/regularity condition; the local-bias bound |theta_h - tau(x0)| <= b_n PRESUPPOSES the point value and does not cure this."
  - "Self-contradictory topic: structure-agnostic (= no-smoothness) pointwise CATE. The smoothness needed to well-define tau(x0) is exactly what the structure-agnostic framing disclaims; adding it back collapses the contribution into smooth-model pointwise minimax prior art (Kennedy-Balakrishnan-Robins-Wasserman 2024)."
reusable_artifacts:
  - path: stat_sa_cate_pointwise_conj_1_fragment.tex
    kind: operator
    one_line: Localized AIPW / DR identity with the localization weight kept inside the conditional expectation, plus the cross-fit product-remainder bound (reusable for a WELL-POSED smoothed/averaged target theta_h).
  - path: stat_sa_cate_pointwise_conj_2_fragment.tex
    kind: witness
    one_line: Three-channel localized Le Cam converse construction (local-bias / local-sample / nuisance-product two-point pairs) — reusable lower-bound machinery for a smoothed local functional, not the ill-posed point value.
proof_attempt_summary: |
  Both conjectures "passed" at Stage 0 (upper=partial->confirmed after granting a standard
  clipped-score caveat; lower=confirmed three-channel Le Cam converse) and D0.5 accepted at
  field. The whole edifice rests on tau_P(x0) being a number, which it is not under the
  topic's own structure-agnostic (no-smoothness) framing. The D-0.5 reviewer lacked an
  estimand-well-definedness gate, so it never interrogated whether the target is a functional
  of P; the localization machinery (theta_h is a clean functional + a bias bridge) masked the
  ill-posed point value. Gate added 2026-06-04; corrected D-0.5 re-review returns REVISE with
  C-wellposed naming exactly this defect. Downgraded.
banked_on: 2026-06-04
---

Downgraded on **reviewer recalibration**, not on a derivation defect. As executed the run
reached (D-0.5 ACCEPT, D0.5 ACCEPT@field); the field pass was a now-fixed gap in the D-0.5
proposal reviewer (no estimand-well-definedness check).

Key files:
- `..._proposal.tex` — the verbatim v2 proposal that was accepted (structure-agnostic pointwise CATE).
- `..._reviews/angle0_v1.json` — original D-0.5 ACCEPT (the miss).
- `..._reviews/angle0_v2.json` — **corrected** D-0.5 REVISE with the `C-wellposed` well-definedness flag.
- `..._reviews/stage_0.5_to_0_attempt1.json` — original D0.5 derivation ACCEPT@field.
- `..._v1.tex` — stitched Stage-0 derivation (both conjectures confirmed under the ill-posed target).

Pipeline-calibration value: this entry is the worked example behind the 2026-06-04 fixes —
D-0.5 `C-wellposed` estimand-well-definedness gate (`stage_neg1_review.txt`) and thmsmith-topics
principle #13 (no self-contradictory topic). See memory `project_d05_refuted_retier_and_oeq_destale`.
