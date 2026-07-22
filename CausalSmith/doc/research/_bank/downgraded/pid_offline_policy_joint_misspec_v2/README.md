---
qid: pid_offline_policy_joint_misspec
spec: v2
topic: "Coupling dichotomy and sharp non-rectangular identified set for offline contextual-bandit policy value V(pi) under JOINT misspecification: a propensity Marginal-Sensitivity-Model budget Gamma together with a structural epsilon-tube (fixed center law F0, fixed metric, stated support regularity) on the conditional potential-outcome law that the MSM clips. Prove the dichotomy: an additive tube on the conditional-outcome MEAN decouples (joint set = rectangular product, trivial), while a tube on the conditional QUANTILE function couples with the active MSM clip (joint set strictly inside the rectangular product). Deliver the closed-form sharp coupled endpoint, the non-rectangularity gap Delta_rect(Gamma,epsilon)>=0 and its positive region, and a Neyman-orthogonal efficient one-step EIF estimator with uniform inference that corrects the rectangular widening of the Frauen et al. (arXiv:2502.13022, ICLR 2026) sharp off-policy estimator V-hat^{+,*}; separate endpoint sharpness from EIF regularity away from the coupling-threshold kink."
novelty_target: field
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: null
reusable: solver_blocked
reraise_status: retry
gap_reasons:
  # Verbatim D0.5 (typed) D0.R escalation findings — TWO escalations on the SAME
  # semiparametric inference rung after two orchestrator directives (recipe, then
  # insight-rich). Identification core proved sound throughout; only the inference
  # rung is undischarged. NOT a novelty rejection (D-0.5 ACCEPT@field held).
  - "uniform_feasible_class_convergence_missing@lem:chat-plus-consistency — plug-in Chat_a_plus consistency needs uniform convergence / argmax-consistency over the CONSTRAINED MSM-cap-tube feasible class; bespoke empirical-process work, not a citable classical result."
  - "consistency_claim_not_discharged@conj:eif-one-step; inference_rung_partially_discharged — the one-step inference package rests on the unproved plug-in consistency."
  - "eif-derivation-asserted@lem:contact-face-eif-decomposition; undeclared_external_imports — the baseline MSM EIF (Frauen Thm 4.4) must be a REGISTERED accepted-substrate-gate in the DAG, not an inline citation; the typed gate requires every final node status=proved and forbids note-level weakening/dropping of the inference claim."
  - "sharpness-rests-on-unproved-attainment@thm:quantile-coupled-endpoint; zero_gap_criterion_needs_attainment@prop:rect-gap; tube_closure_not_reproduced/lower-tube-closure-gap@lem:joint-feasible-extrema-attained — attainment-side findings; the escalation itself notes these are LOCALLY repairable, but a partial edit was forbidden while the inference rung stays undischarged."
  - "redundant_assumptions@thm:quantile-coupled-endpoint — minor, locally fixable."
reusable_artifacts:
  # The identification half + the EIF first-order half are SOUND and reusable; lift
  # them rather than re-derive on a re-raise. All in the proto/core in this directory.
  - path: "discovery/pid_offline_policy_joint_misspec_core.json"
    kind: derivation
    one_line: "Proved (sound) identification core: thm:mean-decoupling (mean-tube rectangular), thm:quantile-coupled-endpoint (sharp coupled quantile-tube endpoint, V_cpl<=V_MSM + iff-equality criterion), prop:rect-gap (Delta_rect>=0 + exact iff-zero), lem:msm-mean-image-interval, lem:quantile-mean-identity."
  - path: "discovery/pid_offline_policy_joint_misspec_core.json"
    kind: derivation
    one_line: "EIF FIRST-ORDER half (sound): def:phi-tube-plus Firpo-form contact-face correction (-1/fobs at contact level Q0+eps, centered score); lem:contact-face-centering proves the centered contact score is conditionally MEAN-ZERO under the latent optimizing law => Neyman-orthogonality of phi_cpl=phi_MSM-phi_tube; lem:contact-face-eif-decomposition (envelope/Milgrom-Segal). Hirano-Porter kink boundary stated as scope."
  - path: "discovery/pid_offline_policy_joint_misspec_d0_escalation_log.jsonl"
    kind: literature_map
    one_line: "Round-2 + round-3 orchestrator directives carry the full literature-grounded EIF recipe (Firpo 2007 quantile-IF, Frauen 2502.13022 Thm 4.4 baseline EIF, Milgrom-Segal 2002 envelope, Hirano-Porter 2012 regularity boundary, Chernozhukov 2018 DML cross-fit) + the contact-condition orthogonality crux."
seeds_burned: []
proof_attempt_summary: |
  Field-tier coupled MSM-Gamma x quantile-tube-epsilon partial-ID. The identification
  core is fully proved and sound: the decouple/couple dichotomy (mean-tube rectangular
  vs quantile-tube coupled), the sharp coupled endpoint with its iff-equality criterion
  (narrowed at D0 from a false pointwise-envelope condition to "some MSM mean-maximizing
  law is jointly tube-feasible"), and the non-rectangularity gap Delta_rect>=0 with exact
  iff-zero. The estimation rung's FIRST-ORDER half also discharged after an insight-rich
  orchestrator directive: phi_cpl=phi_MSM-phi_tube with phi_tube the Firpo contact-face
  correction, and Neyman-orthogonality DERIVED via the contact first-order condition
  (centered contact score conditionally mean-zero under the latent optimizing law). What
  remained genuinely undischarged across TWO D0.5 escalations: (i) plug-in consistency of
  Chat_a_plus = uniform/argmax convergence over the constrained feasible class (bespoke
  empirical-process work), and (ii) registering the baseline MSM EIF (Frauen Thm 4.4) as
  an accepted substrate gate under the strict typed D0 gate (which demands every final
  node status=proved and forbids honestly scoping the inference claim). RETRY path: supply
  the uniform feasible-class consistency as a proper lemma (M-estimation/Glivenko-Cantelli
  over the MSM-cap-tube class) + a working typed-gate substrate-gate registration for the
  classical baseline EIF; the identification core + the orthogonality half lift directly.
banked_on: "2026-06-21"
---

# pid_offline_policy_joint_misspec / v2 — Downgraded

**Topic.** Coupling dichotomy and sharp non-rectangular identified set for offline contextual-bandit policy value V(pi) under JOINT misspecification: a propensity Marginal-Sensitivity-Model budget Gamma together with a structural epsilon-tube (fixed center law F0, fixed metric, stated support regularity) on the conditional potential-outcome law that the MSM clips. Prove the dichotomy: an additive tube on the conditional-outcome MEAN decouples (joint set = rectangular product, trivial), while a tube on the conditional QUANTILE function couples with the active MSM clip (joint set strictly inside the rectangular product). Deliver the closed-form sharp coupled endpoint, the non-rectangularity gap Delta_rect(Gamma,epsilon)>=0 and its positive region, and a Neyman-orthogonal efficient one-step EIF estimator with uniform inference that corrects the rectangular widening of the Frauen et al. (arXiv:2502.13022, ICLR 2026) sharp off-policy estimator V-hat^{+,*}; separate endpoint sharpness from EIF regularity away from the coupling-threshold kink.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** Identification core sound and field-novel (decouple/couple dichotomy: thm:mean-decoupling rectangular mean-tube vs thm:quantile-coupled-endpoint sharp coupled quantile-tube endpoint; prop:rect-gap non-rectangularity gap Delta_rect>=0 with exact iff-zero), and the EIF decomposition phi_cpl=phi_MSM-phi_tube with contact-condition Neyman-orthogonality (centered contact score mean-zero under the latent optimizing law) DERIVED; but D0.5 twice escalated because the semiparametric inference rung's plug-in consistency (uniform feasible-class / argmax convergence) and the substrate-gate registration of the baseline MSM EIF remain genuinely undischarged under the strict typed D0 gate.

## Key files

- `pid_offline_policy_joint_misspec_v2_state.json` — pipeline state at banking (`banked: true`).
- `pid_offline_policy_joint_misspec_v2_proposal.tex` — final proposal version.
- `pid_offline_policy_joint_misspec_v2.tex` — derivation note (if Stage 0 ran).
- `pid_offline_policy_joint_misspec_v2_reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `pid_offline_policy_joint_misspec_v2_reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
