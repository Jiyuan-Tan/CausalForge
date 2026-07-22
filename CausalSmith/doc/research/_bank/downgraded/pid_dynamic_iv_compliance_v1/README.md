---
qid: pid_dynamic_iv_compliance
spec: v1
topic: Partial identification of dynamic treatment effects under non-Markov assignments and imperfect compliance
novelty_target: field
tier_at_proposal: ACCEPT
tier_at_derivation: REVISE
proposal_promise_gap: "tier_genuinely_below"
reusable: not_reusable
reraise_status: re-raise
gap_reasons:
  - "Sharp LP theorem is a standard finite latent response-type sharpness argument, explicitly acknowledged at note lines 327 and 385-386 as not a new sharpness principle."
  - "T=3 strict-witness is baseline-pooling / omitted-stratum mixture logic, not a distinctively dynamic full-history-versus-stagewise result (note lines 369, 390)."
  - "Central Stage -1 kernel (T<=2 minimality of full-history vs. Markovized identification) refuted under the coarsening convention the note actually uses (lines 538-559)."
  - "Reductions (Balke-Pearl static face at T=1, exact-compliance sequential IPW) are inherited, not contribution-bearing."
  - "Literature positioning is honest but locates the result inside generic discrete sharp-bound machinery (Duarte-Finkelstein-Knox-Mummolo-Shpitser 2024; Balke-Pearl 1997) — supports subfield, not field, novelty."
reusable_artifacts:
  - path: pid_dynamic_iv_compliance_v1.tex
    kind: lp_setup
    one_line: Full LP formulation of the T=3 dynamic-IV partial-ID problem with finite response-type enumeration and observation operator; liftable to other angles on the same anchor topic.
  - path: pid_dynamic_iv_compliance_v1.tex
    kind: witness
    one_line: Concrete T=3 strict-gap witness with value -8/81 showing baseline-pooling coarsening loses sign-relevant identifying information.
  - path: pid_dynamic_iv_compliance_v1.tex
    kind: counterexample
    one_line: T=1 counterexample (Counterexample s0-t1-counter) refuting the proposed T<=2 minimality boundary under the stated coarsening convention.
  - path: pid_dynamic_iv_compliance_v1_proposal.tex
    kind: literature_map
    one_line: 12-paper literature map (Chen-Zhang 2023, Han 2024, Balke-Pearl 1997, Duarte et al 2024, Swanson-Labrecque-Hernan 2018, Xu-Zhu-Shi-Luo-Song 2023, Artman et al 2024, Mogstad-Torgovitsky-Walters 2024, Gabriel-Sjolander-Sachs 2023, Pu-Zhang 2021, Cui-Tchetgen 2021, Manski-Pepper 2000, Heckman-Humphries-Veramendi 2016) with claims and tensions — saves a future run from re-doing Step 0a.
  - path: pid_dynamic_iv_compliance_v1_reviews/angle0_v5.json
    kind: other
    one_line: Final ACCEPT proposal review (Stage -0.5) — useful as a calibration sample for what passed proposal but failed derivation.
  - path: pid_dynamic_iv_compliance_v1_oneshot_stage0_5_field_2026-05-14T15-55-41-123Z.txt
    kind: other
    one_line: Final Stage 0.5 field-tier review verdict (status=revise, classification=novelty) — verbatim source for the gap_reasons above.
seeds_burned:
  - index: 0
    one_liner: "Prior work ChenZhang2023 would imply that time-varying IV partial-identification can be organized through Bellman-style dynamic-regime objects. Our seed conjectures that Bellman or stagewise intervals are nonsharp under non-Markov assignment because one latent compliance response map must be pasted across histories."
    reason: "Pursued as angle 0; full-history LP collapses to standard finite response-type sharpness and a baseline-pooling witness rather than a true Bellman-vs-full-history non-pasting theorem. Stage 0.5 field-tier review judged this subfield, not field. Future runs on the same anchor topic should skip seed 0 unless the kernel is re-stated as a post-baseline full-history separation after retaining all assignment-relevant baseline variables."
banked_on: "2026-05-14"
---

# flagship_explore / f1 — Downgraded

**Proposal (D-0.5, ACCEPT after 5 revisions):** field-tier partial-ID
theorem on T=3 dynamic IV with imperfect compliance, claiming history-
separation / no-pasting from one joint dynamic compliance response map, plus
a T<=2 no-separation boundary.

**Derivation (D0.5 field-tier review, REVISE on novelty):** the
constructed LP is correct and reductions to Balke-Pearl and exact-compliance
IPW are valid, but the central content is acknowledged in the note itself as
(a) a standard finite-latent-table sharpness application and (b) a baseline-
pooling coarsening witness. The proposed T<=2 minimality boundary is refuted
by Counterexample s0-t1-counter under the same coarsening convention. Net
content sits at subfield, below the requested field floor.

## Proof attempt summary

A T=3 dynamic IV with binary instruments, treatments, outcomes, and
imperfect compliance was enumerated by latent response type; the standard
finite-type LP was solved over the implied observation operator. The
Markov / stagewise coarsened polytope was shown to strictly contain the
full-history polytope at a concrete (Z, X, Y) draw, with sign-relevant gap
-8/81. The originally proposed T<=2 minimality (full-history strictly
sharper than Markovized at the T<=2 boundary) was disproved at T=1 under the
coarsening convention actually used. The result is correct but, by the
note's own acknowledgement, recovers generic discrete-bound machinery rather
than a new dynamic separation theorem.

## Key files

- [`pid_dynamic_iv_compliance_v1.tex`](pid_dynamic_iv_compliance_v1.tex) — derivation note
  (D0). Contains the LP setup, sharpness lemmas, T=3 witness, T=1
  counterexample, and Section 14 math-object checklist.
- [`pid_dynamic_iv_compliance_v1_proposal.tex`](pid_dynamic_iv_compliance_v1_proposal.tex) —
  final (v5) accepted proposal.
- [`pid_dynamic_iv_compliance_v1_reviews/angle0_v5.json`](pid_dynamic_iv_compliance_v1_reviews/angle0_v5.json)
  — D-0.5 ACCEPT verdict.
- [`pid_dynamic_iv_compliance_v1_oneshot_stage0_5_field_2026-05-14T15-55-41-123Z.txt`](pid_dynamic_iv_compliance_v1_oneshot_stage0_5_field_2026-05-14T15-55-41-123Z.txt)
  — D0.5 final field-tier REVISE verdict (load-bearing for `gap_reasons`).
- [`pid_dynamic_iv_compliance_v1_state.json`](pid_dynamic_iv_compliance_v1_state.json) —
  pipeline state at the moment of banking (`banked: true`,
  `banked_tier: "downgraded"`, `banked_on: 2026-05-14`). The seed registry
  inside this state.json now carries `burned: true` on `seed_details[0]`
  (Chen-Zhang Bellman) so future proposal runs on the same anchor topic
  start from seeds 1..10.

## What a field-tier repair would have to do

Per the D0.5 verdict (verbatim): "a field-tier repair would need a
genuinely dynamic post-baseline full-history separation or non-pasting
theorem after retaining assignment-relevant baseline variables." Concretely,
either (i) a post-baseline full-history separation after explicitly carrying
all assignment-relevant baseline variables through the coarsening, or
(ii) a precise non-pasting theorem for local dynamic IV certificates with a
sharp primal/dual witness. Rephrasing the current LP sharpness or the
baseline-pooling witness will not lift the tier.
