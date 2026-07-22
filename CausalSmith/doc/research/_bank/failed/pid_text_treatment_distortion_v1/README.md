---
qid: pid_text_treatment_distortion
spec: v1
topic: "Sharp partial identification of average treatment effects when the treatment is a high-dimensional textual or visual object summarized by a learned representation that is subject to bounded sup-norm representation distortion against an oracle ground-truth representation, characterizing the sharp identified set of ATEs as a function of representation-distortion budget and the observed-representation outcome regression, recovering point identification under exact representation recovery at the trivial bound and providing a flagship-level non-parametric impossibility result tying any single-representation regression endpoint to a named structural assumption"
novelty_target: flagship
tier_at_proposal: NO-PASS
tier_at_derivation: NA
proposal_promise_gap: "tier_genuinely_below"
reusable: not_reusable
reraise_status: re-raise
gap_reasons:
  - 'Conjecture 2: N-thin-survey — tier=field below novelty_target=flagship; the current flagship is mostly generic interval/random-set minimax algebra plus a workflow-specific GenAI audit, so flagship tier needs a representation-specific statistical or identification theorem not inherited from existing partial-ID inference.'
  - 'Conjecture 2: N-thin-survey — Misses Chernozhukov, Lee, and Rosen 2013, Econometrica, on inference for intersection bounds/sup-inf functionals, which is closer to the simultaneous finite-sample envelope-band clause than Imbens-Manski/Stoye alone.'
  - 'Assumption two-fiber-open / Conjecture 2: C-wellposed — The constants c_j used in the two-fiber witness are not explicitly quantified or bounded; add c_0,c_1 to the existential block, ideally with range constraints compatible with Y in [0,1].'
  - 'proposal: N-thin-survey — tier=letter below novelty_target=flagship; the kernel is a routine finite-support random-set/support-function instantiation, not a flagship-level partial-ID contribution. (angle 0)'
  - 'Theorem 2: N-pub (angle 0) — The exact-recovery regression endpoint is already the point-identification premise in ImaiNakamura2024TextTreatments and related causally sufficient representation papers.'
  - 'Conjecture 2 / Theorem 2 positioning: C-coherence — The proposal sometimes treats epsilon-fiber invariance as a necessary-and-sufficient certificate for the published plug-in endpoint, but Theorem 2 only makes B_epsilon a singleton; equality to Delta_plug also needs endpoint calibration of mu-dagger to the fiber constants.'
reusable_artifacts:
  # TODO: list LP setup / operator / witness / literature_map /
  # counterexample paths inside this directory that future runs should
  # lift rather than re-derive.
seeds_burned: []
proof_attempt_summary: |
  Proposed a sharp partial-identification interval for ATEs when the treatment is a high-dimensional text/image object whose learned representation is only known to be within an ell-infinity distortion budget epsilon of an oracle; the bounding functional (essential ballwise regression envelope over distortion fibers) and the fiber-invariance obstruction for GenAI plug-in endpoints are both mathematically sound and new in the catalogue. The proposal failed not because the math was wrong but because every angle and revision cycle topped out at publishability_tier='field' rather than the required 'flagship' floor — the envelope construction is too close to standard random-set/Beresteanu-Molchanov-Molinari selector algebra to clear flagship novelty without a stronger representation-specific statistical or identification theorem. The math is sound and real at field tier; re-attempting with novelty_target=field, or by adding a uniform test/rate result for epsilon-fiber oscillation, would likely pass.
banked_on: "2026-05-15"
---

# pid_text_treatment_distortion / v1 — Failed

**Topic.** Sharp partial identification of average treatment effects when the treatment is a high-dimensional textual or visual object summarized by a learned representation that is subject to bounded sup-norm representation distortion against an oracle ground-truth representation, characterizing the sharp identified set of ATEs as a function of representation-distortion budget and the observed-representation outcome regression, recovering point identification under exact representation recovery at the trivial bound and providing a flagship-level non-parametric impossibility result tying any single-representation regression endpoint to a named structural assumption

**Novelty target.** flagship

**D-0.5 verdict.** NO-PASS

**D0.5 verdict.** NA

**Banking reason.** D-0.5 NO-PASS at novelty_target=flagship after 3 angles × 5 revises each (15 attempts). All angles consistently achieved tier=field but flagship floor blocked ACCEPT. Math sound at field tier; the kernel could be re-attempted at --novelty field if desired.

## Key files

- `pid_text_treatment_distortion_v1_state.json` — pipeline state at banking (`banked: true`).
- `pid_text_treatment_distortion_v1_proposal.tex` — final proposal version.
- `pid_text_treatment_distortion_v1.tex` — derivation note (if D0 ran).
- `pid_text_treatment_distortion_v1_reviews.jsonl` — per-round reviewer log (D-0.5 and D0.5).
- `pid_text_treatment_distortion_v1_reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
