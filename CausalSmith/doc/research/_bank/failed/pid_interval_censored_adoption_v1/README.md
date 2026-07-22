---
qid: pid_interval_censored_adoption
spec: v1
topic: "New topic: sharp partial identification for staggered-adoption DiD when adoption time is interval-censored rather than observed exactly. Pre-anchor check: closest published anchors are Sun-Abraham and Callaway-Sant'Anna group-time ATT identification with known adoption cohorts, plus Honest-DiD sensitivity work; our theorem is not that because the latent adoption-date refinement is unobserved, so the target is the geometry of all event-time ATT paths compatible with coarsened cohort bins. Require a concrete nonroutine object: an endpoint certificate over latent timing refinements and a two-cohort witness where two refinements induce identical observed coarsened panels but opposite event-time contrast signs. Avoid merely reusing LP duality or pretrend sensitivity; if the contribution is only a missing-cell Manski bound, pivot."
novelty_target: relative-to-literature
tier_at_proposal: NONFLAGSHIP-KILL
tier_at_derivation: NA
proposal_promise_gap: "tier_genuinely_below"
reusable: not_reusable
reraise_status: re-raise
gap_reasons:
  - "Conjecture 1 | Conjecture 2: N-thin-survey -- checklist misses Denteh and Kedagni 2026, whose abstract explicitly covers ambiguous policy timing, DID misclassification, wrong signs, attenuation, and ATT bounds."
  - "Conjecture 1: published prior art incremental -- Augustin-Gutknecht-Liu 2025 and Denteh-Kedagni 2026 cover adjacent staggered-adoption misclassification/ambiguous-timing bounds; Gamma_lambda(P) over exact-event-time refinements remains only a field-tier refinement."
  - "Theorem 2: already-known -- generic consequence of a sharp scalar identified interval excluding zero."
  - "Angle 0: nonflagship-kill -- after v3 the proposal had no soundness or structure flags, but publishability_tier remained field."
reusable_artifacts:
  - path: "pid_interval_censored_adoption_v1_gaps.json"
    kind: literature_map
    one_line: "Useful interval-censored/adoption-timing DiD map: Callaway-Sant'Anna, Sun-Abraham, Goodman-Bacon, de Chaisemartin-D'Haultfoeuille, Manski-Tamer, Augustin-Gutknecht-Liu, and ambiguous-timing DiD comparators."
  - path: "pid_interval_censored_adoption_v1_reviews/angle0_v3.json"
    kind: counterexample
    one_line: "Clean reviewer diagnosis: mathematically clean by v3 but only field-tier/incremental once Denteh-Kedagni 2026 is considered."
  - path: "pid_interval_censored_adoption_v1_proposal_angle0_rejected.tex"
    kind: witness
    one_line: "Reusable finite latent-timing refinement witness, but not enough by itself to support a stronger novelty claim."
seeds_burned: []
proof_attempt_summary: |
  Attempted a new partial-ID topic for staggered-adoption DiD with interval-censored adoption dates, using endpoint certificates over latent timing refinements and opposite-sign observational-equivalence witnesses. The reviewer repaired away correctness issues by v3, but the remaining kernel stayed field-tier: close ambiguous-timing/misclassified-DiD literature already covers wrong signs and ATT bounds, leaving the proposed Gamma_lambda(P) geometry as an incremental refinement. This is a topic/proposal-strength failure rather than reviewer strictness or D0 solver weakness; future attempts should not revisit interval-censored DiD unless they bring a genuinely nonroutine estimator/inference object beyond finite refinement bounds.
banked_on: "2026-05-24"
---

# pid_interval_censored_adoption / v1 â€” Failed

**Topic.** New topic: sharp partial identification for staggered-adoption DiD when adoption time is interval-censored rather than observed exactly. Pre-anchor check: closest published anchors are Sun-Abraham and Callaway-Sant'Anna group-time ATT identification with known adoption cohorts, plus Honest-DiD sensitivity work; our theorem is not that because the latent adoption-date refinement is unobserved, so the target is the geometry of all event-time ATT paths compatible with coarsened cohort bins. Require a concrete nonroutine object: an endpoint certificate over latent timing refinements and a two-cohort witness where two refinements induce identical observed coarsened panels but opposite event-time contrast signs. Avoid merely reusing LP duality or pretrend sensitivity; if the contribution is only a missing-cell Manski bound, pivot.

**Novelty target.** relative-to-literature

**Stage -0.5 verdict.** NONFLAGSHIP-KILL

**Stage 0.5 verdict.** NA

**Banking reason.** Stopped after D-0.5 angle0 v3 remained REVISE@field: repo novelty survived but the kernel was incremental against ambiguous-timing/misclassified DiD comparators, especially Denteh-Kedagni 2026; pivot budget should move to a stronger topic.

## Key files

- `pid_interval_censored_adoption_v1_state.json` â€” pipeline state at banking (`banked: true`).
- `pid_interval_censored_adoption_v1_proposal.tex` â€” final proposal version.
- `pid_interval_censored_adoption_v1.tex` â€” derivation note (if Stage 0 ran).
- `pid_interval_censored_adoption_v1_reviews.jsonl` â€” per-round reviewer log (Stage -0.5 and Stage 0.5).
- `pid_interval_censored_adoption_v1_reviews/` â€” per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
