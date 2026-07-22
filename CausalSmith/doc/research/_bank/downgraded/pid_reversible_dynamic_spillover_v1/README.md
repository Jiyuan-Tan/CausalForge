---
qid: pid_reversible_dynamic_spillover
spec: v1
topic: "Sharp identification of the long-run average treatment effect in a discrete-time panel where treatment is reversible (non-absorbing) and dynamic spillovers between consecutive treatment spells are bounded by an explicit scalar parameter: a closed-form sequence of nested g-formulas characterizing the identified set as a function of the spillover bound, recovering the Robins (1986) g-formula point identification when the bound is zero and the unrestricted Manski-style bounds when the bound is infinite, with a sharpness witness in the form of two extremal joint laws that saturate each face of the identified set; extends Han-Yao-Hsu (2024) absorbing-treatment dynamic identification to the reversible regime explicitly left open in their conclusion"
novelty_target: flagship
tier_at_proposal: NO-PASS
tier_at_derivation: NA
proposal_promise_gap: null  # confirmed null: died at proposal gate, no D0 derivation ⇒ no promise gap to measure
reusable: unknown  # confirmed unknown: solver never ran (not solver_blocked); proposal itself never stabilized to flagship (not a clean not_reusable)
reraise_status: re-raise
gap_reasons:
  # Source: pid_reversible_dynamic_spillover_v1_reviews/*.json (per-version reviewer JSON).
  # Two persistent objection clusters across all 3 angles: novelty-below-flagship and C-wellposed.
  # --- novelty (kernel reads as generic convex-analysis, not a regime-opening causal result) ---
  - "tier=field below novelty_target=flagship; to reach flagship, the kernel needs a causal sharp-bound object that is not just a generic compact-set face-stability criterion, or a named wider-class extension left open by prior literature."
  - "no cited paper leaves this reversible-spell Lipschitz sharpness regime open, so the current kernel reads as a new sensitivity construction rather than a flagship-eligible strict extension or regime opening."
  - "The stationary reward support formula is already standard Markov reward/occupation-measure algebra in Puterman1994 and Altman1999; keep it as background, not a novelty-bearing theorem."
  - "The claimed no-free-stationary-summary warning names KalouptsidiKitamuraLimaSouzaRodrigues2020 and DuarteFinkelsteinKnoxMummoloShpitser2024 as finite sharp-bounds workflows, but neither is shown to publish the extrapolation being refuted." # N-strawman, recurring on Conjecture 2
  - "missing closer comparators: van den Berg and Vikstrom 2022 (Econometrica, 'Long-Run Effects of Dynamically Assigned Treatments'); Kim, Kwon, Kwon, Lee 2018 (QE, Lipschitz partial-ID); Bojinov, Rambachan, Shephard 2021 (QE, dynamic path effects)." # N-thin-survey
  # --- C-wellposed (definitional flaws that block a clean derivation gate) ---
  - "no projection/lifting map identifies faces of the finite compatibility polytopes with faces of the stationary reward correspondence." # face-stability undefined
  - "The rho=0 reduction does not recover the standard Robins g-formula: because the current-treatment mismatch is multiplied by rho, rho=0 forces all observed support outcome regressions at a state to be equal." # sanity reduction fails
  - "The observed support set O_t(h_t) is not typed precisely ... so mu_t^P(w) and d_sp(v,w) are not unambiguously defined on the same objects."
  - "The locked observable law P is a finite-T panel law, but the long-run Cesaro statement and stationary Bellman equations require an infinite stationary process or a compatible sequence P_T."
  - "Endpoint interval convergence does not imply Hausdorff-Cauchy convergence of the full embedded polytopes or faces; objective-null coordinates can oscillate while lower/upper support values converge."
reusable_artifacts:
  # TODO: list LP setup / operator / witness / literature_map /
  # counterexample paths inside this directory that future runs should
  # lift rather than re-derive.
seeds_burned: []
proof_attempt_summary: |
  Proposed a closed-form, spillover-bounded sharp identified set for the long-run ATE in a reversible
  (non-absorbing) dynamic panel — an iff "finite-window endpoint-diameter" frontier (Conjecture 1) for when
  finite reversible-spell sharp intervals converge to a stationary identified set, plus a block-switching
  "endpoint-cycling" witness against any stationary summary (Conjecture 2). Killed at the proposal/novelty gate
  (D-0.5): across 3 angles and ~5 revisions each, reviewers repeatedly capped it at field/letter — the core kernel
  kept reading as generic compact-convex / support-function stability (Schneider1993, RockafellarWets1998,
  Puterman1994/Altman1999) in causal dress rather than a flagship regime-opening result, Conjecture 2 was flagged
  N-strawman (named workflows it claimed to refute don't publish that extrapolation), and several C-wellposed flaws
  persisted (face-comparison map undefined; rho=0 doesn't recover the Robins g-formula; finite-T law vs. infinite
  stationary process mismatch; endpoint convergence not equal to Hausdorff/face convergence). The math was never
  derived — no D0 derivation ran.
banked_on: "2026-05-20"
---

# pid_reversible_dynamic_spillover / v1 — Downgraded

**Topic.** Sharp identification of the long-run average treatment effect in a discrete-time panel where treatment is reversible (non-absorbing) and dynamic spillovers between consecutive treatment spells are bounded by an explicit scalar parameter: a closed-form sequence of nested g-formulas characterizing the identified set as a function of the spillover bound, recovering the Robins (1986) g-formula point identification when the bound is zero and the unrestricted Manski-style bounds when the bound is infinite, with a sharpness witness in the form of two extremal joint laws that saturate each face of the identified set; extends Han-Yao-Hsu (2024) absorbing-treatment dynamic identification to the reversible regime explicitly left open in their conclusion

**Novelty target.** flagship

**D-0.5 verdict.** NO-PASS

**D0.5 verdict.** NA

**Banking reason.** D-0.5 NO-PASS: 3 angles capped at field/letter tier; proposal didn't anchor on a cited open-problem statement so the reviewer never agreed the topic clears flagship novelty.

## Key files

- `pid_reversible_dynamic_spillover_v1_state.json` — pipeline state at banking (`banked: true`).
- `pid_reversible_dynamic_spillover_v1_proposal.tex` — final proposal version.
- `pid_reversible_dynamic_spillover_v1.tex` — derivation note (if D0 ran).
- `pid_reversible_dynamic_spillover_v1_reviews.jsonl` — per-round reviewer log (D-0.5 and D0.5).
- `pid_reversible_dynamic_spillover_v1_reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
