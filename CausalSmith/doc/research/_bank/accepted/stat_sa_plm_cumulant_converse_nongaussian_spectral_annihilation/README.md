---
qid: stat_sa_plm_cumulant_converse
spec: nongaussian_spectral_annihilation
topic: "Develop and audit an effective fixed-separation minimax theory for non-Gaussian partially linear models using complex moment-generating-function zeros. Prove the exact learned-residual factorization and contour-identification identities; derive a numerical zero-localization radius from the exact Luxemburg sub-Gaussian convention; and construct an explicit once-for-all translated-dyadic uniformly conditioned contour bank with a positive dyadic modulus computable from certified-real names of the displayed primitive class constants, without access to the unknown treatment-noise law. Show that the resulting total certified split-sample statistic attains uniform Θ(n^{-1}) MSE under sufficiently small fixed direct L^1(P_X) treatment-code error without an outcome learner. Retain the exact Jin–Mackey–Syrgkanis Theorem 5.4 ACE upper comparison only on the explicit narrower comparison subclass. Treat the bounded-Y Gaussian calculation solely as a source-assumption diagnostic showing that the simultaneous assumptions stated around their Theorem 3.2 force θ_0=0, not as a Gaussian-versus-non-Gaussian minimax dichotomy. Leave the shrinking-separation phase diagram, adaptive switching, uniform inference, and matching local lower bounds open. Position the effective fixed-separation result narrowly against higher-order OML, location-family completeness and zero testing, spectral GMM, ICA treatment-effect estimation, and weak-non-Gaussian inference without claiming that transform zeros themselves are new."
novelty_target: field
banked_novelty_tier: field
tier_at_proposal: ACCEPT
tier_at_derivation: PASS
proposal_promise_gap: "kernel_substituted"
reusable: solver_blocked
reraise_status: unknown
gap_reasons: []
reusable_artifacts: []
seeds_burned: []
proof_attempt_summary: |
  The run proved the fixed-separation transform-zero identification and matched
  n^-1 minimax-risk theory, together with the stated ACE comparison and Gaussian
  diagnostic, and passed the dual-model convergence review with no proof holes.
  The shrinking-separation local minimax frontier, adaptive switching, and
  uniform inference remain open by design.
banked_on: "2026-08-15"
paper_score: 6.2
paper_score_rationale: "The verified core is substantial and potentially publishable, but the manuscript needs serious tightening of scope, naming, exposition, and several claim-fidelity repairs before it reads like a journal submission."
---

# stat_sa_plm_cumulant_converse / nongaussian_spectral_annihilation — Accepted

**Topic.** Develop and audit an effective fixed-separation minimax theory for non-Gaussian partially linear models using complex moment-generating-function zeros. Prove the exact learned-residual factorization and contour-identification identities; derive a numerical zero-localization radius from the exact Luxemburg sub-Gaussian convention; and construct an explicit once-for-all translated-dyadic uniformly conditioned contour bank with a positive dyadic modulus computable from certified-real names of the displayed primitive class constants, without access to the unknown treatment-noise law. Show that the resulting total certified split-sample statistic attains uniform Θ(n^{-1}) MSE under sufficiently small fixed direct L^1(P_X) treatment-code error without an outcome learner. Retain the exact Jin–Mackey–Syrgkanis Theorem 5.4 ACE upper comparison only on the explicit narrower comparison subclass. Treat the bounded-Y Gaussian calculation solely as a source-assumption diagnostic showing that the simultaneous assumptions stated around their Theorem 3.2 force θ_0=0, not as a Gaussian-versus-non-Gaussian minimax dichotomy. Leave the shrinking-separation phase diagram, adaptive switching, uniform inference, and matching local lower bounds open. Position the effective fixed-separation result narrowly against higher-order OML, location-family completeness and zero testing, spectral GMM, ICA treatment-effect estimation, and weak-non-Gaussian inference without claiming that transform zeros themselves are new.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** PASS

**Banking reason.** F5 clean after dual-model convergence review; Lean build green with no proof holes.

## Key files

- `state.json` — pipeline state at banking (`banked: true`).
- `discovery/proposal.tex` — final proposal version.
- `discovery/writeup.tex` — derivation note (if Stage 0 ran).
- `reviews/reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `reviews/` — per-version reviewer JSON files (if present).

## Notes

F7 found no helper ready for upstream promotion. The strongest watchlist items
are the model-free Luxemburg-to-MGF bridge, the nonduplicate Blaschke/Jensen
closure, and the analytic core of `Helpers/UniformDiskSeries.lean`. They remain
paper-local because they currently have no consumer outside this run; the full
uniform-disk file also contains an unused theorem and wrappers around already
promoted IID results. The local certified-complex/transcendental stack was not
promoted because Causalean already provides neighboring certified-contour APIs
with different algorithms, so copying it would create competing primitives.
