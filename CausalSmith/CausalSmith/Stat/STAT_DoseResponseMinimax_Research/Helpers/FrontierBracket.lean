/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Dose-response minimax: certified β-frontier bracket

Stage-2 scaffold. The certified frontier-bracket assembly
`lem:certified-beta-frontier-bracket`: the all-β lower floor
(`thm:sharp-pointwise-lower-bound`) together with the regime-by-regime `ρ_n`
algebra. Packages NO same-class upper theorem. Feeds the `oeq` Prop. Every proof
body is `sorry`.
-/

import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.T_SharpPointwiseLowerBound
import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.Helpers.RateAlgebra

namespace CausalSmith.Stat.DoseResponseMinimax

-- @node: lem:certified-beta-frontier-bracket
/-- Certified β-frontier bracket. Assume the strict-slack baseline. For every
`β > 0` there is `c > 0` with `R_n ≥ c n^{-2α/(2α+1)}` eventually; and — for EVERY
`n ≥ 1`, not merely eventually, matching the note's unconditional `ρ_n` algebra —
in the smooth-covariate regime `s ≥ d/4` (`d ≤ 4s`) the benchmark `ρ_n` collapses
to that oracle exponent, while in the deficient regime `0 < s < d/4` (`4s < d`)
`ρ_n` has a strictly smaller exponent. The regime identities are stated outside the
`∀ᶠ n` (eventually) clause so they are NOT weakened to large `n` only. No same-class
upper endpoint is packaged. -/
lemma certified_beta_frontier_bracket {d : ℕ}
    (alpha beta s M c0 eps0 t0 : ℝ)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hs : 0 < s)
    (hreg : RegimeConstants alpha beta s M c0 eps0 t0)
    (hslack : BaselineSubmodelSlack d beta s M c0 eps0 t0) :
    ∃ c : ℝ, 0 < c ∧
      (∀ᶠ n : ℕ in Filter.atTop,
        c * (n : ℝ) ^ (-(2 * alpha / (2 * alpha + 1)))
          ≤ minimaxRisk M n (HolderDoseClass d alpha beta s M c0 eps0 t0) t0)
      ∧ (∀ n : ℕ, 1 ≤ n →
          ((d : ℝ) ≤ 4 * s →
              publishedHoifRate n alpha s d = (n : ℝ) ^ (-(2 * alpha / (2 * alpha + 1))))
          ∧ (4 * s < (d : ℝ) →
              publishedHoifRate n alpha s d
                  = (n : ℝ) ^ (-(2 / (1 + (d : ℝ) / (4 * s) + 1 / alpha)))
                ∧ 2 / (1 + (d : ℝ) / (4 * s) + 1 / alpha) < 2 * alpha / (2 * alpha + 1))) := by
  rcases sharp_pointwise_lower_bound alpha beta s M c0 eps0 t0
    halpha hbeta hs hreg hslack with ⟨c, hc, hfloor⟩
  refine ⟨c, hc, hfloor, ?_⟩
  intro n hge
  refine ⟨?_, ?_⟩
  · intro hsd
    exact rho_oracle_regime_algebra n alpha s d halpha hs hsd hge
  · intro hsd
    exact rho_deficient_regime_algebra n alpha s d halpha hs hsd hge

end CausalSmith.Stat.DoseResponseMinimax
