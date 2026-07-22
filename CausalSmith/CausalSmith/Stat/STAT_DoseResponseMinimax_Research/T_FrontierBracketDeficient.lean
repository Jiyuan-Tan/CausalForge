/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Dose-response minimax: certified deficient-covariate regime theorem

Stage-2 scaffold. The certified regime theorem `thm:frontier-bracket-deficient`
(`0 < s < d/4`): the all-β lower floor together with the strictly-smaller deficient
`ρ_n` exponent; the same-class upper endpoint is NOT discharged. Every proof body
is `sorry`.
-/

import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.Helpers.TwoPointConstruction
import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.Helpers.RateAlgebra

namespace CausalSmith.Stat.DoseResponseMinimax

-- @node: thm:frontier-bracket-deficient
/-- Certified deficient-covariate regime theorem. Assume the strict-slack baseline.
For every `β > 0` and every `0 < s < d/4` (`4s < d`) there is `c > 0` such that,
for all sufficiently large `n`, `R_n ≥ c n^{-2α/(2α+1)}`, while
`ρ_n = n^{-2/(1+d/(4s)+1/α)}` has a strictly smaller exponent. The same-class upper
endpoint `C ρ_n` is NOT discharged. -/
theorem frontier_bracket_deficient {d : ℕ}
    (alpha beta s M c0 eps0 t0 : ℝ)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hs : 0 < s)
    (hreg : RegimeConstants alpha beta s M c0 eps0 t0)
    (hsd : 4 * s < (d : ℝ))
    (hslack : BaselineSubmodelSlack d beta s M c0 eps0 t0) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop,
      c * (n : ℝ) ^ (-(2 * alpha / (2 * alpha + 1)))
          ≤ minimaxRisk M n (HolderDoseClass d alpha beta s M c0 eps0 t0) t0
        ∧ publishedHoifRate n alpha s d
            = (n : ℝ) ^ (-(2 / (1 + (d : ℝ) / (4 * s) + 1 / alpha)))
        ∧ 2 / (1 + (d : ℝ) / (4 * s) + 1 / alpha) < 2 * alpha / (2 * alpha + 1) := by
  rcases oracle_dose_regression_lower_all_beta alpha beta s M c0 eps0 t0
    halpha hbeta hs hreg hslack with ⟨c, hc, hfloor⟩
  refine ⟨c, hc, ?_⟩
  filter_upwards [hfloor, Filter.eventually_ge_atTop (1 : ℕ)] with n hn hge
  rcases rho_deficient_regime_algebra n alpha s d halpha hs hsd hge with ⟨hrho, hexp⟩
  exact ⟨hn, hrho, hexp⟩

end CausalSmith.Stat.DoseResponseMinimax
