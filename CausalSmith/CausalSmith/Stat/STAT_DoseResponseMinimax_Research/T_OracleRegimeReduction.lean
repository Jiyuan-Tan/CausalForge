/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Dose-response minimax: oracle regime reduction

Stage-2 scaffold. The proposition `prop:oracle-regime-reduction`: in the
smooth-covariate regime `s ≥ d/4`, `ρ_n` collapses to the oracle exponent and the
certified lower floor reduces to the classical interior pointwise nonparametric
regression barrier. Every proof body is `sorry`.
-/

import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.T_SharpPointwiseLowerBound
import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.Helpers.RateAlgebra

namespace CausalSmith.Stat.DoseResponseMinimax

-- @node: prop:oracle-regime-reduction
/-- Oracle regime reduction. Under the assumptions of
`sharp_pointwise_lower_bound`, if `s ≥ d/4` (`d ≤ 4s`) then `ρ_n = n^{-2α/(2α+1)}`
and hence `R_n ≥ c n^{-2α/(2α+1)} = c ρ_n` for some `c > 0`. The certified lower
floor reduces to the classical interior pointwise nonparametric regression
barrier. -/
theorem oracle_regime_reduction {d : ℕ}
    (alpha beta s M c0 eps0 t0 : ℝ)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hs : 0 < s)
    (hreg : RegimeConstants alpha beta s M c0 eps0 t0)
    (hsd : (d : ℝ) ≤ 4 * s)
    (hslack : BaselineSubmodelSlack d beta s M c0 eps0 t0) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop,
      publishedHoifRate n alpha s d = (n : ℝ) ^ (-(2 * alpha / (2 * alpha + 1)))
        ∧ c * publishedHoifRate n alpha s d
            ≤ minimaxRisk M n (HolderDoseClass d alpha beta s M c0 eps0 t0) t0 := by
  rcases sharp_pointwise_lower_bound alpha beta s M c0 eps0 t0
    halpha hbeta hs hreg hslack with ⟨c, hc, hfloor⟩
  refine ⟨c, hc, ?_⟩
  filter_upwards [hfloor, Filter.eventually_ge_atTop (1 : ℕ)] with n hn hge
  have hrho := rho_oracle_regime_algebra n alpha s d halpha hs hsd hge
  constructor
  · exact hrho
  · rw [hrho]
    exact hn

end CausalSmith.Stat.DoseResponseMinimax
