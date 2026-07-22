/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Dose-response minimax: certified smooth-covariate regime theorem

Stage-2 scaffold. The certified regime theorem `thm:sharp-minimax-smooth-covariate`
(`s ≥ d/4`): the certified lower floor lands on the same exponent as the published
benchmark `ρ_n`, with NO matching same-class upper claim. Every proof body is
`sorry`.
-/

import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.T_SharpPointwiseLowerBound
import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.Helpers.RateAlgebra

namespace CausalSmith.Stat.DoseResponseMinimax

-- @node: thm:sharp-minimax-smooth-covariate
/-- Certified smooth-covariate regime theorem. Assume the strict-slack baseline.
For every `β > 0` and every `s ≥ d/4` (`d ≤ 4s`) there is `c > 0` such that, for
all sufficiently large `n`, `R_n ≥ c n^{-2α/(2α+1)} = c ρ_n`. The certified lower
floor lands on the same exponent as `ρ_n`; NO same-class upper bound is claimed. -/
theorem sharp_minimax_smooth_covariate {d : ℕ}
    (alpha beta s M c0 eps0 t0 : ℝ)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hs : 0 < s)
    (hreg : RegimeConstants alpha beta s M c0 eps0 t0)
    (hsd : (d : ℝ) ≤ 4 * s)
    (hslack : BaselineSubmodelSlack d beta s M c0 eps0 t0) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop,
      c * (n : ℝ) ^ (-(2 * alpha / (2 * alpha + 1)))
          ≤ minimaxRisk M n (HolderDoseClass d alpha beta s M c0 eps0 t0) t0
        ∧ (n : ℝ) ^ (-(2 * alpha / (2 * alpha + 1))) = publishedHoifRate n alpha s d := by
  rcases sharp_pointwise_lower_bound alpha beta s M c0 eps0 t0
    halpha hbeta hs hreg hslack with ⟨c, hc, hfloor⟩
  refine ⟨c, hc, ?_⟩
  filter_upwards [hfloor, Filter.eventually_ge_atTop (1 : ℕ)] with n hn hge
  have hrho := rho_oracle_regime_algebra n alpha s d halpha hs hsd hge
  exact ⟨hn, hrho.symm⟩

end CausalSmith.Stat.DoseResponseMinimax
