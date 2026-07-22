/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Dose-response minimax: the certified kernel pointwise lower bound

Stage-2 scaffold. The certified kernel theorem `thm:sharp-pointwise-lower-bound`:
a thin assembly of the crux two-point construction
`lem:oracle-dose-regression-lower-all-beta` on the Hölder dose-response class with
the slack baseline. Every proof body is `sorry`.
-/

import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.Helpers.TwoPointConstruction

namespace CausalSmith.Stat.DoseResponseMinimax

-- @node: thm:sharp-pointwise-lower-bound
/-- Certified kernel converse. Assume the strict-slack baseline. For every `β > 0`
there is `c > 0`, depending only on the fixed model radii and the slack baseline,
such that for all sufficiently large `n`,
`R_n(P_{α,β,s}(M,c_0,ε_0,t_0), t_0) ≥ c n^{-2α/(2α+1)}` — the classical interior
treatment-regression pointwise rate, uniformly over every `β > 0`. -/
theorem sharp_pointwise_lower_bound {d : ℕ}
    (alpha beta s M c0 eps0 t0 : ℝ)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hs : 0 < s)
    (hreg : RegimeConstants alpha beta s M c0 eps0 t0)
    (hslack : BaselineSubmodelSlack d beta s M c0 eps0 t0) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop,
      c * (n : ℝ) ^ (-(2 * alpha / (2 * alpha + 1)))
        ≤ minimaxRisk M n (HolderDoseClass d alpha beta s M c0 eps0 t0) t0 := by
  exact oracle_dose_regression_lower_all_beta alpha beta s M c0 eps0 t0
    halpha hbeta hs hreg hslack

end CausalSmith.Stat.DoseResponseMinimax
