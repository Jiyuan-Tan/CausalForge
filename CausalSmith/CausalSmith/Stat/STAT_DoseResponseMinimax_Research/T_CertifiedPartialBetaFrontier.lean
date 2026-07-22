/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Certified partial beta frontier

Stage-2 scaffold for the authoritative manual resolution replacing the former
open-ended residual. The theorem records only the certified lower floor and the
two regime comparisons; it asserts no same-class upper endpoint.
-/

import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.Frontier

namespace CausalSmith.Stat.DoseResponseMinimax

-- @node: thm:certified-partial-beta-frontier
/-- Under baseline-submodel slack, every fixed `beta > 0` has the oracle lower
floor eventually. In the smooth-covariate regime the floor matches the published
`rho_n` exponent; in the deficient regime the published comparator has a strictly
smaller exponent and no same-class upper endpoint is asserted. -/
theorem certifiedPartialBetaFrontier {d : ℕ}
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
              publishedHoifRate n alpha s d
                = (n : ℝ) ^ (-(2 * alpha / (2 * alpha + 1))))
          ∧ (4 * s < (d : ℝ) →
              publishedHoifRate n alpha s d
                  = (n : ℝ) ^ (-(2 / (1 + (d : ℝ) / (4 * s) + 1 / alpha)))
                ∧ 2 / (1 + (d : ℝ) / (4 * s) + 1 / alpha)
                    < 2 * alpha / (2 * alpha + 1))) := by
  exact certified_beta_frontier_bracket alpha beta s M c0 eps0 t0
    halpha hbeta hs hreg hslack

end CausalSmith.Stat.DoseResponseMinimax
