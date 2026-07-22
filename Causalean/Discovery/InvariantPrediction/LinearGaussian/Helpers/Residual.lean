/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Discovery.InvariantPrediction.LinearGaussian.Regression

/-!
# Invariant Causal Prediction — residual equals the target noise

Algebraic helper lemmas for the completeness proof: with the *causal* coefficient
`γ* = β₀,·`, the regression residual `Y − Σ_k γ*_k X_k` equals the target noise
`ε₀` a.e. in every environment.

* `obsResidual_eq_eps` — observational block: from `hε` at the target row.
* `envResidual_eq_eps` — interventional block: from `hDoStruct` at the target
  (the target is never intervened on, so it keeps its structural equation).

Both use that the target's own coefficient is `0` (`hNoSelf`) to turn the
`Σ_{k≠0}` of the structural equation into the full `Σ_k` of the residual.
-/

namespace Causalean.Discovery.InvariantPrediction.LinearGaussian

open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {p : ℕ}

/-- The **causal coefficient** `γ* = β₀,·` (row `0` of `β`). -/
def causalCoeff (M : ObsSEM p) : Fin (p + 1) → ℝ := fun k => M.β (target p) k

/-- With the causal coefficient, the full-sum `Σ_k β₀ₖ X_k` equals the
structural-equation sum `Σ_{k≠0} β₀ₖ X_k`, since `β₀₀ = 0`. -/
theorem sum_causalCoeff_eq (M : ObsSEM p) (x : Fin (p + 1) → ℝ) :
    ∑ k, M.β (target p) k * x k
      = ∑ k ∈ Finset.univ.erase (target p), M.β (target p) k * x k := by
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (target p))]
  simp [M.hNoSelf (target p)]

/-- **Observational residual is the target noise.**  With `γ = γ* = β₀,·`, the
observational residual `Y − Σ_k β₀ₖ X_k` equals `ε₀` a.e. -/
theorem obsResidual_eq_eps (M : ObsSEM p) :
    ∀ᵐ ω ∂M.P, obsResidual M (causalCoeff M) ω = M.ε ω (target p) := by
  filter_upwards [M.hε] with ω hω
  simp only [obsResidual, causalCoeff, sum_causalCoeff_eq M (M.X ω), hω (target p)]

/-- **Interventional residual is the target noise.**  Since the target is never
intervened on (`hAtarget`), it keeps its structural equation (`hDoStruct`), so the
environment residual `Yᵉ − Σ_k β₀ₖ Xₖᵉ` equals `ε₀` a.e. -/
theorem envResidual_eq_eps (M : ObsSEM p) (e : Env M) :
    ∀ᵐ ω ∂M.P, envResidual e (causalCoeff M) ω = M.ε ω (target p) := by
  filter_upwards [e.hDoStruct (target p) e.hAtarget] with ω hω
  simp only [envResidual, causalCoeff, sum_causalCoeff_eq M (e.X ω), hω]
  ring

end Causalean.Discovery.InvariantPrediction.LinearGaussian
