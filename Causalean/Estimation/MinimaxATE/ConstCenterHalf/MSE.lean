/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Structure-agnostic ATE lower bound: the expected-risk (MSE) form

The paper (Jin–Syrgkanis 2024) states its minimax lower bound in the **quantile**
form (the `(1−γ)`-quantile of the squared error, eq. for `𝔐ⁿ,γ`), which is
exactly the probability-of-miss bound `minimax_lower_bound`
(`1/4 ≤ minimaxMiss …` is the case `γ = 3/4`).  The paper notes this quantile bound
is *stronger* than, and **implies**, the expected-risk (MSE) lower bound used by
Balakrishnan et al.: `𝔐ⁿ,γ ≥ ρ ⟹` minimax `𝔼`-risk `≥ (1−γ)ρ`.

This file makes that implication explicit and mechanical via the Chebyshev/Markov
bridge `nMiss_sq_le_nMSE`: every estimator has mean-squared error at least
`s²/4 ≍ εg·εm` on **some** in-class DGP, where `s = β(α+β)/(1−4β²)`.

The witness DGP is extracted from the two-point bound `1/4 ≤ max(…)`: either the
null estimate `(m̂, ĝ)` itself (left branch) or a single Rademacher-perturbed DGP
(right branch, pulled out of the uniform mixture `Qtrue` by `exists_real_ge_mixture`,
since a finite average is `≤` its maximal component).
-/

import Causalean.Estimation.MinimaxATE.ConstCenterHalf.ChiSquaredCore

/-! # Mean-Squared-Error Lower Bound

This file converts the structure-agnostic average treatment effect lower bound from a
probability-of-miss statement into an expected mean-squared-error statement. The theorem
`minimax_lower_bound_mse` combines `minimax_lower_bound` with the Chebyshev bridge
`nMiss_sq_le_nMSE` and extracts a single in-class witness DGP from either the null law or the
uniform perturbed mixture.

The result isolates the finite-model argument showing that the doubly-robust product rate is an
unavoidable expected-risk floor for some data-generating process in the nuisance class. -/

namespace Causalean.Estimation.MinimaxATE

open MeasureTheory
open Causalean.Stat
open scoped ENNReal BigOperators

variable {K n : ℕ} {α β εg εm : ℝ}

/-- **Structure-agnostic minimax lower bound, expected-risk (MSE) form.**  Under the
same hypotheses as `minimax_lower_bound`, every measurable estimator has
mean-squared error at least `s²/4` (with `s = β(α+β)/(1−4β²) ≍ √(εg·εm)`) on **some**
DGP in the class — the doubly-robust product rate `εg·εm` is an unbeatable
expected-squared-error floor.  This is the weaker, `(1−γ)`-factored consequence
(`γ = 3/4`) of the quantile bound, in the form used by Balakrishnan et al. -/
theorem minimax_lower_bound_mse [NeZero K]
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α + 2 * β ≤ 1 / 2)
    (hm : β ^ 2 ≤ εm) (hg : (α + β) ^ 2 / (1 - 2 * β) ^ 2 ≤ εg)
    (hεg : 0 ≤ εg) (hεm : 0 ≤ εm)
    (hγ : 2 * (α ^ 2 + 2 * α * β + 3 * β ^ 2) ≤ 1)
    (hreg : 2 * (n : ℝ) ^ 2 * (α ^ 2 + 2 * α * β + 3 * β ^ 2) ^ 2 ≤ (K : ℝ) * Real.log 2)
    {est : (Fin n → Obs (Fin K × Bool)) → ℝ} (hest : Measurable est) :
    ∃ p : InClassDGP mhat ghat εg εm,
      (β * (α + β) / (1 - 4 * β ^ 2)) ^ 2 / 4 ≤ nMSE p.2.valid n est := by
  set s := β * (α + β) / (1 - 4 * β ^ 2) with hs_def
  have hβ4 : β ≤ 1 / 4 := by linarith
  have hden : (0 : ℝ) < 1 - 4 * β ^ 2 := by nlinarith
  have hαβ0 : (0 : ℝ) ≤ α + β := by linarith
  have hs0 : 0 ≤ s := by rw [hs_def]; positivity
  haveI : IsProbabilityMeasure (Qfalse K n) := Qfalse_isProb K n
  haveI : IsProbabilityMeasure (Qtrue (K := K) hα hβ hαβ n) := Qtrue_isProb hα hβ hαβ n
  haveI : ∀ lam : Fin K → Bool, IsProbabilityMeasure (Qpert hα hβ hαβ n lam) :=
    fun lam => Qpert_isProb hα hβ hαβ n lam
  -- From `1/4 ≤ nMiss` on an in-class DGP (at its own ATE `θ`), Chebyshev gives MSE `≥ s²/4`.
  have hkey : ∀ {m : Fin K × Bool → ℝ} {g : Bool → Fin K × Bool → ℝ}
      (hin : InClass mhat ghat εg εm m g) (θ : ℝ), ate g = θ →
      1 / 4 ≤ (productLaw hin.valid n).real {x | s ≤ |est x - θ|} →
      ∃ p : InClassDGP mhat ghat εg εm, s ^ 2 / 4 ≤ nMSE p.2.valid n est := by
    intro m g hin θ hθ h14
    refine ⟨⟨(m, g), hin⟩, ?_⟩
    have hcheb : s ^ 2 * (productLaw hin.valid n).real {x | s ≤ |est x - θ|}
        ≤ nMSE hin.valid n est := by
      have h := nMiss_sq_le_nMSE hin.valid n (est := est) hs0
      unfold nMiss at h
      rwa [hθ] at h
    have h1 := mul_le_mul_of_nonneg_left h14 (sq_nonneg s)
    change s ^ 2 / 4 ≤ nMSE hin.valid n est
    calc s ^ 2 / 4 = s ^ 2 * (1 / 4) := by ring
      _ ≤ s ^ 2 * (productLaw hin.valid n).real {x | s ≤ |est x - θ|} := h1
      _ ≤ nMSE hin.valid n est := hcheb
  -- Two-point bound: `1/4 ≤ max(null miss, mixture miss)`.
  have htv := tvDist_Qfalse_Qtrue_le_half (K := K) (n := n) hα hβ hαβ hγ hreg
  have hsep : 2 * s ≤ |(0 : ℝ) - 2 * β * (α + β) / (1 - 4 * β ^ 2)| := by
    rw [zero_sub, abs_neg, abs_of_nonneg (by positivity)]
    rw [hs_def]; apply le_of_eq; ring
  have hmax := two_point_lower_bound_of_tvDist_le
    (P₀ := Qfalse K n) (P₁ := Qtrue hα hβ hαβ n) hest hsep htv
  rw [show (1 - (1 : ℝ) / 2) / 2 = 1 / 4 by norm_num] at hmax
  rcases le_max_iff.mp hmax with hleft | hright
  · -- null branch: `(m̂, ĝ)` is in class, `ate ĝ = 0`
    exact hkey (inClass_null hεg hεm) 0 ate_ghat hleft
  · -- mixture branch: extract a single Rademacher-perturbed DGP
    obtain ⟨lam, hlam⟩ := exists_real_ge_mixture (signWeight K) (signWeight_sum K)
      (fun l => Qpert hα hβ hαβ n l)
      {x | s ≤ |est x - 2 * β * (α + β) / (1 - 4 * β ^ 2)|}
    exact hkey (inClass_perturbed hα hβ hαβ hm hg lam)
      (2 * β * (α + β) / (1 - 4 * β ^ 2)) (ate_gPerturbed hα hβ hαβ lam)
      (le_trans hright hlam)

end Causalean.Estimation.MinimaxATE
