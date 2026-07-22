/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Stat.Nonparametric.LocalPoly.Bias
import Causalean.Stat.Nonparametric.LocalPoly.SmootherVariance
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Interior local-polynomial estimator risk: bias and stochastic-`L²` bounds

Conditional local-polynomial estimator risk bounds, assembling interior bias and stochastic `L²`
estimates for the windowed pointwise estimator.

This module assembles the conditional-on-design bias / variance bounds
(`localPoly_intercept_bias`, `localPoly_intercept_variance_le`) and the **bandwidth-free
density-constant leverage facts** produced by `DensityLeverage`:

* `localPoly_estimatorBias_window` — `estimatorBias = |ĉ₀ − f(t)| ≤ Cbias · h^β` with the explicit
  constant `Cbias = (MH/p!) · L`, where `p = holderDerivOrder β` and
  `L = √(2·cInv·(cTop+1))` is the bandwidth-free leverage
  bound (`MH` the Hölder constant). The `ℓ¹` leverage `∑ᵢ|Sᵢ|` is squeezed by
  `(∑ᵢ|Sᵢ|)² ≤ M₀₀·(M⁻¹)₀₀ ≤ L²` (`equivKernelWeight_abs_sum_sq_le`).
* `localPoly_estimatorStochL2` — `estimatorStochL2 = √Var(ĉ₀) ≤ Cvar · (Nh)^{-1/2}` with the
  explicit constant `Cvar = √(2σ²·W·cInv)`, from `Var ≤ σ²·W·(M⁻¹)₀₀` and the leverage rate
  `(M⁻¹)₀₀ ≤ 2·cInv/(Nh)`.

Both bounds hold conditionally on the design (equivalently, on the high-probability good design
event of `designMatrix_inv_concentration`): once the leverage rate is supplied, the estimator risk
reduces to a deterministic bias bound plus a conditional variance bound. The leverage constants
`cInv`, `cTop` are the explicit density + kernel-moment quantities of
`localPoly_density_inv00_rate` / `localPoly_density_leverage_bound`, so no `S`-level matrix
hypothesis remains.
-/

namespace Causalean.Stat.Nonparametric

open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- **Interior local-polynomial estimator bias `≤ Cbias · h^β`.** Let `ĉ₀ = c 0` be the
degree-`p = holderDerivOrder β` weighted least-squares intercept fit of a
`β`-Hölder function `f` (Hölder constant
`MH`) at noise-free responses, with invertible design moment matrix and all design points within
bandwidth `h` of `t`. If the bandwidth-free leverage bound `√(M₀₀·(M⁻¹)₀₀) ≤ L` holds (`0 ≤ L`,
supplied by `localPoly_density_leverage_bound`), then the conditional bias obeys

`|ĉ₀ − f(t)| ≤ (MH/p!) · L · h^β`,

the standard local-polynomial bias rate with constant `Cbias = (MH/p!) · L`. -/
theorem localPoly_estimatorBias_window {N : ℕ} {β MH lo hi t h L : ℝ} {a w : Fin N → ℝ}
    {f : ℝ → ℝ} {c : Fin ((holderDerivOrder β) + 1) → ℝ}
    (hβ : 0 < β) (hMH : 0 ≤ MH) (hh : 0 ≤ h) (hw : ∀ i, 0 ≤ w i)
    (ht : t ∈ Set.Icc lo hi) (ha : ∀ i, a i ∈ Set.Icc lo hi)
    (hwin : ∀ i, |a i - t| ≤ h)
    (hf : ContDiff ℝ (holderDerivOrder β) f)
    (hb : ∀ x ∈ Set.Icc lo hi, ∀ y ∈ Set.Icc lo hi,
            |iteratedDeriv (holderDerivOrder β) f x - iteratedDeriv (holderDerivOrder β) f y|
              ≤ MH * |x - y| ^ (β - ((holderDerivOrder β) : ℝ)))
    (hMdet : IsUnit (designMatrix (holderDerivOrder β) (fun i => a i - t) w).det)
    (hmin : ∀ c' : Fin ((holderDerivOrder β) + 1) → ℝ,
        (∑ i, w i * (f (a i) - ∑ j, c j * (a i - t) ^ (j : ℕ)) ^ 2)
          ≤ ∑ i, w i * (f (a i) - ∑ j, c' j * (a i - t) ^ (j : ℕ)) ^ 2)
    (hlev : Real.sqrt ((designMatrix (holderDerivOrder β) (fun i => a i - t) w) 0 0
        * (designMatrix (holderDerivOrder β) (fun i => a i - t) w)⁻¹ 0 0) ≤ L) :
    |c 0 - f t| ≤ (MH / ((holderDerivOrder β)).factorial) * L * h ^ β := by
  have hbias := localPoly_intercept_bias hβ hMH hw ht ha hwin hf hb hMdet hmin
  set s := ∑ i, |equivKernelWeight (holderDerivOrder β) (fun i => a i - t) w i| with hs
  have hs_nn : 0 ≤ s := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hsq : s ^ 2
      ≤ (designMatrix (holderDerivOrder β) (fun i => a i - t) w) 0 0
          * (designMatrix (holderDerivOrder β) (fun i => a i - t) w)⁻¹ 0 0 :=
    equivKernelWeight_abs_sum_sq_le hMdet hw
  have hsL : s ≤ L := by
    rw [(Real.sqrt_sq hs_nn).symm]
    exact le_trans (Real.sqrt_le_sqrt hsq) hlev
  have hcoef_nn : 0 ≤ MH / ((holderDerivOrder β)).factorial := div_nonneg hMH (by positivity)
  have hhb : 0 ≤ h ^ β := Real.rpow_nonneg hh β
  calc |c 0 - f t| ≤ (MH / ((holderDerivOrder β)).factorial) * s * h ^ β := hbias
    _ ≤ (MH / ((holderDerivOrder β)).factorial) * L * h ^ β :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsL hcoef_nn) hhb

/-- **Interior local-polynomial estimator stochastic `L²` error `≤ Cvar · (Nh)^{-1/2}`.** The
degree-`p` local-polynomial equivalent-kernel smoother `ĉ₀ = ∑ᵢ Sᵢ Yᵢ` applied to a spherical
family `Y` (scale `σ`) with invertible design moment matrix and weights `0 ≤ wᵢ ≤ W`, on the good
design event where the leverage rate `(M⁻¹)₀₀ ≤ 2·cInv/(Nh)` holds (`0 ≤ cInv`, `0 < Nh`), has
conditional stochastic `L²` error

`√Var(ĉ₀) ≤ √(2σ²·W·cInv) · (Nh)^{-1/2}`,

the standard interior stochastic rate with constant `Cvar = √(2σ²·W·cInv)`. -/
theorem localPoly_estimatorStochL2 {Ω : Type*} {N p : ℕ} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {x w : Fin N → ℝ} {Y : Fin N → Ω → ℝ}
    {σ W cInv Nh : ℝ}
    (hY : ∀ i, MemLp (Y i) 2 μ)
    (hsph : Causalean.GaussMarkov.SphericalFamily Y μ σ)
    (hMdet : IsUnit (designMatrix p x w).det)
    (hw : ∀ i, 0 ≤ w i) (hwW : ∀ i, w i ≤ W) (hW : 0 ≤ W)
    (hcInv : 0 ≤ cInv) (_hNh : 0 < Nh)
    (hrate : (designMatrix p x w)⁻¹ 0 0 ≤ 2 * (cInv / Nh)) :
    Real.sqrt (Var[fun ω => ∑ i, equivKernelWeight p x w i * Y i ω; μ])
      ≤ Real.sqrt (2 * σ ^ 2 * W * cInv) * Real.sqrt Nh⁻¹ := by
  have hvar := localPoly_intercept_variance_le hY hsph hMdet hw hwW
  have hσ2 : 0 ≤ σ ^ 2 := sq_nonneg σ
  have hVarbd :
      Var[fun ω => ∑ i, equivKernelWeight p x w i * Y i ω; μ]
        ≤ 2 * σ ^ 2 * W * cInv * Nh⁻¹ := by
    refine le_trans hvar ?_
    have hWm : W * (designMatrix p x w)⁻¹ 0 0 ≤ W * (2 * (cInv / Nh)) :=
      mul_le_mul_of_nonneg_left hrate hW
    calc σ ^ 2 * (W * (designMatrix p x w)⁻¹ 0 0)
        ≤ σ ^ 2 * (W * (2 * (cInv / Nh))) := mul_le_mul_of_nonneg_left hWm hσ2
      _ = 2 * σ ^ 2 * W * cInv * Nh⁻¹ := by rw [div_eq_mul_inv]; ring
  have hCvar_nn : 0 ≤ 2 * σ ^ 2 * W * cInv :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hσ2) hW) hcInv
  calc Real.sqrt (Var[fun ω => ∑ i, equivKernelWeight p x w i * Y i ω; μ])
      ≤ Real.sqrt (2 * σ ^ 2 * W * cInv * Nh⁻¹) := Real.sqrt_le_sqrt hVarbd
    _ = Real.sqrt (2 * σ ^ 2 * W * cInv) * Real.sqrt Nh⁻¹ := Real.sqrt_mul hCvar_nn _

end Causalean.Stat.Nonparametric
