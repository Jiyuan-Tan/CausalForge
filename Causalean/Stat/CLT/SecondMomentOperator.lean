/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# The second-moment (covariance) operator of a vector-valued influence function

For an influence function `ψ : X → E` valued in a finite-dimensional real
inner-product space with `‖ψ‖²` integrable under `P`, the **second-moment
operator**

    Σ t = ∫ ⟪t, ψ x⟫ • ψ x ∂P

is the self-adjoint positive operator whose quadratic form recovers the
asymptotic-covariance integral

    ⟪Σ t, s⟫ = ∫ ⟪t, ψ x⟫ ⟪s, ψ x⟫ ∂P.

This is the operator `Σ` whose square root (`LinearMap.IsPositive.posSqrt`,
`Causalean/Mathlib/OperatorSqrt.lean`) builds the limiting Gaussian in the
multivariate CLT.  Centering (`∫ ψ = 0`) is *not* assumed here; `Σ` is the raw
second moment.  In the CLT application `ψ` is already centred, so `Σ` is the
covariance.

Key declarations:
* `secondMomentLM` — the operator as a `LinearMap`.
* `secondMomentLM_inner` — the quadratic-form identity.
* `secondMomentLM_isPositive` — `Σ` is a positive operator.
-/
import Causalean.Mathlib.OperatorSqrt
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

/-! # Second-Moment Operator

This file constructs the finite-dimensional second-moment operator associated with a
vector-valued influence function. The operator supplies the covariance object whose
positive square root is used in vector central limit theorems.

The helper theorem `integrable_inner_smul` proves integrability of the operator
integrand. The main API is `secondMomentLM`, the bilinear-form identity
`secondMomentLM_inner`, and `secondMomentLM_isPositive`, which supplies the
positivity needed to take the operator square root used by the concrete Gaussian
limit. -/

open MeasureTheory
open scoped RealInnerProductSpace

namespace Causalean.Stat

variable {X E : Type*} [MeasurableSpace X] {P : Measure X}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ψ : X → E}

/-- The integrand `x ↦ ⟪t, ψ x⟫ • ψ x` is integrable when `‖ψ‖²` is, by the
Cauchy–Schwarz bound `‖⟪t,ψ⟫ • ψ‖ ≤ ‖t‖ ‖ψ‖²`. -/
theorem integrable_inner_smul (hψ : Measurable ψ)
    (hvar : Integrable (fun x => ‖ψ x‖ ^ 2) P) (t : E) :
    Integrable (fun x => ⟪t, ψ x⟫ • ψ x) P := by
  have hmeas : AEStronglyMeasurable (fun x => ⟪t, ψ x⟫ • ψ x) P :=
    ((hψ.const_inner (c := t)).smul hψ).aestronglyMeasurable
  refine Integrable.mono' (hvar.const_mul ‖t‖) hmeas (ae_of_all _ fun x => ?_)
  rw [norm_smul, Real.norm_eq_abs]
  calc |⟪t, ψ x⟫| * ‖ψ x‖
      ≤ (‖t‖ * ‖ψ x‖) * ‖ψ x‖ := by gcongr; exact abs_real_inner_le_norm t (ψ x)
    _ = ‖t‖ * ‖ψ x‖ ^ 2 := by ring

variable (hψ : Measurable ψ) (hvar : Integrable (fun x => ‖ψ x‖ ^ 2) P)

/-- The second-moment operator `Σ t = ∫ ⟪t, ψ x⟫ • ψ x ∂P`, as a linear map. -/
noncomputable def secondMomentLM : E →ₗ[ℝ] E where
  toFun t := ∫ x, ⟪t, ψ x⟫ • ψ x ∂P
  map_add' t₁ t₂ := by
    rw [← integral_add (integrable_inner_smul hψ hvar t₁) (integrable_inner_smul hψ hvar t₂)]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [inner_add_left, add_smul]
  map_smul' c t := by
    simp only [RingHom.id_apply, ← integral_smul]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [inner_smul_left, conj_trivial, mul_smul]

/-- Quadratic-form identity: `⟪Σ t, s⟫ = ∫ ⟪t, ψ⟫ ⟪s, ψ⟫ ∂P`. -/
theorem secondMomentLM_inner (t s : E) :
    ⟪secondMomentLM hψ hvar t, s⟫ = ∫ x, ⟪t, ψ x⟫ * ⟪s, ψ x⟫ ∂P := by
  rw [show ⟪secondMomentLM hψ hvar t, s⟫ = ⟪s, secondMomentLM hψ hvar t⟫ from real_inner_comm _ _]
  change ⟪s, ∫ x, ⟪t, ψ x⟫ • ψ x ∂P⟫ = _
  rw [← integral_inner (integrable_inner_smul hψ hvar t) s]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [inner_smul_right]

/-- The second-moment operator is positive (hence symmetric/self-adjoint). -/
theorem secondMomentLM_isPositive : (secondMomentLM hψ hvar).IsPositive := by
  refine (LinearMap.isPositive_iff _).mpr ⟨fun t s => ?_, fun t => ?_⟩
  · rw [secondMomentLM_inner hψ hvar t s,
      show ⟪t, secondMomentLM hψ hvar s⟫ = ⟪secondMomentLM hψ hvar s, t⟫ from real_inner_comm _ _,
      secondMomentLM_inner hψ hvar s t]
    exact integral_congr_ae (ae_of_all _ fun x => by ring)
  · rw [secondMomentLM_inner hψ hvar t t]
    exact integral_nonneg fun x => mul_self_nonneg _

end Causalean.Stat
