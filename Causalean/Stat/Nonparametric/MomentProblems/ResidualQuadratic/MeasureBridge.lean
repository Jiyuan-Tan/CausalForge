/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Mathlib
import Causalean.Stat.Nonparametric.MomentProblems.ResidualQuadratic.MomentAlgebra

/-!
# Measure-level L² projection residual of `y ↦ y²` onto `span{1, y}`

This file is the measure bridge for the `MomentProblems` stack. `MomentAlgebra.lean` proves the
closed-form residual purely in moment coordinates; this file turns that algebra into the actual
L²(μ) projection residual for probability measures on `ℝ` with finite fourth moment:

    r(μ) = ⨅_{b₀,b₁} ∫ (y² − b₀ − b₁ y)² dμ.

Writing `mₖ = ∫ yᵏ dμ` for the raw moments, the closed form is the Hankel-determinant ratio

    r(μ) = (m₄ − m₂²) − (m₃ − m₁ m₂)² / (m₂ − m₁²)  =  det H₃ / det H₂,

attained at the least-squares optimal coefficients `b₁* = (m₃ − m₁ m₂)/(m₂ − m₁²)`,
`b₀* = m₂ − b₁* m₁` (here written `optIntercept`, `optSlope`).

## Design

The *moment-level* algebra — that the quadratic objective `residualQuad m₁ m₂ m₃ m₄ b₀ b₁` in
`(b₀, b₁)` has minimum the Hankel ratio, via a completed-square / SOS certificate — is proven,
measure-free, in `Causalean.Stat.MomentProblems.ResidualQuadratic.MomentAlgebra`
(`residualQuad_optimalCoeff`, `residualQuad_ge_momentResidual`). This module supplies the
measure-theoretic bridge:

* `residualQuad_eq` — the *bridge*: expanding the square and integrating term by term,
  `∫ (y² − b₀ − b₁ y)² dμ` equals the moment polynomial
  `MomentAlgebra.residualQuad m₁ m₂ m₃ m₄ b₀ b₁` (uses `IsProbabilityMeasure` for the constant
  term `∫ b₀² = b₀²` and integrability of `y, …, y⁴` to split the integral).
* `residualQuad_opt_eq`, `l2ResidualQuadratic_le`, `l2ResidualQuadratic_nonneg`,
  `iInf_residualQuad` — the optimality / infimum bridge transporting the moment-level minimum to
  the `∫`-form and the conditional infimum `⨅ b₀ b₁`.

Finite fourth moment is packaged as `FiniteMoment4 μ` (integrability of `y, y², y³, y⁴`); for a
probability measure with `∫ y⁴ < ∞` all these lower moments are finite, so this is exactly the
"finite 4th moment" hypothesis. Non-degeneracy is `m₁² < m₂` (positive variance).
-/

namespace Causalean.Stat.MomentProblems.ResidualQuadratic.MeasureBridge

open MeasureTheory
open scoped Real

/-- The raw `k`-th moment `mₖ = ∫ yᵏ ∂μ` of a measure `μ` on `ℝ`. -/
noncomputable def moment (μ : Measure ℝ) (k : ℕ) : ℝ := ∫ y, y ^ k ∂μ

/-- Finite-fourth-moment hypothesis bundle: integrability of the powers `y, y², y³, y⁴` against `μ`.
For a probability measure with `∫ y⁴ ∂μ < ∞` all four hold, so this is exactly "μ has a finite
fourth moment". -/
structure FiniteMoment4 (μ : Measure ℝ) : Prop where
  /-- `y ↦ y` is integrable (finite first moment). -/
  int1 : Integrable (fun y : ℝ => y) μ
  /-- `y ↦ y²` is integrable (finite second moment). -/
  int2 : Integrable (fun y : ℝ => y ^ 2) μ
  /-- `y ↦ y³` is integrable (finite third moment). -/
  int3 : Integrable (fun y : ℝ => y ^ 3) μ
  /-- `y ↦ y⁴` is integrable (finite fourth moment). -/
  int4 : Integrable (fun y : ℝ => y ^ 4) μ

/-- The quadratic regression objective in `L²(μ)`: the mean squared residual of the linear fit
`b₀ + b₁ y` to `y²`, i.e. `∫ (y² − b₀ − b₁ y)² ∂μ`. -/
noncomputable def residualQuad (μ : Measure ℝ) (b₀ b₁ : ℝ) : ℝ :=
  ∫ y, (y ^ 2 - b₀ - b₁ * y) ^ 2 ∂μ

/-- The closed-form minimal residual `r(μ) = (m₄ − m₂²) − (m₃ − m₁ m₂)² / (m₂ − m₁²)`, expressed as
the Hankel-determinant ratio `MomentAlgebra.momentResidual` of the raw moments `m₁, m₂, m₃, m₄`. -/
noncomputable def l2ResidualQuadratic (μ : Measure ℝ) : ℝ :=
  Causalean.Stat.MomentProblems.ResidualQuadratic.MomentAlgebra.momentResidual
    (moment μ 1) (moment μ 2) (moment μ 3) (moment μ 4)

/-- The least-squares optimal intercept `b₀* = (m₁ m₃ − m₂²)/(m₁² − m₂) = m₂ − b₁* m₁`. -/
noncomputable def optIntercept (μ : Measure ℝ) : ℝ :=
  Causalean.Stat.MomentProblems.ResidualQuadratic.MomentAlgebra.optIntercept
    (moment μ 1) (moment μ 2) (moment μ 3)

/-- The least-squares optimal slope `b₁* = (m₃ − m₁ m₂)/(m₂ − m₁²)`. -/
noncomputable def optSlope (μ : Measure ℝ) : ℝ :=
  Causalean.Stat.MomentProblems.ResidualQuadratic.MomentAlgebra.optSlope
    (moment μ 1) (moment μ 2) (moment μ 3)

/-- **Bridge (integral → moments).** For a probability measure with finite fourth moment, the
integral objective equals the moment polynomial: expanding
`(y² − b₀ − b₁ y)² = y⁴ − 2b₁ y³ + (b₁² − 2b₀) y² + 2b₀b₁ y + b₀²` and integrating term by term
(using `∫ 1 ∂μ = 1`),

    ∫ (y² − b₀ − b₁ y)² ∂μ = MomentAlgebra.residualQuad m₁ m₂ m₃ m₄ b₀ b₁.

Proof sketch: rewrite the integrand via `ring` to the explicit degree-4 polynomial, then split with
`integral_add`/`integral_sub`/`integral_const_mul`/`integral_const` using the four `Integrable`
fields of `h`; the constant term contributes `b₀² * (μ univ).toReal = b₀²` by
`IsProbabilityMeasure`. Finally reconcile `∫ y ∂μ` with `moment μ 1 = ∫ y^1 ∂μ` via `pow_one`. -/
theorem residualQuad_eq (μ : Measure ℝ) [IsProbabilityMeasure μ] (h : FiniteMoment4 μ)
    (b₀ b₁ : ℝ) :
    residualQuad μ b₀ b₁ =
      Causalean.Stat.MomentProblems.ResidualQuadratic.MomentAlgebra.residualQuad
        (moment μ 1) (moment μ 2) (moment μ 3) (moment μ 4) b₀ b₁ := by
  unfold residualQuad moment
    Causalean.Stat.MomentProblems.ResidualQuadratic.MomentAlgebra.residualQuad
  have hpoly : (fun y : ℝ => (y ^ 2 - b₀ - b₁ * y) ^ 2) =
      fun y : ℝ => (((((y ^ 4 + (-(2 * b₁)) * y ^ 3) + (-(2 * b₀)) * y ^ 2) +
        (b₁ ^ 2) * y ^ 2) + (2 * b₀ * b₁) * y) + b₀ ^ 2) := by
    funext y
    ring
  rw [hpoly]
  have hi3 : Integrable (fun y : ℝ => (-(2 * b₁)) * y ^ 3) μ := h.int3.const_mul _
  have hi2a : Integrable (fun y : ℝ => (-(2 * b₀)) * y ^ 2) μ := h.int2.const_mul _
  have hi2b : Integrable (fun y : ℝ => (b₁ ^ 2) * y ^ 2) μ := h.int2.const_mul _
  have hi1 : Integrable (fun y : ℝ => (2 * b₀ * b₁) * y) μ := h.int1.const_mul _
  have hic : Integrable (fun _ : ℝ => b₀ ^ 2) μ := integrable_const _
  have hs1 : Integrable (fun y : ℝ => y ^ 4 + (-(2 * b₁)) * y ^ 3) μ :=
    h.int4.add hi3
  have hs2 : Integrable
      (fun y : ℝ => (y ^ 4 + (-(2 * b₁)) * y ^ 3) + (-(2 * b₀)) * y ^ 2) μ :=
    hs1.add hi2a
  have hs3 : Integrable
      (fun y : ℝ => ((y ^ 4 + (-(2 * b₁)) * y ^ 3) + (-(2 * b₀)) * y ^ 2) +
        (b₁ ^ 2) * y ^ 2) μ :=
    hs2.add hi2b
  have hs4 : Integrable
      (fun y : ℝ => (((y ^ 4 + (-(2 * b₁)) * y ^ 3) + (-(2 * b₀)) * y ^ 2) +
        (b₁ ^ 2) * y ^ 2) + (2 * b₀ * b₁) * y) μ :=
    hs3.add hi1
  rw [MeasureTheory.integral_add hs4 hic]
  rw [MeasureTheory.integral_add hs3 hi1]
  rw [MeasureTheory.integral_add hs2 hi2b]
  rw [MeasureTheory.integral_add hs1 hi2a]
  rw [MeasureTheory.integral_add h.int4 hi3]
  simp [MeasureTheory.integral_const_mul, MeasureTheory.integral_mul_const,
    MeasureTheory.integral_neg, MeasureTheory.integral_const, mul_assoc, mul_left_comm, mul_comm]
  ring

/-- **Attainment.** At the optimal coefficients `(optIntercept μ, optSlope μ)` the integral
objective attains the closed-form residual `l2ResidualQuadratic μ`, whenever the design is
non-degenerate (`m₁² < m₂`). -/
theorem residualQuad_opt_eq (μ : Measure ℝ) [IsProbabilityMeasure μ] (h : FiniteMoment4 μ)
    (hnd : moment μ 1 ^ 2 < moment μ 2) :
    residualQuad μ (optIntercept μ) (optSlope μ) = l2ResidualQuadratic μ := by
  rw [residualQuad_eq μ h]
  exact Causalean.Stat.MomentProblems.ResidualQuadratic.MomentAlgebra.residualQuad_optimalCoeff
    (moment μ 1) (moment μ 2) (moment μ 3) (moment μ 4) hnd

/-- **Lower bound (infimum).** The closed-form residual is a lower bound of the integral objective
at every choice of coefficients, when the design is non-degenerate. Together with
`residualQuad_opt_eq` this identifies `l2ResidualQuadratic μ` as the minimum
`⨅ b₀ b₁, ∫ (y² − b₀ − b₁ y)² ∂μ`. -/
theorem l2ResidualQuadratic_le (μ : Measure ℝ) [IsProbabilityMeasure μ] (h : FiniteMoment4 μ)
    (hnd : moment μ 1 ^ 2 < moment μ 2) (b₀ b₁ : ℝ) :
    l2ResidualQuadratic μ ≤ residualQuad μ b₀ b₁ := by
  rw [residualQuad_eq μ h]
  exact Causalean.Stat.MomentProblems.ResidualQuadratic.MomentAlgebra.residualQuad_ge_momentResidual
    (moment μ 1) (moment μ 2) (moment μ 3) (moment μ 4) b₀ b₁ hnd

/-- **Non-negativity.** The closed-form residual is non-negative (it is the value at the optimum
of an integral of a square), for a non-degenerate design. -/
theorem l2ResidualQuadratic_nonneg (μ : Measure ℝ) [IsProbabilityMeasure μ] (h : FiniteMoment4 μ)
    (hnd : moment μ 1 ^ 2 < moment μ 2) :
    0 ≤ l2ResidualQuadratic μ := by
  rw [← residualQuad_opt_eq μ h hnd]
  exact integral_nonneg (fun y => sq_nonneg _)

/-- **Headline infimum identity.** For a probability measure with finite fourth moment and positive
variance (`m₁² < m₂`), the conditional infimum of the regression objective over all coefficients is
the closed-form Hankel residual, attained at `(optIntercept μ, optSlope μ)`:

    ⨅ b₀ b₁, ∫ (y² − b₀ − b₁ y)² ∂μ = l2ResidualQuadratic μ.

Proof sketch: `le_antisymm`. The `≥` direction (`l2 ≤ ⨅`) is `le_ciInf` twice, feeding
`l2ResidualQuadratic_le`. The `≤` direction chains `ciInf_le` twice down to
`residualQuad μ (optIntercept μ) (optSlope μ)` (each range is `BddBelow` by
`l2ResidualQuadratic_le`), then rewrites with `residualQuad_opt_eq`. -/
theorem iInf_residualQuad (μ : Measure ℝ) [IsProbabilityMeasure μ] (h : FiniteMoment4 μ)
    (hnd : moment μ 1 ^ 2 < moment μ 2) :
    ⨅ b₀, ⨅ b₁, residualQuad μ b₀ b₁ = l2ResidualQuadratic μ := by
  apply le_antisymm
  · calc
      ⨅ b₀, ⨅ b₁, residualQuad μ b₀ b₁ ≤
          ⨅ b₁, residualQuad μ (optIntercept μ) b₁ := by
        exact ciInf_le
          (⟨l2ResidualQuadratic μ, by
            rintro x ⟨b₀, rfl⟩
            exact le_ciInf (fun b₁ => l2ResidualQuadratic_le μ h hnd b₀ b₁)⟩ :
            BddBelow (Set.range fun b₀ => ⨅ b₁, residualQuad μ b₀ b₁))
          (optIntercept μ)
      _ ≤ residualQuad μ (optIntercept μ) (optSlope μ) := by
        exact ciInf_le
          (⟨l2ResidualQuadratic μ, by
            rintro x ⟨b₁, rfl⟩
            exact l2ResidualQuadratic_le μ h hnd (optIntercept μ) b₁⟩ :
            BddBelow (Set.range fun b₁ => residualQuad μ (optIntercept μ) b₁))
          (optSlope μ)
      _ = l2ResidualQuadratic μ := residualQuad_opt_eq μ h hnd
  · exact le_ciInf (fun b₀ => le_ciInf (fun b₁ => l2ResidualQuadratic_le μ h hnd b₀ b₁))

end Causalean.Stat.MomentProblems.ResidualQuadratic.MeasureBridge
