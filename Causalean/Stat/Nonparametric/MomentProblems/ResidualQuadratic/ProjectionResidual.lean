/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Stat.Nonparametric.MomentProblems.ResidualQuadratic.MeasureBridge

/-!
# Projection residual function for the moment score program

This file is the functional bridge between `MomentProblems.ResidualQuadratic.MeasureBridge` and the
constrained score program. For a probability measure `μ` on `ℝ` with finite fourth moment and
positive variance (`m₁² < m₂`), `MeasureBridge.lean` computes the closed-form residual value
`r(μ) = l2ResidualQuadratic μ`; this file identifies the residual function that attains that value,

    q(y) := y² − (optIntercept μ + optSlope μ · y),

and proves the four facts that make it the orthogonal projection residual of `y²` onto `span{1,y}`:

* `integral_projResidual`      : `∫ q dμ = 0`                  (orthogonal to the constant `1`)
* `integral_id_mul_projResidual` : `∫ y·q dμ = 0`             (orthogonal to `y`)
* `integral_sq_projResidual`   : `∫ q² dμ = r`                (its own L² norm² is the residual `r`)
* `integral_sq_mul_projResidual` : `∫ y²·q dμ = r`           (`y²`-moment of `q` equals `r`)

The first two are the *normal equations* of least squares; here they reduce, after splitting the
integral into raw moments `mₖ = ∫ yᵏ`, to pure moment algebra in the definitions of
`optIntercept`/`optSlope` (division by `m₁² − m₂ ≠ 0`). The last two reuse
`MeasureBridge.residualQuad_opt_eq`, the attainment lemma for the closed-form residual.

These are the ingredients consumed by `ScoreProgram.lean` to solve the constrained minimum-norm
"score program" dual to this projection.
-/

namespace Causalean.Stat.MomentProblems.ResidualQuadratic.ProjectionResidual

open MeasureTheory
open scoped Real

open Causalean.Stat.MomentProblems.ResidualQuadratic.MeasureBridge
  (moment optIntercept optSlope l2ResidualQuadratic residualQuad FiniteMoment4)

/-- The **L² projection residual function** of `y ↦ y²` onto `span{1, y}`:
`q(y) = y² − (optIntercept μ + optSlope μ · y)`, i.e. `y²` minus its least-squares linear fit. -/
noncomputable def projResidual (μ : Measure ℝ) : ℝ → ℝ :=
  fun y => y ^ 2 - (optIntercept μ + optSlope μ * y)

/-- `y ↦ y` is in `L²(μ)` when the second moment is finite. -/
theorem memL2_id (μ : Measure ℝ) [IsFiniteMeasure μ] (h : FiniteMoment4 μ) :
    MemLp (fun y : ℝ => y) 2 μ := by
  refine (memLp_two_iff_integrable_sq (continuous_id.aestronglyMeasurable)).2 ?_
  simpa using h.int2

/-- `y ↦ y²` is in `L²(μ)` when the fourth moment is finite. -/
theorem memL2_sq (μ : Measure ℝ) [IsFiniteMeasure μ] (h : FiniteMoment4 μ) :
    MemLp (fun y : ℝ => y ^ 2) 2 μ := by
  refine (memLp_two_iff_integrable_sq ((continuous_pow 2).aestronglyMeasurable)).2 ?_
  simpa [pow_mul] using h.int4.congr (by filter_upwards with y; ring)

/-- The residual function `q` is square-integrable (`q ∈ L²(μ)`): it is a degree-2 polynomial in
`y` and `μ` has a finite fourth moment. -/
theorem projResidual_memL2 (μ : Measure ℝ) [IsFiniteMeasure μ] (h : FiniteMoment4 μ) :
    MemLp (projResidual μ) 2 μ := by
  -- `q = y² − b₁·y − b₀` is a linear combination of the L²-functions `y²`, `y`, `1`.
  have hsq := memL2_sq μ h
  have hid := memL2_id μ h
  have hconst : MemLp (fun _ : ℝ => optIntercept μ) 2 μ := memLp_const _
  have : MemLp (fun y : ℝ => y ^ 2 - (optIntercept μ + optSlope μ * y)) 2 μ := by
    have h1 : MemLp (fun y : ℝ => optSlope μ * y) 2 μ := hid.const_mul _
    exact (hsq.sub (hconst.add h1))
  simpa [projResidual] using this

/-- `q` is integrable (finite measure + `q ∈ L²`). -/
theorem integrable_projResidual (μ : Measure ℝ) [IsFiniteMeasure μ] (h : FiniteMoment4 μ) :
    Integrable (projResidual μ) μ :=
  (projResidual_memL2 μ h).integrable (by norm_num)

/-- **Orthogonality to the constant.** `∫ q dμ = 0`.

Splitting the integral into raw moments gives `∫ q = m₂ − optIntercept μ − optSlope μ · m₁`
(using `∫ 1 = 1`). Substituting the closed forms
`optIntercept μ = (m₁m₃ − m₂²)/(m₁² − m₂)`, `optSlope μ = (m₁m₂ − m₃)/(m₁² − m₂)` and clearing the
denominator `m₁² − m₂ ≠ 0` (from `hnd : m₁² < m₂`) makes this vanish (`field_simp; ring`). -/
theorem integral_projResidual (μ : Measure ℝ) [IsProbabilityMeasure μ] (h : FiniteMoment4 μ)
    (hnd : moment μ 1 ^ 2 < moment μ 2) :
    ∫ y, projResidual μ y ∂μ = 0 := by
  have hsq : Integrable (fun y : ℝ => y ^ 2) μ :=
    (memL2_sq μ h).integrable (by norm_num)
  have hid : Integrable (fun y : ℝ => y) μ :=
    (memL2_id μ h).integrable (by norm_num)
  have hlin : Integrable (fun y : ℝ => optIntercept μ + optSlope μ * y) μ :=
    (integrable_const (optIntercept μ)).add (hid.const_mul (optSlope μ))
  unfold projResidual
  rw [MeasureTheory.integral_sub hsq hlin]
  rw [MeasureTheory.integral_add (integrable_const (optIntercept μ))
    (hid.const_mul (optSlope μ))]
  rw [MeasureTheory.integral_const_mul]
  simp only [MeasureTheory.integral_const, smul_eq_mul]
  rw [show μ.real Set.univ = 1 by simp]
  rw [show (∫ a : ℝ, a ∂μ) = moment μ 1 by simp [moment]]
  change moment μ 2 - (1 * optIntercept μ + optSlope μ * moment μ 1) = 0
  ring_nf
  have hd : moment μ 1 ^ 2 - moment μ 2 ≠ 0 := by nlinarith
  unfold optIntercept optSlope
    Causalean.Stat.MomentProblems.ResidualQuadratic.MomentAlgebra.optIntercept
    Causalean.Stat.MomentProblems.ResidualQuadratic.MomentAlgebra.optSlope
  field_simp [hd]
  ring

/-- **Orthogonality to `y`.** `∫ y·q dμ = 0`.

`y·q = y³ − optIntercept μ · y − optSlope μ · y²`, so `∫ y·q = m₃ − optIntercept μ · m₁ −
optSlope μ · m₂`; substituting the closed forms and clearing `m₁² − m₂ ≠ 0` gives `0`. -/
theorem integral_id_mul_projResidual (μ : Measure ℝ) [IsProbabilityMeasure μ] (h : FiniteMoment4 μ)
    (hnd : moment μ 1 ^ 2 < moment μ 2) :
    ∫ y, y * projResidual μ y ∂μ = 0 := by
  have hid : Integrable (fun y : ℝ => y) μ :=
    (memL2_id μ h).integrable (by norm_num)
  have hsq : Integrable (fun y : ℝ => y ^ 2) μ :=
    (memL2_sq μ h).integrable (by norm_num)
  have hfun : (fun y : ℝ => y * projResidual μ y) =
      fun y : ℝ => y ^ 3 - optIntercept μ * y - optSlope μ * y ^ 2 := by
    funext y
    simp [projResidual]
    ring
  rw [hfun]
  have hterm1 : Integrable (fun y : ℝ => y ^ 3 - optIntercept μ * y) μ :=
    h.int3.sub (hid.const_mul (optIntercept μ))
  have hterm2 : Integrable (fun y : ℝ => optSlope μ * y ^ 2) μ :=
    hsq.const_mul (optSlope μ)
  rw [MeasureTheory.integral_sub hterm1 hterm2]
  rw [MeasureTheory.integral_sub h.int3 (hid.const_mul (optIntercept μ))]
  rw [MeasureTheory.integral_const_mul]
  rw [MeasureTheory.integral_const_mul]
  rw [show (∫ a : ℝ, a ∂μ) = moment μ 1 by simp [moment]]
  change moment μ 3 - optIntercept μ * moment μ 1 - optSlope μ * moment μ 2 = 0
  have hd : moment μ 1 ^ 2 - moment μ 2 ≠ 0 := by nlinarith
  unfold optIntercept optSlope
    Causalean.Stat.MomentProblems.ResidualQuadratic.MomentAlgebra.optIntercept
    Causalean.Stat.MomentProblems.ResidualQuadratic.MomentAlgebra.optSlope
  field_simp [hd]
  ring

/-- **Self L²-norm.** `∫ q² dμ = r`, the closed-form residual `l2ResidualQuadratic μ`.

`q(y)² = (y² − optIntercept μ − optSlope μ · y)²` is exactly the integrand of
`MeasureBridge.residualQuad μ (optIntercept μ) (optSlope μ)`, whose value at the optimal
coefficients is `l2ResidualQuadratic μ` by `residualQuad_opt_eq`. -/
theorem integral_sq_projResidual (μ : Measure ℝ) [IsProbabilityMeasure μ] (h : FiniteMoment4 μ)
    (hnd : moment μ 1 ^ 2 < moment μ 2) :
    ∫ y, projResidual μ y ^ 2 ∂μ = l2ResidualQuadratic μ := by
  rw [← Causalean.Stat.MomentProblems.ResidualQuadratic.MeasureBridge.residualQuad_opt_eq μ h hnd]
  unfold projResidual Causalean.Stat.MomentProblems.ResidualQuadratic.MeasureBridge.residualQuad
  congr 1
  funext y
  ring

/-- **`y²`-moment.** `∫ y²·q dμ = r`.

Write `y² = q(y) + optIntercept μ + optSlope μ · y`, so `y²·q = q² + optIntercept μ · q +
optSlope μ · (y·q)`. Integrating and using `integral_sq_projResidual` (`∫ q² = r`),
`integral_projResidual` (`∫ q = 0`) and `integral_id_mul_projResidual` (`∫ y·q = 0`) gives `r`. -/
theorem integral_sq_mul_projResidual (μ : Measure ℝ) [IsProbabilityMeasure μ] (h : FiniteMoment4 μ)
    (hnd : moment μ 1 ^ 2 < moment μ 2) :
    ∫ y, y ^ 2 * projResidual μ y ∂μ = l2ResidualQuadratic μ := by
  have hfun : (fun y : ℝ => y ^ 2 * projResidual μ y) =
      fun y : ℝ => projResidual μ y ^ 2 + optIntercept μ * projResidual μ y +
        optSlope μ * (y * projResidual μ y) := by
    funext y
    simp [projResidual]
    ring
  rw [hfun]
  have hq : Integrable (projResidual μ) μ := integrable_projResidual μ h
  have hq2 : Integrable (fun y : ℝ => projResidual μ y ^ 2) μ :=
    (projResidual_memL2 μ h).integrable_sq
  have hyq : Integrable (fun y : ℝ => y * projResidual μ y) μ :=
    (memL2_id μ h).integrable_mul (projResidual_memL2 μ h)
  have hbq : Integrable (fun y : ℝ => optIntercept μ * projResidual μ y) μ :=
    hq.const_mul (optIntercept μ)
  have hcyq : Integrable (fun y : ℝ => optSlope μ * (y * projResidual μ y)) μ :=
    hyq.const_mul (optSlope μ)
  have hsplit1 :
      (∫ y, (projResidual μ y ^ 2 + optIntercept μ * projResidual μ y) +
        optSlope μ * (y * projResidual μ y) ∂μ) =
        (∫ y, projResidual μ y ^ 2 + optIntercept μ * projResidual μ y ∂μ) +
          ∫ y, optSlope μ * (y * projResidual μ y) ∂μ := by
    simpa using MeasureTheory.integral_add (hq2.add hbq) hcyq
  have hsplit2 :
      (∫ y, projResidual μ y ^ 2 + optIntercept μ * projResidual μ y ∂μ) =
        (∫ y, projResidual μ y ^ 2 ∂μ) +
          ∫ y, optIntercept μ * projResidual μ y ∂μ := by
    simpa using MeasureTheory.integral_add hq2 hbq
  rw [hsplit1, hsplit2]
  rw [MeasureTheory.integral_const_mul]
  rw [MeasureTheory.integral_const_mul]
  rw [integral_sq_projResidual μ h hnd]
  rw [integral_projResidual μ h hnd]
  rw [integral_id_mul_projResidual μ h hnd]
  ring

end Causalean.Stat.MomentProblems.ResidualQuadratic.ProjectionResidual
