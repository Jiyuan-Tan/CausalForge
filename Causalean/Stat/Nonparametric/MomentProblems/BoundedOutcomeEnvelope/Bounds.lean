/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Stat.Nonparametric.MomentProblems.BoundedOutcomeEnvelope.Defs

/-!
# Bounded-outcome residual envelope upper bound `r(μ) ≤ ρ(v)`

This file proves the upper-bound half of the bounded-outcome residual envelope. For every admissible
law `μ` (probability measure a.e. supported in `[0,1]` with `∫ y² ∂μ = v²`), the residual
`l2ResidualQuadratic μ` is at most `rhoEnvelope v`.

The bridge to the moment-level `MomentAlgebra.momentResidual_le_envelope` needs three measure-level
facts about the raw moments `m = ∫ y`, `q = ∫ y² = v²`, `m₃ = ∫ y³`, `m₄ = ∫ y⁴`:

* `finiteMoment4_of_admissible` — all four powers are integrable (bounded support + finite measure).
* `moment2_le_moment1` — `q ≤ m`, since `y² ≤ y` a.e. on `[0,1]` (monotone integral).
* `moment1_sq_le_moment2` — `m² ≤ q`, i.e. `Var ≥ 0` (Cauchy–Schwarz for a probability measure).
* `crossMoment_nonneg` — `0 ≤ crossMoment m q m₃ m₄`, because that moment combination equals the
  integral `∫ y (1 − y) (y − xᵥ)² ∂μ` of a function nonnegative on `[0,1]`.

The degenerate case `m² = q` (a point mass) is handled directly: `l2ResidualQuadratic μ = 0`
(vanishing denominator), and `ρ(v) > 0`.
-/

namespace Causalean.Stat.MomentProblems.BoundedOutcomeEnvelope

open Causalean.Stat.MomentProblems.ResidualQuadratic.MomentAlgebra
open Causalean.Stat.MomentProblems.ResidualQuadratic.MeasureBridge
  (moment l2ResidualQuadratic FiniteMoment4)
open MeasureTheory Set
open scoped Real

/-- Every power `y ↦ yᵏ` (`k ≤ 4`) is integrable against an admissible law: on `[0,1]` we have
`|yᵏ| ≤ 1`, and `μ` is a finite measure, so `Integrable.mono'` against the constant `1` applies. -/
theorem finiteMoment4_of_admissible {v : ℝ} {μ : Measure ℝ} (h : Admissible v μ) :
    FiniteMoment4 μ := by
  haveI : IsProbabilityMeasure μ := h.isProb
  have hintPow (k : ℕ) : Integrable (fun y : ℝ => y ^ k) μ := by
    refine Integrable.of_bound ((continuous_pow k).aestronglyMeasurable) 1 ?_
    filter_upwards [h.supp] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hy.1 k)]
    exact pow_le_one₀ hy.1 hy.2
  refine ⟨?_, hintPow 2, hintPow 3, hintPow 4⟩
  simpa using hintPow 1

/-- `q ≤ m`: the second moment is at most the first, because `y² ≤ y` a.e. on `[0,1]`. Uses
`integral_mono_ae` on the a.e. support bound plus integrability of `y, y²`. -/
theorem moment2_le_moment1 {v : ℝ} {μ : Measure ℝ} (h : Admissible v μ) :
    moment μ 2 ≤ moment μ 1 := by
  have hfin := finiteMoment4_of_admissible h
  unfold moment
  refine integral_mono_ae hfin.int2 ?_ ?_
  · simpa [pow_one] using hfin.int1
  · filter_upwards [h.supp] with y hy
    nlinarith [hy.1, hy.2]

/-- `m² ≤ q`: the variance is nonnegative. For a probability measure,
`(∫ y)² ≤ ∫ y²` (Cauchy–Schwarz / Jensen). -/
theorem moment1_sq_le_moment2 {v : ℝ} {μ : Measure ℝ} (h : Admissible v μ) :
    (moment μ 1) ^ 2 ≤ moment μ 2 := by
  haveI : IsProbabilityMeasure μ := h.isProb
  have hfin := finiteMoment4_of_admissible h
  have hmem : MemLp (fun y : ℝ => y) 2 μ := by
    refine (memLp_two_iff_integrable_sq (continuous_id.aestronglyMeasurable)).2 ?_
    simpa using hfin.int2
  have hvar_nonneg := ProbabilityTheory.variance_nonneg (fun y : ℝ => y) μ
  have hvar_eq :
      ProbabilityTheory.variance (fun y : ℝ => y) μ =
        (∫ y : ℝ, y ^ 2 ∂μ) - (∫ y : ℝ, y ∂μ) ^ 2 := by
    rw [ProbabilityTheory.variance_eq_sub hmem]
    simp [pow_two]
  have hle : (∫ y : ℝ, y ∂μ) ^ 2 ≤ ∫ y : ℝ, y ^ 2 ∂μ := by
    rw [hvar_eq] at hvar_nonneg
    linarith
  simpa [moment, pow_one] using hle

/-- `0 ≤ crossMoment m q m₃ m₄`. The certificate cross moment equals the integral
`∫ y (1 − y) (y − xᵥ)² ∂μ` (expand the degree-4 polynomial and integrate term by term, matching the
definition of `crossMoment`); on `[0,1]` the integrand is `≥ 0`, so the integral is `≥ 0`. -/
theorem crossMoment_nonneg {v : ℝ} {μ : Measure ℝ} (h : Admissible v μ) :
    0 ≤ crossMoment (moment μ 1) (moment μ 2) (moment μ 3) (moment μ 4) := by
  have hfin := finiteMoment4_of_admissible h
  set c := extremalMid (moment μ 1) (moment μ 2)
  have hcross_eq :
      crossMoment (moment μ 1) (moment μ 2) (moment μ 3) (moment μ 4) =
        ∫ y, y * (1 - y) * (y - c) ^ 2 ∂μ := by
    unfold crossMoment moment
    change -∫ y, y ^ 4 ∂μ + (1 + 2 * c) * ∫ y, y ^ 3 ∂μ -
        (2 * c + c ^ 2) * ∫ y, y ^ 2 ∂μ + c ^ 2 * ∫ y, y ^ 1 ∂μ =
      ∫ y, y * (1 - y) * (y - c) ^ 2 ∂μ
    have hpoly : (fun y : ℝ => y * (1 - y) * (y - c) ^ 2) =
        fun y : ℝ => ((((-1 : ℝ) * y ^ 4 + (1 + 2 * c) * y ^ 3) +
          (-(2 * c + c ^ 2)) * y ^ 2) + c ^ 2 * y) := by
      funext y
      ring
    rw [hpoly]
    have hi4 : Integrable (fun y : ℝ => (-1 : ℝ) * y ^ 4) μ := hfin.int4.const_mul _
    have hi3 : Integrable (fun y : ℝ => (1 + 2 * c) * y ^ 3) μ := hfin.int3.const_mul _
    have hi2 : Integrable (fun y : ℝ => (-(2 * c + c ^ 2)) * y ^ 2) μ :=
      hfin.int2.const_mul _
    have hi1 : Integrable (fun y : ℝ => c ^ 2 * y) μ := hfin.int1.const_mul _
    have hs1 : Integrable
        (fun y : ℝ => (-1 : ℝ) * y ^ 4 + (1 + 2 * c) * y ^ 3) μ :=
      hi4.add hi3
    have hs2 : Integrable
        (fun y : ℝ => ((-1 : ℝ) * y ^ 4 + (1 + 2 * c) * y ^ 3) +
          (-(2 * c + c ^ 2)) * y ^ 2) μ :=
      hs1.add hi2
    rw [MeasureTheory.integral_add hs2 hi1]
    rw [MeasureTheory.integral_add hs1 hi2]
    rw [MeasureTheory.integral_add hi4 hi3]
    simp [MeasureTheory.integral_mul_const, MeasureTheory.integral_neg, mul_comm, pow_one]
    ring
  rw [hcross_eq]
  refine integral_nonneg_of_ae ?_
  filter_upwards [h.supp] with y hy
  exact mul_nonneg (mul_nonneg hy.1 (by linarith [hy.2])) (sq_nonneg (y - c))

/-- In the degenerate case `m² = q` the closed-form residual is `0` (the Hankel ratio's denominator
`m₁² − m₂` vanishes, so `momentResidual _ _ _ _ = _ / 0 = 0`). -/
theorem l2ResidualQuadratic_eq_zero_of_degenerate {μ : Measure ℝ}
    (hdeg : (moment μ 1) ^ 2 = moment μ 2) :
    l2ResidualQuadratic μ = 0 := by
  unfold l2ResidualQuadratic momentResidual
  rw [show (moment μ 1) ^ 2 - moment μ 2 = 0 by rw [hdeg]; ring, div_zero]

/-- **Measure-level sharp upper bound.** For `v ∈ (0,1)` and every admissible `μ`, the closed-form
residual is at most the envelope value: `l2ResidualQuadratic μ ≤ rhoEnvelope v`.

Nondegenerate case (`m² < q`): `l2ResidualQuadratic μ = momentResidual m q m₃ m₄` (definition), then
apply `MomentAlgebra.momentResidual_le_envelope` at the maximizing root `u = maximizingRoot v`
(which lies in `(v², v)`, giving `q < u`, `u² < q`, `envelopeQuartic u q = 0`), feeding the three
measure-level moment facts above.  Degenerate case (`m² = q`): the residual is `0 < ρ(v)`. -/
theorem l2ResidualQuadratic_le_rho (v : ℝ) (μ : Measure ℝ) (h : Admissible v μ)
    (hv0 : 0 < v) (hv1 : v < 1) :
    l2ResidualQuadratic μ ≤ rhoEnvelope v := by
  have hq0 : (0 : ℝ) < v ^ 2 := by positivity
  have hq1 : v ^ 2 < 1 := by nlinarith
  have hmom2 : moment μ 2 = v ^ 2 := h.moment2_eq
  have hqm : moment μ 2 ≤ moment μ 1 := moment2_le_moment1 h
  have hmq_le : (moment μ 1) ^ 2 ≤ moment μ 2 := moment1_sq_le_moment2 h
  have hmem := maximizingRoot_mem v hv0 hv1
  have hqu : v ^ 2 < maximizingRoot v := hmem.1
  have hroot : envelopeQuartic (maximizingRoot v) (v ^ 2) = 0 := maximizingRoot_quartic v hv0 hv1
  rcases eq_or_lt_of_le hmq_le with hdeg | hlt
  · -- degenerate point-mass case
    rw [l2ResidualQuadratic_eq_zero_of_degenerate hdeg]
    exact le_of_lt (rhoEnvelope_pos v hv0 hv1)
  · -- nondegenerate case: bridge to `momentResidual_le_envelope`
    have hu0 : 0 < maximizingRoot v := lt_trans hq0 hqu
    have huq : (maximizingRoot v) ^ 2 < v ^ 2 := by nlinarith [hmem.2]
    -- `hqm`, `hlt` in `v²`-coordinates:
    have hqm' : v ^ 2 ≤ moment μ 1 := by rw [← hmom2]; exact hqm
    have hmq' : (moment μ 1) ^ 2 < v ^ 2 := by rw [← hmom2]; exact hlt
    have hcross := crossMoment_nonneg h
    rw [hmom2] at hcross
    have hbound :
        momentResidual (moment μ 1) (v ^ 2) (moment μ 3) (moment μ 4)
          ≤ momentEnvelope (maximizingRoot v) (v ^ 2) :=
      momentResidual_le_envelope (moment μ 1) (v ^ 2) (moment μ 3) (moment μ 4)
        (maximizingRoot v) hq0 hq1 hqm' hmq' hcross hqu huq hroot
    have hres : l2ResidualQuadratic μ
        = momentResidual (moment μ 1) (v ^ 2) (moment μ 3) (moment μ 4) := by
      unfold l2ResidualQuadratic; rw [hmom2]
    rw [hres, rhoEnvelope]
    exact hbound

end Causalean.Stat.MomentProblems.BoundedOutcomeEnvelope
