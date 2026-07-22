/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Stat.Nonparametric.MomentProblems.BoundedOutcomeEnvelope.Defs

/-!
# Attainment for the bounded-outcome residual envelope

This file proves the lower-bound/attainment half of the bounded-outcome residual envelope. The
measure-level supremum `ρ(v)` is attained by an explicit three-point law on `{0, xᵥ, 1}`, where
`xᵥ = extremalMid μᵥ (v²)` is the interior support point of the extremal law whose first moment is
the maximizing root `μᵥ = maximizingRoot v`.

The weights `w₀, w₁, w₂` are the unique solution of the three linear moment constraints
`w₀ + w₁ + w₂ = 1`, `w₁ xᵥ + w₂ = μᵥ`, `w₁ xᵥ² + w₂ = v²`, namely

    w₁ = (μᵥ − v²) / (xᵥ (1 − xᵥ)),   w₂ = (v² − μᵥ xᵥ) / (1 − xᵥ),   w₀ = 1 − w₁ − w₂.

For `μᵥ ∈ (v², v)` these are nonnegative and `xᵥ ∈ (0,1)`, so `extremalMeasure v` is a probability
measure supported in `[0,1]`.  Its raw moments are `mₖ = w₁ xᵥᵏ + w₂` (`k ≥ 1`), which match the
extremal moments `(μᵥ, v², extremalM3 μᵥ (v²), extremalM4 μᵥ (v²))`; hence by
`MomentAlgebra.extremalResidual_eq_envelope` its residual equals `momentEnvelope μᵥ (v²) = ρ(v)`.
-/

namespace Causalean.Stat.MomentProblems.BoundedOutcomeEnvelope

open Causalean.Stat.MomentProblems.ResidualQuadratic.MomentAlgebra
open Causalean.Stat.MomentProblems.ResidualQuadratic.MeasureBridge (moment l2ResidualQuadratic)
open MeasureTheory Set
open scoped Real

/-- Interior support point `xᵥ = extremalMid μᵥ (v²)` of the extremal three-point law. -/
noncomputable def extremalSupp (v : ℝ) : ℝ := extremalMid (maximizingRoot v) (v ^ 2)

/-- Weight `w₁` on the interior point `xᵥ`. -/
noncomputable def extremalW1 (v : ℝ) : ℝ :=
  (maximizingRoot v - v ^ 2) / (extremalSupp v * (1 - extremalSupp v))

/-- Weight `w₂` on the point `1`. -/
noncomputable def extremalW2 (v : ℝ) : ℝ :=
  (v ^ 2 - maximizingRoot v * extremalSupp v) / (1 - extremalSupp v)

/-- Weight `w₀` on the point `0`. -/
noncomputable def extremalW0 (v : ℝ) : ℝ := 1 - extremalW1 v - extremalW2 v

/-- The extremal three-point probability law `w₀ δ₀ + w₁ δ_{xᵥ} + w₂ δ₁`. -/
noncomputable def extremalMeasure (v : ℝ) : Measure ℝ :=
  ENNReal.ofReal (extremalW0 v) • Measure.dirac 0
    + ENNReal.ofReal (extremalW1 v) • Measure.dirac (extremalSupp v)
    + ENNReal.ofReal (extremalW2 v) • Measure.dirac 1

/-- The interior support point lies in `(0,1)`: `xᵥ = (μᵥ² − 2 μᵥ v² + v²)/(2 μᵥ (1 − μᵥ)) ∈ (0,1)`
for `μᵥ ∈ (v², v)`. Proof: `nlinarith` from `v² < μᵥ < v < 1`. -/
theorem extremalSupp_mem (v : ℝ) (hv0 : 0 < v) (hv1 : v < 1) :
    extremalSupp v ∈ Ioo (0 : ℝ) 1 := by
  have hmem := maximizingRoot_mem v hv0 hv1
  set u := maximizingRoot v with hu
  have hu0 : 0 < u := lt_trans (by positivity) hmem.1
  have hu1 : u < 1 := lt_trans hmem.2 hv1
  have hq1 : v ^ 2 < 1 := by nlinarith
  have hden : 0 < 2 * u * (1 - u) := by nlinarith
  unfold extremalSupp extremalMid
  rw [← hu]
  constructor
  · apply div_pos
    · have hnum :
          0 < (u - v ^ 2) ^ 2 + v ^ 2 * (1 - v ^ 2) := by
        have hsq : 0 ≤ (u - v ^ 2) ^ 2 := sq_nonneg _
        have hv2pos : 0 < v ^ 2 := by positivity
        have hv2one : 0 < 1 - v ^ 2 := by linarith
        have hprod : 0 < v ^ 2 * (1 - v ^ 2) := mul_pos hv2pos hv2one
        nlinarith
      nlinarith [hnum]
    · exact hden
  · rw [div_lt_one hden]
    nlinarith [hmem.1, hmem.2, hv0, hv1, hu0, hu1,
      sq_nonneg (u - v ^ 2), sq_nonneg (v - u), sq_nonneg (1 - v)]

/-- The three weights are nonnegative for `v ∈ (0,1)`. Proof: `w₁ > 0` since `μᵥ > v²` and
`xᵥ ∈ (0,1)`; `w₂ ≥ 0` since `v² ≥ μᵥ xᵥ`; `w₀ ≥ 0` since `w₁ + w₂ ≤ 1`. All via `nlinarith`
from `v² < μᵥ < v` and `extremalSupp_mem`. -/
theorem extremalW_nonneg (v : ℝ) (hv0 : 0 < v) (hv1 : v < 1) :
    0 ≤ extremalW0 v ∧ 0 ≤ extremalW1 v ∧ 0 ≤ extremalW2 v := by
  have hmem := maximizingRoot_mem v hv0 hv1
  have hx := extremalSupp_mem v hv0 hv1
  set u := maximizingRoot v with hu
  have hu0 : 0 < u := lt_trans (by positivity) hmem.1
  have hu1 : u < 1 := lt_trans hmem.2 hv1
  have hu2lt : u ^ 2 < v ^ 2 := by
    have hdiff : 0 < v - u := sub_pos.mpr hmem.2
    have hsum : 0 < v + u := by nlinarith
    have hprod : 0 < (v - u) * (v + u) := mul_pos hdiff hsum
    nlinarith
  have hdenu : 0 < 2 * u * (1 - u) := by nlinarith
  have hnumx : 0 < u ^ 2 - 2 * u * v ^ 2 + v ^ 2 := by
    have hnum :
        0 < (u - v ^ 2) ^ 2 + v ^ 2 * (1 - v ^ 2) := by
      have hsq : 0 ≤ (u - v ^ 2) ^ 2 := sq_nonneg _
      have hv2pos : 0 < v ^ 2 := by positivity
      have hv2one : 0 < 1 - v ^ 2 := by nlinarith
      have hprod : 0 < v ^ 2 * (1 - v ^ 2) := mul_pos hv2pos hv2one
      nlinarith
    nlinarith [hnum]
  have h1xnum : 0 < 2 * u * (1 - u) - (u ^ 2 - 2 * u * v ^ 2 + v ^ 2) := by
    nlinarith [hmem.1, hmem.2, hv0, hv1, hu0, hu1,
      sq_nonneg (u - v ^ 2), sq_nonneg (v - u), sq_nonneg (1 - v)]
  have hw2num :
      0 ≤ v ^ 2 - u * extremalSupp v := by
    have hformula :
        v ^ 2 - u * extremalSupp v = (v ^ 2 - u ^ 2) / (2 * (1 - u)) := by
      unfold extremalSupp extremalMid
      rw [← hu]
      field_simp [ne_of_gt hu0, ne_of_gt (sub_pos.mpr hu1)]
      ring
    rw [hformula]
    apply div_nonneg
    · nlinarith
    · nlinarith
  have hw0num :
      0 ≤ v ^ 2 - u * extremalSupp v - u + extremalSupp v := by
    have hformula :
        v ^ 2 - u * extremalSupp v - u + extremalSupp v =
          (v ^ 2 - u ^ 2) / (2 * u) := by
      unfold extremalSupp extremalMid
      rw [← hu]
      field_simp [ne_of_gt hu0, ne_of_gt (sub_pos.mpr hu1)]
      ring
    rw [hformula]
    apply div_nonneg
    · nlinarith
    · positivity
  have hw0formula :
      extremalW0 v =
        (v ^ 2 - u * extremalSupp v - u + extremalSupp v) / extremalSupp v := by
    unfold extremalW0 extremalW1 extremalW2
    rw [← hu]
    field_simp [ne_of_gt hx.1, ne_of_gt (sub_pos.mpr hx.2)]
    ring
  constructor
  · rw [hw0formula]
    exact div_nonneg hw0num (le_of_lt hx.1)
  constructor
  · unfold extremalW1
    apply div_nonneg
    · exact sub_nonneg.mpr (le_of_lt hmem.1)
    · apply mul_nonneg
      · exact le_of_lt hx.1
      · exact sub_nonneg.mpr (le_of_lt hx.2)
  · unfold extremalW2
    apply div_nonneg hw2num
    exact sub_nonneg.mpr (le_of_lt hx.2)

/-- **Raw moments of the extremal law.** For `k ≥ 1`, `∫ yᵏ ∂(extremalMeasure v) = w₁ xᵥᵏ + w₂`
(the mass at `0` contributes nothing, the mass at `1` contributes `w₂`). Proof: expand via
`integral_add_measure`, `integral_smul_measure`, `integral_dirac`, using `w_i ≥ 0` to convert
`ENNReal.ofReal wᵢ` back to `wᵢ`, and `(0:ℝ)^k = 0`, `(1:ℝ)^k = 1`. -/
theorem extremalMeasure_moment_pow (v : ℝ) (hv0 : 0 < v) (hv1 : v < 1) {k : ℕ} (hk : 1 ≤ k) :
    moment (extremalMeasure v) k = extremalW1 v * (extremalSupp v) ^ k + extremalW2 v := by
  have hw := extremalW_nonneg v hv0 hv1
  have hk0 : k ≠ 0 := by omega
  let f : ℝ → ℝ := fun y => y ^ k
  have hI0 : Integrable f (ENNReal.ofReal (extremalW0 v) • Measure.dirac (0 : ℝ)) :=
    Integrable.smul_measure
      (μ := Measure.dirac (0 : ℝ)) (c := ENNReal.ofReal (extremalW0 v))
      (integrable_dirac (f := f) (a := (0 : ℝ)) (by simp [f, enorm])) (by simp)
  have hI1 : Integrable f (ENNReal.ofReal (extremalW1 v) • Measure.dirac (extremalSupp v)) :=
    Integrable.smul_measure
      (μ := Measure.dirac (extremalSupp v)) (c := ENNReal.ofReal (extremalW1 v))
      (integrable_dirac (f := f) (a := extremalSupp v) (by simp [f, enorm])) (by simp)
  have hI2 : Integrable f (ENNReal.ofReal (extremalW2 v) • Measure.dirac (1 : ℝ)) :=
    Integrable.smul_measure
      (μ := Measure.dirac (1 : ℝ)) (c := ENNReal.ofReal (extremalW2 v))
      (integrable_dirac (f := f) (a := (1 : ℝ)) (by simp [f, enorm])) (by simp)
  unfold moment extremalMeasure
  change ∫ y, f y ∂(ENNReal.ofReal (extremalW0 v) • Measure.dirac (0 : ℝ)
      + ENNReal.ofReal (extremalW1 v) • Measure.dirac (extremalSupp v)
      + ENNReal.ofReal (extremalW2 v) • Measure.dirac (1 : ℝ)) =
    extremalW1 v * (extremalSupp v) ^ k + extremalW2 v
  rw [integral_add_measure (hI0.add_measure hI1) hI2]
  rw [integral_add_measure hI0 hI1]
  rw [integral_smul_measure, integral_smul_measure, integral_smul_measure]
  simp [f, hw.1, hw.2.1, hw.2.2, hk0, smul_eq_mul]

/-- `extremalMeasure v` is a probability measure (total mass `w₀ + w₁ + w₂ = 1`, weights `≥ 0`). -/
theorem extremalMeasure_isProb (v : ℝ) (hv0 : 0 < v) (hv1 : v < 1) :
    IsProbabilityMeasure (extremalMeasure v) := by
  have hw := extremalW_nonneg v hv0 hv1
  rw [isProbabilityMeasure_iff]
  unfold extremalMeasure
  rw [Measure.add_apply, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.smul_apply]
  simp only [Measure.dirac_apply, Set.indicator_of_mem, Set.mem_univ, Pi.one_apply,
    smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add hw.1 hw.2.1]
  rw [← ENNReal.ofReal_add (add_nonneg hw.1 hw.2.1) hw.2.2]
  have hsum : extremalW0 v + extremalW1 v + extremalW2 v = 1 := by
    unfold extremalW0
    ring
  rw [hsum]
  simp

/-- `extremalMeasure v` is a.e. supported in `[0,1]` (its atoms `0, xᵥ, 1` all lie in `[0,1]`). -/
theorem extremalMeasure_supp (v : ℝ) (hv0 : 0 < v) (hv1 : v < 1) :
    ∀ᵐ y ∂(extremalMeasure v), y ∈ Set.Icc (0 : ℝ) 1 := by
  have hx := extremalSupp_mem v hv0 hv1
  rw [ae_iff]
  change (extremalMeasure v) {y : ℝ | y ∉ Set.Icc (0 : ℝ) 1} = 0
  unfold extremalMeasure
  rw [Measure.add_apply, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.smul_apply]
  simp [hx.1.le, hx.2.le]

/-- First moment: `∫ y ∂(extremalMeasure v) = μᵥ`. Algebraic: `w₁ xᵥ + w₂ = μᵥ`. -/
theorem extremalMeasure_moment1 (v : ℝ) (hv0 : 0 < v) (hv1 : v < 1) :
    moment (extremalMeasure v) 1 = maximizingRoot v := by
  rw [extremalMeasure_moment_pow v hv0 hv1 (by norm_num : 1 ≤ 1)]
  have hmem := maximizingRoot_mem v hv0 hv1
  have hx := extremalSupp_mem v hv0 hv1
  set u := maximizingRoot v with hu
  unfold extremalW1 extremalW2
  rw [← hu]
  field_simp [ne_of_gt hx.1, ne_of_gt (sub_pos.mpr hx.2)]
  ring

/-- Second moment: `∫ y² ∂(extremalMeasure v) = v²`. Algebraic: `w₁ xᵥ² + w₂ = v²`. -/
theorem extremalMeasure_moment2 (v : ℝ) (hv0 : 0 < v) (hv1 : v < 1) :
    moment (extremalMeasure v) 2 = v ^ 2 := by
  rw [extremalMeasure_moment_pow v hv0 hv1 (by norm_num : 1 ≤ 2)]
  have hmem := maximizingRoot_mem v hv0 hv1
  have hx := extremalSupp_mem v hv0 hv1
  set u := maximizingRoot v with hu
  unfold extremalW1 extremalW2
  rw [← hu]
  field_simp [ne_of_gt hx.1, ne_of_gt (sub_pos.mpr hx.2)]
  ring

/-- Third moment matches the extremal `M₃`: `w₁ xᵥ³ + w₂ = extremalM3 μᵥ (v²)`. Pure algebra
(`field_simp`/`ring`) using `xᵥ = extremalMid μᵥ (v²)` and the weight formulas. -/
theorem extremalMeasure_moment3 (v : ℝ) (hv0 : 0 < v) (hv1 : v < 1) :
    moment (extremalMeasure v) 3 = extremalM3 (maximizingRoot v) (v ^ 2) := by
  rw [extremalMeasure_moment_pow v hv0 hv1 (by norm_num : 1 ≤ 3)]
  set u := maximizingRoot v with hu
  set q := v ^ 2 with hq
  have hmem : u ∈ Ioo q v := by simpa [hu, hq] using maximizingRoot_mem v hv0 hv1
  set x := extremalSupp v with hx
  have hu0 : 0 < u := lt_trans (by positivity) hmem.1
  have hu1 : u < 1 := lt_trans hmem.2 hv1
  have hm1alg : extremalW1 v * x + extremalW2 v = u := by
    have h := extremalMeasure_moment1 v hv0 hv1
    rw [extremalMeasure_moment_pow v hv0 hv1 (by norm_num : 1 ≤ 1)] at h
    simpa [hu, hx] using h
  have hm2alg : extremalW1 v * x ^ 2 + extremalW2 v = q := by
    have h := extremalMeasure_moment2 v hv0 hv1
    rw [extremalMeasure_moment_pow v hv0 hv1 (by norm_num : 1 ≤ 2)] at h
    simpa [hq, hx] using h
  have hxformula : x = (u ^ 2 - 2 * u * q + q) / (2 * u * (1 - u)) := by
    rw [hx]
    unfold extremalSupp extremalMid
    rw [← hu, ← hq]
  change extremalW1 v * x ^ 3 + extremalW2 v = extremalM3 u q
  calc
    extremalW1 v * x ^ 3 + extremalW2 v =
        (1 + x) * (extremalW1 v * x ^ 2 + extremalW2 v)
          - x * (extremalW1 v * x + extremalW2 v) := by ring
    _ = (1 + x) * q - x * u := by rw [hm1alg, hm2alg]
    _ = extremalM3 u q := by
      rw [hxformula]
      unfold extremalM3
      field_simp [ne_of_gt hu0, ne_of_gt (sub_pos.mpr hu1),
        sub_ne_zero.mpr (ne_of_lt hu1)]
      ring

/-- Fourth moment matches the extremal `M₄`: `w₁ xᵥ⁴ + w₂ = extremalM4 μᵥ (v²)`. Pure algebra. -/
theorem extremalMeasure_moment4 (v : ℝ) (hv0 : 0 < v) (hv1 : v < 1) :
    moment (extremalMeasure v) 4 = extremalM4 (maximizingRoot v) (v ^ 2) := by
  rw [extremalMeasure_moment_pow v hv0 hv1 (by norm_num : 1 ≤ 4)]
  set u := maximizingRoot v with hu
  set q := v ^ 2 with hq
  have hmem : u ∈ Ioo q v := by simpa [hu, hq] using maximizingRoot_mem v hv0 hv1
  set x := extremalSupp v with hx
  have hu0 : 0 < u := lt_trans (by positivity) hmem.1
  have hu1 : u < 1 := lt_trans hmem.2 hv1
  have hm2alg : extremalW1 v * x ^ 2 + extremalW2 v = q := by
    have h := extremalMeasure_moment2 v hv0 hv1
    rw [extremalMeasure_moment_pow v hv0 hv1 (by norm_num : 1 ≤ 2)] at h
    simpa [hq, hx] using h
  have hm3alg : extremalW1 v * x ^ 3 + extremalW2 v = extremalM3 u q := by
    have h := extremalMeasure_moment3 v hv0 hv1
    rw [extremalMeasure_moment_pow v hv0 hv1 (by norm_num : 1 ≤ 3)] at h
    simpa [hu, hq, hx] using h
  have hxformula : x = (u ^ 2 - 2 * u * q + q) / (2 * u * (1 - u)) := by
    rw [hx]
    unfold extremalSupp extremalMid
    rw [← hu, ← hq]
  change extremalW1 v * x ^ 4 + extremalW2 v = extremalM4 u q
  calc
    extremalW1 v * x ^ 4 + extremalW2 v =
        (1 + x) * (extremalW1 v * x ^ 3 + extremalW2 v)
          - x * (extremalW1 v * x ^ 2 + extremalW2 v) := by ring
    _ = (1 + x) * extremalM3 u q - x * q := by rw [hm2alg, hm3alg]
    _ = extremalM4 u q := by
      rw [hxformula]
      unfold extremalM3 extremalM4
      field_simp [ne_of_gt hu0, ne_of_gt (sub_pos.mpr hu1),
        sub_ne_zero.mpr (ne_of_lt hu1)]
      ring

/-- The extremal law is **admissible**. -/
theorem extremalMeasure_admissible (v : ℝ) (hv0 : 0 < v) (hv1 : v < 1) :
    Admissible v (extremalMeasure v) := by
  refine ⟨extremalMeasure_isProb v hv0 hv1, extremalMeasure_supp v hv0 hv1, ?_⟩
  have := extremalMeasure_moment2 v hv0 hv1
  simpa [moment] using this

/-- **The extremal law realizes `ρ(v)`.** Its residual equals the envelope value:
`l2ResidualQuadratic (extremalMeasure v) = rhoEnvelope v`.

Proof: the four moments are `(μᵥ, v², extremalM3 μᵥ (v²), extremalM4 μᵥ (v²))`, so
`l2ResidualQuadratic = momentResidual μᵥ (v²) (extremalM3 …) (extremalM4 …)`, which equals
`momentEnvelope μᵥ (v²) = rhoEnvelope v` by `MomentAlgebra.extremalResidual_eq_envelope`
(nondegeneracy `μᵥ ≠ 0, 1` and `μᵥ² ≠ v²` from `μᵥ ∈ (v², v)`). -/
theorem extremalMeasure_residual (v : ℝ) (hv0 : 0 < v) (hv1 : v < 1) :
    l2ResidualQuadratic (extremalMeasure v) = rhoEnvelope v := by
  have hmem := maximizingRoot_mem v hv0 hv1
  set u := maximizingRoot v with hu
  have hu0 : u ≠ 0 := ne_of_gt (lt_trans (by positivity) hmem.1)
  have hu1 : u ≠ 1 := ne_of_lt (lt_trans hmem.2 hv1)
  have huq : u ^ 2 ≠ v ^ 2 := by
    have hu0' : (0 : ℝ) < u := lt_trans (by positivity) hmem.1
    have : u ^ 2 < v ^ 2 := by nlinarith [hmem.1, hmem.2, hu0']
    exact ne_of_lt this
  have hm1 := extremalMeasure_moment1 v hv0 hv1
  have hm2 := extremalMeasure_moment2 v hv0 hv1
  have hm3 := extremalMeasure_moment3 v hv0 hv1
  have hm4 := extremalMeasure_moment4 v hv0 hv1
  have hkey := extremalResidual_eq_envelope u (v ^ 2) hu0 hu1 huq
  unfold l2ResidualQuadratic
  rw [hm1, hm2, hm3, hm4]
  -- `extremalM1 u = u`, so `momentResidual u (v²) (extremalM3 u (v²)) (extremalM4 u (v²))`
  -- is exactly the LHS of `hkey`.
  simpa [extremalM1, rhoEnvelope, hu] using hkey

/-- **Envelope attainment.** For `v ∈ (0,1)` there is an admissible law whose residual is exactly
`ρ(v)`.  Together with the upper bound this makes `ρ(v)` the supremum. -/
theorem rho_envelope_attained (v : ℝ) (hv0 : 0 < v) (hv1 : v < 1) :
    ∃ μ : Measure ℝ, Admissible v μ ∧ l2ResidualQuadratic μ = rhoEnvelope v :=
  ⟨extremalMeasure v, extremalMeasure_admissible v hv0 hv1, extremalMeasure_residual v hv0 hv1⟩

end Causalean.Stat.MomentProblems.BoundedOutcomeEnvelope
