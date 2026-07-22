/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Stat.Coupling.ProductLossMonotoneCoupling.Coupling

/-!
# Fréchet–Hoeffding bounds on the joint cdf

For a coupling `π ∈ Π(μ, ν)` with marginal cdfs `F = cdf μ`, `G = cdf ν`, the
**joint cdf** `H_π x y = π (Iic x ×ˢ Iic y)` obeys the pointwise
Fréchet–Hoeffding bounds

    `max (F x + G y - 1) 0 ≤ H_π x y ≤ min (F x) (G y)`.

The upper bound is `H ≤ F` and `H ≤ G` (monotonicity of measure under the two
projections onto the marginals); the lower bound is inclusion–exclusion on the
complement. Both bounds are *attained*:

* the comonotone coupling attains the **upper** bound `H = min (F, G)`;
* the countermonotone coupling attains the **lower** bound `H = max (F+G-1, 0)`.

This is the pointwise ordering that, integrated against the Hoeffding covariance
identity, yields the optimality of the monotone couplings.
-/

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Set
open Causalean.Stat

variable {π : Measure (ℝ × ℝ)} {μ ν : Measure ℝ}

/-- The **joint cdf** of a measure `π` on `ℝ × ℝ`: the mass of the lower-left
quadrant `Iic x ×ˢ Iic y`, as a real number. -/
noncomputable def jointCdf (π : Measure (ℝ × ℝ)) (x y : ℝ) : ℝ :=
  (π (Iic x ×ˢ Iic y)).toReal

/-- **Fréchet–Hoeffding upper bound.** For any coupling `π` of `(μ, ν)`, the
joint cdf is bounded above by the smaller marginal cdf:
`H_π x y ≤ min (cdf μ x) (cdf ν y)`. Proof: `Iic x ×ˢ Iic y ⊆ Iic x ×ˢ univ` and
`⊆ univ ×ˢ Iic y`, whose masses are `μ (Iic x)` and `ν (Iic y)` via the
marginals. -/
theorem frechet_hoeffding_upper (h : IsCoupling π μ ν) (x y : ℝ) :
    jointCdf π x y ≤ min (cdf μ x) (cdf ν y) := by
  letI : IsProbabilityMeasure π := h.isProbabilityMeasure
  haveI : IsProbabilityMeasure μ := by
    rw [← h.map_fst]
    exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  haveI : IsProbabilityMeasure ν := by
    rw [← h.map_snd]
    exact Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  apply le_min
  · unfold jointCdf
    change (π (Iic x ×ˢ Iic y)).toReal ≤ cdf μ x
    rw [cdf_eq_real]
    rw [measureReal_def]
    apply ENNReal.toReal_mono
    · exact measure_ne_top μ _
    · calc
        π (Iic x ×ˢ Iic y) ≤ π (Iic x ×ˢ (univ : Set ℝ)) := by
          exact measure_mono (by
            intro p hp
            exact ⟨hp.1, trivial⟩)
        _ = π (Prod.fst ⁻¹' Iic x) := by
          congr 1
          ext p
          simp
        _ = (π.map Prod.fst) (Iic x) := by
          rw [Measure.map_apply]
          exact measurable_fst
          exact measurableSet_Iic
        _ = μ (Iic x) := by rw [h.map_fst]
  · unfold jointCdf
    change (π (Iic x ×ˢ Iic y)).toReal ≤ cdf ν y
    rw [cdf_eq_real]
    rw [measureReal_def]
    apply ENNReal.toReal_mono
    · exact measure_ne_top ν _
    · calc
        π (Iic x ×ˢ Iic y) ≤ π ((univ : Set ℝ) ×ˢ Iic y) := by
          exact measure_mono (by
            intro p hp
            exact ⟨trivial, hp.2⟩)
        _ = π (Prod.snd ⁻¹' Iic y) := by
          congr 1
          ext p
          simp
        _ = (π.map Prod.snd) (Iic y) := by
          rw [Measure.map_apply]
          exact measurable_snd
          exact measurableSet_Iic
        _ = ν (Iic y) := by rw [h.map_snd]

/-- **Fréchet–Hoeffding lower bound.** For any coupling `π` of `(μ, ν)`,
`max (cdf μ x + cdf ν y - 1) 0 ≤ H_π x y`. Proof: inclusion–exclusion on the
complement of `Iic x ×ˢ Iic y`, using `π` a probability measure and the two
marginals. -/
theorem frechet_hoeffding_lower (h : IsCoupling π μ ν) (x y : ℝ) :
    max (cdf μ x + cdf ν y - 1) 0 ≤ jointCdf π x y := by
  letI : IsProbabilityMeasure π := h.isProbabilityMeasure
  haveI : IsProbabilityMeasure μ := by
    rw [← h.map_fst]
    exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  haveI : IsProbabilityMeasure ν := by
    rw [← h.map_snd]
    exact Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  let A : Set (ℝ × ℝ) := Prod.fst ⁻¹' Iic x
  let B : Set (ℝ × ℝ) := Prod.snd ⁻¹' Iic y
  have hB_meas : MeasurableSet B := measurableSet_Iic.preimage measurable_snd
  have hquad : (Iic (x, y) : Set (ℝ × ℝ)) = A ∩ B := by
    ext p
    constructor
    · intro hp
      exact ⟨hp.1, hp.2⟩
    · intro hp
      exact ⟨hp.1, hp.2⟩
  have hA : π.real A = cdf μ x := by
    rw [cdf_eq_real]
    rw [measureReal_def]
    congr 1
    calc
      π A = (π.map Prod.fst) (Iic x) := by
        rw [Measure.map_apply]
        exact measurable_fst
        exact measurableSet_Iic
      _ = μ (Iic x) := by rw [h.map_fst]
  have hB : π.real B = cdf ν y := by
    rw [cdf_eq_real]
    rw [measureReal_def]
    congr 1
    calc
      π B = (π.map Prod.snd) (Iic y) := by
        rw [Measure.map_apply]
        exact measurable_snd
        exact measurableSet_Iic
      _ = ν (Iic y) := by rw [h.map_snd]
  have hinc := measureReal_union_add_inter (μ := π) (s := A) (t := B) hB_meas
  have hUle : π.real (A ∪ B) ≤ 1 := by
    calc
      π.real (A ∪ B) ≤ π.real (univ : Set (ℝ × ℝ)) := by
        exact measureReal_mono (subset_univ _) (measure_ne_top π _)
      _ = 1 := by simp [Measure.real]
  apply max_le
  · unfold jointCdf
    change cdf μ x + cdf ν y - 1 ≤ π.real (A ∩ B)
    linarith
  · unfold jointCdf
    exact ENNReal.toReal_nonneg

end Causalean.Stat
