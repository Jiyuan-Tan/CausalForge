/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Weighted support from a finite probability measure

Bridge connecting the finite weighted-support tower (`Causalean/Panel/Weighted/*`) to a
probability measure on a finite measurable space.  For a probability measure `μ`
on a `Fintype` `R` with measurable singletons, the point masses
`ω_r := (μ {r}).toReal` form a `WeightedSupport R` whose observed set is the
positive-mass support, and the weighted inner product coincides with the
`L²(μ)` integral pairing:

    ⟨A, B⟩_ω  =  ∫ A·B dμ.

This lets the measure-theoretic cell-bridge layer (`Residualization` /
`CellBridge`) and the finite weighted-support FWL tower (`Weighted/FWL`) be used
interchangeably on a finite probability space.
-/

import Causalean.Panel.Weighted.InnerProduct
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-! # Weighted supports from probability measures

This file connects the finite weighted-support algebra to probability measures
on finite measurable spaces. The construction `ofProbabilityMeasure` turns point
masses into a `WeightedSupport` whose observed set is the positive-mass support,
and `ofProbabilityMeasure_weight` exposes the resulting atom weights.

The main bridge theorem, `ip_eq_integral`, identifies the finite weighted inner
product with the corresponding `L²(μ)` integral pairing. This lets
measure-theoretic cell bridges and finite weighted-support Frisch-Waugh-Lovell
arguments be used interchangeably on a finite probability space. -/

open scoped BigOperators
open MeasureTheory

namespace Causalean
namespace Panel.Weighted
namespace WeightedSupport

variable {R : Type*} [Fintype R] [DecidableEq R]
  [MeasurableSpace R] [MeasurableSingletonClass R]

/-- A probability measure on a finite measurable space induces a weighted
support whose weights are point masses and whose observed records have positive
mass.

The observed set is the positive-mass support. -/
noncomputable def ofProbabilityMeasure (μ : Measure R) [IsProbabilityMeasure μ] :
    WeightedSupport R where
  observed := Finset.univ.filter (fun r => 0 < (μ {r}).toReal)
  observed_nonempty := by
    classical
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    -- If no atom is positive, every atom has zero real mass, so the total
    -- real mass is 0, contradicting `μ.real univ = 1`.
    have hzero : ∀ r : R, (μ {r}).toReal = 0 := by
      intro r
      by_contra hr
      have hpos : 0 < (μ {r}).toReal :=
        lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hr)
      have : r ∈ Finset.univ.filter (fun r => 0 < (μ {r}).toReal) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ r, hpos⟩
      rw [h] at this
      exact absurd this (Finset.notMem_empty r)
    have hsum : ∑ r : R, (μ {r}).toReal = 1 := by
      have := (MeasureTheory.sum_measureReal_preimage_singleton
        (μ := μ) (s := (Finset.univ : Finset R)) (f := id)
        (hf := by intro r _; exact measurableSet_singleton r)
        (h := by intro r _; exact measure_ne_top μ {r}))
      simpa [Measure.real, Set.preimage_id, MeasurableSet.univ,
        measure_univ] using this
    rw [Finset.sum_congr rfl (fun r _ => hzero r)] at hsum
    simp at hsum
  weight := fun r => (μ {r}).toReal
  weight_pos := by
    intro r hr
    exact (Finset.mem_filter.mp hr).2
  weight_zero_off := by
    intro r hr
    by_contra hne
    have hpos : 0 < (μ {r}).toReal :=
      lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hne)
    exact hr (Finset.mem_filter.mpr ⟨Finset.mem_univ r, hpos⟩)
  weight_sum_one := by
    classical
    -- The filtered sum equals the full sum because off-support terms vanish.
    have hfull : ∑ r : R, (μ {r}).toReal = 1 := by
      have := (MeasureTheory.sum_measureReal_preimage_singleton
        (μ := μ) (s := (Finset.univ : Finset R)) (f := id)
        (hf := by intro r _; exact measurableSet_singleton r)
        (h := by intro r _; exact measure_ne_top μ {r}))
      simpa [Measure.real, Set.preimage_id, MeasurableSet.univ,
        measure_univ] using this
    rw [← hfull]
    refine (Finset.sum_filter_of_ne ?_)
    intro r _ hne
    exact lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hne)

/-- The induced weighted support assigns each record the point mass of that
record under the probability measure. -/
@[simp] lemma ofProbabilityMeasure_weight (μ : Measure R) [IsProbabilityMeasure μ]
    (r : R) : (ofProbabilityMeasure μ).weight r = (μ {r}).toReal := rfl

/-- The weighted inner product induced by a finite probability measure is the
`L²(μ)` integral pairing `∫ A·B dμ`. -/
theorem ip_eq_integral (μ : Measure R) [IsProbabilityMeasure μ] (A B : R → ℝ) :
    (ofProbabilityMeasure μ).ip A B = ∫ r, A r * B r ∂μ := by
  classical
  -- The integral over a finite measurable space is the atom-weighted sum.
  rw [MeasureTheory.integral_fintype _ (Integrable.of_finite)]
  -- `ip` sums over `observed`; extend to all of `R` since off-support weights
  -- are zero.
  unfold ip
  rw [Finset.sum_subset (Finset.subset_univ _)]
  · refine Finset.sum_congr rfl ?_
    intro r _
    simp only [ofProbabilityMeasure_weight, Measure.real, smul_eq_mul]
    ring
  · intro r _ hr
    have hzero : (μ {r}).toReal = 0 := by
      by_contra hne
      have hpos : 0 < (μ {r}).toReal :=
        lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hne)
      exact hr (Finset.mem_filter.mpr ⟨Finset.mem_univ r, hpos⟩)
    simp [ofProbabilityMeasure_weight, hzero]

end WeightedSupport
end Panel.Weighted
end Causalean
