/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Stat.Quantile.Quantile
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Probability integral transform (PIT) for the quantile function

This file proves the **probability-integral-transform**: if `μ` is a Borel
probability measure on `ℝ`, then pushing the uniform measure on `(0,1)` through
the (lower) quantile function `Causalean.Stat.quantile μ` recovers `μ`:

    `(volume.restrict (Ioo 0 1)).map (quantile μ) = μ`.

The proof rests on the Galois characterisation `quantile_le_iff` from
`Causalean.Stat.Quantile`:

    `quantile μ τ ≤ x ↔ τ ≤ cdf μ x`     (for interior `0 < τ < 1`),

so that, writing `U` for a `Unif(0,1)` variable,
`P(quantile μ U ≤ x) = P(U ≤ cdf μ x) = cdf μ x`, i.e. the pushforward and `μ`
have the same values on every left-ray `Iic x`, hence are equal by
`Measure.ext_of_Iic`.

These are the reusable primitives feeding the comonotone / countermonotone
optimal couplings in `Coupling.lean`.
-/

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Set
open Causalean.Stat

/-- The uniform probability measure on the open unit interval `(0,1)`, realised
as Lebesgue measure restricted to `Ioo 0 1`. -/
noncomputable def unifOI : Measure ℝ := volume.restrict (Ioo (0 : ℝ) 1)

/-- `unifOI` is a probability measure: `volume (Ioo 0 1) = 1`. -/
instance instIsProbabilityMeasure_unifOI : IsProbabilityMeasure unifOI := by
  constructor
  rw [unifOI, Measure.restrict_apply_univ, Real.volume_Ioo]
  norm_num
  rfl

/-- The quantile function is monotone on the open unit interval `(0,1)`
(immediate from `quantile_mono`, whose hypotheses `0 < τ`, `τ' < 1` hold
throughout the interior). -/
lemma monotoneOn_quantile (μ : Measure ℝ) :
    MonotoneOn (quantile μ) (Ioo (0 : ℝ) 1) := by
  intro a ha b hb hab
  exact quantile_mono ha.1 hb.2 hab

/-- The quantile function is a.e.-measurable with respect to the uniform measure
on `(0,1)`; it is monotone there, and a monotone function is measurable. -/
lemma aemeasurable_quantile_unifOI (μ : Measure ℝ) :
    AEMeasurable (quantile μ) unifOI := by
  exact aemeasurable_restrict_of_monotoneOn measurableSet_Ioo (monotoneOn_quantile μ)

private lemma volume_Ioo_zero_one_inter_Iic {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    volume (Ioo (0 : ℝ) 1 ∩ Iic c) = ENNReal.ofReal c := by
  rcases lt_or_eq_of_le hc1 with hc1lt | rfl
  · have hset : Ioo (0 : ℝ) 1 ∩ Iic c = Ioc (0 : ℝ) c := by
      ext u
      constructor
      · intro h
        exact ⟨h.1.1, h.2⟩
      · intro h
        exact ⟨⟨h.1, lt_of_le_of_lt h.2 hc1lt⟩, h.2⟩
    rw [hset, Real.volume_Ioc]
    congr
    ring
  · have hset : Ioo (0 : ℝ) 1 ∩ Iic (1 : ℝ) = Ioo (0 : ℝ) 1 := by
      ext u
      constructor
      · intro h
        exact h.1
      · intro h
        exact ⟨h, h.2.le⟩
    rw [hset, Real.volume_Ioo]
    norm_num
    rfl

/-- **Probability integral transform.** For a Borel probability measure `μ` on
`ℝ`, the pushforward of `Unif(0,1)` under the quantile function `quantile μ`
equals `μ`.

The proof compares the two measures on the rays `Iic x`. For a uniform variable
`U`, `{u ∈ (0,1) | quantile μ u ≤ x} = {u ∈ (0,1) | u ≤ cdf μ x}` by
`quantile_le_iff`, whose Lebesgue measure is `cdf μ x = μ (Iic x)`; then
`Measure.ext_of_Iic` closes the equality. -/
theorem quantile_map_uniform (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    unifOI.map (quantile μ) = μ := by
  refine Measure.ext_of_Iic (unifOI.map (quantile μ)) μ (fun x => ?_)
  rw [Measure.map_apply₀ (aemeasurable_quantile_unifOI μ) measurableSet_Iic.nullMeasurableSet]
  rw [unifOI, Measure.restrict_apply' measurableSet_Ioo]
  have hset :
      quantile μ ⁻¹' Iic x ∩ Ioo (0 : ℝ) 1 = Ioo (0 : ℝ) 1 ∩ Iic (cdf μ x) := by
    ext u
    constructor
    · intro h
      exact ⟨h.2, (quantile_le_iff h.2.1 h.2.2).mp h.1⟩
    · intro h
      exact ⟨(quantile_le_iff h.1.1 h.1.2).mpr h.2, h.1⟩
  rw [hset, ← ProbabilityTheory.ofReal_cdf μ x]
  exact volume_Ioo_zero_one_inter_Iic (ProbabilityTheory.cdf_nonneg μ x)
    (ProbabilityTheory.cdf_le_one μ x)

end Causalean.Stat
