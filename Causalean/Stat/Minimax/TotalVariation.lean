/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Total variation distance between probability measures

The statistical total variation distance

  `tvDist μ ν = ⨆ A measurable, |μ.real A − ν.real A|`

between two measures on a common space.  Mathlib only carries
`SignedMeasure.totalVariation` (the Jordan-decomposition norm); this file
develops the elementary *testing* characterization that drives Le Cam's
two-point method (`Causalean/Stat/Minimax/LeCam.lean`).

Main results (all under `[IsProbabilityMeasure μ] [IsProbabilityMeasure ν]`):

* `tvDist_nonneg`, `tvDist_le_one` — range `[0,1]`;
* `tvDist_comm` — symmetry;
* `measureReal_sub_le_tvDist` — each signed gap `ν.real A − μ.real A` is `≤ tvDist`;
* `one_sub_tvDist_le_test` — **the testing bound** `1 − tvDist μ ν ≤ μ.real A + ν.real Aᶜ`,
  i.e. the total error of any test (rejection region `A`) is at least `1 − tvDist`.

These are deliberately project-agnostic and are candidates for upstream
contribution to Mathlib.
-/

import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Total Variation Distance

This file defines the statistical total variation distance between two probability
measures on a common measurable space. It develops elementary bounds and the
testing inequality that underlies Le Cam's two-point minimax method. -/

namespace Causalean.Stat

open MeasureTheory
open scoped ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ ν : Measure Ω}

/-- The statistical total variation distance between two measures:
the supremum, over measurable sets `A`, of the gap `|μ.real A − ν.real A|`. -/
noncomputable def tvDist (μ ν : Measure Ω) : ℝ :=
  ⨆ A : {A : Set Ω // MeasurableSet A}, |μ.real A.1 - ν.real A.1|

variable [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- Every term of the supremum defining `tvDist` is bounded by `1`. -/
theorem abs_measureReal_sub_le_one (A : Set Ω) : |μ.real A - ν.real A| ≤ 1 := by
  have hμ : μ.real A ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨measureReal_nonneg, by
      have := measureReal_mono (μ := μ) (Set.subset_univ A) (measure_ne_top μ _)
      simpa [probReal_univ] using this⟩
  have hν : ν.real A ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨measureReal_nonneg, by
      have := measureReal_mono (μ := ν) (Set.subset_univ A) (measure_ne_top ν _)
      simpa [probReal_univ] using this⟩
  rw [abs_le]
  constructor <;> [nlinarith [hμ.1, hμ.2, hν.1, hν.2]; nlinarith [hμ.1, hμ.2, hν.1, hν.2]]

/-- The family defining `tvDist` is bounded above (by `1`). -/
theorem bddAbove_tvDist_range :
    BddAbove (Set.range fun A : {A : Set Ω // MeasurableSet A} => |μ.real A.1 - ν.real A.1|) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨A, rfl⟩
  exact abs_measureReal_sub_le_one A.1

/-- For a measurable set `A`, the gap `|μ.real A − ν.real A|` is at most `tvDist μ ν`. -/
theorem abs_measureReal_sub_le_tvDist {A : Set Ω} (hA : MeasurableSet A) :
    |μ.real A - ν.real A| ≤ tvDist μ ν :=
  le_ciSup bddAbove_tvDist_range (⟨A, hA⟩ : {A : Set Ω // MeasurableSet A})

/-- The signed gap `ν.real A − μ.real A` is at most `tvDist μ ν`. -/
theorem measureReal_sub_le_tvDist {A : Set Ω} (hA : MeasurableSet A) :
    ν.real A - μ.real A ≤ tvDist μ ν :=
  (le_abs_self _).trans <| by
    rw [abs_sub_comm]; exact abs_measureReal_sub_le_tvDist hA

/-- Total variation distance between probability measures is nonnegative. -/
theorem tvDist_nonneg : 0 ≤ tvDist μ ν := by
  have := abs_measureReal_sub_le_tvDist (μ := μ) (ν := ν) MeasurableSet.empty
  simpa using (abs_nonneg _).trans this

/-- Total variation distance between probability measures is at most one. -/
theorem tvDist_le_one : tvDist μ ν ≤ 1 :=
  ciSup_le fun A => abs_measureReal_sub_le_one A.1

/-- `tvDist` is symmetric. -/
theorem tvDist_symm (μ ν : Measure Ω) : tvDist μ ν = tvDist ν μ := by
  unfold tvDist
  congr 1
  ext A
  rw [abs_sub_comm]

/-- **Le Cam testing bound.** For any measurable rejection region `A`, the total
testing error `μ.real A + ν.real Aᶜ` is at least `1 − tvDist μ ν`.  This is the
single inequality on which the two-point method rests. -/
theorem one_sub_tvDist_le_test {A : Set Ω} (hA : MeasurableSet A) :
    1 - tvDist μ ν ≤ μ.real A + ν.real Aᶜ := by
  have hcompl : ν.real Aᶜ = 1 - ν.real A := by
    rw [measureReal_compl hA, probReal_univ]
  rw [hcompl]
  have h := measureReal_sub_le_tvDist (μ := μ) (ν := ν) hA
  linarith

/-- The expectation gap of a measurable statistic confined to an interval of width `c` is at most
that width times the total-variation distance between the two probability laws.

This is the bounded-function side of the dual characterization of total variation, normalized
using the supremum over measurable events. -/
theorem tvDist_integral_range (μ ν : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : Ω → ℝ) (hf : Measurable f) (a c : ℝ) (hc : 0 ≤ c)
    (hrange : ∀ x, f x ∈ Set.Icc a (a + c)) :
    |(∫ x, f x ∂μ) - ∫ x, f x ∂ν| ≤ tvDist μ ν * c := by
  let g : Ω → ℝ := fun x => f x - a
  have hg : Measurable g := hf.sub_const a
  have hg0 : ∀ x, 0 ≤ g x := fun x => by
    dsimp [g]
    linarith [(hrange x).1]
  have hgc : ∀ x, g x ≤ c := fun x => by
    dsimp [g]
    linarith [(hrange x).2]
  have hgint (ρ : Measure Ω) [IsProbabilityMeasure ρ] : Integrable g ρ :=
    Integrable.of_bound hg.aestronglyMeasurable c
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hg0 x)]
        exact hgc x)
  have htail_meas (ρ : Measure Ω) :
      Measurable (fun t : ℝ => ρ.real {x | t ≤ g x}) := by
    change Measurable fun t : ℝ => (ρ {x | t ≤ g x}).toReal
    exact Measurable.ennreal_toReal
      (Antitone.measurable (fun _ _ hst => measure_mono (fun _ hx => hst.trans hx)))
  have htail_int (ρ : Measure Ω) [IsProbabilityMeasure ρ] :
      IntegrableOn (fun t : ℝ => ρ.real {x | t ≤ g x}) (Set.Ioc 0 c) := by
    exact Integrable.of_bound
      ((htail_meas ρ).aestronglyMeasurable.mono_measure Measure.restrict_le_self) 1
      (Filter.Eventually.of_forall fun t => by
        rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
        exact measureReal_le_one)
  have hlayer (ρ : Measure Ω) [IsProbabilityMeasure ρ] :
      ∫ x, g x ∂ρ = ∫ t in Set.Ioc 0 c, ρ.real {x | t ≤ g x} := by
    exact (hgint ρ).integral_eq_integral_Ioc_meas_le
      (Filter.Eventually.of_forall hg0) (Filter.Eventually.of_forall hgc)
  have hfint (ρ : Measure Ω) [IsProbabilityMeasure ρ] : Integrable f ρ :=
    Integrable.of_bound hf.aestronglyMeasurable (|a| + c)
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]
        calc
          |f x| = |a + g x| := by simp [g]
          _ ≤ |a| + |g x| := abs_add_le _ _
          _ ≤ |a| + c := by
            gcongr
            rw [abs_of_nonneg (hg0 x)]
            exact hgc x)
  have hshift (ρ : Measure Ω) [IsProbabilityMeasure ρ] :
      ∫ x, g x ∂ρ = (∫ x, f x ∂ρ) - a := by
    rw [show g = fun x => f x - a from rfl,
      integral_sub (hfint ρ) (integrable_const a)]
    simp
  have heq :
      (∫ x, f x ∂μ) - ∫ x, f x ∂ν =
        (∫ x, g x ∂μ) - ∫ x, g x ∂ν := by
    rw [hshift μ, hshift ν]
    ring
  rw [heq, hlayer μ, hlayer ν, ← integral_sub (htail_int μ) (htail_int ν)]
  have hbound : ∀ᵐ t ∂volume.restrict (Set.Ioc 0 c),
      ‖μ.real {x | t ≤ g x} - ν.real {x | t ≤ g x}‖ ≤ tvDist μ ν := by
    exact Filter.Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs]
      exact abs_measureReal_sub_le_tvDist (hg measurableSet_Ici)
  calc
    |∫ t in Set.Ioc 0 c, (μ.real {x | t ≤ g x} - ν.real {x | t ≤ g x})|
        = ‖∫ t in Set.Ioc 0 c,
            (μ.real {x | t ≤ g x} - ν.real {x | t ≤ g x})‖ := by
          rw [Real.norm_eq_abs]
    _ ≤ tvDist μ ν * volume.real (Set.Ioc 0 c) :=
      norm_setIntegral_le_of_norm_le_const_ae (by simp) hbound
    _ = tvDist μ ν * c := by
      rw [measureReal_def, Real.volume_Ioc,
        ENNReal.toReal_ofReal (by linarith : 0 ≤ c - 0)]
      ring

/-- A measurable statistic that lies almost surely in an interval of width `c` under both laws has
an expectation gap no larger than `c` times their total-variation distance.

The statistic may violate the range restriction on different null sets for the two probability
measures. -/
theorem tvDist_integral_le_of_range_ae (μ ν : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : Ω → ℝ) (hf : Measurable f) (a c : ℝ) (hc : 0 ≤ c)
    (hμ : ∀ᵐ x ∂μ, f x ∈ Set.Icc a (a + c))
    (hν : ∀ᵐ x ∂ν, f x ∈ Set.Icc a (a + c)) :
    |(∫ x, f x ∂μ) - ∫ x, f x ∂ν| ≤ tvDist μ ν * c := by
  let f' : Ω → ℝ := fun x => max a (min (a + c) (f x))
  have hf' : Measurable f' := measurable_const.max (measurable_const.min hf)
  have hac : a ≤ a + c := by linarith
  have hrange : ∀ x, f' x ∈ Set.Icc a (a + c) := fun x => by
    constructor
    · exact le_max_left _ _
    · exact max_le hac (min_le_left _ _)
  have hμ_eq : f' =ᵐ[μ] f := by
    filter_upwards [hμ] with x hx
    simp only [f', min_eq_right hx.2, max_eq_right hx.1]
  have hν_eq : f' =ᵐ[ν] f := by
    filter_upwards [hν] with x hx
    simp only [f', min_eq_right hx.2, max_eq_right hx.1]
  rw [← integral_congr_ae hμ_eq, ← integral_congr_ae hν_eq]
  exact tvDist_integral_range μ ν f' hf' a c hc hrange

/-- A measurable statistic bounded in absolute value by `M` almost surely under both laws has an
expectation gap no larger than `2M` times their total-variation distance.

The factor two is the width of the symmetric interval from `-M` to `M`. -/
theorem tvDist_integral_le_of_abs_le_ae (μ ν : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : Ω → ℝ) (hf : Measurable f) (M : ℝ) (hM : 0 ≤ M)
    (hμ : ∀ᵐ x ∂μ, |f x| ≤ M) (hν : ∀ᵐ x ∂ν, |f x| ≤ M) :
    |(∫ x, f x ∂μ) - ∫ x, f x ∂ν| ≤ 2 * M * tvDist μ ν := by
  have hμ_range : ∀ᵐ x ∂μ, f x ∈ Set.Icc (-M) (-M + 2 * M) := by
    filter_upwards [hμ] with x hx
    have hx' := abs_le.mp hx
    constructor <;> linarith
  have hν_range : ∀ᵐ x ∂ν, f x ∈ Set.Icc (-M) (-M + 2 * M) := by
    filter_upwards [hν] with x hx
    have hx' := abs_le.mp hx
    constructor <;> linarith
  calc
    |(∫ x, f x ∂μ) - ∫ x, f x ∂ν| ≤ tvDist μ ν * (2 * M) :=
      tvDist_integral_le_of_range_ae μ ν f hf (-M) (2 * M) (by positivity)
        hμ_range hν_range
    _ = 2 * M * tvDist μ ν := by ring

end Causalean.Stat
