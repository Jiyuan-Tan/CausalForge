/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-! # Radon–Nikodym derivative on a finite measurable partition

This file proves two general measure-theoretic facts about a numerator measure `μ` that is
a constant multiple of a denominator measure `ν` on each cell of a finite measurable
partition `(s i)` of the ambient space (`μ.restrict (s i) = r i • ν.restrict (s i)`):

* `partition_restrict_absolutelyContinuous` — `μ ≪ ν` (absolute continuity);
* `partition_restrict_integrable_pow_rnDeriv` — every natural-power deviation
  `((dμ/dν) − 1)^n` of the Radon–Nikodym derivative from `1` is `ν`-integrable.

Both are the standard building blocks of a piecewise-constant least-favorable construction in a
two-point minimax lower bound: the per-cell density is the cell ratio, so the global density is
the simple function `∑ i, r i · 1_{s i}`.
-/

namespace Causalean.Mathlib.MeasureTheory

open _root_.MeasureTheory

/-- **Absolute continuity from a finite proportional partition.**  If `(s i)` is a finite
measurable partition of the ambient space and on each cell the numerator measure `μ` is the
constant multiple `r i` of the denominator measure `ν`
(`μ.restrict (s i) = r i • ν.restrict (s i)`), then `μ` is absolutely continuous
with respect to `ν`.  The global density is the simple function whose value on cell `i` is
`r i`, so `μ = ν.withDensity d`. -/
lemma partition_restrict_absolutelyContinuous
    {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} [Finite ι]
    (μ ν : Measure Ω)
    (s : ι → Set Ω) (r : ι → ENNReal)
    (hs : ∀ i, MeasurableSet (s i))
    (hdisj : Pairwise (Function.onFun Disjoint s))
    (hcover : (⋃ i, s i) = Set.univ)
    (hrestrict : ∀ i, μ.restrict (s i) = r i • ν.restrict (s i)) :
    μ ≪ ν := by
  classical
  letI := Fintype.ofFinite ι
  let d : Ω → ENNReal :=
    fun x => ∑ i : ι, (s i).indicator (fun _ => r i) x
  have hμ_sum : μ = Measure.sum (fun i : ι => μ.restrict (s i)) := by
    have h := Measure.restrict_iUnion (μ := μ) (s := s) hdisj hs
    rw [hcover, Measure.restrict_univ] at h
    exact h
  have hν_density_sum :
      ν.withDensity d =
        Measure.sum (fun i : ι =>
          ν.withDensity ((s i).indicator (fun _ => r i))) := by
    ext t ht
    rw [withDensity_apply _ ht]
    simp_rw [Measure.sum_apply _ ht, withDensity_apply _ ht]
    dsimp [d]
    rw [lintegral_finset_sum]
    · simp
    · intro i _
      exact measurable_const.indicator (hs i)
  have hν_density :
      ν.withDensity d =
        Measure.sum (fun i : ι => r i • ν.restrict (s i)) := by
    rw [hν_density_sum]
    refine congrArg Measure.sum ?_
    funext i
    rw [withDensity_indicator (μ := ν) (hs i), withDensity_const]
  have hμ_density : μ = ν.withDensity d := by
    calc
      μ = Measure.sum (fun i : ι => μ.restrict (s i)) := hμ_sum
      _ = Measure.sum (fun i : ι => r i • ν.restrict (s i)) := by
          refine congrArg Measure.sum ?_
          funext i
          exact hrestrict i
      _ = ν.withDensity d := hν_density.symm
  rw [hμ_density]
  exact withDensity_absolutelyContinuous ν d

/-- **Power-deviation integrability from a finite proportional partition.** Under the same
hypotheses — `(s i)` a finite measurable partition and
`μ.restrict (s i) = r i • ν.restrict (s i)` with nonnegative extended-real
constants `r i` and a finite denominator measure `ν` — the deviation of
the Radon–Nikodym derivative from `1`, namely `((dμ/dν) − 1)^n`, is `ν`-integrable.  On each cell
the derivative equals `r i`, so the function is a finite simple function and the
integral is a finite sum of per-cell constants. -/
lemma partition_restrict_integrable_pow_rnDeriv
    {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} [Finite ι]
    (μ ν : Measure Ω) [IsFiniteMeasure ν]
    (s : ι → Set Ω) (r : ι → ENNReal) (n : ℕ)
    (hs : ∀ i, MeasurableSet (s i))
    (hdisj : Pairwise (Function.onFun Disjoint s))
    (hcover : (⋃ i, s i) = Set.univ)
    (hrestrict : ∀ i, μ.restrict (s i) = r i • ν.restrict (s i)) :
    Integrable (fun x => ((μ.rnDeriv ν x).toReal - 1) ^ n) ν := by
  classical
  letI := Fintype.ofFinite ι
  let d : Ω → ENNReal :=
    fun x => ∑ i : ι, (s i).indicator (fun _ => r i) x
  have hd_meas : Measurable d := by
    dsimp [d]
    exact Finset.measurable_sum _ (fun i _ => measurable_const.indicator (hs i))
  have hd_cell : ∀ i, ∀ x ∈ s i, d x = r i := by
    intro i x hx
    dsimp [d]
    change (∑ j : ι, (s j).indicator (fun _ => r j) x) =
      r i
    simpa [Set.indicator_of_mem hx] using
      (Finset.sum_eq_single (s := Finset.univ)
        (f := fun j : ι => (s j).indicator (fun _ => r j) x) i
        (by
          intro j _ hji
          have hxnot : x ∉ s j := by
            have hsd : Disjoint (s j) (s i) := hdisj hji
            exact fun hxj => (Set.disjoint_left.mp hsd) hxj hx
          simp [Set.indicator_of_notMem hxnot])
        (by simp))
  have hμ_sum : μ = Measure.sum (fun i : ι => μ.restrict (s i)) := by
    have h := Measure.restrict_iUnion (μ := μ) (s := s) hdisj hs
    rw [hcover, Measure.restrict_univ] at h
    exact h
  have hν_density_sum :
      ν.withDensity d =
        Measure.sum (fun i : ι =>
          ν.withDensity ((s i).indicator (fun _ => r i))) := by
    ext t ht
    rw [withDensity_apply _ ht]
    simp_rw [Measure.sum_apply _ ht, withDensity_apply _ ht]
    dsimp [d]
    rw [lintegral_finset_sum]
    · simp
    · intro i _
      exact measurable_const.indicator (hs i)
  have hν_density :
      ν.withDensity d =
        Measure.sum (fun i : ι => r i • ν.restrict (s i)) := by
    rw [hν_density_sum]
    refine congrArg Measure.sum ?_
    funext i
    rw [withDensity_indicator (μ := ν) (hs i), withDensity_const]
  have hμ_density : μ = ν.withDensity d := by
    calc
      μ = Measure.sum (fun i : ι => μ.restrict (s i)) := hμ_sum
      _ = Measure.sum (fun i : ι => r i • ν.restrict (s i)) := by
          refine congrArg Measure.sum ?_
          funext i
          exact hrestrict i
      _ = ν.withDensity d := hν_density.symm
  have hrn : μ.rnDeriv ν =ᵐ[ν] d := by
    rw [hμ_density]
    exact Measure.rnDeriv_withDensity ν hd_meas
  have hpiece_int :
      ∀ i, IntegrableOn (fun x => ((d x).toReal - 1) ^ n) (s i) ν := by
    intro i
    refine ((integrable_const (((r i).toReal - 1) ^ n) :
      Integrable (fun _ : Ω => ((r i).toReal - 1) ^ n) ν).integrableOn.congr_fun ?_ (hs i))
    intro x hx
    dsimp
    rw [hd_cell i x hx]
  have hd_int_on :
      IntegrableOn (fun x => ((d x).toReal - 1) ^ n) (⋃ i, s i) ν := by
    exact integrableOn_finite_iUnion.2 hpiece_int
  have hd_int : Integrable (fun x => ((d x).toReal - 1) ^ n) ν := by
    rw [← integrableOn_univ, ← hcover]
    exact hd_int_on
  have heq :
      (fun x => ((μ.rnDeriv ν x).toReal - 1) ^ n)
        =ᵐ[ν] fun x => ((d x).toReal - 1) ^ n := by
    filter_upwards [hrn] with x hx
    rw [hx]
  exact hd_int.congr heq.symm


end Causalean.Mathlib.MeasureTheory
