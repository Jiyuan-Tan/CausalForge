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
partition `(s i)` of the ambient space (`μ.restrict (s i) = c i • ν.restrict (s i)`):

* `partition_restrict_absolutelyContinuous` — `μ ≪ ν` (absolute continuity);
* `partition_restrict_integrable_sq_rnDeriv` — the squared deviation `((dμ/dν) − 1)²` of the
  Radon–Nikodym derivative from `1` is `ν`-integrable.

Both are the standard building blocks of a piecewise-constant least-favorable construction in a
two-point minimax lower bound: the per-cell density is the cell ratio, so the global density is
the simple function `∑ i, c i · 1_{s i}`.
-/

namespace Causalean.Mathlib.MeasureTheory

open _root_.MeasureTheory

/-- **Absolute continuity from a finite proportional partition.**  If `(s i)` is a finite
measurable partition of the ambient space and on each cell the numerator measure `μ` is the
nonnegative constant multiple `c i` of the denominator measure `ν`
(`μ.restrict (s i) = c i • ν.restrict (s i)`), then `μ` is absolutely continuous with respect to
`ν`.  The global density is the simple function `∑ i, c i · 1_{s i}`, so `μ = ν.withDensity d`. -/
lemma partition_restrict_absolutelyContinuous
    {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (μ ν : Measure Ω)
    (s : Fin k → Set Ω) (c : Fin k → ℝ)
    (hs : ∀ i, MeasurableSet (s i))
    (hdisj : Pairwise (Function.onFun Disjoint s))
    (hcover : (⋃ i, s i) = Set.univ)
    (_hc_nonneg : ∀ i, 0 ≤ c i)
    (hrestrict : ∀ i, μ.restrict (s i) = ENNReal.ofReal (c i) • ν.restrict (s i)) :
    μ ≪ ν := by
  classical
  let d : Ω → ENNReal :=
    fun x => ∑ i : Fin k, (s i).indicator (fun _ => ENNReal.ofReal (c i)) x
  have hμ_sum : μ = Measure.sum (fun i : Fin k => μ.restrict (s i)) := by
    have h := Measure.restrict_iUnion (μ := μ) (s := s) hdisj hs
    rw [hcover, Measure.restrict_univ] at h
    exact h
  have hν_density_sum :
      ν.withDensity d =
        Measure.sum (fun i : Fin k =>
          ν.withDensity ((s i).indicator (fun _ => ENNReal.ofReal (c i)))) := by
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
        Measure.sum (fun i : Fin k => ENNReal.ofReal (c i) • ν.restrict (s i)) := by
    rw [hν_density_sum]
    refine congrArg Measure.sum ?_
    funext i
    rw [withDensity_indicator (μ := ν) (hs i), withDensity_const]
  have hμ_density : μ = ν.withDensity d := by
    calc
      μ = Measure.sum (fun i : Fin k => μ.restrict (s i)) := hμ_sum
      _ = Measure.sum (fun i : Fin k => ENNReal.ofReal (c i) • ν.restrict (s i)) := by
          refine congrArg Measure.sum ?_
          funext i
          exact hrestrict i
      _ = ν.withDensity d := hν_density.symm
  rw [hμ_density]
  exact withDensity_absolutelyContinuous ν d

/-- **Square-deviation integrability from a finite proportional partition.**  Under the same
hypotheses — `(s i)` a finite measurable partition and `μ.restrict (s i) = c i • ν.restrict (s i)`
with nonnegative constants `c i` and a finite denominator measure `ν` — the squared deviation of
the Radon–Nikodym derivative from `1`, namely `((dμ/dν) − 1)²`, is `ν`-integrable.  On each cell
the derivative equals the constant `c i`, so the function is a finite simple function and the
integral is a finite sum of per-cell constants. -/
lemma partition_restrict_integrable_sq_rnDeriv
    {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (μ ν : Measure Ω) [IsFiniteMeasure ν]
    (s : Fin k → Set Ω) (c : Fin k → ℝ)
    (hs : ∀ i, MeasurableSet (s i))
    (hdisj : Pairwise (Function.onFun Disjoint s))
    (hcover : (⋃ i, s i) = Set.univ)
    (hc_nonneg : ∀ i, 0 ≤ c i)
    (hrestrict : ∀ i, μ.restrict (s i) = ENNReal.ofReal (c i) • ν.restrict (s i)) :
    Integrable (fun x => ((μ.rnDeriv ν x).toReal - 1) ^ (2 : ℕ)) ν := by
  classical
  let d : Ω → ENNReal :=
    fun x => ∑ i : Fin k, (s i).indicator (fun _ => ENNReal.ofReal (c i)) x
  have hd_meas : Measurable d := by
    dsimp [d]
    exact Finset.measurable_sum _ (fun i _ => measurable_const.indicator (hs i))
  have hd_cell : ∀ i, ∀ x ∈ s i, d x = ENNReal.ofReal (c i) := by
    intro i x hx
    dsimp [d]
    change (∑ j : Fin k, (s j).indicator (fun _ => ENNReal.ofReal (c j)) x) =
      ENNReal.ofReal (c i)
    simpa [Set.indicator_of_mem hx] using
      (Finset.sum_eq_single (s := Finset.univ)
        (f := fun j : Fin k => (s j).indicator (fun _ => ENNReal.ofReal (c j)) x) i
        (by
          intro j _ hji
          have hxnot : x ∉ s j := by
            have hsd : Disjoint (s j) (s i) := hdisj hji
            exact fun hxj => (Set.disjoint_left.mp hsd) hxj hx
          simp [Set.indicator_of_notMem hxnot])
        (by simp))
  have hμ_sum : μ = Measure.sum (fun i : Fin k => μ.restrict (s i)) := by
    have h := Measure.restrict_iUnion (μ := μ) (s := s) hdisj hs
    rw [hcover, Measure.restrict_univ] at h
    exact h
  have hν_density_sum :
      ν.withDensity d =
        Measure.sum (fun i : Fin k =>
          ν.withDensity ((s i).indicator (fun _ => ENNReal.ofReal (c i)))) := by
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
        Measure.sum (fun i : Fin k => ENNReal.ofReal (c i) • ν.restrict (s i)) := by
    rw [hν_density_sum]
    refine congrArg Measure.sum ?_
    funext i
    rw [withDensity_indicator (μ := ν) (hs i), withDensity_const]
  have hμ_density : μ = ν.withDensity d := by
    calc
      μ = Measure.sum (fun i : Fin k => μ.restrict (s i)) := hμ_sum
      _ = Measure.sum (fun i : Fin k => ENNReal.ofReal (c i) • ν.restrict (s i)) := by
          refine congrArg Measure.sum ?_
          funext i
          exact hrestrict i
      _ = ν.withDensity d := hν_density.symm
  have hrn : μ.rnDeriv ν =ᵐ[ν] d := by
    rw [hμ_density]
    exact Measure.rnDeriv_withDensity ν hd_meas
  have hpiece_int :
      ∀ i, IntegrableOn (fun x => ((d x).toReal - 1) ^ (2 : ℕ)) (s i) ν := by
    intro i
    refine ((integrable_const ((c i - 1) ^ (2 : ℕ)) :
      Integrable (fun _ : Ω => (c i - 1) ^ (2 : ℕ)) ν).integrableOn.congr_fun ?_ (hs i))
    intro x hx
    change (c i - 1) ^ (2 : ℕ) = ((d x).toReal - 1) ^ (2 : ℕ)
    rw [hd_cell i x hx, ENNReal.toReal_ofReal (hc_nonneg i)]
  have hd_int_on :
      IntegrableOn (fun x => ((d x).toReal - 1) ^ (2 : ℕ)) (⋃ i, s i) ν := by
    exact integrableOn_finite_iUnion.2 hpiece_int
  have hd_int : Integrable (fun x => ((d x).toReal - 1) ^ (2 : ℕ)) ν := by
    rw [← integrableOn_univ, ← hcover]
    exact hd_int_on
  have heq :
      (fun x => ((μ.rnDeriv ν x).toReal - 1) ^ (2 : ℕ))
        =ᵐ[ν] fun x => ((d x).toReal - 1) ^ (2 : ℕ) := by
    filter_upwards [hrn] with x hx
    rw [hx]
  exact hd_int.congr heq.symm

end Causalean.Mathlib.MeasureTheory
