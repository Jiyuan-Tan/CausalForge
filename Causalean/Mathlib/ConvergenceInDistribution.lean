/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Measure.DiracProba
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd

/-! # Convergence in Distribution Helpers

This file collects general convergence-in-distribution lemmas that are not
specific to the causal-inference layer. It provides deterministic-scalar
Slutsky results for random variables and for weak convergence of probability
measures on the real line.

The lemma `tendstoInMeasure_const_of_tendsto_real` converts ordinary
convergence of deterministic real scalars into convergence in measure for
constant random variables. `TendstoInDistribution.const_mul_of_tendsto_const`
then proves random-variable Slutsky for deterministic scalar multiplication,
and `ProbabilityMeasure.tendsto_map_mul_of_tendsto` gives the analogous
probability-measure pushforward theorem. -/

open Filter
open scoped Topology

namespace MeasureTheory

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {l : Filter ι}

/-- A deterministic real sequence that converges in the usual topological
sense also converges in measure when regarded as a sequence of constant
random variables. -/
lemma tendstoInMeasure_const_of_tendsto_real {a : ι → ℝ} {a₀ : ℝ}
    (ha : Tendsto a l (𝓝 a₀)) :
    TendstoInMeasure μ (fun n => fun _ : Ω => a n) l (fun _ => a₀) := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  have hev : ∀ᶠ n in l, ‖a n - a₀‖ < ε := by
    filter_upwards [(Metric.tendsto_nhds.mp ha) ε hε] with n hn
    simpa [dist_eq_norm] using hn
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [hev] with n hn
  have hlt_abs : |a n - a₀| < ε := by
    simpa [Real.norm_eq_abs] using hn
  have hset :
      {x : Ω | ε ≤ ‖(fun _ : Ω => a n) x - (fun _ : Ω => a₀) x‖} = ∅ := by
    ext x
    simp [not_le.mpr hlt_abs, Real.norm_eq_abs]
  rw [hset]
  simp

/-- Deterministic-scalar Slutsky theorem for Mathlib's random-variable
`TendstoInDistribution`.

If `X n ⇒ Z` and `a n → a₀` deterministically, then
`a n * X n ⇒ a₀ * Z`. -/
theorem TendstoInDistribution.const_mul_of_tendsto_const
    [IsProbabilityMeasure μ] [l.IsCountablyGenerated]
    {X : ι → Ω → ℝ} {Z : Ω → ℝ} {a : ι → ℝ} {a₀ : ℝ}
    (hXZ : TendstoInDistribution X l Z μ)
    (ha : Tendsto a l (𝓝 a₀)) :
    TendstoInDistribution (fun n ω => a n * X n ω) l (fun ω => a₀ * Z ω) μ := by
  have hY : TendstoInMeasure μ (fun n => fun _ : Ω => a n) l (fun _ => a₀) :=
    tendstoInMeasure_const_of_tendsto_real (μ := μ) ha
  have hY_meas : ∀ n, AEMeasurable (fun _ : Ω => a n) μ := by
    intro n
    fun_prop
  simpa using
    (hXZ.continuous_comp_prodMk_of_tendstoInMeasure_const
      (g := fun p : ℝ × ℝ => p.2 * p.1) (by fun_prop) hY hY_meas)

namespace ProbabilityMeasure

/-- Pushing forward `δ_c × ν` by multiplication is the same as pushing forward
`ν` by left multiplication by `c`. -/
private lemma map_mul_eq_map_prod_dirac (c : ℝ) (ν : ProbabilityMeasure ℝ) :
    ((diracProba c).prod ν).map
        ((by fun_prop : Measurable (fun p : ℝ × ℝ => p.1 * p.2)).aemeasurable) =
      ν.map ((measurable_const.mul measurable_id).aemeasurable :
        AEMeasurable (fun x : ℝ => c * x) (ν : Measure ℝ)) := by
  apply Subtype.ext
  change
    Measure.map (fun p : ℝ × ℝ => p.1 * p.2)
        ((Measure.dirac c).prod (ν : Measure ℝ)) =
      Measure.map (fun x : ℝ => c * x) (ν : Measure ℝ)
  rw [Measure.dirac_prod]
  rw [Measure.map_map]
  · rfl
  · fun_prop
  · fun_prop

/-- Measure-level deterministic-scalar Slutsky theorem for weak convergence of
probability measures on ℝ.

If `νᵢ → ν` weakly and `aᵢ → a₀`, then the push-forwards of `νᵢ` by
`x ↦ aᵢ * x` converge weakly to the push-forward of `ν` by `x ↦ a₀ * x`.

This is mathematically standard: weak convergence of probability measures is
tight, and the maps `x ↦ aᵢ * x` converge uniformly on compact sets to
`x ↦ a₀ * x`.  Equivalently, this is the probability-measure version of
deterministic-scalar Slutsky.  It is isolated as a Mathlib contribution
candidate because Mathlib currently has the same-space random-variable
Slutsky theorem but not this varying-map probability-measure wrapper. -/
theorem tendsto_map_mul_of_tendsto {ι : Type*} {l : Filter ι}
    {νs : ι → ProbabilityMeasure ℝ} {ν : ProbabilityMeasure ℝ}
    {a : ι → ℝ} {a₀ : ℝ}
    (hν : Tendsto νs l (𝓝 ν)) (ha : Tendsto a l (𝓝 a₀)) :
    Tendsto
      (fun i => (νs i).map ((measurable_const.mul measurable_id).aemeasurable :
        AEMeasurable (fun x : ℝ => a i * x) (νs i : Measure ℝ)))
      l
      (𝓝 (ν.map ((measurable_const.mul measurable_id).aemeasurable :
        AEMeasurable (fun x : ℝ => a₀ * x) (ν : Measure ℝ)))) := by
  let mulMap : ℝ × ℝ → ℝ := fun p => p.1 * p.2
  have hdirac : Tendsto (fun i => diracProba (a i)) l (𝓝 (diracProba a₀)) :=
    (continuous_diracProba.tendsto a₀).comp ha
  have hprod :
      Tendsto (fun i => (diracProba (a i)).prod (νs i)) l
        (𝓝 ((diracProba a₀).prod ν)) := by
    exact (continuous_prod.tendsto (diracProba a₀, ν)).comp
      (hdirac.prodMk_nhds hν)
  have hmap :
      Tendsto
        (fun i => ((diracProba (a i)).prod (νs i)).map
          ((by fun_prop : Measurable mulMap).aemeasurable))
        l
        (𝓝 (((diracProba a₀).prod ν).map
          ((by fun_prop : Measurable mulMap).aemeasurable))) := by
    exact tendsto_map_of_tendsto_of_continuous _ _ hprod
      (by fun_prop : Continuous mulMap)
  simpa [mulMap, map_mul_eq_map_prod_dirac] using hmap

end ProbabilityMeasure

end MeasureTheory
