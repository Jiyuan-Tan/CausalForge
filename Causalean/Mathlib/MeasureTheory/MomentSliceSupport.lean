/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Topology.Order.Compact
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Moment-slice extreme-point support bound (Richter–Rogosinski / Winkler)

Let `K = [a,b]` be a compact interval and `s : ℝ`.  The *moment slice* is the set of
probability measures on `K` with mean `0` and second moment `s`:

    C = { μ | μ Kᶜ = 0 ∧ ∫ x ∂μ = 0 ∧ ∫ x² ∂μ = s }.

This file proves the support-size part of the Richter–Rogosinski / Karr / Winkler
*canonical representation* theorem for this two-moment slice.  It starts with the
finite-atom perturbation argument: three homogeneous linear constraints (total mass,
mean, second moment) on four-or-more atom weights always admit a nonzero perturbation
`δ`, and `μ ± ε·δ` are then two distinct measures of `C` whose midpoint is `μ`,
contradicting extremality.  The later support argument upgrades this from a finite atom
set to an arbitrary extreme probability measure in the slice.

Main results:
* `exists_moment_perturbation` — pure linear algebra: on `4`-or-more reals there is a
  nonzero weight perturbation killing the three moments `1, x, x²` simultaneously.
* `card_le_three_of_isExtremePoint` — an extreme point of the moment slice supported on a
  finite positive-weight atom set has at most three atoms.
* `exists_isMinOn_momentSlice` — on a compact Hausdorff space the moment slice is weak-*
  compact, so a bounded-continuous objective attains its minimum over the slice.
* `support_finite_ncard_le_three_of_isExtremePoint` — any extreme probability measure in
  the two-moment slice has finite topological support of cardinality at most three.
* `isAtomic_le_three_of_isExtremePoint` and
  `exists_cardSupportLe_three_of_isExtremePoint` — the same conclusion as a positive
  discrete-measure representation and as a finite support carrier.
-/

open MeasureTheory Finset
open scoped ENNReal NNReal BoundedContinuousFunction

namespace Causalean.Mathlib.MeasureTheory

noncomputable section

/-- The discrete probability-measure builder: `∑_{x ∈ T} w x · δ_x`, the weighted sum of
Dirac masses at the points of `T`. -/
noncomputable def discreteMeasure (T : Finset ℝ) (w : ℝ → ℝ) : Measure ℝ :=
  ∑ x ∈ T, ENNReal.ofReal (w x) • Measure.dirac x

/-- The moment slice: probability measures supported on `[a,b]` with mean `0` and second
moment `s`. -/
def MomentSlice (a b s : ℝ) : Set (Measure ℝ) :=
  {μ | IsProbabilityMeasure μ ∧ μ (Set.Icc a b)ᶜ = 0 ∧
        (∫ x, x ∂μ = 0) ∧ (∫ x, x ^ 2 ∂μ = s)}

/-- `μ` is an extreme point of a set `C` of measures: it lies in `C` and is not an interior
point of any nondegenerate segment inside `C`. -/
def IsExtremePoint (C : Set (Measure ℝ)) (μ : Measure ℝ) : Prop :=
  μ ∈ C ∧ ∀ μ₁ ∈ C, ∀ μ₂ ∈ C, ∀ t : ℝ≥0∞, 0 < t → t < 1 →
    μ = t • μ₁ + (1 - t) • μ₂ → μ₁ = μ₂

/-! ### Linear-algebra core -/

/-- **Three-moment perturbation.** On any finite set `T ⊆ ℝ` of more than three points there
is a nonzero real weighting `δ` whose total mass, first moment and second moment all vanish.
This is rank–nullity: three linear functionals (`∑ δ`, `∑ δ·x`, `∑ δ·x²`) on a space of
dimension `> 3` have a nonzero common kernel. -/
theorem exists_moment_perturbation {T : Finset ℝ} (hT : 3 < T.card) :
    ∃ δ : ℝ → ℝ, (∑ x ∈ T, δ x = 0) ∧ (∑ x ∈ T, δ x * x = 0) ∧
      (∑ x ∈ T, δ x * x ^ 2 = 0) ∧ (∃ x ∈ T, δ x ≠ 0) := by
  classical
  set φ : ℝ → (Fin 2 → ℝ) := fun x => ![x, x ^ 2] with hφ
  have hφinj : Function.Injective φ := by
    intro x y h; have := congrFun h 0; simpa [hφ] using this
  have hinjOn : Set.InjOn φ T := hφinj.injOn
  have hcard : Module.finrank ℝ (Fin 2 → ℝ) + 1 < (T.image φ).card := by
    rw [Finset.card_image_of_injOn hinjOn, Module.finrank_pi]; simpa using hT
  obtain ⟨g, hsum0, hgsum, v, hv, hvne⟩ :=
    Module.exists_nontrivial_relation_sum_zero_of_finrank_succ_lt_card hcard
  rw [Finset.sum_image hinjOn] at hgsum hsum0
  have h0 := congrFun hsum0 0
  have h1 := congrFun hsum0 1
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, hφ,
    Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  obtain ⟨x, hxT, hxne⟩ : ∃ x ∈ T, g (φ x) ≠ 0 := by
    rw [Finset.mem_image] at hv; obtain ⟨x, hxT, rfl⟩ := hv; exact ⟨x, hxT, hvne⟩
  exact ⟨fun x => g (φ x), hgsum, h0, h1, x, hxT, hxne⟩

/-! ### Measure-level computations -/

/-- A discrete measure whose atoms all lie in `[a,b]` gives zero mass to the
complement of `[a,b]`. -/
theorem discreteMeasure_apply_compl_Icc {T : Finset ℝ} {w : ℝ → ℝ} {a b : ℝ}
    (hTab : ∀ x ∈ T, x ∈ Set.Icc a b) :
    discreteMeasure T w (Set.Icc a b)ᶜ = 0 := by
  rw [discreteMeasure, Measure.finset_sum_apply]
  apply Finset.sum_eq_zero
  intro x hx
  rw [Measure.smul_apply, Measure.dirac_apply, smul_eq_mul]
  have : x ∉ (Set.Icc a b)ᶜ := by simp [hTab x hx]
  simp [this]

/-- A finite discrete measure is a probability measure when all atom weights
are nonnegative and their sum is one. -/
theorem isProbabilityMeasure_discreteMeasure {T : Finset ℝ} {w : ℝ → ℝ}
    (hw : ∀ x ∈ T, 0 ≤ w x) (hsum : ∑ x ∈ T, w x = 1) :
    IsProbabilityMeasure (discreteMeasure T w) := by
  constructor
  rw [discreteMeasure, Measure.finset_sum_apply]
  have : ∀ x ∈ T, (ENNReal.ofReal (w x) • Measure.dirac x) Set.univ = ENNReal.ofReal (w x) := by
    intro x hx; rw [Measure.smul_apply, smul_eq_mul]; simp
  rw [Finset.sum_congr rfl this, ← ENNReal.ofReal_sum_of_nonneg hw, hsum, ENNReal.ofReal_one]

/-- Integral against a discrete measure is the weighted sum of the integrand over the atoms.
Every real-valued `f` is integrable here since the measure has finite support. -/
theorem integral_discreteMeasure {T : Finset ℝ} {w : ℝ → ℝ} (hw : ∀ x ∈ T, 0 ≤ w x)
    (f : ℝ → ℝ) :
    ∫ x, f x ∂(discreteMeasure T w) = ∑ x ∈ T, w x * f x := by
  rw [discreteMeasure, integral_finset_sum_measure]
  · apply Finset.sum_congr rfl
    intro x hx
    rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hw x hx), smul_eq_mul]
  · intro x hx
    exact (integrable_dirac enorm_lt_top).smul_measure (by simp)

/-- The mass assigned by a finite discrete measure to an atom in its support is
the corresponding atom weight, coerced to `ℝ≥0∞`. -/
theorem discreteMeasure_singleton {T : Finset ℝ} {w : ℝ → ℝ} {x₀ : ℝ} (hx₀ : x₀ ∈ T) :
    discreteMeasure T w {x₀} = ENNReal.ofReal (w x₀) := by
  rw [discreteMeasure, Measure.finset_sum_apply]
  have : ∀ x ∈ T, (ENNReal.ofReal (w x) • Measure.dirac x) {x₀}
      = if x = x₀ then ENNReal.ofReal (w x) else 0 := by
    intro x hx
    rw [Measure.smul_apply, Measure.dirac_apply, smul_eq_mul]
    by_cases h : x = x₀ <;> simp [h, Set.mem_singleton_iff]
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq' T x₀ (fun x => ENNReal.ofReal (w x))]
  simp [hx₀]

/-- A discrete measure whose atom weights are the pointwise average of two nonnegative
weightings is the midpoint of the two corresponding discrete measures. -/
theorem discreteMeasure_midpoint {T : Finset ℝ} {w wp wm : ℝ → ℝ}
    (hp : ∀ x ∈ T, 0 ≤ wp x) (hm : ∀ x ∈ T, 0 ≤ wm x)
    (hmid : ∀ x ∈ T, w x = (1 / 2) * wp x + (1 / 2) * wm x) :
    discreteMeasure T w
      = (1 / 2 : ℝ≥0∞) • discreteMeasure T wp + (1 / 2 : ℝ≥0∞) • discreteMeasure T wm := by
  rw [discreteMeasure, discreteMeasure, discreteMeasure, Finset.smul_sum, Finset.smul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  rw [smul_smul, smul_smul, ← add_smul]
  congr 1
  have e2 : (1 / 2 : ℝ≥0∞) = ENNReal.ofReal (1 / 2) := by
    rw [ENNReal.ofReal_div_of_pos] <;> simp
  rw [e2, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_add (mul_nonneg (by norm_num) (hp x hx)) (mul_nonneg (by norm_num) (hm x hx)),
    ← hmid x hx]

/-! ### Headline -/

/-- **Richter–Rogosinski support bound (finite-atom case).** If a probability measure
`μ = ∑_{x∈T} w x · δ_x` with strictly positive weights lies in the moment slice and is an
extreme point of it, then it has at most three atoms. -/
theorem card_le_three_of_isExtremePoint {a b s : ℝ} {T : Finset ℝ} {w : ℝ → ℝ}
    (hpos : ∀ x ∈ T, 0 < w x) (hTab : ∀ x ∈ T, x ∈ Set.Icc a b)
    (hext : IsExtremePoint (MomentSlice a b s) (discreteMeasure T w)) :
    T.card ≤ 3 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨δ, hδ0, hδ1, hδ2, x₀, hx₀T, hx₀ne⟩ := exists_moment_perturbation hcon
  have hwnn : ∀ x ∈ T, 0 ≤ w x := fun x hx => (hpos x hx).le
  obtain ⟨hμprob, _, hμmean, hμ2⟩ := hext.1
  have hmean : ∑ x ∈ T, w x * x = 0 := by
    rw [← integral_discreteMeasure hwnn (fun x => x)]; exact hμmean
  have hsec : ∑ x ∈ T, w x * x ^ 2 = s := by
    rw [← integral_discreteMeasure hwnn (fun x => x ^ 2)]; exact hμ2
  have huniv : (discreteMeasure T w) Set.univ = ENNReal.ofReal (∑ x ∈ T, w x) := by
    rw [discreteMeasure, Measure.finset_sum_apply, ENNReal.ofReal_sum_of_nonneg hwnn]
    apply Finset.sum_congr rfl; intro x hx; rw [Measure.smul_apply, smul_eq_mul]; simp
  have hmass : ∑ x ∈ T, w x = 1 := by
    have h1 := hμprob.measure_univ; rw [huniv] at h1; exact ENNReal.ofReal_eq_one.mp h1
  have hTne : T.Nonempty := Finset.card_pos.mp (by omega)
  set ε : ℝ := T.inf' hTne (fun x => w x / (|δ x| + 1)) with hεdef
  have hεpos : 0 < ε := by
    rw [hεdef, Finset.lt_inf'_iff]; intro x hx; have := hpos x hx; positivity
  have hbound : ∀ x ∈ T, |ε * δ x| ≤ w x := by
    intro x hx
    rw [abs_mul, abs_of_pos hεpos]
    have hle : ε ≤ w x / (|δ x| + 1) := Finset.inf'_le _ hx
    have hden : (0 : ℝ) < |δ x| + 1 := by positivity
    rw [le_div_iff₀ hden] at hle
    nlinarith [hεpos, abs_nonneg (δ x)]
  set wp : ℝ → ℝ := fun x => w x + ε * δ x with hwp
  set wm : ℝ → ℝ := fun x => w x - ε * δ x with hwm
  have hwpnn : ∀ x ∈ T, 0 ≤ wp x := by
    intro x hx; have := (abs_le.mp (hbound x hx)).1; simp only [hwp]; linarith
  have hwmnn : ∀ x ∈ T, 0 ≤ wm x := by
    intro x hx; have := (abs_le.mp (hbound x hx)).2; simp only [hwm]; linarith
  have hsump : ∑ x ∈ T, wp x = 1 := by
    simp only [hwp, Finset.sum_add_distrib, ← Finset.mul_sum, hδ0, mul_zero, add_zero, hmass]
  have hsumm : ∑ x ∈ T, wm x = 1 := by
    simp only [hwm, Finset.sum_sub_distrib, ← Finset.mul_sum, hδ0, mul_zero, sub_zero, hmass]
  have hmeanp : ∑ x ∈ T, wp x * x = 0 := by
    simp only [hwp, add_mul]
    rw [Finset.sum_add_distrib, hmean, zero_add]
    rw [show (∑ x ∈ T, ε * δ x * x) = ε * ∑ x ∈ T, δ x * x by rw [Finset.mul_sum]; ring_nf,
      hδ1, mul_zero]
  have hmeanm : ∑ x ∈ T, wm x * x = 0 := by
    simp only [hwm, sub_mul]
    rw [Finset.sum_sub_distrib, hmean, zero_sub]
    rw [show (∑ x ∈ T, ε * δ x * x) = ε * ∑ x ∈ T, δ x * x by rw [Finset.mul_sum]; ring_nf,
      hδ1, mul_zero, neg_zero]
  have hsecp : ∑ x ∈ T, wp x * x ^ 2 = s := by
    simp only [hwp, add_mul]
    rw [Finset.sum_add_distrib, hsec]
    rw [show (∑ x ∈ T, ε * δ x * x ^ 2) = ε * ∑ x ∈ T, δ x * x ^ 2 by rw [Finset.mul_sum]; ring_nf,
      hδ2, mul_zero, add_zero]
  have hsecm : ∑ x ∈ T, wm x * x ^ 2 = s := by
    simp only [hwm, sub_mul]
    rw [Finset.sum_sub_distrib, hsec]
    rw [show (∑ x ∈ T, ε * δ x * x ^ 2) = ε * ∑ x ∈ T, δ x * x ^ 2 by rw [Finset.mul_sum]; ring_nf,
      hδ2, mul_zero, sub_zero]
  have hmemp : discreteMeasure T wp ∈ MomentSlice a b s :=
    ⟨isProbabilityMeasure_discreteMeasure hwpnn hsump, discreteMeasure_apply_compl_Icc hTab,
      by rw [integral_discreteMeasure hwpnn (fun x => x)]; exact hmeanp,
      by rw [integral_discreteMeasure hwpnn (fun x => x ^ 2)]; exact hsecp⟩
  have hmemm : discreteMeasure T wm ∈ MomentSlice a b s :=
    ⟨isProbabilityMeasure_discreteMeasure hwmnn hsumm, discreteMeasure_apply_compl_Icc hTab,
      by rw [integral_discreteMeasure hwmnn (fun x => x)]; exact hmeanm,
      by rw [integral_discreteMeasure hwmnn (fun x => x ^ 2)]; exact hsecm⟩
  have hmid : ∀ x ∈ T, w x = (1 / 2) * wp x + (1 / 2) * wm x := by
    intro x hx; simp only [hwp, hwm]; ring
  have hmideq := discreteMeasure_midpoint hwpnn hwmnn hmid
  have hne : discreteMeasure T wp ≠ discreteMeasure T wm := by
    intro heq
    have h1 := discreteMeasure_singleton (w := wp) hx₀T
    have h2 := discreteMeasure_singleton (w := wm) hx₀T
    rw [heq, h2] at h1
    have hwx : wm x₀ = wp x₀ := by
      have := congrArg ENNReal.toReal h1
      rwa [ENNReal.toReal_ofReal (hwmnn x₀ hx₀T), ENNReal.toReal_ofReal (hwpnn x₀ hx₀T)] at this
    simp only [hwp, hwm] at hwx
    have hz : ε * δ x₀ = 0 := by linarith
    rcases mul_eq_zero.mp hz with h | h
    · exact hεpos.ne' h
    · exact hx₀ne h
  have ht : (1 : ℝ≥0∞) - 1 / 2 = 1 / 2 :=
    ENNReal.sub_eq_of_eq_add (by simp) (ENNReal.add_halves 1).symm
  refine absurd (hext.2 _ hmemp _ hmemm (1 / 2) (by norm_num) (by norm_num) ?_) hne
  rw [ht]; exact hmideq

/-! ### Attainment -/

/-- **Attainment of the minimum over a moment slice.** On a compact Hausdorff space `Ω`, the
set of probability measures pinned by two bounded-continuous moment constraints
`∫ g₁ = c₁`, `∫ g₂ = c₂` is weak-* compact, so any bounded-continuous objective `∫ f` attains
its minimum over that (nonempty) slice. The number of constraints is immaterial; the two-moment
case is stated to match the mean/second-moment slice. -/
theorem exists_isMinOn_momentSlice {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]
    [T2Space Ω] [BorelSpace Ω] [CompactSpace Ω] (g₁ g₂ f : Ω →ᵇ ℝ) (c₁ c₂ : ℝ)
    (hne : {μ : ProbabilityMeasure Ω | ∫ x, g₁ x ∂μ = c₁ ∧ ∫ x, g₂ x ∂μ = c₂}.Nonempty) :
    ∃ μ ∈ {μ : ProbabilityMeasure Ω | ∫ x, g₁ x ∂μ = c₁ ∧ ∫ x, g₂ x ∂μ = c₂},
      ∀ ν ∈ {μ : ProbabilityMeasure Ω | ∫ x, g₁ x ∂μ = c₁ ∧ ∫ x, g₂ x ∂μ = c₂},
        ∫ x, f x ∂(μ : Measure Ω) ≤ ∫ x, f x ∂(ν : Measure Ω) := by
  set C := {μ : ProbabilityMeasure Ω | ∫ x, g₁ x ∂μ = c₁ ∧ ∫ x, g₂ x ∂μ = c₂} with hC
  have hcont1 : Continuous fun μ : ProbabilityMeasure Ω => ∫ x, g₁ x ∂μ :=
    ProbabilityMeasure.continuous_integral_boundedContinuousFunction g₁
  have hcont2 : Continuous fun μ : ProbabilityMeasure Ω => ∫ x, g₂ x ∂μ :=
    ProbabilityMeasure.continuous_integral_boundedContinuousFunction g₂
  have hcontf : Continuous fun μ : ProbabilityMeasure Ω => ∫ x, f x ∂μ :=
    ProbabilityMeasure.continuous_integral_boundedContinuousFunction f
  have hCclosed : IsClosed C := by
    have : C = (fun μ : ProbabilityMeasure Ω => ∫ x, g₁ x ∂μ) ⁻¹' {c₁}
        ∩ (fun μ : ProbabilityMeasure Ω => ∫ x, g₂ x ∂μ) ⁻¹' {c₂} := rfl
    rw [this]
    exact (isClosed_singleton.preimage hcont1).inter (isClosed_singleton.preimage hcont2)
  have hCcompact : IsCompact C := hCclosed.isCompact
  obtain ⟨μ, hμC, hmin⟩ := hCcompact.exists_isMinOn hne hcontf.continuousOn
  exact ⟨μ, hμC, fun ν hν => hmin hν⟩

/-! ### General-measure support bound -/

/-- An extreme probability measure in the two-moment slice cannot have four distinct support
points.  Four separated neighborhoods would give a nonzero signed perturbation preserving
mass, mean, and second moment, so the measure would be the midpoint of two different slice
members. -/
theorem not_four_distinct_in_support {a b s : ℝ} {μ : Measure ℝ}
    (hext : IsExtremePoint (MomentSlice a b s) μ)
    (x : Fin 4 → ℝ) (hinj : Function.Injective x)
    (hsupp : ∀ i, x i ∈ μ.support) : False := by
  classical
  obtain ⟨hprob, hcompl, hmean, hsec⟩ := hext.1
  -- (a) integrability of `id` and `t^2` against the probability measure `μ`.
  have hbdd : ∀ᵐ t ∂μ, t ∈ Set.Icc a b := by
    rw [ae_iff]; exact hcompl
  set C : ℝ := max |a| |b| with hC_def
  have hCnn : 0 ≤ C := le_trans (abs_nonneg a) (le_max_left _ _)
  have hbound1 : ∀ᵐ t ∂μ, ‖(fun t => t) t‖ ≤ (fun _ => C) t := by
    filter_upwards [hbdd] with t ht
    obtain ⟨hat, htb⟩ := ht
    simp only [Real.norm_eq_abs]
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · have h1 : -|a| ≤ a := neg_abs_le a
      have h2 : |a| ≤ C := le_max_left _ _
      linarith
    · have h1 : b ≤ |b| := le_abs_self b
      have h2 : |b| ≤ C := le_max_right _ _
      linarith
  have hint1 : Integrable (fun t => t) μ :=
    (integrable_const C).mono' (by fun_prop) hbound1
  have hbound2 : ∀ᵐ t ∂μ, ‖(fun t => t ^ 2) t‖ ≤ (fun _ => C ^ 2) t := by
    filter_upwards [hbound1] with t ht
    simp only [Real.norm_eq_abs] at ht ⊢
    rw [abs_pow]
    nlinarith [abs_nonneg t, ht, hCnn]
  have hint2 : Integrable (fun t => t ^ 2) μ :=
    (integrable_const (C ^ 2)).mono' (by fun_prop) hbound2
  -- (b) four pairwise-disjoint open balls around the support points.
  have hdist_pos : ∀ i j, i ≠ j → 0 < dist (x i) (x j) := fun i j hij =>
    dist_pos.mpr (fun h => hij (hinj h))
  set r : ℝ := (Finset.univ.inf' Finset.univ_nonempty
      (fun p : Fin 4 × Fin 4 => if p.1 = p.2 then (1 : ℝ) else dist (x p.1) (x p.2))) / 2
    with hr_def
  have hr_pos : 0 < r := by
    have hpos : 0 < Finset.univ.inf' Finset.univ_nonempty
        (fun p : Fin 4 × Fin 4 => if p.1 = p.2 then (1 : ℝ) else dist (x p.1) (x p.2)) := by
      rw [Finset.lt_inf'_iff]
      intro p _
      by_cases hp : p.1 = p.2
      · simp [hp]
      · simp only [hp, if_false]; exact hdist_pos p.1 p.2 hp
    rw [hr_def]; linarith
  have hr_le : ∀ i j, i ≠ j → 2 * r ≤ dist (x i) (x j) := by
    intro i j hij
    have hle := Finset.inf'_le
      (fun p : Fin 4 × Fin 4 => if p.1 = p.2 then (1 : ℝ) else dist (x p.1) (x p.2))
      (Finset.mem_univ (i, j))
    simp only [hij, if_false] at hle
    rw [hr_def]; linarith
  set U : Fin 4 → Set ℝ := fun i => Metric.ball (x i) r with hU_def
  have hUopen : ∀ i, IsOpen (U i) := fun i => Metric.isOpen_ball
  have hxU : ∀ i, x i ∈ U i := fun i => Metric.mem_ball_self hr_pos
  have hUdisj : Pairwise (Function.onFun Disjoint U) := by
    intro i j hij
    refine Metric.ball_disjoint_ball ?_
    have := hr_le i j hij; linarith
  have hUmeas : ∀ i, MeasurableSet (U i) := fun i => (hUopen i).measurableSet
  have hUpos : ∀ i, 0 < μ (U i) := fun i =>
    (Measure.mem_support_iff_forall (x i)).1 (hsupp i) (U i) ((hUopen i).mem_nhds (hxU i))
  have hUne : ∀ i, μ (U i) ≠ ∞ := fun i => measure_ne_top μ (U i)
  -- (d)–(e) linear dependence of the four restriction moment vectors in ℝ³.
  set v : Fin 4 → (Fin 3 → ℝ) := fun i =>
    ![(μ (U i)).toReal, ∫ t in U i, t ∂μ, ∫ t in U i, t ^ 2 ∂μ] with hv_def
  have hdep : ¬ LinearIndependent ℝ v := by
    intro hli
    have hcard := hli.fintype_card_le_finrank
    simp only [Fintype.card_fin, Module.finrank_pi] at hcard
    omega
  rw [Fintype.not_linearIndependent_iff] at hdep
  obtain ⟨g, hgsum, i₀, hi₀⟩ := hdep
  have H0 : ∑ i, g i * (μ (U i)).toReal = 0 := by
    have h := congrFun hgsum 0
    simpa [Finset.sum_apply, Pi.smul_apply, hv_def, smul_eq_mul] using h
  have H1 : ∑ i, g i * (∫ t in U i, t ∂μ) = 0 := by
    have h := congrFun hgsum 1
    simpa [Finset.sum_apply, Pi.smul_apply, hv_def, smul_eq_mul] using h
  have H2 : ∑ i, g i * (∫ t in U i, t ^ 2 ∂μ) = 0 := by
    have h := congrFun hgsum 2
    simpa [Finset.sum_apply, Pi.smul_apply, hv_def, smul_eq_mul] using h
  -- (f) small step size keeping all perturbed weights nonnegative.
  set Mg : ℝ := Finset.univ.sup' Finset.univ_nonempty (fun i => |g i|) with hMg_def
  have hMgnn : 0 ≤ Mg :=
    le_trans (abs_nonneg (g i₀)) (Finset.le_sup' (fun i => |g i|) (Finset.mem_univ i₀))
  set ε : ℝ := 1 / (2 * (1 + Mg)) with hε_def
  have hden : 0 < 2 * (1 + Mg) := by positivity
  have hε_pos : 0 < ε := by rw [hε_def]; positivity
  have hε_bound : ∀ i, ε * |g i| ≤ 1 / 2 := by
    intro i
    have hgi : |g i| ≤ Mg := Finset.le_sup' (fun i => |g i|) (Finset.mem_univ i)
    have heq : ε * |g i| = |g i| / (2 * (1 + Mg)) := by rw [hε_def]; ring
    rw [heq, div_le_iff₀ hden]; nlinarith
  have hcoef_pos : ∀ (σ : ℝ), |σ| ≤ 1 → ∀ i, 0 ≤ 1 + σ * ε * g i := by
    intro σ hσ i
    have h1 : |σ * ε * g i| ≤ 1 / 2 := by
      have heq : |σ * ε * g i| = |σ| * (ε * |g i|) := by
        rw [abs_mul, abs_mul, abs_of_pos hε_pos]; ring
      rw [heq]
      calc |σ| * (ε * |g i|) ≤ 1 * (1 / 2) :=
            mul_le_mul hσ (hε_bound i) (by positivity) (by norm_num)
        _ = 1 / 2 := by norm_num
    have := (abs_le.mp h1).1; linarith
  -- (g) measure decomposition over the disjoint cover.
  set W : Set ℝ := ⋃ i, U i with hW_def
  have hWmeas : MeasurableSet W := MeasurableSet.iUnion hUmeas
  have hrestrictW : μ.restrict W = ∑ i, μ.restrict (U i) := by
    rw [hW_def, Measure.restrict_iUnion hUdisj hUmeas, Measure.sum_fintype]
  have hdecomp : μ = μ.restrict Wᶜ + ∑ i, μ.restrict (U i) := by
    rw [← hrestrictW, add_comm]
    exact (Measure.restrict_add_restrict_compl hWmeas).symm
  -- (h) the two perturbed measures.
  set pert : ℝ → Measure ℝ := fun σ =>
    μ.restrict Wᶜ + ∑ i, ENNReal.ofReal (1 + σ * ε * g i) • μ.restrict (U i) with hpert_def
  have hpert_integral : ∀ (σ : ℝ), |σ| ≤ 1 → ∀ (f : ℝ → ℝ), Integrable f μ →
      ∫ t, f t ∂(pert σ)
        = (∫ t in Wᶜ, f t ∂μ) + ∑ i, (1 + σ * ε * g i) * (∫ t in U i, f t ∂μ) := by
    intro σ hσ f hf
    have hsum_int : Integrable f
        (∑ i, ENNReal.ofReal (1 + σ * ε * g i) • μ.restrict (U i)) :=
      (integrable_finset_sum_measure).2
        (fun i _ => (hf.restrict).smul_measure ENNReal.ofReal_ne_top)
    rw [hpert_def, integral_add_measure hf.restrict hsum_int,
      integral_finset_sum_measure
        (fun i _ => (hf.restrict).smul_measure ENNReal.ofReal_ne_top)]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_smul_measure, ENNReal.toReal_ofReal (hcoef_pos σ hσ i), smul_eq_mul]
  have hsplit : ∀ (f : ℝ → ℝ), Integrable f μ →
      (∫ t in Wᶜ, f t ∂μ) + ∑ i, (∫ t in U i, f t ∂μ) = ∫ t, f t ∂μ := by
    intro f hf
    conv_rhs => rw [hdecomp]
    rw [integral_add_measure hf.restrict
        ((integrable_finset_sum_measure).2 (fun i _ => hf.restrict)),
      integral_finset_sum_measure (fun i _ => hf.restrict)]
  have hmass1 : (μ Wᶜ).toReal + ∑ i, (μ (U i)).toReal = 1 := by
    have hsplit1 := hsplit (fun _ => (1 : ℝ)) (integrable_const 1)
    simpa [setIntegral_const, integral_const, hprob.measure_univ] using hsplit1
  have hpert_mem : ∀ (σ : ℝ), |σ| ≤ 1 → pert σ ∈ MomentSlice a b s := by
    intro σ hσ
    have hmean' : ∫ t, t ∂(pert σ) = 0 := by
      rw [hpert_integral σ hσ (fun t => t) hint1]
      have hcollect : (∫ t in Wᶜ, t ∂μ) + ∑ i, (1 + σ * ε * g i) * (∫ t in U i, t ∂μ)
          = ((∫ t in Wᶜ, t ∂μ) + ∑ i, (∫ t in U i, t ∂μ))
            + σ * ε * ∑ i, g i * (∫ t in U i, t ∂μ) := by
        rw [add_assoc]
        congr 1
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro i _; ring
      rw [hcollect, hsplit (fun t => t) hint1, hmean, H1]; ring
    have hsec' : ∫ t, t ^ 2 ∂(pert σ) = s := by
      rw [hpert_integral σ hσ (fun t => t ^ 2) hint2]
      have hcollect : (∫ t in Wᶜ, t ^ 2 ∂μ)
            + ∑ i, (1 + σ * ε * g i) * (∫ t in U i, t ^ 2 ∂μ)
          = ((∫ t in Wᶜ, t ^ 2 ∂μ) + ∑ i, (∫ t in U i, t ^ 2 ∂μ))
            + σ * ε * ∑ i, g i * (∫ t in U i, t ^ 2 ∂μ) := by
        rw [add_assoc]
        congr 1
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro i _; ring
      rw [hcollect, hsplit (fun t => t ^ 2) hint2, hsec, H2]; ring
    have hsupp' : (pert σ) (Set.Icc a b)ᶜ = 0 := by
      rw [hpert_def]
      simp only [Measure.add_apply, Measure.finset_sum_apply, Measure.smul_apply, smul_eq_mul]
      have hWc : μ.restrict Wᶜ (Set.Icc a b)ᶜ = 0 := by
        rw [Measure.restrict_apply measurableSet_Icc.compl]
        exact le_antisymm (le_trans (measure_mono Set.inter_subset_left) (le_of_eq hcompl))
          (zero_le _)
      have hUc : ∀ i, μ.restrict (U i) (Set.Icc a b)ᶜ = 0 := by
        intro i
        rw [Measure.restrict_apply measurableSet_Icc.compl]
        exact le_antisymm (le_trans (measure_mono Set.inter_subset_left) (le_of_eq hcompl))
          (zero_le _)
      rw [hWc, zero_add]
      apply Finset.sum_eq_zero
      intro i _
      rw [hUc i, mul_zero]
    have hprob' : IsProbabilityMeasure (pert σ) := by
      refine ⟨?_⟩
      rw [hpert_def]
      simp only [Measure.add_apply, Measure.finset_sum_apply, Measure.smul_apply, smul_eq_mul,
        Measure.restrict_apply_univ]
      have hreg : ∀ i, (1 + σ * ε * g i) * (μ (U i)).toReal
          = (μ (U i)).toReal + (σ * ε) * (g i * (μ (U i)).toReal) := by intro i; ring
      have hreal : (μ Wᶜ).toReal + ∑ i, (1 + σ * ε * g i) * (μ (U i)).toReal = 1 := by
        rw [Finset.sum_congr rfl (fun i _ => hreg i), Finset.sum_add_distrib,
          ← Finset.mul_sum, H0, mul_zero, add_zero]
        exact hmass1
      have hWfin : μ Wᶜ ≠ ∞ := measure_ne_top μ _
      have hnn : (0 : ℝ) ≤ ∑ i, (1 + σ * ε * g i) * (μ (U i)).toReal :=
        Finset.sum_nonneg (fun i _ =>
          mul_nonneg (hcoef_pos σ hσ i) ENNReal.toReal_nonneg)
      calc μ Wᶜ + ∑ i, ENNReal.ofReal (1 + σ * ε * g i) * μ (U i)
          = ENNReal.ofReal ((μ Wᶜ).toReal
              + ∑ i, (1 + σ * ε * g i) * (μ (U i)).toReal) := by
            rw [ENNReal.ofReal_add ENNReal.toReal_nonneg hnn, ENNReal.ofReal_toReal hWfin]
            congr 1
            rw [ENNReal.ofReal_sum_of_nonneg
              (fun i _ => mul_nonneg (hcoef_pos σ hσ i) ENNReal.toReal_nonneg)]
            apply Finset.sum_congr rfl
            intro i _
            rw [ENNReal.ofReal_mul (hcoef_pos σ hσ i), ENNReal.ofReal_toReal (hUne i)]
        _ = ENNReal.ofReal 1 := by rw [hreal]
        _ = 1 := by simp
    exact ⟨hprob', hsupp', hmean', hsec'⟩
  -- (j) the two perturbations are distinct, witnessed on `U i₀`.
  have hval : ∀ (σ : ℝ), (pert σ) (U i₀) = ENNReal.ofReal (1 + σ * ε * g i₀) * μ (U i₀) := by
    intro σ
    rw [hpert_def]
    simp only [Measure.add_apply, Measure.finset_sum_apply, Measure.smul_apply, smul_eq_mul]
    have hsubW : U i₀ ⊆ W := fun y hy => Set.mem_iUnion.2 ⟨i₀, hy⟩
    have hWc0 : μ.restrict Wᶜ (U i₀) = 0 := by
      rw [Measure.restrict_apply (hUmeas i₀)]
      rw [(disjoint_compl_right.mono_left hsubW).inter_eq, measure_empty]
    have hUi : ∀ j, μ.restrict (U j) (U i₀)
        = if j = i₀ then μ (U i₀) else 0 := by
      intro j
      rw [Measure.restrict_apply (hUmeas i₀)]
      by_cases hji : j = i₀
      · subst hji; rw [Set.inter_self]; simp
      · have hdis : Disjoint (U i₀) (U j) := hUdisj (fun h => hji h.symm)
        rw [hdis.inter_eq, measure_empty]; simp [hji]
    rw [hWc0, zero_add,
      Finset.sum_eq_single i₀
        (fun j _ hj => by rw [hUi j]; simp [hj])
        (fun h => absurd (Finset.mem_univ i₀) h)]
    rw [hUi i₀]; simp
  have hdistinct : pert 1 ≠ pert (-1) := by
    intro heq
    have e1 := hval 1
    have e2 := hval (-1)
    rw [heq] at e1
    rw [e1] at e2
    -- e2 : ofReal (1+1εg i₀) * μ (U i₀) = ofReal (1+(-1)εg i₀) * μ (U i₀)
    have hreal := congrArg ENNReal.toReal e2
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (hcoef_pos 1 (by norm_num) i₀),
      ENNReal.toReal_ofReal (hcoef_pos (-1) (by norm_num) i₀)] at hreal
    have hpos : 0 < (μ (U i₀)).toReal := ENNReal.toReal_pos (hUpos i₀).ne' (hUne i₀)
    have hz : ε * g i₀ = 0 := by
      have h2 : (ε * g i₀) * (μ (U i₀)).toReal = 0 := by linear_combination hreal / 2
      rcases mul_eq_zero.mp h2 with h | h
      · exact h
      · exact absurd h hpos.ne'
    rcases mul_eq_zero.mp hz with h | h
    · exact hε_pos.ne' h
    · exact hi₀ h
  -- (k) midpoint relation and the extreme-point contradiction.
  have hcoef_combine : ∀ i, (1 / 2 : ℝ≥0∞) * ENNReal.ofReal (1 + 1 * ε * g i)
      + (1 / 2 : ℝ≥0∞) * ENNReal.ofReal (1 + (-1) * ε * g i) = 1 := by
    intro i
    rw [← mul_add, ← ENNReal.ofReal_add (hcoef_pos 1 (by norm_num) i)
      (hcoef_pos (-1) (by norm_num) i)]
    have h2 : (1 + 1 * ε * g i) + (1 + (-1) * ε * g i) = 2 := by ring
    rw [h2, show (2 : ℝ) = ((2 : ℝ≥0∞)).toReal by simp, ENNReal.ofReal_toReal (by simp),
      ENNReal.div_mul_cancel (by simp) (by simp)]
  have hmid : μ = (1 / 2 : ℝ≥0∞) • pert 1 + (1 / 2 : ℝ≥0∞) • pert (-1) := by
    refine Measure.ext fun A hA => ?_
    have hpA : ∀ (σ : ℝ), (pert σ) A
        = μ.restrict Wᶜ A + ∑ i, ENNReal.ofReal (1 + σ * ε * g i) * μ.restrict (U i) A := by
      intro σ
      rw [hpert_def]
      simp only [Measure.add_apply, Measure.finset_sum_apply, Measure.smul_apply, smul_eq_mul]
    have hμA : μ A = μ.restrict Wᶜ A + ∑ i, μ.restrict (U i) A := by
      conv_lhs => rw [hdecomp]
      simp only [Measure.add_apply, Measure.finset_sum_apply]
    have key : ∀ i, (1 / 2 : ℝ≥0∞) * (ENNReal.ofReal (1 + 1 * ε * g i) * μ.restrict (U i) A)
        + (1 / 2 : ℝ≥0∞) * (ENNReal.ofReal (1 + (-1) * ε * g i) * μ.restrict (U i) A)
        = μ.restrict (U i) A := by
      intro i
      rw [← mul_assoc, ← mul_assoc, ← add_mul, hcoef_combine i, one_mul]
    rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul,
      hpA 1, hpA (-1), hμA, mul_add, mul_add, Finset.mul_sum, Finset.mul_sum,
      add_add_add_comm, ← Finset.sum_add_distrib]
    congr 1
    · rw [← add_mul, ENNReal.add_halves, one_mul]
    · exact Finset.sum_congr rfl (fun i _ => (key i).symm)
  apply hdistinct
  have ht : (1 : ℝ≥0∞) - 1 / 2 = 1 / 2 :=
    ENNReal.sub_eq_of_eq_add (by simp) (ENNReal.add_halves 1).symm
  refine hext.2 (pert 1) (hpert_mem 1 (by norm_num)) (pert (-1)) (hpert_mem (-1) (by norm_num))
    (1 / 2) (by norm_num) (by norm_num) ?_
  rw [ht]; exact hmid

/-- An extreme probability measure in the two-moment slice has a finite topological support
with at most three points. -/
theorem support_finite_ncard_le_three_of_isExtremePoint {a b s : ℝ} {μ : Measure ℝ}
    (hext : IsExtremePoint (MomentSlice a b s) μ) :
    μ.support.Finite ∧ μ.support.ncard ≤ 3 := by
  classical
  let S : Set ℝ := μ.support
  have hno : ∀ (y : Fin 4 → ℝ), Function.Injective y → (∀ i, y i ∈ S) → False := by
    intro y hyinj hysupp
    exact not_four_distinct_in_support hext y hyinj hysupp
  constructor
  · by_contra hinf
    have hInf : S.Infinite := by simpa [S, Set.not_finite] using hinf
    obtain ⟨t, hts, htfin, htc⟩ := hInf.exists_subset_ncard_eq 4
    have hcard : htfin.toFinset.card = 4 := by
      simpa [Set.ncard_eq_toFinset_card t htfin] using htc
    let e : Fin 4 ↪o ℝ := htfin.toFinset.orderEmbOfFin hcard
    exact hno (fun i => e i) e.injective (fun i => by
      have hmemFin : e i ∈ htfin.toFinset := by
        change htfin.toFinset.orderEmbOfFin hcard i ∈ htfin.toFinset
        exact Finset.orderEmbOfFin_mem htfin.toFinset hcard i
      exact hts (by simpa [Set.Finite.mem_toFinset] using hmemFin))
  · by_contra hle
    push_neg at hle
    have h4 : 4 ≤ S.ncard := Nat.succ_le_of_lt hle
    obtain ⟨t, hts, htc⟩ := Set.exists_subset_card_eq (s := S) h4
    have htfin : t.Finite := Set.finite_of_ncard_ne_zero (by rw [htc]; simp)
    have hcard : htfin.toFinset.card = 4 := by
      simpa [Set.ncard_eq_toFinset_card t htfin] using htc
    let e : Fin 4 ↪o ℝ := htfin.toFinset.orderEmbOfFin hcard
    exact hno (fun i => e i) e.injective (fun i => by
      have hmemFin : e i ∈ htfin.toFinset := by
        change htfin.toFinset.orderEmbOfFin hcard i ∈ htfin.toFinset
        exact Finset.orderEmbOfFin_mem htfin.toFinset hcard i
      exact hts (by simpa [Set.Finite.mem_toFinset] using hmemFin))

/-- An extreme probability measure in the two-moment slice is a positive discrete measure
supported on at most three points of the interval. -/
theorem isAtomic_le_three_of_isExtremePoint {a b s : ℝ} {μ : Measure ℝ}
    (hext : IsExtremePoint (MomentSlice a b s) μ) :
    ∃ (T : Finset ℝ) (w : ℝ → ℝ), (∀ x ∈ T, 0 < w x) ∧ (∀ x ∈ T, x ∈ Set.Icc a b) ∧
      T.card ≤ 3 ∧ μ = discreteMeasure T w := by
  classical
  obtain ⟨hprob, hcompl, _, _⟩ := hext.1
  obtain ⟨hsuppfin, hsuppcard⟩ := support_finite_ncard_le_three_of_isExtremePoint hext
  let T : Finset ℝ := hsuppfin.toFinset
  let w : ℝ → ℝ := fun x => (μ {x}).toReal
  have hTsupport : (T : Set ℝ) = μ.support := by simp [T]
  have hTcard : T.card ≤ 3 := by
    have hcard : T.card = μ.support.ncard := by
      simp [T, Set.ncard_eq_toFinset_card μ.support hsuppfin]
    omega
  have hsingle_pos : ∀ x ∈ μ.support, 0 < μ {x} := by
    intro x hx
    let V : Set ℝ := (μ.support \ {x})ᶜ
    have hVopen : IsOpen V := (hsuppfin.diff (t := ({x} : Set ℝ))).isClosed.isOpen_compl
    have hxV : x ∈ V := by simp [V]
    have hVpos : 0 < μ V := (Measure.mem_support_iff_forall x).1 hx V (hVopen.mem_nhds hxV)
    have hVS : V ∩ μ.support = {x} := by
      ext y
      by_cases hyx : y = x
      · subst hyx
        simp [V, hx]
      · simp [V, hyx]
    have hconull : μ μ.supportᶜ = 0 := Measure.measure_compl_support
    have hVeq : μ (V ∩ μ.support) = μ V := measure_inter_conull (μ := μ) (s := V) hconull
    rw [hVS] at hVeq
    rwa [hVeq]
  have hpos : ∀ x ∈ T, 0 < w x := by
    intro x hxT
    have hxS : x ∈ μ.support := hTsupport ▸ Finset.mem_coe.mpr hxT
    have hlt : μ {x} ≠ ∞ := by
      have hle : μ {x} ≤ μ Set.univ := measure_mono (Set.subset_univ _)
      rw [hprob.measure_univ] at hle
      exact ne_top_of_le_ne_top ENNReal.one_ne_top hle
    have hxpos := hsingle_pos x hxS
    simpa only [w] using ENNReal.toReal_pos hxpos.ne' hlt
  have hTab : ∀ x ∈ T, x ∈ Set.Icc a b := by
    intro x hxT
    by_contra hxnot
    have hxS : x ∈ μ.support := hTsupport ▸ Finset.mem_coe.mpr hxT
    have hxpos : 0 < μ {x} := hsingle_pos x hxS
    have hsub : ({x} : Set ℝ) ⊆ (Set.Icc a b)ᶜ := by simpa [Set.subset_def] using hxnot
    have hle : μ {x} ≤ μ (Set.Icc a b)ᶜ := measure_mono hsub
    rw [hcompl] at hle
    exact (ne_of_gt hxpos) (le_antisymm hle (zero_le _))
  refine ⟨T, w, hpos, hTab, hTcard, ?_⟩
  refine Measure.ext fun A hA => ?_
  have hconull : μ μ.supportᶜ = 0 := Measure.measure_compl_support
  have hAinter : μ (A ∩ μ.support) = μ A := measure_inter_conull (μ := μ) (s := A) hconull
  rw [← hAinter]
  have hUnion : A ∩ μ.support = ⋃ x ∈ T.filter (fun x => x ∈ A), ({x} : Set ℝ) := by
    ext y
    simp [T, Set.Finite.mem_toFinset, and_left_comm, and_assoc]
  rw [hUnion]
  rw [measure_biUnion_finset]
  · rw [discreteMeasure, Measure.finset_sum_apply, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Measure.smul_apply, Measure.dirac_apply, smul_eq_mul]
    have hlt : μ {x} ≠ ∞ := by
      have hle : μ {x} ≤ μ Set.univ := measure_mono (Set.subset_univ _)
      rw [hprob.measure_univ] at hle
      exact ne_top_of_le_ne_top ENNReal.one_ne_top hle
    by_cases hxA : x ∈ A
    · simp [hxA, w, ENNReal.ofReal_toReal hlt]
    · simp [hxA]
  · intro x _ y _ hxy
    exact Set.disjoint_singleton.2 hxy
  · intro x _
    exact MeasurableSet.singleton x

/-- An extreme probability measure in the two-moment slice is carried by a finite set of at
most three points. -/
theorem exists_cardSupportLe_three_of_isExtremePoint {a b s : ℝ} {μ : Measure ℝ}
    (hext : IsExtremePoint (MomentSlice a b s) μ) :
    ∃ T : Finset ℝ, T.card ≤ 3 ∧ μ (↑T : Set ℝ)ᶜ = 0 := by
  classical
  obtain ⟨hsuppfin, hsuppcard⟩ := support_finite_ncard_le_three_of_isExtremePoint hext
  refine ⟨hsuppfin.toFinset, ?_, ?_⟩
  · simpa [Set.ncard_eq_toFinset_card μ.support hsuppfin] using hsuppcard
  · rw [Set.Finite.coe_toFinset]; exact Measure.measure_compl_support


end

end Causalean.Mathlib.MeasureTheory
