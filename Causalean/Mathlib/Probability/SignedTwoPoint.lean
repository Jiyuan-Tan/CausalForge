/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Mathlib.Probability.BernoulliMeasure
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Algebra.Field

/-! # Symmetric signed two-point mean channel

The symmetric two-point outcome law `twoPointMean B u` supported on `{−B, B}` with mean `u`:
`Q_u(B) = (1 + u/B)/2`, `Q_u(−B) = (1 − u/B)/2`.  It is the affine image of the `{0,1}` Bernoulli
law `bernoulliLaw` under `x ↦ 2Bx − B`, which lets its Kullback–Leibler divergence inherit the
quadratic band of the Bernoulli KL.

This file provides:

* `twoPointMean` — the signed two-point channel, with `measurable_twoPointMean`,
  `twoPointMean_isProbabilityMeasure`, `twoPointMean_integral`, `twoPointMean_mean`,
  `twoPointMean_bad_support_zero`;
* `klDiv_map_measurableEquiv` — KL-divergence invariance under a measurable equivalence;
* `twoPointMean_eq_map_bernoulli` — the affine-image representation;
* `bernoulli_mean_channel_kl` — the KL band `KL(Q_u, Q_v) ≤ 2(u − v)²/B²` for `|u|,|v| ≤ B/2`.

It is the reusable least-favorable outcome channel for two-point / Le Cam minimax lower bounds in
a mean-estimation setting.
-/

namespace Causalean.Mathlib.Probability

open MeasureTheory

open scoped ENNReal

/-- **Symmetric two-point mean channel.**  For a scale `B` and a target mean `u`, the law
`twoPointMean B u` on `{−B, B}` puts mass `(1 + u/B)/2` on `B` and `(1 − u/B)/2` on `−B`; its mean
is `u`. -/
noncomputable def twoPointMean (B u : ℝ) : Measure ℝ :=
  ENNReal.ofReal ((1 + u / B) / 2) • Measure.dirac B
    + ENNReal.ofReal ((1 - u / B) / 2) • Measure.dirac (-B)

/-- For a fixed scale `B`, the signed two-point mean channel is measurable as
a function of the target mean `u`. -/
@[fun_prop] lemma measurable_twoPointMean (B : ℝ) :
    Measurable (fun u : ℝ => twoPointMean B u) := by
  unfold twoPointMean
  fun_prop

private lemma twoPointMean_coef_nonneg {B u : ℝ} (hB : 0 < B) (hu : |u| ≤ B) :
    0 ≤ (1 + u / B) / 2 ∧ 0 ≤ (1 - u / B) / 2 := by
  have hbounds := abs_le.mp hu
  constructor <;> field_simp [ne_of_gt hB] <;> nlinarith [hbounds.1, hbounds.2, hB]

/-- **The signed two-point channel is a probability measure.**  For `0 < B` and `|u| ≤ B` the
total mass of `twoPointMean B u` is `1`. -/
lemma twoPointMean_isProbabilityMeasure {B u : ℝ} (hB : 0 < B) (hu : |u| ≤ B) :
    IsProbabilityMeasure (twoPointMean B u) := by
  rw [isProbabilityMeasure_iff]
  unfold twoPointMean
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  simp only [Measure.dirac_apply, Set.indicator_of_mem, Set.mem_univ, Pi.one_apply,
    smul_eq_mul, mul_one]
  rcases twoPointMean_coef_nonneg hB hu with ⟨hplus, hminus⟩
  rw [← ENNReal.ofReal_add hplus hminus]
  rw [show (1 + u / B) / 2 + (1 - u / B) / 2 = (1 : ℝ) by ring]
  simp

/-- **Two-point integral.**  For `0 < B` and `|u| ≤ B`, integrating `f` against `twoPointMean B u`
returns the two-point weighted average `((1 + u/B)/2)·f(B) + ((1 − u/B)/2)·f(−B)`. -/
lemma twoPointMean_integral {B u : ℝ} (hB : 0 < B) (hu : |u| ≤ B)
    (f : ℝ → ℝ) :
    ∫ y, f y ∂twoPointMean B u =
      ((1 + u / B) / 2) * f B + ((1 - u / B) / 2) * f (-B) := by
  unfold twoPointMean
  rw [integral_add_measure]
  · rw [integral_smul_measure, integral_smul_measure]
    rcases twoPointMean_coef_nonneg hB hu with ⟨hplus, hminus⟩
    simp [hplus, hminus, smul_eq_mul]
  · exact Integrable.smul_measure (μ := Measure.dirac B)
      (c := ENNReal.ofReal ((1 + u / B) / 2))
      (integrable_dirac (f := f) (a := B) (by simp [enorm])) (by simp)
  · exact Integrable.smul_measure (μ := Measure.dirac (-B))
      (c := ENNReal.ofReal ((1 - u / B) / 2))
      (integrable_dirac (f := f) (a := -B) (by simp [enorm])) (by simp)

/-- **The mean is `u`.**  For `0 < B` and `|u| ≤ B`, the expectation of the identity under
`twoPointMean B u` is exactly `u`. -/
lemma twoPointMean_mean {B u : ℝ} (hB : 0 < B) (hu : |u| ≤ B) :
    ∫ y, y ∂twoPointMean B u = u := by
  rw [twoPointMean_integral hB hu]
  field_simp [ne_of_gt hB]
  ring

/-- **The channel is supported in `[−M, M]` whenever `|B| ≤ M`.**  The mass that
`twoPointMean B u` places outside the interval `[−M, M]` is `0`. -/
lemma twoPointMean_bad_support_zero {B M u : ℝ} (hBM : |B| ≤ M) :
    (twoPointMean B u) {y | y ∉ Set.Icc (-M) M} = 0 := by
  let S : Set ℝ := {y | y ∉ Set.Icc (-M) M}
  have hS : MeasurableSet S := measurableSet_Icc.compl
  unfold twoPointMean
  change (ENNReal.ofReal ((1 + u / B) / 2) • Measure.dirac B
      + ENNReal.ofReal ((1 - u / B) / 2) • Measure.dirac (-B)) S = 0
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  have hBmem : B ∈ Set.Icc (-M) M := by
    exact abs_le.mp hBM
  have hnegBmem : -B ∈ Set.Icc (-M) M := by
    rw [Set.mem_Icc]
    constructor <;> linarith [abs_le.mp hBM |>.1, abs_le.mp hBM |>.2]
  have hBbad : B ∉ S := by simpa [S] using hBmem
  have hnegBbad : -B ∉ S := by simpa [S] using hnegBmem
  have hdiracB : Measure.dirac B S = 0 := by
    rw [Measure.dirac_apply' B hS]
    simp [hBbad]
  have hdiracNeg : Measure.dirac (-B) S = 0 := by
    rw [Measure.dirac_apply' (-B) hS]
    simp [hnegBbad]
  rw [hdiracB, hdiracNeg]
  simp

/-- **KL-divergence is invariant under a measurable equivalence.**  Pushing both finite measures
`μ, ν` forward through a measurable equivalence `e` leaves their Kullback–Leibler divergence
unchanged: `KL(e_* μ, e_* ν) = KL(μ, ν)`. -/
lemma klDiv_map_measurableEquiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    InformationTheory.klDiv (Measure.map e μ) (Measure.map e ν) =
      InformationTheory.klDiv μ ν := by
  by_cases hμν : μ ≪ ν
  · have hmap : Measure.map e μ ≪ Measure.map e ν := hμν.map e.measurable
    rw [InformationTheory.klDiv_eq_lintegral_klFun,
      InformationTheory.klDiv_eq_lintegral_klFun, if_pos hmap, if_pos hμν]
    rw [e.measurableEmbedding.lintegral_map]
    refine lintegral_congr_ae ?_
    exact (e.measurableEmbedding.rnDeriv_map μ ν).mono fun _ hx => by
      simpa using congrArg
        (fun y : ℝ≥0∞ => ENNReal.ofReal (InformationTheory.klFun y.toReal)) hx
  · have hmap_not : ¬ Measure.map e μ ≪ Measure.map e ν := by
      intro hmap
      apply hμν
      have hback :
          Measure.map e.symm (Measure.map e μ) ≪ Measure.map e.symm (Measure.map e ν) :=
        hmap.map e.symm.measurable
      simpa [Measure.map_map, Function.comp_def] using hback
    rw [InformationTheory.klDiv_eq_lintegral_klFun,
      InformationTheory.klDiv_eq_lintegral_klFun, if_neg hmap_not, if_neg hμν]

/-- **Affine-image representation.**  The `{−B, B}` mean channel is the pushforward of the `{0,1}`
Bernoulli law `bernoulliLaw ((1 + u/B)/2)` under the affine map `x ↦ 2Bx − B` (for `B > 0`). -/
lemma twoPointMean_eq_map_bernoulli (B u : ℝ) (hB : 0 < B) :
    twoPointMean B u =
      Measure.map
        (affineHomeomorph (2 * B) (-B) (by nlinarith : (2 * B : ℝ) ≠ 0)).toMeasurableEquiv
        (bernoulliLaw ((1 + u / B) / 2)) := by
  let e : ℝ ≃ᵐ ℝ :=
    (affineHomeomorph (2 * B) (-B) (by nlinarith : (2 * B : ℝ) ≠ 0)).toMeasurableEquiv
  change twoPointMean B u =
    Measure.map e (bernoulliLaw ((1 + u / B) / 2))
  rw [twoPointMean, bernoulliLaw]
  rw [Measure.map_add _ _ e.measurable]
  rw [Measure.map_smul, Measure.map_smul]
  rw [Measure.map_dirac, Measure.map_dirac]
  simp only [Homeomorph.toMeasurableEquiv_coe, affineHomeomorph_apply, mul_one,
    mul_zero, zero_add, e]
  rw [show 2 * B + -B = B by ring]
  rw [show 1 - (1 + u / B) / 2 = (1 - u / B) / 2 by ring]

/-- **KL band for the signed two-point mean channel.**  For `B > 0` and means `u, v` with
`|u| ≤ B/2` and `|v| ≤ B/2`, the Kullback–Leibler divergence between the two channels is bounded by
the quadratic `KL(Q_u, Q_v) ≤ 2(u − v)²/B²`.  This is the affine transport of the `{0,1}` Bernoulli
KL band onto the `{−B, B}` mean parametrization. -/
lemma bernoulli_mean_channel_kl (B u v : ℝ) (hB : 0 < B)
    (hu : |u| ≤ B / 2) (hv : |v| ≤ B / 2) :
    InformationTheory.klDiv (twoPointMean B u) (twoPointMean B v)
      ≤ ENNReal.ofReal (2 * (u - v) ^ 2 / B ^ 2) := by
  let p : ℝ := (1 + u / B) / 2
  let q : ℝ := (1 + v / B) / 2
  have hB_ne : B ≠ 0 := ne_of_gt hB
  have hu_bounds := abs_le.mp hu
  have hv_bounds := abs_le.mp hv
  have hp_lo : 1 / 4 ≤ p := by
    dsimp [p]
    field_simp [hB_ne]
    nlinarith [hu_bounds.1, hB]
  have hp_hi : p ≤ 3 / 4 := by
    dsimp [p]
    field_simp [hB_ne]
    nlinarith [hu_bounds.2, hB]
  have hq_lo : 1 / 4 ≤ q := by
    dsimp [q]
    field_simp [hB_ne]
    nlinarith [hv_bounds.1, hB]
  have hq_hi : q ≤ 3 / 4 := by
    dsimp [q]
    field_simp [hB_ne]
    nlinarith [hv_bounds.2, hB]
  haveI : IsFiniteMeasure (bernoulliLaw p) := by
    rw [bernoulliLaw]
    refine ⟨?_⟩
    rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
    simp only [Measure.dirac_apply, Set.mem_univ, Set.indicator_of_mem, Pi.one_apply,
      smul_eq_mul, mul_one]
    exact ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩
  haveI : IsFiniteMeasure (bernoulliLaw q) := by
    rw [bernoulliLaw]
    refine ⟨?_⟩
    rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
    simp only [Measure.dirac_apply, Set.mem_univ, Set.indicator_of_mem, Pi.one_apply,
      smul_eq_mul, mul_one]
    exact ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩
  rw [twoPointMean_eq_map_bernoulli B u hB, twoPointMean_eq_map_bernoulli B v hB,
    klDiv_map_measurableEquiv]
  have hbern :
      InformationTheory.klDiv (bernoulliLaw p) (bernoulliLaw q) ≤
        ENNReal.ofReal (4 * (p - q) ^ 2) :=
    bernoulliLaw_klDiv_le_four_sq_sub hp_lo hp_hi hq_lo hq_hi
  calc
    InformationTheory.klDiv (bernoulliLaw p) (bernoulliLaw q)
        ≤ ENNReal.ofReal (4 * (p - q) ^ 2) := hbern
    _ = ENNReal.ofReal ((u - v) ^ 2 / B ^ 2) := by
      congr 1
      subst p
      subst q
      field_simp [hB_ne]
      ring
    _ ≤ ENNReal.ofReal (2 * (u - v) ^ 2 / B ^ 2) := by
      apply ENNReal.ofReal_le_ofReal
      have hsquare : (u - v) ^ 2 ≤ 2 * (u - v) ^ 2 := by
        nlinarith [sq_nonneg (u - v)]
      exact div_le_div_of_nonneg_right hsquare (sq_nonneg B)

end Causalean.Mathlib.Probability
