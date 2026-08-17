/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Hellinger affinity of two densities against a common dominating measure

Le Cam's two-point method needs an upper bound on the total variation distance between the
two candidate laws.  When both laws are written as densities `f, g` against **one** common
dominating measure `μ` — the situation in essentially every explicit construction, where the
two laws are two tilts of the same base measure — the cleanest such bound goes through the
*affinity*

  `densityAffinity μ f g = ∫ √(f·g) ∂μ`

(also called the Bhattacharyya coefficient), and its *defect* `1 − affinity`.

Main results:

* `hellingerSqDensity_eq_two_mul_one_sub_affinity` — for normalized nonnegative densities the
  unhalved squared Hellinger distance `∫ (√f − √g)² ∂μ` equals `2·(1 − affinity)`;
* `tvDist_le_sqrt_two_mul_one_sub_affinity` — the Cauchy–Schwarz comparison
  `tvDist ≤ √(2·(1 − affinity))` between the two `withDensity` laws;
* `densityAffinity_pi` — affinity **tensorizes**: the affinity of two product densities on a
  finite product of measure spaces is the product of the coordinate affinities;
* `one_sub_prod_le_sum` — the union-bound companion `1 − ∏ aᵢ ≤ ∑ (1 − aᵢ)` on `[0,1]`,
  which turns the tensorized affinity into a *sum* of coordinate defects.

This is deliberately an affinity-number interface, not a general Hellinger-divergence theory:
both laws are densities against one common measure, so no mutual absolute-continuity premise
appears.  The complementary route via Radon–Nikodym derivatives (and the Bretagnolle–Huber
lower bound on the affinity) lives in `Causalean/Stat/Minimax/BretagnolleHuber.lean`.
-/

import Causalean.Stat.Minimax.TotalVariation
import Causalean.Stat.Minimax.Scheffe
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Pi

/-! # Hellinger Affinity for Common-Measure Densities

This file develops the Hellinger/Bhattacharyya affinity of two nonnegative densities taken
against a single dominating measure, its identity with the squared Hellinger distance, the
Cauchy–Schwarz bound of total variation by the affinity defect, and the tensorization of
affinity over finite products. These are the ingredients of a product-construction Le Cam
two-point (or multi-point) lower bound. -/

open scoped BigOperators ENNReal
open MeasureTheory

namespace Causalean.Stat

/-- The **Hellinger (Bhattacharyya) affinity** of two nonnegative densities taken against one
common dominating measure: the integral of the square root of their pointwise product.  It
equals one when the two densities agree almost everywhere and falls toward zero as the two
laws separate, so it measures how hard the two laws are to tell apart. -/
noncomputable def densityAffinity
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f g : α → ℝ) : ℝ :=
  ∫ x, Real.sqrt (f x * g x) ∂μ

/-- The **squared Hellinger distance** between two nonnegative densities against one common
dominating measure, in the unhalved convention: the integral of the squared difference of
their pointwise square roots. -/
noncomputable def hellingerSqDensity
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f g : α → ℝ) : ℝ :=
  ∫ x, (Real.sqrt (f x) - Real.sqrt (g x)) ^ 2 ∂μ

/-- For two integrable nonnegative densities that each integrate to one, the unhalved squared
Hellinger distance is exactly twice the affinity defect, i.e. twice one minus the affinity.
This is the algebraic identity that lets an affinity computation be read as a Hellinger
distance and back. -/
lemma hellingerSqDensity_eq_two_mul_one_sub_affinity
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f g : α → ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hf0 : 0 ≤ f) (hg0 : 0 ≤ g)
    (hf1 : ∫ x, f x ∂μ = 1) (hg1 : ∫ x, g x ∂μ = 1) :
    hellingerSqDensity μ f g =
      2 * (1 - densityAffinity μ f g) := by
  have hsf_asm :
      AEStronglyMeasurable (fun x => Real.sqrt (f x)) μ :=
    (Real.continuous_sqrt.measurable.comp_aemeasurable
      hf.aestronglyMeasurable.aemeasurable).aestronglyMeasurable
  have hsg_asm :
      AEStronglyMeasurable (fun x => Real.sqrt (g x)) μ :=
    (Real.continuous_sqrt.measurable.comp_aemeasurable
      hg.aestronglyMeasurable.aemeasurable).aestronglyMeasurable
  have hsf : MemLp (fun x => Real.sqrt (f x)) 2 μ := by
    rw [memLp_two_iff_integrable_sq hsf_asm]
    convert hf using 1
    funext x
    exact Real.sq_sqrt (hf0 x)
  have hsg : MemLp (fun x => Real.sqrt (g x)) 2 μ := by
    rw [memLp_two_iff_integrable_sq hsg_asm]
    convert hg using 1
    funext x
    exact Real.sq_sqrt (hg0 x)
  have hcross :
      Integrable (fun x => Real.sqrt (f x * g x)) μ := by
    convert hsf.integrable_mul hsg using 1
    funext x
    simp only [Pi.mul_apply]
    rw [Real.sqrt_mul (hf0 x)]
  unfold hellingerSqDensity densityAffinity
  rw [show
      (fun x => (Real.sqrt (f x) - Real.sqrt (g x)) ^ 2) =
        (fun x => f x + g x - 2 * Real.sqrt (f x * g x)) by
    funext x
    rw [Real.sqrt_mul (hf0 x)]
    nlinarith [Real.sq_sqrt (hf0 x), Real.sq_sqrt (hg0 x)]]
  change ∫ x, (f + g) x - 2 * Real.sqrt (f x * g x) ∂μ =
    2 * (1 - ∫ x, Real.sqrt (f x * g x) ∂μ)
  rw [integral_sub (hf.add hg) (hcross.const_mul 2),
    show (∫ x, (f + g) x ∂μ) = ∫ x, f x + g x ∂μ by rfl,
    integral_add hf hg, integral_const_mul, hf1, hg1]
  ring

/-- Weighting a common dominating measure by two normalized nonnegative densities produces two
probability laws whose total variation distance is at most the square root of twice the
affinity defect.  This is the Cauchy–Schwarz half of the standard total-variation–Hellinger
comparison, and it is what converts an affinity computation into a Le Cam two-point bound. -/
lemma tvDist_le_sqrt_two_mul_one_sub_affinity
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f g : α → ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hf0 : 0 ≤ f) (hg0 : 0 ≤ g)
    (hf1 : ∫ x, f x ∂μ = 1) (hg1 : ∫ x, g x ∂μ = 1) :
    tvDist
        (μ.withDensity (fun x => ENNReal.ofReal (f x)))
        (μ.withDensity (fun x => ENNReal.ofReal (g x))) ≤
      Real.sqrt (2 * (1 - densityAffinity μ f g)) := by
  let P := μ.withDensity (fun x => ENNReal.ofReal (f x))
  let Q := μ.withDensity (fun x => ENNReal.ofReal (g x))
  have hreal_f {A : Set α} (hA : MeasurableSet A) :
      P.real A = ∫ x in A, f x ∂μ := by
    rw [measureReal_def, withDensity_apply _ hA]
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hf.integrableOn]
    · rw [ENNReal.toReal_ofReal]
      exact integral_nonneg_of_ae
        (Filter.Eventually.of_forall fun x => hf0 x)
    · exact Filter.Eventually.of_forall fun x => hf0 x
  have hreal_g {A : Set α} (hA : MeasurableSet A) :
      Q.real A = ∫ x in A, g x ∂μ := by
    rw [measureReal_def, withDensity_apply _ hA]
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hg.integrableOn]
    · rw [ENNReal.toReal_ofReal]
      exact integral_nonneg_of_ae
        (Filter.Eventually.of_forall fun x => hg0 x)
    · exact Filter.Eventually.of_forall fun x => hg0 x
  have hfg : Integrable (fun x => f x - g x) μ := hf.sub hg
  have hfg0 : ∫ x, (f x - g x) ∂μ = 0 := by
    rw [integral_sub hf hg, hf1, hg1]
    ring
  have htv :
      tvDist P Q ≤
        (1 / 2 : ℝ) * ∫ x, |f x - g x| ∂μ := by
    unfold tvDist
    refine ciSup_le fun A => ?_
    rw [hreal_f A.2, hreal_g A.2,
      ← integral_sub hf.integrableOn hg.integrableOn]
    exact
      abs_setIntegral_le_half_integral_abs_of_integral_eq_zero
        hfg hfg0 A.2
  have hsf_asm :
      AEStronglyMeasurable (fun x => Real.sqrt (f x)) μ :=
    (Real.continuous_sqrt.measurable.comp_aemeasurable
      hf.aestronglyMeasurable.aemeasurable).aestronglyMeasurable
  have hsg_asm :
      AEStronglyMeasurable (fun x => Real.sqrt (g x)) μ :=
    (Real.continuous_sqrt.measurable.comp_aemeasurable
      hg.aestronglyMeasurable.aemeasurable).aestronglyMeasurable
  have hsf : MemLp (fun x => Real.sqrt (f x)) 2 μ := by
    rw [memLp_two_iff_integrable_sq hsf_asm]
    convert hf using 1
    funext x
    exact Real.sq_sqrt (hf0 x)
  have hsg : MemLp (fun x => Real.sqrt (g x)) 2 μ := by
    rw [memLp_two_iff_integrable_sq hsg_asm]
    convert hg using 1
    funext x
    exact Real.sq_sqrt (hg0 x)
  let u : α → ℝ := fun x => Real.sqrt (f x) - Real.sqrt (g x)
  let v : α → ℝ := fun x => Real.sqrt (f x) + Real.sqrt (g x)
  have hu : MemLp u 2 μ := hsf.sub hsg
  have hv : MemLp v 2 μ := hsf.add hsg
  have hfact : ∀ x, |f x - g x| = |u x| * |v x| := by
    intro x
    rw [← abs_mul]
    dsimp [u, v]
    rw [show
      (Real.sqrt (f x) - Real.sqrt (g x)) *
          (Real.sqrt (f x) + Real.sqrt (g x)) =
        Real.sqrt (f x) ^ 2 - Real.sqrt (g x) ^ 2 by ring]
    simp only [Real.sq_sqrt (hf0 x), Real.sq_sqrt (hg0 x)]
  have hholder :
      ∫ x, |u x| * |v x| ∂μ ≤
        (∫ x, |u x| ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) *
          (∫ x, |v x| ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
    apply integral_mul_le_Lp_mul_Lq_of_nonneg
        (p := (2 : ℝ)) (q := (2 : ℝ))
    · exact Real.HolderConjugate.two_two
    · exact Filter.Eventually.of_forall fun x => abs_nonneg _
    · exact Filter.Eventually.of_forall fun x => abs_nonneg _
    · rw [show (ENNReal.ofReal 2 : ℝ≥0∞) = 2 from by norm_num]
      exact hu.abs
    · rw [show (ENNReal.ofReal 2 : ℝ≥0∞) = 2 from by norm_num]
      exact hv.abs
  have hsfg : Integrable
      (fun x => Real.sqrt (f x) * Real.sqrt (g x)) μ :=
    hsf.integrable_mul hsg
  have hu_sq :
      ∫ x, |u x| ^ (2 : ℝ) ∂μ =
        2 * (1 - densityAffinity μ f g) := by
    simp_rw [Real.rpow_two, sq_abs]
    have hpoint : (fun x => u x ^ 2) =
        (fun x => f x + g x -
          2 * Real.sqrt (f x * g x)) := by
      funext x
      dsimp [u]
      rw [show Real.sqrt (f x * g x) =
          Real.sqrt (f x) * Real.sqrt (g x) by
        rw [Real.sqrt_mul (hf0 x)]]
      nlinarith [Real.sq_sqrt (hf0 x), Real.sq_sqrt (hg0 x)]
    rw [hpoint]
    have hsqrtfg : Integrable (fun x => Real.sqrt (f x * g x)) μ := by
      convert hsfg using 1
      funext x
      rw [Real.sqrt_mul (hf0 x)]
    change ∫ x, (f + g) x - (2 * (fun x => Real.sqrt (f x * g x)) x) ∂μ =
      2 * (1 - densityAffinity μ f g)
    rw [integral_sub (hf.add hg) (hsqrtfg.const_mul 2)]
    change (∫ x, f x + g x ∂μ) -
        ∫ x, 2 * Real.sqrt (f x * g x) ∂μ =
      2 * (1 - densityAffinity μ f g)
    rw [integral_add hf hg, integral_const_mul, hf1, hg1]
    simp [densityAffinity]
    ring
  have hv_sq_plain :
      ∫ x, v x ^ 2 ∂μ ≤ 4 := by
    calc
      ∫ x, v x ^ 2 ∂μ ≤ ∫ x, (2 * f x + 2 * g x) ∂μ := by
        apply integral_mono_ae hv.integrable_sq
          ((hf.const_mul 2).add (hg.const_mul 2))
        exact Filter.Eventually.of_forall fun x => by
          dsimp [v]
          have hsf0 := Real.sqrt_nonneg (f x)
          have hsg0 := Real.sqrt_nonneg (g x)
          nlinarith [Real.sq_sqrt (hf0 x), Real.sq_sqrt (hg0 x),
            sq_nonneg (Real.sqrt (f x) - Real.sqrt (g x))]
      _ = 4 := by
        rw [integral_add (hf.const_mul 2) (hg.const_mul 2),
          integral_const_mul, integral_const_mul, hf1, hg1]
        ring
  have hv_sq :
      ∫ x, |v x| ^ (2 : ℝ) ∂μ ≤ 4 := by
    simpa [Real.rpow_two, sq_abs] using hv_sq_plain
  have hu_sq_nonneg : 0 ≤ 2 * (1 - densityAffinity μ f g) := by
    rw [← hu_sq]
    exact integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun x => by positivity)
  exact htv.trans (by
    rw [show (fun x => |f x - g x|) =
        (fun x => |u x| * |v x|) by funext x; exact hfact x]
    calc
      (1 / 2 : ℝ) * ∫ x, |u x| * |v x| ∂μ ≤
          (1 / 2 : ℝ) *
            ((∫ x, |u x| ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) *
              (∫ x, |v x| ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ))) := by
        gcongr
      _ ≤ Real.sqrt (2 * (1 - densityAffinity μ f g)) := by
        rw [hu_sq, ← Real.sqrt_eq_rpow]
        have hv_sq_nonneg :
            0 ≤ ∫ x, |v x| ^ (2 : ℝ) ∂μ :=
          integral_nonneg_of_ae
            (Filter.Eventually.of_forall fun x => by positivity)
        rw [← Real.sqrt_eq_rpow]
        have hsqrtv :
            Real.sqrt (∫ x, |v x| ^ (2 : ℝ) ∂μ) ≤ 2 := by
          rw [Real.sqrt_le_iff]
          norm_num
          simpa [Real.rpow_two, sq_abs] using hv_sq
        nlinarith [Real.sqrt_nonneg
          (2 * (1 - densityAffinity μ f g))])

/-- For finitely many numbers in the unit interval, the amount by which their product falls
short of one is at most the total shortfall of the individual factors.  Applied to coordinate
affinities this is the union-bound step that turns a tensorized affinity into a sum of
coordinate defects. -/
lemma one_sub_prod_le_sum
    {ι : Type*} [Fintype ι] (a : ι → ℝ)
    (ha0 : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i ≤ 1) :
    1 - ∏ i, a i ≤ ∑ i, (1 - a i) := by
  classical
  have hbounds (s : Finset ι) :
      0 ≤ ∏ i ∈ s, a i ∧ ∏ i ∈ s, a i ≤ 1 := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
        rw [Finset.prod_insert hi]
        constructor <;> nlinarith [ha0 i, ha1 i, ih.1, ih.2]
  have hprod (s : Finset ι) :
      1 - ∏ i ∈ s, a i ≤ ∑ i ∈ s, (1 - a i) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
        rw [Finset.prod_insert hi, Finset.sum_insert hi]
        have hP0 : 0 ≤ ∏ j ∈ s, a j := (hbounds s).1
        have hP1 : ∏ j ∈ s, a j ≤ 1 := (hbounds s).2
        have hsum0 : 0 ≤ ∑ j ∈ s, (1 - a j) := by
          exact Finset.sum_nonneg fun j _ => sub_nonneg.mpr (ha1 j)
        nlinarith [ha0 i, ha1 i]
  simpa using hprod Finset.univ

/-- **Affinity tensorizes.**  On a finite product of σ-finite measure spaces, the affinity of
two densities that each factor coordinatewise is the product of the coordinate affinities.
This is what makes an `n`-fold product construction tractable: a single coordinate defect
computation is enough. -/
lemma densityAffinity_pi
    {ι : Type*} [Fintype ι] {E : ι → Type*} [∀ i, MeasurableSpace (E i)]
    (μ : ∀ i, Measure (E i)) [∀ i, SigmaFinite (μ i)]
    (f g : ∀ i, E i → ℝ)
    (hf0 : ∀ i u, 0 ≤ f i u) (hg0 : ∀ i u, 0 ≤ g i u) :
    densityAffinity (Measure.pi μ)
        (fun x => ∏ i, f i (x i))
        (fun x => ∏ i, g i (x i)) =
      ∏ i, ∫ u, Real.sqrt (f i u * g i u) ∂(μ i) := by
  classical
  unfold densityAffinity
  rw [show
      (fun x : ∀ i, E i =>
        Real.sqrt ((∏ i, f i (x i)) * ∏ i, g i (x i))) =
      (fun x => ∏ i, Real.sqrt (f i (x i) * g i (x i))) by
    funext x
    rw [← Finset.prod_mul_distrib]
    rw [Real.sqrt_prod]
    intro i hi
    exact mul_nonneg (hf0 i (x i)) (hg0 i (x i))]
  exact MeasureTheory.integral_fintype_prod_eq_prod
    (fun i u => Real.sqrt (f i u * g i u))

end Causalean.Stat
