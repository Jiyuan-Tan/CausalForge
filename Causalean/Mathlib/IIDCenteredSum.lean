/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Conditional second-moment bound for centered i.i.d. sums

For a finite family `(W_i)_{i ∈ s}` of `Ω → X` random variables that is

* jointly i.i.d. with marginal law `P` (`hW_iid_pi`), and
* independent of a sub-σ-algebra `m_A ≤ m_Ω` (`hW_indep_A`),

and a parametric integrand `g : Ω → X → ℝ` that is jointly measurable for
`m_A.prod σ_X` and lies in `L²(P)` for every `ω`, the standard conditional
variance argument yields

    ∫_Ω ((1/√|s|) Σ_{i ∈ s} (g ω (W_i ω) − ∫ g ω dP))² dμ
      ≤ ∫_Ω ‖g ω‖²_{L²(P)} dμ.

This file isolates that step from the cross-fitting empirical-process bound
in `Causalean/Stat/FoldBEmpiricalProcess.lean`.  It is causal-agnostic and a
candidate for upstream contribution to Mathlib.

## Main result

* `iid_centered_sum_sq_lintegral_le` — the bound above, stated in `lintegral`
  form via `ENNReal.ofReal`.
-/

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Causalean.Mathlib.ELpNormMeasurable

/-! # Centered Sums of Independent Identically Distributed Samples

This file proves a conditional second-moment bound for normalized centered sums
of a finite independent identically distributed sample. The sample coordinates
`W i : Ω → X` are jointly distributed as a product law `P^s` and jointly
independent of a sub-σ-algebra `m_A`; the integrand `g : Ω → X → ℝ` is
`m_A`-measurable in its parameter and square-integrable in the sample
coordinate.

The headline theorem is `iid_centered_sum_sq_lintegral_le`: for nonempty `s`,

`∫⁻ ω, ofReal (((sqrt |s|)⁻¹ * ∑ i ∈ s, (g ω (W i ω) - ∫ x, g ω x ∂P)) ^ 2) ∂μ`
is bounded by
`∫⁻ ω, ofReal ((eLpNorm (g ω) 2 P).toReal ^ 2) ∂μ`.

The supporting lemmas isolate the deterministic normalization step, the
product-space variance estimate using `variance_sum_pi`, and the measure-law
bridge `indep_trim_prod_map_eq` that turns independence of `m_A` from the sample
tuple into a joined product law. The result is reusable outside cross-fitting:
it is a general finite-product probability estimate stated in `lintegral` form
with `ENNReal.ofReal`. -/

namespace Causalean.Mathlib

open MeasureTheory ProbabilityTheory Filter Topology

/-- Pull the `1 / √|s|` normalization out of a nonnegative `lintegral` bound.

This is the deterministic algebraic part of
`iid_centered_sum_sq_lintegral_le`: if the unscaled centered sum has second
moment bounded by `|s|` times a nonnegative benchmark, then the normalized sum
is bounded by that benchmark. -/
private lemma lintegral_ofReal_inv_sqrt_smul_sum_sq_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {ι : Type*} (s : Finset ι) (hs_pos : 0 < s.card)
    (Y : ι → Ω → ℝ) (B : Ω → ℝ)
    (h_sum :
      ∫⁻ ω, ENNReal.ofReal ((∑ i ∈ s, Y i ω) ^ 2) ∂μ ≤
        (s.card : ENNReal) * ∫⁻ ω, ENNReal.ofReal (B ω) ∂μ) :
    ∫⁻ ω, ENNReal.ofReal
        (((Real.sqrt (s.card : ℝ))⁻¹ * ∑ i ∈ s, Y i ω) ^ 2) ∂μ
      ≤ ∫⁻ ω, ENNReal.ofReal (B ω) ∂μ := by
  let nE : ENNReal := s.card
  have hnE_ne_zero : nE ≠ 0 := by
    simp [nE, Nat.ne_of_gt hs_pos]
  have hnE_ne_top : nE ≠ ⊤ := by
    simp [nE]
  have hnE_inv_ne_top : nE⁻¹ ≠ ⊤ :=
    ENNReal.Finiteness.inv_ne_top hnE_ne_zero
  have hpoint : ∀ ω,
      ENNReal.ofReal
          (((Real.sqrt (s.card : ℝ))⁻¹ * ∑ i ∈ s, Y i ω) ^ 2)
        ≤ nE⁻¹ * ENNReal.ofReal ((∑ i ∈ s, Y i ω) ^ 2) := by
    intro ω
    let z : ℝ := ∑ i ∈ s, Y i ω
    have hnR_pos : 0 < (s.card : ℝ) := Nat.cast_pos.mpr hs_pos
    have hreal :
        ((Real.sqrt (s.card : ℝ))⁻¹ * z) ^ 2 =
          ((s.card : ℝ)⁻¹) * z ^ 2 := by
      have hc : ((Real.sqrt (s.card : ℝ))⁻¹) ^ 2 =
          ((s.card : ℝ)⁻¹) := by
        rw [inv_pow]
        rw [Real.sq_sqrt (le_of_lt hnR_pos)]
      rw [mul_pow, hc]
    rw [show ((Real.sqrt (s.card : ℝ))⁻¹ * ∑ i ∈ s, Y i ω) ^ 2 =
        ((s.card : ℝ)⁻¹) * (∑ i ∈ s, Y i ω) ^ 2 by
          simpa [z] using hreal]
    rw [ENNReal.ofReal_mul (inv_nonneg.mpr (le_of_lt hnR_pos))]
    rw [ENNReal.ofReal_inv_of_pos hnR_pos]
    norm_num [nE]
  calc
    ∫⁻ ω, ENNReal.ofReal
        (((Real.sqrt (s.card : ℝ))⁻¹ * ∑ i ∈ s, Y i ω) ^ 2) ∂μ
        ≤ ∫⁻ ω, nE⁻¹ *
            ENNReal.ofReal ((∑ i ∈ s, Y i ω) ^ 2) ∂μ :=
      lintegral_mono hpoint
    _ = nE⁻¹ * ∫⁻ ω, ENNReal.ofReal ((∑ i ∈ s, Y i ω) ^ 2) ∂μ := by
      rw [lintegral_const_mul' _ _ hnE_inv_ne_top]
    _ ≤ nE⁻¹ * (nE *
          ∫⁻ ω, ENNReal.ofReal (B ω) ∂μ) := by
      exact mul_le_mul_right (by simpa [nE] using h_sum) nE⁻¹
    _ = ∫⁻ ω, ENNReal.ofReal (B ω) ∂μ := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hnE_ne_zero hnE_ne_top, one_mul]

/-- For an `L²` real function, the square of its `eLpNorm` is the integral of
the square, in `ENNReal.ofReal` form. -/
private lemma eLpNorm_two_sq_toReal_eq_integral_sq
    {X : Type*} [MeasurableSpace X] {P : Measure X}
    [IsProbabilityMeasure P]
    {f : X → ℝ} (hf : MemLp f 2 P) :
    ENNReal.ofReal ((eLpNorm f 2 P).toReal ^ 2) =
      ENNReal.ofReal (∫ x, (f ^ 2) x ∂P) := by
  have h_eLp := hf.eLpNorm_eq_integral_rpow_norm
    (by norm_num : (2 : ENNReal) ≠ 0)
    (by norm_num : (2 : ENNReal) ≠ ⊤)
  rw [h_eLp]
  simp only [ENNReal.toReal_ofNat]
  have hroot_nonneg : 0 ≤ (∫ a, ‖f a‖ ^ (2 : ℝ) ∂P) ^ (2 : ℝ)⁻¹ := by
    exact Real.rpow_nonneg (integral_nonneg fun x => by positivity) _
  rw [ENNReal.toReal_ofReal hroot_nonneg]
  have hsq : ((∫ a, ‖f a‖ ^ (2 : ℝ) ∂P) ^ (2 : ℝ)⁻¹) ^ 2 =
      ∫ x, f x ^ 2 ∂P := by
    have hint_eq : (∫ a, ‖f a‖ ^ (2 : ℝ) ∂P) = ∫ x, f x ^ 2 ∂P := by
      congr with x
      norm_num [sq_abs]
    rw [hint_eq]
    rw [show ((∫ x, f x ^ 2 ∂P) ^ (2 : ℝ)⁻¹) ^ 2 =
        ((∫ x, f x ^ 2 ∂P) ^ (1 / 2 : ℝ)) ^ 2 by norm_num]
    rw [show ((∫ x, f x ^ 2 ∂P) ^ (1 / 2 : ℝ)) ^ 2 =
        ((∫ x, f x ^ 2 ∂P) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) by
      norm_num [Real.rpow_two]]
    rw [← Real.rpow_mul]
    · norm_num
      exact Real.rpow_one (∫ x, f x ^ 2 ∂P)
    · exact integral_nonneg fun x => sq_nonneg _
  rw [hsq]
  simp [Pi.pow_apply]

/-- The centered second moment of an `L²` real function is bounded by its
uncentered `L²` norm.  This is the diagonal term used below. -/
private lemma centered_sq_lintegral_le_eLpNorm_two_sq
    {X : Type*} [MeasurableSpace X] {P : Measure X}
    [IsProbabilityMeasure P]
    {f : X → ℝ} (hf : MemLp f 2 P) :
    ∫⁻ x, ENNReal.ofReal ((f x - ∫ y, f y ∂P) ^ 2) ∂P ≤
      ENNReal.ofReal ((eLpNorm f 2 P).toReal ^ 2) := by
  have hcenter_int : Integrable (fun x => (f x - ∫ y, f y ∂P) ^ 2) P := by
    have hcenter : MemLp (fun x => f x - ∫ y, f y ∂P) 2 P := by
      simpa [sub_eq_add_neg] using hf.sub (memLp_const (∫ y, f y ∂P))
    exact hcenter.integrable_sq
  have hcenter_nn : 0 ≤ᵐ[P] fun x => (f x - ∫ y, f y ∂P) ^ 2 :=
    Filter.Eventually.of_forall fun x => sq_nonneg _
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hcenter_int hcenter_nn]
  have hvar_eq : ∫ x, (f x - ∫ y, f y ∂P) ^ 2 ∂P = variance f P := by
    rw [(variance_eq_integral hf.aemeasurable).symm]
  rw [hvar_eq]
  have hvar_le : variance f P ≤ ∫ x, (f ^ 2) x ∂P :=
    variance_le_expectation_sq hf.aestronglyMeasurable
  rw [eLpNorm_two_sq_toReal_eq_integral_sq hf]
  exact ENNReal.ofReal_le_ofReal hvar_le

/-- Product-measure version of the centered finite-sum estimate for a fixed
integrand.  This is where finite-product independence kills cross terms, via
Mathlib's `variance_sum_pi`. -/
private lemma pi_centered_sum_sq_lintegral_le
    {X : Type*} [MeasurableSpace X] {P : Measure X}
    [IsProbabilityMeasure P]
    {ι : Type*} (s : Finset ι)
    {f : X → ℝ} (hf : MemLp f 2 P) :
    ∫⁻ v : ((i : s) → X), ENNReal.ofReal
        ((∑ i : s, (f (v i) - ∫ x, f x ∂P)) ^ 2)
        ∂Measure.pi (fun _ : s => P)
      ≤ (s.card : ENNReal) * ENNReal.ofReal ((eLpNorm f 2 P).toReal ^ 2) := by
  classical
  let ν : Measure ((i : s) → X) := Measure.pi (fun _ : s => P)
  let c : ℝ := ∫ x, f x ∂P
  let Y : s → ((i : s) → X) → ℝ := fun i v => f (v i) - c
  have hcenterP : MemLp (fun x => f x - c) 2 P := by
    simpa [c, sub_eq_add_neg] using hf.sub (memLp_const (∫ x, f x ∂P))
  have hYmem : ∀ i : s, MemLp (Y i) 2 ν := by
    intro i
    have hcomp := hcenterP.comp_measurePreserving
      (measurePreserving_eval (fun _ : s => P) i)
    simpa [Y, c, Function.comp_def, ν] using hcomp
  have hsum_mem : MemLp (fun v => ∑ i : s, Y i v) 2 ν := by
    simpa using (memLp_finset_sum Finset.univ (fun i _ => hYmem i))
  have hsum_int : Integrable (fun v => (∑ i : s, Y i v) ^ 2) ν :=
    hsum_mem.integrable_sq
  have hsum_nn : 0 ≤ᵐ[ν] fun v => (∑ i : s, Y i v) ^ 2 :=
    Filter.Eventually.of_forall fun v => sq_nonneg _
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hsum_int hsum_nn]
  have hYint_zero : ∀ i : s, ∫ v, Y i v ∂ν = 0 := by
    intro i
    have hmp := measurePreserving_eval (fun _ : s => P) i
    have hcenter_map : AEStronglyMeasurable (fun x => f x - c)
        (Measure.map (Function.eval i) ν) := by
      rw [hmp.map_eq]
      exact hcenterP.aestronglyMeasurable
    have hmap0 := integral_map hmp.aemeasurable hcenter_map
    rw [hmp.map_eq] at hmap0
    have hmap : ∫ x, f x - c ∂P = ∫ v, f (v i) - c ∂ν := hmap0
    have hcenter_int_zero : ∫ x, f x - c ∂P = 0 := by
      have hf_int : Integrable f P :=
        hf.integrable (by norm_num : (1 : ENNReal) ≤ 2)
      rw [integral_sub hf_int (integrable_const c)]
      simp [c]
    simpa [Y, c, ν] using hmap ▸ hcenter_int_zero
  have hsum_int_zero : ∫ v, (∑ i : s, Y i v) ∂ν = 0 := by
    rw [integral_finset_sum Finset.univ]
    · simp [hYint_zero]
    · intro i _hi
      exact (hYmem i).integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hvar_eq_int :
      variance (fun v => ∑ i : s, Y i v) ν =
        ∫ v, (∑ i : s, Y i v) ^ 2 ∂ν := by
    rw [variance_of_integral_eq_zero hsum_mem.aemeasurable hsum_int_zero]
  have hvar_sum :
      variance (fun v => ∑ i : s, Y i v) ν =
        ∑ i : s, variance (fun x => f x - c) P := by
    rw [show (fun v => ∑ i : s, Y i v) = (∑ i : s, Y i) by
      funext v
      simp]
    have h := variance_sum_pi
      (μ := fun _ : s => P) (X := fun _ : s => fun x => f x - c)
      (fun _ => hcenterP)
    simpa [Y, ν] using h
  rw [← hvar_eq_int, hvar_sum]
  calc
    ENNReal.ofReal (∑ i : s, variance (fun x => f x - c) P)
        ≤ ENNReal.ofReal (∑ i : s, ∫ x, (f ^ 2) x ∂P) := by
          exact ENNReal.ofReal_le_ofReal (Finset.sum_le_sum fun _i _hi => by
            rw [variance_sub_const hf.aestronglyMeasurable c]
            exact variance_le_expectation_sq hf.aestronglyMeasurable)
    _ = (s.card : ENNReal) * ENNReal.ofReal (∫ x, (f ^ 2) x ∂P) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          norm_num
    _ = (s.card : ENNReal) *
          ENNReal.ofReal ((eLpNorm f 2 P).toReal ^ 2) := by
          rw [eLpNorm_two_sq_toReal_eq_integral_sq hf]

/-- Convert independence of a sub-σ-algebra and a random element into the
product law of the joined map, with the first marginal trimmed to the
sub-σ-algebra. -/
lemma indep_trim_prod_map_eq
    {Ω β : Type*} [mΩ : MeasurableSpace Ω] [mβ : MeasurableSpace β]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (m_A : MeasurableSpace Ω) (hm_A_le : m_A ≤ mΩ)
    {Z : Ω → β} (hZ : @Measurable Ω β mΩ mβ Z)
    (hInd : @Indep Ω m_A (MeasurableSpace.comap Z mβ) mΩ μ) :
    @Measure.map Ω (Ω × β) mΩ (@Prod.instMeasurableSpace Ω β m_A mβ)
      (fun ω => (ω, Z ω)) μ =
    @Measure.prod Ω β m_A mβ
      (μ.trim hm_A_le) (@Measure.map Ω β mΩ mβ Z μ) := by
  have hIF : @IndepFun Ω Ω β mΩ m_A mβ id Z μ := by
    rw [IndepFun_iff_Indep]
    simpa using hInd
  have hid_map : @Measure.map Ω Ω mΩ m_A id μ = μ.trim hm_A_le := by
    apply Measure.ext
    intro t ht
    rw [Measure.map_apply (measurable_id'' hm_A_le) ht]
    exact (trim_measurableSet_eq hm_A_le ht).symm
  have hprod := (indepFun_iff_map_prod_eq_prod_map_map
    ((measurable_id'' hm_A_le).aemeasurable) hZ.aemeasurable).mp hIF
  simpa [hid_map, Function.comp_def] using hprod

/-- Fubini/product-space form of the unscaled conditional second-moment
estimate.

The joined-law hypothesis is the output of `indep_trim_prod_map_eq` plus the
i.i.d. product law.  What remains is the finite-product variance calculation:
integrate first over the product coordinates, use `variance_sum_pi` to kill
cross terms, and apply `centered_sq_lintegral_le_eLpNorm_two_sq` to each
diagonal term. -/
private lemma iid_centered_sum_sq_lintegral_unscaled_le_of_joined_law
    {Ω X : Type*} [mΩ : MeasurableSpace Ω] [mX : MeasurableSpace X]
    {μ : Measure Ω} {P : Measure X}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    {ι : Type*} (s : Finset ι)
    (W : ι → Ω → X)
    (hW_meas : ∀ i ∈ s, Measurable (W i))
    (m_A : MeasurableSpace Ω) (hm_A_le : m_A ≤ mΩ)
    (hW_join :
      @Measure.map Ω (Ω × ((i : s) → X)) mΩ
        (@Prod.instMeasurableSpace Ω ((i : s) → X) m_A inferInstance)
        (fun ω => (ω, fun i : s => W i.val ω)) μ =
      @Measure.prod Ω ((i : s) → X) m_A inferInstance
        (μ.trim hm_A_le) (Measure.pi (fun _ : s => P)))
    (g : Ω → X → ℝ)
    (hg_uncurry_meas :
      Measurable[m_A.prod mX]
        (Function.uncurry g))
    (hg_memLp : ∀ ω, MemLp (g ω) 2 P) :
    ∫⁻ ω, ENNReal.ofReal
        ((∑ i ∈ s, (g ω (W i ω) - ∫ x, g ω x ∂P)) ^ 2) ∂μ
      ≤ (s.card : ENNReal) *
          ∫⁻ ω, ENNReal.ofReal ((eLpNorm (g ω) 2 P).toReal ^ 2) ∂μ := by
  classical
  let νA : Measure Ω := μ.trim hm_A_le
  let νX : Measure ((i : s) → X) := Measure.pi (fun _ : s => P)
  let J : Ω → Ω × ((i : s) → X) :=
    fun ω => (ω, fun i : s => W i.val ω)
  let F : Ω × ((i : s) → X) → ENNReal :=
    fun p => ENNReal.ofReal
      ((∑ i : s, (g p.1 (p.2 i) - ∫ x, g p.1 x ∂P)) ^ 2)
  let B : Ω → ENNReal :=
    fun ω => ENNReal.ofReal ((eLpNorm (g ω) 2 P).toReal ^ 2)
  have hJ_meas :
      @Measurable Ω (Ω × ((i : s) → X)) mΩ
        (@Prod.instMeasurableSpace Ω ((i : s) → X) m_A inferInstance) J := by
    apply Measurable.prod
    · exact measurable_id'' hm_A_le
    · exact @measurable_pi_lambda Ω s (fun _ : s => X) mΩ (fun _ : s => mX)
        (fun ω (i : s) => W i.val ω) (fun i => hW_meas i.val i.property)
  have hc_meas : @Measurable Ω ℝ m_A inferInstance
      (fun ω => ∫ x, g ω x ∂P) :=
    hg_uncurry_meas.stronglyMeasurable.integral_prod_right.measurable
  have hF_meas :
      @Measurable (Ω × ((i : s) → X)) ENNReal
        (@Prod.instMeasurableSpace Ω ((i : s) → X) m_A inferInstance)
        inferInstance F := by
    have hterm : ∀ i : s, Measurable fun p : Ω × ((i : s) → X) =>
        g p.1 (p.2 i) - ∫ x, g p.1 x ∂P := by
      intro i
      have hpair : Measurable fun p : Ω × ((i : s) → X) => (p.1, p.2 i) := by
        apply Measurable.prod
        · exact measurable_fst
        · exact (measurable_pi_apply i).comp measurable_snd
      exact (hg_uncurry_meas.comp hpair).sub (hc_meas.comp measurable_fst)
    exact ENNReal.measurable_ofReal.comp
      ((Finset.measurable_sum _ fun i _ => hterm i).pow_const 2)
  have hB_meas : @Measurable Ω ENNReal m_A inferInstance B := by
    have hnorm : @Measurable Ω ℝ m_A inferInstance
        (fun ω => (eLpNorm (g ω) 2 P).toReal) :=
      measurable_eLpNorm_two_toReal_of_uncurry (Ω := Ω) (P := P)
        (g := g) hg_uncurry_meas
    exact ENNReal.measurable_ofReal.comp (hnorm.pow_const 2)
  have hleft_eq : ∫⁻ ω, ENNReal.ofReal
        ((∑ i ∈ s, (g ω (W i ω) - ∫ x, g ω x ∂P)) ^ 2) ∂μ =
      ∫⁻ p, F p ∂
        @Measure.map Ω (Ω × ((i : s) → X)) mΩ
          (@Prod.instMeasurableSpace Ω ((i : s) → X) m_A inferInstance) J μ := by
    rw [@lintegral_map Ω (Ω × ((i : s) → X)) mΩ
      (@Prod.instMeasurableSpace Ω ((i : s) → X) m_A inferInstance)
      μ F J hF_meas hJ_meas]
    apply lintegral_congr_ae
    refine Filter.Eventually.of_forall fun ω => ?_
    simp only [F, J]
    congr 2
    exact (show (∑ i ∈ s, (g ω (W i ω) - ∫ x, g ω x ∂P)) =
        ∑ i : s, (g ω (W i.val ω) - ∫ x, g ω x ∂P) by
      symm
      simpa using
        (Finset.sum_attach s
          (fun i : ι => g ω (W i ω) - ∫ x, g ω x ∂P)))
  have hprod_eq :
      ∫⁻ p, F p ∂
        @Measure.map Ω (Ω × ((i : s) → X)) mΩ
          (@Prod.instMeasurableSpace Ω ((i : s) → X) m_A inferInstance) J μ =
        ∫⁻ p, F p ∂νA.prod νX := by
    rw [show
      @Measure.map Ω (Ω × ((i : s) → X)) mΩ
          (@Prod.instMeasurableSpace Ω ((i : s) → X) m_A inferInstance) J μ =
        νA.prod νX by
      simpa [νA, νX, J] using hW_join]
  have hprod_tonelli :
      ∫⁻ p, F p ∂νA.prod νX = ∫⁻ ω, ∫⁻ v, F (ω, v) ∂νX ∂νA := by
    exact lintegral_prod F hF_meas.aemeasurable
  have hinner_le : ∀ ω, ∫⁻ v, F (ω, v) ∂νX ≤ (s.card : ENNReal) * B ω := by
    intro ω
    simpa [F, B, νX] using
      pi_centered_sum_sq_lintegral_le (s := s) (f := g ω) (hg_memLp ω)
  calc
    ∫⁻ ω, ENNReal.ofReal
        ((∑ i ∈ s, (g ω (W i ω) - ∫ x, g ω x ∂P)) ^ 2) ∂μ
        = ∫⁻ p, F p ∂
            @Measure.map Ω (Ω × ((i : s) → X)) mΩ
              (@Prod.instMeasurableSpace Ω ((i : s) → X) m_A inferInstance) J μ := hleft_eq
    _ = ∫⁻ p, F p ∂νA.prod νX := hprod_eq
    _ = ∫⁻ ω, ∫⁻ v, F (ω, v) ∂νX ∂νA := hprod_tonelli
    _ ≤ ∫⁻ ω, (s.card : ENNReal) * B ω ∂νA :=
      lintegral_mono hinner_le
    _ = (s.card : ENNReal) * ∫⁻ ω, B ω ∂νA := by
      rw [lintegral_const_mul' _ _ (by simp)]
    _ = (s.card : ENNReal) *
          ∫⁻ ω, ENNReal.ofReal ((eLpNorm (g ω) 2 P).toReal ^ 2) ∂μ := by
      rw [lintegral_trim hm_A_le hB_meas]

/-- Unscaled conditional second-moment estimate for a centered i.i.d. sum.

This is the remaining probability-theoretic core: expand the square, push the
diagonal and off-diagonal terms through the conditional product law generated
by `hW_indep_A` and `hW_iid_pi`, kill the cross terms by centering, and bound
the diagonal variance by the L² norm. -/
private lemma iid_centered_sum_sq_lintegral_unscaled_le
    {Ω X : Type*} [mΩ : MeasurableSpace Ω] [mX : MeasurableSpace X]
    {μ : Measure Ω} {P : Measure X}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    {ι : Type*} (s : Finset ι)
    (W : ι → Ω → X)
    (hW_meas : ∀ i ∈ s, Measurable (W i))
    (m_A : MeasurableSpace Ω) (hm_A_le : m_A ≤ mΩ)
    (hW_indep_A :
      Indep m_A
        (MeasurableSpace.comap
          (fun ω (i : s) => W i.val ω) (inferInstance : MeasurableSpace _)) μ)
    (hW_iid_pi :
      (@Measure.map Ω _ mΩ _ (fun ω (i : s) => W i.val ω) μ) =
        Measure.pi (fun _ : s => P))
    (g : Ω → X → ℝ)
    (hg_uncurry_meas :
      Measurable[m_A.prod mX]
        (Function.uncurry g))
    (hg_memLp : ∀ ω, MemLp (g ω) 2 P) :
    ∫⁻ ω, ENNReal.ofReal
        ((∑ i ∈ s, (g ω (W i ω) - ∫ x, g ω x ∂P)) ^ 2) ∂μ
      ≤ (s.card : ENNReal) *
          ∫⁻ ω, ENNReal.ofReal ((eLpNorm (g ω) 2 P).toReal ^ 2) ∂μ := by
  have hZ_meas :
      @Measurable Ω ((i : s) → X) mΩ inferInstance
        (fun ω (i : s) => W i.val ω) := by
    exact @measurable_pi_lambda Ω s (fun _ : s => X) mΩ (fun _ : s => mX)
      (fun ω (i : s) => W i.val ω) (fun i => hW_meas i.val i.property)
  have hW_join :
      @Measure.map Ω (Ω × ((i : s) → X)) mΩ
        (@Prod.instMeasurableSpace Ω ((i : s) → X) m_A inferInstance)
        (fun ω => (ω, fun i : s => W i.val ω)) μ =
      @Measure.prod Ω ((i : s) → X) m_A inferInstance
        (μ.trim hm_A_le) (Measure.pi (fun _ : s => P)) := by
    have hW_join_raw :
        @Measure.map Ω (Ω × ((i : s) → X)) mΩ
          (@Prod.instMeasurableSpace Ω ((i : s) → X) m_A inferInstance)
          (fun ω => (ω, fun i : s => W i.val ω)) μ =
        @Measure.prod Ω ((i : s) → X) m_A inferInstance
          (μ.trim hm_A_le)
          (@Measure.map Ω ((i : s) → X) mΩ inferInstance
            (fun ω (i : s) => W i.val ω) μ) :=
      indep_trim_prod_map_eq
        (Ω := Ω) (β := ((i : s) → X)) (mΩ := mΩ) (μ := μ)
        m_A hm_A_le hZ_meas hW_indep_A
    simpa [hW_iid_pi] using hW_join_raw
  exact iid_centered_sum_sq_lintegral_unscaled_le_of_joined_law
    (Ω := Ω) (X := X) (mΩ := mΩ) (mX := mX) (μ := μ) (P := P)
    (s := s) (W := W) hW_meas m_A hm_A_le hW_join
    g hg_uncurry_meas hg_memLp

/-- **Conditional second-moment bound for a centered i.i.d. sum.**

Setup:
* `m_A` a sub-σ-algebra of the ambient `MeasurableSpace Ω`.
* `(W i)_{i ∈ s}` a finite family of `Ω → X` random variables that are
  - jointly distributed as the i.i.d. product `P^|s|` (`hW_iid_pi`), and
  - jointly independent of `m_A` (`hW_indep_A`).
* `g : Ω → X → ℝ` jointly measurable for `m_A ⊗ σ_X` and `g ω ∈ L²(P)` for
  every `ω`.

Then the centered scaled fold sum

    G(ω) := (1/√|s|) Σ_{i ∈ s} (g ω (W i ω) − ∫ g ω dP)

satisfies the second-moment bound

    ∫_Ω G(ω)² dμ ≤ ∫_Ω ‖g ω‖²_{L²(P)} dμ,

stated in `lintegral` form via `ENNReal.ofReal`.

**Proof outline.**

Let `Y_i(ω) := g ω (W i ω) − ∫ g ω dP` and `c(ω) := ∫ g ω dP` (an
`m_A`-measurable scalar).  Expand the square:

    (Σ Y_i)² = Σ_i Y_i² + Σ_{i ≠ j} Y_i · Y_j.

*Cross terms vanish.*  For `i ≠ j ∈ s`, the trio `(m_A, σ(W_i), σ(W_j))` is
3-wise independent under `μ` (extracted from `hW_indep_A` together with the
i.i.d. product law `hW_iid_pi`).  Pushing the integral through to the
product space `(Ω/m_A) × X × X` and using Fubini, the inner integral is
`(∫_X (g ω x − c ω) dP(x))² = 0` because each centred factor integrates to 0
against `P`.

*Diagonal terms.*  For each `i ∈ s`,
`∫_Ω Y_i(ω)² dμ = ∫_Ω (∫_X (g ω x − c ω)² dP(x)) dμ
                ≤ ∫_Ω (∫_X g ω x² dP(x)) dμ
                = ∫_Ω ‖g ω‖²_{L²(P)} dμ`.
The first equality uses the same product-space Fubini argument; the
inequality is `Var_P(g ω) ≤ E_P[(g ω)²]` (a one-line bound).

*Combine.*  Summing the `|s|` diagonal terms and using the cross-term
vanishing,
`Σ_i Σ_j ∫ Y_i Y_j ≤ |s| · ∫ ‖g‖²_{L²(P)}`.
Dividing by `|s|` (the `(1/√|s|)²` prefactor) gives the claim. -/
theorem iid_centered_sum_sq_lintegral_le
    {Ω X : Type*} [mΩ : MeasurableSpace Ω] [mX : MeasurableSpace X]
    {μ : Measure Ω} {P : Measure X}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    {ι : Type*} (s : Finset ι) (hs_pos : 0 < s.card)
    (W : ι → Ω → X)
    (hW_meas : ∀ i ∈ s, Measurable (W i))
    (m_A : MeasurableSpace Ω) (hm_A_le : m_A ≤ mΩ)
    (hW_indep_A :
      Indep m_A
        (MeasurableSpace.comap
          (fun ω (i : s) => W i.val ω) (inferInstance : MeasurableSpace _)) μ)
    (hW_iid_pi :
      (@Measure.map Ω _ mΩ _ (fun ω (i : s) => W i.val ω) μ) =
        Measure.pi (fun _ : s => P))
    (g : Ω → X → ℝ)
    (hg_uncurry_meas :
      Measurable[m_A.prod mX]
        (Function.uncurry g))
    (hg_memLp : ∀ ω, MemLp (g ω) 2 P) :
    ∫⁻ ω, ENNReal.ofReal
        (((Real.sqrt (s.card : ℝ))⁻¹ *
          ∑ i ∈ s, (g ω (W i ω) - ∫ x, g ω x ∂P)) ^ 2) ∂μ
      ≤ ∫⁻ ω, ENNReal.ofReal ((eLpNorm (g ω) 2 P).toReal ^ 2) ∂μ := by
  let Y : ι → Ω → ℝ :=
    fun i ω => g ω (W i ω) - ∫ x, g ω x ∂P
  let B : Ω → ℝ :=
    fun ω => (eLpNorm (g ω) 2 P).toReal ^ 2
  change
    ∫⁻ ω, ENNReal.ofReal
        (((Real.sqrt (s.card : ℝ))⁻¹ * ∑ i ∈ s, Y i ω) ^ 2) ∂μ
      ≤ ∫⁻ ω, ENNReal.ofReal (B ω) ∂μ
  exact @lintegral_ofReal_inv_sqrt_smul_sum_sq_le Ω mΩ μ ι
    s hs_pos Y B
    (by
      simpa [Y, B] using
        iid_centered_sum_sq_lintegral_unscaled_le
          (Ω := Ω) (X := X) (mΩ := mΩ) (mX := mX) (μ := μ) (P := P)
          (s := s) (W := W) hW_meas m_A hm_A_le hW_indep_A hW_iid_pi
          g hg_uncurry_meas hg_memLp)

end Causalean.Mathlib
