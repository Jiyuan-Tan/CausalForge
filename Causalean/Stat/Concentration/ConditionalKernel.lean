/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Kernel.IndepFun
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Probability.Moments.SubGaussian

/-!
# Fiberwise facts for regular conditional distributions

This module collects measure-theoretic bridges used before applying ordinary
probability inequalities on almost every fiber of a regular conditional
distribution.  In particular, ambient almost-sure facts remain almost sure on
almost every conditional fiber, and a real random variable measurable with
respect to the conditioning σ-algebra is constant on almost every fiber.
-/

namespace Causalean.Stat.Concentration

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

/-- Kernel independence of a finite family of measurable real random variables
specializes to ordinary independence on almost every probability fiber.  The
countable rational half-line generator is what permits one common outer null
set for all measurable events. -/
theorem ProbabilityTheory.Kernel.iIndepFun.ae_iIndepFun_real
    {α Ω ι : Type*} [MeasurableSpace α] [MeasurableSpace Ω]
    {κ : Kernel α Ω} {ν : Measure α} [Finite ι]
    {X : ι → Ω → ℝ} (hX : ∀ i, Measurable (X i))
    (h : ProbabilityTheory.Kernel.iIndepFun X κ ν) :
    ∀ᵐ a ∂ν, ProbabilityTheory.iIndepFun X (κ a) := by
  classical
  let cuts : Set (Set ℝ) := ⋃ q : ℚ, {Set.Iic (q : ℝ)}
  have hident : ∀ᵐ a ∂ν, ∀ (S : Finset ι) (q : ι → ℚ),
      κ a (⋂ i ∈ S, X i ⁻¹' Set.Iic (q i : ℝ)) =
        ∏ i ∈ S, κ a (X i ⁻¹' Set.Iic (q i : ℝ)) := by
    rw [ae_all_iff]
    intro S
    rw [ae_all_iff]
    intro q
    exact (ProbabilityTheory.Kernel.iIndepFun_iff_measure_inter_preimage_eq_mul
      (fun _ : ι ↦ borel ℝ) X).mp h S (fun i _ ↦ measurableSet_Iic)
  filter_upwards [h.ae_isProbabilityMeasure, hident] with a hprob ha
  let π : ι → Set (Set Ω) := fun i ↦ (fun s : Set ℝ ↦ X i ⁻¹' s) '' cuts
  have hπ_pi : ∀ i, IsPiSystem (π i) := by
    intro i
    convert Real.isPiSystem_Iic_rat.comap (X i) using 1
  have hπ_gen : ∀ i, MeasurableSpace.comap (X i) (borel ℝ) =
      MeasurableSpace.generateFrom (π i) := by
    intro i
    rw [Real.borel_eq_generateFrom_Iic_rat, MeasurableSpace.comap_generateFrom]
  have hπ_ind : ProbabilityTheory.iIndepSets π (κ a) := by
    rw [ProbabilityTheory.iIndepSets_iff]
    intro S sets hsets
    have hrat (i : ι) (hi : i ∈ S) :
        ∃ q : ℚ, X i ⁻¹' Set.Iic (q : ℝ) = sets i := by
      rcases hsets i hi with ⟨t, ht, htset⟩
      simp only [cuts, Set.mem_iUnion, Set.mem_singleton_iff] at ht
      obtain ⟨q, hq⟩ := ht
      subst t
      exact ⟨q, htset⟩
    let q : ι → ℚ := fun i ↦ if hi : i ∈ S then
      Classical.choose (hrat i hi)
      else 0
    have hset (i : ι) (hi : i ∈ S) :
        sets i = X i ⁻¹' Set.Iic (q i : ℝ) := by
      simp only [q, dif_pos hi]
      exact (Classical.choose_spec (hrat i hi)).symm
    have hinter : (⋂ i ∈ S, sets i) =
        ⋂ i ∈ S, X i ⁻¹' Set.Iic (q i : ℝ) := by
      apply Set.iInter_congr
      intro i
      apply Set.iInter_congr
      intro hi
      exact hset i hi
    have hprod : (∏ i ∈ S, κ a (sets i)) =
        ∏ i ∈ S, κ a (X i ⁻¹' Set.Iic (q i : ℝ)) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [hset i hi]
    rw [hinter, hprod]
    exact ha S q
  haveI : IsProbabilityMeasure (κ a) := hprob
  have hspaces : ProbabilityTheory.iIndep
      (fun i ↦ MeasurableSpace.comap (X i) (borel ℝ)) (κ a) :=
    ProbabilityTheory.iIndepSets.iIndep
      (fun i ↦ Measurable.comap_le (hX i)) π hπ_pi hπ_gen hπ_ind
  exact hspaces

/-- A finite linear combination of independent, centered, unit-bounded real
random variables is sub-Gaussian with variance proxy equal to the sum of the
squared coefficients. -/
theorem hasSubgaussianMGF_linearCombination_of_iIndep
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (eps : ι → Ω → ℝ) (v : ι → ℝ)
    (hmeas : ∀ i, AEMeasurable (eps i) P)
    (hbound : ∀ i, ∀ᵐ ω ∂P, |eps i ω| ≤ 1)
    (hcenter : ∀ i, ∫ ω, eps i ω ∂P = 0)
    (hindep : ProbabilityTheory.iIndepFun eps P) :
    HasSubgaussianMGF (fun ω ↦ ∑ i, v i * eps i ω)
      ⟨∑ i, (v i) ^ 2, by positivity⟩ P := by
  let Y : ι → Ω → ℝ := fun i ω ↦ v i * eps i ω
  let c : ι → ℝ≥0 := fun i ↦ ⟨(v i) ^ 2, sq_nonneg (v i)⟩
  have hYindep : ProbabilityTheory.iIndepFun Y P :=
    hindep.comp (fun i x ↦ v i * x) (fun i ↦ measurable_const_mul (v i))
  have hYsub : ∀ i, HasSubgaussianMGF (Y i) (c i) P := by
    intro i
    have hYbound : ∀ᵐ ω ∂P, Y i ω ∈ Set.Icc (-|v i|) |v i| := by
      filter_upwards [hbound i] with ω hω
      have habs : |Y i ω| ≤ |v i| := by
        change |v i * eps i ω| ≤ |v i|
        rw [abs_mul]
        nlinarith [abs_nonneg (v i)]
      exact (abs_le.mp habs)
    have hYcenter : ∫ ω, Y i ω ∂P = 0 := by
      simp only [Y, integral_const_mul, hcenter, mul_zero]
    have hsub := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
      ((hmeas i).const_mul (v i)) hYbound hYcenter
    have hc : ((‖|v i| - -|v i|‖₊ / 2) ^ 2) = c i := by
      apply NNReal.eq
      simp only [c, NNReal.coe_pow, NNReal.coe_div,
        NNReal.coe_ofNat, NNReal.coe_mk, coe_nnnorm]
      rw [Real.norm_eq_abs, abs_of_nonneg (by
        linarith [abs_nonneg (v i)] : 0 ≤ |v i| - -|v i|)]
      ring_nf
      exact sq_abs (v i)
    rw [hc] at hsub
    simpa only [Y] using hsub
  have hsum := HasSubgaussianMGF.sum_of_iIndepFun hYindep
    (s := Finset.univ) (fun i _ ↦ hYsub i)
  have hc_sum : (∑ i, c i) =
      ⟨∑ i, (v i) ^ 2, by positivity⟩ := by
    apply NNReal.eq
    simp only [NNReal.coe_sum, c, NNReal.coe_mk]
  rw [hc_sum] at hsum
  simpa only [Y] using hsum

/-- An ambient almost-sure proposition holds on almost every fiber of the
regular conditional distribution. -/
theorem ae_ae_condExpKernel_of_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {p : Ω → Prop}
    (hp : ∀ᵐ ω ∂μ, p ω) :
    ∀ᵐ ω ∂μ.trim hm,
      ∀ᵐ ω' ∂ProbabilityTheory.condExpKernel (mΩ := mΩ) μ m ω, p ω' := by
  apply Measure.ae_ae_of_ae_comp
  rwa [ProbabilityTheory.condExpKernel_comp_trim (mΩ := mΩ) hm]

/-- A random variable measurable with respect to the conditioning
σ-algebra equals its observed value on almost every conditional fiber. -/
theorem ae_eq_const_condExpKernel_of_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {β : Type*} [MeasurableSpace β] [MeasurableEq β] {f : Ω → β}
    (hf : Measurable[m] f) :
    ∀ᵐ ω ∂μ.trim hm,
      ∀ᵐ ω' ∂ProbabilityTheory.condExpKernel (mΩ := mΩ) μ m ω,
        f ω' = f ω := by
  refine @Measure.ae_ae_of_ae_compProd Ω Ω m mΩ (μ.trim hm)
    (ProbabilityTheory.condExpKernel (mΩ := mΩ) μ m) _ _
    (fun pair ↦ f pair.2 = f pair.1) ?_
  rw [ProbabilityTheory.compProd_trim_condExpKernel (mΩ := mΩ) hm]
  rw [ae_map_iff]
  · exact Filter.Eventually.of_forall fun ω ↦ rfl
  · have hfirst : @Measurable Ω Ω mΩ m id := measurable_id'' hm
    have hsecond : @Measurable Ω Ω mΩ mΩ id := measurable_id
    have hdiag : @Measurable Ω (Ω × Ω) mΩ (m.prod mΩ)
        (fun ω ↦ (id ω, id ω)) := by
      refine Measurable.of_comap_le ?_
      rw [MeasurableSpace.prod, MeasurableSpace.comap_sup,
        MeasurableSpace.comap_comp]
      apply sup_le
      · change m.comap (Prod.fst ∘ fun ω ↦ (ω, ω)) ≤ mΩ
        rw [show (Prod.fst ∘ fun ω : Ω ↦ (ω, ω)) = id by rfl,
          MeasurableSpace.comap_id]
        exact hm
      · rw [MeasurableSpace.comap_comp]
        rw [show (Prod.snd ∘ fun ω : Ω ↦ (id ω, id ω)) = id by rfl,
          MeasurableSpace.comap_id]
    exact @Measurable.aemeasurable Ω (Ω × Ω) mΩ (m.prod mΩ)
      (fun ω ↦ (id ω, id ω)) μ hdiag
  · have hfst : @Measurable (Ω × Ω) Ω (m.prod mΩ) m Prod.fst := measurable_fst
    have hsnd : @Measurable (Ω × Ω) Ω (m.prod mΩ) mΩ Prod.snd := measurable_snd
    have hf' : @Measurable Ω β mΩ _ f := hf.mono hm le_rfl
    exact measurableSet_eq_fun (hf'.comp hsnd) (hf.comp hfst)

end Causalean.Stat.Concentration
