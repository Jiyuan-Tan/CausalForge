/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Witness-kernel form of a conditional distribution under conditional independence

This is the measure-theoretic core of a backdoor / Rule-2 argument, stated purely in terms of
Mathlib's `condDistrib`.  No SCM machinery is involved.

If `Y = h X Z C` pointwise and `C` is conditionally independent of `X` given `Z` (expressed as the
a.e. equality of conditional kernels `condDistrib C (X,Z) = condDistrib C Z`), then the conditional
distribution of `Y` given `(X,Z)` is, a.e., the pushforward of `condDistrib C Z` by `h x z`.
-/

import Mathlib.Probability.Kernel.CondDistrib

/-!
# Witness-kernel form of conditional distributions

This file states the measure-theoretic core of a backdoor or Rule-2 argument
purely in terms of Mathlib's conditional distributions, with no SCM machinery.
When an outcome is a measurable function of the conditioning variable and a
residual coordinate, its conditional law is the pushforward of the residual
coordinate's conditional law by that function.

The main construction is `witnessKernel`, a Markov kernel sending a treatment-
covariate pair to the residual conditional law pushed through a structural
response. The theorem `condDistrib_map_of_condDistrib_fst_eq` proves this
witness-kernel form under a conditional-independence hypothesis, while
`condDistrib_map_of_funext` gives the no-treatment specialization where the
conditioning variable already contains the full non-residual information.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω 𝒳 𝒵 𝒞 𝒴 : Type*}
  [MeasurableSpace Ω] [MeasurableSpace 𝒳] [MeasurableSpace 𝒵]
  [MeasurableSpace 𝒞] [StandardBorelSpace 𝒞] [Nonempty 𝒞]
  [MeasurableSpace 𝒴] [StandardBorelSpace 𝒴] [Nonempty 𝒴]

/-- For each treatment-covariate pair, this kernel gives the conditional law of
the outcome obtained by drawing the residual coordinate from its conditional law
given the covariates and then applying the structural response function. -/
noncomputable def witnessKernel (μ : Measure Ω) [IsFiniteMeasure μ]
    {Z : Ω → 𝒵} {C : Ω → 𝒞} {h : 𝒳 → 𝒵 → 𝒞 → 𝒴}
    (hh : Measurable (fun p : (𝒳 × 𝒵) × 𝒞 => h p.1.1 p.1.2 p.2)) :
    Kernel (𝒳 × 𝒵) 𝒴 where
  toFun p := (condDistrib C Z μ p.2).map (h p.1 p.2)
  measurable' := by
    -- Measurability of `c ↦ h p.1 p.2 c` for fixed `p`, derived from the joint measurability `hh`.
    have hhp : ∀ p : 𝒳 × 𝒵, Measurable (h p.1 p.2) := fun p =>
      hh.comp (measurable_const.prodMk measurable_id)
    refine Measure.measurable_of_measurable_coe _ (fun B hB => ?_)
    -- `((condDistrib C Z μ p.2).map (h p.1 p.2)) B = (condDistrib C Z μ p.2) ((h p.1 p.2) ⁻¹' B)`
    have hmap : ∀ p : 𝒳 × 𝒵,
        ((condDistrib C Z μ p.2).map (h p.1 p.2)) B
          = (condDistrib C Z μ p.2) ((h p.1 p.2) ⁻¹' B) := by
      intro p
      rw [Measure.map_apply (hhp p) hB]
    simp_rw [hmap]
    -- Express the inner measure as a kernel lintegral and use measurability of the integrand.
    set κ' : Kernel (𝒳 × 𝒵) 𝒞 :=
      (condDistrib C Z μ).comap (Prod.snd : 𝒳 × 𝒵 → 𝒵) measurable_snd with hκ'
    have hker : ∀ p : 𝒳 × 𝒵,
        (condDistrib C Z μ p.2) ((h p.1 p.2) ⁻¹' B)
          = ∫⁻ c, B.indicator (1 : 𝒴 → ℝ≥0∞) (h p.1 p.2 c) ∂(κ' p) := by
      intro p
      rw [hκ', Kernel.comap_apply, ← lintegral_indicator_one ((hhp p) hB)]
      refine lintegral_congr (fun c => ?_)
      by_cases hc : h p.1 p.2 c ∈ B <;> simp [Set.mem_preimage, hc]
    simp_rw [hker]
    refine Measurable.lintegral_kernel_prod_right ?_
    -- `(p, c) ↦ B.indicator 1 (h p.1 p.2 c)` is measurable from `hh`.
    exact (measurable_const.indicator hB).comp hh

omit [StandardBorelSpace 𝒴] [Nonempty 𝒴] in
/-- Evaluating the witness kernel at a conditioning pair gives the residual conditional law
pushed through the corresponding structural slice. -/
@[simp]
lemma witnessKernel_apply (μ : Measure Ω) [IsFiniteMeasure μ]
    (Z : Ω → 𝒵) (C : Ω → 𝒞) {h : 𝒳 → 𝒵 → 𝒞 → 𝒴}
    (hh : Measurable (fun p : (𝒳 × 𝒵) × 𝒞 => h p.1.1 p.1.2 p.2)) (p : 𝒳 × 𝒵) :
    witnessKernel μ (Z := Z) (C := C) hh p = (condDistrib C Z μ p.2).map (h p.1 p.2) := rfl

/-- The witness kernel is a Markov kernel when the base measure is finite. -/
instance instIsMarkovKernel_witnessKernel (μ : Measure Ω) [IsFiniteMeasure μ]
    {Z : Ω → 𝒵} {C : Ω → 𝒞} {h : 𝒳 → 𝒵 → 𝒞 → 𝒴}
    (hh : Measurable (fun p : (𝒳 × 𝒵) × 𝒞 => h p.1.1 p.1.2 p.2)) :
    IsMarkovKernel (witnessKernel μ (Z := Z) (C := C) hh) := by
  constructor
  intro p
  rw [witnessKernel_apply]
  have hhp : Measurable (h p.1 p.2) := hh.comp (measurable_const.prodMk measurable_id)
  have : IsMarkovKernel (condDistrib C Z μ) := inferInstance
  exact Measure.isProbabilityMeasure_map hhp.aemeasurable

/-- **Witness-kernel form of a conditional distribution under conditional independence.**

If `Y = h X Z C` pointwise and `C` is conditionally independent of `X` given `Z` — expressed as the
a.e. equality of conditional kernels `condDistrib C (X,Z) = condDistrib C Z` — then the conditional
distribution of `Y` given `(X,Z)` is, a.e., the pushforward of `condDistrib C Z` by `h x z`. -/
theorem condDistrib_map_of_condDistrib_fst_eq
    (μ : Measure Ω) [IsFiniteMeasure μ]
    {X : Ω → 𝒳} {Z : Ω → 𝒵} {C : Ω → 𝒞} {h : 𝒳 → 𝒵 → 𝒞 → 𝒴}
    (hX : Measurable X) (hZ : Measurable Z) (hC : Measurable C)
    (hh : Measurable (fun p : (𝒳 × 𝒵) × 𝒞 => h p.1.1 p.1.2 p.2))
    (hCI : (fun p : 𝒳 × 𝒵 => condDistrib C (fun ω => (X ω, Z ω)) μ p)
            =ᵐ[μ.map (fun ω => (X ω, Z ω))]
           (fun p => condDistrib C Z μ p.2)) :
    (fun p : 𝒳 × 𝒵 => condDistrib (fun ω => h (X ω) (Z ω) (C ω)) (fun ω => (X ω, Z ω)) μ p)
      =ᵐ[μ.map (fun ω => (X ω, Z ω))]
      (fun p => (condDistrib C Z μ p.2).map (h p.1 p.2)) := by
  set W : Ω → 𝒳 × 𝒵 := fun ω => (X ω, Z ω) with hW
  set Y : Ω → 𝒴 := fun ω => h (X ω) (Z ω) (C ω) with hY
  have hWmeas : Measurable W := hX.prodMk hZ
  have hYmeas : Measurable Y := by
    have : Y = (fun p : (𝒳 × 𝒵) × 𝒞 => h p.1.1 p.1.2 p.2) ∘ (fun ω => (W ω, C ω)) := rfl
    rw [this]; exact hh.comp ((hWmeas).prodMk hC)
  -- The candidate witness kernel.
  set κ : Kernel (𝒳 × 𝒵) 𝒴 := witnessKernel μ (Z := Z) (C := C) hh with hκ
  -- It suffices, by uniqueness of `condDistrib`, to verify the disintegration identity.
  suffices hgoal : condDistrib Y W μ =ᵐ[μ.map W] κ by
    filter_upwards [hgoal] with p hp
    rw [hp, hκ, witnessKernel_apply]
  refine condDistrib_ae_eq_of_measure_eq_compProd W hYmeas.aemeasurable ?_
  -- Verify `μ.map (W, Y) = μ.map W ⊗ₘ κ` on rectangles.
  refine Measure.ext_prod (fun {A B} hA hB => ?_)
  -- RHS: `(μ.map W ⊗ₘ κ) (A ×ˢ B) = ∫⁻ p in A, κ p B ∂(μ.map W)`.
  rw [Measure.compProd_apply_prod hA hB]
  -- Rewrite `κ p B` using `condDistrib C Z μ p.2 = condDistrib C W μ p` (a.e. via `hCI`).
  have hκB : ∀ p : 𝒳 × 𝒵, κ p B = (condDistrib C Z μ p.2) ((h p.1 p.2) ⁻¹' B) := by
    intro p
    have hhp : Measurable (h p.1 p.2) := hh.comp (measurable_const.prodMk measurable_id)
    rw [hκ, witnessKernel_apply μ Z C hh, Measure.map_apply hhp hB]
  simp_rw [hκB]
  -- Replace `condDistrib C Z μ p.2` by `condDistrib C W μ p` on `A` using `hCI`.
  have hint : ∫⁻ p in A, (condDistrib C Z μ p.2) ((h p.1 p.2) ⁻¹' B) ∂(μ.map W)
      = ∫⁻ p in A, (condDistrib C W μ p) ((h p.1 p.2) ⁻¹' B) ∂(μ.map W) := by
    refine lintegral_congr_ae (ae_restrict_of_ae ?_)
    filter_upwards [hCI] with p hp
    rw [hp]
  rw [hint]
  -- This integral is `(μ.map W ⊗ₘ condDistrib C W μ)` on `{(p,c) | p ∈ A ∧ h p.1 p.2 c ∈ B}`.
  have hCWmarkov : IsMarkovKernel (condDistrib C W μ) := inferInstance
  have hset : MeasurableSet {q : (𝒳 × 𝒵) × 𝒞 | q.1 ∈ A ∧ h q.1.1 q.1.2 q.2 ∈ B} := by
    apply MeasurableSet.inter
    · exact measurable_fst hA
    · exact hh hB
  have hcompProd :
      ∫⁻ p in A, (condDistrib C W μ p) ((h p.1 p.2) ⁻¹' B) ∂(μ.map W)
        = (μ.map W ⊗ₘ condDistrib C W μ)
            {q : (𝒳 × 𝒵) × 𝒞 | q.1 ∈ A ∧ h q.1.1 q.1.2 q.2 ∈ B} := by
    rw [Measure.compProd_apply hset]
    rw [← lintegral_indicator hA]
    refine lintegral_congr (fun p => ?_)
    by_cases hpA : p ∈ A
    · rw [Set.indicator_of_mem hpA]
      congr 1
      ext c
      simp [hpA]
    · rw [Set.indicator_of_notMem hpA]
      have : (Prod.mk p ⁻¹' {q : (𝒳 × 𝒵) × 𝒞 | q.1 ∈ A ∧ h q.1.1 q.1.2 q.2 ∈ B}) = ∅ := by
        ext c; simp [hpA]
      rw [this]; simp
  rw [hcompProd, compProd_map_condDistrib hC.aemeasurable]
  -- Finally identify with `μ.map (W, Y) (A ×ˢ B)`.
  rw [Measure.map_apply (hWmeas.prodMk hC) hset]
  rw [Measure.map_apply (hWmeas.prodMk hYmeas) (hA.prod hB)]
  -- The two preimage events `{W ∈ A ∧ Y ∈ B}` and `{(W,C) ∈ {q | q.1 ∈ A ∧ h … ∈ B}}` coincide.
  congr 1

/-- **No-treatment witness-kernel form of a conditional distribution.**

If `Y = H Z C` pointwise (no separate conditioning-independent coordinate), then the conditional
distribution of `Y` given `Z` is, a.e., the pushforward of `condDistrib C Z` by `H z`.  This is the
`X`-free specialization of `condDistrib_map_of_condDistrib_fst_eq`: with the conditioning variable
`Z` equal to the full information used to split `Y`, no conditional-independence hypothesis is
needed (the trivial `X` carries no information). -/
theorem condDistrib_map_of_funext
    (μ : Measure Ω) [IsFiniteMeasure μ]
    {Z : Ω → 𝒵} {C : Ω → 𝒞} {H : 𝒵 → 𝒞 → 𝒴}
    (hZ : Measurable Z) (hC : Measurable C)
    (hH : Measurable (fun p : 𝒵 × 𝒞 => H p.1 p.2)) :
    (fun z : 𝒵 => condDistrib (fun ω => H (Z ω) (C ω)) Z μ z)
      =ᵐ[μ.map Z]
      (fun z => (condDistrib C Z μ z).map (H z)) := by
  set Y : Ω → 𝒴 := fun ω => H (Z ω) (C ω) with hY
  have hYmeas : Measurable Y := by
    have : Y = (fun p : 𝒵 × 𝒞 => H p.1 p.2) ∘ (fun ω => (Z ω, C ω)) := rfl
    rw [this]; exact hH.comp (hZ.prodMk hC)
  -- The candidate witness kernel `z ↦ (condDistrib C Z μ z).map (H z)`.
  have hHz : ∀ z : 𝒵, Measurable (H z) := fun z =>
    hH.comp (measurable_const.prodMk measurable_id)
  let κ : Kernel 𝒵 𝒴 :=
    { toFun := fun z => (condDistrib C Z μ z).map (H z)
      measurable' := by
        refine Measure.measurable_of_measurable_coe _ (fun B hB => ?_)
        have hmap : ∀ z : 𝒵,
            ((condDistrib C Z μ z).map (H z)) B
              = (condDistrib C Z μ z) ((H z) ⁻¹' B) := fun z => by
          rw [Measure.map_apply (hHz z) hB]
        simp_rw [hmap]
        have hker : ∀ z : 𝒵,
            (condDistrib C Z μ z) ((H z) ⁻¹' B)
              = ∫⁻ c, B.indicator (1 : 𝒴 → ℝ≥0∞) (H z c) ∂(condDistrib C Z μ z) := by
          intro z
          rw [← lintegral_indicator_one ((hHz z) hB)]
          refine lintegral_congr (fun c => ?_)
          by_cases hc : H z c ∈ B <;> simp [Set.mem_preimage, hc]
        simp_rw [hker]
        refine Measurable.lintegral_kernel_prod_right ?_
        exact (measurable_const.indicator hB).comp hH }
  have hκ_apply : ∀ z, κ z = (condDistrib C Z μ z).map (H z) := fun _ => rfl
  haveI hκmarkov : IsMarkovKernel κ := by
    constructor
    intro z
    rw [hκ_apply]
    have : IsMarkovKernel (condDistrib C Z μ) := inferInstance
    exact Measure.isProbabilityMeasure_map (hHz z).aemeasurable
  suffices hgoal : condDistrib Y Z μ =ᵐ[μ.map Z] κ by
    filter_upwards [hgoal] with z hz
    rw [hz, hκ_apply]
  refine condDistrib_ae_eq_of_measure_eq_compProd Z hYmeas.aemeasurable ?_
  refine Measure.ext_prod (fun {A B} hA hB => ?_)
  rw [Measure.compProd_apply_prod hA hB]
  have hκB : ∀ z : 𝒵, κ z B = (condDistrib C Z μ z) ((H z) ⁻¹' B) := by
    intro z; rw [hκ_apply]; exact Measure.map_apply (hHz z) hB
  simp_rw [hκB]
  have hCmarkov : IsMarkovKernel (condDistrib C Z μ) := inferInstance
  have hset : MeasurableSet {q : 𝒵 × 𝒞 | q.1 ∈ A ∧ H q.1 q.2 ∈ B} := by
    apply MeasurableSet.inter
    · exact measurable_fst hA
    · exact hH hB
  have hcompProd :
      ∫⁻ z in A, (condDistrib C Z μ z) ((H z) ⁻¹' B) ∂(μ.map Z)
        = (μ.map Z ⊗ₘ condDistrib C Z μ)
            {q : 𝒵 × 𝒞 | q.1 ∈ A ∧ H q.1 q.2 ∈ B} := by
    rw [Measure.compProd_apply hset, ← lintegral_indicator hA]
    refine lintegral_congr (fun z => ?_)
    by_cases hzA : z ∈ A
    · rw [Set.indicator_of_mem hzA]
      congr 1; ext c; simp [hzA]
    · rw [Set.indicator_of_notMem hzA]
      have : (Prod.mk z ⁻¹' {q : 𝒵 × 𝒞 | q.1 ∈ A ∧ H q.1 q.2 ∈ B}) = ∅ := by
        ext c; simp [hzA]
      rw [this]; simp
  rw [hcompProd, compProd_map_condDistrib hC.aemeasurable]
  rw [Measure.map_apply (hZ.prodMk hC) hset]
  rw [Measure.map_apply (hZ.prodMk hYmeas) (hA.prod hB)]
  congr 1

end ProbabilityTheory
