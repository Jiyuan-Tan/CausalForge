/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# KL identities for shared-base bind/compProd constructions

This file collects the measure-theoretic KL facts needed for least-favourable
law constructions built by Giry-monad binds.  Mathlib currently has the
Radon--Nikodym and kernel decomposition ingredients, but not a ready
Kullback--Leibler chain-rule API for shared-base composition products.
-/

import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Probability.Kernel.Composition.RadonNikodym
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.RadonNikodym

/-! # KL Identities for Shared-Base Binds

This file proves Kullback--Leibler identities for composition products and binds
whose two laws share the same base measure and differ only in their conditional
kernels. These are measure-theoretic chain-rule tools for least-favourable laws
and bind-based information arguments.

Inside the `Measure` namespace:
* `rnDeriv_compProd_right_of_forall_ac` identifies the Radon--Nikodym derivative
  of `μ ⊗ₘ κ` with respect to `μ ⊗ₘ η` as the fibre derivative
  `Kernel.rnDeriv κ η`.
* `klDiv_compProd_right_of_forall_ac` is the KL chain rule for shared-base
  composition products:
  `klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) = ∫⁻ a, klDiv (κ a) (η a) ∂μ`.
* `klDiv_map_measurableEmbedding` shows that KL is invariant under a measurable
  embedding.
* `klDiv_bind_eq_of_base_recording` transfers the chain rule to binds when the
  output records its base coordinate through a measurable projection. -/

namespace Causalean.Mathlib.InformationTheory

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Measure

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  {μ : Measure α} {κ η : Kernel α β}

/-- Radon--Nikodym derivative of a shared-base composition product.

If all fibres of `κ` are absolutely continuous with respect to the
corresponding fibres of `η`, then the RN derivative of `μ ⊗ₘ κ` with respect to
`μ ⊗ₘ η` is the fibre RN derivative. -/
lemma rnDeriv_compProd_right_of_forall_ac
    [MeasurableSpace.CountableOrCountablyGenerated α β]
    [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η]
    (hκη : ∀ a, κ a ≪ η a) :
    (μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) =ᵐ[μ ⊗ₘ η]
      fun p : α × β => Kernel.rnDeriv κ η p.1 p.2 := by
  have hκ_eq : κ =ᵐ[μ] Kernel.withDensity η (Kernel.rnDeriv κ η) := by
    filter_upwards [] with a
    exact (Kernel.withDensity_rnDeriv_eq (κ := κ) (η := η) (a := a) (hκη a)).symm
  have hcomp :
      μ ⊗ₘ κ = (μ ⊗ₘ η).withDensity
        (fun p : α × β => Kernel.rnDeriv κ η p.1 p.2) := by
    calc
      μ ⊗ₘ κ = μ ⊗ₘ Kernel.withDensity η (Kernel.rnDeriv κ η) :=
        Measure.compProd_congr hκ_eq
      _ = (μ ⊗ₘ η).withDensity
          (fun p : α × β => Kernel.rnDeriv κ η p.1 p.2) := by
        rw [Measure.compProd_withDensity]
        exact Kernel.measurable_rnDeriv κ η
  rw [hcomp]
  have hwd := Measure.rnDeriv_withDensity_left_of_absolutelyContinuous
    (μ := μ ⊗ₘ η) (ν := μ ⊗ₘ η)
    (f := fun p : α × β => Kernel.rnDeriv κ η p.1 p.2)
    Measure.AbsolutelyContinuous.rfl
    (Kernel.measurable_rnDeriv κ η).aemeasurable
  refine hwd.trans ?_
  filter_upwards [Measure.rnDeriv_self (μ ⊗ₘ η)] with p hp
  rw [hp, mul_one]

/-- KL chain rule for a shared-base composition product, under pointwise fibre
absolute continuity.

This is the exact identity form used by bind-chain arguments whose output still
remembers the base coordinate. -/
lemma klDiv_compProd_right_of_forall_ac
    [MeasurableSpace.CountableOrCountablyGenerated α β]
    [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η]
    (hκη : ∀ a, κ a ≪ η a) :
    _root_.InformationTheory.klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η)
      = ∫⁻ a, _root_.InformationTheory.klDiv (κ a) (η a) ∂μ := by
  classical
  have hcomp_ac : μ ⊗ₘ κ ≪ μ ⊗ₘ η :=
    Measure.AbsolutelyContinuous.compProd_right (Filter.Eventually.of_forall hκη)
  rw [_root_.InformationTheory.klDiv_eq_lintegral_klFun, if_pos hcomp_ac]
  trans ∫⁻ p : α × β,
      ENNReal.ofReal
        (_root_.InformationTheory.klFun
          ((Kernel.rnDeriv κ η p.1 p.2).toReal)) ∂(μ ⊗ₘ η)
  · refine lintegral_congr_ae ?_
    filter_upwards [rnDeriv_compProd_right_of_forall_ac (μ := μ) (κ := κ) (η := η) hκη]
      with p hp
    rw [hp]
  · rw [Measure.lintegral_compProd]
    · refine lintegral_congr_ae ?_
      filter_upwards [] with a
      rw [_root_.InformationTheory.klDiv_eq_lintegral_klFun, if_pos (hκη a)]
      refine lintegral_congr_ae ?_
      filter_upwards [Kernel.rnDeriv_eq_rnDeriv_measure (κ := κ) (η := η) (a := a)]
        with b hb
      rw [hb]
    · fun_prop

/-- KL is invariant under a measurable embedding. -/
lemma klDiv_map_measurableEmbedding
    {f : α → γ} (hf : MeasurableEmbedding f)
    [IsFiniteMeasure μ] [IsFiniteMeasure (μ.map f)]
    {ν : Measure α} [IsFiniteMeasure ν] [IsFiniteMeasure (ν.map f)] :
    _root_.InformationTheory.klDiv (μ.map f) (ν.map f)
      = _root_.InformationTheory.klDiv μ ν := by
  classical
  by_cases hμν : μ ≪ ν
  · have hmap_ac : μ.map f ≪ ν.map f := hf.absolutelyContinuous_map hμν
    rw [_root_.InformationTheory.klDiv_eq_lintegral_klFun,
      _root_.InformationTheory.klDiv_eq_lintegral_klFun,
      if_pos hmap_ac, if_pos hμν]
    rw [hf.lintegral_map]
    refine lintegral_congr_ae ?_
    filter_upwards [hf.rnDeriv_map μ ν] with x hx
    rw [hx]
  · rw [_root_.InformationTheory.klDiv_of_not_ac hμν]
    have hmap_not_ac : ¬ μ.map f ≪ ν.map f := by
      intro hmap
      exact hμν (Measure.AbsolutelyContinuous.mk fun s hs hs0 => by
        have hpre : f ⁻¹' (f '' s) = s := by
          rw [hf.injective.preimage_image]
        have hs_image : MeasurableSet (f '' s) := hf.measurableSet_image' hs
        have hν_image : ν.map f (f '' s) = 0 := by
          rw [hf.map_apply ν (f '' s), hpre]
          exact hs0
        have hμ_image : μ.map f (f '' s) = 0 := hmap hν_image
        rw [hf.map_apply μ (f '' s), hpre] at hμ_image
        exact hμ_image)
    rw [_root_.InformationTheory.klDiv_of_not_ac hmap_not_ac]

private lemma measurableEmbedding_base_recording
    {B Ω : Type*} [MeasurableSpace B] [MeasurableSpace Ω]
    (proj : Ω → B) (hproj : Measurable proj)
    (hgraph : MeasurableSet {p : B × Ω | p.1 = proj p.2}) :
    MeasurableEmbedding (fun ω : Ω => (proj ω, ω)) := by
  have hg : Measurable (fun ω : Ω => (proj ω, ω)) := hproj.prod measurable_id
  have hRange :
      Set.range (fun ω : Ω => (proj ω, ω))
        = {p : B × Ω | p.1 = proj p.2} := by
    ext p
    constructor
    · rintro ⟨ω, rfl⟩
      rfl
    · intro hp
      exact ⟨p.2, Prod.ext hp.symm rfl⟩
  exact MeasurableEmbedding.of_measurable_inverse hg (by simpa [hRange] using hgraph)
    measurable_snd (by intro ω; rfl)

private lemma map_bind_eq_compProd_of_base_recording
    {B Ω : Type*} [MeasurableSpace B] [MeasurableSpace Ω]
    (m : Measure B) [SFinite m] (κ : Kernel B Ω) [IsSFiniteKernel κ]
    (proj : Ω → B) (hproj : Measurable proj)
    (hκ_fib : ∀ b, (κ b) {ω | proj ω = b}ᶜ = 0) :
    (m.bind κ).map (fun ω : Ω => (proj ω, ω)) = m ⊗ₘ κ := by
  let g : Ω → B × Ω := fun ω => (proj ω, ω)
  have hg : Measurable g := hproj.prod measurable_id
  calc
    (m.bind κ).map (fun ω : Ω => (proj ω, ω)) = m.bind (Kernel.map κ g) := by
      simpa [g] using Measure.map_comp (μ := m) (κ := κ) (f := g) hg
    _ = m.bind (Kernel.id ×ₖ κ) := by
      refine Measure.bind_congr_right ?_
      filter_upwards [] with b
      have hsupp : {ω : Ω | proj ω = b} ∈ ae (κ b) := mem_ae_iff.mpr (hκ_fib b)
      have h_ae : g =ᵐ[κ b] Prod.mk b := by
        filter_upwards [hsupp] with ω hω
        exact Prod.ext hω rfl
      calc
        (Kernel.map κ g) b = (κ b).map g := Kernel.map_apply κ hg b
        _ = (κ b).map (Prod.mk b) := Measure.map_congr h_ae
        _ = (Kernel.id ×ₖ κ) b := by
          ext s hs
          rw [Measure.map_apply measurable_prodMk_left hs, Kernel.id_prod_apply' κ b hs]
    _ = m ⊗ₘ κ := by
      simpa using (Measure.compProd_eq_comp_prod m κ).symm

/-- Shared-base bind chain rule, when the output records its base coordinate via `proj`. -/
lemma klDiv_bind_eq_of_base_recording
    {B Ω : Type*} [MeasurableSpace B] [MeasurableSpace Ω]
    [MeasurableSpace.CountableOrCountablyGenerated B Ω]
    (m : Measure B) [IsFiniteMeasure m]
    (κ η : Kernel B Ω) [IsMarkovKernel κ] [IsMarkovKernel η]
    (proj : Ω → B) (hproj : Measurable proj)
    (hgraph : MeasurableSet {p : B × Ω | p.1 = proj p.2})
    (hκ_fib : ∀ b, (κ b) {ω | proj ω = b}ᶜ = 0)
    (hη_fib : ∀ b, (η b) {ω | proj ω = b}ᶜ = 0)
    (hκη : ∀ b, κ b ≪ η b) :
    _root_.InformationTheory.klDiv (m.bind κ) (m.bind η)
      = ∫⁻ b, _root_.InformationTheory.klDiv (κ b) (η b) ∂m := by
  let g : Ω → B × Ω := fun ω => (proj ω, ω)
  have hg_emb : MeasurableEmbedding g := by
    simpa [g] using measurableEmbedding_base_recording (proj := proj) hproj hgraph
  have hκ_map : (m.bind κ).map g = m ⊗ₘ κ := by
    simpa [g] using map_bind_eq_compProd_of_base_recording
      (m := m) (κ := κ) (proj := proj) hproj hκ_fib
  have hη_map : (m.bind η).map g = m ⊗ₘ η := by
    simpa [g] using map_bind_eq_compProd_of_base_recording
      (m := m) (κ := η) (proj := proj) hproj hη_fib
  haveI hmκ : IsFiniteMeasure (m.bind κ) := by
    rw [← Measure.snd_compProd (μ := m) (κ := κ)]
    infer_instance
  haveI hmη : IsFiniteMeasure (m.bind η) := by
    rw [← Measure.snd_compProd (μ := m) (κ := η)]
    infer_instance
  calc
    _root_.InformationTheory.klDiv (m.bind κ) (m.bind η)
        = _root_.InformationTheory.klDiv ((m.bind κ).map g) ((m.bind η).map g) := by
          exact (klDiv_map_measurableEmbedding
            (μ := m.bind κ) (ν := m.bind η) (f := g) hg_emb).symm
    _ = _root_.InformationTheory.klDiv (m ⊗ₘ κ) (m ⊗ₘ η) := by
      rw [hκ_map, hη_map]
    _ = ∫⁻ b, _root_.InformationTheory.klDiv (κ b) (η b) ∂m :=
      klDiv_compProd_right_of_forall_ac (μ := m) (κ := κ) (η := η) hκη

end Measure

end Causalean.Mathlib.InformationTheory
