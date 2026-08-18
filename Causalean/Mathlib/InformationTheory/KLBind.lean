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
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.Topology.Instances.Real.Lemmas


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

If almost all `μ`-fibres of `κ` are absolutely continuous with respect to the
corresponding fibres of `η`, then the RN derivative of `μ ⊗ₘ κ` with respect to
`μ ⊗ₘ η` is the fibre RN derivative. -/
lemma rnDeriv_compProd_right_of_forall_ac
    [MeasurableSpace.CountableOrCountablyGenerated α β]
    [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η]
    (hκη : ∀ᵐ a ∂μ, κ a ≪ η a) :
    (μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) =ᵐ[μ ⊗ₘ η]
      fun p : α × β => Kernel.rnDeriv κ η p.1 p.2 := by
  have hκ_eq : κ =ᵐ[μ] Kernel.withDensity η (Kernel.rnDeriv κ η) := by
    filter_upwards [hκη] with a ha
    exact (Kernel.withDensity_rnDeriv_eq (κ := κ) (η := η) (a := a) ha).symm
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

/-- For a countably-generated pair of measurable spaces, a finite base measure `μ`, and finite
    kernels `κ`, `η` out of the base, if [`κ b` is absolutely continuous with respect to `η b`
    for `μ`-almost every base point `b`](hyp:hκη), then [the Kullback–Leibler divergence between
    the composition products `μ ⊗ₘ κ` and `μ ⊗ₘ η` equals the `μ`-average, over the base point,
    of the Kullback–Leibler divergence between `κ` and `η` at that base point](goal).

This is the exact identity form used by bind-chain arguments whose output still
remembers the base coordinate. -/
lemma klDiv_compProd_right_of_forall_ac
    [MeasurableSpace.CountableOrCountablyGenerated α β]
    [IsFiniteMeasure μ] [IsFiniteKernel κ] [IsFiniteKernel η]
    (hκη : ∀ᵐ a ∂μ, κ a ≪ η a) :
    _root_.InformationTheory.klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η)
      = ∫⁻ a, _root_.InformationTheory.klDiv (κ a) (η a) ∂μ := by
  classical
  have hcomp_ac : μ ⊗ₘ κ ≪ μ ⊗ₘ η :=
    Measure.AbsolutelyContinuous.compProd_right hκη
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
      filter_upwards [hκη] with a ha
      rw [_root_.InformationTheory.klDiv_eq_lintegral_klFun, if_pos ha]
      refine lintegral_congr_ae ?_
      filter_upwards [Kernel.rnDeriv_eq_rnDeriv_measure (κ := κ) (η := η) (a := a)]
        with b hb
      rw [hb]
    · fun_prop

/-- KL is invariant under a measurable embedding. -/
lemma klDiv_map_measurableEmbedding
    {f : α → γ} (hf : MeasurableEmbedding f)
    [IsFiniteMeasure μ] {ν : Measure α} [IsFiniteMeasure ν] :
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

/-- If a measurable map has a measurable graph, pairing each observation with its map value
produces a measurable embedding into the corresponding product space. -/
lemma measurableEmbedding_base_recording
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

/-- If a kernel is supported almost everywhere on outputs that record their base
coordinate, then mapping its bound measure to the recorded base-output pair gives the
corresponding composition-product measure. -/
lemma map_bind_eq_compProd_of_base_recording
    {B Ω : Type*} [MeasurableSpace B] [MeasurableSpace Ω]
    (m : Measure B) [SFinite m] (κ : Kernel B Ω) [IsSFiniteKernel κ]
    (proj : Ω → B) (hproj : Measurable proj)
    (hκ_fib : ∀ᵐ b ∂m, (κ b) {ω | proj ω = b}ᶜ = 0) :
    (m.bind κ).map (fun ω : Ω => (proj ω, ω)) = m ⊗ₘ κ := by
  let g : Ω → B × Ω := fun ω => (proj ω, ω)
  have hg : Measurable g := hproj.prod measurable_id
  calc
    (m.bind κ).map (fun ω : Ω => (proj ω, ω)) = m.bind (Kernel.map κ g) := by
      simpa [g] using Measure.map_comp (μ := m) (κ := κ) (f := g) hg
    _ = m.bind (Kernel.id ×ₖ κ) := by
      refine Measure.bind_congr_right ?_
      filter_upwards [hκ_fib] with b hκ_fib
      have hsupp : {ω : Ω | proj ω = b} ∈ ae (κ b) := mem_ae_iff.mpr hκ_fib
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

/-- For measurable spaces `B` and `Ω`, a finite base measure `m`, finite kernels `κ`, `η` from `B`
    to `Ω`, and [a measurable projection `proj : Ω → B`](hyp:hproj) whose [graph
    `{(b, ω) | b = proj ω}` is a measurable subset of `B × Ω`](hyp:hgraph), suppose
    [`κ`-almost every output, for `m`-almost every base point `b`, lands in the fibre
    `proj⁻¹{b}`](hyp:hκ_fib), [likewise for `η`](hyp:hη_fib), and [`κ b` is absolutely continuous
    with respect to `η b` for `m`-almost every `b`](hyp:hκη). Then [the Kullback–Leibler
    divergence between the bind of `m` with `κ` and the bind of `m` with `η` equals the
    `m`-average, over the base point `b`, of the Kullback–Leibler divergence between `κ b` and
    `η b`](goal). -/
lemma klDiv_bind_eq_of_base_recording
    {B Ω : Type*} [MeasurableSpace B] [MeasurableSpace Ω]
    [MeasurableSpace.CountableOrCountablyGenerated B Ω]
    (m : Measure B) [IsFiniteMeasure m]
    (κ η : Kernel B Ω) [IsFiniteKernel κ] [IsFiniteKernel η]
    (proj : Ω → B) (hproj : Measurable proj)
    (hgraph : MeasurableSet {p : B × Ω | p.1 = proj p.2})
    (hκ_fib : ∀ᵐ b ∂m, (κ b) {ω | proj ω = b}ᶜ = 0)
    (hη_fib : ∀ᵐ b ∂m, (η b) {ω | proj ω = b}ᶜ = 0)
    (hκη : ∀ᵐ b ∂m, κ b ≪ η b) :
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
/-! ## KL data processing under measurable maps and Markov kernels

The results in this section show that a common observation rule cannot increase
the Kullback--Leibler divergence between two finite laws.  They cover both
deterministic measurable coarsenings and randomized Markov channels.
-/

open Filter
open scoped Topology

namespace Measure

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

private lemma klFun_tangent {x t : ℝ} (hx : 0 ≤ x) (ht : 0 < t) :
    Real.log t * x + 1 - t ≤ _root_.InformationTheory.klFun x := by
  rcases hx.eq_or_lt with rfl | hx
  · simp [_root_.InformationTheory.klFun_apply, ht.le]
  have hlog := Real.log_le_sub_one_of_pos (div_pos ht hx)
  rw [Real.log_div ht.ne' hx.ne'] at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog hx.le
  have heq : x * (t / x - 1) = t - x := by field_simp
  rw [heq] at hmul
  rw [_root_.InformationTheory.klFun_apply]
  nlinarith

private lemma klFun_condExp_le
    {Ω : Type*} {m m₀ : MeasurableSpace Ω} {ν : Measure Ω} [IsFiniteMeasure ν]
    (hm : m ≤ m₀) (p : Ω → ℝ) (hp : Integrable p ν)
    (hp0 : 0 ≤ᵐ[ν] p)
    (hkp : Integrable (fun x => _root_.InformationTheory.klFun (p x)) ν) :
    ∀ᵐ x ∂ν, _root_.InformationTheory.klFun (ν[p | m] x)
      ≤ ν[fun y => _root_.InformationTheory.klFun (p y) | m] x := by
  let z : Ω → ℝ := ν[p | m]
  let w : Ω → ℝ := ν[fun y => _root_.InformationTheory.klFun (p y) | m]
  have hz0 : 0 ≤ᵐ[ν] z := condExp_nonneg hp0
  have hall : ∀ᵐ x ∂ν, ∀ q : ℚ, 0 < q →
      Real.log (q : ℝ) * z x + 1 - (q : ℝ) ≤ w x := by
    rw [ae_all_iff]
    intro q
    by_cases hq : 0 < q
    · have htangent : (fun x => p x * Real.log (q : ℝ) + (1 - (q : ℝ)))
          ≤ᵐ[ν] fun x => _root_.InformationTheory.klFun (p x) := by
        filter_upwards [hp0] with x hx
        have hqr : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
        convert klFun_tangent (x := p x) (t := (q : ℝ)) hx hqr using 1 <;> ring
      let T : ℝ →L[ℝ] ℝ :=
        ContinuousLinearMap.toSpanSingleton ℝ (Real.log (q : ℝ))
      have haff :=
        ContinuousLinearMap.comp_condExp_add_const_comm hm hp T (1 - (q : ℝ))
      have hint : Integrable (fun x => p x * Real.log (q : ℝ) + (1 - (q : ℝ))) ν := by
        fun_prop
      have hmono := condExp_mono (m := m) hint hkp htangent
      filter_upwards [haff, hmono] with x ha hm'
      intro _
      dsimp [z, w, T] at ha ⊢
      calc
        Real.log (q : ℝ) * ν[p | m] x + 1 - (q : ℝ)
            = ν[p | m] x * Real.log (q : ℝ) + (1 - (q : ℝ)) := by ring
        _ = ν[fun y => p y * Real.log (q : ℝ) + (1 - (q : ℝ)) | m] x := ha
        _ ≤ ν[fun y => _root_.InformationTheory.klFun (p y) | m] x := hm'
    · filter_upwards
      exact fun _ h => (hq h).elim
  filter_upwards [hz0, hall] with x hx hallx
  dsimp [z, w] at hx hallx ⊢
  by_cases hz : ν[p | m] x = 0
  · rw [hz, _root_.InformationTheory.klFun_zero]
    let u : ℕ → ℝ := fun n => 1 - 1 / ((n : ℝ) + 1)
    apply le_of_tendsto (show Tendsto u atTop (𝓝 1) by
      simpa [u] using tendsto_const_nhds.sub
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
    filter_upwards
    intro n
    have hq : (0 : ℚ) < 1 / ((n : ℚ) + 1) := by positivity
    simpa [u, hz] using hallx (1 / ((n : ℚ) + 1)) hq
  · have hzpos : 0 < ν[p | m] x := lt_of_le_of_ne hx (Ne.symm hz)
    obtain ⟨u, -, -, hu⟩ := Real.exists_seq_rat_strictMono_tendsto (ν[p | m] x)
    have hu_pos : ∀ᶠ n in atTop, (0 : ℝ) < (u n : ℝ) :=
      hu.eventually (Ioi_mem_nhds hzpos)
    have htend :
        Tendsto (fun n => Real.log (u n : ℝ) * ν[p | m] x + 1 - (u n : ℝ))
          atTop (𝓝 (_root_.InformationTheory.klFun (ν[p | m] x))) := by
      have hc : ContinuousAt
          (fun t : ℝ => Real.log t * ν[p | m] x + 1 - t) (ν[p | m] x) :=
        ((Real.continuousAt_log hz).mul continuousAt_const).add continuousAt_const |>.sub
          continuousAt_id
      simpa [_root_.InformationTheory.klFun_apply, mul_comm, Function.comp_def] using
        hc.tendsto.comp hu
    apply le_of_tendsto htend
    filter_upwards [hu_pos] with n hn
    exact hallx (u n) (by exact_mod_cast hn)

/-- A common measurable observation rule cannot increase the Kullback--Leibler
divergence between two finite input laws, even when the rule merges distinct inputs. -/
theorem klDiv_map_le {μ ν : Measure α} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {f : α → β} (hf : Measurable f) :
    _root_.InformationTheory.klDiv (μ.map f) (ν.map f)
      ≤ _root_.InformationTheory.klDiv μ ν := by
  classical
  by_cases htop : _root_.InformationTheory.klDiv μ ν = ∞
  · rw [htop]
    exact le_top
  have hμν_int := _root_.InformationTheory.klDiv_ne_top_iff.mp htop
  have hμν : μ ≪ ν := hμν_int.1
  have hmap : μ.map f ≪ ν.map f := by
    refine Measure.AbsolutelyContinuous.mk ?_
    intro s hs hs0
    rw [Measure.map_apply hf hs] at hs0 ⊢
    exact hμν hs0
  let mf : Unit → MeasurableSpace α := fun _ => MeasurableSpace.comap f inferInstance
  have hmf : mf () ≤ (inferInstance : MeasurableSpace α) := by
    simpa [mf] using hf.comap_le
  let p : α → ℝ := fun x => (μ.rnDeriv ν x).toReal
  let q : β → ℝ := fun y => ((μ.map f).rnDeriv (ν.map f) y).toReal
  have hp : Integrable p ν := Measure.integrable_toReal_rnDeriv
  have hp0 : 0 ≤ᵐ[ν] p := ae_of_all ν fun _ => ENNReal.toReal_nonneg
  have hkp : Integrable (fun x => _root_.InformationTheory.klFun (p x)) ν := by
    exact (_root_.InformationTheory.integrable_klFun_rnDeriv_iff hμν).2 hμν_int.2
  have hq : Integrable q (ν.map f) := Measure.integrable_toReal_rnDeriv
  have hq_comp : Integrable (q ∘ f) ν := hq.comp_measurable hf
  have hq_cond : q ∘ f =ᵐ[ν] ν[p | mf ()] := by
    apply ae_eq_condExp_of_forall_setIntegral_eq hmf hp
    · intro s _ _
      exact hq_comp.integrableOn
    · intro s hs _
      change ∃ t, MeasurableSet t ∧ f ⁻¹' t = s at hs
      obtain ⟨t, ht, rfl⟩ := hs
      calc
        ∫ x in f ⁻¹' t, (q ∘ f) x ∂ν = ∫ y in t, q y ∂(ν.map f) := by
          symm
          exact setIntegral_map ht (by fun_prop) hf.aemeasurable
        _ = (μ.map f).real t := Measure.setIntegral_toReal_rnDeriv hmap t
        _ = μ.real (f ⁻¹' t) := by simp [Measure.map_apply hf ht, measureReal_def]
        _ = ∫ x in f ⁻¹' t, p x ∂ν :=
          (Measure.setIntegral_toReal_rnDeriv hμν (f ⁻¹' t)).symm
    · have hq_meas : Measurable q := by
        dsimp [q]
        exact (Measure.measurable_rnDeriv _ _).ennreal_toReal
      have hf_mf : Measurable[mf ()] f := by
        simpa [mf] using comap_measurable f
      exact (hq_meas.comp hf_mf).aestronglyMeasurable
  have hJ := klFun_condExp_le hmf p hp hp0 hkp
  have hineq : (fun x => _root_.InformationTheory.klFun (q (f x)))
      ≤ᵐ[ν] ν[fun y => _root_.InformationTheory.klFun (p y) | mf ()] := by
    filter_upwards [hq_cond, hJ] with x hqc hj
    change _root_.InformationTheory.klFun ((q ∘ f) x) ≤ _
    rw [hqc]
    exact hj
  have hw0 : 0 ≤ᵐ[ν] ν[fun y => _root_.InformationTheory.klFun (p y) | mf ()] :=
    condExp_nonneg (ae_of_all ν fun x =>
      _root_.InformationTheory.klFun_nonneg
        (show 0 ≤ p x from ENNReal.toReal_nonneg))
  have hkq_comp : Integrable (fun x => _root_.InformationTheory.klFun (q (f x))) ν := by
    apply Integrable.mono' (integrable_condExp :
      Integrable (ν[fun y => _root_.InformationTheory.klFun (p y) | mf ()]) ν)
    · have hq_meas : Measurable q := by
        dsimp [q]
        exact (Measure.measurable_rnDeriv _ _).ennreal_toReal
      exact (_root_.InformationTheory.measurable_klFun.comp
        (hq_meas.comp hf)).aestronglyMeasurable
    filter_upwards [hineq, hw0] with x hx hwx
    rw [Real.norm_eq_abs, abs_of_nonneg
      (_root_.InformationTheory.klFun_nonneg
        (show 0 ≤ q (f x) from ENNReal.toReal_nonneg))]
    exact hx
  have hkq : Integrable (fun y => _root_.InformationTheory.klFun (q y)) (ν.map f) := by
    rw [integrable_map_measure (by fun_prop) hf.aemeasurable]
    exact hkq_comp
  have hllr_map :
      Integrable (llr (μ.map f) (ν.map f)) (μ.map f) :=
    (_root_.InformationTheory.integrable_klFun_rnDeriv_iff hmap).1 hkq
  apply (ENNReal.toReal_le_toReal
    (_root_.InformationTheory.klDiv_ne_top hmap hllr_map) htop).mp
  rw [_root_.InformationTheory.toReal_klDiv_eq_integral_klFun hmap,
    _root_.InformationTheory.toReal_klDiv_eq_integral_klFun hμν]
  change (∫ y, _root_.InformationTheory.klFun (q y) ∂(ν.map f))
    ≤ ∫ x, _root_.InformationTheory.klFun (p x) ∂ν
  rw [integral_map hf.aemeasurable hkq.1]
  calc
    ∫ x, _root_.InformationTheory.klFun (q (f x)) ∂ν
        ≤ ∫ x, ν[fun y => _root_.InformationTheory.klFun (p y) | mf ()] x ∂ν :=
      integral_mono_ae hkq_comp integrable_condExp hineq
    _ = ∫ x, _root_.InformationTheory.klFun (p x) ∂ν := integral_condExp hmf

/-- Adding an output drawn from the same Markov kernel preserves the
Kullback--Leibler divergence between two finite input laws because the joint
observation still retains the input coordinate. -/
theorem klDiv_compProd_left (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ : Kernel α β) [IsMarkovKernel κ] :
    _root_.InformationTheory.klDiv (μ ⊗ₘ κ) (ν ⊗ₘ κ)
      = _root_.InformationTheory.klDiv μ ν := by
  classical
  by_cases hμν : μ ≪ ν
  · have hcomp : μ ⊗ₘ κ ≪ ν ⊗ₘ κ := hμν.compProd_left κ
    rw [_root_.InformationTheory.klDiv_eq_lintegral_klFun,
      _root_.InformationTheory.klDiv_eq_lintegral_klFun, if_pos hcomp, if_pos hμν]
    calc
      _ = ∫⁻ p : α × β,
          ENNReal.ofReal (_root_.InformationTheory.klFun ((μ.rnDeriv ν p.1).toReal))
            ∂(ν ⊗ₘ κ) := by
        refine lintegral_congr_ae ?_
        filter_upwards [ProbabilityTheory.rnDeriv_measure_compProd_left μ ν κ] with p hp
        rw [hp]
      _ = _ := by
        rw [Measure.lintegral_compProd]
        · simp
        · fun_prop
  · have hcomp : ¬ μ ⊗ₘ κ ≪ ν ⊗ₘ κ := fun hac ↦
      hμν (Measure.absolutelyContinuous_of_compProd hac)
    rw [_root_.InformationTheory.klDiv_of_not_ac hcomp,
      _root_.InformationTheory.klDiv_of_not_ac hμν]

/-- Passing [two finite input laws `μ` and `ν`](hyp:μ,ν) through [the same randomized
observation channel `κ`](hyp:κ), [the Kullback–Leibler divergence between the channel's
output laws is no larger than the divergence between the original input laws, including when
the channel is non-injective or the original divergence is infinite](goal). -/
theorem klDiv_bind_le (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ : Kernel α β) [IsMarkovKernel κ] :
    _root_.InformationTheory.klDiv (μ.bind κ) (ν.bind κ)
      ≤ _root_.InformationTheory.klDiv μ ν := by
  rw [← Measure.snd_compProd μ κ, ← Measure.snd_compProd ν κ]
  exact (klDiv_map_le (μ := μ ⊗ₘ κ) (ν := ν ⊗ₘ κ) measurable_snd).trans_eq
    (klDiv_compProd_left μ ν κ)

/-- Passing two probability laws through a shared Markov channel cannot increase their
Kullback--Leibler divergence; this is the probability-law specialization of the
finite-measure data-processing inequality. -/
theorem klDiv_bind_le_of_isProbabilityMeasure (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (κ : Kernel α β) [IsMarkovKernel κ] :
    _root_.InformationTheory.klDiv (μ.bind κ) (ν.bind κ)
      ≤ _root_.InformationTheory.klDiv μ ν := by
  exact klDiv_bind_le μ ν κ

end Measure


end Causalean.Mathlib.InformationTheory
