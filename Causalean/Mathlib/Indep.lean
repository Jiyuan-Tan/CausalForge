/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Mathlib-adjacent helpers for `IndepFun` / `CondIndepFun`

Generic facts about independence and conditional independence that are candidates
for upstream inclusion in Mathlib.  Consumed by `Causalean.SCM.Do.LocalMarkov` to
discharge the latent-root branch of the local Markov property.

## Main results

* `indepFun_pi_of_disjoint` — coordinate-tuple projections at disjoint `Finset`s
  are `IndepFun` under `Measure.pi`.  Follows from `iIndepFun_pi` and
  `iIndepFun.indepFun_finset`.
* `condIndepFun_pi_of_inter_subset` — under a finite product measure, the tuple
  on `S` is conditionally independent of the tuple on `T` given the tuple on
  `U` whenever `S ∩ T ⊆ U`.
* `comap_eq_bot_of_subsingleton` — the comap σ-algebra of a subsingleton-valued
  function is the trivial σ-algebra `⊥`.
* `condIndepFun_of_indepFun_of_le_bot` — `IndepFun f g μ` lifts to
  `CondIndepFun m' hm' f g μ` whenever `m' ≤ ⊥` (conditioning σ-algebra trivial)
  and `μ` is a probability measure.
-/

import Mathlib.Probability.Independence.Conditional
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Causalean.Mathlib.CondIndep.CondExp

/-! # Independence Helpers for Product Coordinates

This file develops generic independence and conditional-independence facts for
finite coordinate projections under product measures. The results are
Mathlib-adjacent and do not depend on any causal-model definitions; downstream
local-Markov arguments use them as product-measure plumbing.

Main coordinate maps:
* `finsetCoordProj S` projects a dependent product to the coordinates indexed by
  a finite set `S`.
* `finsetCoordProjFromCondResidual S U` reassembles the coordinates on `S` from
  the conditioning block `U` and the residual block `S \ U`.
* `finsetCoordProjPairFromUnion A B` extracts the `A` and `B` sub-blocks from
  their union.

Main results:
* `indepFun_pi_of_disjoint` proves independence of disjoint coordinate blocks
  under a finite product measure.
* `condIndepFun_bot_of_indepFun` lifts ordinary independence to conditional
  independence given the trivial σ-algebra.
* `condIndepFun_pi_cond_residual_of_disjoint` gives conditional independence of
  two residual coordinate blocks after conditioning on a common block.
* `condIndepFun_pi_of_inter_subset` is the public finite-product criterion:
  coordinate blocks on `S` and `T` are conditionally independent given `U` when
  `S ∩ T ⊆ U`.
* `comap_eq_bot_of_subsingleton`, `indepFun_of_map`, and
  `condIndepFun_of_indepFun_indep` provide small σ-algebra and pushforward
  bridges used around the product-coordinate statements. -/

namespace Causalean

open MeasureTheory ProbabilityTheory

-- ============================================================
-- § 1. IndepFun under Measure.pi at disjoint coordinate blocks
-- ============================================================

/-- Coordinate-tuple projections at disjoint `Finset`s are `IndepFun` under
    `Measure.pi` of a family of probability measures.  This is the binary
    aggregation of `iIndepFun_pi` via `iIndepFun.indepFun_finset`. -/
theorem indepFun_pi_of_disjoint
    {ι : Type*} [Fintype ι]
    {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    (μ : (i : ι) → Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    {S T : Finset ι} (hST : Disjoint S T) :
    IndepFun (fun (x : ∀ i, Ω i) (i : {i // i ∈ S}) => x i.val)
             (fun (x : ∀ i, Ω i) (i : {i // i ∈ T}) => x i.val)
             (Measure.pi μ) := by
  have hiindep : iIndepFun (fun (i : ι) (ω : ∀ j, Ω j) => ω i) (Measure.pi μ) :=
    iIndepFun_pi (X := fun _ (ω : Ω _) => ω) (fun _ => aemeasurable_id)
  exact hiindep.indepFun_finset S T hST (fun i => measurable_pi_apply i)

/-- Tuple projection to a finite coordinate block of a dependent product. -/
def finsetCoordProj
    {ι : Type*} [DecidableEq ι] [Fintype ι]
    {Ω : ι → Type*} (S : Finset ι) :
    (∀ i, Ω i) → ((i : {i // i ∈ S}) → Ω i.val) :=
  fun x i => x i.val

/-- `finsetCoordProj` is measurable. -/
theorem measurable_finsetCoordProj
    {ι : Type*} [DecidableEq ι] [Fintype ι]
    {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)] (S : Finset ι) :
    Measurable (finsetCoordProj (Ω := Ω) S) := by
  refine measurable_pi_lambda _ ?_
  intro i
  exact measurable_pi_apply i.val

/-- Reassemble coordinates on `S` from coordinates on `U` and on the residual
    block `S \ U`. -/
def finsetCoordProjFromCondResidual
    {ι : Type*} [DecidableEq ι] [Fintype ι]
    {Ω : ι → Type*} (S U : Finset ι) :
    (((i : {i // i ∈ U}) → Ω i.val) ×
      ((i : {i // i ∈ S \ U}) → Ω i.val)) →
      ((i : {i // i ∈ S}) → Ω i.val) :=
  fun x i =>
    if hiU : i.val ∈ U then
      x.1 ⟨i.val, hiU⟩
    else
      x.2 ⟨i.val, Finset.mem_sdiff.mpr ⟨i.property, hiU⟩⟩

/-- The residual reassembly map is measurable. -/
theorem measurable_finsetCoordProjFromCondResidual
    {ι : Type*} [DecidableEq ι] [Fintype ι]
    {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)] (S U : Finset ι) :
    Measurable (finsetCoordProjFromCondResidual (Ω := Ω) S U) := by
  refine measurable_pi_lambda _ ?_
  intro i
  dsimp [finsetCoordProjFromCondResidual]
  by_cases hiU : i.val ∈ U
  · let j : {j // j ∈ U} := ⟨i.val, hiU⟩
    simpa [hiU, j] using (measurable_pi_apply j).comp measurable_fst
  · let j : {j // j ∈ S \ U} := ⟨i.val, Finset.mem_sdiff.mpr ⟨i.property, hiU⟩⟩
    simpa [hiU, j] using (measurable_pi_apply j).comp measurable_snd

/-- Reassembling `π_U` with the residual projection `π_{S \ U}` gives `π_S`. -/
theorem finsetCoordProjFromCondResidual_comp
    {ι : Type*} [DecidableEq ι] [Fintype ι]
    {Ω : ι → Type*} (S U : Finset ι) :
    finsetCoordProjFromCondResidual (Ω := Ω) S U ∘
      (fun x => (finsetCoordProj (Ω := Ω) U x, finsetCoordProj (Ω := Ω) (S \ U) x))
      = finsetCoordProj (Ω := Ω) S := by
  funext x i
  dsimp [finsetCoordProjFromCondResidual, finsetCoordProj]
  by_cases hiU : i.val ∈ U <;> simp [hiU]

/-- Extract two sub-blocks from the tuple on their union. -/
def finsetCoordProjPairFromUnion
    {ι : Type*} [DecidableEq ι] [Fintype ι]
    {Ω : ι → Type*} (A B : Finset ι) :
    (((i : {i // i ∈ A ∪ B}) → Ω i.val) →
      ((i : {i // i ∈ A}) → Ω i.val) × ((i : {i // i ∈ B}) → Ω i.val)) :=
  fun x =>
    (fun i => x ⟨i.val, Finset.mem_union.mpr (Or.inl i.property)⟩,
     fun i => x ⟨i.val, Finset.mem_union.mpr (Or.inr i.property)⟩)

/-- The union sub-block extraction map is measurable. -/
theorem measurable_finsetCoordProjPairFromUnion
    {ι : Type*} [DecidableEq ι] [Fintype ι]
    {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)] (A B : Finset ι) :
    Measurable (finsetCoordProjPairFromUnion (Ω := Ω) A B) := by
  refine (measurable_pi_lambda _ ?_).prod (measurable_pi_lambda _ ?_)
  · intro i
    exact measurable_pi_apply
      (⟨i.val, Finset.mem_union.mpr (Or.inl i.property)⟩ :
        {j // j ∈ A ∪ B})
  · intro i
    exact measurable_pi_apply
      (⟨i.val, Finset.mem_union.mpr (Or.inr i.property)⟩ :
        {j // j ∈ A ∪ B})

/-- Projecting to `A ∪ B` and then extracting the two sub-blocks gives the
    pair of direct projections to `A` and `B`. -/
theorem finsetCoordProjPairFromUnion_comp
    {ι : Type*} [DecidableEq ι] [Fintype ι]
    {Ω : ι → Type*} (A B : Finset ι) :
    finsetCoordProjPairFromUnion (Ω := Ω) A B ∘
      finsetCoordProj (Ω := Ω) (A ∪ B)
      = fun x => (finsetCoordProj (Ω := Ω) A x,
          finsetCoordProj (Ω := Ω) B x) := by
  funext x
  ext i <;> rfl

/-- Bridge: if `μ` is a probability measure on a standard Borel space `Ω`, then
    unconditional `IndepFun f g μ` lifts to `CondIndepFun ⊥ bot_le f g μ` —
    conditional independence given the trivial σ-algebra.

    Proof via `condIndepFun_iff_condExp_inter_preimage_eq_mul` + `condExp_bot`:
    the conditional expectation of an indicator against the trivial σ-algebra
    collapses to the expectation (the measure of the set), so the conditional
    factorization reduces to the unconditional one. -/
theorem condIndepFun_bot_of_indepFun
    {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    {f : Ω → β} {g : Ω → γ} (hf : Measurable f) (hg : Measurable g)
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (h : IndepFun f g μ) :
    CondIndepFun ⊥ bot_le f g μ := by
  rw [condIndepFun_iff_condExp_inter_preimage_eq_mul hf hg]
  intro s t hs ht
  have hfs : MeasurableSet (f ⁻¹' s) := hf hs
  have hgt : MeasurableSet (g ⁻¹' t) := hg ht
  have hfgst : MeasurableSet (f ⁻¹' s ∩ g ⁻¹' t) := hfs.inter hgt
  have hmst : μ (f ⁻¹' s ∩ g ⁻¹' t) = μ (f ⁻¹' s) * μ (g ⁻¹' t) :=
    h.measure_inter_preimage_eq_mul s t hs ht
  change condExp ⊥ μ (Set.indicator (f ⁻¹' s ∩ g ⁻¹' t) (1 : Ω → ℝ))
    =ᵐ[μ] fun ω =>
      condExp ⊥ μ (Set.indicator (f ⁻¹' s) (1 : Ω → ℝ)) ω
      * condExp ⊥ μ (Set.indicator (g ⁻¹' t) (1 : Ω → ℝ)) ω
  rw [condExp_bot (μ := μ) _, condExp_bot (μ := μ) _, condExp_bot (μ := μ) _]
  refine Filter.Eventually.of_forall fun _ => ?_
  simp only [integral_indicator_one hfgst, integral_indicator_one hfs,
             integral_indicator_one hgt, measureReal_def]
  rw [hmst, ENNReal.toReal_mul]

/-- Finite product residual-block conditional independence.

    This is the missing Mathlib-style product disintegration fact: under a
    finite product probability measure, after conditioning on `π_U`, the
    residual coordinate block `S0` is conditionally independent of `T0` when
    both residual blocks are disjoint from `U` and from each other. -/
theorem condIndepFun_pi_cond_residual_of_disjoint
    {ι : Type*} [DecidableEq ι] [Fintype ι]
    {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)] [∀ i, StandardBorelSpace (Ω i)]
    (μ : (i : ι) → Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    {S0 T0 U : Finset ι} (hS0T0 : Disjoint S0 T0)
    (hS0U : Disjoint S0 U) :
    CondIndepFun
      (MeasurableSpace.comap (finsetCoordProj (Ω := Ω) U) inferInstance)
      (Measurable.comap_le (measurable_finsetCoordProj (Ω := Ω) U))
      (fun x => (finsetCoordProj (Ω := Ω) U x, finsetCoordProj (Ω := Ω) S0 x))
      (fun x => (finsetCoordProj (Ω := Ω) U x, finsetCoordProj (Ω := Ω) T0 x))
      (Measure.pi μ) := by
  classical
  have hS0T0U : Disjoint S0 (T0 ∪ U) := by
    rw [Finset.disjoint_left]
    intro i hiS0 hiT0U
    rcases Finset.mem_union.mp hiT0U with hiT0 | hiU
    · exact (Finset.disjoint_left.mp hS0T0) hiS0 hiT0
    · exact (Finset.disjoint_left.mp hS0U) hiS0 hiU
  have hindep :
      IndepFun
        (finsetCoordProj (Ω := Ω) S0)
        (finsetCoordProj (Ω := Ω) (T0 ∪ U))
        (Measure.pi μ) :=
    indepFun_pi_of_disjoint (Ω := Ω) μ hS0T0U
  have hindep_pair :
      IndepFun
        (finsetCoordProj (Ω := Ω) S0)
        (fun x => (finsetCoordProj (Ω := Ω) T0 x,
          finsetCoordProj (Ω := Ω) U x))
        (Measure.pi μ) := by
    simpa [finsetCoordProjPairFromUnion_comp] using
      hindep.comp measurable_id
        (measurable_finsetCoordProjPairFromUnion (Ω := Ω) T0 U)
  have hbot :
      CondIndepFun ⊥ bot_le
        (finsetCoordProj (Ω := Ω) S0)
        (fun x => (finsetCoordProj (Ω := Ω) T0 x,
          finsetCoordProj (Ω := Ω) U x))
        (Measure.pi μ) :=
    condIndepFun_bot_of_indepFun
      (measurable_finsetCoordProj (Ω := Ω) S0)
      ((measurable_finsetCoordProj (Ω := Ω) T0).prod
        (measurable_finsetCoordProj (Ω := Ω) U))
      hindep_pair
  have hbase :
      CondIndepFun
        (MeasurableSpace.comap (finsetCoordProj (Ω := Ω) U) inferInstance)
        (Measurable.comap_le (measurable_finsetCoordProj (Ω := Ω) U))
        (finsetCoordProj (Ω := Ω) S0)
        (finsetCoordProj (Ω := Ω) T0)
        (Measure.pi μ) := by
    simpa [sup_bot_eq] using
      (condIndepFun_weak_union_of_prodMk
        (Ω := (i : ι) → Ω i)
        (m := ⊥)
        (mΩ := inferInstance)
        (μ := Measure.pi μ)
        bot_le
        (W := finsetCoordProj (Ω := Ω) S0)
        (V := finsetCoordProj (Ω := Ω) T0)
        (A := finsetCoordProj (Ω := Ω) U)
        (measurable_finsetCoordProj (Ω := Ω) S0)
        (measurable_finsetCoordProj (Ω := Ω) T0)
        (measurable_finsetCoordProj (Ω := Ω) U)
        hbot)
  have hleft :
      CondIndepFun
        (MeasurableSpace.comap (finsetCoordProj (Ω := Ω) U) inferInstance)
        (Measurable.comap_le (measurable_finsetCoordProj (Ω := Ω) U))
        (fun x => (finsetCoordProj (Ω := Ω) S0 x,
          finsetCoordProj (Ω := Ω) U x))
        (finsetCoordProj (Ω := Ω) T0)
        (Measure.pi μ) :=
    condIndepFun_prodMk_of_measurable_left
      (m := MeasurableSpace.comap (finsetCoordProj (Ω := Ω) U) inferInstance)
      (mΩ := inferInstance)
      (μ := Measure.pi μ)
      (Measurable.comap_le (measurable_finsetCoordProj (Ω := Ω) U))
      (measurable_finsetCoordProj (Ω := Ω) S0)
      (measurable_finsetCoordProj (Ω := Ω) T0)
      (measurable_finsetCoordProj (Ω := Ω) U)
      (comap_measurable (finsetCoordProj (Ω := Ω) U))
      hbase
  have hright :
      CondIndepFun
        (MeasurableSpace.comap (finsetCoordProj (Ω := Ω) U) inferInstance)
        (Measurable.comap_le (measurable_finsetCoordProj (Ω := Ω) U))
        (fun x => (finsetCoordProj (Ω := Ω) T0 x,
          finsetCoordProj (Ω := Ω) U x))
        (fun x => (finsetCoordProj (Ω := Ω) S0 x,
          finsetCoordProj (Ω := Ω) U x))
        (Measure.pi μ) :=
    condIndepFun_prodMk_of_measurable_left
      (m := MeasurableSpace.comap (finsetCoordProj (Ω := Ω) U) inferInstance)
      (mΩ := inferInstance)
      (μ := Measure.pi μ)
      (Measurable.comap_le (measurable_finsetCoordProj (Ω := Ω) U))
      (measurable_finsetCoordProj (Ω := Ω) T0)
      ((measurable_finsetCoordProj (Ω := Ω) S0).prod
        (measurable_finsetCoordProj (Ω := Ω) U))
      (measurable_finsetCoordProj (Ω := Ω) U)
      (comap_measurable (finsetCoordProj (Ω := Ω) U))
      hleft.symm
  have hswapS :
      Measurable
        (fun p : (((i : {i // i ∈ S0}) → Ω i.val) ×
            ((i : {i // i ∈ U}) → Ω i.val)) => (p.2, p.1)) :=
    measurable_snd.prod measurable_fst
  have hswapT :
      Measurable
        (fun p : (((i : {i // i ∈ T0}) → Ω i.val) ×
            ((i : {i // i ∈ U}) → Ω i.val)) => (p.2, p.1)) :=
    measurable_snd.prod measurable_fst
  exact hright.symm.comp hswapS hswapT

/-- Under a finite product measure, the tuple on `S` is conditionally
    independent of the tuple on `T` given the tuple on `U` whenever the overlap
    `S ∩ T` is absorbed by the conditioning block `U`.

    Intended downstream use: factor two coordinate families through ancestor
    blocks, then apply this lemma on the latent product measure once the common
    latent support is shown to lie inside the conditioning support.

    The proof reduces to `condIndepFun_pi_cond_residual_of_disjoint`, the
    focused finite-product disintegration fact isolated just above. -/
theorem condIndepFun_pi_of_inter_subset
    {ι : Type*} [DecidableEq ι] [Fintype ι]
    {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)] [∀ i, StandardBorelSpace (Ω i)]
    (μ : (i : ι) → Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    {S T U : Finset ι} (hSTU : S ∩ T ⊆ U) :
    CondIndepFun
      (MeasurableSpace.comap (finsetCoordProj (Ω := Ω) U) inferInstance)
      (Measurable.comap_le (measurable_finsetCoordProj (Ω := Ω) U))
      (finsetCoordProj (Ω := Ω) S)
      (finsetCoordProj (Ω := Ω) T)
      (Measure.pi μ) := by
  classical
  let S0 : Finset ι := S \ U
  let T0 : Finset ι := T \ U
  have hS0T0 : Disjoint S0 T0 := by
    rw [Finset.disjoint_left]
    intro i hiS0 hiT0
    change i ∈ S \ U at hiS0
    change i ∈ T \ U at hiT0
    rw [Finset.mem_sdiff] at hiS0
    rw [Finset.mem_sdiff] at hiT0
    exact hiT0.2 (hSTU (Finset.mem_inter.mpr ⟨hiS0.1, hiT0.1⟩))
  have hS0U : Disjoint S0 U := by
    rw [Finset.disjoint_left]
    intro i hiS0 hiU
    change i ∈ S \ U at hiS0
    rw [Finset.mem_sdiff] at hiS0
    exact hiS0.2 hiU
  have hT0U : Disjoint T0 U := by
    rw [Finset.disjoint_left]
    intro i hiT0 hiU
    change i ∈ T \ U at hiT0
    rw [Finset.mem_sdiff] at hiT0
    exact hiT0.2 hiU
  have hbase :
      CondIndepFun
        (MeasurableSpace.comap (finsetCoordProj (Ω := Ω) U) inferInstance)
        (Measurable.comap_le (measurable_finsetCoordProj (Ω := Ω) U))
        (fun x => (finsetCoordProj (Ω := Ω) U x, finsetCoordProj (Ω := Ω) S0 x))
        (fun x => (finsetCoordProj (Ω := Ω) U x, finsetCoordProj (Ω := Ω) T0 x))
        (Measure.pi μ) :=
    condIndepFun_pi_cond_residual_of_disjoint (Ω := Ω) μ hS0T0 hS0U
  have h := hbase.comp
    (measurable_finsetCoordProjFromCondResidual (Ω := Ω) S U)
    (measurable_finsetCoordProjFromCondResidual (Ω := Ω) T U)
  simpa [S0, T0, finsetCoordProjFromCondResidual_comp] using h

-- ============================================================
-- § 2. Trivial-conditioning bridge from IndepFun to CondIndepFun
-- ============================================================

/-- The comap σ-algebra of a function into a `Subsingleton` codomain is the
    trivial σ-algebra `⊥`.  Every measurable set in the codomain is either
    empty or the full space, so every preimage is either `∅` or `univ`. -/
theorem comap_eq_bot_of_subsingleton
    {α β : Type*} [MeasurableSpace β] [Subsingleton β] (f : α → β) :
    MeasurableSpace.comap f inferInstance = (⊥ : MeasurableSpace α) := by
  refine le_antisymm ?_ bot_le
  rintro s ⟨t, _, rfl⟩
  rcases t.eq_empty_or_nonempty with ht | ⟨x, hx⟩
  · rw [ht, Set.preimage_empty]
    exact (MeasurableSpace.measurableSet_bot_iff).mpr (Or.inl rfl)
  · have hpre : f ⁻¹' t = Set.univ := by
      ext ω
      refine ⟨fun _ => trivial, fun _ => ?_⟩
      have : f ω = x := Subsingleton.elim _ _
      simp only [Set.mem_preimage, this, hx]
    rw [hpre]
    exact (MeasurableSpace.measurableSet_bot_iff).mpr (Or.inr rfl)

-- ============================================================
-- § 3. Pushforward bridge for IndepFun
-- ============================================================

/-- Pushforward bridge for `IndepFun`: if `X ∘ φ ⟂ᵢ Y ∘ φ` under `ν`, then
    `X ⟂ᵢ Y` under `ν.map φ`.  Analogue of `LocalMarkov.condIndepFun_of_map`
    at the `IndepFun` level. -/
theorem indepFun_of_map
    {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSpace δ]
    {ν : Measure α} {φ : α → β} (hφ : AEMeasurable φ ν)
    {X : β → γ} (hX : Measurable X) {Y : β → δ} (hY : Measurable Y)
    (h : IndepFun (X ∘ φ) (Y ∘ φ) ν) :
    IndepFun X Y (ν.map φ) := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul] at h ⊢
  intro s t hs ht
  rw [Measure.map_apply_of_aemeasurable hφ ((hX hs).inter (hY ht)),
      Measure.map_apply_of_aemeasurable hφ (hX hs),
      Measure.map_apply_of_aemeasurable hφ (hY ht)]
  have := h s t hs ht
  simp only [Set.preimage_comp] at this
  exact this

-- ============================================================
-- § 4. Conditional independence given a function of an independent block
-- ============================================================

/-- If `X` and `Y` are independent, and the joint `(X, Y)` is independent of the
    conditioning variable `Z`, then `X` and `Y` are conditionally independent
    given the σ-algebra generated by `Z`.

    Reason: because `(X, Y)` is independent of `Z`, conditioning on `σ(Z)` does
    not change the (joint or marginal) law of preimages of `X` and `Y`; the
    relevant conditional expectations collapse to their unconditional means via
    `condExp_indep_eq`, and the factorization then follows from the
    unconditional independence of `X` and `Y`. -/
theorem condIndepFun_of_indepFun_indep
    {Ω β γ δ : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → β} {Y : Ω → γ} {Z : Ω → δ}
    (hX : Measurable X) (hY : Measurable Y) (_hZ : Measurable Z)
    (hXY : IndepFun X Y μ)
    (hindep : Indep (MeasurableSpace.comap (fun ω => (X ω, Y ω)) inferInstance)
        (MeasurableSpace.comap Z inferInstance) μ) :
    CondIndepFun (MeasurableSpace.comap Z inferInstance) _hZ.comap_le X Y μ := by
  have hle₂ : MeasurableSpace.comap Z inferInstance ≤ (inferInstance : MeasurableSpace Ω) :=
    _hZ.comap_le
  have hXYmeas : Measurable (fun ω => (X ω, Y ω)) := hX.prod hY
  have hle₁ : MeasurableSpace.comap (fun ω => (X ω, Y ω)) inferInstance ≤
      (inferInstance : MeasurableSpace Ω) := hXYmeas.comap_le
  rw [condIndepFun_iff_condExp_inter_preimage_eq_mul hX hY]
  intro s t hs ht
  have hAs : MeasurableSet[MeasurableSpace.comap (fun ω => (X ω, Y ω)) inferInstance]
      (X ⁻¹' s) := by
    refine ⟨(s ×ˢ Set.univ : Set (β × γ)), hs.prod MeasurableSet.univ, ?_⟩
    ext ω; simp
  have hAt : MeasurableSet[MeasurableSpace.comap (fun ω => (X ω, Y ω)) inferInstance]
      (Y ⁻¹' t) := by
    refine ⟨(Set.univ ×ˢ t : Set (β × γ)), MeasurableSet.univ.prod ht, ?_⟩
    ext ω; simp
  have hAst := hAs.inter hAt
  have hconst : ∀ {A : Set Ω},
      MeasurableSet[MeasurableSpace.comap (fun ω => (X ω, Y ω)) inferInstance] A →
      (μ⟦A | MeasurableSpace.comap Z inferInstance⟧) =ᵐ[μ] fun _ => (μ A).toReal := by
    intro A hA
    have hsm : StronglyMeasurable[MeasurableSpace.comap (fun ω => (X ω, Y ω)) inferInstance]
        (A.indicator (fun _ : Ω => (1 : ℝ))) :=
      stronglyMeasurable_const.indicator hA
    have hmain := condExp_indep_eq hle₁ hle₂ hsm hindep
    refine hmain.trans ?_
    refine Filter.Eventually.of_forall fun ω => ?_
    have hAmeas : MeasurableSet A := hle₁ _ hA
    simp only []
    rw [show (A.indicator (fun _ : Ω => (1 : ℝ))) = A.indicator 1 from rfl,
      integral_indicator_one hAmeas, measureReal_def]
  have h1 := hconst hAst
  have h2 := hconst hAs
  have h3 := hconst hAt
  have hmul := hXY.measure_inter_preimage_eq_mul s t hs ht
  filter_upwards [h1, h2, h3] with ω e1 e2 e3
  rw [e1, e2, e3, hmul, ENNReal.toReal_mul]

end Causalean
