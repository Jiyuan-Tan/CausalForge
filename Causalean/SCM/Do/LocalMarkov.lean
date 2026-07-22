/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.SCM.Do.FullCondIndep
import Causalean.SCM.Model.EvalFactorization
import Causalean.SCM.Model.EvalLatent
import Causalean.Mathlib.Indep

/-! # Full Local Markov Property

This file proves that each observed variable in a structural causal model is
conditionally independent of its non-descendants, given all of its parents, under
the full joint distribution over observed and latent variables. It also proves
the latent-root analogue and records the pushforward bridge used to move
conditional independence through the evaluation map.

The main public results are:

* `SCM.condIndepFun_of_map`, which transports conditional independence through a
  measurable pushforward.
* `SCM.full_local_markov`, the observed-node local Markov property for
  `jointKernel`.
* `SCM.full_local_markov_latent`, the corresponding independence statement for
  latent root nodes.
-/

namespace Causalean

open scoped MeasureTheory ProbabilityTheory

namespace SCM

universe uN uΩ

variable {N : Type uN} [DecidableEq N] [Fintype N]
variable {Ω : N → Type uΩ} [∀ n, MeasurableSpace (Ω n)]

-- ============================================================
-- § 1. Basic containment
-- ============================================================

/-- Observed nodes lie in randomVars. -/
theorem observed_subset_randomVars (M : Causalean.SCM N Ω) :
    M.observed ⊆ M.randomVars :=
  Finset.subset_union_left

-- ============================================================
-- § 2. Pushforward bridge for CondIndepFun
-- ============================================================

/-- **Pushforward bridge for CondIndepFun.**

    If `X ∘ φ`, `Y ∘ φ`, `Z ∘ φ` satisfy conditional independence under `ν`,
    then `X`, `Y`, `Z` satisfy conditional independence under `ν.map φ`.

    **Proof**: Use the `condDistrib` characterization of conditional independence
    (`condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight`). Since `condDistrib`
    is `(μ.map (X, Y)).condKernel`, precomposing both arguments by `φ` commutes
    with `condDistrib` via `Measure.map_map`. -/
theorem condIndepFun_of_map
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α]
    {β : Type*} [MeasurableSpace β] [StandardBorelSpace β]
    {γ : Type*} [MeasurableSpace γ] [StandardBorelSpace γ] [Nonempty γ]
    {δ : Type*} [MeasurableSpace δ] [StandardBorelSpace δ] [Nonempty δ]
    {ε : Type*} [MeasurableSpace ε]
    {φ : α → β} (hφ : Measurable φ)
    {X : β → γ} (hX : Measurable X)
    {Y : β → δ} (hY : Measurable Y)
    {Z : β → ε} (hZ : Measurable Z)
    {ν : MeasureTheory.Measure α} [MeasureTheory.IsFiniteMeasure ν]
    [MeasureTheory.IsFiniteMeasure (ν.map φ)]
    (h : ProbabilityTheory.CondIndepFun
      (MeasurableSpace.comap (Z ∘ φ) inferInstance)
      (Measurable.comap_le (hZ.comp hφ))
      (X ∘ φ) (Y ∘ φ) ν) :
    ProbabilityTheory.CondIndepFun
      (MeasurableSpace.comap Z inferInstance) (hZ.comap_le)
      X Y (ν.map φ) := by
  -- condDistrib commutes with precomposition by φ (via Measure.map_map)
  have hcd1 : ProbabilityTheory.condDistrib (Y ∘ φ) (Z ∘ φ) ν =
      ProbabilityTheory.condDistrib Y Z (ν.map φ) := by
    simp only [ProbabilityTheory.condDistrib]
    congr 1
    exact (MeasureTheory.Measure.map_map (hZ.prodMk hY) hφ).symm
  have hcd2 : ProbabilityTheory.condDistrib (Y ∘ φ)
        (fun ω ↦ ((Z ∘ φ) ω, (X ∘ φ) ω)) ν =
      ProbabilityTheory.condDistrib Y (fun b ↦ (Z b, X b)) (ν.map φ) := by
    simp only [ProbabilityTheory.condDistrib]
    congr 1
    exact (MeasureTheory.Measure.map_map ((hZ.prodMk hX).prodMk hY) hφ).symm
  have hfilt : ν.map (fun ω ↦ ((Z ∘ φ) ω, (X ∘ φ) ω)) =
      (ν.map φ).map (fun b ↦ (Z b, X b)) :=
    (MeasureTheory.Measure.map_map (hZ.prodMk hX) hφ).symm
  -- Use the condDistrib characterization of conditional independence
  rw [ProbabilityTheory.condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight hY hX hZ]
  have h' := (ProbabilityTheory.condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight
    (hY.comp hφ) (hX.comp hφ) (hZ.comp hφ)).mp h
  rw [hcd2, hcd1, hfilt] at h'
  exact h'

-- ============================================================
-- § 3. Full Local Markov Property
-- ============================================================

/-- **Full Local Markov Property.** Under the full joint distribution
    `jointKernel M s`, each observed variable `v` is conditionally independent
    of its non-descendants given ALL its parents (including latent ones).

    Since `v = f_v(pa(v))` is a deterministic function of its parents,
    conditioning on the parent coordinates makes the singleton projection at
    `v` measurable with respect to the conditioning sigma-algebra, hence
    conditionally independent of the non-descendant projection.

    **Proof strategy**: On `LatentValues M` (source of `evalMap`), the v-coordinate
    of `evalMap` is a measurable function of the Pa(v)-coordinates (by the structural
    equation). So `condIndepFun_of_measurable_left` from Mathlib gives CI in the
    source space. The `condIndepFun_of_map` bridge then transports to `RandomValues`.

    The old `local_markov` (conditioning on `Pa(v) ∩ V` only) was **incorrect**
    for gSCMs with shared latent confounders (e.g. U → V₁, U → V₂). -/
theorem full_local_markov (M : Causalean.SCM N Ω)
    [StandardBorelSpace M.RandomValues]
    [StandardBorelSpace M.LatentValues]
    [∀ s : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.jointKernel s)]
    (v : SWIGNode N) (hv : v ∈ M.observed)
    [StandardBorelSpace (ValuesOn ({v} : Finset (SWIGNode N)) (swigΩ Ω))]
    [Nonempty (ValuesOn ({v} : Finset (SWIGNode N)) (swigΩ Ω))]
    [StandardBorelSpace
      (ValuesOn (M.dag.nonDescendants v ∩ M.randomVars) (swigΩ Ω))]
    [Nonempty (ValuesOn (M.dag.nonDescendants v ∩ M.randomVars) (swigΩ Ω))]
    (s : M.FixedValues) :
    FullCondIndep M
      {v}
      (M.dag.nonDescendants v ∩ M.randomVars)
      (M.dag.parents v ∩ M.randomVars)
      (Finset.singleton_subset_iff.mpr (observed_subset_randomVars M hv))
      Finset.inter_subset_right
      Finset.inter_subset_right
      (M.jointKernel s) := by
  -- Outline:
  -- 1. `jointKernel M s = latentProduct.map (evalMap s)` (`jointKernel_apply_eq`).
  -- 2. `condIndepFun_of_map` with `φ = evalMap s` reduces the goal to CI on
  --    `LatentValues M` under `latentProduct`.
  -- 3. On `LatentValues`, `π_{{v}} ∘ evalMap s` factors through
  --    `π_{Pa(v) ∩ RV} ∘ evalMap s` via `evalMap_observed_unfold` (parent tuple
  --    of `structFun v` reads only from fixed values `s` and from parent-restricted
  --    random values), hence is measurable w.r.t. the conditioning σ-algebra.
  -- 4. `condIndepFun_of_measurable_left` closes the LatentValues-level CI.
  set hv_sub : ({v} : Finset (SWIGNode N)) ⊆ M.randomVars :=
    Finset.singleton_subset_iff.mpr (observed_subset_randomVars M hv) with hv_sub_def
  set hPa_sub : M.dag.parents v ∩ M.randomVars ⊆ M.randomVars :=
    Finset.inter_subset_right with hPa_sub_def
  set hND_sub : M.dag.nonDescendants v ∩ M.randomVars ⊆ M.randomVars :=
    Finset.inter_subset_right with hND_sub_def
  -- Step 1: identify jointKernel s with latentProduct.map (evalMap s).
  have hjk : M.jointKernel s = M.latentProduct.map (fun ℓ => M.evalMap s ℓ) :=
    M.jointKernel_apply_eq s
  have hφ_meas : Measurable (fun ℓ : M.LatentValues => M.evalMap s ℓ) := by
    have : (fun ℓ : M.LatentValues => M.evalMap s ℓ) =
        fun ℓ => Function.uncurry M.evalMap (s, ℓ) := rfl
    rw [this]
    exact M.evalMap_measurable.comp (Measurable.prodMk measurable_const measurable_id)
  haveI : MeasureTheory.IsFiniteMeasure (M.latentProduct.map (fun ℓ => M.evalMap s ℓ)) :=
    hjk ▸ (inferInstance : MeasureTheory.IsFiniteMeasure (M.jointKernel s))
  -- Step 2: build the LatentValues-level CI via `condIndepFun_of_measurable_left`.
  have hlat_ci :
      ProbabilityTheory.CondIndepFun
        (MeasurableSpace.comap (valuesProjection hPa_sub ∘ (fun ℓ => M.evalMap s ℓ))
          inferInstance)
        (Measurable.comap_le
          ((measurable_valuesProjection hPa_sub).comp hφ_meas))
        (valuesProjection hv_sub ∘ (fun ℓ => M.evalMap s ℓ))
        (valuesProjection hND_sub ∘ (fun ℓ => M.evalMap s ℓ))
        M.latentProduct := by
    refine ProbabilityTheory.condIndepFun_of_measurable_left ?_ ?_
    · -- `π_{{v}} ∘ evalMap s` factors through `π_{Pa(v) ∩ RV} ∘ evalMap s` via
      -- the parent-factorization lemma `evalMap_factors_through_parents`.
      obtain ⟨g, hg_meas, hg_eq⟩ := M.evalMap_factors_through_parents s v hv
      -- Wrap `g : ValuesOn (Pa ∩ RV) → swigΩ Ω v` into the singleton product
      -- `g' : ValuesOn (Pa ∩ RV) → ValuesOn {v} (swigΩ Ω)` via a `cast` on the
      -- unique coordinate `w.val = v`.
      let g' : ValuesOn (M.dag.parents v ∩ M.randomVars) (swigΩ Ω) →
               ValuesOn ({v} : Finset (SWIGNode N)) (swigΩ Ω) :=
        fun t w =>
          cast (congrArg (swigΩ Ω) (Finset.mem_singleton.mp w.property).symm) (g t)
      have hg'_meas : Measurable g' := by
        refine measurable_pi_lambda _ ?_
        rintro ⟨w, hw⟩
        have hwv : w = v := Finset.mem_singleton.mp hw
        subst hwv
        -- After `subst`, `Finset.mem_singleton.mp hw : v = v = rfl` by proof
        -- irrelevance; `cast rfl = id`, so the singleton-wrapped function at
        -- the v-coord is just `g`.
        exact hg_meas
      -- Pointwise factorization of `valuesProjection hv_sub ∘ evalMap s`.
      have hfactor :
          (valuesProjection hv_sub ∘ (fun ℓ => M.evalMap s ℓ)) =
            g' ∘ (valuesProjection hPa_sub ∘ (fun ℓ => M.evalMap s ℓ)) := by
        funext ℓ w
        rcases w with ⟨w, hw⟩
        have hwv : w = v := Finset.mem_singleton.mp hw
        subst hwv
        -- Both sides reduce: LHS = evalMap s ℓ ⟨v, hv_sub hw⟩, RHS unfolds
        -- `g'` and collapses the `cast` (proof-irrel on `v = v`).  The
        -- factorization equation `hg_eq ℓ` closes the goal (membership-proof
        -- irrelevance on the subtype witnesses).
        exact hg_eq ℓ
      rw [hfactor]
      -- `g' ∘ φ` is `comap φ`-measurable because `φ` is comap-measurable by
      -- definition of `comap` (preimages of measurables generate the σ-algebra).
      refine hg'_meas.comp ?_
      intro B hB
      exact ⟨B, hB, rfl⟩
    · -- `π_{NonDesc(v) ∩ RV} ∘ evalMap s` is measurable (projection ∘ measurable).
      exact (measurable_valuesProjection hND_sub).comp hφ_meas
  -- Step 3: transport to RandomValues under `latentProduct.map (evalMap s)`.
  have hrand_ci :
      ProbabilityTheory.CondIndepFun
        (MeasurableSpace.comap (valuesProjection hPa_sub) inferInstance)
        (comap_valuesProjection_le hPa_sub)
        (valuesProjection hv_sub) (valuesProjection hND_sub)
        (M.latentProduct.map (fun ℓ => M.evalMap s ℓ)) :=
    condIndepFun_of_map
      (φ := fun ℓ => M.evalMap s ℓ) hφ_meas
      (measurable_valuesProjection hv_sub)
      (measurable_valuesProjection hND_sub)
      (measurable_valuesProjection hPa_sub)
      hlat_ci
  -- Finish: rewrite `latentProduct.map (evalMap s)` as `jointKernel s`.
  unfold FullCondIndep
  convert hrand_ci using 2

-- ============================================================
-- § 4. Latent Local Markov Property
-- ============================================================

/-- **Latent Local Markov Property.** Under the full joint distribution
    `jointKernel M s`, each *latent* (unobserved) variable `a` is
    unconditionally independent of its non-descendants (among random nodes),
    i.e. conditionally independent given `∅`.

    This is the latent-root analogue of `full_local_markov`: since latents have
    no parents (`Pa(a) = ∅`), the conditioning set collapses to `∅` and we get
    an *unconditional* independence.  Intuition: `ℓ_a` is a root of the SCM's
    probabilistic structure (`latentProduct = Measure.pi latentDist`), so it is
    unconditionally independent of any coordinate family whose latent ancestors
    do not include `a` — which is exactly the case for `NonDesc(a) ∩ RV` by
    definition of non-descendants (`a ∉ Anc(v)` for `v ∈ NonDesc(a)`).

    **Proof strategy** (three steps, parallel to `full_local_markov`):
    1. **Reduction to LatentValues.** As before, identify `jointKernel s =
       latentProduct.map (evalMap s)` and apply `condIndepFun_of_map` to reduce
       the goal to a CI statement under `latentProduct`.
    2. **`evalMap` factorization at non-descendants.** Define a measurable
       `g : ValuesOn (Latents \ {a}) → ValuesOn (NonDesc(a) ∩ RV)` such that
       `π_{NonDesc(a) ∩ RV} ∘ evalMap s = g ∘ (latents-minus-a projection)`.
       For `v ∈ NonDesc(a) ∩ RV`:
       * if `v` unobserved (`v ≠ a` because `a ∉ NonDesc(a)`): `evalMap s ℓ v
         = ℓ_v`, depends on `ℓ_v` only.
       * if `v` observed: by `ancestralFactorization`, `evalMap s ℓ v` depends on
         `ℓ` only through `Anc(v) ∩ Unobserved`, which excludes `a` since
         `a ∉ Anc(v)` (as `v ∈ NonDesc(a)`).
    3. **Latent-level CI.**  At this point we have
         `π_{{a}} ∘ evalMap s = "read ℓ_a"` (by `evalMap_unobserved`), and
         `π_{NonDesc(a) ∩ RV} ∘ evalMap s = g ∘ "read ℓ_{Latents \ {a}}"`.
       Under `latentProduct = Measure.pi latentDist`, the coordinate projections
       at the disjoint index sets `{a}` and `Latents \ {a}` are independent
       (standard `Measure.pi` fact).  Therefore the two functions are
       `IndepFun` under `latentProduct`, which gives `CondIndepFun` with
       trivial conditioning (conditioning on `ValuesOn ∅`, whose σ-algebra is
       `{∅, univ}`).

    Used by the global Markov proof's latent-root branch via weak union and
    decomposition, specifically to reduce `{a} ⊥ Y | W` to the
    `W ⊆ NonDesc(a) ∩ RV` sub-case. -/
theorem full_local_markov_latent (M : Causalean.SCM N Ω)
    [StandardBorelSpace M.RandomValues]
    [StandardBorelSpace M.LatentValues]
    [∀ s : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.jointKernel s)]
    (a : SWIGNode N) (ha : a ∈ M.unobserved)
    [StandardBorelSpace (ValuesOn ({a} : Finset (SWIGNode N)) (swigΩ Ω))]
    [Nonempty (ValuesOn ({a} : Finset (SWIGNode N)) (swigΩ Ω))]
    [StandardBorelSpace
      (ValuesOn (M.dag.nonDescendants a ∩ M.randomVars) (swigΩ Ω))]
    [Nonempty (ValuesOn (M.dag.nonDescendants a ∩ M.randomVars) (swigΩ Ω))]
    (s : M.FixedValues) :
    FullCondIndep M
      {a}
      (M.dag.nonDescendants a ∩ M.randomVars)
      (∅ : Finset (SWIGNode N))
      (Finset.singleton_subset_iff.mpr (Finset.mem_union_right _ ha))
      Finset.inter_subset_right
      (Finset.empty_subset _)
      (M.jointKernel s) := by
  classical
  set hv_sub : ({a} : Finset (SWIGNode N)) ⊆ M.randomVars :=
    Finset.singleton_subset_iff.mpr (Finset.mem_union_right _ ha) with hv_sub_def
  set hND_sub : M.dag.nonDescendants a ∩ M.randomVars ⊆ M.randomVars :=
    Finset.inter_subset_right with hND_sub_def
  set hE : (∅ : Finset (SWIGNode N)) ⊆ M.randomVars := Finset.empty_subset _ with hE_def
  -- Step A: jointKernel s = latentProduct.map (evalMap s) and measurability of evalMap s.
  have hjk : M.jointKernel s = M.latentProduct.map (fun ℓ => M.evalMap s ℓ) :=
    M.jointKernel_apply_eq s
  have hφ_meas : Measurable (fun ℓ : M.LatentValues => M.evalMap s ℓ) := by
    have : (fun ℓ : M.LatentValues => M.evalMap s ℓ) =
        fun ℓ => Function.uncurry M.evalMap (s, ℓ) := rfl
    rw [this]
    exact M.evalMap_measurable.comp (Measurable.prodMk measurable_const measurable_id)
  -- Step B: jointKernel s is a probability measure (pushforward of Measure.pi of probability
  -- measures is probability).
  haveI hP_joint : MeasureTheory.IsProbabilityMeasure (M.jointKernel s) := by
    rw [hjk]
    exact MeasureTheory.Measure.isProbabilityMeasure_map hφ_meas.aemeasurable
  -- Step C: The conditioning σ-algebra collapses to ⊥ because the codomain
  -- `ValuesOn ∅ (swigΩ Ω)` is a subsingleton (empty index Finset).
  have h_subs :
      Subsingleton (ValuesOn (∅ : Finset (SWIGNode N)) (swigΩ Ω)) := by
    refine ⟨fun f g => ?_⟩
    funext ⟨w, hw⟩
    exact absurd hw (Finset.notMem_empty _)
  have h_bot :
      MeasurableSpace.comap (valuesProjection (Ω := swigΩ Ω) hE) inferInstance
        = (⊥ : MeasurableSpace M.RandomValues) :=
    @comap_eq_bot_of_subsingleton _ _ _ h_subs _
  -- Step D: Reduce the goal to `CondIndepFun ⊥ bot_le …`.  The conditioning
  -- σ-algebra `comap (valuesProjection hE) inferInstance` equals `⊥` (h_bot),
  -- so we prove the `⊥`-version and transport via `convert`.
  suffices h_ci : ProbabilityTheory.CondIndepFun
      (⊥ : MeasurableSpace M.RandomValues) bot_le
      (valuesProjection hv_sub) (valuesProjection hND_sub) (M.jointKernel s) by
    unfold FullCondIndep
    convert h_ci using 2
  apply condIndepFun_bot_of_indepFun
      (measurable_valuesProjection hv_sub)
      (measurable_valuesProjection hND_sub)
  -- Remaining: IndepFun (valuesProjection hv_sub) (valuesProjection hND_sub) (M.jointKernel s).
  -- Step E: rewrite jointKernel and reduce to IndepFun on latentProduct.
  rw [hjk]
  refine indepFun_of_map hφ_meas.aemeasurable
    (measurable_valuesProjection hv_sub)
    (measurable_valuesProjection hND_sub) ?_
  -- Step F: disjoint latent coordinate index sets.
  set A : {u // u ∈ M.unobserved} := ⟨a, ha⟩ with hA_def
  let S_idx : Finset {u // u ∈ M.unobserved} := {A}
  let T_idx : Finset {u // u ∈ M.unobserved} := Finset.univ.erase A
  have h_disj : Disjoint S_idx T_idx :=
    Finset.disjoint_singleton_left.mpr (Finset.notMem_erase _ _)
  -- Step G: LHS singleton wrap (mirrors the g' pattern in `full_local_markov`).
  let wrap_a :
      ((i : {i // i ∈ S_idx}) → swigΩ Ω i.val.val) →
        ValuesOn ({a} : Finset (SWIGNode N)) (swigΩ Ω) :=
    fun r w =>
      cast (congrArg (swigΩ Ω) (Finset.mem_singleton.mp w.property).symm)
        (r ⟨A, Finset.mem_singleton.mpr rfl⟩)
  have hwrap_meas : Measurable wrap_a := by
    refine measurable_pi_lambda _ ?_
    rintro ⟨w, hw⟩
    have hwv : w = a := Finset.mem_singleton.mp hw
    subst hwv
    exact measurable_pi_apply _
  have h_LHS :
      (valuesProjection hv_sub ∘ fun ℓ : M.LatentValues => M.evalMap s ℓ)
        = wrap_a ∘ fun ℓ : M.LatentValues =>
            fun i : {i // i ∈ S_idx} => ℓ i.val := by
    funext ℓ w
    rcases w with ⟨w, hw⟩
    have hwv : w = a := Finset.mem_singleton.mp hw
    subst hwv
    -- Note: `subst` substitutes `a := w` (not `w := a`), so within this
    -- block the theorem's `a`, `ha` are renamed to `w`, `ha`.  Both sides
    -- reduce to `ℓ ⟨w, ha⟩` via `evalMap_unobserved`; the `cast` in `wrap_a`
    -- collapses on `rfl` (proof-irrelevance on `w = w`).
    exact evalMap_unobserved M s ℓ ⟨w, hv_sub hw⟩ ha
  -- Step H: RHS factorization via the helper.
  have h_T_excl :
      ∀ v ∈ M.dag.nonDescendants a ∩ M.randomVars,
        ¬ M.dag.isAncestor a v ∧ v ≠ a := by
    intro v hv
    have hv_nd : v ∈ M.dag.nonDescendants a := (Finset.mem_inter.mp hv).1
    exact (Finset.mem_filter.mp hv_nd).2
  obtain ⟨g_T, hg_T_meas, hg_T_eq⟩ :=
    M.evalMap_factors_excluding_latent s a ha
      (M.dag.nonDescendants a ∩ M.randomVars) hND_sub h_T_excl
  have h_RHS :
      (valuesProjection hND_sub ∘ fun ℓ : M.LatentValues => M.evalMap s ℓ)
        = g_T ∘ fun ℓ : M.LatentValues =>
            fun i : {i // i ∈ T_idx} => ℓ i.val := by
    funext ℓ
    exact hg_T_eq ℓ
  -- Step I: base IndepFun from `indepFun_pi_of_disjoint` over disjoint
  -- latent index sets.
  haveI : ∀ i, MeasureTheory.IsProbabilityMeasure (M.latentDist i) :=
    M.isProbability_latent
  have h_base :
      ProbabilityTheory.IndepFun
        (fun (ℓ : M.LatentValues) (i : {i // i ∈ S_idx}) => ℓ i.val)
        (fun (ℓ : M.LatentValues) (i : {i // i ∈ T_idx}) => ℓ i.val)
        M.latentProduct := by
    change ProbabilityTheory.IndepFun _ _ (MeasureTheory.Measure.pi M.latentDist)
    exact indepFun_pi_of_disjoint M.latentDist h_disj
  -- Step J: post-compose via `IndepFun.comp` with `wrap_a`, `g_T`.
  rw [h_LHS, h_RHS]
  exact h_base.comp hwrap_meas hg_T_meas

end SCM

end Causalean
