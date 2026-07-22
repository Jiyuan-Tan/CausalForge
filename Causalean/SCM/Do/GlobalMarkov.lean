/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.SCM.Do.LocalMarkov
import Causalean.Graph.DSep.Ancestral
import Causalean.Graph.DSep.OrderedLocalSG

/-! # Full Global Markov Property

This file proves the full global Markov property: d-separation in the causal graph
implies conditional independence under the joint distribution over observed and
latent variables. The result is the full-distribution input from which the
observational Markov property is obtained by projection.

The main exported theorem is `SCM.full_globalMarkov`, with
`SCM.full_globalMarkov_with_fixed` providing the form used by do-calculus proofs
where fixed intervention nodes appear in the graphical conditioning set but only
random coordinates remain in the probabilistic conditioning set. The file also
exposes `SCM.reindexSubtypeProj` and
`SCM.indepFun_valuesProjection_latentProduct`, the product-measure independence
tools used internally by the Markov proof.
-/

namespace Causalean

open scoped MeasureTheory ProbabilityTheory

namespace SCM

universe uN uΩ

variable {N : Type uN} [DecidableEq N] [Fintype N]
variable {Ω : N → Type uΩ} [∀ n, MeasurableSpace (Ω n)]

private noncomputable def latentAncestorsOfSet (M : Causalean.SCM N Ω)
    (T : Finset (SWIGNode N)) : Finset (SWIGNode N) :=
  letI : DecidablePred
      (fun u : SWIGNode N => ∃ v ∈ T, u = v ∨ M.dag.isAncestor u v) :=
    Classical.decPred _
  M.unobserved.filter (fun u => ∃ v ∈ T, u = v ∨ M.dag.isAncestor u v)

private noncomputable def latentResidualOfSet (M : Causalean.SCM N Ω)
    (T W : Finset (SWIGNode N)) : Finset (SWIGNode N) :=
  M.latentAncestorsOfSet T \ M.latentAncestorsOfSet W

private lemma mem_latentAncestorsOfSet (M : Causalean.SCM N Ω)
    {T : Finset (SWIGNode N)} {u : SWIGNode N} :
    u ∈ M.latentAncestorsOfSet T ↔
      u ∈ M.unobserved ∧ ∃ v ∈ T, u = v ∨ M.dag.isAncestor u v := by
  letI : DecidablePred
      (fun u : SWIGNode N => ∃ v ∈ T, u = v ∨ M.dag.isAncestor u v) :=
    Classical.decPred _
  change u ∈ M.unobserved.filter _ ↔ _
  exact Finset.mem_filter

private lemma latentAncestorsOfSet_subset (M : Causalean.SCM N Ω)
    (T : Finset (SWIGNode N)) :
    M.latentAncestorsOfSet T ⊆ M.unobserved := by
  intro u hu
  exact (M.mem_latentAncestorsOfSet.mp hu).1

private lemma latentResidualOfSet_subset (M : Causalean.SCM N Ω)
    (T W : Finset (SWIGNode N)) :
    M.latentResidualOfSet T W ⊆ M.unobserved := by
  intro u hu
  exact M.latentAncestorsOfSet_subset T (Finset.mem_sdiff.mp hu).1

private lemma not_isAncestor_of_fixed_target (M : Causalean.SCM N Ω)
    {u d : SWIGNode N} (hd : d ∈ M.fixed) :
    ¬ M.dag.isAncestor u d := by
  intro hAnc
  cases hAnc with
  | edge hEdge =>
      have hPar : u ∈ M.dag.parents d := M.dag.mem_parents.mpr hEdge
      simpa [M.fixed_are_roots d hd] using hPar
  | trans _ hEdge =>
      have hPar : _ ∈ M.dag.parents d := M.dag.mem_parents.mpr hEdge
      simpa [M.fixed_are_roots d hd] using hPar

private theorem latentAncestorsOfSet_inter_subset_of_dSep_with_fixed
    (M : Causalean.SCM N Ω)
    (a : SWIGNode N) (Y W_rand W_fix : Finset (SWIGNode N))
    (hW_fix : W_fix ⊆ M.fixed)
    (hDisj_aY : Disjoint ({a} : Finset (SWIGNode N)) Y)
    (hdSep : M.dag.dSep {a} Y (W_rand ∪ W_fix)) :
    M.latentAncestorsOfSet ({a} : Finset (SWIGNode N)) ∩ M.latentAncestorsOfSet Y ⊆
      M.latentAncestorsOfSet W_rand := by
  intro u hu
  rcases Finset.mem_inter.mp hu with ⟨huA, huY⟩
  rcases M.mem_latentAncestorsOfSet.mp huA with ⟨hu_lat, vA, hvA, huA'⟩
  rcases M.mem_latentAncestorsOfSet.mp huY with ⟨_, vY, hvY, huY'⟩
  have huAncA : u ∈ M.dag.ancestralSet ({a} : Finset (SWIGNode N)) := by
    rcases huA' with rfl | hAnc
    · exact DAG.subset_ancestralSet M.dag _ (by simpa using hvA)
    · exact DAG.mem_ancestralSet_of_isAncestor M.dag (by simpa using hvA) hAnc
  have huAncY : u ∈ M.dag.ancestralSet Y := by
    rcases huY' with rfl | hAnc
    · exact DAG.subset_ancestralSet M.dag _ hvY
    · exact DAG.mem_ancestralSet_of_isAncestor M.dag hvY hAnc
  have huAncZW :
      u ∈ M.dag.ancestralSet (W_rand ∪ W_fix) := by
    exact DAG.ancestralSet_inter_subset_ancestralSet_of_dSep M.dag hdSep hDisj_aY
      (Finset.mem_inter.mpr ⟨huAncA, huAncY⟩)
  simp only [DAG.ancestralSet, Finset.mem_union, DAG.ancestorsSet,
    Finset.mem_filter, Finset.mem_univ, true_and] at huAncZW
  rcases huAncZW with huW | ⟨w, hwZW, huAncW⟩
  · rcases huW with hw_rand | hw_fix
    · exact (M.mem_latentAncestorsOfSet).mpr ⟨hu_lat, u, hw_rand, Or.inl rfl⟩
    · have hu_not_fixed : u ∉ M.fixed := by
        intro hu_fixed
        obtain ⟨n, hn⟩ := M.fixed_is_fixed u hu_fixed
        obtain ⟨m, hm⟩ := M.unobserved_is_random u hu_lat
        rw [hn] at hm
        cases hm
      exact (hu_not_fixed (hW_fix hw_fix)).elim
  · rcases hwZW with hw_rand | hw_fix
    · exact (M.mem_latentAncestorsOfSet).mpr ⟨hu_lat, w, hw_rand, Or.inr huAncW⟩
    · exact False.elim <| (M.not_isAncestor_of_fixed_target (hW_fix hw_fix)) huAncW

/-- For a node `w ∈ T`, the per-node latent ancestors of `w` are contained in the
    latent ancestors of the whole set `T`. -/
private lemma latentAncestorsOfNode_subset_latentAncestorsOfSet
    (M : Causalean.SCM N Ω) {T : Finset (SWIGNode N)} {w : SWIGNode N} (hw : w ∈ T) :
    M.latentAncestorsOfNode w ⊆ M.latentAncestorsOfSet T := by
  intro u hu
  rcases (M.mem_latentAncestorsOfNode).mp hu with ⟨hu_lat, hOr⟩
  exact (M.mem_latentAncestorsOfSet).mpr ⟨hu_lat, w, hw, hOr⟩

/-- Factor the `T`-projection of `evalMap s` through the latent support
    `latentAncestorsOfSet T`. The downstream use is `T = W_rand`, producing the
    measurable base map needed for the singleton-source global Markov proof. -/
private theorem evalMap_valuesProjection_factors_through_latentAncestorsOfSet
    (M : Causalean.SCM N Ω) [∀ n, Nonempty (Ω n)] (s : M.FixedValues)
    (T : Finset (SWIGNode N)) (hT : T ⊆ M.randomVars) :
    ∃ g : ValuesOn (M.latentAncestorsOfSet T) (swigΩ Ω) →
          ValuesOn T (swigΩ Ω),
      Measurable g ∧
      (valuesProjection hT ∘ fun ℓ : M.LatentValues => M.evalMap s ℓ) =
        g ∘ valuesProjection (Ω := swigΩ Ω) (M.latentAncestorsOfSet_subset T) := by
  classical
  -- For each `w ∈ T` that is observed, the per-node factorization data.
  -- `latentInT w hw : w ∈ latentAncestorsOfSet T` when `w ∈ unobserved` and `w ∈ T`.
  have latentInT : ∀ {w : SWIGNode N}, w ∈ T → w ∈ M.unobserved →
      w ∈ M.latentAncestorsOfSet T := by
    intro w hw hwu
    exact (M.mem_latentAncestorsOfSet).mpr ⟨hwu, w, hw, Or.inl rfl⟩
  -- `w ∈ T` is observed or unobserved.
  have obsOrUnobs : ∀ {w : SWIGNode N}, w ∈ T → w ∈ M.observed ∨ w ∈ M.unobserved := by
    intro w hw
    exact Finset.mem_union.mp (by simpa [SCM.randomVars] using hT hw)
  -- Build `g` coordinatewise.
  refine ⟨fun latentProj w =>
      if hobs : w.val ∈ M.observed then
        (Classical.choose (M.evalMap_factors_through_ancestors w.val hobs))
          (valuesProjection (M.fixedAncestorsOfNode_subset w.val) s)
          (valuesProjection
            (M.latentAncestorsOfNode_subset_latentAncestorsOfSet w.property) latentProj)
      else
        latentProj ⟨w.val, latentInT w.property
          ((obsOrUnobs w.property).resolve_left hobs)⟩,
    ?_, ?_⟩
  · -- Measurability, coordinatewise.
    refine measurable_pi_iff.mpr (fun w => ?_)
    by_cases hobs : w.val ∈ M.observed
    · simp only [dif_pos hobs]
      have hg_meas :=
        (Classical.choose_spec (M.evalMap_factors_through_ancestors w.val hobs)).1
      have hcurry : Measurable
          (fun latentProj : ValuesOn (M.latentAncestorsOfSet T) (swigΩ Ω) =>
            (Classical.choose (M.evalMap_factors_through_ancestors w.val hobs))
              (valuesProjection (M.fixedAncestorsOfNode_subset w.val) s)
              (valuesProjection
                (M.latentAncestorsOfNode_subset_latentAncestorsOfSet w.property)
                latentProj)) := by
        have : (fun latentProj : ValuesOn (M.latentAncestorsOfSet T) (swigΩ Ω) =>
            (Classical.choose (M.evalMap_factors_through_ancestors w.val hobs))
              (valuesProjection (M.fixedAncestorsOfNode_subset w.val) s)
              (valuesProjection
                (M.latentAncestorsOfNode_subset_latentAncestorsOfSet w.property)
                latentProj)) =
            (Function.uncurry
              (Classical.choose (M.evalMap_factors_through_ancestors w.val hobs))) ∘
              (fun latentProj => (valuesProjection (M.fixedAncestorsOfNode_subset w.val) s,
                valuesProjection
                  (M.latentAncestorsOfNode_subset_latentAncestorsOfSet w.property)
                  latentProj)) := by
          funext latentProj; rfl
        rw [this]
        exact hg_meas.comp (measurable_const.prodMk
          (measurable_valuesProjection
            (M.latentAncestorsOfNode_subset_latentAncestorsOfSet w.property)))
      exact hcurry
    · simp only [dif_neg hobs]
      exact measurable_pi_apply _
  · -- The factorization equation.
    funext ℓ
    funext w
    change M.evalMap s ℓ ⟨w.val, hT w.property⟩ =
      (if hobs : w.val ∈ M.observed then
        (Classical.choose (M.evalMap_factors_through_ancestors w.val hobs))
          (valuesProjection (M.fixedAncestorsOfNode_subset w.val) s)
          (valuesProjection
            (M.latentAncestorsOfNode_subset_latentAncestorsOfSet w.property)
            (valuesProjection (M.latentAncestorsOfSet_subset T) ℓ))
      else
        (valuesProjection (M.latentAncestorsOfSet_subset T) ℓ) ⟨w.val, latentInT w.property
          ((obsOrUnobs w.property).resolve_left hobs)⟩)
    by_cases hobs : w.val ∈ M.observed
    · rw [dif_pos hobs]
      have heq :=
        (Classical.choose_spec (M.evalMap_factors_through_ancestors w.val hobs)).2 s ℓ
      -- `heq` rewrites the observed `evalMap` at `w` via the per-node factorization;
      -- the nested latent projection collapses definitionally.
      rw [show M.evalMap s ℓ ⟨w.val, hT w.property⟩ =
          M.evalMap s ℓ ⟨w.val, Finset.mem_union_left _ hobs⟩ from rfl, heq]
      rfl
    · rw [dif_neg hobs]
      have hwu : w.val ∈ M.unobserved := (obsOrUnobs w.property).resolve_left hobs
      rw [M.evalMap_unobserved s ℓ ⟨w.val, hT w.property⟩ hwu]
      rfl

/-- Latent-base / residual factorization of the `T`-projection of `evalMap s`.

    The projection to `T` depends on the latent source only through:

    * the latent ancestor block of `W_rand`, and
    * the residual latent support inside `latentAncestorsOfSet T` but outside
      `latentAncestorsOfSet W_rand`.

    This weaker statement is mathematically correct without any injectivity
    assumption on the map from latent ancestors to the observed `W_rand`
    values.  The stronger claim that the first block can be replaced by the
    actual realized `W_rand` values is false in general. -/
private theorem evalMap_valuesProjection_factors_through_latent_base_and_residual
    (M : Causalean.SCM N Ω) [∀ n, Nonempty (Ω n)] (s : M.FixedValues)
    (T W_rand : Finset (SWIGNode N))
    (hT : T ⊆ M.randomVars) (hW_rand : W_rand ⊆ M.randomVars) :
    ∃ g : ValuesOn (M.latentAncestorsOfSet W_rand) (swigΩ Ω) →
          ValuesOn (M.latentResidualOfSet T W_rand) (swigΩ Ω) →
          ValuesOn T (swigΩ Ω),
      Measurable (Function.uncurry g) ∧
      (valuesProjection hT ∘ fun ℓ : M.LatentValues => M.evalMap s ℓ) =
        fun ℓ =>
          g (valuesProjection (Ω := swigΩ Ω) (M.latentAncestorsOfSet_subset W_rand) ℓ)
            (valuesProjection (Ω := swigΩ Ω) (M.latentResidualOfSet_subset T W_rand) ℓ) := by
  classical
  -- Obtain the single-block factorization through `latentAncestorsOfSet T`.
  obtain ⟨g₀, hg₀_meas, heq₀⟩ :=
    M.evalMap_valuesProjection_factors_through_latentAncestorsOfSet s T hT
  -- For a coordinate `u ∈ latentAncestorsOfSet T` not in `latentAncestorsOfSet W_rand`,
  -- it lies in the residual block.
  have residMem : ∀ {u : SWIGNode N}, u ∈ M.latentAncestorsOfSet T →
      u ∉ M.latentAncestorsOfSet W_rand → u ∈ M.latentResidualOfSet T W_rand := by
    intro u hu hnot
    exact Finset.mem_sdiff.mpr ⟨hu, hnot⟩
  -- Reconstruct the `latentAncestorsOfSet T` coordinates from the two blocks.
  let combine : ValuesOn (M.latentAncestorsOfSet W_rand) (swigΩ Ω) →
      ValuesOn (M.latentResidualOfSet T W_rand) (swigΩ Ω) →
      ValuesOn (M.latentAncestorsOfSet T) (swigΩ Ω) :=
    fun base resid u =>
      if hb : u.val ∈ M.latentAncestorsOfSet W_rand then
        base ⟨u.val, hb⟩
      else
        resid ⟨u.val, residMem u.property hb⟩
  refine ⟨fun base resid => g₀ (combine base resid), ?_, ?_⟩
  · -- Measurability of the uncurried map.
    have hcombine_meas : Measurable (Function.uncurry combine) := by
      refine measurable_pi_iff.mpr (fun u => ?_)
      by_cases hb : u.val ∈ M.latentAncestorsOfSet W_rand
      · have : (fun p : ValuesOn (M.latentAncestorsOfSet W_rand) (swigΩ Ω) ×
              ValuesOn (M.latentResidualOfSet T W_rand) (swigΩ Ω) =>
            Function.uncurry combine p u) =
            fun p => p.1 ⟨u.val, hb⟩ := by
          funext p; simp [combine, Function.uncurry, hb]
        rw [this]
        exact (measurable_pi_apply _).comp measurable_fst
      · have : (fun p : ValuesOn (M.latentAncestorsOfSet W_rand) (swigΩ Ω) ×
              ValuesOn (M.latentResidualOfSet T W_rand) (swigΩ Ω) =>
            Function.uncurry combine p u) =
            fun p => p.2 ⟨u.val, residMem u.property hb⟩ := by
          funext p; simp [combine, Function.uncurry, hb]
        rw [this]
        exact (measurable_pi_apply _).comp measurable_snd
    have huncurry : (Function.uncurry fun base resid => g₀ (combine base resid)) =
        g₀ ∘ Function.uncurry combine := by
      funext p; rfl
    rw [huncurry]
    exact hg₀_meas.comp hcombine_meas
  · -- The factorization equation follows by collapsing the reconstructed latent block.
    funext ℓ
    have hcombine_eq :
        combine (valuesProjection (M.latentAncestorsOfSet_subset W_rand) ℓ)
          (valuesProjection (M.latentResidualOfSet_subset T W_rand) ℓ) =
          valuesProjection (M.latentAncestorsOfSet_subset T) ℓ := by
      funext u
      by_cases hb : u.val ∈ M.latentAncestorsOfSet W_rand
      · simp [combine, hb, valuesProjection]
      · simp [combine, hb, valuesProjection]
    change _ = g₀ (combine _ _)
    rw [hcombine_eq]
    exact congrFun heq₀ ℓ

-- ============================================================
-- § 0. Product-space CI bridge (used by § 1)
-- ============================================================

/-- Measurable reindexing equivalence between the coordinate tuple on the
    subtype-image `S.subtype (· ∈ P)` of `S ⊆ P` and the coordinate tuple on
    `S` itself.  It is the identity on values, only relabelling the index from
    the doubly-nested subtype to the direct subtype `{j // j ∈ S}`. -/
noncomputable def reindexSubtypeProj {M' : Type*} [DecidableEq M'] [Fintype M']
    {Ω' : M' → Type*} [∀ n, MeasurableSpace (Ω' n)] {P : Finset M'}
    (S : Finset M') (hS : S ⊆ P) :
    ((i : {i // i ∈ (S.subtype (· ∈ P))}) → Ω' i.val.val) ≃ᵐ
      ((j : {j // j ∈ S}) → Ω' j.val) where
  toFun := fun f j => f ⟨⟨j.val, hS j.property⟩, by
    simp only [Finset.mem_subtype]; exact j.property⟩
  invFun := fun g i => g ⟨i.val.val, by
    have := i.property; rw [Finset.mem_subtype] at this; exact this⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  measurable_toFun := by
    apply measurable_pi_lambda; intro j; exact measurable_pi_apply _
  measurable_invFun := by
    apply measurable_pi_lambda; intro i; exact measurable_pi_apply _

/-- Under `M.latentProduct = ⊗_{u ∈ 𝐋} ℙ(L_u)`, the coordinate-tuple
    projections at two disjoint latent blocks `A`, `B ⊆ M.unobserved` are
    independent.  The latent product is a `Measure.pi` over the subtype of
    unobserved nodes, so this is `indepFun_pi_of_disjoint` transported along the
    `reindexSubtypeProj` relabelling. -/
theorem indepFun_valuesProjection_latentProduct
    (M : Causalean.SCM N Ω) {A B : Finset (SWIGNode N)}
    (hA : A ⊆ M.unobserved) (hB : B ⊆ M.unobserved) (hAB : Disjoint A B) :
    ProbabilityTheory.IndepFun (valuesProjection (Ω := swigΩ Ω) hA)
      (valuesProjection (Ω := swigΩ Ω) hB) M.latentProduct := by
  classical
  letI := M.isProbability_latent
  set A' : Finset {i // i ∈ M.unobserved} := A.subtype (· ∈ M.unobserved) with hA'def
  set B' : Finset {i // i ∈ M.unobserved} := B.subtype (· ∈ M.unobserved) with hB'def
  have hA'B' : Disjoint A' B' := by
    rw [Finset.disjoint_left]; intro i hiA hiB
    rw [hA'def, Finset.mem_subtype] at hiA
    rw [hB'def, Finset.mem_subtype] at hiB
    exact (Finset.disjoint_left.mp hAB hiA) hiB
  have hbase :
      ProbabilityTheory.IndepFun
        (finsetCoordProj (Ω := fun i : {i // i ∈ M.unobserved} => swigΩ Ω i.val) A')
        (finsetCoordProj (Ω := fun i : {i // i ∈ M.unobserved} => swigΩ Ω i.val) B')
        (MeasureTheory.Measure.pi (fun u => M.latentDist u)) :=
    indepFun_pi_of_disjoint (fun u => M.latentDist u) hA'B'
  exact hbase.comp (reindexSubtypeProj (Ω' := swigΩ Ω) A hA).measurable
    (reindexSubtypeProj (Ω' := swigΩ Ω) B hB).measurable

/-- Shared-base conditional independence under the latent product measure
    `M.latentProduct`.

    Once both sides of `evalMap s` are factored through a common latent block `U`
    and disjoint residual blocks `Rx`, `Ry`, conditioning on any measurable summary
    of `U` (e.g. realized `W`-values) makes the two sides conditionally independent.

    The product-factorization hypothesis is *essential*: for an arbitrary
    probability measure on `M.LatentValues`, the coordinate blocks `Rx` and `Ry`
    may be correlated (consider `U = ∅` with a diagonal measure on `Rx × Ry`),
    and the conclusion fails. We therefore specialize to `M.latentProduct`, which
    is the coordinate-independent latent measure baked into every `SCM`.

    Used by `fullCondIndep_singleton_of_dSep_with_fixed` once the factorization
    through latent ancestor blocks is established.

    Proof sketch: reduce to `condIndepFun_pi_of_inter_subset` via the product-space
    σ-algebra factorization
    `ValuesOn (U ∪ Rx ∪ Ry) Ω ≅ ValuesOn U Ω × ValuesOn Rx Ω × ValuesOn Ry Ω`. -/
private theorem condIndepFun_of_shared_base_valuesProjection_pi
    (M : Causalean.SCM N Ω)
    {U Rx Ry : Finset (SWIGNode N)}
    [StandardBorelSpace M.LatentValues]
    {β γ δ : Type*}
    [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]
    (hU : U ⊆ M.unobserved) (hRx : Rx ⊆ M.unobserved) (hRy : Ry ⊆ M.unobserved)
    {baseMap : ValuesOn U (swigΩ Ω) → β} (hbaseMap : Measurable baseMap)
    {leftMap : β × ValuesOn Rx (swigΩ Ω) → γ} (hleftMap : Measurable leftMap)
    {rightMap : β × ValuesOn Ry (swigΩ Ω) → δ} (hrightMap : Measurable rightMap)
    (hURx : Disjoint U Rx) (hURy : Disjoint U Ry) (hRxRy : Disjoint Rx Ry) :
    ProbabilityTheory.CondIndepFun
      (MeasurableSpace.comap (baseMap ∘ valuesProjection (Ω := swigΩ Ω) hU) inferInstance)
      (Measurable.comap_le (hbaseMap.comp (measurable_valuesProjection (Ω' := swigΩ Ω) hU)))
      (fun ω : M.LatentValues =>
        leftMap (baseMap (valuesProjection (Ω := swigΩ Ω) hU ω),
                 valuesProjection (Ω := swigΩ Ω) hRx ω))
      (fun ω : M.LatentValues =>
        rightMap (baseMap (valuesProjection (Ω := swigΩ Ω) hU ω),
                  valuesProjection (Ω := swigΩ Ω) hRy ω))
      M.latentProduct := by
  classical
  set pU := valuesProjection (Ω := swigΩ Ω) hU with hpU
  set pRx := valuesProjection (Ω := swigΩ Ω) hRx with hpRx
  set pRy := valuesProjection (Ω := swigΩ Ω) hRy with hpRy
  have hpU_meas : Measurable pU := measurable_valuesProjection hU
  have hpRx_meas : Measurable pRx := measurable_valuesProjection hRx
  have hpRy_meas : Measurable pRy := measurable_valuesProjection hRy
  set b : M.LatentValues → β := baseMap ∘ pU with hb
  have hb_meas : Measurable b := hbaseMap.comp hpU_meas
  have hb_𝒢 : Measurable[MeasurableSpace.comap b inferInstance] b :=
    comap_measurable b
  have hle : MeasurableSpace.comap b inferInstance ≤
      (inferInstance : MeasurableSpace M.LatentValues) := hb_meas.comap_le
  -- Step A: the disjoint residual blocks are independent under the latent product.
  have hStepA : ProbabilityTheory.IndepFun pRx pRy M.latentProduct :=
    indepFun_valuesProjection_latentProduct M hRx hRy hRxRy
  -- Step B: the joint residual block is independent of the base summary `b`.
  have hURxRy : Disjoint (Rx ∪ Ry) U := by
    rw [Finset.disjoint_union_left]; exact ⟨hURx.symm, hURy.symm⟩
  have hRxRyU_sub : (Rx ∪ Ry) ⊆ M.unobserved := Finset.union_subset hRx hRy
  have hIndepBlock : ProbabilityTheory.IndepFun
      (valuesProjection (Ω := swigΩ Ω) hRxRyU_sub) pU M.latentProduct :=
    indepFun_valuesProjection_latentProduct M hRxRyU_sub hU hURxRy
  have hsplit : (fun ω => (pRx ω, pRy ω))
      = (fun v : ValuesOn (Rx ∪ Ry) (swigΩ Ω) =>
          (valuesProjection (Ω := swigΩ Ω) (Finset.subset_union_left) v,
           valuesProjection (Ω := swigΩ Ω) (Finset.subset_union_right) v))
        ∘ (valuesProjection (Ω := swigΩ Ω) hRxRyU_sub) := by
    funext ω; rfl
  have hIndepPairU : ProbabilityTheory.IndepFun (fun ω => (pRx ω, pRy ω)) pU
      M.latentProduct := by
    rw [hsplit]
    exact hIndepBlock.comp
      ((measurable_valuesProjection (Finset.subset_union_left (s₁ := Rx) (s₂ := Ry))).prod
        (measurable_valuesProjection (Finset.subset_union_right (s₁ := Rx) (s₂ := Ry))))
      measurable_id
  have hIndepPairB : ProbabilityTheory.IndepFun (fun ω => (pRx ω, pRy ω)) b
      M.latentProduct := hIndepPairU.comp measurable_id hbaseMap
  have hStepB : ProbabilityTheory.Indep
      (MeasurableSpace.comap (fun ω => (pRx ω, pRy ω)) inferInstance)
      (MeasurableSpace.comap b inferInstance) M.latentProduct :=
    (ProbabilityTheory.IndepFun_iff_Indep _ _ _).mp hIndepPairB
  -- Step C: residual conditional independence given `σ(b)`.
  have hStepC : ProbabilityTheory.CondIndepFun
      (MeasurableSpace.comap b inferInstance) hle pRx pRy M.latentProduct :=
    condIndepFun_of_indepFun_indep hpRx_meas hpRy_meas hb_meas hStepA hStepB
  -- Step D: re-attach the `σ(b)`-measurable base coordinate to both sides.
  have hD1 : ProbabilityTheory.CondIndepFun (MeasurableSpace.comap b inferInstance) hle
      (fun ω => (pRx ω, b ω)) pRy M.latentProduct :=
    condIndepFun_prodMk_of_measurable_left hle hpRx_meas hpRy_meas hb_meas hb_𝒢 hStepC
  have hD2 : ProbabilityTheory.CondIndepFun (MeasurableSpace.comap b inferInstance) hle
      (fun ω => (pRy ω, b ω)) (fun ω => (pRx ω, b ω)) M.latentProduct :=
    condIndepFun_prodMk_of_measurable_left hle hpRy_meas (hpRx_meas.prod hb_meas) hb_meas
      hb_𝒢 hD1.symm
  -- Apply the two outer measurable maps `leftMap`, `rightMap` (after swapping the
  -- coordinate pair to `(b, residual)` order).
  exact hD2.symm.comp
    (φ := fun p : ValuesOn Rx (swigΩ Ω) × β => leftMap (p.2, p.1))
    (ψ := fun p : ValuesOn Ry (swigΩ Ω) × β => rightMap (p.2, p.1))
    (hleftMap.comp (measurable_snd.prod measurable_fst))
    (hrightMap.comp (measurable_snd.prod measurable_fst))

-- ============================================================
-- § 1. Singleton-source auxiliary
-- ============================================================

/-- Ordered-local Markov: each random node is conditionally independent of its
    strictly-earlier non-parents given its parents (intersected with randomVars),
    under jointKernel.

    Concretely, for a set `P` of non-descendants of `v` that contains `v`'s random
    parents, the node `v` is conditionally independent of `P` minus its parents,
    given its random parents. This is the local Markov property repackaged into
    the "ordered" form (right set carved out of an arbitrary predecessor block `P`)
    that the Verma–Pearl induction consumes. -/
private theorem fullCondIndep_ordered_local
    (M : Causalean.SCM N Ω) [StandardBorelSpace M.RandomValues]
    [StandardBorelSpace M.LatentValues]
    [∀ s : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.jointKernel s)]
    [∀ (v : SWIGNode N),
      StandardBorelSpace (ValuesOn ({v} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (v : SWIGNode N),
      Nonempty (ValuesOn ({v} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (v : SWIGNode N),
      StandardBorelSpace (ValuesOn (M.dag.nonDescendants v ∩ M.randomVars) (swigΩ Ω))]
    [∀ (v : SWIGNode N),
      Nonempty (ValuesOn (M.dag.nonDescendants v ∩ M.randomVars) (swigΩ Ω))]
    (s : M.FixedValues) (v : SWIGNode N) (hv : v ∈ M.randomVars)
    (P : Finset (SWIGNode N))
    (hP : P ⊆ M.randomVars)
    (hP_nonDesc : P ⊆ M.dag.nonDescendants v)
    (hpa_sub : (M.dag.parents v ∩ M.randomVars) ⊆ P) :
    FullCondIndep M {v} (P \ (M.dag.parents v ∩ M.randomVars))
      (M.dag.parents v ∩ M.randomVars)
      (Finset.singleton_subset_iff.mpr hv)
      (Finset.Subset.trans (Finset.sdiff_subset) hP)
      (Finset.inter_subset_right)
      (M.jointKernel s) := by
  classical
  -- `P \ pa ⊆ nonDescendants v ∩ randomVars`: from `hP_nonDesc` (left) and `hP` (right).
  have hsub_right : (P \ (M.dag.parents v ∩ M.randomVars)) ⊆
      M.dag.nonDescendants v ∩ M.randomVars := by
    intro u hu
    rcases Finset.mem_sdiff.mp hu with ⟨huP, _⟩
    exact Finset.mem_inter.mpr ⟨hP_nonDesc huP, hP huP⟩
  rcases Finset.mem_union.mp hv with hobs | hunobs
  · -- Observed case: direct from `full_local_markov` + `fullCondIndep_subset_right`.
    have hLM := full_local_markov M v hobs s
    exact fullCondIndep_subset_right M
      (Finset.singleton_subset_iff.mpr hv)
      Finset.inter_subset_right
      (Finset.Subset.trans (Finset.sdiff_subset) hP)
      Finset.inter_subset_right
      hsub_right hLM
  · -- Latent case: `a` is a root, so `parents v ∩ randomVars = ∅`.
    have hpar_empty : M.dag.parents v = ∅ := M.unobs_are_roots v hunobs
    have hpa_inter_empty : M.dag.parents v ∩ M.randomVars = ∅ := by
      rw [hpar_empty]; exact Finset.empty_inter _
    -- `full_local_markov_latent` gives `{v} ⊥ (nonDescendants v ∩ randomVars) | ∅`.
    have hLM := full_local_markov_latent M v hunobs s
    -- Shrink the right set to `P \ pa ⊆ nonDescendants v ∩ randomVars`.
    have hLM' := fullCondIndep_subset_right M
      (Finset.singleton_subset_iff.mpr hv)
      Finset.inter_subset_right
      (Finset.Subset.trans (Finset.sdiff_subset) hP)
      (Finset.empty_subset _)
      hsub_right hLM
    -- Align the conditioning set `∅` with `parents v ∩ randomVars` (both `∅`).
    exact fullCondIndep_congr_right M hpa_inter_empty.symm hLM'

/-- **Interpretation of an ordered-local derivation as full conditional
    independence.** Any purely-graphical `OrderedLocalSG` derivation of "`X` ⊥ `Y`
    given `Z`" (over the random set `M.randomVars`) holds as a `FullCondIndep` under
    the joint kernel.

    The proof is by induction on the derivation: the basis constructor is
    `fullCondIndep_ordered_local`, the empty-source constructor is
    `fullCondIndep_const_left`, and the four semi-graphoid constructors map to the
    matching `fullCondIndep_*` axioms. Subset-to-`randomVars` side-conditions are
    recovered from the derivation via `OrderedLocalSG.subset_random`. -/
private theorem fullCondIndep_of_orderedLocalSG
    (M : Causalean.SCM N Ω) [StandardBorelSpace M.RandomValues]
    [StandardBorelSpace M.LatentValues]
    [∀ s : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.jointKernel s)]
    [∀ (v : SWIGNode N),
      StandardBorelSpace (ValuesOn ({v} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (v : SWIGNode N),
      Nonempty (ValuesOn ({v} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (v : SWIGNode N),
      StandardBorelSpace (ValuesOn (M.dag.nonDescendants v ∩ M.randomVars) (swigΩ Ω))]
    [∀ (v : SWIGNode N),
      Nonempty (ValuesOn (M.dag.nonDescendants v ∩ M.randomVars) (swigΩ Ω))]
    (s : M.FixedValues) {X Y Z : Finset (SWIGNode N)}
    (h : M.dag.OrderedLocalSG M.randomVars X Y Z) :
    ∀ (hX : X ⊆ M.randomVars) (hY : Y ⊆ M.randomVars) (hZ : Z ⊆ M.randomVars),
      FullCondIndep M X Y Z hX hY hZ (M.jointKernel s) := by
  induction h with
  | nil Y Z hY' hZ' => intro hX hY hZ; exact fullCondIndep_const_left M hY hZ
  | basis v hv P hP hND hPa =>
      intro hX hY hZ; exact fullCondIndep_ordered_local M s v hv P hP hND hPa
  | symm h' ih =>
      intro hX hY hZ
      obtain ⟨hX0, hY0, hZ0⟩ := h'.subset_random
      exact fullCondIndep_symm M hX0 hY0 hZ0 (ih hX0 hY0 hZ0)
  | decomp h' ih =>
      intro hX hY hZ
      obtain ⟨hX0, hYW0, hZ0⟩ := h'.subset_random
      exact fullCondIndep_decomposition M hX0 hYW0 hY hZ (ih hX0 hYW0 hZ0)
  | weakUnion h' ih =>
      intro hX hY hZ
      obtain ⟨hX0, hYW0, hZ0⟩ := h'.subset_random
      exact fullCondIndep_weak_union M hX0 hYW0 hY hZ0 hZ (ih hX0 hYW0 hZ0)
  | contract h1 h2 ih1 ih2 =>
      intro hX hY hZ
      obtain ⟨hX1, hY1, hZW1⟩ := h1.subset_random
      obtain ⟨_, hW2, hZ2⟩ := h2.subset_random
      exact fullCondIndep_contraction M hX1 hY1 hW2 hZ2 hY hZW1
        (ih1 hX1 hY1 hZW1) (ih2 hX1 hW2 hZ2)

/-- **Singleton-source d-sep with fixed-node conditioning shadow ⟹ full CI.**

    For any single observed-or-latent node `a`, any `Y, W_rand ⊆ M.randomVars`,
    and any `W_fix ⊆ M.fixed`, d-separation `dSep {a} Y (W_rand ∪ W_fix)` in the
    full DAG implies conditional independence `{a} ⊥ Y | W_rand` under
    `M.jointKernel s`.

    The proof routes through a graph-level ordered-local derivation rather than
    dropping `W_fix` from the graph:

    * use `ancestralSet_inter_subset_ancestralSet_of_dSep` with conditioning
      `W_rand ∪ W_fix`;
    * observe that common **latent** ancestors of `{a}` and `Y` cannot land in
      `W_fix` (fixed nodes are not latent), so the latent-overlap is absorbed by
      `W_rand`;
    * invoke `DAG.orderedLocalSG_of_dSep_with_fixed` and interpret the resulting
      ordered-local derivation as `FullCondIndep` via
      `fullCondIndep_of_orderedLocalSG`.

    Used in `full_globalMarkov_with_fixed` step (ii). -/
private theorem fullCondIndep_singleton_of_dSep_with_fixed
    (M : Causalean.SCM N Ω) [StandardBorelSpace M.RandomValues]
    [∀ n, StandardBorelSpace (swigΩ Ω n)] [∀ n, Nonempty (swigΩ Ω n)]
    [∀ s : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.jointKernel s)]
    (a : SWIGNode N) (Y W_rand W_fix : Finset (SWIGNode N))
    (ha : a ∈ M.randomVars)
    (hY : Y ⊆ M.randomVars) (hW_rand : W_rand ⊆ M.randomVars)
    (hW_fix : W_fix ⊆ M.fixed)
    (hDisj_aY : Disjoint ({a} : Finset (SWIGNode N)) Y)
    (hDisj_aW : Disjoint ({a} : Finset (SWIGNode N)) W_rand)
    (hDisj_YW : Disjoint Y W_rand)
    (hdSep : M.dag.dSep {a} Y (W_rand ∪ W_fix))
    (s : M.FixedValues) :
    FullCondIndep M {a} Y W_rand
      (Finset.singleton_subset_iff.mpr ha) hY hW_rand (M.jointKernel s) := by
  have hFR : Disjoint M.fixed M.randomVars := by
    rw [Finset.disjoint_left]
    intro x hxF hxR
    obtain ⟨k, rfl⟩ := M.fixed_is_fixed x hxF
    rcases Finset.mem_union.mp hxR with h | h
    · obtain ⟨m, hm⟩ := M.observed_is_random _ h; exact absurd hm (by simp)
    · obtain ⟨m, hm⟩ := M.unobserved_is_random _ h; exact absurd hm (by simp)
  have hDeriv : M.dag.OrderedLocalSG M.randomVars {a} Y W_rand :=
    M.dag.orderedLocalSG_of_dSep_with_fixed M.randomVars M.fixed {a} Y W_rand W_fix
      M.fixed_are_roots hFR (Finset.singleton_subset_iff.mpr ha) hY hW_rand hW_fix
      hDisj_aY hDisj_aW hDisj_YW hdSep
  exact fullCondIndep_of_orderedLocalSG M s hDeriv
    (Finset.singleton_subset_iff.mpr ha) hY hW_rand

-- ============================================================
-- § 2. Full Global Markov (Verma–Pearl induction)
-- ============================================================

/-- **Full Global Markov with fixed-node conditioning shadow.** d-separation
    with conditioning set `Z_rand ∪ Z_fix`, where `Z_fix ⊆ M.fixed`, implies
    conditional independence at the full distribution level (`jointKernel`)
    conditioned only on the random part `Z_rand`.

    **Proof**: Verma–Pearl induction via `Finset.strongInductionOn` on `X`. At each
    non-empty `X` we pick `a ∈ X` with maximal `M.dag.topoOrder` (via
    `Finset.exists_max_image`); by `topoOrder_injective` every `b ∈ A' := X.erase a`
    has `topoOrder b < topoOrder a`, hence `A' ⊆ NonDesc(a)`.

    * Base `X = ∅`: `condIndepFun_const_left`.
    * Step `X = insert a A'` with `a` topologically-last:
      (i)   `dSep A' Y (Z_rand ∪ Z_fix)` (`DAG.dSep_subset_left`) → IH on
            `A' ⊂ X` gives `A' ⊥ Y | Z_rand`.
      (ii)  `dSep {a} Y ((Z_rand ∪ A') ∪ Z_fix)` (`DAG.dSep_source_to_cond`)
            plus `fullCondIndep_singleton_of_dSep_with_fixed` give
            `{a} ⊥ Y | (Z_rand ∪ A')`
            using the singleton fixed-conditioning bridge.
      (iii) Contraction of (i).symm and (ii).symm gives
            `Y ⊥ ({a} ∪ A') | Z_rand`;
            symm + `singleton_union` + `insert_erase` rewrites to the goal
            using `fullCondIndep_contraction`.

    The theorem packages the graph-level ordered-local derivation with the
    full-distribution semi-graphoid interpretation, allowing fixed nodes to
    appear in the d-separation conditioning set while the probabilistic
    conditioning remains on the random part. -/
theorem full_globalMarkov_with_fixed (M : Causalean.SCM N Ω)
    [StandardBorelSpace M.RandomValues]
    [∀ n, StandardBorelSpace (swigΩ Ω n)] [∀ n, Nonempty (swigΩ Ω n)]
    [∀ s : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.jointKernel s)]
    (X Y Z_rand Z_fix : Finset (SWIGNode N))
    (hX : X ⊆ M.randomVars) (hY : Y ⊆ M.randomVars)
    (hZ_rand : Z_rand ⊆ M.randomVars) (hZ_fix : Z_fix ⊆ M.fixed)
    (hDisj_XY : Disjoint X Y)
    (hDisj_XZ : Disjoint X Z_rand) (hDisj_YZ : Disjoint Y Z_rand)
    (hdSep : M.dag.dSep X Y (Z_rand ∪ Z_fix))
    (s : M.FixedValues) :
    FullCondIndep M X Y Z_rand hX hY hZ_rand (M.jointKernel s) := by
  -- Strong induction on `X` (subset well-founded) with topologically-last selection.
  revert hX hDisj_XY hDisj_XZ hdSep
  induction X using Finset.strongInductionOn with
  | _ X ih =>
    intro hX hDisj_XY hDisj_XZ hdSep
    by_cases hempty : X = ∅
    · -- Base X = ∅: ∅-projection is constant, so CondIndepFun is trivial.
      subst hempty
      unfold FullCondIndep
      let c : ValuesOn (∅ : Finset (SWIGNode N)) (swigΩ Ω) :=
        fun w => absurd w.property (Finset.notMem_empty _)
      have hconst : valuesProjection hX = fun _ => c := by
        funext ξ w; exact absurd w.property (Finset.notMem_empty _)
      rw [hconst]
      exact ProbabilityTheory.condIndepFun_const_left c (valuesProjection hY)
    · -- Inductive step: pick `a ∈ X` with maximal topoOrder.
      have hne : X.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
      obtain ⟨a, ha_mem, ha_max⟩ :
          ∃ a ∈ X, ∀ b ∈ X, M.dag.topoOrder b ≤ M.dag.topoOrder a :=
        X.exists_max_image M.dag.topoOrder hne
      set A' := X.erase a with hA'_def
      have hA'_ssub : A' ⊂ X := Finset.erase_ssubset ha_mem
      have hA'_sub : A' ⊆ X := Finset.erase_subset a X
      have hA' : A' ⊆ M.randomVars := hA'_sub.trans hX
      have ha_rv : a ∈ M.randomVars := hX ha_mem
      have hXeq : insert a A' = X := Finset.insert_erase ha_mem
      -- Topological-max fact: every b ∈ A' is strictly earlier than a.
      -- This is the ordering input used by the singleton step.
      have _ha_strict : ∀ b ∈ A', M.dag.topoOrder b < M.dag.topoOrder a := by
        intro b hb
        have hbX : b ∈ X := hA'_sub hb
        have hbne : b ≠ a := Finset.ne_of_mem_erase hb
        exact lt_of_le_of_ne (ha_max b hbX)
          (fun h => hbne (M.dag.topoOrder_injective h))
      -- Step (i): d-sep monotonicity + IH on A' ⊂ X.
      have h_A'_dsep : M.dag.dSep A' Y (Z_rand ∪ Z_fix) :=
        DAG.dSep_subset_left M.dag hA'_sub hdSep
      have hDisj_A'Y : Disjoint A' Y := Disjoint.mono_left hA'_sub hDisj_XY
      have hDisj_A'Z : Disjoint A' Z_rand := Disjoint.mono_left hA'_sub hDisj_XZ
      have h_A'_ci : FullCondIndep M A' Y Z_rand hA' hY hZ_rand (M.jointKernel s) :=
        ih A' hA'_ssub hA' hDisj_A'Y hDisj_A'Z h_A'_dsep
      -- Step (ii): dSep_source_to_cond → dSep {a} Y ((Z_rand ∪ A') ∪ Z_fix).
      have h_aA'_eq : ({a} ∪ A' : Finset (SWIGNode N)) = X := by
        rw [Finset.singleton_union]; exact hXeq
      have h_a_dsep' : M.dag.dSep {a} Y ((Z_rand ∪ Z_fix) ∪ A') := by
        apply DAG.dSep_source_to_cond M.dag (X := {a}) (S := A')
        · exact Finset.disjoint_singleton_left.mpr (Finset.notMem_erase a X)
        · rw [h_aA'_eq]; exact hdSep
      have h_a_dsep : M.dag.dSep {a} Y ((Z_rand ∪ A') ∪ Z_fix) := by
        simpa [Finset.union_assoc, Finset.union_left_comm, Finset.union_comm] using h_a_dsep'
      have hDisj_aY : Disjoint ({a} : Finset (SWIGNode N)) Y := by
        rw [Finset.disjoint_singleton_left]
        exact fun haY => (Finset.disjoint_left.mp hDisj_XY) ha_mem haY
      have hDisj_aW : Disjoint ({a} : Finset (SWIGNode N)) (Z_rand ∪ A') := by
        rw [Finset.disjoint_union_right]
        refine ⟨?_, ?_⟩
        · rw [Finset.disjoint_singleton_left]
          exact fun h => (Finset.disjoint_left.mp hDisj_XZ ha_mem) h
        · rw [Finset.disjoint_singleton_left]; exact Finset.notMem_erase a X
      have hDisj_YW : Disjoint Y (Z_rand ∪ A') := by
        rw [Finset.disjoint_union_right]
        exact ⟨hDisj_YZ, hDisj_XY.symm.mono_right hA'_sub⟩
      -- Derive `{a} ⊥ Y | (Z_rand ∪ A')` from the singleton-source d-sep auxiliary.
      have h_a_ci : FullCondIndep M {a} Y (Z_rand ∪ A')
          (Finset.singleton_subset_iff.mpr ha_rv) hY
          (Finset.union_subset hZ_rand hA') (M.jointKernel s) :=
        fullCondIndep_singleton_of_dSep_with_fixed M a Y (Z_rand ∪ A') Z_fix
          ha_rv hY (Finset.union_subset hZ_rand hA') hZ_fix hDisj_aY hDisj_aW hDisj_YW
          h_a_dsep s
      -- Step (iii): contraction + symmetry.
      have h_Y_A' := h_A'_ci.symm
      have h_Y_a := h_a_ci.symm
      have h_aA'_rv : ({a} ∪ A') ⊆ M.randomVars :=
        Finset.union_subset (Finset.singleton_subset_iff.mpr ha_rv) hA'
      have h_combined := fullCondIndep_contraction M hY
        (Finset.singleton_subset_iff.mpr ha_rv) hA' hZ_rand h_aA'_rv
        (Finset.union_subset hZ_rand hA') h_Y_a h_Y_A'
      -- h_combined : Y ⊥ ({a} ∪ A') | Z_rand. Symmetrize and transport `{a} ∪ A' = X`.
      exact fullCondIndep_congr_left M h_aA'_eq h_combined.symm

/-- **Full Global Markov Property.** Backward-compatible wrapper around
    `full_globalMarkov_with_fixed` with no fixed-node conditioning shadow. -/
theorem full_globalMarkov (M : Causalean.SCM N Ω)
    [StandardBorelSpace M.RandomValues]
    [∀ n, StandardBorelSpace (swigΩ Ω n)] [∀ n, Nonempty (swigΩ Ω n)]
    [∀ s : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.jointKernel s)]
    (X Y Z : Finset (SWIGNode N))
    (hX : X ⊆ M.randomVars) (hY : Y ⊆ M.randomVars) (hZ : Z ⊆ M.randomVars)
    (hDisj_XY : Disjoint X Y)
    (hDisj_XZ : Disjoint X Z) (hDisj_YZ : Disjoint Y Z)
    (hdSep : M.dag.dSep X Y Z)
    (s : M.FixedValues) :
    FullCondIndep M X Y Z hX hY hZ (M.jointKernel s) := by
  simpa using
    (full_globalMarkov_with_fixed M X Y Z ∅ hX hY hZ (Finset.empty_subset _) hDisj_XY
      hDisj_XZ hDisj_YZ (by simpa using hdSep) s)

end SCM

end Causalean
