/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.SCM.Model.Kernel

/-! # Rule 3 Kernel Identity

This file proves the kernel-level form of Rule 3 of do-calculus for structural
causal models. The transport theorem `fixSet_latentProduct_compat` identifies
the latent-product measure before and after an additional intervention,
`fixSet_evalMap_nonAnc_compat` proves pointwise agreement of evaluation at nodes
with no fixed-intervention ancestors, and
`condDistrib_intervention_ancestral_eq` packages these facts as equality of
observed marginal kernels for targets not descended from the added intervention
nodes.
-/

namespace Causalean

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

namespace SCM

open scoped MeasureTheory ProbabilityTheory

/-- **Cross-SCM latent-product transport for Rule 3.**

    Pushing the intervened latent product `(M'.fixSet Z).latentProduct`
    through the coordinate-rename `valuesProjection` along `fixSet_unobserved` recovers
    the base latent product `M'.latentProduct`.

    True because `fixSet` inherits `latentDist` verbatim and preserves
    `unobserved` definitionally (`fixMono_unobserved` is `rfl`); the intervened
    and base latent products are *literally the same `Measure.pi`* on the same
    per-coordinate measures, just over propositionally-equal index types.  The
    `valuesProjection` cast bridges the two by relabelling the `Subtype` index
    witness.

    Proof: combine `measurePreserving_valuesEquivOfEq` (SCM.lean) — the
    `Measure.pi` transport across an index equality, packaged as a
    `MeasurableEquiv` — with `fixSet_latentDist` (InterventionSet.lean) — the
    pointwise witness that `fixSet` inherits `latentDist` verbatim.  Consumed by
    `condDistrib_intervention_ancestral_eq` to bridge
    the `M2.latentProduct` source on the LHS to the `M'.latentProduct` source
    on the RHS before the pointwise `fixSet_evalMap_nonAnc_compat` discharge. -/
theorem fixSet_latentProduct_compat
    (M' : Causalean.SCM N Ω) (Z : Finset N)
    (hZ_obs : ∀ D ∈ Z, SWIGNode.random D ∈ M'.observed)
    (hZ_fixed : ∀ D ∈ Z, SWIGNode.fixed D ∉ M'.fixed) :
    ((M'.fixSet Z hZ_obs hZ_fixed).latentProduct).map
        (valuesProjection
          (le_of_eq (fixSet_unobserved M' Z hZ_obs hZ_fixed).symm))
      = M'.latentProduct := by
  set M2 := M'.fixSet Z hZ_obs hZ_fixed with hM2
  have h_unobs : M2.unobserved = M'.unobserved := fixSet_unobserved M' Z hZ_obs hZ_fixed
  -- Under the monolithic `fixSet := fixMono`, `M2.unobserved = M'.unobserved` by
  -- `rfl` and `M2.latentDist = M'.latentDist` pointwise by `rfl`.  So the
  -- `valuesProjection`-transport across the identity type-equality is the
  -- identity, and the measure identity reduces to `rfl` on `Measure.pi`.
  change (M2.latentProduct).map (valuesEquivOfEq (Ω := swigΩ Ω) h_unobs) = M'.latentProduct
  unfold latentProduct
  letI := M2.isProbability_latent
  letI := M'.isProbability_latent
  rw [(measurePreserving_valuesEquivOfEq (Ω := swigΩ Ω) h_unobs
        (fun u => M2.latentDist u)).map_eq]
  congr 1

/-- **Helper — `hNoDesc` implies no `SWIGNode.fixed z` is a parent of `v`.**

    A parent is in particular an ancestor (via `isAncestor.edge`), so the
    non-ancestor hypothesis `hNoDesc` lifts to a non-parent hypothesis. -/
private lemma hNoDesc_implies_no_fixed_parent
    {M2 : Causalean.SCM N Ω} {Z : Finset N} {v : SWIGNode N}
    (hNoDesc : ∀ z ∈ Z, ¬ M2.dag.isAncestor (SWIGNode.fixed z) v) :
    ∀ z ∈ Z, SWIGNode.fixed z ∉ M2.dag.parents v := fun z hz hP =>
  hNoDesc z hz (DAG.isAncestor.edge (M2.dag.mem_parents.mp hP))

/-- **Helper — descend `hNoDesc` through a parent edge.**

    If `w ∈ parents v` and no `.fixed z` is an ancestor of `v`, then no
    `.fixed z` is an ancestor of `w` either (else `isAncestor.trans` would
    chain through the `w → v` edge to contradict `hNoDesc`). -/
private lemma hNoDesc_descend_to_parent
    {M2 : Causalean.SCM N Ω} {Z : Finset N} {v w : SWIGNode N}
    (hwP : w ∈ M2.dag.parents v)
    (hNoDesc : ∀ z ∈ Z, ¬ M2.dag.isAncestor (SWIGNode.fixed z) v) :
    ∀ z ∈ Z, ¬ M2.dag.isAncestor (SWIGNode.fixed z) w := fun z hz hanc =>
  hNoDesc z hz (DAG.isAncestor.trans hanc (M2.dag.mem_parents.mp hwP))

set_option maxHeartbeats 800000 in
/-- **Cross-SCM `evalMap` bridge for Rule 3.**

    At an observed node `v` whose `SWIGNode.fixed z` ancestors (`z ∈ Z`) are
    all absent in the intervention graph `(M'.fixSet Z).dag`,
    the `evalMap` value at `v` on `M'.fixSet Z` agrees with the
    `evalMap` value at `v` on `M'` after projecting the fixed-value
    argument via `fixSetProj` and transporting the latent argument along
    `fixSet_unobserved`.

    Analogous to `SCM.induce_evalMap_compat` in `Causal/Model/Induced.lean`,
    but for the further-intervention direction rather than the induced
    sub-SCM direction.

    **Proof.**  Strong recursion on `M2.observedIndex ⟨v, hv⟩`.  Parent-set
    coincidence `fixSet_parents_eq_of_no_fixed_parent` (InterventionSet.lean)
    lets us identify `M2.dag.parents v = M'.dag.parents v` under `hNoDesc`.
    Unfold both sides via `evalMap_observed_unfold` and peel the outer
    `M'.structFun` on both (LHS via `fixMono`'s definitional structFun, which
    makes `M2.structFun ⟨v, hv⟩ ξ` reduce to
    `M'.structFun ⟨v, hv⟩ (fixMonoParentMap … v ξ)` by `rfl`).  The resulting
    pointwise equality of the two parent tuples reduces to a three-way
    per-parent case split (unobserved / fixed / observed) on each `w ∈
    M'.dag.parents v`.  The only new ingredient compared to the induced
    template is the `fixMonoParentMap` collapse: under the no-fixed-parent
    hypothesis, no `.random D` (D ∈ Z) is a parent of `v` in `M'.dag`, so
    `fixMonoParentMap` reduces to the identity-like copy at every parent. -/
theorem fixSet_evalMap_nonAnc_compat
    (M' : Causalean.SCM N Ω) (Z : Finset N)
    (hZ_obs : ∀ D ∈ Z, SWIGNode.random D ∈ M'.observed)
    (hZ_fixed : ∀ D ∈ Z, SWIGNode.fixed D ∉ M'.fixed)
    (s' : (M'.fixSet Z hZ_obs hZ_fixed).FixedValues)
    (ℓ : (M'.fixSet Z hZ_obs hZ_fixed).LatentValues)
    {v : SWIGNode N}
    (hv : v ∈ (M'.fixSet Z hZ_obs hZ_fixed).observed)
    (hNoDesc : ∀ z ∈ Z,
      ¬ (M'.fixSet Z hZ_obs hZ_fixed).dag.isAncestor (SWIGNode.fixed z) v) :
    (M'.fixSet Z hZ_obs hZ_fixed).evalMap s' ℓ
        ⟨v, Finset.mem_union_left _ hv⟩
      = M'.evalMap
          (M'.fixSetProj Z hZ_obs hZ_fixed s')
          (valuesProjection
            (le_of_eq (fixSet_unobserved M' Z hZ_obs hZ_fixed).symm) ℓ)
          ⟨v, Finset.mem_union_left _
            (le_of_eq (fixSet_observed M' Z hZ_obs hZ_fixed) hv)⟩ := by
  classical
  -- Abbreviations (via `let` to avoid `set`'s hypothesis-shadowing behaviour
  -- on dependent arguments).
  let M2 := M'.fixSet Z hZ_obs hZ_fixed
  have h_obs_eq : M2.observed = M'.observed := rfl
  have h_unobs : M2.unobserved = M'.unobserved := rfl
  let s_M1 : M'.FixedValues := M'.fixSetProj Z hZ_obs hZ_fixed s'
  let ℓ_M1 : M'.LatentValues := valuesProjection (le_of_eq h_unobs.symm) ℓ
  -- Strong recursion on `M2.observedIndex ⟨v, hv⟩`, with the no-ancestor
  -- hypothesis carried through the recursion.  Under the monolithic
  -- `fixSet := fixMono`, `M2.observed = M'.observed` and `M2.unobserved =
  -- M'.unobserved` hold by `rfl`, so the coercions in the goal are identities.
  suffices h_obs : ∀ (n : ℕ) (w : SWIGNode N) (hw : w ∈ M2.observed)
      (_hNoD : ∀ z ∈ Z, ¬ M2.dag.isAncestor (SWIGNode.fixed z) w),
      (M2.observedIndex ⟨w, hw⟩).val = n →
      M2.evalMap s' ℓ ⟨w, Finset.mem_union_left _ hw⟩ =
        M'.evalMap s_M1 ℓ_M1 ⟨w, Finset.mem_union_left _ hw⟩ by
    exact h_obs _ v hv hNoDesc rfl
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro v hv hNoD hidx
    -- No `.fixed D` (D ∈ Z) is a parent of v in M2 (contrapositive of hNoD).
    have hNoFP : ∀ D ∈ Z, SWIGNode.fixed D ∉ M2.dag.parents v := fun D hD hP =>
      hNoD D hD (DAG.isAncestor.edge (M2.dag.mem_parents.mp hP))
    have h_parents_eq : M2.dag.parents v = M'.dag.parents v :=
      fixSet_parents_eq_of_no_fixed_parent M' Z hZ_obs hZ_fixed hNoFP
    have hv_M1 : v ∈ M'.observed := hv
    -- Unfold both `evalMap`s via `evalMap_observed_unfold`.
    rw [SCM.evalMap_observed_unfold M2 s' ℓ ⟨v, hv⟩,
        SCM.evalMap_observed_unfold M' s_M1 ℓ_M1 ⟨v, hv_M1⟩]
    -- LHS's outer `M2.structFun ⟨v, hv⟩` is definitionally
    -- `M'.structFun ⟨v, hv_M1⟩` precomposed with `fixMonoParentMap`.
    -- After `congr 1`, the goal reduces to pointwise equality of the two
    -- parent tuples over `M'.dag.parents v`.
    change M'.structFun ⟨v, hv_M1⟩
        (fixMonoParentMap M'.toSWIGGraph Z hZ_obs hZ_fixed v
          (fun w : {w // w ∈ M2.dag.parents v} =>
            if huo : w.val ∈ M2.unobserved then ℓ ⟨w.val, huo⟩
            else if hfix : w.val ∈ M2.fixed then s' ⟨w.val, hfix⟩
            else
              have hedge : M2.dag.edge w.val v := M2.dag.mem_parents.mp w.property
              have hobs : w.val ∈ M2.observed := by
                rcases Finset.mem_union.mp (M2.dag_edges_classified _ _ hedge).1
                  with h1 | h2
                · rcases Finset.mem_union.mp h1 with hfx | hob
                  · exact absurd hfx hfix
                  · exact hob
                · exact absurd h2 huo
              M2.evalMap s' ℓ ⟨w.val, Finset.mem_union_left _ hobs⟩))
      = M'.structFun ⟨v, hv_M1⟩ (fun w : {w // w ∈ M'.dag.parents v} =>
          if huo : w.val ∈ M'.unobserved then ℓ_M1 ⟨w.val, huo⟩
          else if hfix : w.val ∈ M'.fixed then s_M1 ⟨w.val, hfix⟩
          else
            have hedge : M'.dag.edge w.val v := M'.dag.mem_parents.mp w.property
            have hobs : w.val ∈ M'.observed := by
              rcases Finset.mem_union.mp (M'.dag_edges_classified _ _ hedge).1
                with h1 | h2
              · rcases Finset.mem_union.mp h1 with hfx | hob
                · exact absurd hfx hfix
                · exact hob
              · exact absurd h2 huo
            M'.evalMap s_M1 ℓ_M1 ⟨w.val, Finset.mem_union_left _ hobs⟩)
    congr 1
    -- Pointwise equality of the two parent tuples.
    funext w
    -- Bridge: w : {w // w ∈ M'.dag.parents v}, and the LHS tuple is indexed
    -- by `M'.dag.parents v` too (output of `fixMonoParentMap`).  On the LHS,
    -- unfold `fixMonoParentMap` according to w.val's constructor.
    have hNoRD : ∀ D ∈ Z, SWIGNode.random D ∉ M'.dag.parents v := by
      intro D hD hRD
      apply hNoFP D hD
      have hP_M2 := (SWIGGraph.splitMono_parents_char M'.toSWIGGraph Z hZ_obs hZ_fixed
        v (SWIGNode.fixed D)).2 (Or.inr ⟨D, hD, rfl, hRD⟩)
      exact hP_M2
    -- Per-parent three-way case split on `w.val`.
    rcases w with ⟨wVal, hwVal_M1⟩
    -- wVal's position in the LHS (fixMonoParentMap) depends on its form.
    have hwVal_M2 : wVal ∈ M2.dag.parents v := h_parents_eq.symm ▸ hwVal_M1
    -- Compute the LHS at wVal.
    cases wVal with
    | random u =>
      have hu_notZ : u ∉ Z := by
        intro hu
        exact hNoRD u hu hwVal_M1
      -- fixMonoParentMap at ⟨.random u, hwVal_M1⟩ with u ∉ Z:
      -- reads the ξ at ⟨.random u, (splitMono_parents_char …).2 (Or.inl …)⟩.
      rw [fixMonoParentMap_apply_random_notMem M'.toSWIGGraph Z hZ_obs hZ_fixed v _ u
        hu_notZ hwVal_M1]
      -- Now both sides are `if-elif-else` on wVal = .random u.
      -- M2.unobserved = M'.unobserved (rfl), M2.fixed = M'.fixed ∪ Z.image .fixed.
      -- For .random u, it is never in Z.image .fixed, so being in M2.fixed iff M'.fixed.
      by_cases huo : (SWIGNode.random u : SWIGNode N) ∈ M'.unobserved
      · have huo_M2 : SWIGNode.random u ∈ M2.unobserved := huo
        simp only [dif_pos huo, dif_pos huo_M2]
        -- ℓ_M1 at ⟨.random u, huo⟩ = ℓ at ⟨.random u, huo_M2⟩ since
        -- ℓ_M1 := valuesProjection (le_of_eq rfl.symm) ℓ = (by rfl) ℓ.
        rfl
      · have huo_M2 : SWIGNode.random u ∉ M2.unobserved := huo
        simp only [dif_neg huo, dif_neg huo_M2]
        by_cases hfix : (SWIGNode.random u : SWIGNode N) ∈ M'.fixed
        · -- .random u ∈ M'.fixed — impossible since M'.fixed elements are .fixed nodes.
          exfalso
          rcases M'.fixed_is_fixed _ hfix with ⟨_, hfix_eq⟩
          cases hfix_eq
        · have hfix_M2 : (SWIGNode.random u : SWIGNode N) ∉ M2.fixed := by
            intro h
            have : (SWIGNode.random u : SWIGNode N) ∈ M'.fixed ∪ Z.image SWIGNode.fixed := h
            rcases Finset.mem_union.mp this with h1 | h2
            · exact hfix h1
            · rcases Finset.mem_image.mp h2 with ⟨_, _, hEq⟩
              cases hEq
          simp only [dif_neg hfix, dif_neg hfix_M2]
          -- Observed case: apply IH.
          -- Need to derive `M2.observedIndex ⟨.random u, hobs_M2⟩ < n`.
          have hobs_M1 : (SWIGNode.random u : SWIGNode N) ∈ M'.observed := by
            have hedge_M1 : M'.dag.edge (SWIGNode.random u) v :=
              M'.dag.mem_parents.mp hwVal_M1
            rcases Finset.mem_union.mp (M'.dag_edges_classified _ _ hedge_M1).1
              with h1 | h2
            · rcases Finset.mem_union.mp h1 with hfx | hob
              · exact absurd hfx hfix
              · exact hob
            · exact absurd h2 huo
          have hobs_M2 : (SWIGNode.random u : SWIGNode N) ∈ M2.observed := hobs_M1
          -- IH on w.
          have hNoD_w : ∀ z ∈ Z,
              ¬ M2.dag.isAncestor (SWIGNode.fixed z) (SWIGNode.random u) := by
            intro z hz hanc
            exact hNoD z hz (DAG.isAncestor.trans hanc
              (M2.dag.mem_parents.mp hwVal_M2))
          have hidx_w : (M2.observedIndex ⟨SWIGNode.random u, hobs_M2⟩).val
                          < (M2.observedIndex ⟨v, hv⟩).val := by
            have hedge_M2 : M2.dag.edge (SWIGNode.random u) v :=
              M2.dag.mem_parents.mp hwVal_M2
            have hv_eq : (M2.observedAt
                ⟨(M2.observedIndex ⟨v, hv⟩).val,
                  (M2.observedIndex ⟨v, hv⟩).isLt⟩).val = v := by
              have := M2.observedAt_observedIndex ⟨v, hv⟩
              convert this
            have hedge_M2' : M2.dag.edge (SWIGNode.random u)
                (M2.observedAt
                  ⟨(M2.observedIndex ⟨v, hv⟩).val,
                    (M2.observedIndex ⟨v, hv⟩).isLt⟩).val := by
              rw [hv_eq]; exact hedge_M2
            exact M2.observed_parent_index_lt
              (M2.observedIndex ⟨v, hv⟩).isLt hedge_M2' hobs_M2
          rw [hidx] at hidx_w
          exact ih _ hidx_w (SWIGNode.random u) hobs_M2 hNoD_w rfl
    | fixed d =>
      -- fixMonoParentMap at ⟨.fixed d, hwVal_M1⟩: copies ξ at ⟨.fixed d, _⟩.
      rw [fixMonoParentMap_apply_fixed M'.toSWIGGraph Z hZ_obs hZ_fixed v _ d hwVal_M1]
      -- Both sides: .fixed d.  Unobserved case: impossible (unobserved elts are .random).
      have huo : (SWIGNode.fixed d : SWIGNode N) ∉ M'.unobserved := by
        intro h
        rcases M'.unobserved_is_random _ h with ⟨_, hEq⟩
        cases hEq
      have huo_M2 : (SWIGNode.fixed d : SWIGNode N) ∉ M2.unobserved := huo
      simp only [dif_neg huo, dif_neg huo_M2]
      -- Fixed case: .fixed d ∈ M'.fixed iff .fixed d ∈ M2.fixed (if d ∉ Z)
      -- or d ∈ Z (then .fixed d ∈ M2.fixed but may or may not be in M'.fixed).
      by_cases hfix_M1 : (SWIGNode.fixed d : SWIGNode N) ∈ M'.fixed
      · have hfix_M2 : (SWIGNode.fixed d : SWIGNode N) ∈ M2.fixed := by
          change _ ∈ M'.fixed ∪ Z.image SWIGNode.fixed
          exact Finset.mem_union_left _ hfix_M1
        simp only [dif_pos hfix_M1, dif_pos hfix_M2]
        -- s_M1 := fixSetProj s' = valuesProjection (fixSet_fixed_subset) s'.
        -- So s_M1 ⟨.fixed d, hfix_M1⟩ = s' ⟨.fixed d, fixSet_fixed_subset hfix_M1⟩
        --                            = s' ⟨.fixed d, hfix_M2⟩ (by proof irrelevance).
        rfl
      · -- .fixed d ∉ M'.fixed.  Is it in M2.fixed?  Only if d ∈ Z.
        by_cases hd_Z : d ∈ Z
        · -- .fixed d ∈ M2.fixed via Z.image.
          -- But wait — .fixed d being a parent of v in M'.dag would need d ∈ M'.fixed
          -- (since fixed nodes outside M'.fixed are isolated).
          exfalso
          have := M'.fixed_outside_fixed_isolated d hfix_M1
          have hCh : v ∈ M'.dag.children (SWIGNode.fixed d) :=
            M'.dag.mem_children.mpr (M'.dag.mem_parents.mp hwVal_M1)
          simpa [this.2] using hCh
        · have hfix_M2 : (SWIGNode.fixed d : SWIGNode N) ∉ M2.fixed := by
            intro h
            rcases Finset.mem_union.mp (show _ ∈ M'.fixed ∪ Z.image SWIGNode.fixed from h)
              with h1 | h2
            · exact hfix_M1 h1
            · rcases Finset.mem_image.mp h2 with ⟨d', hd'Z, hEq⟩
              have : d = d' := SWIGNode.fixed.inj hEq.symm
              exact hd_Z (this ▸ hd'Z)
          simp only [dif_neg hfix_M1, dif_neg hfix_M2]
          -- Observed case — but `.fixed d ∉ M'.observed` since observed elts are .random.
          exfalso
          have hobs : (SWIGNode.fixed d : SWIGNode N) ∈ M'.observed := by
            have hedge_M1 : M'.dag.edge (SWIGNode.fixed d) v :=
              M'.dag.mem_parents.mp hwVal_M1
            rcases Finset.mem_union.mp (M'.dag_edges_classified _ _ hedge_M1).1
              with h1 | h2
            · rcases Finset.mem_union.mp h1 with hfx | hob
              · exact absurd hfx hfix_M1
              · exact hob
            · exact absurd h2 huo
          rcases M'.observed_is_random _ hobs with ⟨_, hEq⟩
          cases hEq

/-- **Rule 3 core — intervention on non-ancestors of `T` is irrelevant**
    (Option B in the design; covers the simplified `Z_Y = Z` case of the
    tex's Rule 3, sufficient for backdoor / frontdoor demos).

    For `Z : Finset N` and a target set `T ⊆ M'.observed`, if
    **no** `SWIGNode.fixed z` (for `z ∈ Z`) is an ancestor (in the
    intervention SWIG graph `(M'.fixSet Z).dag`) of any `v ∈ T`, then the
    `T`-marginal of `(M'.fixSet Z).obsKernel s'` equals the
    `T`-marginal of `M'.obsKernel (fixSetProj s')`.

    Proof mirrors `SCM.induce_marginal_compat` (`Induced.lean:335`): unfold
    `obsKernel` to `latentProduct.map (evalMap ≫ randomToObserved ≫ π)` via
    `Measure.map_map`, then close by funext + `fixSet_evalMap_nonAnc_compat`.
    The extra complication vs. the induced-subgraph case is that
    `(M'.fixSet Z).latentProduct` equals `M'.latentProduct`
    only propositionally — though `fixSet_unobserved` is `rfl`, the latent-product
    `Subtype` index witness does not reduce definitionally — so the latent-side
    identification is discharged via `fixSet_unobserved` with `▸` casts. -/
theorem condDistrib_intervention_ancestral_eq
    (M' : Causalean.SCM N Ω) (Z : Finset N)
    (hZ_obs : ∀ D ∈ Z, SWIGNode.random D ∈ M'.observed)
    (hZ_fixed : ∀ D ∈ Z, SWIGNode.fixed D ∉ M'.fixed)
    (T : Finset (SWIGNode N))
    (hT : T ⊆ M'.observed)
    (hNoDesc : ∀ z ∈ Z, ∀ v ∈ T,
      ¬ (M'.fixSet Z hZ_obs hZ_fixed).dag.isAncestor (SWIGNode.fixed z) v)
    (s' : (M'.fixSet Z hZ_obs hZ_fixed).FixedValues) :
    ((M'.fixSet Z hZ_obs hZ_fixed).obsKernel s').map
        (valuesProjection
          ((fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hT))
      =
    (M'.obsKernel (M'.fixSetProj Z hZ_obs hZ_fixed s')).map
        (valuesProjection hT) := by
  classical
  -- Measurability bookkeeping.
  have hf_2 : Measurable (fun ℓ : LatentValues (M'.fixSet Z hZ_obs hZ_fixed) =>
      (M'.fixSet Z hZ_obs hZ_fixed).evalMap s' ℓ) :=
    (M'.fixSet Z hZ_obs hZ_fixed).evalMap_measurable.comp
      (Measurable.prodMk measurable_const measurable_id)
  have hf_1 : Measurable (fun ℓ : LatentValues M' =>
      M'.evalMap (M'.fixSetProj Z hZ_obs hZ_fixed s') ℓ) :=
    M'.evalMap_measurable.comp
      (Measurable.prodMk measurable_const measurable_id)
  have hRTO_2 : Measurable (M'.fixSet Z hZ_obs hZ_fixed).randomToObserved :=
    (M'.fixSet Z hZ_obs hZ_fixed).measurable_randomToObserved
  have hRTO_1 : Measurable M'.randomToObserved :=
    M'.measurable_randomToObserved
  have hπ_2 : Measurable (valuesProjection
      ((fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hT)
      : ObservedValues (M'.fixSet Z hZ_obs hZ_fixed) →
          ValuesOn T (swigΩ Ω)) :=
    measurable_valuesProjection _
  have hπ_1 : Measurable (valuesProjection hT
      : ObservedValues M' → ValuesOn T (swigΩ Ω)) :=
    measurable_valuesProjection _
  -- Step 1: unfold `obsKernel` and `jointKernel` to expose the latent push-forwards.
  unfold obsKernel
  rw [ProbabilityTheory.Kernel.map_apply _ hRTO_2,
      ProbabilityTheory.Kernel.map_apply _ hRTO_1,
      jointKernel_apply_eq (M'.fixSet Z hZ_obs hZ_fixed) s',
      jointKernel_apply_eq M' (M'.fixSetProj Z hZ_obs hZ_fixed s')]
  -- Step 2: compose the three nested `Measure.map`s on each side.
  rw [MeasureTheory.Measure.map_map hRTO_2 hf_2,
      MeasureTheory.Measure.map_map hπ_2 (hRTO_2.comp hf_2),
      MeasureTheory.Measure.map_map hRTO_1 hf_1,
      MeasureTheory.Measure.map_map hπ_1 (hRTO_1.comp hf_1)]
  -- Step 3: bridge the source measures via `fixSet_latentProduct_compat`
  -- (the `M2.latentProduct → M'.latentProduct` cast through `valuesProjection`).
  -- This converts the RHS `M'.latentProduct.map G_1` into
  -- `M2.latentProduct.map (G_1 ∘ cast)`, aligning both sides to the same source.
  have hcast : Measurable (valuesProjection
      (le_of_eq (fixSet_unobserved M' Z hZ_obs hZ_fixed).symm)
      : LatentValues (M'.fixSet Z hZ_obs hZ_fixed) →
        LatentValues M') :=
    measurable_valuesProjection _
  rw [← fixSet_latentProduct_compat M' Z hZ_obs hZ_fixed,
      MeasureTheory.Measure.map_map (hπ_1.comp (hRTO_1.comp hf_1)) hcast]
  -- Step 4: both sides are `M2.latentProduct.map (...)`; reduce to pointwise
  -- equality of the composed pushforward functions.
  congr 1
  funext ℓ
  simp only [Function.comp_apply]
  funext v
  simp only [randomToObserved, valuesProjection]
  -- Step 5: pointwise discharge via the cross-SCM evalMap bridge.
  exact fixSet_evalMap_nonAnc_compat M' Z hZ_obs hZ_fixed s' ℓ
    ((fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hT v.property)
    (fun z hz => hNoDesc z hz v.val v.property)

end SCM

end Causalean
