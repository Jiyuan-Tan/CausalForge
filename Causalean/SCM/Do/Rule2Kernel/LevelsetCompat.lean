/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.SCM.Do.Rule2Kernel.Helpers
import Causalean.SCM.Do.GlobalMarkov
import Causalean.SCM.Do.Rule3

/-! # Rule 2 Level-Set Compatibility

This file proves that the evaluation maps of the single-intervention and
double-intervention models agree on the latent level set where the single
intervention already realizes the additional treatment values. This is the
evaluation-map bridge used in the kernel proof of Rule 2 of do-calculus.
-/

namespace Causalean

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

namespace SCM

open scoped MeasureTheory ProbabilityTheory

-- ============================================================
-- § Rule 2 — level-set evalMap bridge (Step B)
-- ============================================================

set_option maxHeartbeats 800000 in
/-- **Cross-SCM `evalMap` level-set bridge for Rule 2.**

    On the "Z-level set" — the set of latents `ℓ` for which
    `(M.fixSet X)`'s `evalMap` produces at every `.random D`  (D ∈ Z)
    exactly the Z-intervention value `s' ⟨.fixed D, _⟩` — the evalMaps
    of the double- and single-intervention SCMs agree at every observed
    `v`.  No d-sep needed: the hypothesis makes children of Z consume
    the same value `z` in both SCMs (via Z.random's structural output
    in single, via Z.fixed directly in double), so downstream values
    recursively agree.

    Compare `fixSet_evalMap_nonAnc_compat` in `Rule3.lean`: that
    lemma's `hNoDesc` rules out `.fixed Z` ancestry of `v` entirely;
    here we allow Z-descendants but constrain the latent to the
    level set.

    **Proof.**  Strong recursion on `M2.observedIndex ⟨v, hv⟩`, mirroring
    `fixSet_evalMap_nonAnc_compat`.  The only new case is `.random u`
    parent with `u ∈ Z`: LHS's `fixMonoParentMap` routes to the `.fixed u`
    coordinate of the M2-tuple (which reads `s' ⟨.fixed u, _⟩`); RHS
    falls through to a recursive `M1.evalMap` at `.random u` which the
    level-set hypothesis collapses to the same `s' ⟨.fixed u, _⟩`. -/
theorem fixSet_evalMap_levelset_compat
    (M' : Causalean.SCM N Ω) (Z : Finset N)
    (hZ_obs : ∀ D ∈ Z, SWIGNode.random D ∈ M'.observed)
    (hZ_fixed : ∀ D ∈ Z, SWIGNode.fixed D ∉ M'.fixed)
    (s' : (M'.fixSet Z hZ_obs hZ_fixed).FixedValues)
    (ℓ : (M'.fixSet Z hZ_obs hZ_fixed).LatentValues)
    (hLevelSet : ∀ D (hD : D ∈ Z),
      M'.evalMap
          (M'.fixSetProj Z hZ_obs hZ_fixed s')
          (valuesProjection
            (le_of_eq
              (fixSet_unobserved M' Z hZ_obs hZ_fixed).symm)
            ℓ)
          ⟨SWIGNode.random D, Finset.mem_union_left _ (hZ_obs D hD)⟩
        = s' ⟨SWIGNode.fixed D,
            SCM.fixed_mem_fixSet M'
              Z hZ_obs hZ_fixed hD⟩)
    {v : SWIGNode N}
    (hv : v ∈ (M'.fixSet Z hZ_obs hZ_fixed).observed) :
    (M'.fixSet Z hZ_obs hZ_fixed).evalMap s' ℓ
        ⟨v, Finset.mem_union_left _ hv⟩
      = M'.evalMap
          (M'.fixSetProj Z hZ_obs hZ_fixed s')
          (valuesProjection
            (le_of_eq
              (fixSet_unobserved M' Z hZ_obs hZ_fixed).symm)
            ℓ)
          ⟨v, Finset.mem_union_left _
            (le_of_eq (fixSet_observed M' Z hZ_obs hZ_fixed)
              hv)⟩ := by
  classical
  let M1 := M'
  let M2 := M1.fixSet Z hZ_obs hZ_fixed
  have h_obs_eq : M2.observed = M1.observed := rfl
  have h_unobs : M2.unobserved = M1.unobserved := rfl
  let s_M1 : M1.FixedValues := M1.fixSetProj Z hZ_obs hZ_fixed s'
  let ℓ_M1 : M1.LatentValues := valuesProjection (le_of_eq h_unobs.symm) ℓ
  -- Strong recursion on `M2.observedIndex ⟨v, hv⟩`.
  suffices h_obs : ∀ (n : ℕ) (w : SWIGNode N) (hw : w ∈ M2.observed),
      (M2.observedIndex ⟨w, hw⟩).val = n →
      M2.evalMap s' ℓ ⟨w, Finset.mem_union_left _ hw⟩ =
        M1.evalMap s_M1 ℓ_M1 ⟨w, Finset.mem_union_left _ hw⟩ by
    exact h_obs _ v hv rfl
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro v hv hidx
    have hv_M1 : v ∈ M1.observed := hv
    rw [SCM.evalMap_observed_unfold M2 s' ℓ ⟨v, hv⟩,
        SCM.evalMap_observed_unfold M1 s_M1 ℓ_M1 ⟨v, hv_M1⟩]
    -- Unfold `M2.structFun ⟨v, _⟩` to `M1.structFun ⟨v, _⟩ ∘ fixMonoParentMap`.
    change M1.structFun ⟨v, hv_M1⟩
        (fixMonoParentMap M1.toSWIGGraph Z hZ_obs hZ_fixed v
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
      = M1.structFun ⟨v, hv_M1⟩ (fun w : {w // w ∈ M1.dag.parents v} =>
          if huo : w.val ∈ M1.unobserved then ℓ_M1 ⟨w.val, huo⟩
          else if hfix : w.val ∈ M1.fixed then s_M1 ⟨w.val, hfix⟩
          else
            have hedge : M1.dag.edge w.val v := M1.dag.mem_parents.mp w.property
            have hobs : w.val ∈ M1.observed := by
              rcases Finset.mem_union.mp (M1.dag_edges_classified _ _ hedge).1
                with h1 | h2
              · rcases Finset.mem_union.mp h1 with hfx | hob
                · exact absurd hfx hfix
                · exact hob
              · exact absurd h2 huo
            M1.evalMap s_M1 ℓ_M1 ⟨w.val, Finset.mem_union_left _ hobs⟩)
    congr 1
    funext w
    rcases w with ⟨wVal, hwVal_M1⟩
    cases wVal with
    | random u =>
      by_cases hu_Z : u ∈ Z
      · -- **New case for Rule 2**: u ∈ Z.  LHS reads M2-tuple at `.fixed u`
        -- (via `fixMonoParentMap_apply_random` since Z is the split target).
        rw [fixMonoParentMap_apply_random M1.toSWIGGraph Z hZ_obs hZ_fixed v u hu_Z _
              hwVal_M1]
        -- LHS evaluation at `.fixed u`: not unobserved (.fixed nodes are fixed),
        -- is in M2.fixed via Z.image .fixed.
        have huo_M2 : (SWIGNode.fixed u : SWIGNode N) ∉ M2.unobserved := by
          intro h
          rcases M2.unobserved_is_random _ h with ⟨_, hEq⟩; cases hEq
        have hfix_M2 : (SWIGNode.fixed u : SWIGNode N) ∈ M2.fixed :=
          SCM.fixed_mem_fixSet M1 Z hZ_obs hZ_fixed hu_Z
        simp only [dif_neg huo_M2, dif_pos hfix_M2]
        -- RHS evaluation at `.random u`: observed, so falls through to
        -- a recursive M1.evalMap call.  Use the level-set hypothesis.
        have hobs_M1 : (SWIGNode.random u : SWIGNode N) ∈ M1.observed :=
          hZ_obs u hu_Z
        have huo_M1 : (SWIGNode.random u : SWIGNode N) ∉ M1.unobserved :=
          Finset.disjoint_left.mp M1.obs_unobs_disjoint hobs_M1
        have hfix_M1 : (SWIGNode.random u : SWIGNode N) ∉ M1.fixed := by
          intro h
          rcases M1.fixed_is_fixed _ h with ⟨_, hEq⟩; cases hEq
        simp only [dif_neg huo_M1, dif_neg hfix_M1]
        -- RHS = M1.evalMap s_M1 ℓ_M1 ⟨.random u, _⟩ = s' ⟨.fixed u, _⟩
        -- by the level-set hypothesis.
        exact (hLevelSet u hu_Z).symm
      · -- **Old case (Rule 3 mirror)**: u ∉ Z.  fixMonoParentMap acts
        -- identity-like at `.random u`.
        rw [fixMonoParentMap_apply_random_notMem M1.toSWIGGraph Z hZ_obs hZ_fixed v _ u
          hu_Z hwVal_M1]
        by_cases huo : (SWIGNode.random u : SWIGNode N) ∈ M1.unobserved
        · have huo_M2 : SWIGNode.random u ∈ M2.unobserved := huo
          simp only [dif_pos huo, dif_pos huo_M2]
          rfl
        · have huo_M2 : SWIGNode.random u ∉ M2.unobserved := huo
          simp only [dif_neg huo, dif_neg huo_M2]
          by_cases hfix : (SWIGNode.random u : SWIGNode N) ∈ M1.fixed
          · exfalso
            rcases M1.fixed_is_fixed _ hfix with ⟨_, hfix_eq⟩; cases hfix_eq
          · have hfix_M2 : (SWIGNode.random u : SWIGNode N) ∉ M2.fixed := by
              intro h
              have : (SWIGNode.random u : SWIGNode N) ∈
                  M1.fixed ∪ Z.image SWIGNode.fixed := h
              rcases Finset.mem_union.mp this with h1 | h2
              · exact hfix h1
              · rcases Finset.mem_image.mp h2 with ⟨_, _, hEq⟩; cases hEq
            simp only [dif_neg hfix, dif_neg hfix_M2]
            -- Observed case: apply IH.
            have hobs_M1 : (SWIGNode.random u : SWIGNode N) ∈ M1.observed := by
              have hedge_M1 : M1.dag.edge (SWIGNode.random u) v :=
                M1.dag.mem_parents.mp hwVal_M1
              rcases Finset.mem_union.mp (M1.dag_edges_classified _ _ hedge_M1).1
                with h1 | h2
              · rcases Finset.mem_union.mp h1 with hfx | hob
                · exact absurd hfx hfix
                · exact hob
              · exact absurd h2 huo
            have hobs_M2 : (SWIGNode.random u : SWIGNode N) ∈ M2.observed := hobs_M1
            -- Need: .random u ∈ M2.dag.parents v to apply the index-decrease lemma.
            -- Since u ∉ Z and .random u ∈ M1.dag.parents v, the splitMono_parents_char
            -- keeps .random u as a parent in M2.
            have hwVal_M2 : SWIGNode.random u ∈ M2.dag.parents v :=
              (SWIGGraph.splitMono_parents_char M1.toSWIGGraph Z hZ_obs hZ_fixed
                v (SWIGNode.random u)).2
                (Or.inl ⟨hwVal_M1,
                  fun D hD heq => hu_Z (SWIGNode.random.inj heq ▸ hD)⟩)
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
            exact ih _ hidx_w (SWIGNode.random u) hobs_M2 rfl
    | fixed d =>
      -- `.fixed d` parent: copies through.
      rw [fixMonoParentMap_apply_fixed M1.toSWIGGraph Z hZ_obs hZ_fixed v _ d hwVal_M1]
      have huo : (SWIGNode.fixed d : SWIGNode N) ∉ M1.unobserved := by
        intro h
        rcases M1.unobserved_is_random _ h with ⟨_, hEq⟩; cases hEq
      have huo_M2 : (SWIGNode.fixed d : SWIGNode N) ∉ M2.unobserved := huo
      simp only [dif_neg huo, dif_neg huo_M2]
      by_cases hfix_M1 : (SWIGNode.fixed d : SWIGNode N) ∈ M1.fixed
      · have hfix_M2 : (SWIGNode.fixed d : SWIGNode N) ∈ M2.fixed := by
          change _ ∈ M1.fixed ∪ Z.image SWIGNode.fixed
          exact Finset.mem_union_left _ hfix_M1
        simp only [dif_pos hfix_M1, dif_pos hfix_M2]
        rfl
      · by_cases hd_Z : d ∈ Z
        · exfalso
          have := M1.fixed_outside_fixed_isolated d hfix_M1
          have hCh : v ∈ M1.dag.children (SWIGNode.fixed d) :=
            M1.dag.mem_children.mpr (M1.dag.mem_parents.mp hwVal_M1)
          simpa [this.2] using hCh
        · have hfix_M2 : (SWIGNode.fixed d : SWIGNode N) ∉ M2.fixed := by
            intro h
            rcases Finset.mem_union.mp
                (show _ ∈ M1.fixed ∪ Z.image SWIGNode.fixed from h) with h1 | h2
            · exact hfix_M1 h1
            · rcases Finset.mem_image.mp h2 with ⟨d', hd'Z, hEq⟩
              have : d = d' := SWIGNode.fixed.inj hEq.symm
              exact hd_Z (this ▸ hd'Z)
          simp only [dif_neg hfix_M1, dif_neg hfix_M2]
          exfalso
          have hobs : (SWIGNode.fixed d : SWIGNode N) ∈ M1.observed := by
            have hedge_M1 : M1.dag.edge (SWIGNode.fixed d) v :=
              M1.dag.mem_parents.mp hwVal_M1
            rcases Finset.mem_union.mp (M1.dag_edges_classified _ _ hedge_M1).1
              with h1 | h2
            · rcases Finset.mem_union.mp h1 with hfx | hob
              · exact absurd hfx hfix_M1
              · exact hob
            · exact absurd h2 huo
          rcases M1.observed_is_random _ hobs with ⟨_, hEq⟩; cases hEq

set_option maxHeartbeats 800000 in
/-- M2-direction level-set evalMap bridge for Rule 2.

    Variant of `fixSet_evalMap_levelset_compat` with the level-set hypothesis
    stated on `M2`'s evaluation (rather than `M1`'s): if `ℓ` satisfies
    `M2.evalMap s' ℓ ⟨.random D, _⟩ = s' ⟨.fixed D, _⟩` for every `D ∈ Z`,
    then `M2.evalMap s' ℓ` and `M1.evalMap (fixSetProj s') (cast ℓ)`
    agree at every observed node `v`.

    Key difference from `fixSet_evalMap_levelset_compat`:
    strong induction uses `M1.observedIndex` (not `M2.observedIndex`)
    because the `u ∈ Z` parent case needs an IH recursion on `.random u`,
    and `.random u` is a parent of `v` in `M1.dag` but *not* in `M2.dag`
    (Z's outgoing edges are rewired to `.fixed` copies in the split).
    M1's topological index still respects M2's DAG ordering because M2
    has fewer observed→observed edges than M1 (every random→random edge
    from Z is moved to a fixed→random edge in M2).

    At the `u ∈ Z` branch: apply IH at `.random u` to get
    `M2 at .random u = M1 at .random u`, then `hLS_M2` gives
    `M2 at .random u = z_u`, concluding `M1 at .random u = z_u`. -/
theorem fixSet_evalMap_levelset_compat_M2
    (M' : Causalean.SCM N Ω) (Z : Finset N)
    (hZ_obs : ∀ D ∈ Z, SWIGNode.random D ∈ M'.observed)
    (hZ_fixed : ∀ D ∈ Z, SWIGNode.fixed D ∉ M'.fixed)
    (s' : (M'.fixSet Z hZ_obs hZ_fixed).FixedValues)
    (ℓ : (M'.fixSet Z hZ_obs hZ_fixed).LatentValues)
    (hLS_M2 : ∀ D (hD : D ∈ Z),
      (M'.fixSet Z hZ_obs hZ_fixed).evalMap s' ℓ
          ⟨SWIGNode.random D, Finset.mem_union_left _ (hZ_obs D hD)⟩
        = s' ⟨SWIGNode.fixed D,
            SCM.fixed_mem_fixSet M'
              Z hZ_obs hZ_fixed hD⟩)
    {v : SWIGNode N}
    (hv : v ∈ (M'.fixSet Z hZ_obs hZ_fixed).observed) :
    (M'.fixSet Z hZ_obs hZ_fixed).evalMap s' ℓ
        ⟨v, Finset.mem_union_left _ hv⟩
      = M'.evalMap
          (M'.fixSetProj Z hZ_obs hZ_fixed s')
          (valuesProjection
            (le_of_eq
              (fixSet_unobserved M' Z hZ_obs hZ_fixed).symm)
            ℓ)
          ⟨v, Finset.mem_union_left _
            (le_of_eq (fixSet_observed M' Z hZ_obs hZ_fixed)
              hv)⟩ := by
  classical
  let M1 := M'
  let M2 := M1.fixSet Z hZ_obs hZ_fixed
  have h_obs_eq : M2.observed = M1.observed := rfl
  have h_unobs : M2.unobserved = M1.unobserved := rfl
  let s_M1 : M1.FixedValues := M1.fixSetProj Z hZ_obs hZ_fixed s'
  let ℓ_M1 : M1.LatentValues := valuesProjection (le_of_eq h_unobs.symm) ℓ
  -- Strong recursion on `M1.observedIndex ⟨v, hv⟩`.
  suffices h_obs : ∀ (n : ℕ) (w : SWIGNode N) (hw : w ∈ M2.observed),
      (M1.observedIndex ⟨w, hw⟩).val = n →
      M2.evalMap s' ℓ ⟨w, Finset.mem_union_left _ hw⟩ =
        M1.evalMap s_M1 ℓ_M1 ⟨w, Finset.mem_union_left _ hw⟩ by
    exact h_obs _ v hv rfl
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro v hv hidx
    have hv_M1 : v ∈ M1.observed := hv
    rw [SCM.evalMap_observed_unfold M2 s' ℓ ⟨v, hv⟩,
        SCM.evalMap_observed_unfold M1 s_M1 ℓ_M1 ⟨v, hv_M1⟩]
    change M1.structFun ⟨v, hv_M1⟩
        (fixMonoParentMap M1.toSWIGGraph Z hZ_obs hZ_fixed v
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
      = M1.structFun ⟨v, hv_M1⟩ (fun w : {w // w ∈ M1.dag.parents v} =>
          if huo : w.val ∈ M1.unobserved then ℓ_M1 ⟨w.val, huo⟩
          else if hfix : w.val ∈ M1.fixed then s_M1 ⟨w.val, hfix⟩
          else
            have hedge : M1.dag.edge w.val v := M1.dag.mem_parents.mp w.property
            have hobs : w.val ∈ M1.observed := by
              rcases Finset.mem_union.mp (M1.dag_edges_classified _ _ hedge).1
                with h1 | h2
              · rcases Finset.mem_union.mp h1 with hfx | hob
                · exact absurd hfx hfix
                · exact hob
              · exact absurd h2 huo
            M1.evalMap s_M1 ℓ_M1 ⟨w.val, Finset.mem_union_left _ hobs⟩)
    congr 1
    funext w
    rcases w with ⟨wVal, hwVal_M1⟩
    cases wVal with
    | random u =>
      by_cases hu_Z : u ∈ Z
      · -- u ∈ Z: IH + hLS_M2 replaces the direct `hLevelSet` appeal.
        rw [fixMonoParentMap_apply_random M1.toSWIGGraph Z hZ_obs hZ_fixed v u hu_Z _
              hwVal_M1]
        have huo_M2 : (SWIGNode.fixed u : SWIGNode N) ∉ M2.unobserved := by
          intro h
          rcases M2.unobserved_is_random _ h with ⟨_, hEq⟩; cases hEq
        have hfix_M2 : (SWIGNode.fixed u : SWIGNode N) ∈ M2.fixed :=
          SCM.fixed_mem_fixSet M1 Z hZ_obs hZ_fixed hu_Z
        simp only [dif_neg huo_M2, dif_pos hfix_M2]
        have hobs_M1_u : (SWIGNode.random u : SWIGNode N) ∈ M1.observed :=
          hZ_obs u hu_Z
        have huo_M1 : (SWIGNode.random u : SWIGNode N) ∉ M1.unobserved :=
          Finset.disjoint_left.mp M1.obs_unobs_disjoint hobs_M1_u
        have hfix_M1 : (SWIGNode.random u : SWIGNode N) ∉ M1.fixed := by
          intro h
          rcases M1.fixed_is_fixed _ h with ⟨_, hEq⟩; cases hEq
        simp only [dif_neg huo_M1, dif_neg hfix_M1]
        -- IH at `.random u` via M1.observed_parent_index_lt (edge in M1.dag).
        have hobs_M2_u : (SWIGNode.random u : SWIGNode N) ∈ M2.observed := hobs_M1_u
        have hidx_u : (M1.observedIndex ⟨SWIGNode.random u, hobs_M1_u⟩).val
                        < (M1.observedIndex ⟨v, hv_M1⟩).val := by
          have hedge_M1 : M1.dag.edge (SWIGNode.random u) v :=
            M1.dag.mem_parents.mp hwVal_M1
          have hv_eq : (M1.observedAt
              ⟨(M1.observedIndex ⟨v, hv_M1⟩).val,
                (M1.observedIndex ⟨v, hv_M1⟩).isLt⟩).val = v := by
            have := M1.observedAt_observedIndex ⟨v, hv_M1⟩
            convert this
          have hedge_M1' : M1.dag.edge (SWIGNode.random u)
              (M1.observedAt
                ⟨(M1.observedIndex ⟨v, hv_M1⟩).val,
                  (M1.observedIndex ⟨v, hv_M1⟩).isLt⟩).val := by
            rw [hv_eq]; exact hedge_M1
          exact M1.observed_parent_index_lt
            (M1.observedIndex ⟨v, hv_M1⟩).isLt hedge_M1' hobs_M1_u
        rw [hidx] at hidx_u
        have h_ih := ih _ hidx_u (SWIGNode.random u) hobs_M2_u rfl
        -- h_ih: M2 at .random u = M1 at .random u.  Combined with hLS_M2: M1 at .random u = z_u.
        rw [← h_ih]
        exact (hLS_M2 u hu_Z).symm
      · -- u ∉ Z: structurally identical to levelset_compat's u ∉ Z branch,
        -- but IH indexes on M1.observedIndex (natural since the edge is in M1.dag).
        rw [fixMonoParentMap_apply_random_notMem M1.toSWIGGraph Z hZ_obs hZ_fixed v _ u
          hu_Z hwVal_M1]
        by_cases huo : (SWIGNode.random u : SWIGNode N) ∈ M1.unobserved
        · have huo_M2 : SWIGNode.random u ∈ M2.unobserved := huo
          simp only [dif_pos huo, dif_pos huo_M2]
          rfl
        · have huo_M2 : SWIGNode.random u ∉ M2.unobserved := huo
          simp only [dif_neg huo, dif_neg huo_M2]
          by_cases hfix : (SWIGNode.random u : SWIGNode N) ∈ M1.fixed
          · exfalso
            rcases M1.fixed_is_fixed _ hfix with ⟨_, hfix_eq⟩; cases hfix_eq
          · have hfix_M2 : (SWIGNode.random u : SWIGNode N) ∉ M2.fixed := by
              intro h
              have : (SWIGNode.random u : SWIGNode N) ∈
                  M1.fixed ∪ Z.image SWIGNode.fixed := h
              rcases Finset.mem_union.mp this with h1 | h2
              · exact hfix h1
              · rcases Finset.mem_image.mp h2 with ⟨_, _, hEq⟩; cases hEq
            simp only [dif_neg hfix, dif_neg hfix_M2]
            have hobs_M1 : (SWIGNode.random u : SWIGNode N) ∈ M1.observed := by
              have hedge_M1 : M1.dag.edge (SWIGNode.random u) v :=
                M1.dag.mem_parents.mp hwVal_M1
              rcases Finset.mem_union.mp (M1.dag_edges_classified _ _ hedge_M1).1
                with h1 | h2
              · rcases Finset.mem_union.mp h1 with hfx | hob
                · exact absurd hfx hfix
                · exact hob
              · exact absurd h2 huo
            have hobs_M2 : (SWIGNode.random u : SWIGNode N) ∈ M2.observed := hobs_M1
            have hidx_w : (M1.observedIndex ⟨SWIGNode.random u, hobs_M1⟩).val
                            < (M1.observedIndex ⟨v, hv_M1⟩).val := by
              have hedge_M1 : M1.dag.edge (SWIGNode.random u) v :=
                M1.dag.mem_parents.mp hwVal_M1
              have hv_eq : (M1.observedAt
                  ⟨(M1.observedIndex ⟨v, hv_M1⟩).val,
                    (M1.observedIndex ⟨v, hv_M1⟩).isLt⟩).val = v := by
                have := M1.observedAt_observedIndex ⟨v, hv_M1⟩
                convert this
              have hedge_M1' : M1.dag.edge (SWIGNode.random u)
                  (M1.observedAt
                    ⟨(M1.observedIndex ⟨v, hv_M1⟩).val,
                      (M1.observedIndex ⟨v, hv_M1⟩).isLt⟩).val := by
                rw [hv_eq]; exact hedge_M1
              exact M1.observed_parent_index_lt
                (M1.observedIndex ⟨v, hv_M1⟩).isLt hedge_M1' hobs_M1
            rw [hidx] at hidx_w
            exact ih _ hidx_w (SWIGNode.random u) hobs_M2 rfl
    | fixed d =>
      -- Unchanged from levelset_compat.
      rw [fixMonoParentMap_apply_fixed M1.toSWIGGraph Z hZ_obs hZ_fixed v _ d hwVal_M1]
      have huo : (SWIGNode.fixed d : SWIGNode N) ∉ M1.unobserved := by
        intro h
        rcases M1.unobserved_is_random _ h with ⟨_, hEq⟩; cases hEq
      have huo_M2 : (SWIGNode.fixed d : SWIGNode N) ∉ M2.unobserved := huo
      simp only [dif_neg huo, dif_neg huo_M2]
      by_cases hfix_M1 : (SWIGNode.fixed d : SWIGNode N) ∈ M1.fixed
      · have hfix_M2 : (SWIGNode.fixed d : SWIGNode N) ∈ M2.fixed := by
          change _ ∈ M1.fixed ∪ Z.image SWIGNode.fixed
          exact Finset.mem_union_left _ hfix_M1
        simp only [dif_pos hfix_M1, dif_pos hfix_M2]
        rfl
      · by_cases hd_Z : d ∈ Z
        · exfalso
          have := M1.fixed_outside_fixed_isolated d hfix_M1
          have hCh : v ∈ M1.dag.children (SWIGNode.fixed d) :=
            M1.dag.mem_children.mpr (M1.dag.mem_parents.mp hwVal_M1)
          simpa [this.2] using hCh
        · have hfix_M2 : (SWIGNode.fixed d : SWIGNode N) ∉ M2.fixed := by
            intro h
            rcases Finset.mem_union.mp
                (show _ ∈ M1.fixed ∪ Z.image SWIGNode.fixed from h) with h1 | h2
            · exact hfix_M1 h1
            · rcases Finset.mem_image.mp h2 with ⟨d', hd'Z, hEq⟩
              have : d = d' := SWIGNode.fixed.inj hEq.symm
              exact hd_Z (this ▸ hd'Z)
          simp only [dif_neg hfix_M1, dif_neg hfix_M2]
          exfalso
          have hobs : (SWIGNode.fixed d : SWIGNode N) ∈ M1.observed := by
            have hedge_M1 : M1.dag.edge (SWIGNode.fixed d) v :=
              M1.dag.mem_parents.mp hwVal_M1
            rcases Finset.mem_union.mp (M1.dag_edges_classified _ _ hedge_M1).1
              with h1 | h2
            · rcases Finset.mem_union.mp h1 with hfx | hob
              · exact absurd hfx hfix_M1
              · exact hob
            · exact absurd h2 huo
          rcases M1.observed_is_random _ hobs with ⟨_, hEq⟩; cases hEq

end SCM

end Causalean
