/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Counterfactual Lemmas for the SCM Layer

Pathwise pushforward identities used by the PO ↔ SCM bridge in
`Causalean/PO/Bridge/FromSCM.lean`:

- `evalMap_fixSet_factual_eq`   ↔  prop:scm-cf-consistency (lines 475–480)
- `evalMap_fixSet_union_eq`     is a composition lemma with an intermediate-value
  hypothesis for a combined intervention, not an order-invariance theorem.

The one-step helper lemmas expose how interventions feed assigned values into
the original structural equations; the pathwise identities use induction along
the topological order in `Evaluation.lean`.
-/

import Causalean.SCM.Model.Evaluation
import Causalean.SCM.Model.InterventionSet

/-! # Counterfactual Identities for Structural Causal Models

This file proves pathwise identities relating evaluation of a structural causal
model before and after interventions. The one-step lemmas
`fixMono_structFun_apply`, `fixSet_structFun_apply`, and
`evalMap_fixSet_observed_apply` expose how intervened parent values enter the
original structural equations. The main theorems `evalMap_fixSet_factual_eq` and
`evalMap_fixSet_union_eq` provide SCM-level factual consistency and composition
with an intermediate-value hypothesis, which are used by the potential-outcome
bridge. -/

namespace Causalean
namespace SCM

universe uN uΩ
variable {N : Type uN} [DecidableEq N] [Fintype N]
variable {Ω : N → Type uΩ} [∀ n, MeasurableSpace (Ω n)]

-- ============================================================
-- § 0. One-step observed-node unfold after interventions
-- ============================================================

/-- After an intervention on a set of observed variables, each observed variable
is still computed by the original structural equation, with intervened parents
replaced by their assigned intervention values. -/
@[simp] lemma fixMono_structFun_apply
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (v : {v // v ∈ (M.fixMono X hObs hFix).observed})
    (ξ : ∀ w : {w // w ∈ (M.fixMono X hObs hFix).dag.parents v.val}, swigΩ Ω w.val) :
    (M.fixMono X hObs hFix).structFun v ξ =
      M.structFun ⟨v.val, v.property⟩
        (fixMonoParentMap M.toSWIGGraph X hObs hFix v.val ξ) := by
  rfl

/-- After an intervention on a set of observed variables, each observed variable
is still computed by the original structural equation, with intervened parents
replaced by their assigned intervention values. -/
@[simp] lemma fixSet_structFun_apply
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (v : {v // v ∈ (M.fixSet X hObs hFix).observed})
    (ξ : ∀ w : {w // w ∈ (M.fixSet X hObs hFix).dag.parents v.val}, swigΩ Ω w.val) :
    (M.fixSet X hObs hFix).structFun v ξ =
      M.structFun ⟨v.val, v.property⟩
        (fixMonoParentMap M.toSWIGGraph X hObs hFix v.val ξ) := by
  rfl

/-- For one recursive evaluation step after an intervention, the value of an
observed variable is the original structural equation evaluated at the parent
values where intervened parents are pinned to their assigned intervention
values. -/
lemma evalMap_fixSet_observed_apply
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (sx : FixedValues (M.fixSet X hObs hFix)) (ℓ : LatentValues M)
    (v : {v // v ∈ M.observed}) :
    (M.fixSet X hObs hFix).evalMap sx ℓ
        ⟨v.val, Finset.mem_union_left _ v.property⟩ =
      M.structFun v
        (fixMonoParentMap M.toSWIGGraph X hObs hFix v.val
          (fun w : {w // w ∈ (M.fixSet X hObs hFix).dag.parents v.val} =>
            if huo : w.val ∈ (M.fixSet X hObs hFix).unobserved then ℓ ⟨w.val, huo⟩
            else if hfix : w.val ∈ (M.fixSet X hObs hFix).fixed then sx ⟨w.val, hfix⟩
            else
              have hedge : (M.fixSet X hObs hFix).dag.edge w.val v.val :=
                (M.fixSet X hObs hFix).dag.mem_parents.mp w.property
              have hobs : w.val ∈ (M.fixSet X hObs hFix).observed := by
                rcases Finset.mem_union.mp
                    ((M.fixSet X hObs hFix).dag_edges_classified _ _ hedge).1 with h1 | h2
                · rcases Finset.mem_union.mp h1 with hfx | hob
                  · exact absurd hfx hfix
                  · exact hob
                · exact absurd h2 huo
              (M.fixSet X hObs hFix).evalMap sx ℓ
                ⟨w.val, Finset.mem_union_left _ hobs⟩)) := by
  rw [evalMap_observed_unfold (M.fixSet X hObs hFix) sx ℓ ⟨v.val, v.property⟩]
  rw [fixSet_structFun_apply]
  rfl

-- ============================================================
-- § 1. Factual consistency (prop:scm-cf-consistency)
-- ============================================================

/-- **prop:scm-cf-consistency** (Basic Concepts.tex L475–480).

    On the event that the natural value of each `D ∈ X` already equals the
    intervention assignment `sx ⟨.fixed D, _⟩`, evaluating `M.fixSet X` with
    combined fixed assignment `sx` agrees pathwise with evaluating the base
    `M` with `s` on every observed node `v.val` not in `X.image .random`.

    Hypotheses:
    - `hOld`: `sx` agrees with `s` on the original `M.fixed` coordinates.
    - `hNew`: for each `D ∈ X`, the base evaluation at `.random D` already
      matches the intervention value `sx ⟨.fixed D, _⟩`.
    - `hv_disj`: the target `v.val` is not one of the intervened `.random D`. -/
theorem evalMap_fixSet_factual_eq
    (M : Causalean.SCM N Ω)
    (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (s : SCM.FixedValues M) (ℓ : SCM.LatentValues M)
    (sx : SCM.FixedValues (M.fixSet X hObs hFix))
    -- sx agrees with s on the original fixed coordinates
    (hOld : ∀ (v : SWIGNode N) (hv : v ∈ M.fixed),
        sx ⟨v, Finset.mem_union_left _ hv⟩ = s ⟨v, hv⟩)
    -- factual condition: base evaluation at .random D equals sx's new fixed value
    (hNew : ∀ D (hD : D ∈ X),
        M.evalMap s ℓ ⟨SWIGNode.random D,
            Finset.mem_union_left _ (hObs D hD)⟩ =
        sx ⟨SWIGNode.fixed D,
              Finset.mem_union_right _ (Finset.mem_image.mpr ⟨D, hD, rfl⟩)⟩)
    -- target is not one of the intervened nodes
    (v : {v // v ∈ M.observed})
    (hv_disj : ∀ D ∈ X, v.val ≠ SWIGNode.random D) :
    (M.fixSet X hObs hFix).evalMap sx ℓ
        ⟨v.val, Finset.mem_union_left _ v.property⟩ =
    M.evalMap s ℓ ⟨v.val, Finset.mem_union_left _ v.property⟩ := by
  classical
  -- Observed/unobserved/fixed-of-M coincide on (M.fixSet X); only X.image .fixed is extra.
  -- Strengthened claim: agreement at EVERY observed node, by strong induction on M's topo index.
  suffices hstr : ∀ (n : ℕ) (hn : n < M.observed.card),
      (M.fixSet X hObs hFix).evalMap sx ℓ
          ⟨(M.observedAt ⟨n, hn⟩).val,
            Finset.mem_union_left _ ((M.observedAt ⟨n, hn⟩).property)⟩ =
      M.evalMap s ℓ
          ⟨(M.observedAt ⟨n, hn⟩).val,
            Finset.mem_union_left _ ((M.observedAt ⟨n, hn⟩).property)⟩ by
    have hkey := hstr (M.observedIndex ⟨v.val, v.property⟩).val
                  (M.observedIndex ⟨v.val, v.property⟩).isLt
    have hat : (M.observedAt (M.observedIndex ⟨v.val, v.property⟩)).val = v.val :=
      M.observedAt_observedIndex ⟨v.val, v.property⟩
    -- rewrite node back to v.val using subtype-value equality on both evalMap args
    have hsub : (⟨(M.observedAt (M.observedIndex ⟨v.val, v.property⟩)).val,
                  Finset.mem_union_left M.unobserved
                    (M.observedAt (M.observedIndex ⟨v.val, v.property⟩)).property⟩
                  : {w // w ∈ M.randomVars})
              = ⟨v.val, Finset.mem_union_left _ v.property⟩ := Subtype.ext hat
    exact hsub ▸ hkey
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro hn
    -- The target observed node, viewed in M and in M.fixSet X (same observed set, by rfl).
    set w₀ : {v // v ∈ M.observed} := M.observedAt ⟨n, hn⟩ with hw₀
    have hw₀' : w₀.val ∈ (M.fixSet X hObs hFix).observed := w₀.property
    -- Unfold both evalMap calls one structFun step.
    rw [evalMap_observed_unfold M s ℓ w₀,
        evalMap_observed_unfold (M.fixSet X hObs hFix) sx ℓ ⟨w₀.val, hw₀'⟩]
    -- The fixSet structFun is M.structFun reindexed via fixMonoParentMap (definitional).
    refine Eq.trans
      (b := M.structFun w₀ (fixMonoParentMap M.toSWIGGraph X hObs hFix w₀.val
        (fun w => if huo : (w : {w // w ∈ (M.fixSet X hObs hFix).dag.parents w₀.val}).val
                      ∈ (M.fixSet X hObs hFix).unobserved then ℓ ⟨w.val, huo⟩
          else if hfix : w.val ∈ (M.fixSet X hObs hFix).fixed then sx ⟨w.val, hfix⟩
          else (M.fixSet X hObs hFix).evalMap sx ℓ ⟨w.val, by
            rcases Finset.mem_union.mp
              (((M.fixSet X hObs hFix).dag_edges_classified _ _
                ((M.fixSet X hObs hFix).dag.mem_parents.mp w.property)).1) with h1 | h2
            · rcases Finset.mem_union.mp h1 with hfx | hob
              · exact absurd hfx hfix
              · exact Finset.mem_union_left _ hob
            · exact absurd h2 huo⟩))) rfl ?_
    -- Now: M.structFun w₀ (fixMonoParentMap ... ξdo) = M.structFun w₀ ξbase.
    -- Peel structFun, prove the parent tuples agree pointwise on M-parents.
    congr 1
    funext w
    -- `w` is an M-parent of `w₀.val`; classify it.
    have hedgeM : M.dag.edge w.val w₀.val := M.dag.mem_parents.mp w.property
    obtain ⟨wVal, hwMem⟩ := w
    simp only at *
    cases wVal with
    | fixed d =>
      -- `.fixed d` is an M-parent ⇒ it must be in `M.fixed` (else isolated).
      have hdfix : SWIGNode.fixed d ∈ M.fixed := by
        by_contra hdf
        have hiso := M.fixed_outside_fixed_isolated d hdf
        have : w₀.val ∈ M.dag.children (SWIGNode.fixed d) :=
          M.dag.mem_children.mpr hedgeM
        rw [hiso.2] at this
        exact (Finset.notMem_empty _) this
      have hdfix' : SWIGNode.fixed d ∈ (M.fixSet X hObs hFix).fixed :=
        Finset.mem_union_left _ hdfix
      have hdnuo : SWIGNode.fixed d ∉ M.unobserved := by
        intro h
        obtain ⟨m, hm⟩ := M.unobserved_is_random _ h
        exact absurd hm (by simp)
      rw [fixMonoParentMap_apply_fixed M.toSWIGGraph X hObs hFix w₀.val _ d hwMem]
      simp only [Subtype.coe_mk]
      -- ξdo at `.fixed d` reads sx; ξbase reads s; equal by hOld.
      split_ifs with h1 <;>
        first
          | exact hOld (SWIGNode.fixed d) hdfix
          | exact absurd h1 hdnuo
    | random u =>
      by_cases hu : u ∈ X
      · -- intervened node: fixMonoParentMap reads `.fixed u`; equal by hNew.
        -- `.random u ∈ M.observed`, hence neither fixed nor unobserved.
        have hru_obs : SWIGNode.random u ∈ M.observed := hObs u hu
        have hru_nuo : SWIGNode.random u ∉ M.unobserved := fun h =>
          (Finset.disjoint_left.mp M.obs_unobs_disjoint hru_obs) h
        have hru_nfix : SWIGNode.random u ∉ M.fixed := by
          intro h; obtain ⟨m, hm⟩ := M.fixed_is_fixed _ h; exact absurd hm (by simp)
        -- `.fixed u ∈ (M.fixSet X).fixed`, not unobserved.
        have hfu : SWIGNode.fixed u ∈ (M.fixSet X hObs hFix).fixed :=
          fixed_mem_fixSet M X hObs hFix hu
        have hfu_nuo : SWIGNode.fixed u ∉ (M.fixSet X hObs hFix).unobserved := by
          intro h
          obtain ⟨m, hm⟩ := (M.fixSet X hObs hFix).unobserved_is_random _ h
          exact absurd hm (by simp)
        rw [fixMonoParentMap_apply_random M.toSWIGGraph X hObs hFix w₀.val u hu _ hwMem]
        simp only [Subtype.coe_mk]
        rw [dif_neg hru_nuo, dif_neg hru_nfix]
        -- ξdo at `.fixed u`: not unobserved, is fixed ⇒ sx ⟨.fixed u⟩.
        rw [dif_neg hfu_nuo, dif_pos hfu]
        exact (hNew u hu).symm
      · -- non-intervened random parent: same classification on both sides.
        have hru_nfix : SWIGNode.random u ∉ M.fixed := by
          intro h; obtain ⟨m, hm⟩ := M.fixed_is_fixed _ h; exact absurd hm (by simp)
        have hru_ndfix : SWIGNode.random u ∉ (M.fixSet X hObs hFix).fixed := by
          intro h
          obtain ⟨m, hm⟩ := (M.fixSet X hObs hFix).fixed_is_fixed _ h
          exact absurd hm (by simp)
        rw [fixMonoParentMap_apply_random_notMem M.toSWIGGraph X hObs hFix w₀.val _ u hu hwMem]
        simp only [Subtype.coe_mk]
        -- Same three-way classification on both sides; resolve simultaneously.
        split_ifs with hd hm hm
        · rfl                            -- both unobserved ⇒ ℓ
        · exact absurd hd hm             -- fixSet-unobs but base-not-unobs (defeq contra)
        · exact absurd hm hd             -- base-unobs but fixSet-not-unobs (defeq contra)
        · -- both observed: recurse via IH at strictly smaller M-index.
          have hru_obs : SWIGNode.random u ∈ M.observed := by
            rcases Finset.mem_union.mp
              (M.dag_edges_classified _ _ hedgeM).1 with hc1 | hc2
            · rcases Finset.mem_union.mp hc1 with hfx | hob
              · exact absurd hfx hru_nfix
              · exact hob
            · exact absurd hc2 hm
          set j := M.observedIndex ⟨SWIGNode.random u, hru_obs⟩ with hj
          have hlt : j.val < n := M.observed_parent_index_lt hn hedgeM hru_obs
          have hihm := ih j.val hlt j.isLt
          -- `⟨j.val, j.isLt⟩ = j` by Fin eta (definitional); node value back to `.random u`.
          have hat : (M.observedAt ⟨j.val, j.isLt⟩).val = SWIGNode.random u :=
            M.observedAt_observedIndex ⟨SWIGNode.random u, hru_obs⟩
          have hsub : (⟨(M.observedAt ⟨j.val, j.isLt⟩).val,
                        Finset.mem_union_left M.unobserved
                          (M.observedAt ⟨j.val, j.isLt⟩).property⟩
                        : {w // w ∈ M.randomVars})
                    = ⟨SWIGNode.random u, Finset.mem_union_left _ hru_obs⟩ :=
            Subtype.ext hat
          -- Transport `hihm` along the node-value equality via an explicit motive.
          refine Eq.ndrec
            (motive := fun w : {w // w ∈ M.randomVars} =>
              (M.fixSet X hObs hFix).evalMap sx ℓ w = M.evalMap s ℓ w)
            hihm hsub

-- ============================================================
-- § 2. Composition with an intermediate-value hypothesis
-- ============================================================

/-- A combined intervention on `X₁ ∪ X₂` agrees with the `X₁` intervention alone
    on a non-intervened observed node when the `X₂` values are already produced
    by the `X₁` intervention.

    The equality compares evaluation after the combined intervention assignment
    `sxU` with evaluation after the `X₁` assignment `sx₁`, provided:
    - `hCompat`: `sxU` agrees with `sx₁` on the `M.fixed ∪ X₁.image .fixed`
      slice (i.e., they match on original fixed and `X₁` intervention coords).
    - `hIntermediate`: the value of `.random D` after the `X₁` intervention
      equals `sxU`'s assignment for each `D ∈ X₂` (the "intermediate" condition).

    This is an SCM-level composition statement, not a comparison of the two
    possible intervention orders. -/
theorem evalMap_fixSet_union_eq
    (M : Causalean.SCM N Ω)
    (X₁ X₂ : Finset N)
    (hDisj : Disjoint X₁ X₂)
    (hObs₁ : ∀ D ∈ X₁, SWIGNode.random D ∈ M.observed)
    (hFix₁ : ∀ D ∈ X₁, SWIGNode.fixed D ∉ M.fixed)
    (hObs₂ : ∀ D ∈ X₂, SWIGNode.random D ∈ M.observed)
    (hFix₂ : ∀ D ∈ X₂, SWIGNode.fixed D ∉ M.fixed)
    (hObsU : ∀ D ∈ X₁ ∪ X₂, SWIGNode.random D ∈ M.observed)
    (hFixU : ∀ D ∈ X₁ ∪ X₂, SWIGNode.fixed D ∉ M.fixed)
    (s : SCM.FixedValues M) (ℓ : SCM.LatentValues M)
    (sx₁ : SCM.FixedValues (M.fixSet X₁ hObs₁ hFix₁))
    (sxU : SCM.FixedValues (M.fixSet (X₁ ∪ X₂) hObsU hFixU))
    -- compatibility: sxU agrees with sx₁ on M.fixed ∪ X₁.image .fixed coords
    (hCompat_old : ∀ (v : SWIGNode N) (hv : v ∈ M.fixed),
        sxU ⟨v, Finset.mem_union_left _ hv⟩ =
        sx₁ ⟨v, Finset.mem_union_left _ hv⟩)
    (hCompat_x₁ : ∀ D (hD : D ∈ X₁),
        sxU ⟨SWIGNode.fixed D,
              Finset.mem_union_right _
                (Finset.mem_image.mpr ⟨D, Finset.mem_union_left _ hD, rfl⟩)⟩ =
        sx₁ ⟨SWIGNode.fixed D,
              Finset.mem_union_right _ (Finset.mem_image.mpr ⟨D, hD, rfl⟩)⟩)
    -- intermediate condition: post-X₁ value of .random D equals sxU's X₂ fixed value
    (hIntermediate : ∀ D (hD : D ∈ X₂),
        (M.fixSet X₁ hObs₁ hFix₁).evalMap sx₁ ℓ
            ⟨SWIGNode.random D,
              Finset.mem_union_left _ (hObs₂ D hD)⟩ =
        sxU ⟨SWIGNode.fixed D,
              Finset.mem_union_right _
                (Finset.mem_image.mpr ⟨D, Finset.mem_union_right _ hD, rfl⟩)⟩)
    -- target is not one of the intervened nodes
    (v : {v // v ∈ M.observed})
    (hv_disj : ∀ D ∈ X₁ ∪ X₂, v.val ≠ SWIGNode.random D) :
    (M.fixSet (X₁ ∪ X₂) hObsU hFixU).evalMap sxU ℓ
        ⟨v.val, Finset.mem_union_left _ v.property⟩ =
    (M.fixSet X₁ hObs₁ hFix₁).evalMap sx₁ ℓ
        ⟨v.val, Finset.mem_union_left _ v.property⟩ := by
  classical
  -- Mirror of `evalMap_fixSet_factual_eq`: strong induction on M's topo index,
  -- comparing `(M.fixSet (X₁∪X₂)).evalMap sxU` with `(M.fixSet X₁).evalMap sx₁`
  -- at every observed node.  The per-parent case analysis collapses the X₂
  -- step via `hIntermediate` and the X₁ step via `hCompat_x₁`.
  suffices hstr : ∀ (n : ℕ) (hn : n < M.observed.card),
      (M.fixSet (X₁ ∪ X₂) hObsU hFixU).evalMap sxU ℓ
          ⟨(M.observedAt ⟨n, hn⟩).val,
            Finset.mem_union_left _ ((M.observedAt ⟨n, hn⟩).property)⟩ =
      (M.fixSet X₁ hObs₁ hFix₁).evalMap sx₁ ℓ
          ⟨(M.observedAt ⟨n, hn⟩).val,
            Finset.mem_union_left _ ((M.observedAt ⟨n, hn⟩).property)⟩ by
    have hkey := hstr (M.observedIndex ⟨v.val, v.property⟩).val
                  (M.observedIndex ⟨v.val, v.property⟩).isLt
    have hat : (M.observedAt (M.observedIndex ⟨v.val, v.property⟩)).val = v.val :=
      M.observedAt_observedIndex ⟨v.val, v.property⟩
    have hsub : (⟨(M.observedAt (M.observedIndex ⟨v.val, v.property⟩)).val,
                  Finset.mem_union_left M.unobserved
                    (M.observedAt (M.observedIndex ⟨v.val, v.property⟩)).property⟩
                  : {w // w ∈ M.randomVars})
              = ⟨v.val, Finset.mem_union_left _ v.property⟩ := Subtype.ext hat
    exact hsub ▸ hkey
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro hn
    set w₀ : {v // v ∈ M.observed} := M.observedAt ⟨n, hn⟩ with hw₀
    have hw₀U : w₀.val ∈ (M.fixSet (X₁ ∪ X₂) hObsU hFixU).observed := w₀.property
    have hw₀₁ : w₀.val ∈ (M.fixSet X₁ hObs₁ hFix₁).observed := w₀.property
    -- Unfold both evalMap calls one structFun step.
    rw [evalMap_observed_unfold (M.fixSet X₁ hObs₁ hFix₁) sx₁ ℓ ⟨w₀.val, hw₀₁⟩,
        evalMap_observed_unfold (M.fixSet (X₁ ∪ X₂) hObsU hFixU) sxU ℓ ⟨w₀.val, hw₀U⟩]
    -- Both fixSet structFuns are `M.structFun w₀` reindexed via `fixMonoParentMap`.
    -- Reduce to: M.structFun w₀ (fixMonoParentMap … X₁∪X₂ ξU)
    --          = M.structFun w₀ (fixMonoParentMap … X₁ ξ₁).
    refine Eq.trans
      (b := M.structFun w₀ (fixMonoParentMap M.toSWIGGraph (X₁ ∪ X₂) hObsU hFixU w₀.val
        (fun w => if huo : (w : {w // w ∈ (M.fixSet (X₁ ∪ X₂) hObsU hFixU).dag.parents w₀.val}).val
                      ∈ (M.fixSet (X₁ ∪ X₂) hObsU hFixU).unobserved then ℓ ⟨w.val, huo⟩
          else if hfix : w.val ∈ (M.fixSet (X₁ ∪ X₂) hObsU hFixU).fixed then sxU ⟨w.val, hfix⟩
          else (M.fixSet (X₁ ∪ X₂) hObsU hFixU).evalMap sxU ℓ ⟨w.val, by
            rcases Finset.mem_union.mp
              (((M.fixSet (X₁ ∪ X₂) hObsU hFixU).dag_edges_classified _ _
                ((M.fixSet (X₁ ∪ X₂) hObsU hFixU).dag.mem_parents.mp w.property)).1) with h1 | h2
            · rcases Finset.mem_union.mp h1 with hfx | hob
              · exact absurd hfx hfix
              · exact Finset.mem_union_left _ hob
            · exact absurd h2 huo⟩))) rfl ?_
    -- Now compare the two parent dispatches directly.
    refine Eq.symm (Eq.trans (b := M.structFun w₀
        (fixMonoParentMap M.toSWIGGraph X₁ hObs₁ hFix₁ w₀.val
        (fun w => if huo : (w : {w // w ∈ (M.fixSet X₁ hObs₁ hFix₁).dag.parents w₀.val}).val
                      ∈ (M.fixSet X₁ hObs₁ hFix₁).unobserved then ℓ ⟨w.val, huo⟩
          else if hfix : w.val ∈ (M.fixSet X₁ hObs₁ hFix₁).fixed then sx₁ ⟨w.val, hfix⟩
          else (M.fixSet X₁ hObs₁ hFix₁).evalMap sx₁ ℓ ⟨w.val, by
            rcases Finset.mem_union.mp
              (((M.fixSet X₁ hObs₁ hFix₁).dag_edges_classified _ _
                ((M.fixSet X₁ hObs₁ hFix₁).dag.mem_parents.mp w.property)).1) with h1 | h2
            · rcases Finset.mem_union.mp h1 with hfx | hob
              · exact absurd hfx hfix
              · exact Finset.mem_union_left _ hob
            · exact absurd h2 huo⟩))) rfl ?_)
    -- Peel structFun; prove the parent tuples agree pointwise on M-parents.
    -- Goal (after symm): structFun(X₁ ξ₁) = structFun(X₁∪X₂ ξU).
    congr 1
    funext w
    have hedgeM : M.dag.edge w.val w₀.val := M.dag.mem_parents.mp w.property
    obtain ⟨wVal, hwMem⟩ := w
    simp only at *
    cases wVal with
    | fixed d =>
      -- `.fixed d` M-parent ⇒ in M.fixed; both sides read their resp. fixed value.
      have hdfix : SWIGNode.fixed d ∈ M.fixed := by
        by_contra hdf
        have hiso := M.fixed_outside_fixed_isolated d hdf
        have : w₀.val ∈ M.dag.children (SWIGNode.fixed d) :=
          M.dag.mem_children.mpr hedgeM
        rw [hiso.2] at this
        exact (Finset.notMem_empty _) this
      have hdnuo : SWIGNode.fixed d ∉ M.unobserved := by
        intro h
        obtain ⟨m, hm⟩ := M.unobserved_is_random _ h
        exact absurd hm (by simp)
      have hd1uo : SWIGNode.fixed d ∉ (M.fixSet X₁ hObs₁ hFix₁).unobserved := hdnuo
      have hdUuo : SWIGNode.fixed d ∉ (M.fixSet (X₁ ∪ X₂) hObsU hFixU).unobserved := hdnuo
      have hd1fix : SWIGNode.fixed d ∈ (M.fixSet X₁ hObs₁ hFix₁).fixed :=
        Finset.mem_union_left _ hdfix
      have hdUfix : SWIGNode.fixed d ∈ (M.fixSet (X₁ ∪ X₂) hObsU hFixU).fixed :=
        Finset.mem_union_left _ hdfix
      rw [fixMonoParentMap_apply_fixed M.toSWIGGraph X₁ hObs₁ hFix₁ w₀.val _ d hwMem,
          fixMonoParentMap_apply_fixed M.toSWIGGraph (X₁ ∪ X₂) hObsU hFixU w₀.val _ d hwMem]
      simp only [Subtype.coe_mk]
      rw [dif_neg hd1uo, dif_pos hd1fix, dif_neg hdUuo, dif_pos hdUfix]
      exact (hCompat_old (SWIGNode.fixed d) hdfix).symm
    | random u =>
      have hru_nfix : SWIGNode.random u ∉ M.fixed := by
        intro h; obtain ⟨m, hm⟩ := M.fixed_is_fixed _ h; exact absurd hm (by simp)
      by_cases hu1 : u ∈ X₁
      · -- u ∈ X₁ ⇒ u ∈ X₁∪X₂; both interventions fix it; equal by hCompat_x₁.
        have huU : u ∈ X₁ ∪ X₂ := Finset.mem_union_left _ hu1
        have hru_nuo : SWIGNode.random u ∉ M.unobserved := fun h =>
          (Finset.disjoint_left.mp M.obs_unobs_disjoint (hObs₁ u hu1)) h
        have hf1 : SWIGNode.fixed u ∈ (M.fixSet X₁ hObs₁ hFix₁).fixed :=
          fixed_mem_fixSet M X₁ hObs₁ hFix₁ hu1
        have hfU : SWIGNode.fixed u ∈ (M.fixSet (X₁ ∪ X₂) hObsU hFixU).fixed :=
          fixed_mem_fixSet M (X₁ ∪ X₂) hObsU hFixU huU
        have hf1_nuo : SWIGNode.fixed u ∉ (M.fixSet X₁ hObs₁ hFix₁).unobserved := by
          intro h
          obtain ⟨m, hm⟩ := (M.fixSet X₁ hObs₁ hFix₁).unobserved_is_random _ h
          exact absurd hm (by simp)
        have hfU_nuo : SWIGNode.fixed u ∉ (M.fixSet (X₁ ∪ X₂) hObsU hFixU).unobserved := by
          intro h
          obtain ⟨m, hm⟩ := (M.fixSet (X₁ ∪ X₂) hObsU hFixU).unobserved_is_random _ h
          exact absurd hm (by simp)
        rw [fixMonoParentMap_apply_random M.toSWIGGraph X₁ hObs₁ hFix₁ w₀.val u hu1 _ hwMem,
            fixMonoParentMap_apply_random M.toSWIGGraph (X₁ ∪ X₂) hObsU hFixU w₀.val u huU _ hwMem]
        simp only [Subtype.coe_mk]
        rw [dif_neg hf1_nuo, dif_pos hf1, dif_neg hfU_nuo, dif_pos hfU]
        -- LHS: sx₁ ⟨.fixed u⟩, RHS: sxU ⟨.fixed u⟩; equal by hCompat_x₁ (symm).
        exact (hCompat_x₁ u hu1).symm
      · by_cases hu2 : u ∈ X₂
        · -- u ∈ X₂ \ X₁: union fixes it (reads sxU ⟨.fixed u⟩);
          -- do(X₁) recurses (reads (M.fixSet X₁).evalMap sx₁ ⟨.random u⟩).
          have huU : u ∈ X₁ ∪ X₂ := Finset.mem_union_right _ hu2
          have hru_obs : SWIGNode.random u ∈ M.observed := hObs₂ u hu2
          have hru_nuo : SWIGNode.random u ∉ M.unobserved := fun h =>
            (Finset.disjoint_left.mp M.obs_unobs_disjoint hru_obs) h
          -- RHS (do X₁) side: u ∉ X₁, so reads .random u; classify it.
          have hru_nd1fix : SWIGNode.random u ∉ (M.fixSet X₁ hObs₁ hFix₁).fixed := by
            intro h
            obtain ⟨m, hm⟩ := (M.fixSet X₁ hObs₁ hFix₁).fixed_is_fixed _ h
            exact absurd hm (by simp)
          have hru_nd1uo : SWIGNode.random u ∉ (M.fixSet X₁ hObs₁ hFix₁).unobserved := hru_nuo
          -- LHS (union) side: reads .fixed u.
          have hfU : SWIGNode.fixed u ∈ (M.fixSet (X₁ ∪ X₂) hObsU hFixU).fixed :=
            fixed_mem_fixSet M (X₁ ∪ X₂) hObsU hFixU huU
          have hfU_nuo : SWIGNode.fixed u ∉ (M.fixSet (X₁ ∪ X₂) hObsU hFixU).unobserved := by
            intro h
            obtain ⟨m, hm⟩ := (M.fixSet (X₁ ∪ X₂) hObsU hFixU).unobserved_is_random _ h
            exact absurd hm (by simp)
          rw [fixMonoParentMap_apply_random_notMem M.toSWIGGraph X₁ hObs₁ hFix₁ w₀.val _ u hu1 hwMem,
              fixMonoParentMap_apply_random M.toSWIGGraph (X₁ ∪ X₂) hObsU hFixU w₀.val u huU _ hwMem]
          simp only [Subtype.coe_mk]
          rw [dif_neg hru_nd1uo, dif_neg hru_nd1fix, dif_neg hfU_nuo, dif_pos hfU]
          -- Goal: (M.fixSet X₁).evalMap sx₁ ℓ ⟨.random u⟩ = sxU ⟨.fixed u⟩.
          -- This is exactly hIntermediate u hu2 (up to membership-proof irrelevance).
          exact hIntermediate u hu2
        · -- u ∉ X₁ ∪ X₂: both recurse; equal by IH at strictly smaller index.
          have huU : u ∉ X₁ ∪ X₂ := fun h =>
            (Finset.mem_union.mp h).elim hu1 hu2
          have hru_nd1fix : SWIGNode.random u ∉ (M.fixSet X₁ hObs₁ hFix₁).fixed := by
            intro h
            obtain ⟨m, hm⟩ := (M.fixSet X₁ hObs₁ hFix₁).fixed_is_fixed _ h
            exact absurd hm (by simp)
          have hru_ndUfix : SWIGNode.random u ∉ (M.fixSet (X₁ ∪ X₂) hObsU hFixU).fixed := by
            intro h
            obtain ⟨m, hm⟩ := (M.fixSet (X₁ ∪ X₂) hObsU hFixU).fixed_is_fixed _ h
            exact absurd hm (by simp)
          rw [fixMonoParentMap_apply_random_notMem M.toSWIGGraph X₁ hObs₁ hFix₁
                w₀.val _ u hu1 hwMem,
              fixMonoParentMap_apply_random_notMem M.toSWIGGraph (X₁ ∪ X₂) hObsU hFixU
                w₀.val _ u huU hwMem]
          simp only [Subtype.coe_mk]
          -- Same three-way classification on both sides.
          split_ifs with hd hm hm
          · rfl
          · exact absurd hd hm
          · exact absurd hm hd
          · -- both observed: recurse via IH at strictly smaller M-index.
            have hru_obs : SWIGNode.random u ∈ M.observed := by
              rcases Finset.mem_union.mp
                (M.dag_edges_classified _ _ hedgeM).1 with hc1 | hc2
              · rcases Finset.mem_union.mp hc1 with hfx | hob
                · exact absurd hfx hru_nfix
                · exact hob
              · exact absurd hc2 hm
            set j := M.observedIndex ⟨SWIGNode.random u, hru_obs⟩ with hj
            have hlt : j.val < n := M.observed_parent_index_lt hn hedgeM hru_obs
            have hihm := ih j.val hlt j.isLt
            have hat : (M.observedAt ⟨j.val, j.isLt⟩).val = SWIGNode.random u :=
              M.observedAt_observedIndex ⟨SWIGNode.random u, hru_obs⟩
            have hsub : (⟨(M.observedAt ⟨j.val, j.isLt⟩).val,
                          Finset.mem_union_left M.unobserved
                            (M.observedAt ⟨j.val, j.isLt⟩).property⟩
                          : {w // w ∈ M.randomVars})
                      = ⟨SWIGNode.random u, Finset.mem_union_left _ hru_obs⟩ :=
              Subtype.ext hat
            -- IH gives `(union).evalMap = (X₁).evalMap`; goal here is the symm.
            refine Eq.symm (Eq.ndrec
              (motive := fun w : {w // w ∈ M.randomVars} =>
                (M.fixSet (X₁ ∪ X₂) hObsU hFixU).evalMap sxU ℓ w =
                  (M.fixSet X₁ hObs₁ hFix₁).evalMap sx₁ ℓ w)
              hihm hsub)

end SCM
end Causalean
