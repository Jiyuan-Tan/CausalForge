/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.SCM.Model.InterventionMono

/-! # Multi-Target Intervention Interface

This file exposes the public interface for set-valued interventions on structural
causal models. It packages the monolithic intervention construction with
preservation lemmas and the fixed-value projections used by the do-calculus
kernel statements.

## Main definitions and results

* `SCM.fixSet` is the public multi-target do-operation, implemented as the
  monolithic intervention `SCM.fixMono`.
* `SCM.fixSet_empty_equiv` shows that intervening on the empty set is
  structurally equivalent to the original model.
* `SCM.fixSet_equiv_congr` transports `SCM.Equiv` through a common intervention
  target set.
* `SCM.swigInterventionSet_insert_equiv` relates iterative singleton insertion
  to the one-shot intervention on `insert y X`.
* `SCM.fixSetProj` and `SCM.fixSetZSlice` provide the fixed-coordinate
  projections used by kernel-level do-calculus statements.
-/

namespace Causalean

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

namespace SCM

-- ============================================================
-- § 1. `fixSet` — monolithic multi-target do
-- ============================================================

/-- **Standard (Pearl) multi-target do** — definitional alias for `fixMono`. -/
noncomputable def fixSet
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed) : Causalean.SCM N Ω :=
  M.fixMono X hObs hFix

-- ============================================================
-- § 2. Interface lemmas
-- ============================================================

/-- `fixSet` preserves `observed`. -/
@[simp] lemma fixSet_observed (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed) :
    (M.fixSet X hObs hFix).observed = M.observed := rfl

/-- `fixSet` preserves `unobserved`. -/
@[simp] lemma fixSet_unobserved (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed) :
    (M.fixSet X hObs hFix).unobserved = M.unobserved := rfl

/-- `fixSet` enlarges `fixed` by exactly `X.image SWIGNode.fixed`. -/
@[simp] lemma fixSet_fixed (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed) :
    (M.fixSet X hObs hFix).fixed = M.fixed ∪ X.image SWIGNode.fixed := rfl

/-- `fixSet` inherits `latentDist` verbatim.  Both sides have the same type
    (`(M.fixSet X _ _).unobserved = M.unobserved` by `rfl`) and equal body. -/
@[simp] lemma fixSet_latentDist (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (u : {u // u ∈ (M.fixSet X hObs hFix).unobserved}) :
    (M.fixSet X hObs hFix).latentDist u = M.latentDist u := rfl

/-- `fixSet` only enlarges the `fixed` set. -/
lemma fixSet_fixed_subset (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed) :
    M.fixed ⊆ (M.fixSet X hObs hFix).fixed :=
  fixMono_fixed_subset M X hObs hFix

/-- `X.image SWIGNode.fixed ⊆ (M.fixSet X _ _).fixed`. -/
lemma fixSet_image_fixed_subset (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed) :
    X.image SWIGNode.fixed ⊆ (M.fixSet X hObs hFix).fixed :=
  fixMono_image_fixed_subset M X hObs hFix

/-- Every `SWIGNode.fixed D` with `D ∈ X` is in the fixed set of `fixSet X`. -/
lemma fixed_mem_fixSet (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    {D : N} (hD : D ∈ X) :
    SWIGNode.fixed D ∈ (M.fixSet X hObs hFix).fixed :=
  fixSet_image_fixed_subset M X hObs hFix
    (Finset.mem_image.mpr ⟨D, hD, rfl⟩)

/-- **SCM-level parent-set coincidence at non-`.fixed`-targeted vertices.**

    If no `SWIGNode.fixed D` (for `D ∈ X`) is a parent of `v` in the
    post-intervention graph `(M.fixSet X)`, then `v`'s parent set in
    `(M.fixSet X)` is identical to `v`'s parent set in `M`.

    Key prerequisite for the Rule 3 non-ancestor `evalMap` bridge
    `fixSet_evalMap_nonAnc_compat` in `Causal/Do/Rule3.lean`. -/
lemma fixSet_parents_eq_of_no_fixed_parent
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    {v : SWIGNode N}
    (hNoFP : ∀ D ∈ X,
      SWIGNode.fixed D ∉ (M.fixSet X hObs hFix).dag.parents v) :
    (M.fixSet X hObs hFix).dag.parents v = M.dag.parents v :=
  fixMono_parents_eq_of_no_fixed_parent M X hObs hFix hNoFP

-- ============================================================
-- § 2b. `fixSet_empty` — intervening on the empty set is equivalent to M
-- ============================================================

/-- **Parent set of `fixSet ∅` coincides with the base.**

    Specialization of `fixSet_parents_eq_of_no_fixed_parent` at `X = ∅`:
    the hypothesis is vacuous (no `D ∈ ∅`), so parents coincide
    unconditionally.  Used by `fixSet_empty_equiv` and by downstream
    single-intervention bridges. -/
lemma fixSet_empty_parents
    (M : Causalean.SCM N Ω)
    (hObs : ∀ D ∈ (∅ : Finset N), SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ (∅ : Finset N), SWIGNode.fixed D ∉ M.fixed)
    (v : SWIGNode N) :
    (M.fixSet ∅ hObs hFix).dag.parents v = M.dag.parents v :=
  fixSet_parents_eq_of_no_fixed_parent M ∅ hObs hFix
    (fun _ hD => absurd hD (Finset.notMem_empty _))

/-- **Edges of `fixSet ∅` coincide with the base.** -/
lemma fixSet_empty_edge
    (M : Causalean.SCM N Ω)
    (hObs : ∀ D ∈ (∅ : Finset N), SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ (∅ : Finset N), SWIGNode.fixed D ∉ M.fixed)
    (u v : SWIGNode N) :
    (M.fixSet ∅ hObs hFix).dag.edge u v ↔ M.dag.edge u v := by
  -- `fixSet ∅ .dag.edge = splitMonoEdgeRel M.dag.edge ∅`, which at `X = ∅`
  -- reduces to `M.dag.edge` by simp.
  cases u with
  | random u =>
    simp [SCM.fixSet, SCM.fixMono, SWIGGraph.splitMono, SWIGGraph.splitMonoDAG,
          SWIGGraph.splitMonoEdgeRel]
  | fixed d =>
    simp [SCM.fixSet, SCM.fixMono, SWIGGraph.splitMono, SWIGGraph.splitMonoDAG,
          SWIGGraph.splitMonoEdgeRel]

/-- **`fixSet ∅` is structurally equivalent to `M`.**

    Since intervening on the empty set performs no rerouting, the
    resulting SCM agrees with `M` on all primitive structural data:
    SWIG graph structure (edges, fixed/observed/unobserved), edge types,
    structural functions (as `HEq`), and latent distributions.

    Note: this is a `SCM.Equiv` statement, not an equality.  The literal
    `M.fixSet ∅ … = M` is **not** provable because `splitMonoTopo` at
    `X = ∅` changes the topological order (each node's topoOrder
    becomes `2·orig + 1`).  The equivalence relation ignores topoOrder,
    which is the right invariant for d-separation and kernel semantics. -/
theorem fixSet_empty_equiv
    (M : Causalean.SCM N Ω)
    (hObs : ∀ D ∈ (∅ : Finset N), SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ (∅ : Finset N), SWIGNode.fixed D ∉ M.fixed) :
    SCM.Equiv (M.fixSet ∅ hObs hFix) M := by
  -- (1) Graph-level equivalence (reused for the parent-set transport below).
  have hGraph : SWIGGraph.Equivalent
      (M.fixSet ∅ hObs hFix).toSWIGGraph M.toSWIGGraph := by
    refine ⟨?_, ?_, rfl, rfl⟩
    · exact fixSet_empty_edge M hObs hFix
    · simp
  refine ⟨hGraph, ?_, ?_, ?_⟩
  · -- (2) Edge-type agreement: the `∃ D ∈ ∅, u = .fixed D` guard is vacuous.
    intro u v _ _
    change (if h : ∃ D ∈ (∅ : Finset N), u = SWIGNode.fixed D then
            M.edgeTypes.edgeType (SWIGNode.random (Classical.choose h)) v
          else M.edgeTypes.edgeType u v)
         = M.edgeTypes.edgeType u v
    rw [dif_neg]
    rintro ⟨D, hD, _⟩
    exact absurd hD (Finset.notMem_empty _)
  · -- (3) HEq structFun, by the standard parent-tuple HEq recipe:
    -- outer `hfunext` over `{v // v ∈ observed}` (defeq on both sides),
    -- inner `hfunext` over parent tuples (domains propositionally equal via
    -- `hGraph.parents_eq`), then reduce `HEq` to `Eq` and show the
    -- `fixMonoParentMap ∅` reindex is the pointwise identity.
    refine Function.hfunext rfl ?_
    rintro v _ hv
    have hv_eq : v = _ := eq_of_heq hv
    subst hv_eq
    refine Function.hfunext ?_ ?_
    · rw [hGraph.parents_eq v.val]
    · rintro ξ₁ ξ₂ hξ
      apply heq_of_eq
      have hP : (M.fixSet ∅ hObs hFix).toSWIGGraph.dag.parents v.val
              = M.toSWIGGraph.dag.parents v.val :=
        hGraph.parents_eq v.val
      -- Pointwise equality of ξ₁ and ξ₂ at matching coordinates, obtained by
      -- reverting both and rewriting `hP` so they end up with the same type.
      have hξ_apply : ∀ (x : SWIGNode N)
          (h₁ : x ∈ (M.fixSet ∅ hObs hFix).toSWIGGraph.dag.parents v.val)
          (h₂ : x ∈ M.toSWIGGraph.dag.parents v.val),
          ξ₁ ⟨x, h₁⟩ = ξ₂ ⟨x, h₂⟩ := by
        revert ξ₁ ξ₂ hξ
        rw [hP]
        rintro ξ₁ ξ₂ hξ x h₁ h₂
        have hξ_eq : ξ₁ = ξ₂ := eq_of_heq hξ
        subst hξ_eq
        rfl
      have h_obs_M : v.val ∈ M.observed := v.property
      -- Unfold `(M.fixSet ∅).structFun v ξ₁` via its `fixMono` definition.
      change M.structFun ⟨v.val, h_obs_M⟩
              (fixMonoParentMap M.toSWIGGraph ∅ hObs hFix v.val ξ₁)
          = M.structFun v ξ₂
      -- Peel `M.structFun ⟨v.val, _⟩`; reduce to tuple-level equality.
      congr 1
      funext ⟨w, hw⟩
      cases w with
      | random u =>
        -- `u ∈ ∅` is vacuous, so `fixMonoParentMap` reads `ξ₁` at `.random u`.
        have hu : u ∉ (∅ : Finset N) := Finset.notMem_empty _
        rw [fixMonoParentMap_apply_random_notMem M.toSWIGGraph ∅ hObs hFix v.val
              ξ₁ u hu hw]
        exact hξ_apply (SWIGNode.random u) _ hw
      | fixed d =>
        -- `fixMonoParentMap` on a `.fixed` coordinate is `rfl`-identity.
        rw [fixMonoParentMap_apply_fixed M.toSWIGGraph ∅ hObs hFix v.val ξ₁ d hw]
        exact hξ_apply (SWIGNode.fixed d) _ hw
  · -- (4) HEq latentDist: inherited verbatim by `fixMono`.
    rfl

-- ============================================================
-- § 2c. `fixSet_equiv_congr` — SCM.Equiv is preserved by fixSet
-- ============================================================

/-- **`fixSet` preserves `SCM.Equiv`.**

    If `M₁` and `M₂` are structurally equivalent, then so are `M₁.fixSet X`
    and `M₂.fixSet X`.  This is the congruence lemma needed to transport
    kernel HEq results across interventions. -/
theorem fixSet_equiv_congr
    {M₁ M₂ : Causalean.SCM N Ω} (h : SCM.Equiv M₁ M₂) (X : Finset N)
    (hObs₁ : ∀ D ∈ X, SWIGNode.random D ∈ M₁.observed)
    (hFix₁ : ∀ D ∈ X, SWIGNode.fixed D ∉ M₁.fixed)
    (hObs₂ : ∀ D ∈ X, SWIGNode.random D ∈ M₂.observed)
    (hFix₂ : ∀ D ∈ X, SWIGNode.fixed D ∉ M₂.fixed) :
    SCM.Equiv (M₁.fixSet X hObs₁ hFix₁) (M₂.fixSet X hObs₂ hFix₂) := by
  obtain ⟨hGraph, hEdgeType, hSF, hLat⟩ := h
  -- (1) Graph-level equivalence via `splitMono_congr`.
  have hGraph' : SWIGGraph.Equivalent
      (M₁.fixSet X hObs₁ hFix₁).toSWIGGraph
      (M₂.fixSet X hObs₂ hFix₂).toSWIGGraph :=
    hGraph.splitMono_congr X hObs₁ hFix₁ hObs₂ hFix₂
  refine ⟨hGraph', ?_, ?_, ?_⟩
  · -- (2) Edge-type agreement.
    -- The `edgeType` of `fixSet` uses a `dite` on `∃ D ∈ X, u = .fixed D`.
    intro u v hu hv
    -- Both sides expand to the same dite structure; split on the guard.
    change (if hh : ∃ D ∈ X, u = SWIGNode.fixed D then
              M₁.edgeTypes.edgeType (SWIGNode.random (Classical.choose hh)) v
            else M₁.edgeTypes.edgeType u v) =
           (if hh : ∃ D ∈ X, u = SWIGNode.fixed D then
              M₂.edgeTypes.edgeType (SWIGNode.random (Classical.choose hh)) v
            else M₂.edgeTypes.edgeType u v)
    split_ifs with hh
    · -- u = .fixed D branch: underlying edge is M.dag.edge (.random D) v.
      -- Retrieve the underlying M₁ and M₂ edges from splitMonoEdgeRel.
      have hD := Classical.choose_spec hh
      -- hu : (M₁.fixSet X).dag.edge u v, which is splitMonoEdgeRel M₁.dag.edge X u v.
      -- With u = .fixed D and D ∈ X, this simplifies to M₁.dag.edge (.random D) v.
      have hu₁ : M₁.dag.edge (SWIGNode.random (Classical.choose hh)) v := by
        have huEq : u = SWIGNode.fixed (Classical.choose hh) := hD.2
        rw [huEq] at hu
        simp only [SCM.fixSet, SCM.fixMono, SWIGGraph.splitMono,
                   SWIGGraph.splitMonoDAG, SWIGGraph.splitMonoEdgeRel,
                   if_pos hD.1] at hu
        exact hu
      have hu₂ : M₂.dag.edge (SWIGNode.random (Classical.choose hh)) v := by
        have huEq : u = SWIGNode.fixed (Classical.choose hh) := hD.2
        rw [huEq] at hv
        simp only [SCM.fixSet, SCM.fixMono, SWIGGraph.splitMono,
                   SWIGGraph.splitMonoDAG, SWIGGraph.splitMonoEdgeRel,
                   if_pos hD.1] at hv
        exact hv
      exact hEdgeType _ _ hu₁ hu₂
    · -- else branch: direct M.dag.edge u v.
      have hu₁ : M₁.dag.edge u v := by
        simp only [SCM.fixSet, SCM.fixMono, SWIGGraph.splitMono,
                   SWIGGraph.splitMonoDAG, SWIGGraph.splitMonoEdgeRel] at hu
        cases u with
        | random r =>
          simp only [SWIGGraph.splitMonoEdgeRel] at hu
          by_cases hr : r ∈ X
          · simp [hr] at hu
          · simpa [hr] using hu
        | fixed d =>
          simp only [SWIGGraph.splitMonoEdgeRel] at hu
          by_cases hd : d ∈ X
          · exfalso; apply hh; exact ⟨d, hd, rfl⟩
          · simpa [hd] using hu
      have hu₂ : M₂.dag.edge u v := by
        simp only [SCM.fixSet, SCM.fixMono, SWIGGraph.splitMono,
                   SWIGGraph.splitMonoDAG, SWIGGraph.splitMonoEdgeRel] at hv
        cases u with
        | random r =>
          simp only [SWIGGraph.splitMonoEdgeRel] at hv
          by_cases hr : r ∈ X
          · simp [hr] at hv
          · simpa [hr] using hv
        | fixed d =>
          simp only [SWIGGraph.splitMonoEdgeRel] at hv
          by_cases hd : d ∈ X
          · exfalso; apply hh; exact ⟨d, hd, rfl⟩
          · simpa [hd] using hv
      exact hEdgeType _ _ hu₁ hu₂
  · -- (3) HEq structFun.
    -- Both `(M_i.fixSet X).structFun v' ξ` unfold to
    --   `M_i.structFun ⟨v'.val, _⟩ (fixMonoParentMap M_i.toSWIGGraph X _ _ v'.val ξ)`.
    -- Outer hfunext: observed domain.
    -- `(M_i.fixSet X).observed = M_i.observed` by rfl, and `M₁.observed = M₂.observed` by hGraph.
    have hObsSplit : (M₁.fixSet X hObs₁ hFix₁).observed = (M₂.fixSet X hObs₂ hFix₂).observed :=
      hGraph'.2.2.1
    refine Function.hfunext (by rw [hObsSplit]) ?_
    rintro v₁ v₂ hv
    have hv_eq : v₁.val = v₂.val := by
      exact (Subtype.heq_iff_coe_eq (by intro x; rw [hObsSplit])).mp hv
    -- Inner hfunext: parent-tuple domain.
    -- Observed sets equal, so split parent sets are equal.
    have hPar : (M₁.fixSet X hObs₁ hFix₁).dag.parents v₁.val =
                (M₂.fixSet X hObs₂ hFix₂).dag.parents v₂.val := by
      rw [hv_eq]; exact hGraph'.parents_eq v₂.val
    refine Function.hfunext ?_ ?_
    · rw [hPar]
    · rintro ξ₁ ξ₂ hξ
      -- Goal: (M₁.fixSet X).structFun v₁ ξ₁ ≍ (M₂.fixSet X).structFun v₂ ξ₂
      -- Both sides unfold to M_i.structFun ⟨v_i.val, _⟩ (fixMonoParentMap ...).
      have hObsEq : M₁.observed = M₂.observed := hGraph.2.2.1
      have hv_obs₁ : v₁.val ∈ M₁.observed := v₁.property
      have hv_obs₂' : v₂.val ∈ M₂.observed := v₂.property
      -- Parent sets.
      have hPar₀ : M₁.dag.parents v₁.val = M₂.dag.parents v₂.val := by
        rw [hGraph.parents_eq v₁.val, hv_eq]
      -- Split parent set equality (via hGraph' and hv_eq).
      have hSplitPar : (M₁.fixSet X hObs₁ hFix₁).dag.parents v₁.val =
                       (M₂.fixSet X hObs₂ hFix₂).dag.parents v₂.val := by
        rw [hGraph'.parents_eq v₁.val, hv_eq]
      -- hξ_apply: pointwise equality from hξ : ξ₁ ≍ ξ₂ over propEq domain types.
      -- Use dcongr_heq since ξ₁, ξ₂ are dependent pi types.
      have hξ_apply : ∀ (x : SWIGNode N)
          (h₁ : x ∈ (M₁.fixSet X hObs₁ hFix₁).dag.parents v₁.val)
          (h₂ : x ∈ (M₂.fixSet X hObs₂ hFix₂).dag.parents v₂.val),
          ξ₁ ⟨x, h₁⟩ = ξ₂ ⟨x, h₂⟩ := by
        intro x h₁ h₂
        apply eq_of_heq
        apply dcongr_heq
        · -- ⟨x, h₁⟩ ≍ ⟨x, h₂⟩
          exact (Subtype.heq_iff_coe_eq (by intro a; rw [hSplitPar])).mpr rfl
        · -- type: swigΩ Ω t₁.val = swigΩ Ω t₂.val given t₁ ≍ t₂
          intro t₁ t₂ ht
          have : t₁.val = t₂.val :=
            (Subtype.heq_iff_coe_eq (by intro a; rw [hSplitPar])).mp ht
          simp [this]
        · -- function HEq
          intro _ _; exact hξ
      -- Step 1: HEq of the structFun applications at v₁ vs v₂.
      have hvHeq : (⟨v₁.val, hv_obs₁⟩ : {v // v ∈ M₁.observed}) ≍
                   (⟨v₂.val, hv_obs₂'⟩ : {v // v ∈ M₂.observed}) := by
        apply (Subtype.heq_iff_coe_eq (by intro x; rw [hObsEq])).mpr
        exact hv_eq
      have hApp : HEq (M₁.structFun ⟨v₁.val, hv_obs₁⟩)
                      (M₂.structFun ⟨v₂.val, hv_obs₂'⟩) := by
        apply dcongr_heq hvHeq
        · intro t₁ t₂ ht
          have hval : t₁.val = t₂.val :=
            (Subtype.heq_iff_coe_eq (by intro x; rw [hObsEq])).mp ht
          rw [hval, hGraph.parents_eq t₂.val]
        · intro _ _; exact hSF
      -- Step 2: HEq of the fixMonoParentMap outputs.
      -- Subtype domain equality for fixMonoParentMap.
      have hPar₀_sub : ({w // w ∈ M₁.dag.parents v₁.val} : Type _) =
                        {w // w ∈ M₂.dag.parents v₂.val} :=
        congrArg (fun s : Finset (SWIGNode N) => {w : SWIGNode N // w ∈ s}) hPar₀
      have hξHeq : HEq
          (fixMonoParentMap M₁.toSWIGGraph X hObs₁ hFix₁ v₁.val ξ₁)
          (fixMonoParentMap M₂.toSWIGGraph X hObs₂ hFix₂ v₂.val ξ₂) := by
        apply Function.hfunext hPar₀_sub
        rintro ⟨w₁val, w₁prop⟩ ⟨w₂val, w₂prop⟩ hw
        have hwval : w₁val = w₂val :=
          (Subtype.heq_iff_coe_eq (by intro x; rw [hPar₀])).mp hw
        subst hwval
        apply heq_of_eq
        cases w₁val with
        | random u =>
          by_cases hu : u ∈ X
          · rw [fixMonoParentMap_apply_random M₁.toSWIGGraph X hObs₁ hFix₁ v₁.val u hu ξ₁ w₁prop,
                fixMonoParentMap_apply_random M₂.toSWIGGraph X hObs₂ hFix₂ v₂.val u hu ξ₂ w₂prop]
            exact hξ_apply (SWIGNode.fixed u) _ _
          · rw [fixMonoParentMap_apply_random_notMem M₁.toSWIGGraph X hObs₁ hFix₁ v₁.val ξ₁ u hu w₁prop,
                fixMonoParentMap_apply_random_notMem M₂.toSWIGGraph X hObs₂ hFix₂ v₂.val ξ₂ u hu w₂prop]
            exact hξ_apply (SWIGNode.random u) _ _
        | fixed d =>
          rw [fixMonoParentMap_apply_fixed M₁.toSWIGGraph X hObs₁ hFix₁ v₁.val ξ₁ d w₁prop,
              fixMonoParentMap_apply_fixed M₂.toSWIGGraph X hObs₂ hFix₂ v₂.val ξ₂ d w₂prop]
          exact hξ_apply (SWIGNode.fixed d) _ _
      -- Combine: goal unfolds definitionally to M_i.structFun at v_i applied to fixMonoParentMap.
      -- Use dcongr_heq: hξHeq as the argument HEq, hApp as the function HEq.
      -- Codomain: swigΩ Ω v₁.val = swigΩ Ω v₂.val follows from hv_eq.
      change HEq (M₁.structFun ⟨v₁.val, hv_obs₁⟩
                    (fixMonoParentMap M₁.toSWIGGraph X hObs₁ hFix₁ v₁.val ξ₁))
                 (M₂.structFun ⟨v₂.val, hv_obs₂'⟩
                    (fixMonoParentMap M₂.toSWIGGraph X hObs₂ hFix₂ v₂.val ξ₂))
      exact dcongr_heq hξHeq (fun _ _ _ => by rw [hv_eq]) (fun _ _ => hApp)
  · -- (4) HEq latentDist: fixMono inherits latentDist by rfl; unobserved sets equal.
    -- Both `(M_i.fixSet X).latentDist = M_i.latentDist` by rfl (same unobserved Finset).
    -- `hLat : HEq M₁.latentDist M₂.latentDist`.
    exact hLat

private lemma fixSet_edgeType_random_eq
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (u : N) (v : SWIGNode N) :
    (M.fixSet X hObs hFix).edgeTypes.edgeType (SWIGNode.random u) v =
      M.edgeTypes.edgeType (SWIGNode.random u) v := by
  change (if h : ∃ D ∈ X, SWIGNode.random u = SWIGNode.fixed D then
      M.edgeTypes.edgeType (SWIGNode.random (Classical.choose h)) v
    else M.edgeTypes.edgeType (SWIGNode.random u) v) =
      M.edgeTypes.edgeType (SWIGNode.random u) v
  rw [dif_neg]
  rintro ⟨D, _hD, hEq⟩
  cases hEq

private lemma fixSet_edgeType_fixed_mem_eq
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (d : N) (v : SWIGNode N) (hd : d ∈ X) :
    (M.fixSet X hObs hFix).edgeTypes.edgeType (SWIGNode.fixed d) v =
      M.edgeTypes.edgeType (SWIGNode.random d) v := by
  change (if h : ∃ D ∈ X, SWIGNode.fixed d = SWIGNode.fixed D then
      M.edgeTypes.edgeType (SWIGNode.random (Classical.choose h)) v
    else M.edgeTypes.edgeType (SWIGNode.fixed d) v) =
      M.edgeTypes.edgeType (SWIGNode.random d) v
  let hmem : ∃ D ∈ X, SWIGNode.fixed d = SWIGNode.fixed D := ⟨d, hd, rfl⟩
  rw [dif_pos hmem]
  have hchoose : Classical.choose hmem = d := by
    exact (SWIGNode.fixed.inj (Classical.choose_spec hmem).2).symm
  rw [hchoose]

private lemma fixSet_edgeType_fixed_notMem_eq
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (d : N) (v : SWIGNode N) (hd : d ∉ X) :
    (M.fixSet X hObs hFix).edgeTypes.edgeType (SWIGNode.fixed d) v =
      M.edgeTypes.edgeType (SWIGNode.fixed d) v := by
  change (if h : ∃ D ∈ X, SWIGNode.fixed d = SWIGNode.fixed D then
      M.edgeTypes.edgeType (SWIGNode.random (Classical.choose h)) v
    else M.edgeTypes.edgeType (SWIGNode.fixed d) v) =
      M.edgeTypes.edgeType (SWIGNode.fixed d) v
  rw [dif_neg]
  rintro ⟨D, hD, hEq⟩
  exact hd ((SWIGNode.fixed.inj hEq) ▸ hD)

/-- **Insert form of monolithic intervention composition.**

    Intervening on `X` and then on a fresh singleton `{y}` is structurally
    equivalent to the one-shot intervention on `insert y X`. -/
theorem swigInterventionSet_insert_equiv
    (M : Causalean.SCM N Ω) (X : Finset N) (y : N)
    (hyX : y ∉ X)
    (hX_obs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hX_fixed : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (hy_obs : ∀ D ∈ ({y} : Finset N),
      SWIGNode.random D ∈ (M.fixSet X hX_obs hX_fixed).observed)
    (hy_fixed : ∀ D ∈ ({y} : Finset N),
      SWIGNode.fixed D ∉ (M.fixSet X hX_obs hX_fixed).fixed)
    (hInsert_obs : ∀ D ∈ insert y X, SWIGNode.random D ∈ M.observed)
    (hInsert_fixed : ∀ D ∈ insert y X, SWIGNode.fixed D ∉ M.fixed) :
    SCM.Equiv
      ((M.fixSet X hX_obs hX_fixed).fixSet ({y} : Finset N) hy_obs hy_fixed)
      (M.fixSet (insert y X) hInsert_obs hInsert_fixed) := by
  classical
  let Mxy : Causalean.SCM N Ω :=
    (M.fixSet X hX_obs hX_fixed).fixSet ({y} : Finset N) hy_obs hy_fixed
  let MyX : Causalean.SCM N Ω :=
    M.fixSet (insert y X) hInsert_obs hInsert_fixed
  have hGraph : SWIGGraph.Equivalent Mxy.toSWIGGraph MyX.toSWIGGraph := by
    refine ⟨?_, ?_, rfl, rfl⟩
    · intro u v
      cases u with
      | random u =>
        by_cases huy : u = y
        · subst u
          simp [Mxy, MyX, SCM.fixSet, SCM.fixMono, SWIGGraph.splitMono,
            SWIGGraph.splitMonoDAG, SWIGGraph.splitMonoEdgeRel, hyX]
        · by_cases huX : u ∈ X
          · simp [Mxy, MyX, SCM.fixSet, SCM.fixMono, SWIGGraph.splitMono,
              SWIGGraph.splitMonoDAG, SWIGGraph.splitMonoEdgeRel, huy, huX]
          · simp [Mxy, MyX, SCM.fixSet, SCM.fixMono, SWIGGraph.splitMono,
              SWIGGraph.splitMonoDAG, SWIGGraph.splitMonoEdgeRel, huy, huX]
      | fixed d =>
        by_cases hdy : d = y
        · subst d
          simp [Mxy, MyX, SCM.fixSet, SCM.fixMono, SWIGGraph.splitMono,
            SWIGGraph.splitMonoDAG, SWIGGraph.splitMonoEdgeRel, hyX]
        · by_cases hdX : d ∈ X
          · simp [Mxy, MyX, SCM.fixSet, SCM.fixMono, SWIGGraph.splitMono,
              SWIGGraph.splitMonoDAG, SWIGGraph.splitMonoEdgeRel, hdy, hdX]
          · simp [Mxy, MyX, SCM.fixSet, SCM.fixMono, SWIGGraph.splitMono,
              SWIGGraph.splitMonoDAG, SWIGGraph.splitMonoEdgeRel, hdy, hdX]
    · ext z
      simp [Mxy, MyX, SCM.fixSet, SCM.fixMono, SWIGGraph.splitMono,
        Finset.image_insert, Finset.mem_union, Finset.mem_image,
        Finset.mem_singleton, Finset.mem_insert]
  refine ⟨hGraph, ?_, ?_, ?_⟩
  · intro u v _ _
    cases u with
    | random u =>
      rw [fixSet_edgeType_random_eq (M.fixSet X hX_obs hX_fixed) ({y} : Finset N)
            hy_obs hy_fixed,
          fixSet_edgeType_random_eq M X hX_obs hX_fixed,
          fixSet_edgeType_random_eq M (insert y X) hInsert_obs hInsert_fixed]
    | fixed d =>
      by_cases hdy : d = y
      · subst d
        rw [fixSet_edgeType_fixed_mem_eq (M.fixSet X hX_obs hX_fixed)
              ({y} : Finset N) hy_obs hy_fixed y v (by simp),
            fixSet_edgeType_random_eq M X hX_obs hX_fixed,
            fixSet_edgeType_fixed_mem_eq M (insert y X) hInsert_obs
              hInsert_fixed y v (Finset.mem_insert_self y X)]
      · by_cases hdX : d ∈ X
        · rw [fixSet_edgeType_fixed_notMem_eq (M.fixSet X hX_obs hX_fixed)
                ({y} : Finset N) hy_obs hy_fixed d v
                (by simpa [Finset.mem_singleton] using hdy),
              fixSet_edgeType_fixed_mem_eq M X hX_obs hX_fixed d v hdX,
              fixSet_edgeType_fixed_mem_eq M (insert y X) hInsert_obs
                hInsert_fixed d v (Finset.mem_insert_of_mem hdX)]
        · have hdInsert : d ∉ insert y X := by
            intro hd
            rcases Finset.mem_insert.mp hd with hEq | hdX'
            · exact hdy hEq
            · exact hdX hdX'
          rw [fixSet_edgeType_fixed_notMem_eq (M.fixSet X hX_obs hX_fixed)
                ({y} : Finset N) hy_obs hy_fixed d v
                (by simpa [Finset.mem_singleton] using hdy),
              fixSet_edgeType_fixed_notMem_eq M X hX_obs hX_fixed d v hdX,
              fixSet_edgeType_fixed_notMem_eq M (insert y X) hInsert_obs
                hInsert_fixed d v hdInsert]
  · refine Function.hfunext rfl ?_
    rintro v _ hv
    have hv_eq : v = _ := eq_of_heq hv
    subst hv_eq
    refine Function.hfunext ?_ ?_
    · rw [hGraph.parents_eq v.val]
    · rintro ξ₁ ξ₂ hξ
      apply heq_of_eq
      have hP : Mxy.toSWIGGraph.dag.parents v.val =
          MyX.toSWIGGraph.dag.parents v.val :=
        hGraph.parents_eq v.val
      have hξ_apply : ∀ (x : SWIGNode N)
          (h₁ : x ∈ Mxy.toSWIGGraph.dag.parents v.val)
          (h₂ : x ∈ MyX.toSWIGGraph.dag.parents v.val),
          ξ₁ ⟨x, h₁⟩ = ξ₂ ⟨x, h₂⟩ := by
        revert ξ₁ ξ₂ hξ
        rw [← hP]
        rintro ξ₁ ξ₂ hξ x h₁ h₂
        have hξ_eq : ξ₁ = ξ₂ := eq_of_heq hξ
        subst hξ_eq
        rfl
      have h_obs_M : v.val ∈ M.observed := by
        have hv' : v.val ∈ Mxy.observed := v.property
        simpa [Mxy, SCM.fixSet, SCM.fixMono, SWIGGraph.splitMono] using hv'
      have h_y_obs' : ∀ D ∈ ({y} : Finset N),
          SWIGNode.random D ∈ (M.toSWIGGraph.splitMono X hX_obs hX_fixed).observed := by
        intro D hD
        exact hy_obs D hD
      have h_y_fix' : ∀ D ∈ ({y} : Finset N),
          SWIGNode.fixed D ∉ (M.toSWIGGraph.splitMono X hX_obs hX_fixed).fixed := by
        intro D hD
        exact hy_fixed D hD
      change M.structFun ⟨v.val, h_obs_M⟩
              (fixMonoParentMap M.toSWIGGraph X hX_obs hX_fixed v.val
                (fixMonoParentMap (M.toSWIGGraph.splitMono X hX_obs hX_fixed)
                  ({y} : Finset N) h_y_obs' h_y_fix' v.val ξ₁))
          =
            M.structFun ⟨v.val, h_obs_M⟩
              (fixMonoParentMap M.toSWIGGraph (insert y X)
                hInsert_obs hInsert_fixed v.val ξ₂)
      congr 1
      funext ⟨w, hw⟩
      cases w with
      | random u =>
        by_cases huy : u = y
        · subst u
          have hy_not_X : y ∉ X := hyX
          rw [fixMonoParentMap_apply_random_notMem M.toSWIGGraph X hX_obs hX_fixed
                v.val _ y hy_not_X hw]
          rw [fixMonoParentMap_apply_random
                (M.toSWIGGraph.splitMono X hX_obs hX_fixed)
                ({y} : Finset N) h_y_obs' h_y_fix' v.val y
                (by simp) ξ₁]
          rw [fixMonoParentMap_apply_random M.toSWIGGraph (insert y X)
                hInsert_obs hInsert_fixed v.val y
                (Finset.mem_insert_self y X) ξ₂ hw]
          exact hξ_apply (SWIGNode.fixed y) _ _
        · by_cases huX : u ∈ X
          · rw [fixMonoParentMap_apply_random M.toSWIGGraph X hX_obs hX_fixed
                v.val u huX _ hw]
            rw [fixMonoParentMap_apply_fixed
                (M.toSWIGGraph.splitMono X hX_obs hX_fixed)
                ({y} : Finset N) h_y_obs' h_y_fix' v.val ξ₁ u]
            rw [fixMonoParentMap_apply_random M.toSWIGGraph (insert y X)
                hInsert_obs hInsert_fixed v.val u
                (Finset.mem_insert_of_mem huX) ξ₂ hw]
            exact hξ_apply (SWIGNode.fixed u) _ _
          · have hu_insert : u ∉ insert y X := by
              intro hu
              rcases Finset.mem_insert.mp hu with hEq | hX
              · exact huy hEq
              · exact huX hX
            rw [fixMonoParentMap_apply_random_notMem M.toSWIGGraph X hX_obs hX_fixed
                v.val _ u huX hw]
            rw [fixMonoParentMap_apply_random_notMem
                (M.toSWIGGraph.splitMono X hX_obs hX_fixed)
                ({y} : Finset N) h_y_obs' h_y_fix' v.val _ u
                (by simpa [Finset.mem_singleton] using huy) _]
            rw [fixMonoParentMap_apply_random_notMem M.toSWIGGraph (insert y X)
                hInsert_obs hInsert_fixed v.val _ u hu_insert hw]
            exact hξ_apply (SWIGNode.random u) _ _
      | fixed d =>
        rw [fixMonoParentMap_apply_fixed M.toSWIGGraph X hX_obs hX_fixed
              v.val _ d hw]
        rw [fixMonoParentMap_apply_fixed
              (M.toSWIGGraph.splitMono X hX_obs hX_fixed)
              ({y} : Finset N) h_y_obs' h_y_fix' v.val ξ₁ d]
        rw [fixMonoParentMap_apply_fixed M.toSWIGGraph (insert y X)
              hInsert_obs hInsert_fixed v.val ξ₂ d hw]
        exact hξ_apply (SWIGNode.fixed d) _ _
  · rfl

-- ============================================================
-- § 3. `fixSetProj` — projection onto original fixed coordinates
-- ============================================================

/-- Canonical projection of post-intervention fixed assignments onto the
    original fixed coordinates.

    Reads an assignment `s' : (M.fixSet X _ _).FixedValues` on the enlarged
    fixed set `M.fixed ∪ X.image .fixed` at its `M.fixed` coordinates,
    producing an assignment `M.FixedValues`.  Used by the single-intervention
    do-calculus rules (`DoCalculus.do_rule2 / do_rule3`) to equate
    `(M'.fixSet Z).obsKernel s'` with `M'.obsKernel (M'.fixSetProj Z _ _ s')`
    after projecting the post-intervention fixed slice. -/
noncomputable def fixSetProj (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed) :
    (M.fixSet X hObs hFix).FixedValues → M.FixedValues :=
  valuesProjection (fixSet_fixed_subset M X hObs hFix)

/-- `fixSetProj` is measurable. -/
theorem measurable_fixSetProj (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed) :
    Measurable (M.fixSetProj X hObs hFix) :=
  measurable_valuesProjection _

-- ============================================================
-- § 4. `fixSetZSlice` — extractor of the inner `do(Z)` slice
-- ============================================================

/-- **Z-fixed-slice extractor.**  Reads a `FixedValues` assignment of the
    double-intervention `((M.fixSet X).fixSet Z)` on the `Z.image .fixed`
    slice, producing a `ValuesOn (Z.image SWIGNode.fixed) (swigΩ Ω)`.
    General-purpose extractor for the inner `do(z)` coordinate slice of a
    two-layer intervention. -/
noncomputable def fixSetZSlice
    (M : Causalean.SCM N Ω) (X Z : Finset N)
    (hX_obs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hX_fixed : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (hZ_obs : ∀ D ∈ Z, SWIGNode.random D ∈
        (M.fixSet X hX_obs hX_fixed).observed)
    (hZ_fixed : ∀ D ∈ Z, SWIGNode.fixed D ∉
        (M.fixSet X hX_obs hX_fixed).fixed) :
    ((M.fixSet X hX_obs hX_fixed).fixSet Z hZ_obs hZ_fixed).FixedValues →
      ValuesOn (Z.image SWIGNode.fixed) (swigΩ Ω) :=
  valuesProjection
    (fixSet_image_fixed_subset (M.fixSet X hX_obs hX_fixed) Z hZ_obs hZ_fixed)

/-- `fixSetZSlice` is measurable. -/
theorem measurable_fixSetZSlice
    (M : Causalean.SCM N Ω) (X Z : Finset N)
    (hX_obs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hX_fixed : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (hZ_obs : ∀ D ∈ Z, SWIGNode.random D ∈
        (M.fixSet X hX_obs hX_fixed).observed)
    (hZ_fixed : ∀ D ∈ Z, SWIGNode.fixed D ∉
        (M.fixSet X hX_obs hX_fixed).fixed) :
    Measurable (M.fixSetZSlice X Z hX_obs hX_fixed hZ_obs hZ_fixed) :=
  measurable_valuesProjection _

end SCM

end Causalean
