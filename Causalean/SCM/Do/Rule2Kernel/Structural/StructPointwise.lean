/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Rule 2 — Pointwise structural identity for filled treatment assignments

Pointwise identity for the `C`-overridden evaluation map
`evalMap_overrideC`: after intervening on `Z`, the random copies of `Z` have
no outgoing edges, so adding their filled intervention values to an override
assignment does not change the observed outcomes in `Y`.

## Main result

* `evalMap_overrideC_dropZr_on_fillZrW` — in the post-intervention model,
  the override on `Z.random ∪ W` at `fillZrW s w` has the same effect on
  `Y` as the override on `W` at `w`.

## Supporting graph facts

* `fixSet_random_no_children` — `.random D` (D ∈ Z) has no outgoing
  edges in `(M.fixSet Z _ _).dag` (from `splitMonoEdgeRel`).
* `fixSet_random_not_isAncestor` — `.random D` (D ∈ Z) is not a proper
  ancestor of any node in `(M.fixSet Z _ _).dag` (via `isAncestor_child`).

## Supporting evaluation facts

* `evalObservedAuxOverride_agree_anc` — mirror of
  `evalObservedAux_agree_anc` from `Evaluation.lean`, lifted to two
  different override sets `C₁`, `C₂` that agree on `(ancestors-or-eq
  of T)`.
* `evalMap_overrideC_agree_anc` — corollary at `v ∈ Y` on
  `evalMap_overrideC`.
* `fillZrW_random_eq_fixed` — `F w` at `.random D` equals the do-value
  `s ⟨.fixed D, _⟩`, by `fillZrW`'s `valuesUnionMk` + `zFixedAsRandom`
  construction.  This supplies the random-copy coordinates used by the
  cross-model comparison in `StructCrossSCM.lean`.
-/

import Causalean.SCM.Do.Rule2Kernel.LevelsetCompat
import Causalean.SCM.Do.Rule2Kernel.Helpers
import Causalean.SCM.Model.EvalOverrideC

/-!
Pointwise structural identities for the Rule 2 kernel proof.

This module proves the graph and evaluation facts that make filled treatment
coordinates inert in the post-intervention model. The graph lemmas
`fixSet_random_no_children` and `fixSet_random_not_isAncestor` show that random
copies of intervened nodes cannot affect downstream evaluation after `fixSet Z`.
The main theorem `evalMap_overrideC_dropZr_on_fillZrW` uses those facts to show
that overriding on `Z.image .random ∪ W` at `fillZrW s w` has the same effect on
`Y` as overriding only on `W` at `w`; `fillZrW_random_eq_fixed` records the
coordinate identity used by the cross-model bridge.
-/

namespace Causalean

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

namespace SCM

open scoped MeasureTheory ProbabilityTheory

-- ============================================================
-- § 1. Graph facts: `.random Z` is split off in `fixSet Z`
-- ============================================================

/-- In `M.fixSet Z _ _`, every `.random D` (D ∈ Z) has no outgoing edges
    (no children).  Direct from the edge relation of `splitMonoEdgeRel`:
    when the source is `.random D` with `D ∈ X`, the relation is `False`. -/
lemma fixSet_random_no_children (M : Causalean.SCM N Ω) (Z : Finset N)
    (hZ_obs : ∀ D ∈ Z, SWIGNode.random D ∈ M.observed)
    (hZ_fixed : ∀ D ∈ Z, SWIGNode.fixed D ∉ M.fixed)
    {D : N} (hD : D ∈ Z) (v : SWIGNode N) :
    ¬ (M.fixSet Z hZ_obs hZ_fixed).dag.edge (SWIGNode.random D) v := by
  intro hEdge
  -- (M.fixSet Z _ _).dag.edge = splitMonoEdgeRel M.toSWIGGraph.dag.edge Z.
  have h_eqrel : (M.fixSet Z hZ_obs hZ_fixed).dag.edge (SWIGNode.random D) v ↔
      SWIGGraph.splitMonoEdgeRel M.toSWIGGraph.dag.edge Z (SWIGNode.random D) v := by
    simp only [SCM.fixSet, SCM.fixMono, SWIGGraph.splitMono, SWIGGraph.splitMonoDAG]
  rw [h_eqrel] at hEdge
  simp only [SWIGGraph.splitMonoEdgeRel, if_pos hD] at hEdge

/-- In `M.fixSet Z _ _`, every `.random D` (D ∈ Z) is not a proper ancestor of
    any node.  Direct consequence of `fixSet_random_no_children` via
    `isAncestor_child`. -/
lemma fixSet_random_not_isAncestor (M : Causalean.SCM N Ω) (Z : Finset N)
    (hZ_obs : ∀ D ∈ Z, SWIGNode.random D ∈ M.observed)
    (hZ_fixed : ∀ D ∈ Z, SWIGNode.fixed D ∉ M.fixed)
    {D : N} (hD : D ∈ Z) (v : SWIGNode N) :
    ¬ (M.fixSet Z hZ_obs hZ_fixed).dag.isAncestor (SWIGNode.random D) v := by
  intro hAnc
  rcases (M.fixSet Z hZ_obs hZ_fixed).dag.isAncestor_child hAnc with
    hE | ⟨c, hE, _⟩
  · exact fixSet_random_no_children M Z hZ_obs hZ_fixed hD v hE
  · exact fixSet_random_no_children M Z hZ_obs hZ_fixed hD c hE

-- ============================================================
-- § 2. Override-agreement helper (mirror of `evalObservedAux_agree_anc`)
-- ============================================================

/-- **Override-version of `evalObservedAux_agree_anc`.**

    Given two override sets `C₁`, `C₂ ⊆ M.observed` and values `c₁`, `c₂`
    on each, together with a target set `T ⊆ M.observed`, if for every
    node `x` that is `=` or `M.dag.isAncestor` of some `t ∈ T`:
    * `x ∈ C₁ ↔ x ∈ C₂` (the two override sets agree on the relevant slice);
    * and whenever both hold, `c₁ ⟨x,_⟩ = c₂ ⟨x,_⟩`;

    then `evalObservedAuxOverride` at `(C₁, c₁)` and `(C₂, c₂)` produce
    the same value at every topological index whose observed node is in
    `T` or an ancestor of `T`.

    Proof by strong recursion mirroring `evalObservedAux_agree_anc`:
    at each step, classify the node-itself C-membership and each parent's
    role identically on both sides; the IH ancestor-witness extends through
    parents using `isAncestor.edge`/`isAncestor.trans`. -/
private lemma evalObservedAuxOverride_agree_anc (M : Causalean.SCM N Ω)
    (T : Finset (SWIGNode N))
    {C₁ C₂ : Finset (SWIGNode N)}
    (hC₁ : C₁ ⊆ M.observed) (hC₂ : C₂ ⊆ M.observed)
    (s : FixedValues M) (ℓ : LatentValues M)
    (c₁ : ValuesOn C₁ (swigΩ Ω)) (c₂ : ValuesOn C₂ (swigΩ Ω))
    (hAgree : ∀ (x : SWIGNode N),
      (∃ t ∈ T, x = t ∨ M.dag.isAncestor x t) →
        ((x ∈ C₁ ↔ x ∈ C₂) ∧
         (∀ (h₁ : x ∈ C₁) (h₂ : x ∈ C₂), c₁ ⟨x, h₁⟩ = c₂ ⟨x, h₂⟩))) :
    ∀ (n : ℕ) (hn : n < M.observed.card)
      (_ : ∃ t ∈ T, (M.observedAt ⟨n, hn⟩).val = t ∨
        M.dag.isAncestor (M.observedAt ⟨n, hn⟩).val t),
      evalObservedAuxOverride M hC₁ s c₁ ℓ n hn =
        evalObservedAuxOverride M hC₂ s c₂ ℓ n hn := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro hn hAnc
    rw [evalObservedAuxOverride_eq M hC₁ s c₁ ℓ n hn,
        evalObservedAuxOverride_eq M hC₂ s c₂ ℓ n hn]
    -- Agreement at the node itself.
    have hSelfAgree := hAgree (M.observedAt ⟨n, hn⟩).val hAnc
    by_cases h1 : (M.observedAt ⟨n, hn⟩).val ∈ C₁
    · have h2 : (M.observedAt ⟨n, hn⟩).val ∈ C₂ := hSelfAgree.1.mp h1
      rw [dif_pos h1, dif_pos h2]
      exact hSelfAgree.2 h1 h2
    · have h2 : (M.observedAt ⟨n, hn⟩).val ∉ C₂ := fun h => h1 (hSelfAgree.1.mpr h)
      rw [dif_neg h1, dif_neg h2]
      congr 1
      funext w
      -- Parent recursion: classify w identically on both sides.
      have hedge : M.dag.edge w.val (M.observedAt ⟨n, hn⟩).val :=
        M.dag.mem_parents.mp w.property
      have hw_anc_obs :
          M.dag.isAncestor w.val (M.observedAt ⟨n, hn⟩).val :=
        DAG.isAncestor.edge hedge
      -- Chain the ancestor witness from `observedAt n` through `w`.
      have hAncW : ∃ t ∈ T, w.val = t ∨ M.dag.isAncestor w.val t := by
        rcases hAnc with ⟨t, ht, hOrAnc⟩
        refine ⟨t, ht, ?_⟩
        rcases hOrAnc with hEq | hAncToT
        · exact Or.inr (hEq ▸ hw_anc_obs)
        · exact Or.inr (M.dag.isAncestor_trans hw_anc_obs hAncToT)
      have hWAgree := hAgree w.val hAncW
      by_cases huo : w.val ∈ M.unobserved
      · rw [parentMapOverride_unobserved M hC₁ s c₁ ℓ hn _ w huo,
            parentMapOverride_unobserved M hC₂ s c₂ ℓ hn _ w huo]
      · by_cases hfix : w.val ∈ M.fixed
        · rw [parentMapOverride_fixed M hC₁ s c₁ ℓ hn _ w huo hfix,
              parentMapOverride_fixed M hC₂ s c₂ ℓ hn _ w huo hfix]
        · -- Observed (non-fixed, non-latent) parent: either in C or recurse.
          have hobs : w.val ∈ M.observed := by
            rcases Finset.mem_union.mp
                (M.dag_edges_classified _ _ hedge).1 with h1' | h2'
            · rcases Finset.mem_union.mp h1' with hfx | hob
              · exact absurd hfx hfix
              · exact hob
            · exact absurd h2' huo
          by_cases hcW1 : w.val ∈ C₁
          · have hcW2 : w.val ∈ C₂ := hWAgree.1.mp hcW1
            rw [parentMapOverride_C M hC₁ s c₁ ℓ hn _ w huo hfix hcW1,
                parentMapOverride_C M hC₂ s c₂ ℓ hn _ w huo hfix hcW2]
            exact hWAgree.2 hcW1 hcW2
          · have hcW2 : w.val ∉ C₂ := fun h => hcW1 (hWAgree.1.mpr h)
            rw [parentMapOverride_observed M hC₁ s c₁ ℓ hn _ w huo hfix hobs hcW1,
                parentMapOverride_observed M hC₂ s c₂ ℓ hn _ w huo hfix hobs hcW2]
            -- Recursion at w's smaller topological index.
            have hj : (M.observedIndex ⟨w.val, hobs⟩).val < n :=
              M.observed_parent_index_lt hn hedge hobs
            congr 1
            apply ih _ hj
            rcases hAncW with ⟨t, ht, hwt⟩
            refine ⟨t, ht, ?_⟩
            have h_at : (M.observedAt
                ⟨(M.observedIndex ⟨w.val, hobs⟩).val,
                  (M.observedIndex ⟨w.val, hobs⟩).isLt⟩).val = w.val :=
              M.observedAt_observedIndex ⟨w.val, hobs⟩
            rw [h_at]
            exact hwt

/-- **Override-agreement for `evalMap_overrideC` on a target set `Y`.**

    Same hypothesis as `evalObservedAuxOverride_agree_anc`, but stated as
    function equality on `Y`. -/
private lemma evalMap_overrideC_agree_anc (M : Causalean.SCM N Ω)
    {Y C₁ C₂ : Finset (SWIGNode N)}
    (hY : Y ⊆ M.observed) (hC₁ : C₁ ⊆ M.observed) (hC₂ : C₂ ⊆ M.observed)
    (s : FixedValues M) (ℓ : LatentValues M)
    (c₁ : ValuesOn C₁ (swigΩ Ω)) (c₂ : ValuesOn C₂ (swigΩ Ω))
    (hAgree : ∀ (x : SWIGNode N),
      (∃ y ∈ Y, x = y ∨ M.dag.isAncestor x y) →
        ((x ∈ C₁ ↔ x ∈ C₂) ∧
         (∀ (h₁ : x ∈ C₁) (h₂ : x ∈ C₂), c₁ ⟨x, h₁⟩ = c₂ ⟨x, h₂⟩))) :
    M.evalMap_overrideC hY hC₁ s c₁ ℓ = M.evalMap_overrideC hY hC₂ s c₂ ℓ := by
  funext v
  rw [evalMap_overrideC_eq M hY hC₁ s c₁ ℓ v,
      evalMap_overrideC_eq M hY hC₂ s c₂ ℓ v]
  congr 1
  apply evalObservedAuxOverride_agree_anc M Y hC₁ hC₂ s ℓ c₁ c₂ hAgree
  refine ⟨v.val, v.property, Or.inl ?_⟩
  exact M.observedAt_observedIndex ⟨v.val, hY v.property⟩

-- ============================================================
-- § 3. Pointwise drop of filled intervention coordinates
-- ============================================================

/-- **Filled intervention coordinates do not affect the post-intervention override on `Y`.**

    In the model obtained by intervening on `Z`, if the target coordinates
    `Y` are disjoint from the random copies of `Z`, then the override on
    `Z.image .random ∪ W` at `fillZrW s w` agrees on `Y` with the override on
    `W` at `w`, as a function of the latent assignment `ℓ`.

    The graph reason is structural: after `fixSet Z`, every `.random D` with
    `D ∈ Z` has no outgoing edges, so no such node can be `Y` itself or a
    proper ancestor of a node in `Y`. -/
theorem evalMap_overrideC_dropZr_on_fillZrW
    (M' : Causalean.SCM N Ω) (Z : Finset N)
    (hZ_obs : ∀ D ∈ Z, SWIGNode.random D ∈ M'.observed)
    (hZ_fixed : ∀ D ∈ Z, SWIGNode.fixed D ∉ M'.fixed)
    (Y W : Finset (SWIGNode N))
    (hY_M2 : Y ⊆ (M'.fixSet Z hZ_obs hZ_fixed).observed)
    (hW_M2 : W ⊆ (M'.fixSet Z hZ_obs hZ_fixed).observed)
    (hZrW : Z.image SWIGNode.random ∪ W ⊆
              (M'.fixSet Z hZ_obs hZ_fixed).observed)
    (hDisj_YZr : Disjoint Y (Z.image SWIGNode.random))
    (s : (M'.fixSet Z hZ_obs hZ_fixed).FixedValues)
    (ℓ : (M'.fixSet Z hZ_obs hZ_fixed).LatentValues)
    (w : ValuesOn W (swigΩ Ω)) :
    (M'.fixSet Z hZ_obs hZ_fixed).evalMap_overrideC hY_M2 hZrW s
        (M'.fillZrW Z hZ_obs hZ_fixed W s w) ℓ
      = (M'.fixSet Z hZ_obs hZ_fixed).evalMap_overrideC hY_M2 hW_M2 s w ℓ := by
  classical
  let M2 := M'.fixSet Z hZ_obs hZ_fixed
  -- Apply the override-agreement helper with C₁ := Zr ∪ W, C₂ := W.
  apply evalMap_overrideC_agree_anc M2 hY_M2 hZrW hW_M2 s ℓ _ _
  intro x hAnc
  -- For x in (ancestors-or-eq of some y ∈ Y) in M2:
  -- We must show x ∈ Zr ∪ W ↔ x ∈ W, and the values agree on the
  -- intersection W.
  -- The key fact: x cannot be a `.random D` (D ∈ Z), since:
  --   (1) if `x = y` with `y ∈ Y`, then x ∉ Zr by hDisj_YZr;
  --   (2) if `x` is a proper M2-ancestor of `y ∈ Y`, then x ≠ .random D
  --       for any D ∈ Z (by fixSet_random_not_isAncestor).
  have hxNotZr : x ∉ Z.image SWIGNode.random := by
    intro hxZr
    rcases Finset.mem_image.mp hxZr with ⟨D, hD, rfl⟩
    rcases hAnc with ⟨y, hy, hOrAnc⟩
    rcases hOrAnc with hEq | hAncToY
    · -- x = .random D = y ∈ Y, contradicting Y disjoint Zr.
      have : SWIGNode.random D ∈ Y := hEq ▸ hy
      exact Finset.disjoint_left.mp hDisj_YZr this
        (Finset.mem_image.mpr ⟨D, hD, rfl⟩)
    · -- .random D is a proper M2-ancestor of y, contradicting
      -- fixSet_random_not_isAncestor.
      exact fixSet_random_not_isAncestor M' Z hZ_obs hZ_fixed hD y hAncToY
  refine ⟨?_, ?_⟩
  · -- x ∈ Zr ∪ W ↔ x ∈ W (given x ∉ Zr).
    constructor
    · intro hxZrW
      rcases Finset.mem_union.mp hxZrW with hxZr | hxW
      · exact absurd hxZr hxNotZr
      · exact hxW
    · intro hxW
      exact Finset.mem_union_right _ hxW
  · -- Values agree on W: fillZrW W s w at x = w at x.
    intro h₁ h₂
    -- h₁ : x ∈ Zr ∪ W, h₂ : x ∈ W.
    show M'.fillZrW Z hZ_obs hZ_fixed W s w ⟨x, h₁⟩ = w ⟨x, h₂⟩
    unfold fillZrW
    rw [valuesUnionMk_apply_right _ _ h₁ hxNotZr h₂]

-- ============================================================
-- § 4. Filled-assignment helper for the cross-model bridge
-- ============================================================

/-- **The filled assignment pins intervention values on the random copies of `Z`.**

    For every `D ∈ Z`, the override value `F w` at `.random D` equals
    `s ⟨.fixed D, _⟩` (the do-value), by `fillZrW`'s construction.  This
    is the structural form of the level-set condition that triggers
    `fixSet_evalMap_levelset_compat_M2`. -/
lemma fillZrW_random_eq_fixed
    (M' : Causalean.SCM N Ω) (Z : Finset N)
    (hZ_obs : ∀ D ∈ Z, SWIGNode.random D ∈ M'.observed)
    (hZ_fixed : ∀ D ∈ Z, SWIGNode.fixed D ∉ M'.fixed)
    (W : Finset (SWIGNode N))
    (s : (M'.fixSet Z hZ_obs hZ_fixed).FixedValues)
    (w : ValuesOn W (swigΩ Ω))
    {D : N} (hD : D ∈ Z)
    (hRD : SWIGNode.random D ∈ Z.image SWIGNode.random ∪ W) :
    M'.fillZrW Z hZ_obs hZ_fixed W s w ⟨SWIGNode.random D, hRD⟩ =
      s ⟨SWIGNode.fixed D,
          SCM.fixed_mem_fixSet M' Z hZ_obs hZ_fixed hD⟩ := by
  unfold fillZrW
  rw [valuesUnionMk_apply_left _ _ hRD
        (Finset.mem_image.mpr ⟨D, hD, rfl⟩)]
  rfl

/- The cross-model companion theorem is in `StructCrossSCM.lean`. -/

end SCM

end Causalean
