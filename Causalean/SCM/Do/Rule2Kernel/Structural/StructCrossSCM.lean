/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Rule 2 — Pointwise cross-model bridge for filled treatment assignments

Pointwise identity for the `C`-overridden evaluation map
`evalMap_overrideC`: the original SCM and the SCM after intervening on `Z`
agree on observed coordinates when both are evaluated at the same
`fillZrW` assignment.

## Main results

* `evalMap_overrideC_observed_unfold` — structFun-form unfold for
  `evalMap_overrideC`, analog of `evalMap_observed_unfold` from
  `Evaluation.lean`, with the C-override short-circuit added.
* `evalMap_overrideC_fixSet_compat_on_fillZrW` — cross-model
  `evalMap_overrideC` bridge stated pointwise on the `fillZrW` assignment.

## Proof strategy

The structFun-form unfold mirrors `evalMap_observed_unfold`
(Evaluation.lean), adding a `C`-override short-circuit.  The
cross-SCM bridge then mirrors `fixSet_evalMap_levelset_compat_M2`
(LevelsetCompat.lean:286), augmenting each recursion step with two
new override branches (node-self in C; parent-in-C short-circuit via
`fillZrW_random_eq_fixed`).  Strong recursion uses `M1.observedIndex`
(not `M2.observedIndex`).
-/

import Causalean.SCM.Do.Rule2Kernel.Structural.StructPointwise

/-!
Cross-SCM pointwise bridge for the Rule 2 kernel proof.

This module compares the original SCM with the SCM after intervening on `Z`.
The public unfold lemma `evalMap_overrideC_observed_unfold` rewrites the
`evalMap_overrideC` map in struct-function form, exposing the override
short-circuit and the recursive observed-parent calls. The main theorem
`evalMap_overrideC_fixSet_compat_on_fillZrW` then proves that, at the filled
assignment produced by `fillZrW`, the original and post-intervention overridden
evaluations agree on every observed coordinate.
-/

namespace Causalean

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

namespace SCM

open scoped MeasureTheory ProbabilityTheory

-- ============================================================
-- § 1. Structural unfold for `evalMap_overrideC` at an observed node
-- ============================================================

/-- Parent dispatch for `evalMap_overrideC` at an observed subtype `v`,
    factoring out the if-else chain so the cast-free unfold lemma
    can state its result in `structFun`-form without transports.

    Mirrors `parentDispatch` from `Evaluation.lean`, adding the
    C-override short-circuit on observed parents.  Restricted here to
    the `Y = M.observed` case so the recursive `evalMap_overrideC` call
    is well-typed at every observed parent. -/
private noncomputable def parentDispatchOverride (M : Causalean.SCM N Ω)
    {C : Finset (SWIGNode N)} (hC : C ⊆ M.observed)
    (s : FixedValues M) (c : ValuesOn C (swigΩ Ω)) (ℓ : LatentValues M)
    (v : {v // v ∈ M.observed}) :
    ∀ w : {w // w ∈ M.dag.parents v.val}, swigΩ Ω w.val := fun w =>
  if huo : w.val ∈ M.unobserved then ℓ ⟨w.val, huo⟩
  else if hfix : w.val ∈ M.fixed then s ⟨w.val, hfix⟩
  else
    have hedge : M.dag.edge w.val v.val := M.dag.mem_parents.mp w.property
    have hobs : w.val ∈ M.observed := by
      rcases Finset.mem_union.mp (M.dag_edges_classified _ _ hedge).1 with h1 | h2
      · rcases Finset.mem_union.mp h1 with hfx | hob
        · exact absurd hfx hfix
        · exact hob
      · exact absurd h2 huo
    if hcW : w.val ∈ C then c ⟨w.val, hcW⟩
    else M.evalMap_overrideC (Finset.Subset.refl _) hC s c ℓ ⟨w.val, hobs⟩

/-- Free-Fin form: at index `j`, the `evalObservedAuxOverride` value at
    `j` equals the C-short-circuit-or-`structFun` form at `M.observedAt j`. -/
private lemma evalObservedAuxOverride_eq_structFunAt
    (M : Causalean.SCM N Ω) {C : Finset (SWIGNode N)} (hC : C ⊆ M.observed)
    (s : FixedValues M) (c : ValuesOn C (swigΩ Ω)) (ℓ : LatentValues M)
    (j : Fin M.observed.card) :
    evalObservedAuxOverride M hC s c ℓ j.val j.isLt
      = if hcSelf : (M.observedAt j).val ∈ C then
          c ⟨(M.observedAt j).val, hcSelf⟩
        else
          M.structFun (M.observedAt j)
            (parentDispatchOverride M hC s c ℓ
              ⟨(M.observedAt j).val, (M.observedAt j).property⟩) := by
  rw [evalObservedAuxOverride_eq M hC s c ℓ j.val j.isLt]
  by_cases hcSelf : (M.observedAt j).val ∈ C
  · simp only [dif_pos hcSelf]
  · simp only [dif_neg hcSelf]
    -- Both sides: M.structFun at M.observedAt j (with Fin eta) applied to a
    -- parent dispatch.  parentMapOverride (with its prev-via-evalObservedAuxOverride)
    -- is definitionally equal to parentDispatchOverride (with its evalMap_overrideC
    -- subterm), because evalMap_overrideC at the (subset_refl) Y unfolds to
    -- the same ▸ evalObservedAuxOverride form as parentMapOverride uses.
    rfl

/-- Cast-navigation helper analogous to `evalObservedAux_cast_eq_structFunAt`.
    Given Fin indices `j, k` with `k = j`, the transported
    `evalObservedAuxOverride` at `k` equals the structFun-form at `j`. -/
private lemma evalObservedAuxOverride_cast_eq_structFunAt
    (M : Causalean.SCM N Ω) {C : Finset (SWIGNode N)} (hC : C ⊆ M.observed)
    (s : FixedValues M) (c : ValuesOn C (swigΩ Ω)) (ℓ : LatentValues M)
    {j k : Fin M.observed.card} (hkj : k = j)
    (hcast : (M.observedAt k).val = (M.observedAt j).val) :
    hcast ▸ evalObservedAuxOverride M hC s c ℓ k.val k.isLt
      = if hcSelf : (M.observedAt j).val ∈ C then
          c ⟨(M.observedAt j).val, hcSelf⟩
        else
          M.structFun (M.observedAt j)
            (parentDispatchOverride M hC s c ℓ
              ⟨(M.observedAt j).val, (M.observedAt j).property⟩) := by
  subst k
  have hrfl : hcast = rfl := Subsingleton.elim _ _
  rw [hrfl]
  exact evalObservedAuxOverride_eq_structFunAt M hC s c ℓ j

/-- **Cast-free observed unfold for `evalMap_overrideC` (Y = M.observed case).**

    Specialized to `Y = M.observed` so that the recursive
    `evalMap_overrideC` call on observed parents is well-typed.  At an
    observed `v ∈ M.observed`, the override map's value is `c ⟨v.val, _⟩`
    if `v.val ∈ C`, and otherwise `M.structFun v` applied to a parent
    tuple combining latents, fixed values, C-overrides, and recursive
    `M.evalMap_overrideC` calls on observed parents not in `C`.

    The analog of `evalMap_observed_unfold` for the C-overridden map. -/
lemma evalMap_overrideC_observed_unfold (M : Causalean.SCM N Ω)
    {C : Finset (SWIGNode N)} (hC : C ⊆ M.observed)
    (s : FixedValues M) (c : ValuesOn C (swigΩ Ω)) (ℓ : LatentValues M)
    (v : {v // v ∈ M.observed}) :
    M.evalMap_overrideC (Finset.Subset.refl _) hC s c ℓ ⟨v.val, v.property⟩
      = if hvC : v.val ∈ C then c ⟨v.val, hvC⟩
        else
          M.structFun v (parentDispatchOverride M hC s c ℓ v) := by
  -- Use the suffices + subst trick (mirror of evalMap_observed_unfold).
  suffices h : ∀ (j : Fin M.observed.card) (w : {v // v ∈ M.observed})
                 (_ : M.observedAt j = w),
               M.evalMap_overrideC (Finset.Subset.refl _) hC s c ℓ
                  ⟨w.val, w.property⟩
                 = if hwC : w.val ∈ C then c ⟨w.val, hwC⟩
                   else
                     M.structFun w (parentDispatchOverride M hC s c ℓ w) by
    have key := h (M.observedIndex ⟨v.val, v.property⟩) v
                  (Subtype.ext (M.observedAt_observedIndex ⟨v.val, v.property⟩))
    exact key
  intro j w hw
  subst hw
  -- `w` eliminated; goal mentions `M.observedAt j` only.
  rw [evalMap_overrideC_eq M (Finset.Subset.refl _) hC s c ℓ
        ⟨(M.observedAt j).val, (M.observedAt j).property⟩]
  -- Apply the cast helper at k := M.observedIndex ⟨(observedAt j).val, _⟩,
  -- which equals j by `observedIndex_observedAt`.
  exact evalObservedAuxOverride_cast_eq_structFunAt M hC s c ℓ
    (M.observedIndex_observedAt j)
    (M.observedAt_observedIndex ⟨(M.observedAt j).val, (M.observedAt j).property⟩)

-- ============================================================
-- § 2. Pointwise cross-model bridge on filled treatment assignments
-- ============================================================

set_option maxHeartbeats 1200000 in
-- The mechanical mirror of `fixSet_evalMap_levelset_compat_M2`
-- (LevelsetCompat.lean:286, also uses 800000 heartbeats) plus the two
-- extra C-override branches at each recursion step pushes elaboration
-- past the default heartbeats limit; raise to 1200000.
/-- **Original and post-intervention override evaluations agree at `fillZrW`.**

    Let `M2 := M'.fixSet Z`, let `sM1 := M'.fixSetProj Z s`, let
    `F := M'.fillZrW Z _ _ W s`, and let `C := Z.image .random ∪ W`.  For
    every observed node `v`, the original model's `C`-overridden evaluation at
    `F w` and the post-intervention model's `C`-overridden evaluation at the
    same `F w` agree, after reindexing the latent assignment along
    `fixSet_unobserved`:

      M1.evalMap_overrideC _ hZrW_M1 sM1 (F w) ℓ̃ ⟨v, _⟩
        = M2.evalMap_overrideC _ hZrW_M2 s    (F w) ℓ  ⟨v, _⟩

    Stated with `Y := M.observed` to enable the recursive
    `evalMap_overrideC` call structure.

    **Proof.**  Strong recursion on `M1.observedIndex ⟨v, hv⟩` (M2's
    order drops `.random Z → ·` edges).  Each step adds two override
    branches to the existing `fixSet_evalMap_levelset_compat_M2` template:

    * **Node-self in C.**  Both sides short-circuit to `F w ⟨v, _⟩` via
      `evalMap_overrideC_apply_of_mem_C`.
    * **Parent-in-C short-circuit.**  Any parent `w' ∈ C` dispatches via
      `parentMapOverride_C` to `F w ⟨w', _⟩` on both sides; no recursion.
      For `w' = .random u` with `u ∈ Z`, this slot coincides with M1's
      fixMonoParentMap routing to `.fixed u`, since
      `F w ⟨.random u, _⟩ = s ⟨.fixed u, _⟩` by `fillZrW_random_eq_fixed`.

    Other branches parallel the existing template. -/
theorem evalMap_overrideC_fixSet_compat_on_fillZrW
    (M' : Causalean.SCM N Ω) (Z : Finset N)
    (hZ_obs : ∀ D ∈ Z, SWIGNode.random D ∈ M'.observed)
    (hZ_fixed : ∀ D ∈ Z, SWIGNode.fixed D ∉ M'.fixed)
    (W : Finset (SWIGNode N))
    (hZrW_M2 : Z.image SWIGNode.random ∪ W ⊆
                (M'.fixSet Z hZ_obs hZ_fixed).observed)
    (hZrW_M1 : Z.image SWIGNode.random ∪ W ⊆ M'.observed)
    (s : (M'.fixSet Z hZ_obs hZ_fixed).FixedValues)
    (w : ValuesOn W (swigΩ Ω))
    (ℓ : (M'.fixSet Z hZ_obs hZ_fixed).LatentValues)
    {v : SWIGNode N}
    (hv : v ∈ (M'.fixSet Z hZ_obs hZ_fixed).observed) :
    M'.evalMap_overrideC (Finset.Subset.refl _) hZrW_M1
        (M'.fixSetProj Z hZ_obs hZ_fixed s)
        (M'.fillZrW Z hZ_obs hZ_fixed W s w)
        (valuesProjection
          (le_of_eq (fixSet_unobserved M' Z hZ_obs hZ_fixed).symm) ℓ)
        ⟨v, hv⟩
      = (M'.fixSet Z hZ_obs hZ_fixed).evalMap_overrideC
          (Finset.Subset.refl _) hZrW_M2 s
          (M'.fillZrW Z hZ_obs hZ_fixed W s w) ℓ
          ⟨v, hv⟩ := by
  classical
  let M1 := M'
  let M2 := M1.fixSet Z hZ_obs hZ_fixed
  have h_obs_eq : M2.observed = M1.observed := rfl
  have h_unobs : M2.unobserved = M1.unobserved := rfl
  let s_M1 : M1.FixedValues := M1.fixSetProj Z hZ_obs hZ_fixed s
  let ℓ_M1 : M1.LatentValues := valuesProjection (le_of_eq h_unobs.symm) ℓ
  let Fw : ValuesOn (Z.image SWIGNode.random ∪ W) (swigΩ Ω) :=
    M'.fillZrW Z hZ_obs hZ_fixed W s w
  -- Strong recursion on `M1.observedIndex ⟨v, hv⟩`.
  suffices h_obs : ∀ (n : ℕ) (w' : SWIGNode N) (hw' : w' ∈ M2.observed),
      (M1.observedIndex ⟨w', hw'⟩).val = n →
        M1.evalMap_overrideC (Finset.Subset.refl _) hZrW_M1 s_M1 Fw ℓ_M1
            ⟨w', hw'⟩
          = M2.evalMap_overrideC (Finset.Subset.refl _) hZrW_M2 s Fw ℓ
              ⟨w', hw'⟩ by
    exact h_obs _ v hv rfl
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro v hv hidx
    have hv_M1 : v ∈ M1.observed := hv
    -- Use the structFun-form unfold on both sides.
    rw [evalMap_overrideC_observed_unfold M1 hZrW_M1 s_M1 Fw ℓ_M1 ⟨v, hv_M1⟩,
        evalMap_overrideC_observed_unfold M2 hZrW_M2 s Fw ℓ ⟨v, hv⟩]
    -- Case split on v ∈ C.
    by_cases hvC : v ∈ Z.image SWIGNode.random ∪ W
    · simp only [dif_pos hvC]
    · simp only [dif_neg hvC]
      -- Both sides are `structFun ⟨v, _⟩ (parentDispatchOverride ...)`.
      -- M2.structFun ⟨v, _⟩ = M1.structFun ⟨v, _⟩ ∘ fixMonoParentMap.
      -- Flip to M2 = M1 orientation to mirror fixSet_evalMap_levelset_compat_M2.
      symm
      change M1.structFun ⟨v, hv_M1⟩
            (fixMonoParentMap M1.toSWIGGraph Z hZ_obs hZ_fixed v
              (fun w' : {w' // w' ∈ M2.dag.parents v} =>
                parentDispatchOverride M2 hZrW_M2 s Fw ℓ ⟨v, hv⟩ w'))
        = M1.structFun ⟨v, hv_M1⟩
            (parentDispatchOverride M1 hZrW_M1 s_M1 Fw ℓ_M1 ⟨v, hv_M1⟩)
      congr 1
      funext wp
      rcases wp with ⟨wpVal, hwpVal_M1⟩
      cases wpVal with
      | random u =>
        by_cases hu_Z : u ∈ Z
        · -- u ∈ Z: fixMonoParentMap routes M2-side to `.fixed u`.
          rw [fixMonoParentMap_apply_random M1.toSWIGGraph Z hZ_obs hZ_fixed v u hu_Z _
                hwpVal_M1]
          -- M2-side: parentDispatchOverride at `⟨.fixed u, _⟩`.
          have huo_M2 : (SWIGNode.fixed u : SWIGNode N) ∉ M2.unobserved := by
            intro h
            rcases M2.unobserved_is_random _ h with ⟨_, hEq⟩; cases hEq
          have hfix_M2 : (SWIGNode.fixed u : SWIGNode N) ∈ M2.fixed :=
            SCM.fixed_mem_fixSet M1 Z hZ_obs hZ_fixed hu_Z
          unfold parentDispatchOverride
          rw [dif_neg huo_M2, dif_pos hfix_M2]
          -- M1-side: parentDispatchOverride at `⟨.random u, _⟩`.
          have hobs_M1_u : (SWIGNode.random u : SWIGNode N) ∈ M1.observed :=
            hZ_obs u hu_Z
          have huo_M1 : (SWIGNode.random u : SWIGNode N) ∉ M1.unobserved :=
            Finset.disjoint_left.mp M1.obs_unobs_disjoint hobs_M1_u
          have hfix_M1 : (SWIGNode.random u : SWIGNode N) ∉ M1.fixed := by
            intro h
            rcases M1.fixed_is_fixed _ h with ⟨_, hEq⟩; cases hEq
          rw [dif_neg huo_M1, dif_neg hfix_M1]
          have hcW : (SWIGNode.random u : SWIGNode N) ∈ Z.image SWIGNode.random ∪ W :=
            Finset.mem_union_left _ (Finset.mem_image.mpr ⟨u, hu_Z, rfl⟩)
          rw [dif_pos hcW]
          -- Goal: s ⟨.fixed u, hfix_M2⟩ = Fw ⟨.random u, hcW⟩.
          exact (fillZrW_random_eq_fixed M' Z hZ_obs hZ_fixed W s w hu_Z hcW).symm
        · -- u ∉ Z: fixMonoParentMap leaves alone.
          rw [fixMonoParentMap_apply_random_notMem M1.toSWIGGraph Z hZ_obs hZ_fixed v _ u
                hu_Z hwpVal_M1]
          unfold parentDispatchOverride
          by_cases huo : (SWIGNode.random u : SWIGNode N) ∈ M1.unobserved
          · have huo_M2 : (SWIGNode.random u : SWIGNode N) ∈ M2.unobserved := huo
            rw [dif_pos huo, dif_pos huo_M2]; rfl
          · have huo_M2 : (SWIGNode.random u : SWIGNode N) ∉ M2.unobserved := huo
            rw [dif_neg huo, dif_neg huo_M2]
            by_cases hfix : (SWIGNode.random u : SWIGNode N) ∈ M1.fixed
            · exfalso
              rcases M1.fixed_is_fixed _ hfix with ⟨_, hEq⟩; cases hEq
            · have hfix_M2 : (SWIGNode.random u : SWIGNode N) ∉ M2.fixed := by
                intro h
                rcases Finset.mem_union.mp
                    (show _ ∈ M1.fixed ∪ Z.image SWIGNode.fixed from h) with h1 | h2
                · exact hfix h1
                · rcases Finset.mem_image.mp h2 with ⟨_, _, hEq⟩; cases hEq
              rw [dif_neg hfix, dif_neg hfix_M2]
              -- Observed parent. Classify on C-membership.
              by_cases hcW : (SWIGNode.random u : SWIGNode N) ∈ Z.image SWIGNode.random ∪ W
              · simp only [dif_pos hcW]
              · simp only [dif_neg hcW]
                -- Recurse via IH at `.random u`.
                have hobs_M1 : (SWIGNode.random u : SWIGNode N) ∈ M1.observed := by
                  have hedge_M1 : M1.dag.edge (SWIGNode.random u) v :=
                    M1.dag.mem_parents.mp hwpVal_M1
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
                    M1.dag.mem_parents.mp hwpVal_M1
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
                exact (ih _ hidx_w (SWIGNode.random u) hobs_M2 rfl).symm
      | fixed d =>
        rw [fixMonoParentMap_apply_fixed M1.toSWIGGraph Z hZ_obs hZ_fixed v _ d hwpVal_M1]
        unfold parentDispatchOverride
        have huo : (SWIGNode.fixed d : SWIGNode N) ∉ M1.unobserved := by
          intro h
          rcases M1.unobserved_is_random _ h with ⟨_, hEq⟩; cases hEq
        have huo_M2 : (SWIGNode.fixed d : SWIGNode N) ∉ M2.unobserved := huo
        rw [dif_neg huo, dif_neg huo_M2]
        by_cases hfix_M1 : (SWIGNode.fixed d : SWIGNode N) ∈ M1.fixed
        · have hfix_M2 : (SWIGNode.fixed d : SWIGNode N) ∈ M2.fixed := by
            change _ ∈ M1.fixed ∪ Z.image SWIGNode.fixed
            exact Finset.mem_union_left _ hfix_M1
          rw [dif_pos hfix_M1, dif_pos hfix_M2]
          rfl
        · by_cases hd_Z : d ∈ Z
          · exfalso
            have := M1.fixed_outside_fixed_isolated d hfix_M1
            have hCh : v ∈ M1.dag.children (SWIGNode.fixed d) :=
              M1.dag.mem_children.mpr (M1.dag.mem_parents.mp hwpVal_M1)
            simpa [this.2] using hCh
          · have hfix_M2 : (SWIGNode.fixed d : SWIGNode N) ∉ M2.fixed := by
              intro h
              rcases Finset.mem_union.mp
                  (show _ ∈ M1.fixed ∪ Z.image SWIGNode.fixed from h) with h1 | h2
              · exact hfix_M1 h1
              · rcases Finset.mem_image.mp h2 with ⟨d', hd'Z, hEq⟩
                have : d = d' := SWIGNode.fixed.inj hEq.symm
                exact hd_Z (this ▸ hd'Z)
            rw [dif_neg hfix_M1, dif_neg hfix_M2]
            -- `.fixed d` cannot be observed.
            exfalso
            have hobs : (SWIGNode.fixed d : SWIGNode N) ∈ M1.observed := by
              have hedge_M1 : M1.dag.edge (SWIGNode.fixed d) v :=
                M1.dag.mem_parents.mp hwpVal_M1
              rcases Finset.mem_union.mp (M1.dag_edges_classified _ _ hedge_M1).1
                with h1 | h2
              · rcases Finset.mem_union.mp h1 with hfx | hob
                · exact absurd hfx hfix_M1
                · exact hob
              · exact absurd h2 huo
            rcases M1.observed_is_random _ hobs with ⟨_, hEq⟩; cases hEq

end SCM

end Causalean
