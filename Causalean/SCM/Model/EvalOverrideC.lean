/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# C-overridden evaluation map for generalized SCMs

Given a gSCM `M` and a fixed subset `C ⊆ M.observed`, the override evaluation
`evalMap_overrideC M hY hC s c ℓ` mirrors `evalMap` but short-circuits at every
observed node `v ∈ C`, reading the value from `c ⟨v, hC ‹›⟩` instead of computing
through `M.structFun`.  This is the canonical SWIG-aligned representative of the
conditional kernel used by `obsCondKernel` (see `Causal/Model/Kernel.lean`).

Four facts are proved in this file:

1. The override returns `c` at any `v ∈ C ∩ Y` (`evalMap_overrideC_apply_of_mem_C`).
2. The override returns `M.structFun`-applied parents at any `v ∈ Y \ C`
   (`evalMap_overrideC_apply_of_not_mem_C`).
3. **Cornerstone:** when `c` is the value `evalMap s ℓ` would have produced at
   `C` anyway, the override coincides with `evalMap` on `Y`
   (`evalMap_overrideC_at_self`).  No d-separation hypothesis is needed.
4. The override is jointly measurable in `(s, c, ℓ)`
   (`measurable_evalMap_overrideC`).

The strong-recursion template mirrors `evalObservedAux` / `evalMap_measurable`
in `Evaluation.lean`; the new short-circuit case is the C-membership branch.

`Equiv` transport (`Equiv.evalMap_overrideC_heq`) is deferred — see Phase F of
the refactor plan.
-/

import Causalean.SCM.Model.Evaluation

/-!
This file defines and analyzes a structural-model evaluation rule that holds a
chosen set of observed variables fixed while evaluating the rest of the model,
supporting conditional kernels aligned with single-world intervention graphs.

The override evaluation short-circuits the chosen observed block and is proved
measurable jointly in the fixed values, override values, and latent realization.

## Main definitions and results

* `SCM.parentMapOverride` and `SCM.evalObservedAuxOverride` are the overridden
  parent-tuple assembly and topological-order evaluator.
* `SCM.evalMap_overrideC` returns values on a target set while short-circuiting
  every coordinate in the override block.
* `SCM.evalMap_overrideC_apply_of_mem_C` and
  `SCM.evalMap_overrideC_apply_of_not_mem_C` are the two public unfold rules for
  target nodes inside and outside the override block.
* `SCM.evalMap_overrideC_at_self` shows that overriding by the model's own
  evaluated values leaves the target evaluation unchanged.
* `SCM.measurable_evalMap_overrideC` proves joint measurability of the override
  evaluation.
-/

namespace Causalean

namespace SCM

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

open scoped MeasureTheory ProbabilityTheory

-- ============================================================
-- § 1. Parent-tuple assembly with C-override short-circuit
-- ============================================================

/-- The override parent-value tuple reads latent, fixed, overridden, or recursively evaluated observed parent values as appropriate.

    Parent-value assembly for the observed node at topological index `n` with the
    extra C-override.  Observed parents `w ∈ C` are read directly from `c`; all
    other parents follow the same three-way classification as `parentMap`. -/
noncomputable def parentMapOverride (M : Causalean.SCM N Ω)
    {C : Finset (SWIGNode N)} (hC : C ⊆ M.observed)
    (s : FixedValues M) (c : ValuesOn C (swigΩ Ω)) (ℓ : LatentValues M)
    {n : ℕ} (hn : n < M.observed.card)
    (prev : ∀ m : ℕ, m < n → ∀ hm : m < M.observed.card,
              swigΩ Ω (M.observedAt ⟨m, hm⟩).val)
    (w : {w // w ∈ M.dag.parents (M.observedAt ⟨n, hn⟩).val}) :
    swigΩ Ω w.val :=
  if huo : w.val ∈ M.unobserved then
    ℓ ⟨w.val, huo⟩
  else if hfix : w.val ∈ M.fixed then
    s ⟨w.val, hfix⟩
  else
    have hedge : M.dag.edge w.val (M.observedAt ⟨n, hn⟩).val :=
      M.dag.mem_parents.mp w.property
    have hcls := (M.dag_edges_classified w.val (M.observedAt ⟨n, hn⟩).val hedge).1
    have hobs : w.val ∈ M.observed :=
      (Finset.mem_union.mp hcls).elim
        (fun hfo => (Finset.mem_union.mp hfo).elim (fun hf => absurd hf hfix) id)
        (fun huo' => absurd huo' huo)
    if hc : w.val ∈ C then
      c ⟨w.val, hc⟩
    else
      (M.observedAt_observedIndex ⟨w.val, hobs⟩) ▸
        prev (M.observedIndex ⟨w.val, hobs⟩).val
             (M.observed_parent_index_lt hn hedge hobs)
             (M.observedIndex ⟨w.val, hobs⟩).isLt

/-- The override parent-value tuple reads a latent parent directly from the latent assignment. -/
lemma parentMapOverride_unobserved (M : Causalean.SCM N Ω)
    {C : Finset (SWIGNode N)} (hC : C ⊆ M.observed)
    (s : FixedValues M) (c : ValuesOn C (swigΩ Ω)) (ℓ : LatentValues M)
    {n : ℕ} (hn : n < M.observed.card)
    (prev : ∀ m : ℕ, m < n → ∀ hm : m < M.observed.card,
              swigΩ Ω (M.observedAt ⟨m, hm⟩).val)
    (w : {w // w ∈ M.dag.parents (M.observedAt ⟨n, hn⟩).val})
    (huo : w.val ∈ M.unobserved) :
    parentMapOverride M hC s c ℓ hn prev w = ℓ ⟨w.val, huo⟩ := by
  unfold parentMapOverride
  rw [dif_pos huo]

/-- The override parent-value tuple reads a fixed parent directly from the fixed-value assignment. -/
lemma parentMapOverride_fixed (M : Causalean.SCM N Ω)
    {C : Finset (SWIGNode N)} (hC : C ⊆ M.observed)
    (s : FixedValues M) (c : ValuesOn C (swigΩ Ω)) (ℓ : LatentValues M)
    {n : ℕ} (hn : n < M.observed.card)
    (prev : ∀ m : ℕ, m < n → ∀ hm : m < M.observed.card,
              swigΩ Ω (M.observedAt ⟨m, hm⟩).val)
    (w : {w // w ∈ M.dag.parents (M.observedAt ⟨n, hn⟩).val})
    (huo : w.val ∉ M.unobserved) (hfix : w.val ∈ M.fixed) :
    parentMapOverride M hC s c ℓ hn prev w = s ⟨w.val, hfix⟩ := by
  unfold parentMapOverride
  rw [dif_neg huo, dif_pos hfix]

/-- The override parent-value tuple reads an overridden observed parent directly from the override assignment. -/
lemma parentMapOverride_C (M : Causalean.SCM N Ω)
    {C : Finset (SWIGNode N)} (hC : C ⊆ M.observed)
    (s : FixedValues M) (c : ValuesOn C (swigΩ Ω)) (ℓ : LatentValues M)
    {n : ℕ} (hn : n < M.observed.card)
    (prev : ∀ m : ℕ, m < n → ∀ hm : m < M.observed.card,
              swigΩ Ω (M.observedAt ⟨m, hm⟩).val)
    (w : {w // w ∈ M.dag.parents (M.observedAt ⟨n, hn⟩).val})
    (huo : w.val ∉ M.unobserved) (hfix : w.val ∉ M.fixed)
    (hc : w.val ∈ C) :
    parentMapOverride M hC s c ℓ hn prev w = c ⟨w.val, hc⟩ := by
  unfold parentMapOverride
  rw [dif_neg huo, dif_neg hfix, dif_pos hc]

/-- The override parent-value tuple reads a non-overridden observed parent from the previous recursive values. -/
lemma parentMapOverride_observed (M : Causalean.SCM N Ω)
    {C : Finset (SWIGNode N)} (hC : C ⊆ M.observed)
    (s : FixedValues M) (c : ValuesOn C (swigΩ Ω)) (ℓ : LatentValues M)
    {n : ℕ} (hn : n < M.observed.card)
    (prev : ∀ m : ℕ, m < n → ∀ hm : m < M.observed.card,
              swigΩ Ω (M.observedAt ⟨m, hm⟩).val)
    (w : {w // w ∈ M.dag.parents (M.observedAt ⟨n, hn⟩).val})
    (huo : w.val ∉ M.unobserved) (hfix : w.val ∉ M.fixed)
    (hobs : w.val ∈ M.observed) (hc : w.val ∉ C) :
    parentMapOverride M hC s c ℓ hn prev w =
      (M.observedAt_observedIndex ⟨w.val, hobs⟩) ▸
        prev (M.observedIndex ⟨w.val, hobs⟩).val
             (M.observed_parent_index_lt hn
                (M.dag.mem_parents.mp w.property) hobs)
             (M.observedIndex ⟨w.val, hobs⟩).isLt := by
  unfold parentMapOverride
  rw [dif_neg huo, dif_neg hfix, dif_neg hc]

-- ============================================================
-- § 2. Strong recursion over topological order with C-override
-- ============================================================

/-- The override auxiliary evaluator computes each observed node in topological order, short-circuiting nodes in the override block.

    Value of the observed node at topological index `n` under the C-override,
    computed by strong recursion using `parentMapOverride`.  If the node itself
    lies in `C`, the value is read from `c`; otherwise it is `M.structFun`
    applied to overridden parents. -/
noncomputable def evalObservedAuxOverride (M : Causalean.SCM N Ω)
    {C : Finset (SWIGNode N)} (hC : C ⊆ M.observed)
    (s : FixedValues M) (c : ValuesOn C (swigΩ Ω)) (ℓ : LatentValues M) (n : ℕ) :
    ∀ hn : n < M.observed.card, swigΩ Ω (M.observedAt ⟨n, hn⟩).val :=
  Nat.strongRecOn'
    (P := fun k => ∀ hk : k < M.observed.card, swigΩ Ω (M.observedAt ⟨k, hk⟩).val)
    n
    (fun k ih hk =>
      if hcSelf : (M.observedAt ⟨k, hk⟩).val ∈ C then
        c ⟨(M.observedAt ⟨k, hk⟩).val, hcSelf⟩
      else
        M.structFun (M.observedAt ⟨k, hk⟩)
          (fun w => parentMapOverride M hC s c ℓ hk ih w))

/-- The override auxiliary evaluator unfolds to either the override value or the structural function applied to overridden parents. -/
lemma evalObservedAuxOverride_eq (M : Causalean.SCM N Ω)
    {C : Finset (SWIGNode N)} (hC : C ⊆ M.observed)
    (s : FixedValues M) (c : ValuesOn C (swigΩ Ω)) (ℓ : LatentValues M)
    (n : ℕ) (hn : n < M.observed.card) :
    evalObservedAuxOverride M hC s c ℓ n hn =
      (if hcSelf : (M.observedAt ⟨n, hn⟩).val ∈ C then
         c ⟨(M.observedAt ⟨n, hn⟩).val, hcSelf⟩
       else
         M.structFun (M.observedAt ⟨n, hn⟩)
           (fun w => parentMapOverride M hC s c ℓ hn
             (fun m _ hm_card => evalObservedAuxOverride M hC s c ℓ m hm_card) w)) := by
  unfold evalObservedAuxOverride
  rw [Nat.strongRecOn'_beta]

-- ============================================================
-- § 3. The C-overridden evaluation map
-- ============================================================

/-- The overridden evaluation map returns target observed values while holding the override block fixed.

    The C-overridden evaluation map.  Returns values on `Y ⊆ M.observed`, with
    every `v ∈ C` short-circuited to `c`.  The recursion mirrors `evalMap` but
    uses `evalObservedAuxOverride` in place of `evalObservedAux`. -/
noncomputable def evalMap_overrideC
    (M : Causalean.SCM N Ω) {Y C : Finset (SWIGNode N)}
    (hY : Y ⊆ M.observed) (hC : C ⊆ M.observed)
    (s : M.FixedValues) (c : ValuesOn C (swigΩ Ω)) (ℓ : M.LatentValues) :
    ValuesOn Y (swigΩ Ω) := fun v =>
  (M.observedAt_observedIndex ⟨v.val, hY v.property⟩) ▸
    evalObservedAuxOverride M hC s c ℓ
      (M.observedIndex ⟨v.val, hY v.property⟩).val
      (M.observedIndex ⟨v.val, hY v.property⟩).isLt

/-- At any target node, the overridden evaluation map is the transported override auxiliary value at that node's topological index.

    Unfold: at any `v ∈ Y` the override equals `evalObservedAuxOverride`
    transported by the topological-index round-trip. -/
lemma evalMap_overrideC_eq
    (M : Causalean.SCM N Ω) {Y C : Finset (SWIGNode N)}
    (hY : Y ⊆ M.observed) (hC : C ⊆ M.observed)
    (s : M.FixedValues) (c : ValuesOn C (swigΩ Ω)) (ℓ : M.LatentValues)
    (v : {v // v ∈ Y}) :
    M.evalMap_overrideC hY hC s c ℓ v =
      (M.observedAt_observedIndex ⟨v.val, hY v.property⟩) ▸
        evalObservedAuxOverride M hC s c ℓ
          (M.observedIndex ⟨v.val, hY v.property⟩).val
          (M.observedIndex ⟨v.val, hY v.property⟩).isLt := rfl

-- ============================================================
-- § 3a. Reusable cast-navigation helpers
-- ============================================================

/-- If `j` is the topological index of `⟨v_val, hv_obs⟩`, the round-trip
    `M.observedAt j` produces a Subtype propositionally equal to `⟨v_val, hv_obs⟩`. -/
private lemma observedAt_observedIndex_subtype (M : Causalean.SCM N Ω)
    {v_val : SWIGNode N} (hv_obs : v_val ∈ M.observed) :
    M.observedAt (M.observedIndex ⟨v_val, hv_obs⟩) = ⟨v_val, hv_obs⟩ :=
  Subtype.ext (M.observedAt_observedIndex ⟨v_val, hv_obs⟩)

/-- Cast-navigation helper for the C-membership branch: if `v ∈ C` and `j` is
    the topological index of `v`, then `c` at the `(M.observedAt j).val` slot
    equals `c` at the `v.val` slot, modulo the SWIGNode equality.

    Proof trick: generalize the underlying-value equality and Subtype-equality
    proofs as fresh variables, then `subst` over the latter to collapse the
    cast to a definitionally-reflexive identity. -/
private lemma c_at_observedAt_eq_c_at_self {C : Finset (SWIGNode N)}
    (M : Causalean.SCM N Ω) (c : ValuesOn C (swigΩ Ω))
    {v_val : SWIGNode N} (hv_obs : v_val ∈ M.observed) (hvC : v_val ∈ C)
    (hcSelf : (M.observedAt (M.observedIndex ⟨v_val, hv_obs⟩)).val ∈ C) :
    (M.observedAt_observedIndex ⟨v_val, hv_obs⟩) ▸
        c ⟨(M.observedAt (M.observedIndex ⟨v_val, hv_obs⟩)).val, hcSelf⟩
      = c ⟨v_val, hvC⟩ := by
  -- Generalize the Subtype-level round-trip; both the underlying-value cast
  -- and `hcSelf` are functions of the LHS.  After `subst` on the Subtype eq,
  -- both reduce to definitional reflexives.
  set w : {v // v ∈ M.observed} := M.observedAt (M.observedIndex ⟨v_val, hv_obs⟩)
  have hsub_w : w = ⟨v_val, hv_obs⟩ := observedAt_observedIndex_subtype M hv_obs
  -- The underlying-value equality is `w.val = v_val`, derived from `hsub_w`.
  -- Replace by Subtype.ext form so that `subst hsub_w` collapses things.
  change (Subtype.ext_iff.mp hsub_w) ▸ c ⟨w.val, hcSelf⟩ = c ⟨v_val, hvC⟩
  -- Now perform the substitution.  hcSelf depends on w, so `clear_value` won't
  -- let us subst directly; we revert it first.
  clear_value w
  subst hsub_w
  rfl

/-- At a target node inside the override block, the overridden evaluation returns the assigned override value. -/
theorem evalMap_overrideC_apply_of_mem_C
    (M : Causalean.SCM N Ω) {Y C : Finset (SWIGNode N)}
    (hY : Y ⊆ M.observed) (hC : C ⊆ M.observed)
    (s : M.FixedValues) (c : ValuesOn C (swigΩ Ω)) (ℓ : M.LatentValues)
    (v : {v // v ∈ Y}) (hvC : v.val ∈ C) :
    M.evalMap_overrideC hY hC s c ℓ v = c ⟨v.val, hvC⟩ := by
  rw [evalMap_overrideC_eq]
  set j : Fin M.observed.card := M.observedIndex ⟨v.val, hY v.property⟩ with hj_def
  rw [evalObservedAuxOverride_eq]
  have hAtJ : M.observedAt ⟨j.val, j.isLt⟩ = M.observedAt j := rfl
  have hcSelf : (M.observedAt ⟨j.val, j.isLt⟩).val ∈ C := by
    rw [hAtJ]
    rw [show M.observedAt j = ⟨v.val, hY v.property⟩ from
          observedAt_observedIndex_subtype M (hY v.property)]
    exact hvC
  rw [dif_pos hcSelf]
  -- Goal: transport ▸ c ⟨(M.observedAt ⟨j.val, j.isLt⟩).val, hcSelf⟩ = c ⟨v.val, hvC⟩
  -- The transport is along `(M.observedAt j).val = v.val`.
  -- Reduce by `c_at_observedAt_eq_c_at_self`, with j ≡ M.observedIndex ⟨v.val, hY v.property⟩.
  -- First: rewrite ⟨j.val, j.isLt⟩ as j using Fin eta.
  have hFinEta : (⟨j.val, j.isLt⟩ : Fin M.observed.card) = j := Fin.ext rfl
  -- Now use a direct calculation.
  -- The expression `(M.observedAt ⟨j.val, j.isLt⟩).val` is defeq to `(M.observedAt j).val`.
  -- The cast proof on the LHS is `M.observedAt_observedIndex ⟨v.val, hY v.property⟩`.
  change (M.observedAt_observedIndex ⟨v.val, hY v.property⟩) ▸
        c ⟨(M.observedAt ⟨j.val, j.isLt⟩).val, hcSelf⟩ = c ⟨v.val, hvC⟩
  -- Reduce to the helper form.
  exact c_at_observedAt_eq_c_at_self M c (hY v.property) hvC hcSelf

/-- At a target node outside the override block, the overridden evaluation applies the structural function to overridden parent values.

    At any `v ∈ Y` with `v.val ∉ C`, the override equals `M.structFun` applied
    to a parent tuple computed via `parentMapOverride`. -/
theorem evalMap_overrideC_apply_of_not_mem_C
    (M : Causalean.SCM N Ω) {Y C : Finset (SWIGNode N)}
    (hY : Y ⊆ M.observed) (hC : C ⊆ M.observed)
    (s : M.FixedValues) (c : ValuesOn C (swigΩ Ω)) (ℓ : M.LatentValues)
    (v : {v // v ∈ Y}) (hvC : v.val ∉ C) :
    M.evalMap_overrideC hY hC s c ℓ v =
      (M.observedAt_observedIndex ⟨v.val, hY v.property⟩) ▸
        M.structFun (M.observedAt (M.observedIndex ⟨v.val, hY v.property⟩))
          (fun w => parentMapOverride M hC s c ℓ
            (M.observedIndex ⟨v.val, hY v.property⟩).isLt
            (fun m _ hm_card => evalObservedAuxOverride M hC s c ℓ m hm_card) w) := by
  rw [evalMap_overrideC_eq]
  set j : Fin M.observed.card := M.observedIndex ⟨v.val, hY v.property⟩ with hj_def
  rw [evalObservedAuxOverride_eq]
  have hAtJ : M.observedAt ⟨j.val, j.isLt⟩ = M.observedAt j := rfl
  have hcSelf : (M.observedAt ⟨j.val, j.isLt⟩).val ∉ C := by
    rw [hAtJ]
    rw [show M.observedAt j = ⟨v.val, hY v.property⟩ from
          observedAt_observedIndex_subtype M (hY v.property)]
    exact hvC
  rw [dif_neg hcSelf]

-- ============================================================
-- § 4. Cornerstone: override at self equals evalMap
-- ============================================================

/-- Cast-collapse helper for the C-membership branch.  Given a Fin index `j`
    and an observed node `v_obs := M.observedAt j`, the transported
    `evalObservedAux` at the round-tripped index equals `evalObservedAux` at
    `j` directly.

    Proof: introduce a fresh witness `hw : M.observedAt k = v_obs` at a free
    Fin `k`, then `subst k` collapses the cast to a reflexive identity. -/
private lemma evalObservedAux_cast_collapse_at_observedAt
    (M : Causalean.SCM N Ω) (s : FixedValues M) (ℓ : LatentValues M)
    (j : Fin M.observed.card) (hvObs : (M.observedAt j).val ∈ M.observed) :
    ((M.observedAt_observedIndex ⟨(M.observedAt j).val, hvObs⟩) ▸
        evalObservedAux M s ℓ
          (M.observedIndex ⟨(M.observedAt j).val, hvObs⟩).val
          (M.observedIndex ⟨(M.observedAt j).val, hvObs⟩).isLt)
      = evalObservedAux M s ℓ j.val j.isLt := by
  -- Step 1: the Subtype ⟨(observedAt j).val, hvObs⟩ equals observedAt j (Subtype.ext).
  have hsubEq :
      (⟨(M.observedAt j).val, hvObs⟩ : {v // v ∈ M.observed}) = M.observedAt j :=
    Subtype.ext rfl
  -- Step 2: the index of observedAt j is j (observedIndex_observedAt).
  have hjEq : M.observedIndex ⟨(M.observedAt j).val, hvObs⟩ = j := by
    rw [hsubEq]; exact M.observedIndex_observedAt _
  -- Step 3: factor through a free Fin `k` and Subtype `w`.  This is the
  -- `evalObservedAux_cast_eq_structFunAt` trick applied here.
  suffices h : ∀ (k : Fin M.observed.card)
                 (hkj : k = j)
                 (hcast : (M.observedAt k).val = (M.observedAt j).val),
              (hcast ▸ evalObservedAux M s ℓ k.val k.isLt
                : swigΩ Ω (M.observedAt j).val)
                = evalObservedAux M s ℓ j.val j.isLt by
    -- Plug in k := observedIndex ⟨(observedAt j).val, hvObs⟩, hkj := hjEq.
    -- The cast proof becomes (observedAt (observedIndex ⟨...⟩)).val = (observedAt j).val,
    -- but we have it as (observedAt (observedIndex ⟨...⟩)).val = ⟨...⟩.val = (observedAt j).val.
    have hcast' :
        (M.observedAt (M.observedIndex
            ⟨(M.observedAt j).val, hvObs⟩)).val = (M.observedAt j).val :=
      M.observedAt_observedIndex ⟨(M.observedAt j).val, hvObs⟩
    exact h _ hjEq hcast'
  intro k hkj hcast
  subst k
  have hpr_rfl : hcast = rfl := Subsingleton.elim _ _
  rw [hpr_rfl]

/-- Helper: if `c` is defined by transporting `evalObservedAux M s ℓ` at the
    topological index of each C-coordinate, then `evalObservedAuxOverride` and
    `evalObservedAux` agree at every topological index.

    Proof by strong recursion: at each step, either the node is in `C` (the
    override reads `c`, which by construction is `evalObservedAux`'s value at
    that node) or both sides apply `M.structFun` to parent tuples that agree
    coordinate-by-coordinate (latent/fixed slots are equal definitionally; C
    slots match by the same argument; observed-but-not-C slots match by IH). -/
private lemma evalObservedAuxOverride_eq_evalObservedAux_at_self
    (M : Causalean.SCM N Ω) {C : Finset (SWIGNode N)} (hC : C ⊆ M.observed)
    (s : FixedValues M) (ℓ : LatentValues M) :
    ∀ (n : ℕ) (hn : n < M.observed.card),
      evalObservedAuxOverride M hC s
        (fun v' : {v // v ∈ C} =>
          (M.observedAt_observedIndex ⟨v'.val, hC v'.property⟩) ▸
            evalObservedAux M s ℓ
              (M.observedIndex ⟨v'.val, hC v'.property⟩).val
              (M.observedIndex ⟨v'.val, hC v'.property⟩).isLt)
        ℓ n hn
      = evalObservedAux M s ℓ n hn := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro hn
    rw [evalObservedAuxOverride_eq]
    by_cases hcSelf : (M.observedAt ⟨n, hn⟩).val ∈ C
    · rw [dif_pos hcSelf]
      -- Goal: c-value at v_sub = evalObservedAux M s ℓ n hn.
      -- Beta-reduce the c-lambda first.
      change ((M.observedAt_observedIndex
              ⟨(M.observedAt ⟨n, hn⟩).val, hC hcSelf⟩) ▸
              evalObservedAux M s ℓ
                (M.observedIndex
                  ⟨(M.observedAt ⟨n, hn⟩).val, hC hcSelf⟩).val
                (M.observedIndex
                  ⟨(M.observedAt ⟨n, hn⟩).val, hC hcSelf⟩).isLt)
            = evalObservedAux M s ℓ n hn
      -- Apply the cast-collapse helper at index ⟨n, hn⟩.
      exact evalObservedAux_cast_collapse_at_observedAt M s ℓ ⟨n, hn⟩ (hC hcSelf)
    · rw [dif_neg hcSelf]
      rw [evalObservedAux_eq]
      congr 1
      funext w
      have hedge : M.dag.edge w.val (M.observedAt ⟨n, hn⟩).val :=
        M.dag.mem_parents.mp w.property
      by_cases huo : w.val ∈ M.unobserved
      · rw [parentMapOverride_unobserved _ _ _ _ _ _ _ _ huo,
            parentMap_unobserved _ _ _ _ _ _ huo]
      · by_cases hfix : w.val ∈ M.fixed
        · rw [parentMapOverride_fixed _ _ _ _ _ _ _ _ huo hfix,
              parentMap_fixed _ _ _ _ _ _ huo hfix]
        · have hobs : w.val ∈ M.observed := by
            rcases Finset.mem_union.mp (M.dag_edges_classified _ _ hedge).1 with h1 | h2
            · rcases Finset.mem_union.mp h1 with hfx | hob
              · exact absurd hfx hfix
              · exact hob
            · exact absurd h2 huo
          have hj : (M.observedIndex ⟨w.val, hobs⟩).val < n :=
            M.observed_parent_index_lt hn hedge hobs
          by_cases hcW : w.val ∈ C
          · rw [parentMapOverride_C _ _ _ _ _ _ _ _ huo hfix hcW]
            -- Goal: c ⟨w.val, hcW⟩ = parentMap s ℓ hn _ w
            -- The c-lambda body at w.val matches parentMap_observed's body (def. eq).
            rw [parentMap_observed _ _ _ _ _ _ huo hfix hobs]
          · rw [parentMapOverride_observed _ _ _ _ _ _ _ _ huo hfix hobs hcW]
            rw [parentMap_observed _ _ _ _ _ _ huo hfix hobs]
            congr 1
            exact ih _ hj _

/-- If the override assignment equals the model's own evaluated values on the override block, then overriding changes nothing on the target set.

    **Cornerstone.**  When `c` is the value that `evalMap s ℓ` would have
    produced at `C`, the override map equals `evalMap` on `Y`.

    The `c` argument here is spelled out directly via `evalObservedAux`
    (avoiding a dependency on `randomToObserved` from `Kernel.lean`); the form
    used downstream in Phase B is `valuesProjection hC (randomToObserved
    (evalMap s ℓ))`, which equals this `c` definitionally — see the auxiliary
    `evalMap_overrideC_at_self_randomToObserved` form below for that variant. -/
theorem evalMap_overrideC_at_self
    (M : Causalean.SCM N Ω) {Y C : Finset (SWIGNode N)}
    (hY : Y ⊆ M.observed) (hC : C ⊆ M.observed)
    (s : M.FixedValues) (ℓ : M.LatentValues) :
    M.evalMap_overrideC hY hC s
        (fun v' : {v // v ∈ C} =>
          (M.observedAt_observedIndex ⟨v'.val, hC v'.property⟩) ▸
            evalObservedAux M s ℓ
              (M.observedIndex ⟨v'.val, hC v'.property⟩).val
              (M.observedIndex ⟨v'.val, hC v'.property⟩).isLt)
        ℓ
      = fun v : {v // v ∈ Y} =>
          (M.observedAt_observedIndex ⟨v.val, hY v.property⟩) ▸
            evalObservedAux M s ℓ
              (M.observedIndex ⟨v.val, hY v.property⟩).val
              (M.observedIndex ⟨v.val, hY v.property⟩).isLt := by
  funext v
  rw [evalMap_overrideC_eq]
  congr 1
  exact evalObservedAuxOverride_eq_evalObservedAux_at_self M hC s ℓ _ _

-- ============================================================
-- § 5. Joint measurability of the override map
-- ============================================================

/-- A measurable map into `swigΩ Ω v` transports along a SWIGNode equality. -/
private lemma measurable_swigΩ_cast' {γ : Type*} [MeasurableSpace γ]
    {v w : SWIGNode N} (h : v = w) {f : γ → swigΩ Ω v} (hf : Measurable f) :
    Measurable (fun x => (h ▸ f x : swigΩ Ω w)) := by
  subst h; exact hf

/-- Measurability of `evalObservedAuxOverride` at each topological index, by
    strong induction.  Mirrors `evalObservedAux_measurable` from `Evaluation.lean`
    with the added C-branch (read from the `c` factor via `measurable_pi_apply`). -/
private lemma evalObservedAuxOverride_measurable
    (M : Causalean.SCM N Ω) {C : Finset (SWIGNode N)} (hC : C ⊆ M.observed) :
    ∀ (n : ℕ) (hn : n < M.observed.card),
      Measurable (fun p : (FixedValues M × ValuesOn C (swigΩ Ω)) × LatentValues M =>
        evalObservedAuxOverride M hC p.1.1 p.1.2 p.2 n hn) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro hn
    have hrw :
        (fun p : (FixedValues M × ValuesOn C (swigΩ Ω)) × LatentValues M =>
            evalObservedAuxOverride M hC p.1.1 p.1.2 p.2 n hn) =
        (fun p =>
          if hcSelf : (M.observedAt ⟨n, hn⟩).val ∈ C then
            p.1.2 ⟨(M.observedAt ⟨n, hn⟩).val, hcSelf⟩
          else
            M.structFun (M.observedAt ⟨n, hn⟩)
              (fun w => parentMapOverride M hC p.1.1 p.1.2 p.2 hn
                (fun m _ hm_card =>
                  evalObservedAuxOverride M hC p.1.1 p.1.2 p.2 m hm_card) w)) := by
      funext p
      exact evalObservedAuxOverride_eq M hC p.1.1 p.1.2 p.2 n hn
    rw [hrw]
    by_cases hcSelf : (M.observedAt ⟨n, hn⟩).val ∈ C
    · simp only [dif_pos hcSelf]
      exact (measurable_pi_apply _).comp (measurable_snd.comp measurable_fst)
    · simp only [dif_neg hcSelf]
      refine (M.structFun_measurable _).comp ?_
      refine measurable_pi_lambda _ (fun w => ?_)
      by_cases huo : w.val ∈ M.unobserved
      · have hfun :
            (fun p : (FixedValues M × ValuesOn C (swigΩ Ω)) × LatentValues M =>
                parentMapOverride M hC p.1.1 p.1.2 p.2 hn
                  (fun m _ hm_card =>
                    evalObservedAuxOverride M hC p.1.1 p.1.2 p.2 m hm_card) w) =
            (fun p => p.2 ⟨w.val, huo⟩) := by
          funext p
          exact parentMapOverride_unobserved M hC p.1.1 p.1.2 p.2 hn _ w huo
        rw [hfun]
        exact (measurable_pi_apply _).comp measurable_snd
      · by_cases hfix : w.val ∈ M.fixed
        · have hfun :
              (fun p : (FixedValues M × ValuesOn C (swigΩ Ω)) × LatentValues M =>
                  parentMapOverride M hC p.1.1 p.1.2 p.2 hn
                    (fun m _ hm_card =>
                      evalObservedAuxOverride M hC p.1.1 p.1.2 p.2 m hm_card) w) =
              (fun p => p.1.1 ⟨w.val, hfix⟩) := by
            funext p
            exact parentMapOverride_fixed M hC p.1.1 p.1.2 p.2 hn _ w huo hfix
          rw [hfun]
          exact (measurable_pi_apply _).comp (measurable_fst.comp measurable_fst)
        · have hedge : M.dag.edge w.val (M.observedAt ⟨n, hn⟩).val :=
            M.dag.mem_parents.mp w.property
          have hobs : w.val ∈ M.observed := by
            have hcls := (M.dag_edges_classified _ _ hedge).1
            rcases Finset.mem_union.mp hcls with hfo | huo'
            · rcases Finset.mem_union.mp hfo with hf | ho
              · exact absurd hf hfix
              · exact ho
            · exact absurd huo' huo
          by_cases hcW : w.val ∈ C
          · have hfun :
                (fun p : (FixedValues M × ValuesOn C (swigΩ Ω)) × LatentValues M =>
                    parentMapOverride M hC p.1.1 p.1.2 p.2 hn
                      (fun m _ hm_card =>
                        evalObservedAuxOverride M hC p.1.1 p.1.2 p.2 m hm_card) w) =
                (fun p => p.1.2 ⟨w.val, hcW⟩) := by
              funext p
              exact parentMapOverride_C M hC p.1.1 p.1.2 p.2 hn _ w huo hfix hcW
            rw [hfun]
            exact (measurable_pi_apply _).comp (measurable_snd.comp measurable_fst)
          · have hj : (M.observedIndex ⟨w.val, hobs⟩).val < n :=
              M.observed_parent_index_lt hn hedge hobs
            have hfun :
                (fun p : (FixedValues M × ValuesOn C (swigΩ Ω)) × LatentValues M =>
                    parentMapOverride M hC p.1.1 p.1.2 p.2 hn
                      (fun m _ hm_card =>
                        evalObservedAuxOverride M hC p.1.1 p.1.2 p.2 m hm_card) w) =
                (fun p =>
                  (M.observedAt_observedIndex ⟨w.val, hobs⟩) ▸
                    evalObservedAuxOverride M hC p.1.1 p.1.2 p.2
                      (M.observedIndex ⟨w.val, hobs⟩).val
                      (M.observedIndex ⟨w.val, hobs⟩).isLt) := by
              funext p
              exact parentMapOverride_observed M hC p.1.1 p.1.2 p.2 hn _ w huo hfix hobs hcW
            rw [hfun]
            exact measurable_swigΩ_cast' _ (ih _ hj _)

/-- The overridden evaluation map is jointly measurable in fixed values, override values, and the latent realization.

    **Joint measurability of `evalMap_overrideC`.**

    The override map is jointly measurable in `((s, c), ℓ)`. -/
theorem measurable_evalMap_overrideC
    (M : Causalean.SCM N Ω) {Y C : Finset (SWIGNode N)}
    (hY : Y ⊆ M.observed) (hC : C ⊆ M.observed) :
    Measurable
      (fun p : (M.FixedValues × ValuesOn C (swigΩ Ω)) × M.LatentValues =>
        M.evalMap_overrideC hY hC p.1.1 p.1.2 p.2) := by
  refine measurable_pi_iff.mpr (fun v => ?_)
  have hfun :
      (fun p : (M.FixedValues × ValuesOn C (swigΩ Ω)) × M.LatentValues =>
          M.evalMap_overrideC hY hC p.1.1 p.1.2 p.2 v) =
      (fun p =>
        (M.observedAt_observedIndex ⟨v.val, hY v.property⟩) ▸
          evalObservedAuxOverride M hC p.1.1 p.1.2 p.2
            (M.observedIndex ⟨v.val, hY v.property⟩).val
            (M.observedIndex ⟨v.val, hY v.property⟩).isLt) := by
    funext p
    exact evalMap_overrideC_eq M hY hC p.1.1 p.1.2 p.2 v
  rw [hfun]
  exact measurable_swigΩ_cast' _ (evalObservedAuxOverride_measurable M hC _ _)

/- Equiv transport (`Equiv.evalMap_overrideC_heq`) deferred — see Phase F. -/

end SCM

end Causalean
