/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.SCM.Model.Kernel

/-! # Kernel Transport Across Equivalent Models

This file proves that structurally equivalent causal models have matching
evaluation maps, latent product measures, joint kernels, and observational kernels.
These transport results allow later do-calculus arguments to compare models whose
topological orderings or proof witnesses differ but whose causal content is the same.

## Main results

* `SCM.evalMap_eq_of_equiv` proves pointwise equality of evaluation maps under
  `SCM.Equiv`, assuming matching fixed and latent inputs.
* `SCM.Equiv.heq_latentProduct`, `SCM.Equiv.heq_jointKernel`, and
  `SCM.Equiv.heq_obsKernel` transport the induced measures and kernels across
  equivalent structural causal models.
* `SCM.Equiv.heq_obsCondKernel` transports observational conditional kernels
  when the conditioning and target coordinate sets are shared.
-/

namespace Causalean

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

namespace SCM

open scoped MeasureTheory ProbabilityTheory

-- ============================================================
-- § 8. Cross-SCM evalMap agreement under `SCM.Equiv`
-- ============================================================

/-- Equivalent structural graphs with matching structural functions produce the
    same output at an observed node whenever corresponding parent values agree.

    Helper: equality of `structFun` applications across equivalent SCMs, given
    pointwise agreement of the parent tuples through the parent-set equality.

    Proof sketch: lift the target to `HEq` via `eq_of_heq`, then build the HEq
    of the applied forms using `dcongr_heq` (for dependent application) +
    `congr_heq` (for the final binary-composition step into the common
    codomain `swigΩ Ω v`).  The HEq of the parent tuples is constructed via
    `Function.hfunext` using `Equivalent.parents_eq` for the subtype-domain
    equality, and subtype HEq comparisons reduce to `.val` equality via
    `Subtype.heq_iff_coe_eq`. -/
theorem structFun_apply_eq_of_equiv
    {M₁ M₂ : Causalean.SCM N Ω}
    (hGraph : SWIGGraph.Equivalent M₁.toSWIGGraph M₂.toSWIGGraph)
    (hSF : HEq M₁.structFun M₂.structFun)
    (v : SWIGNode N)
    (hv_obs₁ : v ∈ M₁.observed) (hv_obs₂ : v ∈ M₂.observed)
    {ξ₁ : (w : {w // w ∈ M₁.dag.parents v}) → swigΩ Ω w.val}
    {ξ₂ : (w : {w // w ∈ M₂.dag.parents v}) → swigΩ Ω w.val}
    (hξ : ∀ (p : SWIGNode N)
            (hp₁ : p ∈ M₁.dag.parents v) (hp₂ : p ∈ M₂.dag.parents v),
          ξ₁ ⟨p, hp₁⟩ = ξ₂ ⟨p, hp₂⟩) :
    M₁.structFun ⟨v, hv_obs₁⟩ ξ₁ = M₂.structFun ⟨v, hv_obs₂⟩ ξ₂ := by
  have hObsEq : M₁.observed = M₂.observed := hGraph.2.2.1
  have pEq : M₁.dag.parents v = M₂.dag.parents v :=
    SWIGGraph.Equivalent.parents_eq hGraph.1 v
  -- Target: both sides live in `swigΩ Ω v`.  Lift to HEq, then back to Eq.
  apply eq_of_heq
  -- Step 1: HEq of the `structFun` applications at `⟨v, ·⟩`.
  --   M₁.structFun ⟨v, hv_obs₁⟩ : (inputs₁) → swigΩ Ω v
  --   M₂.structFun ⟨v, hv_obs₂⟩ : (inputs₂) → swigΩ Ω v
  -- where inputs_i = (w : {w // w ∈ M_i.dag.parents v}) → swigΩ Ω w.val.
  -- `hSF` gives HEq of the full structFuns; apply it at v-level.
  have hvHeq : (⟨v, hv_obs₁⟩ : {v // v ∈ M₁.observed}) ≍
               (⟨v, hv_obs₂⟩ : {v // v ∈ M₂.observed}) := by
    apply (Subtype.heq_iff_coe_eq (by intro x; rw [hObsEq])).mpr
    rfl
  have hApp1 :
      HEq (M₁.structFun ⟨v, hv_obs₁⟩) (M₂.structFun ⟨v, hv_obs₂⟩) := by
    apply dcongr_heq hvHeq
    · -- β₁ t₁ = β₂ t₂ when t₁ ≍ t₂ (same .val).
      intro t₁ t₂ ht
      have hval : t₁.val = t₂.val := by
        have := (Subtype.heq_iff_coe_eq (by intro x; rw [hObsEq])).mp ht
        exact this
      -- Output β is `((w : ...parents t.val) → ...) → swigΩ Ω t.val`, depends on t.val.
      rw [hval]
      -- Remaining type difference is in parents via `M₁.dag.parents` vs `M₂.dag.parents`.
      rw [SWIGGraph.Equivalent.parents_eq hGraph.1 t₂.val]
    · intro _ _; exact hSF
  -- Step 2: HEq of the parent tuples.
  have hξHeq : HEq ξ₁ ξ₂ := by
    apply Function.hfunext (by rw [pEq])
    rintro ⟨p₁val, p₁prop⟩ ⟨p₂val, p₂prop⟩ hp
    have hval : p₁val = p₂val := by
      have := (Subtype.heq_iff_coe_eq (by intro x; rw [pEq])).mp hp
      exact this
    subst hval
    apply heq_of_eq
    exact hξ p₁val p₁prop p₂prop
  -- Step 3: combine hApp1 and hξHeq via `congr_heq` (common codomain `swigΩ Ω v`).
  exact heq_of_eq (congr_heq hApp1 hξHeq)

/-- **Cross-SCM pointwise equality of `evalMap` under `SCM.Equiv`.**

    If `M₁` and `M₂` are structurally equivalent (same graph up to `topoOrder`,
    same edge types, `HEq` on `structFun`) and the inputs `(s₁, ℓ₁)` and
    `(s₂, ℓ₂)` agree coordinate-wise on the shared fixed / unobserved Finsets,
    then their evaluation maps agree pointwise at every node of the (shared)
    random-vars set.

    This is the single load-bearing invariance lemma that lets downstream
    HEq-kernel transport ignore the `topoOrder` discrepancy between `M₁` and
    `M₂`: any kernel derived from `evalMap` (like `jointKernel`, `obsKernel`)
    transports across `SCM.Equiv` by reducing to this lemma.

    Proof strategy: case on whether `w` is observed or unobserved.  Unobserved
    branch is immediate via `evalMap_unobserved` + `hℓ`.  Observed branch uses
    strong induction on `w`'s topological index in `M₁.observed`, unfolding
    both sides via `evalMap_observed_unfold` to a `structFun ∘ parents-dispatch`
    form and then using `Equivalent.parents_eq` + `HEq structFun` + IH to close. -/
theorem evalMap_eq_of_equiv
    {M₁ M₂ : Causalean.SCM N Ω}
    (hGraph : SWIGGraph.Equivalent M₁.toSWIGGraph M₂.toSWIGGraph)
    (hSF : HEq M₁.structFun M₂.structFun)
    (s₁ : FixedValues M₁) (ℓ₁ : LatentValues M₁)
    (s₂ : FixedValues M₂) (ℓ₂ : LatentValues M₂)
    (hs : ∀ {d : SWIGNode N} (hd₁ : d ∈ M₁.fixed) (hd₂ : d ∈ M₂.fixed),
          s₁ ⟨d, hd₁⟩ = s₂ ⟨d, hd₂⟩)
    (hℓ : ∀ {u : SWIGNode N} (hu₁ : u ∈ M₁.unobserved) (hu₂ : u ∈ M₂.unobserved),
          ℓ₁ ⟨u, hu₁⟩ = ℓ₂ ⟨u, hu₂⟩)
    {w : SWIGNode N} (hw₁ : w ∈ M₁.randomVars) (hw₂ : w ∈ M₂.randomVars) :
    M₁.evalMap s₁ ℓ₁ ⟨w, hw₁⟩ = M₂.evalMap s₂ ℓ₂ ⟨w, hw₂⟩ := by
  classical
  -- Case on `w ∈ M₁.observed` vs `w ∈ M₁.unobserved`.
  by_cases hw_obs₁ : w ∈ M₁.observed
  · -- Observed branch: strong induction on M₁-topological-index of `w`.
    have hw_obs₂ : w ∈ M₂.observed := hGraph.2.2.1 ▸ hw_obs₁
    -- Reduce to a predicate indexed by the `Fin` index in M₁'s `observed`.
    suffices key : ∀ (n : ℕ),
        ∀ (v : SWIGNode N) (hv_obs₁ : v ∈ M₁.observed) (hv_obs₂ : v ∈ M₂.observed),
          (M₁.observedIndex ⟨v, hv_obs₁⟩).val = n →
          M₁.evalMap s₁ ℓ₁ ⟨v, Finset.mem_union_left _ hv_obs₁⟩ =
            M₂.evalMap s₂ ℓ₂ ⟨v, Finset.mem_union_left _ hv_obs₂⟩ by
      exact key (M₁.observedIndex ⟨w, hw_obs₁⟩).val w hw_obs₁ hw_obs₂ rfl
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro v hv_obs₁ hv_obs₂ hn_eq
      -- Unfold both sides via `evalMap_observed_unfold`.
      rw [evalMap_observed_unfold M₁ s₁ ℓ₁ ⟨v, hv_obs₁⟩,
          evalMap_observed_unfold M₂ s₂ ℓ₂ ⟨v, hv_obs₂⟩]
      -- Reduce `structFun` application equality to pointwise parent agreement.
      apply structFun_apply_eq_of_equiv hGraph hSF v hv_obs₁ hv_obs₂
      intro p hp₁ hp₂
      -- Dispatch on where `p` lives: unobserved / fixed / observed.
      by_cases hpuo : p ∈ M₁.unobserved
      · have hpuo₂ : p ∈ M₂.unobserved := hGraph.2.2.2 ▸ hpuo
        rw [dif_pos hpuo, dif_pos hpuo₂]
        exact hℓ hpuo hpuo₂
      · have hpuo₂ : p ∉ M₂.unobserved := fun h => hpuo (hGraph.2.2.2.symm ▸ h)
        rw [dif_neg hpuo, dif_neg hpuo₂]
        by_cases hpfix : p ∈ M₁.fixed
        · have hpfix₂ : p ∈ M₂.fixed := hGraph.2.1 ▸ hpfix
          rw [dif_pos hpfix, dif_pos hpfix₂]
          exact hs hpfix hpfix₂
        · have hpfix₂ : p ∉ M₂.fixed := fun h => hpfix (hGraph.2.1.symm ▸ h)
          rw [dif_neg hpfix, dif_neg hpfix₂]
          -- Observed parent: extract hp_obs₁ and apply IH.
          have hedge₁ : M₁.dag.edge p v := M₁.dag.mem_parents.mp hp₁
          have hp_obs₁ : p ∈ M₁.observed := by
            rcases Finset.mem_union.mp
                (M₁.dag_edges_classified _ _ hedge₁).1 with h1 | h2
            · rcases Finset.mem_union.mp h1 with hfx | hob
              · exact absurd hfx hpfix
              · exact hob
            · exact absurd h2 hpuo
          have hp_obs₂ : p ∈ M₂.observed := hGraph.2.2.1 ▸ hp_obs₁
          have hp_lt : (M₁.observedIndex ⟨p, hp_obs₁⟩).val < n := by
            have hlt : (M₁.observedIndex ⟨p, hp_obs₁⟩).val <
                (M₁.observedIndex ⟨v, hv_obs₁⟩).val :=
              M₁.observed_parent_index_lt
                (M₁.observedIndex ⟨v, hv_obs₁⟩).isLt
                (by
                  have := M₁.observedAt_observedIndex ⟨v, hv_obs₁⟩
                  rw [this]
                  exact hedge₁)
                hp_obs₁
            rw [hn_eq] at hlt
            exact hlt
          exact ih _ hp_lt p hp_obs₁ hp_obs₂ rfl
  · -- Unobserved branch.
    have hw_unobs₁ : w ∈ M₁.unobserved := by
      rcases Finset.mem_union.mp hw₁ with ho | hu
      · exact absurd ho hw_obs₁
      · exact hu
    have hw_unobs₂ : w ∈ M₂.unobserved := hGraph.2.2.2 ▸ hw_unobs₁
    rw [M₁.evalMap_unobserved s₁ ℓ₁ ⟨w, hw₁⟩ hw_unobs₁,
        M₂.evalMap_unobserved s₂ ℓ₂ ⟨w, hw₂⟩ hw_unobs₂]
    exact hℓ hw_unobs₁ hw_unobs₂

-- ============================================================
-- HEq transport for kernels
-- ============================================================

/-- **HEq transport for `latentProduct`.**

    Under `SCM.Equiv`, the latent product measures are equal modulo index
    transport.  Follows from `M₁.unobserved = M₂.unobserved` (from `Equivalent`)
    and `HEq M₁.latentDist M₂.latentDist`.

    Proof: destructure both SCMs, subst the unobserved-Finset equality, reduce
    `HEq` on the (now same-typed) `latentDist` families to `Eq`, substitute,
    and close by `rfl`. -/
theorem Equiv.heq_latentProduct
    {M₁ M₂ : Causalean.SCM N Ω}
    (hUnobs : M₁.unobserved = M₂.unobserved)
    (hLD : HEq M₁.latentDist M₂.latentDist) :
    HEq M₁.latentProduct M₂.latentProduct := by
  obtain ⟨⟨dag₁, fixed₁, observed₁, unobserved₁,
           fio₁, oi₁, od₁, oou₁, foi₁, fou₁, aic₁, dc₁⟩,
         eT₁, iota₁, sf₁, mf₁, lD₁, pL₁⟩ := M₁
  obtain ⟨⟨dag₂, fixed₂, observed₂, unobserved₂,
           fio₂, oi₂, od₂, oou₂, foi₂, fou₂, aic₂, dc₂⟩,
         eT₂, iota₂, sf₂, mf₂, lD₂, pL₂⟩ := M₂
  subst hUnobs
  -- After subst, lD₁, lD₂ : (u : {u // u ∈ unobserved₁}) → Measure (swigΩ Ω u.val)
  -- have the same type.
  have hLD_eq : lD₁ = lD₂ := eq_of_heq hLD
  subst hLD_eq
  -- Both sides are `Measure.pi (fun u => lD₁ u)`, the `pL₁`/`pL₂` measurability
  -- witnesses are `Subsingleton`.
  rfl

/-- **HEq transport for `jointKernel`.**

    Under `SCM.Equiv`, the joint kernels are equal modulo index transport.
    Strategy: extract the `latentProduct` HEq *before* destructuring (so Lean
    does not force premature meta unification via `eq_of_heq`), then
    destructure + `subst` the three Finset equalities and `lD`-equality so
    kernel types match defeq, apply `Kernel.ext`, rewrite via
    `jointKernel_apply_eq`, and close pointwise with `evalMap_eq_of_equiv`. -/
theorem Equiv.heq_jointKernel
    {M₁ M₂ : Causalean.SCM N Ω}
    (hGraph : SWIGGraph.Equivalent M₁.toSWIGGraph M₂.toSWIGGraph)
    (hSF : HEq M₁.structFun M₂.structFun)
    (hLD : HEq M₁.latentDist M₂.latentDist) :
    HEq M₁.jointKernel M₂.jointKernel := by
  -- Extract the latent-product HEq first, while `h` still has its
  -- original (non-destructured) type.  Chaining into `eq_of_heq` later
  -- would force the two `latentProduct` types to unify, prematurely
  -- identifying the M₁, M₂ metas of `heq_latentProduct`.
  have h_lp : HEq M₁.latentProduct M₂.latentProduct :=
    Equiv.heq_latentProduct hGraph.2.2.2 hLD
  have h_evalMap_eq := evalMap_eq_of_equiv hGraph hSF
  obtain ⟨⟨dag₁, fixed₁, observed₁, unobserved₁,
           fio₁, oi₁, od₁, oou₁, foi₁, fou₁, aic₁, dc₁⟩,
         eT₁, iota₁, sf₁, mf₁, lD₁, pL₁⟩ := M₁
  obtain ⟨⟨dag₂, fixed₂, observed₂, unobserved₂,
           fio₂, oi₂, od₂, oou₂, foi₂, fou₂, aic₂, dc₂⟩,
         eT₂, iota₂, sf₂, mf₂, lD₂, pL₂⟩ := M₂
  rcases hGraph with ⟨_hEdge, rfl, rfl, rfl⟩
  have hLD_eq : lD₁ = lD₂ := eq_of_heq hLD
  subst hLD_eq
  -- After subst: FixedValues, RandomValues, latentProduct all have matching types.
  apply heq_of_eq
  have hlp := eq_of_heq h_lp
  -- Work at the compProd definition to avoid rw-matching issues on `jointKernel`.
  unfold SCM.jointKernel
  -- Goal: (const _ lp₁ ⊗ₖ det₁).map Prod.snd = (const _ lp₂ ⊗ₖ det₂).map Prod.snd
  congr 1
  -- Goal: const _ lp₁ ⊗ₖ det₁ = const _ lp₂ ⊗ₖ det₂
  rw [hlp]
  -- Goal: const _ lp₂ ⊗ₖ det₁ = const _ lp₂ ⊗ₖ det₂
  congr 1
  -- Goal: det₁ = det₂ (Kernel.deterministic (Function.uncurry evalMap_i) _)
  apply ProbabilityTheory.Kernel.ext
  rintro ⟨s, ℓ⟩
  simp only [ProbabilityTheory.Kernel.deterministic_apply]
  congr 1
  apply funext
  rintro ⟨w, hw⟩
  exact h_evalMap_eq s ℓ s ℓ
    (fun _ _ => rfl) (fun _ _ => rfl) hw hw

/-- **HEq transport for `obsKernel`.**

    `obsKernel = jointKernel.map randomToObserved`.  Reduces to
    `heq_jointKernel` plus `randomToObserved` agreement (both are the same
    coordinate-restriction function after the `observed`/`unobserved`
    Finsets are identified under `SWIGGraph.Equivalent`). -/
theorem Equiv.heq_obsKernel
    {M₁ M₂ : Causalean.SCM N Ω}
    (hGraph : SWIGGraph.Equivalent M₁.toSWIGGraph M₂.toSWIGGraph)
    (hSF : HEq M₁.structFun M₂.structFun)
    (hLD : HEq M₁.latentDist M₂.latentDist) :
    HEq M₁.obsKernel M₂.obsKernel := by
  have h_jk : HEq M₁.jointKernel M₂.jointKernel :=
    Equiv.heq_jointKernel hGraph hSF hLD
  obtain ⟨⟨dag₁, fixed₁, observed₁, unobserved₁,
           fio₁, oi₁, od₁, oou₁, foi₁, fou₁, aic₁, dc₁⟩,
         eT₁, iota₁, sf₁, mf₁, lD₁, pL₁⟩ := M₁
  obtain ⟨⟨dag₂, fixed₂, observed₂, unobserved₂,
           fio₂, oi₂, od₂, oou₂, foi₂, fou₂, aic₂, dc₂⟩,
         eT₂, iota₂, sf₂, mf₂, lD₂, pL₂⟩ := M₂
  rcases hGraph with ⟨_hEdge, rfl, rfl, rfl⟩
  have hLD_eq : lD₁ = lD₂ := eq_of_heq hLD
  subst hLD_eq
  apply heq_of_eq
  have hjk := eq_of_heq h_jk
  unfold SCM.obsKernel
  -- Goal: M₁.jointKernel.map M₁.randomToObserved = M₂.jointKernel.map M₂.randomToObserved
  congr 1
  -- The randomToObserved definitions are identical post-subst; the only difference
  -- is the record identity, which is irrelevant since the function body only uses
  -- the subst'd `observed`/`unobserved` Finsets.

/-- **HEq transport for `obsCondKernel`.**

    Under `SCM.Equiv` and propositionally-equal parameter Finsets (`Y`, `CC`
    both shared), the jointly measurable conditional kernels are HEq-equal.

    Proof strategy: reduce to equality after destructuring/substituting the
    shared SWIG indices, then rewrite the underlying `obsCondPairKernel`
    through `heq_obsKernel`.  The local `IsFiniteKernel` proofs inside
    `obsCondKernel` are proposition-valued and hence proof-irrelevant. -/
private theorem heq_obsCondKernel_aux
    {M₁ M₂ : Causalean.SCM N Ω}
    (hGraph : SWIGGraph.Equivalent M₁.toSWIGGraph M₂.toSWIGGraph)
    (hSF : HEq M₁.structFun M₂.structFun)
    (hLD : HEq M₁.latentDist M₂.latentDist)
    (Y CC : Finset (SWIGNode N))
    (hY₁ : Y ⊆ M₁.observed) (hY₂ : Y ⊆ M₂.observed)
    (hCC₁ : CC ⊆ M₁.observed) (hCC₂ : CC ⊆ M₂.observed)
    [StandardBorelSpace (ValuesOn Y (swigΩ Ω))]
    [Nonempty (ValuesOn Y (swigΩ Ω))]
    [MeasurableSpace.CountableOrCountablyGenerated
      (FixedValues M₁) (ValuesOn CC (swigΩ Ω))]
    [MeasurableSpace.CountableOrCountablyGenerated
      (FixedValues M₂) (ValuesOn CC (swigΩ Ω))] :
    HEq (M₁.obsCondKernel Y CC hY₁ hCC₁) (M₂.obsCondKernel Y CC hY₂ hCC₂) := by
  -- Extract obsKernel HEq while `h` still has its original type.
  have h_ok : HEq M₁.obsKernel M₂.obsKernel :=
    Equiv.heq_obsKernel hGraph hSF hLD
  obtain ⟨⟨dag₁, fixed₁, observed₁, unobserved₁,
           fio₁, oi₁, od₁, oou₁, foi₁, fou₁, aic₁, dc₁⟩,
         eT₁, iota₁, sf₁, mf₁, lD₁, pL₁⟩ := M₁
  obtain ⟨⟨dag₂, fixed₂, observed₂, unobserved₂,
           fio₂, oi₂, od₂, oou₂, foi₂, fou₂, aic₂, dc₂⟩,
         eT₂, iota₂, sf₂, mf₂, lD₂, pL₂⟩ := M₂
  rcases hGraph with ⟨_hEdge, rfl, rfl, rfl⟩
  have hLD_eq : lD₁ = lD₂ := eq_of_heq hLD
  subst hLD_eq
  -- After substs, types on both sides match; `obsKernel`s are propositionally equal.
  have h_ok_eq : _ = _ := eq_of_heq h_ok
  apply heq_of_eq
  unfold SCM.obsCondKernel
  -- Goal: condKernel of (obsCondPairKernel₁) = condKernel of (obsCondPairKernel₂)
  -- The two obsCondPairKernels are equal since they are both built from the same obsKernel.
  congr 1
  unfold SCM.obsCondPairKernel
  rw [h_ok_eq]

/-- **HEq transport for `obsCondKernel`.**

    Under structural equivalence, a conditional observational kernel built from
    observed target and conditioning coordinates is the same for either model. -/
theorem Equiv.heq_obsCondKernel
    {M₁ M₂ : Causalean.SCM N Ω}
    (hGraph : SWIGGraph.Equivalent M₁.toSWIGGraph M₂.toSWIGGraph)
    (hSF : HEq M₁.structFun M₂.structFun)
    (hLD : HEq M₁.latentDist M₂.latentDist)
    (Y CC : Finset (SWIGNode N))
    (hY₁ : Y ⊆ M₁.observed)
    (hCC₁ : CC ⊆ M₁.observed)
    [StandardBorelSpace (ValuesOn Y (swigΩ Ω))]
    [Nonempty (ValuesOn Y (swigΩ Ω))]
    [MeasurableSpace.CountableOrCountablyGenerated
      (FixedValues M₁) (ValuesOn CC (swigΩ Ω))]
    [MeasurableSpace.CountableOrCountablyGenerated
      (FixedValues M₂) (ValuesOn CC (swigΩ Ω))] :
    let hY₂ : Y ⊆ M₂.observed := by
      intro v hv
      rw [← hGraph.2.2.1]
      exact hY₁ hv
    let hCC₂ : CC ⊆ M₂.observed := by
      intro v hv
      rw [← hGraph.2.2.1]
      exact hCC₁ hv
    HEq (M₁.obsCondKernel Y CC hY₁ hCC₁) (M₂.obsCondKernel Y CC hY₂ hCC₂) := by
  dsimp
  apply heq_obsCondKernel_aux hGraph hSF hLD Y CC hY₁

end SCM

end Causalean
