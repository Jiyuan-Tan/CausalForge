/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Correspondence between `jointKernelPrefix` and `evalMap`

The factored prefix kernel `jointKernelPrefix n hn` is built recursively by
sequential `compProd` with the deterministic `stepKernel hn`.  On the value
level, that same recursion realizes a *deterministic* function
`partialEvalMap n hn : FixedValues M → LatentValues M → OrderedLatentPrefixValues M n hn`
whose `Dirac`-pushforward equals `jointKernelPrefix`.

This file packages that deterministic twin and the bridge theorems that
connect it to the existing evaluator `evalObservedAux` from
`Causalean.SCM.Model.Evaluation`. The main correspondence theorem
(`jointKernelPrefix_apply_eq`) identifies the recursive prefix kernel with the
Dirac pushforward of the deterministic prefix map; the evaluator bridge
(`partialEvalMap_observedPrefixValue`) reads each observed-prefix coordinate as
the matching evaluator output.

## Main declarations

* `SCM.partialEvalMap` — deterministic prefix-state builder mirroring
  `jointKernelPrefix`.
* `SCM.measurable_partialEvalMap` — joint measurability of the above.
* `SCM.partialEvalMap_latent` — the `.1` component is the untouched latent.
* `SCM.jointKernelPrefix_apply_eq` — `jointKernelPrefix = Dirac ∘
  partialEvalMap`.
* `SCM.partialEvalMap_observedPrefixValue` — the observed-prefix reader on
  `partialEvalMap` agrees with `evalObservedAux`.
-/

import Causalean.SCM.Factored.PrefixKernel
import Causalean.SCM.Model.Evaluation

/-! # Correspondence Between Prefix Kernels and Evaluation

This file relates the recursive prefix-kernel construction to the deterministic
evaluation map of a structural causal model. It defines the deterministic prefix
state produced by fixed and latent assignments, proves its measurability and
latent projection facts, proves coordinate agreement with `evalObservedAux`, and
identifies each prefix kernel as the pushforward of the latent product through
that deterministic prefix map. -/

namespace Causalean

namespace SCM

universe uN uΩ

variable {N : Type uN} [DecidableEq N] [Fintype N]
variable {Ω : N → Type uΩ} [∀ n, MeasurableSpace (Ω n)]

open scoped MeasureTheory ProbabilityTheory

-- ============================================================
-- § 1. Deterministic prefix-state builder
-- ============================================================

/-- Deterministic twin of `jointKernelPrefix`: produces the prefix state
    `(ℓ, observed-prefix)` at level `n` as a plain function.  Its
    `Dirac`-pushforward equals `jointKernelPrefix n hn` (see
    `jointKernelPrefix_apply_eq`).

    Base case: `n = 0` returns `(ℓ, PUnit.unit)`.
    Step case: extend the `n`-step state with `stepFun hn` applied to `(s, prev)`. -/
noncomputable def partialEvalMap (M : Causalean.SCM N Ω) :
    (n : ℕ) → (hn : n ≤ M.observed.card) →
      FixedValues M → LatentValues M → OrderedLatentPrefixValues M n hn
  | 0, _, _, ℓ => (ℓ, (PUnit.unit : PUnit.{uΩ + 1}))
  | k + 1, hn, s, ℓ =>
      let prev := M.partialEvalMap k (Nat.le_of_succ_le hn) s ℓ
      M.extendOrderedLatentPrefix hn (prev, M.stepFun hn (s, prev))

-- ============================================================
-- § 2. Easy projection lemma: `.1` is the latent
-- ============================================================

/-- The first component of `partialEvalMap` is always the input latent tuple:
    the recursion only writes to the `ObservedPrefixValues` factor. -/
theorem partialEvalMap_latent (M : Causalean.SCM N Ω)
    (s : FixedValues M) (ℓ : LatentValues M) :
    ∀ (n : ℕ) (hn : n ≤ M.observed.card),
      (M.partialEvalMap n hn s ℓ).1 = ℓ
  | 0, _ => rfl
  | k + 1, hn => by
      -- Unfold one step and reduce `extendOrderedLatentPrefix`.
      have ih := M.partialEvalMap_latent s ℓ k (Nat.le_of_succ_le hn)
      -- `partialEvalMap (k+1) hn s ℓ = extendOrderedLatentPrefix hn (prev, stepFun hn (s, prev))`.
      -- `extendOrderedLatentPrefix hn ((ℓ', ξ), y) = (ℓ', (ξ, y))`, so `.1 = prev.1 = ℓ` by IH.
      change (M.extendOrderedLatentPrefix hn
        (M.partialEvalMap k (Nat.le_of_succ_le hn) s ℓ,
          M.stepFun hn (s, M.partialEvalMap k (Nat.le_of_succ_le hn) s ℓ))).1 = ℓ
      -- By definition of `extendOrderedLatentPrefix` on `((ℓ', ξ), y)`.
      set prev := M.partialEvalMap k (Nat.le_of_succ_le hn) s ℓ with hprev
      rcases hprev_eq : prev with ⟨ℓ', ξ⟩
      have : ℓ' = ℓ := by
        have : prev.1 = ℓ := ih
        rw [hprev_eq] at this
        exact this
      subst this
      rfl

-- ============================================================
-- § 3. Measurability
-- ============================================================

/-- `partialEvalMap` is jointly measurable in `(s, ℓ)`.  Proved by induction on
    `n`: the base case is a product of projections, and the step case composes
    the measurable `stepFun`, `extendOrderedLatentPrefix`, and the inductive
    hypothesis. -/
theorem measurable_partialEvalMap (M : Causalean.SCM N Ω) :
    ∀ (n : ℕ) (hn : n ≤ M.observed.card),
      Measurable (fun sℓ : FixedValues M × LatentValues M =>
        M.partialEvalMap n hn sℓ.1 sℓ.2)
  | 0, _ => by
      -- `partialEvalMap 0 _ s ℓ = (ℓ, PUnit.unit)`.
      change Measurable (fun sℓ : FixedValues M × LatentValues M =>
        (sℓ.2, (PUnit.unit : PUnit.{uΩ + 1})))
      exact Measurable.prodMk measurable_snd measurable_const
  | k + 1, hn => by
      have ih := M.measurable_partialEvalMap k (Nat.le_of_succ_le hn)
      -- Build the pair `(prev, stepFun hn (s, prev))`, then apply
      -- `extendOrderedLatentPrefix hn`.
      have hpair :
          Measurable (fun sℓ : FixedValues M × LatentValues M =>
            (M.partialEvalMap k (Nat.le_of_succ_le hn) sℓ.1 sℓ.2,
              M.stepFun hn (sℓ.1,
                M.partialEvalMap k (Nat.le_of_succ_le hn) sℓ.1 sℓ.2))) := by
        refine Measurable.prodMk ih ?_
        refine (M.measurable_stepFun hn).comp ?_
        exact Measurable.prodMk measurable_fst ih
      exact (M.measurable_extendOrderedLatentPrefix hn).comp hpair

-- ============================================================
-- § 3b. Helper: `compProd` with a deterministic second kernel
-- ============================================================

/-- Pointwise evaluation of `κ ⊗ₖ Kernel.deterministic f hf` at `a`:
    it is the pushforward of `κ a` along `b ↦ (b, f (a, b))`.  Factored out of
    the induction step in `jointKernelPrefix_apply_eq` below. -/
private lemma compProd_deterministic_apply
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (κ : ProbabilityTheory.Kernel α β) [ProbabilityTheory.IsSFiniteKernel κ]
    {f : α × β → γ} (hf : Measurable f) (a : α) :
    (κ ⊗ₖ ProbabilityTheory.Kernel.deterministic f hf) a =
      (κ a).map (fun b => (b, f (a, b))) := by
  have hpair : Measurable (fun b : β => (b, f (a, b))) :=
    Measurable.prodMk measurable_id
      (hf.comp (Measurable.prodMk measurable_const measurable_id))
  refine MeasureTheory.Measure.ext fun A hA => ?_
  rw [ProbabilityTheory.Kernel.compProd_apply hA,
      MeasureTheory.Measure.map_apply hpair hA]
  simp only [ProbabilityTheory.Kernel.deterministic_apply]
  trans (∫⁻ b, Set.indicator
            ((fun b => (b, f (a, b))) ⁻¹' A) (fun _ => (1 : ENNReal)) b ∂(κ a))
  · apply MeasureTheory.lintegral_congr
    intro b
    have hSlice : MeasurableSet (Prod.mk b ⁻¹' A) := measurable_prodMk_left hA
    rw [MeasureTheory.Measure.dirac_apply' _ hSlice]
    simp only [Set.indicator, Set.mem_preimage, Pi.one_apply]
    rfl
  · exact MeasureTheory.lintegral_indicator_one (hpair hA)

-- ============================================================
-- § 3c. Unfolding helpers for `observedPrefixValue` and `partialEvalMap`
-- ============================================================

/-- Reading the last slot of a length-`(k+1)` observed prefix built by pairing
    returns the freshly-appended value `y`. -/
private lemma observedPrefixValue_succ_last
    (M : Causalean.SCM N Ω) {k : ℕ} (hn : k + 1 ≤ M.observed.card)
    (ξ : M.ObservedPrefixValues k (Nat.le_of_succ_le hn))
    (y : swigΩ Ω (M.observedAt ⟨k, hn⟩).val) :
    M.observedPrefixValue hn ((ξ, y) : M.ObservedPrefixValues (k + 1) hn)
        (Fin.last k) = y := by
  simp [observedPrefixValue, Fin.lastCases_last]

/-- Reading a non-last slot `j.castSucc` of a length-`(k+1)` prefix recurses to
    reading slot `j` of the length-`k` prefix. -/
private lemma observedPrefixValue_succ_castSucc
    (M : Causalean.SCM N Ω) {k : ℕ} (hn : k + 1 ≤ M.observed.card)
    (ξ : M.ObservedPrefixValues k (Nat.le_of_succ_le hn))
    (y : swigΩ Ω (M.observedAt ⟨k, hn⟩).val) (j : Fin k) :
    M.observedPrefixValue hn ((ξ, y) : M.ObservedPrefixValues (k + 1) hn)
        j.castSucc =
      M.observedPrefixValue (Nat.le_of_succ_le hn) ξ j := by
  simp [observedPrefixValue, Fin.lastCases_castSucc]

/-- The `.1` component of `(partialEvalMap (k+1) hn s ℓ).2` is the earlier
    observed prefix `(partialEvalMap k _ s ℓ).2`. -/
private lemma partialEvalMap_succ_snd_fst
    (M : Causalean.SCM N Ω) (s : FixedValues M) (ℓ : LatentValues M)
    {k : ℕ} (hn : k + 1 ≤ M.observed.card) :
    ((M.partialEvalMap (k + 1) hn s ℓ).2 :
        M.ObservedPrefixValues (k + 1) hn).1 =
      (M.partialEvalMap k (Nat.le_of_succ_le hn) s ℓ).2 := by
  rfl

/-- The `.2` component of `(partialEvalMap (k+1) hn s ℓ).2` is the freshly-produced
    `stepFun` value. -/
private lemma partialEvalMap_succ_snd_snd
    (M : Causalean.SCM N Ω) (s : FixedValues M) (ℓ : LatentValues M)
    {k : ℕ} (hn : k + 1 ≤ M.observed.card) :
    ((M.partialEvalMap (k + 1) hn s ℓ).2 :
        M.ObservedPrefixValues (k + 1) hn).2 =
      M.stepFun hn (s, M.partialEvalMap k (Nat.le_of_succ_le hn) s ℓ) := by
  rfl

-- ============================================================
-- § 4. Bridge to `evalObservedAux`
-- ============================================================

/-- Bridges `partialEvalMap` (kernel-side) to `evalObservedAux` (existing
    evaluator).  Proven by induction on `n` mirroring the definitions: at each
    step, the newly-appended coordinate (index `n`) is `stepFun hn (s, prev) =
    structFun v_n (parentValuesFromPrefix hn (s, prev))`, which equals
    `evalObservedAux M s ℓ n _` once one shows the parent lookups agree.
    Earlier indices are handled by the inductive hypothesis through
    `observedPrefixValue` of the extension.

    This is the coordinate-level bridge used to connect the deterministic
    prefix state with the ordinary evaluator. -/
theorem partialEvalMap_observedPrefixValue (M : Causalean.SCM N Ω)
    (s : FixedValues M) (ℓ : LatentValues M) :
    ∀ (n : ℕ) (hn : n ≤ M.observed.card) (i : Fin n),
      M.observedPrefixValue hn (M.partialEvalMap n hn s ℓ).2 i =
        M.evalObservedAux s ℓ i.val (Nat.lt_of_lt_of_le i.isLt hn)
  | 0, _, i => Fin.elim0 i
  | k + 1, hn, i => by
      refine Fin.lastCases ?_ ?_ i
      · -- Last slot: i = Fin.last k. LHS reduces to stepFun; RHS is evalObservedAux at k.
        -- Step 1: unfold `(partialEvalMap (k+1) hn s ℓ).2` as a pair.
        change M.observedPrefixValue hn
          ((M.partialEvalMap k (Nat.le_of_succ_le hn) s ℓ).2,
            M.stepFun hn (s, M.partialEvalMap k (Nat.le_of_succ_le hn) s ℓ))
          (Fin.last k) = _
        -- Step 2: pick the `y` slot.
        rw [observedPrefixValue_succ_last]
        -- Step 3: unfold `stepFun` and `evalObservedAux_eq` on the RHS.
        unfold stepFun
        rw [evalObservedAux_eq]
        -- Step 4: the `structFun` head matches (both at `⟨k, hn⟩`); reduce to parent-arg eq.
        congr 1
        funext w
        -- Step 5: split by the parent class (fixed / unobserved / observed) on both sides.
        have hfix_disj_unobs : ∀ u : SWIGNode N, u ∈ M.unobserved → u ∉ M.fixed := by
          intro u hu hf
          obtain ⟨m, hm⟩ := M.fixed_is_fixed u hf
          obtain ⟨j, hj⟩ := M.unobserved_is_random u hu
          rw [hm] at hj; cases hj
        simp only [parentValuesFromPrefix]
        by_cases hfix : w.val ∈ M.fixed
        · -- Fixed parent branch.
          simp only [dif_pos hfix]
          have huo : w.val ∉ M.unobserved := fun hu => hfix_disj_unobs _ hu hfix
          exact (parentMap_fixed M s ℓ _ _ w huo hfix).symm
        · simp only [dif_neg hfix]
          by_cases hobs : w.val ∈ M.observed
          · -- Observed parent branch: use IH on smaller prefix index.
            simp only [dif_pos hobs]
            have huo : w.val ∉ M.unobserved := M.not_unobs_of_obs hobs
            -- IH at (k, iobs) where iobs points to the parent's observed index.
            have hedge : M.dag.edge w.val (M.observedAt ⟨k, hn⟩).val :=
              M.dag.mem_parents.mp w.property
            have hlt : M.observedIndex ⟨w.val, hobs⟩ < (⟨k, hn⟩ : Fin M.observed.card) :=
              M.observed_parent_index_lt hn hedge hobs
            have hlt' : (M.observedIndex ⟨w.val, hobs⟩).val < k := by simpa using hlt
            have ih := partialEvalMap_observedPrefixValue M s ℓ k
              (Nat.le_of_succ_le hn) ⟨(M.observedIndex ⟨w.val, hobs⟩).val, hlt'⟩
            -- Rewrite `observedPrefixValue` via IH, so both sides become
            -- `castEq ▸ evalObservedAux s ℓ idx _` for the same equality.
            rw [ih]
            refine Eq.trans ?_ (parentMap_observed M s ℓ _ _ w huo hfix hobs).symm
            -- Collapse the `cast` on LHS and the `▸` on RHS: both transport
            -- along the same `(observedAt (observedIndex w)).val = w.val`.
            -- Proof-irrelevance kills the bound proofs, then `cast_heq`/`eqRec_heq`
            -- close via HEq.
            apply eq_of_heq
            refine (cast_heq _ _).trans ?_
            symm
            exact eqRec_heq _ _
          · -- Unobserved parent branch.
            have hunobs : w.val ∈ M.unobserved := by
              have hedge : M.dag.edge w.val (M.observedAt ⟨k, hn⟩).val :=
                M.dag.mem_parents.mp w.property
              have hclass : w.val ∈ M.fixed ∪ M.observed ∪ M.unobserved :=
                (M.dag_edges_classified _ _ hedge).1
              rcases Finset.mem_union.mp hclass with h | h
              · rcases Finset.mem_union.mp h with h | h
                · exact (hfix h).elim
                · exact (hobs h).elim
              · exact h
            simp only [dif_neg hobs]
            -- LHS: `sℓξ.2.1 ⟨w.val, hunobs⟩` where `sℓξ = (s, partialEvalMap k _ s ℓ)`,
            -- so `.2.1 = (partialEvalMap k _ s ℓ).1 = ℓ`.
            rw [partialEvalMap_latent]
            exact (parentMap_unobserved M s ℓ _ _ w hunobs).symm
      · -- Earlier slots: i = j.castSucc. Apply IH on (k, j).
        intro j
        have ih := partialEvalMap_observedPrefixValue M s ℓ k
          (Nat.le_of_succ_le hn) j
        -- Unfold `(partialEvalMap (k+1) hn s ℓ).2` as the pair `(prev.2, stepFun _)`,
        -- then use `observedPrefixValue_succ_castSucc` to recurse into `prev.2`.
        change M.observedPrefixValue hn
          ((M.partialEvalMap k (Nat.le_of_succ_le hn) s ℓ).2,
            M.stepFun hn (s, M.partialEvalMap k (Nat.le_of_succ_le hn) s ℓ))
          j.castSucc = _
        rw [observedPrefixValue_succ_castSucc]
        simpa using ih

-- ============================================================
-- § 5. Main correspondence
-- ============================================================

/-- **Main correspondence.** The prefix kernel evaluated at `s`
    equals the pushforward of `latentProduct` through the deterministic
    `partialEvalMap n hn s ·`.

    Induction strategy: induct on `n`.
    * Base (`n = 0`): both sides reduce to `latentProduct.map (fun ℓ => (ℓ, PUnit.unit))`
      — `jointKernelPrefixZero` unfolds directly, and `partialEvalMap 0 _` is
      the pairing map.
    * Step (`k+1`): unfold `jointKernelPrefix (k+1) hn` as
      `((jointKernelPrefix k _) ⊗ₖ stepKernel hn).map (extendOrderedLatentPrefix hn)`.
      Apply `Kernel.compProd_apply` and the IH to rewrite the `compProd` as a
      bind against a `Dirac` pushforward, then
      `Kernel.deterministic_apply`/`Measure.map_map` collapses the
      deterministic step kernel into a composition, yielding
      `latentProduct.map (fun ℓ => extendOrderedLatentPrefix hn ((partialEvalMap k _ s ℓ),
        stepFun hn (s, partialEvalMap k _ s ℓ)))`, which is exactly
      `latentProduct.map (partialEvalMap (k+1) hn s ·)` by definition. -/
theorem jointKernelPrefix_apply_eq (M : Causalean.SCM N Ω) (s : FixedValues M) :
    ∀ (n : ℕ) (hn : n ≤ M.observed.card),
      (M.jointKernelPrefix n hn) s =
        M.latentProduct.map (fun ℓ => M.partialEvalMap n hn s ℓ)
  | 0, _ => by
      -- Base: jointKernelPrefixZero at `s` is `latentProduct.map (fun ℓ => (ℓ, PUnit.unit))`,
      -- which matches `partialEvalMap 0 _ s ℓ = (ℓ, PUnit.unit)` by definition.
      -- `partialEvalMap 0 _ s ℓ = (ℓ, PUnit.unit)`, matching the def of
      -- `jointKernelPrefixZero` after unfolding `Kernel.map_apply` + `const_apply`.
      have hpair0 :
          Measurable (fun ℓ : LatentValues M =>
            (ℓ, (PUnit.unit : PUnit.{uΩ + 1}))) := by fun_prop
      change (M.latentKernelOnFixed.map
                (fun ℓ => (ℓ, (PUnit.unit : PUnit.{uΩ + 1})))) s = _
      rw [ProbabilityTheory.Kernel.map_apply _ hpair0]
      unfold latentKernelOnFixed
      rw [ProbabilityTheory.Kernel.const_apply]
      rfl
  | k + 1, hn => by
      have ih := M.jointKernelPrefix_apply_eq s k (Nat.le_of_succ_le hn)
      -- Measurability helpers.
      have hext := M.measurable_extendOrderedLatentPrefix hn
      have hstep := M.measurable_stepFun hn
      have hpair :
          Measurable (fun ξ : M.OrderedLatentPrefixValues k (Nat.le_of_succ_le hn) =>
            (ξ, M.stepFun hn (s, ξ))) :=
        Measurable.prodMk measurable_id
          (hstep.comp (Measurable.prodMk measurable_const measurable_id))
      have hpem :
          Measurable (fun ℓ : LatentValues M =>
            M.partialEvalMap k (Nat.le_of_succ_le hn) s ℓ) :=
        (M.measurable_partialEvalMap k (Nat.le_of_succ_le hn)).comp
          (Measurable.prodMk measurable_const measurable_id)
      -- Unfold `jointKernelPrefix (k+1)` to `(compProd k ⊗ stepKernel).map extend`.
      change (((M.jointKernelPrefix k (Nat.le_of_succ_le hn)) ⊗ₖ
              (M.stepKernel hn)).map (M.extendOrderedLatentPrefix hn)) s = _
      rw [ProbabilityTheory.Kernel.map_apply _ hext]
      -- Collapse the compProd with deterministic stepKernel via 3b helper.
      unfold stepKernel
      rw [compProd_deterministic_apply
            (M.jointKernelPrefix k (Nat.le_of_succ_le hn))
            hstep s]
      -- LHS: `((κ s).map pair).map extend`. Compose via `Measure.map_map`.
      rw [MeasureTheory.Measure.map_map hext hpair]
      -- Apply IH to replace `κ s` with `latentProduct.map (partialEvalMap k _ s ·)`.
      rw [ih]
      -- LHS: `(latentProduct.map (partialEvalMap k _ s)).map (extend ∘ pair)`.
      -- Collapse via `Measure.map_map` once more.
      rw [MeasureTheory.Measure.map_map (hext.comp hpair) hpem]
      -- Match composition with `partialEvalMap (k+1) hn s ·` by definitional unfolding.
      rfl

end SCM

end Causalean
