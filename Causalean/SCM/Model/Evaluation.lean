/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.SCM.Model.SCM

/-! # Evaluation Map

This file defines the evaluation map that sends fixed intervention values and a
latent realization to the values of all random nodes in a structural causal model.
It proves the measurability and ancestral factorization facts that support the
joint-kernel, Markov, and do-calculus layers, using the model's stored
topological order of observed nodes.

## Main definitions and results

* `SCM.parentMap` assembles the fixed, latent, and recursive observed parent
  values for one observed node.
* `SCM.evalObservedAux` evaluates observed nodes by strong recursion over the
  stored topological order.
* `SCM.evalMap` evaluates all random nodes, projecting latent roots directly and
  computing observed nodes through `evalObservedAux`.
* `SCM.evalMap_observed_unfold` exposes the structural-function form of
  evaluation at an observed node.
* `SCM.evalMap_measurable` and `SCM.ancestralFactorization` provide the
  measurability and ancestor-agreement interfaces used by the kernel and Markov
  developments.
-/

namespace Causalean

namespace SCM

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

open scoped MeasureTheory ProbabilityTheory

-- ============================================================
-- § 1. Parent-tuple assembly (one step of the recursion)
-- ============================================================

/-- A parent-value tuple is assembled from fixed, latent, and earlier observed values.

    Assemble the parent-value tuple for the observed node at topological index `n`,
    given a strong recursion hypothesis `prev` that supplies the value at every
    strictly earlier observed node.

    Each parent `w ∈ M.dag.parents (M.observedAt ⟨n, hn⟩).val` is classified via
    `M.dag_edges_classified` into one of three cases:
    * `w ∈ M.fixed`       — read from the fixed-value assignment `s`;
    * `w ∈ M.unobserved`  — read from the latent realization `ℓ`;
    * `w ∈ M.observed`    — recurse through `prev` at the parent's topological
      index, which is strictly smaller by `observed_parent_index_lt`.

    The result is the tuple to be fed into `M.structFun (M.observedAt ⟨n, hn⟩)`. -/
noncomputable def parentMap (M : Causalean.SCM N Ω)
    (s : FixedValues M) (ℓ : LatentValues M)
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
    (M.observedAt_observedIndex ⟨w.val, hobs⟩) ▸
      prev (M.observedIndex ⟨w.val, hobs⟩).val
           (M.observed_parent_index_lt hn hedge hobs)
           (M.observedIndex ⟨w.val, hobs⟩).isLt

/-- The parent-value tuple reads a latent parent directly from the latent assignment. -/
lemma parentMap_unobserved (M : Causalean.SCM N Ω)
    (s : FixedValues M) (ℓ : LatentValues M)
    {n : ℕ} (hn : n < M.observed.card)
    (prev : ∀ m : ℕ, m < n → ∀ hm : m < M.observed.card,
              swigΩ Ω (M.observedAt ⟨m, hm⟩).val)
    (w : {w // w ∈ M.dag.parents (M.observedAt ⟨n, hn⟩).val})
    (huo : w.val ∈ M.unobserved) :
    parentMap M s ℓ hn prev w = ℓ ⟨w.val, huo⟩ := by
  unfold parentMap
  rw [dif_pos huo]

/-- The parent-value tuple reads a fixed parent directly from the fixed-value assignment. -/
lemma parentMap_fixed (M : Causalean.SCM N Ω)
    (s : FixedValues M) (ℓ : LatentValues M)
    {n : ℕ} (hn : n < M.observed.card)
    (prev : ∀ m : ℕ, m < n → ∀ hm : m < M.observed.card,
              swigΩ Ω (M.observedAt ⟨m, hm⟩).val)
    (w : {w // w ∈ M.dag.parents (M.observedAt ⟨n, hn⟩).val})
    (hfix : w.val ∈ M.fixed) :
    parentMap M s ℓ hn prev w = s ⟨w.val, hfix⟩ := by
  unfold parentMap
  have huo : w.val ∉ M.unobserved := by
    intro h
    obtain ⟨m, hm⟩ := M.unobserved_is_random _ h
    obtain ⟨k, hk⟩ := M.fixed_is_fixed _ hfix
    rw [hk] at hm
    exact absurd hm (by simp)
  rw [dif_neg huo, dif_pos hfix]

/-- The parent-value tuple reads an observed parent from the previously computed observed values. -/
lemma parentMap_observed (M : Causalean.SCM N Ω)
    (s : FixedValues M) (ℓ : LatentValues M)
    {n : ℕ} (hn : n < M.observed.card)
    (prev : ∀ m : ℕ, m < n → ∀ hm : m < M.observed.card,
              swigΩ Ω (M.observedAt ⟨m, hm⟩).val)
    (w : {w // w ∈ M.dag.parents (M.observedAt ⟨n, hn⟩).val})
    (hobs : w.val ∈ M.observed) :
    parentMap M s ℓ hn prev w =
      (M.observedAt_observedIndex ⟨w.val, hobs⟩) ▸
        prev (M.observedIndex ⟨w.val, hobs⟩).val
             (M.observed_parent_index_lt hn
                (M.dag.mem_parents.mp w.property) hobs)
             (M.observedIndex ⟨w.val, hobs⟩).isLt := by
  unfold parentMap
  have huo : w.val ∉ M.unobserved := not_unobs_of_obs M.toSWIGGraph hobs
  have hfix : w.val ∉ M.fixed := not_fixed_of_obs M.toSWIGGraph hobs
  rw [dif_neg huo, dif_neg hfix]

-- ============================================================
-- § 2. Strong recursion over the observed topological order
-- ============================================================

/-- The auxiliary evaluator recursively applies structural functions in topological order.

    Value of the observed node at topological index `n`, computed by strong recursion
    on `n` using `parentMap` at each step.

    Defined through `Nat.strongRecOn'` so that the unfold equation
    `evalObservedAux_eq` gives a β-reduced form usable in downstream induction. -/
noncomputable def evalObservedAux (M : Causalean.SCM N Ω)
    (s : FixedValues M) (ℓ : LatentValues M) (n : ℕ) :
    ∀ hn : n < M.observed.card, swigΩ Ω (M.observedAt ⟨n, hn⟩).val :=
  Nat.strongRec
    (motive := fun k => ∀ hk : k < M.observed.card, swigΩ Ω (M.observedAt ⟨k, hk⟩).val)
    (fun k ih hk =>
      M.structFun (M.observedAt ⟨k, hk⟩) (fun w => parentMap M s ℓ hk ih w))
    n

/-- The auxiliary evaluator unfolds to its structural function applied to the parent tuple.

    Unfold equation for `evalObservedAux`: the `n`-th observed node's value is
    `structFun` at that node applied to the parent-value tuple assembled via
    `parentMap` from the earlier observed values. -/
lemma evalObservedAux_eq (M : Causalean.SCM N Ω)
    (s : FixedValues M) (ℓ : LatentValues M) (n : ℕ) (hn : n < M.observed.card) :
    evalObservedAux M s ℓ n hn =
      M.structFun (M.observedAt ⟨n, hn⟩)
        (fun w => parentMap M s ℓ hn
          (fun m _ hm_card => evalObservedAux M s ℓ m hm_card) w) := by
  unfold evalObservedAux
  rw [Nat.strongRec_eq]

-- ============================================================
-- § 3. The evaluation map
-- ============================================================

/-- The evaluation map sends fixed values and a latent realization to the
resulting values of all observed and latent random nodes.

    The evaluation map `φ_M : 𝒳_S × Ω_M → ∏_{w ∈ V ∪ L} 𝒳_w`.

    For each random node `w ∈ V ∪ L`, the value is computed as follows:
    * if `w ∈ M.unobserved` (latent root), the value is `ℓ ⟨w.val, _⟩`;
    * if `w ∈ M.observed`, the value is `evalObservedAux M s ℓ` at `w`'s topological
      index, which internally recurses along the topological order applying
      `M.structFun` at each observed node.

    The assembly is pointwise over `w : {w // w ∈ M.randomVars}`, not as a pair
    `(observed → ..) × (unobserved → ..)`. -/
noncomputable def evalMap (M : Causalean.SCM N Ω) :
    FixedValues M → LatentValues M → RandomValues M := fun s ℓ w =>
  if hobs : w.val ∈ M.observed then
    (M.observedAt_observedIndex ⟨w.val, hobs⟩) ▸
      evalObservedAux M s ℓ (M.observedIndex ⟨w.val, hobs⟩).val
        (M.observedIndex ⟨w.val, hobs⟩).isLt
  else
    have hrand : w.val ∈ M.observed ∪ M.unobserved := by
      have hw := w.property
      change w.val ∈ M.observed ∪ M.unobserved at hw
      exact hw
    have huo : w.val ∈ M.unobserved :=
      (Finset.mem_union.mp hrand).elim (fun ho => absurd ho hobs) id
    ℓ ⟨w.val, huo⟩

/-- On an observed node, the evaluation map is the auxiliary topological-order
evaluation transported to that node. -/
lemma evalMap_observed (M : Causalean.SCM N Ω)
    (s : FixedValues M) (ℓ : LatentValues M)
    (w : {w // w ∈ M.randomVars}) (hobs : w.val ∈ M.observed) :
    M.evalMap s ℓ w =
      (M.observedAt_observedIndex ⟨w.val, hobs⟩) ▸
        evalObservedAux M s ℓ (M.observedIndex ⟨w.val, hobs⟩).val
          (M.observedIndex ⟨w.val, hobs⟩).isLt := by
  unfold evalMap
  rw [dif_pos hobs]

/-- On a latent node, the evaluation map is direct projection from the latent assignment. -/
lemma evalMap_unobserved (M : Causalean.SCM N Ω)
    (s : FixedValues M) (ℓ : LatentValues M)
    (w : {w // w ∈ M.randomVars}) (huo : w.val ∈ M.unobserved) :
    M.evalMap s ℓ w = ℓ ⟨w.val, huo⟩ := by
  unfold evalMap
  rw [dif_neg (not_obs_of_unobs M.toSWIGGraph huo)]

/-- The parent-value dispatch function for `M.structFun v`: each parent
    `w ∈ M.dag.parents v.val` is classified into (unobserved / fixed / observed) and the
    corresponding value is read from the latent realization `ℓ`, the fixed-value
    assignment `s`, or a recursive `M.evalMap` call on the observed parent.

    Extracted as a named private definition so that the cast-free unfold lemma
    `evalMap_observed_unfold` and its helper can share the same assembly without
    inlining the three-way if-else chain. -/
private noncomputable def parentDispatch (M : Causalean.SCM N Ω)
    (s : FixedValues M) (ℓ : LatentValues M) (v : {v // v ∈ M.observed}) :
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
    M.evalMap s ℓ ⟨w.val, Finset.mem_union_left _ hobs⟩

/-- Helper at a *free* `Fin M.observed.card` index `j`: `evalObservedAux` at `j` equals
    `structFun` applied to `parentDispatch`.  Stated at a fresh `j` so there is no
    dependent-motive `▸` cast obstruction; in the observed-parent branch both sides
    produce the *same* `▸`-form via `parentMap_observed` and `evalMap_observed`, so the
    branch closes by `rfl`. -/
private lemma evalObservedAux_eq_structFunAt
    (M : Causalean.SCM N Ω) (s : FixedValues M) (ℓ : LatentValues M)
    (j : Fin M.observed.card) :
    evalObservedAux M s ℓ j.val j.isLt
      = M.structFun (M.observedAt j) (parentDispatch M s ℓ (M.observedAt j)) := by
  rw [evalObservedAux_eq M s ℓ j.val j.isLt]
  -- ⟨j.val, j.isLt⟩ = j definitionally via Fin eta, so the `structFun` head matches.
  congr 1
  funext w
  unfold parentDispatch
  by_cases huo : w.val ∈ M.unobserved
  · rw [parentMap_unobserved M s ℓ j.isLt _ w huo, dif_pos huo]
  · rw [dif_neg huo]
    by_cases hfix : w.val ∈ M.fixed
    · rw [parentMap_fixed M s ℓ j.isLt _ w hfix, dif_pos hfix]
    · rw [dif_neg hfix]
      have hedge : M.dag.edge w.val (M.observedAt j).val :=
        M.dag.mem_parents.mp w.property
      have hobs : w.val ∈ M.observed := by
        rcases Finset.mem_union.mp (M.dag_edges_classified _ _ hedge).1 with h1 | h2
        · rcases Finset.mem_union.mp h1 with hfx | hob
          · exact absurd hfx hfix
          · exact hob
        · exact absurd h2 huo
      rw [parentMap_observed M s ℓ j.isLt _ w hobs]
      -- `M.randomVars` is semireducible, so the `⟨w.val, _⟩` membership witness in the
      -- goal (typed at `M.observed ∪ M.unobserved`) is not seen as well-typed by `rw`'s
      -- keyed matching.  Closing at term level keeps the unfolding at default
      -- transparency, where the two forms are definitionally equal.
      exact (evalMap_observed M s ℓ ⟨w.val, Finset.mem_union_left _ hobs⟩ hobs).symm

/-- Cast-navigation helper: given Fin indices `j`, `k` with `k = j` and the derived
    `.val`-level cast proof, the transported `evalObservedAux` at `k` equals the
    `structFun`-at-`j` form, via the free-index helper `evalObservedAux_eq_structFunAt`.

    Proof trick: `subst` on the Fin equation eliminates `k` (both `j` and `k` are free
    variables so no circular dependency).  After `subst`, the cast proof has a
    reflexive type `(M.observedAt j).val = (M.observedAt j).val`, and proof irrelevance
    (`Subsingleton.elim`) lets us rewrite it to `rfl`, collapsing the `▸`. -/
private lemma evalObservedAux_cast_eq_structFunAt
    (M : Causalean.SCM N Ω) (s : FixedValues M) (ℓ : LatentValues M)
    {j k : Fin M.observed.card} (hkj : k = j)
    (hcast : (M.observedAt k).val = (M.observedAt j).val) :
    hcast ▸ evalObservedAux M s ℓ k.val k.isLt
      = M.structFun (M.observedAt j) (parentDispatch M s ℓ (M.observedAt j)) := by
  -- `subst k` substitutes `k := j` via `hkj`, eliminating `k`.
  subst k
  -- Replace the reflexive cast proof with `rfl` by proof irrelevance.
  have hrfl : hcast = rfl := Subsingleton.elim _ _
  rw [hrfl]
  exact evalObservedAux_eq_structFunAt M s ℓ j

/-- At an observed node, the evaluation map unfolds to the structural function
applied to fixed, latent, or recursively evaluated parent values.

    Unfold `M.evalMap` at a generic observed subtype `v` in the "recursive form": the
    value equals `M.structFun v` applied to a parent tuple where each parent is read
    from fixed values, latent values, or a recursive `M.evalMap` call.

    This is the clean `▸`-free version of `evalMap_observed`/`evalObservedAux_eq` used by
    the induced-subSCM bridge in `Induced.lean`. -/
lemma evalMap_observed_unfold (M : Causalean.SCM N Ω) (s : FixedValues M) (ℓ : LatentValues M)
    (v : {v // v ∈ M.observed}) :
    M.evalMap s ℓ ⟨v.val, Finset.mem_union_left _ v.property⟩
      = M.structFun v (fun w : {w // w ∈ M.dag.parents v.val} =>
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
            M.evalMap s ℓ ⟨w.val, Finset.mem_union_left _ hobs⟩) := by
  -- Reduce to the `parentDispatch` form via a helper that takes the Subtype witness
  -- `hw : M.observedAt j = w` as a parameter.  `subst hw` inside the helper eliminates
  -- the circular dependency between `v` and `M.observedIndex v`.
  suffices h : ∀ (j : Fin M.observed.card) (w : {v // v ∈ M.observed})
                 (_ : M.observedAt j = w),
               M.evalMap s ℓ ⟨w.val, Finset.mem_union_left _ w.property⟩
                 = M.structFun w (parentDispatch M s ℓ w) by
    have key := h (M.observedIndex ⟨v.val, v.property⟩) v
                  (Subtype.ext (M.observedAt_observedIndex ⟨v.val, v.property⟩))
    rw [key]
    rfl
  intro j w hw
  subst hw
  -- `w` eliminated.  Goal mentions `M.observedAt j` only.
  -- `rw` cannot key on `M.evalMap s ℓ ⟨_, _⟩` here: `M.randomVars` is semireducible, so
  -- the membership witness (typed at `M.observed ∪ M.unobserved`) is not accepted at
  -- `implicit` transparency.  Chain the rewrite at term level instead.
  refine (evalMap_observed M s ℓ
      ⟨(M.observedAt j).val, Finset.mem_union_left _ (M.observedAt j).property⟩
      (M.observedAt j).property).trans ?_
  -- Apply the cast helper: the Fin index `M.observedIndex ⟨(M.observedAt j).val, _⟩`
  -- reduces to `j` via `observedIndex_observedAt` (after Subtype eta), and the cast
  -- proof is discharged via proof irrelevance inside the helper.
  exact evalObservedAux_cast_eq_structFunAt M s ℓ
    (M.observedIndex_observedAt j)
    (M.observedAt_observedIndex ⟨(M.observedAt j).val, (M.observedAt j).property⟩)

/-- At every position in a causal model's topological ordering of observed variables, the
recursively evaluated observed value is measurable as a function of the model's fixed and latent
inputs. -/
lemma evalObservedAux_measurable (M : Causalean.SCM N Ω) :
    ∀ (n : ℕ) (hn : n < M.observed.card),
      Measurable (fun p : FixedValues M × LatentValues M =>
        evalObservedAux M p.1 p.2 n hn) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro hn
    have hrw :
        (fun p : FixedValues M × LatentValues M => evalObservedAux M p.1 p.2 n hn) =
        (fun p => M.structFun (M.observedAt ⟨n, hn⟩)
            (fun w => parentMap M p.1 p.2 hn
              (fun m _ hm_card => evalObservedAux M p.1 p.2 m hm_card) w)) := by
      funext p
      exact evalObservedAux_eq M p.1 p.2 n hn
    rw [hrw]
    refine (M.structFun_measurable _).comp ?_
    refine measurable_pi_lambda _ (fun w => ?_)
    by_cases huo : w.val ∈ M.unobserved
    · have hfun :
          (fun p : FixedValues M × LatentValues M =>
              parentMap M p.1 p.2 hn
                (fun m _ hm_card => evalObservedAux M p.1 p.2 m hm_card) w) =
          (fun p => p.2 ⟨w.val, huo⟩) := by
        funext p
        exact parentMap_unobserved M p.1 p.2 hn _ w huo
      rw [hfun]
      exact (measurable_pi_apply _).comp measurable_snd
    · by_cases hfix : w.val ∈ M.fixed
      · have hfun :
            (fun p : FixedValues M × LatentValues M =>
                parentMap M p.1 p.2 hn
                  (fun m _ hm_card => evalObservedAux M p.1 p.2 m hm_card) w) =
            (fun p => p.1 ⟨w.val, hfix⟩) := by
          funext p
          exact parentMap_fixed M p.1 p.2 hn _ w hfix
        rw [hfun]
        exact (measurable_pi_apply _).comp measurable_fst
      · have hedge : M.dag.edge w.val (M.observedAt ⟨n, hn⟩).val :=
          M.dag.mem_parents.mp w.property
        have hobs : w.val ∈ M.observed := by
          have hcls := (M.dag_edges_classified _ _ hedge).1
          rcases Finset.mem_union.mp hcls with hfo | huo'
          · rcases Finset.mem_union.mp hfo with hf | ho
            · exact absurd hf hfix
            · exact ho
          · exact absurd huo' huo
        have hj : (M.observedIndex ⟨w.val, hobs⟩).val < n :=
          M.observed_parent_index_lt hn hedge hobs
        have hfun :
            (fun p : FixedValues M × LatentValues M =>
                parentMap M p.1 p.2 hn
                  (fun m _ hm_card => evalObservedAux M p.1 p.2 m hm_card) w) =
            (fun p =>
              (M.observedAt_observedIndex ⟨w.val, hobs⟩) ▸
                evalObservedAux M p.1 p.2
                  (M.observedIndex ⟨w.val, hobs⟩).val
                  (M.observedIndex ⟨w.val, hobs⟩).isLt) := by
          funext p
          exact parentMap_observed M p.1 p.2 hn _ w hobs
        rw [hfun]
        exact measurable_family_cast _ (ih _ hj _)

/-- The evaluation map is jointly measurable in the fixed-value assignment and latent realization.

    The evaluation map is jointly measurable in `(s, ℓ)`.

    The proof proceeds by structural induction on the topological order: each new
    coordinate is either a projection from `s`/`ℓ` (measurable) or an application of
    `M.structFun v` (measurable by `structFun_measurable`) to a tuple of already-
    measurable coordinates. -/
theorem evalMap_measurable (M : Causalean.SCM N Ω) :
    Measurable (Function.uncurry M.evalMap) := by
  refine measurable_pi_iff.mpr (fun w => ?_)
  by_cases hobs : w.val ∈ M.observed
  · have hfun :
        (fun p : FixedValues M × LatentValues M =>
            Function.uncurry M.evalMap p w) =
        (fun p =>
          (M.observedAt_observedIndex ⟨w.val, hobs⟩) ▸
            evalObservedAux M p.1 p.2
              (M.observedIndex ⟨w.val, hobs⟩).val
              (M.observedIndex ⟨w.val, hobs⟩).isLt) := by
      funext p
      exact evalMap_observed M p.1 p.2 w hobs
    rw [hfun]
    exact measurable_family_cast _ (evalObservedAux_measurable M _ _)
  · have hrand : w.val ∈ M.observed ∪ M.unobserved := by
      have hw := w.property
      change w.val ∈ M.observed ∪ M.unobserved at hw
      exact hw
    have huo : w.val ∈ M.unobserved :=
      (Finset.mem_union.mp hrand).elim (fun ho => absurd ho hobs) id
    have hfun :
        (fun p : FixedValues M × LatentValues M =>
            Function.uncurry M.evalMap p w) =
        (fun p => p.2 ⟨w.val, huo⟩) := by
      funext p
      exact evalMap_unobserved M p.1 p.2 w huo
    rw [hfun]
    exact (measurable_pi_apply _).comp measurable_snd

/-- An observed variable has the same recursively evaluated value under two inputs when
    those inputs agree on every fixed and latent cause that can affect the target variables.
    This expresses the local ancestral dependence of a structural causal model. -/
lemma evalObservedAux_agree_anc (M : Causalean.SCM N Ω)
    (T : Finset (SWIGNode N))
    {s s' : FixedValues M} {ℓ ℓ' : LatentValues M}
    (hs : ∀ (d : SWIGNode N) (hd : d ∈ M.fixed),
      (∃ v ∈ T, d = v ∨ M.dag.isAncestor d v) →
      s ⟨d, hd⟩ = s' ⟨d, hd⟩)
    (hℓ : ∀ (u : SWIGNode N) (hu : u ∈ M.unobserved),
      (∃ v ∈ T, u = v ∨ M.dag.isAncestor u v) →
      ℓ ⟨u, hu⟩ = ℓ' ⟨u, hu⟩) :
    ∀ (n : ℕ) (hn : n < M.observed.card)
      (_ : ∃ v ∈ T, (M.observedAt ⟨n, hn⟩).val = v ∨
        M.dag.isAncestor (M.observedAt ⟨n, hn⟩).val v),
      evalObservedAux M s ℓ n hn = evalObservedAux M s' ℓ' n hn := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro hn hAnc
    rw [evalObservedAux_eq M s ℓ n hn, evalObservedAux_eq M s' ℓ' n hn]
    congr 1
    funext w
    have hedge : M.dag.edge w.val (M.observedAt ⟨n, hn⟩).val :=
      M.dag.mem_parents.mp w.property
    have hw_anc_obs : M.dag.isAncestor w.val (M.observedAt ⟨n, hn⟩).val :=
      DAG.isAncestor.edge hedge
    -- Chain the ancestor witness from `observedAt n` through `w`.
    have hAncW : ∃ v ∈ T, w.val = v ∨ M.dag.isAncestor w.val v := by
      rcases hAnc with ⟨v, hv, hOrAnc⟩
      refine ⟨v, hv, ?_⟩
      rcases hOrAnc with hEq | hAncToV
      · -- `observedAt n = v`, so `w` is a direct ancestor of `v`.
        exact Or.inr (hEq ▸ hw_anc_obs)
      · -- `observedAt n` ancestor of `v`: transit through `w`.
        exact Or.inr (M.dag.isAncestor_trans hw_anc_obs hAncToV)
    by_cases huo : w.val ∈ M.unobserved
    · rw [parentMap_unobserved M s ℓ hn _ w huo,
          parentMap_unobserved M s' ℓ' hn _ w huo]
      exact hℓ w.val huo hAncW
    · by_cases hfix : w.val ∈ M.fixed
      · rw [parentMap_fixed M s ℓ hn _ w hfix,
            parentMap_fixed M s' ℓ' hn _ w hfix]
        exact hs w.val hfix hAncW
      · -- `w` is observed: apply IH at its smaller topological index.
        have hobs : w.val ∈ M.observed := by
          rcases Finset.mem_union.mp (M.dag_edges_classified _ _ hedge).1 with h1 | h2
          · rcases Finset.mem_union.mp h1 with hfx | hob
            · exact absurd hfx hfix
            · exact hob
          · exact absurd h2 huo
        have hj : (M.observedIndex ⟨w.val, hobs⟩).val < n :=
          M.observed_parent_index_lt hn hedge hobs
        rw [parentMap_observed M s ℓ hn _ w hobs,
            parentMap_observed M s' ℓ' hn _ w hobs]
        congr 1
        apply ih _ hj
        -- Re-cast the ancestor witness at `observedAt (observedIndex w) = w`.
        rcases hAncW with ⟨v, hv, hwv⟩
        refine ⟨v, hv, ?_⟩
        have h_at : (M.observedAt
            ⟨(M.observedIndex ⟨w.val, hobs⟩).val,
              (M.observedIndex ⟨w.val, hobs⟩).isLt⟩).val = w.val :=
          M.observedAt_observedIndex ⟨w.val, hobs⟩
        rw [h_at]
        exact hwv

/-- Evaluation on a target set depends only on fixed and latent nodes that are
in or ancestral to that target set.

    **Ancestral factorization** (Lemma `lem:scm-ancestral-factor`).

    For any `T ⊆ V`, the value of `evalMap M s ℓ` at every `v ∈ T` depends on `(s, ℓ)`
    only through the coordinates indexed by `An_G(T) ∩ (S ∪ L)` of `(s, ℓ)` — or, in the
    congruence form stated below, any two inputs `(s, ℓ)` and `(s', ℓ')` that agree on
    every fixed/latent node that is equal to or a proper ancestor of some `v' ∈ T`
    produce the same `evalMap` value at `v`.

    The statement uses the inductive predicate `DAG.isAncestor` rather than the
    computed ancestor set, so the dependence claim is stated directly in terms
    of graph reachability.  It is consumed by `SCM.induce_marginal_compat` and
    the Markov/do-calculus layers. -/
theorem ancestralFactorization (M : Causalean.SCM N Ω)
    (T : Finset (SWIGNode N))
    {s s' : FixedValues M} {ℓ ℓ' : LatentValues M}
    (hs : ∀ (d : SWIGNode N) (hd : d ∈ M.fixed),
      (∃ v ∈ T, d = v ∨ M.dag.isAncestor d v) →
      s ⟨d, hd⟩ = s' ⟨d, hd⟩)
    (hℓ : ∀ (u : SWIGNode N) (hu : u ∈ M.unobserved),
      (∃ v ∈ T, u = v ∨ M.dag.isAncestor u v) →
      ℓ ⟨u, hu⟩ = ℓ' ⟨u, hu⟩)
    {v : SWIGNode N} (hv : v ∈ T) (hv_obs : v ∈ M.observed) :
    M.evalMap s ℓ ⟨v, Finset.mem_union_left _ hv_obs⟩ =
    M.evalMap s' ℓ' ⟨v, Finset.mem_union_left _ hv_obs⟩ := by
  rw [evalMap_observed M s ℓ ⟨v, Finset.mem_union_left _ hv_obs⟩ hv_obs,
      evalMap_observed M s' ℓ' ⟨v, Finset.mem_union_left _ hv_obs⟩ hv_obs]
  congr 1
  apply evalObservedAux_agree_anc M T hs hℓ
  refine ⟨v, hv, Or.inl ?_⟩
  exact M.observedAt_observedIndex ⟨v, hv_obs⟩

end SCM

end Causalean
