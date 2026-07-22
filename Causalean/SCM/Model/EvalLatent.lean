/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Latent-restricted factorization of the evaluation map

This file provides `evalMap_factors_excluding_latent` (§7): for a latent root
`a ∈ M.unobserved` and a Finset `T` of non-descendants of `a`, the projection
of `evalMap s` to `T` factors through all latent coordinates *except* `a`.

Used by `GlobalMarkov.full_local_markov_latent` together with
`indepFun_pi_of_disjoint` to show independence of the `{a}`-projection from
the `T`-projection of `evalMap s`.

## References

* Basic Concepts.tex, Proposition `prop:scm-evalmap`.
-/

import Causalean.SCM.Model.Evaluation

/-! # Latent-Restricted Evaluation Factorization

This file proves that, for a latent root and a set of non-descendant random
coordinates, the corresponding evaluation projection does not depend on the
chosen latent coordinate. The result is used to establish independence claims
for the global Markov property of structural causal models.

The main theorem, `SCM.evalMap_factors_excluding_latent`, states that if
`T ⊆ M.randomVars` contains no descendants of a latent root `a`, then the
projection of `M.evalMap s` to `T` factors through all latent coordinates except
the coordinate at `a`.
-/

namespace Causalean

namespace SCM

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

open scoped MeasureTheory ProbabilityTheory

-- ============================================================
-- § 7. Latent-restricted factorization at non-descendants
-- ============================================================

/-- **Latent-restricted factorization away from a chosen latent root.**

    For a latent root `a ∈ M.unobserved` and any Finset `T ⊆ randomVars` such that
    every `v ∈ T` satisfies `¬ M.dag.isAncestor a v` and `v ≠ a` (in particular,
    `T ⊆ M.dag.nonDescendants a ∩ M.randomVars`), the projection
    `valuesProjection hT ∘ M.evalMap s` factors through the latent coordinates at
    indices in `Finset.univ.erase ⟨a, ha⟩` — i.e., it does not depend on
    `ℓ ⟨a, ha⟩`.

    Used by `GlobalMarkov.full_local_markov_latent` together with
    `indepFun_pi_of_disjoint` to show that the projection of `evalMap s` to `{a}`
    (which only sees latent `⟨a, ha⟩`) is independent of the projection to a
    non-descendants set `T` (which only sees latent coordinates excluding
    `⟨a, ha⟩`). -/
theorem evalMap_factors_excluding_latent (M : Causalean.SCM N Ω)
    (s : FixedValues M) (a : SWIGNode N) (ha : a ∈ M.unobserved)
    (T : Finset (SWIGNode N)) (hT_sub : T ⊆ M.randomVars)
    (h_excl : ∀ v ∈ T, ¬ M.dag.isAncestor a v ∧ v ≠ a) :
    ∃ g : ((i : {i // i ∈ (Finset.univ.erase
              (⟨a, ha⟩ : {u // u ∈ M.unobserved}))}) → swigΩ Ω i.val.val) →
            ValuesOn T (swigΩ Ω),
      Measurable g ∧
      ∀ ℓ : LatentValues M,
        valuesProjection hT_sub (M.evalMap s ℓ)
          = g (fun i => ℓ i.val) := by
  classical
  -- The subtype index we are erasing.
  set A : {u // u ∈ M.unobserved} := ⟨a, ha⟩ with hA_def
  -- Default value at `a`, obtained from `IsProbabilityMeasure`.
  haveI : MeasureTheory.IsProbabilityMeasure (M.latentDist A) :=
    M.isProbability_latent A
  haveI hNE_a : Nonempty (swigΩ Ω a) :=
    MeasureTheory.nonempty_of_isProbabilityMeasure (M.latentDist A)
  let default_at_a : swigΩ Ω a := Classical.arbitrary _
  -- `extend` fills in `default_at_a` at index `A` and copies the rest.
  let extend :
      ((i : {i // i ∈ Finset.univ.erase A}) → swigΩ Ω i.val.val) →
        LatentValues M :=
    fun r u =>
      if hu : u = A then
        (by subst hu; exact default_at_a)
      else
        r ⟨u, Finset.mem_erase.mpr ⟨hu, Finset.mem_univ _⟩⟩
  -- Measurability of `extend`.
  have hext_meas : Measurable extend := by
    refine measurable_pi_iff.mpr (fun u => ?_)
    by_cases hu : u = A
    · -- Constant branch: `extend r u = default_at_a` (up to cast).
      have hfun :
          (fun r : (i : {i // i ∈ Finset.univ.erase A}) → swigΩ Ω i.val.val =>
              extend r u) = fun _ =>
            (by subst hu; exact default_at_a) := by
        funext r
        simp [extend, hu]
      rw [hfun]; exact measurable_const
    · -- Projection branch: `extend r u = r ⟨u, _⟩`.
      have hfun :
          (fun r : (i : {i // i ∈ Finset.univ.erase A}) → swigΩ Ω i.val.val =>
              extend r u) = fun r =>
            r ⟨u, Finset.mem_erase.mpr ⟨hu, Finset.mem_univ _⟩⟩ := by
        funext r
        simp [extend, hu]
      rw [hfun]; exact measurable_pi_apply _
  -- Build `g`.
  refine ⟨fun r => valuesProjection hT_sub (M.evalMap s (extend r)),
    ?_, ?_⟩
  · -- Measurability: projection ∘ evalMap(s, ·) ∘ extend.
    have hev_s :
        Measurable (fun ℓ : LatentValues M => M.evalMap s ℓ) := by
      have := M.evalMap_measurable
      exact this.comp (Measurable.prodMk measurable_const measurable_id)
    exact (measurable_valuesProjection hT_sub).comp (hev_s.comp hext_meas)
  · -- Pointwise factorization.
    intro ℓ
    -- Unfold `valuesProjection` on both sides via `funext` over `w ∈ T`.
    apply funext
    intro w
    -- Notation for the target (full) membership on `M.randomVars`.
    have hw_rand : w.val ∈ M.randomVars := hT_sub w.property
    -- Destruct whether `w.val` is unobserved or observed.
    rcases Finset.mem_union.mp hw_rand with hw_obs | hw_unobs
    · -- Observed case: use `ancestralFactorization` with `T = {w.val}`.
      have hwT_sub : ({w.val} : Finset (SWIGNode N)) ⊆ M.observed :=
        Finset.singleton_subset_iff.mpr hw_obs
      have hwmem : w.val ∈ ({w.val} : Finset (SWIGNode N)) :=
        Finset.mem_singleton.mpr rfl
      -- Show `evalMap s ℓ` and `evalMap s (extend (fun i => ℓ i.val))` agree at `w`.
      -- The `s` agreement is trivial (same `s`).
      -- The `ℓ` agreement: at any ancestor `u` of `w.val` (including `u = w.val`),
      -- `extend (fun i => ℓ i.val) ⟨u, hu⟩ = ℓ ⟨u, hu⟩`.  This holds because
      -- `u ≠ a`: otherwise `isAncestor a w.val` (from `isAncestor u w.val`) or
      -- `a = w.val` (from `u = w.val`), both contradicting `h_excl w.val hwT`.
      have heq :
          M.evalMap s ℓ ⟨w.val, Finset.mem_union_left _ hw_obs⟩ =
          M.evalMap s (extend (fun i => ℓ i.val))
            ⟨w.val, Finset.mem_union_left _ hw_obs⟩ := by
        refine M.ancestralFactorization ({w.val} : Finset (SWIGNode N))
          hwT_sub ?_ ?_ hwmem
        · -- Fixed agreement: same `s` on both sides, `rfl`.
          intro d hd _; rfl
        · -- Latent agreement: `extend (fun i => ℓ i.val) ⟨u, hu⟩ = ℓ ⟨u, hu⟩`.
          intro u hu hAnc
          obtain ⟨v', hv', hOr⟩ := hAnc
          have hv'eq : v' = w.val := Finset.mem_singleton.mp hv'
          have hOr' : u = w.val ∨ M.dag.isAncestor u w.val := hv'eq ▸ hOr
          -- Get the exclusion hypothesis for `w`.
          have hT_w : w.val ∈ T := w.property
          have hexcl_w := h_excl w.val hT_w
          -- Now show `u ≠ a`.
          have hu_ne_a : u ≠ a := by
            intro hu_eq
            subst hu_eq
            rcases hOr' with hueq | hanc
            · -- `u = w.val`: so `w.val = a`, but `w.val ≠ a`.
              exact hexcl_w.2 hueq.symm
            · -- `isAncestor a w.val`, but `¬ isAncestor a w.val`.
              exact hexcl_w.1 hanc
          -- Subtype inequality.
          have hsub_ne : (⟨u, hu⟩ : {u // u ∈ M.unobserved}) ≠ A := by
            intro heq_sub
            apply hu_ne_a
            exact (Subtype.mk.injEq _ _ _ _).mp heq_sub
          -- Unfold `extend` in the `else` branch.
          change ℓ ⟨u, hu⟩ = extend (fun i => ℓ i.val) ⟨u, hu⟩
          simp [extend, hsub_ne]
      -- Conclude the `valuesProjection` equation.
      change (M.evalMap s ℓ) ⟨w.val, hw_rand⟩ =
          valuesProjection hT_sub (M.evalMap s (extend (fun i => ℓ i.val))) w
      -- `valuesProjection hT_sub ξ w = ξ ⟨w.val, hT_sub w.property⟩`.
      change (M.evalMap s ℓ) ⟨w.val, hw_rand⟩
          = M.evalMap s (extend (fun i => ℓ i.val)) ⟨w.val, hT_sub w.property⟩
      -- The two RHS memberships are proof-irrelevant; collapse via `heq`.
      rw [show (⟨w.val, hw_rand⟩ : {w // w ∈ M.randomVars}) =
            ⟨w.val, Finset.mem_union_left _ hw_obs⟩ from
          Subtype.ext rfl]
      rw [show (⟨w.val, hT_sub w.property⟩ : {w // w ∈ M.randomVars}) =
            ⟨w.val, Finset.mem_union_left _ hw_obs⟩ from
          Subtype.ext rfl]
      exact heq
    · -- Unobserved case: both sides collapse to a latent read.
      -- Exclusion at `w`.
      have hT_w : w.val ∈ T := w.property
      have hexcl_w := h_excl w.val hT_w
      have hw_ne_a : w.val ≠ a := hexcl_w.2
      -- LHS: `evalMap s ℓ ⟨w, _⟩ = ℓ ⟨w, hw_unobs⟩`.
      have hlhs : M.evalMap s ℓ ⟨w.val, hw_rand⟩ = ℓ ⟨w.val, hw_unobs⟩ :=
        M.evalMap_unobserved s ℓ ⟨w.val, hw_rand⟩ hw_unobs
      -- RHS: similarly equals `extend _ ⟨w, hw_unobs⟩`.
      have hrhs :
          M.evalMap s (extend (fun i => ℓ i.val)) ⟨w.val, hw_rand⟩
            = extend (fun i => ℓ i.val) ⟨w.val, hw_unobs⟩ :=
        M.evalMap_unobserved s (extend (fun i => ℓ i.val))
          ⟨w.val, hw_rand⟩ hw_unobs
      -- Subtype inequality `⟨w.val, hw_unobs⟩ ≠ A`.
      have hsub_ne : (⟨w.val, hw_unobs⟩ : {u // u ∈ M.unobserved}) ≠ A := by
        intro heq_sub
        apply hw_ne_a
        exact (Subtype.mk.injEq _ _ _ _).mp heq_sub
      -- `extend` in the `else` branch reduces to the `r`-read, which is
      -- `(fun i => ℓ i.val) ⟨⟨w.val, hw_unobs⟩, _⟩ = ℓ ⟨w.val, hw_unobs⟩`.
      have hext_val :
          extend (fun i => ℓ i.val) ⟨w.val, hw_unobs⟩ = ℓ ⟨w.val, hw_unobs⟩ := by
        simp [extend, hsub_ne]
      change (M.evalMap s ℓ) ⟨w.val, hw_rand⟩
          = valuesProjection hT_sub
              (M.evalMap s (extend (fun i => ℓ i.val))) w
      change (M.evalMap s ℓ) ⟨w.val, hw_rand⟩
          = M.evalMap s (extend (fun i => ℓ i.val)) ⟨w.val, hT_sub w.property⟩
      have hrand_eq : (⟨w.val, hT_sub w.property⟩ : {w // w ∈ M.randomVars})
          = ⟨w.val, hw_rand⟩ := rfl
      rw [hrand_eq, hlhs, hrhs, hext_val]

end SCM

end Causalean
