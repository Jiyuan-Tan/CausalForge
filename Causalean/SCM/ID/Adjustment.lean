/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Adjustment functionals (backdoor and frontdoor)

This file defines the **graph-level adjustment functionals** that turn an
SCM's observational kernel into a post-intervention `Y`-marginal under
the backdoor / frontdoor identification criteria.  Their purpose is to
factor cross-SCM identifiability proofs into:

1. A *single-SCM completeness* lemma stating
   `(M.fixSet X).obsKernel.map proj_Y = M.adjustmentFunctional X Y Z`,
   whose content is the do-calculus reasoning (Rules 2 and 3).
2. A *cross-SCM congruence* lemma stating that
   `M.adjustmentFunctional X Y Z` depends only on `M.toSWIGGraph` and
   `M.obsKernel`, hence transports across two SCMs sharing both.

The two pieces compose into the corresponding downstream completeness and
identifiability theorems. The functionals themselves are kernel-native:
their bodies are compositions of observational marginals, `obsCondKernel`,
`Kernel.comap`, `Kernel.map`, and `compProd`, and the invariance theorems
show that no structural fields beyond the SWIG graph and observational kernel
enter the adjustment formulas.

## References

* Basic Concepts.tex, Theorems `thm:scm-backdoor` (lines 636-645) and
  `thm:scm-frontdoor` (lines 647-660).
* Pearl, J. (2009), *Causality*, Theorem 3.3.2 (backdoor) and
  Theorem 3.3.4 (frontdoor).
-/

import Causalean.SCM.Do.DoCalculus
import Causalean.SCM.Model.InterventionSet
import Causalean.SCM.Model.Kernel

/-! # Adjustment Functionals

This file defines graph-level adjustment functionals for backdoor and frontdoor
identification. These functionals express post-intervention outcome distributions in
terms of observational kernels, enabling single-model completeness arguments to be
combined with cross-model invariance statements. It also proves finite-kernel
instances and cross-SCM invariance for both adjustment functionals. -/

namespace Causalean

variable {N : Type*} [DecidableEq N] [Fintype N]

namespace SCM

variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]
-- The genuine per-node primitives. Every ValuesOn-level `StandardBorelSpace`/`Nonempty`,
-- every `obsKernel`/`jointKernel` finiteness, every `CountableOrCountablyGenerated`, and the
-- `obsCondKernel`/adjustment-kernel finiteness instances below all derive from just these two.
variable [∀ n, StandardBorelSpace (swigΩ Ω n)] [∀ n, Nonempty (swigΩ Ω n)]

open scoped MeasureTheory ProbabilityTheory

/-- The observational conditional kernel `obsCondKernel Y CC` is a Markov kernel (its
    values are probability measures), inherited from Mathlib's `condKernel`. -/
instance instIsMarkovKernelObsCondKernel (M : Causalean.SCM N Ω)
    (Y CC : Finset (SWIGNode N)) (hY : Y ⊆ M.observed) (hCC : CC ⊆ M.observed) :
    ProbabilityTheory.IsMarkovKernel (M.obsCondKernel Y CC hY hCC) := by
  unfold SCM.obsCondKernel; infer_instance

/-- **Backdoor adjustment functional.**

    The graph-level functional that maps an SCM's observational kernel
    plus a backdoor-admissible adjustment set `Z` to the post-intervention
    `Y`-marginal kernel.  Concretely, in informal notation,

      `backdoorAdjustment M X Y Z (s_post) =
         ∫_z  (P_{M.obsKernel s_orig}(Y | X = s_post|_X, Z = z))  dP_{M.obsKernel s_orig}(z)`,

    where `s_orig := M.fixSetProj X _ _ s_post` is the original
    fixed-slice underlying the post-intervention slice.  By design the
    body uses `M.toSWIGGraph` and `M.obsKernel` only — no other SCM
    fields enter — so the resulting kernel is invariant under
    SCM-equivalence sharing the SWIG graph and observational kernel
    (`backdoorAdjustment_invariant`).

    Body: `Kernel.bind` over the `Z`-marginal of `M.obsKernel s_orig`
    against the `(X.image .random ∪ Z)`-conditional
    `M.obsCondKernel Y (X.image .random ∪ Z) _ _`, composed with
    `M.fillZrW X hX_obs hX_fixed Z s_post` to fill the `X.image .random`
    slice from `s_post` (reindexed from `X.image .fixed` via
    `zFixedAsRandom`) before pairing with the `Z`-value `z`.  The
    measurability side goal follows from `measurable_fillZrW_prod` together
    with the fixed-slice projection. -/
noncomputable def backdoorAdjustment
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hX_obs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hX_fixed : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (Y Z : Finset (SWIGNode N))
    (_hY : Y ⊆ M.observed)
    (_hZ : Z ⊆ M.observed) :
    ProbabilityTheory.Kernel
      (M.fixSet X hX_obs hX_fixed).FixedValues
      (ValuesOn Y (swigΩ Ω)) := by
  -- X.image SWIGNode.random ∪ Z ⊆ M.observed, combining `hX_obs` and `_hZ`.
  have hXZ : X.image SWIGNode.random ∪ Z ⊆ M.observed := by
    refine Finset.union_subset ?_ _hZ
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨D, hD, rfl⟩
    exact hX_obs D hD
  let zMarginal :
      ProbabilityTheory.Kernel M.FixedValues (ValuesOn Z (swigΩ Ω)) :=
    (M.obsKernel).map (valuesProjection _hZ)
  let zMarginalPost :
      ProbabilityTheory.Kernel
        (M.fixSet X hX_obs hX_fixed).FixedValues
        (ValuesOn Z (swigΩ Ω)) :=
    zMarginal.comap (M.fixSetProj X hX_obs hX_fixed)
      (M.measurable_fixSetProj X hX_obs hX_fixed)
  let condPost :
      ProbabilityTheory.Kernel
        ((M.fixSet X hX_obs hX_fixed).FixedValues × ValuesOn Z (swigΩ Ω))
        (ValuesOn Y (swigΩ Ω)) :=
    (M.obsCondKernel Y (X.image SWIGNode.random ∪ Z) _hY hXZ).comap
      (fun p =>
        (M.fixSetProj X hX_obs hX_fixed p.1,
         M.fillZrW X hX_obs hX_fixed Z p.1 p.2))
      (Measurable.prodMk
        ((M.measurable_fixSetProj X hX_obs hX_fixed).comp measurable_fst)
        (M.measurable_fillZrW_prod X hX_obs hX_fixed Z))
  exact ((zMarginalPost ⊗ₖ condPost).map Prod.snd)

/-- The backdoor-adjustment functional is a finite kernel (a `compProd` of finite
    kernels, pushed through `Prod.snd`). -/
instance instIsFiniteKernelBackdoorAdjustment (M : Causalean.SCM N Ω) (X : Finset N)
    (hX_obs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hX_fixed : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (Y Z : Finset (SWIGNode N)) (hY : Y ⊆ M.observed) (hZ : Z ⊆ M.observed) :
    ProbabilityTheory.IsFiniteKernel (M.backdoorAdjustment X hX_obs hX_fixed Y Z hY hZ) := by
  rw [SCM.backdoorAdjustment]; infer_instance

/-- **Frontdoor adjustment functional.**

    The graph-level functional that maps an SCM's observational kernel
    plus a frontdoor-admissible mediator set `Z` to the post-intervention
    `Y`-marginal kernel using only `M.toSWIGGraph` and `M.obsKernel`.

    Concretely, in informal notation,

      `frontdoorAdjustment M X Y Z (s_post) =
         ∫_z  ( ∫_{x'} P(Y | X = x', Z = z) dP(X' | s_orig) )  dP(Z | X = x_do, s_orig)`,

    where `s_orig := M.fixSetProj X _ _ s_post`, `x_do` is the *intervention*
    treatment value read off the post-intervention slice `s_post` (via
    `zFixedAsRandom`), and `x'` is an *independent observational copy* of
    treatment, integrated only inside the outcome leg.  This is Pearl's
    frontdoor functional: the mediator law `P(Z | X = x_do)` conditions on the
    intervention treatment value, while the outcome leg averages
    `P(Y | X = x', Z = z)` over the observational treatment marginal.  The two
    distinct treatment roles — `x_do` in the mediator law, the integrated `x'`
    in the outcome leg — are the two-stage structure of the frontdoor criterion
    (do-calculus Rule 2 on the mediator step `do(X) → X`, and Rule 2/3 on the
    back-door-free outcome step `do(Z) → Z`).  By design the body uses
    `M.toSWIGGraph` and `M.obsKernel` only, so it is invariant under
    SCM-equivalence sharing the SWIG graph and observational kernel
    (`frontdoorAdjustment_invariant`). -/
noncomputable def frontdoorAdjustment
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hX_obs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hX_fixed : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (Y Z : Finset (SWIGNode N))
    (_hY : Y ⊆ M.observed)
    (_hZ : Z ⊆ M.observed) :
    ProbabilityTheory.Kernel
      (M.fixSet X hX_obs hX_fixed).FixedValues
      (ValuesOn Y (swigΩ Ω)) := by
  -- `X.image SWIGNode.random ⊆ M.observed` (from `hX_obs`).
  have hXr : X.image SWIGNode.random ⊆ M.observed := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨D, hD, rfl⟩
    exact hX_obs D hD
  -- `X.image SWIGNode.random ∪ Z ⊆ M.observed`.
  have hXZ : X.image SWIGNode.random ∪ Z ⊆ M.observed :=
    Finset.union_subset hXr _hZ
  -- **Frontdoor body** (Pearl's frontdoor functional).  In informal notation,
  --   frontdoorAdjustment M X Y Z (s_post)
  --     = ∫_z  ( ∫_{x'} P(Y | X = x', Z = z) dP(X' | s_orig) )  dP(Z | X = x_do)
  -- where `s_orig := M.fixSetProj X _ _ s_post`, `x_do` is the *intervention*
  -- treatment value read off `s_post`, and `x'` is an independent observational
  -- copy of treatment integrated only inside the outcome leg.  The split
  -- between the intervention slice `x_do` in the mediator law `P(Z | X = x_do)`
  -- and the observational marginal `dP(X')` in the outcome leg is the two-stage
  -- structure of the frontdoor criterion.
  --
  -- `x_do` : the intervention treatment slice read off `s_post` — this is the
  -- inner content of `fillZrW` (relabel the do-set fixed `X`-slice as random).
  let xDo : (M.fixSet X hX_obs hX_fixed).FixedValues →
      ValuesOn (X.image SWIGNode.random) (swigΩ Ω) :=
    fun s => zFixedAsRandom
      (valuesProjection (fixSet_image_fixed_subset M X hX_obs hX_fixed) s)
  have hxDo : Measurable xDo :=
    measurable_zFixedAsRandom.comp
      (measurable_valuesProjection (fixSet_image_fixed_subset M X hX_obs hX_fixed))
  -- Mediator law `P(Z | X = x_do, s_orig)`, conditioned on the *intervention* X.
  let zCondXdo :
      ProbabilityTheory.Kernel (M.fixSet X hX_obs hX_fixed).FixedValues
        (ValuesOn Z (swigΩ Ω)) :=
    (M.obsCondKernel Z (X.image SWIGNode.random) _hZ hXr).comap
      (fun s => (M.fixSetProj X hX_obs hX_fixed s, xDo s))
      (Measurable.prodMk (M.measurable_fixSetProj X hX_obs hX_fixed) hxDo)
  -- Observational X'-marginal `P(X' | s_orig)` for the outcome leg.
  let xMarginal :
      ProbabilityTheory.Kernel (M.fixSet X hX_obs hX_fixed).FixedValues
        (ValuesOn (X.image SWIGNode.random) (swigΩ Ω)) :=
    (M.obsKernel.map (valuesProjection hXr)).comap
      (M.fixSetProj X hX_obs hX_fixed)
      (M.measurable_fixSetProj X hX_obs hX_fixed)
  -- Outcome law `P(Y | X' = x', Z = z, s_orig)`.
  let yCondXZ :
      ProbabilityTheory.Kernel
        ((M.fixSet X hX_obs hX_fixed).FixedValues ×
          ValuesOn (X.image SWIGNode.random) (swigΩ Ω) × ValuesOn Z (swigΩ Ω))
        (ValuesOn Y (swigΩ Ω)) :=
    (M.obsCondKernel Y (X.image SWIGNode.random ∪ Z) _hY hXZ).comap
      (fun p =>
        (M.fixSetProj X hX_obs hX_fixed p.1,
         valuesUnionMk p.2.1 p.2.2))
      (Measurable.prodMk
        ((M.measurable_fixSetProj X hX_obs hX_fixed).comp measurable_fst)
        (measurable_valuesUnionMk.comp
          (Measurable.prodMk
            (measurable_fst.comp measurable_snd)
            (measurable_snd.comp measurable_snd))))
  -- Inner outcome leg `∫_{x'} P(Y | X' = x', Z = z) dP(X' | s_orig)`: a kernel
  -- in `(s_post, z)` that integrates out the observational X' while holding `z`.
  let innerY :
      ProbabilityTheory.Kernel
        ((M.fixSet X hX_obs hX_fixed).FixedValues × ValuesOn Z (swigΩ Ω))
        (ValuesOn Y (swigΩ Ω)) :=
    ((xMarginal.comap Prod.fst measurable_fst) ⊗ₖ
      (yCondXZ.comap
        (fun q : ((M.fixSet X hX_obs hX_fixed).FixedValues × ValuesOn Z (swigΩ Ω)) ×
            ValuesOn (X.image SWIGNode.random) (swigΩ Ω) =>
          (q.1.1, q.2, q.1.2))
        (Measurable.prodMk
          (measurable_fst.comp measurable_fst)
          (Measurable.prodMk measurable_snd
            (measurable_snd.comp measurable_fst))))).map Prod.snd
  -- Outer mediator integration `∫_z innerY(·, z) dP(Z | X = x_do)`.
  exact (zCondXdo ⊗ₖ innerY).map Prod.snd

/-- The frontdoor-adjustment functional is a finite kernel (nested `compProd`s of finite
    kernels, pushed through `Prod.snd`). -/
instance instIsFiniteKernelFrontdoorAdjustment (M : Causalean.SCM N Ω) (X : Finset N)
    (hX_obs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hX_fixed : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (Y Z : Finset (SWIGNode N)) (hY : Y ⊆ M.observed) (hZ : Z ⊆ M.observed) :
    ProbabilityTheory.IsFiniteKernel (M.frontdoorAdjustment X hX_obs hX_fixed Y Z hY hZ) := by
  rw [SCM.frontdoorAdjustment]; infer_instance

/-- **Cross-SCM invariance of `backdoorAdjustment`.**

    Two SCMs `M₁`, `M₂` sharing the same SWIG graph and the same
    observational kernel produce equal backdoor-adjustment kernels.  The
    underlying construction depends only on `M.toSWIGGraph` (for the
    type indices `M.fixed`, `M.observed`, `M.fixSet X _ _`) and on
    `M.obsKernel` (for the integrand and integrator measures).

    The conclusion is a `HEq` because the kernel target type
    `(M.fixSet X _ _).FixedValues` reduces to `ValuesOn (M.fixSet X _ _).fixed _`
    and the latter depends on `M.fixed`; with `M₁.toSWIGGraph = M₂.toSWIGGraph`
    we have `(M₁.fixSet X _ _).fixed = (M₂.fixSet X _ _).fixed` propositionally
    but not necessarily definitionally, hence `HEq`.

    Strategy: destructure both SCMs (to expose the SWIGGraph projection as
    a structural field), case-split on `h_swig` to align the SWIG-graph
    indices, then `congr 1` reduces the HEq goal to an `obsKernel`-equality
    subgoal that is exactly `_h_obs` (mod the HEq/Eq distinction). -/
theorem backdoorAdjustment_invariant
    (M₁ M₂ : Causalean.SCM N Ω)
    (h_swig : M₁.toSWIGGraph = M₂.toSWIGGraph)
    (_h_obs : HEq M₁.obsKernel M₂.obsKernel)
    (X : Finset N)
    (hX_obs₁ : ∀ D ∈ X, SWIGNode.random D ∈ M₁.observed)
    (hX_fixed₁ : ∀ D ∈ X, SWIGNode.fixed D ∉ M₁.fixed)
    (hX_obs₂ : ∀ D ∈ X, SWIGNode.random D ∈ M₂.observed)
    (hX_fixed₂ : ∀ D ∈ X, SWIGNode.fixed D ∉ M₂.fixed)
    (Y Z : Finset (SWIGNode N))
    (hY₁ : Y ⊆ M₁.observed) (hZ₁ : Z ⊆ M₁.observed)
    (hY₂ : Y ⊆ M₂.observed) (hZ₂ : Z ⊆ M₂.observed) :
    HEq (M₁.backdoorAdjustment X hX_obs₁ hX_fixed₁ Y Z hY₁ hZ₁)
        (M₂.backdoorAdjustment X hX_obs₂ hX_fixed₂ Y Z hY₂ hZ₂) := by
  -- Kernel-native transport: the remaining work is the HEq compatibility
  -- of `obsCondKernel` (via `heq_obsKernel`/`heq_obsCondKernel` from
  -- `EquivKernel.lean`) plus the `Kernel.comap`/`bind` reindexing along
  -- `fixSetProj` and `fillZrW`.
  obtain ⟨⟨dag₁, fixed₁, observed₁, unobserved₁,
           fio₁, oi₁, od₁, oou₁, foi₁, fou₁, aic₁, dc₁⟩,
         eT₁, iota₁, sf₁, mf₁, lD₁, pL₁⟩ := M₁
  obtain ⟨⟨dag₂, fixed₂, observed₂, unobserved₂,
           fio₂, oi₂, od₂, oou₂, foi₂, fou₂, aic₂, dc₂⟩,
         eT₂, iota₂, sf₂, mf₂, lD₂, pL₂⟩ := M₂
  cases h_swig
  apply heq_of_eq
  -- After `cases h_swig`, the SWIGGraph-level indices on both sides are unified
  -- (proofs `fio/oi/od/...` are Prop-valued, hence definitionally equal by
  -- proof irrelevance), while the non-SWIGGraph fields `eT/iota/sf/mf/lD/pL`
  -- still differ.  The `backdoorAdjustment` body uses only
  -- `toSWIGGraph`-derived data (`fixSetProj`, `fillZrW`, `FixedValues`,
  -- `observed`) plus `obsKernel` and `obsCondKernel`; the latter two agree
  -- via `_h_obs` and its derived `obsCondKernel` consequence.
  have h_ok : _ = _ := eq_of_heq _h_obs
  unfold SCM.backdoorAdjustment
  simp only
  -- Peel off `.map Prod.snd`.
  congr 1
  -- Peel off `⊗ₖ` into zMarginalPost and condPost equalities.
  congr 1
  · -- zMarginalPost equality: `(obsKernel.map (valuesProjection hZ)).comap fixSetProj`
    -- Only uses `obsKernel` (pointed from `h_ok`) and SWIG-level projections.
    congr 1
    · rw [h_ok]
  · -- condPost equality: `(obsCondKernel Y CC hY hXZ).comap (fixSetProj, fillZrW)`
    -- Uses `obsCondKernel` (unfolds to `(obsKernel.map _).condKernel`).
    congr 1
    unfold SCM.obsCondKernel SCM.obsCondPairKernel
    congr 1
    rw [h_ok]

/-- **Cross-SCM invariance of `frontdoorAdjustment`.**

    The frontdoor-adjustment functional depends only on the SWIG graph and the
    observational kernel.  Consequently, two SCMs sharing those data produce
    heterogeneously equal frontdoor-adjustment kernels, even though the fixed-
    and observed-value types are indexed by the individual models. -/
theorem frontdoorAdjustment_invariant
    (M₁ M₂ : Causalean.SCM N Ω)
    (h_swig : M₁.toSWIGGraph = M₂.toSWIGGraph)
    (_h_obs : HEq M₁.obsKernel M₂.obsKernel)
    (X : Finset N)
    (hX_obs₁ : ∀ D ∈ X, SWIGNode.random D ∈ M₁.observed)
    (hX_fixed₁ : ∀ D ∈ X, SWIGNode.fixed D ∉ M₁.fixed)
    (hX_obs₂ : ∀ D ∈ X, SWIGNode.random D ∈ M₂.observed)
    (hX_fixed₂ : ∀ D ∈ X, SWIGNode.fixed D ∉ M₂.fixed)
    (Y Z : Finset (SWIGNode N))
    (hY₁ : Y ⊆ M₁.observed) (hZ₁ : Z ⊆ M₁.observed)
    (hY₂ : Y ⊆ M₂.observed) (hZ₂ : Z ⊆ M₂.observed) :
    HEq (M₁.frontdoorAdjustment X hX_obs₁ hX_fixed₁ Y Z hY₁ hZ₁)
        (M₂.frontdoorAdjustment X hX_obs₂ hX_fixed₂ Y Z hY₂ hZ₂) := by
  -- Mirror the `backdoorAdjustment_invariant` strategy: destructure both
  -- SCMs, `cases h_swig` to align SWIGGraph indices, then `congr` through
  -- the `⊗ₖ` / `.map` / `.comap` plumbing.  Every leg uses only
  -- `M.obsKernel` (transported via `_h_obs`) plus SWIGGraph-derived
  -- projections.
  obtain ⟨⟨dag₁, fixed₁, observed₁, unobserved₁,
           fio₁, oi₁, od₁, oou₁, foi₁, fou₁, aic₁, dc₁, foff₁, aco₁⟩,
         eT₁, iota₁, sf₁, mf₁, lD₁, pL₁⟩ := M₁
  obtain ⟨⟨dag₂, fixed₂, observed₂, unobserved₂,
           fio₂, oi₂, od₂, oou₂, foi₂, fou₂, aic₂, dc₂, foff₂, aco₂⟩,
         eT₂, iota₂, sf₂, mf₂, lD₂, pL₂⟩ := M₂
  cases h_swig
  apply heq_of_eq
  have h_ok : _ = _ := eq_of_heq _h_obs
  unfold SCM.frontdoorAdjustment
  simp only
  -- The body is `((xMarginal ⊗ₖ zCondX) ⊗ₖ yCondXZ.comap …).map Prod.snd`.
  -- Each leg either uses `obsKernel` directly (xMarginal) or `obsCondKernel`
  -- (zCondX, yCondXZ).  Unfolding `obsCondKernel` exposes the joint
  -- `obsKernel.map (·, ·)` whose `condKernel` is taken.  All legs reduce
  -- to a single `obsKernel` argument that we rewrite via `h_ok`.
  unfold SCM.obsCondKernel SCM.obsCondPairKernel
  simp_rw [h_ok]
  -- After `simp_rw [h_ok]` the obsKernel mentions are unified.  The
  -- remaining record-identity differences in `fixSetProj` etc. are
  -- proof-irrelevance noise (only SWIGGraph fields are used, all unified
  -- after `cases h_swig`); `rfl` closes the goal.
  rfl

end SCM

end Causalean
