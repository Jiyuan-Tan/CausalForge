/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Rule 2 — Z-level-set joint kernel agreement

`obsKernel_inter_singleton_Zrand_eq`: for any measurable S and any w,
the measures of `S ∩ π_{Z.rand∪W}⁻¹{fillZrW w}` under M2.obsKernel and
M1.obsKernel agree.  Core of the hC1 step in the main theorem.
-/

import Causalean.SCM.Do.Rule2Kernel.LevelsetCompat
import Causalean.SCM.Do.ObsMarkov
import Causalean.SCM.ID.Overlap

/-! # Level-Set Agreement for Rule 2

This file proves that, on the event where the treatment and adjustment
coordinates take the fixed value inserted by the intervention, the
post-intervention observational kernel and the original observational kernel
assign the same mass to every additional measurable observed event.  This
level-set identity is the cross-model cylinder equality used in the
disintegration argument for Rule 2. -/

namespace Causalean

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

namespace SCM

open scoped MeasureTheory ProbabilityTheory

-- ============================================================
-- § Rule 2 — Z-level-set joint kernel agreement (core of hC1)
-- ============================================================

/-- **Joint kernel agreement on the Z.random-level-set event.**

    For any measurable `S ⊆ ObservedValues` and for the specific point
    `c := fillZrW s' w` in `ValuesOn (Z.random ∪ W)`, the measures of
    `S ∩ π_{Z.random ∪ W}⁻¹ {c}` under `M2.obsKernel s'` and
    `M1.obsKernel (fixSetProj s')` agree.

    Mechanism (no d-sep needed): restricting to the event
    `π_{Z.random ∪ W} = c` forces the underlying latent `ℓ` onto the
    Z-level set (M1.evalMap at `.random D = z_D` for D ∈ Z, equivalently
    M2.evalMap at `.random D = z_D` by Claims A/B); on this set,
    `fixSet_evalMap_levelset_compat` and `fixSet_evalMap_levelset_compat_M2`
    show `M2.evalMap s' ℓ` and `M1.evalMap s_M1 (cast ℓ)` coincide at all
    observed coordinates; `fixSet_latentProduct_compat` then equates the
    two latent-product measures through the `valuesProjection` cast.

    Consumed by the Rule 2 kernel bridge as the cross-SCM cylinder identity
    that, together with `Rule2JointOverlap`, drives the disintegration-uniqueness
    argument for the discrete-treatment route and the product-a.e. witness
    theorem. -/
theorem obsKernel_inter_singleton_Zrand_eq
    (M' : Causalean.SCM N Ω) (Z : Finset N)
    (hZ_obs : ∀ D ∈ Z, SWIGNode.random D ∈ M'.observed)
    (hZ_fixed : ∀ D ∈ Z, SWIGNode.fixed D ∉ M'.fixed)
    (W : Finset (SWIGNode N))
    (hZrW : Z.image SWIGNode.random ∪ W ⊆ M'.observed)
    (hDisj_ZrW : Disjoint (Z.image SWIGNode.random) W)
    [MeasurableSingletonClass
      (ValuesOn (Z.image SWIGNode.random ∪ W) (swigΩ Ω))]
    (s' : (M'.fixSet Z hZ_obs hZ_fixed).FixedValues)
    (w : ValuesOn W (swigΩ Ω))
    {S : Set M'.ObservedValues}
    (hS : MeasurableSet S) :
    (M'.fixSet Z hZ_obs hZ_fixed).obsKernel s'
        (S ∩ (valuesProjection
              ((fixSet_observed M' Z hZ_obs hZ_fixed).symm
                ▸ hZrW))⁻¹'
            {M'.fillZrW Z hZ_obs hZ_fixed W s' w})
      = M'.obsKernel
          (M'.fixSetProj Z hZ_obs hZ_fixed s')
          (S ∩ (valuesProjection hZrW)⁻¹'
               {M'.fillZrW Z hZ_obs hZ_fixed W s' w}) := by
  classical
  -- Abbreviations (via `let`; avoid `set` to prevent elaboration surprises).
  let M1 := M'
  let M2 := M1.fixSet Z hZ_obs hZ_fixed
  -- Use the explicit `.symm ▸` cast so the form matches the goal.
  have hZrW_M2 : Z.image SWIGNode.random ∪ W ⊆ M2.observed :=
    (fixSet_observed M1 Z hZ_obs hZ_fixed).symm ▸ hZrW
  let s_M1 : M1.FixedValues := M1.fixSetProj Z hZ_obs hZ_fixed s'
  let c := M'.fillZrW Z hZ_obs hZ_fixed W s' w
  -- Measurability bookkeeping.
  have h_sing : MeasurableSet ({c} : Set _) := measurableSet_singleton _
  have hπ_M1 : Measurable (valuesProjection hZrW : M1.ObservedValues → _) :=
    measurable_valuesProjection _
  have hπ_M2 : Measurable (valuesProjection hZrW_M2 : M2.ObservedValues → _) :=
    measurable_valuesProjection _
  have h_pre_M1 : MeasurableSet ((valuesProjection hZrW)⁻¹' {c}) := hπ_M1 h_sing
  have h_pre_M2 : MeasurableSet ((valuesProjection hZrW_M2)⁻¹' {c}) := hπ_M2 h_sing
  have hI_M1 : MeasurableSet (S ∩ (valuesProjection hZrW)⁻¹' {c}) :=
    hS.inter h_pre_M1
  have hI_M2 : MeasurableSet (S ∩ (valuesProjection hZrW_M2)⁻¹' {c}) :=
    hS.inter h_pre_M2
  have hRTO_M2 : Measurable M2.randomToObserved := M2.measurable_randomToObserved
  have hRTO_M1 : Measurable M1.randomToObserved := M1.measurable_randomToObserved
  have hf_M1 : Measurable (fun ℓ : M1.LatentValues => M1.evalMap s_M1 ℓ) :=
    M1.evalMap_measurable.comp (Measurable.prodMk measurable_const measurable_id)
  have hf_M2 : Measurable (fun ℓ : M2.LatentValues => M2.evalMap s' ℓ) :=
    M2.evalMap_measurable.comp (Measurable.prodMk measurable_const measurable_id)
  have hcast : Measurable (valuesProjection
      (le_of_eq (fixSet_unobserved M1 Z hZ_obs hZ_fixed).symm)
      : M2.LatentValues → M1.LatentValues) :=
    measurable_valuesProjection _
  -- LHS: unfold obsKernel → jointKernel → latentProduct.map evalMap.
  unfold obsKernel
  rw [ProbabilityTheory.Kernel.map_apply _
        ((M'.fixSet Z hZ_obs hZ_fixed).measurable_randomToObserved),
      ProbabilityTheory.Kernel.map_apply _ M'.measurable_randomToObserved]
  have hI_M2_exp : MeasurableSet
      (S ∩ (valuesProjection
        ((fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hZrW))⁻¹'
          {M'.fillZrW Z hZ_obs hZ_fixed W s' w}) := by
    exact hS.inter ((measurable_valuesProjection _) (measurableSet_singleton _))
  have hI_M1_exp : MeasurableSet
      (S ∩ (valuesProjection hZrW)⁻¹'
          {M'.fillZrW Z hZ_obs hZ_fixed W s' w}) := by
    exact hS.inter ((measurable_valuesProjection _) (measurableSet_singleton _))
  have hmap_M2 :
      (MeasureTheory.Measure.map (M'.fixSet Z hZ_obs hZ_fixed).randomToObserved
          ((M'.fixSet Z hZ_obs hZ_fixed).jointKernel s'))
        (S ∩ (valuesProjection
          ((fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hZrW))⁻¹'
            {M'.fillZrW Z hZ_obs hZ_fixed W s' w})
      = ((M'.fixSet Z hZ_obs hZ_fixed).jointKernel s')
        ((M'.fixSet Z hZ_obs hZ_fixed).randomToObserved ⁻¹'
          (S ∩ (valuesProjection
            ((fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hZrW))⁻¹'
              {M'.fillZrW Z hZ_obs hZ_fixed W s' w})) := by
    exact MeasureTheory.Measure.map_apply
      ((M'.fixSet Z hZ_obs hZ_fixed).measurable_randomToObserved) hI_M2_exp
  have hmap_M1 :
      (MeasureTheory.Measure.map M'.randomToObserved
          (M'.jointKernel (M'.fixSetProj Z hZ_obs hZ_fixed s')))
        (S ∩ (valuesProjection hZrW)⁻¹'
            {M'.fillZrW Z hZ_obs hZ_fixed W s' w})
      = (M'.jointKernel (M'.fixSetProj Z hZ_obs hZ_fixed s'))
        (M'.randomToObserved ⁻¹'
          (S ∩ (valuesProjection hZrW)⁻¹'
            {M'.fillZrW Z hZ_obs hZ_fixed W s' w})) := by
    exact MeasureTheory.Measure.map_apply M'.measurable_randomToObserved hI_M1_exp
  rw [hmap_M2, hmap_M1,
      jointKernel_apply_eq (M'.fixSet Z hZ_obs hZ_fixed) s',
      jointKernel_apply_eq M' (M'.fixSetProj Z hZ_obs hZ_fixed s')]
  have hf_M2_exp : Measurable
      (fun ℓ : (M'.fixSet Z hZ_obs hZ_fixed).LatentValues =>
        (M'.fixSet Z hZ_obs hZ_fixed).evalMap s' ℓ) := by
    exact (M'.fixSet Z hZ_obs hZ_fixed).evalMap_measurable.comp
      (Measurable.prodMk measurable_const measurable_id)
  have hf_M1_exp : Measurable
      (fun ℓ : M'.LatentValues =>
        M'.evalMap (M'.fixSetProj Z hZ_obs hZ_fixed s') ℓ) := by
    exact M'.evalMap_measurable.comp (Measurable.prodMk measurable_const measurable_id)
  have hpre_M2 : MeasurableSet
      ((M'.fixSet Z hZ_obs hZ_fixed).randomToObserved ⁻¹'
        (S ∩ (valuesProjection
          ((fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hZrW))⁻¹'
            {M'.fillZrW Z hZ_obs hZ_fixed W s' w})) :=
    (M'.fixSet Z hZ_obs hZ_fixed).measurable_randomToObserved hI_M2_exp
  have hpre_M1 : MeasurableSet
      (M'.randomToObserved ⁻¹'
        (S ∩ (valuesProjection hZrW)⁻¹'
          {M'.fillZrW Z hZ_obs hZ_fixed W s' w})) :=
    M'.measurable_randomToObserved hI_M1_exp
  have heval_M2 :
      (MeasureTheory.Measure.map
          (fun ℓ : (M'.fixSet Z hZ_obs hZ_fixed).LatentValues =>
            (M'.fixSet Z hZ_obs hZ_fixed).evalMap s' ℓ)
          (M'.fixSet Z hZ_obs hZ_fixed).latentProduct)
        ((M'.fixSet Z hZ_obs hZ_fixed).randomToObserved ⁻¹'
          (S ∩ (valuesProjection
            ((fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hZrW))⁻¹'
              {M'.fillZrW Z hZ_obs hZ_fixed W s' w}))
      = (M'.fixSet Z hZ_obs hZ_fixed).latentProduct
        ((fun ℓ : (M'.fixSet Z hZ_obs hZ_fixed).LatentValues =>
          (M'.fixSet Z hZ_obs hZ_fixed).evalMap s' ℓ) ⁻¹'
          ((M'.fixSet Z hZ_obs hZ_fixed).randomToObserved ⁻¹'
            (S ∩ (valuesProjection
              ((fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hZrW))⁻¹'
                {M'.fillZrW Z hZ_obs hZ_fixed W s' w}))) := by
    exact MeasureTheory.Measure.map_apply hf_M2_exp hpre_M2
  have heval_M1 :
      (MeasureTheory.Measure.map
          (fun ℓ : M'.LatentValues =>
            M'.evalMap (M'.fixSetProj Z hZ_obs hZ_fixed s') ℓ)
          M'.latentProduct)
        (M'.randomToObserved ⁻¹'
          (S ∩ (valuesProjection hZrW)⁻¹'
            {M'.fillZrW Z hZ_obs hZ_fixed W s' w}))
      = M'.latentProduct
        ((fun ℓ : M'.LatentValues =>
          M'.evalMap (M'.fixSetProj Z hZ_obs hZ_fixed s') ℓ) ⁻¹'
          (M'.randomToObserved ⁻¹'
            (S ∩ (valuesProjection hZrW)⁻¹'
              {M'.fillZrW Z hZ_obs hZ_fixed W s' w}))) := by
    exact MeasureTheory.Measure.map_apply hf_M1_exp hpre_M1
  rw [heval_M2, heval_M1,
      ← fixSet_latentProduct_compat M' Z hZ_obs hZ_fixed,
      MeasureTheory.Measure.map_apply (measurable_valuesProjection _)
        (hf_M1_exp hpre_M1)]
  -- Goal: M2.latentProduct {ℓ : rando(M2.evalMap s' ℓ) ∈ I} = M2.latentProduct {ℓ : ...}.
  -- Reduce to set equality on the same M2.latentProduct.
  congr 1
  -- Two preimage sets (in M2.LatentValues):
  --   L2 := {ℓ : rando(M2.evalMap s' ℓ) ∈ S ∩ π_C⁻¹{c}}
  --   L1 := {ℓ : cast ℓ ∈ {ℓ_M1 : rando(M1.evalMap s_M1 ℓ_M1) ∈ S ∩ π_C⁻¹{c}}}
  --      = {ℓ : rando(M1.evalMap s_M1 (cast ℓ)) ∈ S ∩ π_C⁻¹{c}}
  apply Set.eq_of_subset_of_subset
  all_goals
    intro ℓ hℓ
    simp only [Set.mem_preimage, Set.mem_inter_iff] at hℓ ⊢
  -- Both directions use the same core mechanism: on the preimage, one side's
  -- evalMap is on the Z-level set; bridge via Claim A/B to get pointwise
  -- agreement of rando(evalMap) at every observed, hence the other side
  -- inherits membership.
  · -- ⊆: LHS (M2-side) ⊆ RHS (M1-side via cast).
    rcases hℓ with ⟨hS_mem, hπ_mem⟩
    -- Extract LS_M2 from π_C = c.
    have hLS_M2 : ∀ D (hD : D ∈ Z),
        M2.evalMap s' ℓ ⟨SWIGNode.random D,
            Finset.mem_union_left _ (hZ_obs D hD)⟩
          = s' ⟨SWIGNode.fixed D,
              SCM.fixed_mem_fixSet M1 Z hZ_obs hZ_fixed hD⟩ := by
      intro D hD
      -- π_C(rando(M2.evalMap s' ℓ)) = c at ⟨.random D, _⟩.
      have hD_in : SWIGNode.random D ∈ Z.image SWIGNode.random ∪ W :=
        Finset.mem_union_left _ (Finset.mem_image.mpr ⟨D, hD, rfl⟩)
      have hcoord := congrFun hπ_mem ⟨SWIGNode.random D, hD_in⟩
      have hc_at : c ⟨SWIGNode.random D, hD_in⟩ =
          s' ⟨SWIGNode.fixed D,
              SCM.fixed_mem_fixSet M1 Z hZ_obs hZ_fixed hD⟩ := by
        show (valuesUnionMk (zFixedAsRandom
              (valuesProjection
                (fixSet_image_fixed_subset M' Z hZ_obs hZ_fixed) s')) w)
              ⟨SWIGNode.random D, hD_in⟩
            = s' ⟨SWIGNode.fixed D,
                SCM.fixed_mem_fixSet M1 Z hZ_obs hZ_fixed hD⟩
        rw [valuesUnionMk_apply_left _ _ _
              (Finset.mem_image.mpr ⟨D, hD, rfl⟩)]
        rfl
      exact hcoord.trans hc_at
    -- Apply the M2-direction level-set bridge at each observed v.
    refine ⟨?_, ?_⟩
    · -- S membership: rando(M1.evalMap s_M1 (cast ℓ)) ∈ S.
      have heq : M1.randomToObserved
                  (M1.evalMap s_M1 (valuesProjection
                    (le_of_eq (fixSet_unobserved M1 Z hZ_obs hZ_fixed).symm) ℓ))
               = M2.randomToObserved (M2.evalMap s' ℓ) := by
        funext v
        simp only [randomToObserved]
        exact (fixSet_evalMap_levelset_compat_M2 M' Z hZ_obs hZ_fixed
                 s' ℓ hLS_M2 v.property).symm
      rw [heq]
      exact hS_mem
    · -- π_C membership: preserved under the same pointwise equality.
      have heq : M1.randomToObserved
                  (M1.evalMap s_M1 (valuesProjection
                    (le_of_eq (fixSet_unobserved M1 Z hZ_obs hZ_fixed).symm) ℓ))
               = M2.randomToObserved (M2.evalMap s' ℓ) := by
        funext v
        simp only [randomToObserved]
        exact (fixSet_evalMap_levelset_compat_M2 M' Z hZ_obs hZ_fixed
                 s' ℓ hLS_M2 v.property).symm
      rw [heq]
      exact hπ_mem
  · -- ⊇: RHS (M1-side via cast) ⊆ LHS (M2-side).
    rcases hℓ with ⟨hS_mem, hπ_mem⟩
    -- Extract LS_M1(cast ℓ) from π_C = c.
    have hLS_M1 : ∀ D (hD : D ∈ Z),
        M1.evalMap s_M1 (valuesProjection
            (le_of_eq (fixSet_unobserved M1 Z hZ_obs hZ_fixed).symm) ℓ)
          ⟨SWIGNode.random D, Finset.mem_union_left _ (hZ_obs D hD)⟩
          = s' ⟨SWIGNode.fixed D,
              SCM.fixed_mem_fixSet M1 Z hZ_obs hZ_fixed hD⟩ := by
      intro D hD
      have hD_in : SWIGNode.random D ∈ Z.image SWIGNode.random ∪ W :=
        Finset.mem_union_left _ (Finset.mem_image.mpr ⟨D, hD, rfl⟩)
      have hcoord := congrFun hπ_mem ⟨SWIGNode.random D, hD_in⟩
      have hc_at : c ⟨SWIGNode.random D, hD_in⟩ =
          s' ⟨SWIGNode.fixed D,
              SCM.fixed_mem_fixSet M1 Z hZ_obs hZ_fixed hD⟩ := by
        show (valuesUnionMk (zFixedAsRandom
              (valuesProjection
                (fixSet_image_fixed_subset M' Z hZ_obs hZ_fixed) s')) w)
              ⟨SWIGNode.random D, hD_in⟩
            = s' ⟨SWIGNode.fixed D,
                SCM.fixed_mem_fixSet M1 Z hZ_obs hZ_fixed hD⟩
        rw [valuesUnionMk_apply_left _ _ _
              (Finset.mem_image.mpr ⟨D, hD, rfl⟩)]
        rfl
      exact hcoord.trans hc_at
    refine ⟨?_, ?_⟩
    · have heq : M2.randomToObserved (M2.evalMap s' ℓ)
               = M1.randomToObserved
                  (M1.evalMap s_M1 (valuesProjection
                    (le_of_eq (fixSet_unobserved M1 Z hZ_obs hZ_fixed).symm) ℓ)) := by
        funext v
        simp only [randomToObserved]
        exact fixSet_evalMap_levelset_compat M' Z hZ_obs hZ_fixed
                 s' _ hLS_M1 v.property
      rw [heq]
      exact hS_mem
    · have heq : M2.randomToObserved (M2.evalMap s' ℓ)
               = M1.randomToObserved
                  (M1.evalMap s_M1 (valuesProjection
                    (le_of_eq (fixSet_unobserved M1 Z hZ_obs hZ_fixed).symm) ℓ)) := by
        funext v
        simp only [randomToObserved]
        exact fixSet_evalMap_levelset_compat M' Z hZ_obs hZ_fixed
                 s' _ hLS_M1 v.property
      rw [heq]
      exact hπ_mem

-- ============================================================
-- § Rule 2 — rectangle identity helpers
-- ============================================================

/-- Generalized cross-SCM cylinder agreement.

    Generalization of `obsKernel_inter_singleton_Zrand_eq` from a single
    level-set point `{fillZrW w₀}` to an arbitrary measurable `W`-set
    cylinder.

    For measurable `S ⊆ M'.ObservedValues` and measurable
    `A ⊆ ValuesOn W (swigΩ Ω)`, the M2 and M1 measures agree on the
    intersection
    ```
    S ∩ π_W⁻¹ A ∩ π_Zr⁻¹ {ζ_s}
    ```
    where `ζ_s := zFixedAsRandom (valuesProjection s')` is the constant
    `Z.image .random`-tuple read off from the intervention values in `s'`.
    Equivalently, the M2 and M1 measures agree on `S ∩ π_C⁻¹ (fillZrW '' A)`.

    **Why this works.** The proof is structurally identical to
    `obsKernel_inter_singleton_Zrand_eq`: the level-set extraction at each
    `.random D` (D ∈ Z) only consumes the `π_Zr ω = ζ_s` half of the
    cylinder, leaving the `π_W ω ∈ A` half free. Read line-for-line, the
    only change is to weaken `π_C ω = fillZrW w₀` to `π_W ω ∈ A` ∧
    `π_Zr ω = ζ_s`; the cross-SCM `LevelsetCompat` step still applies
    pointwise on the Z-level set of latents.

    Used by `obsKernel_fixSet_W_rect_integral_eq` as the integrated cross-SCM
    bridge that swaps M2 ↔ M1 on level-set cylinders. -/
theorem obsKernel_inter_Wset_Zrand_levelset_eq
    (M' : Causalean.SCM N Ω) (Z : Finset N)
    (hZ_obs : ∀ D ∈ Z, SWIGNode.random D ∈ M'.observed)
    (hZ_fixed : ∀ D ∈ Z, SWIGNode.fixed D ∉ M'.fixed)
    (W : Finset (SWIGNode N))
    (hZrW : Z.image SWIGNode.random ∪ W ⊆ M'.observed)
    (hDisj_ZrW : Disjoint (Z.image SWIGNode.random) W)
    [MeasurableSingletonClass
      (ValuesOn (Z.image SWIGNode.random ∪ W) (swigΩ Ω))]
    (s' : (M'.fixSet Z hZ_obs hZ_fixed).FixedValues)
    {S : Set M'.ObservedValues} {A : Set (ValuesOn W (swigΩ Ω))}
    (hS : MeasurableSet S) (hA : MeasurableSet A) :
    (M'.fixSet Z hZ_obs hZ_fixed).obsKernel s'
        (S ∩ (valuesProjection
              ((fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hZrW))⁻¹'
            ((M'.fillZrW Z hZ_obs hZ_fixed W s') '' A))
      = M'.obsKernel
          (M'.fixSetProj Z hZ_obs hZ_fixed s')
          (S ∩ (valuesProjection hZrW)⁻¹'
               ((M'.fillZrW Z hZ_obs hZ_fixed W s') '' A)) := by
  classical
  -- Abbreviations.
  let M1 := M'
  let M2 := M1.fixSet Z hZ_obs hZ_fixed
  have hZrW_M2 : Z.image SWIGNode.random ∪ W ⊆ M2.observed :=
    (fixSet_observed M1 Z hZ_obs hZ_fixed).symm ▸ hZrW
  let s_M1 : M1.FixedValues := M1.fixSetProj Z hZ_obs hZ_fixed s'
  let F := M'.fillZrW Z hZ_obs hZ_fixed W s'
  -- Measurability bookkeeping for the image preimage.
  have hF_meas : Measurable F :=
    M'.measurable_fillZrW Z hZ_obs hZ_fixed W s'
  -- The image `F '' A` has the explicit form
  --     `{c | π_W^C c ∈ A ∧ π_Zr^C c = ζ_s}`
  -- which is measurable.  Use this to deduce the cylinder
  -- `π_C⁻¹ (F '' A)` is measurable.
  have hπ_M1 : Measurable (valuesProjection hZrW : M1.ObservedValues → _) :=
    measurable_valuesProjection _
  have hπ_M2 : Measurable (valuesProjection hZrW_M2 : M2.ObservedValues → _) :=
    measurable_valuesProjection _
  -- Helper: the Zr-singleton `{ζ_s}` is measurable in
  -- `ValuesOn (Z.image .random) (swigΩ Ω)` provided we have a witness
  -- `w₀ : ValuesOn W (swigΩ Ω)`.  We isolate this as a parameterized lemma.
  -- The proof: pull back the measurable singleton
  -- `{valuesUnionMk ζ_s w₀} ⊆ ValuesOn (Zr ∪ W) (swigΩ Ω)` (which is
  -- measurable by the MSC hypothesis) under the measurable embedding
  -- `ζ ↦ valuesUnionMk ζ w₀`.
  let ζ_s : ValuesOn (Z.image SWIGNode.random) (swigΩ Ω) :=
    zFixedAsRandom
      (valuesProjection (fixSet_image_fixed_subset M' Z hZ_obs hZ_fixed) s')
  have hSingZr : ∀ (w₀ : ValuesOn W (swigΩ Ω)),
      MeasurableSet ({ζ_s} : Set (ValuesOn (Z.image SWIGNode.random) (swigΩ Ω))) := by
    intro w₀
    have hmeas : Measurable
        (fun ζ : ValuesOn (Z.image SWIGNode.random) (swigΩ Ω) =>
          valuesUnionMk ζ w₀) := by
      refine measurable_pi_iff.mpr ?_
      rintro ⟨v, hv⟩
      by_cases hvZ : v ∈ Z.image SWIGNode.random
      · have h_eq : (fun ζ : ValuesOn (Z.image SWIGNode.random) (swigΩ Ω) =>
            valuesUnionMk ζ w₀ ⟨v, hv⟩) = (fun ζ => ζ ⟨v, hvZ⟩) :=
          funext fun _ => valuesUnionMk_apply_left _ _ hv hvZ
        rw [h_eq]
        exact measurable_pi_apply _
      · have hvW : v ∈ W := (Finset.mem_union.mp hv).resolve_left hvZ
        have h_eq : (fun ζ : ValuesOn (Z.image SWIGNode.random) (swigΩ Ω) =>
            valuesUnionMk ζ w₀ ⟨v, hv⟩) = (fun _ => w₀ ⟨v, hvW⟩) :=
          funext fun _ => valuesUnionMk_apply_right _ _ hv hvZ
        rw [h_eq]
        exact measurable_const
    have h_pre : ({ζ_s} : Set (ValuesOn (Z.image SWIGNode.random) (swigΩ Ω))) =
        (fun ζ => valuesUnionMk ζ w₀)⁻¹' ({valuesUnionMk ζ_s w₀} :
          Set (ValuesOn (Z.image SWIGNode.random ∪ W) (swigΩ Ω))) := by
      ext ζ
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      refine ⟨fun h => by rw [h], fun h => ?_⟩
      funext ⟨v, hv⟩
      have hv_union : v ∈ Z.image SWIGNode.random ∪ W :=
        Finset.subset_union_left hv
      have h_coord := congrFun h ⟨v, hv_union⟩
      rw [valuesUnionMk_apply_left _ _ hv_union hv,
          valuesUnionMk_apply_left _ _ hv_union hv] at h_coord
      exact h_coord
    rw [h_pre]
    exact hmeas (measurableSet_singleton _)
  -- Helper: prove `MeasurableSet ((valuesProjection h)⁻¹' (F '' A))` via the
  -- `hImg` decomposition.  The proof is identical for `h = hZrW` (M1 side)
  -- and `h = hZrW_M2` (M2 side); we factor it.
  have hPreImage_meas_gen :
      ∀ {O : Finset (SWIGNode N)} (h : Z.image SWIGNode.random ∪ W ⊆ O)
        (hπ : Measurable
          (valuesProjection h : ValuesOn O (swigΩ Ω) → _)),
        MeasurableSet ((valuesProjection h)⁻¹' (F '' A)) := by
    intro O h hπ
    by_cases hW : Nonempty (ValuesOn W (swigΩ Ω))
    · obtain ⟨w₀⟩ := hW
      have hImg : (F '' A : Set _) =
          (fun c : ValuesOn (Z.image SWIGNode.random ∪ W) (swigΩ Ω) =>
              valuesProjection
                (Finset.subset_union_right (s₁ := Z.image SWIGNode.random)) c)⁻¹' A ∩
          (fun c => valuesProjection
                (Finset.subset_union_left (s₂ := W)) c)⁻¹'
            ({ζ_s} :
              Set (ValuesOn (Z.image SWIGNode.random) (swigΩ Ω))) := by
        ext c
        constructor
        · rintro ⟨w, hwA, rfl⟩
          refine ⟨?_, ?_⟩
          · simp only [Set.mem_preimage]
            show valuesProjection (Finset.subset_union_right) (F w) ∈ A
            have : valuesProjection (Finset.subset_union_right : W ⊆ _) (F w) = w := by
              funext ⟨v, hv⟩
              simp only [valuesProjection, F, fillZrW]
              by_cases hvA : v ∈ Z.image SWIGNode.random
              · exfalso
                exact Finset.disjoint_left.mp hDisj_ZrW hvA hv
              · rw [valuesUnionMk_apply_right _ _ _ hvA hv]
            rw [this]
            exact hwA
          · simp only [Set.mem_preimage, Set.mem_singleton_iff]
            show valuesProjection (Finset.subset_union_left) (F w) = ζ_s
            funext ⟨v, hv⟩
            simp only [valuesProjection, F, fillZrW]
            rw [valuesUnionMk_apply_left _ _ _ hv]
        · rintro ⟨hW_mem, hZr_mem⟩
          simp only [Set.mem_preimage] at hW_mem
          simp only [Set.mem_preimage, Set.mem_singleton_iff] at hZr_mem
          refine ⟨valuesProjection (Finset.subset_union_right : W ⊆ _) c, hW_mem, ?_⟩
          funext ⟨v, hv⟩
          simp only [F, fillZrW]
          rcases Finset.mem_union.mp hv with hZrV | hWV
          · rw [valuesUnionMk_apply_left _ _ _ hZrV]
            have := congrFun hZr_mem ⟨v, hZrV⟩
            simp only [valuesProjection] at this
            exact this.symm
          · by_cases hZrV' : v ∈ Z.image SWIGNode.random
            · rw [valuesUnionMk_apply_left _ _ _ hZrV']
              have := congrFun hZr_mem ⟨v, hZrV'⟩
              simp only [valuesProjection] at this
              exact this.symm
            · rw [valuesUnionMk_apply_right _ _ _ hZrV' hWV]
              simp only [valuesProjection]
      rw [hImg, Set.preimage_inter]
      refine (hπ ((measurable_valuesProjection _) hA)).inter ?_
      exact hπ ((measurable_valuesProjection _) (hSingZr w₀))
    · -- `ValuesOn W` is empty.  Then `A : Set (ValuesOn W)` must be `∅`,
      -- hence `F '' A = ∅` and the preimage is empty (measurable).
      have hA_empty : A = ∅ := by
        ext w
        exact ⟨fun _ => (hW ⟨w⟩).elim, fun h => h.elim⟩
      rw [hA_empty, Set.image_empty, Set.preimage_empty]
      exact MeasurableSet.empty
  have hPreImage_meas_M1 : MeasurableSet ((valuesProjection hZrW)⁻¹' (F '' A)) :=
    hPreImage_meas_gen hZrW hπ_M1
  have hPreImage_meas_M2 : MeasurableSet ((valuesProjection hZrW_M2)⁻¹' (F '' A)) :=
    hPreImage_meas_gen hZrW_M2 hπ_M2
  -- LHS: unfold obsKernel → jointKernel → latentProduct.map evalMap.
  unfold obsKernel
  have hI_M2_exp : MeasurableSet
      (S ∩ (valuesProjection
        ((fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hZrW))⁻¹'
          ((M'.fillZrW Z hZ_obs hZ_fixed W s') '' A)) :=
    hS.inter hPreImage_meas_M2
  have hI_M1_exp : MeasurableSet
      (S ∩ (valuesProjection hZrW)⁻¹'
          ((M'.fillZrW Z hZ_obs hZ_fixed W s') '' A)) :=
    hS.inter hPreImage_meas_M1
  rw [ProbabilityTheory.Kernel.map_apply _
        ((M'.fixSet Z hZ_obs hZ_fixed).measurable_randomToObserved),
      ProbabilityTheory.Kernel.map_apply _ M'.measurable_randomToObserved]
  have hmap_M2 :
      (MeasureTheory.Measure.map (M'.fixSet Z hZ_obs hZ_fixed).randomToObserved
          ((M'.fixSet Z hZ_obs hZ_fixed).jointKernel s'))
        (S ∩ (valuesProjection
          ((fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hZrW))⁻¹'
            ((M'.fillZrW Z hZ_obs hZ_fixed W s') '' A))
      = ((M'.fixSet Z hZ_obs hZ_fixed).jointKernel s')
        ((M'.fixSet Z hZ_obs hZ_fixed).randomToObserved ⁻¹'
          (S ∩ (valuesProjection
            ((fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hZrW))⁻¹'
              ((M'.fillZrW Z hZ_obs hZ_fixed W s') '' A))) :=
    MeasureTheory.Measure.map_apply
      ((M'.fixSet Z hZ_obs hZ_fixed).measurable_randomToObserved) hI_M2_exp
  have hmap_M1 :
      (MeasureTheory.Measure.map M'.randomToObserved
          (M'.jointKernel (M'.fixSetProj Z hZ_obs hZ_fixed s')))
        (S ∩ (valuesProjection hZrW)⁻¹'
            ((M'.fillZrW Z hZ_obs hZ_fixed W s') '' A))
      = (M'.jointKernel (M'.fixSetProj Z hZ_obs hZ_fixed s'))
        (M'.randomToObserved ⁻¹'
          (S ∩ (valuesProjection hZrW)⁻¹'
            ((M'.fillZrW Z hZ_obs hZ_fixed W s') '' A))) :=
    MeasureTheory.Measure.map_apply M'.measurable_randomToObserved hI_M1_exp
  rw [hmap_M2, hmap_M1,
      jointKernel_apply_eq (M'.fixSet Z hZ_obs hZ_fixed) s',
      jointKernel_apply_eq M' (M'.fixSetProj Z hZ_obs hZ_fixed s')]
  have hf_M2_exp : Measurable
      (fun ℓ : (M'.fixSet Z hZ_obs hZ_fixed).LatentValues =>
        (M'.fixSet Z hZ_obs hZ_fixed).evalMap s' ℓ) :=
    (M'.fixSet Z hZ_obs hZ_fixed).evalMap_measurable.comp
      (Measurable.prodMk measurable_const measurable_id)
  have hf_M1_exp : Measurable
      (fun ℓ : M'.LatentValues =>
        M'.evalMap (M'.fixSetProj Z hZ_obs hZ_fixed s') ℓ) :=
    M'.evalMap_measurable.comp (Measurable.prodMk measurable_const measurable_id)
  have hRTO_2 : Measurable (M'.fixSet Z hZ_obs hZ_fixed).randomToObserved :=
    (M'.fixSet Z hZ_obs hZ_fixed).measurable_randomToObserved
  have hRTO_1 : Measurable M'.randomToObserved := M'.measurable_randomToObserved
  have hpre_M2 : MeasurableSet
      ((M'.fixSet Z hZ_obs hZ_fixed).randomToObserved ⁻¹'
        (S ∩ (valuesProjection
          ((fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hZrW))⁻¹'
            ((M'.fillZrW Z hZ_obs hZ_fixed W s') '' A))) :=
    hRTO_2 hI_M2_exp
  have hpre_M1 : MeasurableSet
      (M'.randomToObserved ⁻¹'
        (S ∩ (valuesProjection hZrW)⁻¹'
          ((M'.fillZrW Z hZ_obs hZ_fixed W s') '' A))) :=
    hRTO_1 hI_M1_exp
  rw [MeasureTheory.Measure.map_apply hf_M2_exp hpre_M2,
      MeasureTheory.Measure.map_apply hf_M1_exp hpre_M1,
      ← fixSet_latentProduct_compat M' Z hZ_obs hZ_fixed,
      MeasureTheory.Measure.map_apply (measurable_valuesProjection _)
        (hf_M1_exp hpre_M1)]
  -- Reduce to set equality on the same M2.latentProduct (now post-cast on RHS).
  congr 1
  apply Set.eq_of_subset_of_subset
  all_goals
    intro ℓ hℓ
    simp only [Set.mem_preimage, Set.mem_inter_iff] at hℓ ⊢
  · -- ⊆: LHS (M2-side) ⊆ RHS (M1-side via cast).
    rcases hℓ with ⟨hS_mem, hπ_mem⟩
    rcases hπ_mem with ⟨w₀, hw₀A, hF_eq⟩
    -- Extract LS_M2 from the cylinder constraint hF_eq: the M2-side
    -- projection at each `.random D` equals the Z-slice of `s'`.
    have hLS_M2 : ∀ D (hD : D ∈ Z),
        (M'.fixSet Z hZ_obs hZ_fixed).evalMap s' ℓ
            ⟨SWIGNode.random D,
              Finset.mem_union_left _ (hZ_obs D hD)⟩
          = s' ⟨SWIGNode.fixed D,
              SCM.fixed_mem_fixSet M1 Z hZ_obs hZ_fixed hD⟩ := by
      intro D hD
      have hD_in : SWIGNode.random D ∈ Z.image SWIGNode.random ∪ W :=
        Finset.mem_union_left _ (Finset.mem_image.mpr ⟨D, hD, rfl⟩)
      have hcoord := congrFun hF_eq ⟨SWIGNode.random D, hD_in⟩
      have hc_at : (M'.fillZrW Z hZ_obs hZ_fixed W s' w₀)
          ⟨SWIGNode.random D, hD_in⟩ =
          s' ⟨SWIGNode.fixed D,
              SCM.fixed_mem_fixSet M1 Z hZ_obs hZ_fixed hD⟩ := by
        show (valuesUnionMk (zFixedAsRandom
              (valuesProjection
                (fixSet_image_fixed_subset M' Z hZ_obs hZ_fixed) s')) w₀)
              ⟨SWIGNode.random D, hD_in⟩
            = s' ⟨SWIGNode.fixed D,
                SCM.fixed_mem_fixSet M1 Z hZ_obs hZ_fixed hD⟩
        rw [valuesUnionMk_apply_left _ _ hD_in
              (Finset.mem_image.mpr ⟨D, hD, rfl⟩)]
        rfl
      exact hcoord.symm.trans hc_at
    refine ⟨?_, ?_⟩
    · have heq : M1.randomToObserved
                  (M1.evalMap s_M1 (valuesProjection
                    (le_of_eq (fixSet_unobserved M1 Z hZ_obs hZ_fixed).symm) ℓ))
               = (M'.fixSet Z hZ_obs hZ_fixed).randomToObserved
                  ((M'.fixSet Z hZ_obs hZ_fixed).evalMap s' ℓ) := by
        funext v
        simp only [randomToObserved]
        exact (fixSet_evalMap_levelset_compat_M2 M' Z hZ_obs hZ_fixed
                 s' ℓ hLS_M2 v.property).symm
      rw [heq]
      exact hS_mem
    · refine ⟨w₀, hw₀A, ?_⟩
      have heq : M1.randomToObserved
                  (M1.evalMap s_M1 (valuesProjection
                    (le_of_eq (fixSet_unobserved M1 Z hZ_obs hZ_fixed).symm) ℓ))
               = (M'.fixSet Z hZ_obs hZ_fixed).randomToObserved
                  ((M'.fixSet Z hZ_obs hZ_fixed).evalMap s' ℓ) := by
        funext v
        simp only [randomToObserved]
        exact (fixSet_evalMap_levelset_compat_M2 M' Z hZ_obs hZ_fixed
                 s' ℓ hLS_M2 v.property).symm
      rw [heq]
      exact hF_eq
  · -- ⊇: RHS (M1-side via cast) ⊆ LHS (M2-side).
    rcases hℓ with ⟨hS_mem, hπ_mem⟩
    rcases hπ_mem with ⟨w₀, hw₀A, hF_eq⟩
    have hLS_M1 : ∀ D (hD : D ∈ Z),
        M1.evalMap s_M1 (valuesProjection
            (le_of_eq (fixSet_unobserved M1 Z hZ_obs hZ_fixed).symm) ℓ)
          ⟨SWIGNode.random D, Finset.mem_union_left _ (hZ_obs D hD)⟩
          = s' ⟨SWIGNode.fixed D,
              SCM.fixed_mem_fixSet M1 Z hZ_obs hZ_fixed hD⟩ := by
      intro D hD
      have hD_in : SWIGNode.random D ∈ Z.image SWIGNode.random ∪ W :=
        Finset.mem_union_left _ (Finset.mem_image.mpr ⟨D, hD, rfl⟩)
      have hcoord := congrFun hF_eq ⟨SWIGNode.random D, hD_in⟩
      have hc_at : (M'.fillZrW Z hZ_obs hZ_fixed W s' w₀)
          ⟨SWIGNode.random D, hD_in⟩ =
          s' ⟨SWIGNode.fixed D,
              SCM.fixed_mem_fixSet M1 Z hZ_obs hZ_fixed hD⟩ := by
        show (valuesUnionMk (zFixedAsRandom
              (valuesProjection
                (fixSet_image_fixed_subset M' Z hZ_obs hZ_fixed) s')) w₀)
              ⟨SWIGNode.random D, hD_in⟩
            = s' ⟨SWIGNode.fixed D,
                SCM.fixed_mem_fixSet M1 Z hZ_obs hZ_fixed hD⟩
        rw [valuesUnionMk_apply_left _ _ hD_in
              (Finset.mem_image.mpr ⟨D, hD, rfl⟩)]
        rfl
      exact hcoord.symm.trans hc_at
    refine ⟨?_, ?_⟩
    · have heq : (M'.fixSet Z hZ_obs hZ_fixed).randomToObserved
                  ((M'.fixSet Z hZ_obs hZ_fixed).evalMap s' ℓ)
               = M1.randomToObserved
                  (M1.evalMap s_M1 (valuesProjection
                    (le_of_eq (fixSet_unobserved M1 Z hZ_obs hZ_fixed).symm) ℓ)) := by
        funext v
        simp only [randomToObserved]
        exact fixSet_evalMap_levelset_compat M' Z hZ_obs hZ_fixed
                 s' _ hLS_M1 v.property
      rw [heq]
      exact hS_mem
    · refine ⟨w₀, hw₀A, ?_⟩
      have heq : (M'.fixSet Z hZ_obs hZ_fixed).randomToObserved
                  ((M'.fixSet Z hZ_obs hZ_fixed).evalMap s' ℓ)
               = M1.randomToObserved
                  (M1.evalMap s_M1 (valuesProjection
                    (le_of_eq (fixSet_unobserved M1 Z hZ_obs hZ_fixed).symm) ℓ)) := by
        funext v
        simp only [randomToObserved]
        exact fixSet_evalMap_levelset_compat M' Z hZ_obs hZ_fixed
                 s' _ hLS_M1 v.property
      rw [heq]
      exact hF_eq

/-- Base-model disintegration over condition coordinates.

    Standard disintegration applied to `M.obsCondPairKernel Y CC`: for
    measurable `D ⊆ ValuesOn CC` and `B ⊆ ValuesOn Y`,
    ```
    M.obsKernel s (π_CC⁻¹ D ∩ π_Y⁻¹ B)
      = ∫⁻ c in D, M.obsCondKernel Y CC (s, c) B
                   d((M.obsKernel s).map π_CC).
    ```

    **Proof.** `obsCondPairKernel` is the pushforward of `obsKernel`
    onto `(CC, Y)`, so its value on rectangles equals `obsKernel` on
    the corresponding cylinder.  Its `condKernel` is by definition
    `obsCondKernel Y CC`, and its `fst` equals `obsKernel.map π_CC`.
    `setLIntegral_condKernel_eq_measure_prod` from Mathlib then yields
    the displayed identity. -/
theorem obsKernel_disintegrate_rect
    (M : Causalean.SCM N Ω) (Y CC : Finset (SWIGNode N))
    (hY : Y ⊆ M.observed) (hCC : CC ⊆ M.observed)
    [StandardBorelSpace (ValuesOn Y (swigΩ Ω))]
    [Nonempty (ValuesOn Y (swigΩ Ω))]
    [∀ s : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.obsKernel s)]
    [MeasurableSpace.CountableOrCountablyGenerated
      M.FixedValues (ValuesOn CC (swigΩ Ω))]
    (s : M.FixedValues)
    {D : Set (ValuesOn CC (swigΩ Ω))} {B : Set (ValuesOn Y (swigΩ Ω))}
    (hD : MeasurableSet D) (hB : MeasurableSet B) :
    M.obsKernel s ((valuesProjection hCC)⁻¹' D ∩ (valuesProjection hY)⁻¹' B)
      = ∫⁻ c in D, M.obsCondKernel Y CC hY hCC (s, c) B
                    ∂((M.obsKernel s).map (valuesProjection hCC)) := by
  classical
  have hπCC : Measurable (valuesProjection (Ω := swigΩ Ω) hCC) :=
    measurable_valuesProjection _
  have hπY : Measurable (valuesProjection (Ω := swigΩ Ω) hY) :=
    measurable_valuesProjection _
  -- κ := obsCondPairKernel.
  set κ : ProbabilityTheory.Kernel M.FixedValues
        (ValuesOn CC (swigΩ Ω) × ValuesOn Y (swigΩ Ω)) :=
    M.obsCondPairKernel Y CC hY hCC with hκ_def
  haveI hMarkov_κ : ProbabilityTheory.IsMarkovKernel κ := by
    rw [hκ_def]
    unfold obsCondPairKernel
    exact ProbabilityTheory.Kernel.IsMarkovKernel.map _ (hπCC.prodMk hπY)
  haveI : ProbabilityTheory.IsFiniteKernel κ := inferInstance
  -- Step 1: κ s (D ×ˢ B) = obsKernel cylinder.
  have h_pre :
      (valuesProjection hCC)⁻¹' D ∩ (valuesProjection hY)⁻¹' B
        = (fun ω => (valuesProjection hCC ω, valuesProjection hY ω))⁻¹'
            (D ×ˢ B) := by
    ext ω; simp [Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod]
  have hKpair :
      κ s (D ×ˢ B)
        = M.obsKernel s ((valuesProjection hCC)⁻¹' D ∩ (valuesProjection hY)⁻¹' B) := by
    rw [hκ_def]; unfold obsCondPairKernel
    rw [ProbabilityTheory.Kernel.map_apply' _ (hπCC.prodMk hπY) _ (hD.prod hB)]
    rw [h_pre]
  -- Step 2: Kernel.fst κ s = (M.obsKernel s).map (valuesProjection hCC).
  have hfst :
      ProbabilityTheory.Kernel.fst κ s
        = (M.obsKernel s).map (valuesProjection hCC) := by
    rw [hκ_def]
    unfold obsCondPairKernel
    rw [ProbabilityTheory.Kernel.fst_map_prod _ hπY,
        ProbabilityTheory.Kernel.map_apply _ hπCC]
  -- Step 3: Mathlib disintegration for κ.
  have hKey :
      ∫⁻ c in D, ProbabilityTheory.Kernel.condKernel κ (s, c) B
            ∂(ProbabilityTheory.Kernel.fst κ s)
        = κ s (D ×ˢ B) :=
    ProbabilityTheory.setLIntegral_condKernel_eq_measure_prod (κ := κ) s hD hB
  -- Step 4: obsCondKernel = condKernel of κ (definitional, up to instance).
  -- Assemble (sidestep instance rewriting by going through ENNReal eq).
  rw [← hKpair, ← hKey, hfst]
  -- Goal:  ∫⁻ c in D, condKernel κ (s,c) B d(map π_CC obsKernel s)
  --      = ∫⁻ c in D, obsCondKernel Y CC … (s,c) B d(map π_CC obsKernel s)
  refine MeasureTheory.lintegral_congr_ae ?_
  refine Filter.Eventually.of_forall ?_
  intro c
  -- obsCondKernel is defined as condKernel of obsCondPairKernel.
  change ProbabilityTheory.Kernel.condKernel κ (s, c) B
        = M.obsCondKernel Y CC hY hCC (s, c) B
  rfl


end SCM

end Causalean
