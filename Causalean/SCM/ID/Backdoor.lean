/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.SCM.ID.BackdoorCriterion
import Causalean.SCM.ID.Toolkit.ObsChainRule
import Causalean.SCM.ID.Toolkit.Derivation
import Causalean.SCM.Do.Rule2Kernel.Helpers
import Causalean.SCM.Do.Rule2AE
import Causalean.Mathlib.Probability.Kernel.CompProdAssembly
import Mathlib.Probability.Kernel.CompProdEqIff

/-!
# Backdoor identification, a.e. in the treatment value

The kernel-equality `backdoor_completeness` is pointwise in the post-intervention slice, hence
pointwise in the treatment value `t`.  For non-atomic (continuous) treatment that statement reads
the conditional `obsCondKernel` on the measure-zero `{X = t}` slice, where Mathlib's disintegration
representative is not pinned by the observational law — so the pointwise form is too strong.

This file states the **honest, regime-uniform** version: the identity holds for `νX`-almost-every
treatment value `t`, where `νX` is the observational treatment marginal, under a standard
**positivity / overlap** assumption `P_X × P_Z ≪ P_{X,Z}`.  Discrete/atomic treatment is the special
case where `νX` is atomic, so "a.e. `t`" is "every positive-mass treatment value".

The proof vehicle is the joint identity `νX ⊗ₘ Kdo = νX ⊗ₘ Kbd`, from which the
a.e. statement follows by `ProbabilityTheory.Kernel.ae_eq_of_compProd_eq`.

## Main declarations

* `SCM.treatmentMarginal` — observational treatment marginal `νX`.
* `SCM.BackdoorPositivityAE` — product-overlap condition `P_X × P_Z ≪ P_{X,Z}`.
* `SCM.doKernelY` and `SCM.adjustmentKernelY` — treatment-indexed do and
  backdoor-adjustment kernels for the outcome block.
* `SCM.doKernelY_disintegrate` and `SCM.doKernelY_marginal_const` — chain-rule
  and Rule-3 reductions used in the proof.
* `SCM.backdoor_completeness_ae_compProd` — primary joint-kernel completeness.
* `SCM.backdoor_completeness_ae` — almost-every treatment-value completeness.
* `SCM.backdoor_identifiable_ae` — cross-SCM almost-every identifiability.
-/

namespace Causalean

variable {N : Type*} [DecidableEq N] [Fintype N]

namespace SCM

variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]
-- Genuine per-node primitives; all ValuesOn-level `StandardBorelSpace`/`Nonempty`, kernel
-- finiteness, and `CountableOrCountablyGenerated` instances derive from just these two.
variable [∀ n, StandardBorelSpace (swigΩ Ω n)] [∀ n, Nonempty (swigΩ Ω n)]

open scoped MeasureTheory ProbabilityTheory

-- ============================================================
-- § 1. Treatment marginal and joint positivity
-- ============================================================

/-- The observational treatment marginal `νX = (M.obsKernel s₀).map π_{X.random}`. -/
noncomputable def treatmentMarginal (M : Causalean.SCM N Ω) (X : Finset N)
    (hXr : X.image SWIGNode.random ⊆ M.observed) (s0 : M.FixedValues) :
    MeasureTheory.Measure (ValuesOn (X.image SWIGNode.random) (swigΩ Ω)) :=
  (M.obsKernel s0).map (valuesProjection hXr)

/-- **Joint (product) positivity / overlap at base `s₀`.**

    The product of the observational treatment marginal `νX` and outcome-adjustment marginal `μZ`
    is absolutely continuous w.r.t. the observational joint `μXZ = P_{X,Z}`.  Informally
    `P_X × P_Z ≪ P_{X,Z}` — the standard continuous-treatment positivity, satisfiable in both the
    atomic and non-atomic regimes (vacuous-free, unlike a per-treatment-slice form). -/
def BackdoorPositivityAE (M : Causalean.SCM N Ω) (X : Finset N)
    (Z : Finset (SWIGNode N))
    (hZ : Z ⊆ M.observed)
    (hXr : X.image SWIGNode.random ⊆ M.observed)
    (hXrZ : X.image SWIGNode.random ∪ Z ⊆ M.observed)
    (s0 : M.FixedValues) : Prop :=
  (((M.treatmentMarginal X hXr s0) ⊗ₘ
      (ProbabilityTheory.Kernel.const _
        ((M.obsKernel s0).map (valuesProjection hZ)))).map
      (fun p => valuesUnionMk p.1 p.2))
    ≪ ((M.obsKernel s0).map (valuesProjection hXrZ))

-- ============================================================
-- § 2. The two treatment-indexed kernels
-- ============================================================

/-- Post-intervention `Y`-marginal as a kernel in the treatment value `t`, at base `s₀`:
    `t ↦ ((M.fixSet X).obsKernel (s_post s₀ t)).map π_Y`. -/
noncomputable def doKernelY (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (Y : Finset (SWIGNode N)) (hY : Y ⊆ M.observed) (s0 : M.FixedValues) :
    ProbabilityTheory.Kernel (ValuesOn (X.image SWIGNode.random) (swigΩ Ω))
      (ValuesOn Y (swigΩ Ω)) :=
  (((M.fixSet X hObs hFix).obsKernel.comap (M.fixSetExtend X hObs hFix s0)
      (M.measurable_fixSetExtend X hObs hFix s0)).map
    (valuesProjection ((SCM.fixSet_observed M X hObs hFix).symm ▸ hY)))

/-- Backdoor-adjustment `Y`-marginal as a kernel in the treatment value `t`, at base `s₀`. -/
noncomputable def adjustmentKernelY (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (Y Z : Finset (SWIGNode N)) (hY : Y ⊆ M.observed) (hZ : Z ⊆ M.observed)
    (s0 : M.FixedValues) :
    ProbabilityTheory.Kernel (ValuesOn (X.image SWIGNode.random) (swigΩ Ω))
      (ValuesOn Y (swigΩ Ω)) :=
  (M.backdoorAdjustment X hObs hFix Y Z hY hZ).comap
    (M.fixSetExtend X hObs hFix s0) (M.measurable_fixSetExtend X hObs hFix s0)

/-- The treatment-indexed post-intervention `Y`-marginal kernel is finite. -/
instance instIsFiniteKernelDoKernelY (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (Y : Finset (SWIGNode N)) (hY : Y ⊆ M.observed) (s0 : M.FixedValues) :
    ProbabilityTheory.IsFiniteKernel (M.doKernelY X hObs hFix Y hY s0) := by
  rw [SCM.doKernelY]; infer_instance

/-- The treatment-indexed backdoor-adjustment `Y`-marginal kernel is finite. -/
instance instIsFiniteKernelAdjustmentKernelY (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (Y Z : Finset (SWIGNode N)) (hY : Y ⊆ M.observed) (hZ : Z ⊆ M.observed)
    (s0 : M.FixedValues) :
    ProbabilityTheory.IsFiniteKernel (M.adjustmentKernelY X hObs hFix Y Z hY hZ s0) := by
  rw [SCM.adjustmentKernelY]; infer_instance

-- ============================================================
-- § 2b. Treatment-value-indexed do-calculus (chain rule + Rule 3)
-- ============================================================
-- These lift the kernel-level do-calculus lemmas (the observational chain rule
-- and Rule 3) from the raw `obsKernel`/post-slice level up to the
-- treatment-value-indexed `doKernelY`, so identification proofs never unfold
-- `fixSetExtend`/`fixSetProj` by hand.

/-- **Treatment-indexed chain rule.**  At treatment value `t`, the post-`do(X)`
    `Y`-marginal kernel disintegrates through `Z`: it is the conditional
    `Y ∣ Z` (under `do(X)`) composed with the post-`do(X)` `Z`-marginal kernel.
    The `doKernelY`-level form of `obsKernel_map_eq_obsCondKernel_comp`. -/
theorem doKernelY_disintegrate (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (Y Z : Finset (SWIGNode N)) (hY : Y ⊆ M.observed) (hZ : Z ⊆ M.observed)
    (s0 : M.FixedValues) (t : ValuesOn (X.image SWIGNode.random) (swigΩ Ω)) :
    M.doKernelY X hObs hFix Y hY s0 t
      = ((M.fixSet X hObs hFix).obsCondKernel Y Z
            ((SCM.fixSet_observed M X hObs hFix).symm ▸ hY)
            ((SCM.fixSet_observed M X hObs hFix).symm ▸ hZ)).sectR
          (M.fixSetExtend X hObs hFix s0 t)
        ∘ₘ M.doKernelY X hObs hFix Z hZ s0 t := by
  have hY' : M.doKernelY X hObs hFix Y hY s0 t
      = ((M.fixSet X hObs hFix).obsKernel (M.fixSetExtend X hObs hFix s0 t)).map
          (valuesProjection ((SCM.fixSet_observed M X hObs hFix).symm ▸ hY)) := by
    rw [SCM.doKernelY, ProbabilityTheory.Kernel.map_apply _ (measurable_valuesProjection _),
        ProbabilityTheory.Kernel.comap_apply]
  have hZ' : M.doKernelY X hObs hFix Z hZ s0 t
      = ((M.fixSet X hObs hFix).obsKernel (M.fixSetExtend X hObs hFix s0 t)).map
          (valuesProjection ((SCM.fixSet_observed M X hObs hFix).symm ▸ hZ)) := by
    rw [SCM.doKernelY, ProbabilityTheory.Kernel.map_apply _ (measurable_valuesProjection _),
        ProbabilityTheory.Kernel.comap_apply]
  rw [hY', hZ']
  exact SCM.obsKernel_map_eq_obsCondKernel_comp (M.fixSet X hObs hFix) Y Z _ _ _

/-- **Treatment-indexed Rule 3 (marginal invariance).**  If no `X`-copy is an
    ancestor of any `Z`-node, the post-`do(X)` `Z`-marginal kernel is constant in
    the treatment value and equals the observational `Z`-marginal at base `s₀`.
    The `doKernelY`-level form of `backdoor_rule3_Z_marginal`. -/
theorem doKernelY_marginal_const (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (Z : Finset (SWIGNode N)) (hZ : Z ⊆ M.observed)
    (h_noanc : ∀ z ∈ Z, ∀ D ∈ X,
      ¬ M.toSWIGGraph.dag.isAncestor (SWIGNode.random D) z)
    (s0 : M.FixedValues) (t : ValuesOn (X.image SWIGNode.random) (swigΩ Ω)) :
    M.doKernelY X hObs hFix Z hZ s0 t = (M.obsKernel s0).map (valuesProjection hZ) := by
  have hZ' : M.doKernelY X hObs hFix Z hZ s0 t
      = ((M.fixSet X hObs hFix).obsKernel (M.fixSetExtend X hObs hFix s0 t)).map
          (valuesProjection ((SCM.fixSet_observed M X hObs hFix).symm ▸ hZ)) := by
    rw [SCM.doKernelY, ProbabilityTheory.Kernel.map_apply _ (measurable_valuesProjection _),
        ProbabilityTheory.Kernel.comap_apply]
  rw [hZ']
  have hR3 := SCM.backdoor_rule3_Z_marginal M X hObs hFix Z hZ h_noanc
    (M.fixSetExtend X hObs hFix s0 t)
  rw [SCM.fixSetProj_fixSetExtend] at hR3
  exact hR3

-- ============================================================
-- § 3. Completeness, a.e. in treatment (compProd primary + Form A corollary)
-- ============================================================

/-- **Joint (compProd) completeness — primary form.**

    `νX ⊗ₘ doKernelY = νX ⊗ₘ adjustmentKernelY` at base `s₀`, under the backdoor criterion,
    joint overlap (`Rule2JointOverlap`) and joint positivity (`BackdoorPositivityAE`).  This is the
    object that is well-posed for continuous treatment: it never reads `obsCondKernel` on a
    `μXZ`-null treatment slice. -/
theorem backdoor_completeness_ae_compProd
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (Y Z : Finset (SWIGNode N))
    (hY : Y ⊆ M.observed) (hZ : Z ⊆ M.observed)
    (hXr : X.image SWIGNode.random ⊆ M.observed)
    (hXrZ : X.image SWIGNode.random ∪ Z ⊆ M.observed)
    (_h_bd : M.toSWIGGraph.backdoorCriterion X hObs hFix Y Z)
    (hDisj_YXr : Disjoint Y (X.image SWIGNode.random))
    (hDisj_XrZ : Disjoint (X.image SWIGNode.random) Z)
    (s0 : M.FixedValues)
    (hOverlap : ∀ s : (M.fixSet X hObs hFix).FixedValues,
      Causalean.SCM.ID.Rule2JointOverlap M X hObs hFix Z hXrZ s)
    (_hPositivity : M.BackdoorPositivityAE X Z hZ hXr hXrZ s0) :
    (M.treatmentMarginal X hXr s0) ⊗ₘ (M.doKernelY X hObs hFix Y hY s0)
      = (M.treatmentMarginal X hXr s0) ⊗ₘ (M.adjustmentKernelY X hObs hFix Y Z hY hZ s0) := by
  -- Abbreviations.
  set sT := fun t => M.fixSetExtend X hObs hFix s0 t with hsT
  set hZ_post : Z ⊆ (M.fixSet X hObs hFix).observed :=
    (SCM.fixSet_observed M X hObs hFix).symm ▸ hZ with hZpost_def
  set hY_post : Y ⊆ (M.fixSet X hObs hFix).observed :=
    (SCM.fixSet_observed M X hObs hFix).symm ▸ hY with hYpost_def
  -- μZ = (M.obsKernel s0).map projZ, the observational Z-marginal at base s0.
  set μZ := (M.obsKernel s0).map (valuesProjection hZ) with hμZ
  -- ============================================================
  -- Reduction 1 (chain rule + Rule 3): the do-side Y-marginal kernel at t.
  -- doKernelY t = (sectR (fixSet X).obsCondKernel (sT t)) ∘ₘ μZ
  -- ============================================================
  -- Reduction 1 (chain rule + Rule 3) is now packaged in the treatment-indexed
  -- do-calculus lemmas `doKernelY_disintegrate` and `doKernelY_marginal_const`.
  have hLHS : ∀ t,
      M.doKernelY X hObs hFix Y hY s0 t
        = ((M.fixSet X hObs hFix).obsCondKernel Y Z hY_post hZ_post).sectR (sT t)
          ∘ₘ μZ := by
    intro t
    rw [doKernelY_disintegrate M X hObs hFix Y Z hY hZ s0 t,
      doKernelY_marginal_const M X hObs hFix Z hZ _h_bd.2.2.2.1 s0 t]
  -- ============================================================
  -- Reduction 2 (unfold backdoorAdjustment): the adjustment-side kernel at t.
  -- adjustmentKernelY t = (sectR condPost (sT t)) ∘ₘ μZ
  -- where condPost z = M.obsCondKernel Y (Xr∪Z) (s0, fillZrW (sT t) z).
  -- ============================================================
  -- The `condPost` kernel appearing in `backdoorAdjustment`.
  set hXZ : X.image SWIGNode.random ∪ Z ⊆ M.observed := hXrZ with hXZ_def
  set condPost :
      ProbabilityTheory.Kernel
        ((M.fixSet X hObs hFix).FixedValues × ValuesOn Z (swigΩ Ω))
        (ValuesOn Y (swigΩ Ω)) :=
    (M.obsCondKernel Y (X.image SWIGNode.random ∪ Z) hY hXZ).comap
      (fun p : (M.fixSet X hObs hFix).FixedValues × ValuesOn Z (swigΩ Ω) =>
        (M.fixSetProj X hObs hFix p.1, M.fillZrW X hObs hFix Z p.1 p.2))
      (Measurable.prodMk
        ((M.measurable_fixSetProj X hObs hFix).comp measurable_fst)
        (M.measurable_fillZrW_prod X hObs hFix Z)) with hcondPost_def
  haveI : ProbabilityTheory.IsMarkovKernel
      (M.obsCondKernel Y (X.image SWIGNode.random ∪ Z) hY hXZ) := by
    unfold SCM.obsCondKernel; infer_instance
  haveI : ProbabilityTheory.IsMarkovKernel condPost := by
    rw [hcondPost_def]; infer_instance
  have hRHS : ∀ t,
      M.adjustmentKernelY X hObs hFix Y Z hY hZ s0 t
        = condPost.sectR (sT t) ∘ₘ μZ := by
    intro t
    -- adjustmentKernelY t = backdoorAdjustment (sT t).
    have hadj :
        M.adjustmentKernelY X hObs hFix Y Z hY hZ s0 t
          = M.backdoorAdjustment X hObs hFix Y Z hY hZ (sT t) := by
      rw [SCM.adjustmentKernelY, ProbabilityTheory.Kernel.comap_apply]
    rw [hadj]
    -- Unfold backdoorAdjustment body to ((zMarginalPost ⊗ₖ condPost).map snd) (sT t).
    change ((((M.obsKernel.map (valuesProjection hZ)).comap
            (M.fixSetProj X hObs hFix)
            (M.measurable_fixSetProj X hObs hFix))
          ⊗ₖ condPost).map Prod.snd) (sT t)
      = condPost.sectR (sT t) ∘ₘ μZ
    rw [Causalean.Mathlib.CompProdAssembly.compProd_map_snd_apply,
        ProbabilityTheory.Kernel.comap_apply,
        ProbabilityTheory.Kernel.map_apply _ (measurable_valuesProjection _),
        SCM.fixSetProj_fixSetExtend, ← hμZ]
  -- ============================================================
  -- a.e. Rule 2 on the product νX ⊗ₘ const μZ.
  -- ============================================================
  -- νX = treatmentMarginal = (M.obsKernel s0).map projXr.
  set νX := M.treatmentMarginal X hXr s0 with hνX
  have hνX_eq : νX = (M.obsKernel s0).map (valuesProjection hXr) := by
    rw [hνX, SCM.treatmentMarginal]
  -- The product measure λ = νX ⊗ₘ const μZ.
  set lam := νX ⊗ₘ ProbabilityTheory.Kernel.const _ μZ with hlam
  -- Finiteness instances.
  haveI : MeasureTheory.IsFiniteMeasure νX := by
    rw [hνX_eq]; exact (M.obsKernel s0).isFiniteMeasure_map _
  haveI : MeasureTheory.IsFiniteMeasure μZ := by
    rw [hμZ]; exact (M.obsKernel s0).isFiniteMeasure_map _
  -- Apply the a.e. Rule 2 with Z := X, W := Z.
  have hPos_ae : (((M.obsKernel s0).map (valuesProjection hXr) ⊗ₘ
          ProbabilityTheory.Kernel.const _
            ((M.obsKernel s0).map (valuesProjection hZ))).map
          (fun p => valuesUnionMk p.1 p.2))
        ≪ ((M.obsKernel s0).map (valuesProjection hXrZ)) := _hPositivity
  -- Rule 2 straight from the backdoor criterion: the applicator derives the
  -- d-separation + non-descendance premises internally.
  have hR2 := SCM.backdoor_rule2_ae M X hObs hFix Y Z hY hZ hXr hXrZ
    hDisj_YXr hDisj_XrZ _h_bd s0 hOverlap hPos_ae
  haveI hdoKfin : ProbabilityTheory.IsFiniteKernel
      (M.doKernelY X hObs hFix Y hY s0) := by
    rw [SCM.doKernelY]; infer_instance
  haveI hadjSF : ProbabilityTheory.IsSFiniteKernel
      (M.adjustmentKernelY X hObs hFix Y Z hY hZ s0) := by
    rw [SCM.adjustmentKernelY, SCM.backdoorAdjustment]; infer_instance
  set liftTZ :
      ValuesOn (X.image SWIGNode.random) (swigΩ Ω) × ValuesOn Z (swigΩ Ω) →
        (M.fixSet X hObs hFix).FixedValues × ValuesOn Z (swigΩ Ω) :=
    fun p => (sT p.1, p.2) with hliftTZ_def
  have hliftTZ_meas : Measurable liftTZ := by
    rw [hliftTZ_def, hsT]
    exact Measurable.prodMk
      ((M.measurable_fixSetExtend X hObs hFix s0).comp measurable_fst)
      measurable_snd
  set fL :
      ProbabilityTheory.Kernel
        (ValuesOn (X.image SWIGNode.random) (swigΩ Ω) × ValuesOn Z (swigΩ Ω))
        (ValuesOn Y (swigΩ Ω)) :=
    ((M.fixSet X hObs hFix).obsCondKernel Y Z hY_post hZ_post).comap
      liftTZ hliftTZ_meas with hfL_def
  set fR :
      ProbabilityTheory.Kernel
        (ValuesOn (X.image SWIGNode.random) (swigΩ Ω) × ValuesOn Z (swigΩ Ω))
        (ValuesOn Y (swigΩ Ω)) :=
    condPost.comap liftTZ hliftTZ_meas with hfR_def
  have hL : ∀ t,
      M.doKernelY X hObs hFix Y hY s0 t = (fL.sectR t) ∘ₘ μZ := by
    intro t
    simpa [hfL_def, hliftTZ_def] using hLHS t
  have hR : ∀ t,
      M.adjustmentKernelY X hObs hFix Y Z hY hZ s0 t = (fR.sectR t) ∘ₘ μZ := by
    intro t
    simpa [hfR_def, hliftTZ_def] using hRHS t
  have hae : ∀ᵐ p ∂(νX ⊗ₘ ProbabilityTheory.Kernel.const
        (ValuesOn (X.image SWIGNode.random) (swigΩ Ω)) μZ), fL p = fR p := by
    rw [hνX_eq, hμZ]
    filter_upwards [hR2] with p hp
    simpa [hfL_def, hfR_def, hliftTZ_def, hcondPost_def, hsT,
      ProbabilityTheory.Kernel.comap_apply,
      SCM.fixSetProj_fixSetExtend, SCM.fillZrW_fixSetExtend] using hp
  exact Causalean.Mathlib.CompProdAssembly.compProd_eq_of_inner_ae νX μZ
    (M.doKernelY X hObs hFix Y hY s0)
    (M.adjustmentKernelY X hObs hFix Y Z hY hZ s0)
    fL fR hL hR hae

/-- **Backdoor completeness, a.e. in the treatment value.**

    For `νX`-almost-every treatment value `t`, the post-intervention `Y`-marginal at `(s₀, t)`
    equals the backdoor-adjustment functional at `(s₀, t)`.  Continuous and discrete treatment are
    both covered: discrete is the atomic-`νX` case where "a.e. `t`" is pointwise on the support. -/
theorem backdoor_completeness_ae
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (Y Z : Finset (SWIGNode N))
    (hY : Y ⊆ M.observed) (hZ : Z ⊆ M.observed)
    (hXr : X.image SWIGNode.random ⊆ M.observed)
    (hXrZ : X.image SWIGNode.random ∪ Z ⊆ M.observed)
    (h_bd : M.toSWIGGraph.backdoorCriterion X hObs hFix Y Z)
    (hDisj_YXr : Disjoint Y (X.image SWIGNode.random))
    (hDisj_XrZ : Disjoint (X.image SWIGNode.random) Z)
    (s0 : M.FixedValues)
    (hOverlap : ∀ s : (M.fixSet X hObs hFix).FixedValues,
      Causalean.SCM.ID.Rule2JointOverlap M X hObs hFix Z hXrZ s)
    (hPositivity : M.BackdoorPositivityAE X Z hZ hXr hXrZ s0) :
    ∀ᵐ t ∂(M.treatmentMarginal X hXr s0),
      M.doKernelY X hObs hFix Y hY s0 t
        = M.adjustmentKernelY X hObs hFix Y Z hY hZ s0 t := by
  haveI : MeasureTheory.IsFiniteMeasure (M.treatmentMarginal X hXr s0) := by
    unfold treatmentMarginal
    exact (M.obsKernel s0).isFiniteMeasure_map _
  exact ProbabilityTheory.Kernel.ae_eq_of_compProd_eq
    (M.backdoor_completeness_ae_compProd X hObs hFix Y Z hY hZ hXr hXrZ h_bd
      hDisj_YXr hDisj_XrZ s0 hOverlap hPositivity)

/-- **Backdoor identifiability, a.e. in the treatment value (cross-SCM corollary).**

    Two SCMs `M₁`, `M₂` sharing the same SWIG graph (`h_swig`) and the same
    observational kernel (`h_obs`) produce equal post-intervention `Y`-marginal
    kernels, for `νX`-almost-every treatment value `t`.

    The kernel `doKernelY M X hObs hFix Y hY s0` has
    type `Kernel (ValuesOn (X.image SWIGNode.random) (swigΩ Ω)) (ValuesOn Y (swigΩ Ω))`,
    which depends only on `X`, `Y`, `Ω` — not on `M`'s fixed values.  Hence
    `doKernelY M₁ …` and `doKernelY M₂ …` share a type and the conclusion is a
    plain `=ᵐ[νX]` (filter `MeasureTheory.ae`), not an `HEq`.

    Proof: rewrite each side to `adjustmentKernelY` via `backdoor_completeness_ae`,
    transport across by cross-SCM invariance of the adjustment kernel
    (`backdoorAdjustment_invariant`, after destructuring + `cases h_swig` to align
    the SWIGGraph-derived type indices), and use that the treatment marginals agree
    via `h_obs`. -/
theorem backdoor_identifiable_ae
    (M₁ M₂ : Causalean.SCM N Ω)
    (h_swig : M₁.toSWIGGraph = M₂.toSWIGGraph)
    (X : Finset N) (Y Z : Finset (SWIGNode N))
    (hObs₁ : ∀ D ∈ X, SWIGNode.random D ∈ M₁.observed)
    (hFix₁ : ∀ D ∈ X, SWIGNode.fixed D ∉ M₁.fixed)
    (hObs₂ : ∀ D ∈ X, SWIGNode.random D ∈ M₂.observed)
    (hFix₂ : ∀ D ∈ X, SWIGNode.fixed D ∉ M₂.fixed)
    (hY₁ : Y ⊆ M₁.observed) (hZ₁ : Z ⊆ M₁.observed)
    (hY₂ : Y ⊆ M₂.observed) (hZ₂ : Z ⊆ M₂.observed)
    (hXr₁ : X.image SWIGNode.random ⊆ M₁.observed)
    (hXr₂ : X.image SWIGNode.random ⊆ M₂.observed)
    (hXrZ₁ : X.image SWIGNode.random ∪ Z ⊆ M₁.observed)
    (hXrZ₂ : X.image SWIGNode.random ∪ Z ⊆ M₂.observed)
    (h_bd₁ : M₁.toSWIGGraph.backdoorCriterion X hObs₁ hFix₁ Y Z)
    (h_bd₂ : M₂.toSWIGGraph.backdoorCriterion X hObs₂ hFix₂ Y Z)
    (hDisj_YXr : Disjoint Y (X.image SWIGNode.random))
    (hDisj_XrZ : Disjoint (X.image SWIGNode.random) Z)
    (s0₁ : M₁.FixedValues) (s0₂ : M₂.FixedValues)
    (hOverlap₁ : ∀ s : (M₁.fixSet X hObs₁ hFix₁).FixedValues,
      Causalean.SCM.ID.Rule2JointOverlap M₁ X hObs₁ hFix₁ Z hXrZ₁ s)
    (hOverlap₂ : ∀ s : (M₂.fixSet X hObs₂ hFix₂).FixedValues,
      Causalean.SCM.ID.Rule2JointOverlap M₂ X hObs₂ hFix₂ Z hXrZ₂ s)
    (hPositivity₁ : M₁.BackdoorPositivityAE X Z hZ₁ hXr₁ hXrZ₁ s0₁)
    (hPositivity₂ : M₂.BackdoorPositivityAE X Z hZ₂ hXr₂ hXrZ₂ s0₂)
    (h_obs : HEq M₁.obsKernel M₂.obsKernel)
    (h_s0 : HEq s0₁ s0₂) :
    (M₁.doKernelY X hObs₁ hFix₁ Y hY₁ s0₁)
      =ᵐ[M₁.treatmentMarginal X hXr₁ s0₁]
      (M₂.doKernelY X hObs₂ hFix₂ Y hY₂ s0₂) := by
  -- Destructure both SCMs and `cases h_swig` to align the SWIGGraph-derived
  -- type indices (FixedValues, observed, fixSet, treatmentMarginal); then the
  -- base points `s0₁ s0₂` and obsKernels coincide.
  obtain ⟨⟨dag₁, fixed₁, observed₁, unobserved₁,
           fio₁, oi₁, od₁, oou₁, foi₁, fou₁, aic₁, dc₁, foff₁, aco₁⟩,
         eT₁, iota₁, sf₁, mf₁, lD₁, pL₁⟩ := M₁
  obtain ⟨⟨dag₂, fixed₂, observed₂, unobserved₂,
           fio₂, oi₂, od₂, oou₂, foi₂, fou₂, aic₂, dc₂, foff₂, aco₂⟩,
         eT₂, iota₂, sf₂, mf₂, lD₂, pL₂⟩ := M₂
  cases h_swig
  -- After `cases h_swig` the SWIGGraph fields agree definitionally, so the two
  -- `FixedValues` types coincide and `h_s0` is an equality of base points.
  -- The two SCMs still differ in their non-SWIGGraph fields, so we keep them as
  -- distinct structure literals and use `h_obs` as a rewrite (obsKernel is a
  -- *derived* def, not a structure field, hence not `cases`-able).
  cases h_s0
  -- Step 1: do-side ≡ adjustment-side on each SCM, a.e.
  have hc1 := backdoor_completeness_ae
    ⟨⟨dag₁, fixed₁, observed₁, unobserved₁, fio₁, oi₁, od₁, oou₁,
       foi₁, fou₁, aic₁, dc₁, foff₁, aco₁⟩, eT₁, iota₁, sf₁, mf₁, lD₁, pL₁⟩
    X hObs₁ hFix₁ Y Z hY₁ hZ₁ hXr₁ hXrZ₁ h_bd₁ hDisj_YXr hDisj_XrZ
    s0₁ hOverlap₁ hPositivity₁
  have hc2 := backdoor_completeness_ae
    ⟨⟨dag₁, fixed₁, observed₁, unobserved₁, fio₁, oi₁, od₁, oou₁,
       foi₁, fou₁, aic₁, dc₁, foff₁, aco₁⟩, eT₂, iota₂, sf₂, mf₂, lD₂, pL₂⟩
    X hObs₂ hFix₂ Y Z hY₂ hZ₂ hXr₂ hXrZ₂ h_bd₂ hDisj_YXr hDisj_XrZ
    s0₁ hOverlap₂ hPositivity₂
  -- Step 2: cross-SCM invariance of the adjustment kernel.
  have hinv :
      (⟨⟨dag₁, fixed₁, observed₁, unobserved₁, fio₁, oi₁, od₁, oou₁,
          foi₁, fou₁, aic₁, dc₁, foff₁, aco₁⟩, eT₁, iota₁, sf₁, mf₁, lD₁, pL₁⟩ :
          Causalean.SCM N Ω).adjustmentKernelY X hObs₁ hFix₁ Y Z hY₁ hZ₁ s0₁
        = (⟨⟨dag₁, fixed₁, observed₁, unobserved₁, fio₁, oi₁, od₁, oou₁,
            foi₁, fou₁, aic₁, dc₁, foff₁, aco₁⟩, eT₂, iota₂, sf₂, mf₂, lD₂, pL₂⟩ :
            Causalean.SCM N Ω).adjustmentKernelY X hObs₂ hFix₂ Y Z hY₂ hZ₂ s0₁ := by
    rw [adjustmentKernelY, adjustmentKernelY]
    have hbd := backdoorAdjustment_invariant
      (⟨⟨dag₁, fixed₁, observed₁, unobserved₁, fio₁, oi₁, od₁, oou₁,
          foi₁, fou₁, aic₁, dc₁, foff₁, aco₁⟩, eT₁, iota₁, sf₁, mf₁, lD₁, pL₁⟩ :
          Causalean.SCM N Ω)
      (⟨⟨dag₁, fixed₁, observed₁, unobserved₁, fio₁, oi₁, od₁, oou₁,
          foi₁, fou₁, aic₁, dc₁, foff₁, aco₁⟩, eT₂, iota₂, sf₂, mf₂, lD₂, pL₂⟩ :
          Causalean.SCM N Ω)
      rfl h_obs X hObs₁ hFix₁ hObs₂ hFix₂ Y Z hY₁ hZ₁ hY₂ hZ₂
    rw [eq_of_heq hbd]
    rfl
  -- Step 3: the treatment marginals coincide (same obsKernel, same base, same
  -- projection index).
  have hνX :
      (⟨⟨dag₁, fixed₁, observed₁, unobserved₁, fio₁, oi₁, od₁, oou₁,
          foi₁, fou₁, aic₁, dc₁, foff₁, aco₁⟩, eT₁, iota₁, sf₁, mf₁, lD₁, pL₁⟩ :
          Causalean.SCM N Ω).treatmentMarginal X hXr₁ s0₁
        = (⟨⟨dag₁, fixed₁, observed₁, unobserved₁, fio₁, oi₁, od₁, oou₁,
            foi₁, fou₁, aic₁, dc₁, foff₁, aco₁⟩, eT₂, iota₂, sf₂, mf₂, lD₂, pL₂⟩ :
            Causalean.SCM N Ω).treatmentMarginal X hXr₂ s0₁ := by
    rw [treatmentMarginal, treatmentMarginal, eq_of_heq h_obs]
  -- Assemble: doKernelY M₁ ≡ adjY M₁ = adjY M₂ ≡ doKernelY M₂.
  refine Filter.EventuallyEq.trans hc1 ?_
  rw [hinv, hνX]
  exact Filter.EventuallyEq.symm hc2

end SCM

end Causalean
