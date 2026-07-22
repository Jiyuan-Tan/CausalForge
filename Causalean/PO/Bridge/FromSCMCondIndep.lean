/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.PO.Bridge.FromSCM
import Causalean.PO.Assumptions.IndepCF
import Causalean.SCM.Do.GlobalMarkov
import Causalean.Mathlib.CondDistrib

/-! # Conditional-Independence Bridge from SCMs to Induced PO Systems

This file connects graphical conditional independence in an SCM to
counterfactual conditional independence in the potential-outcome system induced
by that SCM.  The bridge is stated with explicit value-correspondence
hypotheses: consumers identify the PO regimed values with measurable functions
of the SWIG coordinate projections whose d-separation they can prove.  The main
theorem, `POSystem.ofSCM_condIndepCF_of_dSep`, pulls a global-Markov
`CondIndepFun` statement through the induced-system evaluation map and optional
measurable post-processing of the `X`- and `Y`-side values.
-/

namespace Causalean
namespace PO

open MeasureTheory ProbabilityTheory

universe uN uΩ

variable {N : Type uN} [DecidableEq N] [Fintype N]
variable {Ω : N → Type uΩ} [∀ n, MeasurableSpace (Ω n)]

namespace POSystem

private theorem condIndepFun_comp_of_map
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α]
    {β : Type*} [MeasurableSpace β] [StandardBorelSpace β]
    {γ : Type*} [MeasurableSpace γ] [StandardBorelSpace γ] [Nonempty γ]
    {δ : Type*} [MeasurableSpace δ] [StandardBorelSpace δ] [Nonempty δ]
    {ε : Type*} [MeasurableSpace ε]
    {φ : α → β} (hφ : Measurable φ)
    {X : β → γ} (hX : Measurable X)
    {Y : β → δ} (hY : Measurable Y)
    {Z : β → ε} (hZ : Measurable Z)
    {ν : Measure α} [IsFiniteMeasure ν]
    [IsFiniteMeasure (ν.map φ)]
    (h : CondIndepFun
      (MeasurableSpace.comap Z inferInstance) (hZ.comap_le)
      X Y (ν.map φ)) :
    CondIndepFun
      (MeasurableSpace.comap (Z ∘ φ) inferInstance)
      (Measurable.comap_le (hZ.comp hφ))
      (X ∘ φ) (Y ∘ φ) ν := by
  rw [condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight
    (hY.comp hφ) (hX.comp hφ) (hZ.comp hφ)]
  have h_joint := (condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight
    (μ := ν.map φ) (f := Y) (g := X) (k := Z) hY hX hZ).mp h
  have hpair_meas : Measurable (fun b : β => (Z b, X b)) := hZ.prodMk hX
  have hpair_comp : (fun b : β => (Z b, X b)) ∘ φ =
      fun a : α => ((Z ∘ φ) a, (X ∘ φ) a) := rfl
  have htr_pair := condDistrib_map_comp (𝒴 := δ) ν
    (φ := φ) (g := Y) (f := fun b : β => (Z b, X b))
    hφ hY hpair_meas
  have htr_Z := condDistrib_map_comp (𝒴 := δ) ν
    (φ := φ) (g := Y) (f := Z) hφ hY hZ
  rw [hpair_comp] at htr_pair
  have hmap_pair : (ν.map φ).map (fun b : β => (Z b, X b)) =
      ν.map (fun a : α => ((Z ∘ φ) a, (X ∘ φ) a)) := by
    rw [Measure.map_map hpair_meas hφ, hpair_comp]
  have hmap_Z : (ν.map φ).map Z = ν.map (Z ∘ φ) := by
    rw [Measure.map_map hZ hφ]
  rw [hmap_pair] at h_joint htr_pair
  rw [hmap_Z] at htr_Z
  have htr_Z_fst :
      (fun p : ε × γ => condDistrib Y Z (ν.map φ) p.1)
        =ᵐ[ν.map (fun a : α => ((Z ∘ φ) a, (X ∘ φ) a))]
          fun p : ε × γ => condDistrib (Y ∘ φ) (Z ∘ φ) ν p.1 := by
    have hfst_marg : (ν.map (fun a : α => ((Z ∘ φ) a, (X ∘ φ) a))).map Prod.fst =
        ν.map (Z ∘ φ) := by
      rw [Measure.map_map measurable_fst ((hZ.comp hφ).prodMk (hX.comp hφ))]
      rfl
    exact ae_eq_comp (μ := ν.map (fun a : α => ((Z ∘ φ) a, (X ∘ φ) a)))
      (f := Prod.fst)
      (g := fun z => condDistrib Y Z (ν.map φ) z)
      (g' := fun z => condDistrib (Y ∘ φ) (Z ∘ φ) ν z)
      measurable_fst.aemeasurable (by rw [hfst_marg]; exact htr_Z)
  filter_upwards [htr_pair.symm, h_joint, htr_Z_fst] with p hp_pair hp_joint hp_Z
  rw [hp_pair, hp_joint, Kernel.prodMkRight_apply, hp_Z, Kernel.prodMkRight_apply]

/-- If the SWIG node sets `X` and `Y` are d-separated by `Z`, then the matching
regimed variable and counterfactual bundle in the PO system induced by `M` are
conditionally independent given the matching `Z`-projection.

The hypotheses `ha_value`, `hB_value`, and `hc_value` are the explicit
PO-to-SCM value correspondence: under latent draw `ℓ`, the PO value of `a`, the
joint value of `B`, and the conditioning value of `c` are respectively obtained
from the evaluated SCM state `M.evalMap s ℓ` by projecting to `X`, `Y`, and `Z`
(with measurable post-processing for `a` and `B`). -/
theorem ofSCM_condIndepCF_of_dSep
    (M : Causalean.SCM N Ω) (s : SCM.FixedValues M)
    [StandardBorelSpace M.RandomValues] [StandardBorelSpace M.LatentValues]
    [StandardBorelSpace (POSystem.ofSCM M s).Ω]
    [∀ n, StandardBorelSpace (swigΩ Ω n)] [∀ n, Nonempty (swigΩ Ω n)]
    [∀ s' : M.FixedValues, IsFiniteMeasure (M.jointKernel s')]
    {X Y Z : Finset (SWIGNode N)}
    (hX : X ⊆ M.randomVars) (hY : Y ⊆ M.randomVars) (hZ : Z ⊆ M.randomVars)
    (hDisj_XY : Disjoint X Y) (hDisj_XZ : Disjoint X Z) (hDisj_YZ : Disjoint Y Z)
    (hdSep : M.dag.dSep X Y Z)
    {α : Type*} [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
    (a : RegimedVar (POSystem.ofSCM M s) α)
    (B : POCFBundle (POSystem.ofSCM M s))
    [StandardBorelSpace (∀ i : Fin B.n, B.type i)] [Nonempty (∀ i : Fin B.n, B.type i)]
    (c : RegimedVar (POSystem.ofSCM M s) (ValuesOn Z (swigΩ Ω)))
    (aMap : ValuesOn X (swigΩ Ω) → α)
    (BMap : ValuesOn Y (swigΩ Ω) → (∀ i : Fin B.n, B.type i))
    (haMap : Measurable aMap) (hBMap : Measurable BMap)
    (ha_value : a.value =
      aMap ∘ valuesProjection (Ω := swigΩ Ω) hX ∘ (fun ℓ : M.LatentValues => M.evalMap s ℓ))
    (hB_value : B.jointValue =
      BMap ∘ valuesProjection (Ω := swigΩ Ω) hY ∘ (fun ℓ : M.LatentValues => M.evalMap s ℓ))
    (hc_value : c.value =
      valuesProjection (Ω := swigΩ Ω) hZ ∘ (fun ℓ : M.LatentValues => M.evalMap s ℓ)) :
    (POSystem.ofSCM M s).CondIndepCF a B c (POSystem.ofSCM M s).μ := by
  let E : M.LatentValues → M.RandomValues := fun ℓ => M.evalMap s ℓ
  have hE : Measurable E := by
    have hmeas := M.evalMap_measurable
    simpa [E, Function.uncurry] using
      hmeas.comp (Measurable.prodMk measurable_const measurable_id)
  have hFull : SCM.FullCondIndep M X Y Z hX hY hZ (M.jointKernel s) :=
    SCM.full_globalMarkov M X Y Z hX hY hZ hDisj_XY hDisj_XZ hDisj_YZ hdSep s
  have hJointEq : M.jointKernel s = M.latentProduct.map E := by
    simpa [E] using SCM.jointKernel_apply_eq M s
  haveI : IsFiniteMeasure (M.latentProduct.map E) := hJointEq ▸
    (inferInstance : IsFiniteMeasure (M.jointKernel s))
  have hFullMap : CondIndepFun
      (MeasurableSpace.comap (valuesProjection (Ω := swigΩ Ω) hZ) inferInstance)
      (comap_valuesProjection_le (Ω' := swigΩ Ω) hZ)
      (valuesProjection (Ω := swigΩ Ω) hX)
      (valuesProjection (Ω := swigΩ Ω) hY)
      (M.latentProduct.map E) := by
    simpa [SCM.FullCondIndep, hJointEq] using hFull
  have hPull : CondIndepFun
      (MeasurableSpace.comap
        (valuesProjection (Ω := swigΩ Ω) hZ ∘ E) inferInstance)
      (Measurable.comap_le ((measurable_valuesProjection (Ω' := swigΩ Ω) hZ).comp hE))
      (valuesProjection (Ω := swigΩ Ω) hX ∘ E)
      (valuesProjection (Ω := swigΩ Ω) hY ∘ E)
      M.latentProduct :=
    condIndepFun_comp_of_map hE
      (measurable_valuesProjection (Ω' := swigΩ Ω) hX)
      (measurable_valuesProjection (Ω' := swigΩ Ω) hY)
      (measurable_valuesProjection (Ω' := swigΩ Ω) hZ)
      hFullMap
  have hComp : CondIndepFun
      (MeasurableSpace.comap
        (valuesProjection (Ω := swigΩ Ω) hZ ∘ E) inferInstance)
      (Measurable.comap_le ((measurable_valuesProjection (Ω' := swigΩ Ω) hZ).comp hE))
      (aMap ∘ valuesProjection (Ω := swigΩ Ω) hX ∘ E)
      (BMap ∘ valuesProjection (Ω := swigΩ Ω) hY ∘ E)
      M.latentProduct := by
    simpa [Function.comp_assoc] using hPull.comp haMap hBMap
  unfold CondIndepCF
  convert hComp using 3

end POSystem

end PO
end Causalean
