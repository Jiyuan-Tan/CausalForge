/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.SCM.Do.Rule2
import Causalean.SCM.Do.Rule2Kernel.Helpers
import Causalean.SCM.Do.Rule2Kernel.DiscreteZHelpers
import Causalean.SCM.Do.Rule2Kernel.WitnessBridge

/-!
# Rule 2, a.e. in the treatment value (product form + positivity)

The retired pointwise Rule 2 form quantified a.e. in the conditioning value
`w` but pointwise in the treatment value (the `Z.random` do-value spliced via
`fillZrW`). For non-atomic treatment that point lies on a `μ_C`-null slice where
Mathlib's `obsCondKernel` representative is unpinned, so the pointwise form is
too strong.

The honest generalization quantifies a.e. over the **product** `νZ ⊗ₘ μW` of the observational
treatment marginal `νZ := (M'.obsKernel s0).map π_{Zr}` and conditioning marginal
`μW := (M'.obsKernel s0).map π_W`, under a **positivity** hypothesis `(νZ ⊗ₘ μW) ∘ fill⁻¹ ≪ μ_C`.
Both regimes are covered: atomic `νZ` makes "a.e." pointwise on the support.

Why the product (not the joint `μ_C`): the do-side `(M'.fixSet Z).obsCondKernel Y W` is pinned only
under the do-model `W`-marginal (`= μW` via Rule 3), i.e. under the product; the obs-side
`M'.obsCondKernel` is pinned under `μ_C`. Positivity (`product ≪ μ_C`) lifts the
obs-side onto the product, where the do-side is natively pinned. The proof lifts
the discrete d-sep collapse and cross-SCM
bridge (`obsCondKernel_dSep_collapse_ae`, `obsCondKernel_cross_SCM_ae_eq_on_fillZrW`,
`obsKernel_fixSet_W_marginal_eq_M1_marginal`) from the per-treatment slice to
the product via Fubini over the treatment + the product↔joint AC transfer.
-/

namespace Causalean
variable {N : Type*} [DecidableEq N] [Fintype N]
namespace SCM
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]
open scoped MeasureTheory ProbabilityTheory

/-- **Joint-`μ_C`-a.e. cross-SCM condDistrib bridge (isolated hard lemma).**

    For `(νZ ⊗ₘ μW)`-a.e. pair `(t, w)`, the measure-level `W`-conditional of the do-model
    intervened at `t` (evaluated at `w`) equals the original model's `(Z.random ∪ W)`-conditional
    (evaluated at the filled point `fill(t, w)`).  This is the `condDistrib`-level analogue of the
    theorem below; reducing the `obsCondKernel` statement to this lemma is the easy assembly
    (Rule 3 + Fubini + obs-side AC transport, done in `obsCondKernel_fixSet_eq_ae_witness`). -/
theorem condDistrib_fixSet_cross_SCM_bridge
    (M' : Causalean.SCM N Ω) (Z : Finset N)
    (hZ_obs : ∀ D ∈ Z, SWIGNode.random D ∈ M'.observed)
    (hZ_fixed : ∀ D ∈ Z, SWIGNode.fixed D ∉ M'.fixed)
    (Y W : Finset (SWIGNode N))
    (hY : Y ⊆ M'.observed)
    (hW : W ⊆ M'.observed)
    (hZr : Z.image SWIGNode.random ⊆ M'.observed)
    (hZrW : Z.image SWIGNode.random ∪ W ⊆ M'.observed)
    (hDisj_YZr : Disjoint Y (Z.image SWIGNode.random))
    (hDisj_ZrW : Disjoint (Z.image SWIGNode.random) W)
    (hdSep : (M'.fixSet Z hZ_obs hZ_fixed).dag.dSep
      Y (Z.image SWIGNode.random)
      (W ∪ (M'.fixSet Z hZ_obs hZ_fixed).fixed))
    (hWNonDesc : ∀ z ∈ Z, ∀ v ∈ W,
      ¬ (M'.fixSet Z hZ_obs hZ_fixed).dag.isAncestor (SWIGNode.fixed z) v)
    (hWNonDescM1 : ∀ D ∈ Z, ∀ w ∈ W,
      ¬ M'.dag.isAncestor (SWIGNode.random D) w)
    [StandardBorelSpace M'.RandomValues]
    [∀ n, StandardBorelSpace (swigΩ Ω n)] [∀ n, Nonempty (swigΩ Ω n)]
    [StandardBorelSpace (M'.fixSet Z hZ_obs hZ_fixed).RandomValues]
    [StandardBorelSpace (M'.fixSet Z hZ_obs hZ_fixed).ObservedValues]
    [StandardBorelSpace (ValuesOn Y (swigΩ Ω))]
    [Nonempty (ValuesOn Y (swigΩ Ω))]
    [StandardBorelSpace
      (ValuesOn (M'.cutsetLatent Y (Z.image SWIGNode.random ∪ W)) (swigΩ Ω))]
    [Nonempty
      (ValuesOn (M'.cutsetLatent Y (Z.image SWIGNode.random ∪ W)) (swigΩ Ω))]
    [StandardBorelSpace (ValuesOn (Z.image SWIGNode.random) (swigΩ Ω))]
    [Nonempty (ValuesOn (Z.image SWIGNode.random) (swigΩ Ω))]
    [∀ s : M'.FixedValues, MeasureTheory.IsFiniteMeasure (M'.jointKernel s)]
    [∀ s : M'.FixedValues, MeasureTheory.IsFiniteMeasure (M'.obsKernel s)]
    [∀ s : (M'.fixSet Z hZ_obs hZ_fixed).FixedValues,
      MeasureTheory.IsFiniteMeasure
        ((M'.fixSet Z hZ_obs hZ_fixed).jointKernel s)]
    [∀ s : (M'.fixSet Z hZ_obs hZ_fixed).FixedValues,
      MeasureTheory.IsFiniteMeasure
        ((M'.fixSet Z hZ_obs hZ_fixed).obsKernel s)]
    [MeasurableSpace.CountableOrCountablyGenerated
      M'.FixedValues (ValuesOn (Z.image SWIGNode.random ∪ W) (swigΩ Ω))]
    [MeasurableSpace.CountableOrCountablyGenerated
      (M'.fixSet Z hZ_obs hZ_fixed).FixedValues
      (ValuesOn (Z.image SWIGNode.random ∪ W) (swigΩ Ω))]
    [MeasurableSpace.CountableOrCountablyGenerated
      (M'.fixSet Z hZ_obs hZ_fixed).FixedValues (ValuesOn W (swigΩ Ω))]
    [MeasurableSingletonClass
      (ValuesOn (Z.image SWIGNode.random ∪ W) (swigΩ Ω))]
    (s0 : M'.FixedValues)
    (hOverlap : ∀ s : (M'.fixSet Z hZ_obs hZ_fixed).FixedValues,
      Causalean.SCM.ID.Rule2JointOverlap M' Z hZ_obs hZ_fixed W hZrW s)
    (hPositivity_ae :
      (((M'.obsKernel s0).map (valuesProjection hZr) ⊗ₘ
          ProbabilityTheory.Kernel.const _
            ((M'.obsKernel s0).map (valuesProjection hW))).map
          (fun p => valuesUnionMk p.1 p.2))
        ≪ ((M'.obsKernel s0).map (valuesProjection hZrW)))
    :
    ∀ᵐ p ∂((M'.obsKernel s0).map (valuesProjection hZr) ⊗ₘ
            ProbabilityTheory.Kernel.const _
              ((M'.obsKernel s0).map (valuesProjection hW))),
      (M'.fixSet Z hZ_obs hZ_fixed).obsCondKernel Y W
          ((SCM.fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hY)
          ((SCM.fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hW)
          (M'.fixSetExtend Z hZ_obs hZ_fixed s0 p.1, p.2)
        = ProbabilityTheory.condDistrib
            (valuesProjection hY) (valuesProjection hZrW) (M'.obsKernel s0)
            (valuesUnionMk p.1 p.2) := by
  classical
  -- The product measure `λ = νZ ⊗ₘ const μW` and the fill map `G = valuesUnionMk`.
  set νZ := (M'.obsKernel s0).map (valuesProjection hZr) with hνZ
  set μW := (M'.obsKernel s0).map (valuesProjection hW) with hμW
  set lam := νZ ⊗ₘ ProbabilityTheory.Kernel.const _ μW with hlam
  set G : ValuesOn (Z.image SWIGNode.random) (swigΩ Ω) × ValuesOn W (swigΩ Ω)
      → ValuesOn (Z.image SWIGNode.random ∪ W) (swigΩ Ω) :=
    fun p => valuesUnionMk p.1 p.2 with hG
  have hG_meas : Measurable G := measurable_valuesUnionMk
  -- (II) obs-side bridge: `M1.obsCondKernel Y (Zr∪W) (s0, G p) = condDistrib … (G p)`, λ-a.e.
  -- (the proven obs-side AC transport, mirrored from `obsCondKernel_fixSet_eq_ae_witness`).
  have h_obs_cd := obsCondKernel_ae_eq_condDistrib M' Y (Z.image SWIGNode.random ∪ W) hY hZrW s0
  have h_obs_ae_mapG :
      (fun c => M'.obsCondKernel Y (Z.image SWIGNode.random ∪ W) hY hZrW (s0, c))
        =ᵐ[lam.map G]
        ProbabilityTheory.condDistrib (valuesProjection hY) (valuesProjection hZrW)
          (M'.obsKernel s0) :=
    MeasureTheory.Measure.AbsolutelyContinuous.ae_eq hPositivity_ae h_obs_cd
  have h_obs_prod :
      ∀ᵐ p ∂lam,
        M'.obsCondKernel Y (Z.image SWIGNode.random ∪ W) hY hZrW (s0, G p)
          = ProbabilityTheory.condDistrib (valuesProjection hY) (valuesProjection hZrW)
            (M'.obsKernel s0) (G p) :=
    MeasureTheory.ae_of_ae_map hG_meas.aemeasurable h_obs_ae_mapG
  -- (I) do-side reduction: `M2.obsCondKernel Y W (fixSetExtend s0 t, w)
  --      = M1.obsCondKernel Y (Zr∪W) (s0, G (t,w))`, λ-a.e.
  -- This is the posterior witness-kernel cross-SCM bridge
  -- `obsCondKernel_fixSet_M1_eq_ae_product`:
  -- both sides equal the posterior witness kernel
  -- `(condDistrib C_W (π_W∘E) latentProduct).map (h t w)` (`obsSide_eq_witness` + its
  -- do-side M2 mirror), lifted to the product via Rule 3 (`ν_W = μW`) + positivity.
  have h_doSide :
      ∀ᵐ p ∂lam,
        (M'.fixSet Z hZ_obs hZ_fixed).obsCondKernel Y W
            ((SCM.fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hY)
            ((SCM.fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hW)
            (M'.fixSetExtend Z hZ_obs hZ_fixed s0 p.1, p.2)
          = M'.obsCondKernel Y (Z.image SWIGNode.random ∪ W) hY hZrW (s0, G p) :=
    SCM.obsCondKernel_fixSet_M1_eq_ae_product M' Z hZ_obs hZ_fixed Y W
      hY hW hZr hZrW hDisj_ZrW hDisj_YZr hWNonDesc hWNonDescM1 hdSep s0 hPositivity_ae
  -- Chain (I) then (II).
  filter_upwards [h_doSide, h_obs_prod] with p hI hII
  rw [hI, hII]

/-- **Rule 2, a.e. in the treatment value (product form + positivity).**
    For `(νZ ⊗ₘ μW)`-a.e. pair `(t, w)` (treatment `t`, conditioning value `w`), the `W`-conditional
    of the model intervened at `t` equals the original model's `(Z.random ∪ W)`-conditional at the
    filled point `fill(t, w)`.  Positivity (`hPositivity_ae`) places the obs-side on its pinned
    support; the do-side is pinned by Rule 3 + Fubini. -/
theorem obsCondKernel_fixSet_eq_ae_witness
    (M' : Causalean.SCM N Ω) (Z : Finset N)
    (hZ_obs : ∀ D ∈ Z, SWIGNode.random D ∈ M'.observed)
    (hZ_fixed : ∀ D ∈ Z, SWIGNode.fixed D ∉ M'.fixed)
    (Y W : Finset (SWIGNode N))
    (hY : Y ⊆ M'.observed)
    (hW : W ⊆ M'.observed)
    (hZr : Z.image SWIGNode.random ⊆ M'.observed)
    (hZrW : Z.image SWIGNode.random ∪ W ⊆ M'.observed)
    (hDisj_YZr : Disjoint Y (Z.image SWIGNode.random))
    (hDisj_ZrW : Disjoint (Z.image SWIGNode.random) W)
    (hdSep : (M'.fixSet Z hZ_obs hZ_fixed).dag.dSep
      Y (Z.image SWIGNode.random)
      (W ∪ (M'.fixSet Z hZ_obs hZ_fixed).fixed))
    (hWNonDesc : ∀ z ∈ Z, ∀ v ∈ W,
      ¬ (M'.fixSet Z hZ_obs hZ_fixed).dag.isAncestor (SWIGNode.fixed z) v)
    (hWNonDescM1 : ∀ D ∈ Z, ∀ w ∈ W,
      ¬ M'.dag.isAncestor (SWIGNode.random D) w)
    [StandardBorelSpace M'.RandomValues]
    [∀ n, StandardBorelSpace (swigΩ Ω n)] [∀ n, Nonempty (swigΩ Ω n)]
    [StandardBorelSpace (M'.fixSet Z hZ_obs hZ_fixed).RandomValues]
    [StandardBorelSpace (M'.fixSet Z hZ_obs hZ_fixed).ObservedValues]
    [StandardBorelSpace (ValuesOn Y (swigΩ Ω))]
    [Nonempty (ValuesOn Y (swigΩ Ω))]
    [StandardBorelSpace
      (ValuesOn (M'.cutsetLatent Y (Z.image SWIGNode.random ∪ W)) (swigΩ Ω))]
    [Nonempty
      (ValuesOn (M'.cutsetLatent Y (Z.image SWIGNode.random ∪ W)) (swigΩ Ω))]
    [StandardBorelSpace (ValuesOn (Z.image SWIGNode.random) (swigΩ Ω))]
    [Nonempty (ValuesOn (Z.image SWIGNode.random) (swigΩ Ω))]
    [∀ s : M'.FixedValues, MeasureTheory.IsFiniteMeasure (M'.jointKernel s)]
    [∀ s : M'.FixedValues, MeasureTheory.IsFiniteMeasure (M'.obsKernel s)]
    [∀ s : (M'.fixSet Z hZ_obs hZ_fixed).FixedValues,
      MeasureTheory.IsFiniteMeasure
        ((M'.fixSet Z hZ_obs hZ_fixed).jointKernel s)]
    [∀ s : (M'.fixSet Z hZ_obs hZ_fixed).FixedValues,
      MeasureTheory.IsFiniteMeasure
        ((M'.fixSet Z hZ_obs hZ_fixed).obsKernel s)]
    [MeasurableSpace.CountableOrCountablyGenerated
      M'.FixedValues (ValuesOn (Z.image SWIGNode.random ∪ W) (swigΩ Ω))]
    [MeasurableSpace.CountableOrCountablyGenerated
      (M'.fixSet Z hZ_obs hZ_fixed).FixedValues
      (ValuesOn (Z.image SWIGNode.random ∪ W) (swigΩ Ω))]
    [MeasurableSpace.CountableOrCountablyGenerated
      (M'.fixSet Z hZ_obs hZ_fixed).FixedValues (ValuesOn W (swigΩ Ω))]
    [MeasurableSingletonClass
      (ValuesOn (Z.image SWIGNode.random ∪ W) (swigΩ Ω))]
    (s0 : M'.FixedValues)
    (hOverlap : ∀ s : (M'.fixSet Z hZ_obs hZ_fixed).FixedValues,
      Causalean.SCM.ID.Rule2JointOverlap M' Z hZ_obs hZ_fixed W hZrW s)
    (hPositivity_ae :
      (((M'.obsKernel s0).map (valuesProjection hZr) ⊗ₘ
          ProbabilityTheory.Kernel.const _
            ((M'.obsKernel s0).map (valuesProjection hW))).map
          (fun p => valuesUnionMk p.1 p.2))
        ≪ ((M'.obsKernel s0).map (valuesProjection hZrW)))
    :
    ∀ᵐ p ∂((M'.obsKernel s0).map (valuesProjection hZr) ⊗ₘ
            ProbabilityTheory.Kernel.const _
              ((M'.obsKernel s0).map (valuesProjection hW))),
      (M'.fixSet Z hZ_obs hZ_fixed).obsCondKernel Y W
          ((SCM.fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hY)
          ((SCM.fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hW)
          (M'.fixSetExtend Z hZ_obs hZ_fixed s0 p.1, p.2)
        = M'.obsCondKernel Y (Z.image SWIGNode.random ∪ W) hY hZrW
            (s0, valuesUnionMk p.1 p.2) := by
  -- Abbreviations matching the statement.
  set M2 := M'.fixSet Z hZ_obs hZ_fixed with hM2
  set sT := fun t => M'.fixSetExtend Z hZ_obs hZ_fixed s0 t with hsT
  -- Transported subset proofs for the do-model M2.
  set hY_M2 : Y ⊆ M2.observed := (SCM.fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hY with hhY_M2
  set hW_M2 : W ⊆ M2.observed := (SCM.fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hW with hhW_M2
  -- The product measure λ = νZ ⊗ₘ const μW and the fill map G.
  set νZ := (M'.obsKernel s0).map (valuesProjection hZr) with hνZ
  set μW := (M'.obsKernel s0).map (valuesProjection hW) with hμW
  set lam := νZ ⊗ₘ ProbabilityTheory.Kernel.const _ μW with hlam
  set G : ValuesOn (Z.image SWIGNode.random) (swigΩ Ω) × ValuesOn W (swigΩ Ω)
      → ValuesOn (Z.image SWIGNode.random ∪ W) (swigΩ Ω) :=
    fun p => valuesUnionMk p.1 p.2 with hG
  have hG_meas : Measurable G := measurable_valuesUnionMk
  -- Obs-side: pin M1's `obsCondKernel` to `condDistrib`, then transport from
  -- μC onto λ via positivity.
  have h_obs_cd := obsCondKernel_ae_eq_condDistrib M' Y (Z.image SWIGNode.random ∪ W) hY hZrW s0
  -- `λ.map G ≪ μC`, where `μC` is the measure `h_obs_cd` is a.e. for.
  have h_obs_ae_mapG :
      (fun c => M'.obsCondKernel Y (Z.image SWIGNode.random ∪ W) hY hZrW (s0, c))
        =ᵐ[lam.map G]
        ProbabilityTheory.condDistrib (valuesProjection hY) (valuesProjection hZrW)
          (M'.obsKernel s0) :=
    MeasureTheory.Measure.AbsolutelyContinuous.ae_eq hPositivity_ae h_obs_cd
  have h_obs_prod :
      ∀ᵐ p ∂lam,
        M'.obsCondKernel Y (Z.image SWIGNode.random ∪ W) hY hZrW (s0, G p)
          = ProbabilityTheory.condDistrib (valuesProjection hY) (valuesProjection hZrW)
            (M'.obsKernel s0) (G p) :=
    MeasureTheory.ae_of_ae_map hG_meas.aemeasurable h_obs_ae_mapG
  -- The isolated hard bridge: do-side `obsCondKernel` = obs-side `condDistrib`, joint-a.e.
  have h_bridge := condDistrib_fixSet_cross_SCM_bridge M' Z hZ_obs hZ_fixed Y W hY hW hZr hZrW
    hDisj_YZr hDisj_ZrW hdSep hWNonDesc hWNonDescM1 s0 hOverlap hPositivity_ae
  -- Assemble: do-side =[bridge] obs `condDistrib` =[obs, reversed] M1.obsCondKernel.
  filter_upwards [h_obs_prod, h_bridge] with p hobs hbr
  rw [hbr, ← hobs]
  -- See design spec §9.

end SCM
end Causalean
