/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Rule 2 — conditional-kernel a.e. helpers for filled treatment assignments

Two `obsCondKernel`-level a.e. helpers reused by the discrete
backdoor Rule-2 chain (`Rule2Kernel/DiscreteZHelpers.lean`):

* `obsCondKernel_dSep_collapse_ae` — d-sep collapse of the do-model's
  `Y | (Z.random ∪ W)`-conditional onto its `Y | W`-conditional, a.e.;
* `obsCondKernel_cross_SCM_ae_eq_on_fillZrW` — cross-SCM equality of the
  base- vs do-model conditional along the `fillZrW` filled assignment, a.e.

The continuous-`Z` rectangle identity that formerly lived here
(`obsKernel_fixSet_rect_eq`) was retired: it pinned `obsCondKernel` on the
`μ_C`-null `{Z.random = ζ_s}` slice, which is ill-posed for continuous
treatment. The sound continuous Rule 2 is the product-a.e. statement
`obsCondKernel_fixSet_eq_ae_witness` in `Rule2AE.lean`.
-/

import Causalean.SCM.Do.Rule2Kernel.WMarginal
import Causalean.Mathlib.CondDistrib
import Causalean.Mathlib.MeasurableEmbeddingExtras

/-! # Rule 2 conditional-kernel a.e. helpers

This file provides two almost-everywhere equalities of conditional kernels — a
d-separation collapse and a cross-model image comparison — consumed by the
discrete-treatment backdoor Rule-2 derivation. -/

namespace Causalean

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

namespace SCM

open scoped MeasureTheory ProbabilityTheory


-- ============================================================
-- § Helpers (hPinned-free) for the rectangle identity
-- ============================================================

/-- **D-separation collapse for the post-intervention conditional kernel.**

    Under d-separation `Y ⊥ (Z.image .random) | (W ∪ M2.fixed)` in the
    post-intervention SWIG DAG (`hdSep`), the M2 conditional kernel of `Y`
    given the larger conditioning set `C := Z.image .random ∪ W` collapses
    `((M2.obsKernel s).map π_C)`-a.e. onto the M2 conditional kernel of `Y`
    given the smaller set `W`, composed with the natural projection
    `π_W^C : ValuesOn C → ValuesOn W`:
    ```
    ∀ᵐ c ∂((M2.obsKernel s).map π_C),
      M2.obsCondKernel Y C hY hZrW (s, c) B
        = M2.obsCondKernel Y W hY hW (s, valuesProjection_W^C c) B
    ```

    **Proof sketch.**  Two-step bridge:
    1.  `globalMarkov_with_fixed` converts the d-sep hypothesis (with
        `Z_fix := (M2.fixSet …).fixed`) into the observational conditional
        independence `ObsCondIndep M2 Y (Z.image .random) W` under
        `M2.obsKernel s` (an instance of Mathlib's `CondIndepFun`).
    2.  Mathlib's `condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight`
        bridge translates `CondIndepFun` into a `condDistrib` (= condKernel)
        a.e. equality.  Specialising to the pair
        `(valuesProjection hZrW, valuesProjection hW)` gives the displayed
        a.e. equality after a `funext`-level rewrite identifying
        `(π_Zr, π_W) = π_C ∘ id` (since `W ⊆ Zr ∪ W`).

    Used by the discrete-treatment Rule 2 chain to remove the random copies of
    `Z` from the conditioning set. -/
lemma obsCondKernel_dSep_collapse_ae
    (M' : Causalean.SCM N Ω) (Z : Finset N)
    (hZ_obs : ∀ D ∈ Z, SWIGNode.random D ∈ M'.observed)
    (hZ_fixed : ∀ D ∈ Z, SWIGNode.fixed D ∉ M'.fixed)
    (Y W : Finset (SWIGNode N))
    (hY : Y ⊆ M'.observed) (hW : W ⊆ M'.observed)
    [∀ n, StandardBorelSpace (swigΩ Ω n)] [∀ n, Nonempty (swigΩ Ω n)]
    (hdSep : (M'.fixSet Z hZ_obs hZ_fixed).dag.dSep
              Y (Z.image SWIGNode.random)
              (W ∪ (M'.fixSet Z hZ_obs hZ_fixed).fixed))
    [MeasurableSpace.CountableOrCountablyGenerated
      (M'.fixSet Z hZ_obs hZ_fixed).FixedValues
      (ValuesOn (Z.image SWIGNode.random ∪ W) (swigΩ Ω))]
    [MeasurableSpace.CountableOrCountablyGenerated
      (M'.fixSet Z hZ_obs hZ_fixed).FixedValues (ValuesOn W (swigΩ Ω))]
    (s : (M'.fixSet Z hZ_obs hZ_fixed).FixedValues)
    {B : Set (ValuesOn Y (swigΩ Ω))} (hB : MeasurableSet B) :
    let hZr : Z.image SWIGNode.random ⊆ M'.observed := by
      intro v hv
      rcases Finset.mem_image.mp hv with ⟨D, hD, rfl⟩
      exact hZ_obs D hD
    let hZrW : Z.image SWIGNode.random ∪ W ⊆ M'.observed :=
      Finset.union_subset hZr hW
    ∀ᵐ c ∂((MeasureTheory.Measure.map
              (valuesProjection
                ((fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hZrW))
              ((M'.fixSet Z hZ_obs hZ_fixed).obsKernel s))),
      ((M'.fixSet Z hZ_obs hZ_fixed).obsCondKernel Y
          (Z.image SWIGNode.random ∪ W)
          ((fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hY)
          ((fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hZrW)
          (s, c)) B
        = ((M'.fixSet Z hZ_obs hZ_fixed).obsCondKernel Y W
            ((fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hY)
            ((fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hW)
            (s, valuesProjection
                (Finset.subset_union_right
                  (s₁ := Z.image SWIGNode.random) (s₂ := W)) c)) B := by
  classical
  have hZr : Z.image SWIGNode.random ⊆ M'.observed := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨D, hD, rfl⟩
    exact hZ_obs D hD
  have hZrW : Z.image SWIGNode.random ∪ W ⊆ M'.observed := Finset.union_subset hZr hW
  have hDisj_YZr : Disjoint Y (Z.image SWIGNode.random) := hdSep.1
  have hDisj_ZrW : Disjoint (Z.image SWIGNode.random) W :=
    Disjoint.mono_right Finset.subset_union_left hdSep.2.2.1
  have hDisj_YW : Disjoint Y W :=
    Disjoint.mono_right Finset.subset_union_left hdSep.2.1
  -- Abbreviations.
  let M2 := M'.fixSet Z hZ_obs hZ_fixed
  let Zr := Z.image SWIGNode.random
  let μ := M2.obsKernel s
  have hM2_def : M2 = M'.fixSet Z hZ_obs hZ_fixed := rfl
  have hZr_def : Zr = Z.image SWIGNode.random := rfl
  have hμ_def : μ = M2.obsKernel s := rfl
  have hY_M2 : Y ⊆ M2.observed := by
    rw [show M2.observed = M'.observed from fixSet_observed M' Z hZ_obs hZ_fixed]
    exact hY
  have hW_M2 : W ⊆ M2.observed := by
    rw [show M2.observed = M'.observed from fixSet_observed M' Z hZ_obs hZ_fixed]
    exact hW
  have hZrW_M2 : Zr ∪ W ⊆ M2.observed := by
    rw [show M2.observed = M'.observed from fixSet_observed M' Z hZ_obs hZ_fixed]
    exact hZrW
  have hZr_M2 : Zr ⊆ M2.observed := Finset.subset_union_left.trans hZrW_M2
  -- Projection abbreviations.
  let π_Y := valuesProjection (Ω := swigΩ Ω) hY_M2
  let π_W := valuesProjection (Ω := swigΩ Ω) hW_M2
  let π_Zr := valuesProjection (Ω := swigΩ Ω) hZr_M2
  let π_C := valuesProjection (Ω := swigΩ Ω) hZrW_M2
  have hπY_def : π_Y = valuesProjection (Ω := swigΩ Ω) hY_M2 := rfl
  have hπW_def : π_W = valuesProjection (Ω := swigΩ Ω) hW_M2 := rfl
  have hπZr_def : π_Zr = valuesProjection (Ω := swigΩ Ω) hZr_M2 := rfl
  have hπC_def : π_C = valuesProjection (Ω := swigΩ Ω) hZrW_M2 := rfl
  -- (i) globalMarkov_with_fixed (with Z_fix := M2.fixed) converts the
  -- d-sep hypothesis into observational conditional independence.
  have hCI : ObsCondIndep M2 Y Zr W hY_M2 hZr_M2 hW_M2 μ :=
    globalMarkov_with_fixed M2 Y Zr W M2.fixed hY_M2 hZr_M2 hW_M2
      (Finset.Subset.refl _) hdSep s
  -- (ii) Symmetrize and apply Mathlib's `condIndepFun_iff_condDistrib_…`.
  have hπY_meas : Measurable π_Y := measurable_valuesProjection _
  have hπW_meas : Measurable π_W := measurable_valuesProjection _
  have hπZr_meas : Measurable π_Zr := measurable_valuesProjection _
  have hπC_meas : Measurable π_C := measurable_valuesProjection _
  have hMathlib :
      (fun ω => ProbabilityTheory.condDistrib π_Y
          (fun ω' => (π_W ω', π_Zr ω')) μ ω)
        =ᵐ[MeasureTheory.Measure.map
              (fun ω' => (π_W ω', π_Zr ω')) μ]
          (fun ω => (ProbabilityTheory.Kernel.prodMkRight
              (ValuesOn Zr (swigΩ Ω))
              (ProbabilityTheory.condDistrib π_Y π_W μ)) ω) :=
    (ProbabilityTheory.condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight
       (f := π_Y) (g := π_Zr) hπY_meas hπZr_meas hπW_meas).mp hCI.symm
  -- (iii) Measurable equivalence `e : ValuesOn (Zr ∪ W) ≃ᵐ ValuesOn W × ValuesOn Zr`
  -- via `valuesUnionEquiv` (giving `ValZr × ValW`) composed with `prodComm`.
  let e : ValuesOn (Zr ∪ W) (swigΩ Ω) ≃ᵐ
      ValuesOn W (swigΩ Ω) × ValuesOn Zr (swigΩ Ω) :=
    (valuesUnionEquiv (A := Zr) (B := W) hDisj_ZrW).trans
      (MeasurableEquiv.prodComm (α := ValuesOn Zr (swigΩ Ω))
        (β := ValuesOn W (swigΩ Ω)))
  have he_def : e = (valuesUnionEquiv (A := Zr) (B := W) hDisj_ZrW).trans
      (MeasurableEquiv.prodComm (α := ValuesOn Zr (swigΩ Ω))
        (β := ValuesOn W (swigΩ Ω))) := rfl
  -- Pointwise: `e ∘ π_C = (π_W, π_Zr)` (both compute via valuesProjection of
  -- subsets of `Zr ∪ W`).
  have hW_sub : W ⊆ Zr ∪ W := Finset.subset_union_right
  have hZr_sub : Zr ⊆ Zr ∪ W := Finset.subset_union_left
  have h_e_comp : (fun ω => e (π_C ω)) = fun ω => (π_W ω, π_Zr ω) := by
    funext ω
    -- `e := (valuesUnionEquiv hDisj_ZrW).trans prodComm` gives at `π_C ω`:
    --   `prodComm (valuesProjection subset_union_left (π_C ω),
    --              valuesProjection subset_union_right (π_C ω))`
    -- = `(valuesProjection subset_union_right (π_C ω),
    --     valuesProjection subset_union_left (π_C ω))`.
    -- Reduce LHS to the explicit pair form, then rewrite each coord.
    have e_left :
        valuesProjection hW_sub (π_C ω) = π_W ω := by
      rw [hπW_def, hπC_def]
      exact congrFun (valuesProjection_comp hW_sub hZrW_M2).symm ω
    have e_right :
        valuesProjection hZr_sub (π_C ω) = π_Zr ω := by
      rw [hπZr_def, hπC_def]
      exact congrFun (valuesProjection_comp hZr_sub hZrW_M2).symm ω
    -- Both sides are pairs; use `Prod.ext` and pointwise.
    apply Prod.ext
    · -- `(e (π_C ω)).1 = π_W ω`
      show valuesProjection hW_sub (π_C ω) = π_W ω
      exact e_left
    · show valuesProjection hZr_sub (π_C ω) = π_Zr ω
      exact e_right
  -- (iv) Use the change-of-variable lemma to transport `hMathlib` from
  -- `μ.map (π_W, π_Zr)` ≡ `μ.map (e ∘ π_C)` to `μ.map π_C`-a.e.
  have h_e_pi_C : ⇑e ∘ π_C = fun ω => (π_W ω, π_Zr ω) := by
    funext ω; exact congrFun h_e_comp ω
  -- Rewrite `μ.map (π_W, π_Zr)` to `μ.map (e ∘ π_C)`.
  have hmap_eq :
      MeasureTheory.Measure.map (fun ω => (π_W ω, π_Zr ω)) μ
        = MeasureTheory.Measure.map (⇑e ∘ π_C) μ := by
    rw [h_e_pi_C]
  -- Apply the (C) helper: condDistrib π_Y (e ∘ π_C) μ (e c) = condDistrib π_Y π_C μ c
  -- a.e. in c under μ.map π_C.
  have h_cov : ∀ᵐ c ∂(μ.map π_C),
      ProbabilityTheory.condDistrib π_Y (⇑e ∘ π_C) μ (e c)
        = ProbabilityTheory.condDistrib π_Y π_C μ c :=
    condDistrib_comp_right_measurableEquiv μ e hπY_meas hπC_meas
  -- Transport `hMathlib` via `ae_of_ae_map` for `e`.
  -- Step: `hMathlib` is ae on `μ.map (e ∘ π_C) = (μ.map π_C).map e`.
  have hMathlib' :
      (fun b => ProbabilityTheory.condDistrib π_Y
          (fun ω' => (π_W ω', π_Zr ω')) μ b)
        =ᵐ[MeasureTheory.Measure.map (⇑e ∘ π_C) μ]
          (fun b => (ProbabilityTheory.Kernel.prodMkRight
              (ValuesOn Zr (swigΩ Ω))
              (ProbabilityTheory.condDistrib π_Y π_W μ)) b) := by
    rw [← hmap_eq]; exact hMathlib
  have hmap_compose : MeasureTheory.Measure.map (⇑e ∘ π_C) μ
      = MeasureTheory.Measure.map ⇑e (μ.map π_C) :=
    (MeasureTheory.Measure.map_map e.measurable hπC_meas).symm
  rw [hmap_compose] at hMathlib'
  have hMathlib_pulled :
      ∀ᵐ c ∂(μ.map π_C),
        ProbabilityTheory.condDistrib π_Y
            (fun ω' => (π_W ω', π_Zr ω')) μ (e c)
          = (ProbabilityTheory.Kernel.prodMkRight
              (ValuesOn Zr (swigΩ Ω))
              (ProbabilityTheory.condDistrib π_Y π_W μ)) (e c) :=
    MeasureTheory.ae_of_ae_map (μ := μ.map π_C) (f := ⇑e)
      e.measurable.aemeasurable hMathlib'
  -- (v) Bridge `condDistrib` back to `obsCondKernel` via
  -- `obsCondKernel_ae_eq_condDistrib`, twice.
  have h_bridge_C :
      (fun c => M2.obsCondKernel Y (Zr ∪ W) hY_M2 hZrW_M2 (s, c))
        =ᵐ[μ.map π_C]
          ProbabilityTheory.condDistrib π_Y π_C μ :=
    obsCondKernel_ae_eq_condDistrib M2 Y (Zr ∪ W) hY_M2 hZrW_M2 s
  have h_bridge_W :
      (fun w => M2.obsCondKernel Y W hY_M2 hW_M2 (s, w))
        =ᵐ[μ.map π_W]
          ProbabilityTheory.condDistrib π_Y π_W μ :=
    obsCondKernel_ae_eq_condDistrib M2 Y W hY_M2 hW_M2 s
  -- (vi) The RHS-side bridge transports `h_bridge_W` from `μ.map π_W`-a.e.
  -- to `μ.map π_C`-a.e. via the projection `π_W^C : ValC → ValW`.
  -- Note: `μ.map π_W = (μ.map π_C).map π_W^C` because `π_W = π_W^C ∘ π_C`.
  let π_W_C : ValuesOn (Zr ∪ W) (swigΩ Ω) → ValuesOn W (swigΩ Ω) :=
    valuesProjection hW_sub
  have hπW_C_def : π_W_C = valuesProjection (Ω := swigΩ Ω) hW_sub := rfl
  have hπW_C_meas : Measurable π_W_C := measurable_valuesProjection _
  have hπW_factor : π_W = π_W_C ∘ π_C := by
    rw [hπW_def, hπW_C_def, hπC_def]
    exact valuesProjection_comp hW_sub hZrW_M2
  have hmap_W_via_C :
      μ.map π_W = (μ.map π_C).map π_W_C := by
    rw [hπW_factor, ← MeasureTheory.Measure.map_map hπW_C_meas hπC_meas]
  rw [hmap_W_via_C] at h_bridge_W
  have h_bridge_W_pulled :
      ∀ᵐ c ∂(μ.map π_C),
        M2.obsCondKernel Y W hY_M2 hW_M2 (s, π_W_C c)
          = ProbabilityTheory.condDistrib π_Y π_W μ (π_W_C c) :=
    MeasureTheory.ae_of_ae_map (μ := μ.map π_C) (f := π_W_C)
      hπW_C_meas.aemeasurable h_bridge_W
  -- (vii) Combine all ae statements and conclude.
  filter_upwards [h_bridge_C, hMathlib_pulled, h_cov, h_bridge_W_pulled]
    with c hbC hMl hcov hbW
  -- Goal: M2.obsCondKernel Y (Zr ∪ W) (s, c) B
  --     = M2.obsCondKernel Y W (s, π_W_C c) B
  -- where π_W_C uses `subset_union_right`.
  rw [hbC]
  -- Now LHS: condDistrib π_Y π_C μ c B
  rw [← hcov]
  -- Now LHS: condDistrib π_Y (e ∘ π_C) μ (e c) B
  -- but we have `hMl` for `condDistrib π_Y (π_W, π_Zr) μ`.  Use h_e_pi_C.
  have h_e_pi_C' : ProbabilityTheory.condDistrib π_Y (⇑e ∘ π_C) μ
      = ProbabilityTheory.condDistrib π_Y (fun ω' => (π_W ω', π_Zr ω')) μ := by
    rw [h_e_pi_C]
  rw [h_e_pi_C']
  rw [hMl]
  -- Now LHS: (Kernel.prodMkRight _ (condDistrib π_Y π_W μ)) (e c) B
  -- which is `condDistrib π_Y π_W μ ((e c).1) B = condDistrib π_Y π_W μ (π_W_C c) B`.
  rw [ProbabilityTheory.Kernel.prodMkRight_apply]
  -- LHS: condDistrib π_Y π_W μ (e c).1 B
  -- (e c).1 = (prodComm (valuesUnionEquiv hDisj_ZrW c)).1
  --        = (valuesUnionEquiv hDisj_ZrW c).2 = valuesProjection (subset_union_right) c
  --        = π_W_C c
  have h_e_fst : (e c).1 = π_W_C c := by
    -- `e c = prodComm (valuesUnionEquiv hDisj_ZrW c)`,
    -- where `valuesUnionEquiv` returns `(vP subset_union_left c, vP subset_union_right c)`,
    -- so `prodComm` swaps to `(vP subset_union_right c, vP subset_union_left c)`,
    -- and `.1 = vP subset_union_right c = π_W_C c` by `hπW_C_def`.
    show valuesProjection hW_sub c = π_W_C c
    rw [hπW_C_def]
  rw [h_e_fst]
  rw [← hbW]
/-- **Cross-SCM conditional kernels agree along the `fillZrW` filled assignment.**

    The base-model conditional kernel evaluated along
    `F w := fillZrW W s w` agrees almost everywhere with the do-model
    conditional kernel evaluated at the same filled treatment-random-copy and W
    coordinates.  The almost-everywhere measure is the pullback of the
    base-model law on `Z.random ∪ W` through `F`; the statement also carries the
    Rule 2 joint-overlap hypothesis required by its public API.

    More precisely, if we let
    `μ_C^{M1} := (M1.obsKernel sM1).map π_C` and let
    `μ_F := μ_C^{M1}.comap F` be its pullback under the measurable
    embedding `F`, then
    ```
    ∀ᵐ w ∂μ_F,
      M1.obsCondKernel Y C (sM1, F w) B
        = M2.obsCondKernel Y C (s, F w) B
    ```

    **Proof sketch.**  By
    `obsKernel_inter_Wset_Zrand_levelset_eq` (with `S := π_Y⁻¹ B`), the M2
    and M1 measures of `π_Y⁻¹ B ∩ π_C⁻¹ (F''A_W)` coincide for every
    measurable `A_W ⊆ ValuesOn W`.  Applying M1's disintegration to the
    M1 side and M2's disintegration to the M2 side rewrites both as
    `∫_{F''A_W}` integrals against `μ_C^{M1}` and `ν_C^{M2}` respectively.
    The cross-SCM bridge with `S := univ` (= `obsKernel_inter_Wset_…` with
    `S := univ` integrated) further shows `μ_C^{M1}` and `ν_C^{M2}` agree
    on every cylinder generated by the filled assignment, so they coincide as
    measures on `range F`.  Therefore the two integrals are with respect to the same
    measure on `range F`, and by a.e. equality of integrals on the
    π-system of these cylinders we obtain
    `M1.obsCondKernel Y C (sM1, c) B = M2.obsCondKernel Y C (s, c) B`
    for `μ_C^{M1}|_{range F}`-a.e. `c`.  Pull back via the measurable
    embedding `F` to obtain the displayed a.e. equality on `μ_F`.

    Used by the discrete-treatment Rule 2 chain to compare the original and
    post-intervention conditional kernels at filled assignments. -/
lemma obsCondKernel_cross_SCM_ae_eq_on_fillZrW
    (M' : Causalean.SCM N Ω) (Z : Finset N)
    (hZ_obs : ∀ D ∈ Z, SWIGNode.random D ∈ M'.observed)
    (hZ_fixed : ∀ D ∈ Z, SWIGNode.fixed D ∉ M'.fixed)
    (Y W : Finset (SWIGNode N))
    (hY : Y ⊆ M'.observed) (hW : W ⊆ M'.observed)
    (hZrW : Z.image SWIGNode.random ∪ W ⊆ M'.observed)
    (hDisj_ZrW : Disjoint (Z.image SWIGNode.random) W)
    [StandardBorelSpace (ValuesOn Y (swigΩ Ω))]
    [Nonempty (ValuesOn Y (swigΩ Ω))]
    [MeasurableSpace.CountableOrCountablyGenerated
      M'.FixedValues (ValuesOn (Z.image SWIGNode.random ∪ W) (swigΩ Ω))]
    [MeasurableSpace.CountableOrCountablyGenerated
      (M'.fixSet Z hZ_obs hZ_fixed).FixedValues
      (ValuesOn (Z.image SWIGNode.random ∪ W) (swigΩ Ω))]
    [MeasurableSingletonClass
      (ValuesOn (Z.image SWIGNode.random ∪ W) (swigΩ Ω))]
    (s : (M'.fixSet Z hZ_obs hZ_fixed).FixedValues)
    {B : Set (ValuesOn Y (swigΩ Ω))} (hB : MeasurableSet B) :
    ∀ᵐ w ∂((MeasureTheory.Measure.map (valuesProjection hZrW)
              (M'.obsKernel (M'.fixSetProj Z hZ_obs hZ_fixed s))).comap
            (M'.fillZrW Z hZ_obs hZ_fixed W s)),
      (M'.obsCondKernel Y (Z.image SWIGNode.random ∪ W) hY hZrW
        (M'.fixSetProj Z hZ_obs hZ_fixed s,
         M'.fillZrW Z hZ_obs hZ_fixed W s w)) B
      = ((M'.fixSet Z hZ_obs hZ_fixed).obsCondKernel Y
          (Z.image SWIGNode.random ∪ W)
          ((fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hY)
          ((fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hZrW)
          (s, M'.fillZrW Z hZ_obs hZ_fixed W s w)) B := by
  -- Proof skeleton for the rectangle identity. The measure-uniqueness bridge
  -- is packaged in the helper lemmas below; this block keeps the notation
  -- aligned with the obs-side and do-side kernels.
  --
  -- Notation.
  --   M1     := M',
  --   M2     := M'.fixSet Z _ _,
  --   sM1    := M'.fixSetProj Z _ _ s,
  --   F      := M'.fillZrW Z _ _ W s,
  --   C      := Z.image .random ∪ W,
  --   μ_C    := (M1.obsKernel sM1).map π_C       (M1 marginal on C)
  --   ν_C    := (M2.obsKernel s ).map π_C       (M2 marginal on C)
  --   μ_F    := μ_C.comap F                     (pullback via the
  --                                              measurable embedding F)
  --   f1 w   := M1.obsCondKernel Y C (sM1, F w) B,
  --   f2 w   := M2.obsCondKernel Y C (s , F w) B.
  --
  -- We want `f1 =ᵐ[μ_F] f2`.  By
  -- `MeasureTheory.ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite` it
  -- suffices to check, for every measurable `A ⊆ ValuesOn W`,
  --
  --     ∫_A f1 dμ_F = ∫_A f2 dμ_F.                                    (★)
  --
  -- Reducing both sides to the rectangle measure
  -- `M.obsKernel _ (π_C⁻¹ F''A ∩ π_Y⁻¹ B)`:
  --
  -- LHS (★) chain.
  --   ∫_A f1 dμ_F
  --     = ∫_{F''A} g1 c dμ_C                     [MeasurableEmbedding.comap +
  --                                               `lintegral_indicator`,
  --                                               restriction along F]
  --     = M1.obsKernel sM1 (π_C⁻¹ F''A ∩ π_Y⁻¹ B)
  --                                              [`obsKernel_disintegrate_rect`
  --                                               with `M := M1`, `D := F''A`]
  --     = M2.obsKernel s  (π_C⁻¹ F''A ∩ π_Y⁻¹ B)
  --                                              [`obsKernel_inter_Wset_Zrand_levelset_eq`
  --                                               with `S := π_Y⁻¹ B`]
  --
  -- RHS (★) chain.
  --   ∫_A f2 dμ_F
  --     = ∫_{F''A} g2 c dμ_C|_{range F}          [same comap rewrite]
  --     = ∫_{F''A} g2 c dν_C                     [restricted range measure equality]
  --     = M2.obsKernel s (π_C⁻¹ F''A ∩ π_Y⁻¹ B)  [`obsKernel_disintegrate_rect`
  --                                               with `M := M2`]
  --
  -- The two chains coincide exactly after proving the restricted range equality
  --
  --     μ_C |_{range F}  =  ν_C |_{range F}   as measures on range F,    (♭)
  --
  -- holds.  The π-system of filled-assignment cylinders `{ F''A_W : A_W meas }`
  -- generates the trace σ-algebra on range F, and
  -- `obsKernel_inter_Wset_Zrand_levelset_eq` with `S := univ` shows the
  -- two measures agree on each such cylinder; promoting this to a full
  -- The proof splits into the measure equality on `range F` and the
  -- disintegration-uniqueness step on that range. The helper infrastructure
  -- below packages the measurable-embedding and restricted-measure facts used
  -- in those two steps.
  classical
  let M2 := M'.fixSet Z hZ_obs hZ_fixed
  let sM1 : M'.FixedValues := M'.fixSetProj Z hZ_obs hZ_fixed s
  let Zr := Z.image SWIGNode.random
  let F := M'.fillZrW Z hZ_obs hZ_fixed W s
  have hM2_def : M2 = M'.fixSet Z hZ_obs hZ_fixed := rfl
  have hsM1_def : sM1 = M'.fixSetProj Z hZ_obs hZ_fixed s := rfl
  have hZr_def : Zr = Z.image SWIGNode.random := rfl
  have hF_def : F = M'.fillZrW Z hZ_obs hZ_fixed W s := rfl
  have hZrW_M2 : Zr ∪ W ⊆ M2.observed :=
    (fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hZrW
  -- F is a measurable embedding.
  have hF_emb : MeasurableEmbedding F :=
    measurableEmbedding_fillZrW M' Z hZ_obs hZ_fixed W hDisj_ZrW s
  -- μ_C and ν_C: M1 and M2 marginal pushforwards on C := Zr ∪ W.
  let μ_C : MeasureTheory.Measure (ValuesOn (Zr ∪ W) (swigΩ Ω)) :=
    (M'.obsKernel sM1).map (valuesProjection hZrW)
  let ν_C : MeasureTheory.Measure (ValuesOn (Zr ∪ W) (swigΩ Ω)) :=
    (M2.obsKernel s).map (valuesProjection hZrW_M2)
  have hμC_def : μ_C =
      (M'.obsKernel sM1).map (valuesProjection (Ω := swigΩ Ω) hZrW) := rfl
  have hνC_def : ν_C =
      (M2.obsKernel s).map (valuesProjection (Ω := swigΩ Ω) hZrW_M2) := rfl
  -- Both μ_C and ν_C are finite (pushforwards of finite measures).
  have hπC_M1_meas : Measurable (valuesProjection (Ω := swigΩ Ω) hZrW) :=
    measurable_valuesProjection _
  have hπC_M2_meas : Measurable (valuesProjection (Ω := swigΩ Ω) hZrW_M2) :=
    measurable_valuesProjection _
  haveI : MeasureTheory.IsFiniteMeasure μ_C := by
    rw [hμC_def]; exact (M'.obsKernel sM1).isFiniteMeasure_map _
  haveI : MeasureTheory.IsFiniteMeasure ν_C := by
    rw [hνC_def]; exact (M2.obsKernel s).isFiniteMeasure_map _
  ----------------------------------------------------------------
  -- **Part A** : `μ_C.restrict (range F) = ν_C.restrict (range F)`.
  ----------------------------------------------------------------
  have hPartA :
      μ_C.restrict (Set.range F) = ν_C.restrict (Set.range F) := by
    refine
      MeasureTheory.restrict_range_eq_of_forall_image hF_emb μ_C ν_C
        ?_
    intro A hA
    -- ν_C (F''A) = M2.obsKernel s (π_C^{M2}⁻¹(F''A))
    -- μ_C (F''A) = M1.obsKernel sM1 (π_C^{M1}⁻¹(F''A))
    -- The cross-SCM cylinder bridge with `S := univ` gives equality.
    have hImg_meas : MeasurableSet (F '' A) := hF_emb.measurableSet_image' hA
    have hMap_M1 :
        μ_C (F '' A)
          = M'.obsKernel sM1
              ((valuesProjection hZrW)⁻¹' (F '' A)) := by
      rw [hμC_def, MeasureTheory.Measure.map_apply hπC_M1_meas hImg_meas]
    have hMap_M2 :
        ν_C (F '' A)
          = M2.obsKernel s
              ((valuesProjection hZrW_M2)⁻¹' (F '' A)) := by
      rw [hνC_def, MeasureTheory.Measure.map_apply hπC_M2_meas hImg_meas]
    -- Cross-SCM bridge with S := univ.
    have hBridge :
        M2.obsKernel s
            (Set.univ ∩ (valuesProjection hZrW_M2)⁻¹' (F '' A))
          = M'.obsKernel sM1
              (Set.univ ∩ (valuesProjection hZrW)⁻¹' (F '' A)) :=
      obsKernel_inter_Wset_Zrand_levelset_eq M' Z hZ_obs hZ_fixed W
        hZrW hDisj_ZrW s MeasurableSet.univ hA
    rw [Set.univ_inter, Set.univ_inter] at hBridge
    rw [hMap_M1, hMap_M2, hBridge]
  ----------------------------------------------------------------
  -- **Part B** : disintegration uniqueness on `range F`.
  --
  -- From `hPartA`, the M1 and M2 joint measures agree on every set of
  -- the form `π_C⁻¹ E ∩ π_Y⁻¹ B` for measurable `E ⊆ range F`.  Their
  -- disintegrations along `π_C` (via `obsKernel_disintegrate_rect`)
  -- coincide as the same conditional kernel up to a μ_C|_{range F}-null
  -- set.  Concretely, for every measurable `E ⊆ ValuesOn (Zr ∪ W)`:
  --
  --     ∫⁻ c in E ∩ range F, M1.obsCondKernel Y C (sM1, c) B dμ_C
  --       = M1.obsKernel sM1 (π_C⁻¹ (E ∩ range F) ∩ π_Y⁻¹ B)
  --       = M2.obsKernel s   (π_C⁻¹ (E ∩ range F) ∩ π_Y⁻¹ B)     -- bridge
  --       = ∫⁻ c in E ∩ range F, M2.obsCondKernel Y C (s, c) B dν_C
  --       = ∫⁻ c in E ∩ range F, M2.obsCondKernel Y C (s, c) B dμ_C
  --                                                      -- via Part A
  --
  -- Apply `MeasureTheory.ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite`
  -- to `g1 c := M1.obsCondKernel Y C (sM1, c) B` and
  -- `g2 c := M2.obsCondKernel Y C (s, c) B` on `μ_C.restrict (range F)`.
  -- Then transport `g1 ∘ F =ᵐ[μ_F] g2 ∘ F` from
  -- `g1 =ᵐ[μ_C.restrict (range F)] g2` via
  -- `MeasurableEmbedding.ae_map_iff` and `hF_emb.map_comap`.
  --
  ----------------------------------------------------------------
  -- **Part B** : disintegration uniqueness on `range F`.
  ----------------------------------------------------------------
  -- M2-side `Y ⊆ M2.observed`.
  have hY_M2 : Y ⊆ M2.observed :=
    (fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hY
  -- Measurability of the π_Y-preimage of B on both sides.
  have hπY_M1_meas : Measurable (valuesProjection (Ω := swigΩ Ω) hY) :=
    measurable_valuesProjection _
  have hπY_M2_meas : Measurable (valuesProjection (Ω := swigΩ Ω) hY_M2) :=
    measurable_valuesProjection _
  have hπYB_M1 : MeasurableSet ((valuesProjection (Ω := swigΩ Ω) hY)⁻¹' B) :=
    hπY_M1_meas hB
  have hπYB_M2 : MeasurableSet ((valuesProjection (Ω := swigΩ Ω) hY_M2)⁻¹' B) :=
    hπY_M2_meas hB
  -- The integrand functions `f1`, `f2` (M1 and M2 conditional kernels at B).
  let f1 : ValuesOn (Zr ∪ W) (swigΩ Ω) → ENNReal :=
    fun c => M'.obsCondKernel Y (Zr ∪ W) hY hZrW (sM1, c) B
  let f2 : ValuesOn (Zr ∪ W) (swigΩ Ω) → ENNReal :=
    fun c => M2.obsCondKernel Y (Zr ∪ W) hY_M2 hZrW_M2 (s, c) B
  have hf1_meas : Measurable f1 :=
    (ProbabilityTheory.Kernel.measurable_coe _ hB).comp
      (Measurable.prodMk measurable_const measurable_id)
  have hf2_meas : Measurable f2 :=
    (ProbabilityTheory.Kernel.measurable_coe _ hB).comp
      (Measurable.prodMk measurable_const measurable_id)
  -- **Step 1.** For every measurable `A ⊆ ValuesOn W`,
  -- `∫_{F''A} f1 dμ_C = ∫_{F''A} f2 dμ_C`.
  have hStep1 : ∀ A, MeasurableSet A →
      ∫⁻ c in F '' A, f1 c ∂μ_C = ∫⁻ c in F '' A, f2 c ∂μ_C := by
    intro A hA
    have hImg_meas : MeasurableSet (F '' A) := hF_emb.measurableSet_image' hA
    -- M1 disintegration: ∫_{F''A} f1 dμ_C = M1.obsKernel sM1 (π_C⁻¹(F''A) ∩ π_Y⁻¹B).
    have hM1 :
        ∫⁻ c in F '' A, f1 c ∂μ_C
          = M'.obsKernel sM1
              ((valuesProjection hZrW)⁻¹' (F '' A)
                ∩ (valuesProjection hY)⁻¹' B) := by
      show ∫⁻ c in F '' A, f1 c
              ∂((M'.obsKernel sM1).map (valuesProjection hZrW)) = _
      exact (obsKernel_disintegrate_rect M' Y (Zr ∪ W) hY hZrW sM1
              hImg_meas hB).symm
    -- M2 disintegration: ∫_{F''A} f2 dν_C = M2.obsKernel s (π_C⁻¹(F''A) ∩ π_Y⁻¹B).
    have hM2_ν :
        ∫⁻ c in F '' A, f2 c ∂ν_C
          = M2.obsKernel s
              ((valuesProjection hZrW_M2)⁻¹' (F '' A)
                ∩ (valuesProjection hY_M2)⁻¹' B) := by
      show ∫⁻ c in F '' A, f2 c
              ∂((M2.obsKernel s).map (valuesProjection hZrW_M2)) = _
      exact (obsKernel_disintegrate_rect M2 Y (Zr ∪ W) hY_M2 hZrW_M2 s
              hImg_meas hB).symm
    -- Cross-SCM cylinder bridge with `S := π_Y⁻¹ B`.
    have hBridge :
        M2.obsKernel s
            ((valuesProjection hY_M2)⁻¹' B
              ∩ (valuesProjection hZrW_M2)⁻¹' (F '' A))
          = M'.obsKernel sM1
              ((valuesProjection hY)⁻¹' B
                ∩ (valuesProjection hZrW)⁻¹' (F '' A)) :=
      obsKernel_inter_Wset_Zrand_levelset_eq M' Z hZ_obs hZ_fixed W
        hZrW hDisj_ZrW s hπYB_M2 hA
    -- Reorder the intersections to match the disintegration form.
    have hM1_eq_M2 :
        M'.obsKernel sM1
            ((valuesProjection hZrW)⁻¹' (F '' A)
              ∩ (valuesProjection hY)⁻¹' B)
          = M2.obsKernel s
              ((valuesProjection hZrW_M2)⁻¹' (F '' A)
                ∩ (valuesProjection hY_M2)⁻¹' B) := by
      rw [Set.inter_comm ((valuesProjection hZrW)⁻¹' (F '' A)),
          Set.inter_comm ((valuesProjection hZrW_M2)⁻¹' (F '' A))]
      exact hBridge.symm
    -- `μ_C` and `ν_C` agree when restricted to `F '' A ⊆ range F` (Part A).
    have hFA_sub : F '' A ⊆ Set.range F := Set.image_subset_range _ _
    have hRestr_eq :
        μ_C.restrict (F '' A) = ν_C.restrict (F '' A) := by
      calc μ_C.restrict (F '' A)
          = (μ_C.restrict (Set.range F)).restrict (F '' A) := by
                rw [MeasureTheory.Measure.restrict_restrict_of_subset hFA_sub]
        _ = (ν_C.restrict (Set.range F)).restrict (F '' A) := by rw [hPartA]
        _ = ν_C.restrict (F '' A) := by
                rw [MeasureTheory.Measure.restrict_restrict_of_subset hFA_sub]
    -- Switch the M2-side integral measure from `ν_C` to `μ_C`.
    have hM2_μ :
        ∫⁻ c in F '' A, f2 c ∂μ_C
          = M2.obsKernel s
              ((valuesProjection hZrW_M2)⁻¹' (F '' A)
                ∩ (valuesProjection hY_M2)⁻¹' B) := by
      show ∫⁻ c, f2 c ∂(μ_C.restrict (F '' A)) = _
      rw [hRestr_eq]; exact hM2_ν
    rw [hM1, hM1_eq_M2, ← hM2_μ]
  -- **Step 2.** `f1 =ᵐ[μ_C.restrict (range F)] f2` via setLIntegral uniqueness.
  haveI : MeasureTheory.IsFiniteMeasure (μ_C.restrict (Set.range F)) :=
    inferInstance
  have hAE_restrict :
      f1 =ᵐ[μ_C.restrict (Set.range F)] f2 := by
    refine MeasureTheory.ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite
      hf1_meas hf2_meas ?_
    intro E hE _
    have hFinvE_meas : MeasurableSet (F ⁻¹' E) := hF_emb.measurable hE
    -- E ∩ range F = F '' (F ⁻¹' E)  (since F is injective).
    have hImg_eq : E ∩ Set.range F = F '' (F ⁻¹' E) := by
      rw [Set.image_preimage_eq_inter_range]
    -- Reduce `∫_E _ d(μ_C.restrict (range F))` to `∫_{E ∩ range F} _ dμ_C`.
    have h_rew_f1 :
        ∫⁻ c in E, f1 c ∂(μ_C.restrict (Set.range F))
          = ∫⁻ c in E ∩ Set.range F, f1 c ∂μ_C := by
      show ∫⁻ c, f1 c ∂((μ_C.restrict (Set.range F)).restrict E)
            = ∫⁻ c, f1 c ∂(μ_C.restrict (E ∩ Set.range F))
      rw [MeasureTheory.Measure.restrict_restrict' hF_emb.measurableSet_range]
    have h_rew_f2 :
        ∫⁻ c in E, f2 c ∂(μ_C.restrict (Set.range F))
          = ∫⁻ c in E ∩ Set.range F, f2 c ∂μ_C := by
      show ∫⁻ c, f2 c ∂((μ_C.restrict (Set.range F)).restrict E)
            = ∫⁻ c, f2 c ∂(μ_C.restrict (E ∩ Set.range F))
      rw [MeasureTheory.Measure.restrict_restrict' hF_emb.measurableSet_range]
    rw [h_rew_f1, h_rew_f2, hImg_eq]
    exact hStep1 (F ⁻¹' E) hFinvE_meas
  -- **Step 3.** Transport to `∀ᵐ w ∂(μ_C.comap F), f1 (F w) = f2 (F w)`.
  have h_map_comap :
      (μ_C.comap F).map F = μ_C.restrict (Set.range F) :=
    hF_emb.map_comap μ_C
  have hAE_map : ∀ᵐ c ∂((μ_C.comap F).map F), f1 c = f2 c := by
    rw [h_map_comap]; exact hAE_restrict
  exact (hF_emb.ae_map_iff (μ := μ_C.comap F)
          (p := fun c => f1 c = f2 c)).mp hAE_map

end SCM

end Causalean
