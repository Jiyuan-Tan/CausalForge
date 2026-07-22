/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Rule 2 — Discrete-Z helpers (Pearl/SWIG backdoor identification surface)

This file contains the discrete-treatment branch of the Rule 2 kernel proof. It
uses the Pearl/SWIG backdoor condition for `W`, a joint overlap hypothesis, and a
positivity hypothesis to compare the post-intervention `Y | W` kernel with the
pre-intervention `Y | (Z.random ∪ W)` kernel at the filled assignment
`fillZrW`.

The key public declarations are:

* `obsKernel_fixSet_W_marginal_eq_M1_marginal`, the Rule 3 `W`-marginal equality.
* `mu_C_comap_F_eq_nu_C_comap_F`, the cross-SCM pullback equality along
  `fillZrW`.
* `obsCondKernel_cross_eq_ae_of_discrete`, the discrete-treatment conditional
  kernel bridge.

## Discrete-Z typeclass

The discrete-Z scope is signalled by
  `[∀ z : {z // z ∈ Z}, Countable (swigΩ Ω (SWIGNode.random z.val))]`,
combined with the standing `MeasurableSingletonClass (ValuesOn (Zr ∪ W) _)`.
This is the regime in which the canonical pointwise `obsCondKernel` is
well-defined on positive-mass atoms, supporting the rectangle identity's
final disintegration step.

## Continuous-treatment support

For non-atomic treatment values, pointwise conditioning at a single filled
`Z.random` value is not well posed for an arbitrary regular conditional
kernel.  The continuous-treatment Rule 2 statement therefore lives in
`Rule2AE.lean`, where equality is stated almost everywhere over the product of
the treatment and adjustment marginals.  The structural pointwise facts in
`Rule2Kernel/Structural/` supply the `fillZrW` evaluation equalities consumed by
that product-a.e. proof.
-/

import Causalean.SCM.Do.Rule2Kernel.RectIdentity
import Causalean.SCM.Do.Rule3
import Causalean.Mathlib.MeasurableEmbeddingExtras

/-! # Discrete Treatment Helpers for Rule 2

This file provides the discrete-treatment measure-theoretic helpers used to state
Pearl's action-observation exchange without requiring the post-intervention
treatment coordinate to be almost surely pinned. It proves the `W`-marginal
equality `obsKernel_fixSet_W_marginal_eq_M1_marginal`, the filled-assignment
pullback equality `mu_C_comap_F_eq_nu_C_comap_F`, and the discrete conditional
kernel bridge `obsCondKernel_cross_eq_ae_of_discrete`. Together these connect
post-intervention adjustment marginals to pre-intervention joint marginals using
overlap, positivity, and the non-descendance condition needed for the Rule 3
marginal step. -/

namespace Causalean

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

namespace SCM

open scoped MeasureTheory ProbabilityTheory

-- ============================================================
-- § Rule 3 W-marginal equality
-- ============================================================

/-- **Rule 3 W-marginal equality for Rule 2.**

    Under `hWNonDesc` — no `SWIGNode.fixed z` (`z ∈ Z`) is an ancestor in
    `(M'.fixSet Z _ _).dag` of any `v ∈ W` (i.e. Pearl/SWIG backdoor criterion
    (i) specialised to `W`) — the `W`-marginal of `(M'.fixSet Z).obsKernel s`
    coincides with the `W`-marginal of `M'.obsKernel sM1`:
    ```
    ν_W = μ_W   as measures on  ValuesOn W (swigΩ Ω).
    ```

    This is a direct specialization of `condDistrib_intervention_ancestral_eq`
    to `T := W`.  No discrete-Z typeclass or point-mass pinning hypothesis is
    needed at this layer. -/
theorem obsKernel_fixSet_W_marginal_eq_M1_marginal
    (M' : Causalean.SCM N Ω) (Z : Finset N)
    (hZ_obs : ∀ D ∈ Z, SWIGNode.random D ∈ M'.observed)
    (hZ_fixed : ∀ D ∈ Z, SWIGNode.fixed D ∉ M'.fixed)
    (W : Finset (SWIGNode N)) (hW : W ⊆ M'.observed)
    (hWNonDesc : ∀ z ∈ Z, ∀ v ∈ W,
      ¬ (M'.fixSet Z hZ_obs hZ_fixed).dag.isAncestor (SWIGNode.fixed z) v)
    (s : (M'.fixSet Z hZ_obs hZ_fixed).FixedValues) :
    ((M'.fixSet Z hZ_obs hZ_fixed).obsKernel s).map
        (valuesProjection
          ((fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hW))
      = (M'.obsKernel (M'.fixSetProj Z hZ_obs hZ_fixed s)).map
          (valuesProjection hW) := by
  -- Rule 3 specialised to `T := W`: the W-marginal of the intervention
  -- kernel equals the W-marginal of the original kernel, because no z ∈ Z
  -- has `.fixed z` as ancestor of any v ∈ W in the post-intervention DAG.
  exact condDistrib_intervention_ancestral_eq M' Z hZ_obs hZ_fixed W hW
    (fun z hz v hv => hWNonDesc z hz v hv) s

-- ============================================================
-- § Cross-SCM pullback equality
-- ============================================================

/-- **Cross-SCM pullback equality along the filled assignment.**

    The pullback along `F := fillZrW s` of the M1 marginal on
    `C := Zr ∪ W` equals the same pullback of the M2 marginal on `C`.
    This public lemma packages the cross-SCM cylinder equality needed by
    `obsCondKernel_cross_eq_ae_of_discrete` without depending on private proof
    internals in `RectIdentity.lean`.

    By `MeasurableEmbedding.comap_apply`, both pullbacks evaluate on each
    measurable `A_W ⊆ ValuesOn W` to the measure of `F '' A_W`, and the
    cross-SCM cylinder bridge `obsKernel_inter_Wset_Zrand_levelset_eq`
    (with `S := univ`) equates these.  This is pure cross-SCM measure equality
    along the filled assignment; it does not use a discrete-Z typeclass. -/
lemma mu_C_comap_F_eq_nu_C_comap_F
    (M' : Causalean.SCM N Ω) (Z : Finset N)
    (hZ_obs : ∀ D ∈ Z, SWIGNode.random D ∈ M'.observed)
    (hZ_fixed : ∀ D ∈ Z, SWIGNode.fixed D ∉ M'.fixed)
    (W : Finset (SWIGNode N))
    (hZrW : Z.image SWIGNode.random ∪ W ⊆ M'.observed)
    (hDisj_ZrW : Disjoint (Z.image SWIGNode.random) W)
    [MeasurableSingletonClass
      (ValuesOn (Z.image SWIGNode.random ∪ W) (swigΩ Ω))]
    (s : (M'.fixSet Z hZ_obs hZ_fixed).FixedValues) :
    ((M'.obsKernel (M'.fixSetProj Z hZ_obs hZ_fixed s)).map
        (valuesProjection (Ω := swigΩ Ω) hZrW)).comap
      (M'.fillZrW Z hZ_obs hZ_fixed W s)
    = (((M'.fixSet Z hZ_obs hZ_fixed).obsKernel s).map
        (valuesProjection (Ω := swigΩ Ω)
          ((fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hZrW))).comap
      (M'.fillZrW Z hZ_obs hZ_fixed W s) := by
  classical
  let M2 := M'.fixSet Z hZ_obs hZ_fixed
  let sM1 : M'.FixedValues := M'.fixSetProj Z hZ_obs hZ_fixed s
  let F := M'.fillZrW Z hZ_obs hZ_fixed W s
  have hZrW_M2 : Z.image SWIGNode.random ∪ W ⊆ M2.observed :=
    (fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hZrW
  have hF_emb : MeasurableEmbedding F :=
    measurableEmbedding_fillZrW M' Z hZ_obs hZ_fixed W hDisj_ZrW s
  have hπC_M1 : Measurable
      (valuesProjection (Ω := swigΩ Ω) hZrW : M'.ObservedValues → _) :=
    measurable_valuesProjection _
  have hπC_M2 : Measurable
      (valuesProjection (Ω := swigΩ Ω) hZrW_M2 : M2.ObservedValues → _) :=
    measurable_valuesProjection _
  refine MeasureTheory.Measure.ext (fun A_W hA_W => ?_)
  rw [hF_emb.comap_apply, hF_emb.comap_apply]
  have hImg_meas : MeasurableSet (F '' A_W) := hF_emb.measurableSet_image' hA_W
  rw [MeasureTheory.Measure.map_apply hπC_M1 hImg_meas,
      MeasureTheory.Measure.map_apply hπC_M2 hImg_meas]
  have hBridge :
      M2.obsKernel s
          (Set.univ ∩ (valuesProjection hZrW_M2)⁻¹' (F '' A_W))
        = M'.obsKernel sM1
            (Set.univ ∩ (valuesProjection hZrW)⁻¹' (F '' A_W)) :=
    obsKernel_inter_Wset_Zrand_levelset_eq M' Z hZ_obs hZ_fixed W
      hZrW hDisj_ZrW s MeasurableSet.univ hA_W
  rw [Set.univ_inter, Set.univ_inter] at hBridge
  exact hBridge.symm

-- ============================================================
-- § Discrete-treatment conditional-kernel bridge
-- ============================================================

/-- **Discrete-treatment cross-SCM conditional-kernel equality.**

    Establishes the `ν_W`-a.e. agreement of the M1 and M2 conditional kernels
    under the **Pearl/SWIG backdoor hypotheses**:

    * `hWNonDesc` — Rule 3 / backdoor criterion (i) for `W`.
    * `hOverlap`  — `Rule2JointOverlap`, the M2 → M1 absolute-continuity
                    direction (the joint AC bound on Zr ∪ W).
    * `hPositivity` — `μ_W ≪ μ_C.comap F`, Pearl's positivity / overlap on
                      the W-marginal: for M1's marginal `μ_W`-a.e. `w`, the
                      point `(z*, w)` lies in M1's joint support on `Zr ∪ W`.

    **Conclusion.**
    ```
    ∀ᵐ w ∂ν_W,
      M1.obsCondKernel Y (Zr ∪ W) (sM1, F w) B
        = M2.obsCondKernel Y W (s, w) B
    ```

    **Proof chain (Pearl/SWIG standard).**
    1. `obsKernel_fixSet_W_marginal_eq_M1_marginal`: `ν_W = μ_W` as measures.
    2. The d-separation collapse for M2 conditional kernels is pulled back
       through `F` via `MeasurableEmbedding.ae_map_iff` to obtain a
       `ν_C.comap F`-a.e. statement on `w`; construction of `F` gives
       `π_W^C (F w) = w`.
    3. `mu_C_comap_F_eq_nu_C_comap_F`: rewrite `ν_C.comap F = μ_C.comap F`,
       so the simplified L1 statement is `μ_C.comap F`-a.e.
    4. Cross-SCM bridge along the filled assignment: already `μ_C.comap F`-a.e.
    5. Chain L1 and L2 on `μ_C.comap F`-a.e.
    6. **Transport `μ_C.comap F`-a.e. → `μ_W`-a.e.** via `hPositivity` and
       `MeasureTheory.Measure.AbsolutelyContinuous.ae_eq`.
    7. Rewrite `ν_W = μ_W` using the Rule 3 marginal equality to land on the
       goal measure. -/
lemma obsCondKernel_cross_eq_ae_of_discrete
    (M' : Causalean.SCM N Ω) (Z : Finset N)
    (hZ_obs : ∀ D ∈ Z, SWIGNode.random D ∈ M'.observed)
    (hZ_fixed : ∀ D ∈ Z, SWIGNode.fixed D ∉ M'.fixed)
    (Y W : Finset (SWIGNode N))
    (hY : Y ⊆ M'.observed) (hW : W ⊆ M'.observed)
    (hZrW : Z.image SWIGNode.random ∪ W ⊆ M'.observed)
    (hDisj_ZrW : Disjoint (Z.image SWIGNode.random) W)
    (hDisj_YZr : Disjoint Y (Z.image SWIGNode.random))
    (hDisj_YW : Disjoint Y W)
    [∀ n, StandardBorelSpace (swigΩ Ω n)] [∀ n, Nonempty (swigΩ Ω n)]
    (hdSep : (M'.fixSet Z hZ_obs hZ_fixed).dag.dSep
              Y (Z.image SWIGNode.random)
              (W ∪ (M'.fixSet Z hZ_obs hZ_fixed).fixed))
    (hWNonDesc : ∀ z ∈ Z, ∀ v ∈ W,
      ¬ (M'.fixSet Z hZ_obs hZ_fixed).dag.isAncestor (SWIGNode.fixed z) v)
    [StandardBorelSpace (M'.fixSet Z hZ_obs hZ_fixed).RandomValues]
    [StandardBorelSpace (M'.fixSet Z hZ_obs hZ_fixed).ObservedValues]
    [StandardBorelSpace (ValuesOn Y (swigΩ Ω))]
    [Nonempty (ValuesOn Y (swigΩ Ω))]
    [StandardBorelSpace (ValuesOn (Z.image SWIGNode.random) (swigΩ Ω))]
    [Nonempty (ValuesOn (Z.image SWIGNode.random) (swigΩ Ω))]
    [∀ s : M'.FixedValues, MeasureTheory.IsFiniteMeasure (M'.obsKernel s)]
    [∀ s : (M'.fixSet Z hZ_obs hZ_fixed).FixedValues,
      MeasureTheory.IsFiniteMeasure ((M'.fixSet Z hZ_obs hZ_fixed).jointKernel s)]
    [∀ s : (M'.fixSet Z hZ_obs hZ_fixed).FixedValues,
      MeasureTheory.IsFiniteMeasure ((M'.fixSet Z hZ_obs hZ_fixed).obsKernel s)]
    [MeasurableSpace.CountableOrCountablyGenerated
      M'.FixedValues (ValuesOn (Z.image SWIGNode.random ∪ W) (swigΩ Ω))]
    [MeasurableSpace.CountableOrCountablyGenerated
      (M'.fixSet Z hZ_obs hZ_fixed).FixedValues
      (ValuesOn (Z.image SWIGNode.random ∪ W) (swigΩ Ω))]
    [MeasurableSpace.CountableOrCountablyGenerated
      (M'.fixSet Z hZ_obs hZ_fixed).FixedValues (ValuesOn W (swigΩ Ω))]
    [MeasurableSingletonClass
      (ValuesOn (Z.image SWIGNode.random ∪ W) (swigΩ Ω))]
    [∀ _z : {z // z ∈ Z}, Countable (swigΩ Ω (SWIGNode.random _z.val))]
    (s : (M'.fixSet Z hZ_obs hZ_fixed).FixedValues)
    (hOverlap : Causalean.SCM.ID.Rule2JointOverlap
                  M' Z hZ_obs hZ_fixed W hZrW s)
    (hPositivity :
      ((M'.obsKernel (M'.fixSetProj Z hZ_obs hZ_fixed s)).map
          (valuesProjection (Ω := swigΩ Ω) hW))
        ≪ (((M'.obsKernel (M'.fixSetProj Z hZ_obs hZ_fixed s)).map
              (valuesProjection (Ω := swigΩ Ω) hZrW)).comap
            (M'.fillZrW Z hZ_obs hZ_fixed W s)))
    {B : Set (ValuesOn Y (swigΩ Ω))} (hB : MeasurableSet B) :
    ∀ᵐ w ∂(((M'.fixSet Z hZ_obs hZ_fixed).obsKernel s).map
              (valuesProjection
                ((fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hW))),
      (M'.obsCondKernel Y (Z.image SWIGNode.random ∪ W) hY hZrW
        (M'.fixSetProj Z hZ_obs hZ_fixed s,
         M'.fillZrW Z hZ_obs hZ_fixed W s w)) B
      = ((M'.fixSet Z hZ_obs hZ_fixed).obsCondKernel Y W
          ((fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hY)
          ((fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hW)
          (s, w)) B := by
  classical
  -- Abbreviations.
  let M2 := M'.fixSet Z hZ_obs hZ_fixed
  let sM1 : M'.FixedValues := M'.fixSetProj Z hZ_obs hZ_fixed s
  let F := M'.fillZrW Z hZ_obs hZ_fixed W s
  have hY_M2 : Y ⊆ M2.observed :=
    (fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hY
  have hW_M2 : W ⊆ M2.observed :=
    (fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hW
  have hZrW_M2 : Z.image SWIGNode.random ∪ W ⊆ M2.observed :=
    (fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hZrW
  have hF_emb : MeasurableEmbedding F :=
    measurableEmbedding_fillZrW M' Z hZ_obs hZ_fixed W hDisj_ZrW s
  -- Marginal measures.
  let μ_C : MeasureTheory.Measure (ValuesOn (Z.image SWIGNode.random ∪ W) (swigΩ Ω)) :=
    (M'.obsKernel sM1).map (valuesProjection hZrW)
  let ν_C : MeasureTheory.Measure (ValuesOn (Z.image SWIGNode.random ∪ W) (swigΩ Ω)) :=
    (M2.obsKernel s).map (valuesProjection hZrW_M2)
  let μ_W : MeasureTheory.Measure (ValuesOn W (swigΩ Ω)) :=
    (M'.obsKernel sM1).map (valuesProjection (Ω := swigΩ Ω) hW)
  let ν_W : MeasureTheory.Measure (ValuesOn W (swigΩ Ω)) :=
    (M2.obsKernel s).map (valuesProjection (Ω := swigΩ Ω) hW_M2)
  have hμC_def : μ_C =
      (M'.obsKernel sM1).map (valuesProjection (Ω := swigΩ Ω) hZrW) := rfl
  have hνC_def : ν_C =
      (M2.obsKernel s).map (valuesProjection (Ω := swigΩ Ω) hZrW_M2) := rfl
  -- (1) Cross-SCM bridge: μ_C.comap F-a.e. w, M1.obsCondKernel(C)(sM1, F w) B
  --                = M2.obsCondKernel(C)(s, F w) B.
  have h_L2 := obsCondKernel_cross_SCM_ae_eq_on_fillZrW M' Z hZ_obs hZ_fixed
    Y W hY hW hZrW hDisj_ZrW s hB
  -- (2) D-sep collapse: ν_C-a.e. c, M2.obsCondKernel(C)(s, c) B
  --                = M2.obsCondKernel(W)(s, π_W^C c) B.
  have h_L1 := obsCondKernel_dSep_collapse_ae M' Z hZ_obs hZ_fixed Y W
    hY hW hZrW hDisj_YZr hDisj_ZrW hDisj_YW hdSep s hB
  -- (3) Pullback equality: μ_C.comap F = ν_C.comap F.
  have hPartA : μ_C.comap F = ν_C.comap F :=
    mu_C_comap_F_eq_nu_C_comap_F M' Z hZ_obs hZ_fixed W hZrW hDisj_ZrW s
  -- (4) Rule 3 marginal equality: ν_W = μ_W as measures.
  have hν_W_eq_μ_W : ν_W = μ_W := by
    change (M2.obsKernel s).map (valuesProjection hW_M2)
         = (M'.obsKernel sM1).map (valuesProjection hW)
    exact obsKernel_fixSet_W_marginal_eq_M1_marginal
      M' Z hZ_obs hZ_fixed W hW hWNonDesc s
  -- (5) Transport h_L1 from ν_C-a.e. (in `c`) to ν_C.comap F-a.e. (in `w`,
  -- with `c := F w`).  Step (5a): ν_C-a.e. → ν_C.restrict (range F)-a.e.
  have h_L1_restrict :
      ∀ᵐ c ∂(ν_C.restrict (Set.range F)),
        (M2.obsCondKernel Y (Z.image SWIGNode.random ∪ W) hY_M2 hZrW_M2 (s, c)) B
        = (M2.obsCondKernel Y W hY_M2 hW_M2
            (s, valuesProjection
                (Finset.subset_union_right
                  (s₁ := Z.image SWIGNode.random) (s₂ := W)) c)) B :=
    MeasureTheory.ae_restrict_of_ae h_L1
  -- (5b): ν_C.restrict (range F) = (ν_C.comap F).map F  (`hF_emb.map_comap`).
  have h_map_comap_ν : (ν_C.comap F).map F = ν_C.restrict (Set.range F) :=
    hF_emb.map_comap ν_C
  rw [← h_map_comap_ν] at h_L1_restrict
  -- (5c): Pull back through F via MeasurableEmbedding.ae_map_iff.
  have h_L1_pulled :
      ∀ᵐ w ∂(ν_C.comap F),
        (M2.obsCondKernel Y (Z.image SWIGNode.random ∪ W) hY_M2 hZrW_M2 (s, F w)) B
        = (M2.obsCondKernel Y W hY_M2 hW_M2
            (s, valuesProjection
                (Finset.subset_union_right
                  (s₁ := Z.image SWIGNode.random) (s₂ := W)) (F w))) B :=
    (hF_emb.ae_map_iff (μ := ν_C.comap F)
      (p := fun c =>
        (M2.obsCondKernel Y (Z.image SWIGNode.random ∪ W) hY_M2 hZrW_M2 (s, c)) B
        = (M2.obsCondKernel Y W hY_M2 hW_M2
            (s, valuesProjection
                (Finset.subset_union_right
                  (s₁ := Z.image SWIGNode.random) (s₂ := W)) c)) B)).mp h_L1_restrict
  -- (6) `π_W^C (F w) = w`, by construction of F.
  have h_proj_F : ∀ w : ValuesOn W (swigΩ Ω),
      valuesProjection (Finset.subset_union_right
        (s₁ := Z.image SWIGNode.random) (s₂ := W)) (F w) = w := by
    intro w
    funext ⟨v, hvW⟩
    have hv_in : v ∈ Z.image SWIGNode.random ∪ W :=
      Finset.subset_union_right hvW
    have hvNotZr : v ∉ Z.image SWIGNode.random := fun hvZr =>
      Finset.disjoint_left.mp hDisj_ZrW hvZr hvW
    simp only [valuesProjection, F, fillZrW]
    rw [valuesUnionMk_apply_right _ _ hv_in hvNotZr hvW]
  -- (7) Simplify h_L1_pulled using h_proj_F.
  have h_L1_simpl :
      ∀ᵐ w ∂(ν_C.comap F),
        (M2.obsCondKernel Y (Z.image SWIGNode.random ∪ W) hY_M2 hZrW_M2 (s, F w)) B
        = (M2.obsCondKernel Y W hY_M2 hW_M2 (s, w)) B := by
    refine Filter.Eventually.mono h_L1_pulled (fun w hw => ?_)
    rw [h_proj_F] at hw
    exact hw
  -- (8) Combine h_L2 (μ_C.comap F-a.e.) with h_L1_simpl (ν_C.comap F-a.e.),
  -- using the pullback equality to identify the two measures.
  have h_L1_simpl_μ : ∀ᵐ w ∂(μ_C.comap F),
      (M2.obsCondKernel Y (Z.image SWIGNode.random ∪ W) hY_M2 hZrW_M2 (s, F w)) B
      = (M2.obsCondKernel Y W hY_M2 hW_M2 (s, w)) B := by
    rw [hPartA]; exact h_L1_simpl
  have h_chain_μ : ∀ᵐ w ∂(μ_C.comap F),
      (M'.obsCondKernel Y (Z.image SWIGNode.random ∪ W) hY hZrW
        (sM1, F w)) B
      = (M2.obsCondKernel Y W hY_M2 hW_M2 (s, w)) B := by
    filter_upwards [h_L2, h_L1_simpl_μ] with w hL2 hL1
    exact hL2.trans hL1
  -- (9) Transport from μ_C.comap F-a.e. to μ_W-a.e. via hPositivity.
  have h_chain_μW : ∀ᵐ w ∂μ_W,
      (M'.obsCondKernel Y (Z.image SWIGNode.random ∪ W) hY hZrW
        (sM1, F w)) B
      = (M2.obsCondKernel Y W hY_M2 hW_M2 (s, w)) B :=
    hPositivity.ae_eq h_chain_μ
  -- (10) Rewrite the goal's measure ν_W to μ_W via the Rule 3 marginal equality.
  change ∀ᵐ w ∂ν_W, _
  rw [hν_W_eq_μ_W]
  exact h_chain_μW

end SCM

end Causalean
