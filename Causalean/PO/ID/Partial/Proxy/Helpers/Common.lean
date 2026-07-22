/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Proximal partial-identification — common helpers

Lemmas shared across `WBased.lean`, `ZBased.lean`, and `TwoProxy.lean` that do
not depend on a specific bridge:

1. **Marginalisation identity** (`meanYofA_eq_strata`): rewrites the marginal
   target `E[Y(a)]` as a convex combination of the conditional target
   `E[Y(a) | A = ¬a]` and the consistency-identified factual mean
   `E[Y | A = a]` on the same arm. This converts each Theorem 1/2/3 (which
   bound the conditional target) into its corresponding Corollary 1/2 (which
   bound the marginal target).

2. **Y(a) clamp lemmas** (`YofA_essbound_above`, `YofA_essbound_below`):
   transfer pointwise a.e. bounds on `Y` to `Y(a)` under latent
   exchangeability + consistency.
-/

import Causalean.PO.ID.Partial.Proxy.Assumptions
import Causalean.PO.ID.Exact.Proximal.Helpers

/-! # Common proximal-proxy partial-identification helpers

This file provides reusable conditional-expectation and stratum-decomposition
lemmas for W-based, Z-based, and two-proxy partial-identification bounds. It
connects bridge functions to observed conditional means and supplies a generic
set-integral pull-out lemma for sigma-measurable factors.
-/

namespace Causalean
namespace PO

open MeasureTheory ProbabilityTheory

namespace POProximalSystem

variable {P : POSystem}
  {γ_X γ_Z γ_W γ_U : Type*}
  [MeasurableSpace γ_X] [MeasurableSpace γ_Z]
  [MeasurableSpace γ_W] [MeasurableSpace γ_U]
  {S : POProximalSystem P γ_X γ_Z γ_W γ_U}
  {μ : Measure P.Ω} [IsFiniteMeasure μ] [StandardBorelSpace P.Ω]

/-! ### Marginalisation identity -/

omit [IsFiniteMeasure μ] [StandardBorelSpace P.Ω] in
/-- `E[Y(a)] = ∫_{A = ¬a} Y(a) dμ + ∫_{A = a} Y dμ`.
Combines the stratum decomposition `μ = μ.restrict {A=a} + μ.restrict {A=¬a}`
with consistency on the `{A = a}` arm.

This is the core identity used to derive Corollaries 1, 2 of the paper from
Theorems 1, 2: any bound on `∫_{A=¬a} Y(a) dμ` lifts to a bound on
`E[Y(a)]` by adding the (point-identified) factual integral on `{A = a}`. -/
lemma meanYofA_eq_strata (HC : POSystem.Consistency P) (a : Bool)
    (hAY : S.Avar.v ≠ S.Yvar.v) (hYofA : Integrable (S.YofA a) μ) :
    S.meanYofA μ a
      = (∫ ω in {ω | S.A ω ≠ a}, S.YofA a ω ∂μ)
      + (∫ ω in {ω | S.A ω = a}, S.Y ω ∂μ) := by
  -- Step 1: split the unrestricted integral by the partition {A = a} ∪ {A ≠ a}.
  have hs_meas : MeasurableSet {ω : P.Ω | S.A ω = a} :=
    S.measurable_A (measurableSet_singleton a)
  have hsplit : S.meanYofA μ a
      = (∫ ω in {ω | S.A ω = a}, S.YofA a ω ∂μ)
      + (∫ ω in {ω | S.A ω ≠ a}, S.YofA a ω ∂μ) := by
    have := MeasureTheory.integral_add_compl (μ := μ) (f := S.YofA a) hs_meas hYofA
    have hcompl : ({ω : P.Ω | S.A ω = a})ᶜ = {ω | S.A ω ≠ a} := by
      ext ω; simp
    simp only [POProximalSystem.meanYofA] at *
    rw [← this, hcompl]
  -- Step 2: on {A = a}, Y(a) =ᵐ Y by consistency.
  have hYeq : S.YofA a =ᵐ[μ.restrict {ω | S.A ω = a}] S.Y := by
    apply ae_restrict_of_forall_mem hs_meas
    intro ω hω
    exact POVar.cf_eq_factual_on_event HC S.Yvar S.Avar a hAY.symm hω
  have hint_eq : (∫ ω in {ω | S.A ω = a}, S.YofA a ω ∂μ)
      = (∫ ω in {ω | S.A ω = a}, S.Y ω ∂μ) :=
    integral_congr_ae hYeq
  rw [hsplit, hint_eq, add_comm]

/-! ### Y(a) clamp lemmas -/

/-- `Y(a)` inherits Y's a.e. upper bound under latent exchangeability and
consistency. Requires `overlap_strong`: every σ_UX-measurable null-on-`{A=a}` set
is globally null, so the single-arm bound lifts globally. -/
lemma YofA_essbound_above {a : Bool} (HC : POSystem.Consistency P)
    (latent_exch : CondIndepFun S.σ_UX S.σ_UX_le (S.YofA a) S.A μ)
    (hAY : S.Avar.v ≠ S.Yvar.v)
    (overlap : ∀ s : Set P.Ω, MeasurableSet[S.σ_UX] s →
        μ (s ∩ {ω | S.A ω = a}) = 0 → μ s = 0)
    {M : ℝ} (hY : ∀ᵐ ω ∂μ, S.Y ω ≤ M) :
    ∀ᵐ ω ∂μ, S.YofA a ω ≤ M := by
  have hYeq : S.Y =ᵐ[μ.restrict {ω | S.A ω = a}] S.YofA a := by
    have hs : MeasurableSet {ω : P.Ω | S.A ω = a} := S.measurable_A (measurableSet_singleton a)
    apply ae_restrict_of_forall_mem hs
    intro ω hω
    exact (POVar.cf_eq_factual_on_event HC S.Yvar S.Avar a hAY.symm hω).symm
  exact Causalean.ae_le_YofA_of_ae_le_Y (mΩ := P.measΩ) (σ_UX := S.σ_UX) S.σ_UX_le
    S.measurable_A S.measurable_Y (S.measurable_YofA a) a latent_exch hYeq overlap hY

/-- `Y(a)` inherits Y's a.e. lower bound. Mirror of `YofA_essbound_above`. -/
lemma YofA_essbound_below {a : Bool} (HC : POSystem.Consistency P)
    (latent_exch : CondIndepFun S.σ_UX S.σ_UX_le (S.YofA a) S.A μ)
    (hAY : S.Avar.v ≠ S.Yvar.v)
    (overlap : ∀ s : Set P.Ω, MeasurableSet[S.σ_UX] s →
        μ (s ∩ {ω | S.A ω = a}) = 0 → μ s = 0)
    {M : ℝ} (hY : ∀ᵐ ω ∂μ, M ≤ S.Y ω) :
    ∀ᵐ ω ∂μ, M ≤ S.YofA a ω := by
  have hYeq : S.Y =ᵐ[μ.restrict {ω | S.A ω = a}] S.YofA a := by
    have hs : MeasurableSet {ω : P.Ω | S.A ω = a} := S.measurable_A (measurableSet_singleton a)
    apply ae_restrict_of_forall_mem hs
    intro ω hω
    exact (POVar.cf_eq_factual_on_event HC S.Yvar S.Avar a hAY.symm hω).symm
  exact Causalean.ae_le_YofA_of_ae_le_Y_below (mΩ := P.measΩ) (σ_UX := S.σ_UX) S.σ_UX_le
    S.measurable_A S.measurable_Y (S.measurable_YofA a) a latent_exch hYeq overlap hY

/-! ### Observed-data collapse: replacing `h(a,W,X)` with `μ[Y | σ_AX]` on `{A=a}` -/

/-- Core observed-data collapse identity (no assumption-bundle dependency).

Given a bridge function `h : Bool × γ_W × γ_X → ℝ` together with the bridge
equation `μ[Y - h(A,W,X) | σ_AUX] =ᵐ 0` and the relevant integrability, the
conditional expectation `μ[Y | σ_AX]` agrees a.e. on `{A = a}` with
`μ[h(a, W, X) | σ_AX]`.

This is the raw-input variant — it takes the bridge data directly, so it can be
consumed by both the W-only bundle (`WBasedAssumptions`) and the two-proxy
bundle (`TwoProxyAssumptions`), which share the bridge_h field but differ in
their auxiliary fields. -/
lemma condExp_Y_eq_condExp_h_arm_AX_core
    {h : Bool × γ_W × γ_X → ℝ} (a : Bool)
    (hYInt : Integrable S.Y μ)
    (hhAInt : Integrable (fun ω => h (S.A ω, S.W ω, S.X ω)) μ)
    (hhArmInt : Integrable (fun ω => h (a, S.W ω, S.X ω)) μ)
    (hbridge : (μ[fun ω => S.Y ω - h (S.A ω, S.W ω, S.X ω) | S.σ_AUX]) =ᵐ[μ] 0) :
    μ[S.Y | S.σ_AX]
      =ᵐ[μ.restrict {ω | S.A ω = a}]
      μ[fun ω => h (a, S.W ω, S.X ω) | S.σ_AX] := by
  have hs_meas : MeasurableSet {ω : P.Ω | S.A ω = a} :=
    S.measurable_A (measurableSet_singleton a)
  -- Step 1: bridge equation gives μ[Y | σ_AUX] =ᵐ[μ] μ[h(A,W,X) | σ_AUX] globally.
  have hCEsub : μ[fun ω => S.Y ω - h (S.A ω, S.W ω, S.X ω) | S.σ_AUX]
      =ᵐ[μ] μ[S.Y | S.σ_AUX] - μ[fun ω => h (S.A ω, S.W ω, S.X ω) | S.σ_AUX] :=
    MeasureTheory.condExp_sub (m := S.σ_AUX) hYInt hhAInt
  have hBridge_AUX : μ[S.Y | S.σ_AUX]
      =ᵐ[μ] μ[fun ω => h (S.A ω, S.W ω, S.X ω) | S.σ_AUX] := by
    have h1 := hCEsub.symm.trans hbridge
    filter_upwards [h1] with ω hω
    have : (μ[S.Y | S.σ_AUX]) ω
        - (μ[fun ω => h (S.A ω, S.W ω, S.X ω) | S.σ_AUX]) ω = 0 := by
      simpa [Pi.sub_apply, Pi.zero_apply] using hω
    linarith
  -- Step 2: on {A=a}, h(A,W,X) = h(a,W,X), hence
  --   μ[h(A,W,X) | σ_AUX] =ᵐ[restrict {A=a}] μ[h(a,W,X) | σ_AUX].
  -- Indicator-zero argument (same pattern as `BridgeW.lean`'s `hCE_h_eq`).
  have hCE_h_eq : μ[fun ω => h (S.A ω, S.W ω, S.X ω) | S.σ_AUX]
      =ᵐ[μ.restrict {ω | S.A ω = a}]
      μ[fun ω => h (a, S.W ω, S.X ω) | S.σ_AUX] := by
    set d : P.Ω → ℝ := fun ω => h (S.A ω, S.W ω, S.X ω) - h (a, S.W ω, S.X ω)
    have hdint : Integrable d μ := hhAInt.sub hhArmInt
    have hd_zero_on_arm : d =ᵐ[μ.restrict {ω | S.A ω = a}] 0 := by
      apply ae_restrict_of_forall_mem hs_meas
      intro ω hω
      have : S.A ω = a := hω
      simp [d, this]
    have hs_in_m : MeasurableSet[S.σ_AUX] {ω | S.A ω = a} := by
      refine ⟨Prod.fst ⁻¹' {a}, ?_, ?_⟩
      · exact measurable_fst (measurableSet_singleton a)
      · ext ω; rfl
    have hind_zero : ({ω | S.A ω = a}).indicator d =ᵐ[μ] 0 := by
      simpa using Causalean.indicator_aeEq_of_aeEq_restrict hs_meas hd_zero_on_arm
    have hd_zero_cond : μ[d | S.σ_AUX] =ᵐ[μ.restrict {ω | S.A ω = a}] 0 := by
      have hindCE_zero : ({ω | S.A ω = a}).indicator (μ[d | S.σ_AUX])
          =ᵐ[μ] 0 := Causalean.condExp_indicator_aeEq_zero hs_in_m hdint hind_zero
      have hindCE_zero' :
          ({ω | S.A ω = a}).indicator (μ[d | S.σ_AUX])
            =ᵐ[μ] ({ω | S.A ω = a}).indicator (0 : P.Ω → ℝ) := by
        simpa using hindCE_zero
      simpa using Causalean.aeEq_restrict_of_indicator_aeEq hs_meas hindCE_zero'
    have hCE_dsub : μ[d | S.σ_AUX]
        =ᵐ[μ] μ[fun ω => h (S.A ω, S.W ω, S.X ω) | S.σ_AUX]
            - μ[fun ω => h (a, S.W ω, S.X ω) | S.σ_AUX] :=
      MeasureTheory.condExp_sub (m := S.σ_AUX) hhAInt hhArmInt
    have hCE_dsub_restrict :
        μ[d | S.σ_AUX]
          =ᵐ[μ.restrict {ω | S.A ω = a}]
          μ[fun ω => h (S.A ω, S.W ω, S.X ω) | S.σ_AUX]
            - μ[fun ω => h (a, S.W ω, S.X ω) | S.σ_AUX] :=
      ae_restrict_of_ae hCE_dsub
    have hdiff_zero : (μ[fun ω => h (S.A ω, S.W ω, S.X ω) | S.σ_AUX]
          - μ[fun ω => h (a, S.W ω, S.X ω) | S.σ_AUX])
        =ᵐ[μ.restrict {ω | S.A ω = a}] 0 :=
      hCE_dsub_restrict.symm.trans hd_zero_cond
    filter_upwards [hdiff_zero] with ω hω
    have : (μ[fun ω => h (S.A ω, S.W ω, S.X ω) | S.σ_AUX]) ω
        - (μ[fun ω => h (a, S.W ω, S.X ω) | S.σ_AUX]) ω = 0 := by
      simpa [Pi.sub_apply, Pi.zero_apply] using hω
    linarith
  -- Step 3: combine to get μ[Y | σ_AUX] =ᵐ[restrict {A=a}] μ[h(a,W,X) | σ_AUX].
  have hBridge_AUX_arm : μ[S.Y | S.σ_AUX]
      =ᵐ[μ.restrict {ω | S.A ω = a}]
      μ[fun ω => h (S.A ω, S.W ω, S.X ω) | S.σ_AUX] :=
    ae_restrict_of_ae hBridge_AUX
  have hY_h_AUX : μ[S.Y | S.σ_AUX]
      =ᵐ[μ.restrict {ω | S.A ω = a}]
      μ[fun ω => h (a, S.W ω, S.X ω) | S.σ_AUX] :=
    Filter.EventuallyEq.trans hBridge_AUX_arm hCE_h_eq
  -- Step 4: apply tower property `condExp_condExp_of_le` with σ_AX ≤ σ_AUX
  --   to bring both sides down to σ_AX.
  -- μ[μ[Y | σ_AUX] | σ_AX] = μ[Y | σ_AX] globally (a.e.). Same for the h-side.
  have hAX_le_AUX : S.σ_AX ≤ S.σ_AUX := S.σ_AX_le_σ_AUX
  have hY_tower : μ[μ[S.Y | S.σ_AUX] | S.σ_AX] =ᵐ[μ] μ[S.Y | S.σ_AX] :=
    MeasureTheory.condExp_condExp_of_le (m₁ := S.σ_AX) (m₂ := S.σ_AUX)
      hAX_le_AUX S.σ_AUX_le
  have hh_tower : μ[μ[fun ω => h (a, S.W ω, S.X ω) | S.σ_AUX] | S.σ_AX]
      =ᵐ[μ] μ[fun ω => h (a, S.W ω, S.X ω) | S.σ_AX] :=
    MeasureTheory.condExp_condExp_of_le (m₁ := S.σ_AX) (m₂ := S.σ_AUX)
      hAX_le_AUX S.σ_AUX_le
  -- The σ_AUX-conditional expectations coincide a.e. on {A = a}; we lift this
  -- through the σ_AX tower. The set {A = a} is σ_AX-measurable, and applying
  -- `condExp_congr_ae` over the restricted measure converts the `{A=a}`-a.e.
  -- equality of σ_AUX-CE's to a `{A=a}`-a.e. equality of their σ_AX-CE's via
  -- `setIntegral_condExp` would be a heavy detour. Simpler: use the indicator
  -- trick at σ_AX level too.
  --
  -- Step 4 (clean form): apply the indicator trick directly to bring the
  -- σ_AUX-equality on {A=a} to a σ_AX-equality on {A=a}. Set
  --   D := μ[Y | σ_AUX] - μ[h(a,W,X) | σ_AUX].
  -- We have D =ᵐ[restrict {A=a}] 0. Hence indicator_{A=a} D =ᵐ[μ] 0, so
  --   E[indicator_{A=a} D | σ_AX] =ᵐ[μ] 0
  --   = indicator_{A=a} · E[D | σ_AX]    (since {A=a} ∈ σ_AX)
  -- Applying tower again: E[D | σ_AX] = μ[Y | σ_AX] - μ[h(a,W,X) | σ_AX] a.e.
  -- So indicator_{A=a} · (μ[Y | σ_AX] - μ[h(a,W,X) | σ_AX]) =ᵐ[μ] 0,
  -- which yields the desired restrict-{A=a} equality.
  set f1 : P.Ω → ℝ := μ[S.Y | S.σ_AUX]
  set f2 : P.Ω → ℝ := μ[fun ω => h (a, S.W ω, S.X ω) | S.σ_AUX]
  set D : P.Ω → ℝ := f1 - f2
  have hf1_int : Integrable f1 μ := MeasureTheory.integrable_condExp
  have hf2_int : Integrable f2 μ := MeasureTheory.integrable_condExp
  have hD_int : Integrable D μ := hf1_int.sub hf2_int
  have hD_zero_on_arm : D =ᵐ[μ.restrict {ω | S.A ω = a}] 0 := by
    filter_upwards [hY_h_AUX] with ω hω
    simp [D, f1, f2, Pi.sub_apply, hω]
  have hs_in_AX : MeasurableSet[S.σ_AX] {ω | S.A ω = a} := by
    refine ⟨Prod.fst ⁻¹' {a}, ?_, ?_⟩
    · exact measurable_fst (measurableSet_singleton a)
    · ext ω; rfl
  have hind_D_zero : ({ω | S.A ω = a}).indicator D =ᵐ[μ] 0 := by
    simpa using Causalean.indicator_aeEq_of_aeEq_restrict hs_meas hD_zero_on_arm
  have hD_zero_AX : μ[D | S.σ_AX] =ᵐ[μ.restrict {ω | S.A ω = a}] 0 := by
    have hindCE_zero : ({ω | S.A ω = a}).indicator (μ[D | S.σ_AX]) =ᵐ[μ] 0 :=
      Causalean.condExp_indicator_aeEq_zero hs_in_AX hD_int hind_D_zero
    have hindCE_zero' :
        ({ω | S.A ω = a}).indicator (μ[D | S.σ_AX])
          =ᵐ[μ] ({ω | S.A ω = a}).indicator (0 : P.Ω → ℝ) := by
      simpa using hindCE_zero
    simpa using Causalean.aeEq_restrict_of_indicator_aeEq hs_meas hindCE_zero'
  -- Decompose μ[D | σ_AX] = μ[f1 | σ_AX] - μ[f2 | σ_AX] and apply tower.
  have hCE_Dsub : μ[D | S.σ_AX] =ᵐ[μ] μ[f1 | S.σ_AX] - μ[f2 | S.σ_AX] :=
    MeasureTheory.condExp_sub (m := S.σ_AX) hf1_int hf2_int
  have hf1_AX_eq : μ[f1 | S.σ_AX] =ᵐ[μ] μ[S.Y | S.σ_AX] := hY_tower
  have hf2_AX_eq : μ[f2 | S.σ_AX] =ᵐ[μ] μ[fun ω => h (a, S.W ω, S.X ω) | S.σ_AX] :=
    hh_tower
  have hCE_Dsub_AX : μ[D | S.σ_AX]
      =ᵐ[μ] μ[S.Y | S.σ_AX] - μ[fun ω => h (a, S.W ω, S.X ω) | S.σ_AX] := by
    refine hCE_Dsub.trans ?_
    filter_upwards [hf1_AX_eq, hf2_AX_eq] with ω h1 h2
    simp [Pi.sub_apply, h1, h2]
  -- Combine with hD_zero_AX (over the restricted measure).
  have hCE_Dsub_AX_arm : μ[D | S.σ_AX]
      =ᵐ[μ.restrict {ω | S.A ω = a}]
      μ[S.Y | S.σ_AX] - μ[fun ω => h (a, S.W ω, S.X ω) | S.σ_AX] :=
    ae_restrict_of_ae hCE_Dsub_AX
  have hdiff_zero_AX : (μ[S.Y | S.σ_AX]
        - μ[fun ω => h (a, S.W ω, S.X ω) | S.σ_AX])
      =ᵐ[μ.restrict {ω | S.A ω = a}] 0 :=
    Filter.EventuallyEq.trans (Filter.EventuallyEq.symm hCE_Dsub_AX_arm) hD_zero_AX
  filter_upwards [hdiff_zero_AX] with ω hω
  have : (μ[S.Y | S.σ_AX]) ω
      - (μ[fun ω => h (a, S.W ω, S.X ω) | S.σ_AX]) ω = 0 := by
    simpa [Pi.sub_apply, Pi.zero_apply] using hω
  linarith

/-- In the W-proxy bundle, the observed conditional mean of the outcome equals the
conditional mean of the bridge function on the matching treatment arm.

This specializes the raw observed-data collapse identity using the W-only bridge
and integrability assumptions. It is the bundled-input wrapper around
`condExp_Y_eq_condExp_h_arm_AX_core` for the W-only assumption bundle. -/
lemma condExp_Y_eq_condExp_h_arm_AX
    (HA : POProximalSystem.WBasedAssumptions S μ) (a : Bool)
    (_hAY : S.Avar.v ≠ S.Yvar.v) :
    μ[S.Y | S.σ_AX]
      =ᵐ[μ.restrict {ω | S.A ω = a}]
      μ[fun ω => HA.h (a, S.W ω, S.X ω) | S.σ_AX] :=
  condExp_Y_eq_condExp_h_arm_AX_core (h := HA.h) a
    HA.integrable_Y HA.integrable_h (HA.integrable_h_arm a) HA.bridge

/-- In the two-proxy bundle, the observed conditional mean of the outcome equals the
conditional mean of the bridge function on the matching treatment arm.

This uses the two-proxy bridge field, since the two-proxy assumptions do not
project to the W-only assumption bundle. It is the bundled-input wrapper around
`condExp_Y_eq_condExp_h_arm_AX_core` for the two-proxy assumption bundle. -/
lemma condExp_Y_eq_condExp_h_arm_AX_twoProxy
    (HA : POProximalSystem.TwoProxyAssumptions S μ) (a : Bool)
    (_hAY : S.Avar.v ≠ S.Yvar.v) :
    μ[S.Y | S.σ_AX]
      =ᵐ[μ.restrict {ω | S.A ω = a}]
      μ[fun ω => HA.h (a, S.W ω, S.X ω) | S.σ_AX] :=
  condExp_Y_eq_condExp_h_arm_AX_core (h := HA.h) a
    HA.integrable_Y HA.integrable_h (HA.integrable_h_arm a) HA.bridge_h

end POProximalSystem

/-! ### Generic helper: σ-measurable left pull-out under a set integral

Pure-Mathlib lemma used by the proximal envelope-collapse step. Combines
`condExp_mul_of_stronglyMeasurable_left` (m-strongly-measurable left factor pulls
through the conditional expectation) with `setIntegral_condExp` on an
m-measurable set. -/

/-- A sigma-measurable left factor can be pulled through conditional expectation
inside a set integral over a measurable event. -/
lemma setIntegral_mul_condExp_of_stronglyMeasurableLeft
    {Ω} {m mΩ : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {f g : Ω → ℝ}
    (hf_sm : StronglyMeasurable[m] f)
    (hg_int : Integrable g μ) (hfg_int : Integrable (f * g) μ)
    {s : Set Ω} (hs_m : MeasurableSet[m] s) :
    ∫ ω in s, f ω * g ω ∂μ = ∫ ω in s, f ω * (μ[g | m]) ω ∂μ := by
  -- Step 1: pull-out a.e. equality.
  have h_pull : (μ[f * g | m]) =ᵐ[μ] f * μ[g | m] :=
    condExp_mul_of_stronglyMeasurable_left hf_sm hfg_int hg_int
  -- Step 2: setIntegral_condExp on the m-measurable set s.
  have h_setInt : ∫ ω in s, (μ[f * g | m]) ω ∂μ = ∫ ω in s, (f * g) ω ∂μ :=
    setIntegral_condExp hm hfg_int hs_m
  -- Step 3: integral_congr_ae for the pull-out, restricted to s.
  have h_pull_restrict : (μ[f * g | m]) =ᵐ[μ.restrict s] (f * μ[g | m]) :=
    ae_restrict_of_ae h_pull
  have h_congr : ∫ ω in s, (μ[f * g | m]) ω ∂μ
      = ∫ ω in s, (f * μ[g | m]) ω ∂μ :=
    integral_congr_ae h_pull_restrict
  -- Combine.
  have h_eq := h_setInt.symm.trans h_congr
  -- h_eq : ∫_s (f*g) = ∫_s (f * μ[g|m]); rewrite Pi.mul_apply.
  simpa [Pi.mul_apply] using h_eq

end PO
end Causalean
