/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Proximal partial-identification — W-only bridge-substitution identity

`condIntYofA_eq_h_arm`: on the off-arm stratum `{A = ¬a}`,
`∫_{A=¬a} Y(a) dμ = ∫_{A=¬a} h(a, W, X) dμ`, using the W-only bridge bundle
`POProximalSystem.WBasedAssumptions`. Used by Theorem 1 / Corollary 1.
-/

import Causalean.PO.ID.Partial.Proxy.Helpers.Common

/-! # W-proxy bridge identity for partial identification

This file proves the W-only bridge-substitution identity used by the proximal
partial-identification bounds. It reduces the off-arm counterfactual integral
to an observable bridge-function integral under consistency, latent
exchangeability, the W-proxy independence condition, and the outcome bridge.
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

/-! ### Bridge-substitution identity -/

/-- On the off-arm stratum `{A = ¬a}`,
`∫_{A=¬a} Y(a) dμ = ∫_{A=¬a} h(a, W, X) dμ`,
provided we have:

* `latent_exch a` : Y(a) ⟂ A | (U, X);
* `proxy_WA`      : W ⟂ A | (U, X);
* `bridge`        : E[Y - h(A, W, X) | σ(A, U, X)] = 0 a.s.;
* consistency.

Proof outline (paper Appendix, eqs (a)-(c)):
  ∫_{A=¬a} Y(a) dμ
    = ∫_{A=¬a} E[Y(a) | σ_UX] dμ      (tower; valid since σ_UX-meas)
    = ∫_{A=¬a} E[Y(a) | σ_AUX] dμ     (latent_exch, drop A)
    = ∫_{A=¬a} E[Y | σ_AUX] dμ        (consistency on {A=a} extends via σ_AUX)
    = ∫_{A=¬a} E[h(A,W,X) | σ_AUX] dμ (bridge)
    = ∫_{A=¬a} E[h(¬a,W,X) | σ_AUX] dμ
        (because on {A=¬a}, h(A,W,X) = h(¬a,W,X), and we then use proxy_WA
         to drop the A=¬a conditioning, getting equivalence with h(a,W,X)
         under W ⟂ A | (U,X))
    = ∫_{A=¬a} h(a, W, X) dμ.

This uses the same conditional-expectation pull-out interface as the exact-ID
helpers (`condExp_h_drop_A`, etc.), so this lemma keeps the same assumption
shape and proof pattern. -/
lemma condIntYofA_eq_h_arm (HA : POProximalSystem.WBasedAssumptions S μ) (a : Bool)
    (hAY : S.Avar.v ≠ S.Yvar.v) :
    (∫ ω in {ω | S.A ω ≠ a}, S.YofA a ω ∂μ)
      = (∫ ω in {ω | S.A ω ≠ a}, HA.h (a, S.W ω, S.X ω) ∂μ) := by
  -- Set s' := {A ≠ a}. Strategy:
  --  (A) ∫_{A≠a} Y(a) dμ = ∫_{A≠a} E[Y(a) | σ_AUX] dμ           (tower, indic σ_AUX-meas)
  --                       = ∫_{A≠a} E[Y(a) | σ_UX]  dμ           (latent_exch_to_condExp')
  --  (B) E[Y(a) | σ_UX] =ᵐ[μ] E[h(a,W,X) | σ_UX]                  (KEY STEP, see below)
  --      ⇒ ∫_{A≠a} E[Y(a) | σ_UX] dμ = ∫_{A≠a} E[h(a,W,X) | σ_UX] dμ
  --  (C) ∫_{A≠a} E[h(a,W,X) | σ_UX] dμ
  --        = ∫_{A≠a} E[h(a,W,X) | σ_AUX] dμ                       (condExp_h_drop_A')
  --        = ∫_{A≠a} h(a,W,X) dμ                                   (tower again)
  set s' : Set P.Ω := {ω | S.A ω ≠ a} with hs'_def
  set s : Set P.Ω := {ω | S.A ω = a} with hs_def
  have hs'_meas : MeasurableSet s' := by
    have : MeasurableSet ({a} : Set Bool) := measurableSet_singleton a
    have hsm : MeasurableSet s := S.measurable_A this
    have h_compl : s' = sᶜ := by ext ω; simp [s', s]
    rw [h_compl]; exact hsm.compl
  have hs_meas : MeasurableSet s := S.measurable_A (measurableSet_singleton a)
  -- s' is also σ_AUX-measurable (it's the preimage of {¬a} under projection (A,U,X) ↦ A).
  have hs'_in_AUX : MeasurableSet[S.σ_AUX] s' := by
    refine ⟨Prod.fst ⁻¹' {b : Bool | b ≠ a}, ?_, ?_⟩
    · exact measurable_fst (MeasurableSet.compl (measurableSet_singleton a))
    · ext ω; rfl
  -- Integrability shortcuts.
  have hYInt : Integrable S.Y μ := HA.integrable_Y
  have hYaInt : Integrable (S.YofA a) μ := HA.integrable_YofA a
  have hhArmInt : Integrable (fun ω => HA.h (a, S.W ω, S.X ω)) μ := HA.integrable_h_arm a
  have hhAInt : Integrable (fun ω => HA.h (S.A ω, S.W ω, S.X ω)) μ := HA.integrable_h
  have h_meas_haWX : Measurable (fun ω => HA.h (a, S.W ω, S.X ω)) := by
    have hp : Measurable (fun ω : P.Ω => (a, S.W ω, S.X ω)) := by
      exact Measurable.prodMk measurable_const
        (Measurable.prodMk S.measurable_W S.measurable_X)
    exact HA.measurable_h.comp hp
  -- Helpers (primed versions, taking individual fields).
  have hLatent : μ[S.YofA a | S.σ_AUX] =ᵐ[μ] μ[S.YofA a | S.σ_UX] :=
    POProximalSystem.latent_exch_to_condExp' a (HA.latent_exch a) hYaInt
  have hHdropA : μ[fun ω => HA.h (a, S.W ω, S.X ω) | S.σ_AUX]
      =ᵐ[μ] μ[fun ω => HA.h (a, S.W ω, S.X ω) | S.σ_UX] :=
    POProximalSystem.condExp_h_drop_A' HA.proxy_WA HA.measurable_h a hhArmInt
  -- ============================================================
  -- (A) ∫_{A≠a} Y(a) dμ = ∫_{A≠a} E[Y(a) | σ_UX] dμ.
  -- ============================================================
  -- Step A.1: tower w.r.t. σ_AUX (since 1_{A≠a} is σ_AUX-meas).
  -- ∫_{A≠a} Y(a) = ∫ 1_{A≠a} · Y(a) = ∫ E[1_{A≠a} · Y(a) | σ_AUX]
  --             = ∫ 1_{A≠a} · E[Y(a) | σ_AUX] = ∫_{A≠a} E[Y(a) | σ_AUX].
  have hStepA1 : (∫ ω in s', S.YofA a ω ∂μ)
      = (∫ ω in s', (μ[S.YofA a | S.σ_AUX]) ω ∂μ) := by
    -- Use `setIntegral_condExp` directly: ∫_t f = ∫_t E[f|m] for t ∈ m.
    have := MeasureTheory.setIntegral_condExp (μ := μ) (m := S.σ_AUX) S.σ_AUX_le hYaInt hs'_in_AUX
    -- This gives us ∫_t E[f|m] = ∫_t f, which we need to flip.
    exact this.symm
  -- Step A.2: replace E[Y(a) | σ_AUX] by E[Y(a) | σ_UX] via hLatent (a.e. global).
  have hStepA2 : (∫ ω in s', (μ[S.YofA a | S.σ_AUX]) ω ∂μ)
      = (∫ ω in s', (μ[S.YofA a | S.σ_UX]) ω ∂μ) :=
    integral_congr_ae (ae_restrict_of_ae hLatent)
  -- ============================================================
  -- (C) ∫_{A≠a} h(a,W,X) dμ = ∫_{A≠a} E[h(a,W,X) | σ_UX] dμ. (mirror of A)
  -- ============================================================
  have hStepC1 : (∫ ω in s', HA.h (a, S.W ω, S.X ω) ∂μ)
      = (∫ ω in s', (μ[fun ω => HA.h (a, S.W ω, S.X ω) | S.σ_AUX]) ω ∂μ) := by
    have := MeasureTheory.setIntegral_condExp (μ := μ) (m := S.σ_AUX) S.σ_AUX_le hhArmInt hs'_in_AUX
    exact this.symm
  have hStepC2 : (∫ ω in s', (μ[fun ω => HA.h (a, S.W ω, S.X ω) | S.σ_AUX]) ω ∂μ)
      = (∫ ω in s', (μ[fun ω => HA.h (a, S.W ω, S.X ω) | S.σ_UX]) ω ∂μ) :=
    integral_congr_ae (ae_restrict_of_ae hHdropA)
  -- ============================================================
  -- (B) KEY STEP: E[Y(a) | σ_UX] =ᵐ[μ] E[h(a,W,X) | σ_UX] globally.
  --
  -- Derivation on {A=a}:
  --   On {A=a}: by consistency, Y =ᵐ Y(a).
  --     ⇒ E[Y | σ_AUX] =ᵐ[restrict {A=a}] E[Y(a) | σ_AUX]   (consistency_event')
  --   By bridge: E[Y - h(A,W,X) | σ_AUX] =ᵐ 0 globally
  --     ⇒ E[Y | σ_AUX] =ᵐ[μ] E[h(A,W,X) | σ_AUX]            (linearity)
  --   On {A=a}: h(A,W,X) = h(a,W,X) pointwise
  --     ⇒ E[h(A,W,X) | σ_AUX] =ᵐ[restrict {A=a}] E[h(a,W,X) | σ_AUX]
  --   Combining, on {A=a}: E[Y(a) | σ_AUX] =ᵐ E[h(a,W,X) | σ_AUX].
  --   Apply hLatent + hHdropA (a.e. globally, hence a.e. on restrict) to translate:
  --   on {A=a}: E[Y(a) | σ_UX] =ᵐ E[h(a,W,X) | σ_UX].
  --
  -- Lift from {A=a} to globally μ-a.e. — this is the SUBTLE STEP.
  -- Both LHS and RHS are σ_UX-measurable. Generally, equality on a set need
  -- not lift to global, but if A ⫫ (relevant σ_UX content) suitably... this
  -- needs additional structural assumption (e.g. positivity of pushforward
  -- under σ_UX) that is not in the WBased bundle.
  -- ============================================================
  -- needs: σ_UX-measurable functions equal μ-a.e.-on-{A=a} are equal μ-a.e.,
  -- assuming μ({A=a}) > 0 and the σ_UX-pushforward sees both arms.
  have hKey : μ[S.YofA a | S.σ_UX]
      =ᵐ[μ] μ[fun ω => HA.h (a, S.W ω, S.X ω) | S.σ_UX] := by
    -- Both sides are σ_UX-measurable. We assemble a.e.-equality on
    -- `{A = a}` (the factual arm) and lift via the abstract single-arm
    -- a.e.-equality lemma `Causalean.ae_eq_of_ae_eq_restrict_arm`.
    --
    -- Step 1: on {A=a}, by consistency, Y =ᵐ Y(a), hence
    --         E[Y | σ_AUX] =ᵐ[restrict {A=a}] E[Y(a) | σ_AUX].
    have hConsist : μ[S.Y | S.σ_AUX]
        =ᵐ[μ.restrict {ω | S.A ω = a}] μ[S.YofA a | S.σ_AUX] :=
      POProximalSystem.consistency_event'
        HA.consistency a hAY hYInt hYaInt
    -- Step 2: bridge equation gives μ[Y - h(A,W,X) | σ_AUX] =ᵐ 0 globally
    --   ⇒ μ[Y | σ_AUX] =ᵐ μ[h(A,W,X) | σ_AUX] globally.
    have hCEsub : μ[fun ω => S.Y ω - HA.h (S.A ω, S.W ω, S.X ω) | S.σ_AUX]
        =ᵐ[μ] μ[S.Y | S.σ_AUX] - μ[fun ω => HA.h (S.A ω, S.W ω, S.X ω) | S.σ_AUX] :=
      MeasureTheory.condExp_sub (m := S.σ_AUX) hYInt hhAInt
    have hBridge : μ[S.Y | S.σ_AUX]
        =ᵐ[μ] μ[fun ω => HA.h (S.A ω, S.W ω, S.X ω) | S.σ_AUX] := by
      have h1 := hCEsub.symm.trans HA.bridge
      filter_upwards [h1] with ω hω
      have : (μ[S.Y | S.σ_AUX]) ω - (μ[fun ω => HA.h (S.A ω, S.W ω, S.X ω) | S.σ_AUX]) ω = 0 := by
        simpa [Pi.sub_apply, Pi.zero_apply] using hω
      linarith
    -- Step 3: on {A=a}, h(A,W,X) = h(a,W,X) pointwise, hence
    --         μ[h(A,W,X) | σ_AUX] =ᵐ[restrict {A=a}] μ[h(a,W,X) | σ_AUX].
    have hh_eq_on_arm : (fun ω => HA.h (S.A ω, S.W ω, S.X ω))
        =ᵐ[μ.restrict {ω | S.A ω = a}] (fun ω => HA.h (a, S.W ω, S.X ω)) := by
      apply ae_restrict_of_forall_mem hs_meas
      intro ω hω
      have : S.A ω = a := hω
      simp [this]
    have hCE_h_eq : μ[fun ω => HA.h (S.A ω, S.W ω, S.X ω) | S.σ_AUX]
        =ᵐ[μ.restrict {ω | S.A ω = a}]
        μ[fun ω => HA.h (a, S.W ω, S.X ω) | S.σ_AUX] := by
      -- Strategy: use linearity.  Set d := h(A,W,X) - h(a,W,X), which is
      -- 0 a.e. on {A=a}, thus E[d | σ_AUX] =ᵐ 0 on {A=a} (via the same
      -- consistency-event argument).
      set d : P.Ω → ℝ := fun ω => HA.h (S.A ω, S.W ω, S.X ω) - HA.h (a, S.W ω, S.X ω)
      have hdint : Integrable d μ := hhAInt.sub hhArmInt
      have hd_zero_on_arm : d =ᵐ[μ.restrict {ω | S.A ω = a}] 0 := by
        apply ae_restrict_of_forall_mem hs_meas
        intro ω hω
        have : S.A ω = a := hω
        simp [d, this]
      -- Reuse the indicator-trick.
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
          =ᵐ[μ] μ[fun ω => HA.h (S.A ω, S.W ω, S.X ω) | S.σ_AUX]
              - μ[fun ω => HA.h (a, S.W ω, S.X ω) | S.σ_AUX] :=
        MeasureTheory.condExp_sub (m := S.σ_AUX) hhAInt hhArmInt
      have hCE_dsub_restrict :
          μ[d | S.σ_AUX]
            =ᵐ[μ.restrict {ω | S.A ω = a}]
            μ[fun ω => HA.h (S.A ω, S.W ω, S.X ω) | S.σ_AUX]
              - μ[fun ω => HA.h (a, S.W ω, S.X ω) | S.σ_AUX] :=
        ae_restrict_of_ae hCE_dsub
      have hdiff_zero : (μ[fun ω => HA.h (S.A ω, S.W ω, S.X ω) | S.σ_AUX]
            - μ[fun ω => HA.h (a, S.W ω, S.X ω) | S.σ_AUX])
          =ᵐ[μ.restrict {ω | S.A ω = a}] 0 :=
        hCE_dsub_restrict.symm.trans hd_zero_cond
      filter_upwards [hdiff_zero] with ω hω
      have : (μ[fun ω => HA.h (S.A ω, S.W ω, S.X ω) | S.σ_AUX]) ω
          - (μ[fun ω => HA.h (a, S.W ω, S.X ω) | S.σ_AUX]) ω = 0 := by
        simpa [Pi.sub_apply, Pi.zero_apply] using hω
      linarith
    -- Step 4: combine: on {A=a},
    --   E[Y(a) | σ_AUX] =ᵐ E[Y | σ_AUX] =ᵐ E[h(A,W,X) | σ_AUX] =ᵐ E[h(a,W,X) | σ_AUX].
    have hCE_eq_on_arm : μ[S.YofA a | S.σ_AUX]
        =ᵐ[μ.restrict {ω | S.A ω = a}]
        μ[fun ω => HA.h (a, S.W ω, S.X ω) | S.σ_AUX] :=
      (hConsist.symm.trans (ae_restrict_of_ae hBridge)).trans hCE_h_eq
    -- Step 5: translate σ_AUX to σ_UX via hLatent and hHdropA (a.e. globally
    -- ⇒ a.e. on restrict).
    have hCE_UX_eq_on_arm : μ[S.YofA a | S.σ_UX]
        =ᵐ[μ.restrict {ω | S.A ω = a}]
        μ[fun ω => HA.h (a, S.W ω, S.X ω) | S.σ_UX] := by
      have h1 : μ[S.YofA a | S.σ_AUX] =ᵐ[μ.restrict {ω | S.A ω = a}]
          μ[S.YofA a | S.σ_UX] := ae_restrict_of_ae hLatent
      have h2 : μ[fun ω => HA.h (a, S.W ω, S.X ω) | S.σ_AUX]
          =ᵐ[μ.restrict {ω | S.A ω = a}]
          μ[fun ω => HA.h (a, S.W ω, S.X ω) | S.σ_UX] :=
        ae_restrict_of_ae hHdropA
      exact h1.symm.trans (hCE_eq_on_arm.trans h2)
    -- Step 6: lift via the single-arm a.e.-equality support lemma.
    -- Both sides are σ_UX-measurable.
    have hf_m : Measurable[S.σ_UX] (μ[S.YofA a | S.σ_UX]) :=
      MeasureTheory.stronglyMeasurable_condExp.measurable
    have hg_m : Measurable[S.σ_UX] (μ[fun ω => HA.h (a, S.W ω, S.X ω) | S.σ_UX]) :=
      MeasureTheory.stronglyMeasurable_condExp.measurable
    exact Causalean.ae_eq_of_ae_eq_restrict_arm (mΩ := P.measΩ)
      S.σ_UX S.σ_UX_le a
      hf_m hg_m hCE_UX_eq_on_arm (HA.overlap_strong a)
  -- (B) integrated form.
  have hStepB : (∫ ω in s', (μ[S.YofA a | S.σ_UX]) ω ∂μ)
      = (∫ ω in s', (μ[fun ω => HA.h (a, S.W ω, S.X ω) | S.σ_UX]) ω ∂μ) :=
    integral_congr_ae (ae_restrict_of_ae hKey)
  -- Chain (A) → (B) → (C).
  rw [hStepA1, hStepA2, hStepB, ← hStepC2, ← hStepC1]

end POProximalSystem

end PO
end Causalean
