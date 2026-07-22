/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.PO.ID.Partial.Proxy.Helpers.Common
import Causalean.PO.ID.Exact.Proximal.Helpers
import Causalean.Mathlib.LikelihoodRatioSwap
import Causalean.Mathlib.CondIndep

/-! # Two-Proxy Bridge Substitution

This file proves the two-proxy bridge-substitution identity used in proximal
partial identification. It represents the off-arm mean of the treatment-specific
potential outcome as a same-arm integral of the outcome bridge multiplied by
the treatment-side proxy bridge.

Under the probability-ratio convention for the proxy bridge, no separate
stratum odds-ratio factor appears in this identity; that factor is recovered
later after conditioning on the treatment and covariates. The proof follows the
paper's sequence of latent exchangeability, outcome bridge substitution,
likelihood-ratio arm swap, and proxy independence factorization. -/

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

/-- **Two-proxy bridge-substitution identity, same-arm form**
(Ghassami-Shpitser-Tchetgen Tchetgen 2024, Theorem 3, equation (★) at the
end of the proof, in the codebase's probability-ratio q convention).

Conclusion (same-arm form):

    ∫_{A ≠ a} Y(a) dμ = ∫_{A = a} h(a, W, X) · q(Z, a, X) dμ.

No `stratumOddsRatio` weight appears: the probability-ratio q already
encodes the off-arm-to-on-arm change of measure at the latent level (see
`likelihoodRatio_swapA_spec`). This is the natural target for the
`IsUpperEnvWZ` / `IsLowerEnvWZ` envelope predicates, which are a.e.
inequalities of σ_AX-measurable functions **on `{A = a}`**. The
`stratumOddsRatio` factor that appears in the public WZ bound is recovered
downstream by collapsing `μ[q | σ_AX]` on `{A = a}` via
`condExp_q_eq_stratumOddsRatio_arm_AX`.

Proof chain (matches paper lines (a)–(d)): four named sub-`have`s
`hStepA` (latent_exch + tower at σ_AUX), `hStepC` (likelihoodRatio_swapA arm-swap),
`hStepB` (consistency + bridge_h on `{A=a}`), and `hStepD1`/`hStepD2`/`hStepD3`
(bridge_q + proxy_WZ_indep factorisation via prodMk-lift to
(W,X) ⟂ (Z,X) | σ_AUX + tower {A=a} ∈ σ_AUX). Closed modulo
the conditional-independence support lemmas `condExp_mul_of_condIndep` and
`condIndepFun_prodMk_of_measurable_left`, together with the likelihood-ratio
swap helper
`setIntegral_eq_setIntegral_mul_of_likelihoodRatio_swap`. -/
lemma condIntYofA_eq_hq_armSwap_twoProxy
    (HA : POProximalSystem.TwoProxyAssumptions S μ) (a : Bool)
    (hAY : S.Avar.v ≠ S.Yvar.v) :
    (∫ ω in {ω | S.A ω ≠ a}, S.YofA a ω ∂μ)
      = ∫ ω in {ω | S.A ω = a},
          HA.h (a, S.W ω, S.X ω) * HA.q (S.Z ω, a, S.X ω) ∂μ := by
  -- Set up measurable sets and integrability shortcuts.
  set s' : Set P.Ω := {ω | S.A ω ≠ a} with hs'_def
  set s : Set P.Ω := {ω | S.A ω = a} with hs_def
  have hs_meas : MeasurableSet s := S.measurable_A (measurableSet_singleton a)
  have hs'_meas : MeasurableSet s' := by
    have h_compl : s' = sᶜ := by ext ω; simp [s', s]
    rw [h_compl]; exact hs_meas.compl
  have hs_in_AUX : MeasurableSet[S.σ_AUX] s := by
    refine ⟨Prod.fst ⁻¹' {a}, ?_, ?_⟩
    · exact measurable_fst (measurableSet_singleton a)
    · ext ω; rfl
  have hs'_in_AUX : MeasurableSet[S.σ_AUX] s' := by
    refine ⟨Prod.fst ⁻¹' {b : Bool | b ≠ a}, ?_, ?_⟩
    · exact measurable_fst (MeasurableSet.compl (measurableSet_singleton a))
    · ext ω; rfl
  have hs_in_UX_Bool : MeasurableSet ({a} : Set Bool) := measurableSet_singleton a
  -- Integrability shortcuts.
  have hYInt : Integrable S.Y μ := HA.integrable_Y
  have hYaInt : Integrable (S.YofA a) μ := HA.integrable_YofA a
  have hhArmInt : Integrable (fun ω => HA.h (a, S.W ω, S.X ω)) μ :=
    HA.integrable_h_arm a
  have hhAInt : Integrable (fun ω => HA.h (S.A ω, S.W ω, S.X ω)) μ :=
    HA.integrable_h
  have hqInt : Integrable (fun ω => HA.q (S.Z ω, a, S.X ω)) μ := HA.integrable_q a
  have hhqInt : Integrable
      (fun ω => HA.h (a, S.W ω, S.X ω) * HA.q (S.Z ω, a, S.X ω)) μ :=
    HA.integrable_hq_arm a
  have hLInt : Integrable (HA.likelihoodRatio_swapA a) μ :=
    HA.integrable_likelihoodRatio_swapA a
  have hYaLInt : Integrable
      (fun ω => (μ[S.YofA a | S.σ_UX]) ω * HA.likelihoodRatio_swapA a ω) μ :=
    HA.integrable_condExpYofA_mul_L a
  -- Measurabilities.
  have h_meas_haWX : Measurable (fun ω => HA.h (a, S.W ω, S.X ω)) := by
    have hp : Measurable (fun ω : P.Ω => (a, S.W ω, S.X ω)) :=
      Measurable.prodMk measurable_const
        (Measurable.prodMk S.measurable_W S.measurable_X)
    exact HA.measurable_h.comp hp
  have h_meas_qZaX : Measurable (fun ω => HA.q (S.Z ω, a, S.X ω)) := by
    have hp : Measurable (fun ω : P.Ω => (S.Z ω, a, S.X ω)) :=
      Measurable.prodMk S.measurable_Z
        (Measurable.prodMk measurable_const S.measurable_X)
    exact HA.measurable_q.comp hp
  have hL_m : Measurable[S.σ_UX] (HA.likelihoodRatio_swapA a) :=
    HA.measurable_likelihoodRatio_swapA a
  -- ============================================================
  -- (a) latent_exch + tower at σ_AUX:
  --     ∫_{A≠a} Y(a) dμ = ∫_{A≠a} μ[Y(a) | σ_AUX] dμ
  --                     = ∫_{A≠a} μ[Y(a) | σ_UX]  dμ.
  -- ============================================================
  have hLatent : μ[S.YofA a | S.σ_AUX] =ᵐ[μ] μ[S.YofA a | S.σ_UX] :=
    POProximalSystem.latent_exch_to_condExp' a (HA.latent_exch a) hYaInt
  have hStepA : (∫ ω in s', S.YofA a ω ∂μ)
      = (∫ ω in s', (μ[S.YofA a | S.σ_UX]) ω ∂μ) := by
    have h1 : (∫ ω in s', S.YofA a ω ∂μ)
        = (∫ ω in s', (μ[S.YofA a | S.σ_AUX]) ω ∂μ) := by
      have := MeasureTheory.setIntegral_condExp (μ := μ) (m := S.σ_AUX)
        S.σ_AUX_le hYaInt hs'_in_AUX
      exact this.symm
    have h2 : (∫ ω in s', (μ[S.YofA a | S.σ_AUX]) ω ∂μ)
        = (∫ ω in s', (μ[S.YofA a | S.σ_UX]) ω ∂μ) :=
      integral_congr_ae (ae_restrict_of_ae hLatent)
    exact h1.trans h2
  -- ============================================================
  -- (c) likelihoodRatio_swapA_spec change-of-measure:
  --     ∫_{A≠a} μ[Y(a) | σ_UX] dμ
  --       = ∫_{A=a} μ[Y(a) | σ_UX] · L dμ.
  -- ============================================================
  have hCondYa_meas : Measurable[S.σ_UX] (μ[S.YofA a | S.σ_UX]) :=
    MeasureTheory.stronglyMeasurable_condExp.measurable
  have hStepC : (∫ ω in s', (μ[S.YofA a | S.σ_UX]) ω ∂μ)
      = (∫ ω in s, (μ[S.YofA a | S.σ_UX]) ω
              * HA.likelihoodRatio_swapA a ω ∂μ) := by
    -- Apply L2 with arms (a, ¬a). Needs a ≠ ¬a (true since Bool).
    have h_swap := Causalean.setIntegral_eq_setIntegral_mul_of_likelihoodRatio_swap
      (m := S.σ_UX) (mΩ := P.measΩ) S.σ_UX_le S.measurable_A a (!a)
      (L := HA.likelihoodRatio_swapA a)
      (f := μ[S.YofA a | S.σ_UX])
      hL_m hCondYa_meas
      MeasureTheory.integrable_condExp.integrableOn hYaLInt.integrableOn
      (by
        -- Spec form: μ[1_{A=a}|σ_UX] · L =ᵐ μ[1_{A=¬a}|σ_UX].
        have := HA.likelihoodRatio_swapA_spec a
        -- Goal is the same — `!a = ¬a` and `(¬ ·) = (· ≠ a)` for Bool.
        have hset_eq : ({ω' : P.Ω | S.A ω' = !a} : Set P.Ω)
            = {ω' | S.A ω' ≠ a} := by
          ext ω; cases a <;> cases hA : S.A ω <;> simp [hA]
        rw [hset_eq]
        exact this)
    -- h_swap : ∫_{A=¬a} f = ∫_{A=a} f * L.
    -- Show s' = {ω | S.A ω = !a}.
    have hs'_eq : s' = {ω | S.A ω = !a} := by
      ext ω; cases a <;> cases hA : S.A ω <;> simp [s', hA]
    rw [hs'_eq]
    exact h_swap
  -- ============================================================
  -- (b) On restrict {A=a}: μ[Y(a)|σ_UX] =ᵐ μ[h(a,W,X)|σ_AUX].
  -- Chain:
  --   μ[Y(a)|σ_UX] =ᵐ[μ] μ[Y(a)|σ_AUX]                  (latent_exch, global)
  --   μ[Y(a)|σ_AUX] =ᵐ[restrict {A=a}] μ[Y|σ_AUX]         (consistency_event' symm)
  --   μ[Y|σ_AUX]    =ᵐ[μ]              μ[h(A,W,X)|σ_AUX]  (bridge_h)
  --   μ[h(A,W,X)|σ_AUX] =ᵐ[restrict {A=a}] μ[h(a,W,X)|σ_AUX]  (h matches on arm)
  -- ============================================================
  -- Step b.1: μ[Y|σ_AUX] =ᵐ[μ] μ[h(A,W,X)|σ_AUX] globally.
  have hCEsub : μ[fun ω => S.Y ω - HA.h (S.A ω, S.W ω, S.X ω) | S.σ_AUX]
      =ᵐ[μ] μ[S.Y | S.σ_AUX]
            - μ[fun ω => HA.h (S.A ω, S.W ω, S.X ω) | S.σ_AUX] :=
    MeasureTheory.condExp_sub (m := S.σ_AUX) hYInt hhAInt
  have hBridge_AUX : μ[S.Y | S.σ_AUX]
      =ᵐ[μ] μ[fun ω => HA.h (S.A ω, S.W ω, S.X ω) | S.σ_AUX] := by
    have h1 := hCEsub.symm.trans HA.bridge_h
    filter_upwards [h1] with ω hω
    have : (μ[S.Y | S.σ_AUX]) ω
        - (μ[fun ω => HA.h (S.A ω, S.W ω, S.X ω) | S.σ_AUX]) ω = 0 := by
      simpa [Pi.sub_apply, Pi.zero_apply] using hω
    linarith
  -- Step b.2: on restrict {A=a}, μ[h(A,W,X)|σ_AUX] =ᵐ μ[h(a,W,X)|σ_AUX].
  have hCE_h_eq : μ[fun ω => HA.h (S.A ω, S.W ω, S.X ω) | S.σ_AUX]
      =ᵐ[μ.restrict s] μ[fun ω => HA.h (a, S.W ω, S.X ω) | S.σ_AUX] := by
    set d : P.Ω → ℝ := fun ω => HA.h (S.A ω, S.W ω, S.X ω)
                              - HA.h (a, S.W ω, S.X ω)
    have hdint : Integrable d μ := hhAInt.sub hhArmInt
    have hd_zero_on_arm : d =ᵐ[μ.restrict s] 0 := by
      apply ae_restrict_of_forall_mem hs_meas
      intro ω hω
      have : S.A ω = a := hω
      simp [d, this]
    have hind_zero : s.indicator d =ᵐ[μ] 0 := by
      simpa using Causalean.indicator_aeEq_of_aeEq_restrict hs_meas hd_zero_on_arm
    have hd_zero_cond : μ[d | S.σ_AUX] =ᵐ[μ.restrict s] 0 := by
      have hindCE_zero : s.indicator (μ[d | S.σ_AUX]) =ᵐ[μ] 0 :=
        Causalean.condExp_indicator_aeEq_zero hs_in_AUX hdint hind_zero
      have hindCE_zero' :
          s.indicator (μ[d | S.σ_AUX]) =ᵐ[μ] s.indicator (0 : P.Ω → ℝ) := by
        simpa using hindCE_zero
      simpa using Causalean.aeEq_restrict_of_indicator_aeEq hs_meas hindCE_zero'
    have hCE_dsub : μ[d | S.σ_AUX]
        =ᵐ[μ] μ[fun ω => HA.h (S.A ω, S.W ω, S.X ω) | S.σ_AUX]
              - μ[fun ω => HA.h (a, S.W ω, S.X ω) | S.σ_AUX] :=
      MeasureTheory.condExp_sub (m := S.σ_AUX) hhAInt hhArmInt
    have hCE_dsub_restrict : μ[d | S.σ_AUX]
        =ᵐ[μ.restrict s]
        μ[fun ω => HA.h (S.A ω, S.W ω, S.X ω) | S.σ_AUX]
              - μ[fun ω => HA.h (a, S.W ω, S.X ω) | S.σ_AUX] :=
      ae_restrict_of_ae hCE_dsub
    have hdiff_zero : (μ[fun ω => HA.h (S.A ω, S.W ω, S.X ω) | S.σ_AUX]
          - μ[fun ω => HA.h (a, S.W ω, S.X ω) | S.σ_AUX])
        =ᵐ[μ.restrict s] 0 :=
      hCE_dsub_restrict.symm.trans hd_zero_cond
    filter_upwards [hdiff_zero] with ω hω
    have : (μ[fun ω => HA.h (S.A ω, S.W ω, S.X ω) | S.σ_AUX]) ω
        - (μ[fun ω => HA.h (a, S.W ω, S.X ω) | S.σ_AUX]) ω = 0 := by
      simpa [Pi.sub_apply, Pi.zero_apply] using hω
    linarith
  -- Step b.3: combine to get on restrict {A=a}:
  --   μ[Y(a)|σ_UX] =ᵐ μ[h(a,W,X)|σ_AUX].
  have hConsist : μ[S.Y | S.σ_AUX]
      =ᵐ[μ.restrict s] μ[S.YofA a | S.σ_AUX] :=
    POProximalSystem.consistency_event'
      HA.consistency a hAY hYInt hYaInt
  have hYa_AUX_eq_h_AUX : μ[S.YofA a | S.σ_AUX]
      =ᵐ[μ.restrict s] μ[fun ω => HA.h (a, S.W ω, S.X ω) | S.σ_AUX] :=
    Filter.EventuallyEq.trans (Filter.EventuallyEq.symm hConsist)
      (Filter.EventuallyEq.trans (ae_restrict_of_ae hBridge_AUX) hCE_h_eq)
  have hYa_UX_eq_h_AUX : μ[S.YofA a | S.σ_UX]
      =ᵐ[μ.restrict s] μ[fun ω => HA.h (a, S.W ω, S.X ω) | S.σ_AUX] :=
    Filter.EventuallyEq.trans
      (Filter.EventuallyEq.symm (ae_restrict_of_ae hLatent))
      hYa_AUX_eq_h_AUX
  -- Substitute under integral on {A=a}.
  have hStepB : (∫ ω in s, (μ[S.YofA a | S.σ_UX]) ω
                  * HA.likelihoodRatio_swapA a ω ∂μ)
      = (∫ ω in s, (μ[fun ω => HA.h (a, S.W ω, S.X ω) | S.σ_AUX]) ω
                    * HA.likelihoodRatio_swapA a ω ∂μ) := by
    refine integral_congr_ae ?_
    filter_upwards [hYa_UX_eq_h_AUX] with ω hω
    rw [hω]
  -- ============================================================
  -- (b'/d) Replace L by μ[q(Z,a,X)|σ_AUX] (via bridge_q on restrict {A=a}),
  -- then use proxy_WZ_indep to factor μ[h·q|σ_AUX] = μ[h|σ_AUX] · μ[q|σ_AUX]
  -- and tower {A=a} ∈ σ_AUX to fold the integral back to ∫_{A=a} h·q.
  -- ============================================================
  -- Step d.1: bridge_q gives, on restrict {A=a},
  --           L =ᵐ μ[q(Z,a,X)|σ_AUX].
  have hBridgeQ : μ[fun ω => HA.q (S.Z ω, a, S.X ω) | S.σ_AUX]
      =ᵐ[μ.restrict s] HA.likelihoodRatio_swapA a := HA.bridge_q a
  have hStepD1 : (∫ ω in s, (μ[fun ω => HA.h (a, S.W ω, S.X ω) | S.σ_AUX]) ω
                    * HA.likelihoodRatio_swapA a ω ∂μ)
      = (∫ ω in s, (μ[fun ω => HA.h (a, S.W ω, S.X ω) | S.σ_AUX]) ω
                    * (μ[fun ω => HA.q (S.Z ω, a, S.X ω) | S.σ_AUX]) ω ∂μ) := by
    refine integral_congr_ae ?_
    filter_upwards [hBridgeQ.symm] with ω hω
    rw [hω]
  -- Step d.2: proxy_WZ_indep + condExp_mul_of_condIndep to factor.
  -- We need (W, X) ⟂ (Z, X) | σ_AUX.  Apply prodMk-left twice (with symmetry).
  have hX_m_AUX : Measurable[S.σ_AUX] S.X := by
    -- X = (fun (p : Bool × γ_U × γ_X) => p.2.2) ∘ S.AUX, with σ_AUX = comap AUX.
    intro t ht
    refine ⟨(fun p : Bool × γ_U × γ_X => p.2.2) ⁻¹' t, ?_, ?_⟩
    · exact (measurable_snd.comp measurable_snd) ht
    · ext ω; rfl
  -- Lift proxy_WZ_indep : W ⟂ Z | σ_AUX  to  (W,X) ⟂ Z | σ_AUX.
  have hWX_Z : ProbabilityTheory.CondIndepFun S.σ_AUX S.σ_AUX_le
      (fun ω => (S.W ω, S.X ω)) S.Z μ :=
    Causalean.condIndepFun_prodMk_of_measurable_left S.σ_AUX_le
      S.measurable_W S.measurable_Z S.measurable_X hX_m_AUX HA.proxy_WZ_indep
  -- Symm: Z ⟂ (W,X) | σ_AUX.
  have hZ_WX : ProbabilityTheory.CondIndepFun S.σ_AUX S.σ_AUX_le
      S.Z (fun ω => (S.W ω, S.X ω)) μ := hWX_Z.symm
  -- Lift to (Z,X) ⟂ (W,X) | σ_AUX.
  have hZX_WX : ProbabilityTheory.CondIndepFun S.σ_AUX S.σ_AUX_le
      (fun ω => (S.Z ω, S.X ω)) (fun ω => (S.W ω, S.X ω)) μ := by
    have hWX_meas : Measurable (fun ω : P.Ω => (S.W ω, S.X ω)) :=
      Measurable.prodMk S.measurable_W S.measurable_X
    exact Causalean.condIndepFun_prodMk_of_measurable_left S.σ_AUX_le
      S.measurable_Z hWX_meas S.measurable_X hX_m_AUX hZ_WX
  -- Symm again: (W,X) ⟂ (Z,X) | σ_AUX.
  have hWX_ZX : ProbabilityTheory.CondIndepFun S.σ_AUX S.σ_AUX_le
      (fun ω => (S.W ω, S.X ω)) (fun ω => (S.Z ω, S.X ω)) μ := hZX_WX.symm
  -- Now apply condExp_mul_of_condIndep with
  -- u(w,x) = h(a,w,x), v(z,x) = q(z,a,x).
  set u : γ_W × γ_X → ℝ := fun p => HA.h (a, p.1, p.2)
  set v : γ_Z × γ_X → ℝ := fun p => HA.q (p.1, a, p.2)
  have hu_meas : Measurable u := by
    have : Measurable (fun p : γ_W × γ_X => (a, p.1, p.2)) :=
      Measurable.prodMk measurable_const
        (Measurable.prodMk measurable_fst measurable_snd)
    exact HA.measurable_h.comp this
  have hv_meas : Measurable v := by
    have : Measurable (fun p : γ_Z × γ_X => (p.1, a, p.2)) :=
      Measurable.prodMk measurable_fst
        (Measurable.prodMk measurable_const measurable_snd)
    exact HA.measurable_q.comp this
  have hWX_meas : Measurable (fun ω : P.Ω => (S.W ω, S.X ω)) :=
    Measurable.prodMk S.measurable_W S.measurable_X
  have hZX_meas : Measurable (fun ω : P.Ω => (S.Z ω, S.X ω)) :=
    Measurable.prodMk S.measurable_Z S.measurable_X
  -- Identifications: u (W ω, X ω) = h(a, W ω, X ω); v (Z ω, X ω) = q(Z ω, a, X ω).
  have hu_eq : (fun ω => u (S.W ω, S.X ω))
      = fun ω => HA.h (a, S.W ω, S.X ω) := rfl
  have hv_eq : (fun ω => v (S.Z ω, S.X ω))
      = fun ω => HA.q (S.Z ω, a, S.X ω) := rfl
  have hu_int : Integrable (fun ω => u (S.W ω, S.X ω)) μ := by
    change Integrable (fun ω => HA.h (a, S.W ω, S.X ω)) μ; exact hhArmInt
  have hv_int : Integrable (fun ω => v (S.Z ω, S.X ω)) μ := by
    change Integrable (fun ω => HA.q (S.Z ω, a, S.X ω)) μ; exact hqInt
  have huv_int : Integrable
      (fun ω => u (S.W ω, S.X ω) * v (S.Z ω, S.X ω)) μ := by
    change Integrable
      (fun ω => HA.h (a, S.W ω, S.X ω) * HA.q (S.Z ω, a, S.X ω)) μ
    exact hhqInt
  have hCondExpMul := Causalean.condExp_mul_of_condIndep S.σ_AUX_le
    hWX_meas hZX_meas hWX_ZX hu_meas hv_meas hu_int hv_int huv_int
  -- Step d.3: substitute the factored form under the integral on s.
  have hStepD2 : (∫ ω in s, (μ[fun ω => HA.h (a, S.W ω, S.X ω) | S.σ_AUX]) ω
                    * (μ[fun ω => HA.q (S.Z ω, a, S.X ω) | S.σ_AUX]) ω ∂μ)
      = (∫ ω in s,
          (μ[fun ω => HA.h (a, S.W ω, S.X ω)
                * HA.q (S.Z ω, a, S.X ω) | S.σ_AUX]) ω ∂μ) := by
    refine integral_congr_ae ?_
    have hCM_restrict :
        (μ[fun ω => u (S.W ω, S.X ω) * v (S.Z ω, S.X ω) | S.σ_AUX])
          =ᵐ[μ.restrict s]
          (μ[fun ω => u (S.W ω, S.X ω) | S.σ_AUX])
            * (μ[fun ω => v (S.Z ω, S.X ω) | S.σ_AUX]) :=
      ae_restrict_of_ae hCondExpMul
    filter_upwards [hCM_restrict] with ω hω
    -- hω is at the (W,X)/(Z,X) level; rewrite via hu_eq, hv_eq.
    show (μ[fun ω => HA.h (a, S.W ω, S.X ω) | S.σ_AUX]) ω
        * (μ[fun ω => HA.q (S.Z ω, a, S.X ω) | S.σ_AUX]) ω
      = (μ[fun ω => HA.h (a, S.W ω, S.X ω)
                * HA.q (S.Z ω, a, S.X ω) | S.σ_AUX]) ω
    have hω' : (μ[fun ω => u (S.W ω, S.X ω) * v (S.Z ω, S.X ω) | S.σ_AUX]) ω
        = (μ[fun ω => u (S.W ω, S.X ω) | S.σ_AUX]) ω
            * (μ[fun ω => v (S.Z ω, S.X ω) | S.σ_AUX]) ω := by
      have := hω
      simpa [Pi.mul_apply] using this
    -- Translate u, v back to explicit forms via hu_eq, hv_eq (definitional).
    simpa [u, v] using hω'.symm
  -- Step d.4: tower ({A=a} ∈ σ_AUX)
  --   ∫_{A=a} μ[h·q | σ_AUX] dμ = ∫_{A=a} h·q dμ.
  have hStepD3 : (∫ ω in s,
        (μ[fun ω => HA.h (a, S.W ω, S.X ω)
              * HA.q (S.Z ω, a, S.X ω) | S.σ_AUX]) ω ∂μ)
      = (∫ ω in s,
          HA.h (a, S.W ω, S.X ω) * HA.q (S.Z ω, a, S.X ω) ∂μ) :=
    MeasureTheory.setIntegral_condExp (μ := μ) (m := S.σ_AUX) S.σ_AUX_le
      hhqInt hs_in_AUX
  -- Chain everything: (a) → (c) → (b) → (d.1) → (d.2) → (d.3).
  calc (∫ ω in s', S.YofA a ω ∂μ)
      = (∫ ω in s', (μ[S.YofA a | S.σ_UX]) ω ∂μ) := hStepA
    _ = (∫ ω in s, (μ[S.YofA a | S.σ_UX]) ω
              * HA.likelihoodRatio_swapA a ω ∂μ) := hStepC
    _ = (∫ ω in s, (μ[fun ω => HA.h (a, S.W ω, S.X ω) | S.σ_AUX]) ω
              * HA.likelihoodRatio_swapA a ω ∂μ) := hStepB
    _ = (∫ ω in s, (μ[fun ω => HA.h (a, S.W ω, S.X ω) | S.σ_AUX]) ω
              * (μ[fun ω => HA.q (S.Z ω, a, S.X ω) | S.σ_AUX]) ω ∂μ) := hStepD1
    _ = (∫ ω in s,
              (μ[fun ω => HA.h (a, S.W ω, S.X ω)
                    * HA.q (S.Z ω, a, S.X ω) | S.σ_AUX]) ω ∂μ) := hStepD2
    _ = (∫ ω in s,
              HA.h (a, S.W ω, S.X ω) * HA.q (S.Z ω, a, S.X ω) ∂μ) := hStepD3

end POProximalSystem

end PO
end Causalean
