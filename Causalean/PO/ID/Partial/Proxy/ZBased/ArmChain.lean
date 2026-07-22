/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Proximal partial identification — Z-based bridge-substitution arm-level lemmas

The two paired bridge-substitution arm-level lemmas underlying Theorem 2 of
Ghassami-Shpitser-Tchetgen Tchetgen (arXiv 2304.04374), Section 2.2:

* `condIntYofA_le_envelope_arm`  — paired upper arm chain.
* `envelope_le_condIntYofA_arm`  — paired lower arm chain.

These walk the off-arm bridge-substitution chain that converts
`∫_{A=¬a} Y(a) dμ` into the corresponding envelope integral, using the
treatment-side bridge `q` and the σ_AZX-conditional envelope.
-/

import Causalean.PO.ID.Partial.Proxy.Helpers
import Causalean.Mathlib.LikelihoodRatioSwap

/-! # Z-based proximal arm-swap chain

This file proves the Z-proxy arm-swap and envelope lemmas used by
`ZBased.lean`. The chain starts from the off-arm integral
`∫_{A != a} Y(a)`, swaps it to the observed arm using the bundled likelihood
ratio, substitutes the treatment bridge `q`, materializes `μ[Y | σ_AZX]`, and
then applies the Z-envelope predicates.

Main declarations:
* `condIntYofA_le_envelope_arm` is the upper arm-chain inequality.
* `envelope_le_condIntYofA_arm` is the lower arm-chain inequality.

The private helper `condIntYq_factor_arm` packages the conditional-independence
factorization that rewrites the `q`-weighted conditional expectation in the
middle of both chains.
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

/-! ### Bridge-substitution identities (envelope form) -/

/-- Factorisation identity used inside the arm chains (paper Theorem 2,
intermediate step). On `s = {A = a}`,
  `∫_s μ[Y|σ_AUX]·μ[q|σ_AUX] dμ = ∫_s μ[Y|σ_AZX]·q dμ`.
The chain is:
  μ[Y|σ_AUX]·μ[q|σ_AUX]
    = μ[q · Y | σ_AUX]            (CI factorisation: lift Z⟂Y|σ_AUX to (Z,X)⟂Y|σ_AUX)
  ∫_s μ[q · Y | σ_AUX] dμ
    = ∫_s q · Y dμ                  (setIntegral_condExp on s ∈ σ_AUX)
    = ∫_s q · μ[Y|σ_AZX] dμ        (L1 with q σ_AZX-meas, s ∈ σ_AZX). -/
private lemma condIntYq_factor_arm
    (HA : POProximalSystem.ZBasedAssumptions S μ) (a : Bool) :
    (∫ ω in {ω | S.A ω = a}, (μ[S.Y | S.σ_AUX]) ω
              * (μ[fun ω' => HA.q (S.Z ω', a, S.X ω') | S.σ_AUX]) ω ∂μ)
      = (∫ ω in {ω | S.A ω = a}, (μ[S.Y | S.σ_AZX]) ω
                  * HA.q (S.Z ω, a, S.X ω) ∂μ) := by
  set s : Set P.Ω := {ω | S.A ω = a} with hs_def
  -- s ∈ σ_AUX (A is the first projection of (A, U, X)).
  have hs_in_AUX : MeasurableSet[S.σ_AUX] s := by
    refine ⟨Prod.fst ⁻¹' {a}, ?_, ?_⟩
    · exact measurable_fst (measurableSet_singleton a)
    · ext ω; rfl
  -- s ∈ σ_AZX (A is the first projection of (A, Z, X)).
  have hs_in_AZX : MeasurableSet[S.σ_AZX] s := by
    refine ⟨Prod.fst ⁻¹' {a}, ?_, ?_⟩
    · exact measurable_fst (measurableSet_singleton a)
    · ext ω; rfl
  -- X is σ_AUX-measurable (third projection of (A, U, X)).
  have hX_m_AUX : Measurable[S.σ_AUX] S.X := by
    intro t ht
    refine ⟨(fun p : Bool × γ_U × γ_X => p.2.2) ⁻¹' t, ?_, ?_⟩
    · exact (measurable_snd.comp measurable_snd) ht
    · ext ω; rfl
  -- (Z, X) measurable.
  have hZX_meas : Measurable (fun ω : P.Ω => (S.Z ω, S.X ω)) :=
    Measurable.prodMk S.measurable_Z S.measurable_X
  -- Lift CI: Z ⟂ Y | σ_AUX (= proxy_YZ.symm)  ⟹  (Z, X) ⟂ Y | σ_AUX.
  have hZ_Y : ProbabilityTheory.CondIndepFun S.σ_AUX S.σ_AUX_le S.Z S.Y μ :=
    HA.proxy_YZ.symm
  have hZX_Y : ProbabilityTheory.CondIndepFun S.σ_AUX S.σ_AUX_le
      (fun ω => (S.Z ω, S.X ω)) S.Y μ :=
    Causalean.condIndepFun_prodMk_of_measurable_left S.σ_AUX_le
      S.measurable_Z S.measurable_Y S.measurable_X hX_m_AUX hZ_Y
  -- Apply condExp_mul_of_condIndep with f = (Z, X), g = Y,
  -- u (z, x) = q (z, a, x), v = id.
  set u : γ_Z × γ_X → ℝ := fun p => HA.q (p.1, a, p.2) with hu_def
  set v : ℝ → ℝ := fun y => y with hv_def
  have hu_meas : Measurable u := by
    have hpair : Measurable (fun p : γ_Z × γ_X => (p.1, a, p.2)) :=
      Measurable.prodMk measurable_fst
        (Measurable.prodMk measurable_const measurable_snd)
    exact HA.measurable_q.comp hpair
  have hv_meas : Measurable v := measurable_id
  have hu_int : Integrable (fun ω => u (S.Z ω, S.X ω)) μ := by
    change Integrable (fun ω => HA.q (S.Z ω, a, S.X ω)) μ
    exact HA.integrable_q a
  have hv_int : Integrable (fun ω => v (S.Y ω)) μ := HA.integrable_Y
  -- Y · q is integrable; reorient to q · Y for the lemma.
  have hYq : Integrable (fun ω => S.Y ω * HA.q (S.Z ω, a, S.X ω)) μ :=
    HA.integrable_Y_mul_q a
  have hqY : Integrable (fun ω => HA.q (S.Z ω, a, S.X ω) * S.Y ω) μ := by
    have hcomm : (fun ω => HA.q (S.Z ω, a, S.X ω) * S.Y ω)
        = (fun ω => S.Y ω * HA.q (S.Z ω, a, S.X ω)) := by funext ω; ring
    rw [hcomm]; exact hYq
  have huv_int : Integrable
      (fun ω => u (S.Z ω, S.X ω) * v (S.Y ω)) μ := by
    change Integrable (fun ω => HA.q (S.Z ω, a, S.X ω) * S.Y ω) μ
    exact hqY
  have hCondExpMul := Causalean.condExp_mul_of_condIndep S.σ_AUX_le
    hZX_meas S.measurable_Y hZX_Y hu_meas hv_meas hu_int hv_int huv_int
  -- σ_AZX-measurability of `q (Z ω, a, X ω)` (factor through (A, Z, X)).
  have hq_meas_AZX : Measurable[S.σ_AZX] (fun ω => HA.q (S.Z ω, a, S.X ω)) := by
    intro t ht
    refine ⟨(fun p : Bool × γ_Z × γ_X => HA.q (p.2.1, a, p.2.2)) ⁻¹' t, ?_, ?_⟩
    · have hpair : Measurable
          (fun p : Bool × γ_Z × γ_X => (p.2.1, a, p.2.2)) :=
        Measurable.prodMk (measurable_fst.comp measurable_snd)
          (Measurable.prodMk measurable_const
            (measurable_snd.comp measurable_snd))
      exact (HA.measurable_q.comp hpair) ht
    · ext ω; rfl
  have hq_sm_AZX : StronglyMeasurable[S.σ_AZX]
      (fun ω => HA.q (S.Z ω, a, S.X ω)) :=
    hq_meas_AZX.stronglyMeasurable
  -- (A) Substitute under integral via `condExp_mul_of_condIndep`:
  --     ∫_s μ[Y|σ_AUX] · μ[q|σ_AUX] dμ = ∫_s μ[q · Y | σ_AUX] dμ.
  have hStepA : (∫ ω in s, (μ[S.Y | S.σ_AUX]) ω
                  * (μ[fun ω' => HA.q (S.Z ω', a, S.X ω') | S.σ_AUX]) ω ∂μ)
      = (∫ ω in s,
            (μ[fun ω => HA.q (S.Z ω, a, S.X ω) * S.Y ω | S.σ_AUX]) ω ∂μ) := by
    refine integral_congr_ae ?_
    have hCM_restrict :
        (μ[fun ω => u (S.Z ω, S.X ω) * v (S.Y ω) | S.σ_AUX])
          =ᵐ[μ.restrict s]
          (μ[fun ω => u (S.Z ω, S.X ω) | S.σ_AUX])
            * (μ[fun ω => v (S.Y ω) | S.σ_AUX]) :=
      ae_restrict_of_ae hCondExpMul
    filter_upwards [hCM_restrict] with ω hω
    have hω' : (μ[fun ω => HA.q (S.Z ω, a, S.X ω) * S.Y ω | S.σ_AUX]) ω
        = (μ[fun ω => HA.q (S.Z ω, a, S.X ω) | S.σ_AUX]) ω
            * (μ[fun ω => S.Y ω | S.σ_AUX]) ω := by
      have := hω
      simpa [u, v, Pi.mul_apply] using this
    -- Bridge α/η-equivalent forms: μ[S.Y | σ] = μ[fun ω => S.Y ω | σ] (η),
    -- and μ[fun ω' => q ω' | σ] = μ[fun ω => q ω | σ] (α-rename).
    change (μ[S.Y | S.σ_AUX]) ω
        * (μ[fun ω' => HA.q (S.Z ω', a, S.X ω') | S.σ_AUX]) ω
      = (μ[fun ω => HA.q (S.Z ω, a, S.X ω) * S.Y ω | S.σ_AUX]) ω
    rw [hω', mul_comm]
  -- (B) Tower σ_AUX (s ∈ σ_AUX): ∫_s μ[q · Y|σ_AUX] = ∫_s q · Y.
  have hStepB :
      (∫ ω in s,
          (μ[fun ω => HA.q (S.Z ω, a, S.X ω) * S.Y ω | S.σ_AUX]) ω ∂μ)
        = (∫ ω in s, HA.q (S.Z ω, a, S.X ω) * S.Y ω ∂μ) :=
    MeasureTheory.setIntegral_condExp (μ := μ) (m := S.σ_AUX)
      S.σ_AUX_le hqY hs_in_AUX
  -- (C) L1 with m = σ_AZX, f = q (σ_AZX-meas), g = Y, s ∈ σ_AZX:
  --     ∫_s q · Y dμ = ∫_s q · μ[Y|σ_AZX] dμ.
  have hStepC : (∫ ω in s, HA.q (S.Z ω, a, S.X ω) * S.Y ω ∂μ)
      = (∫ ω in s, HA.q (S.Z ω, a, S.X ω) * (μ[S.Y | S.σ_AZX]) ω ∂μ) :=
    setIntegral_mul_condExp_of_stronglyMeasurableLeft
      (m := S.σ_AZX) S.σ_AZX_le hq_sm_AZX HA.integrable_Y hqY hs_in_AZX
  -- (D) mul_comm to match the goal orientation.
  have hStepD : (∫ ω in s, HA.q (S.Z ω, a, S.X ω) * (μ[S.Y | S.σ_AZX]) ω ∂μ)
      = (∫ ω in s, (μ[S.Y | S.σ_AZX]) ω * HA.q (S.Z ω, a, S.X ω) ∂μ) := by
    refine integral_congr_ae ?_
    refine Filter.Eventually.of_forall ?_
    intro ω; ring
  exact hStepA.trans (hStepB.trans (hStepC.trans hStepD))

set_option maxHeartbeats 400000 in
/-- Off-arm bridge-substitution identity, **upper** envelope side.

On the off-arm stratum `{A = ¬a}`,
  `∫_{A=¬a} Y(a) dμ ≤ ∫_{A=¬a} Uenv(a, X) dμ`,
provided

* `consistency`        : the ambient PO system is consistent;
* `latent_exch a`      : Y(a) ⟂ A | (U, X);
* `proxy_YZ`           : Y ⟂ Z | (A, U, X);
* `bridge_q a`         : E[q(Z, a, X) | σ(A, U, X)] = likelihoodRatio_swapA a
                         a.s. on `{A = a}`;
* `IsUpperEnvZ μ a Uenv`: `Uenv(a, X)` upper-bounds `E[Y | σ_AZX]` μ-a.e. on
                         `{A = a}`.

Proof outline (paper Appendix, Theorem 2):

  ∫_{A=¬a} Y(a) dμ
    = ∫ E[Y(a) | σ_AUX] · 𝟙{A=¬a} dμ                    (tower, σ_AUX-meas indic)
    = ∫ E[Y(a) | σ_UX]  · 𝟙{A=¬a} dμ                    (latent_exch, drop A)
  -- swap arms via the likelihood ratio (likelihoodRatio_swapA_spec):
    = ∫_{A=a} E[Y(a) | σ_UX] · likelihoodRatio_swapA a dμ
    = ∫_{A=a} E[Y   | σ_UX] · likelihoodRatio_swapA a dμ (consistency on {A=a})
  -- substitute the bridge for the likelihood ratio:
    = ∫_{A=a} E[Y | σ_UX] · E[q(Z,a,X) | σ_AUX] dμ      (bridge_q a)
    = ∫_{A=a} E[Y · q(Z,a,X) | σ_AUX] dμ                (q is σ_AZX-meas)
  -- drop Z under proxy_YZ to materialise the envelope:
    = ∫_{A=a} E[Y | σ_AZX] · q(Z,a,X) dμ                (proxy_YZ + factorisation)
    ≤ ∫_{A=a} Uenv(a,X) · q(Z,a,X) dμ                   (IsUpperEnvZ)
  -- collapse q back to the likelihood ratio:
    = ∫_{A=a} Uenv(a,X) · likelihoodRatio_swapA a dμ
    = ∫_{A=¬a} Uenv(a,X) dμ                             (likelihoodRatio_swapA_spec).

The chain is structurally analogous to `condIntYofA_eq_h_arm` in
`Helpers.lean` but uses the Z-bridge `q` (treatment-side) instead of the
W-bridge `h` (outcome-side). The middle step that materialises
`E[Y | σ_AZX]` and substitutes `Uenv` is the analogue of
`condExp_drop_Z'` (proxy_YZ side). -/
lemma condIntYofA_le_envelope_arm
    (HA : POProximalSystem.ZBasedAssumptions S μ) (a : Bool)
    (hAY : S.Avar.v ≠ S.Yvar.v)
    {Uenv : Bool × γ_X → ℝ} (hU : S.IsUpperEnvZ μ a Uenv)
    (hUInt : Integrable (fun ω => Uenv (a, S.X ω)) μ)
    (hU_int :
      Integrable (fun ω => Uenv (a, S.X ω) * HA.q (S.Z ω, a, S.X ω)) μ)
    (hU_int_L :
      Integrable (fun ω => Uenv (a, S.X ω) * HA.likelihoodRatio_swapA a ω) μ) :
    (∫ ω in {ω | S.A ω ≠ a}, S.YofA a ω ∂μ)
      ≤ (∫ ω in {ω | S.A ω ≠ a}, Uenv (a, S.X ω) ∂μ) := by
  -- Implements the chain in the docstring (paper Thm 2 Appendix).
  -- We materialise each line as a `have` and chain them together.
  set s' : Set P.Ω := {ω | S.A ω ≠ a} with hs'_def
  set s : Set P.Ω := {ω | S.A ω = a} with hs_def
  have hs_meas : MeasurableSet s := S.measurable_A (measurableSet_singleton a)
  have hs'_meas : MeasurableSet s' := by
    have h_compl : s' = sᶜ := by ext ω; simp [s', s]
    rw [h_compl]; exact hs_meas.compl
  have hs'_in_AUX : MeasurableSet[S.σ_AUX] s' := by
    refine ⟨Prod.fst ⁻¹' {b : Bool | b ≠ a}, ?_, ?_⟩
    · exact measurable_fst (MeasurableSet.compl (measurableSet_singleton a))
    · ext ω; rfl
  have hs_in_AUX_set : MeasurableSet[S.σ_AUX] s := by
    refine ⟨Prod.fst ⁻¹' {a}, ?_, ?_⟩
    · exact measurable_fst (measurableSet_singleton a)
    · ext ω; rfl
  -- Integrability shortcuts.
  have hYInt : Integrable S.Y μ := HA.integrable_Y
  have hYaInt : Integrable (S.YofA a) μ := HA.integrable_YofA a
  have hqInt : Integrable (fun ω => HA.q (S.Z ω, a, S.X ω)) μ := HA.integrable_q a
  -- σ_AUX-version of latent_exch and consistency.
  have hLatent : μ[S.YofA a | S.σ_AUX] =ᵐ[μ] μ[S.YofA a | S.σ_UX] :=
    POProximalSystem.latent_exch_to_condExp' a (HA.latent_exch a) hYaInt
  have hConsist : μ[S.Y | S.σ_AUX]
      =ᵐ[μ.restrict s] μ[S.YofA a | S.σ_AUX] :=
    POProximalSystem.consistency_event'
      HA.consistency a hAY hYInt hYaInt
  -- ============================================================
  -- (1) ∫_{A≠a} Y(a) dμ = ∫_{A≠a} E[Y(a) | σ_AUX] dμ
  -- ============================================================
  have hStep1 : (∫ ω in s', S.YofA a ω ∂μ)
      = (∫ ω in s', (μ[S.YofA a | S.σ_AUX]) ω ∂μ) := by
    have := MeasureTheory.setIntegral_condExp (μ := μ) (m := S.σ_AUX)
      S.σ_AUX_le hYaInt hs'_in_AUX
    exact this.symm
  -- ============================================================
  -- (2) ∫_{A≠a} E[Y(a) | σ_AUX] dμ = ∫_{A≠a} E[Y(a) | σ_UX] dμ
  -- ============================================================
  have hStep2 : (∫ ω in s', (μ[S.YofA a | S.σ_AUX]) ω ∂μ)
      = (∫ ω in s', (μ[S.YofA a | S.σ_UX]) ω ∂μ) :=
    integral_congr_ae (ae_restrict_of_ae hLatent)
  -- ============================================================
  -- (3+10) Arm-swap via the likelihood ratio (combines steps 3 and 10):
  --   ∫_{A≠a} f dμ = ∫_{A=a} f · L dμ  for σ_UX-meas f.
  --
  -- Justification sketch: tower against σ_UX, then apply
  -- `likelihoodRatio_swapA_spec` to convert E[𝟙{A≠a}|σ_UX] into
  -- E[𝟙{A=a}|σ_UX] · L, then collapse E[𝟙{A=a}|σ_UX] back via tower.
  -- The forward direction (E[𝟙_{A=a}|σ_UX] absorbing L into 𝟙_{A=a}) is
  -- the substantive measure-theoretic content, supplied by the likelihood-ratio
  -- swap specification in the assumption bundle.
  -- ============================================================
  have hArmSwap_Y : (∫ ω in s', (μ[S.YofA a | S.σ_UX]) ω ∂μ)
      = (∫ ω in s, (μ[S.YofA a | S.σ_UX]) ω
            * HA.likelihoodRatio_swapA a ω ∂μ) := by
    -- Apply L2 (`setIntegral_eq_setIntegral_mul_of_likelihoodRatio_swap`).
    -- Setup: m = σ_UX, A = S.A, (a, a') = (a, !a), f = μ[Y(a)|σ_UX], L = LR.
    have hf_m : Measurable[S.σ_UX] (μ[S.YofA a | S.σ_UX] : P.Ω → ℝ) :=
      (stronglyMeasurable_condExp).measurable
    have hL_m : Measurable[S.σ_UX] (HA.likelihoodRatio_swapA a) :=
      HA.measurable_likelihoodRatio_swapA a
    haveI : IsFiniteMeasure (μ.trim S.σ_UX_le) := isFiniteMeasure_trim S.σ_UX_le
    haveI : SigmaFinite (μ.trim S.σ_UX_le) := inferInstance
    have hfInt : Integrable (fun ω => (μ[S.YofA a | S.σ_UX]) ω) μ := integrable_condExp
    -- Integrability of f * L is supplied by the bundle field below.
    have hfLInt :
        Integrable (fun ω => (μ[S.YofA a | S.σ_UX]) ω * HA.likelihoodRatio_swapA a ω) μ :=
      HA.integrable_condExpYofA_mul_L a
    -- hSpec from the bundle.
    have hSpec :=  HA.likelihoodRatio_swapA_spec a
    -- Convert {A ω ≠ a} to {A ω = !a} using Bool decidability.
    have h_ne_eq : ({ω | S.A ω ≠ a} : Set P.Ω) = {ω | S.A ω = !a} := by
      ext ω; constructor
      · intro h; cases ha : S.A ω <;> cases a <;> simp_all
      · intro h; cases ha : S.A ω <;> cases a <;> simp_all
    -- Apply L2.
    have hL2 :=
      Causalean.setIntegral_eq_setIntegral_mul_of_likelihoodRatio_swap
        S.σ_UX_le S.measurable_A a (!a) hL_m hf_m hfInt.integrableOn hfLInt.integrableOn
        (by
          -- Need hSpec's RHS to use (!a) instead of (≠ a). They're equal as sets.
          have h_ind_eq :
              (Set.indicator ({ω' | S.A ω' = !a}) (fun _ => (1:ℝ)))
                = Set.indicator ({ω' | S.A ω' ≠ a}) (fun _ => (1:ℝ)) := by
            congr 1
            ext ω; constructor
            · intro h; cases ha : S.A ω <;> cases a <;> simp_all
            · intro h; cases ha : S.A ω <;> cases a <;> simp_all
          rw [h_ind_eq]
          exact hSpec)
    -- hL2: ∫_{S.A ω = !a} f dμ = ∫_{S.A ω = a} f * L dμ.
    -- Goal: ∫ in s', f dμ = ∫ in s, f * L dμ. s' = {A ≠ a}, s = {A = a}.
    rw [show s' = {ω | S.A ω = !a} from h_ne_eq]
    exact hL2
  -- ============================================================
  -- (4) On {A=a}: replace E[Y(a) | σ_UX] by E[Y | σ_UX].
  --
  -- From hConsist (on {A=a}: E[Y|σ_AUX] =ᵐ E[Y(a)|σ_AUX]) and hLatent
  -- (global: E[Y(a)|σ_AUX] =ᵐ E[Y(a)|σ_UX]) plus the analogous transfer
  -- for Y, we get E[Y|σ_UX] =ᵐ[restrict s] E[Y(a)|σ_UX].
  -- ============================================================
  -- Corrected step: use σ_AUX rather than σ_UX in the middle of the chain.
  -- This avoids requiring a separate `Y ⟂ A | σ_UX` lift; paper Theorem 2 does not bundle it.
  -- hCE_eq_arm_AUX : μ[Y(a)|σ_UX] =ᵐ[restrict s] μ[Y|σ_AUX].
  -- Derived from: hLatent.symm (gives μ[Y(a)|σ_UX] =ᵐ μ[Y(a)|σ_AUX] globally)
  -- and hConsist.symm (gives μ[Y(a)|σ_AUX] =ᵐ[restrict s] μ[Y|σ_AUX]).
  have hCE_eq_arm_AUX : μ[S.YofA a | S.σ_UX]
      =ᵐ[μ.restrict s] μ[S.Y | S.σ_AUX] := by
    have h1 : μ[S.YofA a | S.σ_UX]
        =ᵐ[μ.restrict s] μ[S.YofA a | S.σ_AUX] := ae_restrict_of_ae hLatent.symm
    exact h1.trans hConsist.symm
  have hStep4 : (∫ ω in s, (μ[S.YofA a | S.σ_UX]) ω
                  * HA.likelihoodRatio_swapA a ω ∂μ)
      = (∫ ω in s, (μ[S.Y | S.σ_AUX]) ω
                  * HA.likelihoodRatio_swapA a ω ∂μ) := by
    refine integral_congr_ae ?_
    filter_upwards [hCE_eq_arm_AUX] with ω hω
    rw [hω]
  -- ============================================================
  -- (5) Substitute the bridge: on {A=a}, L = E[q(Z,a,X) | σ_AUX].
  -- ============================================================
  have hStep5 : (∫ ω in s, (μ[S.Y | S.σ_AUX]) ω
                  * HA.likelihoodRatio_swapA a ω ∂μ)
      = (∫ ω in s, (μ[S.Y | S.σ_AUX]) ω
                  * (μ[fun ω' => HA.q (S.Z ω', a, S.X ω') | S.σ_AUX]) ω ∂μ) := by
    refine integral_congr_ae ?_
    have hbridge := HA.bridge_q a
    filter_upwards [hbridge] with ω hω
    rw [hω]
  -- ============================================================
  -- (6,7) Combined factorisation step:
  --   ∫_{A=a} E[Y|σ_UX] · E[q|σ_AUX] dμ
  --     = ∫_{A=a} E[Y · q | σ_AZX] · 1 dμ
  --     = ∫_{A=a} (μ[Y|σ_AZX]) ω · q(Z,a,X) dμ
  -- This uses proxy_YZ (Y ⟂ Z | σ_AUX) and σ_AZX-measurability of q.
  -- The combined manipulation is the Mathlib gap.
  -- ============================================================
  have hStep67 : (∫ ω in s, (μ[S.Y | S.σ_AUX]) ω
                    * (μ[fun ω' => HA.q (S.Z ω', a, S.X ω') | S.σ_AUX]) ω ∂μ)
      = (∫ ω in s, (μ[S.Y | S.σ_AZX]) ω
                    * HA.q (S.Z ω, a, S.X ω) ∂μ) :=
    condIntYq_factor_arm HA a
  -- ============================================================
  -- (8) Apply IsUpperEnvZ pointwise a.e. on {A=a}, with q ≥ 0.
  -- ============================================================
  have hStep8 : (∫ ω in s, (μ[S.Y | S.σ_AZX]) ω
                    * HA.q (S.Z ω, a, S.X ω) ∂μ)
      ≤ (∫ ω in s, Uenv (a, S.X ω)
                    * HA.q (S.Z ω, a, S.X ω) ∂μ) := by
    refine MeasureTheory.setIntegral_mono_ae_restrict ?_ ?_ ?_
    · -- Integrability of LHS on s, supplied by the bundle field
      -- `integrable_condExpY_mul_q`.
      exact (HA.integrable_condExpY_mul_q a).restrict
    · exact hU_int.restrict
    · -- Pointwise a.e. comparison from `hU` and `q ≥ 0`.
      have hUpper := hU.2
      filter_upwards [hUpper] with ω hω
      have hqnn : 0 ≤ HA.q (S.Z ω, a, S.X ω) := HA.q_nonneg _
      exact mul_le_mul_of_nonneg_right hω hqnn
  -- ============================================================
  -- (9) Reverse the bridge: on {A=a}, E[q(Z,a,X) | σ_AUX] = L.
  -- ============================================================
  have hStep9 : (∫ ω in s, Uenv (a, S.X ω)
                    * HA.q (S.Z ω, a, S.X ω) ∂μ)
      = (∫ ω in s, Uenv (a, S.X ω)
                    * HA.likelihoodRatio_swapA a ω ∂μ) := by
    -- Apply L1 (setIntegral_mul_condExp_of_stronglyMeasurableLeft) with
    -- m = σ_AUX, f = Uenv(a, X) (σ_X-meas, hence σ_AUX-meas via
    -- σ_X_le_σ_AUX), g = q(Z, a, X), s = {A=a} ∈ σ_AUX.
    -- Then bridge_q substitutes μ[q|σ_AUX] for L on s.
    have hUmeas_X : Measurable[S.σ_X] (fun ω => Uenv (a, S.X ω)) := by
      have hUenv_meas : Measurable Uenv := hU.1
      have hpair : Measurable[S.σ_X] (fun ω : P.Ω => (a, S.X ω)) := by
        refine Measurable.prodMk (m := S.σ_X) (measurable_const) ?_
        -- S.X is σ_X-measurable by definition.
        intro t ht
        exact ⟨t, ht, rfl⟩
      exact hUenv_meas.comp hpair
    have hUmeas_AUX : Measurable[S.σ_AUX] (fun ω => Uenv (a, S.X ω)) :=
      hUmeas_X.mono S.σ_X_le_σ_AUX le_rfl
    have hU_sm : StronglyMeasurable[S.σ_AUX] (fun ω => Uenv (a, S.X ω)) :=
      hUmeas_AUX.stronglyMeasurable
    have hL1 := setIntegral_mul_condExp_of_stronglyMeasurableLeft
      (m := S.σ_AUX) S.σ_AUX_le hU_sm hqInt hU_int hs_in_AUX_set
    -- hL1: ∫_s Uenv·q dμ = ∫_s Uenv · μ[q|σ_AUX] dμ
    rw [hL1]
    refine integral_congr_ae ?_
    have hbridge := HA.bridge_q a
    filter_upwards [hbridge] with ω hω
    rw [hω]
  -- ============================================================
  -- (10) Reverse arm-swap to {A≠a}.
  -- ============================================================
  have hStep10 : (∫ ω in s, Uenv (a, S.X ω)
                    * HA.likelihoodRatio_swapA a ω ∂μ)
      = (∫ ω in s', Uenv (a, S.X ω) ∂μ) := by
    -- Symmetric to hArmSwap_Y. Apply L2 with f = Uenv(a, X) (σ_UX-meas via
    -- σ_X ≤ σ_UX), L = likelihoodRatio_swapA, (a, !a). Then convert
    -- {S.A ω = !a} back to {S.A ω ≠ a}.
    have hUmeas_X : Measurable[S.σ_X] (fun ω => Uenv (a, S.X ω)) := by
      have hUenv_meas : Measurable Uenv := hU.1
      have hpair : Measurable[S.σ_X] (fun ω : P.Ω => (a, S.X ω)) := by
        refine Measurable.prodMk (m := S.σ_X) (measurable_const) ?_
        intro t ht; exact ⟨t, ht, rfl⟩
      exact hUenv_meas.comp hpair
    have hUmeas_UX : Measurable[S.σ_UX] (fun ω => Uenv (a, S.X ω)) :=
      hUmeas_X.mono S.σ_X_le_σ_UX le_rfl
    have hL_m : Measurable[S.σ_UX] (HA.likelihoodRatio_swapA a) :=
      HA.measurable_likelihoodRatio_swapA a
    have hSpec := HA.likelihoodRatio_swapA_spec a
    have h_ne_eq : ({ω | S.A ω ≠ a} : Set P.Ω) = {ω | S.A ω = !a} := by
      ext ω; constructor
      · intro h; cases ha : S.A ω <;> cases a <;> simp_all
      · intro h; cases ha : S.A ω <;> cases a <;> simp_all
    have hL2 :=
      Causalean.setIntegral_eq_setIntegral_mul_of_likelihoodRatio_swap
        S.σ_UX_le S.measurable_A a (!a) hL_m hUmeas_UX hUInt.integrableOn hU_int_L.integrableOn
        (by
          have h_ind_eq :
              (Set.indicator ({ω' | S.A ω' = !a}) (fun _ => (1:ℝ)))
                = Set.indicator ({ω' | S.A ω' ≠ a}) (fun _ => (1:ℝ)) := by
            congr 1
            ext ω; constructor
            · intro h; cases ha : S.A ω <;> cases a <;> simp_all
            · intro h; cases ha : S.A ω <;> cases a <;> simp_all
          rw [h_ind_eq]
          exact hSpec)
    -- hL2 : ∫_{S.A ω = !a} Uenv(a,X) dμ = ∫_{S.A ω = a} Uenv(a,X) · L dμ
    rw [show s' = {ω | S.A ω = !a} from h_ne_eq]
    exact hL2.symm
  -- Chain all steps. Steps (1)-(7) are equalities, (8) is the inequality,
  -- (9)-(10) are equalities.
  calc (∫ ω in s', S.YofA a ω ∂μ)
      = (∫ ω in s', (μ[S.YofA a | S.σ_AUX]) ω ∂μ) := hStep1
    _ = (∫ ω in s', (μ[S.YofA a | S.σ_UX]) ω ∂μ) := hStep2
    _ = (∫ ω in s, (μ[S.YofA a | S.σ_UX]) ω
            * HA.likelihoodRatio_swapA a ω ∂μ) := hArmSwap_Y
    _ = (∫ ω in s, (μ[S.Y | S.σ_AUX]) ω
            * HA.likelihoodRatio_swapA a ω ∂μ) := hStep4
    _ = (∫ ω in s, (μ[S.Y | S.σ_AUX]) ω
            * (μ[fun ω' => HA.q (S.Z ω', a, S.X ω') | S.σ_AUX]) ω ∂μ) := hStep5
    _ = (∫ ω in s, (μ[S.Y | S.σ_AZX]) ω
            * HA.q (S.Z ω, a, S.X ω) ∂μ) := hStep67
    _ ≤ (∫ ω in s, Uenv (a, S.X ω)
            * HA.q (S.Z ω, a, S.X ω) ∂μ) := hStep8
    _ = (∫ ω in s, Uenv (a, S.X ω)
            * HA.likelihoodRatio_swapA a ω ∂μ) := hStep9
    _ = (∫ ω in s', Uenv (a, S.X ω) ∂μ) := hStep10

set_option maxHeartbeats 400000 in
/-- Off-arm bridge-substitution identity, **lower** envelope side. Mirror of
`condIntYofA_le_envelope_arm`. -/
lemma envelope_le_condIntYofA_arm
    (HA : POProximalSystem.ZBasedAssumptions S μ) (a : Bool)
    (hAY : S.Avar.v ≠ S.Yvar.v)
    {Lenv : Bool × γ_X → ℝ} (hL : S.IsLowerEnvZ μ a Lenv)
    (hLInt : Integrable (fun ω => Lenv (a, S.X ω)) μ)
    (hL_int :
      Integrable (fun ω => Lenv (a, S.X ω) * HA.q (S.Z ω, a, S.X ω)) μ)
    (hL_int_L :
      Integrable (fun ω => Lenv (a, S.X ω) * HA.likelihoodRatio_swapA a ω) μ) :
    (∫ ω in {ω | S.A ω ≠ a}, Lenv (a, S.X ω) ∂μ)
      ≤ (∫ ω in {ω | S.A ω ≠ a}, S.YofA a ω ∂μ) := by
  -- Mirror of `condIntYofA_le_envelope_arm` with the inequality reversed at
  -- step (8). Walk the chain in reverse direction.
  set s' : Set P.Ω := {ω | S.A ω ≠ a} with hs'_def
  set s : Set P.Ω := {ω | S.A ω = a} with hs_def
  have hs_meas : MeasurableSet s := S.measurable_A (measurableSet_singleton a)
  have hs'_meas : MeasurableSet s' := by
    have h_compl : s' = sᶜ := by ext ω; simp [s', s]
    rw [h_compl]; exact hs_meas.compl
  have hs'_in_AUX : MeasurableSet[S.σ_AUX] s' := by
    refine ⟨Prod.fst ⁻¹' {b : Bool | b ≠ a}, ?_, ?_⟩
    · exact measurable_fst (MeasurableSet.compl (measurableSet_singleton a))
    · ext ω; rfl
  have hs_in_AUX_set : MeasurableSet[S.σ_AUX] s := by
    refine ⟨Prod.fst ⁻¹' {a}, ?_, ?_⟩
    · exact measurable_fst (measurableSet_singleton a)
    · ext ω; rfl
  have hYInt : Integrable S.Y μ := HA.integrable_Y
  have hYaInt : Integrable (S.YofA a) μ := HA.integrable_YofA a
  have hqInt : Integrable (fun ω => HA.q (S.Z ω, a, S.X ω)) μ := HA.integrable_q a
  have hLatent : μ[S.YofA a | S.σ_AUX] =ᵐ[μ] μ[S.YofA a | S.σ_UX] :=
    POProximalSystem.latent_exch_to_condExp' a (HA.latent_exch a) hYaInt
  have hConsist : μ[S.Y | S.σ_AUX]
      =ᵐ[μ.restrict s] μ[S.YofA a | S.σ_AUX] :=
    POProximalSystem.consistency_event'
      HA.consistency a hAY hYInt hYaInt
  -- (1) ∫_{A≠a} Y(a) dμ = ∫_{A≠a} E[Y(a) | σ_AUX] dμ.
  have hStep1 : (∫ ω in s', S.YofA a ω ∂μ)
      = (∫ ω in s', (μ[S.YofA a | S.σ_AUX]) ω ∂μ) := by
    have := MeasureTheory.setIntegral_condExp (μ := μ) (m := S.σ_AUX)
      S.σ_AUX_le hYaInt hs'_in_AUX
    exact this.symm
  -- (2) ∫_{A≠a} E[Y(a) | σ_AUX] dμ = ∫_{A≠a} E[Y(a) | σ_UX] dμ.
  have hStep2 : (∫ ω in s', (μ[S.YofA a | S.σ_AUX]) ω ∂μ)
      = (∫ ω in s', (μ[S.YofA a | S.σ_UX]) ω ∂μ) :=
    integral_congr_ae (ae_restrict_of_ae hLatent)
  -- (3) Arm-swap. Same as upper case — apply L2.
  have hArmSwap_Y : (∫ ω in s', (μ[S.YofA a | S.σ_UX]) ω ∂μ)
      = (∫ ω in s, (μ[S.YofA a | S.σ_UX]) ω
            * HA.likelihoodRatio_swapA a ω ∂μ) := by
    have hf_m : Measurable[S.σ_UX] (μ[S.YofA a | S.σ_UX] : P.Ω → ℝ) :=
      (stronglyMeasurable_condExp).measurable
    have hL_m : Measurable[S.σ_UX] (HA.likelihoodRatio_swapA a) :=
      HA.measurable_likelihoodRatio_swapA a
    haveI : IsFiniteMeasure (μ.trim S.σ_UX_le) := isFiniteMeasure_trim S.σ_UX_le
    haveI : SigmaFinite (μ.trim S.σ_UX_le) := inferInstance
    have hfInt : Integrable (fun ω => (μ[S.YofA a | S.σ_UX]) ω) μ := integrable_condExp
    have hfLInt :
        Integrable (fun ω => (μ[S.YofA a | S.σ_UX]) ω * HA.likelihoodRatio_swapA a ω) μ :=
      HA.integrable_condExpYofA_mul_L a
    have hSpec := HA.likelihoodRatio_swapA_spec a
    have h_ne_eq : ({ω | S.A ω ≠ a} : Set P.Ω) = {ω | S.A ω = !a} := by
      ext ω; constructor
      · intro h; cases ha : S.A ω <;> cases a <;> simp_all
      · intro h; cases ha : S.A ω <;> cases a <;> simp_all
    have hL2 :=
      Causalean.setIntegral_eq_setIntegral_mul_of_likelihoodRatio_swap
        S.σ_UX_le S.measurable_A a (!a) hL_m hf_m hfInt.integrableOn hfLInt.integrableOn
        (by
          have h_ind_eq :
              (Set.indicator ({ω' | S.A ω' = !a}) (fun _ => (1:ℝ)))
                = Set.indicator ({ω' | S.A ω' ≠ a}) (fun _ => (1:ℝ)) := by
            congr 1
            ext ω; constructor
            · intro h; cases ha : S.A ω <;> cases a <;> simp_all
            · intro h; cases ha : S.A ω <;> cases a <;> simp_all
          rw [h_ind_eq]
          exact hSpec)
    rw [show s' = {ω | S.A ω = !a} from h_ne_eq]
    exact hL2
  -- (4) Replace E[Y(a) | σ_UX] by E[Y | σ_AUX] on {A=a}.
  -- Corrected: see upper case for the σ_UX/σ_AUX correction.
  have hCE_eq_arm_AUX : μ[S.YofA a | S.σ_UX]
      =ᵐ[μ.restrict s] μ[S.Y | S.σ_AUX] := by
    have h1 : μ[S.YofA a | S.σ_UX]
        =ᵐ[μ.restrict s] μ[S.YofA a | S.σ_AUX] := ae_restrict_of_ae hLatent.symm
    exact h1.trans hConsist.symm
  have hStep4 : (∫ ω in s, (μ[S.YofA a | S.σ_UX]) ω
                  * HA.likelihoodRatio_swapA a ω ∂μ)
      = (∫ ω in s, (μ[S.Y | S.σ_AUX]) ω
                  * HA.likelihoodRatio_swapA a ω ∂μ) := by
    refine integral_congr_ae ?_
    filter_upwards [hCE_eq_arm_AUX] with ω hω
    rw [hω]
  -- (5) bridge_q substitution.
  have hStep5 : (∫ ω in s, (μ[S.Y | S.σ_AUX]) ω
                  * HA.likelihoodRatio_swapA a ω ∂μ)
      = (∫ ω in s, (μ[S.Y | S.σ_AUX]) ω
                  * (μ[fun ω' => HA.q (S.Z ω', a, S.X ω') | S.σ_AUX]) ω ∂μ) := by
    refine integral_congr_ae ?_
    have hbridge := HA.bridge_q a
    filter_upwards [hbridge] with ω hω
    rw [hω]
  -- (6,7) Factorisation. See upper-case `hStep67` for full justification.
  have hStep67 : (∫ ω in s, (μ[S.Y | S.σ_AUX]) ω
                    * (μ[fun ω' => HA.q (S.Z ω', a, S.X ω') | S.σ_AUX]) ω ∂μ)
      = (∫ ω in s, (μ[S.Y | S.σ_AZX]) ω
                    * HA.q (S.Z ω, a, S.X ω) ∂μ) :=
    condIntYq_factor_arm HA a
  -- (8) Lower envelope inequality (reversed).
  have hStep8 : (∫ ω in s, Lenv (a, S.X ω)
                    * HA.q (S.Z ω, a, S.X ω) ∂μ)
      ≤ (∫ ω in s, (μ[S.Y | S.σ_AZX]) ω
                    * HA.q (S.Z ω, a, S.X ω) ∂μ) := by
    refine MeasureTheory.setIntegral_mono_ae_restrict ?_ ?_ ?_
    · exact hL_int.restrict
    · -- Integrability of `μ[Y|σ_AZX] · q`, supplied by the bundle field
      -- `integrable_condExpY_mul_q`.
      exact (HA.integrable_condExpY_mul_q a).restrict
    · have hLower := hL.2
      filter_upwards [hLower] with ω hω
      have hqnn : 0 ≤ HA.q (S.Z ω, a, S.X ω) := HA.q_nonneg _
      exact mul_le_mul_of_nonneg_right hω hqnn
  -- (9) Reverse bridge substitution for Lenv. Same as upper-case `hStep9`.
  have hStep9 : (∫ ω in s, Lenv (a, S.X ω)
                    * HA.q (S.Z ω, a, S.X ω) ∂μ)
      = (∫ ω in s, Lenv (a, S.X ω)
                    * HA.likelihoodRatio_swapA a ω ∂μ) := by
    have hLmeas_X : Measurable[S.σ_X] (fun ω => Lenv (a, S.X ω)) := by
      have hLenv_meas : Measurable Lenv := hL.1
      have hpair : Measurable[S.σ_X] (fun ω : P.Ω => (a, S.X ω)) := by
        refine Measurable.prodMk (m := S.σ_X) (measurable_const) ?_
        intro t ht; exact ⟨t, ht, rfl⟩
      exact hLenv_meas.comp hpair
    have hLmeas_AUX : Measurable[S.σ_AUX] (fun ω => Lenv (a, S.X ω)) :=
      hLmeas_X.mono S.σ_X_le_σ_AUX le_rfl
    have hL_sm : StronglyMeasurable[S.σ_AUX] (fun ω => Lenv (a, S.X ω)) :=
      hLmeas_AUX.stronglyMeasurable
    have hL1 := setIntegral_mul_condExp_of_stronglyMeasurableLeft
      (m := S.σ_AUX) S.σ_AUX_le hL_sm hqInt hL_int hs_in_AUX_set
    rw [hL1]
    refine integral_congr_ae ?_
    have hbridge := HA.bridge_q a
    filter_upwards [hbridge] with ω hω
    rw [hω]
  -- (10) Reverse arm-swap for Lenv. Same as upper-case `hStep10`.
  have hStep10 : (∫ ω in s, Lenv (a, S.X ω)
                    * HA.likelihoodRatio_swapA a ω ∂μ)
      = (∫ ω in s', Lenv (a, S.X ω) ∂μ) := by
    have hLmeas_X : Measurable[S.σ_X] (fun ω => Lenv (a, S.X ω)) := by
      have hLenv_meas : Measurable Lenv := hL.1
      have hpair : Measurable[S.σ_X] (fun ω : P.Ω => (a, S.X ω)) := by
        refine Measurable.prodMk (m := S.σ_X) (measurable_const) ?_
        intro t ht; exact ⟨t, ht, rfl⟩
      exact hLenv_meas.comp hpair
    have hLmeas_UX : Measurable[S.σ_UX] (fun ω => Lenv (a, S.X ω)) :=
      hLmeas_X.mono S.σ_X_le_σ_UX le_rfl
    have hL_m : Measurable[S.σ_UX] (HA.likelihoodRatio_swapA a) :=
      HA.measurable_likelihoodRatio_swapA a
    have hSpec := HA.likelihoodRatio_swapA_spec a
    have h_ne_eq : ({ω | S.A ω ≠ a} : Set P.Ω) = {ω | S.A ω = !a} := by
      ext ω; constructor
      · intro h; cases ha : S.A ω <;> cases a <;> simp_all
      · intro h; cases ha : S.A ω <;> cases a <;> simp_all
    have hL2 :=
      Causalean.setIntegral_eq_setIntegral_mul_of_likelihoodRatio_swap
        S.σ_UX_le S.measurable_A a (!a) hL_m hLmeas_UX hLInt.integrableOn hL_int_L.integrableOn
        (by
          have h_ind_eq :
              (Set.indicator ({ω' | S.A ω' = !a}) (fun _ => (1:ℝ)))
                = Set.indicator ({ω' | S.A ω' ≠ a}) (fun _ => (1:ℝ)) := by
            congr 1
            ext ω; constructor
            · intro h; cases ha : S.A ω <;> cases a <;> simp_all
            · intro h; cases ha : S.A ω <;> cases a <;> simp_all
          rw [h_ind_eq]
          exact hSpec)
    rw [show s' = {ω | S.A ω = !a} from h_ne_eq]
    exact hL2.symm
  -- Chain: invert hStep1-hStep5/hStep67 around the inequality hStep8.
  calc (∫ ω in s', Lenv (a, S.X ω) ∂μ)
      = (∫ ω in s, Lenv (a, S.X ω)
            * HA.likelihoodRatio_swapA a ω ∂μ) := hStep10.symm
    _ = (∫ ω in s, Lenv (a, S.X ω)
            * HA.q (S.Z ω, a, S.X ω) ∂μ) := hStep9.symm
    _ ≤ (∫ ω in s, (μ[S.Y | S.σ_AZX]) ω
            * HA.q (S.Z ω, a, S.X ω) ∂μ) := hStep8
    _ = (∫ ω in s, (μ[S.Y | S.σ_AUX]) ω
            * (μ[fun ω' => HA.q (S.Z ω', a, S.X ω') | S.σ_AUX]) ω ∂μ) :=
        hStep67.symm
    _ = (∫ ω in s, (μ[S.Y | S.σ_AUX]) ω
            * HA.likelihoodRatio_swapA a ω ∂μ) := hStep5.symm
    _ = (∫ ω in s, (μ[S.YofA a | S.σ_UX]) ω
            * HA.likelihoodRatio_swapA a ω ∂μ) := hStep4.symm
    _ = (∫ ω in s', (μ[S.YofA a | S.σ_UX]) ω ∂μ) := hArmSwap_Y.symm
    _ = (∫ ω in s', (μ[S.YofA a | S.σ_AUX]) ω ∂μ) := hStep2.symm
    _ = (∫ ω in s', S.YofA a ω ∂μ) := hStep1.symm

end POProximalSystem

end PO
end Causalean
