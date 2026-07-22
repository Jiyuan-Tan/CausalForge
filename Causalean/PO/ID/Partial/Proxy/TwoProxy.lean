/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Proximal partial identification — two-proxy bounds (Theorem 3)

Bounds on `E[Y(a) | A = ¬a]` under the two-proxy bundle of
Ghassami-Shpitser-Tchetgen Tchetgen (2024, Theorem 3): two conditionally
independent invalid proxies `W` and `Z`, with bridges `h` and `q`.

The proof template (mirrors `WBased.lean`):

1. `condIntYofA_eq_hq_armSwap_twoProxy`: same-arm bridge-substitution
       ∫_{A ≠ a} Y(a) dμ = ∫_{A = a} h(a, W, X) · q(Z, a, X) dμ.
   Under the codebase's probability-ratio `q` convention there is no
   stratumOddsRatio weight here — the latent change of measure is
   absorbed into `q` itself by `likelihoodRatio_swapA_spec`.
2. `IsUpperEnvWZ` / `IsLowerEnvWZ`: same-arm joint-vs-product envelope,
   an a.e. inequality of σ_AX-measurable functions on `{A = a}`:
       μ[h · q | σ_AX] ≤ Uenv(a, X) · μ[h | σ_AX] · μ[q | σ_AX].
3. The bound is closed entirely on `{A = a}` (no fiber transport):
   apply the σ_AX-conditional pull-out
       ∫_{A=a} h · q dμ
           = ∫_{A=a} μ[h · q | σ_AX] dμ
   then `setIntegral_mono_ae` against the envelope, and finally collapse
   `μ[h | σ_AX] =ᵐ μ[Y | σ_AX]` (helper `condExp_Y_eq_condExp_h_arm_AX`)
   and `μ[q | σ_AX] =ᵐ stratumOddsRatio` (helper
   `condExp_q_eq_stratumOddsRatio_arm_AX`) on `{A = a}`. Both `h` and `q`
   disappear from the public statement.

## Main result

* `condMeanYofA_WZ_bounds` — sandwich bound on `E[Y(a) | A = ¬a]`,
  clamped by `[essinf Y, essup Y]` and the joint-WZ envelope bounds in
  the W-shaped observable form
  `stratumOddsRatio · Uenv(a, X) · μ[Y | σ_AX]` integrated over `{A = a}`.
-/

import Causalean.PO.ID.Partial.Proxy.Helpers

/-! # Two-proxy proximal partial-identification bounds

This file proves the two-proxy proximal partial-identification sandwich for the
off-arm counterfactual mean. The bridge-substitution identity
`condIntYofA_eq_hq_armSwap_twoProxy` moves the target to the observed treatment
arm; the joint W-Z envelope predicates `IsLowerEnvWZ` and `IsUpperEnvWZ` then
bound the bridge product by observable conditional means and stratum odds
ratios.

The main declaration is `condMeanYofA_WZ_bounds`, the Theorem 3 bound for
`condMeanYofA`. Its public statement contains only observable objects:
`stratumOddsRatio`, the envelope functions, and `μ[Y | σ_AX]`; the latent
bridges `h` and `q` are eliminated by the conditional-expectation collapse
lemmas.
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

/-! ### Two-proxy partial-identification bound (Theorem 3) -/

/-- **Theorem 3** (Ghassami-Shpitser-Tchetgen Tchetgen 2024, two-proxy
partial identification).

Given:
* `HA`     : the two-proxy assumption bundle (consistency, latent
             exchangeability, `W ⟂ Z | (A, U, X)` per Assumption 6, bridges
             `h` and `q`, product integrability of `h · q`, essential
             `Y`-bounds);
* `Lenv`, `Uenv` : lower / upper envelope functions for the same-arm
             joint-vs-product W-Z density ratio
                 ρ(w, z, x) = p(w, z | A=a, x) / (p(w | A=a, x) · p(z | A=a, x))
             (operationalised by `IsLowerEnvWZ` / `IsUpperEnvWZ`);
* `hμpos` : the off-arm stratum has positive mass.

Conclusion: `E[Y(a) | A = ¬a]` lies between the trivial essential bound
and the integrated envelope bound in the same observable form as the
W-only theorem (Theorem 1):

    p⁻¹ · ∫_{A=a} stratumOddsRatio · Lenv(a, X) · μ[Y | σ_AX] dμ
      ≤ E[Y(a) | A = ¬a]
      ≤ p⁻¹ · ∫_{A=a} stratumOddsRatio · Uenv(a, X) · μ[Y | σ_AX] dμ

where `p = μ{A ≠ a}.toReal`. The latent bridges `h`, `q` do not appear in
the public statement: `h` is collapsed to `μ[Y | σ_AX]` and `q` to
`stratumOddsRatio` on `{A = a}` via the helpers
`condExp_Y_eq_condExp_h_arm_AX` and `condExp_q_eq_stratumOddsRatio_arm_AX`. -/
theorem condMeanYofA_WZ_bounds
    (HA : POProximalSystem.TwoProxyAssumptions S μ) (a : Bool)
    (hAY : S.Avar.v ≠ S.Yvar.v)
    (Lenv Uenv : Bool × γ_X → ℝ)
    (hL : S.IsLowerEnvWZ μ a Lenv) (hU : S.IsUpperEnvWZ μ a Uenv)
    (hμpos : 0 < (μ {ω | S.A ω ≠ a}).toReal)
    -- Phase B integrability hypotheses (per project decision):
    -- the paper assumes implicit boundedness of the envelope and odds-ratio,
    -- which would make these L¹. We surface them as hypotheses here.
    (hU_envInt : Integrable (fun ω =>
          Uenv (a, S.X ω)
          * (μ[fun ω' => HA.h (a, S.W ω', S.X ω') | S.σ_AX]) ω
          * (μ[fun ω' => HA.q (S.Z ω', a, S.X ω') | S.σ_AX]) ω) μ)
    (hL_envInt : Integrable (fun ω =>
          Lenv (a, S.X ω)
          * (μ[fun ω' => HA.h (a, S.W ω', S.X ω') | S.σ_AX]) ω
          * (μ[fun ω' => HA.q (S.Z ω', a, S.X ω') | S.σ_AX]) ω) μ) :
    max (Classical.choose HA.Y_bdd_below)
        ((μ {ω | S.A ω ≠ a}).toReal⁻¹ *
         ∫ ω in {ω | S.A ω = a},
           S.stratumOddsRatio μ a ω * Lenv (a, S.X ω) * (μ[S.Y | S.σ_AX]) ω ∂μ)
      ≤ S.condMeanYofA μ a
    ∧ S.condMeanYofA μ a ≤
    min (Classical.choose HA.Y_bdd_above)
        ((μ {ω | S.A ω ≠ a}).toReal⁻¹ *
         ∫ ω in {ω | S.A ω = a},
           S.stratumOddsRatio μ a ω * Uenv (a, S.X ω) * (μ[S.Y | S.σ_AX]) ω ∂μ)
    := by
  -- Notation.
  set s' : Set P.Ω := {ω | S.A ω ≠ a} with hs'_def
  set s : Set P.Ω := {ω | S.A ω = a} with hs_def
  set p : ℝ := (μ s').toReal with hp_def
  -- Bridge identity (same-arm form, prob-ratio q convention — no stratumOddsRatio):
  --   ∫_{A≠a} Y(a) dμ = ∫_{A=a} h(a,W,X) · q(Z,a,X) dμ.
  have hBridge : (∫ ω in s', S.YofA a ω ∂μ)
      = ∫ ω in s, HA.h (a, S.W ω, S.X ω) * HA.q (S.Z ω, a, S.X ω) ∂μ :=
    POProximalSystem.condIntYofA_eq_hq_armSwap_twoProxy HA a hAY
  have hp_inv_nn : 0 ≤ p⁻¹ := le_of_lt (inv_pos.mpr hμpos)
  -- Trivial clamps via essential Y bounds (independent of the envelope chain).
  have hU_triv : S.condMeanYofA μ a ≤ Classical.choose HA.Y_bdd_above := by
    set M : ℝ := Classical.choose HA.Y_bdd_above with hM_def
    have hM : ∀ᵐ ω ∂μ, S.Y ω ≤ M := Classical.choose_spec HA.Y_bdd_above
    have hYa : ∀ᵐ ω ∂μ, S.YofA a ω ≤ M :=
      POProximalSystem.YofA_essbound_above HA.consistency (HA.latent_exch a) hAY
        (HA.overlap_strong a) hM
    have hs'_meas : MeasurableSet s' := by
      have : MeasurableSet ({a} : Set Bool) := measurableSet_singleton a
      have hsm : MeasurableSet s := S.measurable_A this
      have h_compl : s' = sᶜ := by ext ω; simp [s', s]
      rw [h_compl]; exact hsm.compl
    have hYaInt : Integrable (S.YofA a) μ := HA.integrable_YofA a
    have h_le : (∫ ω in s', S.YofA a ω ∂μ) ≤ ∫ _ in s', M ∂μ := by
      refine setIntegral_mono_ae ?_ ?_ hYa
      · exact hYaInt.integrableOn
      · exact integrableOn_const
    have h_const : (∫ _ in s', M ∂μ) = M * p := by
      rw [setIntegral_const]
      simp [hp_def, MeasureTheory.measureReal_def, mul_comm]
    have h_int_le : (∫ ω in s', S.YofA a ω ∂μ) ≤ M * p := h_le.trans_eq h_const
    have hgoal : p⁻¹ * (∫ ω in s', S.YofA a ω ∂μ) ≤ p⁻¹ * (M * p) :=
      mul_le_mul_of_nonneg_left h_int_le hp_inv_nn
    have hp_ne : p ≠ 0 := ne_of_gt hμpos
    have h_eq : p⁻¹ * (M * p) = M := by field_simp
    rw [h_eq] at hgoal
    unfold POProximalSystem.condMeanYofA
    exact hgoal
  have hL_triv : Classical.choose HA.Y_bdd_below ≤ S.condMeanYofA μ a := by
    set M : ℝ := Classical.choose HA.Y_bdd_below with hM_def
    have hM : ∀ᵐ ω ∂μ, M ≤ S.Y ω := Classical.choose_spec HA.Y_bdd_below
    have hYa : ∀ᵐ ω ∂μ, M ≤ S.YofA a ω :=
      POProximalSystem.YofA_essbound_below HA.consistency (HA.latent_exch a) hAY
        (HA.overlap_strong a) hM
    have hs'_meas : MeasurableSet s' := by
      have : MeasurableSet ({a} : Set Bool) := measurableSet_singleton a
      have hsm : MeasurableSet s := S.measurable_A this
      have h_compl : s' = sᶜ := by ext ω; simp [s', s]
      rw [h_compl]; exact hsm.compl
    have hYaInt : Integrable (S.YofA a) μ := HA.integrable_YofA a
    have h_le : (∫ _ in s', M ∂μ) ≤ ∫ ω in s', S.YofA a ω ∂μ := by
      refine setIntegral_mono_ae ?_ ?_ hYa
      · exact integrableOn_const
      · exact hYaInt.integrableOn
    have h_const : (∫ _ in s', M ∂μ) = M * p := by
      rw [setIntegral_const]
      simp [hp_def, MeasureTheory.measureReal_def, mul_comm]
    have h_int_le : M * p ≤ (∫ ω in s', S.YofA a ω ∂μ) := h_const ▸ h_le
    have hgoal : p⁻¹ * (M * p) ≤ p⁻¹ * (∫ ω in s', S.YofA a ω ∂μ) :=
      mul_le_mul_of_nonneg_left h_int_le hp_inv_nn
    have hp_ne : p ≠ 0 := ne_of_gt hμpos
    have h_eq : p⁻¹ * (M * p) = M := by field_simp
    rw [h_eq] at hgoal
    unfold POProximalSystem.condMeanYofA
    exact hgoal
  -- ============================================================
  -- ENVELOPE CHAIN (same-arm; no fiber transport)
  --
  -- After the same-arm bridge identity ∫_{A≠a} Y(a) dμ = ∫_{A=a} h·q dμ,
  -- both sides of the envelope chain live on `{A = a}`. Internal chain
  -- (one direction shown):
  --
  --   ∫_{A=a} h(a,W,X) · q(Z,a,X) dμ
  --     = ∫_{A=a} μ[h · q | σ_AX] dμ                           (σ_AX pull-out)
  --     ≤ ∫_{A=a} Uenv(a,X) · μ[h|σ_AX] · μ[q|σ_AX] dμ          (hU.2)
  --     = ∫_{A=a} Uenv(a,X) · μ[Y|σ_AX] · stratumOddsRatio dμ
  --                                  (helpers: μ[h|σ_AX]→μ[Y|σ_AX],
  --                                            μ[q|σ_AX]→stratumOddsRatio
  --                                   on `restrict {A=a}`)
  --     = ∫_{A=a} stratumOddsRatio · Uenv(a,X) · μ[Y|σ_AX] dμ.
  --
  -- The σ_AX-pull-out step is identical to the W-only case in `WBased.lean`.
  -- The two collapses use existing helpers:
  -- `condExp_Y_eq_condExp_h_arm_AX` and
  -- `condExp_q_eq_stratumOddsRatio_arm_AX`.
  -- ============================================================
  -- Notation for the bridge factors and their measurability.
  set φW : γ_W × γ_X → ℝ := fun p => HA.h (a, p.1, p.2) with hφW_def
  set φZ : γ_Z × γ_X → ℝ := fun p => HA.q (p.1, a, p.2) with hφZ_def
  have hφW_meas : Measurable φW := by
    have : Measurable (fun p : γ_W × γ_X => (a, p.1, p.2)) :=
      Measurable.prodMk measurable_const
        (Measurable.prodMk measurable_fst measurable_snd)
    exact HA.measurable_h.comp this
  have hφZ_meas : Measurable φZ := by
    have : Measurable (fun p : γ_Z × γ_X => (p.1, a, p.2)) :=
      Measurable.prodMk measurable_fst
        (Measurable.prodMk measurable_const measurable_snd)
    exact HA.measurable_q.comp this
  have hφW_nn : ∀ x, 0 ≤ φW x := fun _ => HA.h_nonneg _
  have hφZ_nn : ∀ x, 0 ≤ φZ x := fun _ => HA.q_nonneg _
  -- Integrabilities for the envelope predicate.
  have hφW_int : Integrable (fun ω => φW (S.W ω, S.X ω)) μ :=
    HA.integrable_h_arm a
  have hφZ_int : Integrable (fun ω => φZ (S.Z ω, S.X ω)) μ :=
    HA.integrable_q a
  have hφWZ_int : Integrable
      (fun ω => φW (S.W ω, S.X ω) * φZ (S.Z ω, S.X ω)) μ :=
    HA.integrable_hq_arm a
  -- σ_AX-measurability of {A = a}.
  have hs_meas : MeasurableSet s := S.measurable_A (measurableSet_singleton a)
  have hs_in_AX : MeasurableSet[S.σ_AX] s := by
    refine ⟨Prod.fst ⁻¹' {a}, ?_, ?_⟩
    · exact measurable_fst (measurableSet_singleton a)
    · ext ω; simp [s, POProximalSystem.AX]
  -- Collapse identities.
  have hCollapse_h :
      μ[S.Y | S.σ_AX] =ᵐ[μ.restrict s]
      μ[fun ω => HA.h (a, S.W ω, S.X ω) | S.σ_AX] :=
    POProximalSystem.condExp_Y_eq_condExp_h_arm_AX_twoProxy HA a hAY
  have hCollapse_q :
      (μ[fun ω => HA.q (S.Z ω, a, S.X ω) | S.σ_AX])
        =ᵐ[μ.restrict s] S.stratumOddsRatio μ a :=
    POProximalSystem.condExp_q_eq_stratumOddsRatio_arm_AX HA a hAY
  -- Step (ii): σ_AX pull-out.
  have hPull : ∫ ω in s,
        HA.h (a, S.W ω, S.X ω) * HA.q (S.Z ω, a, S.X ω) ∂μ
      = ∫ ω in s,
        (μ[fun ω => φW (S.W ω, S.X ω) * φZ (S.Z ω, S.X ω) | S.σ_AX]) ω ∂μ := by
    have h_setInt :
        ∫ ω in s,
          (μ[fun ω => φW (S.W ω, S.X ω) * φZ (S.Z ω, S.X ω) | S.σ_AX]) ω ∂μ
        = ∫ ω in s, φW (S.W ω, S.X ω) * φZ (S.Z ω, S.X ω) ∂μ :=
      setIntegral_condExp S.σ_AX_le hφWZ_int hs_in_AX
    simp only [φW, φZ] at h_setInt ⊢
    exact h_setInt.symm
  -- Step (iii): apply hU.2 envelope and integrate.
  have hEnvAE := hU.2 φW φZ hφW_meas hφZ_meas hφW_nn hφZ_nn hφWZ_int hφW_int hφZ_int
  -- The envelope-bound integrand on the rhs.
  have hEnvBound_int : IntegrableOn
      (fun ω => Uenv (a, S.X ω)
        * (μ[fun ω' => φW (S.W ω', S.X ω') | S.σ_AX]) ω
        * (μ[fun ω' => φZ (S.Z ω', S.X ω') | S.σ_AX]) ω) s μ := by
    simp only [φW, φZ]
    exact hU_envInt.integrableOn
  have hCondMul_int : IntegrableOn
      (fun ω => (μ[fun ω => φW (S.W ω, S.X ω) * φZ (S.Z ω, S.X ω) | S.σ_AX]) ω) s μ :=
    integrable_condExp.integrableOn
  -- setIntegral_mono_ae over {A = a}.
  have hMono :
      ∫ ω in s, (μ[fun ω => φW (S.W ω, S.X ω) * φZ (S.Z ω, S.X ω) | S.σ_AX]) ω ∂μ
      ≤ ∫ ω in s,
          Uenv (a, S.X ω)
          * (μ[fun ω' => φW (S.W ω', S.X ω') | S.σ_AX]) ω
          * (μ[fun ω' => φZ (S.Z ω', S.X ω') | S.σ_AX]) ω ∂μ :=
    setIntegral_mono_ae_restrict hCondMul_int hEnvBound_int hEnvAE
  -- Step (iv)+(v): collapse h → Y and q → stratumOddsRatio on {A=a}, and rearrange.
  have hRewrite :
      ∫ ω in s,
          Uenv (a, S.X ω)
          * (μ[fun ω' => φW (S.W ω', S.X ω') | S.σ_AX]) ω
          * (μ[fun ω' => φZ (S.Z ω', S.X ω') | S.σ_AX]) ω ∂μ
      = ∫ ω in s,
          S.stratumOddsRatio μ a ω * Uenv (a, S.X ω) * (μ[S.Y | S.σ_AX]) ω ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hCollapse_h, hCollapse_q] with ω hh hq
    simp only [φW, φZ] at *
    rw [hh, hq]; ring
  -- Assemble.
  have hU_arm : (∫ ω in s', S.YofA a ω ∂μ)
      ≤ ∫ ω in s,
          S.stratumOddsRatio μ a ω * Uenv (a, S.X ω)
          * (μ[S.Y | S.σ_AX]) ω ∂μ := by
    rw [hBridge, hPull]
    exact hMono.trans (le_of_eq hRewrite)
  -- ----- LOWER -----
  have hEnvAE_L := hL.2 φW φZ hφW_meas hφZ_meas hφW_nn hφZ_nn hφWZ_int hφW_int hφZ_int
  have hEnvBound_L_int : IntegrableOn
      (fun ω => Lenv (a, S.X ω)
        * (μ[fun ω' => φW (S.W ω', S.X ω') | S.σ_AX]) ω
        * (μ[fun ω' => φZ (S.Z ω', S.X ω') | S.σ_AX]) ω) s μ := by
    simp only [φW, φZ]
    exact hL_envInt.integrableOn
  have hMono_L :
      ∫ ω in s,
          Lenv (a, S.X ω)
          * (μ[fun ω' => φW (S.W ω', S.X ω') | S.σ_AX]) ω
          * (μ[fun ω' => φZ (S.Z ω', S.X ω') | S.σ_AX]) ω ∂μ
      ≤ ∫ ω in s, (μ[fun ω => φW (S.W ω, S.X ω) * φZ (S.Z ω, S.X ω) | S.σ_AX]) ω ∂μ :=
    setIntegral_mono_ae_restrict hEnvBound_L_int hCondMul_int hEnvAE_L
  have hRewrite_L :
      ∫ ω in s,
          Lenv (a, S.X ω)
          * (μ[fun ω' => φW (S.W ω', S.X ω') | S.σ_AX]) ω
          * (μ[fun ω' => φZ (S.Z ω', S.X ω') | S.σ_AX]) ω ∂μ
      = ∫ ω in s,
          S.stratumOddsRatio μ a ω * Lenv (a, S.X ω) * (μ[S.Y | S.σ_AX]) ω ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hCollapse_h, hCollapse_q] with ω hh hq
    simp only [φW, φZ] at *
    rw [hh, hq]; ring
  have hL_arm : (∫ ω in s,
          S.stratumOddsRatio μ a ω * Lenv (a, S.X ω)
          * (μ[S.Y | S.σ_AX]) ω ∂μ)
      ≤ (∫ ω in s', S.YofA a ω ∂μ) := by
    rw [hBridge, hPull, ← hRewrite_L]
    exact hMono_L
  -- Divide by p = μ(s').toReal to get bounds on `condMeanYofA`.
  have hU_cond : S.condMeanYofA μ a
      ≤ p⁻¹ *
        ∫ ω in s,
          S.stratumOddsRatio μ a ω * Uenv (a, S.X ω)
          * (μ[S.Y | S.σ_AX]) ω ∂μ := by
    have h := mul_le_mul_of_nonneg_left hU_arm hp_inv_nn
    unfold POProximalSystem.condMeanYofA
    exact h
  have hL_cond : p⁻¹ *
        ∫ ω in s,
          S.stratumOddsRatio μ a ω * Lenv (a, S.X ω)
          * (μ[S.Y | S.σ_AX]) ω ∂μ
      ≤ S.condMeanYofA μ a := by
    have h := mul_le_mul_of_nonneg_left hL_arm hp_inv_nn
    unfold POProximalSystem.condMeanYofA
    exact h
  -- ============================================================
  -- ASSEMBLE
  -- ============================================================
  refine ⟨?_, ?_⟩
  · exact max_le hL_triv hL_cond
  · exact le_min hU_triv hU_cond

end POProximalSystem

end PO
end Causalean
