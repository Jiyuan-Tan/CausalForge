/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Proximal partial identification — W-based bounds (Theorem 1, Corollary 1)

Bounds on `E[Y(a) | A = ¬a]` (Theorem 1) and on `E[Y(a)]` (Corollary 1)
under the W-only proxy bundle of Ghassami-Shpitser-Tchetgen Tchetgen
(2024, arXiv 2304.04374, Section 2.1):

  consistency  +  Y(a) ⟂ A | (U, X)  +  W ⟂ A | (U, X)  +  outcome bridge `h`.

The proof template mirrors `TwoProxy.lean`: the outcome-bridge identity
`condIntYofA_eq_h_arm` reduces `∫_{A=¬a} Y(a) dμ` to the bridge moment
`∫_{A=¬a} h(a, W, X) dμ`, then the W-density-ratio envelope
(`IsLowerEnvW` / `IsUpperEnvW`) bounds that moment by an integral over
`{A = a}` against `stratumOddsRatio · Lenv` / `stratumOddsRatio · Uenv`.

## Main results

* `condMeanYofA_W_bounds` — Theorem 1: sandwich on `E[Y(a) | A = ¬a]`,
  clamped by the trivial essential-`Y` bounds and the W-envelope bounds.
* `meanYofA_W_bounds`     — Corollary 1: marginal version, derived from
  Theorem 1 by adding the point-identified `∫_{A = a} Y dμ`
  (`meanYofA_eq_strata`).
-/

import Causalean.PO.ID.Partial.Proxy.Helpers

/-! # W-based proximal partial-identification bounds

This file proves the W-only proximal partial-identification bounds of
Ghassami-Shpitser-Tchetgen Tchetgen for a potential-outcome system with an
outcome-inducing proxy `W`. The outcome bridge rewrites the off-arm target
`E[Y(a) | A != a]` as a bridge moment, and the W-density-ratio envelope
predicates `IsLowerEnvW` and `IsUpperEnvW` turn that moment into observable
integrals over the on-arm stratum.

Main declarations:
* `condMeanYofA_W_bounds` is the conditional Theorem 1 sandwich for
  `condMeanYofA`, combining the envelope bounds with the trivial essential
  bounds on `Y`.
* `meanYofA_W_bounds` is the marginal Corollary 1 sandwich for `meanYofA`,
  obtained by adding the consistency-identified `{A = a}` contribution.
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

/-! ### Theorem 1 — bound on `E[Y(a) | A = ¬a]` -/

/-- **Theorem 1** (Ghassami-Shpitser-Tchetgen Tchetgen 2024, W-only
partial identification).

Given:
* `HA`     : the W-only assumption bundle (consistency, latent
             exchangeability, `W ⟂ A | (U, X)`, outcome bridge `h`,
             essential `Y`-bounds);
* `Lenv`, `Uenv` : lower/upper envelope functions for the W-density ratio
                   `r(w, x) = p(w | A = ¬a, x) / p(w | A = a, x)`,
             operationalised by the integrated forms `IsLowerEnvW`,
             `IsUpperEnvW`;
* `hμpos` : the off-arm stratum has positive mass.

Conclusion: the conditional target `E[Y(a) | A = ¬a]` lies between the
trivial essential bound and the integrated envelope bound, on each side. -/
theorem condMeanYofA_W_bounds
    (HA : POProximalSystem.WBasedAssumptions S μ) (a : Bool)
    (hAY : S.Avar.v ≠ S.Yvar.v)
    (Lenv Uenv : Bool × γ_X → ℝ)
    (hL : S.IsLowerEnvW μ a Lenv) (hU : S.IsUpperEnvW μ a Uenv)
    (hμpos : 0 < (μ {ω | S.A ω ≠ a}).toReal)
    (hU_int_h : Integrable
        (fun ω => S.stratumOddsRatio μ a ω * Uenv (a, S.X ω) *
          HA.h (a, S.W ω, S.X ω)) μ)
    (hL_int_h : Integrable
        (fun ω => S.stratumOddsRatio μ a ω * Lenv (a, S.X ω) *
          HA.h (a, S.W ω, S.X ω)) μ) :
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
  -- φ : the bridge integrand viewed as a function of (W, X).
  let φ : γ_W × γ_X → ℝ := fun wx => HA.h (a, wx.1, wx.2)
  -- Measurability of φ.
  have h_meas_φ : Measurable φ := by
    have hp : Measurable (fun wx : γ_W × γ_X => (a, wx.1, wx.2)) := by
      refine Measurable.prodMk measurable_const ?_
      exact Measurable.prodMk measurable_fst measurable_snd
    exact HA.measurable_h.comp hp
  -- Integrability of `ω ↦ φ (W ω, X ω) = h(a, W ω, X ω)`.
  have h_int_φ : Integrable (fun ω => φ (S.W ω, S.X ω)) μ := HA.integrable_h_arm a
  -- Bridge substitution: ∫_{A≠a} Y(a) dμ = ∫_{A≠a} h(a, W, X) dμ.
  have hBridge : (∫ ω in s', S.YofA a ω ∂μ)
      = (∫ ω in s', HA.h (a, S.W ω, S.X ω) ∂μ) :=
    POProximalSystem.condIntYofA_eq_h_arm HA a hAY
  -- ============================================================
  -- UPPER BOUND
  -- ============================================================
  -- Step U1: nonnegativity of φ. The paper assumes Y ≥ 0 ⇒ h ≥ 0. The
  -- WBased bundle does not bundle nonnegativity of `h`; this is the same
  -- gap as in `TwoProxy.lean`.
  have h_nonneg_φ : ∀ x, 0 ≤ φ x := by
    intro x; exact HA.h_nonneg _
  -- Step U2: apply the upper envelope predicate to φ.
  have hU_int : ∫ ω in s', φ (S.W ω, S.X ω) ∂μ
      ≤ ∫ ω in s,
          S.stratumOddsRatio μ a ω * Uenv (a, S.X ω) * φ (S.W ω, S.X ω) ∂μ :=
    hU.2 φ h_meas_φ h_nonneg_φ h_int_φ hU_int_h
  -- Step U3: chain bridge + envelope to bound ∫_{A≠a} Y(a).
  have hU_arm : (∫ ω in s', S.YofA a ω ∂μ)
      ≤ ∫ ω in s,
          S.stratumOddsRatio μ a ω * Uenv (a, S.X ω) * HA.h (a, S.W ω, S.X ω) ∂μ := by
    rw [hBridge]; exact hU_int
  -- Step U4: divide by μ(s').toReal to get a bound on `condMeanYofA`.
  have hp_inv_nn : 0 ≤ p⁻¹ := le_of_lt (inv_pos.mpr hμpos)
  -- Collapse: rewrite the integral on {A=a} with `h(a,W,X)` factor as
  -- the same integral with `μ[Y | σ_AX]` factor. Strategy:
  --   (i)  σ_AX-measurable factor `f := stratumOddsRatio · Uenv(a,X)`
  --        pulls into the conditional expectation:
  --          μ[f · h(a,W,X) | σ_AX] =ᵐ f · μ[h(a,W,X) | σ_AX].
  --   (ii) `setIntegral_condExp` on σ_AX-meas set s = {A=a} gives
  --          ∫_s f · h(a,W,X) dμ = ∫_s μ[f · h(a,W,X) | σ_AX] dμ.
  --   (iii) Combine: ∫_s f · h(a,W,X) dμ = ∫_s f · μ[h(a,W,X) | σ_AX] dμ.
  --   (iv) Collapse helper on s: μ[h(a,W,X)|σ_AX] =ᵐ μ[Y|σ_AX] on `restrict s`.
  --   (v)  Hence ∫_s f · μ[h(a,W,X) | σ_AX] dμ = ∫_s f · μ[Y | σ_AX] dμ
  --        (`integral_congr_ae`).
  have hs_meas : MeasurableSet s := S.measurable_A (measurableSet_singleton a)
  have hs_in_AX : MeasurableSet[S.σ_AX] s := by
    refine ⟨Prod.fst ⁻¹' {a}, ?_, ?_⟩
    · exact measurable_fst (measurableSet_singleton a)
    · ext ω; simp [s, POProximalSystem.AX]
  have hCollapse :
      μ[S.Y | S.σ_AX] =ᵐ[μ.restrict s]
      μ[fun ω => HA.h (a, S.W ω, S.X ω) | S.σ_AX] :=
    POProximalSystem.condExp_Y_eq_condExp_h_arm_AX HA a hAY
  -- σ_X / σ_AX strong-measurability of the envelope-and-X factor.
  have hX_σX : Measurable[S.σ_X] S.X := Measurable.of_comap_le le_rfl
  have hUenv_σX : Measurable[S.σ_X] (fun ω => Uenv (a, S.X ω)) := by
    have hU_meas : Measurable Uenv := hU.1
    have hpair : Measurable[S.σ_X] (fun ω => (a, S.X ω)) :=
      Measurable.prodMk measurable_const hX_σX
    exact hU_meas.comp hpair
  have hLenv_σX : Measurable[S.σ_X] (fun ω => Lenv (a, S.X ω)) := by
    have hL_meas : Measurable Lenv := hL.1
    have hpair : Measurable[S.σ_X] (fun ω => (a, S.X ω)) :=
      Measurable.prodMk measurable_const hX_σX
    exact hL_meas.comp hpair
  have hSOR_σX : StronglyMeasurable[S.σ_X] (S.stratumOddsRatio μ a) := by
    unfold POProximalSystem.stratumOddsRatio
    refine ((stronglyMeasurable_condExp.measurable).div
      (stronglyMeasurable_condExp.measurable)).stronglyMeasurable
  have hUenv_σAX : Measurable[S.σ_AX] (fun ω => Uenv (a, S.X ω)) :=
    hUenv_σX.mono S.σ_X_le_σ_AX le_rfl
  have hLenv_σAX : Measurable[S.σ_AX] (fun ω => Lenv (a, S.X ω)) :=
    hLenv_σX.mono S.σ_X_le_σ_AX le_rfl
  have hSOR_σAX : StronglyMeasurable[S.σ_AX] (S.stratumOddsRatio μ a) :=
    hSOR_σX.mono S.σ_X_le_σ_AX
  have hfU_sm : StronglyMeasurable[S.σ_AX]
      (fun ω => S.stratumOddsRatio μ a ω * Uenv (a, S.X ω)) :=
    hSOR_σAX.mul hUenv_σAX.stronglyMeasurable
  have hfL_sm : StronglyMeasurable[S.σ_AX]
      (fun ω => S.stratumOddsRatio μ a ω * Lenv (a, S.X ω)) :=
    hSOR_σAX.mul hLenv_σAX.stronglyMeasurable
  have hh_int : Integrable (fun ω => HA.h (a, S.W ω, S.X ω)) μ :=
    HA.integrable_h_arm a
  -- L1 + collapse: replace `h(a,W,X)` with `μ[Y|σ_AX]` on the {A=a} integral.
  have hU_collapse : (∫ ω in s,
          S.stratumOddsRatio μ a ω * Uenv (a, S.X ω) * HA.h (a, S.W ω, S.X ω) ∂μ)
      = ∫ ω in s,
          S.stratumOddsRatio μ a ω * Uenv (a, S.X ω) * (μ[S.Y | S.σ_AX]) ω ∂μ := by
    have h1 :=
      setIntegral_mul_condExp_of_stronglyMeasurableLeft S.σ_AX_le hfU_sm
        hh_int hU_int_h hs_in_AX
    have h_ae : (fun ω => S.stratumOddsRatio μ a ω * Uenv (a, S.X ω)
            * (μ[fun ω' => HA.h (a, S.W ω', S.X ω')|S.σ_AX]) ω)
        =ᵐ[μ.restrict s]
        (fun ω => S.stratumOddsRatio μ a ω * Uenv (a, S.X ω)
            * (μ[S.Y | S.σ_AX]) ω) := by
      filter_upwards [hCollapse] with ω hω
      simp [hω]
    exact h1.trans (integral_congr_ae h_ae)
  have hL_collapse : (∫ ω in s,
          S.stratumOddsRatio μ a ω * Lenv (a, S.X ω) * HA.h (a, S.W ω, S.X ω) ∂μ)
      = ∫ ω in s,
          S.stratumOddsRatio μ a ω * Lenv (a, S.X ω) * (μ[S.Y | S.σ_AX]) ω ∂μ := by
    have h1 :=
      setIntegral_mul_condExp_of_stronglyMeasurableLeft S.σ_AX_le hfL_sm
        hh_int hL_int_h hs_in_AX
    have h_ae : (fun ω => S.stratumOddsRatio μ a ω * Lenv (a, S.X ω)
            * (μ[fun ω' => HA.h (a, S.W ω', S.X ω')|S.σ_AX]) ω)
        =ᵐ[μ.restrict s]
        (fun ω => S.stratumOddsRatio μ a ω * Lenv (a, S.X ω)
            * (μ[S.Y | S.σ_AX]) ω) := by
      filter_upwards [hCollapse] with ω hω
      simp [hω]
    exact h1.trans (integral_congr_ae h_ae)
  -- Step U5 (collapse the {A=a} integral): replace `h(a,W,X)` with `μ[Y|σ_AX]`.
  have hU_cond : S.condMeanYofA μ a
      ≤ p⁻¹ *
        ∫ ω in s,
          S.stratumOddsRatio μ a ω * Uenv (a, S.X ω) * (μ[S.Y | S.σ_AX]) ω ∂μ := by
    have hgoal := mul_le_mul_of_nonneg_left hU_arm hp_inv_nn
    rw [hU_collapse] at hgoal
    unfold POProximalSystem.condMeanYofA
    exact hgoal
  -- Step U5: trivial upper clamp via Y_bdd_above. Needs `Y(a) ≤ essup Y` a.e.
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
  -- ============================================================
  -- LOWER BOUND (mirror of upper)
  -- ============================================================
  have hL_int : ∫ ω in s,
        S.stratumOddsRatio μ a ω * Lenv (a, S.X ω) * φ (S.W ω, S.X ω) ∂μ
      ≤ ∫ ω in s', φ (S.W ω, S.X ω) ∂μ :=
    hL.2 φ h_meas_φ h_nonneg_φ h_int_φ hL_int_h
  have hL_arm : (∫ ω in s,
          S.stratumOddsRatio μ a ω * Lenv (a, S.X ω) * HA.h (a, S.W ω, S.X ω) ∂μ)
      ≤ (∫ ω in s', S.YofA a ω ∂μ) := by
    rw [hBridge]; exact hL_int
  have hL_cond : p⁻¹ *
        ∫ ω in s,
          S.stratumOddsRatio μ a ω * Lenv (a, S.X ω) * (μ[S.Y | S.σ_AX]) ω ∂μ
      ≤ S.condMeanYofA μ a := by
    have hgoal := mul_le_mul_of_nonneg_left hL_arm hp_inv_nn
    rw [hL_collapse] at hgoal
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
  -- ASSEMBLE
  -- ============================================================
  refine ⟨?_, ?_⟩
  · -- max (essinf Y) (envelope-lower) ≤ condMeanYofA
    exact max_le hL_triv hL_cond
  · -- condMeanYofA ≤ min (essup Y) (envelope-upper)
    exact le_min hU_triv hU_cond

/-! ### Corollary 1 — bound on the marginal `E[Y(a)]` -/

/-- **Corollary 1** (Ghassami-Shpitser-Tchetgen Tchetgen 2024, W-only
marginal version).

Marginal version of Theorem 1. The `{A = a}` stratum integral is
point-identified via consistency, so only the `{A = ¬a}` stratum needs
the envelope bound. The overall bound is the **maximum of the trivial
clamp and the envelope clamp** on each side, mirroring the conditional
form of Theorem 1:

  max(infY · μ{A≠a}, envelope-lower) + ∫_{A=a} Y dμ
    ≤ E[Y(a)]
    ≤ min(supY · μ{A≠a}, envelope-upper) + ∫_{A=a} Y dμ.

The trivial clamp `infY · μ{A≠a} + ∫_{A=a} Y dμ` (and its upper-side
mirror) corresponds to the worst-case potential outcome on the off-arm
stratum; the envelope clamp uses the W-density-ratio envelope. The bound
is in observable-data form: `μ[Y | σ_AX] = E[Y | A, X]` is the observable
conditional expectation of `Y`, replacing the latent bridge `h(a, W, X)`
via the collapse identity `condExp_Y_eq_condExp_h_arm_AX`.

Obtained from `condMeanYofA_W_bounds`'s envelope and trivial clamps by
`meanYofA_eq_strata`. -/
theorem meanYofA_W_bounds
    (HA : POProximalSystem.WBasedAssumptions S μ) (a : Bool)
    (hAY : S.Avar.v ≠ S.Yvar.v)
    (Lenv Uenv : Bool × γ_X → ℝ)
    (hL : S.IsLowerEnvW μ a Lenv) (hU : S.IsUpperEnvW μ a Uenv)
    (hU_int_h : Integrable
        (fun ω => S.stratumOddsRatio μ a ω * Uenv (a, S.X ω) *
          HA.h (a, S.W ω, S.X ω)) μ)
    (hL_int_h : Integrable
        (fun ω => S.stratumOddsRatio μ a ω * Lenv (a, S.X ω) *
          HA.h (a, S.W ω, S.X ω)) μ)
    (hU_int_Y : Integrable
        (fun ω => S.stratumOddsRatio μ a ω * Uenv (a, S.X ω) *
          (μ[S.Y | S.σ_AX]) ω) μ)
    (hL_int_Y : Integrable
        (fun ω => S.stratumOddsRatio μ a ω * Lenv (a, S.X ω) *
          (μ[S.Y | S.σ_AX]) ω) μ) :
    max (Classical.choose HA.Y_bdd_below * (μ {ω | S.A ω ≠ a}).toReal)
        (∫ ω in {ω | S.A ω = a},
          S.stratumOddsRatio μ a ω * Lenv (a, S.X ω) * (μ[S.Y | S.σ_AX]) ω ∂μ)
        + (∫ ω in {ω | S.A ω = a}, S.Y ω ∂μ)
      ≤ S.meanYofA μ a
    ∧ S.meanYofA μ a ≤
      min (Classical.choose HA.Y_bdd_above * (μ {ω | S.A ω ≠ a}).toReal)
          (∫ ω in {ω | S.A ω = a},
            S.stratumOddsRatio μ a ω * Uenv (a, S.X ω) * (μ[S.Y | S.σ_AX]) ω ∂μ)
        + (∫ ω in {ω | S.A ω = a}, S.Y ω ∂μ) := by
  -- Notation.
  set s' : Set P.Ω := {ω | S.A ω ≠ a} with hs'_def
  set s : Set P.Ω := {ω | S.A ω = a} with hs_def
  set p : ℝ := (μ s').toReal with hp_def
  -- φ : the bridge integrand viewed as a function of (W, X).
  let φ : γ_W × γ_X → ℝ := fun wx => HA.h (a, wx.1, wx.2)
  have h_meas_φ : Measurable φ := by
    have hp : Measurable (fun wx : γ_W × γ_X => (a, wx.1, wx.2)) := by
      refine Measurable.prodMk measurable_const ?_
      exact Measurable.prodMk measurable_fst measurable_snd
    exact HA.measurable_h.comp hp
  have h_int_φ : Integrable (fun ω => φ (S.W ω, S.X ω)) μ := HA.integrable_h_arm a
  -- Bridge nonnegativity (paper: Y ≥ 0 ⇒ h ≥ 0).
  have h_nonneg_φ : ∀ x, 0 ≤ φ x := by
    intro x; exact HA.h_nonneg _
  -- Bridge substitution: ∫_{A≠a} Y(a) dμ = ∫_{A≠a} h(a, W, X) dμ.
  have hBridge : (∫ ω in s', S.YofA a ω ∂μ)
      = (∫ ω in s', HA.h (a, S.W ω, S.X ω) ∂μ) :=
    POProximalSystem.condIntYofA_eq_h_arm HA a hAY
  -- Marginalisation identity: meanYofA = ∫_{A≠a} Y(a) + ∫_{A=a} Y.
  have hsplit : S.meanYofA μ a
      = (∫ ω in s', S.YofA a ω ∂μ) + (∫ ω in s, S.Y ω ∂μ) :=
    POProximalSystem.meanYofA_eq_strata (S := S) (μ := μ)
      HA.consistency a hAY (HA.integrable_YofA a)
  -- {A ≠ a} is measurable.
  have hs'_meas : MeasurableSet s' := by
    have : MeasurableSet ({a} : Set Bool) := measurableSet_singleton a
    have hsm : MeasurableSet s := S.measurable_A this
    have h_compl : s' = sᶜ := by ext ω; simp [s', s]
    rw [h_compl]; exact hsm.compl
  -- ============================================================
  -- TRIVIAL CLAMPS via essential Y bounds on the off-arm stratum.
  -- ============================================================
  have hU_triv_arm : (∫ ω in s', S.YofA a ω ∂μ)
      ≤ Classical.choose HA.Y_bdd_above * p := by
    set M : ℝ := Classical.choose HA.Y_bdd_above with hM_def
    have hM : ∀ᵐ ω ∂μ, S.Y ω ≤ M := Classical.choose_spec HA.Y_bdd_above
    have hYa : ∀ᵐ ω ∂μ, S.YofA a ω ≤ M :=
      POProximalSystem.YofA_essbound_above HA.consistency (HA.latent_exch a) hAY
        (HA.overlap_strong a) hM
    have hYaInt : Integrable (S.YofA a) μ := HA.integrable_YofA a
    have h_le : (∫ ω in s', S.YofA a ω ∂μ) ≤ ∫ _ in s', M ∂μ := by
      refine setIntegral_mono_ae ?_ ?_ hYa
      · exact hYaInt.integrableOn
      · exact integrableOn_const
    have h_const : (∫ _ in s', M ∂μ) = M * p := by
      rw [setIntegral_const]
      simp [hp_def, MeasureTheory.measureReal_def, mul_comm]
    exact h_le.trans_eq h_const
  have hL_triv_arm : Classical.choose HA.Y_bdd_below * p
      ≤ (∫ ω in s', S.YofA a ω ∂μ) := by
    set M : ℝ := Classical.choose HA.Y_bdd_below with hM_def
    have hM : ∀ᵐ ω ∂μ, M ≤ S.Y ω := Classical.choose_spec HA.Y_bdd_below
    have hYa : ∀ᵐ ω ∂μ, M ≤ S.YofA a ω :=
      POProximalSystem.YofA_essbound_below HA.consistency (HA.latent_exch a) hAY
        (HA.overlap_strong a) hM
    have hYaInt : Integrable (S.YofA a) μ := HA.integrable_YofA a
    have h_le : (∫ _ in s', M ∂μ) ≤ ∫ ω in s', S.YofA a ω ∂μ := by
      refine setIntegral_mono_ae ?_ ?_ hYa
      · exact integrableOn_const
      · exact hYaInt.integrableOn
    have h_const : (∫ _ in s', M ∂μ) = M * p := by
      rw [setIntegral_const]
      simp [hp_def, MeasureTheory.measureReal_def, mul_comm]
    exact h_const ▸ h_le
  -- ============================================================
  -- ENVELOPE CLAMPS via IsUpperEnvW / IsLowerEnvW + bridge + collapse.
  -- ============================================================
  have hU_int : ∫ ω in s', φ (S.W ω, S.X ω) ∂μ
      ≤ ∫ ω in s,
          S.stratumOddsRatio μ a ω * Uenv (a, S.X ω) * φ (S.W ω, S.X ω) ∂μ :=
    hU.2 φ h_meas_φ h_nonneg_φ h_int_φ hU_int_h
  have hL_int : ∫ ω in s,
        S.stratumOddsRatio μ a ω * Lenv (a, S.X ω) * φ (S.W ω, S.X ω) ∂μ
      ≤ ∫ ω in s', φ (S.W ω, S.X ω) ∂μ :=
    hL.2 φ h_meas_φ h_nonneg_φ h_int_φ hL_int_h
  have hU_arm_h : (∫ ω in s', S.YofA a ω ∂μ)
      ≤ ∫ ω in s,
          S.stratumOddsRatio μ a ω * Uenv (a, S.X ω) * HA.h (a, S.W ω, S.X ω) ∂μ := by
    rw [hBridge]; exact hU_int
  have hL_arm_h : (∫ ω in s,
          S.stratumOddsRatio μ a ω * Lenv (a, S.X ω) * HA.h (a, S.W ω, S.X ω) ∂μ)
      ≤ (∫ ω in s', S.YofA a ω ∂μ) := by
    rw [hBridge]; exact hL_int
  -- Collapse step: replace `h(a,W,X)` factor with `μ[Y | σ_AX]` on `{A=a}`.
  -- σ_AX-pull-out lemma `∫_s f · g dμ = ∫_s f · μ[g | σ_AX] dμ` for
  -- σ_AX-measurable f and integrable g, combined with
  -- `condExp_Y_eq_condExp_h_arm_AX`.
  -- σ_AX-measurable set s = {A = a}.
  have hs_meas : MeasurableSet s := S.measurable_A (measurableSet_singleton a)
  have hs_in_AX : MeasurableSet[S.σ_AX] s := by
    refine ⟨Prod.fst ⁻¹' {a}, ?_, ?_⟩
    · exact measurable_fst (measurableSet_singleton a)
    · ext ω; simp [s, POProximalSystem.AX]
  -- Collapse identity (proved in `Helpers/Common.lean`).
  have hCollapse :
      μ[S.Y | S.σ_AX] =ᵐ[μ.restrict s]
      μ[fun ω => HA.h (a, S.W ω, S.X ω) | S.σ_AX] :=
    POProximalSystem.condExp_Y_eq_condExp_h_arm_AX HA a hAY
  -- σ_X-strong-measurability of the Uenv-and-X factor (then lifted to σ_AX).
  have hX_σX : Measurable[S.σ_X] S.X := Measurable.of_comap_le le_rfl
  have hUenv_σX : Measurable[S.σ_X] (fun ω => Uenv (a, S.X ω)) := by
    have hU_meas : Measurable Uenv := hU.1
    have hpair : Measurable[S.σ_X] (fun ω => (a, S.X ω)) :=
      Measurable.prodMk measurable_const hX_σX
    exact hU_meas.comp hpair
  have hLenv_σX : Measurable[S.σ_X] (fun ω => Lenv (a, S.X ω)) := by
    have hL_meas : Measurable Lenv := hL.1
    have hpair : Measurable[S.σ_X] (fun ω => (a, S.X ω)) :=
      Measurable.prodMk measurable_const hX_σX
    exact hL_meas.comp hpair
  -- stratumOddsRatio is σ_X-strong-measurable (quotient of two σ_X condExps).
  have hSOR_σX : StronglyMeasurable[S.σ_X] (S.stratumOddsRatio μ a) := by
    unfold POProximalSystem.stratumOddsRatio
    -- ℝ has no `ContinuousDiv` instance, so go via `Measurable.div`.
    refine ((stronglyMeasurable_condExp.measurable).div
      (stronglyMeasurable_condExp.measurable)).stronglyMeasurable
  have hUenv_σAX : Measurable[S.σ_AX] (fun ω => Uenv (a, S.X ω)) :=
    hUenv_σX.mono S.σ_X_le_σ_AX le_rfl
  have hLenv_σAX : Measurable[S.σ_AX] (fun ω => Lenv (a, S.X ω)) :=
    hLenv_σX.mono S.σ_X_le_σ_AX le_rfl
  have hSOR_σAX : StronglyMeasurable[S.σ_AX] (S.stratumOddsRatio μ a) :=
    hSOR_σX.mono S.σ_X_le_σ_AX
  -- Build σ_AX-strong-measurability of f := stratumOddsRatio · Uenv(a,X).
  have hfU_sm : StronglyMeasurable[S.σ_AX]
      (fun ω => S.stratumOddsRatio μ a ω * Uenv (a, S.X ω)) :=
    hSOR_σAX.mul hUenv_σAX.stronglyMeasurable
  have hfL_sm : StronglyMeasurable[S.σ_AX]
      (fun ω => S.stratumOddsRatio μ a ω * Lenv (a, S.X ω)) :=
    hSOR_σAX.mul hLenv_σAX.stronglyMeasurable
  -- Integrability of g₁ = h(a, W, X) (from the bundle).
  have hh_int : Integrable (fun ω => HA.h (a, S.W ω, S.X ω)) μ :=
    HA.integrable_h_arm a
  -- Integrability of g₂ = μ[Y | σ_AX] (always integrable).
  have hcondY_int : Integrable (fun ω => (μ[S.Y | S.σ_AX]) ω) μ :=
    integrable_condExp
  -- Caller-supplied integrability (paper's implicit "all integrals finite"
  -- convention; not bundled in `WBasedAssumptions` because `Uenv`/`Lenv` are
  -- theorem-level parameters). Repackage to the L1 lemma's `(f * g)` shape.
  have hfU_h_int : Integrable
      ((fun ω => S.stratumOddsRatio μ a ω * Uenv (a, S.X ω)) *
       (fun ω => HA.h (a, S.W ω, S.X ω))) μ := by
    simpa [Pi.mul_apply] using hU_int_h
  have hfU_condY_int : Integrable
      ((fun ω => S.stratumOddsRatio μ a ω * Uenv (a, S.X ω)) *
       (fun ω => (μ[S.Y | S.σ_AX]) ω)) μ := by
    simpa [Pi.mul_apply] using hU_int_Y
  have hfL_h_int : Integrable
      ((fun ω => S.stratumOddsRatio μ a ω * Lenv (a, S.X ω)) *
       (fun ω => HA.h (a, S.W ω, S.X ω))) μ := by
    simpa [Pi.mul_apply] using hL_int_h
  have hfL_condY_int : Integrable
      ((fun ω => S.stratumOddsRatio μ a ω * Lenv (a, S.X ω)) *
       (fun ω => (μ[S.Y | S.σ_AX]) ω)) μ := by
    simpa [Pi.mul_apply] using hL_int_Y
  -- Apply L1 (twice on each side) and then `condExp_Y_eq_condExp_h_arm_AX`.
  have hU_collapse : (∫ ω in s,
          S.stratumOddsRatio μ a ω * Uenv (a, S.X ω) * HA.h (a, S.W ω, S.X ω) ∂μ)
      = ∫ ω in s,
          S.stratumOddsRatio μ a ω * Uenv (a, S.X ω) * (μ[S.Y | S.σ_AX]) ω ∂μ := by
    -- L1 on g = h(a,W,X): ∫_s f·g = ∫_s f · μ[g|σ_AX]
    have h1 :=
      setIntegral_mul_condExp_of_stronglyMeasurableLeft S.σ_AX_le hfU_sm
        hh_int hfU_h_int hs_in_AX
    -- L1 on g' = μ[Y|σ_AX]: ∫_s f·μ[Y|σ_AX] = ∫_s f · μ[μ[Y|σ_AX]|σ_AX] = ∫_s f · μ[Y|σ_AX]
    -- so we use it the other direction; we need only h1 plus a `congr_ae` on s
    -- to swap μ[h|σ_AX] → μ[Y|σ_AX] using the collapse.
    have h_ae : (fun ω => S.stratumOddsRatio μ a ω * Uenv (a, S.X ω)
            * (μ[fun ω' => HA.h (a, S.W ω', S.X ω')|S.σ_AX]) ω)
        =ᵐ[μ.restrict s]
        (fun ω => S.stratumOddsRatio μ a ω * Uenv (a, S.X ω)
            * (μ[S.Y | S.σ_AX]) ω) := by
      filter_upwards [hCollapse] with ω hω
      simp [hω]
    have h2 := integral_congr_ae h_ae
    -- h1 : ∫_s f * h = ∫_s f * μ[h|σ_AX]
    -- h2 : ∫_s f * μ[h|σ_AX] = ∫_s f * μ[Y|σ_AX]
    exact h1.trans h2
  have hL_collapse : (∫ ω in s,
          S.stratumOddsRatio μ a ω * Lenv (a, S.X ω) * HA.h (a, S.W ω, S.X ω) ∂μ)
      = ∫ ω in s,
          S.stratumOddsRatio μ a ω * Lenv (a, S.X ω) * (μ[S.Y | S.σ_AX]) ω ∂μ := by
    have h1 :=
      setIntegral_mul_condExp_of_stronglyMeasurableLeft S.σ_AX_le hfL_sm
        hh_int hfL_h_int hs_in_AX
    have h_ae : (fun ω => S.stratumOddsRatio μ a ω * Lenv (a, S.X ω)
            * (μ[fun ω' => HA.h (a, S.W ω', S.X ω')|S.σ_AX]) ω)
        =ᵐ[μ.restrict s]
        (fun ω => S.stratumOddsRatio μ a ω * Lenv (a, S.X ω)
            * (μ[S.Y | S.σ_AX]) ω) := by
      filter_upwards [hCollapse] with ω hω
      simp [hω]
    have h2 := integral_congr_ae h_ae
    exact h1.trans h2
  have hU_arm : (∫ ω in s', S.YofA a ω ∂μ)
      ≤ ∫ ω in s,
          S.stratumOddsRatio μ a ω * Uenv (a, S.X ω) * (μ[S.Y | S.σ_AX]) ω ∂μ := by
    rw [← hU_collapse]; exact hU_arm_h
  have hL_arm : (∫ ω in s,
          S.stratumOddsRatio μ a ω * Lenv (a, S.X ω) * (μ[S.Y | S.σ_AX]) ω ∂μ)
      ≤ (∫ ω in s', S.YofA a ω ∂μ) := by
    rw [← hL_collapse]; exact hL_arm_h
  -- ============================================================
  -- ASSEMBLE: combine trivial + envelope clamps via max/min, then add
  -- the consistency-identified {A = a} integral.
  -- ============================================================
  refine ⟨?_, ?_⟩
  · -- Lower: max(trivial-lower, envelope-lower) + ∫_{A=a} Y ≤ meanYofA.
    rw [hsplit]
    have h_max : max (Classical.choose HA.Y_bdd_below * p)
                     (∫ ω in s,
                       S.stratumOddsRatio μ a ω * Lenv (a, S.X ω) * (μ[S.Y | S.σ_AX]) ω ∂μ)
                  ≤ (∫ ω in s', S.YofA a ω ∂μ) :=
      max_le hL_triv_arm hL_arm
    linarith
  · -- Upper: meanYofA ≤ min(trivial-upper, envelope-upper) + ∫_{A=a} Y.
    rw [hsplit]
    have h_min : (∫ ω in s', S.YofA a ω ∂μ)
                  ≤ min (Classical.choose HA.Y_bdd_above * p)
                        (∫ ω in s,
                          S.stratumOddsRatio μ a ω * Uenv (a, S.X ω) * (μ[S.Y | S.σ_AX]) ω ∂μ) :=
      le_min hU_triv_arm hU_arm
    linarith

end POProximalSystem

end PO
end Causalean
