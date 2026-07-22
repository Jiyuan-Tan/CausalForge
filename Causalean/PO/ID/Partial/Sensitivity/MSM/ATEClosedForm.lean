/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Marginal Sensitivity Model — the sharp ATE interval in closed form (Dorn–Guo)

Combines the four unconditional quantile-balancing closed forms — treated upper/lower
(`CutoffConstruct`/`LowerBound`) and control upper/lower (`ControlCutoffConstruct`/`ControlLowerBound`) —
into the closed form of the sharp ATE interval. Following Dorn–Guo, the ATE endpoints oppose the arm
bounds:

    ateUpperCalib Λ = msmUpperCalib Λ − msmLowerCalib0 Λ = candMean (cutoffProp Λ cTU) − candMean0 (lowerCutoffProp0 Λ cCL),
    ateLowerCalib Λ = msmLowerCalib Λ − msmUpperCalib0 Λ = candMean (lowerCutoffProp Λ cTL) − candMean0 (cutoffProp0 Λ cCU),

each a quantile-balancing candidate mean at a conditional-quantile cutoff. `ate_endpoints_eq_cutoff` gives
the endpoint closed forms; `ate_mem_Icc_cutoff` combines them with the interval validity
(`ate_mem_Icc_calib`) to place the true ATE inside the closed-form interval. -/

import Causalean.PO.ID.Partial.Sensitivity.MSM.ATE
import Causalean.PO.ID.Partial.Sensitivity.MSM.LowerBound
import Causalean.PO.ID.Partial.Sensitivity.MSM.ControlLowerBound

/-! # Closed-form marginal-sensitivity-model ATE endpoints

This file combines the four arm-level quantile-cutoff closed forms into
closed-form endpoints for the calibrated ATE interval. The true ATE is then
placed in the interval whose endpoints are the appropriate differences of the
treated and control cutoff candidate means.

The theorem `ate_endpoints_eq_cutoff` gives the endpoint representation using
treated upper/lower cutoffs and control upper/lower cutoffs. The theorem
`ate_mem_Icc_cutoff` combines those endpoint equalities with armwise interval
validity to put `ate` in the resulting closed-form interval.
-/

namespace Causalean
namespace PO

open MeasureTheory ProbabilityTheory

namespace POBackdoorSystem

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
variable (S : POBackdoorSystem P γ)

/-- **The sharp ATE interval endpoints in closed form.** Combining the four unconditional
quantile-balancing closed forms, the sharp ATE endpoints are differences of
conditional-quantile candidate means:
`ateUpperCalib = candMean (cutoffProp cTU) − candMean0 (lowerCutoffProp0 cCL)`
(treated upper minus control lower) and
`ateLowerCalib = candMean (lowerCutoffProp cTL) − candMean0 (cutoffProp0 cCU)`
(treated lower minus control upper), for `σ(X)`-measurable conditional-quantile cutoffs. -/
theorem ate_endpoints_eq_cutoff (Λ : ℝ) (hΛ : 1 < Λ)
    -- treated arm regularity
    (hoverlapT : ∀ᵐ ω ∂P.μ, 0 < S.propScore true ω ∧ S.propScore true ω < 1)
    (hatomlessT : ∀ a : γ, Continuous (condCDF S.treatedXYLaw a))
    (hlevelTU : ∀ᵐ ω ∂P.μ, 0 < S.calibLevel Λ ω ∧ S.calibLevel Λ ω < 1)
    (hlevelTL : ∀ᵐ ω ∂P.μ, 0 < S.calibLevelLower Λ ω ∧ S.calibLevelLower Λ ω < 1)
    (hbddT : BddAbove (S.candMean '' S.MSMSetCalib Λ))
    (hmeasT : ∀ etilde ∈ S.MSMSetCalib Λ, AEMeasurable etilde P.μ)
    (hregTU : ∀ c : P.Ω → ℝ, Measurable[S.sigmaX] c →
      Integrable c P.μ ∧
      Integrable (fun ω => S.dVar.indicator true ω / S.cutoffProp Λ c ω) P.μ ∧
      Integrable (fun ω =>
        S.dVar.indicator true ω * (if c ω < S.factualY ω then (1 : ℝ) else 0)) P.μ ∧
      Integrable (fun ω => S.dVar.indicator true ω * S.wMin Λ ω) P.μ ∧
      Integrable (fun ω => (S.wMax Λ ω - S.wMin Λ ω) *
        (S.dVar.indicator true ω * (if c ω < S.factualY ω then (1 : ℝ) else 0))) P.μ ∧
      Integrable (fun ω => S.dVar.indicator true ω * |S.factualY ω| * S.wMax Λ ω) P.μ ∧
      Integrable (fun ω => S.dVar.indicator true ω * S.wMax Λ ω) P.μ ∧
      Integrable (fun ω => |c ω| * S.dVar.indicator true ω * S.wMax Λ ω) P.μ)
    (hregTL : ∀ c : P.Ω → ℝ, Measurable[S.sigmaX] c →
      Integrable c P.μ ∧
      Integrable (fun ω => S.dVar.indicator true ω / S.lowerCutoffProp Λ c ω) P.μ ∧
      Integrable (fun ω =>
        S.dVar.indicator true ω * (if c ω < S.factualY ω then (1 : ℝ) else 0)) P.μ ∧
      Integrable (fun ω => S.dVar.indicator true ω * S.wMax Λ ω) P.μ ∧
      Integrable (fun ω => (S.wMax Λ ω - S.wMin Λ ω) *
        (S.dVar.indicator true ω * (if c ω < S.factualY ω then (1 : ℝ) else 0))) P.μ ∧
      Integrable (fun ω => S.dVar.indicator true ω * |S.factualY ω| * S.wMax Λ ω) P.μ ∧
      Integrable (fun ω => |c ω| * S.dVar.indicator true ω * S.wMax Λ ω) P.μ)
    -- control arm regularity
    (hoverlapC : ∀ᵐ ω ∂P.μ, 0 < S.propScore false ω ∧ S.propScore false ω < 1)
    (hatomlessC : ∀ a : γ, Continuous (condCDF S.controlXYLaw a))
    (hlevelCU : ∀ᵐ ω ∂P.μ, 0 < S.calibLevel0 Λ ω ∧ S.calibLevel0 Λ ω < 1)
    (hlevelCL : ∀ᵐ ω ∂P.μ, 0 < S.calibLevelLower0 Λ ω ∧ S.calibLevelLower0 Λ ω < 1)
    (hbddC : BddAbove (S.candMean0 '' S.MSMSetCalib0 Λ))
    (hmeasC : ∀ etilde ∈ S.MSMSetCalib0 Λ, AEMeasurable etilde P.μ)
    (hregCU : ∀ c : P.Ω → ℝ, Measurable[S.sigmaX] c →
      Integrable c P.μ ∧
      Integrable (fun ω => S.dVar.indicator false ω / S.cutoffProp0 Λ c ω) P.μ ∧
      Integrable (fun ω =>
        S.dVar.indicator false ω * (if c ω < S.factualY ω then (1 : ℝ) else 0)) P.μ ∧
      Integrable (fun ω => S.dVar.indicator false ω * S.wMin0 Λ ω) P.μ ∧
      Integrable (fun ω => (S.wMax0 Λ ω - S.wMin0 Λ ω) *
        (S.dVar.indicator false ω * (if c ω < S.factualY ω then (1 : ℝ) else 0))) P.μ ∧
      Integrable (fun ω => S.dVar.indicator false ω * |S.factualY ω| * S.wMax0 Λ ω) P.μ ∧
      Integrable (fun ω => S.dVar.indicator false ω * S.wMax0 Λ ω) P.μ ∧
      Integrable (fun ω => |c ω| * S.dVar.indicator false ω * S.wMax0 Λ ω) P.μ)
    (hregCL : ∀ c : P.Ω → ℝ, Measurable[S.sigmaX] c →
      Integrable c P.μ ∧
      Integrable (fun ω => S.dVar.indicator false ω / S.lowerCutoffProp0 Λ c ω) P.μ ∧
      Integrable (fun ω =>
        S.dVar.indicator false ω * (if c ω < S.factualY ω then (1 : ℝ) else 0)) P.μ ∧
      Integrable (fun ω => S.dVar.indicator false ω * S.wMax0 Λ ω) P.μ ∧
      Integrable (fun ω => (S.wMax0 Λ ω - S.wMin0 Λ ω) *
        (S.dVar.indicator false ω * (if c ω < S.factualY ω then (1 : ℝ) else 0))) P.μ ∧
      Integrable (fun ω => S.dVar.indicator false ω * |S.factualY ω| * S.wMax0 Λ ω) P.μ ∧
      Integrable (fun ω => |c ω| * S.dVar.indicator false ω * S.wMax0 Λ ω) P.μ) :
    ∃ cTU cTL cCU cCL : P.Ω → ℝ,
      (Measurable[S.sigmaX] cTU ∧ Measurable[S.sigmaX] cTL ∧
        Measurable[S.sigmaX] cCU ∧ Measurable[S.sigmaX] cCL) ∧
      S.ateUpperCalib Λ =
        S.candMean (S.cutoffProp Λ cTU) - S.candMean0 (S.lowerCutoffProp0 Λ cCL) ∧
      S.ateLowerCalib Λ =
        S.candMean (S.lowerCutoffProp Λ cTL) - S.candMean0 (S.cutoffProp0 Λ cCU) := by
  obtain ⟨cTU, hcTU, _, hTU⟩ :=
    S.msmUpperCalib_eq_cutoff_unconditional Λ hΛ hoverlapT hatomlessT hlevelTU hbddT hmeasT hregTU
  obtain ⟨cTL, hcTL, _, hTL⟩ :=
    S.msmLowerCalib_eq_cutoff_unconditional Λ hΛ hoverlapT hatomlessT hlevelTL hmeasT hregTL
  obtain ⟨cCU, hcCU, _, hCU⟩ :=
    S.msmUpperCalib0_eq_cutoff_unconditional Λ hΛ hoverlapC hatomlessC hlevelCU hbddC hmeasC hregCU
  obtain ⟨cCL, hcCL, _, hCL⟩ :=
    S.msmLowerCalib0_eq_cutoff_unconditional Λ hΛ hoverlapC hatomlessC hlevelCL hmeasC hregCL
  refine ⟨cTU, cTL, cCU, cCL, ⟨hcTU, hcTL, hcCU, hcCL⟩, ?_, ?_⟩
  · unfold POBackdoorSystem.ateUpperCalib
    rw [hTU, hCL]
  · unfold POBackdoorSystem.ateLowerCalib
    rw [hTL, hCU]

/-- **The true ATE lies in the sharp closed-form interval.** Combining
`ate_endpoints_eq_cutoff` (the closed-form endpoints) with `ate_mem_Icc_calib`
(interval validity), the true `τ = E[Y(1)] − E[Y(0)]` lies in the quantile-balancing
closed-form interval. The per-arm validity inputs `hT`, `hC` are the same as for
`ate_mem_Icc_calib`. -/
theorem ate_mem_Icc_cutoff (Λ : ℝ) (hΛ : 1 < Λ)
    (hoverlapT : ∀ᵐ ω ∂P.μ, 0 < S.propScore true ω ∧ S.propScore true ω < 1)
    (hatomlessT : ∀ a : γ, Continuous (condCDF S.treatedXYLaw a))
    (hlevelTU : ∀ᵐ ω ∂P.μ, 0 < S.calibLevel Λ ω ∧ S.calibLevel Λ ω < 1)
    (hlevelTL : ∀ᵐ ω ∂P.μ, 0 < S.calibLevelLower Λ ω ∧ S.calibLevelLower Λ ω < 1)
    (hbddT : BddAbove (S.candMean '' S.MSMSetCalib Λ))
    (hmeasT : ∀ etilde ∈ S.MSMSetCalib Λ, AEMeasurable etilde P.μ)
    (hregTU : ∀ c : P.Ω → ℝ, Measurable[S.sigmaX] c →
      Integrable c P.μ ∧
      Integrable (fun ω => S.dVar.indicator true ω / S.cutoffProp Λ c ω) P.μ ∧
      Integrable (fun ω =>
        S.dVar.indicator true ω * (if c ω < S.factualY ω then (1 : ℝ) else 0)) P.μ ∧
      Integrable (fun ω => S.dVar.indicator true ω * S.wMin Λ ω) P.μ ∧
      Integrable (fun ω => (S.wMax Λ ω - S.wMin Λ ω) *
        (S.dVar.indicator true ω * (if c ω < S.factualY ω then (1 : ℝ) else 0))) P.μ ∧
      Integrable (fun ω => S.dVar.indicator true ω * |S.factualY ω| * S.wMax Λ ω) P.μ ∧
      Integrable (fun ω => S.dVar.indicator true ω * S.wMax Λ ω) P.μ ∧
      Integrable (fun ω => |c ω| * S.dVar.indicator true ω * S.wMax Λ ω) P.μ)
    (hregTL : ∀ c : P.Ω → ℝ, Measurable[S.sigmaX] c →
      Integrable c P.μ ∧
      Integrable (fun ω => S.dVar.indicator true ω / S.lowerCutoffProp Λ c ω) P.μ ∧
      Integrable (fun ω =>
        S.dVar.indicator true ω * (if c ω < S.factualY ω then (1 : ℝ) else 0)) P.μ ∧
      Integrable (fun ω => S.dVar.indicator true ω * S.wMax Λ ω) P.μ ∧
      Integrable (fun ω => (S.wMax Λ ω - S.wMin Λ ω) *
        (S.dVar.indicator true ω * (if c ω < S.factualY ω then (1 : ℝ) else 0))) P.μ ∧
      Integrable (fun ω => S.dVar.indicator true ω * |S.factualY ω| * S.wMax Λ ω) P.μ ∧
      Integrable (fun ω => |c ω| * S.dVar.indicator true ω * S.wMax Λ ω) P.μ)
    (hoverlapC : ∀ᵐ ω ∂P.μ, 0 < S.propScore false ω ∧ S.propScore false ω < 1)
    (hatomlessC : ∀ a : γ, Continuous (condCDF S.controlXYLaw a))
    (hlevelCU : ∀ᵐ ω ∂P.μ, 0 < S.calibLevel0 Λ ω ∧ S.calibLevel0 Λ ω < 1)
    (hlevelCL : ∀ᵐ ω ∂P.μ, 0 < S.calibLevelLower0 Λ ω ∧ S.calibLevelLower0 Λ ω < 1)
    (hbddC : BddAbove (S.candMean0 '' S.MSMSetCalib0 Λ))
    (hmeasC : ∀ etilde ∈ S.MSMSetCalib0 Λ, AEMeasurable etilde P.μ)
    (hregCU : ∀ c : P.Ω → ℝ, Measurable[S.sigmaX] c →
      Integrable c P.μ ∧
      Integrable (fun ω => S.dVar.indicator false ω / S.cutoffProp0 Λ c ω) P.μ ∧
      Integrable (fun ω =>
        S.dVar.indicator false ω * (if c ω < S.factualY ω then (1 : ℝ) else 0)) P.μ ∧
      Integrable (fun ω => S.dVar.indicator false ω * S.wMin0 Λ ω) P.μ ∧
      Integrable (fun ω => (S.wMax0 Λ ω - S.wMin0 Λ ω) *
        (S.dVar.indicator false ω * (if c ω < S.factualY ω then (1 : ℝ) else 0))) P.μ ∧
      Integrable (fun ω => S.dVar.indicator false ω * |S.factualY ω| * S.wMax0 Λ ω) P.μ ∧
      Integrable (fun ω => S.dVar.indicator false ω * S.wMax0 Λ ω) P.μ ∧
      Integrable (fun ω => |c ω| * S.dVar.indicator false ω * S.wMax0 Λ ω) P.μ)
    (hregCL : ∀ c : P.Ω → ℝ, Measurable[S.sigmaX] c →
      Integrable c P.μ ∧
      Integrable (fun ω => S.dVar.indicator false ω / S.lowerCutoffProp0 Λ c ω) P.μ ∧
      Integrable (fun ω =>
        S.dVar.indicator false ω * (if c ω < S.factualY ω then (1 : ℝ) else 0)) P.μ ∧
      Integrable (fun ω => S.dVar.indicator false ω * S.wMax0 Λ ω) P.μ ∧
      Integrable (fun ω => (S.wMax0 Λ ω - S.wMin0 Λ ω) *
        (S.dVar.indicator false ω * (if c ω < S.factualY ω then (1 : ℝ) else 0))) P.μ ∧
      Integrable (fun ω => S.dVar.indicator false ω * |S.factualY ω| * S.wMax0 Λ ω) P.μ ∧
      Integrable (fun ω => |c ω| * S.dVar.indicator false ω * S.wMax0 Λ ω) P.μ)
    (hT : S.Y1mean ∈ Set.Icc (S.msmLowerCalib Λ) (S.msmUpperCalib Λ))
    (hC : S.Y0mean ∈ Set.Icc (S.msmLowerCalib0 Λ) (S.msmUpperCalib0 Λ)) :
    ∃ cTU cTL cCU cCL : P.Ω → ℝ,
      (Measurable[S.sigmaX] cTU ∧ Measurable[S.sigmaX] cTL ∧
        Measurable[S.sigmaX] cCU ∧ Measurable[S.sigmaX] cCL) ∧
      S.ate ∈ Set.Icc
        (S.candMean (S.lowerCutoffProp Λ cTL) - S.candMean0 (S.cutoffProp0 Λ cCU))
        (S.candMean (S.cutoffProp Λ cTU) - S.candMean0 (S.lowerCutoffProp0 Λ cCL)) := by
  obtain ⟨cTU, cTL, cCU, cCL, hmeas, hUp, hLo⟩ :=
    S.ate_endpoints_eq_cutoff Λ hΛ hoverlapT hatomlessT hlevelTU hlevelTL hbddT hmeasT hregTU hregTL
      hoverlapC hatomlessC hlevelCU hlevelCL hbddC hmeasC hregCU hregCL
  have hval := S.ate_mem_Icc_calib Λ hT hC
  rw [hUp, hLo] at hval
  exact ⟨cTU, cTL, cCU, cCL, hmeas, hval⟩

end POBackdoorSystem

end PO
end Causalean
