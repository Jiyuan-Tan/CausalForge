/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Finite variance of the AIPW influence function — `lem:est-aipw-finite-var`

`E[ψ_AIPW²] < ∞` under strict overlap, a factual outcome second moment, and
direct square-integrability gates for the outcome-regression components.
-/

import Causalean.Estimation.ATE.Score.AIPWMoment
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-! # Finite Variance for AIPW

This file proves square integrability of the augmented inverse-probability
weighted influence function for the back-door average treatment effect. The
result supplies the finite-variance condition needed by asymptotic linearity
and efficiency arguments in the estimation layer.

The headline theorem `aipw_finite_var` assumes direct L² gates for
`μ_val(d, X)`, while `aipw_finite_var_of_counterfactual_sq` derives those gates
from counterfactual second moments under the back-door assumptions.
-/

namespace Causalean
namespace Estimation
namespace ATE

open MeasureTheory ProbabilityTheory Filter Topology Causalean.PO

namespace BackdoorEstimationSystem

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
  [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]

/-- **Finite variance of `ψ_AIPW`** — `lem:est-aipw-finite-var`.

Under strict overlap (`ε ∈ (0, 1/2]`), `E[Y²] < ∞`, and direct `L²(P)` gates
for `μ(d, X)` for both treatment arms, the AIPW influence function is
square-integrable against the observed data law `P_Z`.

The theorem states the variance result at the level used by the score proof:
the regression terms must be square-integrable on the realized covariates.
The stronger counterfactual-second-moment route is provided separately by
`aipw_finite_var_of_counterfactual_sq`. -/
theorem aipw_finite_var (S : BackdoorEstimationSystem P γ) {ε : ℝ}
    (h_overlap : S.StrictOverlap ε)
    (h_y2 : Integrable (fun ω => (S.toPOBackdoorSystem.factualY ω) ^ 2) P.μ)
    (hμ_L2 : ∀ d : Bool, MemLp
      (fun ω => S.μ_val d (S.toPOBackdoorSystem.factualX ω)) 2 P.μ) :
    Integrable (fun z => (S.ψ_AIPW z) ^ 2) (S.P_Z) := by
  have hψ_meas : Measurable S.ψ_AIPW := by
    unfold BackdoorEstimationSystem.ψ_AIPW aipwMoment indA projX projA projY
    have hx : Measurable (fun z : γ × Bool × ℝ => z.1) := measurable_fst
    have hy : Measurable (fun z : γ × Bool × ℝ => z.2.2) := by measurability
    have hμt : Measurable (fun z : γ × Bool × ℝ => S.μ_val true z.1) :=
      (S.μ_meas true).comp hx
    have hμf : Measurable (fun z : γ × Bool × ℝ => S.μ_val false z.1) :=
      (S.μ_meas false).comp hx
    have he : Measurable (fun z : γ × Bool × ℝ => S.e_val z.1) :=
      S.e_meas.comp hx
    have hind : Measurable (fun z : γ × Bool × ℝ =>
        if z.2.1 = true then (1 : ℝ) else 0) := by
      have ha : Measurable (fun z : γ × Bool × ℝ => z.2.1) := by measurability
      exact (Measurable.of_discrete
        (f := fun b : Bool => if b = true then (1 : ℝ) else 0)).comp ha
    exact ((((hμt.sub hμf).add ((hind.div he).mul (hy.sub hμt))).sub
      (((measurable_const.sub hind).div (measurable_const.sub he)).mul
        (hy.sub hμf))).sub measurable_const)
  have hY_L2 : MemLp S.toPOBackdoorSystem.factualY 2 P.μ := by
    exact (memLp_two_iff_integrable_sq
      S.toPOBackdoorSystem.measurable_factualY.aestronglyMeasurable).2 h_y2
  have he_lower :
      ∀ᵐ ω ∂P.μ, ε ≤ S.e_val (S.toPOBackdoorSystem.factualX ω) := by
    filter_upwards [h_overlap.2.2, S.e_compat] with ω hover hcomp
    simpa [hcomp] using hover.1
  have he_upper :
      ∀ᵐ ω ∂P.μ, S.e_val (S.toPOBackdoorSystem.factualX ω) ≤ 1 - ε := by
    filter_upwards [h_overlap.2.2, S.e_compat] with ω hover hcomp
    simpa [hcomp] using hover.2
  have hw_true_bound :
      ∀ᵐ ω ∂P.μ,
        ‖indA (S.factualZ ω) /
          S.e_val (S.toPOBackdoorSystem.factualX ω)‖ ≤ ε⁻¹ := by
    filter_upwards [he_lower] with ω he
    by_cases hD : S.toPOBackdoorSystem.factualD ω = true
    · have hpos : 0 < S.e_val (S.toPOBackdoorSystem.factualX ω) := S.e_pos _
      have hle : (S.e_val (S.toPOBackdoorSystem.factualX ω))⁻¹ ≤ ε⁻¹ :=
        (inv_le_inv₀ hpos h_overlap.1).2 he
      simpa [BackdoorEstimationSystem.factualZ, indA, projA, projX, hD, one_div,
        Real.norm_eq_abs, abs_of_pos hpos] using hle
    · have hεinv_nonneg : 0 ≤ ε⁻¹ := inv_nonneg.mpr h_overlap.1.le
      simpa [BackdoorEstimationSystem.factualZ, indA, projA, projX, hD] using hεinv_nonneg
  have hw_false_bound :
      ∀ᵐ ω ∂P.μ,
        ‖(1 - indA (S.factualZ ω)) /
          (1 - S.e_val (S.toPOBackdoorSystem.factualX ω))‖ ≤ ε⁻¹ := by
    filter_upwards [he_upper] with ω he
    by_cases hD : S.toPOBackdoorSystem.factualD ω = true
    · have hεinv_nonneg : 0 ≤ ε⁻¹ := inv_nonneg.mpr h_overlap.1.le
      simpa [BackdoorEstimationSystem.factualZ, indA, projA, projX, hD] using hεinv_nonneg
    · have hden : ε ≤ 1 - S.e_val (S.toPOBackdoorSystem.factualX ω) := by
        linarith
      have hdenpos : 0 < 1 - S.e_val (S.toPOBackdoorSystem.factualX ω) :=
        lt_of_lt_of_le h_overlap.1 hden
      have hle : (1 - S.e_val (S.toPOBackdoorSystem.factualX ω))⁻¹ ≤ ε⁻¹ :=
        (inv_le_inv₀ hdenpos h_overlap.1).2 hden
      simpa [BackdoorEstimationSystem.factualZ, indA, projA, projX, hD, one_div,
        Real.norm_eq_abs, abs_of_pos hdenpos] using hle
  have hw_true_Linf :
      MemLp
        (fun ω => indA (S.factualZ ω) /
          S.e_val (S.toPOBackdoorSystem.factualX ω)) ⊤ P.μ := by
    refine MemLp.of_bound ?_ ε⁻¹ hw_true_bound
    apply Measurable.aestronglyMeasurable
    have hind : Measurable (fun ω => indA (S.factualZ ω)) := by
      simpa [indA, projA, BackdoorEstimationSystem.factualZ] using
        (Measurable.of_discrete
          (f := fun b : Bool => if b = true then (1 : ℝ) else 0)).comp
            S.toPOBackdoorSystem.measurable_factualD
    exact hind.div (S.e_meas.comp S.toPOBackdoorSystem.measurable_factualX)
  have hw_false_Linf :
      MemLp
        (fun ω => (1 - indA (S.factualZ ω)) /
          (1 - S.e_val (S.toPOBackdoorSystem.factualX ω))) ⊤ P.μ := by
    refine MemLp.of_bound ?_ ε⁻¹ hw_false_bound
    apply Measurable.aestronglyMeasurable
    have hind : Measurable (fun ω => indA (S.factualZ ω)) := by
      simpa [indA, projA, BackdoorEstimationSystem.factualZ] using
        (Measurable.of_discrete
          (f := fun b : Bool => if b = true then (1 : ℝ) else 0)).comp
            S.toPOBackdoorSystem.measurable_factualD
    exact (measurable_const.sub hind).div
      (measurable_const.sub (S.e_meas.comp S.toPOBackdoorSystem.measurable_factualX))
  have hterm_true_L2 :
      MemLp
        (fun ω =>
          (indA (S.factualZ ω) /
            S.e_val (S.toPOBackdoorSystem.factualX ω)) *
          (S.toPOBackdoorSystem.factualY ω -
            S.μ_val true (S.toPOBackdoorSystem.factualX ω))) 2 P.μ := by
    simpa using (hY_L2.sub (hμ_L2 true)).mul hw_true_Linf
  have hterm_false_L2 :
      MemLp
        (fun ω =>
          ((1 - indA (S.factualZ ω)) /
            (1 - S.e_val (S.toPOBackdoorSystem.factualX ω))) *
          (S.toPOBackdoorSystem.factualY ω -
            S.μ_val false (S.toPOBackdoorSystem.factualX ω))) 2 P.μ := by
    simpa using (hY_L2.sub (hμ_L2 false)).mul hw_false_Linf
  have hψ_comp_L2 : MemLp (fun ω => S.ψ_AIPW (S.factualZ ω)) 2 P.μ := by
    have hbase_L2 :
        MemLp
          (fun ω =>
            S.μ_val true (S.toPOBackdoorSystem.factualX ω) -
            S.μ_val false (S.toPOBackdoorSystem.factualX ω)) 2 P.μ :=
      (hμ_L2 true).sub (hμ_L2 false)
    have hconst_L2 : MemLp (fun _ : P.Ω => S.θ₀) 2 P.μ :=
      memLp_const _
    have hsum_L2 :=
      ((hbase_L2.add hterm_true_L2).sub hterm_false_L2).sub hconst_L2
    simpa [BackdoorEstimationSystem.ψ_AIPW, aipwMoment,
      BackdoorEstimationSystem.factualZ, projX, projY] using hsum_L2
  have hψ_L2 : MemLp S.ψ_AIPW 2 (S.P_Z) := by
    rw [BackdoorEstimationSystem.P_Z]
    exact (memLp_map_measure_iff hψ_meas.aestronglyMeasurable
      S.measurable_factualZ.aemeasurable).2 hψ_comp_L2
  exact hψ_L2.integrable_sq

/-- Counterfactual second moments are a stronger sufficient condition for
`aipw_finite_var`.

Under the back-door assumptions, conditional Jensen turns `Y(d) ∈ L²(P)` into
`μ(d, X) ∈ L²(P)`, discharging the direct regression gates of the headline
finite-variance theorem. -/
theorem aipw_finite_var_of_counterfactual_sq
    (S : BackdoorEstimationSystem P γ) {ε : ℝ}
    (h_overlap : S.StrictOverlap ε)
    (hA : S.toPOBackdoorSystem.Assumptions)
    (h_y2 : Integrable (fun ω => (S.toPOBackdoorSystem.factualY ω) ^ 2) P.μ)
    (h_yd2 : ∀ d : Bool, Integrable
      (fun ω => (S.toPOBackdoorSystem.YofD d ω) ^ 2) P.μ) :
    Integrable (fun z => (S.ψ_AIPW z) ^ 2) (S.P_Z) := by
  have hμ_L2 :
      ∀ d : Bool, MemLp
        (fun ω => S.μ_val d (S.toPOBackdoorSystem.factualX ω)) 2 P.μ := by
    intro d
    have hYd_L2 : MemLp (S.toPOBackdoorSystem.YofD d) 2 P.μ := by
      exact (memLp_two_iff_integrable_sq
        (S.toPOBackdoorSystem.measurable_YofD d).aestronglyMeasurable).2 (h_yd2 d)
    have hcond_L2 :
        MemLp (P.μ[S.toPOBackdoorSystem.YofD d |
          S.toPOBackdoorSystem.sigmaX]) 2 P.μ :=
      hYd_L2.condExp
    exact hcond_L2.ae_eq (S.μ_compat hA d)
  exact S.aipw_finite_var h_overlap h_y2 hμ_L2

end BackdoorEstimationSystem

end ATE
end Estimation
end Causalean
