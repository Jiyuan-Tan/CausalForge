/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Hahn (1998) variance decomposition for the AIPW influence function

This file proves the Hahn semiparametric efficiency-bound formula for the
back-door ATE.  The AIPW influence function variance decomposes as

    ∫ ψ_AIPW² dP_Z
      = ∫ (μ₁(x) − μ₀(x) − θ₀)² dP_X
        + ∫ (a / e(x)²)   (y − μ₁(x))² dP_Z
        + ∫ ((1−a) / (1−e(x))²) (y − μ₀(x))² dP_Z,

the three terms being, respectively, the variance of the conditional ATE
function, and the two inverse-propensity-weighted conditional outcome
variances.  This is the Hahn efficiency bound `V_H`.

Proof.  Writing `ψ = A + B − C` with
* `A = μ₁ − μ₀ − θ₀`,
* `B = (a/e)(y − μ₁)`,
* `C = ((1−a)/(1−e))(y − μ₀)`,

and using `a ∈ {0,1}` (so `a² = a`, `(1−a)² = 1−a`, `a(1−a) = 0`, hence
`B·C = 0`), one gets pointwise `ψ² = A² + B² + C² + 2AB − 2AC`.  The two
cross terms integrate to zero by `weighted_residual_integral_zero`
(σ(X)-pull-out + `cond_exp_residual_zero`), the squares `B²`, `C²` give the
two IPW terms (with `a² = a`), and `A²` gives the first term after the
`P_Z.map projX = P_X` pushforward.
-/

import Causalean.Estimation.ATE.InfluenceFunction
import Causalean.Estimation.ATE.DML

/-!
# Hahn variance decomposition for the AIPW influence function

This module develops the L² and variance algebra behind the Hahn (1998)
semiparametric efficiency bound for the backdoor ATE. The main theorem
`BackdoorEstimationSystem.aipw_variance_hahn_decomposition` proves that
`∫ ψ_AIPW² dP_Z` splits into the conditional-ATE variance term plus the two
inverse-propensity-weighted conditional outcome-variance terms.

The helper lemmas establish bounded inverse-propensity weights and L²
membership for the regression representatives under overlap and square-integrable
outcomes. The final theorem `dml_ATE_attains_hahn_bound` rewrites the limiting
variance in the one-shot DML central-limit theorem by this Hahn decomposition.
-/

namespace Causalean
namespace Estimation
namespace ATE

open MeasureTheory ProbabilityTheory Filter Topology Causalean.PO

namespace BackdoorEstimationSystem

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
  [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]

/-! ## L² building blocks (mirroring `aipw_finite_var`)

Under back-door assumptions, strict overlap and `L²` outcomes, the three
pieces `A = μ₁ − μ₀ − θ₀`, `B = (a/e)(y − μ₁)`, `C = ((1−a)/(1−e))(y − μ₀)`
of `ψ_AIPW ∘ factualZ` are each square-integrable against `P.μ`. -/

/-- The `L∞` propensity weight `a / e(X)` is bounded by `ε⁻¹`. -/
private lemma hahn_weight_true_Linf (S : BackdoorEstimationSystem P γ) {ε : ℝ}
    (h_overlap : S.StrictOverlap ε) :
    MemLp (fun ω => indA (S.factualZ ω) /
      S.e_val (S.toPOBackdoorSystem.factualX ω)) ⊤ P.μ := by
  have he_lower :
      ∀ᵐ ω ∂P.μ, ε ≤ S.e_val (S.toPOBackdoorSystem.factualX ω) := by
    filter_upwards [h_overlap.2.2, S.e_compat] with ω hover hcomp
    simpa [hcomp] using hover.1
  have hbound :
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
  refine MemLp.of_bound ?_ ε⁻¹ hbound
  apply Measurable.aestronglyMeasurable
  have hind : Measurable (fun ω => indA (S.factualZ ω)) := by
    simpa [indA, projA, BackdoorEstimationSystem.factualZ] using
      (Measurable.of_discrete
        (f := fun b : Bool => if b = true then (1 : ℝ) else 0)).comp
          S.toPOBackdoorSystem.measurable_factualD
  exact hind.div (S.e_meas.comp S.toPOBackdoorSystem.measurable_factualX)

/-- The `L∞` propensity weight `(1−a) / (1−e(X))` is bounded by `ε⁻¹`. -/
private lemma hahn_weight_false_Linf (S : BackdoorEstimationSystem P γ) {ε : ℝ}
    (h_overlap : S.StrictOverlap ε) :
    MemLp (fun ω => (1 - indA (S.factualZ ω)) /
      (1 - S.e_val (S.toPOBackdoorSystem.factualX ω))) ⊤ P.μ := by
  have he_upper :
      ∀ᵐ ω ∂P.μ, S.e_val (S.toPOBackdoorSystem.factualX ω) ≤ 1 - ε := by
    filter_upwards [h_overlap.2.2, S.e_compat] with ω hover hcomp
    simpa [hcomp] using hover.2
  have hbound :
      ∀ᵐ ω ∂P.μ,
        ‖(1 - indA (S.factualZ ω)) /
          (1 - S.e_val (S.toPOBackdoorSystem.factualX ω))‖ ≤ ε⁻¹ := by
    filter_upwards [he_upper] with ω he
    by_cases hD : S.toPOBackdoorSystem.factualD ω = true
    · have hεinv_nonneg : 0 ≤ ε⁻¹ := inv_nonneg.mpr h_overlap.1.le
      simpa [BackdoorEstimationSystem.factualZ, indA, projA, projX, hD] using hεinv_nonneg
    · have hden : ε ≤ 1 - S.e_val (S.toPOBackdoorSystem.factualX ω) := by linarith
      have hdenpos : 0 < 1 - S.e_val (S.toPOBackdoorSystem.factualX ω) :=
        lt_of_lt_of_le h_overlap.1 hden
      have hle : (1 - S.e_val (S.toPOBackdoorSystem.factualX ω))⁻¹ ≤ ε⁻¹ :=
        (inv_le_inv₀ hdenpos h_overlap.1).2 hden
      simpa [BackdoorEstimationSystem.factualZ, indA, projA, projX, hD, one_div,
        Real.norm_eq_abs, abs_of_pos hdenpos] using hle
  refine MemLp.of_bound ?_ ε⁻¹ hbound
  apply Measurable.aestronglyMeasurable
  have hind : Measurable (fun ω => indA (S.factualZ ω)) := by
    simpa [indA, projA, BackdoorEstimationSystem.factualZ] using
      (Measurable.of_discrete
        (f := fun b : Bool => if b = true then (1 : ℝ) else 0)).comp
          S.toPOBackdoorSystem.measurable_factualD
  exact (measurable_const.sub hind).div
    (measurable_const.sub (S.e_meas.comp S.toPOBackdoorSystem.measurable_factualX))

/-- `μ_val d ∘ factualX` is `L²(P.μ)` (via the derived counterfactual `μ_compat`
and conditional Jensen). The `μ_compat` reading now requires `Assumptions`, so this
lemma carries `hA`; its only caller (`aipw_variance_hahn_decomposition`) supplies it.
-/
private lemma hahn_mu_L2 (S : BackdoorEstimationSystem P γ)
    (hA : S.toPOBackdoorSystem.Assumptions)
    (h_yd2 : ∀ d : Bool, Integrable
      (fun ω => (S.toPOBackdoorSystem.YofD d ω) ^ 2) P.μ) (d : Bool) :
    MemLp (fun ω => S.μ_val d (S.toPOBackdoorSystem.factualX ω)) 2 P.μ := by
  have hYd_L2 : MemLp (S.toPOBackdoorSystem.YofD d) 2 P.μ :=
    (memLp_two_iff_integrable_sq
      (S.toPOBackdoorSystem.measurable_YofD d).aestronglyMeasurable).2 (h_yd2 d)
  exact (hYd_L2.condExp).ae_eq (S.μ_compat hA d)

/-! ## Hahn variance decomposition -/

set_option maxHeartbeats 1000000 in
-- The proof assembles many `MemLp`/integrability facts, a pointwise `ψ²`
-- expansion, two σ(X)-pull-out cross-term vanishings, and three pushforward
-- rewrites in one term, exceeding the default heartbeat budget.
/-- **Hahn (1998) variance decomposition** of the AIPW influence function.

Under the back-door assumptions, strict overlap, and square-integrability of
the factual and counterfactual outcomes, the variance of the AIPW influence
function splits into the variance of the conditional-ATE function plus the two
inverse-propensity-weighted conditional outcome variances:

    ∫ ψ_AIPW² dP_Z
      = ∫ (μ₁ − μ₀ − θ₀)² dP_X
        + ∫ (a / e²)   (y − μ₁)² dP_Z
        + ∫ ((1−a) / (1−e)²) (y − μ₀)² dP_Z.

The right-hand side is the Hahn semiparametric efficiency bound `V_H`.

The proof assembles many `MemLp`/integrability facts, a pointwise `ψ²`
expansion, two σ(X)-pull-out cross-term vanishings, and three pushforward
rewrites in a single term, so it exceeds the default heartbeat budget. -/
theorem aipw_variance_hahn_decomposition (S : BackdoorEstimationSystem P γ)
    {ε : ℝ}
    (h_overlap : S.StrictOverlap ε)
    (hA : S.toPOBackdoorSystem.Assumptions)
    (h_y2 : Integrable (fun ω => (S.toPOBackdoorSystem.factualY ω) ^ 2) P.μ)
    (h_yd2 : ∀ d : Bool, Integrable
      (fun ω => (S.toPOBackdoorSystem.YofD d ω) ^ 2) P.μ) :
    (∫ z, (S.ψ_AIPW z) ^ 2 ∂S.P_Z)
      = (∫ x, (S.μ_val true x - S.μ_val false x - S.θ₀) ^ 2 ∂S.P_X)
        + (∫ z, (indA z / (S.e_val (projX z)) ^ 2) *
            (projY z - S.μ_val true (projX z)) ^ 2 ∂S.P_Z)
        + (∫ z, ((1 - indA z) / (1 - S.e_val (projX z)) ^ 2) *
            (projY z - S.μ_val false (projX z)) ^ 2 ∂S.P_Z) := by
  classical
  -- Ω-level pieces.
  set X : P.Ω → γ := S.toPOBackdoorSystem.factualX with hX
  set Y : P.Ω → ℝ := S.toPOBackdoorSystem.factualY with hY
  set a : P.Ω → ℝ := fun ω => indA (S.factualZ ω) with ha
  set e : P.Ω → ℝ := fun ω => S.e_val (S.toPOBackdoorSystem.factualX ω) with he
  set μ1 : P.Ω → ℝ := fun ω => S.μ_val true (S.toPOBackdoorSystem.factualX ω) with hμ1
  set μ0 : P.Ω → ℝ := fun ω => S.μ_val false (S.toPOBackdoorSystem.factualX ω) with hμ0
  set Afn : P.Ω → ℝ := fun ω => μ1 ω - μ0 ω - S.θ₀ with hAfn
  set Bfn : P.Ω → ℝ := fun ω => (a ω / e ω) * (Y ω - μ1 ω) with hBfn
  set Cfn : P.Ω → ℝ := fun ω => ((1 - a ω) / (1 - e ω)) * (Y ω - μ0 ω) with hCfn
  -- `a ω` is `0` or `1`.
  have ha01 : ∀ ω, a ω = 0 ∨ a ω = 1 := by
    intro ω
    by_cases hD : S.toPOBackdoorSystem.factualD ω = true
    · right; simp [ha, indA, projA, BackdoorEstimationSystem.factualZ, hD]
    · left; simp [ha, indA, projA, BackdoorEstimationSystem.factualZ, hD]
  -- `a = 1_{D=true}` and `1 - a = 1_{D=false}`.
  have ha_ind : ∀ ω, a ω = S.toPOBackdoorSystem.dVar.indicator true ω := by
    intro ω
    by_cases hD : S.toPOBackdoorSystem.factualD ω = true
    · have hInd : S.toPOBackdoorSystem.dVar.indicator true ω = 1 :=
        S.toPOBackdoorSystem.dVar.indicator_apply_eq_one hD
      simp [ha, indA, projA, BackdoorEstimationSystem.factualZ, hD, hInd]
    · have hInd : S.toPOBackdoorSystem.dVar.indicator true ω = 0 :=
        S.toPOBackdoorSystem.dVar.indicator_apply_eq_zero (x := true) hD
      simp [ha, indA, projA, BackdoorEstimationSystem.factualZ, hD, hInd]
  have hna_ind : ∀ ω, 1 - a ω = S.toPOBackdoorSystem.dVar.indicator false ω := by
    intro ω
    have hsum : S.toPOBackdoorSystem.dVar.indicator true ω +
        S.toPOBackdoorSystem.dVar.indicator false ω = 1 :=
      S.toPOBackdoorSystem.dVar.indicator_add_indicator_not ω
    rw [ha_ind ω]; linarith
  -- `L²` membership of the three pieces.
  have hμ1_L2 : MemLp μ1 2 P.μ := S.hahn_mu_L2 hA h_yd2 true
  have hμ0_L2 : MemLp μ0 2 P.μ := S.hahn_mu_L2 hA h_yd2 false
  have hY_L2 : MemLp Y 2 P.μ :=
    (memLp_two_iff_integrable_sq
      S.toPOBackdoorSystem.measurable_factualY.aestronglyMeasurable).2 h_y2
  have hwT_Linf : MemLp (fun ω => a ω / e ω) ⊤ P.μ := S.hahn_weight_true_Linf h_overlap
  have hwF_Linf : MemLp (fun ω => (1 - a ω) / (1 - e ω)) ⊤ P.μ :=
    S.hahn_weight_false_Linf h_overlap
  have hA_L2 : MemLp Afn 2 P.μ := (hμ1_L2.sub hμ0_L2).sub (memLp_const _)
  have hBfn_L2' :
      MemLp (fun ω => (a ω / e ω) * (Y ω - μ1 ω)) 2 P.μ := by
    simpa using (hY_L2.sub hμ1_L2).mul hwT_Linf
  have hB_L2 : MemLp Bfn 2 P.μ := by simpa [hBfn] using hBfn_L2'
  have hCfn_L2' :
      MemLp (fun ω => ((1 - a ω) / (1 - e ω)) * (Y ω - μ0 ω)) 2 P.μ := by
    simpa using (hY_L2.sub hμ0_L2).mul hwF_Linf
  have hC_L2 : MemLp Cfn 2 P.μ := by simpa [hCfn] using hCfn_L2'
  -- Integrability of the five squared/cross pieces (each a product of two L²).
  have hAB_int : Integrable (fun ω => Afn ω * Bfn ω) P.μ :=
    hA_L2.integrable_mul hB_L2
  have hAC_int : Integrable (fun ω => Afn ω * Cfn ω) P.μ :=
    hA_L2.integrable_mul hC_L2
  have hA2_int : Integrable (fun ω => Afn ω ^ 2) P.μ := by
    simpa [sq] using hA_L2.integrable_mul hA_L2
  have hB2_int : Integrable (fun ω => Bfn ω ^ 2) P.μ := by
    simpa [sq] using hB_L2.integrable_mul hB_L2
  have hC2_int : Integrable (fun ω => Cfn ω ^ 2) P.μ := by
    simpa [sq] using hC_L2.integrable_mul hC_L2
  -- Pointwise expansion `ψ(factualZ ω)² = A² + B² + C² + 2AB − 2AC`.
  have hψ_sq : ∀ ω, (S.ψ_AIPW (S.factualZ ω)) ^ 2 =
      Afn ω ^ 2 + Bfn ω ^ 2 + Cfn ω ^ 2 +
        2 * (Afn ω * Bfn ω) - 2 * (Afn ω * Cfn ω) := by
    intro ω
    have hexpand :
        S.ψ_AIPW (S.factualZ ω) = Afn ω + Bfn ω - Cfn ω := by
      unfold BackdoorEstimationSystem.ψ_AIPW BackdoorEstimationSystem.aipwMoment
      simp only [BackdoorEstimationSystem.factualZ, projX, projY,
        hBfn, hCfn, ha, he, hμ1, hμ0, hY]
      ring
    rw [hexpand]
    simp only [hAfn, hBfn, hCfn]
    rcases ha01 ω with h0 | h1
    · rw [show a ω = 0 from h0]; ring
    · rw [show a ω = 1 from h1]; ring
  -- Cross-term weights `g` for the σ(X)-pull-out lemma.
  set gT : γ → ℝ := fun x => (S.μ_val true x - S.μ_val false x - S.θ₀) / S.e_val x
    with hgT
  set gF : γ → ℝ :=
    fun x => (S.μ_val true x - S.μ_val false x - S.θ₀) / (1 - S.e_val x) with hgF
  have hgT_meas : Measurable gT :=
    (((S.μ_meas true).sub (S.μ_meas false)).sub measurable_const).div S.e_meas
  have hgF_meas : Measurable gF :=
    (((S.μ_meas true).sub (S.μ_meas false)).sub measurable_const).div
      (measurable_const.sub S.e_meas)
  -- `A·B` is the `d = true` weighted residual.
  have hAB_eq : ∀ ω, Afn ω * Bfn ω =
      gT (S.toPOBackdoorSystem.factualX ω) *
        (S.toPOBackdoorSystem.dVar.indicator true ω *
          (S.toPOBackdoorSystem.factualY ω -
            S.μ_val true (S.toPOBackdoorSystem.factualX ω))) := by
    intro ω
    have hae := ha_ind ω
    simp only [hAfn, hBfn, hgT, hμ1, hμ0, hY, he]
    rw [← hae]
    ring
  have hAB_int' : Integrable
      (fun ω => gT (S.toPOBackdoorSystem.factualX ω) *
        (S.toPOBackdoorSystem.dVar.indicator true ω *
          (S.toPOBackdoorSystem.factualY ω -
            S.μ_val true (S.toPOBackdoorSystem.factualX ω)))) P.μ :=
    hAB_int.congr (Filter.Eventually.of_forall hAB_eq)
  have hAB_zero : ∫ ω, Afn ω * Bfn ω ∂P.μ = 0 := by
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hAB_eq)]
    exact S.weighted_residual_integral_zero hA true gT hgT_meas hAB_int'
      (S.cond_exp_residual_zero hA true)
  -- `A·C` is the `d = false` weighted residual.
  have hAC_eq : ∀ ω, Afn ω * Cfn ω =
      gF (S.toPOBackdoorSystem.factualX ω) *
        (S.toPOBackdoorSystem.dVar.indicator false ω *
          (S.toPOBackdoorSystem.factualY ω -
            S.μ_val false (S.toPOBackdoorSystem.factualX ω))) := by
    intro ω
    have hae := hna_ind ω
    simp only [hAfn, hCfn, hgF, hμ1, hμ0, hY, he]
    rw [← hae]
    ring
  have hAC_int' : Integrable
      (fun ω => gF (S.toPOBackdoorSystem.factualX ω) *
        (S.toPOBackdoorSystem.dVar.indicator false ω *
          (S.toPOBackdoorSystem.factualY ω -
            S.μ_val false (S.toPOBackdoorSystem.factualX ω)))) P.μ :=
    hAC_int.congr (Filter.Eventually.of_forall hAC_eq)
  have hAC_zero : ∫ ω, Afn ω * Cfn ω ∂P.μ = 0 := by
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hAC_eq)]
    exact S.weighted_residual_integral_zero hA false gF hgF_meas hAC_int'
      (S.cond_exp_residual_zero hA false)
  -- LHS: push `∫ ψ² ∂P_Z` to `∫ ψ(factualZ ·)² ∂P.μ`, expand and integrate.
  have hψ_meas : Measurable S.ψ_AIPW := S.measurable_ψ_AIPW
  have hLHS : (∫ z, (S.ψ_AIPW z) ^ 2 ∂S.P_Z)
      = (∫ ω, Afn ω ^ 2 ∂P.μ) + (∫ ω, Bfn ω ^ 2 ∂P.μ) +
          (∫ ω, Cfn ω ^ 2 ∂P.μ) := by
    rw [BackdoorEstimationSystem.P_Z,
      MeasureTheory.integral_map S.measurable_factualZ.aemeasurable
        (hψ_meas.pow_const 2).aestronglyMeasurable]
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hψ_sq)]
    have iAB : Integrable (fun ω => Afn ω ^ 2 + Bfn ω ^ 2) P.μ := hA2_int.add hB2_int
    have iABC : Integrable (fun ω => Afn ω ^ 2 + Bfn ω ^ 2 + Cfn ω ^ 2) P.μ :=
      iAB.add hC2_int
    have icAB : Integrable (fun ω => 2 * (Afn ω * Bfn ω)) P.μ := hAB_int.const_mul 2
    have icAC : Integrable (fun ω => 2 * (Afn ω * Cfn ω)) P.μ := hAC_int.const_mul 2
    have iABCpAB :
        Integrable (fun ω => (Afn ω ^ 2 + Bfn ω ^ 2 + Cfn ω ^ 2) +
          2 * (Afn ω * Bfn ω)) P.μ := iABC.add icAB
    rw [MeasureTheory.integral_sub iABCpAB icAC]
    rw [MeasureTheory.integral_add iABC icAB]
    rw [MeasureTheory.integral_add iAB hC2_int]
    rw [MeasureTheory.integral_add hA2_int hB2_int]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    rw [hAB_zero, hAC_zero]
    ring
  rw [hLHS]
  -- Term 1: `∫ A² ∂P.μ = ∫ (μ₁ − μ₀ − θ₀)² ∂P_X`.
  have hTerm1 : (∫ ω, Afn ω ^ 2 ∂P.μ)
      = ∫ x, (S.μ_val true x - S.μ_val false x - S.θ₀) ^ 2 ∂S.P_X := by
    rw [BackdoorEstimationSystem.P_X]
    rw [MeasureTheory.integral_map
      S.toPOBackdoorSystem.measurable_factualX.aemeasurable
      (by
        exact (((S.μ_meas true).sub (S.μ_meas false)).sub
          measurable_const).pow_const 2 |>.aestronglyMeasurable)]
  -- Term 2: `∫ B² ∂P.μ = ∫ (a/e²)(y − μ₁)² ∂P_Z`.
  have hTerm2 : (∫ ω, Bfn ω ^ 2 ∂P.μ)
      = ∫ z, indA z / S.e_val (projX z) ^ 2 *
          (projY z - S.μ_val true (projX z)) ^ 2 ∂S.P_Z := by
    rw [BackdoorEstimationSystem.P_Z]
    have hmeas2 : Measurable (fun z : γ × Bool × ℝ =>
        indA z / S.e_val (projX z) ^ 2 *
          (projY z - S.μ_val true (projX z)) ^ 2) := by
      have hx : Measurable (fun z : γ × Bool × ℝ => z.1) := measurable_fst
      have hy : Measurable (fun z : γ × Bool × ℝ => z.2.2) := measurable_snd.snd
      have hind : Measurable (fun z : γ × Bool × ℝ => indA z) := by
        unfold indA projA
        exact (Measurable.of_discrete
          (f := fun b : Bool => if b = true then (1 : ℝ) else 0)).comp
            measurable_snd.fst
      have he2 : Measurable (fun z : γ × Bool × ℝ => S.e_val (projX z) ^ 2) :=
        ((S.e_meas.comp hx).pow_const 2)
      have hμt : Measurable (fun z : γ × Bool × ℝ => S.μ_val true (projX z)) :=
        (S.μ_meas true).comp hx
      exact (hind.div he2).mul ((hy.sub hμt).pow_const 2)
    rw [MeasureTheory.integral_map S.measurable_factualZ.aemeasurable
      hmeas2.aestronglyMeasurable]
    apply MeasureTheory.integral_congr_ae
    refine Filter.Eventually.of_forall (fun ω => ?_)
    change Bfn ω ^ 2 = a ω / e ω ^ 2 * (Y ω - μ1 ω) ^ 2
    have hsq : a ω ^ 2 = a ω := by rcases ha01 ω with h | h <;> rw [h] <;> ring
    simp only [hBfn]
    rw [mul_pow, div_pow, hsq]
  -- Term 3: `∫ C² ∂P.μ = ∫ ((1−a)/(1−e)²)(y − μ₀)² ∂P_Z`.
  have hTerm3 : (∫ ω, Cfn ω ^ 2 ∂P.μ)
      = ∫ z, (1 - indA z) / (1 - S.e_val (projX z)) ^ 2 *
          (projY z - S.μ_val false (projX z)) ^ 2 ∂S.P_Z := by
    rw [BackdoorEstimationSystem.P_Z]
    have hmeas3 : Measurable (fun z : γ × Bool × ℝ =>
        (1 - indA z) / (1 - S.e_val (projX z)) ^ 2 *
          (projY z - S.μ_val false (projX z)) ^ 2) := by
      have hx : Measurable (fun z : γ × Bool × ℝ => z.1) := measurable_fst
      have hy : Measurable (fun z : γ × Bool × ℝ => z.2.2) := measurable_snd.snd
      have hind : Measurable (fun z : γ × Bool × ℝ => indA z) := by
        unfold indA projA
        exact (Measurable.of_discrete
          (f := fun b : Bool => if b = true then (1 : ℝ) else 0)).comp
            measurable_snd.fst
      have he2 : Measurable (fun z : γ × Bool × ℝ =>
          (1 - S.e_val (projX z)) ^ 2) :=
        ((measurable_const.sub (S.e_meas.comp hx)).pow_const 2)
      have hμf : Measurable (fun z : γ × Bool × ℝ => S.μ_val false (projX z)) :=
        (S.μ_meas false).comp hx
      exact ((measurable_const.sub hind).div he2).mul ((hy.sub hμf).pow_const 2)
    rw [MeasureTheory.integral_map S.measurable_factualZ.aemeasurable
      hmeas3.aestronglyMeasurable]
    apply MeasureTheory.integral_congr_ae
    refine Filter.Eventually.of_forall (fun ω => ?_)
    change Cfn ω ^ 2 = (1 - a ω) / (1 - e ω) ^ 2 * (Y ω - μ0 ω) ^ 2
    have hsq : (1 - a ω) ^ 2 = 1 - a ω := by
      rcases ha01 ω with h | h <;> rw [h] <;> ring
    simp only [hCfn]
    rw [mul_pow, div_pow, hsq]
  rw [hTerm1, hTerm2, hTerm3]

end BackdoorEstimationSystem

open Causalean.Stat
open BackdoorEstimationSystem

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
  [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]

/-- **The one-shot DML ATE attains the Hahn efficiency bound.**

Composing `dml_ATE_tendstoNormal` with `aipw_variance_hahn_decomposition`,
the rescaled estimator `√|B(n)| (θ̂ⁿ − θ₀)` converges in distribution to the
mean-zero Gaussian whose variance is the Hahn semiparametric efficiency bound

    V_H = ∫ (μ₁ − μ₀ − θ₀)² dP_X
          + ∫ (a / e²)   (y − μ₁)² dP_Z
          + ∫ ((1−a) / (1−e)²) (y − μ₀)² dP_Z.

The hypotheses are exactly those of `dml_ATE_tendstoNormal`; the conclusion
only rewrites the limiting variance via the variance decomposition. -/
theorem dml_ATE_attains_hahn_bound
    (S : BackdoorEstimationSystem P γ)
    {ε : ℝ}
    (hA : S.toPOBackdoorSystem.Assumptions)
    (h_overlap : S.StrictOverlap ε)
    (h_y2 : Integrable (fun ω => (S.toPOBackdoorSystem.factualY ω) ^ 2) P.μ)
    (h_yd2 : ∀ d : Bool, Integrable
      (fun ω => (S.toPOBackdoorSystem.YofD d ω) ^ 2) P.μ)
    (sample : IIDSample P.Ω (γ × Bool × ℝ) P.μ S.P_Z)
    (split : OneShotSplit sample)
    {c : ℝ} (hc_pos : 0 < c) (hc_lt : c < 1)
    (h_split_rate :
      Tendsto (fun n => ((split.foldB n).card : ℝ) / n) atTop (𝓝 c))
    (μ_hat : ℕ → P.Ω → (Bool → γ → ℝ))
    (e_hat : ℕ → P.Ω → (γ → ℝ))
    (h_mu_meas :
      ∀ n a, Measurable (fun (p : P.Ω × γ) => μ_hat n p.1 a p.2))
    (h_e_meas :
      ∀ n, Measurable (fun (p : P.Ω × γ) => e_hat n p.1 p.2))
    (h_mu_memLp :
      ∀ n ω a, MemLp (fun x => μ_hat n ω a x) 2 S.P_X)
    (h_e_memLp :
      ∀ n ω, MemLp (fun x => e_hat n ω x) 2 S.P_X)
    (h_e_overlap :
      ∀ n ω, ∀ᵐ x ∂S.P_X, ε ≤ e_hat n ω x ∧ e_hat n ω x ≤ 1 - ε)
    (h_mu_foldA :
      ∀ n,
        Measurable[MeasurableSpace.comap
          (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance]
          (μ_hat n))
    (h_e_foldA :
      ∀ n,
        Measurable[MeasurableSpace.comap
          (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance]
          (e_hat n))
    (h_mu_uncurry_foldA :
      ∀ n a,
        Measurable[(MeasurableSpace.comap
            (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance).prod
          (inferInstance : MeasurableSpace γ)]
          (fun (p : P.Ω × γ) => μ_hat n p.1 a p.2))
    (h_e_uncurry_foldA :
      ∀ n,
        Measurable[(MeasurableSpace.comap
            (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance).prod
          (inferInstance : MeasurableSpace γ)]
          (fun (p : P.Ω × γ) => e_hat n p.1 p.2))
    (h_mu_rate :
      ∀ a : Bool,
        IsLittleOp
          (fun n ω =>
            (eLpNorm (fun x => μ_hat n ω a x - S.μ_val a x) 2 S.P_X).toReal)
          (fun _ => (1 : ℝ)) P.μ)
    (h_e_rate :
      IsLittleOp
        (fun n ω =>
          (eLpNorm (fun x => e_hat n ω x - S.e_val x) 2 S.P_X).toReal)
        (fun _ => (1 : ℝ)) P.μ)
    (h_product_rate :
      ∀ a : Bool,
        IsLittleOp
          (fun n ω =>
            (eLpNorm (fun x => μ_hat n ω a x - S.μ_val a x) 2 S.P_X).toReal *
              (eLpNorm (fun x => e_hat n ω x - S.e_val x) 2 S.P_X).toReal)
          (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) P.μ)
    (hψ_meas : Measurable (S.ψ_AIPW))
    (hθn_meas : ∀ n : ℕ, AEMeasurable
      (IsAsymLinear.rescaledEstimator
        (dmlEstimator S sample split μ_hat e_hat) S.θ₀ split.foldB n) P.μ)
    (hSum_meas : ∀ n : ℕ, AEMeasurable
      (IsAsymLinear.normalizedSum sample (S.ψ_AIPW) split.foldB n) P.μ) :
    Tendsto_dist
      (IsAsymLinear.rescaledEstimator
        (dmlEstimator S sample split μ_hat e_hat) S.θ₀ split.foldB)
      (gaussianMeasure 0
        ((∫ x, (S.μ_val true x - S.μ_val false x - S.θ₀) ^ 2 ∂S.P_X)
          + (∫ z, (indA z / (S.e_val (projX z)) ^ 2) *
              (projY z - S.μ_val true (projX z)) ^ 2 ∂S.P_Z)
          + (∫ z, ((1 - indA z) / (1 - S.e_val (projX z)) ^ 2) *
              (projY z - S.μ_val false (projX z)) ^ 2 ∂S.P_Z)))
      P.μ
      hθn_meas := by
  rw [← S.aipw_variance_hahn_decomposition h_overlap hA h_y2 h_yd2]
  exact dml_ATE_tendstoNormal S hA h_overlap h_y2 h_yd2
    sample split hc_pos hc_lt h_split_rate μ_hat e_hat h_mu_meas h_e_meas
    h_mu_memLp h_e_memLp h_e_overlap h_mu_foldA h_e_foldA
    h_mu_uncurry_foldA h_e_uncurry_foldA h_mu_rate h_e_rate h_product_rate
    hψ_meas hθn_meas hSum_meas

end ATE
end Estimation
end Causalean
