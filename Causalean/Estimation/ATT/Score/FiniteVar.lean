import Causalean.Estimation.ATT.Score.AIPWMoment
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
Proves finite variance for the ATT AIPW moment under back-door assumptions,
one-sided overlap, and square-integrable outcomes. The result supplies the L2
input required by the ATT asymptotic-linear and CLT arguments.
-/

/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Finite variance of the ATT AIPW moment — `lem:est-aipw-finite-var-att`

`E[(m_AIPW^ATT)²] < ∞` under the one-sided ATT back-door assumption bundle, a
one-sided upper-overlap bound, and square-integrability of the factual
outcome and the control-arm counterfactual outcome `Y(0)`.  Parallels
`Estimation/ATE/Score/FiniteVar.lean`.
-/

/-!
This file proves that the augmented inverse-probability weighted moment for the
average treatment effect on the treated has finite variance under the one-sided
ATT back-door assumption bundle, a separate one-sided upper-overlap bound, and
square-integrable outcomes.

The public results are `aipw_finite_var_ATT`, square-integrability of the truth
moment against `P_Z`, `ipw_estimated_integrable`, integrability of a
learner-side control-arm IPW correction from one-sided overlap and an
`L²(P_X)` control regression, and `ipw_truth_integrable`, the corresponding
PO-level truth integrability fact used by the mean-zero and DML arguments.
-/

namespace Causalean
namespace Estimation
namespace ATT

open MeasureTheory ProbabilityTheory Filter Topology Causalean.PO
open Causalean.Estimation.ATE.BackdoorEstimationSystem (projX projA projY indA)

namespace TreatedEstimationSystem

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
  [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]

/-- **Finite variance of the ATT AIPW moment** — `lem:est-aipw-finite-var-att`.

Under the one-sided ATT back-door assumption bundle, one-sided upper overlap
(`ε ∈ (0, 1/2]`), `E[Y²] < ∞`, and square-integrability of the
control-arm counterfactual `Y(0)`, the ATT AIPW moment evaluated at the truth
is square-integrable against the data law `P_Z`.

The `h_y0_2` hypothesis is needed because `μ₀_val ∘ factualX =ᵐ μ[Y(0)|σX]`
(via `μ₀_compat`), and conditional Jensen converts square-integrability of
`Y(0)` into square-integrability of its conditional expectation.

Only the `< 1` (one-sided) overlap is required because the control-arm IPW
weight `e/(1−e)` is bounded by `(1−ε)/ε` under that bound; the treated-arm
factor `A` is already in `[0,1]`. -/
-- Outline: mirror `aipw_finite_var` from `Estimation/ATE/Score/FiniteVar.lean`.
-- Steps: (i) measurability of the moment; (ii) `Y, μ₀ ∈ L²` via
-- `memLp_two_iff_integrable_sq` and `MemLp.condExp` on `μ[Y(0)|σX]`;
-- (iii) `(1−A)·e/(1−e)` is `L^∞` from `e_val ≤ 1−ε`; (iv) `A` is `L^∞`;
-- (v) `MemLp.mul`-products; (vi) sum to get the moment in `L²`; (vii)
-- transfer from `P.μ` to `P_Z` via `memLp_map_measure_iff`.
theorem aipw_finite_var_ATT
    (S : TreatedEstimationSystem P γ) {ε : ℝ}
    (h_overlap : S.OneSidedOverlap ε)
    (hA : S.toPOBackdoorSystem.ATTAssumptions)
    (h_y2 : Integrable (fun ω => (S.toPOBackdoorSystem.factualY ω) ^ 2) P.μ)
    (h_y0_2 : Integrable
      (fun ω => (S.toPOBackdoorSystem.YofD false ω) ^ 2) P.μ) :
    Integrable
      (fun z => (aipwMomentATT z S.μ₀_val S.e_val S.θ₀) ^ 2) S.P_Z := by
  have hmoment_meas :
      Measurable (fun z => aipwMomentATT z S.μ₀_val S.e_val S.θ₀) := by
    simpa [aipwMomentATTFunctional, η₀] using
      (measurable_aipwMomentATTFunctional (η := S.η₀) (θ := S.θ₀))
  have hY_L2 : MemLp S.toPOBackdoorSystem.factualY 2 P.μ := by
    exact (memLp_two_iff_integrable_sq
      S.toPOBackdoorSystem.measurable_factualY.aestronglyMeasurable).2 h_y2
  have hμ₀_L2 :
      MemLp (fun ω => S.μ₀_val (S.toPOBackdoorSystem.factualX ω)) 2 P.μ := by
    have hY0_L2 : MemLp (S.toPOBackdoorSystem.YofD false) 2 P.μ := by
      exact (memLp_two_iff_integrable_sq
        (S.toPOBackdoorSystem.measurable_YofD false).aestronglyMeasurable).2 h_y0_2
    have hcond_L2 :
        MemLp (P.μ[S.toPOBackdoorSystem.YofD false |
          S.toPOBackdoorSystem.sigmaX]) 2 P.μ :=
      hY0_L2.condExp
    exact hcond_L2.ae_eq (S.μ₀_compat hA)
  have hindA_meas : Measurable (fun ω => indA (S.factualZ ω)) := by
    simpa [indA, ATE.BackdoorEstimationSystem.projA,
      TreatedEstimationSystem.factualZ] using
      (Measurable.of_discrete
        (f := fun b : Bool => if b = true then (1 : ℝ) else 0)).comp
          S.toPOBackdoorSystem.measurable_factualD
  have hA_bound :
      ∀ᵐ ω ∂P.μ, ‖indA (S.factualZ ω)‖ ≤ (1 : ℝ) := by
    filter_upwards with ω
    by_cases hD : S.toPOBackdoorSystem.factualD ω = true
    · simp [TreatedEstimationSystem.factualZ, indA,
        ATE.BackdoorEstimationSystem.projA, hD]
    · simp [TreatedEstimationSystem.factualZ, indA,
        ATE.BackdoorEstimationSystem.projA, hD]
  have hA_Linf : MemLp (fun ω => indA (S.factualZ ω)) ⊤ P.μ := by
    exact MemLp.of_bound hindA_meas.aestronglyMeasurable (1 : ℝ) hA_bound
  have he_nonneg :
      ∀ᵐ ω ∂P.μ, 0 ≤ S.e_val (S.toPOBackdoorSystem.factualX ω) := by
    filter_upwards [S.propScore_true_nonneg_ae, S.e_compat] with ω hnonneg hcomp
    simpa [hcomp] using hnonneg
  have he_upper :
      ∀ᵐ ω ∂P.μ, S.e_val (S.toPOBackdoorSystem.factualX ω) ≤ 1 - ε := by
    filter_upwards [h_overlap.2.2, S.e_compat] with ω hover hcomp
    simpa [hcomp] using hover
  have hw_false_bound :
      ∀ᵐ ω ∂P.μ,
        ‖(1 - indA (S.factualZ ω)) *
          (S.e_val (S.toPOBackdoorSystem.factualX ω) /
            (1 - S.e_val (S.toPOBackdoorSystem.factualX ω)))‖ ≤ ε⁻¹ := by
    filter_upwards [he_nonneg, he_upper] with ω hnonneg hupper
    by_cases hD : S.toPOBackdoorSystem.factualD ω = true
    · have hεinv_nonneg : 0 ≤ ε⁻¹ := inv_nonneg.mpr h_overlap.1.le
      simpa [TreatedEstimationSystem.factualZ, indA,
        ATE.BackdoorEstimationSystem.projA, hD] using hεinv_nonneg
    · have hden : ε ≤ 1 - S.e_val (S.toPOBackdoorSystem.factualX ω) := by
        linarith
      have hdenpos : 0 < 1 - S.e_val (S.toPOBackdoorSystem.factualX ω) :=
        lt_of_lt_of_le h_overlap.1 hden
      have hle_inv :
          (1 - S.e_val (S.toPOBackdoorSystem.factualX ω))⁻¹ ≤ ε⁻¹ :=
        (inv_le_inv₀ hdenpos h_overlap.1).2 hden
      have he_le_one : S.e_val (S.toPOBackdoorSystem.factualX ω) ≤ 1 := by
        linarith
      have hratio_nonneg :
          0 ≤ S.e_val (S.toPOBackdoorSystem.factualX ω) /
            (1 - S.e_val (S.toPOBackdoorSystem.factualX ω)) :=
        div_nonneg hnonneg hdenpos.le
      have hratio_le :
          S.e_val (S.toPOBackdoorSystem.factualX ω) /
              (1 - S.e_val (S.toPOBackdoorSystem.factualX ω)) ≤ ε⁻¹ := by
        calc
          S.e_val (S.toPOBackdoorSystem.factualX ω) /
              (1 - S.e_val (S.toPOBackdoorSystem.factualX ω))
              = S.e_val (S.toPOBackdoorSystem.factualX ω) *
                  (1 - S.e_val (S.toPOBackdoorSystem.factualX ω))⁻¹ := by
                rw [div_eq_mul_inv]
          _ ≤ 1 * ε⁻¹ := by
                exact mul_le_mul he_le_one hle_inv
                  (inv_nonneg.mpr hdenpos.le) zero_le_one
          _ = ε⁻¹ := one_mul _
      have hnorm_eq :
          ‖(1 - indA (S.factualZ ω)) *
            (S.e_val (S.toPOBackdoorSystem.factualX ω) /
              (1 - S.e_val (S.toPOBackdoorSystem.factualX ω)))‖
            = S.e_val (S.toPOBackdoorSystem.factualX ω) /
              (1 - S.e_val (S.toPOBackdoorSystem.factualX ω)) := by
        have hind_eq : indA (S.factualZ ω) = 0 := by
          simp only [TreatedEstimationSystem.factualZ, indA,
            ATE.BackdoorEstimationSystem.projA, hD]
          rfl
        rw [hind_eq]
        change ‖(1 - 0) *
            (S.e_val (S.toPOBackdoorSystem.factualX ω) /
              (1 - S.e_val (S.toPOBackdoorSystem.factualX ω)))‖
          = S.e_val (S.toPOBackdoorSystem.factualX ω) /
              (1 - S.e_val (S.toPOBackdoorSystem.factualX ω))
        rw [sub_zero, one_mul, Real.norm_eq_abs, abs_of_nonneg hratio_nonneg]
      rw [hnorm_eq]
      exact hratio_le
  have hw_false_Linf :
      MemLp
        (fun ω =>
          (1 - indA (S.factualZ ω)) *
            (S.e_val (S.toPOBackdoorSystem.factualX ω) /
              (1 - S.e_val (S.toPOBackdoorSystem.factualX ω)))) ⊤ P.μ := by
    refine MemLp.of_bound ?_ ε⁻¹ hw_false_bound
    apply Measurable.aestronglyMeasurable
    exact (measurable_const.sub hindA_meas).mul
      ((S.e_meas.comp S.toPOBackdoorSystem.measurable_factualX).div
        (measurable_const.sub
          (S.e_meas.comp S.toPOBackdoorSystem.measurable_factualX)))
  have hterm_true_L2 :
      MemLp
        (fun ω =>
          indA (S.factualZ ω) *
            (S.toPOBackdoorSystem.factualY ω -
              S.μ₀_val (S.toPOBackdoorSystem.factualX ω))) 2 P.μ := by
    simpa [mul_comm] using (hY_L2.sub hμ₀_L2).mul hA_Linf
  have hterm_false_L2 :
      MemLp
        (fun ω =>
          ((1 - indA (S.factualZ ω)) *
            (S.e_val (S.toPOBackdoorSystem.factualX ω) /
              (1 - S.e_val (S.toPOBackdoorSystem.factualX ω)))) *
            (S.toPOBackdoorSystem.factualY ω -
              S.μ₀_val (S.toPOBackdoorSystem.factualX ω))) 2 P.μ := by
    exact MemLp.mul' (p := ⊤) (q := 2) (r := 2)
      (hY_L2.sub hμ₀_L2) hw_false_Linf
  have htheta_L2 :
      MemLp (fun ω => indA (S.factualZ ω) * S.θ₀) 2 P.μ := by
    exact MemLp.mul' (p := ⊤) (q := 2) (r := 2)
      (memLp_const (α := P.Ω) S.θ₀) hA_Linf
  have hmoment_comp_L2 :
      MemLp
        (fun ω => aipwMomentATT (S.factualZ ω) S.μ₀_val S.e_val S.θ₀) 2 P.μ := by
    have hsum_L2 := (hterm_true_L2.sub hterm_false_L2).sub htheta_L2
    simpa [aipwMomentATT, TreatedEstimationSystem.factualZ,
      ATE.BackdoorEstimationSystem.projX, ATE.BackdoorEstimationSystem.projY]
      using hsum_L2
  have hmoment_L2 :
      MemLp (fun z => aipwMomentATT z S.μ₀_val S.e_val S.θ₀) 2 S.P_Z := by
    rw [TreatedEstimationSystem.P_Z]
    exact (memLp_map_measure_iff hmoment_meas.aestronglyMeasurable
      S.measurable_factualZ.aemeasurable).2 hmoment_comp_L2
  exact hmoment_L2.integrable_sq

/-! ## Integrability of the IPW correction (derived, not assumed) -/

/-- **Integrability of an estimated-nuisance ATT IPW correction** (over `P_Z`).

For any nuisance pair with `0 ≤ e ≤ 1 − ε` `P_X`-a.e. and `μ₀ ∈ L²(P_X)`, the
value-space control-arm IPW residual `(1 − A)·(e/(1−e))·(Y − μ₀)` is
`L²(P_Z) ⊆ L¹(P_Z)`: the weight `(1 − A)·e/(1−e)` is `P_Z`-a.e. bounded by `ε⁻¹`
and the residual `Y − μ₀` is square-integrable.  Discharges the per-learner
`h_IPW_at` integrability gate from one-sided overlap and `L²` learners. -/
theorem ipw_estimated_integrable
    (S : TreatedEstimationSystem P γ) {ε : ℝ} (hε : 0 < ε)
    (η : TreatedNuisanceVec γ)
    (he_lb : ∀ᵐ x ∂S.P_X, 0 ≤ η.e_fn x)
    (he_ub : ∀ᵐ x ∂S.P_X, η.e_fn x ≤ 1 - ε)
    (hμ₀_memLp : MemLp η.μ₀_fn 2 S.P_X)
    (h_y2 : Integrable (fun ω => (S.toPOBackdoorSystem.factualY ω) ^ 2) P.μ) :
    Integrable (fun z =>
        (1 - indA z) * (η.e_fn (projX z) / (1 - η.e_fn (projX z)))
          * (projY z - η.μ₀_fn (projX z))) S.P_Z := by
  haveI : IsProbabilityMeasure S.P_Z := by
    unfold TreatedEstimationSystem.P_Z
    exact Measure.isProbabilityMeasure_map S.measurable_factualZ.aemeasurable
  have hX : Measurable (projX : γ × Bool × ℝ → γ) := by unfold projX; fun_prop
  have hYm : Measurable (projY : γ × Bool × ℝ → ℝ) := by unfold projY; fun_prop
  have hAm : Measurable (projA : γ × Bool × ℝ → Bool) := by unfold projA; fun_prop
  have hindA : Measurable (indA : γ × Bool × ℝ → ℝ) := by
    unfold indA
    refine Measurable.ite ?_ measurable_const measurable_const
    exact hAm (MeasurableSet.singleton true)
  have heX : Measurable (fun z : γ × Bool × ℝ => η.e_fn (projX z)) := η.e_meas.comp hX
  -- transfer the `P_X`-a.e. propensity bounds to `P_Z`-a.e. along `projX`
  have hmap : S.P_Z.map (fun z : γ × Bool × ℝ => z.1) = S.P_X :=
    S.P_Z_map_projX_eq_P_X
  have he_lb_Z : ∀ᵐ z ∂S.P_Z, 0 ≤ η.e_fn (projX z) := by
    rw [← hmap] at he_lb
    exact (ae_map_iff hX.aemeasurable
      (measurableSet_le measurable_const η.e_meas)).mp he_lb
  have he_ub_Z : ∀ᵐ z ∂S.P_Z, η.e_fn (projX z) ≤ 1 - ε := by
    rw [← hmap] at he_ub
    exact (ae_map_iff hX.aemeasurable
      (measurableSet_le η.e_meas measurable_const)).mp he_ub
  -- the IPW weight is bounded by `ε⁻¹`, hence in `L^∞`
  have hw_bound : ∀ᵐ z ∂S.P_Z,
      ‖(1 - indA z) * (η.e_fn (projX z) / (1 - η.e_fn (projX z)))‖ ≤ ε⁻¹ := by
    filter_upwards [he_lb_Z, he_ub_Z] with z hlb hub
    by_cases hAz : projA z = true
    · have h1 : indA z = 1 := by simp [indA, hAz]
      rw [h1]; simp only [sub_self, zero_mul, norm_zero]; exact inv_nonneg.mpr hε.le
    · have h0 : indA z = 0 := by simp [indA, hAz]
      have hden : ε ≤ 1 - η.e_fn (projX z) := by linarith
      have hdenpos : 0 < 1 - η.e_fn (projX z) := lt_of_lt_of_le hε hden
      have hle_inv : (1 - η.e_fn (projX z))⁻¹ ≤ ε⁻¹ := (inv_le_inv₀ hdenpos hε).2 hden
      have he_le_one : η.e_fn (projX z) ≤ 1 := by linarith
      have hratio_nonneg : 0 ≤ η.e_fn (projX z) / (1 - η.e_fn (projX z)) :=
        div_nonneg hlb hdenpos.le
      have hratio_le : η.e_fn (projX z) / (1 - η.e_fn (projX z)) ≤ ε⁻¹ := by
        rw [div_eq_mul_inv]
        calc η.e_fn (projX z) * (1 - η.e_fn (projX z))⁻¹
            ≤ 1 * ε⁻¹ :=
              mul_le_mul he_le_one hle_inv (inv_nonneg.mpr hdenpos.le) zero_le_one
          _ = ε⁻¹ := one_mul _
      rw [h0]
      simp only [sub_zero, one_mul, Real.norm_eq_abs, abs_of_nonneg hratio_nonneg]
      exact hratio_le
  have hw_Linf : MemLp
      (fun z => (1 - indA z) * (η.e_fn (projX z) / (1 - η.e_fn (projX z)))) ⊤ S.P_Z := by
    refine MemLp.of_bound ?_ ε⁻¹ hw_bound
    exact ((measurable_const.sub hindA).mul
      (heX.div (measurable_const.sub heX))).aestronglyMeasurable
  -- the residual `Y − μ₀` is in `L²(P_Z)`
  have hprojY_L2 : MemLp (projY : γ × Bool × ℝ → ℝ) 2 S.P_Z := by
    rw [TreatedEstimationSystem.P_Z]
    refine (memLp_map_measure_iff hYm.aestronglyMeasurable
      S.measurable_factualZ.aemeasurable).2 ?_
    exact (memLp_two_iff_integrable_sq
      S.toPOBackdoorSystem.measurable_factualY.aestronglyMeasurable).2 h_y2
  have hμX_L2 : MemLp (fun z : γ × Bool × ℝ => η.μ₀_fn (projX z)) 2 S.P_Z := by
    have h1 : MemLp η.μ₀_fn 2 (S.P_Z.map (fun z : γ × Bool × ℝ => z.1)) := by
      rw [hmap]; exact hμ₀_memLp
    exact (memLp_map_measure_iff η.μ₀_meas.aestronglyMeasurable hX.aemeasurable).1 h1
  have hresid_L2 : MemLp (fun z => projY z - η.μ₀_fn (projX z)) 2 S.P_Z :=
    hprojY_L2.sub hμX_L2
  exact (MemLp.mul' (p := ⊤) (q := 2) (r := 2) hresid_L2 hw_Linf).integrable (by norm_num)

/-- **Integrability of the truth-nuisance ATT IPW correction** (over `P.μ`).

The PO-level control-arm IPW residual is `L²(P.μ) ⊆ L¹(P.μ)`.  Derived from
`ipw_estimated_integrable` at the truth `η₀`: transfer the value-space integral
back to `P.μ` along the data map `factualZ`, then rewrite to the PO
representatives via `e_compat`, `μ₀_reg_compat`, and the indicator identity.
Discharges the `hIPW` gate of `aipw_mean_zero_ATT` / `att_dml_isAsymLinear`
from one-sided overlap and `L²` outcomes alone (no pointwise bounds). -/
theorem ipw_truth_integrable
    (S : TreatedEstimationSystem P γ) {ε : ℝ}
    (h_overlap : S.OneSidedOverlap ε)
    (hA : S.toPOBackdoorSystem.ATTAssumptions)
    (h_y2 : Integrable (fun ω => (S.toPOBackdoorSystem.factualY ω) ^ 2) P.μ)
    (h_y0_2 : Integrable (fun ω => (S.toPOBackdoorSystem.YofD false ω) ^ 2) P.μ) :
    Integrable (fun ω =>
        (1 - S.toPOBackdoorSystem.dVar.indicator true ω)
          * (S.toPOBackdoorSystem.propScore true ω
              / (1 - S.toPOBackdoorSystem.propScore true ω))
          * (S.toPOBackdoorSystem.factualY ω
              - S.toPOBackdoorSystem.adjustedCE false ω)) P.μ := by
  haveI : IsProbabilityMeasure S.P_X := by
    unfold TreatedEstimationSystem.P_X
    exact Measure.isProbabilityMeasure_map
      S.toPOBackdoorSystem.measurable_factualX.aemeasurable
  -- `μ₀_val ∈ L²(P_X)` from `μ₀_val ∘ factualX =ᵐ μ[Y(0)|σX]` and conditional Jensen
  have hμ₀_val_memLp : MemLp S.μ₀_val 2 S.P_X := by
    have hY0_L2 : MemLp (S.toPOBackdoorSystem.YofD false) 2 P.μ :=
      (memLp_two_iff_integrable_sq
        (S.toPOBackdoorSystem.measurable_YofD false).aestronglyMeasurable).2 h_y0_2
    have hcomp_L2 :
        MemLp (fun ω => S.μ₀_val (S.toPOBackdoorSystem.factualX ω)) 2 P.μ :=
      hY0_L2.condExp.ae_eq (S.μ₀_compat hA)
    rw [TreatedEstimationSystem.P_X]
    exact (memLp_map_measure_iff S.μ₀_meas.aestronglyMeasurable
      S.toPOBackdoorSystem.measurable_factualX.aemeasurable).2 hcomp_L2
  -- transfer the `P.μ`-a.e. propensity bounds (via `e_compat`) to `P_X`-a.e.
  have he_lb_PX : ∀ᵐ x ∂S.P_X, 0 ≤ S.e_val x := by
    rw [TreatedEstimationSystem.P_X]
    refine (ae_map_iff S.toPOBackdoorSystem.measurable_factualX.aemeasurable
      (measurableSet_le measurable_const S.e_meas)).mpr ?_
    filter_upwards [S.propScore_true_nonneg_ae, S.e_compat] with ω hov hc
    rw [← hc]; exact hov
  have he_ub_PX : ∀ᵐ x ∂S.P_X, S.e_val x ≤ 1 - ε := by
    rw [TreatedEstimationSystem.P_X]
    refine (ae_map_iff S.toPOBackdoorSystem.measurable_factualX.aemeasurable
      (measurableSet_le S.e_meas measurable_const)).mpr ?_
    filter_upwards [h_overlap.2.2, S.e_compat] with ω hov hc
    rw [← hc]; exact hov
  -- value-space integrability at the truth, then transfer `P_Z → P.μ`
  have hval := ipw_estimated_integrable S h_overlap.1 S.η₀ he_lb_PX he_ub_PX
    hμ₀_val_memLp h_y2
  have hmeas_g : AEStronglyMeasurable
      (fun z => (1 - indA z) * (S.η₀.e_fn (projX z) / (1 - S.η₀.e_fn (projX z)))
        * (projY z - S.η₀.μ₀_fn (projX z))) S.P_Z :=
    hval.aestronglyMeasurable
  have htransfer := ((integrable_map_measure hmeas_g
    S.measurable_factualZ.aemeasurable).mp
    (by rw [← TreatedEstimationSystem.P_Z]; exact hval))
  refine htransfer.congr ?_
  filter_upwards [S.e_compat, S.μ₀_reg_compat] with ω he hμ
  have hindA_eq :
      indA (S.factualZ ω) = S.toPOBackdoorSystem.dVar.indicator true ω := by
    by_cases hD : S.toPOBackdoorSystem.factualD ω = true
    · simp [TreatedEstimationSystem.factualZ, indA, projA, hD,
        S.toPOBackdoorSystem.dVar.indicator_apply_eq_one hD]
    · simp [TreatedEstimationSystem.factualZ, indA, projA, hD,
        S.toPOBackdoorSystem.dVar.indicator_apply_eq_zero (x := true) hD]
  change (1 - indA (S.factualZ ω))
        * (S.η₀.e_fn (projX (S.factualZ ω)) / (1 - S.η₀.e_fn (projX (S.factualZ ω))))
        * (projY (S.factualZ ω) - S.η₀.μ₀_fn (projX (S.factualZ ω)))
      = (1 - S.toPOBackdoorSystem.dVar.indicator true ω)
          * (S.toPOBackdoorSystem.propScore true ω
              / (1 - S.toPOBackdoorSystem.propScore true ω))
          * (S.toPOBackdoorSystem.factualY ω
              - S.toPOBackdoorSystem.adjustedCE false ω)
  rw [hindA_eq]
  simp only [TreatedEstimationSystem.factualZ, projX, projY,
    TreatedEstimationSystem.η₀, ← he, hμ]

end TreatedEstimationSystem

end ATT
end Estimation
end Causalean
