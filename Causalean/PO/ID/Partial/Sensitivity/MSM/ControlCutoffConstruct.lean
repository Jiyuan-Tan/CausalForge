/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.PO.ID.Partial.Sensitivity.MSM.ControlQuantileBalance
import Causalean.PO.ID.Partial.Sensitivity.MSM.CutoffConstruct

/-! # Marginal Sensitivity Model -- constructing the calibrating control cutoff

This file is the control-arm mirror of `CutoffConstruct`: it constructs a `σ(X)`-measurable
cutoff solving the control conditional-survival calibration equation and uses it to discharge the
membership hypothesis in the calibrated control sharp upper bound.

The file defines `controlSet`, `controlXYLaw`, `controlCondCDF`, and
`calibLevel0`; proves the constant and functional survival bridges
`controlSurv_const_eq` and `controlSurv_eq`; constructs a measurable cutoff in
`exists_calibrating_cutoff0`; and packages the unconditional sharp upper
endpoint as `msmUpperCalib0_eq_cutoff_unconditional`.
-/

namespace Causalean
namespace PO

open MeasureTheory ProbabilityTheory

namespace POBackdoorSystem

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
variable (S : POBackdoorSystem P γ)

/-- `σ(X)`-measurable sets are exactly preimages of measurable covariate sets. -/
private lemma exists_measurableSet_through_factualX0 {s : Set P.Ω}
    (hs : MeasurableSet[S.sigmaX] s) :
    ∃ B : Set γ, MeasurableSet B ∧ S.factualX ⁻¹' B = s := by
  rw [POBackdoorSystem.sigmaX] at hs
  exact MeasurableSpace.measurableSet_comap.mp hs

/-- The **control set** `{ω | D(ω) = 0}`. -/
def controlSet : Set P.Ω := S.factualD ⁻¹' {false}

/-- The **control push-forward law** of `(X, Y)`: the law of the factual covariate and
outcome on the sub-population of control units, `(μ restricted to {D=0}) ∘ (X, Y)⁻¹`. -/
noncomputable def controlXYLaw : Measure (γ × ℝ) :=
  (P.μ.restrict S.controlSet).map (fun ω => (S.factualX ω, S.factualY ω))

/-- The **control conditional CDF** of `Y` given `X`, evaluated along the factual covariate:
`F(t | X(ω)) = P(Y ≤ t | X = X(ω), D = 0)`. -/
noncomputable def controlCondCDF (ω : P.Ω) (t : ℝ) : ℝ :=
  condCDF S.controlXYLaw (S.factualX ω) t

private lemma measurableSet_controlSet : MeasurableSet S.controlSet := by
  unfold POBackdoorSystem.controlSet
  exact MeasurableSet.singleton false |>.preimage S.measurable_factualD

private lemma control_indicator_eq :
    S.dVar.indicator false = S.controlSet.indicator (fun _ : P.Ω => (1 : ℝ)) := by
  funext ω
  unfold POBackdoorSystem.controlSet POVar.indicator POVar.event POBackdoorSystem.factualD
  rfl

private lemma controlXYLaw_fst :
    S.controlXYLaw.fst = (P.μ.restrict S.controlSet).map S.factualX := by
  unfold POBackdoorSystem.controlXYLaw MeasureTheory.Measure.fst
  rw [MeasureTheory.Measure.map_map measurable_fst
    (S.measurable_factualX.prodMk S.measurable_factualY)]
  rfl

private lemma control_le_indicator_eq (t : ℝ) :
    (fun ω => S.dVar.indicator false ω * (if S.factualY ω ≤ t then (1 : ℝ) else 0))
      = fun ω => (S.controlSet ∩ {ω | S.factualY ω ≤ t}).indicator
          (fun _ : P.Ω => (1 : ℝ)) ω := by
  funext ω
  unfold POBackdoorSystem.controlSet POVar.indicator POVar.event POBackdoorSystem.factualD
  by_cases hD : S.dVar.factual ω = false <;> by_cases hY : S.factualY ω ≤ t <;>
    simp [hD, hY]

private lemma measurableSet_factualY_le (t : ℝ) : MeasurableSet {ω | S.factualY ω ≤ t} :=
  measurableSet_le S.measurable_factualY measurable_const

private lemma integrable_control_le_indicator (t : ℝ) :
    Integrable (fun ω => S.dVar.indicator false ω *
      (if S.factualY ω ≤ t then (1 : ℝ) else 0)) P.μ := by
  rw [control_le_indicator_eq]
  exact (integrable_const (α := P.Ω) (μ := P.μ) (c := (1 : ℝ))).indicator
    ((S.measurableSet_controlSet).inter (S.measurableSet_factualY_le t))

private lemma measurable_controlCondCDF_const (t : ℝ) :
    Measurable[S.sigmaX] (fun ω => S.controlCondCDF ω t) := by
  rw [POBackdoorSystem.sigmaX]
  unfold POBackdoorSystem.controlCondCDF
  exact (ProbabilityTheory.measurable_condCDF S.controlXYLaw t).comp
    (comap_measurable S.factualX)

private lemma stronglyMeasurable_controlCondCDF_const (t : ℝ) :
    StronglyMeasurable[S.sigmaX] (fun ω => S.controlCondCDF ω t) :=
  (S.measurable_controlCondCDF_const t).stronglyMeasurable

private lemma measurable_controlCondCDF_const_ambient (t : ℝ) :
    Measurable (fun ω => S.controlCondCDF ω t) :=
  (S.measurable_controlCondCDF_const t).mono S.sigmaX_le le_rfl

private lemma eventually_norm_controlCondCDF_le_one (t : ℝ) :
    ∀ᵐ ω ∂P.μ, ‖S.controlCondCDF ω t‖ ≤ 1 := by
  exact Filter.Eventually.of_forall fun ω => by
    unfold POBackdoorSystem.controlCondCDF
    rw [Real.norm_of_nonneg (ProbabilityTheory.condCDF_nonneg S.controlXYLaw (S.factualX ω) t)]
    exact ProbabilityTheory.condCDF_le_one S.controlXYLaw (S.factualX ω) t

private lemma integrable_propScore_mul_controlCondCDF (t : ℝ) :
    Integrable (fun ω => S.propScore false ω * S.controlCondCDF ω t) P.μ := by
  have he : Integrable (S.propScore false) P.μ := by
    unfold POBackdoorSystem.propScore
    exact MeasureTheory.integrable_condExp
  exact he.mul_bdd
    ((S.measurable_controlCondCDF_const_ambient t).aestronglyMeasurable)
    (S.eventually_norm_controlCondCDF_le_one t)

private lemma integrable_control_indicator_mul_controlCondCDF (t : ℝ) :
    Integrable (fun ω => S.dVar.indicator false ω * S.controlCondCDF ω t) P.μ := by
  exact (S.dVar.integrable_indicator false).mul_bdd
    ((S.measurable_controlCondCDF_const_ambient t).aestronglyMeasurable)
    (S.eventually_norm_controlCondCDF_le_one t)

private lemma setIntegral_propScore_mul_controlCondCDF_eq_le (t : ℝ)
    (s : Set P.Ω) (hs : MeasurableSet[S.sigmaX] s) :
    ∫ ω in s, S.propScore false ω * S.controlCondCDF ω t ∂P.μ =
      ∫ ω in s, S.dVar.indicator false ω *
        (if S.factualY ω ≤ t then (1 : ℝ) else 0) ∂P.μ := by
  classical
  obtain ⟨B, hB, rfl⟩ := S.exists_measurableSet_through_factualX0 hs
  let F : γ → ℝ := fun a => condCDF S.controlXYLaw a t
  have hpre_m : MeasurableSet[S.sigmaX] (S.factualX ⁻¹' B) := by
    rw [POBackdoorSystem.sigmaX]
    exact ⟨B, hB, rfl⟩
  have hpre : MeasurableSet (S.factualX ⁻¹' B) := hB.preimage S.measurable_factualX
  have hpull :
      P.μ[fun ω => S.dVar.indicator false ω * S.controlCondCDF ω t | S.sigmaX]
        =ᵐ[P.μ] (fun ω => S.propScore false ω * S.controlCondCDF ω t) := by
    have h := MeasureTheory.condExp_mul_of_stronglyMeasurable_right
      (m := S.sigmaX) (μ := P.μ)
      (S.stronglyMeasurable_controlCondCDF_const t)
      (S.integrable_control_indicator_mul_controlCondCDF t)
      (S.dVar.integrable_indicator false)
    exact h.trans (Filter.EventuallyEq.of_eq (by funext ω; rfl))
  have hleft_to_ZF :
      ∫ ω in S.factualX ⁻¹' B, S.propScore false ω * S.controlCondCDF ω t ∂P.μ =
        ∫ ω in S.factualX ⁻¹' B, S.dVar.indicator false ω *
          S.controlCondCDF ω t ∂P.μ := by
    calc
      ∫ ω in S.factualX ⁻¹' B, S.propScore false ω * S.controlCondCDF ω t ∂P.μ
          = ∫ ω in S.factualX ⁻¹' B,
              P.μ[fun ω => S.dVar.indicator false ω * S.controlCondCDF ω t | S.sigmaX] ω
                ∂P.μ := by
              refine MeasureTheory.setIntegral_congr_ae hpre ?_
              filter_upwards [hpull] with ω hω _hmem
              exact hω.symm
      _ = ∫ ω in S.factualX ⁻¹' B, S.dVar.indicator false ω *
            S.controlCondCDF ω t ∂P.μ := by
          exact MeasureTheory.setIntegral_condExp S.sigmaX_le
            (S.integrable_control_indicator_mul_controlCondCDF t) hpre_m
  have hZF_indicator :
      ∫ ω in S.factualX ⁻¹' B, S.dVar.indicator false ω *
          S.controlCondCDF ω t ∂P.μ =
        ∫ ω in (S.factualX ⁻¹' B) ∩ S.controlSet, S.controlCondCDF ω t ∂P.μ := by
    have hcongr : Set.EqOn
        (fun ω => S.dVar.indicator false ω * S.controlCondCDF ω t)
        (fun ω => S.controlSet.indicator (fun ω => S.controlCondCDF ω t) ω)
        (S.factualX ⁻¹' B) := by
      intro ω _hω
      rw [S.control_indicator_eq]
      by_cases hT : ω ∈ S.controlSet <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, hT]
    calc
      ∫ ω in S.factualX ⁻¹' B, S.dVar.indicator false ω *
          S.controlCondCDF ω t ∂P.μ
          = ∫ ω in S.factualX ⁻¹' B,
              S.controlSet.indicator (fun ω => S.controlCondCDF ω t) ω ∂P.μ :=
            MeasureTheory.setIntegral_congr_fun hpre hcongr
      _ = ∫ ω in (S.factualX ⁻¹' B) ∩ S.controlSet, S.controlCondCDF ω t ∂P.μ := by
            rw [MeasureTheory.setIntegral_indicator S.measurableSet_controlSet]
  have hmap :
      ∫ a in B, F a ∂S.controlXYLaw.fst =
        ∫ ω in (S.factualX ⁻¹' B) ∩ S.controlSet, S.controlCondCDF ω t ∂P.μ := by
    have hF_aesm : AEStronglyMeasurable F S.controlXYLaw.fst :=
      (ProbabilityTheory.measurable_condCDF S.controlXYLaw t).aestronglyMeasurable
    calc
      ∫ a in B, F a ∂S.controlXYLaw.fst
          = ∫ a in B, F a ∂((P.μ.restrict S.controlSet).map S.factualX) := by
              rw [S.controlXYLaw_fst]
      _ = ∫ ω in S.factualX ⁻¹' B, F (S.factualX ω) ∂(P.μ.restrict S.controlSet) := by
              exact MeasureTheory.setIntegral_map hB (by simpa [S.controlXYLaw_fst] using hF_aesm)
                S.measurable_factualX.aemeasurable
      _ = ∫ ω in (S.factualX ⁻¹' B) ∩ S.controlSet, F (S.factualX ω) ∂P.μ := by
              rw [MeasureTheory.Measure.restrict_restrict hpre]
      _ = ∫ ω in (S.factualX ⁻¹' B) ∩ S.controlSet, S.controlCondCDF ω t ∂P.μ := by
              rfl
  haveI : IsFiniteMeasure S.controlXYLaw := by
    unfold POBackdoorSystem.controlXYLaw
    infer_instance
  have hcondcdf :
      ∫ a in B, F a ∂S.controlXYLaw.fst = S.controlXYLaw.real (B ×ˢ Set.Iic t) := by
    simpa [F] using ProbabilityTheory.setIntegral_condCDF S.controlXYLaw t hB
  have hpush :
      S.controlXYLaw (B ×ˢ Set.Iic t) =
        P.μ ((S.factualX ⁻¹' B ∩ {ω | S.factualY ω ≤ t}) ∩ S.controlSet) := by
    unfold POBackdoorSystem.controlXYLaw
    have hpair : Measurable (fun ω : P.Ω => (S.factualX ω, S.factualY ω)) :=
      S.measurable_factualX.prodMk S.measurable_factualY
    have hprod : MeasurableSet (B ×ˢ Set.Iic t : Set (γ × ℝ)) :=
      hB.prod measurableSet_Iic
    rw [MeasureTheory.Measure.map_apply hpair hprod]
    rw [MeasureTheory.Measure.restrict_apply (hprod.preimage hpair)]
    apply congrArg P.μ
    ext ω
    simp [Set.mem_prod, Set.mem_Iic, and_assoc]
  have hleft_measure :
      ∫ ω in S.factualX ⁻¹' B, S.propScore false ω * S.controlCondCDF ω t ∂P.μ =
        P.μ.real ((S.factualX ⁻¹' B ∩ {ω | S.factualY ω ≤ t}) ∩ S.controlSet) := by
    rw [hleft_to_ZF, hZF_indicator, ← hmap, hcondcdf]
    rw [MeasureTheory.measureReal_def, hpush, MeasureTheory.measureReal_def]
  have hright_measure :
      ∫ ω in S.factualX ⁻¹' B,
        S.dVar.indicator false ω * (if S.factualY ω ≤ t then (1 : ℝ) else 0) ∂P.μ =
        P.μ.real ((S.factualX ⁻¹' B ∩ {ω | S.factualY ω ≤ t}) ∩ S.controlSet) := by
    rw [S.control_le_indicator_eq t]
    rw [MeasureTheory.setIntegral_indicator
      ((S.measurableSet_controlSet).inter (S.measurableSet_factualY_le t))]
    rw [MeasureTheory.setIntegral_const]
    simp only [smul_eq_mul, mul_one]
    rw [MeasureTheory.measureReal_def]
    apply congrArg ENNReal.toReal
    congr 1
    ext ω
    simp [and_left_comm, and_comm]
  rw [hleft_measure, hright_measure]

private lemma controlLe_const_eq (t : ℝ) :
    P.μ[fun ω => S.dVar.indicator false ω *
      (if S.factualY ω ≤ t then (1 : ℝ) else 0) | S.sigmaX]
      =ᵐ[P.μ] fun ω => S.propScore false ω * S.controlCondCDF ω t := by
  classical
  set f : P.Ω → ℝ := fun ω => S.dVar.indicator false ω *
    (if S.factualY ω ≤ t then (1 : ℝ) else 0)
  set g : P.Ω → ℝ := fun ω => S.propScore false ω * S.controlCondCDF ω t
  have hf : Integrable f P.μ := by
    change Integrable (fun ω => S.dVar.indicator false ω *
      (if S.factualY ω ≤ t then (1 : ℝ) else 0)) P.μ
    exact S.integrable_control_le_indicator t
  have hg_int : ∀ (s : Set P.Ω), MeasurableSet[S.sigmaX] s → P.μ s < ⊤ →
      IntegrableOn g s P.μ := by
    intro s _hs _hfin
    change IntegrableOn (fun ω => S.propScore false ω * S.controlCondCDF ω t) s P.μ
    exact (S.integrable_propScore_mul_controlCondCDF t).integrableOn
  have hg_eq : ∀ (s : Set P.Ω), MeasurableSet[S.sigmaX] s → P.μ s < ⊤ →
      ∫ x in s, g x ∂P.μ = ∫ x in s, f x ∂P.μ := by
    intro s hs _hfin
    change (∫ x in s, S.propScore false x * S.controlCondCDF x t ∂P.μ) =
      ∫ x in s, S.dVar.indicator false x *
        (if S.factualY x ≤ t then (1 : ℝ) else 0) ∂P.μ
    exact S.setIntegral_propScore_mul_controlCondCDF_eq_le t s hs
  have hprop_smeas : StronglyMeasurable[S.sigmaX] (S.propScore false) := by
    unfold POBackdoorSystem.propScore
    exact MeasureTheory.stronglyMeasurable_condExp
  have hg_sm : StronglyMeasurable[S.sigmaX] g := by
    change StronglyMeasurable[S.sigmaX]
      (fun ω => S.propScore false ω * S.controlCondCDF ω t)
    exact hprop_smeas.mul (S.stronglyMeasurable_controlCondCDF_const t)
  have hle : S.sigmaX ≤ (inferInstance : MeasurableSpace P.Ω) := S.sigmaX_le
  have h := MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq
    hle hf hg_int hg_eq hg_sm.aestronglyMeasurable
  exact h.symm

/-- The **calibration quantile level** `τ(ω) = 1 − survTarget0(ω)/e(ω)`: the control-conditional-CDF
level whose quantile is the calibrating cutoff. -/
noncomputable def calibLevel0 (Λ : ℝ) (ω : P.Ω) : ℝ :=
  1 - S.survTarget0 Λ ω / S.propScore false ω

/-- **The survival bridge (constant cutoff).** The weighted conditional survival equals the control
conditional survival scaled by the propensity:
`E[(1-Z)·1{Y>t} | σ(X)] = e₀(X)·(1 − F₀(t | X))` a.e. The genuine
measure-theoretic content relates a conditional expectation under `μ` to the conditional CDF of the
control push-forward law. -/
theorem controlSurv_const_eq (t : ℝ) :
    P.μ[fun ω => S.dVar.indicator false ω * (if t < S.factualY ω then (1 : ℝ) else 0) | S.sigmaX]
      =ᵐ[P.μ] fun ω => S.propScore false ω * (1 - S.controlCondCDF ω t) := by
  classical
  have hpoint :
      (fun ω => S.dVar.indicator false ω * (if t < S.factualY ω then (1 : ℝ) else 0))
        =ᵐ[P.μ]
      (fun ω => S.dVar.indicator false ω -
        S.dVar.indicator false ω * (if S.factualY ω ≤ t then (1 : ℝ) else 0)) := by
    exact Filter.Eventually.of_forall fun ω => by
      by_cases hle : S.factualY ω ≤ t
      · have hnot : ¬ t < S.factualY ω := not_lt.mpr hle
        simp [hle, hnot]
      · have hlt : t < S.factualY ω := lt_of_not_ge hle
        simp [hle, hlt]
  refine (MeasureTheory.condExp_congr_ae (m := S.sigmaX) (μ := P.μ) hpoint).trans ?_
  have hsub := MeasureTheory.condExp_sub
    (μ := P.μ) (m := S.sigmaX)
    (f := S.dVar.indicator false)
    (g := fun ω => S.dVar.indicator false ω *
      (if S.factualY ω ≤ t then (1 : ℝ) else 0))
    (S.dVar.integrable_indicator false) (S.integrable_control_le_indicator t)
  have hle_bridge := S.controlLe_const_eq t
  filter_upwards [hsub, hle_bridge] with ω hsubω hleω
  change P.μ[S.dVar.indicator false - (fun ω => S.dVar.indicator false ω *
      (if S.factualY ω ≤ t then (1 : ℝ) else 0)) | S.sigmaX] ω =
    S.propScore false ω * (1 - S.controlCondCDF ω t)
  rw [hsubω]
  change S.propScore false ω -
      P.μ[fun ω => S.dVar.indicator false ω *
        (if S.factualY ω ≤ t then (1 : ℝ) else 0) | S.sigmaX] ω =
    S.propScore false ω * (1 - S.controlCondCDF ω t)
  rw [hleω]
  ring

private lemma setIntegral_condCDF_variable (ρ : Measure (γ × ℝ)) [IsFiniteMeasure ρ]
    {B : Set γ} (hB : MeasurableSet B) {q : γ → ℝ} (hq : Measurable q) :
    ∫ a in B, condCDF ρ a (q a) ∂ρ.fst =
      ρ.real {p : γ × ℝ | p.1 ∈ B ∧ p.2 ≤ q p.1} := by
  rw [← ENNReal.ofReal_eq_ofReal_iff]
  · rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal]
    · rw [setLIntegral_condCDF_variable ρ hB hq]
      exact (ENNReal.ofReal_toReal (measure_ne_top ρ _)).symm
    · exact (integrable_condCDF_variable ρ hq).integrableOn
    · exact ae_of_all _ fun a => ProbabilityTheory.condCDF_nonneg ρ a (q a)
  · exact MeasureTheory.setIntegral_nonneg hB fun a _ =>
      ProbabilityTheory.condCDF_nonneg ρ a (q a)
  · exact ENNReal.toReal_nonneg

private lemma control_le_indicator_variable_eq (c : P.Ω → ℝ) :
    (fun ω => S.dVar.indicator false ω * (if S.factualY ω ≤ c ω then (1 : ℝ) else 0))
      = fun ω => (S.controlSet ∩ {ω | S.factualY ω ≤ c ω}).indicator
          (fun _ : P.Ω => (1 : ℝ)) ω := by
  funext ω
  unfold POBackdoorSystem.controlSet POVar.indicator POVar.event POBackdoorSystem.factualD
  by_cases hD : S.dVar.factual ω = false <;> by_cases hY : S.factualY ω ≤ c ω <;>
    simp [hD, hY]

private lemma measurableSet_factualY_le_cutoff (c : P.Ω → ℝ) (hc : Measurable[S.sigmaX] c) :
    MeasurableSet {ω | S.factualY ω ≤ c ω} :=
  measurableSet_le S.measurable_factualY (hc.mono S.sigmaX_le le_rfl)

private lemma integrable_control_le_indicator_variable (c : P.Ω → ℝ)
    (hc : Measurable[S.sigmaX] c) :
    Integrable (fun ω => S.dVar.indicator false ω *
      (if S.factualY ω ≤ c ω then (1 : ℝ) else 0)) P.μ := by
  rw [control_le_indicator_variable_eq]
  exact (integrable_const (α := P.Ω) (μ := P.μ) (c := (1 : ℝ))).indicator
    ((S.measurableSet_controlSet).inter (S.measurableSet_factualY_le_cutoff c hc))

private lemma measurable_controlCondCDF_variable (c : P.Ω → ℝ)
    (hc : Measurable[S.sigmaX] c) :
    Measurable[S.sigmaX] (fun ω => S.controlCondCDF ω (c ω)) := by
  obtain ⟨q, hq, hc_eq⟩ := S.exists_factor_through_factualX hc
  haveI : IsFiniteMeasure S.controlXYLaw := by
    unfold POBackdoorSystem.controlXYLaw
    infer_instance
  rw [POBackdoorSystem.sigmaX, hc_eq]
  unfold POBackdoorSystem.controlCondCDF
  exact (measurable_condCDF_variable S.controlXYLaw hq).comp
    (comap_measurable S.factualX)

private lemma stronglyMeasurable_controlCondCDF_variable (c : P.Ω → ℝ)
    (hc : Measurable[S.sigmaX] c) :
    StronglyMeasurable[S.sigmaX] (fun ω => S.controlCondCDF ω (c ω)) :=
  (S.measurable_controlCondCDF_variable c hc).stronglyMeasurable

private lemma measurable_controlCondCDF_variable_ambient (c : P.Ω → ℝ)
    (hc : Measurable[S.sigmaX] c) :
    Measurable (fun ω => S.controlCondCDF ω (c ω)) :=
  (S.measurable_controlCondCDF_variable c hc).mono S.sigmaX_le le_rfl

private lemma eventually_norm_controlCondCDF_variable_le_one (c : P.Ω → ℝ) :
    ∀ᵐ ω ∂P.μ, ‖S.controlCondCDF ω (c ω)‖ ≤ 1 := by
  exact Filter.Eventually.of_forall fun ω => by
    unfold POBackdoorSystem.controlCondCDF
    rw [Real.norm_of_nonneg (ProbabilityTheory.condCDF_nonneg
      S.controlXYLaw (S.factualX ω) (c ω))]
    exact ProbabilityTheory.condCDF_le_one S.controlXYLaw (S.factualX ω) (c ω)

private lemma integrable_propScore_mul_controlCondCDF_variable (c : P.Ω → ℝ)
    (hc : Measurable[S.sigmaX] c) :
    Integrable (fun ω => S.propScore false ω * S.controlCondCDF ω (c ω)) P.μ := by
  have he : Integrable (S.propScore false) P.μ := by
    unfold POBackdoorSystem.propScore
    exact MeasureTheory.integrable_condExp
  exact he.mul_bdd
    ((S.measurable_controlCondCDF_variable_ambient c hc).aestronglyMeasurable)
    (S.eventually_norm_controlCondCDF_variable_le_one c)

private lemma integrable_control_indicator_mul_controlCondCDF_variable (c : P.Ω → ℝ)
    (hc : Measurable[S.sigmaX] c) :
    Integrable (fun ω => S.dVar.indicator false ω * S.controlCondCDF ω (c ω)) P.μ := by
  exact (S.dVar.integrable_indicator false).mul_bdd
    ((S.measurable_controlCondCDF_variable_ambient c hc).aestronglyMeasurable)
    (S.eventually_norm_controlCondCDF_variable_le_one c)

private lemma setIntegral_propScore_mul_controlCondCDF_eq_le_variable (c : P.Ω → ℝ)
    (hc : Measurable[S.sigmaX] c) (s : Set P.Ω) (hs : MeasurableSet[S.sigmaX] s) :
    ∫ ω in s, S.propScore false ω * S.controlCondCDF ω (c ω) ∂P.μ =
      ∫ ω in s, S.dVar.indicator false ω *
        (if S.factualY ω ≤ c ω then (1 : ℝ) else 0) ∂P.μ := by
  classical
  obtain ⟨B, hB, rfl⟩ := S.exists_measurableSet_through_factualX0 hs
  obtain ⟨q, hq, hc_eq⟩ := S.exists_factor_through_factualX hc
  rw [hc_eq]
  let F : γ → ℝ := fun a => condCDF S.controlXYLaw a (q a)
  haveI : IsFiniteMeasure S.controlXYLaw := by
    unfold POBackdoorSystem.controlXYLaw
    infer_instance
  have hcq : Measurable[S.sigmaX] (fun ω => q (S.factualX ω)) := by
    rw [POBackdoorSystem.sigmaX]
    exact hq.comp (comap_measurable S.factualX)
  have hpre_m : MeasurableSet[S.sigmaX] (S.factualX ⁻¹' B) := by
    rw [POBackdoorSystem.sigmaX]
    exact ⟨B, hB, rfl⟩
  have hpre : MeasurableSet (S.factualX ⁻¹' B) := hB.preimage S.measurable_factualX
  have hpull :
      P.μ[fun ω => S.dVar.indicator false ω * S.controlCondCDF ω (q (S.factualX ω))
          | S.sigmaX]
        =ᵐ[P.μ] (fun ω => S.propScore false ω *
          S.controlCondCDF ω (q (S.factualX ω))) := by
    have h := MeasureTheory.condExp_mul_of_stronglyMeasurable_right
      (m := S.sigmaX) (μ := P.μ)
      (S.stronglyMeasurable_controlCondCDF_variable (fun ω => q (S.factualX ω)) hcq)
      (S.integrable_control_indicator_mul_controlCondCDF_variable
        (fun ω => q (S.factualX ω)) hcq)
      (S.dVar.integrable_indicator false)
    exact h.trans (Filter.EventuallyEq.of_eq (by funext ω; rfl))
  have hleft_to_ZF :
      ∫ ω in S.factualX ⁻¹' B, S.propScore false ω *
          S.controlCondCDF ω (q (S.factualX ω)) ∂P.μ =
        ∫ ω in S.factualX ⁻¹' B, S.dVar.indicator false ω *
          S.controlCondCDF ω (q (S.factualX ω)) ∂P.μ := by
    calc
      ∫ ω in S.factualX ⁻¹' B, S.propScore false ω *
          S.controlCondCDF ω (q (S.factualX ω)) ∂P.μ
          = ∫ ω in S.factualX ⁻¹' B,
              P.μ[fun ω => S.dVar.indicator false ω *
                S.controlCondCDF ω (q (S.factualX ω)) | S.sigmaX] ω ∂P.μ := by
              refine MeasureTheory.setIntegral_congr_ae hpre ?_
              filter_upwards [hpull] with ω hω _hmem
              exact hω.symm
      _ = ∫ ω in S.factualX ⁻¹' B, S.dVar.indicator false ω *
            S.controlCondCDF ω (q (S.factualX ω)) ∂P.μ := by
          exact MeasureTheory.setIntegral_condExp S.sigmaX_le
            (S.integrable_control_indicator_mul_controlCondCDF_variable
              (fun ω => q (S.factualX ω)) hcq) hpre_m
  have hZF_indicator :
      ∫ ω in S.factualX ⁻¹' B, S.dVar.indicator false ω *
          S.controlCondCDF ω (q (S.factualX ω)) ∂P.μ =
        ∫ ω in (S.factualX ⁻¹' B) ∩ S.controlSet,
          S.controlCondCDF ω (q (S.factualX ω)) ∂P.μ := by
    have hcongr : Set.EqOn
        (fun ω => S.dVar.indicator false ω * S.controlCondCDF ω (q (S.factualX ω)))
        (fun ω => S.controlSet.indicator
          (fun ω => S.controlCondCDF ω (q (S.factualX ω))) ω)
        (S.factualX ⁻¹' B) := by
      intro ω _hω
      rw [S.control_indicator_eq]
      by_cases hT : ω ∈ S.controlSet <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, hT]
    calc
      ∫ ω in S.factualX ⁻¹' B, S.dVar.indicator false ω *
          S.controlCondCDF ω (q (S.factualX ω)) ∂P.μ
          = ∫ ω in S.factualX ⁻¹' B,
              S.controlSet.indicator
                (fun ω => S.controlCondCDF ω (q (S.factualX ω))) ω ∂P.μ :=
            MeasureTheory.setIntegral_congr_fun hpre hcongr
      _ = ∫ ω in (S.factualX ⁻¹' B) ∩ S.controlSet,
            S.controlCondCDF ω (q (S.factualX ω)) ∂P.μ := by
            rw [MeasureTheory.setIntegral_indicator S.measurableSet_controlSet]
  have hmap :
      ∫ a in B, F a ∂S.controlXYLaw.fst =
        ∫ ω in (S.factualX ⁻¹' B) ∩ S.controlSet,
          S.controlCondCDF ω (q (S.factualX ω)) ∂P.μ := by
    have hF_aesm : AEStronglyMeasurable F S.controlXYLaw.fst :=
      (measurable_condCDF_variable S.controlXYLaw hq).aestronglyMeasurable
    calc
      ∫ a in B, F a ∂S.controlXYLaw.fst
          = ∫ a in B, F a ∂((P.μ.restrict S.controlSet).map S.factualX) := by
              rw [S.controlXYLaw_fst]
      _ = ∫ ω in S.factualX ⁻¹' B, F (S.factualX ω)
            ∂(P.μ.restrict S.controlSet) := by
              exact MeasureTheory.setIntegral_map hB
                (by simpa [S.controlXYLaw_fst] using hF_aesm)
                S.measurable_factualX.aemeasurable
      _ = ∫ ω in (S.factualX ⁻¹' B) ∩ S.controlSet, F (S.factualX ω) ∂P.μ := by
              rw [MeasureTheory.Measure.restrict_restrict hpre]
      _ = ∫ ω in (S.factualX ⁻¹' B) ∩ S.controlSet,
            S.controlCondCDF ω (q (S.factualX ω)) ∂P.μ := by
              rfl
  have hcondcdf :
      ∫ a in B, F a ∂S.controlXYLaw.fst =
        S.controlXYLaw.real {p : γ × ℝ | p.1 ∈ B ∧ p.2 ≤ q p.1} := by
    simpa [F] using setIntegral_condCDF_variable S.controlXYLaw hB hq
  have hpush :
      S.controlXYLaw {p : γ × ℝ | p.1 ∈ B ∧ p.2 ≤ q p.1} =
        P.μ ((S.factualX ⁻¹' B ∩ {ω | S.factualY ω ≤ q (S.factualX ω)}) ∩
          S.controlSet) := by
    unfold POBackdoorSystem.controlXYLaw
    have hpair : Measurable (fun ω : P.Ω => (S.factualX ω, S.factualY ω)) :=
      S.measurable_factualX.prodMk S.measurable_factualY
    have hV : MeasurableSet {p : γ × ℝ | p.1 ∈ B ∧ p.2 ≤ q p.1} :=
      (hB.preimage measurable_fst).inter
        (measurableSet_le measurable_snd (hq.comp measurable_fst))
    rw [MeasureTheory.Measure.map_apply hpair hV]
    rw [MeasureTheory.Measure.restrict_apply (hV.preimage hpair)]
    apply congrArg P.μ
    ext ω
    simp [and_assoc]
  have hleft_measure :
      ∫ ω in S.factualX ⁻¹' B, S.propScore false ω *
          S.controlCondCDF ω (q (S.factualX ω)) ∂P.μ =
        P.μ.real ((S.factualX ⁻¹' B ∩ {ω | S.factualY ω ≤ q (S.factualX ω)}) ∩
          S.controlSet) := by
    rw [hleft_to_ZF, hZF_indicator, ← hmap, hcondcdf]
    rw [MeasureTheory.measureReal_def, hpush, MeasureTheory.measureReal_def]
  have hright_measure :
      ∫ ω in S.factualX ⁻¹' B,
        S.dVar.indicator false ω *
          (if S.factualY ω ≤ q (S.factualX ω) then (1 : ℝ) else 0) ∂P.μ =
        P.μ.real ((S.factualX ⁻¹' B ∩ {ω | S.factualY ω ≤ q (S.factualX ω)}) ∩
          S.controlSet) := by
    rw [S.control_le_indicator_variable_eq (fun ω => q (S.factualX ω))]
    rw [MeasureTheory.setIntegral_indicator
      ((S.measurableSet_controlSet).inter
        (S.measurableSet_factualY_le_cutoff (fun ω => q (S.factualX ω)) hcq))]
    rw [MeasureTheory.setIntegral_const]
    simp only [smul_eq_mul, mul_one]
    rw [MeasureTheory.measureReal_def]
    apply congrArg ENNReal.toReal
    congr 1
    ext ω
    simp [and_left_comm, and_comm]
  rw [hleft_measure, hright_measure]

private lemma controlLe_eq (c : P.Ω → ℝ) (hc : Measurable[S.sigmaX] c) :
    P.μ[fun ω => S.dVar.indicator false ω *
      (if S.factualY ω ≤ c ω then (1 : ℝ) else 0) | S.sigmaX]
      =ᵐ[P.μ] fun ω => S.propScore false ω * S.controlCondCDF ω (c ω) := by
  classical
  set f : P.Ω → ℝ := fun ω => S.dVar.indicator false ω *
    (if S.factualY ω ≤ c ω then (1 : ℝ) else 0)
  set g : P.Ω → ℝ := fun ω => S.propScore false ω * S.controlCondCDF ω (c ω)
  have hf : Integrable f P.μ := by
    change Integrable (fun ω => S.dVar.indicator false ω *
      (if S.factualY ω ≤ c ω then (1 : ℝ) else 0)) P.μ
    exact S.integrable_control_le_indicator_variable c hc
  have hg_int : ∀ (s : Set P.Ω), MeasurableSet[S.sigmaX] s → P.μ s < ⊤ →
      IntegrableOn g s P.μ := by
    intro s _hs _hfin
    change IntegrableOn (fun ω => S.propScore false ω * S.controlCondCDF ω (c ω)) s P.μ
    exact (S.integrable_propScore_mul_controlCondCDF_variable c hc).integrableOn
  have hg_eq : ∀ (s : Set P.Ω), MeasurableSet[S.sigmaX] s → P.μ s < ⊤ →
      ∫ x in s, g x ∂P.μ = ∫ x in s, f x ∂P.μ := by
    intro s hs _hfin
    change (∫ x in s, S.propScore false x * S.controlCondCDF x (c x) ∂P.μ) =
      ∫ x in s, S.dVar.indicator false x *
        (if S.factualY x ≤ c x then (1 : ℝ) else 0) ∂P.μ
    exact S.setIntegral_propScore_mul_controlCondCDF_eq_le_variable c hc s hs
  have hprop_smeas : StronglyMeasurable[S.sigmaX] (S.propScore false) := by
    unfold POBackdoorSystem.propScore
    exact MeasureTheory.stronglyMeasurable_condExp
  have hg_sm : StronglyMeasurable[S.sigmaX] g := by
    change StronglyMeasurable[S.sigmaX]
      (fun ω => S.propScore false ω * S.controlCondCDF ω (c ω))
    exact hprop_smeas.mul (S.stronglyMeasurable_controlCondCDF_variable c hc)
  have hle : S.sigmaX ≤ (inferInstance : MeasurableSpace P.Ω) := S.sigmaX_le
  have h := MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq
    hle hf hg_int hg_eq hg_sm.aestronglyMeasurable
  exact h.symm

/-- **The survival bridge (functional cutoff).** The version of `controlSurv_const_eq` evaluated
at a `σ(X)`-measurable cutoff `c`:
`E[(1-Z)·1{Y>c(X)} | σ(X)] = e₀(X)·(1 − F₀(c(X) | X))` a.e. Since `c` is
`σ(X)`-measurable it is frozen inside the conditional expectation, reducing to the
constant-cutoff bridge fibrewise. This is the form consumed by `exists_calibrating_cutoff0`. -/
theorem controlSurv_eq (c : P.Ω → ℝ) (hc : Measurable[S.sigmaX] c) :
    S.controlSurv c =ᵐ[P.μ] fun ω => S.propScore false ω * (1 - S.controlCondCDF ω (c ω)) := by
  classical
  unfold POBackdoorSystem.controlSurv
  have hpoint :
      (fun ω => S.dVar.indicator false ω * (if c ω < S.factualY ω then (1 : ℝ) else 0))
        =ᵐ[P.μ]
      (fun ω => S.dVar.indicator false ω -
        S.dVar.indicator false ω * (if S.factualY ω ≤ c ω then (1 : ℝ) else 0)) := by
    exact Filter.Eventually.of_forall fun ω => by
      by_cases hle : S.factualY ω ≤ c ω
      · have hnot : ¬ c ω < S.factualY ω := not_lt.mpr hle
        simp [hle, hnot]
      · have hlt : c ω < S.factualY ω := lt_of_not_ge hle
        simp [hle, hlt]
  refine (MeasureTheory.condExp_congr_ae (m := S.sigmaX) (μ := P.μ) hpoint).trans ?_
  have hsub := MeasureTheory.condExp_sub
    (μ := P.μ) (m := S.sigmaX)
    (f := S.dVar.indicator false)
    (g := fun ω => S.dVar.indicator false ω *
      (if S.factualY ω ≤ c ω then (1 : ℝ) else 0))
    (S.dVar.integrable_indicator false) (S.integrable_control_le_indicator_variable c hc)
  have hle_bridge := S.controlLe_eq c hc
  filter_upwards [hsub, hle_bridge] with ω hsubω hleω
  change P.μ[S.dVar.indicator false - (fun ω => S.dVar.indicator false ω *
      (if S.factualY ω ≤ c ω then (1 : ℝ) else 0)) | S.sigmaX] ω =
    S.propScore false ω * (1 - S.controlCondCDF ω (c ω))
  rw [hsubω]
  change S.propScore false ω -
      P.μ[fun ω => S.dVar.indicator false ω *
        (if S.factualY ω ≤ c ω then (1 : ℝ) else 0) | S.sigmaX] ω =
    S.propScore false ω * (1 - S.controlCondCDF ω (c ω))
  rw [hleω]
  ring

/-- Existence of a calibrating cutoff. Under overlap, `1 < Λ`, an atomless control
conditional outcome law (`condCDF` of the control push-forward continuous), and a strictly-interior
calibration level, there is a `σ(X)`-measurable cutoff `c` solving the survival equation
`controlSurv c =ᵐ survTarget0 Λ`. The cutoff is the conditional quantile `Q_{calibLevel0}(X)`. -/
theorem exists_calibrating_cutoff0 (Λ : ℝ) (_hΛ : 1 < Λ)
    (hoverlap : ∀ᵐ ω ∂P.μ, 0 < S.propScore false ω ∧ S.propScore false ω < 1)
    (hatomless : ∀ a : γ, Continuous (condCDF S.controlXYLaw a))
    (hlevel : ∀ᵐ ω ∂P.μ, 0 < S.calibLevel0 Λ ω ∧ S.calibLevel0 Λ ω < 1) :
    ∃ c : P.Ω → ℝ, Measurable[S.sigmaX] c ∧ S.controlSurv c =ᵐ[P.μ] S.survTarget0 Λ := by
  classical
  have hprop_meas : Measurable[S.sigmaX] (S.propScore false) := by
    unfold POBackdoorSystem.propScore
    exact stronglyMeasurable_condExp.measurable
  have hwMin0_meas : Measurable[S.sigmaX] (S.wMin0 Λ) := by
    unfold POBackdoorSystem.wMin0
    exact measurable_const.add
      ((measurable_const.sub hprop_meas).div (measurable_const.mul hprop_meas))
  have hwMax0_meas : Measurable[S.sigmaX] (S.wMax0 Λ) := by
    unfold POBackdoorSystem.wMax0
    exact measurable_const.add
      ((measurable_const.mul (measurable_const.sub hprop_meas)).div hprop_meas)
  have hsurvTarget0_meas : Measurable[S.sigmaX] (S.survTarget0 Λ) := by
    unfold POBackdoorSystem.survTarget0
    exact (measurable_const.sub (hwMin0_meas.mul hprop_meas)).div
      (hwMax0_meas.sub hwMin0_meas)
  have hlevel_meas : Measurable[S.sigmaX] (S.calibLevel0 Λ) := by
    unfold POBackdoorSystem.calibLevel0
    exact measurable_const.sub (hsurvTarget0_meas.div hprop_meas)
  obtain ⟨g, hg, hg_eq⟩ := S.exists_factor_through_factualX hlevel_meas
  let τ : γ → ℝ := fun a => if 0 < g a ∧ g a < 1 then g a else (1 / 2 : ℝ)
  have hτ_meas : Measurable τ := by
    dsimp [τ]
    refine Measurable.ite ?_ hg measurable_const
    exact (measurableSet_lt measurable_const hg).inter (measurableSet_lt hg measurable_const)
  have hτ0 : ∀ a, 0 < τ a := by
    intro a
    dsimp [τ]
    by_cases ha : 0 < g a ∧ g a < 1
    · simp [ha]
    · simp [ha]
  have hτ1 : ∀ a, τ a < 1 := by
    intro a
    dsimp [τ]
    by_cases ha : 0 < g a ∧ g a < 1
    · simp [ha]
    · simp only [ha, ↓reduceIte]
      norm_num
  haveI : IsFiniteMeasure S.controlXYLaw := by
    unfold POBackdoorSystem.controlXYLaw
    infer_instance
  obtain ⟨hq_meas, hq_attain⟩ :=
    Causalean.Mathlib.measurable_condQuantile_and_attains
      S.controlXYLaw τ hτ_meas hτ0 hτ1 hatomless
  let c : P.Ω → ℝ := fun ω =>
    Causalean.Mathlib.condQuantile S.controlXYLaw τ (S.factualX ω)
  have hc_meas : Measurable[S.sigmaX] c := by
    rw [POBackdoorSystem.sigmaX]
    exact hq_meas.comp (comap_measurable S.factualX)
  refine ⟨c, hc_meas, ?_⟩
  have hτ_eq_level : ∀ᵐ ω ∂P.μ, τ (S.factualX ω) = S.calibLevel0 Λ ω := by
    filter_upwards [hlevel] with ω hω
    have hgx : g (S.factualX ω) = S.calibLevel0 Λ ω := by
      exact (congrFun hg_eq ω).symm
    dsimp [τ]
    rw [hgx]
    simp [hω]
  have hsurv := S.controlSurv_eq c hc_meas
  filter_upwards [hsurv, hτ_eq_level, hoverlap] with ω hsurvω hτω hoverlapω
  rw [hsurvω]
  have hcdf :
      S.controlCondCDF ω (c ω) = τ (S.factualX ω) := by
    unfold POBackdoorSystem.controlCondCDF c
    exact hq_attain (S.factualX ω)
  rw [hcdf, hτω]
  unfold POBackdoorSystem.calibLevel0
  have hpos : S.propScore false ω ≠ 0 := ne_of_gt hoverlapω.1
  field_simp [hpos]
  ring

/-- The sharp upper bound, unconditionally. Combining the constructed
calibrating cutoff with `msmUpperCalib0_eq_cutoff`, the Dorn–Guo sharp upper bound has the
quantile-balancing closed form `msmUpperCalib0 Λ = candMean0 (cutoffProp0 Λ c)` for the
conditional-quantile cutoff `c` -- with no `hcut_mem` hypothesis, the membership now discharged by
`exists_calibrating_cutoff0`. Regularity: overlap, `1 < Λ`, atomless control outcome law, interior
level, and the envelope-integrability of the candidate means; `c` is the constructed cutoff. -/
theorem msmUpperCalib0_eq_cutoff_unconditional (Λ : ℝ) (hΛ : 1 < Λ)
    (hoverlap : ∀ᵐ ω ∂P.μ, 0 < S.propScore false ω ∧ S.propScore false ω < 1)
    (hatomless : ∀ a : γ, Continuous (condCDF S.controlXYLaw a))
    (hlevel : ∀ᵐ ω ∂P.μ, 0 < S.calibLevel0 Λ ω ∧ S.calibLevel0 Λ ω < 1)
    (_hbdd : BddAbove (S.candMean0 '' S.MSMSetCalib0 Λ))
    (hmeas : ∀ etilde ∈ S.MSMSetCalib0 Λ, AEMeasurable etilde P.μ)
    (hreg : ∀ c : P.Ω → ℝ, Measurable[S.sigmaX] c →
      Integrable c P.μ ∧
      Integrable (fun ω => S.dVar.indicator false ω / S.cutoffProp0 Λ c ω) P.μ ∧
      Integrable (fun ω =>
        S.dVar.indicator false ω * (if c ω < S.factualY ω then (1 : ℝ) else 0)) P.μ ∧
      Integrable (fun ω => S.dVar.indicator false ω * S.wMin0 Λ ω) P.μ ∧
      Integrable (fun ω => (S.wMax0 Λ ω - S.wMin0 Λ ω) *
        (S.dVar.indicator false ω * (if c ω < S.factualY ω then (1 : ℝ) else 0))) P.μ ∧
      Integrable (fun ω => S.dVar.indicator false ω * |S.factualY ω| * S.wMax0 Λ ω) P.μ ∧
      Integrable (fun ω => S.dVar.indicator false ω * S.wMax0 Λ ω) P.μ ∧
      Integrable (fun ω => |c ω| * S.dVar.indicator false ω * S.wMax0 Λ ω) P.μ) :
    ∃ c : P.Ω → ℝ, Measurable[S.sigmaX] c ∧
      S.cutoffProp0 Λ c ∈ S.MSMSetCalib0 Λ ∧
      S.msmUpperCalib0 Λ = S.candMean0 (S.cutoffProp0 Λ c) := by
  obtain ⟨c, hc_meas, hsurv⟩ :=
    S.exists_calibrating_cutoff0 Λ hΛ hoverlap hatomless hlevel
  obtain ⟨hc_int, hint, hint1, hmin_int, hdiff_int,
    henv, hweight_env, hc_env⟩ := hreg c hc_meas
  have hcut_mem : S.cutoffProp0 Λ c ∈ S.MSMSetCalib0 Λ :=
    S.cutoffProp0_mem_MSMSetCalib0_of_survival Λ hΛ hoverlap c hc_meas
      hint hint1 hmin_int hdiff_int hsurv
  have heq : S.msmUpperCalib0 Λ = S.candMean0 (S.cutoffProp0 Λ c) :=
    S.msmUpperCalib0_eq_cutoff Λ (le_of_lt hΛ) hoverlap c hc_meas
      hc_int hcut_mem henv hweight_env hc_env hmeas
  exact ⟨c, hc_meas, hcut_mem, heq⟩

end POBackdoorSystem

end PO
end Causalean
