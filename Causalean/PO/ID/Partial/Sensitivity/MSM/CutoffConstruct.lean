/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Marginal Sensitivity Model — constructing the calibrating cutoff

`QuantileBalance.msmUpperCalib_eq_cutoff` and `CutoffSelection.cutoffProp_mem_MSMSetCalib_of_survival`
reduce the Dorn–Guo sharp upper bound to one construction: a `σ(X)`-measurable cutoff `c` solving the
conditional-survival equation `treatedSurv c =ᵐ survTarget Λ`. This file performs that construction and
discharges the last hypothesis, yielding the **unconditional** sharp closed form.

The cutoff is the conditional quantile `Q_{τ}(X)` of `Y` among the treated, where the level
`τ(X) = 1 − survTarget(X)/e(X)` (`calibLevel`) is set by the sensitivity budget. The construction uses:
* the **treated push-forward law** `treatedXYLaw = ((μ↾{D=1}) ∘ (X,Y))` and Mathlib's `condCDF` of it —
  the conditional CDF of `Y` given `X` among the treated;
* the **bridge** `treatedSurv_const_eq`: `E[Z·1{Y>t}|σ(X)] = e(X)·(1 − F(t|X))` (relating the weighted
  conditional survival to the treated conditional CDF);
* the **measurable conditional quantile** `Causalean.Mathlib.measurable_condQuantile_and_attains`
  (atomless conditional law ⇒ a measurable cutoff attaining any interior level), at level `τ(X)`.

**Atomless / continuous-outcome hypothesis.** Exact attainment needs the treated conditional law of `Y`
to be atomless (`condCDF` continuous) — the Dorn–Guo continuous-outcome caveat, carried as a hypothesis.

Scope: the upper bound (treated). The lower bound and the ATE specialization mirror this. -/

import Causalean.PO.ID.Partial.Sensitivity.MSM.CutoffSelection
import Causalean.PO.ID.Partial.Sensitivity.MSM.QuantileBalance
import Causalean.Mathlib.Probability.MeasurableCondQuantile

/-! # Construction of treated-arm calibrated cutoff weights

This file constructs the treated-arm quantile cutoff used in the sharp MSM
upper bound. Measurable conditional quantiles provide a `σ(X)`-measurable
cutoff whose induced boundary weight is calibrated and therefore attains the
closed-form upper endpoint.

It defines `treatedSet`, `treatedXYLaw`, `treatedCondCDF`, and `calibLevel`;
proves the constant and functional survival bridges `treatedSurv_const_eq` and
`treatedSurv_eq`; exposes `exists_factor_through_factualX`; constructs a cutoff
in `exists_calibrating_cutoff`; and packages the unconditional upper endpoint
as `msmUpperCalib_eq_cutoff_unconditional`.
-/

namespace Causalean
namespace PO

open MeasureTheory ProbabilityTheory

namespace POBackdoorSystem

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
variable (S : POBackdoorSystem P γ)

/-- `σ(X)`-measurable sets are exactly preimages of measurable covariate sets. -/
private lemma exists_measurableSet_through_factualX {s : Set P.Ω}
    (hs : MeasurableSet[S.sigmaX] s) :
    ∃ B : Set γ, MeasurableSet B ∧ S.factualX ⁻¹' B = s := by
  rw [POBackdoorSystem.sigmaX] at hs
  exact MeasurableSpace.measurableSet_comap.mp hs

/-- The **treated set** `{ω | D(ω) = 1}`. -/
def treatedSet : Set P.Ω := S.factualD ⁻¹' {true}

/-- The **treated push-forward law** of `(X, Y)`: the law of the factual covariate and
outcome on the sub-population of treated units, `(μ restricted to {D=1}) ∘ (X, Y)⁻¹`. -/
noncomputable def treatedXYLaw : Measure (γ × ℝ) :=
  (P.μ.restrict S.treatedSet).map (fun ω => (S.factualX ω, S.factualY ω))

/-- The **treated conditional CDF** of `Y` given `X`, evaluated along the factual covariate:
`F(t | X(ω)) = P(Y ≤ t | X = X(ω), D = 1)`. -/
noncomputable def treatedCondCDF (ω : P.Ω) (t : ℝ) : ℝ :=
  condCDF S.treatedXYLaw (S.factualX ω) t

private lemma measurableSet_treatedSet : MeasurableSet S.treatedSet := by
  unfold POBackdoorSystem.treatedSet
  exact MeasurableSet.singleton true |>.preimage S.measurable_factualD

private lemma treated_indicator_eq :
    S.dVar.indicator true = S.treatedSet.indicator (fun _ : P.Ω => (1 : ℝ)) := by
  funext ω
  unfold POBackdoorSystem.treatedSet POVar.indicator POVar.event POBackdoorSystem.factualD
  rfl

private lemma treatedXYLaw_fst :
    S.treatedXYLaw.fst = (P.μ.restrict S.treatedSet).map S.factualX := by
  unfold POBackdoorSystem.treatedXYLaw MeasureTheory.Measure.fst
  rw [MeasureTheory.Measure.map_map measurable_fst
    (S.measurable_factualX.prodMk S.measurable_factualY)]
  rfl

private lemma treated_le_indicator_eq (t : ℝ) :
    (fun ω => S.dVar.indicator true ω * (if S.factualY ω ≤ t then (1 : ℝ) else 0))
      = fun ω => (S.treatedSet ∩ {ω | S.factualY ω ≤ t}).indicator
          (fun _ : P.Ω => (1 : ℝ)) ω := by
  funext ω
  unfold POBackdoorSystem.treatedSet POVar.indicator POVar.event POBackdoorSystem.factualD
  by_cases hD : S.dVar.factual ω = true <;> by_cases hY : S.factualY ω ≤ t <;>
    simp [hD, hY]

private lemma measurableSet_factualY_le (t : ℝ) : MeasurableSet {ω | S.factualY ω ≤ t} :=
  measurableSet_le S.measurable_factualY measurable_const

private lemma integrable_treated_le_indicator (t : ℝ) :
    Integrable (fun ω => S.dVar.indicator true ω *
      (if S.factualY ω ≤ t then (1 : ℝ) else 0)) P.μ := by
  rw [treated_le_indicator_eq]
  exact (integrable_const (α := P.Ω) (μ := P.μ) (c := (1 : ℝ))).indicator
    ((S.measurableSet_treatedSet).inter (S.measurableSet_factualY_le t))

private lemma measurable_treatedCondCDF_const (t : ℝ) :
    Measurable[S.sigmaX] (fun ω => S.treatedCondCDF ω t) := by
  rw [POBackdoorSystem.sigmaX]
  unfold POBackdoorSystem.treatedCondCDF
  exact (ProbabilityTheory.measurable_condCDF S.treatedXYLaw t).comp
    (comap_measurable S.factualX)

private lemma stronglyMeasurable_treatedCondCDF_const (t : ℝ) :
    StronglyMeasurable[S.sigmaX] (fun ω => S.treatedCondCDF ω t) :=
  (S.measurable_treatedCondCDF_const t).stronglyMeasurable

private lemma measurable_treatedCondCDF_const_ambient (t : ℝ) :
    Measurable (fun ω => S.treatedCondCDF ω t) :=
  (S.measurable_treatedCondCDF_const t).mono S.sigmaX_le le_rfl

private lemma eventually_norm_treatedCondCDF_le_one (t : ℝ) :
    ∀ᵐ ω ∂P.μ, ‖S.treatedCondCDF ω t‖ ≤ 1 := by
  exact Filter.Eventually.of_forall fun ω => by
    unfold POBackdoorSystem.treatedCondCDF
    rw [Real.norm_of_nonneg (ProbabilityTheory.condCDF_nonneg S.treatedXYLaw (S.factualX ω) t)]
    exact ProbabilityTheory.condCDF_le_one S.treatedXYLaw (S.factualX ω) t

private lemma integrable_propScore_mul_treatedCondCDF (t : ℝ) :
    Integrable (fun ω => S.propScore true ω * S.treatedCondCDF ω t) P.μ := by
  have he : Integrable (S.propScore true) P.μ := by
    unfold POBackdoorSystem.propScore
    exact MeasureTheory.integrable_condExp
  exact he.mul_bdd
    ((S.measurable_treatedCondCDF_const_ambient t).aestronglyMeasurable)
    (S.eventually_norm_treatedCondCDF_le_one t)

private lemma integrable_treated_indicator_mul_treatedCondCDF (t : ℝ) :
    Integrable (fun ω => S.dVar.indicator true ω * S.treatedCondCDF ω t) P.μ := by
  exact (S.dVar.integrable_indicator true).mul_bdd
    ((S.measurable_treatedCondCDF_const_ambient t).aestronglyMeasurable)
    (S.eventually_norm_treatedCondCDF_le_one t)

private lemma setIntegral_propScore_mul_treatedCondCDF_eq_le (t : ℝ)
    (s : Set P.Ω) (hs : MeasurableSet[S.sigmaX] s) :
    ∫ ω in s, S.propScore true ω * S.treatedCondCDF ω t ∂P.μ =
      ∫ ω in s, S.dVar.indicator true ω *
        (if S.factualY ω ≤ t then (1 : ℝ) else 0) ∂P.μ := by
  classical
  obtain ⟨B, hB, rfl⟩ := S.exists_measurableSet_through_factualX hs
  let F : γ → ℝ := fun a => condCDF S.treatedXYLaw a t
  have hpre_m : MeasurableSet[S.sigmaX] (S.factualX ⁻¹' B) := by
    rw [POBackdoorSystem.sigmaX]
    exact ⟨B, hB, rfl⟩
  have hpre : MeasurableSet (S.factualX ⁻¹' B) := hB.preimage S.measurable_factualX
  have hpull :
      P.μ[fun ω => S.dVar.indicator true ω * S.treatedCondCDF ω t | S.sigmaX]
        =ᵐ[P.μ] (fun ω => S.propScore true ω * S.treatedCondCDF ω t) := by
    have h := MeasureTheory.condExp_mul_of_stronglyMeasurable_right
      (m := S.sigmaX) (μ := P.μ)
      (S.stronglyMeasurable_treatedCondCDF_const t)
      (S.integrable_treated_indicator_mul_treatedCondCDF t)
      (S.dVar.integrable_indicator true)
    exact h.trans (Filter.EventuallyEq.of_eq (by funext ω; rfl))
  have hleft_to_ZF :
      ∫ ω in S.factualX ⁻¹' B, S.propScore true ω * S.treatedCondCDF ω t ∂P.μ =
        ∫ ω in S.factualX ⁻¹' B, S.dVar.indicator true ω *
          S.treatedCondCDF ω t ∂P.μ := by
    calc
      ∫ ω in S.factualX ⁻¹' B, S.propScore true ω * S.treatedCondCDF ω t ∂P.μ
          = ∫ ω in S.factualX ⁻¹' B,
              P.μ[fun ω => S.dVar.indicator true ω * S.treatedCondCDF ω t | S.sigmaX] ω
                ∂P.μ := by
              refine MeasureTheory.setIntegral_congr_ae hpre ?_
              filter_upwards [hpull] with ω hω _hmem
              exact hω.symm
      _ = ∫ ω in S.factualX ⁻¹' B, S.dVar.indicator true ω *
            S.treatedCondCDF ω t ∂P.μ := by
          exact MeasureTheory.setIntegral_condExp S.sigmaX_le
            (S.integrable_treated_indicator_mul_treatedCondCDF t) hpre_m
  have hZF_indicator :
      ∫ ω in S.factualX ⁻¹' B, S.dVar.indicator true ω *
          S.treatedCondCDF ω t ∂P.μ =
        ∫ ω in (S.factualX ⁻¹' B) ∩ S.treatedSet, S.treatedCondCDF ω t ∂P.μ := by
    have hcongr : Set.EqOn
        (fun ω => S.dVar.indicator true ω * S.treatedCondCDF ω t)
        (fun ω => S.treatedSet.indicator (fun ω => S.treatedCondCDF ω t) ω)
        (S.factualX ⁻¹' B) := by
      intro ω _hω
      rw [S.treated_indicator_eq]
      by_cases hT : ω ∈ S.treatedSet <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, hT]
    calc
      ∫ ω in S.factualX ⁻¹' B, S.dVar.indicator true ω *
          S.treatedCondCDF ω t ∂P.μ
          = ∫ ω in S.factualX ⁻¹' B,
              S.treatedSet.indicator (fun ω => S.treatedCondCDF ω t) ω ∂P.μ :=
            MeasureTheory.setIntegral_congr_fun hpre hcongr
      _ = ∫ ω in (S.factualX ⁻¹' B) ∩ S.treatedSet, S.treatedCondCDF ω t ∂P.μ := by
            rw [MeasureTheory.setIntegral_indicator S.measurableSet_treatedSet]
  have hmap :
      ∫ a in B, F a ∂S.treatedXYLaw.fst =
        ∫ ω in (S.factualX ⁻¹' B) ∩ S.treatedSet, S.treatedCondCDF ω t ∂P.μ := by
    have hF_aesm : AEStronglyMeasurable F S.treatedXYLaw.fst :=
      (ProbabilityTheory.measurable_condCDF S.treatedXYLaw t).aestronglyMeasurable
    calc
      ∫ a in B, F a ∂S.treatedXYLaw.fst
          = ∫ a in B, F a ∂((P.μ.restrict S.treatedSet).map S.factualX) := by
              rw [S.treatedXYLaw_fst]
      _ = ∫ ω in S.factualX ⁻¹' B, F (S.factualX ω) ∂(P.μ.restrict S.treatedSet) := by
              exact MeasureTheory.setIntegral_map hB (by simpa [S.treatedXYLaw_fst] using hF_aesm)
                S.measurable_factualX.aemeasurable
      _ = ∫ ω in (S.factualX ⁻¹' B) ∩ S.treatedSet, F (S.factualX ω) ∂P.μ := by
              rw [MeasureTheory.Measure.restrict_restrict hpre]
      _ = ∫ ω in (S.factualX ⁻¹' B) ∩ S.treatedSet, S.treatedCondCDF ω t ∂P.μ := by
              rfl
  haveI : IsFiniteMeasure S.treatedXYLaw := by
    unfold POBackdoorSystem.treatedXYLaw
    infer_instance
  have hcondcdf :
      ∫ a in B, F a ∂S.treatedXYLaw.fst = S.treatedXYLaw.real (B ×ˢ Set.Iic t) := by
    simpa [F] using ProbabilityTheory.setIntegral_condCDF S.treatedXYLaw t hB
  have hpush :
      S.treatedXYLaw (B ×ˢ Set.Iic t) =
        P.μ ((S.factualX ⁻¹' B ∩ {ω | S.factualY ω ≤ t}) ∩ S.treatedSet) := by
    unfold POBackdoorSystem.treatedXYLaw
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
      ∫ ω in S.factualX ⁻¹' B, S.propScore true ω * S.treatedCondCDF ω t ∂P.μ =
        P.μ.real ((S.factualX ⁻¹' B ∩ {ω | S.factualY ω ≤ t}) ∩ S.treatedSet) := by
    rw [hleft_to_ZF, hZF_indicator, ← hmap, hcondcdf]
    rw [MeasureTheory.measureReal_def, hpush, MeasureTheory.measureReal_def]
  have hright_measure :
      ∫ ω in S.factualX ⁻¹' B,
        S.dVar.indicator true ω * (if S.factualY ω ≤ t then (1 : ℝ) else 0) ∂P.μ =
        P.μ.real ((S.factualX ⁻¹' B ∩ {ω | S.factualY ω ≤ t}) ∩ S.treatedSet) := by
    rw [S.treated_le_indicator_eq t]
    rw [MeasureTheory.setIntegral_indicator
      ((S.measurableSet_treatedSet).inter (S.measurableSet_factualY_le t))]
    rw [MeasureTheory.setIntegral_const]
    simp only [smul_eq_mul, mul_one]
    rw [MeasureTheory.measureReal_def]
    apply congrArg ENNReal.toReal
    congr 1
    ext ω
    simp [and_assoc, and_comm]
  rw [hleft_measure, hright_measure]

private lemma treatedLe_const_eq (t : ℝ) :
    P.μ[fun ω => S.dVar.indicator true ω *
      (if S.factualY ω ≤ t then (1 : ℝ) else 0) | S.sigmaX]
      =ᵐ[P.μ] fun ω => S.propScore true ω * S.treatedCondCDF ω t := by
  classical
  set f : P.Ω → ℝ := fun ω => S.dVar.indicator true ω *
    (if S.factualY ω ≤ t then (1 : ℝ) else 0)
  set g : P.Ω → ℝ := fun ω => S.propScore true ω * S.treatedCondCDF ω t
  have hf : Integrable f P.μ := by
    change Integrable (fun ω => S.dVar.indicator true ω *
      (if S.factualY ω ≤ t then (1 : ℝ) else 0)) P.μ
    exact S.integrable_treated_le_indicator t
  have hg_int : ∀ (s : Set P.Ω), MeasurableSet[S.sigmaX] s → P.μ s < ⊤ →
      IntegrableOn g s P.μ := by
    intro s _hs _hfin
    change IntegrableOn (fun ω => S.propScore true ω * S.treatedCondCDF ω t) s P.μ
    exact (S.integrable_propScore_mul_treatedCondCDF t).integrableOn
  have hg_eq : ∀ (s : Set P.Ω), MeasurableSet[S.sigmaX] s → P.μ s < ⊤ →
      ∫ x in s, g x ∂P.μ = ∫ x in s, f x ∂P.μ := by
    intro s hs _hfin
    change (∫ x in s, S.propScore true x * S.treatedCondCDF x t ∂P.μ) =
      ∫ x in s, S.dVar.indicator true x *
        (if S.factualY x ≤ t then (1 : ℝ) else 0) ∂P.μ
    exact S.setIntegral_propScore_mul_treatedCondCDF_eq_le t s hs
  have hprop_smeas : StronglyMeasurable[S.sigmaX] (S.propScore true) := by
    unfold POBackdoorSystem.propScore
    exact MeasureTheory.stronglyMeasurable_condExp
  have hg_sm : StronglyMeasurable[S.sigmaX] g := by
    change StronglyMeasurable[S.sigmaX]
      (fun ω => S.propScore true ω * S.treatedCondCDF ω t)
    exact hprop_smeas.mul (S.stronglyMeasurable_treatedCondCDF_const t)
  have hle : S.sigmaX ≤ (inferInstance : MeasurableSpace P.Ω) := S.sigmaX_le
  have h := MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq
    hle hf hg_int hg_eq hg_sm.aestronglyMeasurable
  exact h.symm

/-- The **calibration quantile level** `τ(ω) = 1 − survTarget(ω)/e(ω)`: the treated-conditional-CDF
level whose quantile is the calibrating cutoff. -/
noncomputable def calibLevel (Λ : ℝ) (ω : P.Ω) : ℝ :=
  1 - S.survTarget Λ ω / S.propScore true ω

/-- **The survival bridge (constant cutoff).** The weighted conditional survival equals the treated
conditional survival scaled by the propensity:
`E[Z·1{Y>t} | σ(X)] = e(X)·(1 − F(t | X))` a.e. The genuine measure-theoretic
content relates a conditional expectation under `μ` (weighted by the treatment
indicator) to the conditional CDF of the treated push-forward law. -/
theorem treatedSurv_const_eq (t : ℝ) :
    P.μ[fun ω => S.dVar.indicator true ω * (if t < S.factualY ω then (1 : ℝ) else 0) | S.sigmaX]
      =ᵐ[P.μ] fun ω => S.propScore true ω * (1 - S.treatedCondCDF ω t) := by
  classical
  have hpoint :
      (fun ω => S.dVar.indicator true ω * (if t < S.factualY ω then (1 : ℝ) else 0))
        =ᵐ[P.μ]
      (fun ω => S.dVar.indicator true ω -
        S.dVar.indicator true ω * (if S.factualY ω ≤ t then (1 : ℝ) else 0)) := by
    exact Filter.Eventually.of_forall fun ω => by
      by_cases hle : S.factualY ω ≤ t
      · have hnot : ¬ t < S.factualY ω := not_lt.mpr hle
        simp [hle, hnot]
      · have hlt : t < S.factualY ω := lt_of_not_ge hle
        simp [hle, hlt]
  refine (MeasureTheory.condExp_congr_ae (m := S.sigmaX) (μ := P.μ) hpoint).trans ?_
  have hsub := MeasureTheory.condExp_sub
    (μ := P.μ) (m := S.sigmaX)
    (f := S.dVar.indicator true)
    (g := fun ω => S.dVar.indicator true ω *
      (if S.factualY ω ≤ t then (1 : ℝ) else 0))
    (S.dVar.integrable_indicator true) (S.integrable_treated_le_indicator t)
  have hle_bridge := S.treatedLe_const_eq t
  filter_upwards [hsub, hle_bridge] with ω hsubω hleω
  change P.μ[S.dVar.indicator true - (fun ω => S.dVar.indicator true ω *
      (if S.factualY ω ≤ t then (1 : ℝ) else 0)) | S.sigmaX] ω =
    S.propScore true ω * (1 - S.treatedCondCDF ω t)
  rw [hsubω]
  change S.propScore true ω -
      P.μ[fun ω => S.dVar.indicator true ω *
        (if S.factualY ω ≤ t then (1 : ℝ) else 0) | S.sigmaX] ω =
    S.propScore true ω * (1 - S.treatedCondCDF ω t)
  rw [hleω]
  ring

private lemma exists_factor_through_factualX_private {f : P.Ω → ℝ}
    (hf : Measurable[S.sigmaX] f) :
    ∃ g : γ → ℝ, Measurable g ∧ f = fun ω => g (S.factualX ω) := by
  rw [POBackdoorSystem.sigmaX] at hf
  obtain ⟨g, hg, hfg⟩ := hf.exists_eq_measurable_comp (f := S.factualX)
  exact ⟨g, hg, by simpa [Function.comp_def] using hfg⟩

/-- The conditional CDF remains measurable when evaluated at a measurable cutoff. -/
lemma measurable_condCDF_variable (ρ : Measure (γ × ℝ)) [IsFiniteMeasure ρ]
    {q : γ → ℝ} (hq : Measurable q) :
    Measurable (fun a => condCDF ρ a (q a)) := by
  classical
  let V : Set (γ × ℝ) := {p : γ × ℝ | p.2 ≤ q p.1}
  have hV : MeasurableSet V := by
    dsimp [V]
    exact measurableSet_le measurable_snd (hq.comp measurable_fst)
  let hf := ProbabilityTheory.isCondKernelCDF_condCDF ρ
  have hkern : Measurable fun a : γ =>
      hf.toKernel (fun p : Unit × γ => condCDF ρ p.2) ((), a) (Prod.mk a ⁻¹' V) := by
    exact Kernel.measurable_kernel_prodMk_left'
      (η := hf.toKernel (fun p : Unit × γ => condCDF ρ p.2)) hV ()
  have hfun : (fun a : γ => condCDF ρ a (q a)) = fun a =>
      (hf.toKernel (fun p : Unit × γ => condCDF ρ p.2) ((), a)
        (Prod.mk a ⁻¹' V)).toReal := by
    funext a
    have hpre : Prod.mk a ⁻¹' V = Set.Iic (q a) := by
      ext y
      simp [V]
    rw [hpre, ProbabilityTheory.IsCondKernelCDF.toKernel_Iic]
    exact (ENNReal.toReal_ofReal (ProbabilityTheory.condCDF_nonneg ρ a (q a))).symm
  rw [hfun]
  exact ENNReal.measurable_toReal.comp hkern

/-- The conditional CDF evaluated at a measurable cutoff is integrable under
the first marginal. -/
lemma integrable_condCDF_variable (ρ : Measure (γ × ℝ)) [IsFiniteMeasure ρ]
    {q : γ → ℝ} (hq : Measurable q) :
    Integrable (fun a => condCDF ρ a (q a)) ρ.fst := by
  refine (integrable_const (μ := ρ.fst) (c := (1 : ℝ))).mono'
    (measurable_condCDF_variable ρ hq).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun a => by
    rw [Real.norm_of_nonneg (ProbabilityTheory.condCDF_nonneg ρ a (q a))]
    exact ProbabilityTheory.condCDF_le_one ρ a (q a)

/-- Set-lintegral form of the conditional CDF identity at a measurable
variable cutoff. -/
lemma setLIntegral_condCDF_variable (ρ : Measure (γ × ℝ)) [IsFiniteMeasure ρ]
    {B : Set γ} (hB : MeasurableSet B) {q : γ → ℝ} (hq : Measurable q) :
    ∫⁻ a in B, ENNReal.ofReal (condCDF ρ a (q a)) ∂ρ.fst =
      ρ {p : γ × ℝ | p.1 ∈ B ∧ p.2 ≤ q p.1} := by
  classical
  let V : Set (γ × ℝ) := {p : γ × ℝ | p.1 ∈ B ∧ p.2 ≤ q p.1}
  have hV : MeasurableSet V := by
    dsimp [V]
    exact (hB.preimage measurable_fst).inter
      (measurableSet_le measurable_snd (hq.comp measurable_fst))
  let hf := ProbabilityTheory.isCondKernelCDF_condCDF ρ
  have hmem := ProbabilityTheory.lintegral_toKernel_mem (κ := Kernel.const Unit ρ)
    (ν := Kernel.const Unit ρ.fst)
    (f := fun p : Unit × γ => condCDF ρ p.2) hf () hV
  have hpoint : ∀ a : γ,
      hf.toKernel (fun p : Unit × γ => condCDF ρ p.2) ((), a) (Prod.mk a ⁻¹' V) =
        B.indicator (fun a => ENNReal.ofReal (condCDF ρ a (q a))) a := by
    intro a
    by_cases ha : a ∈ B
    · have hpre : Prod.mk a ⁻¹' V = Set.Iic (q a) := by
        ext y
        simp [V, ha]
      rw [hpre, ProbabilityTheory.IsCondKernelCDF.toKernel_Iic]
      simp [Set.indicator_of_mem ha]
    · have hpre : Prod.mk a ⁻¹' V = ∅ := by
        ext y
        simp [V, ha]
      rw [hpre]
      simp [Set.indicator_of_notMem ha]
  calc
    ∫⁻ a in B, ENNReal.ofReal (condCDF ρ a (q a)) ∂ρ.fst
        = ∫⁻ a, B.indicator (fun a => ENNReal.ofReal (condCDF ρ a (q a))) a
            ∂ρ.fst := by
          exact (MeasureTheory.lintegral_indicator hB _).symm
    _ = ∫⁻ a, hf.toKernel (fun p : Unit × γ => condCDF ρ p.2) ((), a)
          (Prod.mk a ⁻¹' V) ∂(Kernel.const Unit ρ.fst ()) := by
          simp only [Kernel.const_apply]
          exact lintegral_congr_ae (Filter.Eventually.of_forall fun a => (hpoint a).symm)
    _ = Kernel.const Unit ρ () V := hmem
    _ = ρ V := by simp

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

private lemma treated_le_indicator_variable_eq (c : P.Ω → ℝ) :
    (fun ω => S.dVar.indicator true ω * (if S.factualY ω ≤ c ω then (1 : ℝ) else 0))
      = fun ω => (S.treatedSet ∩ {ω | S.factualY ω ≤ c ω}).indicator
          (fun _ : P.Ω => (1 : ℝ)) ω := by
  funext ω
  unfold POBackdoorSystem.treatedSet POVar.indicator POVar.event POBackdoorSystem.factualD
  by_cases hD : S.dVar.factual ω = true <;> by_cases hY : S.factualY ω ≤ c ω <;>
    simp [hD, hY]

private lemma measurableSet_factualY_le_cutoff (c : P.Ω → ℝ) (hc : Measurable[S.sigmaX] c) :
    MeasurableSet {ω | S.factualY ω ≤ c ω} :=
  measurableSet_le S.measurable_factualY (hc.mono S.sigmaX_le le_rfl)

private lemma integrable_treated_le_indicator_variable (c : P.Ω → ℝ)
    (hc : Measurable[S.sigmaX] c) :
    Integrable (fun ω => S.dVar.indicator true ω *
      (if S.factualY ω ≤ c ω then (1 : ℝ) else 0)) P.μ := by
  rw [treated_le_indicator_variable_eq]
  exact (integrable_const (α := P.Ω) (μ := P.μ) (c := (1 : ℝ))).indicator
    ((S.measurableSet_treatedSet).inter (S.measurableSet_factualY_le_cutoff c hc))

private lemma measurable_treatedCondCDF_variable (c : P.Ω → ℝ)
    (hc : Measurable[S.sigmaX] c) :
    Measurable[S.sigmaX] (fun ω => S.treatedCondCDF ω (c ω)) := by
  obtain ⟨q, hq, hc_eq⟩ := S.exists_factor_through_factualX_private hc
  haveI : IsFiniteMeasure S.treatedXYLaw := by
    unfold POBackdoorSystem.treatedXYLaw
    infer_instance
  rw [POBackdoorSystem.sigmaX, hc_eq]
  unfold POBackdoorSystem.treatedCondCDF
  exact (measurable_condCDF_variable S.treatedXYLaw hq).comp
    (comap_measurable S.factualX)

private lemma stronglyMeasurable_treatedCondCDF_variable (c : P.Ω → ℝ)
    (hc : Measurable[S.sigmaX] c) :
    StronglyMeasurable[S.sigmaX] (fun ω => S.treatedCondCDF ω (c ω)) :=
  (S.measurable_treatedCondCDF_variable c hc).stronglyMeasurable

private lemma measurable_treatedCondCDF_variable_ambient (c : P.Ω → ℝ)
    (hc : Measurable[S.sigmaX] c) :
    Measurable (fun ω => S.treatedCondCDF ω (c ω)) :=
  (S.measurable_treatedCondCDF_variable c hc).mono S.sigmaX_le le_rfl

private lemma eventually_norm_treatedCondCDF_variable_le_one (c : P.Ω → ℝ) :
    ∀ᵐ ω ∂P.μ, ‖S.treatedCondCDF ω (c ω)‖ ≤ 1 := by
  exact Filter.Eventually.of_forall fun ω => by
    unfold POBackdoorSystem.treatedCondCDF
    rw [Real.norm_of_nonneg (ProbabilityTheory.condCDF_nonneg
      S.treatedXYLaw (S.factualX ω) (c ω))]
    exact ProbabilityTheory.condCDF_le_one S.treatedXYLaw (S.factualX ω) (c ω)

private lemma integrable_propScore_mul_treatedCondCDF_variable (c : P.Ω → ℝ)
    (hc : Measurable[S.sigmaX] c) :
    Integrable (fun ω => S.propScore true ω * S.treatedCondCDF ω (c ω)) P.μ := by
  have he : Integrable (S.propScore true) P.μ := by
    unfold POBackdoorSystem.propScore
    exact MeasureTheory.integrable_condExp
  exact he.mul_bdd
    ((S.measurable_treatedCondCDF_variable_ambient c hc).aestronglyMeasurable)
    (S.eventually_norm_treatedCondCDF_variable_le_one c)

private lemma integrable_treated_indicator_mul_treatedCondCDF_variable (c : P.Ω → ℝ)
    (hc : Measurable[S.sigmaX] c) :
    Integrable (fun ω => S.dVar.indicator true ω * S.treatedCondCDF ω (c ω)) P.μ := by
  exact (S.dVar.integrable_indicator true).mul_bdd
    ((S.measurable_treatedCondCDF_variable_ambient c hc).aestronglyMeasurable)
    (S.eventually_norm_treatedCondCDF_variable_le_one c)

private lemma setIntegral_propScore_mul_treatedCondCDF_eq_le_variable (c : P.Ω → ℝ)
    (hc : Measurable[S.sigmaX] c) (s : Set P.Ω) (hs : MeasurableSet[S.sigmaX] s) :
    ∫ ω in s, S.propScore true ω * S.treatedCondCDF ω (c ω) ∂P.μ =
      ∫ ω in s, S.dVar.indicator true ω *
        (if S.factualY ω ≤ c ω then (1 : ℝ) else 0) ∂P.μ := by
  classical
  obtain ⟨B, hB, rfl⟩ := S.exists_measurableSet_through_factualX hs
  obtain ⟨q, hq, hc_eq⟩ := S.exists_factor_through_factualX_private hc
  rw [hc_eq]
  let F : γ → ℝ := fun a => condCDF S.treatedXYLaw a (q a)
  haveI : IsFiniteMeasure S.treatedXYLaw := by
    unfold POBackdoorSystem.treatedXYLaw
    infer_instance
  have hcq : Measurable[S.sigmaX] (fun ω => q (S.factualX ω)) := by
    rw [POBackdoorSystem.sigmaX]
    exact hq.comp (comap_measurable S.factualX)
  have hpre_m : MeasurableSet[S.sigmaX] (S.factualX ⁻¹' B) := by
    rw [POBackdoorSystem.sigmaX]
    exact ⟨B, hB, rfl⟩
  have hpre : MeasurableSet (S.factualX ⁻¹' B) := hB.preimage S.measurable_factualX
  have hpull :
      P.μ[fun ω => S.dVar.indicator true ω * S.treatedCondCDF ω (q (S.factualX ω))
          | S.sigmaX]
        =ᵐ[P.μ] (fun ω => S.propScore true ω *
          S.treatedCondCDF ω (q (S.factualX ω))) := by
    have h := MeasureTheory.condExp_mul_of_stronglyMeasurable_right
      (m := S.sigmaX) (μ := P.μ)
      (S.stronglyMeasurable_treatedCondCDF_variable (fun ω => q (S.factualX ω)) hcq)
      (S.integrable_treated_indicator_mul_treatedCondCDF_variable
        (fun ω => q (S.factualX ω)) hcq)
      (S.dVar.integrable_indicator true)
    exact h.trans (Filter.EventuallyEq.of_eq (by funext ω; rfl))
  have hleft_to_ZF :
      ∫ ω in S.factualX ⁻¹' B, S.propScore true ω *
          S.treatedCondCDF ω (q (S.factualX ω)) ∂P.μ =
        ∫ ω in S.factualX ⁻¹' B, S.dVar.indicator true ω *
          S.treatedCondCDF ω (q (S.factualX ω)) ∂P.μ := by
    calc
      ∫ ω in S.factualX ⁻¹' B, S.propScore true ω *
          S.treatedCondCDF ω (q (S.factualX ω)) ∂P.μ
          = ∫ ω in S.factualX ⁻¹' B,
              P.μ[fun ω => S.dVar.indicator true ω *
                S.treatedCondCDF ω (q (S.factualX ω)) | S.sigmaX] ω ∂P.μ := by
              refine MeasureTheory.setIntegral_congr_ae hpre ?_
              filter_upwards [hpull] with ω hω _hmem
              exact hω.symm
      _ = ∫ ω in S.factualX ⁻¹' B, S.dVar.indicator true ω *
            S.treatedCondCDF ω (q (S.factualX ω)) ∂P.μ := by
          exact MeasureTheory.setIntegral_condExp S.sigmaX_le
            (S.integrable_treated_indicator_mul_treatedCondCDF_variable
              (fun ω => q (S.factualX ω)) hcq) hpre_m
  have hZF_indicator :
      ∫ ω in S.factualX ⁻¹' B, S.dVar.indicator true ω *
          S.treatedCondCDF ω (q (S.factualX ω)) ∂P.μ =
        ∫ ω in (S.factualX ⁻¹' B) ∩ S.treatedSet,
          S.treatedCondCDF ω (q (S.factualX ω)) ∂P.μ := by
    have hcongr : Set.EqOn
        (fun ω => S.dVar.indicator true ω * S.treatedCondCDF ω (q (S.factualX ω)))
        (fun ω => S.treatedSet.indicator
          (fun ω => S.treatedCondCDF ω (q (S.factualX ω))) ω)
        (S.factualX ⁻¹' B) := by
      intro ω _hω
      rw [S.treated_indicator_eq]
      by_cases hT : ω ∈ S.treatedSet <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, hT]
    calc
      ∫ ω in S.factualX ⁻¹' B, S.dVar.indicator true ω *
          S.treatedCondCDF ω (q (S.factualX ω)) ∂P.μ
          = ∫ ω in S.factualX ⁻¹' B,
              S.treatedSet.indicator
                (fun ω => S.treatedCondCDF ω (q (S.factualX ω))) ω ∂P.μ :=
            MeasureTheory.setIntegral_congr_fun hpre hcongr
      _ = ∫ ω in (S.factualX ⁻¹' B) ∩ S.treatedSet,
            S.treatedCondCDF ω (q (S.factualX ω)) ∂P.μ := by
            rw [MeasureTheory.setIntegral_indicator S.measurableSet_treatedSet]
  have hmap :
      ∫ a in B, F a ∂S.treatedXYLaw.fst =
        ∫ ω in (S.factualX ⁻¹' B) ∩ S.treatedSet,
          S.treatedCondCDF ω (q (S.factualX ω)) ∂P.μ := by
    have hF_aesm : AEStronglyMeasurable F S.treatedXYLaw.fst :=
      (measurable_condCDF_variable S.treatedXYLaw hq).aestronglyMeasurable
    calc
      ∫ a in B, F a ∂S.treatedXYLaw.fst
          = ∫ a in B, F a ∂((P.μ.restrict S.treatedSet).map S.factualX) := by
              rw [S.treatedXYLaw_fst]
      _ = ∫ ω in S.factualX ⁻¹' B, F (S.factualX ω)
            ∂(P.μ.restrict S.treatedSet) := by
              exact MeasureTheory.setIntegral_map hB
                (by simpa [S.treatedXYLaw_fst] using hF_aesm)
                S.measurable_factualX.aemeasurable
      _ = ∫ ω in (S.factualX ⁻¹' B) ∩ S.treatedSet, F (S.factualX ω) ∂P.μ := by
              rw [MeasureTheory.Measure.restrict_restrict hpre]
      _ = ∫ ω in (S.factualX ⁻¹' B) ∩ S.treatedSet,
            S.treatedCondCDF ω (q (S.factualX ω)) ∂P.μ := by
              rfl
  have hcondcdf :
      ∫ a in B, F a ∂S.treatedXYLaw.fst =
        S.treatedXYLaw.real {p : γ × ℝ | p.1 ∈ B ∧ p.2 ≤ q p.1} := by
    simpa [F] using setIntegral_condCDF_variable S.treatedXYLaw hB hq
  have hpush :
      S.treatedXYLaw {p : γ × ℝ | p.1 ∈ B ∧ p.2 ≤ q p.1} =
        P.μ ((S.factualX ⁻¹' B ∩ {ω | S.factualY ω ≤ q (S.factualX ω)}) ∩
          S.treatedSet) := by
    unfold POBackdoorSystem.treatedXYLaw
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
      ∫ ω in S.factualX ⁻¹' B, S.propScore true ω *
          S.treatedCondCDF ω (q (S.factualX ω)) ∂P.μ =
        P.μ.real ((S.factualX ⁻¹' B ∩ {ω | S.factualY ω ≤ q (S.factualX ω)}) ∩
          S.treatedSet) := by
    rw [hleft_to_ZF, hZF_indicator, ← hmap, hcondcdf]
    rw [MeasureTheory.measureReal_def, hpush, MeasureTheory.measureReal_def]
  have hright_measure :
      ∫ ω in S.factualX ⁻¹' B,
        S.dVar.indicator true ω *
          (if S.factualY ω ≤ q (S.factualX ω) then (1 : ℝ) else 0) ∂P.μ =
        P.μ.real ((S.factualX ⁻¹' B ∩ {ω | S.factualY ω ≤ q (S.factualX ω)}) ∩
          S.treatedSet) := by
    rw [S.treated_le_indicator_variable_eq (fun ω => q (S.factualX ω))]
    rw [MeasureTheory.setIntegral_indicator
      ((S.measurableSet_treatedSet).inter
        (S.measurableSet_factualY_le_cutoff (fun ω => q (S.factualX ω)) hcq))]
    rw [MeasureTheory.setIntegral_const]
    simp only [smul_eq_mul, mul_one]
    rw [MeasureTheory.measureReal_def]
    apply congrArg ENNReal.toReal
    congr 1
    ext ω
    simp [and_assoc, and_comm]
  rw [hleft_measure, hright_measure]

private lemma treatedLe_eq (c : P.Ω → ℝ) (hc : Measurable[S.sigmaX] c) :
    P.μ[fun ω => S.dVar.indicator true ω *
      (if S.factualY ω ≤ c ω then (1 : ℝ) else 0) | S.sigmaX]
      =ᵐ[P.μ] fun ω => S.propScore true ω * S.treatedCondCDF ω (c ω) := by
  classical
  set f : P.Ω → ℝ := fun ω => S.dVar.indicator true ω *
    (if S.factualY ω ≤ c ω then (1 : ℝ) else 0)
  set g : P.Ω → ℝ := fun ω => S.propScore true ω * S.treatedCondCDF ω (c ω)
  have hf : Integrable f P.μ := by
    change Integrable (fun ω => S.dVar.indicator true ω *
      (if S.factualY ω ≤ c ω then (1 : ℝ) else 0)) P.μ
    exact S.integrable_treated_le_indicator_variable c hc
  have hg_int : ∀ (s : Set P.Ω), MeasurableSet[S.sigmaX] s → P.μ s < ⊤ →
      IntegrableOn g s P.μ := by
    intro s _hs _hfin
    change IntegrableOn (fun ω => S.propScore true ω * S.treatedCondCDF ω (c ω)) s P.μ
    exact (S.integrable_propScore_mul_treatedCondCDF_variable c hc).integrableOn
  have hg_eq : ∀ (s : Set P.Ω), MeasurableSet[S.sigmaX] s → P.μ s < ⊤ →
      ∫ x in s, g x ∂P.μ = ∫ x in s, f x ∂P.μ := by
    intro s hs _hfin
    change (∫ x in s, S.propScore true x * S.treatedCondCDF x (c x) ∂P.μ) =
      ∫ x in s, S.dVar.indicator true x *
        (if S.factualY x ≤ c x then (1 : ℝ) else 0) ∂P.μ
    exact S.setIntegral_propScore_mul_treatedCondCDF_eq_le_variable c hc s hs
  have hprop_smeas : StronglyMeasurable[S.sigmaX] (S.propScore true) := by
    unfold POBackdoorSystem.propScore
    exact MeasureTheory.stronglyMeasurable_condExp
  have hg_sm : StronglyMeasurable[S.sigmaX] g := by
    change StronglyMeasurable[S.sigmaX]
      (fun ω => S.propScore true ω * S.treatedCondCDF ω (c ω))
    exact hprop_smeas.mul (S.stronglyMeasurable_treatedCondCDF_variable c hc)
  have hle : S.sigmaX ≤ (inferInstance : MeasurableSpace P.Ω) := S.sigmaX_le
  have h := MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq
    hle hf hg_int hg_eq hg_sm.aestronglyMeasurable
  exact h.symm

/-- **The survival bridge (functional cutoff).** The version of `treatedSurv_const_eq`
evaluated at a `σ(X)`-measurable cutoff `c`:
`E[Z·1{Y>c(X)} | σ(X)] = e(X)·(1 − F(c(X) | X))` a.e. Since `c` is `σ(X)`-measurable,
it is "frozen" inside the conditional expectation, reducing to the constant-cutoff
bridge fibrewise. This is the form consumed by `exists_calibrating_cutoff`. -/
theorem treatedSurv_eq (c : P.Ω → ℝ) (hc : Measurable[S.sigmaX] c) :
    S.treatedSurv c =ᵐ[P.μ] fun ω => S.propScore true ω * (1 - S.treatedCondCDF ω (c ω)) := by
  classical
  unfold POBackdoorSystem.treatedSurv
  have hpoint :
      (fun ω => S.dVar.indicator true ω * (if c ω < S.factualY ω then (1 : ℝ) else 0))
        =ᵐ[P.μ]
      (fun ω => S.dVar.indicator true ω -
        S.dVar.indicator true ω * (if S.factualY ω ≤ c ω then (1 : ℝ) else 0)) := by
    exact Filter.Eventually.of_forall fun ω => by
      by_cases hle : S.factualY ω ≤ c ω
      · have hnot : ¬ c ω < S.factualY ω := not_lt.mpr hle
        simp [hle, hnot]
      · have hlt : c ω < S.factualY ω := lt_of_not_ge hle
        simp [hle, hlt]
  refine (MeasureTheory.condExp_congr_ae (m := S.sigmaX) (μ := P.μ) hpoint).trans ?_
  have hsub := MeasureTheory.condExp_sub
    (μ := P.μ) (m := S.sigmaX)
    (f := S.dVar.indicator true)
    (g := fun ω => S.dVar.indicator true ω *
      (if S.factualY ω ≤ c ω then (1 : ℝ) else 0))
    (S.dVar.integrable_indicator true) (S.integrable_treated_le_indicator_variable c hc)
  have hle_bridge := S.treatedLe_eq c hc
  filter_upwards [hsub, hle_bridge] with ω hsubω hleω
  change P.μ[S.dVar.indicator true - (fun ω => S.dVar.indicator true ω *
      (if S.factualY ω ≤ c ω then (1 : ℝ) else 0)) | S.sigmaX] ω =
    S.propScore true ω * (1 - S.treatedCondCDF ω (c ω))
  rw [hsubω]
  change S.propScore true ω -
      P.μ[fun ω => S.dVar.indicator true ω *
        (if S.factualY ω ≤ c ω then (1 : ℝ) else 0) | S.sigmaX] ω =
    S.propScore true ω * (1 - S.treatedCondCDF ω (c ω))
  rw [hleω]
  ring

/-- **σ(X)-measurable functions factor through `X`.** If `f` is `σ(X)`-measurable then
`f = g ∘ X` for a measurable `g : γ → ℝ`. This is standard `comap` factorization:
the conditioning is on the value of `X`. -/
theorem exists_factor_through_factualX {f : P.Ω → ℝ} (hf : Measurable[S.sigmaX] f) :
    ∃ g : γ → ℝ, Measurable g ∧ f = fun ω => g (S.factualX ω) := by
  rw [POBackdoorSystem.sigmaX] at hf
  obtain ⟨g, hg, hfg⟩ := hf.exists_eq_measurable_comp (f := S.factualX)
  exact ⟨g, hg, by simpa [Function.comp_def] using hfg⟩

/-- Existence of a calibrating cutoff. Under overlap, `1 < Λ`, an atomless treated
conditional outcome law (`condCDF` of the treated push-forward continuous), and a strictly-interior
calibration level, there is a `σ(X)`-measurable cutoff `c` solving the survival equation
`treatedSurv c =ᵐ survTarget Λ`. The cutoff is the conditional quantile `Q_{calibLevel}(X)`. -/
theorem exists_calibrating_cutoff (Λ : ℝ) (hΛ : 1 < Λ)
    (hoverlap : ∀ᵐ ω ∂P.μ, 0 < S.propScore true ω ∧ S.propScore true ω < 1)
    (hatomless : ∀ a : γ, Continuous (condCDF S.treatedXYLaw a))
    (hlevel : ∀ᵐ ω ∂P.μ, 0 < S.calibLevel Λ ω ∧ S.calibLevel Λ ω < 1) :
    ∃ c : P.Ω → ℝ, Measurable[S.sigmaX] c ∧ S.treatedSurv c =ᵐ[P.μ] S.survTarget Λ := by
  classical
  have hprop_meas : Measurable[S.sigmaX] (S.propScore true) := by
    unfold POBackdoorSystem.propScore
    exact stronglyMeasurable_condExp.measurable
  have hwMin_meas : Measurable[S.sigmaX] (S.wMin Λ) := by
    unfold POBackdoorSystem.wMin
    exact measurable_const.add
      ((measurable_const.sub hprop_meas).div (measurable_const.mul hprop_meas))
  have hwMax_meas : Measurable[S.sigmaX] (S.wMax Λ) := by
    unfold POBackdoorSystem.wMax
    exact measurable_const.add
      ((measurable_const.mul (measurable_const.sub hprop_meas)).div hprop_meas)
  have hsurvTarget_meas : Measurable[S.sigmaX] (S.survTarget Λ) := by
    unfold POBackdoorSystem.survTarget
    exact (measurable_const.sub (hwMin_meas.mul hprop_meas)).div
      (hwMax_meas.sub hwMin_meas)
  have hlevel_meas : Measurable[S.sigmaX] (S.calibLevel Λ) := by
    unfold POBackdoorSystem.calibLevel
    exact measurable_const.sub (hsurvTarget_meas.div hprop_meas)
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
    · simpa [ha] using ha.1
    · simp [ha]
  have hτ1 : ∀ a, τ a < 1 := by
    intro a
    dsimp [τ]
    by_cases ha : 0 < g a ∧ g a < 1
    · simpa [ha] using ha.2
    · simp only [ha, ↓reduceIte]
      norm_num
  haveI : IsFiniteMeasure S.treatedXYLaw := by
    unfold POBackdoorSystem.treatedXYLaw
    infer_instance
  obtain ⟨hq_meas, hq_attain⟩ :=
    Causalean.Mathlib.measurable_condQuantile_and_attains
      S.treatedXYLaw τ hτ_meas hτ0 hτ1 hatomless
  let c : P.Ω → ℝ := fun ω =>
    Causalean.Mathlib.condQuantile S.treatedXYLaw τ (S.factualX ω)
  have hc_meas : Measurable[S.sigmaX] c := by
    rw [POBackdoorSystem.sigmaX]
    exact hq_meas.comp (comap_measurable S.factualX)
  refine ⟨c, hc_meas, ?_⟩
  have hτ_eq_level : ∀ᵐ ω ∂P.μ, τ (S.factualX ω) = S.calibLevel Λ ω := by
    filter_upwards [hlevel] with ω hω
    have hgx : g (S.factualX ω) = S.calibLevel Λ ω := by
      exact (congrFun hg_eq ω).symm
    dsimp [τ]
    rw [hgx]
    simp [hω]
  have hsurv := S.treatedSurv_eq c hc_meas
  filter_upwards [hsurv, hτ_eq_level, hoverlap] with ω hsurvω hτω hoverlapω
  rw [hsurvω]
  have hcdf :
      S.treatedCondCDF ω (c ω) = τ (S.factualX ω) := by
    unfold POBackdoorSystem.treatedCondCDF c
    exact hq_attain (S.factualX ω)
  rw [hcdf, hτω]
  unfold POBackdoorSystem.calibLevel
  have hpos : S.propScore true ω ≠ 0 := ne_of_gt hoverlapω.1
  field_simp [hpos]
  ring

/-- The sharp upper bound, unconditionally. Combining the constructed calibrating
cutoff with `msmUpperCalib_eq_cutoff`, the Dorn–Guo sharp upper bound has the
quantile-balancing closed form `msmUpperCalib Λ = candMean (cutoffProp Λ c)` for
the conditional-quantile cutoff `c`, with no `hcut_mem` hypothesis. Membership is
discharged by `exists_calibrating_cutoff`; regularity assumptions cover overlap,
`1 < Λ`, atomless treated outcome law, interior level, and envelope integrability. -/
theorem msmUpperCalib_eq_cutoff_unconditional (Λ : ℝ) (hΛ : 1 < Λ)
    (hoverlap : ∀ᵐ ω ∂P.μ, 0 < S.propScore true ω ∧ S.propScore true ω < 1)
    (hatomless : ∀ a : γ, Continuous (condCDF S.treatedXYLaw a))
    (hlevel : ∀ᵐ ω ∂P.μ, 0 < S.calibLevel Λ ω ∧ S.calibLevel Λ ω < 1)
    (hbdd : BddAbove (S.candMean '' S.MSMSetCalib Λ))
    (hmeas : ∀ etilde ∈ S.MSMSetCalib Λ, AEMeasurable etilde P.μ)
    (hreg : ∀ c : P.Ω → ℝ, Measurable[S.sigmaX] c →
      Integrable c P.μ ∧
      Integrable (fun ω => S.dVar.indicator true ω / S.cutoffProp Λ c ω) P.μ ∧
      Integrable (fun ω =>
        S.dVar.indicator true ω * (if c ω < S.factualY ω then (1 : ℝ) else 0)) P.μ ∧
      Integrable (fun ω => S.dVar.indicator true ω * S.wMin Λ ω) P.μ ∧
      Integrable (fun ω => (S.wMax Λ ω - S.wMin Λ ω) *
        (S.dVar.indicator true ω * (if c ω < S.factualY ω then (1 : ℝ) else 0))) P.μ ∧
      Integrable (fun ω => S.dVar.indicator true ω * |S.factualY ω| * S.wMax Λ ω) P.μ ∧
      Integrable (fun ω => S.dVar.indicator true ω * S.wMax Λ ω) P.μ ∧
      Integrable (fun ω => |c ω| * S.dVar.indicator true ω * S.wMax Λ ω) P.μ) :
    ∃ c : P.Ω → ℝ, Measurable[S.sigmaX] c ∧
      S.cutoffProp Λ c ∈ S.MSMSetCalib Λ ∧
      S.msmUpperCalib Λ = S.candMean (S.cutoffProp Λ c) := by
  obtain ⟨c, hc_meas, hsurv⟩ :=
    S.exists_calibrating_cutoff Λ hΛ hoverlap hatomless hlevel
  obtain ⟨hc_int, hint, hint1, hmin_int, hdiff_int,
    henv, hweight_env, hc_env⟩ := hreg c hc_meas
  have hcut_mem : S.cutoffProp Λ c ∈ S.MSMSetCalib Λ :=
    S.cutoffProp_mem_MSMSetCalib_of_survival Λ hΛ hoverlap c hc_meas
      hint hint1 hmin_int hdiff_int hsurv
  have heq : S.msmUpperCalib Λ = S.candMean (S.cutoffProp Λ c) :=
    S.msmUpperCalib_eq_cutoff Λ (le_of_lt hΛ) hoverlap c hc_meas
      hc_int hcut_mem henv hweight_env hc_env hmeas
  exact ⟨c, hc_meas, hcut_mem, heq⟩

end POBackdoorSystem

end PO
end Causalean
