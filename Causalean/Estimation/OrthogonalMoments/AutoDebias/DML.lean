/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Automatic debiasing — DML estimator and asymptotic linearity

This file instantiates the automatic-debiasing construction from
`doc/basic_concepts/po/estimation/automatic_debiasing.tex` in the abstract DML
framework:

* `linAutoNuisance S` — the joint nuisance type `H_γ × (X → ℝ)` carrying
  componentwise `AddCommGroup`/`Module ℝ`.
* `linAutoGeneralMoment S rep ε` — `GeneralMoment` instance built from
  the linear Riesz score: `m (γ, α) z θ := linRieszScore S γ α θ z`.
* `linAuto_meanZero` — `MeanZero` for the AutoDML moment.
* `linAuto_bilinearRem` — bilinear remainder via `rieszScore_bilinearRem` +
  Cauchy–Schwarz on `L²(P_X)`.
* `linAutoDMLEstimator S rep ε sample split η_hat` — the one-shot
  Auto-DML estimator, built as a `dmlChernozhukovEstimator`.
* `linAutoDML_asymptoticLinear` — asymptotic-linearity wrapper at
  `θ₀ := L_of_m S S.g₀`, assuming the mean-zero, remainder, and rate
  hypotheses required by the abstract DML theorem.

Mirrors `Estimation/OrthogonalMoments/AIPWInstance.lean` style.
-/

import Causalean.Estimation.OrthogonalMoments.DMLChernozhukov
import Causalean.Estimation.OrthogonalMoments.AutoDebias.Linear
import Causalean.Stat.SampleSplit
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-! # Automatic Debiasing DML Estimator

This file instantiates the abstract Chernozhukov double machine learning
framework with the linear automatic-debiasing score. It packages the joint
regression and Riesz-representer nuisance, proves reusable mean-zero and
bilinear-remainder lemmas, and states an asymptotic-linearity wrapper under the
abstract DML theorem's supplied hypotheses. -/

namespace Causalean.Estimation.OrthogonalMoments.AutoDebias

open MeasureTheory ProbabilityTheory Filter Topology Causalean.Stat
  Causalean.Estimation.OrthogonalMoments

/-- **Joint nuisance type** for the linear Auto-DML moment: a regression
function `γ ∈ H_γ` paired with a Riesz-representer candidate
`α : X → ℝ`.  Carries componentwise `AddCommGroup` / `Module ℝ`. -/
def linAutoNuisance (S : LinRegFnSys) : Type _ := S.H_γ × (S.X → ℝ)

noncomputable instance linAutoNuisance.instAddCommGroup (S : LinRegFnSys) :
    AddCommGroup (linAutoNuisance S) := by
  unfold linAutoNuisance
  infer_instance

noncomputable instance linAutoNuisance.instModule (S : LinRegFnSys) :
    Module ℝ (linAutoNuisance S) := by
  unfold linAutoNuisance
  exact Prod.instModule

/-- **Linear Auto-DML moment** as a `GeneralMoment` instance.

The bilinear seminorms are the L²(P_X) norms of `γ_target η.1 - γ_target g₀`
and `η.2 - rep.α₀` respectively.  `J₀ = -1` since the score
`linRieszScore γ α θ z = L γ + α(X) (Y_obs - γ(X)) - θ` is linear in `θ`
with slope `-1`. -/
noncomputable def linAutoGeneralMoment
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (S : LinRegFnSys)
    (rep : Causalean.Estimation.OrthogonalMoments.RieszRepresentation
              S.H_γ S.γ_target (L_of_m S) S.P_X)
    (ε : ℝ) (hε_nn : 0 ≤ ε)
    (h_score_meas : ∀ η : linAutoNuisance S, ∀ θ : ℝ,
      Measurable (fun z => linRieszScore S η.1 η.2 θ z)) :
    GeneralMoment Ω μ S.Z S.P_Z (linAutoNuisance S) where
  m := fun η z θ => linRieszScore S η.1 η.2 θ z
  η₀ := (S.g₀, rep.α₀)
  θ₀ := L_of_m S S.g₀
  H_ε := { η : linAutoNuisance S |
    (eLpNorm (fun x => S.γ_target η.1 x - S.γ_target S.g₀ x) 2 S.P_X).toReal ≤ ε ∧
    (eLpNorm (fun x => η.2 x - rep.α₀ x) 2 S.P_X).toReal ≤ ε }
  ρ₁ := fun η η' =>
    ⟨(eLpNorm (fun x => S.γ_target η.1 x - S.γ_target η'.1 x) 2 S.P_X).toReal,
     ENNReal.toReal_nonneg⟩
  ρ₂ := fun η η' =>
    ⟨(eLpNorm (fun x => η.2 x - η'.2 x) 2 S.P_X).toReal,
     ENNReal.toReal_nonneg⟩
  m_meas := h_score_meas
  η₀_mem := by
    refine ⟨?_, ?_⟩
    · have h1 : (fun x => S.γ_target S.g₀ x - S.γ_target S.g₀ x)
              = (fun _ : S.X => (0 : ℝ)) := by funext x; ring
      rw [h1]
      simp [hε_nn]
    · have h2 : (fun x => rep.α₀ x - rep.α₀ x)
              = (fun _ : S.X => (0 : ℝ)) := by funext x; ring
      rw [h2]
      simp [hε_nn]
  J₀ := -1
  J₀_ne_zero := by norm_num

/-- **Mean-zero of the linear Auto-DML moment at the truth.**
Specialises `linRieszScore_meanZero`. -/
theorem linAuto_meanZero
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (S : LinRegFnSys)
    (rep : Causalean.Estimation.OrthogonalMoments.RieszRepresentation
              S.H_γ S.γ_target (L_of_m S) S.P_X)
    (ε : ℝ) (hε_nn : 0 ≤ ε)
    (h_score_meas : ∀ η : linAutoNuisance S, ∀ θ : ℝ,
      Measurable (fun z => linRieszScore S η.1 η.2 θ z))
    (h_α₀_resid_int :
      Integrable
        (fun z => rep.α₀ (S.proj_X z) *
          (S.Y_obs z - S.γ_target S.g₀ (S.proj_X z))) S.P_Z) :
    MeanZero (linAutoGeneralMoment μ S rep ε hε_nn h_score_meas) := by
  unfold MeanZero linAutoGeneralMoment
  exact linRieszScore_meanZero S rep h_α₀_resid_int

/-- **Per-η integrability bundle for the linear Auto-DML bilinear remainder.**

Names the conjunction of finite-moment hypotheses required by
`rieszScore_bilinearRem` so callers can see the exact API shape. -/
private def linAuto_int_pred (S : LinRegFnSys)
    (rep : Causalean.Estimation.OrthogonalMoments.RieszRepresentation
              S.H_γ S.γ_target (L_of_m S) S.P_X)
    (η : linAutoNuisance S) : Prop :=
  Integrable (fun z =>
      η.2 (S.proj_X z) *
        (S.Y_obs z - S.γ_target S.g₀ (S.proj_X z))) S.P_Z ∧
  Integrable (fun z =>
      η.2 (S.proj_X z) * S.γ_target η.1 (S.proj_X z)) S.P_Z ∧
  Integrable (fun z =>
      η.2 (S.proj_X z) * S.γ_target S.g₀ (S.proj_X z)) S.P_Z ∧
  Integrable (fun x => rep.α₀ x * S.γ_target η.1 x) S.P_X ∧
  Integrable (fun x => rep.α₀ x * S.γ_target S.g₀ x) S.P_X ∧
  Integrable η.2 S.P_X ∧
  Integrable (S.γ_target η.1) S.P_X ∧
  Integrable (S.γ_target S.g₀) S.P_X ∧
  Integrable
    (fun z => rep.α₀ (S.proj_X z) *
      (S.Y_obs z - S.γ_target S.g₀ (S.proj_X z))) S.P_Z ∧
  (∫ z, η.2 (S.proj_X z) *
          (S.Y_obs z - S.γ_target S.g₀ (S.proj_X z)) ∂S.P_Z = 0)

/-- **Bilinear remainder bound for the linear Auto-DML moment.**

Uses `rieszScore_bilinearRem` to factor the population orthogonal moment
as `-∫ x, (α - α₀) (γ_target γ - γ_target g₀) dP_X`, then bounds the
absolute value by the product of L²(P_X) norms via Cauchy–Schwarz. -/
theorem linAuto_bilinearRem
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (S : LinRegFnSys)
    (rep : Causalean.Estimation.OrthogonalMoments.RieszRepresentation
              S.H_γ S.γ_target (L_of_m S) S.P_X)
    (ε : ℝ) (hε_nn : 0 ≤ ε)
    (h_score_meas : ∀ η : linAutoNuisance S, ∀ θ : ℝ,
      Measurable (fun z => linRieszScore S η.1 η.2 θ z)) :
    ∃ C : ℝ, ∀ η ∈ (linAutoGeneralMoment μ S rep ε hε_nn h_score_meas).H_ε,
      linAuto_int_pred S rep η →
      MemLp (fun x => S.γ_target η.1 x - S.γ_target S.g₀ x) 2 S.P_X →
      MemLp (fun x => η.2 x - rep.α₀ x) 2 S.P_X →
      |∫ z, (linAutoGeneralMoment μ S rep ε hε_nn h_score_meas).m η z
              (linAutoGeneralMoment μ S rep ε hε_nn h_score_meas).θ₀ ∂S.P_Z|
        ≤ C *
          (((linAutoGeneralMoment μ S rep ε hε_nn h_score_meas).ρ₁ η
              (linAutoGeneralMoment μ S rep ε hε_nn h_score_meas).η₀ : NNReal) : ℝ) *
          (((linAutoGeneralMoment μ S rep ε hε_nn h_score_meas).ρ₂ η
              (linAutoGeneralMoment μ S rep ε hε_nn h_score_meas).η₀ : NNReal) : ℝ) := by
  refine ⟨1, ?_⟩
  intro η _ h_int hγ hα
  rcases h_int with
    ⟨h_int_resid_α, h_int_αγ, h_int_αγ₀, h_int_α₀γ, h_int_α₀γ₀, h_int_α,
      h_int_γ, h_int_γ₀, h_int_resid_α₀, h_orthog_α⟩
  let dα : S.X → ℝ := fun x => η.2 x - rep.α₀ x
  let dγ : S.X → ℝ := fun x => S.γ_target η.1 x - S.γ_target S.g₀ x
  have h_orthog_α₀ :
      ∫ z, rep.α₀ (S.proj_X z) * (S.Y_obs z - S.γ_target S.g₀ (S.proj_X z))
        ∂S.P_Z = 0 :=
    S.regression_resid_orthog rep.α₀ rep.α₀_meas h_int_resid_α₀
  have hrem_sub :
      (∫ z, linRieszScore S η.1 η.2 (L_of_m S S.g₀) z ∂S.P_Z)
        - (∫ z, linRieszScore S S.g₀ rep.α₀ (L_of_m S S.g₀) z ∂S.P_Z)
        = -∫ x, dα x * dγ x ∂S.P_X := by
    unfold linRieszScore dα dγ
    exact Causalean.Estimation.OrthogonalMoments.rieszScore_bilinearRem rep S.g₀
      η.1 η.2 S.proj_X S.Y_obs S.pushforward S.proj_X_meas h_orthog_α₀ h_orthog_α
      h_int_resid_α h_int_αγ h_int_αγ₀ h_int_α₀γ h_int_α₀γ₀ h_int_α h_int_γ
      h_int_γ₀
  have htruth : ∫ z, linRieszScore S S.g₀ rep.α₀ (L_of_m S S.g₀) z ∂S.P_Z = 0 :=
    linRieszScore_meanZero S rep h_int_resid_α₀
  have hrem : ∫ z, linRieszScore S η.1 η.2 (L_of_m S S.g₀) z ∂S.P_Z
      = -∫ x, dα x * dγ x ∂S.P_X := by
    simpa [htruth] using hrem_sub
  have h_abs_rewrite :
      |∫ z, (linAutoGeneralMoment μ S rep ε hε_nn h_score_meas).m η z
        (linAutoGeneralMoment μ S rep ε hε_nn h_score_meas).θ₀ ∂S.P_Z|
        = |∫ x, dα x * dγ x ∂S.P_X| := by
    rw [show (∫ z, (linAutoGeneralMoment μ S rep ε hε_nn h_score_meas).m η z
        (linAutoGeneralMoment μ S rep ε hε_nn h_score_meas).θ₀ ∂S.P_Z)
        = ∫ z, linRieszScore S η.1 η.2 (L_of_m S S.g₀) z ∂S.P_Z by rfl]
    rw [hrem, abs_neg]
  have h_abs_int : |∫ x, dα x * dγ x ∂S.P_X| ≤ ∫ x, |dα x * dγ x| ∂S.P_X :=
    MeasureTheory.abs_integral_le_integral_abs
  have hcs : ∫ x, |dα x * dγ x| ∂S.P_X
      ≤ (eLpNorm dα 2 S.P_X).toReal * (eLpNorm dγ 2 S.P_X).toReal := by
    simpa [dα, dγ, abs_mul] using
      (integral_abs_mul_le_eLpNorm_mul_eLpNorm (ν := S.P_X) (f := dα) (g := dγ)
        hα hγ)
  have hfin :
      (eLpNorm dα 2 S.P_X).toReal * (eLpNorm dγ 2 S.P_X).toReal
        = 1 * (((linAutoGeneralMoment μ S rep ε hε_nn h_score_meas).ρ₁ η
          (linAutoGeneralMoment μ S rep ε hε_nn h_score_meas).η₀ : NNReal) : ℝ)
          * (((linAutoGeneralMoment μ S rep ε hε_nn h_score_meas).ρ₂ η
            (linAutoGeneralMoment μ S rep ε hε_nn h_score_meas).η₀ : NNReal) : ℝ) := by
    simp [linAutoGeneralMoment, dα, dγ, mul_comm]
  exact h_abs_rewrite.trans_le ((h_abs_int.trans hcs).trans (le_of_eq hfin))

/-- **One-shot linear Auto-DML estimator.**

Built as a `dmlChernozhukovEstimator` over the `linAutoGeneralMoment`
instance.  Equivalently:
`θ̂_n = (1/|B(n)|) Σ_{i ∈ B(n)} [m_lin(Z_i; ĝ_n) + α̂_n(X_i)(Y_i - ĝ_n(X_i))]`. -/
noncomputable def linAutoDMLEstimator
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (S : LinRegFnSys)
    (rep : Causalean.Estimation.OrthogonalMoments.RieszRepresentation
              S.H_γ S.γ_target (L_of_m S) S.P_X)
    (ε : ℝ) (hε_nn : 0 ≤ ε)
    (h_score_meas : ∀ η : linAutoNuisance S, ∀ θ : ℝ,
      Measurable (fun z => linRieszScore S η.1 η.2 θ z))
    (sample : IIDSample Ω S.Z μ S.P_Z)
    (split : OneShotSplit sample)
    (η_hat : ℕ → Ω → linAutoNuisance S) :
    ℕ → Ω → ℝ :=
  Causalean.Estimation.OrthogonalMoments.dmlChernozhukovEstimator
    (linAutoGeneralMoment μ S rep ε hε_nn h_score_meas) sample split η_hat

/-- **Linear Auto-DML asymptotic-linearity wrapper.**

This theorem applies the abstract Chernozhukov DML asymptotic-linearity result
to the linear automatic-debiasing moment after the caller supplies the
mean-zero condition, the per-estimator bilinear remainder bound, and the
standard score-difference, individual-rate, and product-rate hypotheses.
Its conclusion is asymptotic linearity at the target value with the influence
function given by the baseline linear Riesz score multiplied by the inverse
Jacobian factor. -/
theorem linAutoDML_asymptoticLinear
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [StandardBorelSpace Ω] [IsFiniteMeasure μ] [IsProbabilityMeasure μ]
    (S : LinRegFnSys)
    (rep : Causalean.Estimation.OrthogonalMoments.RieszRepresentation
              S.H_γ S.γ_target (L_of_m S) S.P_X)
    (ε : ℝ) (hε_nn : 0 ≤ ε)
    (h_score_meas : ∀ η : linAutoNuisance S, ∀ θ : ℝ,
      Measurable (fun z => linRieszScore S η.1 η.2 θ z))
    (sample : IIDSample Ω S.Z μ S.P_Z)
    (split : OneShotSplit sample)
    {c : ℝ} (hc_pos : 0 < c)
    (h_split_rate :
      Tendsto (fun n => ((split.foldB n).card : ℝ) / n) atTop (𝓝 c))
    (η_hat : ℕ → Ω → linAutoNuisance S)
    (hMZ : MeanZero (linAutoGeneralMoment μ S rep ε hε_nn h_score_meas))
    (hFV :
      Integrable
        (fun z => (linRieszScore S S.g₀ rep.α₀ (L_of_m S S.g₀) z) ^ 2) S.P_Z)
    {Crem : ℝ}
    (hBR_at :
      ∀ n ω,
        |∫ z, (linAutoGeneralMoment μ S rep ε hε_nn h_score_meas).m (η_hat n ω) z
                (linAutoGeneralMoment μ S rep ε hε_nn h_score_meas).θ₀ ∂S.P_Z| ≤
          Crem *
            (((linAutoGeneralMoment μ S rep ε hε_nn h_score_meas).ρ₁
                (η_hat n ω) (linAutoGeneralMoment μ S rep ε hε_nn h_score_meas).η₀ : NNReal) : ℝ) *
            (((linAutoGeneralMoment μ S rep ε hε_nn h_score_meas).ρ₂
                (η_hat n ω) (linAutoGeneralMoment μ S rep ε hε_nn h_score_meas).η₀ : NNReal) : ℝ))
    (h_m_meas :
      ∀ n, Measurable (fun (p : Ω × S.Z) =>
        (linAutoGeneralMoment μ S rep ε hε_nn h_score_meas).m (η_hat n p.1) p.2
          (linAutoGeneralMoment μ S rep ε hε_nn h_score_meas).θ₀))
    (h_m_foldA :
      ∀ n,
        Measurable[MeasurableSpace.comap
          (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance]
          (fun ω z => (linAutoGeneralMoment μ S rep ε hε_nn h_score_meas).m (η_hat n ω) z
            (linAutoGeneralMoment μ S rep ε hε_nn h_score_meas).θ₀))
    (h_m_foldA_uncurry :
      ∀ n,
        Measurable[(MeasurableSpace.comap
            (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance).prod
          (inferInstance : MeasurableSpace S.Z)]
          (fun (p : Ω × S.Z) =>
            (linAutoGeneralMoment μ S rep ε hε_nn h_score_meas).m (η_hat n p.1) p.2
              (linAutoGeneralMoment μ S rep ε hε_nn h_score_meas).θ₀))
    (h_m_int : ∀ n ω,
      Integrable (fun z =>
        (linAutoGeneralMoment μ S rep ε hε_nn h_score_meas).m (η_hat n ω) z
          (linAutoGeneralMoment μ S rep ε hε_nn h_score_meas).θ₀) S.P_Z)
    (h_m_sq_int : ∀ n ω,
      Integrable (fun z =>
        ((linAutoGeneralMoment μ S rep ε hε_nn h_score_meas).m (η_hat n ω) z
          (linAutoGeneralMoment μ S rep ε hε_nn h_score_meas).θ₀) ^ 2) S.P_Z)
    (h_score_diff_rate :
      IsLittleOp
        (fun n ω =>
          (eLpNorm
            (fun z =>
              (linAutoGeneralMoment μ S rep ε hε_nn h_score_meas).m (η_hat n ω) z
                  (linAutoGeneralMoment μ S rep ε hε_nn h_score_meas).θ₀ -
                (linAutoGeneralMoment μ S rep ε hε_nn h_score_meas).m
                  (linAutoGeneralMoment μ S rep ε hε_nn h_score_meas).η₀ z
                  (linAutoGeneralMoment μ S rep ε hε_nn h_score_meas).θ₀)
            2 S.P_Z).toReal)
        (fun _ => (1 : ℝ)) μ)
    (h_product_rate :
      IsLittleOp
        (fun n ω =>
          (((linAutoGeneralMoment μ S rep ε hε_nn h_score_meas).ρ₁
              (η_hat n ω) (linAutoGeneralMoment μ S rep ε hε_nn h_score_meas).η₀ : NNReal) : ℝ) *
            (((linAutoGeneralMoment μ S rep ε hε_nn h_score_meas).ρ₂
                (η_hat n ω) (linAutoGeneralMoment μ S rep ε hε_nn h_score_meas).η₀ : NNReal) : ℝ))
        (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) μ) :
    IsAsymLinear
      (linAutoDMLEstimator S rep ε hε_nn h_score_meas sample split η_hat)
      (L_of_m S S.g₀)
      (fun z => -(linAutoGeneralMoment μ S rep ε hε_nn h_score_meas).J₀_inv *
                linRieszScore S S.g₀ rep.α₀ (L_of_m S S.g₀) z)
      sample
      split.foldB := by
  unfold linAutoDMLEstimator
  simpa [linAutoGeneralMoment] using
    (Causalean.Estimation.OrthogonalMoments.dml_chernozhukov_asymptoticLinear
      (linAutoGeneralMoment μ S rep ε hε_nn h_score_meas)
      hMZ hFV
      sample split hc_pos h_split_rate
      η_hat (Crem := Crem) hBR_at
      h_m_meas h_m_foldA h_m_foldA_uncurry h_m_int h_m_sq_int
      h_score_diff_rate h_product_rate)

end Causalean.Estimation.OrthogonalMoments.AutoDebias
