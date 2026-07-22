/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# AIPW instance of the abstract `GeneralMoment` framework — ATT version

Instantiates `Causalean/Estimation/OrthogonalMoments/MomentFunctional.lean` and friends
with the AIPW back-door **ATT** moment, and rebuilds the ATT AIPW
asymptotic-linearity theorem on top of the abstract
`dml_chernozhukov_asymptoticLinear`.

* `attGeneralMoment S hη₀_mem hπ_pos` — `GeneralMoment` instance.
* `att_meanZero`                            — `MeanZero` for ATT AIPW.
* `att_bilinearRem`                         — `BilinearRemainder` for ATT AIPW.
* `att_dml_isAsymLinear`                    — headline ATT AIPW asymptotic
                                              linearity, via
                                              `dml_chernozhukov_asymptoticLinear`.

Structural deviations from the ATE counterpart in
`Estimation/OrthogonalMoments/AIPWInstance.lean`:

* The bilinear seminorm `ρ₁` is the L²(P_X) norm of the **single** μ-residual
  `Δμ₀ := η.μ₀_fn − η'.μ₀_fn` — there is no sum over treatment arms (the ATT
  AIPW form only uses `μ₀`).
* `ρ₂` is the L²(P_X) norm of `Δe` (same as ATE).
* The Jacobian `J₀ = −π_T` (not `−1`) because the ATT AIPW moment is
  rescaled: `m_AIPW^ATT(η, z, θ) = ψ̃(η, z) − A·θ`, and
  `∂_θ ∫ m_AIPW^ATT(η₀, z, θ) dP_Z = −∫ A dP_Z = −π_T`.
* `η₀_mem` records the a.e. one-sided-overlap and L²/L∞ gates in `H_ε`.

Since `J₀ = −π_T`, the influence function in the abstract conclusion
`fun z => −J₀_inv · m(η₀, z, θ₀)` is `(1/π_T) · aipwMomentATTFunctional S.η₀ z S.θ₀`,
which equals `S.ψ_ATT z` modulo a constant `θ₀` shift on the `−A·θ` slot.

References:
* NL doc `lem:est-aipw-mean-zero-att`, `lem:est-aipw-finite-var-att`,
  `thm:est-dml-att-al`.
* Plan §11 (ATTInstance), §12 (DML), §13 (InfluenceFunction).
-/

import Causalean.Estimation.OrthogonalMoments.DMLChernozhukov
import Causalean.Estimation.ATT.Remainder.Bound
import Causalean.Estimation.ATT.Score.AIPWMoment
import Causalean.Estimation.ATT.Score.FiniteVar
import Causalean.Estimation.ATT.Score.AIPWScoreL2
import Causalean.Estimation.ATT.Score.MeanZero

/-!
Instantiates the abstract orthogonal-moment DML theorem for the average
treatment effect on the treated. It connects the ATT AIPW score, remainder
identity, score-continuity bounds, and sample-splitting assumptions to
asymptotic linearity.

The main declarations are `attGeneralMoment`, the `MeanZero` bridge
`att_meanZero`, the bilinear remainder bridge `att_bilinearRem`, and the
headline abstract asymptotic-linearity theorem `att_dml_isAsymLinear`.  This
file is the ATT specialization of the general orthogonal-moment interface; the
user-facing estimator wrapper is in `Estimation/ATT/DML.lean`.
-/

namespace Causalean
namespace Estimation
namespace ATT

open MeasureTheory ProbabilityTheory Filter Topology Causalean.PO Causalean.Stat
open Causalean.Estimation.OrthogonalMoments
open TreatedEstimationSystem

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
  [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]

/-- ATT AIPW instance of the abstract `GeneralMoment`.

The bilinear seminorms are the L²(P_X) norms of the `μ₀_fn` and `e_fn`
differences.  Only the control-arm μ-residual appears (no sum over arms),
matching the single cross-product produced by `aipw_remainder_bound_ATT`.

The Jacobian `J₀ = −π_T` is taken as a parameter (via the positivity
hypothesis `hπ_pos`) because the ATT AIPW moment carries an `A·θ` term
rather than a plain `θ` term, so the population Jacobian is the marginal
treatment probability rather than `±1`. -/
noncomputable def attGeneralMoment
    (S : TreatedEstimationSystem P γ) {ε : ℝ}
    (hη₀_mem : S.η₀ ∈ H_ε S ε)
    (hπ_pos : 0 < S.π_val) :
    GeneralMoment P.Ω P.μ (γ × Bool × ℝ) S.P_Z (TreatedNuisanceVec γ) where
  m       := fun η z θ => aipwMomentATTFunctional η z θ
  η₀      := S.η₀
  θ₀      := S.θ₀
  H_ε     := H_ε S ε
  ρ₁      := fun η η' =>
    ⟨(eLpNorm (fun x => η.μ₀_fn x - η'.μ₀_fn x) 2 S.P_X).toReal,
     ENNReal.toReal_nonneg⟩
  ρ₂      := fun η η' =>
    ⟨(eLpNorm (fun x => η.e_fn x - η'.e_fn x) 2 S.P_X).toReal,
     ENNReal.toReal_nonneg⟩
  m_meas  := fun η θ =>
    TreatedEstimationSystem.measurable_aipwMomentATTFunctional η θ
  η₀_mem  := hη₀_mem
  -- ATT AIPW is a linear-in-`θ` score `m_AIPW^ATT(η, z, θ) = ψ̃(η, z) − A·θ`,
  -- so the population Jacobian is
  -- `J₀ = ∂_θ ∫ m(η₀, z, θ) dP_Z |_{θ=θ₀} = −∫ A dP_Z = −π_T`.
  J₀         := -S.π_val
  J₀_ne_zero := by
    intro h
    have : S.π_val = 0 := by linarith [show -S.π_val = 0 from h]
    linarith

/-- ATT AIPW satisfies `MeanZero`.  Direct repackaging of
`aipw_mean_zero_ATT` from `Estimation/ATT/Score/MeanZero.lean`. -/
theorem att_meanZero
    (S : TreatedEstimationSystem P γ) {ε : ℝ}
    (hη₀_mem : S.η₀ ∈ H_ε S ε)
    (_h_overlap : S.OneSidedOverlap ε)
    (hA : S.toPOBackdoorSystem.ATTAssumptions)
    (hπ_pos : 0 < S.π_val)
    (_h_y2 : Integrable (fun ω => (S.toPOBackdoorSystem.factualY ω) ^ 2) P.μ)
    (_h_y0_2 : Integrable (fun ω => (S.toPOBackdoorSystem.YofD false ω) ^ 2) P.μ)
    (hIPW : Integrable (fun ω =>
        (1 - S.toPOBackdoorSystem.dVar.indicator true ω)
          * (S.toPOBackdoorSystem.propScore true ω
              / (1 - S.toPOBackdoorSystem.propScore true ω))
          * (S.toPOBackdoorSystem.factualY ω
              - S.toPOBackdoorSystem.adjustedCE false ω)) P.μ) :
    MeanZero (attGeneralMoment S hη₀_mem hπ_pos) := by
  unfold MeanZero attGeneralMoment
  exact aipw_mean_zero_ATT S hA hπ_pos hIPW

/-- ATT AIPW satisfies `BilinearRemainder` with constant `aipw_rem_const_ATT ε`.

Direct corollary of `aipw_remainder_bound_ATT` from
`Estimation/ATT/Remainder/Bound.lean`: the ATT remainder is a single L²(P_X)
cross-product `‖Δμ₀‖ · ‖Δe‖`, so no Σ-over-arms shape conversion is needed
(unlike the ATE counterpart). -/
theorem att_bilinearRem
    (S : TreatedEstimationSystem P γ) {ε : ℝ}
    (hη₀_mem : S.η₀ ∈ H_ε S ε)
    (h_overlap : S.OneSidedOverlap ε)
    (hA : S.toPOBackdoorSystem.ATTAssumptions)
    (hπ_pos : 0 < S.π_val)
    (h_y2 : Integrable (fun ω => (S.toPOBackdoorSystem.factualY ω) ^ 2) P.μ)
    (h_y0_2 : Integrable (fun ω => (S.toPOBackdoorSystem.YofD false ω) ^ 2) P.μ)
    (h_L2 : ∀ η ∈ H_ε S ε,
      MemLp (fun x => η.μ₀_fn x - S.μ₀_val x) 2 S.P_X ∧
      MemLp (fun x => η.e_fn x - S.e_val x) 2 S.P_X)
    (h_IPW : ∀ η ∈ H_ε S ε, Integrable (fun z =>
        (1 - Causalean.Estimation.ATE.BackdoorEstimationSystem.indA z)
          * (η.e_fn (Causalean.Estimation.ATE.BackdoorEstimationSystem.projX z)
              / (1 - η.e_fn
                  (Causalean.Estimation.ATE.BackdoorEstimationSystem.projX z)))
          * (Causalean.Estimation.ATE.BackdoorEstimationSystem.projY z
              - η.μ₀_fn
                  (Causalean.Estimation.ATE.BackdoorEstimationSystem.projX z)))
        S.P_Z) :
    ∃ C, BilinearRemainder (attGeneralMoment S hη₀_mem hπ_pos) C := by
  refine ⟨aipw_rem_const_ATT ε, ?_⟩
  intro η hη
  obtain ⟨hΔμ₀, hΔe⟩ := h_L2 η hη
  have h := aipw_remainder_bound_ATT S h_overlap hA hπ_pos h_y2 h_y0_2
    η hη hΔμ₀ hΔe (h_IPW η hη)
  change |∫ z, aipwMomentATTFunctional η z S.θ₀ ∂(S.P_Z)| ≤
      aipw_rem_const_ATT ε *
        (eLpNorm (fun x => η.μ₀_fn x - S.μ₀_val x) 2 S.P_X).toReal *
        (eLpNorm (fun x => η.e_fn x - S.e_val x) 2 S.P_X).toReal
  exact h

/-- **Headline ATT AIPW DML asymptotic-linearity theorem**, derived from the
abstract `dml_chernozhukov_asymptoticLinear` in
`Estimation/OrthogonalMoments/DMLChernozhukov.lean`.

Assuming the one-sided ATT back-door assumption bundle, a.e. nuisance-class
membership in `H_ε`, marginal treatment positivity, second
moments, sample-split measurability, and the stated nuisance rates, the ATT
AIPW one-step estimator is asymptotically linear in the abstract Chernozhukov
moment framework.

**Conclusion (Chernozhukov form):** the Chernozhukov one-step estimator
`θ̂_n = θ₀ − J₀⁻¹ · Pₙ m(η̂, ·, θ₀)` for `M = attGeneralMoment` is
asymptotically linear at `S.θ₀` with influence function

  `ψ(z) = −M.J₀_inv · M.m M.η₀ z M.θ₀
        = (1/π_T) · aipwMomentATTFunctional S.η₀ z S.θ₀`

(using `J₀ = −π_T`, so `J₀_inv = −1/π_T`).  Modulo the linear-in-`θ` shift on
the `−A·θ` slot of the ATT moment, this matches the standard ATT influence
function `ψ_ATT` from `AIPWMoment.lean`.

Composes the abstract theorem with `att_meanZero`, `aipw_finite_var_ATT`,
and a per-η̂_n bilinear remainder bound built directly from
`aipw_remainder_bound_ATT` (the ATT analogue of the per-η̂ route used in
`aipw_dml_isAsymLinear`).  The score-difference rate is supplied by
`aipw_score_diff_isLittleOp_one_ATT` from `Estimation/ATT/Score/AIPWScoreL2.lean`. -/
theorem att_dml_isAsymLinear
    (S : TreatedEstimationSystem P γ) {ε : ℝ}
    (hη₀_mem : S.η₀ ∈ H_ε S ε)
    (h_e_lb : ∀ x, 0 ≤ S.e_val x)
    (h_overlap : S.OneSidedOverlap ε)
    (hA : S.toPOBackdoorSystem.ATTAssumptions)
    (hπ_pos : 0 < S.π_val)
    (h_y2 : Integrable (fun ω => (S.toPOBackdoorSystem.factualY ω) ^ 2) P.μ)
    (h_y0_2 : Integrable (fun ω => (S.toPOBackdoorSystem.YofD false ω) ^ 2) P.μ)
    (hIPW : Integrable (fun ω =>
        (1 - S.toPOBackdoorSystem.dVar.indicator true ω)
          * (S.toPOBackdoorSystem.propScore true ω
              / (1 - S.toPOBackdoorSystem.propScore true ω))
          * (S.toPOBackdoorSystem.factualY ω
              - S.toPOBackdoorSystem.adjustedCE false ω)) P.μ)
    (sample : IIDSample P.Ω (γ × Bool × ℝ) P.μ S.P_Z)
    (split : OneShotSplit sample)
    {c : ℝ} (hc_pos : 0 < c) (_hc_lt : c < 1)
    (h_split_rate :
      Tendsto (fun n => ((split.foldB n).card : ℝ) / n) atTop (𝓝 c))
    (η_hat : ℕ → P.Ω → TreatedNuisanceVec γ)
    (h_in_Hε : ∀ n ω, η_hat n ω ∈ H_ε S ε)
    (h_e_lb_hat : ∀ n ω x, 0 ≤ (η_hat n ω).e_fn x)
    (h_mu_diff_memLp :
      ∀ n ω, MemLp
        (fun x => (η_hat n ω).μ₀_fn x - S.μ₀_val x) 2 S.P_X)
    (h_e_diff_memLp :
      ∀ n ω, MemLp
        (fun x => (η_hat n ω).e_fn x - S.e_val x) 2 S.P_X)
    (h_IPW_at :
      ∀ n ω, Integrable (fun z =>
        (1 - Causalean.Estimation.ATE.BackdoorEstimationSystem.indA z)
          * ((η_hat n ω).e_fn
                (Causalean.Estimation.ATE.BackdoorEstimationSystem.projX z)
              / (1 - (η_hat n ω).e_fn
                  (Causalean.Estimation.ATE.BackdoorEstimationSystem.projX z)))
          * (Causalean.Estimation.ATE.BackdoorEstimationSystem.projY z
              - (η_hat n ω).μ₀_fn
                  (Causalean.Estimation.ATE.BackdoorEstimationSystem.projX z)))
        S.P_Z)
    (h_m_meas :
      ∀ n, Measurable (fun (p : P.Ω × (γ × Bool × ℝ)) =>
        aipwMomentATTFunctional (η_hat n p.1) p.2 S.θ₀))
    (h_m_foldA :
      ∀ n,
        Measurable[MeasurableSpace.comap
          (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance]
          (fun ω z => aipwMomentATTFunctional (η_hat n ω) z S.θ₀))
    (h_m_foldA_uncurry :
      ∀ n,
        Measurable[(MeasurableSpace.comap
            (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance).prod
          (inferInstance : MeasurableSpace (γ × Bool × ℝ))]
          (fun (p : P.Ω × (γ × Bool × ℝ)) =>
            aipwMomentATTFunctional (η_hat n p.1) p.2 S.θ₀))
    (h_m_int : ∀ n ω,
      Integrable (fun z => aipwMomentATTFunctional (η_hat n ω) z S.θ₀) S.P_Z)
    (h_m_sq_int : ∀ n ω,
      Integrable (fun z => (aipwMomentATTFunctional (η_hat n ω) z S.θ₀) ^ 2) S.P_Z)
    (h_indiv_rate_ρ₁ :
      IsLittleOp
        (fun n ω =>
          (((attGeneralMoment S hη₀_mem hπ_pos).ρ₁
              (η_hat n ω) S.η₀ : NNReal) : ℝ))
        (fun _ => (1 : ℝ)) P.μ)
    (h_indiv_rate_ρ₂ :
      IsLittleOp
        (fun n ω =>
          (((attGeneralMoment S hη₀_mem hπ_pos).ρ₂
              (η_hat n ω) S.η₀ : NNReal) : ℝ))
        (fun _ => (1 : ℝ)) P.μ)
    (h_product_rate :
      IsLittleOp
        (fun n ω =>
          (((attGeneralMoment S hη₀_mem hπ_pos).ρ₁
              (η_hat n ω) S.η₀ : NNReal) : ℝ) *
            (((attGeneralMoment S hη₀_mem hπ_pos).ρ₂
                (η_hat n ω) S.η₀ : NNReal) : ℝ))
        (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) P.μ) :
    IsAsymLinear
      (Causalean.Estimation.OrthogonalMoments.dmlChernozhukovEstimator
        (attGeneralMoment S hη₀_mem hπ_pos) sample split η_hat)
      S.θ₀
      (fun z => -(attGeneralMoment S hη₀_mem hπ_pos).J₀_inv *
                aipwMomentATTFunctional S.η₀ z S.θ₀)
      sample
      split.foldB := by
  have hMZ := att_meanZero S hη₀_mem h_overlap hA hπ_pos h_y2 h_y0_2 hIPW
  have hFV :
      Integrable (fun z =>
        ((attGeneralMoment S hη₀_mem hπ_pos).m
          (attGeneralMoment S hη₀_mem hπ_pos).η₀ z
          (attGeneralMoment S hη₀_mem hπ_pos).θ₀) ^ 2) S.P_Z := by
    simpa [attGeneralMoment, ψ_ATT, η₀, aipwMomentATTFunctional] using
      aipw_finite_var_ATT S h_overlap hA h_y2 h_y0_2
  have hBR_at :
      ∀ n ω,
        |∫ z, (attGeneralMoment S hη₀_mem hπ_pos).m (η_hat n ω) z
                (attGeneralMoment S hη₀_mem hπ_pos).θ₀ ∂S.P_Z| ≤
          aipw_rem_const_ATT ε *
            (((attGeneralMoment S hη₀_mem hπ_pos).ρ₁
                (η_hat n ω) (attGeneralMoment S hη₀_mem hπ_pos).η₀ : NNReal) : ℝ) *
            (((attGeneralMoment S hη₀_mem hπ_pos).ρ₂
                (η_hat n ω) (attGeneralMoment S hη₀_mem hπ_pos).η₀ : NNReal) : ℝ) := by
    intro n ω
    have h := aipw_remainder_bound_ATT S h_overlap hA hπ_pos h_y2 h_y0_2
      (η_hat n ω) (h_in_Hε n ω) (h_mu_diff_memLp n ω) (h_e_diff_memLp n ω)
      (h_IPW_at n ω)
    change |∫ z, aipwMomentATTFunctional (η_hat n ω) z S.θ₀ ∂(S.P_Z)| ≤
        aipw_rem_const_ATT ε *
          (eLpNorm (fun x => (η_hat n ω).μ₀_fn x - S.μ₀_val x) 2 S.P_X).toReal *
          (eLpNorm (fun x => (η_hat n ω).e_fn x - S.e_val x) 2 S.P_X).toReal
    exact h
  have h_mu_rate :
      IsLittleOp
        (fun n ω =>
          (eLpNorm (fun x => (η_hat n ω).μ₀_fn x - S.μ₀_val x) 2 S.P_X).toReal)
        (fun _ => (1 : ℝ)) P.μ := by
    simpa [attGeneralMoment, η₀] using h_indiv_rate_ρ₁
  have h_e_rate :
      IsLittleOp
        (fun n ω =>
          (eLpNorm (fun x => (η_hat n ω).e_fn x - S.e_val x) 2 S.P_X).toReal)
        (fun _ => (1 : ℝ)) P.μ := by
    simpa [attGeneralMoment, η₀] using h_indiv_rate_ρ₂
  have h_score_diff_rate :
      IsLittleOp
        (fun n ω =>
          (eLpNorm
            (fun z =>
              (attGeneralMoment S hη₀_mem hπ_pos).m (η_hat n ω) z
                  (attGeneralMoment S hη₀_mem hπ_pos).θ₀ -
                (attGeneralMoment S hη₀_mem hπ_pos).m
                  (attGeneralMoment S hη₀_mem hπ_pos).η₀ z
                  (attGeneralMoment S hη₀_mem hπ_pos).θ₀)
            2 S.P_Z).toReal)
        (fun _ => (1 : ℝ)) P.μ := by
    simpa [attGeneralMoment] using
      aipw_score_diff_isLittleOp_one_ATT S h_overlap hη₀_mem h_e_lb hA
        h_y2 h_y0_2 η_hat h_in_Hε h_e_lb_hat h_mu_diff_memLp h_e_diff_memLp
        h_mu_rate h_e_rate
  simpa [attGeneralMoment] using
    (Causalean.Estimation.OrthogonalMoments.dml_chernozhukov_asymptoticLinear
      (attGeneralMoment S hη₀_mem hπ_pos)
      hMZ hFV
      sample split hc_pos h_split_rate
      η_hat (Crem := aipw_rem_const_ATT ε) hBR_at
      h_m_meas h_m_foldA h_m_foldA_uncurry h_m_int h_m_sq_int
      h_score_diff_rate h_product_rate)

end ATT
end Estimation
end Causalean
