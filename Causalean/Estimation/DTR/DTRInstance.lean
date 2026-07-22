/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Sequential DR (DTR, n = 2) instance of the abstract `GeneralMoment`

Instantiates `Causalean/Estimation/OrthogonalMoments/MomentFunctional.lean` and friends
with the sequential DR (DTR) moment, and rebuilds the DTR
asymptotic-linearity theorem on top of the abstract Chernozhukov-form DML
theorem.

* `seqDRGeneralMoment S h_e_pointwise`  — `GeneralMoment` instance.
* `seqDR_meanZero`                      — `MeanZero` for sequential DR.
* `seqDR_bilinearRem`                   — `BilinearRemainder` for sequential DR.
* `seqDR_dml_isAsymLinear`              — headline DTR asymptotic linearity,
                                          via `dml_chernozhukov_asymptoticLinear`.

Stagewise version of `Estimation/OrthogonalMoments/AIPWInstance.lean`.  Key differences
to the ATE instance:

* The data tuple is `γ 0 × δ × γ 1 × δ × ℝ` (cf. `Setup.lean`), with the
  truth nuisance carrying four functions `(μ₀_val, e₀_val, μ₁_val, e₁_val)`.
* The bilinear seminorms `ρ₁, ρ₂` aggregate the two stages of `μ`/`e`:

  `ρ₁(η, η') := ‖Δμ₀‖_{L²(P_H₀)} + ‖Δμ₁‖_{L²(P_H₁)}`,
  `ρ₂(η, η') := ‖Δe₀‖_{L²(P_H₀)} + ‖Δe₁‖_{L²(P_H₁)}`.

  This matches the `(Σ ‖Δμ_k‖) · (Σ ‖Δe_k‖)` factor produced by
  `seqDR_remainder_bound`.
* The Jacobian `J₀ = -1` because the score is linear: `m_seqDR(η, z, θ) =
  ψ_seqDR(η, z) − θ`.
-/

import Causalean.Estimation.DTR.MeanZero
import Causalean.Estimation.DTR.FiniteVar
import Causalean.Estimation.DTR.RemainderBound
import Causalean.Estimation.DTR.ScoreL2
import Causalean.Estimation.OrthogonalMoments.AIPWInstance
import Causalean.Estimation.OrthogonalMoments.DMLChernozhukov

/-! # Sequential Doubly Robust Moment Instance

This file instantiates the abstract orthogonal-moment framework with the
two-period sequential doubly robust moment for a dynamic treatment regime. It
records the mean-zero, bilinear-remainder, and asymptotic-linearity ingredients
needed to reuse the general DML theorem. -/

namespace Causalean
namespace Estimation
namespace DTR

open MeasureTheory ProbabilityTheory Filter Topology Causalean.PO Causalean.Stat
open Causalean.Estimation.OrthogonalMoments
open DTREstimationSystem

variable {P : POSystem} {δ : Type} {γ : Fin 2 → Type}
  [MeasurableSpace δ] [MeasurableSingletonClass δ]
  [∀ k, MeasurableSpace (γ k)]
  [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]

/-- Sequential DR (DTR, n = 2) instance of the abstract `GeneralMoment`.

The bilinear seminorms aggregate over the two stages: `ρ₁` sums the
stagewise L²(P_H_k) norms of the outcome-regression differences, `ρ₂` the
stagewise L²(P_H_k) norms of the propensity differences.  This matches the
`(‖Δμ₀‖ + ‖Δμ₁‖) · (‖Δe₀‖ + ‖Δe₁‖)` shape from
`seqDR_remainder_bound`. -/
noncomputable def seqDRGeneralMoment
    (S : DTREstimationSystem P δ γ) {ε : ℝ}
    (h_e_pointwise :
      (∀ s₀, ε ≤ S.e₀_val s₀ ∧ S.e₀_val s₀ ≤ 1 - ε)
        ∧ (∀ h, ε ≤ S.e₁_val h ∧ S.e₁_val h ≤ 1 - ε)) :
    GeneralMoment P.Ω P.μ (γ 0 × δ × γ 1 × δ × ℝ) S.P_Z
      (DTRNuisanceVec₂ δ γ) where
  m       := fun η z θ => S.seqDRMomentFunctional η z θ
  η₀      := S.η₀
  θ₀      := S.θ₀
  H_ε     := DTREstimationSystem.H_ε ε
  ρ₁      := fun η η' =>
    ⟨(eLpNorm (fun s₀ => η.μ₀_fn s₀ - η'.μ₀_fn s₀) 2 S.P_H₀).toReal +
       (eLpNorm (fun h => η.μ₁_fn h - η'.μ₁_fn h) 2 S.P_H₁).toReal,
     by positivity⟩
  ρ₂      := fun η η' =>
    ⟨(eLpNorm (fun s₀ => η.e₀_fn s₀ - η'.e₀_fn s₀) 2 S.P_H₀).toReal +
       (eLpNorm (fun h => η.e₁_fn h - η'.e₁_fn h) 2 S.P_H₁).toReal,
     by positivity⟩
  m_meas  := fun η θ => S.measurable_seqDRMomentFunctional η θ
  η₀_mem  := h_e_pointwise
  -- Sequential DR is a linear score `m_seqDR(η, z, θ) = ψ_seqDR(η, z) − θ`,
  -- so the population Jacobian
  -- `J₀ = ∂_θ ∫ m(η₀, z, θ) dP_Z |_{θ=θ₀} = −1`.
  J₀         := -1
  J₀_ne_zero := by norm_num

/-- Sequential DR (DTR) satisfies `MeanZero`. -/
theorem seqDR_meanZero
    (S : DTREstimationSystem P δ γ) {ε : ℝ}
    (h_e_pointwise :
      (∀ s₀, ε ≤ S.e₀_val s₀ ∧ S.e₀_val s₀ ≤ 1 - ε)
        ∧ (∀ h, ε ≤ S.e₁_val h ∧ S.e₁_val h ≤ 1 - ε))
    (h_overlap : S.StrictOverlap ε)
    (hA : S.toPODTRSystem.Assumptions)
    (h_y2 : Integrable (fun ω => (S.toPODTRSystem.factualY ω) ^ 2) P.μ) :
    MeanZero (seqDRGeneralMoment S h_e_pointwise) := by
  unfold MeanZero seqDRGeneralMoment
  exact seqDR_mean_zero S h_overlap hA h_y2

/-- Sequential DR (DTR) satisfies `BilinearRemainder` with constant
`seqDR_rem_const ε`. -/
theorem seqDR_bilinearRem
    (S : DTREstimationSystem P δ γ) {ε : ℝ}
    (h_e_pointwise :
      (∀ s₀, ε ≤ S.e₀_val s₀ ∧ S.e₀_val s₀ ≤ 1 - ε)
        ∧ (∀ h, ε ≤ S.e₁_val h ∧ S.e₁_val h ≤ 1 - ε))
    (h_overlap : S.StrictOverlap ε)
    (hA : S.toPODTRSystem.Assumptions)
    (h_y2 : Integrable (fun ω => (S.toPODTRSystem.factualY ω) ^ 2) P.μ)
    (h_yd2 : ∀ dbar : Fin 2 → δ,
      Integrable (fun ω => (S.toPODTRSystem.Y_of dbar ω) ^ 2) P.μ)
    (h_L2 : ∀ η ∈ DTREstimationSystem.H_ε (δ := δ) (γ := γ) ε,
      MemLp (fun s₀ => η.μ₀_fn s₀ - S.μ₀_val s₀) 2 S.P_H₀ ∧
      MemLp (fun h => η.μ₁_fn h - S.μ₁_val h) 2 S.P_H₁ ∧
      MemLp (fun s₀ => η.e₀_fn s₀ - S.e₀_val s₀) 2 S.P_H₀ ∧
      MemLp (fun h => η.e₁_fn h - S.e₁_val h) 2 S.P_H₁) :
    ∃ C, BilinearRemainder (seqDRGeneralMoment S h_e_pointwise) C := by
  refine ⟨seqDR_rem_const ε, ?_⟩
  intro η hη
  obtain ⟨hΔμ₀, hΔμ₁, hΔe₀, hΔe₁⟩ := h_L2 η hη
  have h := seqDR_remainder_bound S h_overlap hA h_y2 h_yd2
    η hη hΔμ₀ hΔμ₁ hΔe₀ hΔe₁
  change |∫ z, S.seqDRMomentFunctional η z S.θ₀ ∂(S.P_Z)| ≤
      seqDR_rem_const ε *
        ((eLpNorm (fun s₀ => η.μ₀_fn s₀ - S.μ₀_val s₀) 2 S.P_H₀).toReal +
          (eLpNorm (fun h => η.μ₁_fn h - S.μ₁_val h) 2 S.P_H₁).toReal) *
        ((eLpNorm (fun s₀ => η.e₀_fn s₀ - S.e₀_val s₀) 2 S.P_H₀).toReal +
          (eLpNorm (fun h => η.e₁_fn h - S.e₁_val h) 2 S.P_H₁).toReal)
  exact h

set_option maxHeartbeats 1200000 in
-- The wrapper composes a long hypothesis list (rate translations, score
-- measurability, integrability, two transport equalities) and applies the
-- abstract `dml_chernozhukov_asymptoticLinear`; the resulting elaboration
-- exceeds the default heartbeat budget.  Mirrors ATE/DML.lean.
/-- **Headline sequential DR (DTR) DML asymptotic-linearity theorem**,
derived from the abstract `dml_chernozhukov_asymptoticLinear` in
`Estimation/OrthogonalMoments/DMLChernozhukov.lean`.

**Conclusion (Chernozhukov form).**  The Chernozhukov one-step estimator
`θ̂_n = θ₀ − J₀⁻¹ · Pₙ m(η̂, ·, θ₀) = (1/|B|) Σ ψ_seqDR(η̂, Z_i)` (the
last equality uses `J₀ = −1`, see `seqDRGeneralMoment`) is asymptotically
linear at `S.θ₀` with influence function

  `ψ(z) = −M.J₀_inv · M.m M.η₀ z M.θ₀ = S.seqDRMomentFunctional S.η₀ z S.θ₀`

(again using `J₀_inv = −1`).  This is the standard sequential DR
influence function, mean-zero at the truth.

Composes the abstract theorem with `seqDR_meanZero`, `seqDR_finite_var`,
`seqDR_remainder_bound` (used to construct the per-η̂_n bilinear
remainder bound directly, replacing the ∀-quantified
`seqDR_bilinearRem`), and the DTR-specific score-difference rate from
`seqDR_score_diff_isLittleOp_one`.

The L²-difference hypotheses are required only at the specific learners
`η̂_n n ω` (not over the entire `H_ε ε` ball). -/
theorem seqDR_dml_isAsymLinear
    (S : DTREstimationSystem P δ γ) {ε : ℝ}
    (h_e_pointwise :
      (∀ s₀, ε ≤ S.e₀_val s₀ ∧ S.e₀_val s₀ ≤ 1 - ε)
        ∧ (∀ h, ε ≤ S.e₁_val h ∧ S.e₁_val h ≤ 1 - ε))
    (h_overlap : S.StrictOverlap ε)
    (hA : S.toPODTRSystem.Assumptions)
    (h_y2 : Integrable (fun ω => (S.toPODTRSystem.factualY ω) ^ 2) P.μ)
    (h_yd2 : ∀ dbar : Fin 2 → δ,
      Integrable (fun ω => (S.toPODTRSystem.Y_of dbar ω) ^ 2) P.μ)
    (sample : IIDSample P.Ω (γ 0 × δ × γ 1 × δ × ℝ) P.μ S.P_Z)
    (split : OneShotSplit sample)
    {c : ℝ} (hc_pos : 0 < c) (_hc_lt : c < 1)
    (h_split_rate :
      Tendsto (fun n => ((split.foldB n).card : ℝ) / n) atTop (𝓝 c))
    (η_hat : ℕ → P.Ω → DTRNuisanceVec₂ δ γ)
    (h_in_Hε : ∀ n ω, η_hat n ω ∈ DTREstimationSystem.H_ε ε)
    (h_mu0_diff_memLp : ∀ n ω,
      MemLp (fun s₀ => (η_hat n ω).μ₀_fn s₀ - S.μ₀_val s₀) 2 S.P_H₀)
    (h_mu1_diff_memLp : ∀ n ω,
      MemLp (fun h => (η_hat n ω).μ₁_fn h - S.μ₁_val h) 2 S.P_H₁)
    (h_e0_diff_memLp : ∀ n ω,
      MemLp (fun s₀ => (η_hat n ω).e₀_fn s₀ - S.e₀_val s₀) 2 S.P_H₀)
    (h_e1_diff_memLp : ∀ n ω,
      MemLp (fun h => (η_hat n ω).e₁_fn h - S.e₁_val h) 2 S.P_H₁)
    (h_m_meas :
      ∀ n, Measurable (fun (p : P.Ω × (γ 0 × δ × γ 1 × δ × ℝ)) =>
        S.seqDRMomentFunctional (η_hat n p.1) p.2 S.θ₀))
    (h_m_foldA :
      ∀ n,
        Measurable[MeasurableSpace.comap
          (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance]
          (fun ω z => S.seqDRMomentFunctional (η_hat n ω) z S.θ₀))
    (h_m_foldA_uncurry :
      ∀ n,
        Measurable[(MeasurableSpace.comap
            (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance).prod
          (inferInstance : MeasurableSpace (γ 0 × δ × γ 1 × δ × ℝ))]
          (fun (p : P.Ω × (γ 0 × δ × γ 1 × δ × ℝ)) =>
            S.seqDRMomentFunctional (η_hat n p.1) p.2 S.θ₀))
    (h_m_int : ∀ n ω,
      Integrable (fun z => S.seqDRMomentFunctional (η_hat n ω) z S.θ₀) S.P_Z)
    (h_m_sq_int : ∀ n ω,
      Integrable
        (fun z => (S.seqDRMomentFunctional (η_hat n ω) z S.θ₀) ^ 2) S.P_Z)
    (h_indiv_rate_ρ₁ :
      IsLittleOp
        (fun n ω =>
          (((seqDRGeneralMoment S h_e_pointwise).ρ₁
              (η_hat n ω) S.η₀ : NNReal) : ℝ))
        (fun _ => (1 : ℝ)) P.μ)
    (h_indiv_rate_ρ₂ :
      IsLittleOp
        (fun n ω =>
          (((seqDRGeneralMoment S h_e_pointwise).ρ₂
              (η_hat n ω) S.η₀ : NNReal) : ℝ))
        (fun _ => (1 : ℝ)) P.μ)
    (h_product_rate :
      IsLittleOp
        (fun n ω =>
          (((seqDRGeneralMoment S h_e_pointwise).ρ₁
              (η_hat n ω) S.η₀ : NNReal) : ℝ) *
            (((seqDRGeneralMoment S h_e_pointwise).ρ₂
                (η_hat n ω) S.η₀ : NNReal) : ℝ))
        (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) P.μ) :
    IsAsymLinear
      (Causalean.Estimation.OrthogonalMoments.dmlChernozhukovEstimator
        (seqDRGeneralMoment S h_e_pointwise) sample split η_hat)
      S.θ₀
      (fun z => -(seqDRGeneralMoment S h_e_pointwise).J₀_inv *
                S.seqDRMomentFunctional S.η₀ z S.θ₀)
      sample
      split.foldB := by
  have hMZ := seqDR_meanZero S h_e_pointwise h_overlap hA h_y2
  have hFV :
      Integrable (fun z =>
        ((seqDRGeneralMoment S h_e_pointwise).m
          (seqDRGeneralMoment S h_e_pointwise).η₀ z
          (seqDRGeneralMoment S h_e_pointwise).θ₀) ^ 2) S.P_Z := by
    simpa [seqDRGeneralMoment, DTREstimationSystem.ψ_seqDR,
      DTREstimationSystem.η₀, DTREstimationSystem.seqDRMomentFunctional] using
        seqDR_finite_var S h_overlap hA h_y2 h_yd2
  have hBR_at :
      ∀ n ω,
        |∫ z, (seqDRGeneralMoment S h_e_pointwise).m (η_hat n ω) z
                (seqDRGeneralMoment S h_e_pointwise).θ₀ ∂S.P_Z| ≤
          seqDR_rem_const ε *
            (((seqDRGeneralMoment S h_e_pointwise).ρ₁
                (η_hat n ω) (seqDRGeneralMoment S h_e_pointwise).η₀ : NNReal) : ℝ) *
            (((seqDRGeneralMoment S h_e_pointwise).ρ₂
                (η_hat n ω) (seqDRGeneralMoment S h_e_pointwise).η₀ : NNReal) : ℝ) := by
    intro n ω
    have h := seqDR_remainder_bound S h_overlap hA h_y2 h_yd2
      (η_hat n ω) (h_in_Hε n ω)
      (h_mu0_diff_memLp n ω) (h_mu1_diff_memLp n ω)
      (h_e0_diff_memLp n ω) (h_e1_diff_memLp n ω)
    change |∫ z, S.seqDRMomentFunctional (η_hat n ω) z S.θ₀ ∂(S.P_Z)| ≤
        seqDR_rem_const ε *
          ((eLpNorm (fun s₀ => (η_hat n ω).μ₀_fn s₀ - S.μ₀_val s₀) 2 S.P_H₀).toReal +
            (eLpNorm (fun h => (η_hat n ω).μ₁_fn h - S.μ₁_val h) 2 S.P_H₁).toReal) *
          ((eLpNorm (fun s₀ => (η_hat n ω).e₀_fn s₀ - S.e₀_val s₀) 2 S.P_H₀).toReal +
            (eLpNorm (fun h => (η_hat n ω).e₁_fn h - S.e₁_val h) 2 S.P_H₁).toReal)
    exact h
  have h_mu0_rate :
      IsLittleOp
        (fun n ω =>
          (eLpNorm
            (fun s₀ => (η_hat n ω).μ₀_fn s₀ - S.μ₀_val s₀) 2 S.P_H₀).toReal)
        (fun _ => (1 : ℝ)) P.μ := by
    intro δ hδ
    rw [ENNReal.tendsto_nhds_zero]
    intro κ hκ
    have hsum_event :=
      (ENNReal.tendsto_nhds_zero.mp (h_indiv_rate_ρ₁ δ hδ)) κ hκ
    filter_upwards [hsum_event] with n hn
    refine (measure_mono ?_).trans hn
    intro ω hω
    have hcoord_le :
        |(eLpNorm
          (fun s₀ => (η_hat n ω).μ₀_fn s₀ - S.μ₀_val s₀) 2 S.P_H₀).toReal| ≤
          |(((seqDRGeneralMoment S h_e_pointwise).ρ₁
            (η_hat n ω) S.η₀ : NNReal) : ℝ)| := by
      simp only [seqDRGeneralMoment, DTREstimationSystem.η₀]
      rw [abs_of_nonneg ENNReal.toReal_nonneg]
      rw [abs_of_nonneg (NNReal.coe_nonneg _)]
      exact le_add_of_nonneg_right ENNReal.toReal_nonneg
    exact lt_of_lt_of_le hω hcoord_le
  have h_mu1_rate :
      IsLittleOp
        (fun n ω =>
          (eLpNorm
            (fun h => (η_hat n ω).μ₁_fn h - S.μ₁_val h) 2 S.P_H₁).toReal)
        (fun _ => (1 : ℝ)) P.μ := by
    intro δ hδ
    rw [ENNReal.tendsto_nhds_zero]
    intro κ hκ
    have hsum_event :=
      (ENNReal.tendsto_nhds_zero.mp (h_indiv_rate_ρ₁ δ hδ)) κ hκ
    filter_upwards [hsum_event] with n hn
    refine (measure_mono ?_).trans hn
    intro ω hω
    have hcoord_le :
        |(eLpNorm
          (fun h => (η_hat n ω).μ₁_fn h - S.μ₁_val h) 2 S.P_H₁).toReal| ≤
          |(((seqDRGeneralMoment S h_e_pointwise).ρ₁
            (η_hat n ω) S.η₀ : NNReal) : ℝ)| := by
      simp only [seqDRGeneralMoment, DTREstimationSystem.η₀]
      rw [abs_of_nonneg ENNReal.toReal_nonneg]
      rw [abs_of_nonneg (NNReal.coe_nonneg _)]
      exact le_add_of_nonneg_left ENNReal.toReal_nonneg
    exact lt_of_lt_of_le hω hcoord_le
  have h_e0_rate :
      IsLittleOp
        (fun n ω =>
          (eLpNorm
            (fun s₀ => (η_hat n ω).e₀_fn s₀ - S.e₀_val s₀) 2 S.P_H₀).toReal)
        (fun _ => (1 : ℝ)) P.μ := by
    intro δ hδ
    rw [ENNReal.tendsto_nhds_zero]
    intro κ hκ
    have hsum_event :=
      (ENNReal.tendsto_nhds_zero.mp (h_indiv_rate_ρ₂ δ hδ)) κ hκ
    filter_upwards [hsum_event] with n hn
    refine (measure_mono ?_).trans hn
    intro ω hω
    have hcoord_le :
        |(eLpNorm
          (fun s₀ => (η_hat n ω).e₀_fn s₀ - S.e₀_val s₀) 2 S.P_H₀).toReal| ≤
          |(((seqDRGeneralMoment S h_e_pointwise).ρ₂
            (η_hat n ω) S.η₀ : NNReal) : ℝ)| := by
      simp only [seqDRGeneralMoment, DTREstimationSystem.η₀]
      rw [abs_of_nonneg ENNReal.toReal_nonneg]
      rw [abs_of_nonneg (NNReal.coe_nonneg _)]
      exact le_add_of_nonneg_right ENNReal.toReal_nonneg
    exact lt_of_lt_of_le hω hcoord_le
  have h_e1_rate :
      IsLittleOp
        (fun n ω =>
          (eLpNorm
            (fun h => (η_hat n ω).e₁_fn h - S.e₁_val h) 2 S.P_H₁).toReal)
        (fun _ => (1 : ℝ)) P.μ := by
    intro δ hδ
    rw [ENNReal.tendsto_nhds_zero]
    intro κ hκ
    have hsum_event :=
      (ENNReal.tendsto_nhds_zero.mp (h_indiv_rate_ρ₂ δ hδ)) κ hκ
    filter_upwards [hsum_event] with n hn
    refine (measure_mono ?_).trans hn
    intro ω hω
    have hcoord_le :
        |(eLpNorm
          (fun h => (η_hat n ω).e₁_fn h - S.e₁_val h) 2 S.P_H₁).toReal| ≤
          |(((seqDRGeneralMoment S h_e_pointwise).ρ₂
            (η_hat n ω) S.η₀ : NNReal) : ℝ)| := by
      simp only [seqDRGeneralMoment, DTREstimationSystem.η₀]
      rw [abs_of_nonneg ENNReal.toReal_nonneg]
      rw [abs_of_nonneg (NNReal.coe_nonneg _)]
      exact le_add_of_nonneg_left ENNReal.toReal_nonneg
    exact lt_of_lt_of_le hω hcoord_le
  have h_score_diff_rate :
      IsLittleOp
        (fun n ω =>
          (eLpNorm
            (fun z =>
              (seqDRGeneralMoment S h_e_pointwise).m (η_hat n ω) z
                  (seqDRGeneralMoment S h_e_pointwise).θ₀ -
                (seqDRGeneralMoment S h_e_pointwise).m
                  (seqDRGeneralMoment S h_e_pointwise).η₀ z
                  (seqDRGeneralMoment S h_e_pointwise).θ₀)
            2 S.P_Z).toReal)
        (fun _ => (1 : ℝ)) P.μ := by
    simpa [seqDRGeneralMoment] using
      seqDR_score_diff_isLittleOp_one
        S h_overlap hA h_y2 h_yd2 η_hat h_in_Hε
        h_mu0_diff_memLp h_mu1_diff_memLp h_e0_diff_memLp h_e1_diff_memLp
        h_mu0_rate h_mu1_rate h_e0_rate h_e1_rate
  simpa [seqDRGeneralMoment] using
    (Causalean.Estimation.OrthogonalMoments.dml_chernozhukov_asymptoticLinear
      (seqDRGeneralMoment S h_e_pointwise)
      hMZ hFV
      sample split hc_pos h_split_rate
      η_hat (Crem := seqDR_rem_const ε) hBR_at
      h_m_meas h_m_foldA h_m_foldA_uncurry h_m_int h_m_sq_int
      h_score_diff_rate h_product_rate)

end DTR
end Estimation
end Causalean
