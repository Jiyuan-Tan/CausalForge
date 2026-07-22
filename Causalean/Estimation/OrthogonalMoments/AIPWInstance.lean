/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# AIPW instance of the abstract `GeneralMoment` framework

Instantiates the abstract `GeneralMoment` framework with the AIPW back-door
moment, and derives the AIPW asymptotic-linearity theorem from the abstract
`dml_chernozhukov_asymptoticLinear` theorem.

* `aipwGeneralMoment S hη₀_mem`   — `GeneralMoment` instance.
* `aipw_meanZero`                        — `MeanZero` for AIPW.
* `aipw_bilinearRem`                     — `BilinearRemainder` for AIPW.
* `aipw_dml_isAsymLinear`                — headline AIPW asymptotic linearity,
                                            via `dml_chernozhukov_asymptoticLinear`.

This file uses the per-η̂ bilinear-remainder route for
`aipw_dml_isAsymLinear`. The older Gâteaux-derivative AIPW witnesses are not
exported from this instance; their supporting material (an unfinished,
`sorry`-carrying Neyman-orthogonality development) is documented in
`doc/basic_concepts/po/estimation/aipw_if.tex` and preserved in git history.

See `docs/superpowers/specs/2026-05-06-general-dml-framework-design.md` §5.
-/

import Causalean.Estimation.OrthogonalMoments.DMLChernozhukov
import Causalean.Estimation.ATE.Remainder.Bound
import Causalean.Estimation.ATE.Score.AIPWMoment
import Causalean.Estimation.ATE.Score.FiniteVar
import Causalean.Estimation.ATE.Score.AIPWScoreL2

/-! # AIPW General-Moment Instance

This file instantiates the abstract orthogonal-moment framework with the
augmented inverse-probability weighted moment for the back-door average
treatment effect. It packages mean-zero, finite-variance, and bilinear
remainder facts so the general double-machine-learning theorem applies to the
AIPW estimator.

The main declarations are `aipwGeneralMoment`, `aipw_meanZero`,
`aipw_bilinearRem`, and the headline theorem `aipw_dml_isAsymLinear`, which
specializes `dml_chernozhukov_asymptoticLinear` to the AIPW score. -/

namespace Causalean
namespace Estimation
namespace ATE

open MeasureTheory ProbabilityTheory Filter Topology Causalean.PO Causalean.Stat
open Causalean.Estimation.OrthogonalMoments
open BackdoorEstimationSystem

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
  [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]

/-- AIPW instance of the abstract `GeneralMoment`.  The bilinear seminorms
are the L²(P_X) norms of the `μ_fn` and `e_fn` differences; `ρ₁` aggregates
both treatment arms of `μ_fn` (matching the `Σ_a ‖Δμ_a‖` factor produced by
`aipw_remainder_bound`). -/
noncomputable def aipwGeneralMoment
    (S : BackdoorEstimationSystem P γ) {ε : ℝ}
    (hη₀_mem : S.η₀ ∈ H_ε_aeL2 S ε) :
    GeneralMoment P.Ω P.μ (γ × Bool × ℝ) S.P_Z (NuisanceVec γ) where
  m       := fun η z θ => aipwMomentFunctional η z θ
  η₀      := S.η₀
  θ₀      := S.θ₀
  H_ε     := H_ε_aeL2 S ε
  ρ₁      := fun η η' =>
    ⟨(eLpNorm (fun x => η.μ_fn true  x - η'.μ_fn true  x) 2 S.P_X).toReal +
     (eLpNorm (fun x => η.μ_fn false x - η'.μ_fn false x) 2 S.P_X).toReal,
     by positivity⟩
  ρ₂      := fun η η' =>
    ⟨(eLpNorm (fun x => η.e_fn x - η'.e_fn x) 2 S.P_X).toReal,
     by positivity⟩
  m_meas  := fun η θ =>
    BackdoorEstimationSystem.measurable_aipwMomentFunctional η θ
  η₀_mem  := hη₀_mem
  -- AIPW is a linear score `m_AIPW(η, z, θ) = ψ_AIPW(η, z) − θ`, so the
  -- population Jacobian `J₀ = ∂_θ ∫ m(η₀, z, θ) dP_Z |_{θ=θ₀} = −1`.
  J₀         := -1
  J₀_ne_zero := by norm_num

/-- AIPW satisfies `MeanZero`. -/
theorem aipw_meanZero
    (S : BackdoorEstimationSystem P γ) {ε : ℝ}
    (hη₀_mem : S.η₀ ∈ H_ε_aeL2 S ε)
    (h_overlap : S.StrictOverlap ε)
    (hA : S.toPOBackdoorSystem.Assumptions)
    (h_y2 : Integrable (fun ω => (S.toPOBackdoorSystem.factualY ω) ^ 2) P.μ)
    (h_yd2 : ∀ d : Bool, Integrable
      (fun ω => (S.toPOBackdoorSystem.YofD d ω) ^ 2) P.μ) :
    MeanZero (aipwGeneralMoment S hη₀_mem) := by
  unfold MeanZero aipwGeneralMoment
  exact aipw_mean_zero_of_square_integrable S h_overlap hA h_y2 h_yd2

/-- AIPW satisfies `BilinearRemainder` with constant `aipw_rem_const ε`. -/
theorem aipw_bilinearRem
    (S : BackdoorEstimationSystem P γ) {ε : ℝ}
    (hη₀_mem : S.η₀ ∈ H_ε_aeL2 S ε)
    (h_overlap : S.StrictOverlap ε)
    (hA : S.toPOBackdoorSystem.Assumptions)
    (h_y2 : Integrable (fun ω => (S.toPOBackdoorSystem.factualY ω) ^ 2) P.μ)
    (h_yd2 : ∀ d : Bool, Integrable
      (fun ω => (S.toPOBackdoorSystem.YofD d ω) ^ 2) P.μ)
    (h_L2 : ∀ η ∈ H_ε_aeL2 S ε,
      (∀ d, MemLp (fun x => η.μ_fn d x - S.μ_val d x) 2 S.P_X) ∧
      MemLp (fun x => η.e_fn x - S.e_val x) 2 S.P_X) :
    ∃ C, BilinearRemainder (aipwGeneralMoment S hη₀_mem) C := by
  refine ⟨aipw_rem_const ε, ?_⟩
  intro η hη
  obtain ⟨hμ, hΔe⟩ := h_L2 η hη
  have h := BackdoorEstimationSystem.aipw_remainder_bound S h_overlap hA h_y2 h_yd2 η hη hμ hΔe
  -- Convert the Σ_a (‖Δμ_a‖ * ‖Δe‖) RHS shape into (‖Δμ_T‖ + ‖Δμ_F‖) * ‖Δe‖.
  have hsum :
      ∑ a : Bool,
        (eLpNorm (fun x => η.μ_fn a x - S.μ_val a x) 2 S.P_X).toReal *
          (eLpNorm (fun x => η.e_fn x - S.e_val x) 2 S.P_X).toReal
      = ((eLpNorm (fun x => η.μ_fn true x - S.μ_val true x) 2 S.P_X).toReal +
         (eLpNorm (fun x => η.μ_fn false x - S.μ_val false x) 2 S.P_X).toReal) *
        (eLpNorm (fun x => η.e_fn x - S.e_val x) 2 S.P_X).toReal := by
    rw [Fintype.sum_bool, add_mul]
  rw [hsum] at h
  -- After unfolding `M = aipwGeneralMoment`, the goal reduces to `h`
  -- (η₀.μ_fn = S.μ_val, η₀.e_fn = S.e_val by the constructor of η₀).
  change |∫ z, aipwMomentFunctional η z S.θ₀ ∂(S.P_Z)| ≤
      aipw_rem_const ε *
        ((eLpNorm (fun x => η.μ_fn true x - S.μ_val true x) 2 S.P_X).toReal +
         (eLpNorm (fun x => η.μ_fn false x - S.μ_val false x) 2 S.P_X).toReal) *
      (eLpNorm (fun x => η.e_fn x - S.e_val x) 2 S.P_X).toReal
  linarith [h]

/-- **Headline AIPW DML asymptotic-linearity theorem**, derived from the
abstract `dml_chernozhukov_asymptoticLinear` in
`Estimation/OrthogonalMoments/DMLChernozhukov.lean`.

**Conclusion (Chernozhukov form):**  the Chernozhukov one-step estimator
`θ̂_n = θ₀ − J₀⁻¹ · Pₙ m(η̂, ·, θ₀) = (1/|B|) Σ ψ_AIPW(η̂, Z_i)` (the last
equality uses `J₀ = −1`, see `aipwGeneralMoment`) is asymptotically linear
at `S.θ₀` with influence function

  `ψ(z) = −M.J₀_inv · M.m M.η₀ z M.θ₀ = aipwMomentFunctional S.η₀ z S.θ₀`

(again using `J₀_inv = −1`).  This is the standard AIPW influence
function — mean-zero at the truth.

Composes the abstract theorem in `DMLChernozhukov.lean` with `aipw_meanZero`,
`aipw_finite_var`, `aipw_remainder_bound` (used to construct the per-η̂_n
bilinear remainder bound directly, replacing the ∀-quantified
`aipw_bilinearRem`), and the AIPW-specific score-difference rate from
`aipw_score_diff_isLittleOp_one`.

The L²-difference hypotheses `h_mu_diff_memLp` / `h_e_diff_memLp` are
required only at the specific learners `η̂_n n ω` (not over the entire
`H_ε ε` ball).  This matches the Chernozhukov-form abstract API and avoids
the artificial ∀-quantification used by the standalone
`aipw_bilinearRem` characterization. -/
theorem aipw_dml_isAsymLinear
    (S : BackdoorEstimationSystem P γ) {ε : ℝ}
    (hη₀_mem : S.η₀ ∈ H_ε_aeL2 S ε)
    (h_overlap : S.StrictOverlap ε)
    (hA : S.toPOBackdoorSystem.Assumptions)
    (h_y2 : Integrable (fun ω => (S.toPOBackdoorSystem.factualY ω) ^ 2) P.μ)
    (h_yd2 : ∀ d : Bool, Integrable
      (fun ω => (S.toPOBackdoorSystem.YofD d ω) ^ 2) P.μ)
    (sample : IIDSample P.Ω (γ × Bool × ℝ) P.μ S.P_Z)
    (split : OneShotSplit sample)
    {c : ℝ} (hc_pos : 0 < c)
    (h_split_rate :
      Tendsto (fun n => ((split.foldB n).card : ℝ) / n) atTop (𝓝 c))
    (η_hat : ℕ → P.Ω → NuisanceVec γ)
    (h_in_Hε : ∀ n ω, η_hat n ω ∈ H_ε_aeL2 S ε)
    (h_mu_diff_memLp :
      ∀ n ω a, MemLp
        (fun x => (η_hat n ω).μ_fn a x - S.μ_val a x) 2 S.P_X)
    (h_e_diff_memLp :
      ∀ n ω, MemLp
        (fun x => (η_hat n ω).e_fn x - S.e_val x) 2 S.P_X)
    (h_m_meas :
      ∀ n, Measurable (fun (p : P.Ω × (γ × Bool × ℝ)) =>
        aipwMomentFunctional (η_hat n p.1) p.2 S.θ₀))
    (h_m_foldA :
      ∀ n,
        Measurable[MeasurableSpace.comap
          (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance]
          (fun ω z => aipwMomentFunctional (η_hat n ω) z S.θ₀))
    (h_m_foldA_uncurry :
      ∀ n,
        Measurable[(MeasurableSpace.comap
            (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance).prod
          (inferInstance : MeasurableSpace (γ × Bool × ℝ))]
          (fun (p : P.Ω × (γ × Bool × ℝ)) =>
            aipwMomentFunctional (η_hat n p.1) p.2 S.θ₀))
    (h_m_int : ∀ n ω,
      Integrable (fun z => aipwMomentFunctional (η_hat n ω) z S.θ₀) S.P_Z)
    (h_m_sq_int : ∀ n ω,
      Integrable (fun z => (aipwMomentFunctional (η_hat n ω) z S.θ₀) ^ 2) S.P_Z)
    (h_indiv_rate_ρ₁ :
      IsLittleOp
        (fun n ω =>
          (((aipwGeneralMoment S hη₀_mem).ρ₁
              (η_hat n ω) S.η₀ : NNReal) : ℝ))
        (fun _ => (1 : ℝ)) P.μ)
    (h_indiv_rate_ρ₂ :
      IsLittleOp
        (fun n ω =>
          (((aipwGeneralMoment S hη₀_mem).ρ₂
              (η_hat n ω) S.η₀ : NNReal) : ℝ))
        (fun _ => (1 : ℝ)) P.μ)
    (h_product_rate :
      IsLittleOp
        (fun n ω =>
          (((aipwGeneralMoment S hη₀_mem).ρ₁
              (η_hat n ω) S.η₀ : NNReal) : ℝ) *
            (((aipwGeneralMoment S hη₀_mem).ρ₂
                (η_hat n ω) S.η₀ : NNReal) : ℝ))
        (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) P.μ) :
    IsAsymLinear
      (Causalean.Estimation.OrthogonalMoments.dmlChernozhukovEstimator
        (aipwGeneralMoment S hη₀_mem) sample split η_hat)
      S.θ₀
      (fun z => -(aipwGeneralMoment S hη₀_mem).J₀_inv *
                aipwMomentFunctional S.η₀ z S.θ₀)
      sample
      split.foldB := by
  have hMZ := aipw_meanZero S hη₀_mem h_overlap hA h_y2 h_yd2
  have hFV :
      Integrable (fun z =>
        ((aipwGeneralMoment S hη₀_mem).m
          (aipwGeneralMoment S hη₀_mem).η₀ z
          (aipwGeneralMoment S hη₀_mem).θ₀) ^ 2) S.P_Z := by
    simpa [aipwGeneralMoment, BackdoorEstimationSystem.ψ_AIPW,
      BackdoorEstimationSystem.η₀, aipwMomentFunctional] using
        BackdoorEstimationSystem.aipw_finite_var_of_counterfactual_sq S
          h_overlap hA h_y2 h_yd2
  -- Per-η̂_n bilinear remainder, built directly from `aipw_remainder_bound`.
  -- Replaces the ∀-quantified `aipw_bilinearRem` route.
  have hBR_at :
      ∀ n ω,
        |∫ z, (aipwGeneralMoment S hη₀_mem).m (η_hat n ω) z
                (aipwGeneralMoment S hη₀_mem).θ₀ ∂S.P_Z| ≤
          aipw_rem_const ε *
            (((aipwGeneralMoment S hη₀_mem).ρ₁
                (η_hat n ω) (aipwGeneralMoment S hη₀_mem).η₀ : NNReal) : ℝ) *
            (((aipwGeneralMoment S hη₀_mem).ρ₂
                (η_hat n ω) (aipwGeneralMoment S hη₀_mem).η₀ : NNReal) : ℝ) := by
    intro n ω
    have h := BackdoorEstimationSystem.aipw_remainder_bound S h_overlap hA h_y2 h_yd2
      (η_hat n ω) (h_in_Hε n ω) (h_mu_diff_memLp n ω) (h_e_diff_memLp n ω)
    -- Convert `Σ_a (‖Δμ_a‖ * ‖Δe‖)` into `(‖Δμ_T‖ + ‖Δμ_F‖) * ‖Δe‖`.
    have hsum :
        ∑ a : Bool,
          (eLpNorm (fun x => (η_hat n ω).μ_fn a x - S.μ_val a x) 2 S.P_X).toReal *
            (eLpNorm (fun x => (η_hat n ω).e_fn x - S.e_val x) 2 S.P_X).toReal
        = ((eLpNorm (fun x => (η_hat n ω).μ_fn true x - S.μ_val true x) 2 S.P_X).toReal +
           (eLpNorm (fun x => (η_hat n ω).μ_fn false x - S.μ_val false x) 2 S.P_X).toReal) *
          (eLpNorm (fun x => (η_hat n ω).e_fn x - S.e_val x) 2 S.P_X).toReal := by
      rw [Fintype.sum_bool, add_mul]
    rw [hsum] at h
    -- Unfold `M = aipwGeneralMoment` (η₀.μ_fn = S.μ_val, η₀.e_fn = S.e_val).
    change |∫ z, aipwMomentFunctional (η_hat n ω) z S.θ₀ ∂(S.P_Z)| ≤
        aipw_rem_const ε *
          ((eLpNorm (fun x => (η_hat n ω).μ_fn true x - S.μ_val true x) 2 S.P_X).toReal +
           (eLpNorm (fun x => (η_hat n ω).μ_fn false x - S.μ_val false x) 2 S.P_X).toReal) *
        (eLpNorm (fun x => (η_hat n ω).e_fn x - S.e_val x) 2 S.P_X).toReal
    linarith [h]
  -- Translate aggregated `ρ₁` rate into per-arm `μ_hat - μ_val` L² rate.
  have h_mu_rate :
      ∀ a : Bool,
        IsLittleOp
          (fun n ω =>
            (eLpNorm
              (fun x => (η_hat n ω).μ_fn a x - S.μ_val a x) 2 S.P_X).toReal)
          (fun _ => (1 : ℝ)) P.μ := by
    intro a δ hδ
    rw [ENNReal.tendsto_nhds_zero]
    intro κ hκ
    have hsum_event :=
      (ENNReal.tendsto_nhds_zero.mp (h_indiv_rate_ρ₁ δ hδ)) κ hκ
    filter_upwards [hsum_event] with n hn
    refine (measure_mono ?_).trans hn
    intro ω hω
    have hcoord_le :
        |(eLpNorm
          (fun x => (η_hat n ω).μ_fn a x - S.μ_val a x) 2 S.P_X).toReal| ≤
          |(((aipwGeneralMoment S hη₀_mem).ρ₁
            (η_hat n ω) S.η₀ : NNReal) : ℝ)| := by
      by_cases ha : a = true
      · subst a
        simp only [aipwGeneralMoment, BackdoorEstimationSystem.η₀]
        rw [abs_of_nonneg ENNReal.toReal_nonneg]
        rw [abs_of_nonneg (NNReal.coe_nonneg _)]
        change (eLpNorm
          (fun x => (η_hat n ω).μ_fn true x - S.μ_val true x) 2 S.P_X).toReal ≤
          (eLpNorm
            (fun x => (η_hat n ω).μ_fn true x - S.μ_val true x) 2 S.P_X).toReal +
            (eLpNorm
              (fun x => (η_hat n ω).μ_fn false x - S.μ_val false x) 2 S.P_X).toReal
        exact le_add_of_nonneg_right ENNReal.toReal_nonneg
      · have ha_false : a = false := by
          cases a <;> simp_all
        subst a
        simp only [aipwGeneralMoment, BackdoorEstimationSystem.η₀]
        rw [abs_of_nonneg ENNReal.toReal_nonneg]
        rw [abs_of_nonneg (NNReal.coe_nonneg _)]
        change (eLpNorm
          (fun x => (η_hat n ω).μ_fn false x - S.μ_val false x) 2 S.P_X).toReal ≤
          (eLpNorm
            (fun x => (η_hat n ω).μ_fn true x - S.μ_val true x) 2 S.P_X).toReal +
            (eLpNorm
              (fun x => (η_hat n ω).μ_fn false x - S.μ_val false x) 2 S.P_X).toReal
        exact le_add_of_nonneg_left ENNReal.toReal_nonneg
    exact lt_of_lt_of_le hω hcoord_le
  have h_e_rate :
      IsLittleOp
        (fun n ω =>
          (eLpNorm
            (fun x => (η_hat n ω).e_fn x - S.e_val x) 2 S.P_X).toReal)
        (fun _ => (1 : ℝ)) P.μ := by
    simpa [aipwGeneralMoment, BackdoorEstimationSystem.η₀] using h_indiv_rate_ρ₂
  have h_score_diff_rate :
      IsLittleOp
        (fun n ω =>
          (eLpNorm
            (fun z =>
              (aipwGeneralMoment S hη₀_mem).m (η_hat n ω) z
                  (aipwGeneralMoment S hη₀_mem).θ₀ -
                (aipwGeneralMoment S hη₀_mem).m
                  (aipwGeneralMoment S hη₀_mem).η₀ z
                  (aipwGeneralMoment S hη₀_mem).θ₀)
            2 S.P_Z).toReal)
        (fun _ => (1 : ℝ)) P.μ := by
    simpa [aipwGeneralMoment] using
      BackdoorEstimationSystem.aipw_score_diff_isLittleOp_one
        S h_overlap hA h_y2 h_yd2 η_hat h_in_Hε
        h_mu_diff_memLp h_e_diff_memLp h_mu_rate h_e_rate
  simpa [aipwGeneralMoment] using
    (Causalean.Estimation.OrthogonalMoments.dml_chernozhukov_asymptoticLinear
      (aipwGeneralMoment S hη₀_mem)
      hMZ hFV
      sample split hc_pos h_split_rate
      η_hat (Crem := aipw_rem_const ε) hBR_at
      h_m_meas h_m_foldA h_m_foldA_uncurry h_m_int h_m_sq_int
      h_score_diff_rate h_product_rate)

end ATE
end Estimation
end Causalean
