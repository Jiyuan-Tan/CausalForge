/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Feasible (solved) partially linear DML estimator and its asymptotic normality

The headline file `Estimation/PLR/DML.lean` proves √|B|-asymptotic normality
for the **one-step** Chernozhukov estimator
`θ̂_os = θ₀ − J₀⁻¹ · Pₙ ψ(η̂, ·, θ₀)`, where the inverse partialling-out
Jacobian `J₀⁻¹` is plugged in as a known population constant.  In practice one
does not know `J₀`: the analyst *solves* the empirical moment equation
`Pₙ ψ(η̂, ·, θ) = 0` for `θ`, which — because the partially linear score is
affine in `θ` — has the closed Robinson partialling-out form

    θ̂_feas = Pₙ[(Y − ℓ̂)(D − m̂)] / Pₙ[(D − m̂)²].

This file defines that *feasible* estimator and proves it has the same Gaussian
limit as the one-step estimator, by the standard "one-step ≈ solved estimator"
asymptotic-equivalence argument:

* the two rescaled recentered estimators differ by
  `(J₀⁻¹ − (Pₙmₐ)⁻¹) · ((√|B|)⁻¹ Σ ψ)`, an exact algebraic identity off the
  null event `{Pₙmₐ = 0}` (the partially linear score being linear in `θ` makes
  this identity sharp, not just asymptotic);
* `(Pₙmₐ)⁻¹ →ₚ J₀⁻¹` by the supplied Jacobian-consistency hypothesis and the
  continuous-mapping theorem for reciprocals (`J₀ ≠ 0`), so the first factor is
  `o_p(1)`;
* the normalized influence sum `(√|B|)⁻¹ Σ ψ` is `O_p(1)` (it is the one-step
  rescaled estimator up to the nonzero constant `−J₀`), tight by Prokhorov;
* the product is `o_p(1)`, the null event has vanishing measure, and Slutsky
  absorption (`Tendsto_dist.add_isLittleOp_one`) transports the one-step
  Gaussian limit to the feasible estimator.

This mirrors the analogous one-step ⇒ solved reductions for the AIPW and ATE
DML estimators; only one new probabilistic input is required, the in-probability
consistency of the empirical partialling-out Jacobian over fold B.
-/

import Causalean.Estimation.PLR.DML
import Causalean.Stat.Limit.ContinuousMapping
import Causalean.Stat.Orthogonality.ConditionalOp
import Causalean.Stat.EmpiricalProcess.CrossFitRate

/-! # Feasible partially linear DML

This file treats the one-dimensional partially linear regression model, so the
orthogonal score is affine in a single scalar treatment-effect parameter. It
defines the solved Robinson ratio estimator `plrFeasibleEstimator`, whose
numerator is the empirical covariance of residualized outcome and treatment and
whose denominator is the empirical treatment residual variance. The theorem
`plr_dml_feasible_tendstoNormal` reduces its √|B|-asymptotic normality to the
one-step normality theorem `plr_dml_tendstoNormal` by the standard
asymptotic-equivalence argument. -/

namespace Causalean
namespace Estimation
namespace PLR

open MeasureTheory ProbabilityTheory Causalean.Stat Causalean.PO
open Causalean.Estimation.OrthogonalMoments
open Filter Topology

namespace PLRSystem

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
  [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ] [IsProbabilityMeasure P.μ]

/-- **Feasible (solved) partially linear DML estimator.**  Solving the empirical
Robinson partialling-out moment equation `Pₙ ψ(η̂, ·, θ) = 0` for `θ` — which,
because the score is affine in `θ`, is the explicit ratio of the empirical
covariance of the residualized outcome and residualized treatment to the
empirical second moment of the residualized treatment:

    θ̂_feas(n) = (Σ_{i∈B(n)} (Yᵢ − ℓ̂(Xᵢ))(Dᵢ − m̂(Xᵢ)))
                 / (Σ_{i∈B(n)} (Dᵢ − m̂(Xᵢ))²)
              = Pₙ[(Y − ℓ̂)(D − m̂)] / Pₙ[(D − m̂)²].

The fold-size factor `|B(n)|⁻¹` cancels between numerator and denominator, so it
does not appear.  The denominator is the empirical second moment of the
treatment residual; equivalently it is the negative of the empirical
partialling-out Jacobian `−Σ mₐ`, since `mₐ = −(residual)²`. -/
noncomputable def plrFeasibleEstimator (S : PLRSystem P γ)
    (sample : IIDSample P.Ω (γ × ℝ × ℝ) P.μ S.P_Z) (split : OneShotSplit sample)
    (η_hat : ℕ → P.Ω → PLRNuisance γ) (n : ℕ) : P.Ω → ℝ :=
  fun ω => (∑ i ∈ split.foldB n, plrMomentB (η_hat n ω) (sample.Z i ω))
            / (∑ i ∈ split.foldB n, (plrResidual (η_hat n ω) (sample.Z i ω)) ^ 2)

/-- **Feasible partially linear DML asymptotic-normality theorem.**  Under the
same hypotheses as the one-step normality result `plr_dml_tendstoNormal` —
the sample, sample split with a fixed limiting fold-B share, the estimated
nuisance sequence, and the full integrability / square-integrability /
per-observation remainder / measurability / rate bundle — together with one new
probabilistic input, the in-probability consistency of the empirical
partialling-out Jacobian over fold B to its population value `J₀`, the rescaled
*feasible* estimator (the solved Robinson partialling-out estimator, recentered
at the true slope and scaled by the square root of the fold-B sample size)
converges in distribution to the same centered Gaussian as the one-step
estimator: a normal law whose variance is the population second moment of the
inverse-Jacobian-scaled partialling-out score at the true regressions.

The proof is the standard one-step ≈ solved-estimator asymptotic-equivalence
argument: the two rescaled estimators differ by the product of a factor that is
`o_p(1)` (driven by the Jacobian consistency through the reciprocal
continuous-mapping theorem) and the normalized influence sum that is `O_p(1)`
(tightness of the one-step limit), so the difference is `o_p(1)` and Slutsky
absorption carries the one-step Gaussian limit over. -/
theorem plr_dml_feasible_tendstoNormal
    (S : PLRSystem P γ)
    (sample : IIDSample P.Ω (γ × ℝ × ℝ) P.μ S.P_Z)
    (split : OneShotSplit sample)
    {c : ℝ} (hc_pos : 0 < c)
    (h_split_rate :
      Tendsto (fun n => ((split.foldB n).card : ℝ) / n) atTop (𝓝 c))
    (η_hat : ℕ → P.Ω → PLRNuisance γ)
    (hU : Integrable S.U P.μ)
    (hUV : Integrable (fun ω => S.U ω * S.toPOPartialLinearModel.resid ω) P.μ)
    (hbX : Integrable (fun ω => S.b (S.factualX ω)) P.μ)
    (hD : Integrable S.factualD P.μ)
    (hV : MemLp S.resid 2 P.μ)
    (hsq : Integrable
      (fun ω => (plrMomentFunctional S.η₀ (S.factualZ ω) S.θ₀) ^ 2) P.μ)
    (hΔl : ∀ n ω, MemLp (fun x => (η_hat n ω).lFn x - S.lVal x) 2 S.P_X)
    (hΔm : ∀ n ω, MemLp (fun x => (η_hat n ω).mFn x - S.mVal x) 2 S.P_X)
    (hUΔm : ∀ n ω, Integrable
      (fun ω' => S.U ω' *
        ((η_hat n ω).mFn (S.factualX ω') - S.mVal (S.factualX ω'))) P.μ)
    (hΔlV : ∀ n ω, Integrable
      (fun ω' => ((η_hat n ω).lFn (S.factualX ω') - S.lVal (S.factualX ω'))
        * S.resid ω') P.μ)
    (hVΔm : ∀ n ω, Integrable
      (fun ω' => S.resid ω' *
        ((η_hat n ω).mFn (S.factualX ω') - S.mVal (S.factualX ω'))) P.μ)
    (h_m_meas :
      ∀ n, Measurable (fun (p : P.Ω × (γ × ℝ × ℝ)) =>
        S.plrGeneralMoment.m (η_hat n p.1) p.2 S.plrGeneralMoment.θ₀))
    (h_m_foldA :
      ∀ n,
        Measurable[MeasurableSpace.comap
          (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance]
          (fun ω z => S.plrGeneralMoment.m (η_hat n ω) z S.plrGeneralMoment.θ₀))
    (h_m_foldA_uncurry :
      ∀ n,
        Measurable[(MeasurableSpace.comap
            (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance).prod
          (inferInstance : MeasurableSpace (γ × ℝ × ℝ))]
          (fun (p : P.Ω × (γ × ℝ × ℝ)) =>
            S.plrGeneralMoment.m (η_hat n p.1) p.2 S.plrGeneralMoment.θ₀))
    (h_m_int : ∀ n ω,
      Integrable (fun z =>
        S.plrGeneralMoment.m (η_hat n ω) z S.plrGeneralMoment.θ₀) S.P_Z)
    (h_m_sq_int : ∀ n ω,
      Integrable (fun z =>
        (S.plrGeneralMoment.m (η_hat n ω) z S.plrGeneralMoment.θ₀) ^ 2) S.P_Z)
    (h_score_diff_rate :
      IsLittleOp
        (fun n ω =>
          (eLpNorm
            (fun z =>
              S.plrGeneralMoment.m (η_hat n ω) z S.plrGeneralMoment.θ₀ -
                S.plrGeneralMoment.m S.plrGeneralMoment.η₀ z S.plrGeneralMoment.θ₀)
            2 S.P_Z).toReal)
        (fun _ => (1 : ℝ)) P.μ)
    (h_product_rate :
      IsLittleOp
        (fun n ω =>
          ((S.plrGeneralMoment.ρ₁ (η_hat n ω) S.plrGeneralMoment.η₀ : NNReal) : ℝ) *
            ((S.plrGeneralMoment.ρ₂ (η_hat n ω) S.plrGeneralMoment.η₀ : NNReal) : ℝ))
        (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) P.μ)
    (hψ_meas :
      Measurable
        (fun z => -S.plrGeneralMoment.J₀_inv * plrMomentFunctional S.η₀ z S.θ₀))
    (hθn_meas : ∀ n, AEMeasurable
      (IsAsymLinear.rescaledEstimator
        (dmlChernozhukovEstimator S.plrGeneralMoment sample split η_hat)
        S.θ₀ split.foldB n) P.μ)
    (hSum_meas : ∀ n, AEMeasurable
      (IsAsymLinear.normalizedSum sample
        (fun z => -S.plrGeneralMoment.J₀_inv * plrMomentFunctional S.η₀ z S.θ₀)
        split.foldB n) P.μ)
    -- The single new probabilistic hypothesis: in-probability consistency of the
    -- empirical partialling-out Jacobian over fold B to its population value.
    (hJ_consist :
      Tendsto_inProb
        (fun n ω => ((split.foldB n).card : ℝ)⁻¹ *
          ∑ i ∈ split.foldB n, plrMomentA (η_hat n ω) (sample.Z i ω))
        (fun _ => S.plrGeneralMoment.J₀) P.μ)
    (hθn_feas : ∀ n, AEMeasurable
      (IsAsymLinear.rescaledEstimator
        (plrFeasibleEstimator S sample split η_hat) S.θ₀ split.foldB n) P.μ) :
    Tendsto_dist
      (IsAsymLinear.rescaledEstimator
        (plrFeasibleEstimator S sample split η_hat) S.θ₀ split.foldB)
      (gaussianMeasure 0
        (∫ z, (-S.plrGeneralMoment.J₀_inv * plrMomentFunctional S.η₀ z S.θ₀) ^ 2
          ∂S.P_Z))
      P.μ
      hθn_feas := by
  -- Step 1: the one-step rescaled estimator converges to the Gaussian target.
  have hOS :=
    S.plr_dml_tendstoNormal sample split hc_pos h_split_rate η_hat
      hU hUV hbX hD hV hsq hΔl hΔm hUΔm hΔlV hVΔm
      h_m_meas h_m_foldA h_m_foldA_uncurry h_m_int h_m_sq_int
      h_score_diff_rate h_product_rate hψ_meas hθn_meas hSum_meas
  -- Abbreviations.
  set J₀ : ℝ := S.plrGeneralMoment.J₀ with hJ₀_def
  have hJ₀_ne : J₀ ≠ 0 := S.plrGeneralMoment.J₀_ne_zero
  -- The empirical partialling-out Jacobian `Pₙ mₐ = |B|⁻¹ Σ mₐ`.
  set Pmₐ : ℕ → P.Ω → ℝ :=
    fun n ω => ((split.foldB n).card : ℝ)⁻¹ *
      ∑ i ∈ split.foldB n, plrMomentA (η_hat n ω) (sample.Z i ω) with hPmₐ_def
  -- The normalized influence sum `(√|B|)⁻¹ Σ ψ`.
  set Sψ : ℕ → P.Ω → ℝ :=
    fun n ω => (Real.sqrt ((split.foldB n).card : ℝ))⁻¹ *
      ∑ i ∈ split.foldB n, plrMomentFunctional (η_hat n ω) (sample.Z i ω) S.θ₀
    with hSψ_def
  -- The one-step rescaled estimator (the `Xn` of the Slutsky step).
  set Xn : ℕ → P.Ω → ℝ :=
    IsAsymLinear.rescaledEstimator
      (dmlChernozhukovEstimator S.plrGeneralMoment sample split η_hat)
      S.θ₀ split.foldB with hXn_def
  -- The feasible rescaled estimator (the `Yn`).
  set Yn : ℕ → P.Ω → ℝ :=
    IsAsymLinear.rescaledEstimator
      (plrFeasibleEstimator S sample split η_hat) S.θ₀ split.foldB with hYn_def
  -- The factor that turns out to be `o_p(1)`: `J₀⁻¹ − (Pₙmₐ)⁻¹`.
  set Fn : ℕ → P.Ω → ℝ :=
    fun n ω => S.plrGeneralMoment.J₀_inv - (Pmₐ n ω)⁻¹ with hFn_def
  -- Step 4: `(√|B|)⁻¹ Σ ψ = −J₀ · (one-step rescaled estimator)` pointwise,
  -- hence `O_p(1)` by tightness of the one-step Gaussian limit.
  have hSψ_eq : Sψ = fun n ω => (-J₀) * Xn n ω := by
    funext n ω
    -- Abbreviate the influence sum `Σ ψ`; `m(η̂, z, θ₀) = plrMomentFunctional`
    -- definitionally, so this is also the empirical-moment sum of `Xn`.
    set Sumψ : ℝ := ∑ i ∈ split.foldB n,
      plrMomentFunctional (η_hat n ω) (sample.Z i ω) S.θ₀ with hSumψ_def
    -- The one-step empirical-moment sum is `Sumψ` (definitional projection
    -- equalities `m = plrMomentFunctional`, `θ₀ = S.θ₀`).
    have hθ₀_proj : S.plrGeneralMoment.θ₀ = S.θ₀ := rfl
    have hsum_m : (∑ i ∈ split.foldB n,
        S.plrGeneralMoment.m (η_hat n ω) (sample.Z i ω) S.θ₀) = Sumψ :=
      rfl
    have hXn_val : Xn n ω = Real.sqrt ((split.foldB n).card : ℝ) *
        (-(J₀⁻¹ * (((split.foldB n).card : ℝ)⁻¹ * Sumψ))) := by
      simp only [hXn_def, IsAsymLinear.rescaledEstimator, dmlChernozhukovEstimator,
        GeneralMoment.J₀_inv, hJ₀_def, hθ₀_proj, hsum_m]
      ring
    have hSψ_val : Sψ n ω = (Real.sqrt ((split.foldB n).card : ℝ))⁻¹ * Sumψ := rfl
    rw [hSψ_val, hXn_val]
    rcases Nat.eq_zero_or_pos (split.foldB n).card with hcard | hcard
    · -- Empty fold: both sides vanish.
      simp only [hcard, Nat.cast_zero, Real.sqrt_zero, inv_zero, zero_mul,
        mul_zero, neg_zero]
    · -- Nonempty fold: use `√|B| · |B|⁻¹ = (√|B|)⁻¹` and `J₀ · J₀⁻¹ = 1`.
      have hcard_pos : (0 : ℝ) < ((split.foldB n).card : ℝ) := by
        exact_mod_cast hcard
      have hcard_ne : ((split.foldB n).card : ℝ) ≠ 0 := ne_of_gt hcard_pos
      have hsqrt_ne : Real.sqrt ((split.foldB n).card : ℝ) ≠ 0 :=
        ne_of_gt (Real.sqrt_pos.mpr hcard_pos)
      have hsqrt_sq : Real.sqrt ((split.foldB n).card : ℝ) *
          Real.sqrt ((split.foldB n).card : ℝ) = ((split.foldB n).card : ℝ) :=
        Real.mul_self_sqrt (le_of_lt hcard_pos)
      -- `(√|B|)⁻¹ = √|B| · |B|⁻¹` since `|B| = √|B| · √|B|`.
      have hsqrt_inv : (Real.sqrt ((split.foldB n).card : ℝ))⁻¹
          = Real.sqrt ((split.foldB n).card : ℝ) * ((split.foldB n).card : ℝ)⁻¹ := by
        field_simp
        linarith [hsqrt_sq]
      rw [hsqrt_inv]
      field_simp
  -- `(√|B|)⁻¹ Σ ψ = O_p(1)`.
  have hSψ_bigO : IsBigOp Sψ (fun _ => (1 : ℝ)) P.μ := by
    rw [hSψ_eq]
    exact Causalean.Stat.IsBigOp.const_mul (-J₀) (Tendsto_dist.tightness hθn_meas hOS)
  -- Step 3: `(Pₙmₐ)⁻¹ →ₚ J₀⁻¹`, hence `Fn = J₀⁻¹ − (Pₙmₐ)⁻¹ →ₚ 0`, i.e. `o_p(1)`.
  have hPmₐ_inv : Tendsto_inProb (fun n ω => 1 / Pmₐ n ω) (fun _ => 1 / J₀) P.μ := by
    have := (hJ_consist).inv hJ₀_ne
    simpa [hPmₐ_def, hJ₀_def] using this
  have hFn_inProb : Tendsto_inProb Fn (fun _ => 0) P.μ := by
    -- `Fn = J₀⁻¹ − (Pₙmₐ)⁻¹ = (1/J₀) − (1/Pₙmₐ)`; it converges to `0`.
    have hconv :
        Tendsto_inProb (fun n ω => (fun n ω => 1 / Pmₐ n ω) n ω - 1 / J₀)
          (fun _ => 0) P.μ := hPmₐ_inv.sub_const
    -- Rewrite `1/x = x⁻¹` and flip the sign to match `Fn`.
    have hneg :
        Tendsto_inProb (fun n ω => -(fun n ω => 1 / Pmₐ n ω - 1 / J₀) n ω)
          (fun _ => 0) P.μ := by
      have hcont : ContinuousAt (fun x : ℝ => -x) (0 : ℝ) := (continuous_neg).continuousAt
      have := hconv.comp_continuousAt (g := fun x : ℝ => -x) hcont
      simpa using this
    have hFn_eq : Fn = fun n ω => -((fun n ω => 1 / Pmₐ n ω) n ω - 1 / J₀) := by
      funext n ω
      simp only [hFn_def, GeneralMoment.J₀_inv, hJ₀_def, one_div]
      ring
    rw [hFn_eq]
    exact hneg
  have hFn_littleO : IsLittleOp Fn (fun _ => (1 : ℝ)) P.μ :=
    hFn_inProb.isLittleOp_one
  -- Step 5: the product `Fn · Sψ = o_p(1)`.
  have hprod_littleO :
      IsLittleOp (fun n ω => Sψ n ω * Fn n ω) (fun _ => (1 : ℝ)) P.μ :=
    hSψ_bigO.mul_isLittleOp_one_isLittleOp hFn_littleO
  -- Step 2 + 6: off the null event `{Pₙmₐ = 0}`, the rescaled difference equals
  -- `Fn · Sψ`.  The null event has vanishing measure, so the rescaled difference
  -- is itself `o_p(1)`.
  -- (a) The algebraic identity on `{Pₙmₐ ≠ 0}`.
  have hdiff_eq :
      ∀ n ω, Pmₐ n ω ≠ 0 →
        Yn n ω - Xn n ω = Sψ n ω * Fn n ω := by
    intro n ω hPne
    -- On a nonempty fold (forced by `Pₙmₐ ≠ 0`), expand both estimators.
    have hcard_pos : 0 < (split.foldB n).card := by
      rcases Nat.eq_zero_or_pos (split.foldB n).card with hz | hpos
      · exact absurd (by
          simp only [hPmₐ_def, Finset.card_eq_zero.mp hz, Finset.sum_empty,
            mul_zero]) hPne
      · exact hpos
    have hcardR_pos : (0 : ℝ) < ((split.foldB n).card : ℝ) := by exact_mod_cast hcard_pos
    have hcardR_ne : ((split.foldB n).card : ℝ) ≠ 0 := ne_of_gt hcardR_pos
    have hsqrt_pos : (0 : ℝ) < Real.sqrt ((split.foldB n).card : ℝ) :=
      Real.sqrt_pos.mpr hcardR_pos
    have hsqrt_ne : Real.sqrt ((split.foldB n).card : ℝ) ≠ 0 := ne_of_gt hsqrt_pos
    have hsqrt_sq : Real.sqrt ((split.foldB n).card : ℝ) *
        Real.sqrt ((split.foldB n).card : ℝ) = ((split.foldB n).card : ℝ) :=
      Real.mul_self_sqrt (le_of_lt hcardR_pos)
    -- Denominator of the feasible estimator: `D := Σ residual²`.
    set D : ℝ := ∑ i ∈ split.foldB n,
      (plrResidual (η_hat n ω) (sample.Z i ω)) ^ 2 with hD_def
    -- `Σ mₐ = −D`.
    have hsum_a : ∑ i ∈ split.foldB n, plrMomentA (η_hat n ω) (sample.Z i ω)
        = -D := by
      simp only [hD_def, plrMomentA, Finset.sum_neg_distrib]
    -- `Pₙmₐ = |B|⁻¹ · (−D)`, and `Pₙmₐ ≠ 0` gives `D ≠ 0`.
    have hPmₐ_val : Pmₐ n ω = ((split.foldB n).card : ℝ)⁻¹ * (-D) := by
      simp only [hPmₐ_def, hsum_a]
    have hD_ne : D ≠ 0 := by
      intro hDz
      apply hPne
      rw [hPmₐ_val, hDz, neg_zero, mul_zero]
    -- `Σ ψ = (Σ mₐ)·θ₀ + Σ m_b = −D·θ₀ + Σ m_b` by the linear decomposition.
    set Sb : ℝ := ∑ i ∈ split.foldB n,
      plrMomentB (η_hat n ω) (sample.Z i ω) with hSb_def
    have hsum_psi : ∑ i ∈ split.foldB n,
        plrMomentFunctional (η_hat n ω) (sample.Z i ω) S.θ₀ = (-D) * S.θ₀ + Sb := by
      calc
        ∑ i ∈ split.foldB n,
            plrMomentFunctional (η_hat n ω) (sample.Z i ω) S.θ₀
            = ∑ i ∈ split.foldB n,
                (plrMomentA (η_hat n ω) (sample.Z i ω) * S.θ₀
                  + plrMomentB (η_hat n ω) (sample.Z i ω)) := by
              apply Finset.sum_congr rfl
              intro i _
              exact plrMoment_decomp _ _ _
        _ = (∑ i ∈ split.foldB n, plrMomentA (η_hat n ω) (sample.Z i ω)) * S.θ₀
              + ∑ i ∈ split.foldB n, plrMomentB (η_hat n ω) (sample.Z i ω) := by
              rw [Finset.sum_add_distrib, ← Finset.sum_mul]
        _ = (-D) * S.θ₀ + Sb := by rw [hsum_a, hSb_def]
    -- Feasible estimator value: `θ̂_feas = Sb / D`.
    have hfeas_val : plrFeasibleEstimator S sample split η_hat n ω = Sb / D := by
      simp only [plrFeasibleEstimator, hSb_def, hD_def]
    -- Now expand `Yn − Xn` and `Sψ · Fn`, and check the algebraic identity.
    simp only [hYn_def, hXn_def, hSψ_def, hFn_def, IsAsymLinear.rescaledEstimator,
      dmlChernozhukovEstimator, GeneralMoment.J₀_inv, hfeas_val, hsum_psi,
      hPmₐ_val]
    -- `m(η̂, z, θ₀) = plrMomentFunctional η̂ z θ₀` definitionally; rewrite its sum.
    rw [show (∑ i ∈ split.foldB n,
          S.plrGeneralMoment.m (η_hat n ω) (sample.Z i ω) S.plrGeneralMoment.θ₀)
        = (-D) * S.θ₀ + Sb from hsum_psi]
    -- Everything is now a rational identity in `√|B|, |B|, D, Sb, θ₀, J₀`.
    -- Canonicalize the moment projections (`θ₀ = S.θ₀`, `J₀⁻¹` from `J₀`).
    have hJ₀'_ne : S.plrGeneralMoment.J₀ ≠ 0 := S.plrGeneralMoment.J₀_ne_zero
    have hθ₀_proj : S.plrGeneralMoment.θ₀ = S.θ₀ := rfl
    have hPmₐ_term_ne : ((split.foldB n).card : ℝ)⁻¹ * (-D) ≠ 0 := by
      rw [← hPmₐ_val]; exact hPne
    rw [hθ₀_proj]
    field_simp
    rw [show Real.sqrt ((split.foldB n).card : ℝ) ^ 2 = ((split.foldB n).card : ℝ) by
      rw [sq]; exact hsqrt_sq]
    ring
  -- (b) The null event `{Pₙmₐ = 0}` has vanishing measure, because `Pₙmₐ →ₚ J₀ ≠ 0`.
  have hbad_to_zero :
      Tendsto (fun n => P.μ {ω | Yn n ω - Xn n ω ≠ Sψ n ω * Fn n ω}) atTop (𝓝 0) := by
    -- On `{Pₙmₐ ≠ 0}` the difference equals `Sψ · Fn`, so the bad set is contained
    -- in `{Pₙmₐ = 0} ⊆ {|Pₙmₐ − J₀| ≥ |J₀|}`, whose measure → 0 by consistency.
    have hsubset : ∀ n,
        {ω | Yn n ω - Xn n ω ≠ Sψ n ω * Fn n ω}
          ⊆ {ω | |J₀| ≤ |Pmₐ n ω - J₀|} := by
      intro n ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      by_contra hlt
      push_neg at hlt
      -- `|Pₙmₐ − J₀| < |J₀|` forces `Pₙmₐ ≠ 0` (else `|−J₀| = |J₀| < |J₀|`).
      have hne : Pmₐ n ω ≠ 0 := by
        intro hz
        rw [hz, zero_sub, abs_neg] at hlt
        exact (lt_irrefl _ hlt)
      exact hω (hdiff_eq n ω hne)
    -- Measure of `{|Pₙmₐ − J₀| ≥ |J₀|}` → 0 from `Pₙmₐ →ₚ J₀` and `J₀ ≠ 0`.
    have hJabs_pos : 0 < |J₀| := abs_pos.mpr hJ₀_ne
    have hconsist : Tendsto_inProb Pmₐ (fun _ => J₀) P.μ := by
      simpa [hPmₐ_def, hJ₀_def] using hJ_consist
    have hconsist_norm := hconsist
    unfold Tendsto_inProb at hconsist_norm
    rw [tendstoInMeasure_iff_norm] at hconsist_norm
    have htail := hconsist_norm |J₀| hJabs_pos
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htail
      (fun _ => zero_le _) ?_
    intro n
    refine measure_mono ?_
    intro ω hω
    simp only [Set.mem_setOf_eq, Real.norm_eq_abs] at hω ⊢
    exact (hsubset n hω)
  -- The rescaled difference `Yn − Xn` is `o_p(1)`.
  have hrem_littleO : IsLittleOp (fun n ω => Yn n ω - Xn n ω) (fun _ => (1 : ℝ)) P.μ :=
    IsLittleOp.of_eq_on_asymptotic hbad_to_zero hprod_littleO
  -- Step 7: Slutsky absorption transports the one-step Gaussian limit.
  exact Tendsto_dist.add_isLittleOp_one hθn_meas hθn_feas hOS hrem_littleO

end PLRSystem

end PLR
end Estimation
end Causalean
