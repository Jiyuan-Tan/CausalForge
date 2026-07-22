/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Fold-B Jacobian consistency for the feasible partially linear DML estimator

`Estimation/PLR/Feasible.lean` proves √|B|-asymptotic normality of the *feasible*
(solved Robinson partialling-out) estimator, but only after *assuming* one
remaining probabilistic input: the in-probability consistency of the empirical
partialling-out Jacobian over the estimation fold B,

    Pₙmₐ(η̂) := |B(n)|⁻¹ Σ_{i ∈ B(n)} mₐ(η̂(n,ω), Zᵢ)  →ₚ  J₀ = −E[(D − m_val(X))²].

This file proves that consistency from the same primitives the rest of the PLR
development uses (the new fold-B weak law of large numbers, the orthogonality of
the treatment residual to covariate functions, and the L²(P_X) treatment-
regression rate), so applications can supply the feasible-estimator normality
theorem's Jacobian-consistency input rather than leaving it as a separate
assumption.

**Decomposition.**  Write `g₀ := mₐ(η₀, ·)` (the partialling-out moment at the
truth) and `Y₀ n ω := |B(n)|⁻¹ Σ_{i ∈ B(n)} g₀ (Zᵢ)`.

1. `∫ g₀ dP_Z = J₀`.  Change of variables to `μ`, then `mₐ(η₀, z) = −(d − m_val x)²`
   and the `residSecondMoment` / `J₀` definitions.
2. `Y₀ →ₚ J₀`.  The fold-B WLLN applied to the fixed statistic `g₀`, with the
   limit rewritten by step 1.
3. `Yn − Y₀ →ₚ 0`, where `Yn` is the empirical Jacobian at the estimated nuisance.
   Split the per-observation increment `Δa := mₐ(η̂) − mₐ(η₀)` into a *bias* part
   `∫ Δa dP_Z` and a *centered* part `|B|⁻¹ Σ (Δa(Zᵢ) − ∫ Δa dP_Z)`.
   * **bias** `∫ Δa dP_Z = −‖Δm‖²_{L²(P_X)}`, where `Δm := m_val − m̂`.  The cross
     term `∫ (D − m_val(X))·Δm(X)` vanishes by orthogonality of the residual
     (`integral_condExpZero_mul_comp_factualX` with `condExp_resid_sigmaX`), and the
     squared L²(P_X) magnitude is `o_p(1)` by the treatment-regression rate.
   * **centered** part is `o_p(1)` from the fold-B centered empirical-process bound
     (`foldB_centered_sum_isLittleOp_one`) renormalized by `(√|B|)⁻¹ → 0`.
4. Combine `Yn − J₀ = (Yn − Y₀) + (Y₀ − J₀)`, both `o_p(1)`.

The bias half uses change of variables, the fold-B weak law, and orthogonality.
The centered half renormalizes the fold-B centered empirical-process bound by
the extra `(√|B|)⁻¹ → 0` factor.
-/

import Causalean.Estimation.PLR.Feasible
import Causalean.Stat.SampleSplit.FoldBWLLN
import Causalean.Stat.SampleSplit.FoldBEmpiricalProcess
import Causalean.Stat.Limit.Convergence

/-! # Fold-B Jacobian consistency

This file proves `plr_jacobian_consistency`, which discharges the `hJ_consist`
hypothesis of `plr_dml_feasible_tendstoNormal`: the empirical partialling-out
Jacobian, averaged over the estimation fold, converges in probability to its
population value. It also records the population identity
`integral_plrMomentA_η₀_eq_J₀`, the probability-measure instance for `P_Z`, and
the bias identity `integral_plrMomentA_diff_eq` used in the proof. -/

namespace Causalean
namespace Estimation
namespace PLR

open MeasureTheory ProbabilityTheory Causalean.Stat Causalean.PO
open Causalean.Estimation.OrthogonalMoments
open Filter Topology

namespace PLRSystem

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
  [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ] [IsProbabilityMeasure P.μ]

/-- The population integral of the partialling-out moment at the truth equals the
Jacobian: `∫ mₐ(η₀, ·) dP_Z = J₀ = −E[(D − m_val(X))²]`.

Change of variables `∫ · dP_Z = ∫ · ∘ (X,D,Y) dμ`, then the pointwise identity
`mₐ(η₀, z) = −(z.d − m_val(z.x))²` and the `residSecondMoment` / `J₀`
definitions. -/
lemma integral_plrMomentA_η₀_eq_J₀ (S : PLRSystem P γ) :
    ∫ z, plrMomentA S.η₀ z ∂S.P_Z = S.plrGeneralMoment.J₀ := by
  rw [S.integral_P_Z (measurable_plrMomentA S.η₀)]
  change ∫ ω, plrMomentA S.η₀ (S.factualZ ω) ∂P.μ = -S.residSecondMoment
  rw [residSecondMoment, ← integral_neg]
  apply integral_congr_ae
  filter_upwards with ω
  simp only [plrMomentA, plrResidual, η₀, factualZ]

/-- The joint observed-data law `P_Z` is a probability measure: it is the pushforward
of the probability measure `P.μ` along the measurable observation map `(X, D, Y)`. -/
instance instIsProbabilityMeasureP_Z (S : PLRSystem P γ) :
    IsProbabilityMeasure S.P_Z :=
  Measure.isProbabilityMeasure_map S.measurable_factualZ.aemeasurable

/-- **Bias of the empirical-Jacobian increment.**  The population integral of the
increment `Δa := mₐ(η̂, ·) − mₐ(η₀, ·)` is minus the squared L²(P_X) magnitude of
the treatment-regression error `Δm := m_val − m̂`:

    ∫ (mₐ(η̂, ·) − mₐ(η₀, ·)) dP_Z = −∫ Δm(X)² dμ.

Pointwise `Δa(z) = −2·(d − m_val(x))·Δm(x) − Δm(x)²`; after change of variables the
cross term `∫ (D − m_val(X))·Δm(X)` vanishes by orthogonality of the treatment
residual to covariate functions (`integral_condExpZero_mul_comp_factualX` with
`condExp_resid_sigmaX`), leaving the squared regression error. -/
lemma integral_plrMomentA_diff_eq (S : PLRSystem P γ)
    (η : PLRNuisance γ)
    (hD : Integrable S.factualD P.μ)
    (hresid_sq : Integrable
      (fun ω => (S.factualD ω - S.mVal (S.factualX ω)) ^ 2) P.μ)
    (hΔm_sq : Integrable
      (fun ω => (S.mVal (S.factualX ω) - η.mFn (S.factualX ω)) ^ 2) P.μ)
    (hcross : Integrable
      (fun ω => (S.factualD ω - S.mVal (S.factualX ω))
        * (S.mVal (S.factualX ω) - η.mFn (S.factualX ω))) P.μ) :
    ∫ z, (plrMomentA η z - plrMomentA S.η₀ z) ∂S.P_Z
      = -∫ ω, (S.mVal (S.factualX ω) - η.mFn (S.factualX ω)) ^ 2 ∂P.μ := by
  -- Change of variables to `μ`.
  have hmeas : Measurable (fun z => plrMomentA η z - plrMomentA S.η₀ z) :=
    (measurable_plrMomentA η).sub (measurable_plrMomentA S.η₀)
  rw [S.integral_P_Z hmeas]
  -- Abbreviate the (pulled-back) residual and regression error.
  set V₀ : P.Ω → ℝ := fun ω => S.factualD ω - S.mVal (S.factualX ω) with hV₀_def
  set Δm : P.Ω → ℝ := fun ω => S.mVal (S.factualX ω) - η.mFn (S.factualX ω) with hΔm_def
  -- Pointwise expansion: `Δa ∘ Z = −2·V₀·Δm − Δm²`.
  have hpt :
      (fun ω => plrMomentA η (S.factualZ ω) - plrMomentA S.η₀ (S.factualZ ω))
        = fun ω => (-2) * (V₀ ω * Δm ω) - Δm ω ^ 2 := by
    funext ω
    simp only [plrMomentA, plrResidual, η₀, factualZ, hV₀_def, hΔm_def]
    ring
  rw [hpt]
  -- Linearity of the integral over the two summands.
  have hsmul : Integrable (fun ω => (-2 : ℝ) * (V₀ ω * Δm ω)) P.μ :=
    hcross.const_mul _
  have hΔmsq' : Integrable (fun ω => Δm ω ^ 2) P.μ := hΔm_sq
  rw [integral_sub hsmul hΔmsq', integral_const_mul]
  -- The cross term `∫ V₀·Δm` vanishes by orthogonality of the residual.
  have hcross_zero : ∫ ω, V₀ ω * Δm ω ∂P.μ = 0 := by
    -- `V₀ =ᵐ resid` via `mVal_compat` (`m_val(X) =ᵐ mReg`, `resid = D − mReg`).
    have hV₀_ae : (fun ω => V₀ ω * Δm ω)
        =ᵐ[P.μ] fun ω => S.resid ω * Δm ω := by
      filter_upwards [S.mVal_compat] with ω hω
      simp only [hV₀_def]
      have hr : S.resid ω = S.factualD ω - S.mReg ω := rfl
      rw [hr, hω]
    rw [integral_congr_ae hV₀_ae]
    -- Orthogonality: `Δm = (m_val − m̂)(X)` is a covariate function, residual ⟂.
    have hh_meas : Measurable (fun x => S.mVal x - η.mFn x) :=
      S.mVal_meas.sub η.mMeas
    have hresid_int : Integrable S.resid P.μ := by
      have : S.resid = fun ω => S.factualD ω - S.mReg ω := rfl
      rw [this]
      exact hD.sub MeasureTheory.integrable_condExp
    have hwg_int : Integrable
        (fun ω => S.resid ω * (S.mVal (S.factualX ω) - η.mFn (S.factualX ω))) P.μ := by
      have hae : (fun ω => S.resid ω * (S.mVal (S.factualX ω) - η.mFn (S.factualX ω)))
          =ᵐ[P.μ] fun ω => V₀ ω * Δm ω := by
        filter_upwards [S.mVal_compat] with ω hω
        simp only [hV₀_def, hΔm_def]
        have hr : S.resid ω = S.factualD ω - S.mReg ω := rfl
        rw [hr, hω]
      exact (hcross.congr hae.symm)
    exact S.integral_condExpZero_mul_comp_factualX hh_meas
      (S.condExp_resid_sigmaX hD) hresid_int hwg_int
  rw [hcross_zero]
  simp only [hΔm_def, mul_zero, zero_sub]

/-- An `o_p(1)` sequence converges in probability to `0`.  (The reverse of
`Tendsto_inProb.isLittleOp_one`; both unfold to the vanishing of the deviation-set
measures, differing only between strict `<` at threshold `ε·1` and weak `≤` at
threshold `ε`.) -/
private lemma tendsto_inProb_zero_of_isLittleOp_one {Xn : ℕ → P.Ω → ℝ}
    (h : IsLittleOp Xn (fun _ => (1 : ℝ)) P.μ) :
    Tendsto_inProb Xn (fun _ => 0) P.μ := by
  unfold Tendsto_inProb
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  -- `h (ε/2)` controls the strict-`<` tail at threshold `ε/2`, which contains the
  -- weak-`≤` tail at threshold `ε`.
  have ht := h (ε / 2) (by linarith)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun _ => zero_le _) ?_
  intro n
  apply measure_mono
  intro ω hω
  simp only [Set.mem_setOf_eq, Real.norm_eq_abs, sub_zero, mul_one] at hω ⊢
  linarith [hω]

/-- The squared L²(P_X) magnitude of the treatment-regression error coincides with
the `μ`-integral of the squared pulled-back error:
`∫ (m_val(X) − m̂(X))² dμ = ((‖m_val − m̂‖_{L²(P_X)}).toReal)²`. -/
private lemma integral_Δm_sq_eq_rate_sq (S : PLRSystem P γ) (η : PLRNuisance γ)
    (hΔm : MemLp (fun x => S.mVal x - η.mFn x) 2 S.P_X) :
    ∫ ω, (S.mVal (S.factualX ω) - η.mFn (S.factualX ω)) ^ 2 ∂P.μ
      = ((eLpNorm (fun x => S.mVal x - η.mFn x) 2 S.P_X).toReal) ^ 2 := by
  set g : γ → ℝ := fun x => S.mVal x - η.mFn x with hg_def
  have hg_meas : Measurable g := S.mVal_meas.sub η.mMeas
  -- Change of variables `μ → P_X`.
  have hcov : ∫ ω, (g (S.factualX ω)) ^ 2 ∂P.μ = ∫ x, (g x) ^ 2 ∂S.P_X := by
    rw [P_X, integral_map S.measurable_factualX.aemeasurable
      (hg_meas.pow_const 2).aestronglyMeasurable]
  rw [show (fun ω => (S.mVal (S.factualX ω) - η.mFn (S.factualX ω)) ^ 2)
      = (fun ω => (g (S.factualX ω)) ^ 2) from rfl, hcov]
  -- `∫ g² dP_X = (‖g‖₂)²` for `g ∈ L²(P_X)`.
  have hpow := hΔm.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
  have hnorm_eq : (∫ x, ‖g x‖ ^ ENNReal.toReal 2 ∂S.P_X) = ∫ x, (g x) ^ 2 ∂S.P_X := by
    apply integral_congr_ae
    filter_upwards with x
    have h2 : ENNReal.toReal (2 : ENNReal) = (2 : ℝ) := by norm_num
    rw [h2, Real.norm_eq_abs, Real.rpow_two, sq_abs]
  have hI_nonneg : 0 ≤ ∫ x, (g x) ^ 2 ∂S.P_X :=
    integral_nonneg fun x => by positivity
  rw [hpow, ENNReal.toReal_ofReal
    (Real.rpow_nonneg (integral_nonneg_of_ae (Eventually.of_forall fun x => by positivity)) _),
    hnorm_eq]
  have h2 : ENNReal.toReal (2 : ENNReal) = (2 : ℝ) := by norm_num
  rw [h2]
  rw [← Real.rpow_natCast ((∫ x, (g x) ^ 2 ∂S.P_X) ^ ((2 : ℝ)⁻¹)) 2,
    ← Real.rpow_mul hI_nonneg]
  rw [show (2 : ℝ)⁻¹ * (2 : ℕ) = 1 by norm_num, Real.rpow_one]

/-- **Fold-B Jacobian consistency.**  The empirical partialling-out Jacobian at the
estimated nuisance, averaged over the estimation fold,

    Pₙmₐ(η̂) = |B(n)|⁻¹ Σ_{i ∈ B(n)} mₐ(η̂(n,ω), Zᵢ),

converges in probability to its population value `J₀ = −E[(D − m_val(X))²]`.
This supplies the `hJ_consist` hypothesis of `plr_dml_feasible_tendstoNormal`
from primitive L²-rate, integrability, and fold-B empirical-process assumptions.

The truth-Jacobian average converges to `J₀` by the fold-B weak law of large numbers
(applied to the fixed statistic `mₐ(η₀, ·)`).  The increment between the estimated and
the truth Jacobian splits into a population bias `∫ (mₐ(η̂) − mₐ(η₀)) dP_Z = −‖Δm‖²₂`
— which vanishes in probability because the treatment-regression error has L²(P_X) rate
`o_p(1)` — and a centered empirical fluctuation, controlled by the fold-B centered
empirical-process bound. -/
theorem plr_jacobian_consistency
    (S : PLRSystem P γ)
    (sample : IIDSample P.Ω (γ × ℝ × ℝ) P.μ S.P_Z)
    (split : OneShotSplit sample)
    (η_hat : ℕ → P.Ω → PLRNuisance γ)
    (hD : Integrable S.factualD P.μ)
    -- Square-integrability of the partialling-out moment at the truth (a fourth-moment
    -- condition on the treatment residual), so the fold-B WLLN applies to `mₐ(η₀, ·)`.
    (hg0_memLp : MemLp (plrMomentA S.η₀) 2 S.P_Z)
    -- Per-`(n, ω)` integrability witnesses for the bias decomposition.
    (hresid_sq : Integrable
      (fun ω => (S.factualD ω - S.mVal (S.factualX ω)) ^ 2) P.μ)
    (hΔm_sq : ∀ n ω, Integrable
      (fun ω' => (S.mVal (S.factualX ω') - (η_hat n ω).mFn (S.factualX ω')) ^ 2) P.μ)
    (hcross : ∀ n ω, Integrable
      (fun ω' => (S.factualD ω' - S.mVal (S.factualX ω'))
        * (S.mVal (S.factualX ω') - (η_hat n ω).mFn (S.factualX ω'))) P.μ)
    -- L²(P_X) square-integrability of the treatment-regression error.
    (hΔm_memLp : ∀ n ω, MemLp (fun x => S.mVal x - (η_hat n ω).mFn x) 2 S.P_X)
    -- The treatment-regression L²(P_X) `o_p(1)` rate.
    (h_m_rate :
      IsLittleOp
        (fun n ω =>
          (eLpNorm (fun x => S.mVal x - (η_hat n ω).mFn x) 2 S.P_X).toReal)
        (fun _ => (1 : ℝ)) P.μ)
    -- Fold-A measurability of the partialling-out-moment increment (mirroring the
    -- `h_m_foldA`-style hypotheses of `plr_dml_isAsymLinear`: `η̂` is fold-A trained).
    (hΔa_meas :
      ∀ n, Measurable (Function.uncurry
        (fun ω z => plrMomentA (η_hat n ω) z - plrMomentA S.η₀ z)))
    (hΔa_foldA :
      ∀ n,
        Measurable[MeasurableSpace.comap
          (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance]
          (fun ω z => plrMomentA (η_hat n ω) z - plrMomentA S.η₀ z))
    (hΔa_uncurry_foldA :
      ∀ n,
        Measurable[(MeasurableSpace.comap
            (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance).prod
          (inferInstance : MeasurableSpace (γ × ℝ × ℝ))]
          (Function.uncurry
            (fun ω z => plrMomentA (η_hat n ω) z - plrMomentA S.η₀ z)))
    -- Per-`(n, ω)` `L²(P_Z)` membership of the increment.
    (hΔa_memLp : ∀ n ω,
      MemLp (fun z => plrMomentA (η_hat n ω) z - plrMomentA S.η₀ z) 2 S.P_Z)
    -- L²(P_Z) `o_p(1)` rate of the increment (mirroring the boundedness bookkeeping of
    -- `plr_score_diff_isLittleOp_one`: the residual is bounded, `Δm` is bounded, and the
    -- L²(P_X) rate then propagates to the `mₐ`-increment).
    (hΔa_rate :
      IsLittleOp
        (fun n ω =>
          (eLpNorm (fun z => plrMomentA (η_hat n ω) z - plrMomentA S.η₀ z) 2 S.P_Z).toReal)
        (fun _ => (1 : ℝ)) P.μ) :
    Tendsto_inProb
      (fun n ω => ((split.foldB n).card : ℝ)⁻¹ *
        ∑ i ∈ split.foldB n, plrMomentA (η_hat n ω) (sample.Z i ω))
      (fun _ => S.plrGeneralMoment.J₀) P.μ := by
  classical
  -- Abbreviations: the truth statistic `g₀`, the truth-Jacobian average `Y₀`, and the
  -- target `Yn`.
  set g₀ : (γ × ℝ × ℝ) → ℝ := plrMomentA S.η₀ with hg₀_def
  set Yn : ℕ → P.Ω → ℝ := fun n ω => ((split.foldB n).card : ℝ)⁻¹ *
    ∑ i ∈ split.foldB n, plrMomentA (η_hat n ω) (sample.Z i ω) with hYn_def
  set Y₀ : ℕ → P.Ω → ℝ := fun n ω => ((split.foldB n).card : ℝ)⁻¹ *
    ∑ i ∈ split.foldB n, g₀ (sample.Z i ω) with hY₀_def
  set J₀ : ℝ := S.plrGeneralMoment.J₀ with hJ₀_def
  -- STEP 2: `Y₀ →ₚ J₀` by the fold-B WLLN, with the limit rewritten by step 1.
  have hY₀_lim : Tendsto_inProb Y₀ (fun _ => J₀) P.μ := by
    have hwlln := OneShotSplit.foldB_sampleMean_tendsto_inProb sample split
      (measurable_plrMomentA S.η₀) hg0_memLp
    have hint : ∫ z, g₀ z ∂S.P_Z = J₀ := S.integral_plrMomentA_η₀_eq_J₀
    rw [hint] at hwlln
    exact hwlln
  -- STEP 3a (bias): `bias n ω = ∫ Δa dP_Z = −‖Δm‖²₂`, which is `o_p(1)`.
  set bias : ℕ → P.Ω → ℝ := fun n ω =>
    ∫ z, (plrMomentA (η_hat n ω) z - plrMomentA S.η₀ z) ∂S.P_Z with hbias_def
  have hbias_eq : ∀ n ω, bias n ω
      = -((eLpNorm (fun x => S.mVal x - (η_hat n ω).mFn x) 2 S.P_X).toReal) ^ 2 := by
    intro n ω
    simp only [hbias_def]
    rw [S.integral_plrMomentA_diff_eq (η_hat n ω) hD hresid_sq (hΔm_sq n ω) (hcross n ω)]
    rw [S.integral_Δm_sq_eq_rate_sq (η_hat n ω) (hΔm_memLp n ω)]
  -- `‖Δm‖₂ →ₚ 0`, so its square →ₚ 0, so `bias →ₚ 0`, hence `o_p(1)`.
  set rateM : ℕ → P.Ω → ℝ := fun n ω =>
    (eLpNorm (fun x => S.mVal x - (η_hat n ω).mFn x) 2 S.P_X).toReal with hrateM_def
  have hrateM_lo : IsLittleOp rateM (fun _ => (1 : ℝ)) P.μ := h_m_rate
  have hrateM_inProb : Tendsto_inProb rateM (fun _ => 0) P.μ :=
    tendsto_inProb_zero_of_isLittleOp_one hrateM_lo
  have hrateMsq_inProb : Tendsto_inProb (fun n ω => (rateM n ω) ^ 2) (fun _ => 0) P.μ := by
    have hcont : ContinuousAt (fun x : ℝ => x ^ 2) (0 : ℝ) :=
      (continuous_pow 2).continuousAt
    have := hrateM_inProb.comp_continuousAt (g := fun x : ℝ => x ^ 2) hcont
    simpa using this
  have hbias_inProb : Tendsto_inProb bias (fun _ => 0) P.μ := by
    have heq : bias = fun n ω => -((rateM n ω) ^ 2) := by
      funext n ω; rw [hbias_eq n ω, hrateM_def]
    rw [heq]
    have hcont : ContinuousAt (fun x : ℝ => -x) (0 : ℝ) := (continuous_neg).continuousAt
    have := hrateMsq_inProb.comp_continuousAt (g := fun x : ℝ => -x) hcont
    simpa using this
  have hbias_lo : IsLittleOp bias (fun _ => (1 : ℝ)) P.μ := hbias_inProb.isLittleOp_one
  -- The "effective" bias `(|B|⁻¹·|B|)·bias` — equal to `bias` on nonempty folds and `0`
  -- on empty folds — so that the pointwise decomposition below holds for ALL `n`.  Its
  -- `{0,1}`-valued prefactor leaves it `o_p(1)`.
  set biasEff : ℕ → P.Ω → ℝ := fun n ω =>
    (((split.foldB n).card : ℝ)⁻¹ * (split.foldB n).card) * bias n ω with hbiasEff_def
  have hbiasEff_lo : IsLittleOp biasEff (fun _ => (1 : ℝ)) P.μ := by
    refine IsLittleOp.of_abs_le_const_mul_one (C := 1) one_pos hbias_lo ?_
    intro n ω
    simp only [hbiasEff_def]
    rcases Nat.eq_zero_or_pos (split.foldB n).card with hcard | hcard
    · simp [hcard]
    · have hcardR_ne : ((split.foldB n).card : ℝ) ≠ 0 := by
        simp only [ne_eq, Nat.cast_eq_zero]; omega
      rw [inv_mul_cancel₀ hcardR_ne, one_mul, one_mul]
  -- STEP 3b (centered): `centered n ω = |B|⁻¹ Σ (Δa(Zᵢ) − ∫Δa)` is `o_p(1)`.
  set centered : ℕ → P.Ω → ℝ := fun n ω => ((split.foldB n).card : ℝ)⁻¹ *
    ∑ i ∈ split.foldB n,
      ((plrMomentA (η_hat n ω) (sample.Z i ω) - plrMomentA S.η₀ (sample.Z i ω))
        - ∫ z, (plrMomentA (η_hat n ω) z - plrMomentA S.η₀ z) ∂S.P_Z) with hcentered_def
  have hcentered_lo : IsLittleOp centered (fun _ => (1 : ℝ)) P.μ := by
    -- The fold-B centered empirical-process bound gives the `(√|B|)⁻¹`-normalized sum
    -- as `o_p(1)`; renormalizing by the extra `(√|B|)⁻¹ → 0` factor keeps it `o_p(1)`.
    -- The random function family `f n ω z = mₐ(η̂(n,ω), z) − mₐ(η₀, z)`.
    set f : ℕ → P.Ω → (γ × ℝ × ℝ) → ℝ :=
      fun n ω z => plrMomentA (η_hat n ω) z - plrMomentA S.η₀ z with hf_def
    -- The `(√|B|)⁻¹`-normalized centered fold-B sum is `o_p(1)`.
    have hsqrt_centered :
        IsLittleOp
          (fun n ω =>
            (Real.sqrt ((split.foldB n).card : ℝ))⁻¹ *
              ∑ i ∈ split.foldB n, (f n ω (sample.Z i ω) - ∫ x, f n ω x ∂S.P_Z))
          (fun _ => (1 : ℝ)) P.μ :=
      foldB_centered_sum_isLittleOp_one sample split f hΔa_meas
        hΔa_uncurry_foldA hΔa_memLp hΔa_rate
    set centeredSqrt : ℕ → P.Ω → ℝ :=
      fun n ω =>
        (Real.sqrt ((split.foldB n).card : ℝ))⁻¹ *
          ∑ i ∈ split.foldB n, (f n ω (sample.Z i ω) - ∫ x, f n ω x ∂S.P_Z)
      with hcenteredSqrt_def
    -- `centeredSqrt` is `O_p(1)` (it converges in probability to `0`).
    have hcenteredSqrt_bigO : IsBigOp centeredSqrt (fun _ => (1 : ℝ)) P.μ :=
      (tendsto_inProb_zero_of_isLittleOp_one hsqrt_centered).isBigOp_one
    -- The deterministic factor `(√|B(n)|)⁻¹ → 0`, since `|B(n)| → ∞`.
    have ha_tendsto :
        Tendsto (fun n => (Real.sqrt ((split.foldB n).card : ℝ))⁻¹) atTop (𝓝 0) := by
      have hcard : Tendsto (fun n => ((split.foldB n).card : ℝ)) atTop atTop :=
        tendsto_natCast_atTop_atTop.comp split.foldB_card_tendsto
      have hsqrt : Tendsto (fun n => Real.sqrt ((split.foldB n).card : ℝ)) atTop atTop :=
        Real.tendsto_sqrt_atTop.comp hcard
      exact hsqrt.inv_tendsto_atTop
    -- `centered = (√|B|)⁻¹ · centeredSqrt`, an `o_p(1)·(→0)` product.
    have hprod_lo :
        IsLittleOp
          (fun n ω => (Real.sqrt ((split.foldB n).card : ℝ))⁻¹ * centeredSqrt n ω)
          (fun _ => (1 : ℝ)) P.μ :=
      IsBigOp.const_mul_tendsto_zero hcenteredSqrt_bigO ha_tendsto
    -- Pointwise: `centered = (√|B|)⁻¹ · centeredSqrt`.
    have hcentered_eq :
        centered = fun n ω =>
          (Real.sqrt ((split.foldB n).card : ℝ))⁻¹ * centeredSqrt n ω := by
      funext n ω
      simp only [hcentered_def, hcenteredSqrt_def, hf_def]
      rw [← mul_assoc]
      -- `|B|⁻¹ = (√|B|)⁻¹ · (√|B|)⁻¹`.
      have hinv :
          ((split.foldB n).card : ℝ)⁻¹
            = (Real.sqrt ((split.foldB n).card : ℝ))⁻¹ *
                (Real.sqrt ((split.foldB n).card : ℝ))⁻¹ := by
        rw [← mul_inv]
        rcases Nat.eq_zero_or_pos (split.foldB n).card with hcard | hcard
        · simp [hcard]
        · have hcardR_pos : (0 : ℝ) < ((split.foldB n).card : ℝ) := by exact_mod_cast hcard
          rw [Real.mul_self_sqrt (le_of_lt hcardR_pos)]
      rw [hinv]
    rw [hcentered_eq]
    exact hprod_lo
  -- STEP 3 combine: `Yn − Y₀ = centered + biasEff` pointwise, for ALL `n` (the empty
  -- fold makes every term — including `biasEff` — vanish).
  have hYn_sub_Y₀ : ∀ n ω, Yn n ω - Y₀ n ω = centered n ω + biasEff n ω := by
    intro n ω
    rcases Nat.eq_zero_or_pos (split.foldB n).card with hcard | hcard
    · -- Empty fold: every term is `0`.
      simp only [hYn_def, hY₀_def, hcentered_def, hbiasEff_def, hbias_def, hg₀_def,
        Finset.card_eq_zero.mp hcard, Finset.sum_empty, Finset.card_empty, mul_zero,
        Nat.cast_zero, inv_zero, zero_mul, sub_zero, add_zero]
    · -- Nonempty fold: `|B|⁻¹ Σ Δa = |B|⁻¹ Σ (Δa − c) + c` where `c = ∫Δa` and the
      -- correction `|B|⁻¹ · |B| · c = c`.
      have hcardR_ne : ((split.foldB n).card : ℝ) ≠ 0 := by
        simp only [ne_eq, Nat.cast_eq_zero]; omega
      simp only [hYn_def, hY₀_def, hcentered_def, hbiasEff_def, hbias_def, hg₀_def]
      set c : ℝ := ∫ z, (plrMomentA (η_hat n ω) z - plrMomentA S.η₀ z) ∂S.P_Z with hc_def
      -- RHS centered sum splits as `Σ (Δaᵢ) − |B|·c`.
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
      rw [Finset.sum_sub_distrib, mul_sub, ← mul_assoc]
      rw [inv_mul_cancel₀ hcardR_ne, one_mul]
      ring
  have hYn_sub_Y₀_lo : IsLittleOp (fun n ω => Yn n ω - Y₀ n ω) (fun _ => (1 : ℝ)) P.μ := by
    have heq : (fun n ω => Yn n ω - Y₀ n ω) = fun n ω => centered n ω + biasEff n ω := by
      funext n ω; exact hYn_sub_Y₀ n ω
    rw [heq]
    exact IsLittleOp.add_one hcentered_lo hbiasEff_lo
  -- STEP 4: `Yn − J₀ = (Yn − Y₀) + (Y₀ − J₀)`, both `o_p(1)`; back to `Tendsto_inProb`.
  have hY₀_sub_lo : IsLittleOp (fun n ω => Y₀ n ω - J₀) (fun _ => (1 : ℝ)) P.μ :=
    hY₀_lim.sub_const.isLittleOp_one
  have hYn_sub_J₀_lo : IsLittleOp (fun n ω => Yn n ω - J₀) (fun _ => (1 : ℝ)) P.μ := by
    have heq : (fun n ω => Yn n ω - J₀)
        = fun n ω => (Yn n ω - Y₀ n ω) + (Y₀ n ω - J₀) := by
      funext n ω; ring
    rw [heq]
    exact IsLittleOp.add_one hYn_sub_Y₀_lo hY₀_sub_lo
  -- Convert `IsLittleOp (Yn − J₀) 1` back into `Tendsto_inProb Yn J₀`.
  have hYn_sub_inProb : Tendsto_inProb (fun n ω => Yn n ω - J₀) (fun _ => 0) P.μ :=
    tendsto_inProb_zero_of_isLittleOp_one hYn_sub_J₀_lo
  -- `Yn = (Yn − J₀) + J₀`, so `Yn →ₚ J₀`.
  have hfinal : Tendsto_inProb Yn (fun _ => J₀) P.μ := by
    have hcont : ContinuousAt (fun x : ℝ => x + J₀) (0 : ℝ) :=
      (continuous_add_const J₀).continuousAt
    have := hYn_sub_inProb.comp_continuousAt (g := fun x : ℝ => x + J₀) hcont
    simpa using this
  exact hfinal

end PLRSystem

end PLR
end Estimation
end Causalean
