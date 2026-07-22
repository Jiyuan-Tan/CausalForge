/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Abstract one-shot DML in **classical Chernozhukov form**

This file proves the general Chernozhukov form of the one-shot DML theorem:
the moment is evaluated at the truth `M.θ₀`, the estimator is a one-step
Z-step `θ̂ = θ₀ − J₀⁻¹ · Pₙ m(η̂, ·, θ₀)`, and the conclusion's influence
function is `−J₀⁻¹ · m(η₀, ·, θ₀)`.

For the AIPW linear score (`m(η, z, θ) = ψ(η, z) − θ`, `J₀ = −1`), the
estimator reduces to `Pₙ ψ(η̂, ·)` and the influence function reduces to
`m(η₀, ·, θ₀)` — recovering the existing AIPW production proof.

The proof uses the standard G+B decomposition (centered fold-B sum + bias)
with the Chernozhukov-form score `m(η̂, ·, θ₀)` and influence function
`−J₀⁻¹ · m(η₀, ·, θ₀)`.
The bilinear-remainder hypothesis bounds `|∫ m(η̂, z, θ₀) dP_Z|`, matching
`MeanZero` at `θ = θ₀` directly (no `hθ_zero` reduction needed).

References:
* Chernozhukov, Chetverikov, Demirer, Duflo, Hansen, Newey, Robins (2018).
  *Double/Debiased Machine Learning for Treatment and Structural
  Parameters*.  Econometrics Journal 21(1), C1–C68.  Theorem 3.1
  (linear-score) and Theorem 3.2 (non-linear-score).
* See `doc/basic_concepts/Semi-parametric Inference/
  semi_parametric_inference.tex`, `thm:sp-generic-dml`.
-/

import Causalean.Estimation.OrthogonalMoments.RemainderBound
import Causalean.Stat.Sample
import Causalean.Stat.SampleSplit
import Causalean.Stat.CLT.AsymptoticLinearity
import Causalean.Stat.SampleSplit.PartialFoldCLT
import Causalean.Stat.Limit.Convergence
import Causalean.Stat.SampleSplit.FoldBEmpiricalProcess

/-! # Chernozhukov-Form Double Machine Learning

This file proves the abstract one-shot double machine learning theorem in the
classical Chernozhukov form. The estimator evaluates the moment at the true
target, rescales by the inverse Jacobian, and yields asymptotic linearity with
the corresponding influence function. -/

namespace Causalean
namespace Estimation
namespace OrthogonalMoments

open MeasureTheory ProbabilityTheory Filter Topology Causalean.Stat

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
         {Z : Type*} [MeasurableSpace Z] {P_Z : MeasureTheory.Measure Z}
         {H : Type*} [AddCommGroup H] [Module ℝ H]

/-- **Chernozhukov one-step DML estimator.**  Evaluates the score at the
truth `M.θ₀` and rescales by the Jacobian inverse:

    θ̂_n := M.θ₀ − M.J₀⁻¹ · ((1/|B(n)|) Σ_{i ∈ B(n)} m(η̂(n), Z_i, M.θ₀))

This is the form that matches Chernozhukov et al. (2018) Eq. (3.7).  For
linear scores `m(η, z, θ) = m_a(η, z) θ + m_b(η, z)` (the AIPW family),
the empirical mean of `m(η̂, ·, θ₀)` collapses to a clean expression in
`m_b` and the recentering with `J₀⁻¹` recovers the standard sample-mean
form. -/
noncomputable def dmlChernozhukovEstimator
    (M : GeneralMoment Ω μ Z P_Z H)
    (sample : IIDSample Ω Z μ P_Z)
    (split : OneShotSplit sample)
    (η_hat : ℕ → Ω → H)
    (n : ℕ) : Ω → ℝ :=
  fun ω =>
    M.θ₀ - M.J₀_inv * (((split.foldB n).card : ℝ)⁻¹ *
      ∑ i ∈ split.foldB n, M.m (η_hat n ω) (sample.Z i ω) M.θ₀)

/-- **Asymptotic linearity of the Chernozhukov DML estimator.**  Drops the
zero-centering hypothesis `hθ_zero` from `dml_asymptoticLinear`.  Conclusion
is in **Chernozhukov form**: influence function `−J₀⁻¹ · m(η₀, ·, θ₀)` and
asymptotic variance `J₀⁻¹ Σ J₀⁻ᵀ` where `Σ := ∫ m(η₀, z, θ₀)² dP_Z`.

Hypotheses (mirroring `dml_asymptoticLinear`):

* `hMZ`         — `MeanZero M`, i.e., `∫ m(η₀, z, M.θ₀) dP_Z = 0`;
* `hFV`         — `Integrable (m(η₀, ·, θ₀))² P_Z`;
* `hBR_at`      — per-`η̂_n` bilinear remainder bound:
                  `|∫ m(η̂_n, z, θ₀) dP_Z| ≤ Crem · ρ₁(η̂_n, η₀) · ρ₂(η̂_n, η₀)`.
                  (Chernozhukov-form supersedes the `BilinearRemainder M Crem`
                  ∀-quantified predicate; instances need only justify the bound
                  at the specific learners they plug in.)  Neyman orthogonality
                  is implicitly required for this bound to hold and is checked
                  by the user when supplying `_hBR_at`;
* one-shot split with rate `|B(n)|/n → c ∈ (0, ∞)` (`hc_pos`, `h_split_rate`);
* the standard fold-A measurability conditions;
* product rate `ρ₁ · ρ₂ = o_p(n^{-1/2})`;
* `h_score_diff_rate` — abstract analogue of AIPW's
  `aipw_score_diff_isLittleOp_one`.

Conclusion: the estimator is asymptotically linear at `M.θ₀` with influence
function `fun z => -M.J₀_inv * M.m M.η₀ z M.θ₀`, indexed over `split.foldB`. -/
theorem dml_chernozhukov_asymptoticLinear
    [StandardBorelSpace Ω] [IsFiniteMeasure μ] [IsProbabilityMeasure μ]
    (M : GeneralMoment Ω μ Z P_Z H)
    (_hMZ : MeanZero M)
    (_hFV : Integrable (fun z => (M.m M.η₀ z M.θ₀) ^ 2) P_Z)
    (sample : IIDSample Ω Z μ P_Z)
    (split : OneShotSplit sample)
    {c : ℝ} (_hc_pos : 0 < c)
    (_h_split_rate :
      Tendsto (fun n => ((split.foldB n).card : ℝ) / n) atTop (𝓝 c))
    (η_hat : ℕ → Ω → H)
    {Crem : ℝ}
    (_hBR_at :
      ∀ n ω,
        |∫ z, M.m (η_hat n ω) z M.θ₀ ∂P_Z| ≤
          Crem * ((M.ρ₁ (η_hat n ω) M.η₀ : NNReal) : ℝ) *
                 ((M.ρ₂ (η_hat n ω) M.η₀ : NNReal) : ℝ))
    (_h_m_meas :
      ∀ n, Measurable (fun (p : Ω × Z) => M.m (η_hat n p.1) p.2 M.θ₀))
    (_h_m_foldA :
      ∀ n,
        Measurable[MeasurableSpace.comap
          (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance]
          (fun ω z => M.m (η_hat n ω) z M.θ₀))
    (_h_m_foldA_uncurry :
      ∀ n,
        Measurable[(MeasurableSpace.comap
            (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance).prod
          (inferInstance : MeasurableSpace Z)]
          (fun (p : Ω × Z) => M.m (η_hat n p.1) p.2 M.θ₀))
    (_h_m_int :
      ∀ n ω, Integrable (fun z => M.m (η_hat n ω) z M.θ₀) P_Z)
    (_h_m_sq_int :
      ∀ n ω, Integrable (fun z => (M.m (η_hat n ω) z M.θ₀) ^ 2) P_Z)
    (_h_score_diff_rate :
      IsLittleOp
        (fun n ω =>
          (eLpNorm
            (fun z => M.m (η_hat n ω) z M.θ₀ - M.m M.η₀ z M.θ₀) 2 P_Z).toReal)
        (fun _ => (1 : ℝ)) μ)
    (_h_product_rate :
      IsLittleOp
        (fun n ω =>
          ((M.ρ₁ (η_hat n ω) M.η₀ : NNReal) : ℝ) *
            ((M.ρ₂ (η_hat n ω) M.η₀ : NNReal) : ℝ))
        (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) μ) :
    IsAsymLinear
      (dmlChernozhukovEstimator M sample split η_hat)
      M.θ₀
      (fun z => -M.J₀_inv * M.m M.η₀ z M.θ₀)
      sample
      split.foldB := by
  refine ⟨?_, ?_, ?_⟩
  · -- mean_zero
    rw [integral_const_mul]
    rw [show (∫ a, M.m M.η₀ a M.θ₀ ∂P_Z) = 0 by
      simpa [MeanZero] using _hMZ]
    ring
  · -- finite_var
    simpa [mul_pow, mul_assoc, mul_left_comm, mul_comm] using
      (_hFV.const_mul (M.J₀_inv ^ 2))
  · -- remainder: centered fold-B fluctuation plus population remainder.
    let f : ℕ → Ω → Z → ℝ := fun n ω z =>
      M.m (η_hat n ω) z M.θ₀ - M.m M.η₀ z M.θ₀
    let G : ℕ → Ω → ℝ := fun n ω =>
      (Real.sqrt ((split.foldB n).card : ℝ))⁻¹ *
        ∑ i ∈ split.foldB n, (f n ω (sample.Z i ω) -
          ∫ z, f n ω z ∂P_Z)
    let B : ℕ → Ω → ℝ := fun n ω =>
      Real.sqrt ((split.foldB n).card : ℝ) * ∫ z, f n ω z ∂P_Z
    let R : ℕ → Ω → ℝ := fun n ω =>
      Real.sqrt ((split.foldB n).card : ℝ) *
          (dmlChernozhukovEstimator M sample split η_hat n ω - M.θ₀) -
        (Real.sqrt ((split.foldB n).card : ℝ))⁻¹ *
          ∑ i ∈ split.foldB n, (-M.J₀_inv * M.m M.η₀ (sample.Z i ω) M.θ₀)
    haveI : IsProbabilityMeasure P_Z := by
      rw [← sample.law]
      exact Measure.isProbabilityMeasure_map (sample.meas 0).aemeasurable
    have htruth_L2 : MemLp (fun z => M.m M.η₀ z M.θ₀) 2 P_Z :=
      (memLp_two_iff_integrable_sq
        (M.m_meas M.η₀ M.θ₀).aestronglyMeasurable).2 _hFV
    have hf_meas : ∀ n, Measurable (Function.uncurry (f n)) := by
      intro n
      change Measurable (fun p : Ω × Z =>
        M.m (η_hat n p.1) p.2 M.θ₀ - M.m M.η₀ p.2 M.θ₀)
      exact (_h_m_meas n).sub ((M.m_meas M.η₀ M.θ₀).comp measurable_snd)
    have hf_foldA :
        ∀ n,
          Measurable[MeasurableSpace.comap
            (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance]
            (fun ω => f n ω) := by
      intro n
      change Measurable[MeasurableSpace.comap
          (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance]
        (fun ω z => M.m (η_hat n ω) z M.θ₀ - M.m M.η₀ z M.θ₀)
      exact (_h_m_foldA n).sub measurable_const
    have hf_uncurry_foldA :
        ∀ n,
          Measurable[(MeasurableSpace.comap
              (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance).prod
            (inferInstance : MeasurableSpace Z)]
            (Function.uncurry (f n)) := by
      intro n
      change Measurable[(MeasurableSpace.comap
          (fun ω (i : split.foldA n) => sample.Z i ω) inferInstance).prod
        (inferInstance : MeasurableSpace Z)]
        (fun p : Ω × Z => M.m (η_hat n p.1) p.2 M.θ₀ - M.m M.η₀ p.2 M.θ₀)
      exact (_h_m_foldA_uncurry n).sub ((M.m_meas M.η₀ M.θ₀).comp measurable_snd)
    have hf_memLp : ∀ n ω, MemLp (f n ω) 2 P_Z := by
      intro n ω
      have hrand_L2 : MemLp (fun z => M.m (η_hat n ω) z M.θ₀) 2 P_Z :=
        (memLp_two_iff_integrable_sq
          (M.m_meas (η_hat n ω) M.θ₀).aestronglyMeasurable).2 (_h_m_sq_int n ω)
      simpa [f] using hrand_L2.sub htruth_L2
    have hf_rate_one :
        IsLittleOp (fun n ω => (eLpNorm (f n ω) 2 P_Z).toReal)
          (fun _ => (1 : ℝ)) μ := by
      simpa [f] using _h_score_diff_rate
    have hG : IsLittleOp G (fun _ => (1 : ℝ)) μ := by
      simpa [G] using
        foldB_centered_sum_isLittleOp_one sample split f
          hf_meas hf_uncurry_foldA hf_memLp hf_rate_one
    have h_int_eq : ∀ n ω,
        ∫ z, f n ω z ∂P_Z =
          ∫ z, M.m (η_hat n ω) z M.θ₀ ∂P_Z := by
      intro n ω
      have hf_int : Integrable (f n ω) P_Z :=
        (hf_memLp n ω).integrable (by norm_num : (1 : ENNReal) ≤ 2)
      have htruth_int : Integrable (fun z => M.m M.η₀ z M.θ₀) P_Z :=
        htruth_L2.integrable (by norm_num : (1 : ENNReal) ≤ 2)
      have hzero : (∫ z, M.m M.η₀ z M.θ₀ ∂P_Z) = 0 := by
        simpa [MeanZero] using _hMZ
      calc
        ∫ z, f n ω z ∂P_Z =
            ∫ z, (M.m (η_hat n ω) z M.θ₀ - M.m M.η₀ z M.θ₀) ∂P_Z := by rfl
        _ = ∫ z, M.m (η_hat n ω) z M.θ₀ ∂P_Z -
            ∫ z, M.m M.η₀ z M.θ₀ ∂P_Z :=
          integral_sub (_h_m_int n ω) htruth_int
        _ = ∫ z, M.m (η_hat n ω) z M.θ₀ ∂P_Z := by
          rw [hzero]
          ring
    have h_int_raw_rate :
        IsLittleOp (fun n ω => ∫ z, M.m (η_hat n ω) z M.θ₀ ∂P_Z)
          (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) μ := by
      intro ε hε
      rw [ENNReal.tendsto_nhds_zero]
      intro δ hδ
      let K : ℝ := |Crem| + 1
      have hKpos : 0 < K := by
        dsimp [K]
        linarith [abs_nonneg Crem]
      have htarget := (ENNReal.tendsto_nhds_zero.mp
        (_h_product_rate (ε / K) (div_pos hε hKpos))) δ hδ
      exact htarget.mono fun n hn => (measure_mono (by
        intro ω hω
        let prodρ : ℝ :=
          ((M.ρ₁ (η_hat n ω) M.η₀ : NNReal) : ℝ) *
            ((M.ρ₂ (η_hat n ω) M.η₀ : NNReal) : ℝ)
        have hprod_nonneg : 0 ≤ prodρ := by
          dsimp [prodρ]
          exact mul_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)
        have hbr := _hBR_at n ω
        have hbr0 :
            |∫ z, M.m (η_hat n ω) z M.θ₀ ∂P_Z| ≤ Crem * prodρ := by
          simpa [prodρ, mul_assoc] using hbr
        have hle_abs :
            |∫ z, M.m (η_hat n ω) z M.θ₀ ∂P_Z| ≤ |Crem| * prodρ :=
          hbr0.trans (mul_le_mul_of_nonneg_right (le_abs_self Crem) hprod_nonneg)
        have hKbound :
            |∫ z, M.m (η_hat n ω) z M.θ₀ ∂P_Z| ≤ K * prodρ := by
          refine hle_abs.trans ?_
          exact mul_le_mul_of_nonneg_right (by dsimp [K]; linarith) hprod_nonneg
        have hlt_bound :
            ε * ((n : ℝ) ^ (-(1 / 2 : ℝ))) < K * prodρ :=
          lt_of_lt_of_le hω hKbound
        have hdiv_lt :
            (ε * ((n : ℝ) ^ (-(1 / 2 : ℝ)))) / K < prodρ := by
          rw [div_lt_iff₀ hKpos]
          simpa [mul_comm, mul_left_comm, mul_assoc] using hlt_bound
        have hsmall :
            (ε / K) * ((n : ℝ) ^ (-(1 / 2 : ℝ))) < |prodρ| := by
          have hdiv_eq :
              (ε * ((n : ℝ) ^ (-(1 / 2 : ℝ)))) / K =
                (ε / K) * ((n : ℝ) ^ (-(1 / 2 : ℝ))) := by
            ring
          rw [← hdiv_eq]
          simpa [abs_of_nonneg hprod_nonneg] using hdiv_lt
        exact hsmall)).trans hn
    have h_int_rate :
        IsLittleOp (fun n ω => ∫ z, f n ω z ∂P_Z)
          (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) μ := by
      convert h_int_raw_rate using 1
      funext n ω
      exact h_int_eq n ω
    have hB : IsLittleOp B (fun _ => (1 : ℝ)) μ := by
      intro ε' hε'
      rw [ENNReal.tendsto_nhds_zero]
      intro δ hδ
      let C : ℝ := Real.sqrt c + 1
      have hCpos : 0 < C := by
        dsimp [C]
        linarith [Real.sqrt_nonneg c]
      have hCnonneg : 0 ≤ C := le_of_lt hCpos
      have hC2 : c < C ^ 2 := by
        dsimp [C]
        nlinarith [Real.sq_sqrt (le_of_lt _hc_pos), Real.sqrt_nonneg c]
      have hratio_event : ∀ᶠ n in atTop, ((split.foldB n).card : ℝ) / n < C ^ 2 := by
        exact _h_split_rate.eventually_lt_const hC2
      have hn_event : ∀ᶠ n : ℕ in atTop, n ≠ 0 := by
        exact eventually_ne_atTop 0
      have hint_event := (ENNReal.tendsto_nhds_zero.mp
        (h_int_rate (ε' / C) (div_pos hε' hCpos))) δ hδ
      filter_upwards [hratio_event, hn_event, hint_event] with n hratio hn_ne hn
      refine (measure_mono ?_).trans hn
      intro ω hω
      have hn_pos_nat : 0 < n := Nat.pos_of_ne_zero hn_ne
      have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos_nat
      have hn_nonneg : 0 ≤ (n : ℝ) := le_of_lt hn_pos
      have hsqrtn_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_pos
      have hsqrtn_nonneg : 0 ≤ Real.sqrt (n : ℝ) := le_of_lt hsqrtn_pos
      have hcard_le : ((split.foldB n).card : ℝ) ≤ C ^ 2 * (n : ℝ) := by
        have hlt : ((split.foldB n).card : ℝ) < C ^ 2 * (n : ℝ) := by
          field_simp [hn_pos.ne'] at hratio ⊢
          nlinarith
        exact le_of_lt hlt
      have hsqrt_le :
          Real.sqrt ((split.foldB n).card : ℝ) ≤ C * Real.sqrt (n : ℝ) := by
        calc
          Real.sqrt ((split.foldB n).card : ℝ) ≤ Real.sqrt (C ^ 2 * (n : ℝ)) :=
            Real.sqrt_le_sqrt hcard_le
          _ = Real.sqrt (C ^ 2) * Real.sqrt (n : ℝ) := by
            rw [Real.sqrt_mul (sq_nonneg C)]
          _ = C * Real.sqrt (n : ℝ) := by
            rw [Real.sqrt_sq hCnonneg]
      have hsqrtcard_nonneg : 0 ≤ Real.sqrt ((split.foldB n).card : ℝ) :=
        Real.sqrt_nonneg _
      have hlt_prod :
          ε' < Real.sqrt ((split.foldB n).card : ℝ) * |∫ z, f n ω z ∂P_Z| := by
        simpa [B, abs_mul, abs_of_nonneg hsqrtcard_nonneg] using hω
      have hle_prod :
          Real.sqrt ((split.foldB n).card : ℝ) * |∫ z, f n ω z ∂P_Z| ≤
            (C * Real.sqrt (n : ℝ)) * |∫ z, f n ω z ∂P_Z| := by
        exact mul_le_mul_of_nonneg_right hsqrt_le (abs_nonneg _)
      have hlt_bound :
          ε' < (C * Real.sqrt (n : ℝ)) * |∫ z, f n ω z ∂P_Z| :=
        lt_of_lt_of_le hlt_prod hle_prod
      have hrn_eq : (n : ℝ) ^ (-(1 / 2 : ℝ)) = (Real.sqrt (n : ℝ))⁻¹ := by
        rw [Real.rpow_neg hn_nonneg]
        rw [← Real.sqrt_eq_rpow]
      have hdiv_lt :
          ε' / (C * Real.sqrt (n : ℝ)) < |∫ z, f n ω z ∂P_Z| := by
        rw [div_lt_iff₀ (mul_pos hCpos hsqrtn_pos)]
        nlinarith [hlt_bound]
      have hsmall :
          (ε' / C) * ((n : ℝ) ^ (-(1 / 2 : ℝ))) <
            |∫ z, f n ω z ∂P_Z| := by
        rw [hrn_eq]
        convert hdiv_lt using 1
        field_simp [hCpos.ne', hsqrtn_pos.ne']
      exact hsmall
    have hsum : IsLittleOp (fun n ω => G n ω + B n ω) (fun _ => (1 : ℝ)) μ := by
      intro ε' hε'
      rw [ENNReal.tendsto_nhds_zero]
      intro η hη
      by_cases hηtop : η = ⊤
      · filter_upwards with n
        simp [hηtop]
      have hηpos : 0 < η.toReal := ENNReal.toReal_pos (ne_of_gt hη) hηtop
      let α : ℝ := η.toReal / 4
      have hαpos : 0 < α := by
        dsimp [α]
        linarith
      let A : ℕ → Set Ω := fun n => {ω | (ε' / 2) * 1 < |G n ω|}
      let Cset : ℕ → Set Ω := fun n => {ω | (ε' / 2) * 1 < |B n ω|}
      let Dset : ℕ → Set Ω := fun n => {ω | ε' * 1 < |G n ω + B n ω|}
      have hGevent_le := (ENNReal.tendsto_nhds_zero.mp (hG (ε' / 2) (by linarith)))
        (ENNReal.ofReal α) (ENNReal.ofReal_pos.mpr hαpos)
      have hBevent_le := (ENNReal.tendsto_nhds_zero.mp (hB (ε' / 2) (by linarith)))
        (ENNReal.ofReal α) (ENNReal.ofReal_pos.mpr hαpos)
      have htwo_alpha_lt_eta : ENNReal.ofReal (2 * α) < η := by
        rw [ENNReal.ofReal_lt_iff_lt_toReal]
        · dsimp [α]
          linarith
        · dsimp [α]
          linarith [le_of_lt hηpos]
        · exact hηtop
      filter_upwards [hGevent_le, hBevent_le] with n hGA hBC
      have hsubset : Dset n ⊆ A n ∪ Cset n := by
        intro ω hω
        by_contra hnot
        have hnotA : ¬ (ε' / 2) * 1 < |G n ω| := by
          intro hx
          exact hnot (Or.inl hx)
        have hnotC : ¬ (ε' / 2) * 1 < |B n ω| := by
          intro hy
          exact hnot (Or.inr hy)
        have hGle : |G n ω| ≤ (ε' / 2) * 1 := le_of_not_gt hnotA
        have hBle : |B n ω| ≤ (ε' / 2) * 1 := le_of_not_gt hnotC
        have hsum_le : |G n ω + B n ω| ≤ ε' * 1 := by
          calc
            |G n ω + B n ω| ≤ |G n ω| + |B n ω| :=
              abs_add_le (G n ω) (B n ω)
            _ ≤ (ε' / 2) * 1 + (ε' / 2) * 1 := add_le_add hGle hBle
            _ = ε' * 1 := by ring
        exact not_lt_of_ge hsum_le hω
      exact le_of_lt <| calc
        μ {ω | ε' * 1 < |G n ω + B n ω|} = μ (Dset n) := by
          simp [Dset]
        _ ≤ μ (A n ∪ Cset n) := measure_mono hsubset
        _ ≤ μ (A n) + μ (Cset n) := MeasureTheory.measure_union_le (A n) (Cset n)
        _ ≤ ENNReal.ofReal α + ENNReal.ofReal α := add_le_add hGA hBC
        _ = ENNReal.ofReal (2 * α) := by
          rw [← ENNReal.ofReal_add]
          · congr 1
            ring
          · linarith
          · linarith
        _ < η := htwo_alpha_lt_eta
    have const_mul_isLittleOp_one : ∀ (a : ℝ) (X : ℕ → Ω → ℝ),
        IsLittleOp X (fun _ => (1 : ℝ)) μ →
          IsLittleOp (fun n ω => a * X n ω) (fun _ => (1 : ℝ)) μ := by
      intro a X hX ε hε
      by_cases ha : a = 0
      · subst a
        have hzero :
            (fun n => μ {ω | ε * (fun _ => (1 : ℝ)) n < |0 * X n ω|}) =
              fun _ => (0 : ENNReal) := by
          funext n
          simp [hε.not_gt]
        rw [hzero]
        exact tendsto_const_nhds
      · have hscale_pos : 0 < ε / |a| := div_pos hε (abs_pos.mpr ha)
        have hXt := hX (ε / |a|) hscale_pos
        refine hXt.congr' ?_
        filter_upwards with n
        congr 1
        ext ω
        simp only [Set.mem_setOf_eq, mul_one, abs_mul]
        rw [div_lt_iff₀ (abs_pos.mpr ha)]
        ring_nf
    have hdecomp : R = fun n ω => -M.J₀_inv * (G n ω + B n ω) := by
      funext n ω
      unfold R G B f dmlChernozhukovEstimator
      by_cases hcard : (split.foldB n).card = 0
      · simp [hcard]
      · have hcard_pos : 0 < ((split.foldB n).card : ℝ) := by
          exact_mod_cast Nat.pos_of_ne_zero hcard
        have hsqrt_pos : 0 < Real.sqrt ((split.foldB n).card : ℝ) :=
          Real.sqrt_pos.mpr hcard_pos
        have hsqrt_sq :
            Real.sqrt ((split.foldB n).card : ℝ) *
                Real.sqrt ((split.foldB n).card : ℝ) =
              ((split.foldB n).card : ℝ) :=
          Real.mul_self_sqrt hcard_pos.le
        field_simp [hsqrt_pos.ne', hsqrt_sq]
        simp [Finset.sum_add_distrib, Finset.sum_neg_distrib,
          Finset.sum_const, nsmul_eq_mul, sub_eq_add_neg, ← Finset.mul_sum]
        ring
    change IsLittleOp R (fun _ => (1 : ℝ)) μ
    rw [hdecomp]
    exact const_mul_isLittleOp_one (-M.J₀_inv) (fun n ω => G n ω + B n ω) hsum

end OrthogonalMoments
end Estimation
end Causalean
