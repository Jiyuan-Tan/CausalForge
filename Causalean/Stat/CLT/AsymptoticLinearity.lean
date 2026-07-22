/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Asymptotic linearity of estimators

Predicate `IsAsymLinear θn θ₀ ψ S` matching `def:est-asym-linear` in
`doc/basic_concepts/po/estimation.tex`, plus the headline corollary that
asymptotic linearity implies `√n`-asymptotic normality
(`prop:est-al-implies-an`).

`gaussianMeasure m σ²` is a real-typed wrapper around Mathlib's
`ProbabilityTheory.gaussianReal` so the rest of the project does not need to
juggle `NNReal` for the variance.  The CLT contact-point lemma
`IIDSample.clt_normalized_sum` consumes the upstream CLT formalisation and
packages it as convergence in distribution for the project's normalized
i.i.d. sums.
-/

import Clt.CLT
import Causalean.Stat.Sample
import Causalean.Stat.Limit.Convergence

/-! # Scalar Asymptotic Linearity

This file provides the scalar asymptotic-linearity interface used by the
estimation and inference layers. `gaussianMeasure` is the project's real-valued
Gaussian wrapper, and `IsAsymLinear` records a mean-zero influence function,
finite second moment, and an `o_p(1)` linearization remainder along a chosen
finite index family.

The namespace also exposes `IsAsymLinear.normalizedSum` and
`IsAsymLinear.rescaledEstimator`. The main limit results are
`IIDSample.clt_normalized_sum`, the CLT contact point for normalized i.i.d.
sums, `Tendsto_dist.add_isLittleOp_one` and related Slutsky/congruence
wrappers, and `IsAsymLinear.tendsto_normal`, which turns full-sample scalar
asymptotic linearity into asymptotic normality. -/

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Filter Topology

/-! ## Gaussian measure on ℝ

Real-typed alias for `ProbabilityTheory.gaussianReal`.  Negative variances
collapse to `0` (Dirac mass at `m`) via `Real.toNNReal`. -/

/-- Gaussian measure on `ℝ` with mean `m` and variance `v`.  Real-typed
wrapper around `ProbabilityTheory.gaussianReal`; if `v < 0` the variance is
clipped to `0` and the measure degenerates to `Measure.dirac m`. -/
noncomputable def gaussianMeasure (m v : ℝ) : Measure ℝ :=
  gaussianReal m v.toNNReal

/-- `gaussianMeasure m v` is a probability measure for every real `m, v`. -/
instance instIsProbabilityMeasureGaussianMeasure (m v : ℝ) :
    IsProbabilityMeasure (gaussianMeasure m v) := by
  unfold gaussianMeasure
  infer_instance

/-! ## Asymptotic linearity -/

/-- An estimator is asymptotically linear when its scaled estimation error
equals the normalized empirical average of a mean-zero, square-integrable
influence function plus a term that is negligible in probability.

The finite index set attached to each sample size chooses which observations
enter the empirical average:

* `mean_zero`  : `∫ ψ dP = 0`.
* `finite_var` : `∫ ψ² dP < ∞`.
* `remainder`  : `√|I n| (θn n − θ₀) − (1/√|I n|) Σ_{i ∈ I n} ψ (Z_i) = o_p(1)`.

The full-sample case is `I n = Finset.range n` and recovers the classical
asymptotic-linearity definition (`prop:est-al-implies-an`).  For sample-split
estimators, `I n = split.foldB n` gives the fold-B asymptotic linearity
(`thm:est-plug-in-ate-al`, `thm:est-dml-ate-al`); under a fixed split ratio
`|B(n)|/n → c ∈ (0, 1)`, the fold-B form implies √n-asymptotic normality
with variance `σ²/c` (the standard sample-splitting cost). -/
structure IsAsymLinear {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {μ : Measure Ω} {P : Measure X}
    (θn : ℕ → Ω → ℝ) (θ₀ : ℝ) (ψ : X → ℝ)
    (S : IIDSample Ω X μ P) (I : ℕ → Finset ℕ) : Prop where
  mean_zero  : ∫ x, ψ x ∂P = 0
  finite_var : Integrable (fun x => (ψ x) ^ 2) P
  remainder  :
    IsLittleOp
      (fun n ω =>
        Real.sqrt ((I n).card : ℝ) * (θn n ω - θ₀)
          - (Real.sqrt ((I n).card : ℝ))⁻¹ *
            ∑ i ∈ I n, ψ (S.Z i ω))
      (fun _ => (1 : ℝ)) μ

namespace IsAsymLinear

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X} [IsProbabilityMeasure μ]
  {θn : ℕ → Ω → ℝ} {θ₀ : ℝ} {ψ : X → ℝ} {S : IIDSample Ω X μ P}

/-- The normalised partial sum `(1/√|I n|) Σ_{i ∈ I n} ψ(Z_i)`. -/
noncomputable def normalizedSum (S : IIDSample Ω X μ P) (ψ : X → ℝ)
    (I : ℕ → Finset ℕ) (n : ℕ) : Ω → ℝ :=
  fun ω => (Real.sqrt ((I n).card : ℝ))⁻¹ * ∑ i ∈ I n, ψ (S.Z i ω)

/-- The rescaled estimator `√|I n| (θn n − θ₀)`. -/
noncomputable def rescaledEstimator (θn : ℕ → Ω → ℝ) (θ₀ : ℝ)
    (I : ℕ → Finset ℕ) (n : ℕ) : Ω → ℝ :=
  fun ω => Real.sqrt ((I n).card : ℝ) * (θn n ω - θ₀)

end IsAsymLinear

/-! ## CLT contact point

`IIDSample.clt_normalized_sum` is the only place where the upstream CLT
dependency is consumed.  It says: along an i.i.d. sample with mean-zero,
square-integrable transform `ψ`, the normalised partial sum
`(1/√n) Σ_{i<n} ψ(Z_i)` converges in distribution to `N(0, ∫ ψ² dP)` under the
ambient measure `μ`.
-/
/-- **Central limit theorem for normalised sample sums.** Along an i.i.d.
sample, for any measurable, mean-zero, square-integrable transform of the
observations, the normalised partial sum (the sum of the transformed
observations divided by the square root of the sample size) converges in
distribution to a centred normal law whose variance is the population second
moment of the transform. This is the single contact point through which the
upstream CLT enters the estimation theory. -/
theorem IIDSample.clt_normalized_sum
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {μ : Measure Ω} {P : Measure X} [IsProbabilityMeasure μ]
    (S : IIDSample Ω X μ P) {ψ : X → ℝ}
    (hψ_meas : Measurable ψ)
    (hψ_mean : ∫ x, ψ x ∂P = 0)
    (hψ_sq_int : Integrable (fun x => (ψ x) ^ 2) P)
    (hSum_meas : ∀ n, AEMeasurable
      (IsAsymLinear.normalizedSum S ψ (fun m => Finset.range m) n) μ) :
    Tendsto_dist
      (IsAsymLinear.normalizedSum S ψ (fun m => Finset.range m))
      (gaussianMeasure 0 (∫ x, (ψ x) ^ 2 ∂P))
      μ
      hSum_meas := by
  let σ2 : ℝ := ∫ x, (ψ x) ^ 2 ∂P
  have hσ2_nonneg : 0 ≤ σ2 := by
    dsimp [σ2]
    exact integral_nonneg fun x => sq_nonneg (ψ x)
  by_cases hσ2_zero : σ2 = 0
  · have hsq_zero_ae : (fun x => (ψ x) ^ 2) =ᵐ[P] 0 := by
      exact (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (ψ x)) hψ_sq_int).1 hσ2_zero
    have hψ_zero_ae : ψ =ᵐ[P] 0 := by
      filter_upwards [hsq_zero_ae] with x hx
      exact eq_zero_of_pow_eq_zero hx
    have hlaw_i : ∀ i, μ.map (S.Z i) = P := by
      intro i
      rw [← (S.identDist i).map_eq, S.law]
    have hY_zero_ae : ∀ i, (fun ω => ψ (S.Z i ω)) =ᵐ[μ] 0 := by
      intro i
      have hset : MeasurableSet {x | ψ x = 0} := hψ_meas (measurableSet_singleton 0)
      have hmap : ∀ᵐ x ∂μ.map (S.Z i), ψ x = 0 := by
        simpa [hlaw_i i] using hψ_zero_ae
      rwa [ae_map_iff (S.meas i).aemeasurable hset] at hmap
    have hnorm_zero_ae : ∀ n,
        IsAsymLinear.normalizedSum S ψ (fun m => Finset.range m) n =ᵐ[μ] 0 := by
      intro n
      rw [Filter.EventuallyEq]
      have hfin : ∀ᶠ ω in ae μ, ∀ i ∈ Finset.range n, ψ (S.Z i ω) = 0 := by
        simpa using (Finset.eventually_all (Finset.range n)).2 fun i _ => hY_zero_ae i
      filter_upwards [hfin] with ω hω
      have hsum : ∑ i ∈ Finset.range n, ψ (S.Z i ω) = 0 := by
        exact Finset.sum_eq_zero fun i hi => hω i hi
      simp [IsAsymLinear.normalizedSum, hsum]
    have hmap_zero : ∀ n,
        μ.map (IsAsymLinear.normalizedSum S ψ (fun m => Finset.range m) n)
          = Measure.dirac 0 := by
      intro n
      rw [Measure.map_congr (hnorm_zero_ae n)]
      change μ.map (fun _ : Ω => (0 : ℝ)) = Measure.dirac 0
      rw [Measure.map_const]
      simp
    unfold Tendsto_dist
    have hseq :
        (fun n =>
          (⟨μ.map (IsAsymLinear.normalizedSum S ψ (fun m => Finset.range m) n),
              Measure.isProbabilityMeasure_map (hSum_meas n)⟩ : ProbabilityMeasure ℝ))
          = fun _ => (⟨Measure.dirac 0, inferInstance⟩ : ProbabilityMeasure ℝ) := by
      funext n
      apply Subtype.ext
      exact hmap_zero n
    have htarget :
        (⟨gaussianMeasure 0 (∫ x, (ψ x) ^ 2 ∂P),
            instIsProbabilityMeasureGaussianMeasure 0 (∫ x, (ψ x) ^ 2 ∂P)⟩ : ProbabilityMeasure ℝ)
          = (⟨Measure.dirac 0, inferInstance⟩ : ProbabilityMeasure ℝ) := by
      apply Subtype.ext
      simp [gaussianMeasure, σ2, hσ2_zero, gaussianReal_zero_var]
    rw [hseq, htarget]
    exact tendsto_const_nhds
  · have hσ2_pos : 0 < σ2 := lt_of_le_of_ne hσ2_nonneg (Ne.symm hσ2_zero)
    let σ : ℝ := Real.sqrt σ2
    have hσ_pos : 0 < σ := by
      dsimp [σ]
      exact Real.sqrt_pos.2 hσ2_pos
    have hσ_ne : σ ≠ 0 := ne_of_gt hσ_pos
    let Y : ℕ → Ω → ℝ := fun i ω => ψ (S.Z i ω) / σ
    have hY_meas : ∀ i, Measurable (Y i) := by
      intro i
      exact (hψ_meas.comp (S.meas i)).div_const σ
    let μprob : ProbabilityMeasure Ω := ⟨μ, inferInstance⟩
    have hlaw0 : μ.map (S.Z 0) = P := S.law
    have hmean0 : μprob[Y 0] = 0 := by
      change ∫ ω, ψ (S.Z 0 ω) / σ ∂μ = 0
      rw [integral_div]
      have hmap_int : ∫ ω, ψ (S.Z 0 ω) ∂μ = ∫ x, ψ x ∂P := by
        calc
          ∫ ω, ψ (S.Z 0 ω) ∂μ
              = ∫ x, ψ x ∂(μ.map (S.Z 0)) := by
                rw [integral_map (S.meas 0).aemeasurable hψ_meas.aestronglyMeasurable]
          _ = ∫ x, ψ x ∂P := by rw [hlaw0]
      rw [hmap_int, hψ_mean, zero_div]
    have hsq_int_Z0 : Integrable (fun ω => (ψ (S.Z 0 ω)) ^ 2) μ := by
      have hmap_int : Integrable (fun x => (ψ x) ^ 2) (μ.map (S.Z 0)) := by
        simpa [hlaw0] using hψ_sq_int
      exact hmap_int.comp_measurable (S.meas 0)
    have hvar1 : μprob[Y 0 ^ 2] = 1 := by
      change ∫ ω, (ψ (S.Z 0 ω) / σ) ^ 2 ∂μ = 1
      have hmap_sq : ∫ ω, (ψ (S.Z 0 ω)) ^ 2 ∂μ = σ2 := by
        dsimp [σ2]
        calc
          ∫ ω, (ψ (S.Z 0 ω)) ^ 2 ∂μ
              = ∫ x, (ψ x) ^ 2 ∂(μ.map (S.Z 0)) := by
                rw [integral_map (S.meas 0).aemeasurable]
                exact (hψ_meas.pow_const 2).aestronglyMeasurable
          _ = ∫ x, (ψ x) ^ 2 ∂P := by rw [hlaw0]
      calc
        ∫ ω, (ψ (S.Z 0 ω) / σ) ^ 2 ∂μ
            = (∫ ω, (ψ (S.Z 0 ω)) ^ 2 ∂μ) / σ ^ 2 := by
              rw [← integral_div]
              · congr with ω
                ring
        _ = σ2 / σ ^ 2 := by rw [hmap_sq]
        _ = 1 := by
          rw [show σ ^ 2 = σ2 by
            dsimp [σ]
            exact Real.sq_sqrt hσ2_nonneg]
          field_simp [hσ2_pos.ne']
    have hindep : iIndepFun Y μ := by
      simpa [Y, Function.comp_def] using
        S.indep.comp (fun _ x => ψ x / σ) (fun _ => hψ_meas.div_const σ)
    have hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ := by
      intro i
      simpa [Y, Function.comp_def] using
        (S.identDist i).symm.comp (hψ_meas.div_const σ)
    have hclt :
        Tendsto (fun n : ℕ => μprob.map (aemeasurable_invSqrtMulSum n hY_meas))
          atTop (𝓝 stdGaussian) :=
      ProbabilityTheory.central_limit hY_meas hmean0 hvar1 hindep hident
    have hcont : Continuous (fun x : ℝ => σ * x) := continuous_const.mul continuous_id
    have hscaled :=
      ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
        (fun n : ℕ => μprob.map (aemeasurable_invSqrtMulSum n hY_meas))
        stdGaussian hclt hcont
    unfold Tendsto_dist
    convert hscaled using 1
    · funext n
      apply Subtype.ext
      change (μ.map (IsAsymLinear.normalizedSum S ψ (fun m => Finset.range m) n))
        = Measure.map (fun x : ℝ => σ * x) (Measure.map (invSqrtMulSum Y n) μ)
      rw [Measure.map_map]
      · apply Measure.map_congr
        filter_upwards with ω
        simp only [Function.comp_apply]
        dsimp [IsAsymLinear.normalizedSum, invSqrtMulSum, Y]
        rw [show ((Finset.range n).card : ℝ) = (n : ℝ) by simp [Finset.card_range]]
        rw [← Fin.sum_univ_eq_sum_range]
        calc
          (Real.sqrt (n : ℝ))⁻¹ * ∑ i : Fin n, ψ (S.Z i ω)
              = σ * ((Real.sqrt (n : ℝ))⁻¹ * ∑ i : Fin n, ψ (S.Z i ω) / σ) := by
                rw [← Finset.sum_div Finset.univ (fun i : Fin n => ψ (S.Z i ω)) σ]
                field_simp [hσ_ne]
          _ = σ * ((Real.sqrt (n : ℝ))⁻¹ * ∑ i : Fin n, Y i ω) := by
                rfl
      · exact hcont.measurable
      · exact (measurable_invSqrtMulSum n hY_meas)
    · congr 1
      apply Subtype.ext
      change gaussianMeasure 0 (∫ x, (ψ x) ^ 2 ∂P)
        = Measure.map (fun x : ℝ => σ * x) (stdGaussian : Measure ℝ)
      simp [gaussianMeasure, stdGaussian, σ2, σ, gaussianReal_map_const_mul,
        Real.sq_sqrt hσ2_nonneg, Real.toNNReal_of_nonneg hσ2_nonneg]

/-! ## Slutsky absorption at the `Tendsto_dist` level

Adding an `o_p(1)` perturbation to a sequence converging in distribution
preserves the limit.  Mathlib has the analogous fact for
`MeasureTheory.TendstoInDistribution`
(`tendstoInDistribution_of_tendstoInMeasure_sub`); here we restate it for
our measure-level wrapper. -/

/-- If `Xn ⇒ Q` in distribution and `Yn − Xn = o_p(1)`, then `Yn ⇒ Q`. -/
theorem Tendsto_dist.add_isLittleOp_one
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Xn Yn : ℕ → Ω → ℝ} {Q : Measure ℝ} [IsProbabilityMeasure Q]
    (hXn : ∀ n, AEMeasurable (Xn n) μ)
    (hYn : ∀ n, AEMeasurable (Yn n) μ)
    (hX : Tendsto_dist Xn Q μ hXn)
    (hRem : IsLittleOp (fun n ω => Yn n ω - Xn n ω) (fun _ => (1 : ℝ)) μ) :
    Tendsto_dist Yn Q μ hYn := by
  have hXY : TendstoInMeasure μ (fun n ω => Yn n ω - Xn n ω) atTop (0 : Ω → ℝ) := by
    rw [tendstoInMeasure_iff_norm]
    intro ε hε
    have hhalf : 0 < ε / 2 := by positivity
    have hrem : Tendsto (fun n => μ {ω | ε / 2 < |Yn n ω - Xn n ω|}) atTop (𝓝 0) := by
      simpa using hRem (ε / 2) hhalf
    rw [ENNReal.tendsto_nhds_zero] at hrem ⊢
    intro δ hδ
    filter_upwards [hrem δ hδ] with n hn
    have hsubset :
        {x | ε ≤ ‖Yn n x - Xn n x - (0 : Ω → ℝ) x‖}
          ⊆ {ω | ε / 2 < |Yn n ω - Xn n ω|} := by
      intro ω hω
      have hω' : ε ≤ |Yn n ω - Xn n ω| := by
        simpa [Real.norm_eq_abs] using hω
      exact lt_of_lt_of_le (by linarith) hω'
    exact le_trans (measure_mono hsubset) hn
  unfold Tendsto_dist at hX ⊢
  suffices ∀ (F : ℝ → ℝ) (hF_bounded : ∃ (C : ℝ), ∀ x y, dist (F x) (F y) ≤ C)
      (hF_lip : ∃ L, LipschitzWith L F),
      Tendsto (fun n ↦ ∫ y, F y ∂(μ.map (Yn n))) atTop (𝓝 (∫ y, F y ∂Q)) by
    rwa [tendsto_iff_forall_lipschitz_integral_tendsto]
  rintro F ⟨M, hF_bounded⟩ ⟨L, hF_lip⟩
  have hF_cont : Continuous F := hF_lip.continuous
  obtain rfl | hL := eq_zero_or_pos L
  · simp only [LipschitzWith.zero_iff] at hF_lip
    specialize hF_lip (0 : ℝ)
    simp only [← hF_lip, integral_const, smul_eq_mul]
    have h_prob n : IsProbabilityMeasure (μ.map (Yn n)) := Measure.isProbabilityMeasure_map (hYn n)
    simp
  simp_rw [Metric.tendsto_nhds, Real.dist_eq]
  suffices ∀ ε > 0, ∀ᶠ n in atTop, |∫ y, F y ∂(μ.map (Yn n)) - ∫ y, F y ∂Q| < L * ε by
    intro ε hε
    convert this (ε / L) (by positivity)
    field_simp
  intro ε hε
  have h_le n : |∫ y, F y ∂(μ.map (Yn n)) - ∫ y, F y ∂Q|
      ≤ L * (ε / 2) + M * μ.real {ω | ε / 2 ≤ ‖Yn n ω - Xn n ω‖}
        + |∫ y, F y ∂(μ.map (Xn n)) - ∫ y, F y ∂Q| := by
    refine (abs_sub_le (∫ y, F y ∂(μ.map (Yn n))) (∫ y, F y ∂(μ.map (Xn n)))
      (∫ y, F y ∂Q)).trans ?_
    gcongr
    have h_int_Y : Integrable (fun x ↦ F (Yn n x)) μ := by
      refine Integrable.of_bound (by fun_prop) (‖F (0 : ℝ)‖ + M) (ae_of_all _ fun a ↦ ?_)
      specialize hF_bounded (Yn n a) 0
      rw [← sub_le_iff_le_add']
      exact (abs_sub_abs_le_abs_sub (F (Yn n a)) (F 0)).trans hF_bounded
    have h_int_X : Integrable (fun x ↦ F (Xn n x)) μ := by
      refine Integrable.of_bound (by fun_prop) (‖F (0 : ℝ)‖ + M) (ae_of_all _ fun a ↦ ?_)
      specialize hF_bounded (Xn n a) 0
      rw [← sub_le_iff_le_add']
      exact (abs_sub_abs_le_abs_sub (F (Xn n a)) (F 0)).trans hF_bounded
    have h_int_sub : Integrable (fun a ↦ ‖F (Yn n a) - F (Xn n a)‖) μ := by
      rw [integrable_norm_iff (by fun_prop)]
      exact h_int_Y.sub h_int_X
    rw [integral_map (by fun_prop) (by fun_prop), integral_map (by fun_prop) (by fun_prop),
      ← integral_sub h_int_Y h_int_X, ← Real.norm_eq_abs]
    calc ‖∫ a, F (Yn n a) - F (Xn n a) ∂μ‖
    _ ≤ ∫ a, ‖F (Yn n a) - F (Xn n a)‖ ∂μ := norm_integral_le_integral_norm _
    _ = ∫ a in {x | ‖Yn n x - Xn n x‖ < ε / 2}, ‖F (Yn n a) - F (Xn n a)‖ ∂μ
        + ∫ a in {x | ε / 2 ≤ ‖Yn n x - Xn n x‖}, ‖F (Yn n a) - F (Xn n a)‖ ∂μ := by
      symm
      simp_rw [← not_lt]
      refine integral_add_compl₀ ?_ h_int_sub
      exact nullMeasurableSet_lt (by fun_prop) (by fun_prop)
    _ ≤ ∫ a in {x | ‖Yn n x - Xn n x‖ < ε / 2}, L * (ε / 2) ∂μ
        + ∫ a in {x | ε / 2 ≤ ‖Yn n x - Xn n x‖}, M ∂μ := by
      gcongr ?_ + ?_
      · refine setIntegral_mono_on₀ h_int_sub.integrableOn integrableOn_const ?_ ?_
        · exact nullMeasurableSet_lt (by fun_prop) (by fun_prop)
        · exact fun x hx ↦ hF_lip.norm_sub_le_of_le hx.le
      · refine setIntegral_mono h_int_sub.integrableOn integrableOn_const fun a ↦ ?_
        rw [← dist_eq_norm]
        convert hF_bounded _ _
    _ = L * (ε / 2) * μ.real {x | ‖Yn n x - Xn n x‖ < ε / 2}
        + M * μ.real {ω | ε / 2 ≤ ‖Yn n ω - Xn n ω‖} := by
      simp only [integral_const, MeasurableSet.univ, measureReal_restrict_apply, Set.univ_inter,
        smul_eq_mul]
      ring
    _ ≤ L * (ε / 2) + M * μ.real {ω | ε / 2 ≤ ‖Yn n ω - Xn n ω‖} := by
      rw [mul_assoc]
      gcongr
      grw [measureReal_le_one, mul_one]
  have h_tendsto :
      Tendsto (fun n ↦ L * (ε / 2) + M * μ.real {ω | ε / 2 ≤ ‖Yn n ω - Xn n ω‖}
        + |∫ y, F y ∂(μ.map (Xn n)) - ∫ y, F y ∂Q|) atTop (𝓝 (L * ε / 2)) := by
    suffices Tendsto (fun n ↦ L * (ε / 2) + M * μ.real {ω | ε / 2 ≤ ‖Yn n ω - Xn n ω‖}
        + |∫ y, F y ∂(μ.map (Xn n)) - ∫ y, F y ∂Q|) atTop (𝓝 (L * ε / 2 + M * 0 + 0)) by
      simpa
    refine (Tendsto.add ?_ (Tendsto.const_mul _ ?_)).add ?_
    · rw [mul_div_assoc]
      exact tendsto_const_nhds
    · simp only [tendstoInMeasure_iff_measureReal_norm, Pi.zero_apply, sub_zero] at hXY
      exact hXY (ε / 2) (by positivity)
    · simp_rw [tendsto_iff_forall_lipschitz_integral_tendsto] at hX
      simpa [tendsto_iff_dist_tendsto_zero] using hX F ⟨M, hF_bounded⟩ ⟨L, hF_lip⟩
  have h_lt : L * ε / 2 < L * ε := half_lt_self (by positivity)
  filter_upwards [h_tendsto.eventually_lt_const h_lt] with n hn using (h_le n).trans_lt hn

/-- Convergence in distribution is invariant under eventual a.e. equality of
the random variables. -/
theorem Tendsto_dist.congr_ae
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Xn Yn : ℕ → Ω → ℝ} {Q : Measure ℝ} [IsProbabilityMeasure Q]
    (hXn : ∀ n, AEMeasurable (Xn n) μ)
    (hYn : ∀ n, AEMeasurable (Yn n) μ)
    (hX : Tendsto_dist Xn Q μ hXn)
    (hXY : ∀ᶠ n in atTop, Xn n =ᵐ[μ] Yn n) :
    Tendsto_dist Yn Q μ hYn := by
  unfold Tendsto_dist at hX ⊢
  refine hX.congr' ?_
  filter_upwards [hXY] with n hn
  apply Subtype.ext
  exact Measure.map_congr hn

/-- Deterministic-scalar Slutsky for Gaussian limits, phrased for the
project's measure-level `Tendsto_dist` wrapper.

If `Xn ⇒ N(0, v)` and deterministic scalars `a n → a₀`, then
`a n • Xn ⇒ N(0, a₀² v)`.  This is the Gaussian specialization of the
measure-level deterministic-scalar Slutsky wrapper. -/
theorem Tendsto_dist.const_mul_tendsto_gaussian
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Xn : ℕ → Ω → ℝ} {a : ℕ → ℝ} {a₀ v : ℝ}
    (hXn : ∀ n, AEMeasurable (Xn n) μ)
    (hScaled : ∀ n, AEMeasurable (fun ω => a n * Xn n ω) μ)
    (hX : Tendsto_dist Xn (gaussianMeasure 0 v) μ hXn)
    (ha : Tendsto a atTop (𝓝 a₀)) :
    Tendsto_dist (fun n ω => a n * Xn n ω)
      (gaussianMeasure 0 (a₀ ^ 2 * v)) μ hScaled := by
  haveI : IsProbabilityMeasure ((gaussianMeasure 0 v).map (fun x : ℝ => a₀ * x)) :=
    Measure.isProbabilityMeasure_map (measurable_const.mul measurable_id).aemeasurable
  have hscaled_dist :
      Tendsto_dist (fun n ω => a n * Xn n ω)
        ((gaussianMeasure 0 v).map (fun x : ℝ => a₀ * x)) μ hScaled :=
    Tendsto_dist.const_mul_tendsto hXn hScaled hX ha
  have hmap :
      (gaussianMeasure 0 v).map (fun x : ℝ => a₀ * x)
        = gaussianMeasure 0 (a₀ ^ 2 * v) := by
    simp [gaussianMeasure, gaussianReal_map_const_mul, mul_zero,
      Real.toNNReal_mul (sq_nonneg a₀), Real.toNNReal_of_nonneg (sq_nonneg a₀)]
  simpa [hmap] using hscaled_dist

/-! ## Asymptotic linearity ⇒ asymptotic normality

The headline statement.  Combines `IIDSample.clt_normalized_sum` (the CLT
contact point) with `Tendsto_dist.add_isLittleOp_one` (Slutsky). -/

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X} [IsProbabilityMeasure μ]
  {θn : ℕ → Ω → ℝ} {θ₀ : ℝ} {ψ : X → ℝ} {S : IIDSample Ω X μ P}

/-- Asymptotic linearity implies `√n (θn − θ₀) ⇒ N(0, ∫ ψ² dP)`.

The Gaussian target is `gaussianMeasure 0 σ²` where `σ² = ∫ ψ² dP`.  The
measurability hypothesis on the rescaled estimator and the partial sum is
imposed at the call site (proof obligations the caller carries). -/
theorem IsAsymLinear.tendsto_normal
    (h : IsAsymLinear θn θ₀ ψ S (fun m => Finset.range m))
    (hψ_meas : Measurable ψ)
    (hθn_meas : ∀ n : ℕ, AEMeasurable
      (IsAsymLinear.rescaledEstimator θn θ₀ (fun m => Finset.range m) n) μ)
    (hSum_meas : ∀ n : ℕ, AEMeasurable
      (IsAsymLinear.normalizedSum S ψ (fun m => Finset.range m) n) μ) :
    Tendsto_dist
      (IsAsymLinear.rescaledEstimator θn θ₀ (fun m => Finset.range m))
      (gaussianMeasure 0 (∫ x, (ψ x) ^ 2 ∂P))
      μ
      hθn_meas := by
  have hCLT :=
    IIDSample.clt_normalized_sum S hψ_meas h.mean_zero h.finite_var hSum_meas
  refine Tendsto_dist.add_isLittleOp_one hSum_meas hθn_meas hCLT ?_
  -- `IsAsymLinear.remainder` uses `(I n).card` with `I = Finset.range`, which
  -- equals `n`; the resulting `IsLittleOp` matches the Slutsky absorption form.
  have := h.remainder
  simpa [IsAsymLinear.normalizedSum, IsAsymLinear.rescaledEstimator,
    Finset.card_range] using this

end Causalean.Stat
