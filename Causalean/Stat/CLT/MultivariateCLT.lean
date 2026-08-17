/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Multivariate central limit theorem (Cramér–Wold)

The vector analogue of `IIDSample.clt_normalized_sum`
(`Causalean/Stat/CLT/AsymptoticLinearity.lean`).  For a vector-valued influence
function `ψ : X → E` (`E` a finite-dimensional real inner-product space) the
normalised i.i.d. sum `(1/√n) Σ_{i<n} ψ(Zᵢ)` converges in distribution to the
Gaussian limit with covariance `Σ = E[ψ ψᵀ]`.

The proof is the **Cramér–Wold device**: weak convergence on `E` is equivalent
to pointwise convergence of characteristic functions (Lévy continuity,
`MeasureTheory.ProbabilityMeasure.tendsto_iff_tendsto_charFun` from the `Clt`
package), and each value `charFun(μ.map vecNS)(t)` equals the *scalar* char.
function of the projected sum `⟪t, vecNS⟫ = (1/√n) Σ ⟪t, ψ(Zᵢ)⟫`, to which the
already-proven scalar CLT applies.  This discharges the multivariate CLT
contact `_hCLT` taken as a hypothesis by
`IsAsymLinearVec.tendsto_normal_vec` and `deltaMethod` (the vector Δ-method).

## Status of the limit law

The genuinely reusable content here is the Cramér–Wold reduction and the
per-direction charFun limit `charFun(μ.map vecNS)(t) → exp(−½ ∫⟪t,ψ⟫² dP)`.
The theorems below state the limit *abstractly*, taking the target
`Q : Measure E` together with the hypothesis that its characteristic function is
the Gaussian one
(`charFun Q t = exp(−½ ∫⟪t,ψ⟫² dP)`).

This abstract hypothesis is **discharged concretely** in
`Causalean/Stat/CLT/GaussianLimit.lean`: the multivariate-Gaussian characteristic
function is proven in the current Mathlib pin
(`ProbabilityTheory.IsGaussian.charFun_eq'`), so `GaussianLimit` constructs the
covariance-`Σ` Gaussian `gaussianLimit ψ` explicitly (as `stdGaussian.map √Σ`,
with `Σ` the second-moment operator of `ψ` and `√Σ` its positive operator
square root) and proves `IIDSample.clt_normalizedSum_vec` with no abstract `Q`
or charFun hypothesis remaining.  The abstract theorems here remain the reusable
Cramér–Wold core that `GaussianLimit` specialises.

Key declarations:

* `inner_normalizedSum` : `⟪t, vecNS n ω⟫ = scalarNS_{⟪t,ψ⟫} n ω` (projection).
* `IIDSample.normalizedSum_vec_charFun_tendsto` : the per-direction charFun
  limit.
* `Tendsto_dist_vec.of_charFun_tendsto` : Cramér–Wold wrapper (pointwise
  charFun convergence ⇒ weak convergence).
* `IIDSample.clt_normalizedSum_vec_of_charFun` : the multivariate CLT contact
  for an abstract Gaussian-charFun target `Q` (discharges `_hCLT`).
* `IsAsymLinearVec.tendsto_normal_vec_clt` : end-to-end vector asymptotic
  normality from vector asymptotic linearity (no CLT hypothesis).
-/

import Causalean.Stat.CLT.AsymptoticLinearity
import Causalean.Stat.CLT.AsymptoticLinearityVec
import Causalean.Stat.Limit.ConvergenceVec

/-! # Multivariate Central Limit Theorem

This file proves the Cramér-Wold reduction for normalized sums of
finite-dimensional vector-valued functions of an i.i.d. sample. It provides the
abstract multivariate central limit theorem used by vector asymptotic linearity
and the delta method, with the concrete Gaussian law supplied in the Gaussian
limit module.

Important declarations include `inner_normalizedSum`, which identifies each
projection of the vector normalized sum with a scalar normalized sum,
`IIDSample.normalizedSum_vec_charFun_tendsto` for the per-direction
characteristic-function limit, `Tendsto_dist_vec.of_charFun_tendsto` for the
Cramér-Wold wrapper, `IIDSample.clt_normalizedSum_vec_of_charFun` for the
abstract Gaussian-target CLT, and `IsAsymLinearVec.tendsto_normal_vec_clt` for
end-to-end vector asymptotic normality. -/

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Filter Topology Complex
open scoped RealInnerProductSpace

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X}
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Range index family (the full-sample case). -/
private noncomputable abbrev rng : ℕ → Finset ℕ := fun m => Finset.range m

/-! ## Projection of the vector normalised sum -/

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The inner product of `t` with the vector normalised sum is the scalar
normalised sum of the projected influence function `x ↦ ⟪t, ψ x⟫`. -/
theorem inner_normalizedSum (S : IIDSample Ω X μ P) (ψ : X → E) (t : E)
    (I : ℕ → Finset ℕ) (n : ℕ) (ω : Ω) :
    ⟪t, IsAsymLinearVec.normalizedSum S ψ I n ω⟫
      = IsAsymLinear.normalizedSum S (fun x => ⟪t, ψ x⟫) I n ω := by
  simp only [IsAsymLinearVec.normalizedSum, IsAsymLinear.normalizedSum,
    real_inner_smul_right, inner_sum]

/-! ## Per-direction characteristic-function limit -/

/-- **Per-direction charFun limit (general core).**  Assuming only that the
scalar projection `⟪t,ψ⟫` in the chosen direction `t` is square-integrable
(weaker than requiring the whole vector `ψ` to be square-integrable) and
mean-zero, the characteristic function of the vector normalised sum, evaluated
at `t`, converges to `exp(−½ ∫⟪t,ψ⟫² dP)`.  The full-vector convenience form is
`normalizedSum_vec_charFun_tendsto` below. -/
theorem IIDSample.normalizedSum_vec_charFun_tendsto_of_proj_integrable
    (S : IIDSample Ω X μ P) {ψ : X → E}
    (hψ_meas : Measurable ψ) (t : E)
    (hvar_t : Integrable (fun x => (⟪t, ψ x⟫) ^ 2) P)
    (hmean : ∫ x, ⟪t, ψ x⟫ ∂P = 0) :
    Tendsto
      (fun n => charFun (μ.map (IsAsymLinearVec.normalizedSum S ψ rng n)) t)
      atTop
      (𝓝 (Complex.exp (-(((∫ x, (⟪t, ψ x⟫) ^ 2 ∂P : ℝ)) : ℂ) / 2))) := by
  haveI : IsProbabilityMeasure μ := S.indep.isProbabilityMeasure
  haveI : IsProbabilityMeasure P := by
    rw [← S.law]
    exact Measure.isProbabilityMeasure_map (S.meas 0).aemeasurable
  -- projected influence function and its regularity
  set ψt : X → ℝ := fun x => ⟪t, ψ x⟫ with hψt_def
  have hψt_meas : Measurable ψt := by
    have h : Measurable (fun x => (innerSL ℝ t) (ψ x)) :=
      (innerSL ℝ t).continuous.measurable.comp hψ_meas
    simpa [innerSL_apply_apply, hψt_def] using h
  have hψt_mean : ∫ x, ψt x ∂P = 0 := by
    simpa [hψt_def] using hmean
  have hψt_var : Integrable (fun x => (ψt x) ^ 2) P := by
    simpa [hψt_def] using hvar_t
  -- measurability of the partial sums (mirrors `IIDSample.measurable_sampleMean`)
  have hSumScalar_meas : ∀ n,
      AEMeasurable (IsAsymLinear.normalizedSum S ψt rng n) μ := by
    intro n
    unfold IsAsymLinear.normalizedSum
    exact ((Finset.measurable_sum _
      (fun i _ => hψt_meas.comp (S.meas i))).const_mul _).aemeasurable
  have hSumVec_meas : ∀ n,
      AEMeasurable (IsAsymLinearVec.normalizedSum S ψ rng n) μ := by
    intro n
    unfold IsAsymLinearVec.normalizedSum
    exact ((Finset.measurable_sum _
      (fun i _ => hψ_meas.comp (S.meas i))).const_smul _).aemeasurable
  -- scalar CLT for the projected influence function
  have h_scalar :=
    S.clt_normalized_sum hψt_meas hψt_mean hψt_var
  unfold Tendsto_dist at h_scalar
  -- convert weak convergence to pointwise charFun convergence (Lévy, E = ℝ)
  have h_char1 :
      Tendsto
        (fun n => charFun (μ.map (IsAsymLinear.normalizedSum S ψt rng n)) (1 : ℝ))
        atTop
        (𝓝 (charFun (gaussianMeasure 0 (∫ x, (ψt x) ^ 2 ∂P)) (1 : ℝ))) := by
    have h := (MeasureTheory.ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp
      h_scalar) (1 : ℝ)
    simpa [ProbabilityMeasure.coe_mk] using h
  -- the scalar charFun limit equals the announced complex exponential
  have hv_nonneg : 0 ≤ ∫ x, (ψt x) ^ 2 ∂P := integral_nonneg fun x => sq_nonneg _
  have h_gauss :
      charFun (gaussianMeasure 0 (∫ x, (ψt x) ^ 2 ∂P)) (1 : ℝ)
        = Complex.exp (-(((∫ x, (ψt x) ^ 2 ∂P : ℝ)) : ℂ) / 2) := by
    rw [gaussianMeasure, charFun_gaussianReal]
    push_cast [Real.coe_toNNReal _ hv_nonneg]
    ring_nf
  -- charFun of the vector sum at `t` equals the scalar charFun at `1`
  have h_bridge : ∀ n,
      charFun (μ.map (IsAsymLinearVec.normalizedSum S ψ rng n)) t
        = charFun (μ.map (IsAsymLinear.normalizedSum S ψt rng n)) (1 : ℝ) := by
    intro n
    rw [charFun_apply, charFun_apply_real,
      integral_map (hSumVec_meas n) (by fun_prop),
      integral_map (hSumScalar_meas n) (by fun_prop)]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    have hval : (⟪IsAsymLinearVec.normalizedSum S ψ rng n ω, t⟫ : ℝ)
        = IsAsymLinear.normalizedSum S ψt rng n ω := by
      rw [real_inner_comm]; exact inner_normalizedSum S ψ t rng n ω
    simp only [hval, Complex.ofReal_one, one_mul]
  -- assemble
  have hfun :
      (fun n => charFun (μ.map (IsAsymLinearVec.normalizedSum S ψ rng n)) t)
        = (fun n => charFun (μ.map (IsAsymLinear.normalizedSum S ψt rng n)) (1 : ℝ)) :=
    funext h_bridge
  rw [hfun]
  rw [h_gauss] at h_char1
  exact h_char1

/-- **Per-direction charFun limit (full-vector form).**  Convenience wrapper of
`normalizedSum_vec_charFun_tendsto_of_proj_integrable` for the common case where
the whole vector `ψ` is square-integrable: the projection `⟪t,ψ⟫` is then
square-integrable by Cauchy–Schwarz, so callers holding the standard full-vector
`L²` condition need not re-establish the per-direction one. -/
theorem IIDSample.normalizedSum_vec_charFun_tendsto
    (S : IIDSample Ω X μ P) {ψ : X → E}
    (hψ_meas : Measurable ψ)
    (hvar : Integrable (fun x => ‖ψ x‖ ^ 2) P) (t : E)
    (hmean : ∫ x, ⟪t, ψ x⟫ ∂P = 0) :
    Tendsto
      (fun n => charFun (μ.map (IsAsymLinearVec.normalizedSum S ψ rng n)) t)
      atTop
      (𝓝 (Complex.exp (-(((∫ x, (⟪t, ψ x⟫) ^ 2 ∂P : ℝ)) : ℂ) / 2))) := by
  have hψt_meas : Measurable (fun x => (⟪t, ψ x⟫ : ℝ)) := by
    have h : Measurable (fun x => (innerSL ℝ t) (ψ x)) :=
      (innerSL ℝ t).continuous.measurable.comp hψ_meas
    simpa [innerSL_apply_apply] using h
  have hvar_t : Integrable (fun x => (⟪t, ψ x⟫) ^ 2) P := by
    have hbd : Integrable (fun x => ‖t‖ ^ 2 * ‖ψ x‖ ^ 2) P := hvar.const_mul _
    refine hbd.mono' (hψt_meas.pow_const 2).aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hsq : (⟪t, ψ x⟫) ^ 2 ≤ (‖t‖ * ‖ψ x‖) ^ 2 := by
      nlinarith [abs_real_inner_le_norm t (ψ x), abs_nonneg (⟪t, ψ x⟫ : ℝ),
        sq_abs (⟪t, ψ x⟫ : ℝ), norm_nonneg t, norm_nonneg (ψ x)]
    calc (⟪t, ψ x⟫) ^ 2 ≤ (‖t‖ * ‖ψ x‖) ^ 2 := hsq
      _ = ‖t‖ ^ 2 * ‖ψ x‖ ^ 2 := by ring
  exact S.normalizedSum_vec_charFun_tendsto_of_proj_integrable hψ_meas t hvar_t hmean

/-! ## Cramér–Wold wrapper -/

/-- **Cramér–Wold / Lévy continuity wrapper.** For an `E`-valued sequence `Xn`, if [each `Xn n`
is a.e. measurable](hyp:hXn) and [the characteristic functions of `Xn n` converge pointwise, at
every point `t`, to the characteristic function of a probability measure `Q`](hyp:hchar), then
[the sequence `Xn` converges in distribution to `Q`](goal).

    Restatement of
`MeasureTheory.ProbabilityMeasure.tendsto_iff_tendsto_charFun` (`Clt` package)
for the project's `Tendsto_dist_vec` wrapper. -/
theorem Tendsto_dist_vec.of_charFun_tendsto
    [IsProbabilityMeasure μ] {Xn : ℕ → Ω → E} {Q : Measure E} [IsProbabilityMeasure Q]
    (hXn : ∀ n, AEMeasurable (Xn n) μ)
    (hchar : ∀ t : E,
      Tendsto (fun n => charFun (μ.map (Xn n)) t) atTop (𝓝 (charFun Q t))) :
    Tendsto_dist_vec Xn Q μ hXn := by
  unfold Tendsto_dist_vec
  refine MeasureTheory.ProbabilityMeasure.tendsto_iff_tendsto_charFun.mpr fun t => ?_
  simpa [ProbabilityMeasure.coe_mk] using hchar t

/-! ## Multivariate CLT contact for an abstract Gaussian-charFun target -/

/-- **Multivariate CLT contact.** Along the i.i.d. sample `S`, for an influence function `ψ`
that is [measurable](hyp:hψ_meas), [has population mean zero](hyp:hmean), and [is
square-integrable](hyp:hvar), and a target probability measure `Q` on `E` whose characteristic
function is [the Gaussian one $\exp(-\tfrac12\int\langle t,\psi\rangle^2\,dP)$ at every point
`t`](hyp:hQ), then [the vector normalised sum converges in distribution to `Q`](goal).

    This discharges the `_hCLT` hypothesis of
`IsAsymLinearVec.tendsto_normal_vec` and of `deltaMethod`. -/
theorem IIDSample.clt_normalizedSum_vec_of_charFun
    (S : IIDSample Ω X μ P) {ψ : X → E}
    (hψ_meas : Measurable ψ)
    (hmean : ∫ x, ψ x ∂P = 0) (hvar : Integrable (fun x => ‖ψ x‖ ^ 2) P)
    (Q : Measure E) [IsProbabilityMeasure Q]
    (hQ : ∀ t : E, charFun Q t
          = Complex.exp (-(((∫ x, (⟪t, ψ x⟫) ^ 2 ∂P : ℝ)) : ℂ) / 2)) :
    @Tendsto_dist_vec Ω E _ _ _ _ (IsAsymLinearVec.normalizedSum S ψ rng) Q μ
      S.indep.isProbabilityMeasure ‹IsProbabilityMeasure Q›
      (by
        intro n
        unfold IsAsymLinearVec.normalizedSum
        exact ((Finset.measurable_sum _
          (fun i _ => hψ_meas.comp (S.meas i))).const_smul _).aemeasurable) := by
  haveI : IsProbabilityMeasure μ := S.indep.isProbabilityMeasure
  have hSum_meas : ∀ n, AEMeasurable (IsAsymLinearVec.normalizedSum S ψ rng n) μ := by
    intro n
    unfold IsAsymLinearVec.normalizedSum
    exact ((Finset.measurable_sum _
      (fun i _ => hψ_meas.comp (S.meas i))).const_smul _).aemeasurable
  haveI : IsProbabilityMeasure P := by
    rw [← S.law]
    exact Measure.isProbabilityMeasure_map (S.meas 0).aemeasurable
  have hψ_int : Integrable ψ P :=
    ((MeasureTheory.memLp_two_iff_integrable_sq_norm
      hψ_meas.aestronglyMeasurable).2 hvar).integrable
      (by norm_num)
  refine Tendsto_dist_vec.of_charFun_tendsto (Q := Q) hSum_meas fun t => ?_
  rw [hQ t]
  apply S.normalizedSum_vec_charFun_tendsto hψ_meas hvar t
  have h := integral_inner (𝕜 := ℝ) hψ_int t
  simpa [hmean, inner_zero_right] using h

/-! ## End-to-end vector asymptotic normality -/

/-- **Vector asymptotic normality from asymptotic linearity (no CLT hypothesis).** Given [that
`θn` is vector-asymptotically-linear at `θ₀` with influence function `ψ` along the i.i.d. sample
`S`](hyp:h), where `ψ` is [measurable](hyp:hψ_meas), a target probability measure `Q` on `E`
whose [characteristic function is the Gaussian one $\exp(-\tfrac12\int\langle
t,\psi\rangle^2\,dP)$ at every point `t`](hyp:hQ), and [the rescaled estimator is a.e.
measurable at every sample size](hyp:hθn_meas), then [the pushforward laws of the rescaled
estimator converge to `Q`](goal).

    Combines `IsAsymLinearVec.tendsto_normal_vec` with the
multivariate CLT contact `clt_normalizedSum_vec_of_charFun`. -/
theorem IsAsymLinearVec.tendsto_normal_vec_clt
    {θn : ℕ → Ω → E} {θ₀ : E} {ψ : X → E}
    {S : IIDSample Ω X μ P}
    (h : IsAsymLinearVec θn θ₀ ψ S rng)
    (hψ_meas : Measurable ψ)
    (Q : Measure E) [IsProbabilityMeasure Q]
    (hQ : ∀ t : E, charFun Q t
          = Complex.exp (-(((∫ x, (⟪t, ψ x⟫) ^ 2 ∂P : ℝ)) : ℂ) / 2))
    (hθn_meas : ∀ n, AEMeasurable (IsAsymLinearVec.rescaledEstimator θn θ₀ rng n) μ) :
    Tendsto (β := ProbabilityMeasure E)
      (fun n => ⟨μ.map (IsAsymLinearVec.rescaledEstimator θn θ₀ rng n),
                  @Measure.isProbabilityMeasure_map Ω E _ _ μ
                    S.indep.isProbabilityMeasure _ (hθn_meas n)⟩)
      atTop (𝓝 ⟨Q, ‹IsProbabilityMeasure Q›⟩) :=
  by
    haveI : IsProbabilityMeasure μ := S.indep.isProbabilityMeasure
    have hSum_meas : ∀ n, AEMeasurable (IsAsymLinearVec.normalizedSum S ψ rng n) μ := by
      intro n
      unfold IsAsymLinearVec.normalizedSum
      exact ((Finset.measurable_sum _
        (fun i _ => hψ_meas.comp (S.meas i))).const_smul _).aemeasurable
    exact IsAsymLinearVec.tendsto_normal_vec ⟨Q, ‹IsProbabilityMeasure Q›⟩ h.remainder
      hθn_meas hSum_meas
      (S.clt_normalizedSum_vec_of_charFun hψ_meas h.mean_zero h.finite_var Q hQ)

end Causalean.Stat
