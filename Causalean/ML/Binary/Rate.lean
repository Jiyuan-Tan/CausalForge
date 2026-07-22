/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.ML.Ridge.Rate
import Mathlib.Analysis.SpecialFunctions.Sigmoid

/-! # L²-regularized logistic regression — estimation rate (root-n)

The L²-penalized logistic quasi-score M-estimator and its root-n L²-estimation
rate toward the penalized population target. The response coordinate is
real-valued in this file, so the result is a logistic quasi-score rate rather
than a zero-one-only binary model. This is the binary-response analogue of the
ridge rate (`ML/Ridge/Rate.lean`): the `λ‖β‖²` penalty makes the penalized objective globally
`2λ`-strongly convex, so — exactly as the ridge `λI` made the Gram positive definite —
the coefficient error is controlled by a strong-convexity basic inequality instead of a
closed-form inverse.

Crux (this file): with `β̂ₙ` solving the empirical penalized first-order condition
`∇ₙ(β̂ₙ) = 0` and `β⋆` the population FOC point, strong monotonicity of the gradient map
(the logistic part is monotone since `σ` is increasing; the penalty contributes `2λ·id`)
gives `2λ‖β̂ₙ − β⋆‖ ≤ ∑ₖ |∇ₙ(β⋆)ₖ|`, and the empirical gradient at `β⋆` is a centered
i.i.d. mean ⇒ `O_p(n^{-1/2})`.  The predictor rate then follows from the `1/4`-Lipschitz
`σ` and the shared linear-predictor L² bound `eLpNorm_predictor_sub_le`.
-/

namespace Causalean.ML

open MeasureTheory BigOperators Causalean.Stat

variable {Ω γ K : Type*} [MeasurableSpace Ω] [MeasurableSpace γ]
  [Fintype K] [DecidableEq K] {μ : Measure Ω}

/-- Empirical penalized-logistic gradient at `β` (coordinate form):
`∇ₙ(β)ₖ = n⁻¹ Σ_{i<n} (σ⟨β,φᵢ⟩ − yᵢ) φᵢₖ + 2λ βₖ`. -/
noncomputable def regLogisticGrad (φ : FeatureMap γ K) (Z : ℕ → Ω → γ × ℝ)
    (lam : ℝ) (n : ℕ) (ω : Ω) (β : K → ℝ) : K → ℝ :=
  fun k => (n : ℝ)⁻¹ * (∑ i ∈ Finset.range n,
      (Real.sigmoid (∑ j, β j * φ.φ (Z i ω).1 j) - (Z i ω).2) * φ.φ (Z i ω).1 k)
    + 2 * lam * β k

/-- The penalized population first-order condition at `β⋆`:
`E[(σ⟨β⋆,φ⟩ − Y) φₖ] + 2λ β⋆ₖ = 0` for every feature `k`. -/
def IsPopulationRegLogistic (P : Measure (γ × ℝ)) (φ : FeatureMap γ K)
    (lam : ℝ) (βstar : K → ℝ) : Prop :=
  ∀ k, (∫ z, (Real.sigmoid (∑ j, βstar j * φ.φ z.1 j) - z.2) * φ.φ z.1 k ∂P)
    + 2 * lam * βstar k = 0

/-- The logistic predictor `x ↦ σ(⟨β, φ(x)⟩)` (the fitted conditional probability). -/
noncomputable def logisticPredictor (φ : FeatureMap γ K) (β : K → ℝ) : γ → ℝ :=
  fun x => Real.sigmoid (∑ k, β k * φ.φ x k)

private lemma monotone_mul_sub_nonneg {f : ℝ → ℝ} (hf : Monotone f) (u v : ℝ) :
    0 ≤ (f u - f v) * (u - v) := by
  by_cases huv : u ≤ v
  · have hfv : f u ≤ f v := hf huv
    exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hfv) (sub_nonpos.mpr huv)
  · have hvu : v ≤ u := le_of_not_ge huv
    have hfv : f v ≤ f u := hf hvu
    exact mul_nonneg (sub_nonneg.mpr hfv) (sub_nonneg.mpr hvu)

omit [DecidableEq K] in
private lemma pi_norm_sq_le_sum_sq (v : K → ℝ) :
    ‖v‖ ^ 2 ≤ ∑ k, (v k) ^ 2 := by
  classical
  let s : ℝ := ∑ k, (v k) ^ 2
  have hs_nonneg : 0 ≤ s := by
    dsimp [s]
    exact Finset.sum_nonneg fun k _ => sq_nonneg _
  have hnorm_le : ‖v‖ ≤ Real.sqrt s := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg s)).2 (fun k => ?_)
    rw [Real.norm_eq_abs]
    have hk_sq : (v k) ^ 2 ≤ s := by
      dsimp [s]
      exact Finset.single_le_sum (f := fun j => (v j) ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ k)
    exact Real.abs_le_sqrt hk_sq
  calc
    ‖v‖ ^ 2 ≤ (Real.sqrt s) ^ 2 := by
      exact sq_le_sq' (by nlinarith [norm_nonneg v, Real.sqrt_nonneg s]) hnorm_le
    _ = s := Real.sq_sqrt hs_nonneg
    _ = ∑ k, (v k) ^ 2 := rfl

private lemma sigmoid_lipschitz_quarter : LipschitzWith (Real.toNNReal (1 / 4)) Real.sigmoid := by
  refine lipschitzWith_of_nnnorm_deriv_le differentiable_sigmoid ?_
  intro x
  rw [Real.deriv_sigmoid]
  rw [Real.nnnorm_of_nonneg
    (mul_nonneg (Real.sigmoid_pos x).le (sub_nonneg.mpr (Real.sigmoid_lt_one x).le))]
  apply NNReal.coe_le_coe.mp
  change Real.sigmoid x * (1 - Real.sigmoid x) ≤ (Real.toNNReal (1 / 4) : ℝ)
  rw [Real.coe_toNNReal]
  · have hs0 : 0 ≤ Real.sigmoid x := (Real.sigmoid_pos x).le
    have hs1 : Real.sigmoid x ≤ 1 := (Real.sigmoid_lt_one x).le
    nlinarith [sq_nonneg (Real.sigmoid x - (1 / 2 : ℝ))]
  · norm_num

omit [DecidableEq K] in
private lemma linear_predictor_sub_memLp (φ : FeatureMap γ K) (P : Measure (γ × ℝ))
    [IsProbabilityMeasure P]
    (hφ : ∀ k, Measurable (fun x => φ.φ x k))
    (h4 : Integrable (fun z => (∑ k, (φ.φ z.1 k) ^ 2) ^ 2) P)
    (β βstar : K → ℝ) :
    MemLp (fun x : γ => (∑ k, β k * φ.φ x k) - ∑ k, βstar k * φ.φ x k) 2
      (P.map Prod.fst) := by
  classical
  have hmeasP : ∀ k, Measurable (fun z : γ × ℝ => φ.φ z.1 k) := fun k =>
    (hφ k).comp measurable_fst
  have hsum_meas : Measurable (fun z : γ × ℝ => ∑ k, (φ.φ z.1 k) ^ 2) :=
    Finset.measurable_sum _ (fun k _ => (hmeasP k).pow_const 2)
  have hsumsq_int : Integrable (fun z : γ × ℝ => ∑ k, (φ.φ z.1 k) ^ 2) P := by
    refine Integrable.mono' (g := fun z => 1 + (∑ k, (φ.φ z.1 k) ^ 2) ^ 2)
      ((integrable_const (1 : ℝ)).add h4) hsum_meas.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun z => ?_)
    have hnn : (0 : ℝ) ≤ ∑ k, (φ.φ z.1 k) ^ 2 :=
      Finset.sum_nonneg (fun k _ => sq_nonneg _)
    rw [Real.norm_of_nonneg hnn]
    nlinarith [sq_nonneg ((∑ k, (φ.φ z.1 k) ^ 2) - 1)]
  have hphisq_int : ∀ k, Integrable (fun z : γ × ℝ => (φ.φ z.1 k) ^ 2) P := by
    intro k
    refine Integrable.mono hsumsq_int ((hmeasP k).pow_const 2).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun z => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _), Real.norm_of_nonneg
      (Finset.sum_nonneg (fun k _ => sq_nonneg _))]
    exact Finset.single_le_sum (f := fun k => (φ.φ z.1 k) ^ 2)
      (fun i _ => sq_nonneg _) (Finset.mem_univ k)
  have hmemLp : ∀ k, MemLp (fun z : γ × ℝ => φ.φ z.1 k) 2 P := fun k =>
    (memLp_two_iff_integrable_sq (hmeasP k).aestronglyMeasurable).mpr (hphisq_int k)
  have hcomp : MemLp
      (fun z : γ × ℝ => (∑ k, β k * φ.φ z.1 k) - ∑ k, βstar k * φ.φ z.1 k)
      2 P := by
    exact (memLp_finset_sum _ (fun k _ => (hmemLp k).const_mul (β k))).sub
      (memLp_finset_sum _ (fun k _ => (hmemLp k).const_mul (βstar k)))
  have hmeas : Measurable
      (fun x : γ => (∑ k, β k * φ.φ x k) - ∑ k, βstar k * φ.φ x k) :=
    (Finset.measurable_sum _ (fun k _ => measurable_const.mul (hφ k))).sub
      (Finset.measurable_sum _ (fun k _ => measurable_const.mul (hφ k)))
  rw [memLp_map_measure_iff hmeas.aestronglyMeasurable measurable_fst.aemeasurable]
  simpa [Function.comp_def] using hcomp

/-- **Strong-convexity basic inequality (deterministic).** If `β̂` solves the empirical
penalized FOC `∇ₙ(β̂) = 0` and `λ > 0`, the coefficient error is controlled by the
empirical gradient at the target: `2λ‖β̂ − β⋆‖ ≤ ∑ₖ |∇ₙ(β⋆)ₖ|`. -/
theorem regLogistic_basic_inequality (φ : FeatureMap γ K) (Z : ℕ → Ω → γ × ℝ)
    {lam : ℝ} (hlam : 0 < lam) (βstar : K → ℝ) (n : ℕ) (ω : Ω) {βhat : K → ℝ}
    (hFOC : regLogisticGrad φ Z lam n ω βhat = 0) :
    2 * lam * ‖βhat - βstar‖ ≤ ∑ k, |regLogisticGrad φ Z lam n ω βstar k| := by
  classical
  let δ : K → ℝ := βhat - βstar
  let lin : (K → ℝ) → ℕ → ℝ := fun β i => ∑ j, β j * φ.φ (Z i ω).1 j
  let S0 : ℝ :=
    ∑ k, (regLogisticGrad φ Z lam n ω βhat k -
      regLogisticGrad φ Z lam n ω βstar k) * δ k
  let a : ℕ → ℝ := fun i => Real.sigmoid (lin βhat i) - Real.sigmoid (lin βstar i)
  let b : ℕ → K → ℝ := fun i k => φ.φ (Z i ω).1 k
  have hgrad_diff : ∀ k,
      regLogisticGrad φ Z lam n ω βhat k - regLogisticGrad φ Z lam n ω βstar k =
        (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, a i * b i k + 2 * lam * δ k := by
    intro k
    have hsum :
        (∑ i ∈ Finset.range n, (Real.sigmoid (lin βhat i) - (Z i ω).2) * b i k) -
          (∑ i ∈ Finset.range n, (Real.sigmoid (lin βstar i) - (Z i ω).2) * b i k)
        = ∑ i ∈ Finset.range n, a i * b i k := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl ?_
      intro i _
      dsimp [a]
      ring
    dsimp [regLogisticGrad, lin, b]
    change (n : ℝ)⁻¹ *
          (∑ i ∈ Finset.range n, (Real.sigmoid (lin βhat i) - (Z i ω).2) * b i k)
        + 2 * lam * βhat k -
          ((n : ℝ)⁻¹ *
            (∑ i ∈ Finset.range n, (Real.sigmoid (lin βstar i) - (Z i ω).2) * b i k)
          + 2 * lam * βstar k)
      = (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, a i * b i k + 2 * lam * δ k
    rw [← hsum]
    dsimp [δ]
    ring_nf
  have hinner : ∀ i, ∑ k, b i k * δ k = lin βhat i - lin βstar i := by
    intro i
    dsimp [b, δ, lin]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro k _
    ring
  have hsum_emp :
      ∑ k, ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, a i * b i k) * δ k =
        (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, a i * (lin βhat i - lin βstar i) := by
    calc
      ∑ k, ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, a i * b i k) * δ k
          = (n : ℝ)⁻¹ * ∑ k, (∑ i ∈ Finset.range n, a i * b i k) * δ k := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro k _
            ring
      _ = (n : ℝ)⁻¹ * ∑ k, ∑ i ∈ Finset.range n, (a i * b i k) * δ k := by
            congr 1
            refine Finset.sum_congr rfl ?_
            intro k _
            rw [Finset.sum_mul]
      _ = (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, ∑ k, (a i * b i k) * δ k := by
            congr 1
            rw [Finset.sum_comm]
      _ = (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, a i * (lin βhat i - lin βstar i) := by
            congr 1
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [← hinner i, Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro k _
            ring
  have hS_eq : S0 =
      (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
        (Real.sigmoid (lin βhat i) - Real.sigmoid (lin βstar i)) *
          (lin βhat i - lin βstar i)
      + 2 * lam * ∑ k, (δ k) ^ 2 := by
    calc
      S0
          = ∑ k, (((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, a i * b i k
              + 2 * lam * δ k) * δ k) := by
            dsimp [S0]
            refine Finset.sum_congr rfl ?_
            intro k _
            rw [hgrad_diff]
      _ = ∑ k, ((n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, a i * b i k) * δ k
            + ∑ k, (2 * lam * δ k) * δ k := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl ?_
            intro k _
            ring
      _ = (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, a i * (lin βhat i - lin βstar i)
            + 2 * lam * ∑ k, (δ k) ^ 2 := by
            rw [hsum_emp]
            congr 1
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro k _
            ring
      _ = (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
              (Real.sigmoid (lin βhat i) - Real.sigmoid (lin βstar i)) *
                (lin βhat i - lin βstar i)
            + 2 * lam * ∑ k, (δ k) ^ 2 := rfl
  have hlog_nonneg :
      0 ≤ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n,
        (Real.sigmoid (lin βhat i) - Real.sigmoid (lin βstar i)) *
          (lin βhat i - lin βstar i) := by
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))
      (Finset.sum_nonneg fun i _ =>
        monotone_mul_sub_nonneg Real.sigmoid_monotone (lin βhat i) (lin βstar i))
  have hS_lower : 2 * lam * ∑ k, (δ k) ^ 2 ≤ S0 := by
    nlinarith [hS_eq, hlog_nonneg]
  have hS_grad : S0 = - ∑ k, regLogisticGrad φ Z lam n ω βstar k * δ k := by
    dsimp [S0, δ]
    simp [congrFun hFOC]
  have hneg_le_abs :
      - ∑ k, regLogisticGrad φ Z lam n ω βstar k * δ k
        ≤ ∑ k, |regLogisticGrad φ Z lam n ω βstar k| * |δ k| := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum ?_
    intro k _
    calc
      -(regLogisticGrad φ Z lam n ω βstar k * δ k)
          ≤ |regLogisticGrad φ Z lam n ω βstar k * δ k| := neg_le_abs _
      _ = |regLogisticGrad φ Z lam n ω βstar k| * |δ k| := by rw [abs_mul]
  have hdot_bound :
      ∑ k, |regLogisticGrad φ Z lam n ω βstar k| * |δ k|
        ≤ (∑ k, |regLogisticGrad φ Z lam n ω βstar k|) * ‖δ‖ := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum ?_
    intro k _
    have hcoord := norm_le_pi_norm δ k
    have habs : |δ k| ≤ ‖δ‖ := by
      simpa [Real.norm_eq_abs] using hcoord
    exact mul_le_mul_of_nonneg_left habs (abs_nonneg _)
  have hS_upper :
      S0 ≤ (∑ k, |regLogisticGrad φ Z lam n ω βstar k|) * ‖δ‖ := by
    calc
      S0 = - ∑ k, regLogisticGrad φ Z lam n ω βstar k * δ k := hS_grad
      _ ≤ ∑ k, |regLogisticGrad φ Z lam n ω βstar k| * |δ k| := hneg_le_abs
      _ ≤ (∑ k, |regLogisticGrad φ Z lam n ω βstar k|) * ‖δ‖ := hdot_bound
  have hquad :
      2 * lam * ‖δ‖ ^ 2
        ≤ (∑ k, |regLogisticGrad φ Z lam n ω βstar k|) * ‖δ‖ := by
    have hnormsq := pi_norm_sq_le_sum_sq δ
    have hleft : 2 * lam * ‖δ‖ ^ 2 ≤ 2 * lam * ∑ k, (δ k) ^ 2 := by
      exact mul_le_mul_of_nonneg_left hnormsq (by nlinarith)
    exact hleft.trans (hS_lower.trans hS_upper)
  by_cases hzero : ‖δ‖ = 0
  · rw [show ‖βhat - βstar‖ = ‖δ‖ by rfl, hzero, mul_zero]
    exact Finset.sum_nonneg fun k _ => abs_nonneg _
  · have hnorm_pos : 0 < ‖δ‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
    have hfinal : 2 * lam * ‖δ‖ ≤ ∑ k, |regLogisticGrad φ Z lam n ω βstar k| := by
      calc
        2 * lam * ‖δ‖ = (2 * lam * ‖δ‖ ^ 2) / ‖δ‖ := by
          field_simp [hnorm_pos.ne']
        _ ≤ ((∑ k, |regLogisticGrad φ Z lam n ω βstar k|) * ‖δ‖) / ‖δ‖ := by
          exact div_le_div_of_nonneg_right hquad hnorm_pos.le
        _ = ∑ k, |regLogisticGrad φ Z lam n ω βstar k| := by
          field_simp [hnorm_pos.ne']
    simpa [δ] using hfinal

/-- Each coordinate of the empirical penalized gradient at the population target
is `O_p(n^{-1/2})`; the population score equations make the i.i.d. summands
centered. -/
theorem regLogisticGrad_coord_isBigOp (φ : FeatureMap γ K) (P : Measure (γ × ℝ))
    [IsProbabilityMeasure P] (S : IIDSample Ω (γ × ℝ) μ P) [IsProbabilityMeasure μ]
    {lam : ℝ} (βstar : K → ℝ) (hpop : IsPopulationRegLogistic P φ lam βstar)
    (hφ : ∀ k, Measurable (fun x => φ.φ x k))
    (hscore : ∀ k, MemLp
      (fun z => (Real.sigmoid (∑ j, βstar j * φ.φ z.1 j) - z.2) * φ.φ z.1 k) 2 P)
    (k : K) :
    Causalean.Stat.IsBigOp
      (fun n ω => regLogisticGrad φ S.Z lam n ω βstar k)
      (fun n => (Real.sqrt (n : ℝ))⁻¹) μ := by
  classical
  let g : γ × ℝ → ℝ :=
    fun z => (Real.sigmoid (∑ j, βstar j * φ.φ z.1 j) - z.2) * φ.φ z.1 k
  have hφ_prod : ∀ k, Measurable (fun z : γ × ℝ => φ.φ z.1 k) := fun k =>
    (hφ k).comp measurable_fst
  have hg_meas : Measurable g := by
    dsimp [g]
    have hlin : Measurable (fun z : γ × ℝ => ∑ j, βstar j * φ.φ z.1 j) :=
      Finset.measurable_sum _ fun j _ => measurable_const.mul (hφ_prod j)
    exact ((continuous_sigmoid.measurable.comp hlin).sub measurable_snd).mul
      (hφ_prod k)
  have hcoord :
      (fun n ω => regLogisticGrad φ S.Z lam n ω βstar k) =
        (fun n ω => S.sampleMean g n ω - ∫ z, g z ∂P) := by
    funext n ω
    have hpopk : (∫ z, g z ∂P) + 2 * lam * βstar k = 0 := by
      simpa [g] using hpop k
    dsimp [regLogisticGrad, IIDSample.sampleMean, g]
    linarith
  have hk0 := S.sampleMean_sub_isBigOp hg_meas (by simpa [g] using hscore k)
  let A : ℝ := ∫ z, (g z) ^ 2 ∂P
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact integral_nonneg fun z => sq_nonneg _
  have hrate_le : ∀ n : ℕ,
      Real.sqrt (A / (n : ℝ)) ≤
        (Real.sqrt A + 1) * (Real.sqrt (n : ℝ))⁻¹ := by
    intro n
    calc
      Real.sqrt (A / (n : ℝ))
          = Real.sqrt A * (Real.sqrt (n : ℝ))⁻¹ := by
            rw [Real.sqrt_div hA_nonneg, div_eq_mul_inv]
      _ ≤ (Real.sqrt A + 1) * (Real.sqrt (n : ℝ))⁻¹ := by
            exact mul_le_mul_of_nonneg_right
              (by linarith [Real.sqrt_nonneg A])
              (inv_nonneg.mpr (Real.sqrt_nonneg (n : ℝ)))
  have hk1 : Causalean.Stat.IsBigOp
      (fun n ω => S.sampleMean g n ω - ∫ z, g z ∂P)
      (fun n => (Real.sqrt A + 1) * (Real.sqrt (n : ℝ))⁻¹) μ := by
    exact Causalean.Stat.IsBigOp.mono_rate
      (fun n => Real.sqrt_nonneg (A / (n : ℝ))) hrate_le hk0
  have hk2 : Causalean.Stat.IsBigOp
      (fun n ω => S.sampleMean g n ω - ∫ z, g z ∂P)
      (fun n => (Real.sqrt (n : ℝ))⁻¹) μ := by
    exact Causalean.Stat.IsBigOp.scale_rate
      (rn := fun n => (Real.sqrt (n : ℝ))⁻¹)
      (by linarith [Real.sqrt_nonneg A]) hk1
  rw [hcoord]
  exact hk2

/-- The regularized-logistic coefficient error is `O_p(n^{-1/2})`: the
strong-convexity basic inequality converts the centered-gradient bound into a
coefficient-error bound. -/
theorem regLogisticCoef_isBigOp (φ : FeatureMap γ K) (P : Measure (γ × ℝ))
    [IsProbabilityMeasure P] (S : IIDSample Ω (γ × ℝ) μ P) [IsProbabilityMeasure μ]
    {lam : ℝ} (hlam : 0 < lam) (βstar : K → ℝ) (βhat : ℕ → Ω → K → ℝ)
    (hpop : IsPopulationRegLogistic P φ lam βstar)
    (hFOC : ∀ n ω, regLogisticGrad φ S.Z lam n ω (βhat n ω) = 0)
    (hφ : ∀ k, Measurable (fun x => φ.φ x k))
    (hscore : ∀ k, MemLp
      (fun z => (Real.sigmoid (∑ j, βstar j * φ.φ z.1 j) - z.2) * φ.φ z.1 k) 2 P) :
    Causalean.Stat.IsBigOp
      (fun n ω => ‖βhat n ω - βstar‖) (fun n => (Real.sqrt (n : ℝ))⁻¹) μ := by
  classical
  let rn : ℕ → ℝ := fun n => (Real.sqrt (n : ℝ))⁻¹
  have hgrad_abs : ∀ k,
      Causalean.Stat.IsBigOp
        (fun n ω => |regLogisticGrad φ S.Z lam n ω βstar k|) rn μ := by
    intro k
    simpa [Causalean.Stat.IsBigOp, abs_abs, rn] using
      (regLogisticGrad_coord_isBigOp φ P S βstar hpop hφ hscore k)
  have hsum_abs : Causalean.Stat.IsBigOp
      (fun n ω => ∑ k, |regLogisticGrad φ S.Z lam n ω βstar k|) rn μ := by
    simpa using
      (IsBigOp.finset_sum (μ := μ) (s := (Finset.univ : Finset K))
        (X := fun k n ω => |regLogisticGrad φ S.Z lam n ω βstar k|)
        (fun k _ => hgrad_abs k))
  have hscaled : Causalean.Stat.IsBigOp
      (fun n ω => (1 / (2 * lam)) *
        ∑ k, |regLogisticGrad φ S.Z lam n ω βstar k|) rn μ := by
    exact IsBigOp.const_mul (μ := μ) (c := 1 / (2 * lam)) hsum_abs
  refine IsBigOp.of_abs_le
    (Xn := fun n ω => ‖βhat n ω - βstar‖)
    (Yn := fun n ω => (1 / (2 * lam)) *
      ∑ k, |regLogisticGrad φ S.Z lam n ω βstar k|) ?_ hscaled
  intro n ω
  have hden_pos : 0 < 2 * lam := by nlinarith
  have hbound0 := regLogistic_basic_inequality φ S.Z hlam βstar n ω (hFOC n ω)
  have hsum_nonneg :
      0 ≤ ∑ k, |regLogisticGrad φ S.Z lam n ω βstar k| :=
    Finset.sum_nonneg fun k _ => abs_nonneg _
  have hscale_nonneg :
      0 ≤ (1 / (2 * lam)) * ∑ k, |regLogisticGrad φ S.Z lam n ω βstar k| := by
    exact mul_nonneg (le_of_lt (one_div_pos.mpr hden_pos)) hsum_nonneg
  rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hscale_nonneg]
  calc
    ‖βhat n ω - βstar‖
        = (2 * lam)⁻¹ * ((2 * lam) * ‖βhat n ω - βstar‖) := by
          field_simp [hden_pos.ne']
    _ ≤ (2 * lam)⁻¹ * ∑ k, |regLogisticGrad φ S.Z lam n ω βstar k| := by
          exact mul_le_mul_of_nonneg_left hbound0 (inv_nonneg.mpr hden_pos.le)
    _ = (1 / (2 * lam)) * ∑ k, |regLogisticGrad φ S.Z lam n ω βstar k| := by
          ring

/-- **Regularized-logistic root-n estimation rate.** Under the penalized population FOC,
`λ > 0`, the L⁴ feature moment, and a square-integrable score, the fitted logistic
probability `σ(⟨β̂ₙ, φ⟩)` attains the root-n L²-rate toward the population target
`σ(⟨β⋆, φ⟩)`.  Assembled from the coefficient rate, the `1/4`-Lipschitz `σ`, and the
shared linear-predictor L² bound. -/
theorem regLogistic_achievesL2Rate (φ : FeatureMap γ K) (P : Measure (γ × ℝ))
    [IsProbabilityMeasure P] (S : IIDSample Ω (γ × ℝ) μ P) [IsProbabilityMeasure μ]
    {lam : ℝ} (hlam : 0 < lam) (βstar : K → ℝ) (βhat : ℕ → Ω → K → ℝ)
    (hpop : IsPopulationRegLogistic P φ lam βstar)
    (hFOC : ∀ n ω, regLogisticGrad φ S.Z lam n ω (βhat n ω) = 0)
    (hφ : ∀ k, Measurable (fun x => φ.φ x k))
    (h4 : Integrable (fun z => (∑ k, (φ.φ z.1 k) ^ 2) ^ 2) P)
    (hscore : ∀ k, MemLp
      (fun z => (Real.sigmoid (∑ j, βstar j * φ.φ z.1 j) - z.2) * φ.φ z.1 k) 2 P) :
    AchievesL2Rate (fun n ω => logisticPredictor φ (βhat n ω))
      (logisticPredictor φ βstar) P (fun n => (Real.sqrt (n : ℝ))⁻¹) μ := by
  classical
  rcases eLpNorm_predictor_sub_le φ P hφ h4 βstar with ⟨C, hC_nonneg, hC_bound⟩
  have hcoef := regLogisticCoef_isBigOp φ P S hlam βstar βhat hpop hFOC hφ hscore
  let D : ℝ := (1 / 4 : ℝ) * C
  have hD_nonneg : 0 ≤ D := by
    dsimp [D]
    exact mul_nonneg (by norm_num) hC_nonneg
  have hpred_bound : ∀ n ω,
      (eLpNorm
        (fun x => logisticPredictor φ (βhat n ω) x - logisticPredictor φ βstar x) 2
        (P.map Prod.fst)).toReal
        ≤ D * ‖βhat n ω - βstar‖ := by
    intro n ω
    let β : K → ℝ := βhat n ω
    let linDiff : γ → ℝ :=
      fun x => (∑ k, β k * φ.φ x k) - ∑ k, βstar k * φ.φ x k
    have hlin_mem := linear_predictor_sub_memLp φ P hφ h4 β βstar
    have hlin_ne_top : eLpNorm linDiff 2 (P.map Prod.fst) ≠ ⊤ := by
      simpa [linDiff] using hlin_mem.eLpNorm_ne_top
    have hscale_ne_top : eLpNorm ((1 / 4 : ℝ) • linDiff) 2 (P.map Prod.fst) ≠ ⊤ := by
      rw [eLpNorm_const_smul]
      exact ENNReal.mul_ne_top (by simp) hlin_ne_top
    have hmono :
        eLpNorm (fun x => logisticPredictor φ β x - logisticPredictor φ βstar x) 2
            (P.map Prod.fst)
          ≤ eLpNorm ((1 / 4 : ℝ) • linDiff) 2 (P.map Prod.fst) := by
      refine eLpNorm_mono (μ := P.map Prod.fst) (p := 2) (fun x => ?_)
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      dsimp [logisticPredictor, linDiff]
      have h := sigmoid_lipschitz_quarter.dist_le_mul
        (∑ k, β k * φ.φ x k) (∑ k, βstar k * φ.φ x k)
      simpa [Real.dist_eq, abs_sub_comm, div_eq_mul_inv] using h
    have hsig_le :
        (eLpNorm (fun x => logisticPredictor φ β x - logisticPredictor φ βstar x) 2
          (P.map Prod.fst)).toReal
          ≤ (1 / 4 : ℝ) *
            (eLpNorm linDiff 2 (P.map Prod.fst)).toReal := by
      calc
        (eLpNorm (fun x => logisticPredictor φ β x - logisticPredictor φ βstar x) 2
            (P.map Prod.fst)).toReal
            ≤ (eLpNorm ((1 / 4 : ℝ) • linDiff) 2 (P.map Prod.fst)).toReal :=
              ENNReal.toReal_mono hscale_ne_top hmono
        _ = (1 / 4 : ℝ) * (eLpNorm linDiff 2 (P.map Prod.fst)).toReal := by
              rw [eLpNorm_const_smul]
              rw [ENNReal.toReal_mul]
              · norm_num [Real.norm_eq_abs]
    have hlin_bound :
        (eLpNorm linDiff 2 (P.map Prod.fst)).toReal ≤ C * ‖β - βstar‖ := by
      simpa [linDiff, β] using hC_bound β
    dsimp [D]
    nlinarith
  have hpred_finite : ∀ n ω,
      eLpNorm
        (fun x => logisticPredictor φ (βhat n ω) x - logisticPredictor φ βstar x) 2
        (P.map Prod.fst) ≠ ⊤ := by
    intro n ω
    let β : K → ℝ := βhat n ω
    let linDiff : γ → ℝ :=
      fun x => (∑ k, β k * φ.φ x k) - ∑ k, βstar k * φ.φ x k
    have hlin_mem := linear_predictor_sub_memLp φ P hφ h4 β βstar
    have hlin_ne_top : eLpNorm linDiff 2 (P.map Prod.fst) ≠ ⊤ := by
      simpa [linDiff] using hlin_mem.eLpNorm_ne_top
    have hscale_ne_top : eLpNorm ((1 / 4 : ℝ) • linDiff) 2 (P.map Prod.fst) ≠ ⊤ := by
      rw [eLpNorm_const_smul]
      exact ENNReal.mul_ne_top (by simp) hlin_ne_top
    have hmono :
        eLpNorm (fun x => logisticPredictor φ β x - logisticPredictor φ βstar x) 2
            (P.map Prod.fst)
          ≤ eLpNorm ((1 / 4 : ℝ) • linDiff) 2 (P.map Prod.fst) := by
      refine eLpNorm_mono (μ := P.map Prod.fst) (p := 2) (fun x => ?_)
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      dsimp [logisticPredictor, linDiff]
      have h := sigmoid_lipschitz_quarter.dist_le_mul
        (∑ k, β k * φ.φ x k) (∑ k, βstar k * φ.φ x k)
      simpa [Real.dist_eq, abs_sub_comm, div_eq_mul_inv] using h
    exact ne_of_lt (lt_of_le_of_lt hmono (lt_top_iff_ne_top.mpr hscale_ne_top))
  unfold AchievesL2Rate
  constructor
  · exact hpred_finite
  intro ε hε
  rcases hcoef ε hε with ⟨M0, hM0⟩
  let M : ℝ := max M0 0
  have hM0_le_M : M0 ≤ M := le_max_left M0 0
  have hM_nonneg : 0 ≤ M := le_max_right M0 0
  refine ⟨D * M, ?_⟩
  have hlim_M :
      Filter.limsup
          (fun n : ℕ =>
            μ {ω | M * (Real.sqrt (n : ℝ))⁻¹ <
              |‖βhat n ω - βstar‖|}) Filter.atTop
        ≤ ENNReal.ofReal ε := by
    refine le_trans (Filter.limsup_le_limsup (Filter.Eventually.of_forall ?_)) hM0
    intro n
    apply measure_mono
    intro ω hω
    have hr_nonneg : 0 ≤ (Real.sqrt (n : ℝ))⁻¹ :=
      inv_nonneg.mpr (Real.sqrt_nonneg _)
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hM0_le_M hr_nonneg) hω
  refine le_trans (Filter.limsup_le_limsup (Filter.Eventually.of_forall ?_)) hlim_M
  intro n
  apply measure_mono
  intro ω hω
  by_cases hD_zero : D = 0
  · have hpred_le_zero :
        (eLpNorm
          (fun x =>
            logisticPredictor φ (βhat n ω) x - logisticPredictor φ βstar x) 2
          (P.map Prod.fst)).toReal ≤ 0 := by
      simpa [hD_zero] using hpred_bound n ω
    have hpred_nonneg :
        0 ≤ (eLpNorm
          (fun x =>
            logisticPredictor φ (βhat n ω) x - logisticPredictor φ βstar x) 2
          (P.map Prod.fst)).toReal :=
      ENNReal.toReal_nonneg
    have hpred_abs :
        |(eLpNorm
          (fun x =>
            logisticPredictor φ (βhat n ω) x - logisticPredictor φ βstar x) 2
          (P.map Prod.fst)).toReal| = 0 := by
      rw [abs_of_nonneg hpred_nonneg]
      exact le_antisymm hpred_le_zero hpred_nonneg
    rw [hD_zero, zero_mul, zero_mul] at hω
    have hpred_abs' :
        |(fun n ω =>
            (eLpNorm
              (fun x =>
                logisticPredictor φ (βhat n ω) x - logisticPredictor φ βstar x) 2
              (P.map Prod.fst)).toReal) n ω| = 0 := by
      simpa using hpred_abs
    exfalso
    have hωlt :
        0 <
          |(fun n ω =>
              (eLpNorm
                (fun x =>
                  logisticPredictor φ (βhat n ω) x - logisticPredictor φ βstar x) 2
                (P.map Prod.fst)).toReal) n ω| := by
      simpa using hω
    rw [hpred_abs'] at hωlt
    exact (lt_irrefl (0 : ℝ)) hωlt
  · have hD_pos : 0 < D := lt_of_le_of_ne hD_nonneg (Ne.symm hD_zero)
    have hpred_bound' :
        (eLpNorm
          (fun x =>
            logisticPredictor φ (βhat n ω) x - logisticPredictor φ βstar x) 2
          (P.map Prod.fst)).toReal
          ≤ D * ‖βhat n ω - βstar‖ := hpred_bound n ω
    have hpred_nonneg :
        0 ≤ (eLpNorm
          (fun x =>
            logisticPredictor φ (βhat n ω) x - logisticPredictor φ βstar x) 2
          (P.map Prod.fst)).toReal :=
      ENNReal.toReal_nonneg
    have hnorm_nonneg : 0 ≤ ‖βhat n ω - βstar‖ := norm_nonneg _
    have hlt :
        D * (M * (Real.sqrt (n : ℝ))⁻¹) <
          D * ‖βhat n ω - βstar‖ := by
      calc
        D * (M * (Real.sqrt (n : ℝ))⁻¹)
            = (D * M) * (Real.sqrt (n : ℝ))⁻¹ := by ring
        _ < |(eLpNorm
              (fun x =>
                logisticPredictor φ (βhat n ω) x - logisticPredictor φ βstar x) 2
              (P.map Prod.fst)).toReal| := hω
        _ = (eLpNorm
              (fun x =>
                logisticPredictor φ (βhat n ω) x - logisticPredictor φ βstar x) 2
              (P.map Prod.fst)).toReal := by
              rw [abs_of_nonneg hpred_nonneg]
        _ ≤ D * ‖βhat n ω - βstar‖ := hpred_bound'
    have hlt' : M * (Real.sqrt (n : ℝ))⁻¹ < ‖βhat n ω - βstar‖ := by
      nlinarith [hD_pos, hlt]
    simpa [abs_of_nonneg hnorm_nonneg] using hlt'

end Causalean.ML
