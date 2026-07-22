/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Linear-smoother specialisation for the DR-Learner CATE estimator

This file proves the Hölder-type product bound for the smoothed DR-bias
term from `doc/basic_concepts/po/estimation/dr_learner_cate.tex`, and the
resulting oracle-efficiency corollary plugging that bound into
`dr_oracle_efficient`.

Two declarations are provided:

* `cate_linear_smoother_bias_bound` — linear-smoother bias bound. The smoothed
  bias of `condBias η_hat η₀` is bounded arm-by-arm by
  `aipw_rem_const ε * c_n * ‖Δπ‖_{w,p} * Σ_a ‖Δμ_a‖_{w,q}` once the linear
  smoother is witnessed by `IsLinearSmoother op n ω x B w xs` and the
  absolute-weight envelope `Σ |w_i| ≤ c_n` is in place.
* `cate_dr_oracle_efficient_linear` — corollary of `dr_oracle_efficient`
  specialised to a `LinearSmootherOp`.
-/

import Causalean.Estimation.CATE.Kennedy.OracleExpansion
import Causalean.Estimation.OrthogonalMoments.LinearSmoother
import Causalean.Estimation.ATE.Remainder.Bound

/-! # Linear-Smoother DR-Learner Bounds

This file specializes the doubly robust CATE oracle expansion to linear
smoothers. It bounds the smoothed nuisance bias by weighted outcome-regression
and propensity-score errors in `cate_linear_smoother_bias_bound` and uses the
linear-smoother projection to obtain the oracle-efficiency corollary
`cate_dr_oracle_efficient_linear`. -/

namespace Causalean
namespace Estimation
namespace CATE

open MeasureTheory ProbabilityTheory Filter Topology
  Causalean.PO Causalean.Stat Causalean.Estimation.ATE Causalean.Estimation.OrthogonalMoments

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
  [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]

/-- **Linear-smoother bias bound for the DR-Learner CATE estimator.**

For a CATE estimation system `S` with strict overlap `ε`, a
`LinearSmootherOp` `op` witnessed by `IsLinearSmoother` at `(n, ω, x)` with
weights `w` over data tuples `xs : ι → γ × Bool × ℝ` enumerating `B`, and
an estimated nuisance vector `η_hat n ω` whose realisation lives in the
overlap-bounded set `H_ε ε`, the smoothed DR-bias term obeys the
Hölder-type product bound

    |op.evalAt n ω (condBias η_hat η₀ ∘ z.1) x|
      ≤ aipw_rem_const ε * c_n
          * WeightedNorm B w (Δπ ∘ xs.1) p
          * Σ_a WeightedNorm B w (Δμ_a ∘ xs.1) q,

with `Δπ := η_hat.e_fn − S.e_val`, `Δμ_a := η_hat.μ_fn a − S.μ_val a`, and
conjugate exponents `Real.HolderConjugate p q`.

Proof outline: expand `condBias` as a sum over `a : Bool` of
`((η_hat.e_fn − S.e_val) (η_hat.μ_fn a − S.μ_val a))/(if a then η_hat.e_fn else 1 − η_hat.e_fn)`.
Use `IsLinearSmoother` to expand `evalAt` as `Σ_i w_i * condBias … (xs i).1`.
For each arm `a`, bound the denominator pointwise by `1/ε` (overlap), then
factor `Σ |w_j|` and apply Hölder via `Real.inner_le_Lp_mul_Lq_of_nonneg`
with the normalised weights `α_i = |w_i|/Σ|w_j|`. Sum over arms; absorb the
`Σ |w_j| ≤ c_n` and `1/ε ≤ aipw_rem_const ε` factors. -/
theorem cate_linear_smoother_bias_bound
    (S : CATEEstimationSystem P γ)
    {ε : ℝ} (h_overlap : S.toBackdoorEstimationSystem.StrictOverlap ε)
    (op : LinearSmootherOp P.Ω P.μ γ)
    (η_hat : ℕ → P.Ω → NuisanceVec γ)
    (n : ℕ) (ω : P.Ω) (x : γ)
    {ι : Type*} (B : Finset ι) (w : ι → ℝ) (xs : ι → γ × Bool × ℝ)
    (c_n p q : ℝ)
    (h_overlap_η_hat : η_hat n ω ∈
                         BackdoorEstimationSystem.H_ε (γ := γ) ε)
    (hLin : LinearSmootherOp.IsLinearSmoother op n ω x B w xs)
    (hWeights : ∑ i ∈ B, |w i| ≤ c_n)
    (hConj : Real.HolderConjugate p q) :
    |op.evalAt n ω
        (fun z => condBias (η_hat n ω)
                    S.toBackdoorEstimationSystem.η₀ z.1) x|
      ≤ BackdoorEstimationSystem.aipw_rem_const ε * c_n
        * WeightedNorm B w
            (fun i => (η_hat n ω).e_fn (xs i).1 - S.e_val (xs i).1) p
        * (∑ a : Bool, WeightedNorm B w
            (fun i => (η_hat n ω).μ_fn a (xs i).1 - S.μ_val a (xs i).1) q) := by
  classical
  let η : NuisanceVec γ := η_hat n ω
  let C : ℝ := BackdoorEstimationSystem.aipw_rem_const ε
  let de : γ → ℝ := fun y => η.e_fn y - S.e_val y
  let dμ : Bool → γ → ℝ := fun a y => η.μ_fn a y - S.μ_val a y
  have hC_ge_inv : ε⁻¹ ≤ C := by
    unfold C BackdoorEstimationSystem.aipw_rem_const
    have hpos : 0 < ε := h_overlap.1
    have hone : 0 < 1 - ε := by linarith [h_overlap.2.1]
    have hden : 0 < ε * (1 - ε) := mul_pos hpos hone
    rw [div_eq_mul_inv]
    field_simp [hpos.ne', hden.ne']
    nlinarith [h_overlap.2.1]
  have hC_nonneg : 0 ≤ C :=
    (inv_nonneg.mpr h_overlap.1.le).trans hC_ge_inv
  have hη_lower : ∀ y, ε ≤ η.e_fn y := fun y => (h_overlap_η_hat y).1
  have hη_upper : ∀ y, η.e_fn y ≤ 1 - ε := fun y => (h_overlap_η_hat y).2
  have hη_pos : ∀ y, 0 < η.e_fn y := fun y => lt_of_lt_of_le h_overlap.1 (hη_lower y)
  have hη_false_pos : ∀ y, 0 < 1 - η.e_fn y := by
    intro y
    have : ε ≤ 1 - η.e_fn y := by linarith [hη_upper y]
    exact lt_of_lt_of_le h_overlap.1 this
  have hpoint : ∀ y, |condBias η S.toBackdoorEstimationSystem.η₀ y|
      ≤ C * ∑ a : Bool, |de y| * |dμ a y| := by
    intro y
    have hdenT : η.e_fn y ≠ 0 := (hη_pos y).ne'
    have hdenF : 1 - η.e_fn y ≠ 0 := (hη_false_pos y).ne'
    have hinvT : |(η.e_fn y)⁻¹| ≤ C := by
      have hle : (η.e_fn y)⁻¹ ≤ ε⁻¹ :=
        (inv_le_inv₀ (hη_pos y) h_overlap.1).2 (hη_lower y)
      rw [abs_of_pos (inv_pos.mpr (hη_pos y))]
      exact hle.trans hC_ge_inv
    have hinvF : |(1 - η.e_fn y)⁻¹| ≤ C := by
      have hden : ε ≤ 1 - η.e_fn y := by linarith [hη_upper y]
      have hle : (1 - η.e_fn y)⁻¹ ≤ ε⁻¹ :=
        (inv_le_inv₀ (hη_false_pos y) h_overlap.1).2 hden
      rw [abs_of_pos (inv_pos.mpr (hη_false_pos y))]
      exact hle.trans hC_ge_inv
    have hT :
        |(de y * dμ true y) / η.e_fn y| ≤ C * (|de y| * |dμ true y|) := by
      calc
        |(de y * dμ true y) / η.e_fn y|
            = |de y| * |dμ true y| * |(η.e_fn y)⁻¹| := by
              rw [div_eq_mul_inv]
              simp [abs_mul, mul_assoc, mul_comm]
        _ ≤ |de y| * |dμ true y| * C :=
              mul_le_mul_of_nonneg_left hinvT (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        _ = C * (|de y| * |dμ true y|) := by ring
    have hF :
        |(de y * dμ false y) / (1 - η.e_fn y)| ≤ C * (|de y| * |dμ false y|) := by
      calc
        |(de y * dμ false y) / (1 - η.e_fn y)|
            = |de y| * |dμ false y| * |(1 - η.e_fn y)⁻¹| := by
              rw [div_eq_mul_inv]
              simp [abs_mul, mul_assoc, mul_comm]
        _ ≤ |de y| * |dμ false y| * C :=
              mul_le_mul_of_nonneg_left hinvF (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        _ = C * (|de y| * |dμ false y|) := by ring
    calc
      |condBias η S.toBackdoorEstimationSystem.η₀ y|
          = |(de y * dμ true y) / η.e_fn y +
              (de y * dμ false y) / (1 - η.e_fn y)| := by
              simp [condBias, BackdoorEstimationSystem.η₀, de, dμ]
      _ ≤ |(de y * dμ true y) / η.e_fn y| +
            |(de y * dμ false y) / (1 - η.e_fn y)| := abs_add_le _ _
      _ ≤ C * (|de y| * |dμ true y|) +
            C * (|de y| * |dμ false y|) := add_le_add hT hF
      _ = C * ∑ a : Bool, |de y| * |dμ a y| := by
            simp
            ring
  let absOp : LinearSmootherOp P.Ω P.μ γ :=
    { evalAt := fun _ _ f _ => ∑ i ∈ B, |w i| * f (xs i)
      meas_evalAt_const := by
        intro _ c
        simpa using (measurable_const :
          Measurable (fun _ : P.Ω × γ => ∑ i ∈ B, |w i| * c))
      weights := fun _ _ _ _ => 0 }
  have hAbsLin : LinearSmootherOp.IsLinearSmoother absOp n ω x B (fun i => |w i|) xs := by
    intro f
    rfl
  have hAbsWeights : ∑ i ∈ B, |(|w i|)| ≤ c_n := by
    simpa [abs_of_nonneg] using hWeights
  have hProd : ∀ a : Bool,
      ∑ i ∈ B, |w i| * (|de (xs i).1| * |dμ a (xs i).1|)
        ≤ c_n
          * WeightedNorm B w (fun i => de (xs i).1) p
          * WeightedNorm B w (fun i => dμ a (xs i).1) q := by
    intro a
    have h :=
      smoother_bias_product_holder absOp n ω x
        (fun y => |de y|) (fun y => |dμ a y|)
        B (fun i => |w i|) xs c_n p q hAbsLin hAbsWeights hConj
    have hsum_nonneg :
        0 ≤ ∑ i ∈ B, |w i| * (|de (xs i).1| * |dμ a (xs i).1|) := by
      refine Finset.sum_nonneg ?_
      intro i hi
      positivity
    simpa [absOp, WeightedNorm, abs_of_nonneg, hsum_nonneg, de, dμ, mul_assoc]
      using h
  have hEval :
      op.evalAt n ω
        (fun z => condBias (η_hat n ω)
                    S.toBackdoorEstimationSystem.η₀ z.1) x
        = ∑ i ∈ B, w i * condBias η S.toBackdoorEstimationSystem.η₀ (xs i).1 := by
    simpa [η] using
      hLin (fun z => condBias (η_hat n ω) S.toBackdoorEstimationSystem.η₀ z.1)
  have hMain :
      |∑ i ∈ B, w i * condBias η S.toBackdoorEstimationSystem.η₀ (xs i).1|
        ≤ C * c_n
          * WeightedNorm B w (fun i => de (xs i).1) p
          * (∑ a : Bool, WeightedNorm B w (fun i => dμ a (xs i).1) q) := by
    calc
      |∑ i ∈ B, w i * condBias η S.toBackdoorEstimationSystem.η₀ (xs i).1|
          ≤ ∑ i ∈ B, |w i * condBias η S.toBackdoorEstimationSystem.η₀ (xs i).1| :=
            Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i ∈ B, |w i| * |condBias η S.toBackdoorEstimationSystem.η₀ (xs i).1| := by
            simp [abs_mul]
      _ ≤ ∑ i ∈ B, |w i| *
            (C * ∑ a : Bool, |de (xs i).1| * |dμ a (xs i).1|) := by
            refine Finset.sum_le_sum ?_
            intro i hi
            exact mul_le_mul_of_nonneg_left (hpoint (xs i).1) (abs_nonneg _)
      _ = C * ∑ a : Bool,
            ∑ i ∈ B, |w i| * (|de (xs i).1| * |dμ a (xs i).1|) := by
            simp only [Fintype.sum_bool, Finset.mul_sum, mul_add,
              Finset.sum_add_distrib]
            congr 1 <;> (refine Finset.sum_congr rfl ?_; intro i _; ring)
      _ ≤ C * ∑ a : Bool,
            (c_n * WeightedNorm B w (fun i => de (xs i).1) p
              * WeightedNorm B w (fun i => dμ a (xs i).1) q) := by
            exact mul_le_mul_of_nonneg_left
              (Finset.sum_le_sum (fun a _ => hProd a)) hC_nonneg
      _ = C * c_n
          * WeightedNorm B w (fun i => de (xs i).1) p
          * (∑ a : Bool, WeightedNorm B w (fun i => dμ a (xs i).1) q) := by
            simp only [Fintype.sum_bool]
            ring
  simpa [hEval, C, de, dμ, η] using hMain

/-- **Oracle efficiency for the DR-Learner with a linear-smoother
second stage** — corollary of `dr_oracle_efficient` specialised to a
`LinearSmootherOp` operator.

This is just the projection of the linear-smoother operator onto its
`SecondStageOperator` ancestor (named `toSecondStageOperator` by the
`extends` declaration in `LinearSmoother.lean` line ~53), composed
with `dr_oracle_efficient`.

In the load-bearing linear-smoother application the user combines this
with `cate_linear_smoother_bias_bound` to discharge `hSmoothedBias`. -/
theorem cate_dr_oracle_efficient_linear
    (S : CATEEstimationSystem P γ)
    (hA : S.toPOBackdoorSystem.Assumptions)
    {ε : ℝ} (_h_overlap : S.toBackdoorEstimationSystem.StrictOverlap ε)
    (op : LinearSmootherOp P.Ω P.μ γ)
    (η_hat : ℕ → P.Ω → NuisanceVec γ)
    (x : γ)
    (d_n : ℕ → P.Ω → ℝ)
    (BiasIdent :
      (ℕ → P.Ω → γ × Bool × ℝ → ℝ) →
      (γ × Bool × ℝ → ℝ) →
      (ℕ → P.Ω → γ → ℝ) → Prop)
    (hStab : Stable op.toSecondStageOperator S.τ_val d_n x BiasIdent)
    (hCons : Tendsto_inProb d_n (fun _ => 0) P.μ)
    (hBias : BiasIdent
              (fun n ω z => phi_eta z (η_hat n ω))
              (fun z => phi₀ S z)
              (fun n ω u => condBias (η_hat n ω)
                            S.toBackdoorEstimationSystem.η₀ u))
    (hSmoothedBias : IsLittleOp
      (fun n ω => op.evalAt n ω
        (fun z => condBias (η_hat n ω)
                    S.toBackdoorEstimationSystem.η₀ z.1) x)
      (fun n => drOracleRiskScale S op.toSecondStageOperator x n) P.μ) :
    IsLittleOp
      (fun n ω => drLearnerEstimator S op.toSecondStageOperator η_hat n ω x
                    - drOracleEstimator S op.toSecondStageOperator n ω x)
      (fun n => drOracleRiskScale S op.toSecondStageOperator x n) P.μ :=
  dr_oracle_efficient S hA op.toSecondStageOperator η_hat x d_n BiasIdent
    hStab hCons hBias hSmoothedBias

end CATE
end Estimation
end Causalean
