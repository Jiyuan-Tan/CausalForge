/- Executable-program certificates for the polynomial estimator's fallback branch. -/

import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.PolynomialUpper.ClippingAssembly
import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.PolynomialUpper.Heavy

namespace CausalSmith.Stat.DiscreteAteHeterogeneityFrontier

open Set

-- @node: polynomialArmMeanCode
/-- This straight-line program computes an empirical treatment-arm mean. -/
noncomputable def polynomialArmMeanCode {d : ℕ} (a : Bool) (k : Fin d) :
    AggregatedArithmeticProgram d :=
  .iteLt (.const 0) (.count a k) (.div (.outcomeSum a k) (.count a k)) (.const 0)

-- @node: polynomialHeavyCode
/-- This straight-line program computes the heavy-cell contribution to the polynomial estimator. -/
noncomputable def polynomialHeavyCode {n d : ℕ} (M : ℝ) (k : Fin d) :
    AggregatedArithmeticProgram d :=
  .mul
    (.div (.add (.count false k) (.count true k)) (.const (estimationBlockSize n)))
    (.div (.sub (polynomialArmMeanCode true k) (polynomialArmMeanCode false k))
      (.const M))

-- @node: polynomialMarkedCode
/-- This straight-line program computes a marked polynomial term. -/
noncomputable def polynomialMarkedCode {n d : ℕ} (M : ℝ)
    (k : Fin d) (a : Bool) (j : ℕ) : AggregatedArithmeticProgram d :=
  .div
    (.mul (.mul (.div (.outcomeSum a k) (.const M))
      (.armDescFactorial a k 1 j)) (.cellSub k (j + 1)))
    (.const ((estimationBlockSize n).descFactorial (j + 2)))

-- @node: polynomialLightCode
/-- This straight-line program computes the light-cell polynomial contribution. -/
noncomputable def polynomialLightCode {n d : ℕ} (M B : ℝ) (K : ℕ)
    (k : Fin d) : AggregatedArithmeticProgram d :=
  .sumTerms (K - 1) fun j =>
    .mul (.const (shiftedCoefficient K j.val / B ^ (j.val + 1)))
      (.sub (polynomialMarkedCode (n := n) M k true j.val)
        (polynomialMarkedCode (n := n) M k false j.val))

-- @node: calibratedPolynomialCode
/-- This straight-line program assembles the calibrated polynomial estimator. -/
noncomputable def calibratedPolynomialCode (n d : ℕ) (M : ℝ) :
    AggregatedArithmeticProgram d :=
  let K := polynomialDegree n
  let B := 4096 * logEN n / (estimationBlockSize n : ℕ)
  .mul (.const M)
    (.maximum (.const (-1)) (.minimum (.const 1)
      (.sumCells fun k =>
        .iteLt (.const (256 * logEN n)) (.pilot k)
          (polynomialHeavyCode (n := n) M k)
          (polynomialLightCode (n := n) M B K k))))

-- @node: polynomialMarkedCode_eval
/-- [Each marked syntax node evaluates to the aggregate falling-factorial statistic](goal). -/
lemma polynomialMarkedCode_eval {n d : ℕ} (M : ℝ) (sample : Fin n → Obs d)
    (k : Fin d) (a : Bool) (j : ℕ) :
    (polynomialMarkedCode (n := n) M k a j).eval
        (aggregatePolynomialSample sample) =
      orderedMarkedFactorial M sample k a j := by
  simp [polynomialMarkedCode, AggregatedArithmeticProgram.eval,
    aggregatePolynomialSample, orderedMarkedFactorial, estimationCellCount,
    estimationBlockSize]

-- @node: polynomialLightCode_eval
/-- [Each light-cell syntax subtree evaluates to the declared polynomial term](goal). -/
lemma polynomialLightCode_eval {n d : ℕ} (M B : ℝ) (K : ℕ)
    (sample : Fin n → Obs d) (k : Fin d) :
    (polynomialLightCode (n := n) M B K k).eval
        (aggregatePolynomialSample sample) =
      lightPolynomialTerm M B K sample k := by
  classical
  unfold polynomialLightCode lightPolynomialTerm
  simp only [AggregatedArithmeticProgram.eval]
  simp_rw [polynomialMarkedCode_eval]
  simpa using Fin.sum_univ_eq_sum_range
    (fun j : ℕ => shiftedCoefficient K j / B ^ (j + 1) *
      (orderedMarkedFactorial M sample k true j -
        orderedMarkedFactorial M sample k false j)) (K - 1)

-- @node: calibratedPolynomialCode_computes
/-- [Evaluation of the explicit aggregate syntax is the calibrated estimator branch](goal). -/
lemma calibratedPolynomialCode_computes {n d : ℕ} (M : ℝ)
    (sample : Fin n → Obs d) :
    (calibratedPolynomialCode n d M).eval (aggregatePolynomialSample sample) =
      M * clip (-1) 1 (polynomialNormalizedSum M sample) := by
  classical
  simp only [calibratedPolynomialCode, AggregatedArithmeticProgram.eval,
    polynomialLightCode_eval]
  simp [polynomialHeavyCode, polynomialArmMeanCode, aggregatePolynomialSample,
    AggregatedArithmeticProgram.eval, polynomialNormalizedSum,
    heavyEmpiricalTerm, estimationArmMean,
    estimationCellCount, estimationBlockSize, clip]

-- @node: calibratedPolynomialCode_operationCount_le
/-- [The explicit syntax fits the fixed quadratic-in-degree per-cell budget](goal). -/
lemma calibratedPolynomialCode_operationCount_le (n d : ℕ) (M : ℝ) :
    (calibratedPolynomialCode n d M).operationCount ≤ polynomialOperationBudget n d := by
  classical
  let K := polynomialDegree n
  have hterm (j : Fin (K - 1)) : 12 + 2 * j.val ≤ 14 * (K + 1) := by
    omega
  have hsum : (∑ j : Fin (K - 1), (12 + 2 * j.val)) ≤
      (K - 1) * (14 * (K + 1)) := by
    have h := Finset.sum_le_sum (s := Finset.univ) fun j _ => hterm j
    simpa using h
  dsimp [K] at hsum
  have hsum' :
      (∑ j : Fin (polynomialDegree n - 1),
        (1 + (1 + (1 + (1 + (2 + j.val) + 1)) +
          (1 + (1 + (2 + j.val) + 1))))) ≤
        (polynomialDegree n - 1) * (14 * (polynomialDegree n + 1)) := by
    calc
      _ = ∑ j : Fin (polynomialDegree n - 1), (12 + 2 * j.val) := by
        apply Finset.sum_congr rfl
        intro j _
        omega
      _ ≤ _ := hsum
  have hlight : polynomialDegree n - 1 +
      (∑ j : Fin (polynomialDegree n - 1),
        (1 + (1 + (1 + (1 + (2 + j.val) + 1)) +
          (1 + (1 + (2 + j.val) + 1))))) ≤
      16 * (polynomialDegree n + 1) ^ 2 := by
    have hk : polynomialDegree n - 1 ≤ polynomialDegree n := Nat.sub_le _ _
    have hprod : (polynomialDegree n - 1) *
        (14 * (polynomialDegree n + 1)) ≤
        polynomialDegree n * (14 * (polynomialDegree n + 1)) :=
      Nat.mul_le_mul_right _ hk
    have hcoarse := Nat.add_le_add hk (hsum'.trans hprod)
    apply hcoarse.trans
    nlinarith
  have hsq : 1 ≤ (polynomialDegree n + 1) ^ 2 := by
    nlinarith
  have hmax : max 9 (polynomialDegree n - 1 +
      (∑ j : Fin (polynomialDegree n - 1),
        (1 + (1 + (1 + (1 + (2 + j.val) + 1)) +
          (1 + (1 + (2 + j.val) + 1)))))) ≤
      16 * (polynomialDegree n + 1) ^ 2 := by
    exact max_le (by nlinarith [hsq]) hlight
  simp [calibratedPolynomialCode, polynomialHeavyCode, polynomialArmMeanCode,
    polynomialLightCode, polynomialMarkedCode,
    AggregatedArithmeticProgram.operationCount, polynomialOperationBudget]
  have hmul := Nat.mul_le_mul_left d (Nat.add_le_add_left hmax 1)
  nlinarith [hmul, hsq]

/-- If [the indicated calibration branch applies](hyp:hbranch), [the calibrated branch has a
  concrete aggregate program with the advertised budget](goal). -/
lemma polynomialComplexityBound_of_calibrated {n d : ℕ}
    {handle : PolynomialHandle} {M : ℝ}
    (hbranch : handle.N ≤ n ∧ (d : ℝ) ≤ handle.rho * n * logEN n) :
    PolynomialExactComplexityCertificate n d handle M := by
  let program : AggregatedPolynomialProgram n d handle M :=
    { code := calibratedPolynomialCode n d M
      computesEstimator := by
        intro sample
        rw [calibratedPolynomialCode_computes]
        simp [polyEstimator, rawPolyEstimator, hbranch, polynomialNormalizedSum] }
  exact ⟨program, calibratedPolynomialCode_operationCount_le n d M⟩

/-- If [the indicated calibration branch applies](hyp:hbranch), [on either declared fallback
  branch, the constant-zero aggregate program computes the estimator and has zero arithmetic
  cost](goal). -/
lemma polynomialComplexityBound_of_not_calibrated {n d : ℕ}
    {handle : PolynomialHandle} {M : ℝ}
    (hbranch : ¬ (handle.N ≤ n ∧
      (d : ℝ) ≤ handle.rho * n * logEN n)) :
    PolynomialExactComplexityCertificate n d handle M := by
  let program : AggregatedPolynomialProgram n d handle M :=
    { code := .const 0
      computesEstimator := by
        intro sample
        simp [AggregatedArithmeticProgram.eval, polyEstimator,
          rawPolyEstimator, hbranch] }
  refine ⟨program, ?_⟩
  exact Nat.zero_le _

/-- If [the calibration handle is available](hyp:handle), [every branch of the total polynomial
  estimator has an executable certificate](goal). -/
lemma polynomialComplexityBound_all_branches (n d : ℕ)
    (handle : PolynomialHandle) (M : ℝ) :
    PolynomialExactComplexityCertificate n d handle M := by
  by_cases hbranch : handle.N ≤ n ∧
      (d : ℝ) ≤ handle.rho * n * logEN n
  · exact polynomialComplexityBound_of_calibrated hbranch
  · exact polynomialComplexityBound_of_not_calibrated hbranch

/-- If [the calibration handle is available](hyp:handle), [the fixed `128` proof-local certificate
  implies the public family-level `O(d K²)` arithmetic statement](goal). -/
lemma polynomialComplexityBound (handle : PolynomialHandle) :
    PolynomialComplexityBound handle := by
  refine ⟨128, by norm_num, ?_⟩
  intro n d M
  obtain ⟨program, hprogram⟩ :=
    polynomialComplexityBound_all_branches n d handle M
  exact ⟨program, by simpa [polynomialOperationBudget] using hprogram⟩

end CausalSmith.Stat.DiscreteAteHeterogeneityFrontier
