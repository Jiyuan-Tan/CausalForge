import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Causal.DecisionClass
import Mathlib.Data.Matrix.Invertible
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Winsorized stabilized signed-distance local polynomial estimator

This module defines the empirical Gram and score, the guarded inverse, the
clipped contrast, the population coefficient used by the cited bias theorem,
and the pointwise selected-kernel winsorization bias lemma.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace CausalSmith.Stat.BddUniformLogPenalty

-- @node: estimatorMatrixMeasurableSpace
/-- Equip estimator matrices with the product measurable structure. -/
local instance estimatorMatrixMeasurableSpace (q : ℕ) :
    MeasurableSpace (Matrix (Fin q) (Fin q) ℝ) :=
  MeasurableSpace.pi

-- @node: estimatorMatrixBorelSpace
/-- The estimator-matrix measurable structure is its Borel structure. -/
local instance estimatorMatrixBorelSpace (q : ℕ) :
    BorelSpace (Matrix (Fin q) (Fin q) ℝ) :=
  ⟨by
    change MeasurableSpace.pi = borel (Fin q → Fin q → ℝ)
    exact BorelSpace.measurable_eq⟩

/-- Arm membership for a signed distance. -/
def signedArm (t : Bool) (d : ℝ) : Prop := if t then 0 ≤ d else d < 0

/-- Empirical local-polynomial Gram matrix from compressed observations. -/
noncomputable def empiricalGram (n p : ℕ) (t : Bool) (h : ℝ)
    (u : SignedDistanceSample n) : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ := by
  classical
  exact fun j k => (n : ℝ)⁻¹ * h⁻¹ ^ 2 * ∑ i,
    (if signedArm t (u i).2 then 1 else 0) *
      uniformKernel ((u i).2 / h) * polyBasis p ((u i).2 / h) j *
      polyBasis p ((u i).2 / h) k

/-- Winsorized empirical local-polynomial score. -/
noncomputable def empiricalScore (n p : ℕ) (t : Bool) (h B : ℝ)
    (u : SignedDistanceSample n) : Fin (p + 1) → ℝ := by
  classical
  exact fun j => (n : ℝ)⁻¹ * h⁻¹ ^ 2 * ∑ i,
    (if signedArm t (u i).2 then 1 else 0) * uniformKernel ((u i).2 / h) *
      polyBasis p ((u i).2 / h) j * winsorize B (u i).1

/-- Quadratic-form empirical Gram guard at `(2L)⁻¹`. -/
def empiricalGramGuard {p : ℕ} (L : ℝ)
    (A : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ) : Prop :=
  ∀ v : Fin (p + 1) → ℝ,
    (2 * L)⁻¹ * ∑ i, (v i) ^ 2 ≤ matrixQuadratic A v

/-- The guarded coefficient: inverse score on the stable branch and zero
otherwise. -/
noncomputable def guardedCoefficient (n p : ℕ) (L : ℝ) (t : Bool)
    (h B : ℝ) (u : SignedDistanceSample n) : Fin (p + 1) → ℝ := by
  classical
  exact if empiricalGramGuard L (empiricalGram n p t h u) then
    Matrix.mulVec (empiricalGram n p t h u)⁻¹ (empiricalScore n p t h B u)
  else 0

/-- Projection onto `[-C,C]`. -/
def clip (C y : ℝ) : ℝ := max (-C) (min C y)

/-- The theorem's winsorization level `B_n = a_n^(-1/3)`. -/
noncomputable def winsorLevel (n : ℕ) : ℝ :=
  Real.rpow (frontierRate n) (-(1 : ℝ) / 3)
  -- @realizes B_n(a_n^(-1/3))

/-- Population score in the original, unwinsorized normal equations. -/
noncomputable def populationScore (P : A1A2Law) (p : ℕ) (t : Bool)
    (x : Score) (h : ℝ) : Fin (p + 1) → ℝ := by
  classical
  exact fun j => ∫ w,
    h⁻¹ ^ 2 *
      (if signedArm t (signedDistance (knownGeometry P) x (causalScore w))
        then 1 else 0) *
      uniformKernel (signedDistance (knownGeometry P) x (causalScore w) / h) *
      polyBasis p (signedDistance (knownGeometry P) x (causalScore w) / h) j *
      observedOutcome P w ∂P.law

/-- The original population local-polynomial coefficient. -/
noncomputable def populationCoefficient (P : A1A2Law) (p : ℕ) (t : Bool)
    (x : Score) (h : ℝ) : Fin (p + 1) → ℝ :=
  Matrix.mulVec (populationGram P p t x h)⁻¹ (populationScore P p t x h)

-- @node: def:cty-stabilized-local-polynomial-estimator
/-- The winsorized, clipped, Gram-stabilized signed-distance local-polynomial
rule at bandwidth `h`, using `B(h)=h^(-1/3)`. -/
noncomputable def stabilizedLocalPolynomial (n p : ℕ) (L h : ℝ) :
    A1A2RuleFun n :=
  fun w G x =>
    let u := geometrySignedDistanceData n G w x
    let B := Real.rpow h (-(1 : ℝ) / 3)
    clip (2 * L)
      (guardedCoefficient n p L true h B u 0 -
        guardedCoefficient n p L false h B u 0)
  -- @realizes \widehat{\tau}^{12,\mathrm{LP}}_{n,h}(winsorized stabilized LP rule)
  -- @realizes h(bandwidth argument) @realizes \psi_B(winsorization inside score)

/-- The fixed uniform kernel is Borel measurable. -/
-- @node: uniformKernel_measurable
lemma uniformKernel_measurable : Measurable uniformKernel := by
  unfold uniformKernel
  exact measurable_const.indicator measurableSet_Icc

/-- Each coordinate of the finite monomial basis is Borel measurable. -/
-- @node: polyBasis_apply_measurable
lemma polyBasis_apply_measurable (p : ℕ) (j : Fin (p + 1)) :
    Measurable (fun d : ℝ => polyBasis p d j) := by
  unfold polyBasis
  fun_prop

/-- Winsorization at a fixed level is Borel measurable. -/
-- @node: winsorize_measurable
lemma winsorize_measurable (B : ℝ) : Measurable (winsorize B) := by
  unfold winsorize
  apply Measurable.ite measurableSet_Iio
  · fun_prop
  · apply Measurable.ite (by
      simpa using measurableSet_singleton (0 : ℝ))
    · fun_prop
    · fun_prop

/-- A finite real matrix-valued map is measurable exactly when all of its
entries are measurable. -/
-- @node: estimatorMeasurable_matrix_iff
lemma estimatorMeasurable_matrix_iff
    {α : Type*} [MeasurableSpace α] {q : ℕ}
    (f : α → Matrix (Fin q) (Fin q) ℝ) :
    Measurable f ↔ ∀ i j, Measurable (fun x => f x i j) := by
  constructor
  · intro hf i j
    exact measurable_pi_iff.mp (measurable_pi_iff.mp hf i) j
  · intro h
    exact measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => h i j

/-- Mathlib's total inverse on finite real matrices is Borel measurable. -/
-- @node: estimatorMatrix_inv_measurable
lemma estimatorMatrix_inv_measurable (q : ℕ) :
    Measurable (fun G : Matrix (Fin q) (Fin q) ℝ => G⁻¹) := by
  rw [estimatorMeasurable_matrix_iff]
  intro i j
  simp only [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv]
  fun_prop

/-- Every coordinate of an inverse-matrix--vector product is measurable when
the matrix and vector inputs are measurable. -/
-- @node: estimatorInv_mulVec_apply_measurable
lemma estimatorInv_mulVec_apply_measurable
    {α : Type*} [MeasurableSpace α] {q : ℕ}
    (G : α → Matrix (Fin q) (Fin q) ℝ) (v : α → Fin q → ℝ)
    (hG : Measurable G) (hv : Measurable v) (i : Fin q) :
    Measurable (fun x => (G x)⁻¹.mulVec (v x) i) := by
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.measurable_sum
  intro j _
  exact ((estimatorMeasurable_matrix_iff _).mp
      ((estimatorMatrix_inv_measurable q).comp hG) i j).mul
    (measurable_pi_iff.mp hv j)

/-- The empirical local-polynomial Gram matrix is measurable in the
compressed sample. -/
-- @node: empiricalGram_measurable
lemma empiricalGram_measurable (n p : ℕ) (t : Bool) (h : ℝ) :
    Measurable (empiricalGram n p t h) := by
  classical
  rw [estimatorMeasurable_matrix_iff]
  intro j k
  unfold empiricalGram
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro i _
  have hpair : Measurable (fun u : SignedDistanceSample n => u i) :=
    measurable_pi_apply i
  have hd : Measurable (fun u : SignedDistanceSample n => (u i).2) :=
    measurable_snd.comp hpair
  have harm : Measurable (fun u : SignedDistanceSample n =>
      if signedArm t (u i).2 then (1 : ℝ) else 0) := by
    cases t
    · simp only [signedArm, Bool.false_eq_true, if_false]
      exact Measurable.ite (measurableSet_lt hd measurable_const)
        measurable_const measurable_const
    · simp only [signedArm, if_true]
      exact Measurable.ite (measurableSet_le measurable_const hd)
        measurable_const measurable_const
  exact ((harm.mul
      (uniformKernel_measurable.comp (hd.div_const h))).mul
        ((polyBasis_apply_measurable p j).comp (hd.div_const h))).mul
          ((polyBasis_apply_measurable p k).comp (hd.div_const h))

/-- The winsorized empirical score is measurable in the compressed sample. -/
-- @node: empiricalScore_measurable
lemma empiricalScore_measurable (n p : ℕ) (t : Bool) (h B : ℝ) :
    Measurable (empiricalScore n p t h B) := by
  classical
  rw [measurable_pi_iff]
  intro j
  unfold empiricalScore
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro i _
  have hpair : Measurable (fun u : SignedDistanceSample n => u i) :=
    measurable_pi_apply i
  have hy : Measurable (fun u : SignedDistanceSample n => (u i).1) :=
    measurable_fst.comp hpair
  have hd : Measurable (fun u : SignedDistanceSample n => (u i).2) :=
    measurable_snd.comp hpair
  have harm : Measurable (fun u : SignedDistanceSample n =>
      if signedArm t (u i).2 then (1 : ℝ) else 0) := by
    cases t
    · simp only [signedArm, Bool.false_eq_true, if_false]
      exact Measurable.ite (measurableSet_lt hd measurable_const)
        measurable_const measurable_const
    · simp only [signedArm, if_true]
      exact Measurable.ite (measurableSet_le measurable_const hd)
        measurable_const measurable_const
  exact ((harm.mul
      (uniformKernel_measurable.comp (hd.div_const h))).mul
        ((polyBasis_apply_measurable p j).comp (hd.div_const h))).mul
          ((winsorize_measurable B).comp hy)

/-- The quadratic-form Gram guard is a Borel set of finite matrices. -/
-- @node: empiricalGramGuard_measurableSet
lemma empiricalGramGuard_measurableSet {p : ℕ} (L : ℝ) :
    MeasurableSet {A : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ |
      empiricalGramGuard L A} := by
  apply IsClosed.measurableSet
  unfold empiricalGramGuard matrixQuadratic
  simp only [Set.setOf_forall]
  apply isClosed_iInter
  intro v
  apply isClosed_le <;> fun_prop

/-- The guarded inverse coefficient vector is measurable in the compressed
sample. -/
-- @node: guardedCoefficient_measurable
lemma guardedCoefficient_measurable (n p : ℕ) (L h B : ℝ) (t : Bool) :
    Measurable (guardedCoefficient n p L t h B) := by
  unfold guardedCoefficient
  apply Measurable.ite
  · exact (empiricalGramGuard_measurableSet L).preimage
      (empiricalGram_measurable n p t h)
  · rw [measurable_pi_iff]
    intro i
    apply estimatorInv_mulVec_apply_measurable
    · exact empiricalGram_measurable n p t h
    · exact empiricalScore_measurable n p t h B
  · fun_prop

/-- The explicit estimator is a member of the sectionwise-Borel decision
class at every positive bandwidth. -/
-- @node: stabilizedLocalPolynomial_mem
lemma stabilizedLocalPolynomial_mem (n p : ℕ) (ν L h : ℝ) (_hh : 0 < h) :
    stabilizedLocalPolynomial n p L h ∈
      A1A2PointIndexedDecisionClass n p ν L := by
  let B := Real.rpow h (-(1 : ℝ) / 3)
  let T : A1A2PIRule n := {
    map := fun _G _x u => clip (2 * L)
      (guardedCoefficient n p L true h B u 0 -
        guardedCoefficient n p L false h B u 0)
    section_measurable := by
      intro G x
      unfold clip
      exact measurable_const.max (measurable_const.min
        ((measurable_pi_iff.mp
            (guardedCoefficient_measurable n p L h B true) 0).sub
          (measurable_pi_iff.mp
            (guardedCoefficient_measurable n p L h B false) 0))) }
  refine ⟨T, ?_⟩
  intro P hP w x hx
  have hu : geometrySignedDistanceData n (knownGeometry P) w x =
      signedDistanceData n P w x := by
    funext i
    apply Prod.ext
    · simp only [geometrySignedDistanceData, signedDistanceData,
        observedOutcome, treatment, knownGeometry]
      by_cases hi : causalScore (w i) ∈ P.A1 <;>
        simp [Set.indicator, hi]
    · rfl
  simp only [stabilizedLocalPolynomial, T, B]
  rw [hu]

-- @node: abs_sub_winsorize_le_abs
/-- Winsorization cannot remove more than the magnitude of its input. -/
lemma abs_sub_winsorize_le_abs {B y : ℝ} (hB : 0 ≤ B) :
    |y - winsorize B y| ≤ |y| := by
  by_cases hy : y < 0
  · rw [winsorize, if_pos hy]
    rcases le_total |y| B with hay | hBa
    · rw [min_eq_left hay]
      have hw : -|y| = y := by rw [abs_of_neg hy]; ring
      rw [hw, sub_self, abs_zero]
      exact abs_nonneg y
    · rw [min_eq_right hBa]
      rw [abs_of_nonpos (by rw [abs_of_neg hy] at hBa; linarith)]
      rw [abs_of_neg hy]
      linarith
  · rw [winsorize, if_neg hy]
    by_cases hy0 : y = 0
    · simp [hy0]
    · rw [if_neg hy0]
      have hypos : 0 < y := lt_of_le_of_ne (le_of_not_gt hy) (Ne.symm hy0)
      rcases le_total |y| B with hay | hBa
      · rw [min_eq_left hay]
        rw [abs_of_pos hypos, sub_self, abs_zero]
        exact hypos.le
      · rw [min_eq_right hBa]
        rw [abs_of_nonneg (by rw [abs_of_pos hypos] at hBa; linarith)]
        rw [abs_of_pos hypos]
        linarith

-- @node: winsorize_tail_le_moment
/-- Above a threshold at least one, the winsorization remainder is dominated
by the `(2+ν)` moment times `B⁻³` whenever `ν ≥ 2`. -/
lemma winsorize_tail_le_moment {ν B y : ℝ} (hν : 2 ≤ ν) (hB : 1 ≤ B) :
    |y - winsorize B y| ≤ |y| ^ (2 + ν) * B ^ (-3 : ℤ) := by
  by_cases hay : |y| ≤ B
  · have hw : winsorize B y = y := by
      by_cases hy : y < 0
      · rw [winsorize, if_pos hy, min_eq_left hay, abs_of_neg hy]
        ring
      · by_cases hy0 : y = 0
        · simp [winsorize, hy0]
        · have hypos : 0 < y := lt_of_le_of_ne (le_of_not_gt hy) (Ne.symm hy0)
          rw [winsorize, if_neg hy, if_neg hy0, min_eq_left hay, abs_of_pos hypos]
    rw [hw, sub_self, abs_zero]
    positivity
  · have hBa : B < |y| := lt_of_not_ge hay
    have ha1 : 1 ≤ |y| := hB.trans hBa.le
    have hpow : |y| ^ (4 : ℕ) ≤ |y| ^ (2 + ν) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le ha1 (by norm_num; linarith)
    have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB
    have hB3pos : 0 < B ^ (3 : ℕ) := pow_pos hBpos _
    have hratio : |y| ≤ |y| ^ (4 : ℕ) * B ^ (-3 : ℤ) := by
      change |y| ≤ |y| ^ (4 : ℕ) * (B ^ (3 : ℕ))⁻¹
      apply (le_mul_inv_iff₀ hB3pos).2
      calc
        |y| * B ^ (3 : ℕ) ≤ |y| * |y| ^ (3 : ℕ) :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (le_trans zero_le_one hB) hBa.le 3) (abs_nonneg y)
        _ = |y| ^ (4 : ℕ) := by ring
    exact (abs_sub_winsorize_le_abs (le_trans zero_le_one hB)).trans
      (hratio.trans (mul_le_mul_of_nonneg_right hpow (by positivity)))

-- @node: lem:cty-winsorization-bias
/-- A pointwise selected-kernel `(2+ν)` moment envelope gives the deterministic
`B⁻³` winsorization bias bound. -/
lemma cty_winsorization_bias (p : ℕ) (ν L B : ℝ) (P : A1A2Law)
    (hP : A1A2Class p ν L P) (hB : 1 ≤ B) (t : Bool)
    (x : Score) (hx : x ∈ P.support) :
    |(∫ y, y ∂selectedA1A2CondKer P ν L t x) -
        (∫ y, winsorize B y ∂selectedA1A2CondKer P ν L t x)| ≤
      L * B ^ (-3 : ℤ) := by
  rcases hP with ⟨hν, hL, hSupport, hDensCont, hDens, hMu, hVar,
    hMean, hVariance, hMoment, hGeom, hVC, hGram, hMass, hSlice⟩
  have hK : Nonempty (A1A2KernelWitness P ν L) := hMean.1
  letI : IsProbabilityMeasure (selectedA1A2CondKer P ν L t x) :=
    (selectedA1A2CondKer_markov hK t).isProbabilityMeasure x
  have hmoment := hMoment t x hx
  have hpow_int : Integrable (fun y : ℝ => |y| ^ (2 + ν))
      (selectedA1A2CondKer P ν L t x) := by
    refine ⟨((Real.continuous_rpow_const (by linarith)).comp
      continuous_abs).measurable.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    have hlt : selectedA1A2CondAbsMoment P ν L t x < ∞ :=
      lt_of_le_of_lt hmoment ENNReal.ofReal_lt_top
    simpa [selectedA1A2CondAbsMoment, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)] using hlt
  have hy_abs : Integrable (fun y : ℝ => |y|)
      (selectedA1A2CondKer P ν L t x) := by
    have hint := integrable_norm_rpow_of_le
      (μ := selectedA1A2CondKer P ν L t x)
      (f := fun y : ℝ => y) measurable_id.aestronglyMeasurable
      (p := 1) (q := 2 + ν) (by norm_num) (by linarith) (by linarith) hpow_int
    simpa [Real.norm_eq_abs, Real.rpow_one] using hint
  have hy : Integrable (fun y : ℝ => y) (selectedA1A2CondKer P ν L t x) :=
    hy_abs.mono measurable_id.aestronglyMeasurable (by simp [Real.norm_eq_abs])
  have hwin : Integrable (fun y : ℝ => winsorize B y)
      (selectedA1A2CondKer P ν L t x) := by
    have hwin_meas : Measurable (fun y : ℝ => winsorize B y) := by
      unfold winsorize
      apply Measurable.ite measurableSet_Iio
      · fun_prop
      · have hz : MeasurableSet {y : ℝ | y = 0} := by
          simpa only [Set.setOf_eq_eq_singleton] using measurableSet_singleton (0 : ℝ)
        apply Measurable.ite hz
        · fun_prop
        · fun_prop
    refine (integrable_const B).mono hwin_meas.aestronglyMeasurable ?_
    filter_upwards [] with y
    dsimp [winsorize]
    split_ifs
    · rw [abs_neg, abs_of_nonneg (le_min (abs_nonneg y)
        (le_trans zero_le_one hB)), abs_of_nonneg (le_trans zero_le_one hB)]
      exact min_le_right _ _
    · simpa using abs_nonneg B
    · rw [abs_of_nonneg (le_min (abs_nonneg y)
        (le_trans zero_le_one hB)), abs_of_nonneg (le_trans zero_le_one hB)]
      exact min_le_right _ _
  rw [← integral_sub hy hwin]
  calc
    |∫ y, y - winsorize B y ∂selectedA1A2CondKer P ν L t x| ≤
        ∫ y, |y| ^ (2 + ν) * B ^ (-3 : ℤ)
          ∂selectedA1A2CondKer P ν L t x := by
      change ‖∫ y, y - winsorize B y ∂selectedA1A2CondKer P ν L t x‖ ≤ _
      apply norm_integral_le_of_norm_le (hpow_int.mul_const _)
      filter_upwards [] with y
      simpa [Real.norm_eq_abs] using winsorize_tail_le_moment hν hB (y := y)
    _ = B ^ (-3 : ℤ) * ∫ y, |y| ^ (2 + ν)
        ∂selectedA1A2CondKer P ν L t x := by
      rw [← integral_const_mul]
      congr 1
      funext y
      ring
    _ ≤ L * B ^ (-3 : ℤ) := by
      have hLint : ∫ y, |y| ^ (2 + ν)
          ∂selectedA1A2CondKer P ν L t x ≤ L := by
        rw [← ENNReal.ofReal_le_ofReal_iff (le_trans (by norm_num) hL)]
        rw [ofReal_integral_eq_lintegral_ofReal hpow_int
          (Filter.Eventually.of_forall fun y => Real.rpow_nonneg (abs_nonneg y) _)]
        simpa [selectedA1A2CondAbsMoment] using hmoment
      nlinarith [show 0 ≤ B ^ (-3 : ℤ) by positivity]

end CausalSmith.Stat.BddUniformLogPenalty
