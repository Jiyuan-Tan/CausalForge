import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.LightCellVariance
import Mathlib.Algebra.Order.Chebyshev

namespace CausalSmith.Stat.DiscreteAteMinimaxLoggap

open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- A flattened index set for one arm of the sparse factorial lift. -/
def sparseIndexSet (M : ℕ) : Finset (ℕ × ℕ × Cell) :=
  ((Finset.range (M - 1)).product
    ((Finset.range M).product (Finset.univ : Finset Cell))).filter
      fun u => u.2.1 ≤ u.1

lemma mem_sparseIndexSet {M j t : ℕ} {ay : Cell} :
    (j, t, ay) ∈ sparseIndexSet M ↔ j < M - 1 ∧ t < j + 1 := by
  simp [sparseIndexSet]
  omega

lemma filter_range_le_eq_range_succ {M j : ℕ} (hj : j < M) :
    (Finset.range M).filter (fun t => t ≤ j) = Finset.range (j + 1) := by
  ext t
  simp
  omega

/-- Establishes the stated summation identity or bound for sum sparse Index Set. -/
lemma sum_sparseIndexSet {M : ℕ} (f : ℕ → ℕ → Cell → ℝ) :
    ∑ u ∈ sparseIndexSet M, f u.1 u.2.1 u.2.2 =
      ∑ j ∈ Finset.range (M - 1),
        ∑ t ∈ Finset.range (j + 1), ∑ ay : Cell, f j t ay := by
  classical
  let S := Finset.range (M - 1)
  let T := (Finset.range M).product (Finset.univ : Finset Cell)
  calc
    ∑ u ∈ sparseIndexSet M, f u.1 u.2.1 u.2.2 =
        ∑ u ∈ S.product T,
          if u.2.1 ≤ u.1 then f u.1 u.2.1 u.2.2 else 0 := by
      exact Finset.sum_filter _ _
    _ = ∑ j ∈ S, ∑ v ∈ T,
        if v.1 ≤ j then f j v.1 v.2 else 0 := by
      exact Finset.sum_product S T _
    _ = ∑ j ∈ S, ∑ t ∈ Finset.range M, ∑ ay : Cell,
        if t ≤ j then f j t ay else 0 := by
      apply Finset.sum_congr rfl
      intro j _hj
      exact Finset.sum_product (Finset.range M) Finset.univ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      calc
        (∑ t ∈ Finset.range M, ∑ ay : Cell,
            if t ≤ j then f j t ay else 0) =
            ∑ t ∈ (Finset.range M).filter (fun t => t ≤ j),
              ∑ ay : Cell, f j t ay := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro t _ht
          by_cases h : t ≤ j <;> simp [h]
        _ = _ := by
          rw [filter_range_le_eq_range_succ (by
            have := Finset.mem_range.mp hj
            omega)]

/-- Defines sparse Term, the stated quantity or construction used in the discrete average-treatment-effect estimator. -/
noncomputable def sparseTerm {n d : ℕ} (sample : Fin n → Obs d)
    (k : Fin d) (a : Fin 2) (u : ℕ × ℕ × Cell) : ℝ :=
  sparseCoefficient (polynomialDegree n) (bandwidth n) u.1 u.2.1 *
    factorialMonomial sample k
      (factorialExpansionIndex a u.2.2 u.1 u.2.1)

/-- Establishes the stated equality relating sparse Arm Contribution eq sum sparse Term. -/
lemma sparseArmContribution_eq_sum_sparseTerm {n d : ℕ}
    (sample : Fin n → Obs d) (k : Fin d) (a : Fin 2) :
    sparseArmContribution sample k a =
      ∑ u ∈ sparseIndexSet (polynomialDegree n), sparseTerm sample k a u := by
  classical
  unfold sparseArmContribution sparseTerm
  exact (sum_sparseIndexSet (fun j t ay =>
    sparseCoefficient (polynomialDegree n) (bandwidth n) j t *
      factorialMonomial sample k (factorialExpansionIndex a ay j t))).symm

/-- Establishes the stated property of sparse Index degree in the discrete average-treatment-effect construction. -/
lemma sparseIndex_degree {M : ℕ} {u : ℕ × ℕ × Cell}
    (hu : u ∈ sparseIndexSet M) : u.1 + 2 ≤ M := by
  rw [mem_sparseIndexSet] at hu
  omega

/-- Establishes the stated upper bound for sparse Index inner le. -/
lemma sparseIndex_inner_le {M : ℕ} {u : ℕ × ℕ × Cell}
    (hu : u ∈ sparseIndexSet M) : u.2.1 ≤ u.1 := by
  rw [mem_sparseIndexSet] at hu
  exact Nat.lt_succ_iff.mp (by simpa only [Nat.succ_eq_add_one] using hu.2)

/-- Defines sparse Term Envelope, the stated quantity or construction used in the discrete average-treatment-effect estimator. -/
noncomputable def sparseTermEnvelope {d : ℕ} (P : DiscreteLaw d)
    (k : Fin d) (M m : ℕ) (B : ℝ) (a : Fin 2)
    (u : ℕ × ℕ × Cell) : ℝ :=
  |sparseCoefficient M B u.1 u.2.1| *
    (factorialExpansionIndex a u.2.2 u.1 u.2.1).prod
      (fun cy e => (cellVector P k cy + (M : ℝ) / m) ^ e)

/-- Establishes the stated equality relating sum sparse Term Envelope eq sparse Arm Envelope. -/
lemma sum_sparseTermEnvelope_eq_sparseArmEnvelope {d M m : ℕ} {B : ℝ}
    (P : DiscreteLaw d) (k : Fin d) (a : Fin 2) :
    ∑ u ∈ sparseIndexSet M, sparseTermEnvelope P k M m B a u =
      sparseArmEnvelope M B (shiftedCellVector P k M m) a := by
  classical
  unfold sparseTermEnvelope sparseArmEnvelope shiftedCellVector sparseCoefficient
  exact sum_sparseIndexSet (fun j t ay =>
    |(B⁻¹ * gCoefficient M j * B⁻¹ ^ j * (Nat.choose j t : ℝ))| *
      (factorialExpansionIndex a ay j t).prod
        (fun cy e => (cellVector P k cy + (M : ℝ) / m) ^ e))

/-- Shows that integrable sparse Term mul is integrable under the stated sampling distribution. -/
lemma integrable_sparseTerm_mul {n d : ℕ} (P : DiscreteLaw d)
    (k : Fin d) (a b : Fin 2) (u v : ℕ × ℕ × Cell) :
    Integrable (fun ω : ℕ → Obs d =>
      sparseTerm (fun i : Fin n => ω i) k a u *
        sparseTerm (fun i : Fin n => ω i) k b v)
      (Measure.infinitePi (fun _ : ℕ => obsLaw P)) := by
  have h := integrable_factorialMonomial_mul_trunc (n := n) P k
    (factorialExpansionIndex a u.2.2 u.1 u.2.1)
    (factorialExpansionIndex b v.2.2 v.1 v.2.1)
  convert h.const_mul
    (sparseCoefficient (polynomialDegree n) (bandwidth n) u.1 u.2.1 *
      sparseCoefficient (polynomialDegree n) (bandwidth n) v.1 v.2.1) using 1
  funext ω
  simp only [sparseTerm]
  ring

/-- Shows that integrable sparse Term is integrable under the stated sampling distribution. -/
lemma integrable_sparseTerm {n d : ℕ} (P : DiscreteLaw d)
    (k : Fin d) (a : Fin 2) (u : ℕ × ℕ × Cell) :
    Integrable (fun ω : ℕ → Obs d =>
      sparseTerm (fun i : Fin n => ω i) k a u)
      (Measure.infinitePi (fun _ : ℕ => obsLaw P)) := by
  unfold sparseTerm
  exact (integrable_factorialMonomial_trunc P k _).const_mul _

/-- The diagonal arm bound obtained by summing the joint factorial-moment
certificate over the flattened sparse polynomial. -/
lemma integral_sparseArm_sq_le {n d : ℕ} (P : DiscreteLaw d) (k : Fin d)
    (a : Fin 2) (hn : 0 < splitSize n 1)
    (hsize : 4 * polynomialDegree n ^ 2 ≤ splitSize n 1) :
    ∫ ω : ℕ → Obs d,
        sparseArmContribution (fun i : Fin n => ω i) k a ^ 2
        ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P)) ≤
      Real.exp 1 *
        (sparseArmEnvelope (polynomialDegree n) (bandwidth n)
          (shiftedCellVector P k (polynomialDegree n) (splitSize n 1)) a) ^ 2 := by
  classical
  let S := sparseIndexSet (polynomialDegree n)
  let T := fun u : ℕ × ℕ × Cell => fun ω : ℕ → Obs d =>
    sparseTerm (fun i : Fin n => ω i) k a u
  let E := fun u : ℕ × ℕ × Cell =>
    sparseTermEnvelope P k (polynomialDegree n) (splitSize n 1)
      (bandwidth n) a u
  simp_rw [sparseArmContribution_eq_sum_sparseTerm]
  change ∫ ω, (∑ u ∈ S, T u ω) ^ 2 ∂_ ≤ _
  simp_rw [pow_two, Finset.sum_mul_sum]
  rw [integral_finset_sum S (fun u _hu =>
    integrable_finset_sum S (fun v _hv => integrable_sparseTerm_mul P k a a u v))]
  have hsum : (∑ u ∈ S, ∫ ω : ℕ → Obs d,
      ∑ v ∈ S, T u ω * T v ω
      ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P))) ≤
      ∑ u ∈ S, ∑ v ∈ S, Real.exp 1 * (E u * E v) := by
    apply Finset.sum_le_sum
    intro u hu
    rw [integral_finset_sum S (fun v _hv => integrable_sparseTerm_mul P k a a u v)]
    apply Finset.sum_le_sum
    intro v hv
    have hterm := integral_sparse_terms_mul_shift_le
        (M := polynomialDegree n) (B := bandwidth n) P k a a
      u.1 u.2.1 v.1 v.2.1 u.2.2 v.2.2
      (sparseIndex_inner_le hu) (sparseIndex_inner_le hv)
      (sparseIndex_degree hu) (sparseIndex_degree hv) hn hsize
    dsimp only [T, E, sparseTerm, sparseTermEnvelope]
    convert hterm using 1 <;> ring
  refine hsum.trans ?_
  change (∑ u ∈ S, ∑ v ∈ S, Real.exp 1 * (E u * E v)) ≤ _
  rw [show (∑ u ∈ S, ∑ v ∈ S, Real.exp 1 * (E u * E v)) =
        Real.exp 1 * (∑ u ∈ S, E u) ^ 2 by
      rw [pow_two, Finset.sum_mul_sum]
      simp only [Finset.mul_sum]
      ]
  rw [sum_sparseTermEnvelope_eq_sparseArmEnvelope]
  rw [pow_two]

/-- A genuinely light cell has a uniformly bounded shifted coefficient
envelope.  This is equation (15) followed by the exact `A=6` certificate. -/
lemma sparseArmEnvelope_shifted_le {n d : ℕ} (P : DiscreteLaw d) (k : Fin d)
    (a : Fin 2) (hM : 0 < polynomialDegree n) (hB : 0 < bandwidth n)
    (hmass : cellMass P k +
      4 * (polynomialDegree n : ℝ) / splitSize n 1 ≤ bandwidth n) :
    sparseArmEnvelope (polynomialDegree n) (bandwidth n)
        (shiftedCellVector P k (polynomialDegree n) (splitSize n 1)) a ≤
      bandwidth n * 6 ^ polynomialDegree n := by
  apply sparseArmEnvelope_le hM hB _
    (shiftedCellVector_nonneg P k (polynomialDegree n) (splitSize n 1))
  rw [shiftedCellVector_sum]
  exact hmass

lemma sparseArmEnvelope_nonneg {M : ℕ} {B : ℝ} (v : Cell → ℝ)
    (hv : ∀ ay, 0 ≤ v ay) (a : Fin 2) : 0 ≤ sparseArmEnvelope M B v a := by
  unfold sparseArmEnvelope
  exact Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun t _ =>
    Finset.sum_nonneg fun ay _ => mul_nonneg (abs_nonneg _)
      (multiMonomial_nonneg _ _ hv)

/-- Evaluates or bounds the stated integral involving integral sparse Arm sq rate le. -/
lemma integral_sparseArm_sq_rate_le {n d : ℕ} (P : DiscreteLaw d)
    (k : Fin d) (a : Fin 2) (hn : 0 < splitSize n 1)
    (hsize : 4 * polynomialDegree n ^ 2 ≤ splitSize n 1)
    (hM : 0 < polynomialDegree n) (hB : 0 < bandwidth n)
    (hmass : cellMass P k +
      4 * (polynomialDegree n : ℝ) / splitSize n 1 ≤ bandwidth n) :
    ∫ ω : ℕ → Obs d,
        sparseArmContribution (fun i : Fin n => ω i) k a ^ 2
        ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P)) ≤
      Real.exp 1 * (bandwidth n * 6 ^ polynomialDegree n) ^ 2 := by
  refine (integral_sparseArm_sq_le P k a hn hsize).trans ?_
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos 1).le
  apply pow_le_pow_left₀
  · unfold sparseArmEnvelope
    exact Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun t _ =>
      Finset.sum_nonneg fun ay _ => mul_nonneg (abs_nonneg _)
        (multiMonomial_nonneg _ _
          (shiftedCellVector_nonneg P k (polynomialDegree n) (splitSize n 1)))
  · exact sparseArmEnvelope_shifted_le P k a hM hB hmass

/-- Shows that integrable sparse Arm sq is integrable under the stated sampling distribution. -/
lemma integrable_sparseArm_sq {n d : ℕ} (P : DiscreteLaw d)
    (k : Fin d) (a : Fin 2) :
    Integrable (fun ω : ℕ → Obs d =>
      sparseArmContribution (fun i : Fin n => ω i) k a ^ 2)
      (Measure.infinitePi (fun _ : ℕ => obsLaw P)) := by
  classical
  simp_rw [sparseArmContribution_eq_sum_sparseTerm, pow_two,
    Finset.sum_mul_sum]
  exact integrable_finset_sum _ fun u _ =>
    integrable_finset_sum _ fun v _ => integrable_sparseTerm_mul P k a a u v

/-- Shows that integrable sparse Arm is integrable under the stated sampling distribution. -/
lemma integrable_sparseArm {n d : ℕ} (P : DiscreteLaw d)
    (k : Fin d) (a : Fin 2) :
    Integrable (fun ω : ℕ → Obs d =>
      sparseArmContribution (fun i : Fin n => ω i) k a)
      (Measure.infinitePi (fun _ : ℕ => obsLaw P)) := by
  classical
  simp_rw [sparseArmContribution_eq_sum_sparseTerm]
  exact integrable_finset_sum _ fun u _ => integrable_sparseTerm P k a u

/-- Shows that integrable factorial Polynomial Contribution trunc rate is integrable under the stated sampling distribution. -/
lemma integrable_factorialPolynomialContribution_trunc_rate {n d : ℕ}
    (P : DiscreteLaw d) (k : Fin d) :
    Integrable (fun ω : ℕ → Obs d =>
      factorialPolynomialContribution (fun i : Fin n => ω i) k)
      (Measure.infinitePi (fun _ : ℕ => obsLaw P)) := by
  rw [show (fun ω : ℕ → Obs d =>
      factorialPolynomialContribution (fun i : Fin n => ω i) k) =
      (fun ω => sparseArmContribution (fun i : Fin n => ω i) k 1 -
        sparseArmContribution (fun i : Fin n => ω i) k 0) by
    funext ω
    exact factorialPolynomialContribution_eq_sparseArms _ _]
  apply Integrable.sub
  · unfold sparseArmContribution
    exact integrable_finset_sum _ fun j _ => integrable_finset_sum _ fun t _ =>
      integrable_finset_sum _ fun ay _ =>
        (integrable_factorialMonomial_trunc P k _).const_mul _
  · unfold sparseArmContribution
    exact integrable_finset_sum _ fun j _ => integrable_finset_sum _ fun t _ =>
      integrable_finset_sum _ fun ay _ =>
        (integrable_factorialMonomial_trunc P k _).const_mul _

/-- Shows that integrable factorial Polynomial Contribution sq is integrable under the stated sampling distribution. -/
lemma integrable_factorialPolynomialContribution_sq {n d : ℕ}
    (P : DiscreteLaw d) (k : Fin d) :
    Integrable (fun ω : ℕ → Obs d =>
      factorialPolynomialContribution (fun i : Fin n => ω i) k ^ 2)
      (Measure.infinitePi (fun _ : ℕ => obsLaw P)) := by
  rw [show (fun ω : ℕ → Obs d =>
      factorialPolynomialContribution (fun i : Fin n => ω i) k ^ 2) =
      (fun ω =>
        sparseArmContribution (fun i : Fin n => ω i) k 1 ^ 2 +
        sparseArmContribution (fun i : Fin n => ω i) k 0 ^ 2 -
        2 * (sparseArmContribution (fun i : Fin n => ω i) k 1 *
          sparseArmContribution (fun i : Fin n => ω i) k 0)) by
    funext ω
    rw [factorialPolynomialContribution_eq_sparseArms]
    ring]
  have h10 : Integrable (fun ω : ℕ → Obs d =>
      sparseArmContribution (fun i : Fin n => ω i) k 1 *
        sparseArmContribution (fun i : Fin n => ω i) k 0)
      (Measure.infinitePi (fun _ : ℕ => obsLaw P)) := by
    classical
    simp_rw [sparseArmContribution_eq_sum_sparseTerm, Finset.sum_mul_sum]
    exact integrable_finset_sum _ fun u _ =>
      integrable_finset_sum _ fun v _ => integrable_sparseTerm_mul P k 1 0 u v
  exact ((integrable_sparseArm_sq P k 1).add
    (integrable_sparseArm_sq P k 0)).sub (h10.const_mul 2)

/-- Diagonal second moment of one genuinely light polynomial cell. -/
lemma integral_factorialPolynomialContribution_sq_le {n d : ℕ}
    (P : DiscreteLaw d) (k : Fin d) (hn : 0 < splitSize n 1)
    (hsize : 4 * polynomialDegree n ^ 2 ≤ splitSize n 1)
    (hM : 0 < polynomialDegree n) (hB : 0 < bandwidth n)
    (hmass : cellMass P k +
      4 * (polynomialDegree n : ℝ) / splitSize n 1 ≤ bandwidth n) :
    ∫ ω : ℕ → Obs d,
        factorialPolynomialContribution (fun i : Fin n => ω i) k ^ 2
        ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P)) ≤
      4 * Real.exp 1 * (bandwidth n * 6 ^ polynomialDegree n) ^ 2 := by
  let X := fun ω : ℕ → Obs d =>
    sparseArmContribution (fun i : Fin n => ω i) k 1
  let Y := fun ω : ℕ → Obs d =>
    sparseArmContribution (fun i : Fin n => ω i) k 0
  have hpoint (ω : ℕ → Obs d) :
      factorialPolynomialContribution (fun i : Fin n => ω i) k ^ 2 ≤
        2 * X ω ^ 2 + 2 * Y ω ^ 2 := by
    rw [factorialPolynomialContribution_eq_sparseArms]
    dsimp only [X, Y]
    nlinarith [sq_nonneg
      (sparseArmContribution (fun i : Fin n => ω i) k 1 +
       sparseArmContribution (fun i : Fin n => ω i) k 0)]
  have hmono :
      ∫ ω : ℕ → Obs d,
          factorialPolynomialContribution (fun i : Fin n => ω i) k ^ 2
          ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P)) ≤
        ∫ ω : ℕ → Obs d, (2 * X ω ^ 2 + 2 * Y ω ^ 2)
          ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P)) := by
    apply integral_mono (integrable_factorialPolynomialContribution_sq P k)
    · exact ((integrable_sparseArm_sq P k 1).const_mul 2).add
        ((integrable_sparseArm_sq P k 0).const_mul 2)
    · exact hpoint
  refine hmono.trans ?_
  rw [integral_add, integral_const_mul, integral_const_mul]
  · have h1 := integral_sparseArm_sq_rate_le P k 1 hn hsize hM hB hmass
    have h0 := integral_sparseArm_sq_rate_le P k 0 hn hsize hM hB hmass
    nlinarith
  · exact (integrable_sparseArm_sq P k 1).const_mul 2
  · exact (integrable_sparseArm_sq P k 0).const_mul 2

/-- Defines sparse Term Mean, the stated quantity or construction used in the discrete average-treatment-effect estimator. -/
noncomputable def sparseTermMean {d : ℕ} (P : DiscreteLaw d)
    (k : Fin d) (M : ℕ) (B : ℝ) (a : Fin 2)
    (u : ℕ × ℕ × Cell) : ℝ :=
  sparseCoefficient M B u.1 u.2.1 *
    (factorialExpansionIndex a u.2.2 u.1 u.2.1).prod
      (fun cy e => (cellVector P k cy) ^ e)

/-- Defines sparse Arm Mean, the stated quantity or construction used in the discrete average-treatment-effect estimator. -/
noncomputable def sparseArmMean {d : ℕ} (P : DiscreteLaw d)
    (k : Fin d) (M : ℕ) (B : ℝ) (a : Fin 2) : ℝ :=
  ∑ u ∈ sparseIndexSet M, sparseTermMean P k M B a u

/-- Defines sparse Polynomial Mean, the stated quantity or construction used in the discrete average-treatment-effect estimator. -/
noncomputable def sparsePolynomialMean {d : ℕ} (P : DiscreteLaw d)
    (k : Fin d) (M : ℕ) (B : ℝ) : ℝ :=
  sparseArmMean P k M B 1 - sparseArmMean P k M B 0

/-- Shows that integrable factorial Monomial cross trunc is integrable under the stated sampling distribution. -/
lemma integrable_factorialMonomial_cross_trunc {n d : ℕ}
    (P : DiscreteLaw d) (k l : Fin d) (r s : MultiIndex) :
    Integrable (fun ω : ℕ → Obs d =>
      factorialMonomial (fun i : Fin n => ω i) k r *
        factorialMonomial (fun i : Fin n => ω i) l s)
      (Measure.infinitePi (fun _ : ℕ => obsLaw P)) := by
  letI : IsProbabilityMeasure (obsLaw P) := inferInstance
  simp_rw [factorialMonomial_trunc_eq_observationCount P]
  let S := iidSampleShift (Causalean.Stat.iidSample_infinitePi (obsLaw P)) (n / 2)
  have hraw : Integrable (fun ω : ℕ → Obs d =>
      multinomialFactorialCount (observationExponent k r)
          (fun j : Fin (splitSize n 1) => S.Z j ω) *
        multinomialFactorialCount (observationExponent l s)
          (fun j : Fin (splitSize n 1) => S.Z j ω))
      (Measure.infinitePi (fun _ : ℕ => obsLaw P)) := by
    simp_rw [multinomialFactorialCount_mul]
    apply integrable_finset_sum
    intro H _hH
    exact Integrable.const_mul
      (integrable_multinomialFactorialCount_sample S
        (mergedExponent (observationExponent k r) (observationExponent l s) H)
        (splitSize n 1)) _
  convert hraw.div_const
    (((splitSize n 1).descFactorial
        (exponentDegree (observationExponent k r)) : ℝ) *
      (splitSize n 1).descFactorial
        (exponentDegree (observationExponent l s))) using 1
  funext ω
  ring

/-- Shows that integrable sparse Term cross mul is integrable under the stated sampling distribution. -/
lemma integrable_sparseTerm_cross_mul {n d : ℕ} (P : DiscreteLaw d)
    (k l : Fin d) (a b : Fin 2) (u v : ℕ × ℕ × Cell) :
    Integrable (fun ω : ℕ → Obs d =>
      sparseTerm (fun i : Fin n => ω i) k a u *
        sparseTerm (fun i : Fin n => ω i) l b v)
      (Measure.infinitePi (fun _ : ℕ => obsLaw P)) := by
  have h := integrable_factorialMonomial_cross_trunc (n := n) P k l
    (factorialExpansionIndex a u.2.2 u.1 u.2.1)
    (factorialExpansionIndex b v.2.2 v.1 v.2.1)
  convert h.const_mul
    (sparseCoefficient (polynomialDegree n) (bandwidth n) u.1 u.2.1 *
      sparseCoefficient (polynomialDegree n) (bandwidth n) v.1 v.2.1) using 1
  funext ω
  simp only [sparseTerm]
  ring

/-- Evaluates or bounds the stated integral involving integral sparse Term eq mean. -/
lemma integral_sparseTerm_eq_mean {n d : ℕ} (P : DiscreteLaw d)
    (k : Fin d) (a : Fin 2) (u : ℕ × ℕ × Cell)
    (hu : u ∈ sparseIndexSet (polynomialDegree n))
    (hMle : polynomialDegree n ≤ splitSize n 1) :
    ∫ ω : ℕ → Obs d, sparseTerm (fun i : Fin n => ω i) k a u
        ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P)) =
      sparseTermMean P k (polynomialDegree n) (bandwidth n) a u := by
  unfold sparseTerm sparseTermMean
  rw [integral_const_mul, integral_factorialMonomial_trunc]
  have hd := sparseIndex_degree hu
  rw [multiDegree_factorialExpansionIndex _ _ _ _ (sparseIndex_inner_le hu)]
  exact hd.trans hMle

/-- Evaluates or bounds the stated integral involving integral sparse Arm Contribution eq mean. -/
lemma integral_sparseArmContribution_eq_mean {n d : ℕ}
    (P : DiscreteLaw d) (k : Fin d) (a : Fin 2)
    (hMle : polynomialDegree n ≤ splitSize n 1) :
    ∫ ω : ℕ → Obs d, sparseArmContribution (fun i : Fin n => ω i) k a
        ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P)) =
      sparseArmMean P k (polynomialDegree n) (bandwidth n) a := by
  classical
  simp_rw [sparseArmContribution_eq_sum_sparseTerm]
  rw [
    integral_finset_sum _ (fun u _hu =>
      integrable_sparseTerm P k a u)]
  unfold sparseArmMean
  apply Finset.sum_congr rfl
  intro u hu
  exact integral_sparseTerm_eq_mean P k a u hu hMle

/-- Evaluates or bounds the stated integral involving integral factorial Polynomial Contribution eq sparse Polynomial Mean. -/
lemma integral_factorialPolynomialContribution_eq_sparsePolynomialMean
    {n d : ℕ} (P : DiscreteLaw d) (k : Fin d)
    (hMle : polynomialDegree n ≤ splitSize n 1) :
    ∫ ω : ℕ → Obs d,
        factorialPolynomialContribution (fun i : Fin n => ω i) k
        ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P)) =
      sparsePolynomialMean P k (polynomialDegree n) (bandwidth n) := by
  rw [show (fun ω : ℕ → Obs d =>
      factorialPolynomialContribution (fun i : Fin n => ω i) k) =
      (fun ω => sparseArmContribution (fun i : Fin n => ω i) k 1 -
        sparseArmContribution (fun i : Fin n => ω i) k 0) by
    funext ω
    exact factorialPolynomialContribution_eq_sparseArms _ _]
  rw [integral_sub]
  · rw [integral_sparseArmContribution_eq_mean P k 1 hMle,
      integral_sparseArmContribution_eq_mean P k 0 hMle]
    rfl
  · exact integrable_sparseArm P k 1
  · exact integrable_sparseArm P k 0

/-- Establishes the stated property of sparse Term Mean abs in the discrete average-treatment-effect construction. -/
lemma sparseTermMean_abs {d : ℕ} (P : DiscreteLaw d) (k : Fin d)
    (M : ℕ) (B : ℝ) (a : Fin 2) (u : ℕ × ℕ × Cell) :
    |sparseTermMean P k M B a u| =
      |sparseCoefficient M B u.1 u.2.1| *
        (factorialExpansionIndex a u.2.2 u.1 u.2.1).prod
          (fun cy e => (cellVector P k cy) ^ e) := by
  unfold sparseTermMean
  rw [abs_mul, abs_of_nonneg (multiMonomial_nonneg _ _
    (fun cy => (cellVector_mem_unitCube P k cy).1))]

/-- Establishes the stated equality relating sum abs sparse Term Mean eq envelope. -/
lemma sum_abs_sparseTermMean_eq_envelope {d M : ℕ} {B : ℝ}
    (P : DiscreteLaw d) (k : Fin d) (a : Fin 2) :
    ∑ u ∈ sparseIndexSet M, |sparseTermMean P k M B a u| =
      sparseArmEnvelope M B (cellVector P k) a := by
  classical
  simp_rw [sparseTermMean_abs]
  unfold sparseArmEnvelope sparseCoefficient
  exact sum_sparseIndexSet (fun j t ay =>
    |B⁻¹ * gCoefficient M j * B⁻¹ ^ j * (Nat.choose j t : ℝ)| *
      (factorialExpansionIndex a ay j t).prod
        (fun cy e => cellVector P k cy ^ e))

/-- Establishes the stated upper bound for sparse Arm Mean abs le envelope. -/
lemma sparseArmMean_abs_le_envelope {d M : ℕ} {B : ℝ}
    (P : DiscreteLaw d) (k : Fin d) (a : Fin 2) :
    |sparseArmMean P k M B a| ≤ sparseArmEnvelope M B (cellVector P k) a := by
  unfold sparseArmMean
  calc
    |∑ u ∈ sparseIndexSet M, sparseTermMean P k M B a u| ≤
        ∑ u ∈ sparseIndexSet M, |sparseTermMean P k M B a u| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = _ := sum_abs_sparseTermMean_eq_envelope P k a

/-- Establishes the stated upper bound for sparse Term cross covariance le. -/
lemma sparseTerm_cross_covariance_le {n d : ℕ} (P : DiscreteLaw d)
    (k l : Fin d) (hkl : k ≠ l) (a b : Fin 2)
    (u v : ℕ × ℕ × Cell)
    (hu : u ∈ sparseIndexSet (polynomialDegree n))
    (hv : v ∈ sparseIndexSet (polynomialDegree n))
    (hsize : 4 * polynomialDegree n ^ 2 ≤ splitSize n 1) :
    |∫ ω : ℕ → Obs d,
        sparseTerm (fun i : Fin n => ω i) k a u *
          sparseTerm (fun i : Fin n => ω i) l b v
        ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P)) -
      sparseTermMean P k (polynomialDegree n) (bandwidth n) a u *
        sparseTermMean P l (polynomialDegree n) (bandwidth n) b v| ≤
      (2 * (polynomialDegree n : ℝ) ^ 2 / splitSize n 1) *
        |sparseTermMean P k (polynomialDegree n) (bandwidth n) a u| *
        |sparseTermMean P l (polynomialDegree n) (bandwidth n) b v| := by
  let r := factorialExpansionIndex a u.2.2 u.1 u.2.1
  let s := factorialExpansionIndex b v.2.2 v.1 v.2.1
  let c := sparseCoefficient (polynomialDegree n) (bandwidth n) u.1 u.2.1
  let e := sparseCoefficient (polynomialDegree n) (bandwidth n) v.1 v.2.1
  let x := r.prod fun cy q => (cellVector P k cy) ^ q
  let y := s.prod fun cy q => (cellVector P l cy) ^ q
  have hr : multiDegree r ≤ polynomialDegree n := by
    dsimp only [r]
    rw [multiDegree_factorialExpansionIndex _ _ _ _ (sparseIndex_inner_le hu)]
    exact sparseIndex_degree hu
  have hs : multiDegree s ≤ polynomialDegree n := by
    dsimp only [s]
    rw [multiDegree_factorialExpansionIndex _ _ _ _ (sparseIndex_inner_le hv)]
    exact sparseIndex_degree hv
  have hcov := factorialMonomial_cross_covariance_le P k l hkl r s hr hs hsize
  have hx0 : 0 ≤ x := multiMonomial_nonneg r _
    (fun cy => (cellVector_mem_unitCube P k cy).1)
  have hy0 : 0 ≤ y := multiMonomial_nonneg s _
    (fun cy => (cellVector_mem_unitCube P l cy).1)
  rw [show (fun ω : ℕ → Obs d =>
      sparseTerm (fun i : Fin n => ω i) k a u *
        sparseTerm (fun i : Fin n => ω i) l b v) =
      (fun ω => c * e *
        (factorialMonomial (fun i : Fin n => ω i) k r *
          factorialMonomial (fun i : Fin n => ω i) l s)) by
    funext ω
    simp only [sparseTerm, c, e, r, s]
    ring,
    integral_const_mul]
  change |c * e *
      (∫ ω : ℕ → Obs d,
        factorialMonomial (fun i : Fin n => ω i) k r *
          factorialMonomial (fun i : Fin n => ω i) l s
        ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P))) -
      (c * x) * (e * y)| ≤ _
  rw [show c * e *
      (∫ ω : ℕ → Obs d,
        factorialMonomial (fun i : Fin n => ω i) k r *
          factorialMonomial (fun i : Fin n => ω i) l s
        ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P))) -
      (c * x) * (e * y) =
      c * e * ((∫ ω : ℕ → Obs d,
        factorialMonomial (fun i : Fin n => ω i) k r *
          factorialMonomial (fun i : Fin n => ω i) l s
        ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P))) - x * y) by ring,
    abs_mul]
  dsimp only [sparseTermMean]
  change |c * e| * |(∫ ω : ℕ → Obs d,
      factorialMonomial (fun i : Fin n => ω i) k r *
        factorialMonomial (fun i : Fin n => ω i) l s
      ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P))) - x * y| ≤
    (2 * (polynomialDegree n : ℝ) ^ 2 / splitSize n 1) *
      |c * x| * |e * y|
  rw [abs_mul c e, abs_mul c x, abs_mul e y,
    abs_of_nonneg hx0, abs_of_nonneg hy0]
  calc
    |c| * |e| * |(∫ ω : ℕ → Obs d,
        factorialMonomial (fun i : Fin n => ω i) k r *
          factorialMonomial (fun i : Fin n => ω i) l s
        ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P))) - x * y| ≤
      |c| * |e| *
        ((2 * (polynomialDegree n : ℝ) ^ 2 / splitSize n 1) * x * y) := by
      gcongr
    _ = _ := by ring

set_option maxHeartbeats 1000000 in
/-- Establishes the stated upper bound for sparse Arm cross covariance le. -/
lemma sparseArm_cross_covariance_le {n d : ℕ} (P : DiscreteLaw d)
    (k l : Fin d) (hkl : k ≠ l) (a b : Fin 2)
    (hsize : 4 * polynomialDegree n ^ 2 ≤ splitSize n 1) :
    |∫ ω : ℕ → Obs d,
        sparseArmContribution (fun i : Fin n => ω i) k a *
          sparseArmContribution (fun i : Fin n => ω i) l b
        ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P)) -
      sparseArmMean P k (polynomialDegree n) (bandwidth n) a *
        sparseArmMean P l (polynomialDegree n) (bandwidth n) b| ≤
      (2 * (polynomialDegree n : ℝ) ^ 2 / splitSize n 1) *
        sparseArmEnvelope (polynomialDegree n) (bandwidth n)
          (cellVector P k) a *
        sparseArmEnvelope (polynomialDegree n) (bandwidth n)
          (cellVector P l) b := by
  classical
  let S := sparseIndexSet (polynomialDegree n)
  simp_rw [sparseArmContribution_eq_sum_sparseTerm]
  simp_rw [Finset.sum_mul_sum]
  rw [integral_finset_sum S (fun u _ =>
    integrable_finset_sum S (fun v _ => integrable_sparseTerm_cross_mul P k l a b u v))]
  simp_rw [integral_finset_sum S (fun v _ =>
    integrable_sparseTerm_cross_mul P k l a b _ v)]
  unfold sparseArmMean
  rw [Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
  let C := fun u v : ℕ × ℕ × Cell =>
    ∫ ω : ℕ → Obs d,
      sparseTerm (fun i : Fin n => ω i) k a u *
        sparseTerm (fun i : Fin n => ω i) l b v
      ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P))
  let U := fun u : ℕ × ℕ × Cell =>
    sparseTermMean P k (polynomialDegree n) (bandwidth n) a u
  let V := fun v : ℕ × ℕ × Cell =>
    sparseTermMean P l (polynomialDegree n) (bandwidth n) b v
  let q := 2 * (polynomialDegree n : ℝ) ^ 2 / splitSize n 1
  change |∑ u ∈ S, ((∑ v ∈ S, C u v) -
      ∑ v ∈ S, U u * V v)| ≤
    q * sparseArmEnvelope (polynomialDegree n) (bandwidth n) (cellVector P k) a *
      sparseArmEnvelope (polynomialDegree n) (bandwidth n) (cellVector P l) b
  simp_rw [← Finset.sum_sub_distrib]
  change |∑ u ∈ S, ∑ v ∈ S, (C u v - U u * V v)| ≤
    q * sparseArmEnvelope (polynomialDegree n) (bandwidth n) (cellVector P k) a *
      sparseArmEnvelope (polynomialDegree n) (bandwidth n) (cellVector P l) b
  calc
    |∑ u ∈ S, ∑ v ∈ S, (C u v - U u * V v)| ≤
      ∑ u ∈ S, ∑ v ∈ S, |C u v - U u * V v| := by
      exact Finset.abs_sum_le_sum_abs _ _ |>.trans
        (Finset.sum_le_sum fun u _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ u ∈ S, ∑ v ∈ S, q * |U u| * |V v| := by
      apply Finset.sum_le_sum
      intro u hu
      apply Finset.sum_le_sum
      intro v hv
      simpa only [C, U, V, q] using
        sparseTerm_cross_covariance_le P k l hkl a b u v hu hv hsize
    _ = _ := by
      have hU : (∑ u ∈ S, |U u|) =
          sparseArmEnvelope (polynomialDegree n) (bandwidth n) (cellVector P k) a :=
        sum_abs_sparseTermMean_eq_envelope P k a
      have hV : (∑ v ∈ S, |V v|) =
          sparseArmEnvelope (polynomialDegree n) (bandwidth n) (cellVector P l) b :=
        sum_abs_sparseTermMean_eq_envelope P l b
      calc
        (∑ u ∈ S, ∑ v ∈ S, q * |U u| * |V v|) =
            ∑ u ∈ S, q * |U u| * (∑ v ∈ S, |V v|) := by
          apply Finset.sum_congr rfl
          intro u hu
          exact (Finset.mul_sum (s := S) (f := fun v => |V v|)
            (q * |U u|)).symm
        _ = (∑ u ∈ S, q * |U u|) * (∑ v ∈ S, |V v|) := by
          exact (Finset.sum_mul (s := S) (f := fun u => q * |U u|)
            (∑ v ∈ S, |V v|)).symm
        _ = q * (∑ u ∈ S, |U u|) * (∑ v ∈ S, |V v|) := by
          congr 1
          exact (Finset.mul_sum (s := S) (f := fun u => |U u|) q).symm
        _ = _ := by rw [hU, hV]

/-- Shows that integrable sparse Arm cross mul is integrable under the stated sampling distribution. -/
lemma integrable_sparseArm_cross_mul {n d : ℕ} (P : DiscreteLaw d)
    (k l : Fin d) (a b : Fin 2) :
    Integrable (fun ω : ℕ → Obs d =>
      sparseArmContribution (fun i : Fin n => ω i) k a *
        sparseArmContribution (fun i : Fin n => ω i) l b)
      (Measure.infinitePi (fun _ : ℕ => obsLaw P)) := by
  classical
  simp_rw [sparseArmContribution_eq_sum_sparseTerm, Finset.sum_mul_sum]
  exact integrable_finset_sum _ fun u _ =>
    integrable_finset_sum _ fun v _ =>
      integrable_sparseTerm_cross_mul P k l a b u v

/-- Establishes the stated property of factorial Polynomial cross covariance decompose in the discrete average-treatment-effect construction. -/
lemma factorialPolynomial_cross_covariance_decompose {n d : ℕ}
    (P : DiscreteLaw d) (k l : Fin d) :
    (∫ ω : ℕ → Obs d,
        factorialPolynomialContribution (fun i : Fin n => ω i) k *
          factorialPolynomialContribution (fun i : Fin n => ω i) l
        ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P))) -
      sparsePolynomialMean P k (polynomialDegree n) (bandwidth n) *
        sparsePolynomialMean P l (polynomialDegree n) (bandwidth n) =
      ((∫ ω : ℕ → Obs d,
          sparseArmContribution (fun i : Fin n => ω i) k 1 *
            sparseArmContribution (fun i : Fin n => ω i) l 1
            ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P))) -
        sparseArmMean P k (polynomialDegree n) (bandwidth n) 1 *
          sparseArmMean P l (polynomialDegree n) (bandwidth n) 1) -
      ((∫ ω : ℕ → Obs d,
          sparseArmContribution (fun i : Fin n => ω i) k 1 *
            sparseArmContribution (fun i : Fin n => ω i) l 0
            ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P))) -
        sparseArmMean P k (polynomialDegree n) (bandwidth n) 1 *
          sparseArmMean P l (polynomialDegree n) (bandwidth n) 0) -
      ((∫ ω : ℕ → Obs d,
          sparseArmContribution (fun i : Fin n => ω i) k 0 *
            sparseArmContribution (fun i : Fin n => ω i) l 1
            ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P))) -
        sparseArmMean P k (polynomialDegree n) (bandwidth n) 0 *
          sparseArmMean P l (polynomialDegree n) (bandwidth n) 1) +
      ((∫ ω : ℕ → Obs d,
          sparseArmContribution (fun i : Fin n => ω i) k 0 *
            sparseArmContribution (fun i : Fin n => ω i) l 0
            ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P))) -
        sparseArmMean P k (polynomialDegree n) (bandwidth n) 0 *
          sparseArmMean P l (polynomialDegree n) (bandwidth n) 0) := by
  simp_rw [factorialPolynomialContribution_eq_sparseArms]
  rw [show (fun ω : ℕ → Obs d =>
      (sparseArmContribution (fun i : Fin n => ω i) k 1 -
        sparseArmContribution (fun i : Fin n => ω i) k 0) *
      (sparseArmContribution (fun i : Fin n => ω i) l 1 -
        sparseArmContribution (fun i : Fin n => ω i) l 0)) =
      (fun ω =>
        sparseArmContribution (fun i : Fin n => ω i) k 1 *
          sparseArmContribution (fun i : Fin n => ω i) l 1 -
        sparseArmContribution (fun i : Fin n => ω i) k 1 *
          sparseArmContribution (fun i : Fin n => ω i) l 0 -
        sparseArmContribution (fun i : Fin n => ω i) k 0 *
          sparseArmContribution (fun i : Fin n => ω i) l 1 +
        sparseArmContribution (fun i : Fin n => ω i) k 0 *
          sparseArmContribution (fun i : Fin n => ω i) l 0) by
    funext ω
    ring]
  have h11 := integrable_sparseArm_cross_mul (n := n) P k l 1 1
  have h10 := integrable_sparseArm_cross_mul (n := n) P k l 1 0
  have h01 := integrable_sparseArm_cross_mul (n := n) P k l 0 1
  have h00 := integrable_sparseArm_cross_mul (n := n) P k l 0 0
  have hi :
      (∫ ω : ℕ → Obs d,
          sparseArmContribution (fun i : Fin n => ω i) k 1 *
              sparseArmContribution (fun i : Fin n => ω i) l 1 -
            sparseArmContribution (fun i : Fin n => ω i) k 1 *
              sparseArmContribution (fun i : Fin n => ω i) l 0 -
            sparseArmContribution (fun i : Fin n => ω i) k 0 *
              sparseArmContribution (fun i : Fin n => ω i) l 1 +
            sparseArmContribution (fun i : Fin n => ω i) k 0 *
              sparseArmContribution (fun i : Fin n => ω i) l 0
          ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P))) =
        (∫ ω, sparseArmContribution (fun i : Fin n => ω i) k 1 *
            sparseArmContribution (fun i : Fin n => ω i) l 1
            ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P))) -
        (∫ ω, sparseArmContribution (fun i : Fin n => ω i) k 1 *
            sparseArmContribution (fun i : Fin n => ω i) l 0
            ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P))) -
        (∫ ω, sparseArmContribution (fun i : Fin n => ω i) k 0 *
            sparseArmContribution (fun i : Fin n => ω i) l 1
            ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P))) +
        (∫ ω, sparseArmContribution (fun i : Fin n => ω i) k 0 *
            sparseArmContribution (fun i : Fin n => ω i) l 0
            ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P))) := by
    calc
      _ = (∫ ω, sparseArmContribution (fun i : Fin n => ω i) k 1 *
              sparseArmContribution (fun i : Fin n => ω i) l 1 -
            sparseArmContribution (fun i : Fin n => ω i) k 1 *
              sparseArmContribution (fun i : Fin n => ω i) l 0 -
            sparseArmContribution (fun i : Fin n => ω i) k 0 *
              sparseArmContribution (fun i : Fin n => ω i) l 1
              ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P))) +
          (∫ ω, sparseArmContribution (fun i : Fin n => ω i) k 0 *
              sparseArmContribution (fun i : Fin n => ω i) l 0
              ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P))) :=
        by simpa only [Pi.add_apply, Pi.sub_apply] using
          integral_add ((h11.sub h10).sub h01) h00
      _ = _ := by
        congr 1
        calc
          (∫ ω, sparseArmContribution (fun i : Fin n => ω i) k 1 *
                  sparseArmContribution (fun i : Fin n => ω i) l 1 -
                sparseArmContribution (fun i : Fin n => ω i) k 1 *
                  sparseArmContribution (fun i : Fin n => ω i) l 0 -
                sparseArmContribution (fun i : Fin n => ω i) k 0 *
                  sparseArmContribution (fun i : Fin n => ω i) l 1
              ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P))) =
              (∫ ω, sparseArmContribution (fun i : Fin n => ω i) k 1 *
                    sparseArmContribution (fun i : Fin n => ω i) l 1 -
                  sparseArmContribution (fun i : Fin n => ω i) k 1 *
                    sparseArmContribution (fun i : Fin n => ω i) l 0
                ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P))) -
              (∫ ω, sparseArmContribution (fun i : Fin n => ω i) k 0 *
                  sparseArmContribution (fun i : Fin n => ω i) l 1
                ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P))) := by
            simpa only [Pi.sub_apply] using integral_sub (h11.sub h10) h01
          _ = _ := by
            rw [show
              (∫ ω, sparseArmContribution (fun i : Fin n => ω i) k 1 *
                    sparseArmContribution (fun i : Fin n => ω i) l 1 -
                  sparseArmContribution (fun i : Fin n => ω i) k 1 *
                    sparseArmContribution (fun i : Fin n => ω i) l 0
                ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P))) =
                (∫ ω, sparseArmContribution (fun i : Fin n => ω i) k 1 *
                    sparseArmContribution (fun i : Fin n => ω i) l 1
                  ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P))) -
                (∫ ω, sparseArmContribution (fun i : Fin n => ω i) k 1 *
                    sparseArmContribution (fun i : Fin n => ω i) l 0
                  ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P))) by
              simpa only [Pi.sub_apply] using integral_sub h11 h10]
  rw [hi]
  unfold sparsePolynomialMean
  ring

/-- Equation (16): covariance between distinct light categories, with all
normalization constants explicit. -/
lemma factorialPolynomial_cross_covariance_le {n d : ℕ}
    (P : DiscreteLaw d) (k l : Fin d) (hkl : k ≠ l)
    (hM : 0 < polynomialDegree n) (hB : 0 < bandwidth n)
    (hsize : 4 * polynomialDegree n ^ 2 ≤ splitSize n 1)
    (hk : cellMass P k ≤ bandwidth n)
    (hl : cellMass P l ≤ bandwidth n) :
    |(∫ ω : ℕ → Obs d,
        factorialPolynomialContribution (fun i : Fin n => ω i) k *
          factorialPolynomialContribution (fun i : Fin n => ω i) l
        ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P))) -
      sparsePolynomialMean P k (polynomialDegree n) (bandwidth n) *
        sparsePolynomialMean P l (polynomialDegree n) (bandwidth n)| ≤
      8 * (polynomialDegree n : ℝ) ^ 2 / splitSize n 1 *
        (bandwidth n * 6 ^ polynomialDegree n) ^ 2 := by
  let q := 2 * (polynomialDegree n : ℝ) ^ 2 / splitSize n 1
  let R := bandwidth n * 6 ^ polynomialDegree n
  have henvk (a : Fin 2) :
      sparseArmEnvelope (polynomialDegree n) (bandwidth n)
          (cellVector P k) a ≤ R := by
    exact sparseArmEnvelope_le hM hB _
      (fun cy => (cellVector_mem_unitCube P k cy).1)
      (by
        have hm := vectorMass_cellVector P k
        simp [vectorMass, vectorArmMass] at hm
        have hsum : (∑ ay : Cell, cellVector P k ay) = cellMass P k := by
          simpa [Fintype.sum_prod_type, Fin.sum_univ_two] using hm
        rw [hsum]
        exact hk) a
  have henvl (a : Fin 2) :
      sparseArmEnvelope (polynomialDegree n) (bandwidth n)
          (cellVector P l) a ≤ R := by
    exact sparseArmEnvelope_le hM hB _
      (fun cy => (cellVector_mem_unitCube P l cy).1)
      (by
        have hm := vectorMass_cellVector P l
        simp [vectorMass, vectorArmMass] at hm
        have hsum : (∑ ay : Cell, cellVector P l ay) = cellMass P l := by
          simpa [Fintype.sum_prod_type, Fin.sum_univ_two] using hm
        rw [hsum]
        exact hl) a
  have hq0 : 0 ≤ q := by unfold q; positivity
  have hR0 : 0 ≤ R := by unfold R; positivity
  have hc (a b : Fin 2) :
      |(∫ ω : ℕ → Obs d,
          sparseArmContribution (fun i : Fin n => ω i) k a *
            sparseArmContribution (fun i : Fin n => ω i) l b
            ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P))) -
        sparseArmMean P k (polynomialDegree n) (bandwidth n) a *
          sparseArmMean P l (polynomialDegree n) (bandwidth n) b| ≤ q * R ^ 2 := by
    refine (sparseArm_cross_covariance_le P k l hkl a b hsize).trans ?_
    change q * _ * _ ≤ q * R ^ 2
    rw [pow_two]
    have hek0 : 0 ≤ sparseArmEnvelope (polynomialDegree n) (bandwidth n)
        (cellVector P k) a := sparseArmEnvelope_nonneg _
          (fun cy => (cellVector_mem_unitCube P k cy).1) a
    have hel0 : 0 ≤ sparseArmEnvelope (polynomialDegree n) (bandwidth n)
        (cellVector P l) b := sparseArmEnvelope_nonneg _
          (fun cy => (cellVector_mem_unitCube P l cy).1) b
    calc
      q * _ * _ ≤ q * R * sparseArmEnvelope (polynomialDegree n)
          (bandwidth n) (cellVector P l) b := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (henvk a) hq0) hel0
      _ ≤ q * R * R := by
        exact mul_le_mul_of_nonneg_left (henvl b) (mul_nonneg hq0 hR0)
      _ = q * (R * R) := by ring
  rw [factorialPolynomial_cross_covariance_decompose P k l]
  have four_abs (x y z w : ℝ) :
      |x - y - z + w| ≤ |x| + |y| + |z| + |w| := by
    calc
      |x - y - z + w| ≤ |x - y - z| + |w| := abs_add_le _ _
      _ ≤ (|x - y| + |z|) + |w| := by gcongr; exact abs_sub _ _
      _ ≤ (|x| + |y| + |z|) + |w| := by gcongr; exact abs_sub _ _
      _ = _ := by ring
  calc
    |_ - _ - _ + _| ≤ |_| + |_| + |_| + |_| := four_abs _ _ _ _
    _ ≤ 4 * (q * R ^ 2) := by
      have h11 := hc 1 1
      have h10 := hc 1 0
      have h01 := hc 0 1
      have h00 := hc 0 0
      linarith
    _ = _ := by unfold q R; ring

/-- Shows that integrable factorial Polynomial cross mul is integrable under the stated sampling distribution. -/
lemma integrable_factorialPolynomial_cross_mul {n d : ℕ}
    (P : DiscreteLaw d) (k l : Fin d) :
    Integrable (fun ω : ℕ → Obs d =>
      factorialPolynomialContribution (fun i : Fin n => ω i) k *
        factorialPolynomialContribution (fun i : Fin n => ω i) l)
      (Measure.infinitePi (fun _ : ℕ => obsLaw P)) := by
  simp_rw [factorialPolynomialContribution_eq_sparseArms]
  rw [show (fun ω : ℕ → Obs d =>
      (sparseArmContribution (fun i : Fin n => ω i) k 1 -
        sparseArmContribution (fun i : Fin n => ω i) k 0) *
      (sparseArmContribution (fun i : Fin n => ω i) l 1 -
        sparseArmContribution (fun i : Fin n => ω i) l 0)) =
      (fun ω =>
        sparseArmContribution (fun i : Fin n => ω i) k 1 *
          sparseArmContribution (fun i : Fin n => ω i) l 1 -
        sparseArmContribution (fun i : Fin n => ω i) k 1 *
          sparseArmContribution (fun i : Fin n => ω i) l 0 -
        sparseArmContribution (fun i : Fin n => ω i) k 0 *
          sparseArmContribution (fun i : Fin n => ω i) l 1 +
        sparseArmContribution (fun i : Fin n => ω i) k 0 *
          sparseArmContribution (fun i : Fin n => ω i) l 0) by
    funext ω
    ring]
  exact (((integrable_sparseArm_cross_mul P k l 1 1).sub
    (integrable_sparseArm_cross_mul P k l 1 0)).sub
    (integrable_sparseArm_cross_mul P k l 0 1)).add
    (integrable_sparseArm_cross_mul P k l 0 0)

/-- The off-diagonal centered covariance estimate, packaged separately so that
the pilot-selection layer need not normalize a large factorial expression. -/
lemma integral_factorialPolynomial_centered_cross_le {n d : ℕ}
    (P : DiscreteLaw d) (k l : Fin d) (hkl : k ≠ l)
    (hM : 0 < polynomialDegree n) (hB : 0 < bandwidth n)
    (hsize : 4 * polynomialDegree n ^ 2 ≤ splitSize n 1)
    (hk : cellMass P k ≤ bandwidth n)
    (hl : cellMass P l ≤ bandwidth n) :
    ∫ ω : ℕ → Obs d,
        (factorialPolynomialContribution (fun i : Fin n => ω i) k -
          sparsePolynomialMean P k (polynomialDegree n) (bandwidth n)) *
        (factorialPolynomialContribution (fun i : Fin n => ω i) l -
          sparsePolynomialMean P l (polynomialDegree n) (bandwidth n))
        ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P)) ≤
      8 * (polynomialDegree n : ℝ) ^ 2 / splitSize n 1 *
        (bandwidth n * 6 ^ polynomialDegree n) ^ 2 := by
  have hMle : polynomialDegree n ≤ splitSize n 1 := by
    nlinarith [Nat.mul_self_le_mul_self
      (show 1 ≤ polynomialDegree n by omega)]
  let μ := Measure.infinitePi (fun _ : ℕ => obsLaw P)
  let f := fun ω : ℕ → Obs d =>
    factorialPolynomialContribution (fun i : Fin n => ω i) k
  let g := fun ω : ℕ → Obs d =>
    factorialPolynomialContribution (fun i : Fin n => ω i) l
  let mk := sparsePolynomialMean P k (polynomialDegree n) (bandwidth n)
  let ml := sparsePolynomialMean P l (polynomialDegree n) (bandwidth n)
  have hf : Integrable f μ :=
    integrable_factorialPolynomialContribution_trunc_rate P k
  have hg : Integrable g μ :=
    integrable_factorialPolynomialContribution_trunc_rate P l
  have hfg : Integrable (fun ω => f ω * g ω) μ :=
    integrable_factorialPolynomial_cross_mul P k l
  have hcenter : (∫ ω, (f ω - mk) * (g ω - ml) ∂μ) =
      (∫ ω, f ω * g ω ∂μ) - mk * ml := by
    rw [show (fun ω => (f ω - mk) * (g ω - ml)) =
        (fun ω => f ω * g ω - ml * f ω - mk * g ω + mk * ml) by
      funext ω
      ring]
    calc
      (∫ ω, f ω * g ω - ml * f ω - mk * g ω + mk * ml ∂μ) =
        (∫ ω, f ω * g ω - ml * f ω - mk * g ω ∂μ) +
          ∫ _ω, mk * ml ∂μ := by
        simpa only [Pi.add_apply, Pi.sub_apply] using
          integral_add ((hfg.sub (hf.const_mul ml)).sub (hg.const_mul mk))
            (integrable_const (mk * ml))
      _ = ((∫ ω, f ω * g ω - ml * f ω ∂μ) -
          ∫ ω, mk * g ω ∂μ) + ∫ _ω, mk * ml ∂μ := by
        rw [show (∫ ω, f ω * g ω - ml * f ω - mk * g ω ∂μ) =
          (∫ ω, f ω * g ω - ml * f ω ∂μ) -
            ∫ ω, mk * g ω ∂μ by
          simpa only [Pi.sub_apply] using
            integral_sub (hfg.sub (hf.const_mul ml)) (hg.const_mul mk)]
      _ = (((∫ ω, f ω * g ω ∂μ) - ∫ ω, ml * f ω ∂μ) -
          ∫ ω, mk * g ω ∂μ) + ∫ _ω, mk * ml ∂μ := by
        rw [show (∫ ω, f ω * g ω - ml * f ω ∂μ) =
          (∫ ω, f ω * g ω ∂μ) - ∫ ω, ml * f ω ∂μ by
          simpa only [Pi.sub_apply] using integral_sub hfg (hf.const_mul ml)]
      _ = (∫ ω, f ω * g ω ∂μ) - mk * ml := by
        rw [integral_const_mul, integral_const_mul]
        simp only [integral_const, measureReal_univ_eq_one, one_smul]
        rw [show (∫ ω, f ω ∂μ) = mk by
          simpa only [f, μ, mk] using
            integral_factorialPolynomialContribution_eq_sparsePolynomialMean P k hMle,
          show (∫ ω, g ω ∂μ) = ml by
          simpa only [g, μ, ml] using
            integral_factorialPolynomialContribution_eq_sparsePolynomialMean P l hMle]
        ring
  rw [hcenter]
  simpa only [f, g, mk, ml, μ] using
    (le_abs_self ((∫ ω : ℕ → Obs d,
      factorialPolynomialContribution (fun i : Fin n => ω i) k *
        factorialPolynomialContribution (fun i : Fin n => ω i) l
        ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P))) -
      sparsePolynomialMean P k (polynomialDegree n) (bandwidth n) *
        sparsePolynomialMean P l (polynomialDegree n) (bandwidth n))).trans
      (factorialPolynomial_cross_covariance_le P k l hkl hM hB hsize hk hl)

/-- Establishes the stated upper bound for sparse Polynomial Mean abs le. -/
lemma sparsePolynomialMean_abs_le {n d : ℕ} (P : DiscreteLaw d)
    (k : Fin d) (hM : 0 < polynomialDegree n) (hB : 0 < bandwidth n)
    (hk : cellMass P k ≤ bandwidth n) :
    |sparsePolynomialMean P k (polynomialDegree n) (bandwidth n)| ≤
      2 * (bandwidth n * 6 ^ polynomialDegree n) := by
  unfold sparsePolynomialMean
  refine (abs_sub _ _).trans ?_
  have h1 := sparseArmMean_abs_le_envelope
    (M := polynomialDegree n) (B := bandwidth n) P k 1
  have h0 := sparseArmMean_abs_le_envelope
    (M := polynomialDegree n) (B := bandwidth n) P k 0
  have he (a : Fin 2) :
      sparseArmEnvelope (polynomialDegree n) (bandwidth n)
          (cellVector P k) a ≤ bandwidth n * 6 ^ polynomialDegree n :=
    sparseArmEnvelope_le hM hB _
      (fun cy => (cellVector_mem_unitCube P k cy).1)
      (by
        have hm := vectorMass_cellVector P k
        simp [vectorMass, vectorArmMass] at hm
        have hsum : (∑ ay : Cell, cellVector P k ay) = cellMass P k := by
          simpa [Fintype.sum_prod_type, Fin.sum_univ_two] using hm
        rw [hsum]
        exact hk) a
  linarith [he 1, he 0]

/-- Evaluates or bounds the stated integral involving integral factorial Polynomial centered sq le. -/
lemma integral_factorialPolynomial_centered_sq_le {n d : ℕ}
    (P : DiscreteLaw d) (k : Fin d) (hn : 0 < splitSize n 1)
    (hM : 0 < polynomialDegree n) (hB : 0 < bandwidth n)
    (hsize : 4 * polynomialDegree n ^ 2 ≤ splitSize n 1)
    (hmassShift : cellMass P k +
      4 * (polynomialDegree n : ℝ) / splitSize n 1 ≤ bandwidth n)
    (hmass : cellMass P k ≤ bandwidth n) :
    ∫ ω : ℕ → Obs d,
        (factorialPolynomialContribution (fun i : Fin n => ω i) k -
          sparsePolynomialMean P k (polynomialDegree n) (bandwidth n)) ^ 2
        ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P)) ≤
      8 * (Real.exp 1 + 1) *
        (bandwidth n * 6 ^ polynomialDegree n) ^ 2 := by
  let X := fun ω : ℕ → Obs d =>
    factorialPolynomialContribution (fun i : Fin n => ω i) k
  let m := sparsePolynomialMean P k (polynomialDegree n) (bandwidth n)
  let R := bandwidth n * 6 ^ polynomialDegree n
  have hmabs : |m| ≤ 2 * R :=
    sparsePolynomialMean_abs_le P k hM hB hmass
  have hm2 : m ^ 2 ≤ 4 * R ^ 2 := by
    rw [← sq_abs]
    nlinarith [sq_nonneg (|m| - 2 * R), abs_nonneg m]
  have hpoint (ω : ℕ → Obs d) :
      (X ω - m) ^ 2 ≤ 2 * X ω ^ 2 + 2 * m ^ 2 := by
    nlinarith [sq_nonneg (X ω + m)]
  have hint :
      ∫ ω, (X ω - m) ^ 2 ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P)) ≤
        ∫ ω, (2 * X ω ^ 2 + 2 * m ^ 2)
          ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P)) := by
    apply integral_mono
    · have hi : Integrable (fun ω : ℕ → Obs d =>
          factorialPolynomialContribution (fun i : Fin n => ω i) k ^ 2 -
            ((2 * m) * factorialPolynomialContribution (fun i : Fin n => ω i) k -
              m ^ 2)) (Measure.infinitePi (fun _ : ℕ => obsLaw P)) :=
        (integrable_factorialPolynomialContribution_sq (n := n) P k).sub
        (((integrable_factorialPolynomialContribution_trunc_rate P k).const_mul
          (2 * m)).sub (integrable_const (m ^ 2)))
      convert hi using 1
      funext ω
      dsimp only [X]
      ring
    · exact ((integrable_factorialPolynomialContribution_sq P k).const_mul 2).add
        (integrable_const (2 * m ^ 2))
    · exact hpoint
  refine hint.trans ?_
  rw [integral_add, integral_const_mul, integral_const]
  simp only [measureReal_univ_eq_one, one_smul]
  · have hX := integral_factorialPolynomialContribution_sq_le
      P k hn hsize hM hB hmassShift
    change 2 * (∫ ω, X ω ^ 2 ∂_) + 2 * m ^ 2 ≤ _
    nlinarith [Real.exp_pos 1]
  · exact (integrable_factorialPolynomialContribution_sq P k).const_mul 2
  · exact integrable_const _

/- The deterministic-set variant is not used by the final random-selection
argument; the latter is proved directly below.  Keeping this derivation out of
the compiled surface avoids duplicating the expensive double-sum proof.

noncomputable def fixedLightCentered {n d : ℕ} (P : DiscreteLaw d)
    (sample : Fin n → Obs d) (S : Finset (Fin d)) : ℝ :=
  ∑ k ∈ S, (factorialPolynomialContribution sample k -
    sparsePolynomialMean P k (polynomialDegree n) (bandwidth n))

/- Equation (17), before the elementary rate algebra: a deterministic set
of genuinely light categories has the sharp diagonal-plus-cross variance. -/
set_option maxHeartbeats 2000000 in
lemma fixedLightCentered_second_moment_le {n d : ℕ}
    (P : DiscreteLaw d) (S : Finset (Fin d))
    (hn : 0 < splitSize n 1) (hM : 0 < polynomialDegree n)
    (hB : 0 < bandwidth n)
    (hsize : 4 * polynomialDegree n ^ 2 ≤ splitSize n 1)
    (hlight : ∀ k ∈ S,
      cellMass P k + 4 * (polynomialDegree n : ℝ) / splitSize n 1 ≤
        bandwidth n) :
    ∫ ω : ℕ → Obs d,
        fixedLightCentered P (fun i : Fin n => ω i) S ^ 2
        ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P)) ≤
      (S.card : ℝ) * (8 * (Real.exp 1 + 1)) *
          (bandwidth n * 6 ^ polynomialDegree n) ^ 2 +
        (S.card : ℝ) ^ 2 *
          (8 * (polynomialDegree n : ℝ) ^ 2 / splitSize n 1) *
          (bandwidth n * 6 ^ polynomialDegree n) ^ 2 := by
  classical
  let X := fun k : Fin d => fun ω : ℕ → Obs d =>
    factorialPolynomialContribution (fun i : Fin n => ω i) k -
      sparsePolynomialMean P k (polynomialDegree n) (bandwidth n)
  let D := 8 * (Real.exp 1 + 1) *
    (bandwidth n * 6 ^ polynomialDegree n) ^ 2
  let Q := 8 * (polynomialDegree n : ℝ) ^ 2 / splitSize n 1 *
    (bandwidth n * 6 ^ polynomialDegree n) ^ 2
  have hmass (k : Fin d) (hk : k ∈ S) : cellMass P k ≤ bandwidth n :=
    (le_add_of_nonneg_right (by positivity :
      0 ≤ 4 * (polynomialDegree n : ℝ) / splitSize n 1)).trans (hlight k hk)
  have hpair (k : Fin d) (hk : k ∈ S) (l : Fin d) (hl : l ∈ S) :
      ∫ ω : ℕ → Obs d, X k ω * X l ω
          ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P)) ≤
        (if k = l then D else 0) + Q := by
    by_cases hkl : k = l
    · subst l
      rw [if_pos rfl]
      have hd := integral_factorialPolynomial_centered_sq_le
        P k hn hM hB hsize (hlight k hk) (hmass k hk)
      have hd' : (∫ ω, X k ω * X k ω
          ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P))) ≤ D := by
        simpa only [X, D, pow_two] using hd
      refine hd'.trans (le_add_of_nonneg_right ?_)
      dsimp only [Q]
      positivity
    · rw [if_neg hkl, zero_add]
      change (∫ ω,
          (factorialPolynomialContribution (fun i : Fin n => ω i) k -
            sparsePolynomialMean P k (polynomialDegree n) (bandwidth n)) *
          (factorialPolynomialContribution (fun i : Fin n => ω i) l -
            sparsePolynomialMean P l (polynomialDegree n) (bandwidth n)) ∂_) ≤ Q
      have hMle : polynomialDegree n ≤ splitSize n 1 := by
        nlinarith [Nat.mul_self_le_mul_self (show 1 ≤ polynomialDegree n by omega)]
      rw [integral_mul_sub_const_sub_const
        (integrable_factorialPolynomialContribution_trunc_rate P k)
        (integrable_factorialPolynomialContribution_trunc_rate P l)
        (integrable_factorialPolynomial_cross_mul P k l),
        integral_factorialPolynomialContribution_eq_sparsePolynomialMean P k hMle,
        integral_factorialPolynomialContribution_eq_sparsePolynomialMean P l hMle]
      have hc := factorialPolynomial_cross_covariance_le P k l hkl
        hM hB hsize (hmass k hk) (hmass l hl)
      exact (le_abs_self _).trans hc
  simp_rw [fixedLightCentered, pow_two, Finset.sum_mul_sum]
  rw [integral_finset_sum S (fun k _ =>
    integrable_finset_sum S (fun l _ => by
      exact (((integrable_factorialPolynomial_cross_mul P k l).sub
        ((integrable_factorialPolynomialContribution_trunc_rate P k).const_mul _)).sub
        ((integrable_factorialPolynomialContribution_trunc_rate P l).const_mul _)).add
        (integrable_const _)))]
  simp_rw [integral_finset_sum S (fun l _ => by
    exact (((integrable_factorialPolynomial_cross_mul P _ l).sub
      ((integrable_factorialPolynomialContribution_trunc_rate P _).const_mul _)).sub
      ((integrable_factorialPolynomialContribution_trunc_rate P l).const_mul _)).add
      (integrable_const _))]
  refine (Finset.sum_le_sum fun k hk =>
    Finset.sum_le_sum fun l hl => hpair k hk l hl).trans ?_
  change (∑ k ∈ S, ∑ l ∈ S, (if k = l then D else 0) + Q) ≤ _
  rw [show (∑ k ∈ S, ∑ l ∈ S, (if k = l then D else 0) + Q) =
      (S.card : ℝ) * D + (S.card : ℝ) ^ 2 * Q by
    simp [Finset.sum_add_distrib, pow_two]
    ring]
  rfl

-/

end CausalSmith.Stat.DiscreteAteMinimaxLoggap
