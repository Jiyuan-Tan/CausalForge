import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.FiniteGridSelection
import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.OneArmPriorLift

/-!
# Selected-grid prior lift

Elementary range facts needed to inverse-tilt the finite approximation priors.
-/

namespace CausalSmith.Stat.DiscreteAteMinimaxLoggap

lemma oneArmPoleScale_pos {n : ℕ} (hn : 1 ≤ n) : 0 < oneArmPoleScale n := by
  unfold oneArmPoleScale
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  positivity

lemma oneArmPoleScale_three_le_one {n : ℕ} (hn : 1 ≤ n) :
    3 * oneArmPoleScale n ≤ 1 := by
  unfold oneArmPoleScale
  rw [mul_one_div, div_le_iff₀ (by positivity :
    (0 : ℝ) < 10000000000 * (n : ℝ) ^ 2)]
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith [sq_nonneg ((n : ℝ) - 1)]

lemma oneArmSelectionGrid_mem_Icc {n : ℕ} (hn : 1 ≤ n)
    (i : Fin (2 * n + 4)) :
    oneArmSelectionGrid n i ∈ Set.Icc (oneArmPoleScale n) 1 := by
  by_cases hi : i.1 < 3
  · rw [oneArmSelectionGrid]
    simp only [hi, if_true]
    constructor
    · have ha := oneArmPoleScale_pos hn
      have hcoef : (1 : ℝ) ≤ (i.1 + 1 : ℕ) := by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le _))
      nlinarith
    · have hcoef : ((i.1 + 1 : ℕ) : ℝ) ≤ 3 := by exact_mod_cast hi
      have ha := oneArmPoleScale_pos hn
      exact (mul_le_mul_of_nonneg_right hcoef ha.le).trans
        (oneArmPoleScale_three_le_one hn)
  · rw [oneArmSelectionGrid]
    simp only [hi, if_false]
    apply oneArmAffineMeshNode_mem_Icc hn

lemma oneArmSelectionGrid_pos {n : ℕ} (hn : 1 ≤ n)
    (i : Fin (2 * n + 4)) : 0 < oneArmSelectionGrid n i :=
  (oneArmPoleScale_pos hn).trans_le (oneArmSelectionGrid_mem_Icc hn i).1

lemma oneArmSelectionGrid_add_pole_pos {n : ℕ} (hn : 1 ≤ n)
    (i : Fin (2 * n + 4)) :
    0 < oneArmSelectionGrid n i + oneArmPoleScale n :=
  add_pos (oneArmSelectionGrid_pos hn i) (oneArmPoleScale_pos hn)

/-- Both selected-grid Jordan priors admit the inverse-size tilt with shift
equal to the calibrated pole scale. -/
lemma oneArmSelectionGrid_inverseTiltWeight_nonneg
    (n : ℕ) (hn : 1 ≤ n) (ω : PMF (Fin (2 * n + 4))) :
    ∀ z, 0 ≤ inverseTiltWeight ω (oneArmSelectionGrid n) (oneArmPoleScale n) z := by
  exact inverseTiltWeight_nonneg ω (oneArmSelectionGrid n)
    (oneArmPoleScale_pos hn).le (fun i => (oneArmSelectionGrid_mem_Icc hn i).1)

/-- Coefficients representing `P(x)/x` in the selected reciprocal-monomial
basis.  The final coordinate is harmless when `P` has degree at most `n`. -/
noncomputable def oneArmPolynomialDivCoeff (n : ℕ) (P : Polynomial ℝ) :
    Fin (n + 2) → ℝ := fun j => P.coeff j.1

lemma oneArmPolynomial_eq_constant_add_X_mul_divPolynomial
    (n : ℕ) (P : Polynomial ℝ) (hdeg : P.natDegree ≤ n) :
    P = Polynomial.C (P.coeff 0) + Polynomial.X *
      oneArmSelectionPolynomial n (oneArmPolynomialDivCoeff n P) := by
  ext k
  rw [Polynomial.coeff_add]
  by_cases hk : k = 0
  · subst k
    simp [oneArmSelectionPolynomial]
  · rw [Polynomial.coeff_C, if_neg hk, zero_add,
      show k = (k - 1) + 1 by omega, Polynomial.coeff_X_mul]
    rw [oneArmSelectionPolynomial]
    rw [Polynomial.finsetSum_coeff]
    have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    rw [show k - 1 + 1 = k by omega]
    by_cases hkn : k ≤ n + 1
    · let j : Fin (n + 2) := ⟨k, by omega⟩
      rw [Fintype.sum_eq_single j]
      · simp [j, oneArmPolynomialDivCoeff, hk]
      · intro t ht
        have htk : t.1 ≠ k := by
          intro h
          exact ht (Fin.ext h)
        by_cases ht0 : t.1 = 0
        · simp [ht0]
        · have hexp : t.1 - 1 ≠ k - 1 := by omega
          simp only [ht0, if_false, oneArmPolynomialDivCoeff,
            Polynomial.coeff_C_mul_X_pow]
          rw [if_neg (fun h => hexp h.symm)]
    · have hklarge : n < k := by omega
      have hPk : P.coeff k = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (hdeg.trans_lt hklarge)
      rw [hPk]
      symm
      apply Finset.sum_eq_zero
      intro j hj
      by_cases hj0 : j.1 = 0
      · simp [hj0]
      · have hexp : j.1 - 1 ≠ k - 1 := by omega
        simp only [hj0, if_false, oneArmPolynomialDivCoeff,
          Polynomial.coeff_C_mul_X_pow]
        rw [if_neg (fun h => hexp h.symm)]

lemma oneArmSelectionBasis_represents_polynomial_div
    {n : ℕ} (hn : 1 ≤ n) (P : Polynomial ℝ) (hdeg : P.natDegree ≤ n)
    (i : Fin (2 * n + 4)) :
    finiteGridBasisEval (oneArmSelectionBasis n)
        (oneArmPolynomialDivCoeff n P) i =
      P.eval (oneArmSelectionGrid n i) / oneArmSelectionGrid n i := by
  let x := oneArmSelectionGrid n i
  have hx : x ≠ 0 := ne_of_gt (oneArmSelectionGrid_pos hn i)
  rw [finiteGridBasisEval_apply, oneArmSelectionBasis_sum_eq]
  have hpoly := congrArg (fun Q : Polynomial ℝ => Q.eval x)
    (oneArmPolynomial_eq_constant_add_X_mul_divPolynomial n P hdeg)
  simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
    Polynomial.eval_X] at hpoly
  dsimp [oneArmPolynomialDivCoeff]
  change P.coeff 0 / x +
      (oneArmSelectionPolynomial n (oneArmPolynomialDivCoeff n P)).eval x =
    P.eval x / x
  field_simp [hx]
  nlinarith [hpoly]

/-- Matching the selected reciprocal-monomial basis matches every rational
triple test generated by the inverse tilt through the same total degree. -/
lemma oneArmSelection_moment_matching_tripleTest
    {D : ℕ} (hD : 1 ≤ D) (omega0 omega1 : PMF (Fin (2 * D + 4)))
    (hmom : ∀ c,
      ∑ r, (omega0 r).toReal *
          finiteGridBasisEval (oneArmSelectionBasis D) c r =
        ∑ r, (omega1 r).toReal *
          finiteGridBasisEval (oneArmSelectionBasis D) c r)
    (i j k : ℕ) (hdegree : i + j + k ≤ D) :
    ∑ r, (omega0 r).toReal *
        (oneArmSelectionGrid D r ^ (i + k) *
          (oneArmSelectionGrid D r + oneArmPoleScale D) ^ j /
            oneArmSelectionGrid D r) =
      ∑ r, (omega1 r).toReal *
        (oneArmSelectionGrid D r ^ (i + k) *
          (oneArmSelectionGrid D r + oneArmPoleScale D) ^ j /
            oneArmSelectionGrid D r) := by
  let P : Polynomial ℝ :=
    Polynomial.X ^ (i + k) *
      (Polynomial.X + Polynomial.C (oneArmPoleScale D)) ^ j
  have hPdeg : P.natDegree ≤ D := by
    calc
      P.natDegree ≤ (i + k) + j := by
        dsimp [P]
        calc
          _ ≤ (Polynomial.X ^ (i + k)).natDegree +
              ((Polynomial.X + Polynomial.C (oneArmPoleScale D)) ^ j).natDegree :=
            Polynomial.natDegree_mul_le
          _ ≤ (i + k) + j := by
            gcongr
            · simp
            · calc
                ((Polynomial.X + Polynomial.C (oneArmPoleScale D)) ^ j).natDegree ≤
                    j * (Polynomial.X + Polynomial.C (oneArmPoleScale D)).natDegree :=
                  Polynomial.natDegree_pow_le
                _ ≤ j * 1 := Nat.mul_le_mul_left j
                  ((Polynomial.natDegree_add_le _ _).trans (by simp))
                _ = j := Nat.mul_one j
      _ ≤ D := by omega
  have h := hmom (oneArmPolynomialDivCoeff D P)
  simpa only [oneArmSelectionBasis_represents_polynomial_div hD P hPdeg,
    P, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_add, Polynomial.eval_C] using h

/-- Selected-grid basis matching transports through inverse tilting to every
raw observable moment through degree `D`. -/
lemma oneArmSelection_inverseTilt_liftedRawMoment_eq
    {D : ℕ} (hD : 1 ≤ D) (omega0 omega1 : PMF (Fin (2 * D + 4)))
    (hmom : ∀ c,
      ∑ r, (omega0 r).toReal *
          finiteGridBasisEval (oneArmSelectionBasis D) c r =
        ∑ r, (omega1 r).toReal *
          finiteGridBasisEval (oneArmSelectionBasis D) c r)
    (scale epsilon : ℝ) (i j k : ℕ) (hdegree : i + j + k ≤ D) :
    ∑ z, (inverseTiltPMF omega0 (oneArmSelectionGrid D) (oneArmPoleScale D)
          (oneArmSelectionGrid_inverseTiltWeight_nonneg D hD omega0) z).toReal *
        (liftedCellMass scale (oneArmSelectionGrid D) z ^ i *
          (liftedCellMass scale (oneArmSelectionGrid D) z *
            liftedPropensity epsilon (oneArmPoleScale D)
              (oneArmSelectionGrid D) z) ^ j *
          (liftedCellMass scale (oneArmSelectionGrid D) z *
            liftedPropensity epsilon (oneArmPoleScale D)
              (oneArmSelectionGrid D) z *
            liftedOutcomeMean (oneArmPoleScale D)
              (oneArmSelectionGrid D) z) ^ k) =
      ∑ z, (inverseTiltPMF omega1 (oneArmSelectionGrid D) (oneArmPoleScale D)
          (oneArmSelectionGrid_inverseTiltWeight_nonneg D hD omega1) z).toReal *
        (liftedCellMass scale (oneArmSelectionGrid D) z ^ i *
          (liftedCellMass scale (oneArmSelectionGrid D) z *
            liftedPropensity epsilon (oneArmPoleScale D)
              (oneArmSelectionGrid D) z) ^ j *
          (liftedCellMass scale (oneArmSelectionGrid D) z *
            liftedPropensity epsilon (oneArmPoleScale D)
              (oneArmSelectionGrid D) z *
            liftedOutcomeMean (oneArmPoleScale D)
              (oneArmSelectionGrid D) z) ^ k) := by
  apply inverseTilt_liftedRawMoment_eq omega0 omega1 (oneArmSelectionGrid D)
    (oneArmSelectionGrid_inverseTiltWeight_nonneg D hD omega0)
    (oneArmSelectionGrid_inverseTiltWeight_nonneg D hD omega1)
    (fun r => ne_of_gt (oneArmSelectionGrid_pos hD r))
    (fun r => ne_of_gt (oneArmSelectionGrid_add_pole_pos hD r)) D
  · intro i' j' k' hpos hdeg
    exact oneArmSelection_moment_matching_tripleTest hD omega0 omega1 hmom
      i' j' k' hdeg
  · exact hdegree

end CausalSmith.Stat.DiscreteAteMinimaxLoggap
