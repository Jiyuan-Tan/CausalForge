import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.Estimator
import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.ShiftedChebyshev
import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.MvPolynomialEnvelope
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Data.Nat.Choose.Cast

namespace CausalSmith.Stat.DiscreteAteMinimaxLoggap

open scoped BigOperators

/-- Shifted-Chebyshev coefficient expansion used in the paper's equation (1). -/
lemma shifted_chebyshev_expansion (M : ℕ) (x : ℝ) :
    (Polynomial.Chebyshev.T ℝ M).eval (1 - 2 * x) =
      1 + ∑ j ∈ Finset.Icc 1 M,
        (-1 : ℝ) ^ j * (M : ℝ) / (M + j) *
          Nat.choose (M + j) (2 * j) * 4 ^ j * x ^ j :=
  shiftedChebyshevExpansion M x

lemma chebyshev_gPolynomial_identity {M : ℕ} (hM : 0 < M) (x : ℝ) :
    (Polynomial.Chebyshev.T ℝ M).eval (1 - 2 * x) =
      1 - 2 * (M : ℝ)^2 * x + 2 * (M : ℝ)^2 * x^2 * gPolynomial M x := by
  rw [shifted_chebyshev_expansion]
  let a : ℕ → ℝ := fun j =>
    (-1 : ℝ) ^ j * (M : ℝ) / (M + j) *
      Nat.choose (M + j) (2 * j) * 4 ^ j * x ^ j
  have hM1 : 1 ≤ M := hM
  have hs : Finset.Icc 1 M = insert 1 (Finset.Icc 2 M) := by
    symm
    exact Finset.insert_Icc_add_one_left_eq_Icc hM1
  have hnot : 1 ∉ Finset.Icc 2 M := by simp
  have hi : Finset.Icc 2 M = Finset.Ico 2 (M + 1) := by
    ext j
    simp
  change 1 + ∑ j ∈ Finset.Icc 1 M, a j = _
  rw [hs, Finset.sum_insert hnot, hi, Finset.sum_Ico_eq_sum_range]
  have hsub : M + 1 - 2 = M - 1 := by omega
  rw [hsub]
  have ha1 : a 1 = -2 * (M : ℝ)^2 * x := by
    dsimp [a]
    rw [Nat.cast_choose_two]
    norm_num
    push_cast
    have hMn : (M : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  rw [ha1]
  have hsum : (∑ k ∈ Finset.range (M - 1), a (2 + k)) =
      2 * (M : ℝ)^2 * x^2 * gPolynomial M x := by
    unfold gPolynomial
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hkn : k + 2 ≤ M := by simp only [Finset.mem_range] at hk; omega
    have hden : (M : ℝ) + (k : ℝ) + 2 ≠ 0 := by positivity
    simp only [a, gCoefficient]
    push_cast
    rw [show 2 + k = k + 2 by omega]
    rw [show 2 * (k + 2) = 2 * k + 4 by omega]
    rw [show M + (k + 2) = M + k + 2 by omega]
    rw [pow_add x k 2, pow_add (-1 : ℝ) k 2, pow_add 4 k 2]
    rw [show (-1 : ℝ)^2 = 1 by ring, show (4 : ℝ)^2 = 16 by ring]
    simp only [mul_one]
    rw [show (4 : ℝ)^k = 2^(2*k) by
      calc
        (4 : ℝ)^k = (2^2 : ℝ)^k := by norm_num
        _ = 2^(2*k) := by rw [pow_mul]]
    rw [show 2 * k = k * 2 by omega]
    rw [show (2 : ℝ)^(k*2+3) = 2^(k*2) * 8 by rw [pow_add]; norm_num]
    field_simp [hden]
    ring
  rw [hsum]
  ring

/-- Uniform reciprocal-approximation certificate on `[0,1]`. -/
lemma gPolynomial_certificate {M : ℕ} (hM : 0 < M) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    x * |1 - x * gPolynomial M x| ≤ ((M : ℝ) ^ 2)⁻¹ := by
  let t := (Polynomial.Chebyshev.T ℝ M).eval (1 - 2 * x)
  have hy : |1 - 2 * x| ≤ (1 : ℝ) := by
    rw [abs_le]
    constructor <;> linarith [hx.1, hx.2]
  have ht : |t| ≤ (1 : ℝ) := by
    exact Polynomial.Chebyshev.abs_eval_T_real_le_one M hy
  have hdiff : |1 - t| ≤ (2 : ℝ) := by
    calc
      |1 - t| ≤ |(1 : ℝ)| + |t| := abs_sub _ _
      _ ≤ 2 := by norm_num; linarith
  have hm : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hm2 : 0 < (M : ℝ)^2 := sq_pos_of_pos hm
  have hid : 1 - t = 2 * (M : ℝ)^2 * x * (1 - x * gPolynomial M x) := by
    dsimp [t]
    rw [chebyshev_gPolynomial_identity hM x]
    ring
  have habs : |1 - t| = 2 * (M : ℝ)^2 * x * |1 - x * gPolynomial M x| := by
    rw [hid, abs_mul, abs_mul, abs_mul]
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2),
      abs_of_nonneg (sq_nonneg (M : ℝ)), abs_of_nonneg hx.1]
  rw [inv_eq_one_div]
  apply (le_div_iff₀ hm2).2
  rw [habs] at hdiff
  nlinarith [abs_nonneg (1 - x * gPolynomial M x)]

private lemma eval_cellApproxPolynomial (M : ℕ) (B : ℝ) (u : Cell → ℝ) :
    (cellApproxPolynomial M B).eval u =
      B⁻¹ * vectorMass u * u (1,1) * gPolynomial M (vectorArmMass u 1 / B) -
      B⁻¹ * vectorMass u * u (0,1) * gPolynomial M (vectorArmMass u 0 / B) := by
  simp [cellApproxPolynomial, mvMass, mvArmMass, vectorMass, vectorArmMass,
    gPolynomial, div_eq_mul_inv]
  ring

/-- Cone approximation bound for the explicit four-cell polynomial. -/
lemma cellApproxPolynomial_error {M : ℕ} (hM : 0 < M) {B epsilon : ℝ}
    {u : Cell → ℝ} (he0 : 0 < epsilon) (hu : u ∈ overlapCone epsilon)
    (hB : vectorMass u ≤ B) :
    |(cellApproxPolynomial M B).eval u - cellPhi u| ≤
      2 * B / (epsilon * M ^ 2) := by
  rcases hu with ⟨hu_nonneg, hu_low, hu_up⟩
  by_cases huz : u = 0
  · subst u
    rw [eval_cellApproxPolynomial]
    have hB0 : 0 ≤ B := by simpa [vectorMass, vectorArmMass] using hB
    simp [cellPhi, vectorMass, vectorArmMass]
    exact div_nonneg (mul_nonneg (by norm_num) hB0)
      (le_of_lt (mul_pos he0 (by positivity)))
  have hs0 : 0 ≤ vectorMass u := by
    simp only [vectorMass, vectorArmMass]
    linarith [hu_nonneg (0,0), hu_nonneg (0,1), hu_nonneg (1,0), hu_nonneg (1,1)]
  have hsne : vectorMass u ≠ 0 := by
    intro hs
    apply huz
    funext i
    rcases i with ⟨a,y⟩
    fin_cases a <;> fin_cases y
    all_goals
      have h00 := hu_nonneg (0,0)
      have h01 := hu_nonneg (0,1)
      have h10 := hu_nonneg (1,0)
      have h11 := hu_nonneg (1,1)
      simp only [vectorMass, vectorArmMass] at hs
      simp_all
      linarith
  have hs : 0 < vectorMass u := lt_of_le_of_ne hs0 (Ne.symm hsne)
  have hBp : 0 < B := lt_of_lt_of_le hs hB
  have hM2 : 0 < (M : ℝ)^2 := by positivity
  have hlow0 : epsilon * vectorMass u ≤ vectorArmMass u 0 := by
    rw [vectorMass] at hu_up ⊢
    linarith
  have arm_bound (a : Fin 2)
      (ha : epsilon * vectorMass u ≤ vectorArmMass u a) :
      |B⁻¹ * vectorMass u * u (a,1) *
          gPolynomial M (vectorArmMass u a / B) -
        vectorMass u * (u (a,1) / vectorArmMass u a)| ≤
        B / (epsilon * (M : ℝ)^2) := by
    have hsa0 : 0 ≤ vectorArmMass u a := by
      rw [vectorArmMass]
      exact add_nonneg (hu_nonneg (a,0)) (hu_nonneg (a,1))
    have hsap : 0 < vectorArmMass u a :=
      lt_of_lt_of_le (mul_pos he0 hs) ha
    have htas : u (a,1) ≤ vectorArmMass u a := by
      simp only [vectorArmMass]
      linarith [hu_nonneg (a,0)]
    have hsaB : vectorArmMass u a ≤ B := by
      have h0 : vectorArmMass u 0 ≤ vectorMass u := by
        rw [vectorMass]
        have hn : 0 ≤ vectorArmMass u 1 := by
          rw [vectorArmMass]
          exact add_nonneg (hu_nonneg (1,0)) (hu_nonneg (1,1))
        linarith
      have h1 : vectorArmMass u 1 ≤ vectorMass u := by
        rw [vectorMass]
        have hn : 0 ≤ vectorArmMass u 0 := by
          rw [vectorArmMass]
          exact add_nonneg (hu_nonneg (0,0)) (hu_nonneg (0,1))
        linarith
      have : vectorArmMass u a ≤ vectorMass u := by
        fin_cases a
        · simpa using h0
        · simpa using h1
      exact this.trans hB
    have hx : vectorArmMass u a / B ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · positivity
      · exact (div_le_one hBp).2 hsaB
    have hcert := gPolynomial_certificate hM hx
    let E := |1 - (vectorArmMass u a / B) *
      gPolynomial M (vectorArmMass u a / B)|
    have hxp : 0 < vectorArmMass u a / B := div_pos hsap hBp
    have hE : E ≤ B / (vectorArmMass u a * (M : ℝ)^2) := by
      have h' : E ≤ ((M : ℝ)^2)⁻¹ / (vectorArmMass u a / B) :=
        (le_div_iff₀ hxp).2 (by simpa [E, mul_comm] using hcert)
      calc
        E ≤ ((M : ℝ)^2)⁻¹ / (vectorArmMass u a / B) := h'
        _ = B / (vectorArmMass u a * (M : ℝ)^2) := by field_simp
    have hcoef0 : 0 ≤ vectorMass u * u (a,1) / vectorArmMass u a := by
      exact div_nonneg (mul_nonneg hs0 (hu_nonneg (a,1))) hsa0
    have hcoef : vectorMass u * u (a,1) / vectorArmMass u a ≤ vectorMass u := by
      apply (div_le_iff₀ hsap).2
      nlinarith [hu_nonneg (a,1)]
    have hfactor :
        vectorMass u * u (a,1) / vectorArmMass u a * E ≤
          B / (epsilon * (M : ℝ)^2) := by
      calc
        vectorMass u * u (a,1) / vectorArmMass u a * E
            ≤ vectorMass u * (B / (vectorArmMass u a * (M : ℝ)^2)) := by
              gcongr
        _ ≤ B / (epsilon * (M : ℝ)^2) := by
          field_simp
          nlinarith
    have hid :
        B⁻¹ * vectorMass u * u (a,1) *
              gPolynomial M (vectorArmMass u a / B) -
            vectorMass u * (u (a,1) / vectorArmMass u a) =
          -(vectorMass u * u (a,1) / vectorArmMass u a) *
            (1 - (vectorArmMass u a / B) *
              gPolynomial M (vectorArmMass u a / B)) := by
      field_simp
      ring
    rw [hid, abs_mul, abs_neg]
    rw [abs_of_nonneg hcoef0]
    exact hfactor
  have hb1 := arm_bound 1 hu_low
  have hb0 := arm_bound 0 hlow0
  rw [eval_cellApproxPolynomial, cellPhi, if_neg huz]
  have hdecomp :
      B⁻¹ * vectorMass u * u (1, 1) * gPolynomial M (vectorArmMass u 1 / B) -
          B⁻¹ * vectorMass u * u (0, 1) * gPolynomial M (vectorArmMass u 0 / B) -
        vectorMass u * (u (1, 1) / vectorArmMass u 1 -
          u (0, 1) / vectorArmMass u 0) =
        (B⁻¹ * vectorMass u * u (1,1) * gPolynomial M (vectorArmMass u 1 / B) -
          vectorMass u * (u (1,1) / vectorArmMass u 1)) -
        (B⁻¹ * vectorMass u * u (0,1) * gPolynomial M (vectorArmMass u 0 / B) -
          vectorMass u * (u (0,1) / vectorArmMass u 0)) := by ring
  rw [hdecomp]
  calc
    |(_ : ℝ) - _| ≤ |(_ : ℝ)| + |(_ : ℝ)| := abs_sub _ _
    _ ≤ B / (epsilon * (M : ℝ)^2) + B / (epsilon * (M : ℝ)^2) :=
      add_le_add hb1 hb0
    _ = 2 * B / (epsilon * (M : ℝ)^2) := by ring

/-- Establishes the stated property of env C in the discrete average-treatment-effect construction. -/
lemma env_C (c : ℝ) (v : Cell → ℝ) :
    coefficientEnvelope (MvPolynomial.C c) v = |c| := by
  rw [show MvPolynomial.C c = MvPolynomial.monomial 0 c by rfl]
  unfold coefficientEnvelope monomialWeight
  by_cases hc : c = 0
  · simp [hc]
  · rw [MvPolynomial.support_monomial]
    simp [hc]

/-- Establishes the stated property of env X in the discrete average-treatment-effect construction. -/
lemma env_X (i : Cell) (v : Cell → ℝ) :
    coefficientEnvelope (MvPolynomial.X i) v = v i := by
  change coefficientEnvelope (MvPolynomial.monomial (Finsupp.single i 1) 1) v = _
  unfold coefficientEnvelope monomialWeight
  rw [MvPolynomial.support_monomial]
  simp
  rcases i with ⟨a,y⟩
  fin_cases a <;> fin_cases y <;>
    simp [Fintype.prod_prod_type, Fin.prod_univ_two]

/-- Shows that env nonneg is nonnegative. -/
lemma env_nonneg (p : MvPolynomial Cell ℝ) (v : Cell → ℝ) (hv : ∀ i, 0 ≤ v i) :
    0 ≤ coefficientEnvelope p v := by
  unfold coefficientEnvelope
  exact Finset.sum_nonneg fun r hr =>
    mul_nonneg (abs_nonneg _) (monomialWeight_nonneg v hv r)

/-- Establishes the stated upper bound for env pow le. -/
lemma env_pow_le (p : MvPolynomial Cell ℝ) (v : Cell → ℝ) (hv : ∀ i, 0 ≤ v i)
    (j : ℕ) : coefficientEnvelope (p^j) v ≤ coefficientEnvelope p v ^ j := by
  induction j with
  | zero =>
      change coefficientEnvelope (MvPolynomial.C 1) v ≤ 1
      rw [env_C]
      norm_num
  | succ j ih =>
      rw [pow_succ, pow_succ]
      calc
        coefficientEnvelope (p^j*p) v ≤
            coefficientEnvelope (p^j) v * coefficientEnvelope p v :=
          coefficientEnvelope_mul_le _ _ _ hv
        _ ≤ coefficientEnvelope p v ^ j * coefficientEnvelope p v := by
          exact mul_le_mul_of_nonneg_right ih (env_nonneg p v hv)

/-- Establishes the stated upper bound for env sum le. -/
lemma env_sum_le {ι : Type} [DecidableEq ι] (s : Finset ι)
    (f : ι → MvPolynomial Cell ℝ) (v : Cell → ℝ) (hv : ∀ i, 0 ≤ v i) :
    coefficientEnvelope (∑ i ∈ s, f i) v ≤ ∑ i ∈ s, coefficientEnvelope (f i) v := by
  induction s using Finset.induction_on with
  | empty => simp [coefficientEnvelope]
  | insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (coefficientEnvelope_add_le _ _ _ hv).trans (add_le_add_right ih _)

/-- Defines gpos, the stated quantity or construction used in the discrete average-treatment-effect estimator. -/
noncomputable def gpos (M : ℕ) (z : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (M-1), |gCoefficient M j| * z^j

/-- Establishes the stated property of abs g Coefficient in the discrete average-treatment-effect construction. -/
lemma abs_gCoefficient {M : ℕ} (hM : 0 < M) (j : ℕ) :
    |gCoefficient M j| = 2^(2*j+3) / ((M:ℝ)*(M+j+2)) * Nat.choose (M+j+2) (2*j+4) := by
  unfold gCoefficient
  rw [abs_mul, abs_div, abs_mul, abs_pow, abs_neg, abs_one]
  rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ 2^(2*j+3))]
  rw [abs_of_pos (mul_pos (by exact_mod_cast hM) (by positivity))]
  rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ (Nat.choose (M+j+2) (2*j+4) : ℝ))]
  norm_num

/-- Establishes the stated property of sign g Coefficient in the discrete average-treatment-effect construction. -/
lemma sign_gCoefficient {M : ℕ} (hM : 0 < M) (j : ℕ) :
    |gCoefficient M j| = (-1 : ℝ)^j * gCoefficient M j := by
  rw [abs_gCoefficient hM]
  unfold gCoefficient
  have hs : (-1 : ℝ)^j * (-1 : ℝ)^j = 1 := by
    rw [← pow_add]
    rw [show j+j=2*j by omega, pow_mul]
    simp
  calc
    2 ^ (2*j+3) / ((M:ℝ)*(M+j+2)) * Nat.choose (M+j+2) (2*j+4)
        = ((-1 : ℝ)^j * (-1 : ℝ)^j) *
            (2 ^ (2*j+3) / ((M:ℝ)*(M+j+2)) * Nat.choose (M+j+2) (2*j+4)) := by
              rw [hs, one_mul]
    _ = _ := by ring

/-- Establishes the stated equality relating gpos eq. -/
lemma gpos_eq (M : ℕ) (hM : 0 < M) (z : ℝ) :
    gpos M z = gPolynomial M (-z) := by
  unfold gpos gPolynomial
  apply Finset.sum_congr rfl
  intro j hj
  rw [sign_gCoefficient hM, neg_pow]
  ring

/-- Establishes the stated upper bound for chebyshev three le. -/
lemma chebyshev_three_le (M : ℕ) :
    (Polynomial.Chebyshev.T ℝ M).eval 3 ≤ (6 : ℝ)^M := by
  induction M using Nat.twoStepInduction with
  | zero => simp
  | one => norm_num [Polynomial.Chebyshev.T_one]
  | more n hn hn1 =>
      rw [show (n+2 : ℕ) = (n:ℤ)+2 by omega]
      rw [Polynomial.Chebyshev.T_add_two]
      simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat,
        Polynomial.eval_X]
      have hnonneg : 0 ≤ (Polynomial.Chebyshev.T ℝ n).eval 3 :=
        le_trans (by norm_num) (Polynomial.Chebyshev.one_le_eval_T_real n (by norm_num))
      calc
        2 * 3 * (Polynomial.Chebyshev.T ℝ (n+1)).eval 3 -
            (Polynomial.Chebyshev.T ℝ n).eval 3
            ≤ 6 * (Polynomial.Chebyshev.T ℝ (n+1)).eval 3 := by linarith
        _ ≤ 6 * 6^(n+1) := by
          gcongr
          simpa using hn1
        _ = 6^(n+2) := by rw [pow_succ]; ring

/-- Shows that gpos nonneg is nonnegative. -/
lemma gpos_nonneg (M : ℕ) {z : ℝ} (hz : 0 ≤ z) : 0 ≤ gpos M z := by
  unfold gpos
  exact Finset.sum_nonneg fun j hj => mul_nonneg (abs_nonneg _) (pow_nonneg hz _)

/-- Establishes the stated upper bound for gpos bound. -/
lemma gpos_bound {M : ℕ} (hM : 0 < M) {z : ℝ} (hz : 0 ≤ z) :
    gpos M z ≤ (6:ℝ)^M * max 1 (z^(M-2)) := by
  have hid := chebyshev_gPolynomial_identity hM (-1 : ℝ)
  norm_num at hid
  rw [← gpos_eq M hM 1] at hid
  have hg1n := gpos_nonneg M (show (0:ℝ) ≤ 1 by norm_num)
  have hm1 : (1:ℝ) ≤ (M:ℝ)^2 := by
    have : (1:ℝ) ≤ M := by exact_mod_cast hM
    nlinarith
  have hg1T : gpos M 1 ≤ (Polynomial.Chebyshev.T ℝ M).eval 3 := by
    have hmul := mul_le_mul_of_nonneg_right hm1 hg1n
    have hgterm : gpos M 1 ≤ 2 * (M:ℝ)^2 * gpos M 1 := by
      nlinarith [mul_nonneg (sq_nonneg (M:ℝ)) hg1n]
    calc
      gpos M 1 ≤ 1 + 2 * (M:ℝ)^2 + 2 * (M:ℝ)^2 * 1 * gpos M 1 := by
        simp only [mul_one]
        linarith [sq_nonneg (M:ℝ)]
      _ = (Polynomial.Chebyshev.T ℝ M).eval 3 := hid.symm
  have hg1 : gpos M 1 ≤ (6:ℝ)^M := hg1T.trans (chebyshev_three_le M)
  by_cases hz1 : z ≤ 1
  · have hgz : gpos M z ≤ gpos M 1 := by
      unfold gpos
      apply Finset.sum_le_sum
      intro j hj
      gcongr
    calc
      gpos M z ≤ gpos M 1 := hgz
      _ ≤ (6:ℝ)^M := hg1
      _ ≤ (6:ℝ)^M * max 1 (z^(M-2)) := by
        have : (1:ℝ) ≤ max 1 (z^(M-2)) := le_max_left _ _
        nlinarith [pow_nonneg (show (0:ℝ) ≤ 6 by norm_num) M]
  · have h1z : 1 ≤ z := le_of_not_ge hz1
    have hgz : gpos M z ≤ z^(M-2) * gpos M 1 := by
      unfold gpos
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j hj
      have hjle : j ≤ M-2 := by simp only [Finset.mem_range] at hj; omega
      have hp : z^j ≤ z^(M-2) := pow_le_pow_right₀ h1z hjle
      simp only [one_pow, mul_one]
      rw [mul_comm (z^(M-2))]
      exact mul_le_mul_of_nonneg_left hp (abs_nonneg _)
    calc
      gpos M z ≤ z^(M-2) * gpos M 1 := hgz
      _ ≤ z^(M-2) * (6:ℝ)^M := by
        gcongr
      _ ≤ (6:ℝ)^M * max 1 (z^(M-2)) := by
        have := le_max_right (1:ℝ) (z^(M-2))
        nlinarith [pow_nonneg (show (0:ℝ) ≤ 6 by norm_num) M]

/-- Establishes the stated upper bound for env arm le. -/
lemma env_arm_le (a : Fin 2) (v : Cell → ℝ) (hv : ∀ i, 0 ≤ v i) :
    coefficientEnvelope (mvArmMass a) v ≤ vectorArmMass v a := by
  unfold mvArmMass vectorArmMass
  calc
    coefficientEnvelope (MvPolynomial.X (a,0) + MvPolynomial.X (a,1)) v ≤
        coefficientEnvelope (MvPolynomial.X (a,0)) v +
          coefficientEnvelope (MvPolynomial.X (a,1)) v :=
      coefficientEnvelope_add_le _ _ _ hv
    _ = _ := by rw [env_X, env_X]

/-- Establishes the stated upper bound for env mass le. -/
lemma env_mass_le (v : Cell → ℝ) (hv : ∀ i, 0 ≤ v i) :
    coefficientEnvelope mvMass v ≤ vectorMass v := by
  unfold mvMass vectorMass
  calc
    coefficientEnvelope (mvArmMass 0 + mvArmMass 1) v ≤
        coefficientEnvelope (mvArmMass 0) v + coefficientEnvelope (mvArmMass 1) v :=
      coefficientEnvelope_add_le _ _ _ hv
    _ ≤ vectorArmMass v 0 + vectorArmMass v 1 :=
      add_le_add (env_arm_le 0 v hv) (env_arm_le 1 v hv)

/-- Establishes the stated upper bound for env eval G le. -/
lemma env_evalG_le {M : ℕ} {B R : ℝ} (hB : 0 < B) (hR : 0 ≤ R)
    (s : MvPolynomial Cell ℝ) (v : Cell → ℝ) (hv : ∀ i, 0 ≤ v i)
    (hs : coefficientEnvelope s v ≤ R) :
    coefficientEnvelope
      (∑ j ∈ Finset.range (M-1),
        MvPolynomial.C (gCoefficient M j) * (MvPolynomial.C B⁻¹ * s)^j) v ≤
      gpos M (R/B) := by
  calc
    coefficientEnvelope
      (∑ j ∈ Finset.range (M-1),
        MvPolynomial.C (gCoefficient M j) * (MvPolynomial.C B⁻¹ * s)^j) v
        ≤ ∑ j ∈ Finset.range (M-1), coefficientEnvelope
          (MvPolynomial.C (gCoefficient M j) * (MvPolynomial.C B⁻¹ * s)^j) v :=
      env_sum_le _ _ _ hv
    _ ≤ ∑ j ∈ Finset.range (M-1), |gCoefficient M j| * (R/B)^j := by
      apply Finset.sum_le_sum
      intro j hj
      calc
        coefficientEnvelope
            (MvPolynomial.C (gCoefficient M j) * (MvPolynomial.C B⁻¹ * s)^j) v
            ≤ coefficientEnvelope (MvPolynomial.C (gCoefficient M j)) v *
                coefficientEnvelope ((MvPolynomial.C B⁻¹ * s)^j) v :=
              coefficientEnvelope_mul_le _ _ _ hv
        _ ≤ |gCoefficient M j| *
              coefficientEnvelope (MvPolynomial.C B⁻¹ * s) v ^ j := by
              rw [env_C]
              gcongr
              exact env_pow_le _ _ hv _
        _ ≤ |gCoefficient M j| * (R/B)^j := by
          have hscaled : coefficientEnvelope (MvPolynomial.C B⁻¹ * s) v ≤ R/B := by
            calc
              coefficientEnvelope (MvPolynomial.C B⁻¹ * s) v ≤
                  coefficientEnvelope (MvPolynomial.C B⁻¹) v *
                    coefficientEnvelope s v := coefficientEnvelope_mul_le _ _ _ hv
              _ = B⁻¹ * coefficientEnvelope s v := by
                rw [env_C, abs_of_pos (inv_pos.mpr hB)]
              _ ≤ B⁻¹ * R := by gcongr
              _ = R/B := by ring
          have hp := pow_le_pow_left₀
            (env_nonneg (MvPolynomial.C B⁻¹ * s) v hv) hscaled j
          exact mul_le_mul_of_nonneg_left hp (abs_nonneg _)
    _ = gpos M (R/B) := rfl

/-- Establishes the stated upper bound for env mul4 le. -/
lemma env_mul4_le (p q r s : MvPolynomial Cell ℝ) (v : Cell → ℝ)
    (hv : ∀ i, 0 ≤ v i) :
    coefficientEnvelope (p*q*r*s) v ≤ coefficientEnvelope p v *
      coefficientEnvelope q v * coefficientEnvelope r v * coefficientEnvelope s v := by
  calc
    coefficientEnvelope (p*q*r*s) v ≤
        coefficientEnvelope (p*q*r) v * coefficientEnvelope s v :=
      coefficientEnvelope_mul_le _ _ _ hv
    _ ≤ (coefficientEnvelope (p*q) v * coefficientEnvelope r v) *
          coefficientEnvelope s v := by
      exact mul_le_mul_of_nonneg_right
        (coefficientEnvelope_mul_le (p*q) r v hv) (env_nonneg s v hv)
    _ ≤ ((coefficientEnvelope p v * coefficientEnvelope q v) *
          coefficientEnvelope r v) * coefficientEnvelope s v := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (coefficientEnvelope_mul_le p q v hv) (env_nonneg r v hv))
        (env_nonneg s v hv)

/-- The numerical absolute-coefficient certificate with base `A=6`. -/
lemma cellApproxPolynomial_coeff_envelope (M : ℕ) {B : ℝ} (hB : 0 < B)
    (v : Cell → ℝ) (hv : ∀ i, 0 ≤ v i) :
    ∑ r ∈ (cellApproxPolynomial M B).support,
        |(cellApproxPolynomial M B).coeff r| *
          r.prod (fun i e => (v i) ^ e) ≤
      B * 6 ^ M *
        max ((vectorMass v / B) ^ 2) ((vectorMass v / B) ^ M) := by
  change coefficientEnvelope (cellApproxPolynomial M B) v ≤ _
  by_cases hsmall : M < 2
  · interval_cases M
    · simp [cellApproxPolynomial, coefficientEnvelope, le_of_lt hB]
    · simp [cellApproxPolynomial, coefficientEnvelope]
      have hz0 : 0 ≤ vectorMass v / B := by
        apply div_nonneg
        · dsimp [vectorMass, vectorArmMass]
          linarith [hv (0,0), hv (0,1), hv (1,0), hv (1,1)]
        · exact le_of_lt hB
      positivity
  have hM2 : 2 ≤ M := Nat.le_of_not_gt hsmall
  have hM : 0 < M := by omega
  let R := vectorMass v
  let z := R/B
  let evalG (s : MvPolynomial Cell ℝ) :=
    ∑ j ∈ Finset.range (M-1),
      MvPolynomial.C (gCoefficient M j) * (MvPolynomial.C B⁻¹ * s)^j
  have hR : 0 ≤ R := by
    dsimp [R, vectorMass, vectorArmMass]
    linarith [hv (0,0), hv (0,1), hv (1,0), hv (1,1)]
  have hz : 0 ≤ z := div_nonneg hR (le_of_lt hB)
  have hArm0 : coefficientEnvelope (mvArmMass 0) v ≤ R :=
    (env_arm_le 0 v hv).trans (by
      dsimp [R, vectorMass]
      have hn : 0 ≤ vectorArmMass v 1 := by
        dsimp [vectorArmMass]
        linarith [hv (1,0), hv (1,1)]
      linarith)
  have hArm1 : coefficientEnvelope (mvArmMass 1) v ≤ R :=
    (env_arm_le 1 v hv).trans (by
      dsimp [R, vectorMass]
      have hn : 0 ≤ vectorArmMass v 0 := by
        dsimp [vectorArmMass]
        linarith [hv (0,0), hv (0,1)]
      linarith)
  have hEval (a : Fin 2) : coefficientEnvelope (evalG (mvArmMass a)) v ≤ gpos M z := by
    apply env_evalG_le hB hR (mvArmMass a) v hv
    fin_cases a
    · simpa using hArm0
    · simpa using hArm1
  have hArm (a : Fin 2) :
      coefficientEnvelope
        (MvPolynomial.C B⁻¹ * mvMass * MvPolynomial.X (a,1) * evalG (mvArmMass a)) v ≤
        B⁻¹ * R * v (a,1) * gpos M z := by
    calc
      coefficientEnvelope
          (MvPolynomial.C B⁻¹ * mvMass * MvPolynomial.X (a,1) * evalG (mvArmMass a)) v
          ≤ coefficientEnvelope (MvPolynomial.C B⁻¹) v *
              coefficientEnvelope mvMass v * coefficientEnvelope (MvPolynomial.X (a,1)) v *
                coefficientEnvelope (evalG (mvArmMass a)) v := env_mul4_le _ _ _ _ _ hv
      _ = B⁻¹ * coefficientEnvelope mvMass v * v (a,1) *
            coefficientEnvelope (evalG (mvArmMass a)) v := by
          rw [env_C, abs_of_pos (inv_pos.mpr hB), env_X]
      _ ≤ B⁻¹ * R * v (a,1) * gpos M z := by
        have hmass := env_mass_le v hv
        have he := hEval a
        have hgp := gpos_nonneg M hz
        have ht := hv (a,1)
        have hbi : 0 ≤ B⁻¹ := le_of_lt (inv_pos.mpr hB)
        have h1 : B⁻¹ * coefficientEnvelope mvMass v ≤ B⁻¹ * R :=
          mul_le_mul_of_nonneg_left hmass hbi
        have h2 : B⁻¹ * coefficientEnvelope mvMass v * v (a,1) ≤
            B⁻¹ * R * v (a,1) := mul_le_mul_of_nonneg_right h1 ht
        exact mul_le_mul h2 he (env_nonneg (evalG (mvArmMass a)) v hv) (by positivity)
  have hpoly : coefficientEnvelope (cellApproxPolynomial M B) v ≤
      B⁻¹ * R^2 * gpos M z := by
    change coefficientEnvelope
      (MvPolynomial.C B⁻¹ * mvMass * MvPolynomial.X (1,1) * evalG (mvArmMass 1) -
       MvPolynomial.C B⁻¹ * mvMass * MvPolynomial.X (0,1) * evalG (mvArmMass 0)) v ≤ _
    calc
      coefficientEnvelope (_ - _) v ≤ coefficientEnvelope
          (MvPolynomial.C B⁻¹ * mvMass * MvPolynomial.X (1,1) * evalG (mvArmMass 1)) v +
        coefficientEnvelope
          (MvPolynomial.C B⁻¹ * mvMass * MvPolynomial.X (0,1) * evalG (mvArmMass 0)) v :=
            coefficientEnvelope_sub_le _ _ _ hv
      _ ≤ B⁻¹ * R * v (1,1) * gpos M z +
          B⁻¹ * R * v (0,1) * gpos M z := add_le_add (hArm 1) (hArm 0)
      _ ≤ B⁻¹ * R^2 * gpos M z := by
        have ht : v (1,1) + v (0,1) ≤ R := by
          dsimp [R, vectorMass, vectorArmMass]
          linarith [hv (0,0), hv (1,0)]
        have hgp := gpos_nonneg M hz
        have hbi : 0 ≤ B⁻¹ := le_of_lt (inv_pos.mpr hB)
        have hfac0 : 0 ≤ B⁻¹ * R * gpos M z := by positivity
        calc
          B⁻¹ * R * v (1,1) * gpos M z + B⁻¹ * R * v (0,1) * gpos M z =
              (B⁻¹ * R * gpos M z) * (v (1,1) + v (0,1)) := by ring
          _ ≤ (B⁻¹ * R * gpos M z) * R :=
            mul_le_mul_of_nonneg_left ht hfac0
          _ = B⁻¹ * R^2 * gpos M z := by ring
  have hg := gpos_bound hM hz
  calc
    coefficientEnvelope (cellApproxPolynomial M B) v ≤ B⁻¹ * R^2 * gpos M z := hpoly
    _ ≤ B⁻¹ * R^2 * ((6:ℝ)^M * max 1 (z^(M-2))) := by
      gcongr
    _ = B * 6^M * max (z^2) (z^M) := by
      have hzrel : R = B*z := by dsimp [z]; field_simp
      have hpow : z^2 * z^(M-2) = z^M := by
        rw [← pow_add]
        congr 1
        omega
      rw [hzrel]
      have hBne : B ≠ 0 := ne_of_gt hB
      by_cases hh : (1:ℝ) ≤ z^(M-2)
      · rw [max_eq_right hh, max_eq_right]
        · rw [← hpow]
          field_simp
        · exact (show z^2 ≤ z^M by rw [← hpow]; nlinarith [pow_nonneg hz 2])
      · have hh' : z^(M-2) ≤ 1 := le_of_not_ge hh
        rw [max_eq_left hh', max_eq_left]
        · field_simp
        · rw [← hpow]
          nlinarith [pow_nonneg hz 2]
    _ = B * 6 ^ M * max ((vectorMass v / B)^2) ((vectorMass v / B)^M) := rfl

end CausalSmith.Stat.DiscreteAteMinimaxLoggap
