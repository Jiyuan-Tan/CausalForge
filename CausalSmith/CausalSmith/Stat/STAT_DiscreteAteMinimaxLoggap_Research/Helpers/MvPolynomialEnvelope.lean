import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.Estimator
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace CausalSmith.Stat.DiscreteAteMinimaxLoggap

open scoped BigOperators Pointwise

/-- Defines monomial Weight, the stated quantity or construction used in the discrete average-treatment-effect estimator. -/
noncomputable def monomialWeight (v : Cell → ℝ) (r : MultiIndex) : ℝ :=
  r.prod (fun i e => v i ^ e)

/-- Defines coefficient Envelope, the stated quantity or construction used in the discrete average-treatment-effect estimator. -/
noncomputable def coefficientEnvelope (p : MvPolynomial Cell ℝ) (v : Cell → ℝ) : ℝ :=
  ∑ r ∈ p.support, |p.coeff r| * monomialWeight v r

/-- Shows that monomial Weight nonneg is nonnegative. -/
lemma monomialWeight_nonneg (v : Cell → ℝ) (hv : ∀ i, 0 ≤ v i) (r : MultiIndex) :
    0 ≤ monomialWeight v r := by
  unfold monomialWeight
  exact Finset.prod_nonneg fun i _ => pow_nonneg (hv i) _

/-- Establishes the stated property of monomial Weight add in the discrete average-treatment-effect construction. -/
lemma monomialWeight_add (v : Cell → ℝ) (r s : MultiIndex) :
    monomialWeight v (r+s) = monomialWeight v r * monomialWeight v s := by
  unfold monomialWeight
  apply Finsupp.prod_add_index
  · intro; simp
  · intro a ha b₁ b₂
    exact pow_add _ _ _

/-- Establishes the stated property of coefficient Envelope extend in the discrete average-treatment-effect construction. -/
lemma coefficientEnvelope_extend (p : MvPolynomial Cell ℝ) (v : Cell → ℝ)
    (s : Finset MultiIndex) (hs : p.support ⊆ s) :
    coefficientEnvelope p v = ∑ r ∈ s, |p.coeff r| * monomialWeight v r := by
  unfold coefficientEnvelope
  apply Finset.sum_subset hs
  intro r hrs hrp
  have hc : p.coeff r = 0 := not_ne_iff.mp ((MvPolynomial.mem_support_iff).not.mp hrp)
  simp [hc]

/-- Establishes the stated upper bound for coefficient Envelope add le. -/
lemma coefficientEnvelope_add_le (p q : MvPolynomial Cell ℝ) (v : Cell → ℝ)
    (hv : ∀ i, 0 ≤ v i) :
    coefficientEnvelope (p+q) v ≤ coefficientEnvelope p v + coefficientEnvelope q v := by
  let s := p.support ∪ q.support
  rw [coefficientEnvelope_extend (p+q) v s MvPolynomial.support_add]
  rw [coefficientEnvelope_extend p v s (Finset.subset_union_left)]
  rw [coefficientEnvelope_extend q v s (Finset.subset_union_right)]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro r hr
  rw [MvPolynomial.coeff_add]
  have hw := monomialWeight_nonneg v hv r
  nlinarith [abs_add_le (p.coeff r) (q.coeff r)]

/-- Establishes the stated property of coefficient Envelope neg in the discrete average-treatment-effect construction. -/
lemma coefficientEnvelope_neg (p : MvPolynomial Cell ℝ) (v : Cell → ℝ) :
    coefficientEnvelope (-p) v = coefficientEnvelope p v := by
  unfold coefficientEnvelope
  simp

/-- Establishes the stated upper bound for coefficient Envelope sub le. -/
lemma coefficientEnvelope_sub_le (p q : MvPolynomial Cell ℝ) (v : Cell → ℝ)
    (hv : ∀ i, 0 ≤ v i) :
    coefficientEnvelope (p-q) v ≤ coefficientEnvelope p v + coefficientEnvelope q v := by
  rw [sub_eq_add_neg]
  calc
    coefficientEnvelope (p + -q) v ≤
        coefficientEnvelope p v + coefficientEnvelope (-q) v :=
      coefficientEnvelope_add_le _ _ _ hv
    _ = _ := by rw [coefficientEnvelope_neg]

/-- Establishes the stated upper bound for coefficient Envelope mul le. -/
lemma coefficientEnvelope_mul_le (p q : MvPolynomial Cell ℝ) (v : Cell → ℝ)
    (hv : ∀ i, 0 ≤ v i) :
    coefficientEnvelope (p*q) v ≤ coefficientEnvelope p v * coefficientEnvelope q v := by
  let S := p.support ×ˢ q.support
  let U := p.support + q.support
  have hsupp : (p*q).support ⊆ U := MvPolynomial.support_mul p q
  rw [coefficientEnvelope_extend (p*q) v U hsupp]
  have hcoeff (n : MultiIndex) :
      |(p*q).coeff n| * monomialWeight v n ≤
        ∑ rs ∈ S, if rs.1 + rs.2 = n then
          (|p.coeff rs.1| * monomialWeight v rs.1) *
            (|q.coeff rs.2| * monomialWeight v rs.2) else 0 := by
    rw [MvPolynomial.coeff_mul]
    let A := Finset.antidiagonal n
    have heq :
        (∑ rs ∈ A, p.coeff rs.1 * q.coeff rs.2) =
          ∑ rs ∈ A ∩ S, p.coeff rs.1 * q.coeff rs.2 := by
      symm
      apply Finset.sum_subset Finset.inter_subset_left
      intro rs hrs hrsnot
      have hnotS : rs ∉ S := by
        intro hS
        exact hrsnot (Finset.mem_inter.mpr ⟨hrs, hS⟩)
      by_cases hp : rs.1 ∈ p.support
      · have hq : rs.2 ∉ q.support := by
          intro hq
          exact hnotS (by simp [S, hp, hq])
        have hc : q.coeff rs.2 = 0 :=
          not_ne_iff.mp ((MvPolynomial.mem_support_iff).not.mp hq)
        simp [hc]
      · have hc : p.coeff rs.1 = 0 :=
          not_ne_iff.mp ((MvPolynomial.mem_support_iff).not.mp hp)
        simp [hc]
    rw [heq]
    calc
      |∑ rs ∈ A ∩ S, p.coeff rs.1 * q.coeff rs.2| * monomialWeight v n
          ≤ (∑ rs ∈ A ∩ S, |p.coeff rs.1 * q.coeff rs.2|) *
              monomialWeight v n := by
            exact mul_le_mul_of_nonneg_right
              (Finset.abs_sum_le_sum_abs (G := ℝ)
                (fun rs : MultiIndex × MultiIndex => p.coeff rs.1 * q.coeff rs.2) (A ∩ S))
              (monomialWeight_nonneg v hv n)
      _ = ∑ rs ∈ A ∩ S,
          (|p.coeff rs.1| * monomialWeight v rs.1) *
            (|q.coeff rs.2| * monomialWeight v rs.2) := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro rs hrs
            have hadd : rs.1 + rs.2 = n := by
              simpa [A] using (Finset.mem_inter.mp hrs).1
            rw [abs_mul, ← hadd, monomialWeight_add]
            ring
      _ = ∑ rs ∈ S, if rs.1 + rs.2 = n then
          (|p.coeff rs.1| * monomialWeight v rs.1) *
            (|q.coeff rs.2| * monomialWeight v rs.2) else 0 := by
            rw [← Finset.sum_filter]
            apply Finset.sum_congr
            · ext rs
              simp [A, and_comm]
            · intro rs hrs
              simp only [Finset.mem_filter] at hrs
              simp
  calc
    (∑ n ∈ U, |(p*q).coeff n| * monomialWeight v n)
        ≤ ∑ n ∈ U, ∑ rs ∈ S, if rs.1 + rs.2 = n then
            (|p.coeff rs.1| * monomialWeight v rs.1) *
              (|q.coeff rs.2| * monomialWeight v rs.2) else 0 := by
          gcongr with n hn
          exact hcoeff n
    _ = ∑ rs ∈ S, (|p.coeff rs.1| * monomialWeight v rs.1) *
              (|q.coeff rs.2| * monomialWeight v rs.2) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro rs hrs
          have hmem : rs.1 + rs.2 ∈ U := by
            rcases (Finset.mem_product.mp
              (show rs ∈ p.support ×ˢ q.support from hrs)) with ⟨hr, hs⟩
            exact Finset.mem_add.mpr ⟨rs.1, hr, rs.2, hs, rfl⟩
          rw [Finset.sum_eq_single (rs.1+rs.2)]
          · simp
          · intro n hn hne
            simp [hne.symm]
          · exact fun h => (h hmem).elim
    _ = coefficientEnvelope p v * coefficientEnvelope q v := by
          unfold S coefficientEnvelope
          rw [Finset.sum_product, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro r hr
          rw [Finset.mul_sum]

end CausalSmith.Stat.DiscreteAteMinimaxLoggap
