import Causalean.Mathlib.AlgebraicGeometry.PolynomialImageDimension.Transcendence
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Nondegenerate

/-!
# Jacobian certificates for polynomial-image dimension

In characteristic zero, a nonzero square Jacobian minor certifies algebraic
independence of the selected coordinate polynomials.  A matching upper
transcendence-degree or finite presentation certificate then gives exact image
dimension.
-/

namespace Causalean.Mathlib.AlgebraicGeometry.PolynomialImageDimension

set_option maxSynthPendingDepth 16

noncomputable section

/-- The polynomial coordinate subalgebra inherits its usual complex-algebra
structure, allowing the Jacobian argument to use its transcendence degree. -/
local instance jacobianCoordinateSubalgebraAlgebra {ι κ : Type*}
    (f : κ → MvPolynomial ι ℂ) :
    Algebra ℂ (polynomialCoordinateSubalgebra f) :=
  Subalgebra.algebra (polynomialCoordinateSubalgebra f)

/-- A polynomial Jacobian minor records the determinant of selected derivative
coordinates of a polynomial parameterization before evaluating it at any point. -/
def polynomialJacobianMinor {ι κ : Type*} {d : ℕ}
    (f : κ → MvPolynomial ι ℂ) (rows : Fin d → κ) (cols : Fin d → ι) :
    MvPolynomial ι ℂ :=
  Matrix.det (fun a b => MvPolynomial.pderiv (cols b) (f (rows a)))

-- The next three lemmas are the reusable algebraic core of the Jacobian
-- criterion.  Keeping them private avoids enlarging the public API while giving
-- the proof below independently checkable intermediate statements.

private lemma pderiv_polynomialPullback
    {ι κ : Type*} [Fintype κ]
    (f : κ → MvPolynomial ι ℂ) (P : MvPolynomial κ ℂ) (i : ι) :
    MvPolynomial.pderiv i (polynomialPullback f P) =
      ∑ j : κ,
        polynomialPullback f (MvPolynomial.pderiv j P) *
          MvPolynomial.pderiv i (f j) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a => simp [polynomialPullback]
  | add P Q hP hQ =>
      simp only [map_add, hP, hQ]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
  | mul_X P j hP =>
      simp only [map_mul, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X,
        map_add, hP]
      simp_rw [add_mul]
      rw [Finset.sum_add_distrib]
      congr 1
      · rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro x _
        ring
      · simp [polynomialPullback, Pi.single_apply]

private lemma totalDegree_pderiv_lt
    {σ R : Type*} [CommRing R] {i : σ} {P : MvPolynomial σ R}
    (hP : MvPolynomial.pderiv i P ≠ 0) :
    (MvPolynomial.pderiv i P).totalDegree < P.totalDegree := by
  classical
  have hdeg_pos : 0 < P.totalDegree := by
    apply Nat.pos_of_ne_zero
    intro hdeg
    apply hP
    rw [(MvPolynomial.totalDegree_eq_zero_iff_eq_C).mp hdeg,
      MvPolynomial.pderiv_C]
  have hle : (MvPolynomial.pderiv i P).totalDegree ≤ P.totalDegree - 1 := by
    have hpderiv : MvPolynomial.pderiv i P =
        ∑ m ∈ P.support,
          MvPolynomial.pderiv i (MvPolynomial.monomial m (P.coeff m)) := by
      simpa only [map_sum] using
        congrArg (MvPolynomial.pderiv i) P.as_sum
    rw [hpderiv]
    apply MvPolynomial.totalDegree_finsetSum_le
    intro m hm
    rw [MvPolynomial.pderiv_monomial]
    by_cases hmi : m i = 0
    · simp [hmi]
    · refine (MvPolynomial.totalDegree_monomial_le _ _).trans ?_
      change (m - Finsupp.single i 1).degree ≤ P.totalDegree - 1
      have hmdeg : (m - Finsupp.single i 1).degree + 1 = m.degree := by
        simpa [Finsupp.degree_eq_weight_one] using
          (Finsupp.weight_sub_single_add
            (w := fun _ : σ => (1 : ℕ)) hmi)
      have hmle : m.degree ≤ P.totalDegree := by
        simpa [Finsupp.degree_apply] using MvPolynomial.le_totalDegree hm
      omega
  exact hle.trans_lt (Nat.sub_lt hdeg_pos Nat.zero_lt_one)

private lemma sum_X_mul_pderiv_eq_sum_degree
    {σ : Type*} [Fintype σ] (P : MvPolynomial σ ℂ) :
    (∑ i : σ, MvPolynomial.X i * MvPolynomial.pderiv i P) =
      ∑ m ∈ P.support,
        m.degree • MvPolynomial.monomial m (P.coeff m) := by
  classical
  calc
    (∑ i : σ, MvPolynomial.X i * MvPolynomial.pderiv i P) =
        ∑ i : σ, MvPolynomial.X i * MvPolynomial.pderiv i
          (∑ m ∈ P.support, MvPolynomial.monomial m (P.coeff m)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg (fun Q => MvPolynomial.X i * MvPolynomial.pderiv i Q)
        P.as_sum
    _ = _ := by
      simp_rw [map_sum, Finset.mul_sum,
        MvPolynomial.X_mul_pderiv_monomial]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro m _
      rw [← Finset.sum_smul, ← Finsupp.degree_eq_sum]

private lemma eq_C_of_forall_pderiv_eq_zero
    {σ : Type*} [Fintype σ] (P : MvPolynomial σ ℂ)
    (hP : ∀ i, MvPolynomial.pderiv i P = 0) :
    P = MvPolynomial.C (P.coeff 0) := by
  classical
  have heuler := sum_X_mul_pderiv_eq_sum_degree P
  have hleft : (∑ i : σ,
      MvPolynomial.X i * MvPolynomial.pderiv i P) = 0 := by
    simp [hP]
  rw [hleft] at heuler
  have hdegree : ∀ m ∈ P.support, m.degree = 0 := by
    intro m hm
    have hc := congrArg (MvPolynomial.coeff m) heuler
    have hrhs : MvPolynomial.coeff m
        (∑ x ∈ P.support,
          x.degree • MvPolynomial.monomial x (P.coeff x)) =
          (m.degree : ℂ) * P.coeff m := by
      calc
        _ = ∑ x ∈ P.support, MvPolynomial.coeff m
              (x.degree • MvPolynomial.monomial x (P.coeff x)) :=
          MvPolynomial.coeff_sum P.support
            (fun x => x.degree • MvPolynomial.monomial x (P.coeff x)) m
        _ = _ := by
          have hcoeff_nsmul (n : ℕ) (Q : MvPolynomial σ ℂ) :
              MvPolynomial.coeff m (n • Q) = n • MvPolynomial.coeff m Q :=
            (MvPolynomial.coeffAddMonoidHom m).map_nsmul Q n
          simp_rw [hcoeff_nsmul, MvPolynomial.coeff_monomial]
          rw [Finset.sum_eq_single m]
          · simp [nsmul_eq_mul]
          · intro x hx hxm
            simp [hxm]
          · exact fun hnot => (hnot hm).elim
    have hmul : (m.degree : ℂ) * P.coeff m = 0 := by
      rw [hrhs] at hc
      exact hc.symm
    have hcoeff : P.coeff m ≠ 0 := MvPolynomial.mem_support_iff.mp hm
    have hcast : (m.degree : ℂ) = 0 :=
      (mul_eq_zero.mp hmul).resolve_right hcoeff
    exact_mod_cast hcast
  apply MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
  rw [MvPolynomial.totalDegree]
  exact Finset.sup_eq_zero.mpr fun m hm => by
    change Finsupp.degree m = 0
    exact hdegree m hm

/-- Over the complex numbers, a nonzero square Jacobian minor proves that the
corresponding coordinate polynomials satisfy no nontrivial algebraic relation. -/
theorem algebraicIndependent_of_polynomialJacobianMinor_ne_zero
    {ι κ : Type*} {d : ℕ} (f : κ → MvPolynomial ι ℂ)
    (rows : Fin d → κ) (cols : Fin d → ι)
    (hminor : polynomialJacobianMinor f rows cols ≠ 0) :
    AlgebraicIndependent ℂ (fun a => f (rows a)) := by
  classical
  let g : Fin d → MvPolynomial ι ℂ := fun a => f (rows a)
  by_contra hAI
  rw [algebraicIndependent_iff] at hAI
  push_neg at hAI
  obtain ⟨P₀, hP₀ker, hP₀ne⟩ := hAI
  let bad : ℕ → Prop := fun n =>
    ∃ P : MvPolynomial (Fin d) ℂ,
      P ≠ 0 ∧ polynomialPullback g P = 0 ∧ P.totalDegree = n
  have hbad : ∃ n, bad n := by
    refine ⟨P₀.totalDegree, P₀, hP₀ne, ?_, rfl⟩
    simpa [g, polynomialPullback] using hP₀ker
  let n := Nat.find hbad
  obtain ⟨P, hPne, hPker, hPdeg⟩ : bad n := Nat.find_spec hbad
  let J : Matrix (Fin d) (Fin d) (MvPolynomial ι ℂ) :=
    fun a b => MvPolynomial.pderiv (cols b) (g a)
  let v : Fin d → MvPolynomial ι ℂ :=
    fun a => polynomialPullback g (MvPolynomial.pderiv a P)
  have hchain (b : Fin d) :
      ∑ a : Fin d,
        polynomialPullback g (MvPolynomial.pderiv a P) *
          MvPolynomial.pderiv (cols b) (g a) = 0 := by
    have hp := congrArg (MvPolynomial.pderiv (cols b)) hPker
    simpa [pderiv_polynomialPullback] using hp
  have hmul : Matrix.mulVec J.transpose v = 0 := by
    funext b
    simpa [J, v, Matrix.mulVec, dotProduct, mul_comm] using hchain b
  have hdet : J.transpose.det ≠ 0 := by
    simpa [J, g, polynomialJacobianMinor] using hminor
  have hv : v = 0 := Matrix.eq_zero_of_mulVec_eq_zero hdet hmul
  have hpartials : ∀ a : Fin d, MvPolynomial.pderiv a P = 0 := by
    intro a
    have hQker : polynomialPullback g (MvPolynomial.pderiv a P) = 0 := by
      have ha := congrFun hv a
      simpa [v] using ha
    by_contra hQne
    have hlt := totalDegree_pderiv_lt hQne
    have hbadQ : bad (MvPolynomial.pderiv a P).totalDegree :=
      ⟨MvPolynomial.pderiv a P, hQne, hQker, rfl⟩
    have hmin : n ≤ (MvPolynomial.pderiv a P).totalDegree := by
      dsimp [n]
      exact Nat.find_min' hbad hbadQ
    exact (not_lt_of_ge hmin) (hlt.trans_eq hPdeg)
  have hconst := eq_C_of_forall_pderiv_eq_zero P hpartials
  have hcoeff : P.coeff 0 = 0 := by
    have hk := hPker
    rw [hconst] at hk
    simpa [polynomialPullback] using hk
  apply hPne
  rw [hconst, hcoeff, MvPolynomial.C_0]

/-- A nonzero square Jacobian minor together with a matching upper bound on
transcendence degree identifies the exact affine dimension of a polynomial
image closure. -/
theorem polynomialImageClosure_dimension_of_jacobian
    {ι κ : Type*} [Finite ι] [Finite κ] {d : ℕ}
    (f : κ → MvPolynomial ι ℂ) (rows : Fin d → κ) (cols : Fin d → ι)
    (hminor : polynomialJacobianMinor f rows cols ≠ 0)
    (hupper : @Algebra.trdeg ℂ (polynomialCoordinateSubalgebra f) _ _
      (jacobianCoordinateSubalgebraAlgebra f) ≤ d) :
    HasAffineZariskiDimension d (polynomialImageClosure f) := by
  let calgebra : Algebra ℂ (polynomialCoordinateSubalgebra f) :=
    jacobianCoordinateSubalgebraAlgebra f
  let selected : Fin d → polynomialCoordinateSubalgebra f := fun a =>
    ⟨f (rows a), by
      change f (rows a) ∈ (polynomialPullback f).range
      exact ⟨MvPolynomial.X (rows a), by simp [polynomialPullback]⟩⟩
  have hind :=
    algebraicIndependent_of_polynomialJacobianMinor_ne_zero f rows cols hminor
  have hselected : @AlgebraicIndependent (Fin d) ℂ
      (polynomialCoordinateSubalgebra f) selected _ _ calgebra := by
    apply (@AlgHom.algebraicIndependent_iff (Fin d) ℂ
      (polynomialCoordinateSubalgebra f) (MvPolynomial ι ℂ) selected
      _ _ _ calgebra _ (polynomialCoordinateSubalgebra f).val
      Subtype.val_injective).mp
    simpa [selected, Function.comp_def] using hind
  have hlower : (d : Cardinal) ≤
      @Algebra.trdeg ℂ (polynomialCoordinateSubalgebra f) _ _
        (jacobianCoordinateSubalgebraAlgebra f) := by
    simpa using (@AlgebraicIndependent.lift_cardinalMk_le_trdeg
      (Fin d) ℂ (polynomialCoordinateSubalgebra f) selected _ _ calgebra _
      hselected)
  exact polynomialImageClosure_dimension_of_trdeg f d
    (le_antisymm hupper hlower)

/-- A nonzero Jacobian minor and a surjective presentation using the same number
of generators identify the exact affine dimension of a polynomial image closure. -/
theorem polynomialImageClosure_dimension_of_jacobian_and_surjection
    {ι κ : Type*} [Finite ι] [Finite κ] {d : ℕ}
    (f : κ → MvPolynomial ι ℂ) (rows : Fin d → κ) (cols : Fin d → ι)
    (hminor : polynomialJacobianMinor f rows cols ≠ 0)
    (present : MvPolynomial (Fin d) ℂ →ₐ[ℂ]
      polynomialCoordinateSubalgebra f)
    (hsurj : Function.Surjective present) :
    HasAffineZariskiDimension d (polynomialImageClosure f) := by
  exact polynomialImageClosure_dimension_of_jacobian f rows cols hminor
    (coordinateSubalgebra_trdeg_le_of_surjection f d present hsurj)

end

end Causalean.Mathlib.AlgebraicGeometry.PolynomialImageDimension
