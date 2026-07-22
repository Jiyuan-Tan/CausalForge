import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Multivariate monomial Gram matrices

This module proves that distinct multivariate monomials have a positive-definite Gram matrix on
every nondegenerate real cube.  It also supplies the resulting uniform quadratic coercivity bound.
-/

open scoped BigOperators
open MeasureTheory Set

namespace Causalean.Mathlib.Analysis

/-- The closed sup-norm ball contains the vectors whose every coordinate lies within the stated
radius of the corresponding coordinate of the center. -/
def supBall {d : ℕ} (x0 : Fin d → ℝ) (r : ℝ) : Set (Fin d → ℝ) :=
  {x | ∀ i, |x i - x0 i| ≤ r}

/-- A multivariate monomial multiplies the coordinates of a vector after raising each coordinate
to its assigned nonnegative integer exponent. -/
def monomial {d : ℕ} (e : Fin d → ℕ) (u : Fin d → ℝ) : ℝ :=
  ∏ j : Fin d, (u j) ^ (e j)

/-- The monomial Gram matrix records the integrals of every pairwise product of a finite family of
multivariate monomials over a centered closed cube. -/
noncomputable def monomialGram {d p : ℕ} (expo : Fin p → (Fin d → ℕ)) (r : ℝ) :
    Matrix (Fin p) (Fin p) ℝ :=
  Matrix.of fun k l => ∫ u in {u : Fin d → ℝ | ∀ j, |u j| ≤ r},
    monomial (expo k) u * monomial (expo l) u

private def cube (d : ℕ) (r : ℝ) : Set (Fin d → ℝ) :=
  {u | ∀ j, |u j| ≤ r}

private lemma cube_eq_pi_Icc (d : ℕ) (r : ℝ) :
    cube d r = Set.pi Set.univ (fun _ : Fin d => Set.Icc (-r) r) := by
  ext u
  simp only [cube, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc,
    abs_le]

private lemma isCompact_cube (d : ℕ) (r : ℝ) : IsCompact (cube d r) := by
  rw [cube_eq_pi_Icc]
  exact isCompact_univ_pi fun _ => isCompact_Icc

private lemma continuous_monomial {d : ℕ} (e : Fin d → ℕ) :
    Continuous (monomial e) := by
  unfold monomial
  exact continuous_finset_prod _ fun j _ => (continuous_apply j).pow (e j)

private lemma continuous_monomialCombination {d p : ℕ}
    (expo : Fin p → (Fin d → ℕ)) (z : Fin p → ℝ) :
    Continuous (fun u => ∑ k, z k * monomial (expo k) u) := by
  exact continuous_finset_sum _ fun k _ =>
    continuous_const.mul (continuous_monomial (expo k))

private lemma integrableOn_monomial_product {d : ℕ} (e f : Fin d → ℕ) (r : ℝ) :
    IntegrableOn (fun u => monomial e u * monomial f u) (cube d r) := by
  exact ((continuous_monomial e).mul (continuous_monomial f)).continuousOn.integrableOn_compact
    (isCompact_cube d r)

private noncomputable def exponentFinsupp {d : ℕ} (e : Fin d → ℕ) : Fin d →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm e

private noncomputable def monomialPolynomial {d : ℕ} (e : Fin d → ℕ) : MvPolynomial (Fin d) ℝ :=
  MvPolynomial.monomial (exponentFinsupp e) 1

private lemma eval_monomialPolynomial {d : ℕ} (e : Fin d → ℕ) (u : Fin d → ℝ) :
    MvPolynomial.eval u (monomialPolynomial e) = monomial e u := by
  simp [monomialPolynomial, exponentFinsupp, monomial, MvPolynomial.eval_monomial,
    Finsupp.prod_fintype]

private noncomputable def monomialCombinationPolynomial {d p : ℕ} (expo : Fin p → (Fin d → ℕ))
    (z : Fin p → ℝ) : MvPolynomial (Fin d) ℝ :=
  ∑ k, MvPolynomial.C (z k) * monomialPolynomial (expo k)

private lemma eval_monomialCombinationPolynomial {d p : ℕ}
    (expo : Fin p → (Fin d → ℕ)) (z : Fin p → ℝ) (u : Fin d → ℝ) :
    MvPolynomial.eval u (monomialCombinationPolynomial expo z) =
      ∑ k, z k * monomial (expo k) u := by
  simp [monomialCombinationPolynomial, eval_monomialPolynomial]

private lemma monomial_coefficients_eq_zero_of_vanishes_on_openCube {d p : ℕ}
    {expo : Fin p → (Fin d → ℕ)} {r : ℝ} (hr : 0 < r)
    (hexpo : Function.Injective expo) (z : Fin p → ℝ)
    (hz : ∀ u, (∀ j, u j ∈ Set.Ioo (-r) r) →
      (∑ k, z k * monomial (expo k) u) = 0) : z = 0 := by
  let P := monomialCombinationPolynomial expo z
  have hP : P = 0 := by
    apply MvPolynomial.funext_set (fun _ : Fin d => Set.Ioo (-r) r)
      (fun _ => Set.Ioo_infinite (by linarith))
    intro u hu
    change MvPolynomial.eval u (monomialCombinationPolynomial expo z) =
      MvPolynomial.eval u 0
    rw [eval_monomialCombinationPolynomial, map_zero]
    exact hz u (fun j => hu j (Set.mem_univ j))
  funext k
  have hcoeff := congrArg
    (MvPolynomial.coeffAddMonoidHom (exponentFinsupp (expo k))) hP
  have hfs : Function.Injective (fun e : Fin d → ℕ => exponentFinsupp e) := by
    intro e e' he
    apply congrArg Finsupp.equivFunOnFinite at he
    simpa [exponentFinsupp] using he
  simp only [P, monomialCombinationPolynomial, map_sum, map_zero] at hcoeff
  simpa [monomialPolynomial, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_monomial,
    hfs.eq_iff, hexpo.eq_iff] using hcoeff

/-- A linear combination of distinct multivariate monomials that vanishes throughout a cube with
positive radius must have every coefficient equal to zero. -/
theorem monomial_linearIndependent_on_cube {d p : ℕ} {expo : Fin p → (Fin d → ℕ)} {r : ℝ}
    (hr : 0 < r) (hexpo : Function.Injective expo) (z : Fin p → ℝ)
    (hz : ∀ u, (∀ j, |u j| ≤ r) → (∑ k, z k * monomial (expo k) u) = 0) :
    z = 0 := by
  apply monomial_coefficients_eq_zero_of_vanishes_on_openCube hr hexpo z
  intro u hu
  apply hz u
  intro j
  rw [abs_le]
  exact ⟨(hu j).1.le, (hu j).2.le⟩

/-- Evaluating the monomial Gram quadratic form at a coefficient vector equals integrating the
square of the corresponding monomial combination over the cube. -/
theorem monomialGram_quadForm {d p : ℕ} (expo : Fin p → (Fin d → ℕ)) {r : ℝ}
    (hr : 0 < r) (z : Fin p → ℝ) :
    ∑ k, ∑ l, z k * monomialGram expo r k l * z l =
      ∫ u in {u : Fin d → ℝ | ∀ j, |u j| ≤ r},
        (∑ k, z k * monomial (expo k) u) ^ 2 := by
  have _hr := hr
  change (∑ k, ∑ l, z k * (∫ u in cube d r,
      monomial (expo k) u * monomial (expo l) u) * z l) = _
  have hkl (k l : Fin p) : IntegrableOn
      (fun u => (z k * monomial (expo k) u) * (z l * monomial (expo l) u))
      (cube d r) :=
    (((continuous_const.mul (continuous_monomial (expo k))).mul
      (continuous_const.mul (continuous_monomial (expo l)))).continuousOn.integrableOn_compact
        (isCompact_cube d r))
  calc
    _ = ∑ k, ∑ l, ∫ u in cube d r,
        (z k * monomial (expo k) u) * (z l * monomial (expo l) u) := by
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      rw [show (fun u => (z k * monomial (expo k) u) * (z l * monomial (expo l) u)) =
          fun u => (z k * z l) * (monomial (expo k) u * monomial (expo l) u) by
        funext u
        ring, MeasureTheory.integral_const_mul]
      ring
    _ = ∫ u in cube d r, ∑ k, ∑ l,
        (z k * monomial (expo k) u) * (z l * monomial (expo l) u) := by
      symm
      rw [MeasureTheory.integral_finset_sum Finset.univ (fun k _ =>
        integrable_finset_sum _ fun l _ => hkl k l)]
      apply Finset.sum_congr rfl
      intro k _
      rw [MeasureTheory.integral_finset_sum Finset.univ (fun l _ => hkl k l)]
    _ = ∫ u in cube d r, (∑ k, z k * monomial (expo k) u) ^ 2 := by
      congr 1
      funext u
      rw [pow_two, Finset.sum_mul_sum]

/-- The monomial Gram matrix is symmetric, and hence Hermitian over the real numbers. -/
theorem monomialGram_isHermitian {d p : ℕ} (expo : Fin p → (Fin d → ℕ)) (r : ℝ) :
    (monomialGram expo r).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro k l
  simp only [star_id_of_comm]
  simp [monomialGram, mul_comm]

/-- Every coefficient vector gives a nonnegative quadratic form under the monomial Gram matrix. -/
theorem monomialGram_posSemidef {d p : ℕ} (expo : Fin p → (Fin d → ℕ)) {r : ℝ}
    (hr : 0 < r) : (monomialGram expo r).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (monomialGram_isHermitian expo r)
  intro z
  rw [show star z = z by ext k; simp]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  simp_rw [← mul_assoc]
  rw [monomialGram_quadForm expo hr z]
  exact MeasureTheory.integral_nonneg_of_ae
    (Filter.Eventually.of_forall fun _ => sq_nonneg _)

/-- Distinct multivariate monomials have a positive-definite Gram matrix on every cube with
positive radius. -/
theorem monomialGram_posDef {d p : ℕ} (expo : Fin p → (Fin d → ℕ)) {r : ℝ}
    (hr : 0 < r) (hexpo : Function.Injective expo) :
    (monomialGram expo r).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (monomialGram_isHermitian expo r)
  intro z hz
  rw [show star z = z by ext k; simp]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  simp_rw [← mul_assoc]
  rw [monomialGram_quadForm expo hr z]
  let f : (Fin d → ℝ) → ℝ := fun u => ∑ k, z k * monomial (expo k) u
  have hfcont : Continuous f := continuous_monomialCombination expo z
  have hfint : IntegrableOn (fun u => (f u) ^ 2) (cube d r) :=
    (hfcont.pow 2).continuousOn.integrableOn_compact (isCompact_cube d r)
  have hnonneg : 0 ≤ ∫ u in cube d r, (f u) ^ 2 :=
    MeasureTheory.integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun _ => sq_nonneg _)
  by_contra hpos
  have hintzero : (∫ u in cube d r, (f u) ^ 2) = 0 :=
    le_antisymm (le_of_not_gt hpos) hnonneg
  have hae_sq : (fun u => (f u) ^ 2) =ᵐ[volume.restrict (cube d r)] 0 :=
    (MeasureTheory.setIntegral_eq_zero_iff_of_nonneg_ae
      (Filter.Eventually.of_forall fun _ => sq_nonneg _) hfint).mp hintzero
  have hae_f : f =ᵐ[volume.restrict (cube d r)] 0 :=
    hae_sq.mono fun u hu => by simpa using (sq_eq_zero_iff.mp hu)
  let U : Set (Fin d → ℝ) := Set.pi Set.univ (fun _ => Set.Ioo (-r) r)
  have hUopen : IsOpen U :=
    isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)
  have hUcube : U ⊆ cube d r := by
    intro u hu j
    rw [abs_le]
    exact ⟨(hu j (Set.mem_univ j)).1.le, (hu j (Set.mem_univ j)).2.le⟩
  have hae_U : f =ᵐ[volume.restrict U] 0 :=
    ae_restrict_of_ae_restrict_of_subset hUcube hae_f
  have hpoint : Set.EqOn f 0 U :=
    MeasureTheory.Measure.eqOn_open_of_ae_eq hae_U hUopen hfcont.continuousOn
      continuous_zero.continuousOn
  apply hz
  apply monomial_coefficients_eq_zero_of_vanishes_on_openCube hr hexpo z
  intro u hu
  exact hpoint (fun j _ => hu j)

private lemma sum_sq_pos {p : ℕ} (z : Fin p → ℝ) (hz : z ≠ 0) :
    0 < ∑ k, (z k) ^ 2 := by
  have hnonneg : 0 ≤ ∑ k, (z k) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  refine lt_of_le_of_ne hnonneg ?_
  intro heq
  apply hz
  funext k
  have hk : (z k) ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mp heq.symm k
      (Finset.mem_univ k)
  exact sq_eq_zero_iff.mp hk

/-- A fixed family of distinct monomials on a cube with positive radius admits a positive uniform
lower bound: its Gram quadratic form dominates the squared Euclidean norm of the coefficients. -/
theorem exists_monomialGram_coercive {d p : ℕ} (expo : Fin p → (Fin d → ℕ)) {r : ℝ}
    (hr : 0 < r) (hexpo : Function.Injective expo) :
    ∃ cmin : ℝ, 0 < cmin ∧ ∀ z : Fin p → ℝ,
      cmin * (∑ k, (z k) ^ 2) ≤
        ∑ k, ∑ l, z k * monomialGram expo r k l * z l := by
  by_cases hp : p = 0
  · subst p
    refine ⟨1, one_pos, ?_⟩
    intro z
    simp
  have hp0 : 0 < p := Nat.pos_of_ne_zero hp
  let q : (Fin p → ℝ) → ℝ := fun z =>
    ∑ k, ∑ l, z k * monomialGram expo r k l * z l
  let s2 : (Fin p → ℝ) → ℝ := fun z => ∑ k, (z k) ^ 2
  let S : Set (Fin p → ℝ) := {z | s2 z = 1}
  have hqcont : Continuous q := by
    dsimp [q]
    fun_prop
  have hs2cont : Continuous s2 := by
    dsimp [s2]
    fun_prop
  have hSclosed : IsClosed S := by
    exact isClosed_eq hs2cont continuous_const
  have hSbounded : Bornology.IsBounded S := by
    apply (Metric.isBounded_iff_subset_closedBall 0).mpr
    refine ⟨1, ?_⟩
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right]
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro k
    rw [Real.norm_eq_abs, ← sq_le_one_iff_abs_le_one]
    have hk : (z k) ^ 2 ≤ 1 := by
      rw [← hz]
      exact Finset.single_le_sum (fun i _ => sq_nonneg (z i)) (Finset.mem_univ k)
    exact hk
  have hScompact : IsCompact S :=
    Metric.isCompact_iff_isClosed_bounded.mpr ⟨hSclosed, hSbounded⟩
  let e : Fin p := ⟨0, hp0⟩
  let zunit : Fin p → ℝ := Pi.single e 1
  have hzunit : zunit ∈ S := by
    classical
    simp [S, s2, zunit, Pi.single_apply]
  obtain ⟨zmin, hzmin, hmin⟩ :=
    hScompact.exists_isMinOn ⟨zunit, hzunit⟩ hqcont.continuousOn
  have hPD := monomialGram_posDef expo hr hexpo
  have hzmin_ne : zmin ≠ 0 := by
    intro hzero
    simp [S, s2, hzero] at hzmin
  have hqmin_pos : 0 < q zmin := by
    have h := hPD.dotProduct_mulVec_pos hzmin_ne
    rw [show star zmin = zmin by ext k; simp] at h
    simpa only [q, dotProduct, Matrix.mulVec, Finset.mul_sum, ← mul_assoc] using h
  refine ⟨q zmin, hqmin_pos, ?_⟩
  intro z
  by_cases hz : z = 0
  · simp [hz, q]
  have hspos : 0 < s2 z := by
    exact sum_sq_pos z hz
  let a : ℝ := (Real.sqrt (s2 z))⁻¹
  let w : Fin p → ℝ := a • z
  have hsqrt : (Real.sqrt (s2 z)) ^ 2 = s2 z := by
    exact (Real.sq_sqrt hspos.le)
  have hsqrt_ne : Real.sqrt (s2 z) ≠ 0 := (Real.sqrt_pos.2 hspos).ne'
  have hwS : w ∈ S := by
    simp only [S, Set.mem_setOf_eq, s2, w, Pi.smul_apply, smul_eq_mul]
    calc
      ∑ k, (a * z k) ^ 2 = a ^ 2 * ∑ k, (z k) ^ 2 := by
        simp_rw [mul_pow, Finset.mul_sum]
      _ = 1 := by
        dsimp [a]
        rw [inv_pow, hsqrt]
        exact inv_mul_cancel₀ hspos.ne'
  have hscale : q w = a ^ 2 * q z := by
    dsimp [q, w]
    symm
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    ring
  have hlower : q zmin ≤ q w := hmin hwS
  rw [hscale] at hlower
  change q zmin * s2 z ≤ q z
  calc
    q zmin * s2 z ≤ (a ^ 2 * q z) * s2 z :=
      mul_le_mul_of_nonneg_right hlower hspos.le
    _ = q z := by
      dsimp [a]
      rw [inv_pow, hsqrt]
      field_simp

end Causalean.Mathlib.Analysis
