/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Coercivity of local-polynomial moment matrices

This file represents finite local-polynomial coefficient vectors as
polynomials and proves a positive, dimension-dependent lower bound for their
weighted squared moment on a nondegenerate radial interval.
-/

open MeasureTheory Set
open scoped BigOperators Interval Polynomial

namespace Causalean.Stat.Nonparametric.LocalPolynomial
/-- The polynomial represented by the local-polynomial coefficient vector. -/
-- @node: localPolynomial
noncomputable def localPolynomial (p : ℕ) (v : Fin (p + 1) → ℝ) : ℝ[X] :=
  ∑ i, Polynomial.C (v i) * Polynomial.X ^ (i : ℕ)

/-- Evaluation of the coefficient polynomial is the dot product with the
monomial basis. -/
-- @node: localPolynomial_eval
lemma localPolynomial_eval (p : ℕ) (v : Fin (p + 1) → ℝ) (u : ℝ) :
    (localPolynomial p v).eval u = ∑ i, v i * u ^ (i : ℕ) := by
  simp only [localPolynomial, Polynomial.eval_finset_sum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

/-- The coefficient polynomial vanishes only when every coefficient does. -/
-- @node: localPolynomial_eq_zero_iff
lemma localPolynomial_eq_zero_iff (p : ℕ) (v : Fin (p + 1) → ℝ) :
    localPolynomial p v = 0 ↔ v = 0 := by
  constructor
  · intro hp
    funext i
    have hc := congrArg (fun q : ℝ[X] => q.coeff (i : ℕ)) hp
    simp only [localPolynomial, Polynomial.finset_sum_coeff,
      Polynomial.coeff_C_mul_X_pow] at hc
    rw [Finset.sum_eq_single i] at hc
    · simpa using hc
    · intro j hj hji
      have hne : (i : ℕ) ≠ (j : ℕ) := by
        intro hij
        exact hji (Fin.ext hij.symm)
      simp [hne]
    · simp
  · rintro rfl
    simp [localPolynomial]

/-- The fixed radial energy used in the polar-sector lower bound. -/
-- @node: radialPolynomialEnergy
noncomputable def radialPolynomialEnergy (p : ℕ)
    (v : Fin (p + 1) → ℝ) : ℝ :=
  ∑ i : Fin (p + 1), ∑ j : Fin (p + 1),
    v i * v j / ((i : ℕ) + (j : ℕ) + 2 : ℕ)

/-- The explicit moment matrix is exactly the weighted squared-polynomial
integral on the unit interval. -/
-- @node: radialPolynomialEnergy_eq_integral
lemma radialPolynomialEnergy_eq_integral (p : ℕ)
    (v : Fin (p + 1) → ℝ) :
    radialPolynomialEnergy p v =
      ∫ u in (0 : ℝ)..1, (∑ i, v i * u ^ (i : ℕ)) ^ 2 * u := by
  rw [radialPolynomialEnergy]
  simp_rw [pow_two, Fintype.sum_mul_sum]
  simp_rw [Finset.sum_mul]
  rw [intervalIntegral.integral_finset_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [intervalIntegral.integral_finset_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [show (fun u : ℝ => (v i * u ^ (i : ℕ)) * (v j * u ^ (j : ℕ)) * u) =
      fun u => (v i * v j) * u ^ ((i : ℕ) + (j : ℕ) + 1) by
    funext u; rw [pow_add]; ring]
  rw [intervalIntegral.integral_const_mul, integral_pow]
  · push_cast
    ring
  all_goals
    intros
    apply Continuous.intervalIntegrable
    fun_prop

/-- A nonzero coefficient vector has strictly positive radial energy. -/
-- @node: radialPolynomialEnergy_pos
lemma radialPolynomialEnergy_pos (p : ℕ) {v : Fin (p + 1) → ℝ}
    (hv : v ≠ 0) : 0 < radialPolynomialEnergy p v := by
  let f : ℝ → ℝ := fun u => (∑ i, v i * u ^ (i : ℕ)) ^ 2 * u
  have hfcont : Continuous f := by fun_prop
  have hfint : IntervalIntegrable f volume 0 1 := hfcont.intervalIntegrable 0 1
  rw [radialPolynomialEnergy_eq_integral]
  have hpoly : localPolynomial p v ≠ 0 := by
    simpa [localPolynomial_eq_zero_iff] using hv
  have hroots : Set.Finite {u : ℝ | Polynomial.IsRoot (localPolynomial p v) u} :=
    (Polynomial.roots (localPolynomial p v)).toFinset.finite_toSet.subset (by
      intro u hu
      simpa [Polynomial.mem_roots hpoly] using hu)
  have hinter : Set.Infinite (Set.Ioo (0 : ℝ) 1) := Set.Ioo_infinite (by norm_num)
  obtain ⟨u, huI, huroot⟩ := (hinter.diff hroots).nonempty
  have hune : (∑ i, v i * u ^ (i : ℕ)) ≠ 0 := by
    rw [← localPolynomial_eval]
    intro he
    exact huroot (by simpa [Polynomial.IsRoot] using he)
  have hfu : f u ≠ 0 := mul_ne_zero (pow_ne_zero 2 hune) (ne_of_gt huI.1)
  rw [intervalIntegral.integral_pos_iff_support_of_nonneg_ae'
    (by
      filter_upwards [ae_restrict_mem
        (measurableSet_uIoc : MeasurableSet (Set.uIoc (0 : ℝ) 1))] with x hx
      rw [Set.uIoc_of_le (by norm_num)] at hx
      have hx0 : 0 ≤ x := by
        exact hx.1.le
      change 0 ≤ (∑ i, v i * x ^ (i : ℕ)) ^ 2 * x
      exact mul_nonneg (sq_nonneg _) hx0) hfint]
  refine ⟨by norm_num, ?_⟩
  let U := Function.support f ∩ Set.Ioo (0 : ℝ) 1
  have hUopen : IsOpen U := hfcont.isOpen_support.inter isOpen_Ioo
  have hUne : U.Nonempty := ⟨u, hfu, huI⟩
  exact lt_of_lt_of_le (hUopen.measure_pos volume hUne) (measure_mono (by
    intro x hx
    exact ⟨hx.1, hx.2.1, hx.2.2.le⟩))

/-- The radial energy is a continuous quadratic function of its coefficient
vector. -/
-- @node: radialPolynomialEnergy_continuous
lemma radialPolynomialEnergy_continuous (p : ℕ) :
    Continuous (radialPolynomialEnergy p) := by
  unfold radialPolynomialEnergy
  fun_prop

/-- Radial energy is homogeneous of degree two in the coefficient vector. -/
-- @node: radialPolynomialEnergy_smul
lemma radialPolynomialEnergy_smul (p : ℕ) (a : ℝ)
    (v : Fin (p + 1) → ℝ) :
    radialPolynomialEnergy p (a • v) = a ^ 2 * radialPolynomialEnergy p v := by
  unfold radialPolynomialEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- [For a polynomial degree bound `p`](hyp:p), [there is a positive constant such that the
radial polynomial energy of any coefficient vector is bounded below by that constant times
the sum of the squared coefficients](goal): on the Euclidean unit sphere, radial polynomial
energy has a positive minimum, and homogeneity packages this as a coercive lower bound for
all coefficient vectors. -/
-- @node: radialPolynomialEnergy_coercive
lemma radialPolynomialEnergy_coercive (p : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ v : Fin (p + 1) → ℝ,
      c * ∑ i, (v i) ^ 2 ≤ radialPolynomialEnergy p v := by
  let S : Set (Fin (p + 1) → ℝ) := Metric.sphere 0 1
  have hScompact : IsCompact S := isCompact_sphere 0 1
  have hSne : S.Nonempty := by
    refine ⟨fun _i => 1, ?_⟩
    rw [Metric.mem_sphere, dist_zero_right]
    simpa using (pi_norm_const' (ι := Fin (p + 1)) (1 : ℝ))
  obtain ⟨v0, hv0S, hv0min⟩ := hScompact.exists_isMinOn hSne
    (radialPolynomialEnergy_continuous p).continuousOn
  have hv0ne : v0 ≠ 0 := by
    intro h
    subst v0
    simpa [S] using hv0S
  let c := radialPolynomialEnergy p v0 / (p + 1 : ℝ)
  have hqpos : (0 : ℝ) < p + 1 := by positivity
  refine ⟨c, div_pos (radialPolynomialEnergy_pos p hv0ne) hqpos, ?_⟩
  intro v
  by_cases hv : v = 0
  · subst v
    simp [radialPolynomialEnergy]
  · let r : ℝ := ‖v‖
    have hrpos : 0 < r := norm_pos_iff.mpr hv
    let u : Fin (p + 1) → ℝ := r⁻¹ • v
    have huS : u ∈ S := by
      rw [Metric.mem_sphere, dist_zero_right]
      change ‖r⁻¹ • v‖ = 1
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hrpos]
      exact inv_mul_cancel₀ hrpos.ne'
    have hmin := hv0min huS
    have hscale := radialPolynomialEnergy_smul p r u
    have hru : r • u = v := by
      ext i
      simp [u, r, hrpos.ne']
    rw [hru] at hscale
    have hsum : ∑ i, (v i) ^ 2 ≤ (p + 1 : ℝ) * r ^ 2 := by
      calc
        ∑ i, (v i) ^ 2 ≤ ∑ _i : Fin (p + 1), r ^ 2 := by
          apply Finset.sum_le_sum
          intro i hi
          simpa [sq_abs, r] using
            (sq_le_sq₀ (abs_nonneg (v i)) (norm_nonneg v)).2
              (norm_le_pi_norm v i)
        _ = (p + 1 : ℝ) * r ^ 2 := by simp
    dsimp [c]
    calc
      radialPolynomialEnergy p v0 / (p + 1 : ℝ) * ∑ i, (v i) ^ 2
          = radialPolynomialEnergy p v0 *
              ((∑ i, (v i) ^ 2) / (p + 1 : ℝ)) := by ring
      _ ≤ radialPolynomialEnergy p v0 * r ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (radialPolynomialEnergy_pos p hv0ne).le
        exact (div_le_iff₀ hqpos).2 (by simpa [mul_comm] using hsum)
      _ ≤ radialPolynomialEnergy p u * r ^ 2 := by
        exact mul_le_mul_of_nonneg_right hmin (sq_nonneg r)
      _ = radialPolynomialEnergy p v := by
        rw [mul_comm, ← hscale]

/-- The same coercivity constant works in both signed-distance orientations.
The negative orientation merely changes coefficient `i` by the sign
`(-1)^i`, which preserves the sum of coefficient squares. -/
-- @node: signedRadialPolynomialEnergy_coercive
lemma signedRadialPolynomialEnergy_coercive (p : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : Bool, ∀ v : Fin (p + 1) → ℝ,
      c * ∑ i, (v i) ^ 2 ≤
        ∫ u in (0 : ℝ)..1,
          (∑ i, v i * (if t then u else -u) ^ (i : ℕ)) ^ 2 * u := by
  obtain ⟨c, hc, hcoercive⟩ := radialPolynomialEnergy_coercive p
  refine ⟨c, hc, ?_⟩
  intro t v
  cases t with
  | true =>
      simpa [radialPolynomialEnergy_eq_integral] using hcoercive v
  | false =>
      let w : Fin (p + 1) → ℝ := fun i => (-1 : ℝ) ^ (i : ℕ) * v i
      have hnorm : ∑ i, (w i) ^ 2 = ∑ i, (v i) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [w, mul_pow]
        rw [show ((-1 : ℝ) ^ (i : ℕ)) ^ 2 = 1 by
          rw [← pow_mul]; simp]
        ring
      have hpoly (u : ℝ) :
          ∑ i, w i * u ^ (i : ℕ) =
            ∑ i, v i * (-u) ^ (i : ℕ) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [w]
        rw [neg_pow]
        ring
      rw [← hnorm]
      refine (hcoercive w).trans_eq ?_
      rw [radialPolynomialEnergy_eq_integral]
      apply intervalIntegral.integral_congr
      intro u hu
      dsimp only
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [hpoly]

end Causalean.Stat.Nonparametric.LocalPolynomial
