import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Data.Nat.Choose.Cast

namespace CausalSmith.Stat.DiscreteAteMinimaxLoggap

open Polynomial
open scoped BigOperators

private lemma taylorChebyshev_coeff_formula (M j : ℕ) :
    (Polynomial.taylor 1 (Polynomial.Chebyshev.T ℝ M)).coeff j =
      ((Polynomial.derivative : ℝ[X] → ℝ[X])^[j]
        (Polynomial.Chebyshev.T ℝ M)).eval 1 / (j.factorial : ℝ) := by
  rw [Polynomial.taylor_coeff]
  have hpoly : j.factorial • (Polynomial.hasseDeriv j)
      (Polynomial.Chebyshev.T ℝ M) =
      ((Polynomial.derivative : ℝ[X] → ℝ[X])^[j]
        (Polynomial.Chebyshev.T ℝ M)) := by
    exact congrFun (Polynomial.factorial_smul_hasseDeriv (R := ℝ) j)
      (Polynomial.Chebyshev.T ℝ M)
  have he := congrArg (fun p : ℝ[X] => p.eval 1) hpoly
  simp only [nsmul_eq_mul] at he
  rw [eq_div_iff]
  · simpa [mul_comm] using he
  · exact_mod_cast j.factorial_ne_zero

private lemma taylorChebyshev_coeff_recurrence (M j : ℕ) :
    ((j+1 : ℕ) : ℝ) * (2*j+1 : ℕ) *
        (Polynomial.taylor 1 (Polynomial.Chebyshev.T ℝ M)).coeff (j+1) =
      ((M : ℝ)^2 - (j : ℝ)^2) *
        (Polynomial.taylor 1 (Polynomial.Chebyshev.T ℝ M)).coeff j := by
  rw [taylorChebyshev_coeff_formula, taylorChebyshev_coeff_formula]
  have hr := Polynomial.Chebyshev.iterate_derivative_T_eval_one_recurrence
    (R := ℝ) (M : ℤ) j
  push_cast at hr
  rw [Nat.factorial_succ]
  have hfac : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
  have hj1 : ((j+1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp
  push_cast
  linear_combination ((j : ℝ) + 1) * (j.factorial : ℝ) * hr

private noncomputable def shiftedCoeff (M j : ℕ) : ℝ :=
  (-1 : ℝ)^j * (M : ℝ) / (M+j) * Nat.choose (M+j) (2*j) * 4^j

private lemma choose_shift (M j : ℕ) (hj : j < M) :
    Nat.choose (M+j+1) (2*j+2) * (2*j+2) * (2*j+1) =
      (M+j+1) * (M-j) * Nat.choose (M+j) (2*j) := by
  have hsub : M + j + 1 - (2 * j + 1) = M - j := by omega
  calc
    Nat.choose (M+j+1) (2*j+2) * (2*j+2) * (2*j+1)
        = (Nat.choose (M+j+1) (2*j+1) *
            (M+j+1-(2*j+1))) * (2*j+1) := by
              rw [Nat.choose_succ_right_eq]
    _ = (Nat.choose (M+j+1) (2*j+1) * (2*j+1)) * (M-j) := by
          rw [hsub]
          ac_rfl
    _ = ((M+j+1) * Nat.choose (M+j) (2*j)) * (M-j) := by
          rw [← Nat.add_one_mul_choose_eq]
    _ = (M+j+1) * (M-j) * Nat.choose (M+j) (2*j) := by ac_rfl

private lemma shiftedCoeff_recurrence (M j : ℕ) (hj : j < M) :
    ((j+1 : ℕ) : ℝ) * (2*j+1 : ℕ) * shiftedCoeff M (j+1) =
      -2 * ((M : ℝ)^2 - (j : ℝ)^2) * shiftedCoeff M j := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (Nat.zero_lt_of_lt hj)
  have hd0 : (0 : ℝ) < M + j := by positivity
  have hd1 : (0 : ℝ) < M + j + 1 := by positivity
  have hc := congrArg (fun n : ℕ => (n : ℝ)) (choose_shift M j hj)
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at hc
  rw [Nat.cast_sub (Nat.le_of_lt hj)] at hc
  let C1 : ℝ := Nat.choose (M+j+1) (2*j+2)
  let C0 : ℝ := Nat.choose (M+j) (2*j)
  change C1 * (2*(j:ℝ)+2) * (2*(j:ℝ)+1) =
    ((M:ℝ)+(j:ℝ)+1) * ((M:ℝ)-(j:ℝ)) * C0 at hc
  have core :
      ((j+1 : ℕ) : ℝ) * (2*j+1 : ℕ) *
          ((Nat.choose (M+j+1) (2*j+2) : ℝ) / (M+j+1)) * 4 =
        2 * ((M : ℝ)^2 - (j : ℝ)^2) *
          ((Nat.choose (M+j) (2*j) : ℝ) / (M+j)) := by
    push_cast
    change ((j:ℝ)+1) * (2*(j:ℝ)+1) *
        (C1 / ((M:ℝ)+(j:ℝ)+1)) * 4 =
      2 * ((M:ℝ)^2-(j:ℝ)^2) * (C0 / ((M:ℝ)+(j:ℝ)))
    calc
      ((j:ℝ)+1) * (2*(j:ℝ)+1) * (C1 / ((M:ℝ)+(j:ℝ)+1)) * 4
          = 2 * (C1 * (2*(j:ℝ)+2) * (2*(j:ℝ)+1)) /
              ((M:ℝ)+(j:ℝ)+1) := by ring
      _ = 2 * ((((M:ℝ)+(j:ℝ)+1) * ((M:ℝ)-(j:ℝ)) * C0) /
              ((M:ℝ)+(j:ℝ)+1)) := by rw [hc]; ring
      _ = 2 * ((M:ℝ)-(j:ℝ)) * C0 := by field_simp
      _ = 2 * ((M:ℝ)^2-(j:ℝ)^2) *
            (C0 / ((M:ℝ)+(j:ℝ))) := by field_simp; ring
  rw [shiftedCoeff, shiftedCoeff]
  push_cast
  rw [show M + (j + 1) = M + j + 1 by omega]
  rw [show 2 * (j + 1) = 2 * j + 2 by omega]
  rw [pow_succ, pow_succ]
  push_cast at core
  have hc' := congrArg
    (fun z : ℝ => -(M : ℝ) * (-1 : ℝ)^j * 4^j * z) core
  convert hc' using 1 <;>
    simp only [Nat.add_comm, Nat.add_assoc, Nat.mul_comm] <;> ring

private noncomputable def shiftedTaylorCoeff (M j : ℕ) : ℝ :=
  (Polynomial.taylor 1 (Polynomial.Chebyshev.T ℝ M)).coeff j * (-2 : ℝ)^j

private lemma shiftedTaylorCoeff_recurrence (M j : ℕ) :
    ((j+1 : ℕ) : ℝ) * (2*j+1 : ℕ) * shiftedTaylorCoeff M (j+1) =
      -2 * ((M : ℝ)^2 - (j : ℝ)^2) * shiftedTaylorCoeff M j := by
  have hr := taylorChebyshev_coeff_recurrence M j
  rw [shiftedTaylorCoeff, shiftedTaylorCoeff, pow_succ]
  push_cast at hr ⊢
  linear_combination (-2 : ℝ)^j * (-2) * hr

private lemma shiftedTaylorCoeff_eq {M : ℕ} (hM : 0 < M) {j : ℕ} (hj : j ≤ M) :
    shiftedTaylorCoeff M j = shiftedCoeff M j := by
  induction j with
  | zero =>
      rw [shiftedTaylorCoeff, shiftedCoeff]
      simp
      have hMn : (M : ℝ) ≠ 0 := by positivity
      field_simp
  | succ j ih =>
      have hjlt : j < M := by omega
      have hb := shiftedTaylorCoeff_recurrence M j
      have hs := shiftedCoeff_recurrence M j hjlt
      have ih' := ih (by omega)
      have hfac : ((j+1 : ℕ) : ℝ) * (2*j+1 : ℕ) ≠ 0 := by positivity
      apply (mul_left_cancel₀ hfac)
      rw [ih'] at hb
      exact hb.trans hs.symm

/-- Explicit coefficient expansion of the shifted Chebyshev polynomial. -/
lemma shiftedChebyshevExpansion (M : ℕ) (x : ℝ) :
    (Polynomial.Chebyshev.T ℝ M).eval (1 - 2 * x) =
      1 + ∑ j ∈ Finset.Icc 1 M,
        (-1 : ℝ) ^ j * (M : ℝ) / (M + j) *
          Nat.choose (M + j) (2 * j) * 4 ^ j * x ^ j := by
  by_cases hM : M = 0
  · subst M
    simp
  have hMp : 0 < M := Nat.pos_of_ne_zero hM
  let p := Polynomial.taylor 1 (Polynomial.Chebyshev.T ℝ M)
  have hdeg : p.natDegree = M := by
    dsimp [p]
    simp
  calc
    (Polynomial.Chebyshev.T ℝ M).eval (1 - 2*x) = p.eval (-2*x) := by
      rw [Polynomial.taylor_eval]
      congr 2
      ring
    _ = ∑ j ∈ Finset.range (M+1), p.coeff j * (-2*x)^j := by
      rw [Polynomial.eval_eq_sum_range, hdeg]
    _ = ∑ j ∈ Finset.range (M+1), shiftedTaylorCoeff M j * x^j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [shiftedTaylorCoeff]
      dsimp [p]
      rw [mul_pow]
      ring
    _ = ∑ j ∈ Finset.range (M+1), shiftedCoeff M j * x^j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [shiftedTaylorCoeff_eq hMp (by simpa using hj)]
    _ = 1 + ∑ j ∈ Finset.Icc 1 M, shiftedCoeff M j * x^j := by
      have hs : Finset.range (M+1) = insert 0 (Finset.Icc 1 M) := by
        ext j
        simp
        omega
      rw [hs, Finset.sum_insert (by simp)]
      simp [shiftedCoeff, hM]
    _ = 1 + ∑ j ∈ Finset.Icc 1 M,
        (-1 : ℝ) ^ j * (M : ℝ) / (M + j) *
          Nat.choose (M + j) (2 * j) * 4 ^ j * x ^ j := by
      rfl

end CausalSmith.Stat.DiscreteAteMinimaxLoggap
