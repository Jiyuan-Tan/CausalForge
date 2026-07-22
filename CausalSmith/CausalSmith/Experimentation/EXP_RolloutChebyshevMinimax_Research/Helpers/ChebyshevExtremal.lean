/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Chebyshev extremal helpers: exterior-point growth and endpoint bounds

`lem:chebyshev-exterior-extremal` (classical alternation proof, feasible) and
`lem:continuous-chebyshev-endpoint-bound`.
-/

import CausalSmith.Experimentation.EXP_RolloutChebyshevMinimax_Research.Basic
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Analysis.SpecialFunctions.Sqrt

open scoped BigOperators

namespace CausalSmith.Experimentation.RolloutChebyshev

-- @node: neg_one_pow_mul_le_of_abs_le_one
lemma neg_one_pow_mul_le_of_abs_le_one {a : ℝ} {i : ℕ} (ha : |a| ≤ 1) :
    (-1 : ℝ) ^ i * a ≤ 1 := by
  apply le_of_abs_le
  rwa [abs_mul, abs_neg_one_pow, one_mul]

-- @node: chebyshev_exterior_lagrange_coeff_nonneg
lemma chebyshev_exterior_lagrange_coeff_nonneg {n i : ℕ} (hi : i ∈ Finset.Iic n)
    {x0 : ℝ} (hx0 : 1 < x0) :
    0 ≤ (-1 : ℝ) ^ i *
      (Lagrange.basis (Finset.Iic n) (Polynomial.Chebyshev.node n) i).eval x0 := by
  classical
  rw [Lagrange.basis, Polynomial.eval_prod]
  simp only [Lagrange.basisDivisor, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
    Polynomial.eval_X]
  rw [Finset.prod_mul_distrib]
  have hnum_pos :
      0 < ∏ j ∈ (Finset.Iic n).erase i,
        (x0 - Polynomial.Chebyshev.node n j) := by
    refine Finset.prod_pos ?_
    intro j hj
    have hnode_le_one : Polynomial.Chebyshev.node n j ≤ 1 :=
      (Polynomial.Chebyshev.node_mem_Icc (n := n) (i := j)).2
    linarith
  have hden_signed_pos :
      0 < (-1 : ℝ) ^ i *
        ∏ j ∈ (Finset.Iic n).erase i,
          (Polynomial.Chebyshev.node n i - Polynomial.Chebyshev.node n j) := by
    have hi_le : i ≤ n := Finset.mem_Iic.mp hi
    have hleft :
        0 < ∏ j ∈ Finset.range i,
          ((-1 : ℝ) *
            (Polynomial.Chebyshev.node n i - Polynomial.Chebyshev.node n j)) := by
      refine Finset.prod_pos ?_
      intro j hj
      have hji : j < i := Finset.mem_range.mp hj
      have hlt : Polynomial.Chebyshev.node n i < Polynomial.Chebyshev.node n j :=
        Polynomial.Chebyshev.node_lt hi_le hji
      nlinarith
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range] at hleft
    have hright :
        0 < ∏ j ∈ Finset.Ioc i n,
          (Polynomial.Chebyshev.node n i - Polynomial.Chebyshev.node n j) := by
      refine Finset.prod_pos ?_
      intro j hj
      have hji : i < j := (Finset.mem_Ioc.mp hj).1
      have hjn : j ≤ n := (Finset.mem_Ioc.mp hj).2
      have hlt : Polynomial.Chebyshev.node n j < Polynomial.Chebyshev.node n i :=
        Polynomial.Chebyshev.node_lt hjn hji
      linarith
    have hunion :
        (Finset.Iic n).erase i = Finset.range i ∪ Finset.Ioc i n := by
      ext j
      simp only [Finset.mem_erase, Finset.mem_Iic, Finset.mem_union, Finset.mem_range,
        Finset.mem_Ioc]
      omega
    have hdisjoint : Disjoint (Finset.range i) (Finset.Ioc i n) := by
      rw [Finset.disjoint_iff_ne]
      intro a ha b hb
      have hai : a < i := Finset.mem_range.mp ha
      have hib : i < b := (Finset.mem_Ioc.mp hb).1
      omega
    rw [hunion, Finset.prod_union hdisjoint]
    rw [← mul_assoc]
    exact mul_pos hleft hright
  have hden_inv_signed_pos :
      0 < (-1 : ℝ) ^ i *
        ∏ j ∈ (Finset.Iic n).erase i,
          (Polynomial.Chebyshev.node n i - Polynomial.Chebyshev.node n j)⁻¹ := by
    have hi_le : i ≤ n := Finset.mem_Iic.mp hi
    have hleft :
        0 < ∏ j ∈ Finset.range i,
          ((-1 : ℝ) *
            (Polynomial.Chebyshev.node n i - Polynomial.Chebyshev.node n j)⁻¹) := by
      refine Finset.prod_pos ?_
      intro j hj
      have hji : j < i := Finset.mem_range.mp hj
      have hlt : Polynomial.Chebyshev.node n i < Polynomial.Chebyshev.node n j :=
        Polynomial.Chebyshev.node_lt hi_le hji
      have hinv_neg : (Polynomial.Chebyshev.node n i -
          Polynomial.Chebyshev.node n j)⁻¹ < 0 := inv_lt_zero'.mpr (by linarith)
      nlinarith
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range] at hleft
    have hright :
        0 < ∏ j ∈ Finset.Ioc i n,
          (Polynomial.Chebyshev.node n i - Polynomial.Chebyshev.node n j)⁻¹ := by
      refine Finset.prod_pos ?_
      intro j hj
      have hji : i < j := (Finset.mem_Ioc.mp hj).1
      have hjn : j ≤ n := (Finset.mem_Ioc.mp hj).2
      have hlt : Polynomial.Chebyshev.node n j < Polynomial.Chebyshev.node n i :=
        Polynomial.Chebyshev.node_lt hjn hji
      exact inv_pos.mpr (by linarith)
    have hunion :
        (Finset.Iic n).erase i = Finset.range i ∪ Finset.Ioc i n := by
      ext j
      simp only [Finset.mem_erase, Finset.mem_Iic, Finset.mem_union, Finset.mem_range,
        Finset.mem_Ioc]
      omega
    have hdisjoint : Disjoint (Finset.range i) (Finset.Ioc i n) := by
      rw [Finset.disjoint_iff_ne]
      intro a ha b hb
      have hai : a < i := Finset.mem_range.mp ha
      have hib : i < b := (Finset.mem_Ioc.mp hb).1
      omega
    rw [hunion, Finset.prod_union hdisjoint]
    rw [← mul_assoc]
    exact mul_pos hleft hright
  have hprod_pos :
      0 < ((-1 : ℝ) ^ i *
        ∏ j ∈ (Finset.Iic n).erase i,
          (Polynomial.Chebyshev.node n i - Polynomial.Chebyshev.node n j)⁻¹) *
        ∏ j ∈ (Finset.Iic n).erase i,
          (x0 - Polynomial.Chebyshev.node n j) :=
    mul_pos hden_inv_signed_pos hnum_pos
  refine le_of_lt ?_
  convert hprod_pos using 1
  ring

-- @node: lem:chebyshev-exterior-extremal
/-- Classical exterior-point Chebyshev extremal inequality (Rivlin1974): every real polynomial
`P` of degree ≤ β with `sup_{[-1,1]} |P| ≤ 1` satisfies `|P(x₀)| ≤ T_β(x₀)` for every `x₀ > 1`.
The formal proof uses the equivalent Lagrange-interpolation form of the alternation argument:
the exterior evaluation functional has the Chebyshev alternating signs on the extremal nodes. -/
lemma chebyshev_exterior_extremal (beta : ℕ) (_hbeta : 1 ≤ beta) (P : Polynomial ℝ)
    (hdeg : P.natDegree ≤ beta) (hbound : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → |P.eval x| ≤ 1)
    (x0 : ℝ) (hx0 : 1 < x0) :
    |P.eval x0| ≤ (Polynomial.Chebyshev.T ℝ (beta : ℤ)).eval x0 := by
  classical
  let s : Finset ℕ := Finset.Iic beta
  let v : ℕ → ℝ := Polynomial.Chebyshev.node beta
  let T : Polynomial ℝ := Polynomial.Chebyshev.T ℝ (beta : ℤ)
  have hvs : Set.InjOn v s := by
    simpa [s, v, Nat.range_succ_eq_Iic] using
      (Polynomial.Chebyshev.strictAntiOn_node beta).injOn
  have hcard : s.card = beta + 1 := by simp [s]
  have hTdegree : T.degree < (s.card : WithBot ℕ) := by
    dsimp [T]
    rw [hcard, Polynomial.Chebyshev.degree_T, Int.natAbs_natCast]
    exact WithBot.coe_lt_coe.mpr (Nat.lt_succ_self beta)
  have upper :
      ∀ Q : Polynomial ℝ, Q.natDegree ≤ beta →
        (∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → |Q.eval x| ≤ 1) →
          Q.eval x0 ≤ T.eval x0 := by
    intro Q hQdeg hQbound
    have hQdegree : Q.degree < (s.card : WithBot ℕ) := by
      rw [hcard]
      exact lt_of_le_of_lt (show Q.degree ≤ (Q.natDegree : WithBot ℕ) from
          Polynomial.degree_le_natDegree)
        (WithBot.coe_lt_coe.mpr (Nat.lt_succ_of_le hQdeg))
    have hQinterp := Lagrange.eq_interpolate (s := s) (v := v) hvs hQdegree
    have hTinterp := Lagrange.eq_interpolate (s := s) (v := v) hvs hTdegree
    have hQeval :
        Q.eval x0 = ∑ i ∈ s, Q.eval (v i) * (Lagrange.basis s v i).eval x0 := by
      have h := congrArg (fun R : Polynomial ℝ => R.eval x0) hQinterp
      simpa [Lagrange.interpolate_apply, Polynomial.eval_finset_sum, Polynomial.eval_mul,
        mul_comm, mul_left_comm, mul_assoc] using h
    have hTeval :
        T.eval x0 = ∑ i ∈ s, T.eval (v i) * (Lagrange.basis s v i).eval x0 := by
      have h := congrArg (fun R : Polynomial ℝ => R.eval x0) hTinterp
      simpa [Lagrange.interpolate_apply, Polynomial.eval_finset_sum, Polynomial.eval_mul,
        mul_comm, mul_left_comm, mul_assoc] using h
    rw [hQeval, hTeval]
    refine Finset.sum_le_sum ?_
    intro i hi
    have hi_le : i ≤ beta := by simpa [s] using hi
    have hnode_mem : v i ∈ Set.Icc (-1 : ℝ) 1 := by
      simpa [v] using (Polynomial.Chebyshev.node_mem_Icc (n := beta) (i := i))
    have hcoeff_nonneg :
        0 ≤ (-1 : ℝ) ^ i * (Lagrange.basis s v i).eval x0 := by
      simpa [s, v] using
        (chebyshev_exterior_lagrange_coeff_nonneg (n := beta) (i := i)
          (by simpa [s] using hi) hx0)
    calc
      Q.eval (v i) * (Lagrange.basis s v i).eval x0
          = ((-1 : ℝ) ^ i * Q.eval (v i)) *
              ((-1 : ℝ) ^ i * (Lagrange.basis s v i).eval x0) := by
            have hsignsq : (-1 : ℝ) ^ i * (-1 : ℝ) ^ i = 1 := by
              rw [← pow_add]
              have heven : Even (i + i) := ⟨i, by omega⟩
              simp [heven.neg_one_pow]
            calc
              Q.eval (v i) * (Lagrange.basis s v i).eval x0
                  = 1 * (Q.eval (v i) * (Lagrange.basis s v i).eval x0) := by ring
              _ = (((-1 : ℝ) ^ i) * ((-1 : ℝ) ^ i)) *
                    (Q.eval (v i) * (Lagrange.basis s v i).eval x0) := by rw [hsignsq]
              _ = ((-1 : ℝ) ^ i * Q.eval (v i)) *
                    ((-1 : ℝ) ^ i * (Lagrange.basis s v i).eval x0) := by ring
      _ ≤ 1 * ((-1 : ℝ) ^ i * (Lagrange.basis s v i).eval x0) := by
            exact mul_le_mul_of_nonneg_right
              (neg_one_pow_mul_le_of_abs_le_one (hQbound (v i) hnode_mem))
              hcoeff_nonneg
      _ = T.eval (v i) * (Lagrange.basis s v i).eval x0 := by
            rw [one_mul]
            change (-1 : ℝ) ^ i * (Lagrange.basis s v i).eval x0 =
              (Polynomial.Chebyshev.T ℝ (beta : ℕ)).eval
                (Polynomial.Chebyshev.node beta i) * (Lagrange.basis s v i).eval x0
            rw [Polynomial.Chebyshev.eval_T_real_node
              (show i ∈ Finset.Iic beta from by simpa [s] using hi)]
  have hupper := upper P hdeg hbound
  have hneg_upper : (-P).eval x0 ≤ T.eval x0 := by
    refine upper (-P) ?_ ?_
    · simpa using hdeg
    · intro x hx
      simpa using hbound x hx
  have hupper' : P.eval x0 ≤ (Polynomial.Chebyshev.T ℝ (beta : ℤ)).eval x0 := by
    simpa [T] using hupper
  have hneg_upper' : -P.eval x0 ≤ (Polynomial.Chebyshev.T ℝ (beta : ℤ)).eval x0 := by
    simpa [T] using hneg_upper
  exact abs_le.mpr ⟨by linarith, hupper'⟩

end CausalSmith.Experimentation.RolloutChebyshev
