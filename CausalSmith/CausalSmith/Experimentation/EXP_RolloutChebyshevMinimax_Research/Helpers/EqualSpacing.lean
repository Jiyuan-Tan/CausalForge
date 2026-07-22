/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Equal-spacing benchmark and no-extrapolation boundary
-/

import CausalSmith.Experimentation.EXP_RolloutChebyshevMinimax_Research.Helpers.EqualSpacingArithmetic
import CausalSmith.Experimentation.EXP_RolloutChebyshevMinimax_Research.Helpers.Amplification
import Mathlib.LinearAlgebra.Lagrange

open scoped BigOperators

namespace CausalSmith.Experimentation.RolloutChebyshev

-- @node: equalSchedule_injective
lemma equalSchedule_injective (beta : ℕ) (q : ℝ) (hbeta : 1 ≤ beta) (hq : 0 < q) :
    Function.Injective (equalSchedule beta q) := by
  intro a b hab
  have hbeta_pos_nat : 0 < beta := by omega
  have hbeta_ne : (beta : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hbeta_pos_nat)
  have hq_ne : q ≠ 0 := ne_of_gt hq
  have hreal : (a : ℝ) = (b : ℝ) := by
    dsimp [equalSchedule] at hab
    field_simp [hbeta_ne, hq_ne] at hab
    linarith
  exact Fin.ext (by exact_mod_cast hreal)

-- @node: equalSchedule_lagrange_basis_eval_one_le
lemma equalSchedule_lagrange_basis_eval_one_le (beta : ℕ) (q : ℝ)
    (hbeta : 1 ≤ beta) (hq : 0 < q ∧ q ≤ 1) (j : Fin (beta + 1)) :
    |(Lagrange.basis (Finset.univ : Finset (Fin (beta + 1))) (equalSchedule beta q) j).eval 1|
      ≤ ((beta : ℝ) / q) ^ beta /
        ((j.val.factorial : ℝ) * ((beta - j.val).factorial : ℝ)) := by
  classical
  let S : Finset (Fin (beta + 1)) := Finset.univ
  let p : Fin (beta + 1) → ℝ := equalSchedule beta q
  have hbeta_pos_nat : 0 < beta := by omega
  have hbeta_pos : 0 < (beta : ℝ) := by exact_mod_cast hbeta_pos_nat
  have hbeta_ne : (beta : ℝ) ≠ 0 := ne_of_gt hbeta_pos
  have hq_pos : 0 < q := hq.1
  have hq_ne : q ≠ 0 := ne_of_gt hq_pos
  have hcard : (S.erase j).card = beta := by simp [S]
  have hden_fin :
      (∏ m ∈ S.erase j, |(j.val : ℝ) - (m.val : ℝ)|) =
        (j.val.factorial : ℝ) * ((beta - j.val).factorial : ℝ) := by
    have hjle : j.val ≤ beta := Nat.le_of_lt_succ j.isLt
    calc
      (∏ m ∈ S.erase j, |(j.val : ℝ) - (m.val : ℝ)|)
          = ∏ m ∈ (Finset.Iic beta).erase j.val, |(j.val : ℝ) - (m : ℝ)| := by
            refine Finset.prod_bij (fun m _ => m.val) ?_ ?_ ?_ ?_
            · intro m hm
              rcases Finset.mem_erase.mp hm with ⟨hmne, _⟩
              exact Finset.mem_erase.mpr
                ⟨by exact fun h => hmne (Fin.ext h),
                  by simpa using Nat.le_of_lt_succ m.isLt⟩
            · intro a ha b hb hval
              exact Fin.ext hval
            · intro m hm
              rcases Finset.mem_erase.mp hm with ⟨hmne, hmle⟩
              refine ⟨⟨m, Nat.lt_succ_of_le (Finset.mem_Iic.mp hmle)⟩, ?_, rfl⟩
              exact Finset.mem_erase.mpr ⟨by exact fun h => hmne (congrArg Fin.val h), by simp [S]⟩
            · intro m hm
              rfl
      _ = (j.val.factorial : ℝ) * ((beta - j.val).factorial : ℝ) :=
            prod_Iic_erase_abs_sub_eq_factorial beta j.val hjle
  have hbasis :
      |(Lagrange.basis S p j).eval 1| =
        ∏ m ∈ S.erase j, |((p j - p m)⁻¹) * (1 - p m)| := by
    simp [S, p, Lagrange.basis, Lagrange.basisDivisor, Polynomial.eval_prod, Finset.abs_prod,
      abs_mul, abs_inv]
  have hfactor :
      ∀ m ∈ S.erase j,
        |((p j - p m)⁻¹) * (1 - p m)| ≤
          ((beta : ℝ) / q) * |(j.val : ℝ) - (m.val : ℝ)|⁻¹ := by
    intro m hm
    rcases Finset.mem_erase.mp hm with ⟨hmne, _⟩
    have hmle : (m.val : ℝ) ≤ (beta : ℝ) := by
      exact_mod_cast Nat.le_of_lt_succ m.isLt
    have hpm_le_one : p m ≤ 1 := by
      have hleq : q * (m.val : ℝ) / (beta : ℝ) ≤ q := by
        calc
          q * (m.val : ℝ) / (beta : ℝ) ≤ q * (beta : ℝ) / (beta : ℝ) := by
            gcongr
          _ = q := by field_simp [hbeta_ne]
      exact hleq.trans hq.2
    have hpm_nonneg : 0 ≤ p m := by
      dsimp [p, equalSchedule]
      positivity
    have hnum : |1 - p m| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith
    have hdiff_ne : (j.val : ℝ) - (m.val : ℝ) ≠ 0 := by
      intro hzero
      have hval : j.val = m.val := by exact_mod_cast sub_eq_zero.mp hzero
      exact hmne (Fin.ext hval.symm)
    have hpdiff : p j - p m =
        (q / (beta : ℝ)) * ((j.val : ℝ) - (m.val : ℝ)) := by
      dsimp [p, equalSchedule]
      ring
    have hscale_pos : 0 < q / (beta : ℝ) := div_pos hq_pos hbeta_pos
    calc
      |((p j - p m)⁻¹) * (1 - p m)|
          = |1 - p m| * |p j - p m|⁻¹ := by
            rw [abs_mul, abs_inv, mul_comm]
      _ ≤ 1 * |p j - p m|⁻¹ := by
            exact mul_le_mul_of_nonneg_right hnum (inv_nonneg.mpr (abs_nonneg _))
      _ = ((beta : ℝ) / q) * |(j.val : ℝ) - (m.val : ℝ)|⁻¹ := by
            rw [hpdiff, abs_mul, abs_of_pos hscale_pos]
            field_simp [hbeta_ne, hq_ne, hdiff_ne]
  calc
    |(Lagrange.basis (Finset.univ : Finset (Fin (beta + 1))) (equalSchedule beta q) j).eval 1|
        = |(Lagrange.basis S p j).eval 1| := by rfl
    _ = ∏ m ∈ S.erase j, |((p j - p m)⁻¹) * (1 - p m)| := hbasis
    _ ≤ ∏ m ∈ S.erase j, ((beta : ℝ) / q) * |(j.val : ℝ) - (m.val : ℝ)|⁻¹ := by
          refine Finset.prod_le_prod ?_ hfactor
          intro m hm
          positivity
    _ = ((beta : ℝ) / q) ^ beta *
          (∏ m ∈ S.erase j, |(j.val : ℝ) - (m.val : ℝ)|)⁻¹ := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, hcard, Finset.prod_inv_distrib]
    _ = ((beta : ℝ) / q) ^ beta /
          ((j.val.factorial : ℝ) * ((beta - j.val).factorial : ℝ)) := by
          rw [hden_fin]
          ring

-- @node: prop:equal-spacing-benchmark
/-- Equal-spacing benchmark: `A_β(p^eq(β,q)) ≤ 9 (β/q)^{2β}` for every integer `β ≥ 1` and every
`q ∈ (0,1]` (the universal constant `C_eq = 9`). Constructed via Lagrange-basis weights on the
equal grid with the ℓ¹ bound `∑|w_j| ≤ 3 (β/q)^β`, plus the endpoint case at `q = 1`.
The leading conjunct `∀ j, p^eq(β,q) j ∈ [0,1]` realizes the schedule's core space
`p^eq(β,q) ∈ [0,1]^(β+1)` (the range clause the note states for the benchmark grid); the second
conjunct is the amplification bound proper. The range predicate `hq : 0 < q ∧ q ≤ 1` realizes the
core space `q ∈ (0,1]`.
@realizes p^eq(beta,q)(range [0,1]^(β+1): Icc conjunct on conclusion; β≥1, q∈(0,1])
@realizes q(carrier ℝ; range 0 < q ≤ 1 via hq) -/
lemma equal_spacing_benchmark (beta : ℕ) (q : ℝ) (hbeta : 1 ≤ beta)
    (hq : 0 < q ∧ q ≤ 1) :  -- @realizes q(0 < q ∧ q ≤ 1)
    (∀ j, equalSchedule beta q j ∈ Set.Icc (0 : ℝ) 1) ∧  -- @realizes p^eq(beta,q)(∈[0,1]^(β+1))
      amplification beta beta (equalSchedule beta q) ≤ 9 * ((beta : ℝ) / q) ^ (2 * beta) := by
  classical
  have hbeta_pos_nat : 0 < beta := by omega
  have hbeta_pos : 0 < (beta : ℝ) := by exact_mod_cast hbeta_pos_nat
  have hbeta_ne : (beta : ℝ) ≠ 0 := ne_of_gt hbeta_pos
  have hq_pos : 0 < q := hq.1
  have hq_ne : q ≠ 0 := ne_of_gt hq_pos
  have hrange : ∀ j, equalSchedule beta q j ∈ Set.Icc (0 : ℝ) 1 := by
    intro j
    constructor
    · dsimp [equalSchedule]
      positivity
    · have hjle : (j.val : ℝ) ≤ (beta : ℝ) := by
        exact_mod_cast Nat.le_of_lt_succ j.isLt
      have hleq : q * (j.val : ℝ) / (beta : ℝ) ≤ q := by
        calc
          q * (j.val : ℝ) / (beta : ℝ) ≤ q * (beta : ℝ) / (beta : ℝ) := by
            gcongr
          _ = q := by field_simp [hbeta_ne]
      exact hleq.trans hq.2
  refine ⟨hrange, ?_⟩
  let p : Fin (beta + 1) → ℝ := equalSchedule beta q
  let w : Fin (beta + 1) → ℝ := fun j =>
    (Lagrange.basis (Finset.univ : Finset (Fin (beta + 1))) p j).eval 1 -
      (Lagrange.basis (Finset.univ : Finset (Fin (beta + 1))) p j).eval 0
  have hp : Function.Injective p := by
    simpa [p] using equalSchedule_injective beta q hbeta hq_pos
  have hw : UnbiasedWeights beta beta p w := by
    simpa [w] using lagrange_endpoint_weights_unbiased beta beta p (le_refl beta) hp
  have hA_le : amplification beta beta p ≤ (∑ j, |w j|) ^ 2 := by
    unfold amplification
    apply csInf_le
    · use 0
      intro x hx
      rcases hx with ⟨w', hw', rfl⟩
      positivity
    · exact ⟨w, hw, rfl⟩
  have hy_ge_one : 1 ≤ (beta : ℝ) / q := by
    rw [le_div_iff₀ hq_pos]
    have hbeta_one : (1 : ℝ) ≤ (beta : ℝ) := by exact_mod_cast hbeta
    nlinarith [hq.2]
  have hy_nonneg : 0 ≤ (beta : ℝ) / q := le_trans (by norm_num) hy_ge_one
  have hsum_eval1 :
      (∑ j : Fin (beta + 1),
        |(Lagrange.basis (Finset.univ : Finset (Fin (beta + 1))) p j).eval 1|)
        ≤ 2 * ((beta : ℝ) / q) ^ beta := by
    calc
      (∑ j : Fin (beta + 1),
        |(Lagrange.basis (Finset.univ : Finset (Fin (beta + 1))) p j).eval 1|)
          ≤ ∑ j : Fin (beta + 1),
              ((beta : ℝ) / q) ^ beta /
                ((j.val.factorial : ℝ) * ((beta - j.val).factorial : ℝ)) := by
            refine Finset.sum_le_sum ?_
            intro j hj
            simpa [p] using equalSchedule_lagrange_basis_eval_one_le beta q hbeta hq j
      _ = ((beta : ℝ) / q) ^ beta *
            (∑ j : Fin (beta + 1),
              (1 : ℝ) / ((j.val.factorial : ℝ) * ((beta - j.val).factorial : ℝ))) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro j hj
            ring
      _ ≤ ((beta : ℝ) / q) ^ beta * 2 := by
            exact mul_le_mul_of_nonneg_left (factorial_reciprocal_sum_le_two beta hbeta)
              (pow_nonneg hy_nonneg beta)
      _ = 2 * ((beta : ℝ) / q) ^ beta := by ring
  have hsum_eval0 :
      (∑ j : Fin (beta + 1),
        |(Lagrange.basis (Finset.univ : Finset (Fin (beta + 1))) p j).eval 0|) = 1 := by
    let z : Fin (beta + 1) := 0
    have hpz : p z = 0 := by simp [p, equalSchedule]
    calc
      (∑ j : Fin (beta + 1),
        |(Lagrange.basis (Finset.univ : Finset (Fin (beta + 1))) p j).eval 0|)
          = ∑ j : Fin (beta + 1), if j = z then (1 : ℝ) else 0 := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            by_cases hz : j = z
            · subst j
              have heval :
                  (Lagrange.basis (Finset.univ : Finset (Fin (beta + 1))) p z).eval (p z) =
                    1 := by
                simpa using Lagrange.eval_basis_self hp.injOn (Finset.mem_univ z)
              have hzero :
                  (Lagrange.basis (Finset.univ : Finset (Fin (beta + 1))) p z).eval 0 =
                    1 := by
                simpa [hpz] using heval
              simp [hzero]
            · have heval :
                  (Lagrange.basis (Finset.univ : Finset (Fin (beta + 1))) p j).eval (p z) =
                    0 := by
                simpa using Lagrange.eval_basis_of_ne hz (Finset.mem_univ z)
              have hzero :
                  (Lagrange.basis (Finset.univ : Finset (Fin (beta + 1))) p j).eval 0 =
                    0 := by
                simpa [hpz] using heval
              simp [hzero, hz]
      _ = 1 := by
            norm_num [Finset.sum_ite_eq', z]
  have hsumw : (∑ j, |w j|) ≤ 3 * ((beta : ℝ) / q) ^ beta := by
    calc
      (∑ j, |w j|)
          ≤ ∑ j : Fin (beta + 1),
              (|(Lagrange.basis (Finset.univ : Finset (Fin (beta + 1))) p j).eval 1| +
                |(Lagrange.basis (Finset.univ : Finset (Fin (beta + 1))) p j).eval 0|) := by
            refine Finset.sum_le_sum ?_
            intro j hj
            dsimp [w]
            simpa using (abs_sub_le
              ((Lagrange.basis (Finset.univ : Finset (Fin (beta + 1))) p j).eval 1)
              0
              ((Lagrange.basis (Finset.univ : Finset (Fin (beta + 1))) p j).eval 0))
      _ =
          (∑ j : Fin (beta + 1),
            |(Lagrange.basis (Finset.univ : Finset (Fin (beta + 1))) p j).eval 1|) +
          (∑ j : Fin (beta + 1),
            |(Lagrange.basis (Finset.univ : Finset (Fin (beta + 1))) p j).eval 0|) := by
            rw [Finset.sum_add_distrib]
      _ ≤ 2 * ((beta : ℝ) / q) ^ beta + 1 := by
            exact add_le_add hsum_eval1 (le_of_eq hsum_eval0)
      _ ≤ 3 * ((beta : ℝ) / q) ^ beta := by
            have hpow_ge_one : 1 ≤ ((beta : ℝ) / q) ^ beta := one_le_pow₀ hy_ge_one
            nlinarith
  have hsumw_nonneg : 0 ≤ ∑ j, |w j| := by positivity
  have hbound_nonneg : 0 ≤ 3 * ((beta : ℝ) / q) ^ beta := by positivity
  calc
    amplification beta beta (equalSchedule beta q) = amplification beta beta p := by rfl
    _ ≤ (∑ j, |w j|) ^ 2 := hA_le
    _ ≤ (3 * ((beta : ℝ) / q) ^ beta) ^ 2 :=
          sq_le_sq' (by linarith) hsumw
    _ = 9 * ((beta : ℝ) / q) ^ (2 * beta) := by
          calc
            (3 * ((beta : ℝ) / q) ^ beta) ^ 2
                = 9 * (((beta : ℝ) / q) ^ beta) ^ 2 := by ring
            _ = 9 * ((beta : ℝ) / q) ^ (beta * 2) := by rw [pow_mul]
            _ = 9 * ((beta : ℝ) / q) ^ (2 * beta) := by ring_nf

end CausalSmith.Experimentation.RolloutChebyshev
