/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Chebyshev endpoint growth

`lem:continuous-chebyshev-endpoint-bound`, split from `ChebyshevExtremal` so the exterior
alternation proof and the endpoint-growth algebra remain separately checkable.
-/

import CausalSmith.Experimentation.EXP_RolloutChebyshevMinimax_Research.Helpers.ChebyshevExtremal

open scoped BigOperators

namespace CausalSmith.Experimentation.RolloutChebyshev

-- @node: chebyshev_eval_eq_lambda_average
lemma chebyshev_eval_eq_lambda_average (n : ℕ) (x : ℝ) (hx : 1 ≤ x) :
    (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval x =
      ((x + Real.sqrt (x ^ 2 - 1)) ^ n + ((x + Real.sqrt (x ^ 2 - 1)) ^ n)⁻¹) / 2 := by
  let a := Real.arcosh x
  have hcosh : Real.cosh a = x := by simpa [a] using Real.cosh_arcosh hx
  have hexp : Real.exp a = x + Real.sqrt (x ^ 2 - 1) := by
    simpa [a] using Real.exp_arcosh hx
  calc
    (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval x
        = (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval (Real.cosh a) := by rw [hcosh]
    _ = Real.cosh ((n : ℤ) * a) := by simp
    _ = (Real.exp ((n : ℤ) * a) + Real.exp (-((n : ℤ) * a))) / 2 := by
          rw [Real.cosh_eq]
    _ = ((x + Real.sqrt (x ^ 2 - 1)) ^ n +
          ((x + Real.sqrt (x ^ 2 - 1)) ^ n)⁻¹) / 2 := by
          rw [Real.exp_neg]
          have hcast : ((n : ℤ) : ℝ) = (n : ℝ) := by norm_num
          rw [hcast, Real.exp_nat_mul, hexp]

-- @node: endpoint_lambda_mono
lemma endpoint_lambda_mono {q qmax : ℝ} (hq : 0 < q) (hqq : q ≤ qmax)
    (hqmax_lt : qmax < 1) :
    (2 / qmax - 1) + Real.sqrt ((2 / qmax - 1) ^ 2 - 1) ≤
      (2 / q - 1) + Real.sqrt ((2 / q - 1) ^ 2 - 1) := by
  have hqmax_pos : 0 < qmax := lt_of_lt_of_le hq hqq
  let xq := 2 / q - 1
  let xm := 2 / qmax - 1
  have hxm_pos : 0 < xm := by
    have hdiv : 1 < 1 / qmax := one_lt_one_div hqmax_pos hqmax_lt
    dsimp [xm]
    nlinarith [show 2 / qmax = 2 * (1 / qmax) by ring]
  have hxm_one : 1 ≤ xm := by
    have hdiv : 1 < 1 / qmax := one_lt_one_div hqmax_pos hqmax_lt
    dsimp [xm]
    nlinarith [show 2 / qmax = 2 * (1 / qmax) by ring]
  have hxq_one : 1 ≤ xq := by
    have hq_lt_one : q < 1 := lt_of_le_of_lt hqq hqmax_lt
    have hdiv : 1 < 1 / q := one_lt_one_div hq hq_lt_one
    dsimp [xq]
    nlinarith [show 2 / q = 2 * (1 / q) by ring]
  have hxm_le_xq : xm ≤ xq := by
    have hinv : 1 / qmax ≤ 1 / q := one_div_le_one_div_of_le hq hqq
    dsimp [xm, xq]
    nlinarith [show 2 / q = 2 * (1 / q) by ring,
      show 2 / qmax = 2 * (1 / qmax) by ring]
  have harc : Real.arcosh xm ≤ Real.arcosh xq := by
    exact (Real.arcosh_le_arcosh hxm_pos (lt_of_lt_of_le zero_lt_one hxq_one)).2 hxm_le_xq
  have hexp_le : Real.exp (Real.arcosh xm) ≤ Real.exp (Real.arcosh xq) :=
    Real.exp_monotone harc
  simpa [xq, xm, Real.exp_arcosh hxm_one, Real.exp_arcosh hxq_one] using hexp_le

-- @node: chebyshev_lambda_average_add_one_le
lemma chebyshev_lambda_average_add_one_le {lam : ℝ} (hlam : 1 ≤ lam) {n : ℕ}
    (_hn : 1 ≤ n) :
    (lam ^ n + (lam ^ n)⁻¹) / 2 + 1 ≤ 2 * lam ^ n := by
  have hpow_ge_one : 1 ≤ lam ^ n := one_le_pow₀ hlam
  have hinv_le : (lam ^ n)⁻¹ ≤ lam ^ n := by
    calc
      (lam ^ n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hpow_ge_one
      _ ≤ lam ^ n := hpow_ge_one
  nlinarith

-- @node: chebyshev_lambda_average_sub_one_ge
lemma chebyshev_lambda_average_sub_one_ge {lam lam0 : ℝ} (h0 : 1 < lam0)
    (hge : lam0 ≤ lam) {n : ℕ} (hn : 1 ≤ n) :
    (lam ^ n + (lam ^ n)⁻¹) / 2 - 1 ≥
      (1 / 2) * (1 - lam0⁻¹) ^ 2 * lam ^ n := by
  have hlam_pos : 0 < lam := lt_of_lt_of_le (lt_trans zero_lt_one h0) hge
  have hpow_pos : 0 < lam ^ n := pow_pos hlam_pos n
  have hpow_ge_lam0 : lam0 ≤ lam ^ n := by
    calc
      lam0 ≤ lam := hge
      _ ≤ lam ^ n := by
          exact le_self_pow₀ (le_trans (le_of_lt h0) hge) (by omega)
  have hinv_le : (lam ^ n)⁻¹ ≤ lam0⁻¹ :=
    (inv_le_inv₀ (lt_of_lt_of_le (lt_trans zero_lt_one h0) hpow_ge_lam0)
        (lt_trans zero_lt_one h0)).mpr
      hpow_ge_lam0
  have hsub_ge : 1 - lam0⁻¹ ≤ 1 - (lam ^ n)⁻¹ := by linarith
  have hnonneg : 0 ≤ 1 - lam0⁻¹ := by
    have hle : lam0⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (le_of_lt h0)
    linarith
  have hsquare : (1 - lam0⁻¹) ^ 2 ≤ (1 - (lam ^ n)⁻¹) ^ 2 := by
    exact pow_le_pow_left₀ hnonneg hsub_ge 2
  have halg : (lam ^ n + (lam ^ n)⁻¹) / 2 - 1 =
      (1 / 2) * (1 - (lam ^ n)⁻¹) ^ 2 * lam ^ n := by
    field_simp [ne_of_gt hpow_pos]
    ring
  rw [halg]
  gcongr

-- @node: lem:continuous-chebyshev-endpoint-bound
/-- Endpoint growth: writing `x_q = 2/q - 1`, `λ(q) = x_q + √(x_q² - 1)`, for every degree-β
polynomial `R` with `sup_{[-1,1]} |R| ≤ 1` the endpoint contrast obeys the uniform upper bound
`|R(x_q) - R(-1)| ≤ C(q_max) λ(q)^β`, and the Chebyshev polynomial `T_β` supplies the matching
lower order `T_β(x_q) - 1 ≥ c(q_max) λ(q)^β`, both uniform over `q ∈ (0, q_max]`
(via `x_q = cosh a`, `T_β(x_q) = cosh(β a)`, `λ(q) = eᵃ`). Uses `chebyshev_exterior_extremal`. -/
lemma continuous_chebyshev_endpoint_bound (qmax : ℝ) (hqmax : 0 < qmax ∧ qmax < 1) :
    ∃ Cupper clower : ℝ, 0 < Cupper ∧ 0 < clower ∧
      ∀ (beta : ℕ) (q : ℝ), 1 ≤ beta → 0 < q → q ≤ qmax →
        (∀ R : Polynomial ℝ, R.natDegree ≤ beta →
            (∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → |R.eval x| ≤ 1) →
            |R.eval (2 / q - 1) - R.eval (-1)| ≤
              Cupper * ((2 / q - 1) + Real.sqrt ((2 / q - 1) ^ 2 - 1)) ^ beta) ∧
          (Polynomial.Chebyshev.T ℝ (beta : ℤ)).eval (2 / q - 1) - 1 ≥
            clower * ((2 / q - 1) + Real.sqrt ((2 / q - 1) ^ 2 - 1)) ^ beta := by
  let lam0 := (2 / qmax - 1) + Real.sqrt ((2 / qmax - 1) ^ 2 - 1)
  have hlam0_gt : 1 < lam0 := by
    have hx : 1 < 2 / qmax - 1 := by
      have hdiv : 1 < 1 / qmax := one_lt_one_div hqmax.1 hqmax.2
      nlinarith [show 2 / qmax = 2 * (1 / qmax) by ring]
    have hs : 0 ≤ Real.sqrt ((2 / qmax - 1) ^ 2 - 1) := Real.sqrt_nonneg _
    dsimp [lam0]
    nlinarith
  refine ⟨2, (1 / 2) * (1 - lam0⁻¹) ^ 2, by norm_num, ?_, ?_⟩
  · have hinv : lam0⁻¹ < 1 := inv_lt_one_of_one_lt₀ hlam0_gt
    have hsub : 0 < 1 - lam0⁻¹ := by linarith
    positivity
  · intro beta q hbeta hq hqle
    let xq := 2 / q - 1
    let lam := xq + Real.sqrt (xq ^ 2 - 1)
    have hq_lt_one : q < 1 := lt_of_le_of_lt hqle hqmax.2
    have hxq_gt : 1 < xq := by
      have hdiv : 1 < 1 / q := one_lt_one_div hq hq_lt_one
      dsimp [xq]
      nlinarith [show 2 / q = 2 * (1 / q) by ring]
    have hxq_one : 1 ≤ xq := le_of_lt hxq_gt
    have hlam_gt : 1 < lam := by
      have hs : 0 ≤ Real.sqrt (xq ^ 2 - 1) := Real.sqrt_nonneg _
      dsimp [lam]
      nlinarith
    have hlam0_le_lam : lam0 ≤ lam := by
      simpa [lam0, lam, xq] using
        endpoint_lambda_mono (q := q) (qmax := qmax) hq hqle hqmax.2
    constructor
    · intro R hdeg hbound
      have hcheb_abs := chebyshev_exterior_extremal beta hbeta R hdeg hbound xq hxq_gt
      have hRneg : |R.eval (-1)| ≤ 1 := hbound (-1) (by constructor <;> norm_num)
      have htri : |R.eval xq - R.eval (-1)| ≤ |R.eval xq| + |R.eval (-1)| :=
        by simpa using (abs_sub_le (R.eval xq) 0 (R.eval (-1)))
      have hTupper : (Polynomial.Chebyshev.T ℝ (beta : ℤ)).eval xq + 1 ≤
          2 * lam ^ beta := by
        rw [chebyshev_eval_eq_lambda_average beta xq hxq_one]
        simpa [lam] using
          chebyshev_lambda_average_add_one_le (lam := lam) (le_of_lt hlam_gt) hbeta
      calc
        |R.eval (2 / q - 1) - R.eval (-1)| = |R.eval xq - R.eval (-1)| := by rfl
        _ ≤ |R.eval xq| + |R.eval (-1)| := htri
        _ ≤ (Polynomial.Chebyshev.T ℝ (beta : ℤ)).eval xq + 1 := add_le_add hcheb_abs hRneg
        _ ≤ 2 * lam ^ beta := hTupper
        _ = 2 * ((2 / q - 1) + Real.sqrt ((2 / q - 1) ^ 2 - 1)) ^ beta := by rfl
    · have hlower := chebyshev_lambda_average_sub_one_ge (lam := lam) (lam0 := lam0)
          hlam0_gt hlam0_le_lam hbeta
      rw [chebyshev_eval_eq_lambda_average beta xq hxq_one]
      simpa [lam, lam0, xq] using hlower

end CausalSmith.Experimentation.RolloutChebyshev
