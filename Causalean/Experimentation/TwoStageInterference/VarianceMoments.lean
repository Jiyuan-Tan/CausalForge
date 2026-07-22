/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Hudgens–Halloran (2008): expected within-group sample variance

The moment calculation behind the conservative variance estimator.  Whenever a design treats a
deterministic fixed count of units with the completely-randomized inclusion moments (the mixed
strategy of Assumption 1 being the canonical case), the expectation of the observed sample variance
of one state's outcomes (the treated-state outcomes among the treated units, or the
untreated-state outcomes among the control units) equals the corresponding *population* sample
variance with the `n−1` denominator.  Concretely, for a `{0,1}`-valued selection family `U`
(idempotent, with first moment `m/n`, pairwise second moment `m(m−1)/(n(n−1))`, and a
deterministic total `m` on the design's support), the realized sample variance
`(1/(m−1))∑ⱼ Uⱼ(xⱼ − x̄_U)²` has expectation `(1/(n−1))∑ⱼ(xⱼ − x̄)²`.

This `E_Shat` lemma is paper-agnostic in the selection family; the treated case instantiates
`U = T`, `m = K`, and the control case instantiates `U = 1 − T`, `m = n − K`.  It is the single
moment fact consumed by `E_varHat_conservative`.
-/

import Causalean.Experimentation.TwoStageInterference.Variance

/-! # Within-group sample-variance moments

Observed within-group sample variance has the correct finite-population expectation under
fixed-count randomization with completely-randomized first and second moments.

The main lemma is `E_Shat`.  For a `{0,1}`-valued selection family `U` with deterministic
support total `M`, first moment `M/n`, and pairwise moment `M(M-1)/(n(n-1))`, it proves that the
expected realized sample variance
`(1/(M-1)) * sum_j U_j * (x_j - xbar_U)^2` equals the population sample variance with denominator
`n-1`.  This paper-agnostic moment calculation is instantiated by the treated and control
selection families in the Hudgens-Halloran two-stage-interference variance estimator.  The
support-congruence helper `E_congr_supp` lets the proof rewrite the statistic only on assignments
that have positive design mass.
-/

open scoped BigOperators
open Finset

namespace Causalean
namespace Experimentation
namespace TwoStageInterference

open DesignBased

section Moments

variable {n : ℕ}

/-- **Support congruence for expectation.**  Two random variables that agree on every assignment
the design gives positive weight have equal expectation, since the off-support assignments
contribute `0 = p w · _` to the finite sum either way. -/
lemma E_congr_supp (ρ : FiniteDesign (Fin n → Bool)) {f g : (Fin n → Bool) → ℝ}
    (h : ∀ w, ρ.p w ≠ 0 → f w = g w) : ρ.E f = ρ.E g := by
  unfold FiniteDesign.E
  refine Finset.sum_congr rfl (fun w _ => ?_)
  by_cases hw : ρ.p w = 0
  · rw [hw]; ring
  · rw [h w hw]

/-- **Expectation of an observed sample variance.**  Let `U : Fin n → (Fin n → Bool) → ℝ` be a
`{0,1}`-valued selection family with the completely-randomized moments: each `Uⱼ` is idempotent,
has first moment `m/n` and pairwise (`j ≠ k`) second moment `m(m−1)/(n(n−1))`, and on the
design's support exactly `m` units are selected (`∑ⱼ Uⱼ = m`).  Then the expectation of the
realized sample variance of `x` over the selected units, `(1/(m−1))∑ⱼ Uⱼ(xⱼ − x̄_U)²` with
`x̄_U = (∑ Uⱼxⱼ)/m`, equals the population sample variance `(1/(n−1))∑ⱼ(xⱼ − x̄)²`. -/
lemma E_Shat (ρ : FiniteDesign (Fin n → Bool)) (M : ℝ) (x : Fin n → ℝ)
    (U : Fin n → (Fin n → Bool) → ℝ)
    (hnr : (n : ℝ) ≠ 0) (hn1r : (n - 1 : ℝ) ≠ 0)
    (hmr : M ≠ 0) (hm1r : (M - 1 : ℝ) ≠ 0)
    (hidem : ∀ j w, U j w * U j w = U j w)
    (hmean : ∀ j, ρ.E (U j) = M / n)
    (hpair : ∀ j k, j ≠ k →
      ρ.E (fun w => U j w * U k w) = (M * (M - 1) : ℝ) / (n * (n - 1)))
    (hsupp : ∀ w, ρ.p w ≠ 0 → (∑ j, U j w) = M) :
    ρ.E (fun w => (∑ j, U j w * (x j - (∑ i, U i w * x i) / M) ^ 2) / (M - 1))
      = (∑ j, (x j - (∑ i, x i) / n) ^ 2) / (n - 1) := by
  -- Step 1: support-expansion of the numerator into raw moments.
  -- On the support, ∑ⱼ Uⱼ(xⱼ − m_U)² = (∑ⱼ Uⱼxⱼ²) − (∑ⱼ Uⱼxⱼ)²/M.
  have hnum : ρ.E (fun w => ∑ j, U j w * (x j - (∑ i, U i w * x i) / M) ^ 2)
      = ρ.E (fun w => (∑ j, U j w * x j ^ 2) - M⁻¹ * (∑ i, U i w * x i) ^ 2) := by
    refine E_congr_supp ρ (fun w hw => ?_)
    set S1w : ℝ := ∑ i, U i w * x i with hS1w
    -- expand the square (xⱼ − m_U)² = xⱼ² − 2 m_U xⱼ + m_U²
    have hexp : ∀ j, U j w * (x j - S1w / M) ^ 2
        = U j w * x j ^ 2 - 2 * (S1w / M) * (U j w * x j) + (S1w / M) ^ 2 * U j w := by
      intro j; ring
    simp only [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    -- pull the sum-independent factors out of the second and third sums
    rw [← Finset.mul_sum (Finset.univ : Finset (Fin n)) (fun j => U j w * x j)
          (2 * (S1w / M)),
        ← Finset.mul_sum (Finset.univ : Finset (Fin n)) (fun j => U j w)
          ((S1w / M) ^ 2)]
    -- ∑ⱼ Uⱼxⱼ = S1w, ∑ⱼ Uⱼ = M on support
    have hUx : (∑ j, U j w * x j) = S1w := rfl
    rw [hUx, hsupp w hw]
    field_simp
    ring
  rw [show (fun w => (∑ j, U j w * (x j - (∑ i, U i w * x i) / M) ^ 2) / (M - 1))
        = (fun w => (∑ j, U j w * (x j - (∑ i, U i w * x i) / M) ^ 2) * ((M - 1)⁻¹))
      from by funext w; rw [div_eq_mul_inv]]
  rw [FiniteDesign.E_mul_const, hnum, FiniteDesign.E_sub, FiniteDesign.E_const_mul]
  -- Step 2: the two raw-moment expectations.
  -- E[∑ⱼ Uⱼxⱼ²] = (m/n)∑ⱼxⱼ².
  have hE1 : ρ.E (fun w => ∑ j, U j w * x j ^ 2) = (M / n : ℝ) * ∑ j, x j ^ 2 := by
    rw [FiniteDesign.E_sum]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [FiniteDesign.E_mul_const, hmean j]
  -- E[(∑ⱼ Uⱼxⱼ)²] = (m/n)∑xⱼ² + m(m−1)/(n(n−1)) · ((∑x)² − ∑x²).
  have hE2 : ρ.E (fun w => (∑ i, U i w * x i) ^ 2)
      = (M / n : ℝ) * (∑ j, x j ^ 2)
        + (M * (M - 1) : ℝ) / (n * (n - 1)) * ((∑ j, x j) ^ 2 - ∑ j, x j ^ 2) := by
    -- expand the square into a double sum
    have hsq : ∀ w, (∑ i, U i w * x i) ^ 2
        = ∑ j, ∑ k, (x j * x k) * (U j w * U k w) := by
      intro w
      rw [sq, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => by ring))
    simp only [hsq]
    rw [FiniteDesign.E_sum]
    -- now ∑ⱼ E[∑ₖ (xⱼxₖ)(Uⱼ Uₖ)]
    have hinner : ∀ j, ρ.E (fun w => ∑ k, (x j * x k) * (U j w * U k w))
        = ∑ k, (x j * x k) * ρ.E (fun w => U j w * U k w) := by
      intro j
      rw [FiniteDesign.E_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [FiniteDesign.E_const_mul]
    simp only [hinner]
    -- split the inner sum at the diagonal k = j
    have hdiag : ∀ j, ρ.E (fun w => U j w * U j w) = (M / n : ℝ) := by
      intro j
      rw [show (fun w => U j w * U j w) = U j from by funext w; rw [hidem j w]]
      exact hmean j
    have hsplit : ∀ j, (∑ k, (x j * x k) * ρ.E (fun w => U j w * U k w))
        = (x j ^ 2) * (M / n : ℝ)
          + (M * (M - 1) : ℝ) / (n * (n - 1)) * (x j * (∑ k, x k) - x j ^ 2) := by
      intro j
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
      rw [hdiag j]
      -- off-diagonal terms use hpair
      have hoff : (∑ k ∈ Finset.univ.erase j, (x j * x k) * ρ.E (fun w => U j w * U k w))
          = (M * (M - 1) : ℝ) / (n * (n - 1)) * (∑ k ∈ Finset.univ.erase j, x j * x k) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun k hk => ?_)
        have hjk : j ≠ k := (Finset.ne_of_mem_erase hk).symm
        rw [hpair j k hjk]; ring
      rw [hoff]
      -- ∑_{k≠j} xⱼxₖ = xⱼ(∑x) − xⱼxⱼ
      have herase : (∑ k ∈ Finset.univ.erase j, x j * x k) = x j * (∑ k, x k) - x j * x j := by
        rw [← Finset.mul_sum, ← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
        ring
      rw [herase]; ring
    simp only [hsplit, Finset.sum_add_distrib]
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    -- ∑ⱼ xⱼ(∑x) − xⱼ² = (∑x)² − ∑x²
    have hcollapse : (∑ j, (x j * (∑ k, x k) - x j ^ 2))
        = (∑ j, x j) ^ 2 - ∑ j, x j ^ 2 := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
      congr 1
      rw [sq]
    rw [hcollapse]
    ring
  rw [hE1, hE2]
  -- Step 3: algebra collapses E[num]·(m−1)⁻¹ to the population sample variance.
  rw [sum_sub_mean_sq (by
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h] at hnr
    · exact h) x]
  -- Let P = ∑x², Q = (∑x)². Goal is a pure field identity in P, Q, n, m.
  set P : ℝ := ∑ j, x j ^ 2
  set Q : ℝ := (∑ j, x j) ^ 2
  field_simp
  ring
end Moments

end TwoStageInterference
end Experimentation
end Causalean
