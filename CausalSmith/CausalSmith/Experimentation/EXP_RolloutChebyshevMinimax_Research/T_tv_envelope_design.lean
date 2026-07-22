/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Main deliverable 1: the total-variation envelope rollout design theorem

`thm:tv-envelope-design`.
-/

import CausalSmith.Experimentation.EXP_RolloutChebyshevMinimax_Research.Basic
import CausalSmith.Experimentation.EXP_RolloutChebyshevMinimax_Research.Helpers.Variance
import CausalSmith.Experimentation.EXP_RolloutChebyshevMinimax_Research.Helpers.Amplification
import CausalSmith.Experimentation.EXP_RolloutChebyshevMinimax_Research.Helpers.MinimaxAssembly
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Real.Pointwise

open Causalean.Experimentation.DesignBased
open scoped BigOperators Pointwise

namespace CausalSmith.Experimentation.RolloutChebyshev

-- @node: thm:tv-envelope-design
/-- **Main deliverable 1 (TV-envelope rollout design theorem).** Assume `β ≥ 1` and `k ≥ β`.
For every budgeted schedule `p ∈ S_{k,q}` and every law `P ∈ P_β` (bundled as
`RolloutLawClass`), the unbiased weight set is nonempty, and for every `w ∈ W_β(p)` the linear
rollout estimator `hat_τ_{w,p} = ∑ⱼ wⱼ bar_Y_j` is design-unbiased for `τ_P = m_P(1) - m_P(0)`
and satisfies the sharp total-variation variance bound
`Var_pi(hat_τ_{w,p}) ≤ (σ₀²/n)(∑ⱼ|wⱼ|)²`.

Minimizing the right side over `W_β(p)` yields the fixed-schedule envelope optimum: the
smallest achievable envelope variance `inf_{w∈W_β(p)} (σ₀²/n)(∑ⱼ|wⱼ|)²` equals
`(σ₀²/n) A_β(p)` (`def:amplification-criterion`), the design-objective reduction recorded as the
third conjunct. Taking the further infimum over budgeted schedules `S_{k,q}` gives the minimax
envelope variance `inf_{p∈S_{k,q}} (σ₀²/n) A_β(p) = (σ₀²/n) M_{β,k,q}`
(`def:minimaxAmplification`), the fourth conjunct. Both reductions hold because the nonnegative
constant `σ₀²/n ≥ 0` pulls through the infimum (`Real.sInf_smul_of_nonneg`). The fifth conjunct is
the *optimal-schedule characterization*: any budgeted schedule `p*` that attains the minimax value
`A_β(p*) = M_{β,k,q}` minimizes the envelope variance `(σ₀²/n) A_β` over all of `S_{k,q}` — i.e.
`(σ₀²/n) A_β(p*) ≤ (σ₀²/n) A_β(p')` for every budgeted `p'`. This is the conditional
`attains-the-inf ⇒ minimizes` statement (`minimaxAmplification_le_of_budgeted` plus
`σ₀²/n ≥ 0`), not an existence claim. The one remaining consequence the note draws — that such an
optimal schedule *exists*, i.e. the minimax infimum is actually *attained* (e.g. by the shifted
Chebyshev–Lobatto grid) — is NOT provable here without a schedule-class attainment argument; it is
the content of `chebyshev_minimax` and is deliberately left to that theorem rather than asserted
vacuously here.

The variance bound is **sharp** over the diagonal variance envelope: for every `w ∈ W_β(p)`
there is a positive semidefinite (rank-one) covariance matrix `Γ` with diagonal bounded by
`σ₀²/n` whose quadratic form attains `(σ₀²/n)(∑ⱼ|wⱼ|)²`, so the envelope constant cannot be
improved (this is the rank-one worst case of `lem:variance-envelope-sharpness`). The sign
constraint `0 ≤ σ₀²` records the round-mean variance constant's range `σ₀² ∈ ℝ₊`. -/
theorem tv_envelope_design (n k beta : ℕ) (q sigma0sq : ℝ) {Ω : Type*} [Fintype Ω]
    (D : FiniteDesign Ω) (Y : Fin n → (Fin n → Bool) → ℝ)
    (Z : Fin (k + 1) → Ω → (Fin n → Bool)) (barY : Fin (k + 1) → Ω → ℝ)
    (m : ℝ → ℝ) (a : ℕ → ℝ) (hbeta : 1 ≤ beta) (hk : beta ≤ k) (hsig : 0 ≤ sigma0sq)
    (p : Fin (k + 1) → ℝ) (hp : BudgetedSchedule k q p)
    (hP : RolloutLawClass n k beta D Y Z barY m a sigma0sq p) :
    (∃ w : Fin (k + 1) → ℝ, UnbiasedWeights beta k p w) ∧
      (∀ w : Fin (k + 1) → ℝ, UnbiasedWeights beta k p w →
        D.E (fun z => ∑ j, w j * barY j z) = m 1 - m 0 ∧
          D.Var (fun z => ∑ j, w j * barY j z)
            ≤ sigma0sq / (n : ℝ) * (∑ j, |w j|) ^ 2 ∧
          ∃ Γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ, Γ.PosSemidef ∧
            (∀ j, Γ j j ≤ sigma0sq / (n : ℝ)) ∧
            (∑ i, ∑ j, w i * Γ i j * w j) = sigma0sq / (n : ℝ) * (∑ j, |w j|) ^ 2) ∧
      (sInf { v : ℝ | ∃ w : Fin (k + 1) → ℝ, UnbiasedWeights beta k p w ∧
          v = sigma0sq / (n : ℝ) * (∑ j, |w j|) ^ 2 }
        = sigma0sq / (n : ℝ) * amplification beta k p) ∧
      (sInf { v : ℝ | ∃ p' : Fin (k + 1) → ℝ, BudgetedSchedule k q p' ∧
          v = sigma0sq / (n : ℝ) * amplification beta k p' }
        = sigma0sq / (n : ℝ) * minimaxAmplification beta k q) ∧
      (∀ pstar : Fin (k + 1) → ℝ, BudgetedSchedule k q pstar →
          amplification beta k pstar = minimaxAmplification beta k q →
        ∀ p' : Fin (k + 1) → ℝ, BudgetedSchedule k q p' →
          sigma0sq / (n : ℝ) * amplification beta k pstar
            ≤ sigma0sq / (n : ℝ) * amplification beta k p') := by
  have hc : (0 : ℝ) ≤ sigma0sq / (n : ℝ) := div_nonneg hsig (Nat.cast_nonneg n)
  refine ⟨unbiased_weight_set_nonempty beta k q p hbeta hk hp, ?_, ?_, ?_, ?_⟩
  · intro w hw
    constructor
    · rw [FiniteDesign.E_sum]
      have hmean : (∑ j : Fin (k + 1), D.E (fun z => w j * barY j z)) =
          ∑ j : Fin (k + 1), w j * m (p j) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [FiniteDesign.E_const_mul, hP.mean_curve]
      rw [hmean]
      have hpoly_at_nodes : ∀ j : Fin (k + 1),
          m (p j) = ∑ ell ∈ Finset.range (beta + 1), a ell * (p j) ^ ell := by
        intro j
        exact hP.beta_polynomial (p j) (hp.1 j)
      have hsum_poly : (∑ j : Fin (k + 1), w j * m (p j)) =
          ∑ ell ∈ Finset.range (beta + 1),
            a ell * ∑ j : Fin (k + 1), w j * (p j) ^ ell := by
        simp_rw [hpoly_at_nodes]
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        simp [mul_left_comm]
      rw [hsum_poly]
      have hendpoint :=
        rollout_polynomial_identity n k beta Y Z barY m a hP.static_rollout hP.beta_polynomial
      rw [hendpoint]
      have hsplit : (∑ ell ∈ Finset.range (beta + 1),
          a ell * ∑ j : Fin (k + 1), w j * (p j) ^ ell) =
          a 0 * (∑ j : Fin (k + 1), w j * (p j) ^ (0 : ℕ)) +
            ∑ ell ∈ Finset.Icc 1 beta,
              a ell * ∑ j : Fin (k + 1), w j * (p j) ^ ell := by
        clear hsum_poly hendpoint hpoly_at_nodes hmean hbeta hk hP hw
        induction beta with
        | zero => simp
        | succ beta ih =>
            rw [Finset.sum_range_succ]
            rw [ih]
            rw [Finset.sum_Icc_succ_top (Nat.succ_pos beta)]
            ring
      rw [hsplit, hw.1]
      simp
      apply Finset.sum_congr rfl
      intro ell hell
      rw [hw.2 ell (Finset.mem_Icc.mp hell).1 (Finset.mem_Icc.mp hell).2]
      ring
    · exact variance_envelope_sharpness n k D barY sigma0sq w hsig hP.variance_envelope
  · -- Fixed-schedule envelope optimum: the best achievable envelope variance over `W_β(p)` is
    -- `(σ₀²/n)·A_β(p)`, by pulling the nonnegative constant `σ₀²/n` through the `sInf`.
    have hset : { v : ℝ | ∃ w : Fin (k + 1) → ℝ, UnbiasedWeights beta k p w ∧
          v = sigma0sq / (n : ℝ) * (∑ j, |w j|) ^ 2 }
        = (sigma0sq / (n : ℝ)) •
            { v : ℝ | ∃ w : Fin (k + 1) → ℝ, UnbiasedWeights beta k p w ∧
              v = (∑ j, |w j|) ^ 2 } := by
      ext v
      simp only [Set.mem_smul_set, Set.mem_setOf_eq, smul_eq_mul]
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact ⟨(∑ j, |w j|) ^ 2, ⟨w, hw, rfl⟩, rfl⟩
      · rintro ⟨x, ⟨w, hw, rfl⟩, rfl⟩
        exact ⟨w, hw, rfl⟩
    unfold amplification
    rw [hset, Real.sInf_smul_of_nonneg hc, smul_eq_mul]
  · -- Minimax envelope: the infimum of the fixed-schedule envelope optima over `S_{k,q}` is
    -- `(σ₀²/n)·M_{β,k,q}`, again by pulling `σ₀²/n ≥ 0` through the `sInf`.
    have hset : { v : ℝ | ∃ p' : Fin (k + 1) → ℝ, BudgetedSchedule k q p' ∧
          v = sigma0sq / (n : ℝ) * amplification beta k p' }
        = (sigma0sq / (n : ℝ)) •
            { v : ℝ | ∃ p' : Fin (k + 1) → ℝ, BudgetedSchedule k q p' ∧
              v = amplification beta k p' } := by
      ext v
      simp only [Set.mem_smul_set, Set.mem_setOf_eq, smul_eq_mul]
      constructor
      · rintro ⟨p', hp', rfl⟩
        exact ⟨amplification beta k p', ⟨p', hp', rfl⟩, rfl⟩
      · rintro ⟨x, ⟨p', hp', rfl⟩, rfl⟩
        exact ⟨p', hp', rfl⟩
    unfold minimaxAmplification
    rw [hset, Real.sInf_smul_of_nonneg hc, smul_eq_mul]
  · -- Optimal-schedule characterization (conditional): any budgeted `pstar` attaining the
    -- minimax value `M_{β,k,q}` minimizes the envelope variance `(σ₀²/n)·A_β` over `S_{k,q}`.
    -- This is `attains inf ⇒ ≤ all others`, NOT an existence/attainment claim, so it is
    -- provable here without the schedule-class attainment argument of `chebyshev_minimax`.
    intro pstar _hpstar hpstar_eq p' hp'
    have hle : amplification beta k pstar ≤ amplification beta k p' := by
      rw [hpstar_eq]
      exact minimaxAmplification_le_of_budgeted beta k q p' hp'
    exact mul_le_mul_of_nonneg_left hle hc

end CausalSmith.Experimentation.RolloutChebyshev
