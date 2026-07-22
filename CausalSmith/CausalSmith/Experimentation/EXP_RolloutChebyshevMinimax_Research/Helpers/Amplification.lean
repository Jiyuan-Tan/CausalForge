/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Amplification helpers: ℓ¹/ℓ∞ dual-norm identity and weight-set nonemptiness

`lem:amplification-dual-norm` and `lem:unbiased-weight-set-nonempty`.
-/

import CausalSmith.Experimentation.EXP_RolloutChebyshevMinimax_Research.Basic
import Causalean.Mathlib.Analysis.FiniteDimL1LinfDuality.Basic
import Causalean.Mathlib.Analysis.FiniteDimL1LinfDuality.Duality
import Causalean.Mathlib.Analysis.FiniteDimL1LinfDuality.NonemptyDuality
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Vandermonde

open scoped BigOperators

namespace CausalSmith.Experimentation.RolloutChebyshev

open Polynomial Causalean.Mathlib.Analysis.FiniteDimL1LinfDuality

-- @node: lem:amplification-dual-norm
/-- ℓ¹/ℓ∞ duality: for a schedule `p` with distinct nodes and nonempty `W_β(p)`, the minimal
total-variation norm of a representing weight vector equals the dual (Chebyshev) norm
`sup{ |r(1)-r(0)| : deg r ≤ β, max_j |r(p_j)| ≤ 1 }`, and `A_β(p)` is its square.
Matching the note, the only premises are that the nodes are distinct and that `W_β(p)` is
nonempty (feasibility of the primal); there is no `β ≤ k` side-condition on the statement. -/
lemma amplification_dual_norm (beta k : ℕ) (p : Fin (k + 1) → ℝ)
    (hp : Function.Injective p)
    (hne : ∃ w : Fin (k + 1) → ℝ, UnbiasedWeights beta k p w) :
    sInf { s : ℝ | ∃ w : Fin (k + 1) → ℝ, UnbiasedWeights beta k p w ∧ s = ∑ j, |w j| }
        = sSup { t : ℝ | ∃ r : Polynomial ℝ, r.natDegree ≤ beta ∧
            (∀ j, |r.eval (p j)| ≤ 1) ∧ t = |r.eval 1 - r.eval 0| } ∧
      amplification beta k p
        = (sSup { t : ℝ | ∃ r : Polynomial ℝ, r.natDegree ≤ beta ∧
            (∀ j, |r.eval (p j)| ≤ 1) ∧ t = |r.eval 1 - r.eval 0| }) ^ 2 := by
  have _ : Function.Injective p := hp
  -- Bridge the run's `UnbiasedWeights` to the duality substrate's `MomentSol`.
  have key : ∀ w : Fin (k + 1) → ℝ,
      UnbiasedWeights beta k p w ↔ w ∈ MomentSol p beta := by
    intro w
    simp only [UnbiasedWeights, MomentSol, Set.mem_setOf_eq]
    constructor
    · rintro ⟨h0, hpos⟩ ℓ hℓ
      rcases Nat.eq_zero_or_pos ℓ with hz | hℓpos
      · subst hz; simpa using h0
      · rw [if_neg (by omega : ℓ ≠ 0)]; exact hpos ℓ hℓpos hℓ
    · intro h
      refine ⟨?_, ?_⟩
      · have h0 := h 0 (Nat.zero_le _); simpa using h0
      · intro ℓ h1 hℓ
        have hh := h ℓ hℓ
        rwa [if_neg (by omega : ℓ ≠ 0)] at hh
  -- The run's primal set is the substrate's `primalNormSet`; its dual set is `dualValSet`.
  have hprimal_set :
      { s : ℝ | ∃ w : Fin (k + 1) → ℝ, UnbiasedWeights beta k p w ∧ s = ∑ j, |w j| }
        = primalNormSet p beta := by
    ext s
    simp only [primalNormSet, Set.mem_setOf_eq]
    exact ⟨fun ⟨w, hw, hs⟩ => ⟨w, (key w).mp hw, hs⟩,
           fun ⟨w, hw, hs⟩ => ⟨w, (key w).mpr hw, hs⟩⟩
  have hmoment_nonempty : (MomentSol p beta).Nonempty := by
    rcases hne with ⟨w, hw⟩
    exact ⟨w, (key w).mp hw⟩
  refine ⟨?_, ?_⟩
  · -- First conjunct: exactly the ℓ¹/ℓ∞ duality identity.
    rw [hprimal_set]
    exact l1_repr_eq_sup_dual_of_momentSol_nonempty hmoment_nonempty
  · -- Second conjunct: compare the squared infimum directly with the dual square.
    let A : Set ℝ :=
      { v : ℝ | ∃ w : Fin (k + 1) → ℝ, UnbiasedWeights beta k p w ∧
        v = (∑ j, |w j|) ^ 2 }
    have hA_bdd : BddBelow A := by
      refine ⟨0, ?_⟩
      intro v hv
      rcases hv with ⟨w, _hw, rfl⟩
      exact sq_nonneg _
    have hA_nonempty : A.Nonempty := by
      rcases hne with ⟨w, hw⟩
      exact ⟨(∑ j, |w j|) ^ 2, w, hw, rfl⟩
    have hD_nonneg : 0 ≤ sSup (dualValSet p beta) :=
      dual_nonneg_of_momentSol_nonempty hmoment_nonempty
    have hdual_eq : sInf (primalNormSet p beta) = sSup (dualValSet p beta) :=
      l1_repr_eq_sup_dual_of_momentSol_nonempty hmoment_nonempty
    have hAmp_lower : (sSup (dualValSet p beta)) ^ 2 ≤ sInf A := by
      refine le_csInf hA_nonempty ?_
      intro v hv
      rcases hv with ⟨w, hw, rfl⟩
      have hwM : w ∈ MomentSol p beta := (key w).mp hw
      have hnorm_mem : (∑ j, |w j|) ∈ primalNormSet p beta := ⟨w, hwM, rfl⟩
      have hD_le_norm : sSup (dualValSet p beta) ≤ ∑ j, |w j| := by
        rw [← hdual_eq]
        exact csInf_le primalNormSet_bddBelow hnorm_mem
      have hnorm_nonneg : 0 ≤ ∑ j, |w j| :=
        Finset.sum_nonneg (fun j _ => abs_nonneg (w j))
      exact sq_le_sq' (by linarith) hD_le_norm
    have hAmp_upper : sInf A ≤ (sSup (dualValSet p beta)) ^ 2 := by
      obtain ⟨w, hw, hw_norm⟩ :=
        exists_moment_le_dual_of_momentSol_nonempty hmoment_nonempty
      have hw_unbiased : UnbiasedWeights beta k p w := (key w).mpr hw
      have hnorm_nonneg : 0 ≤ ∑ j, |w j| :=
        Finset.sum_nonneg (fun j _ => abs_nonneg (w j))
      have hsq : (∑ j, |w j|) ^ 2 ≤ (sSup (dualValSet p beta)) ^ 2 :=
        sq_le_sq' (by linarith) hw_norm
      calc
        sInf A ≤ (∑ j, |w j|) ^ 2 :=
          csInf_le hA_bdd ⟨w, hw_unbiased, rfl⟩
        _ ≤ (sSup (dualValSet p beta)) ^ 2 := hsq
    unfold amplification
    change sInf A = (sSup (dualValSet p beta)) ^ 2
    exact le_antisymm hAmp_upper hAmp_lower

-- @node: lagrange_endpoint_weights_unbiased
/-- Lagrange endpoint weights on any `k+1` distinct nodes reproduce the endpoint contrast for
all polynomials of degree at most `β` when `β ≤ k`, hence satisfy the moment equations for
`W_β(p)`. -/
lemma lagrange_endpoint_weights_unbiased (beta k : ℕ) (p : Fin (k + 1) → ℝ)
    (hk : beta ≤ k) (hp : Function.Injective p) :
    UnbiasedWeights beta k p
      (fun j => (Lagrange.basis (Finset.univ : Finset (Fin (k + 1))) p j).eval 1 -
        (Lagrange.basis (Finset.univ : Finset (Fin (k + 1))) p j).eval 0) := by
  classical
  let w : Fin (k + 1) → ℝ := fun j =>
    (Lagrange.basis (Finset.univ : Finset (Fin (k + 1))) p j).eval 1 -
      (Lagrange.basis (Finset.univ : Finset (Fin (k + 1))) p j).eval 0
  have hmoment : ∀ ell : ℕ, ell ≤ beta →
      ∑ j : Fin (k + 1), w j * (p j) ^ ell = (1 : ℝ) ^ ell - (0 : ℝ) ^ ell := by
    intro ell hle
    let P : Polynomial ℝ := (Polynomial.X : Polynomial ℝ) ^ ell
    have hdeg : P.degree < (Finset.univ : Finset (Fin (k + 1))).card := by
      dsimp [P]
      rw [Fintype.card_fin, Polynomial.degree_X_pow]
      norm_cast
      exact Nat.lt_succ_of_le (le_trans hle hk)
    have hinterp : P = Lagrange.interpolate (Finset.univ : Finset (Fin (k + 1))) p
        (fun j => P.eval (p j)) := by
      exact Lagrange.eq_interpolate (s := (Finset.univ : Finset (Fin (k + 1))))
        (v := p) hp.injOn hdeg
    have h1 := congrArg (fun Q : Polynomial ℝ => Q.eval 1) hinterp
    have h0 := congrArg (fun Q : Polynomial ℝ => Q.eval 0) hinterp
    have hsum1 : (1 : ℝ) ^ ell =
        ∑ j : Fin (k + 1), (p j) ^ ell *
          (Lagrange.basis (Finset.univ : Finset (Fin (k + 1))) p j).eval 1 := by
      simpa [P, Lagrange.interpolate_apply, Polynomial.eval_finset_sum, Polynomial.eval_mul,
        mul_comm, mul_left_comm, mul_assoc] using h1
    have hsum0 : (0 : ℝ) ^ ell =
        ∑ j : Fin (k + 1), (p j) ^ ell *
          (Lagrange.basis (Finset.univ : Finset (Fin (k + 1))) p j).eval 0 := by
      simpa [P, Lagrange.interpolate_apply, Polynomial.eval_finset_sum, Polynomial.eval_mul,
        mul_comm, mul_left_comm, mul_assoc] using h0
    calc
      ∑ j : Fin (k + 1), w j * (p j) ^ ell
          = ∑ j : Fin (k + 1), ((p j) ^ ell *
              (Lagrange.basis (Finset.univ : Finset (Fin (k + 1))) p j).eval 1 -
            (p j) ^ ell *
              (Lagrange.basis (Finset.univ : Finset (Fin (k + 1))) p j).eval 0) := by
            apply Finset.sum_congr rfl
            intro j _
            simp [w]
            ring
      _ = (∑ j : Fin (k + 1), (p j) ^ ell *
              (Lagrange.basis (Finset.univ : Finset (Fin (k + 1))) p j).eval 1) -
            (∑ j : Fin (k + 1), (p j) ^ ell *
              (Lagrange.basis (Finset.univ : Finset (Fin (k + 1))) p j).eval 0) := by
            rw [Finset.sum_sub_distrib]
      _ = (1 : ℝ) ^ ell - (0 : ℝ) ^ ell := by rw [← hsum1, ← hsum0]
  constructor
  · simpa [w] using hmoment 0 (by omega)
  · intro ell hell hle
    have h := hmoment ell hle
    simpa [w, one_pow, zero_pow (ne_of_gt hell)] using h

-- @node: lem:unbiased-weight-set-nonempty
/-- For `β ≥ 1` and `k ≥ β`, the linear-unbiased weight set `W_β(p)` is nonempty for every
budgeted schedule `p ∈ S_{k,q}`: distinct nodes make the `(β+1)×(k+1)` moment matrix
full row rank (a nonzero degree-≤β polynomial cannot vanish at `k+1 ≥ β+1` distinct points),
so `w ↦ Bw` is surjective onto the target moment vector. -/
lemma unbiased_weight_set_nonempty (beta k : ℕ) (q : ℝ) (p : Fin (k + 1) → ℝ)
    (_hbeta : 1 ≤ beta) (hk : beta ≤ k) (hp : BudgetedSchedule k q p) :
    ∃ w : Fin (k + 1) → ℝ, UnbiasedWeights beta k p w := by
  exact ⟨_, lagrange_endpoint_weights_unbiased beta k p hk hp.2.2.1.injective⟩

end CausalSmith.Experimentation.RolloutChebyshev
