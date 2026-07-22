/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Mathlib.Analysis.FiniteDimL1LinfDuality.Basic

/-!
# Weak duality: the representation identity and `dual ≤ primal`

The analytic core is the **representation identity**: an admissible weight `w`
reproduces the endpoint contrast of every degree-`≤ β` polynomial through its
node values,
`r.eval 1 - r.eval 0 = ∑ j, w j * r.eval (p j)`.

From it, weak duality is immediate:
`|r.eval 1 - r.eval 0| = |∑ j, w j * r.eval (p j)| ≤ ∑ j, |w j| * |r.eval (p j)|
  ≤ ∑ j, |w j|`
whenever `|r.eval (p j)| ≤ 1` at every node.  Thus every dual value is `≤` every
primal value, i.e. `dual_le_primal`, giving `sSup (dualValSet) ≤ sInf (primalNormSet)`.
-/

open Polynomial

namespace Causalean.Mathlib.Analysis.FiniteDimL1LinfDuality

variable {k β : ℕ} {p : Fin (k + 1) → ℝ}

/-- **Representation identity.**  If `w ∈ MomentSol p β` and `r.natDegree ≤ β`,
then the endpoint contrast of `r` is reproduced by the weighted node values:
`r.eval 1 - r.eval 0 = ∑ j, w j * r.eval (p j)`.

Proof: expand `r.eval x = ∑ ℓ ∈ range (r.natDegree + 1), r.coeff ℓ * x ^ ℓ`
(`Polynomial.eval_eq_sum_range`), swap the order of summation, and apply the
moment condition `∑ j, w j * (p j)^ℓ = if ℓ = 0 then 0 else 1` for each `ℓ ≤ β`.
On the left, `r.eval 1 - r.eval 0 = ∑ ℓ ∈ range (n+1), r.coeff ℓ * (1^ℓ - 0^ℓ)`
matches the same `if`-pattern. -/
theorem repr_identity {w : Fin (k + 1) → ℝ} (hw : w ∈ MomentSol p β)
    {r : Polynomial ℝ} (hr : r.natDegree ≤ β) :
    r.eval 1 - r.eval 0 = ∑ j, w j * r.eval (p j) := by
  classical
  let n := r.natDegree + 1
  have h_moment :
      ∀ ℓ ∈ Finset.range n, ∑ j, w j * p j ^ ℓ = if ℓ = 0 then (0 : ℝ) else 1 := by
    intro ℓ hℓ
    exact hw ℓ ((Nat.le_of_lt_succ (by simpa [n] using hℓ)).trans hr)
  have h_lhs :
      r.eval 1 - r.eval 0 =
        ∑ ℓ ∈ Finset.range n, r.coeff ℓ * (if ℓ = 0 then (0 : ℝ) else 1) := by
    calc
      r.eval 1 - r.eval 0 =
          (∑ ℓ ∈ Finset.range n, r.coeff ℓ * (1 : ℝ) ^ ℓ) -
            (∑ ℓ ∈ Finset.range n, r.coeff ℓ * (0 : ℝ) ^ ℓ) := by
        rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range]
      _ = ∑ ℓ ∈ Finset.range n,
          (r.coeff ℓ * (1 : ℝ) ^ ℓ - r.coeff ℓ * (0 : ℝ) ^ ℓ) := by
        rw [Finset.sum_sub_distrib]
      _ = ∑ ℓ ∈ Finset.range n,
          r.coeff ℓ * ((1 : ℝ) ^ ℓ - (0 : ℝ) ^ ℓ) := by
        refine Finset.sum_congr rfl ?_
        intro ℓ hℓ
        exact (mul_sub (r.coeff ℓ) ((1 : ℝ) ^ ℓ) ((0 : ℝ) ^ ℓ)).symm
      _ = ∑ ℓ ∈ Finset.range n, r.coeff ℓ * (if ℓ = 0 then (0 : ℝ) else 1) := by
        refine Finset.sum_congr rfl ?_
        intro ℓ hℓ
        by_cases hℓ0 : ℓ = 0
        · simp [hℓ0]
        · simp [hℓ0]
  have h_rhs :
      ∑ j, w j * r.eval (p j) =
        ∑ ℓ ∈ Finset.range n, r.coeff ℓ * (if ℓ = 0 then (0 : ℝ) else 1) := by
    calc
      ∑ j, w j * r.eval (p j)
          = ∑ j, w j *
              (∑ ℓ ∈ Finset.range n, r.coeff ℓ * p j ^ ℓ) := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        rw [Polynomial.eval_eq_sum_range]
      _ = ∑ j, ∑ ℓ ∈ Finset.range n, w j * (r.coeff ℓ * p j ^ ℓ) := by
        simp [Finset.mul_sum]
      _ = ∑ ℓ ∈ Finset.range n, ∑ j, w j * (r.coeff ℓ * p j ^ ℓ) := by
        rw [Finset.sum_comm]
      _ = ∑ ℓ ∈ Finset.range n, r.coeff ℓ * (∑ j, w j * p j ^ ℓ) := by
        refine Finset.sum_congr rfl ?_
        intro ℓ hℓ
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro j hj
        ac_rfl
      _ = ∑ ℓ ∈ Finset.range n, r.coeff ℓ * (if ℓ = 0 then (0 : ℝ) else 1) := by
        refine Finset.sum_congr rfl ?_
        intro ℓ hℓ
        rw [h_moment ℓ hℓ]
  rw [h_lhs, h_rhs]

/-- **Weak duality.**  Every dual value is bounded by every primal value:
if `s ∈ primalNormSet p β` and `t ∈ dualValSet p β` then `t ≤ s`.

Proof: pick `w ∈ MomentSol p β` with `s = ∑ j, |w j|` and `r` with
`r.natDegree ≤ β`, `|r.eval (p j)| ≤ 1`, `t = |r.eval 1 - r.eval 0|`.  Then by
`repr_identity`, `t = |∑ j, w j * r.eval (p j)| ≤ ∑ j, |w j| * |r.eval (p j)|
≤ ∑ j, |w j| = s`. -/
theorem dual_le_primal {s t : ℝ} (hs : s ∈ primalNormSet p β)
    (ht : t ∈ dualValSet p β) : t ≤ s := by
  rcases hs with ⟨w, hw, rfl⟩
  rcases ht with ⟨r, hr_degree, hr_bound, rfl⟩
  rw [repr_identity hw hr_degree]
  calc
    |∑ j, w j * r.eval (p j)| ≤ ∑ j, |w j * r.eval (p j)| := by
      simpa using
        (Finset.abs_sum_le_sum_abs (fun j : Fin (k + 1) => w j * r.eval (p j)) Finset.univ)
    _ = ∑ j, |w j| * |r.eval (p j)| := by
      simp [abs_mul]
    _ ≤ ∑ j, |w j| * 1 := by
      refine Finset.sum_le_sum ?_
      intro j hj
      exact mul_le_mul_of_nonneg_left (hr_bound j) (abs_nonneg (w j))
    _ = ∑ j, |w j| := by
      simp

/-- The dual set is bounded above (by any primal value; the primal set is
nonempty for distinct nodes and `β ≤ k`). -/
theorem dualValSet_bddAbove (hp : Function.Injective p) (hβ : β ≤ k) :
    BddAbove (dualValSet p β) := by
  rcases primalNormSet_nonempty hp hβ with ⟨s, hs⟩
  exact ⟨s, fun t ht => dual_le_primal hs ht⟩

/-- Consequence of weak duality: `sSup (dualValSet p β) ≤ sInf (primalNormSet p β)`. -/
theorem sSup_dual_le_sInf_primal (hp : Function.Injective p) (hβ : β ≤ k) :
    sSup (dualValSet p β) ≤ sInf (primalNormSet p β) := by
  exact csSup_le dualValSet_nonempty fun t ht =>
    le_csInf (primalNormSet_nonempty hp hβ) fun s hs =>
      dual_le_primal hs ht

end Causalean.Mathlib.Analysis.FiniteDimL1LinfDuality
