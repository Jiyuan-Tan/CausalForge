/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Mathlib

/-!
# Finite-dimensional ℓ¹/ℓ∞ duality for minimum-norm node representation — definitions

Fix `k + 1` nodes `p : Fin (k+1) → ℝ` and a degree bound `β ≤ k`.  We study the
minimum ℓ¹ norm of a *weight vector* `w : Fin (k+1) → ℝ` that reproduces the
endpoint contrast `r ↦ r.eval 1 - r.eval 0` on every real polynomial `r` of
degree `≤ β`, sampled at the nodes.

The weight `w` reproduces the contrast on all degree-`≤ β` polynomials iff it
solves the **moment system**
`∑ j, w j * (p j) ^ ℓ = (if ℓ = 0 then 0 else 1)` for every `ℓ ≤ β`
(test against monomials `X^ℓ`; the RHS is `1^ℓ - 0^ℓ`).  That system is the set
`MomentSol p β`.

The two extremal quantities are
* the **primal**  `sInf (primalNormSet p β)` — the least achievable `∑ j, |w j|`
  over `w ∈ MomentSol p β`;
* the **dual**    `sSup (dualValSet p β)`   — the largest achievable
  `|r.eval 1 - r.eval 0|` over polynomials `r` of degree `≤ β` bounded by `1` at
  the nodes.

The main theorem `l1_repr_eq_sup_dual` (in `Duality.lean`) is the identity
`sInf (primalNormSet p β) = sSup (dualValSet p β)`: finite-dimensional
ℓ¹/ℓ∞ Hahn–Banach / LP duality specialised to the node-sampling map.

This file only sets up the definitions and the basic well-posedness facts
(nonemptiness / boundedness of the two real sets).  Everything is stated for
*arbitrary* distinct nodes and *arbitrary* `β ≤ k`, so it is reusable and not
gerrymandered to any downstream schedule.

## Standard reference
Finite-dimensional LP duality / ℓ¹–ℓ∞ Hahn–Banach duality (the ℓ¹/ℓ∞ pairing on
`ℝⁿ`); the min-norm-representation `=` dual-sup identity is standard
optimal-recovery / convex-analysis duality.
-/

open Polynomial

namespace Causalean.Mathlib.Analysis.FiniteDimL1LinfDuality

variable {k β : ℕ} {p : Fin (k + 1) → ℝ}

/-- The **moment system** of admissible weight vectors.  `w ∈ MomentSol p β`
means that for every degree `ℓ ≤ β` the sampled weighted sum
`∑ j, w j * (p j) ^ ℓ` equals `1^ℓ - 0^ℓ`, i.e. `0` when `ℓ = 0` and `1`
otherwise.  Equivalently, `w` reproduces the endpoint contrast
`r ↦ r.eval 1 - r.eval 0` on every real polynomial `r` of degree `≤ β` via the
node values `(r.eval (p j))ⱼ`. -/
def MomentSol (p : Fin (k + 1) → ℝ) (β : ℕ) : Set (Fin (k + 1) → ℝ) :=
  {w | ∀ ℓ, ℓ ≤ β → ∑ j, w j * p j ^ ℓ = if ℓ = 0 then (0 : ℝ) else 1}

/-- The set of achievable ℓ¹ norms of admissible weights:
`primalNormSet p β = { ∑ j, |w j| : w ∈ MomentSol p β }`.  Its infimum is the
primal (min-norm-representation) value. -/
def primalNormSet (p : Fin (k + 1) → ℝ) (β : ℕ) : Set ℝ :=
  {s | ∃ w ∈ MomentSol p β, s = ∑ j, |w j|}

/-- The set of achievable endpoint contrasts of node-bounded polynomials:
`dualValSet p β = { |r.eval 1 - r.eval 0| : r.natDegree ≤ β, ∀ j, |r.eval (p j)| ≤ 1 }`.
Its supremum is the dual value. -/
def dualValSet (p : Fin (k + 1) → ℝ) (β : ℕ) : Set ℝ :=
  {t | ∃ r : Polynomial ℝ,
        r.natDegree ≤ β ∧ (∀ j, |r.eval (p j)| ≤ 1) ∧ t = |r.eval 1 - r.eval 0|}

/-- The dual set is nonempty: the zero polynomial contributes the value `0`
(degree `0 ≤ β`, trivially node-bounded, contrast `0`). -/
theorem dualValSet_nonempty : (dualValSet p β).Nonempty := by
  refine ⟨0, ?_⟩
  refine ⟨(0 : Polynomial ℝ), ?_, ?_, ?_⟩
  · simp
  · intro j
    simp
  · simp

/-- Every element of the primal set is `≥ 0` (a sum of absolute values), so the
set is bounded below by `0`. -/
theorem primalNormSet_bddBelow : BddBelow (primalNormSet p β) := by
  refine ⟨0, fun s hs => ?_⟩
  rcases hs with ⟨w, _hw, rfl⟩
  exact Finset.sum_nonneg (fun j _ => abs_nonneg (w j))

/-- `0` is a lower bound for the primal set. -/
theorem primalNormSet_nonneg {s : ℝ} (hs : s ∈ primalNormSet p β) : 0 ≤ s := by
  rcases hs with ⟨w, _hw, rfl⟩
  exact Finset.sum_nonneg (fun j _ => abs_nonneg (w j))

/-- **Nonemptiness of the moment system (Vandermonde).**  For `k + 1` *distinct*
nodes and `β ≤ k`, the moment map `w ↦ (∑ j, w j * (p j)^ℓ)_{ℓ ≤ β}` is
surjective (equivalently, its transpose — node-evaluation of degree-`≤ β`
polynomials — is injective, since a nonzero polynomial of degree `≤ β ≤ k` has at
most `β < k + 1` roots).  Hence the moment system has a solution. -/
theorem momentSol_nonempty (hp : Function.Injective p) (hβ : β ≤ k) :
    (MomentSol p β).Nonempty := by
  classical
  let e : Fin (β + 1) → Fin (k + 1) := fun i =>
    ⟨i, Nat.lt_succ_of_le ((Nat.le_of_lt_succ i.isLt).trans hβ)⟩
  let q : Fin (β + 1) → ℝ := fun i => p (e i)
  let y : Fin (β + 1) → ℝ := fun ℓ => if (ℓ : ℕ) = 0 then 0 else 1
  have hq : Function.Injective q := by
    intro i j hij
    apply Fin.ext
    have heq : e i = e j := hp hij
    simpa [e] using congrArg Fin.val heq
  have hAunit : IsUnit (Matrix.vandermonde q) := by
    refine (Matrix.isUnit_iff_isUnit_det _).mpr ?_
    exact isUnit_iff_ne_zero.mpr ((Matrix.det_vandermonde_ne_zero_iff).mpr hq)
  obtain ⟨a, ha⟩ := (Matrix.vecMul_surjective_iff_isUnit.mpr hAunit) y
  refine ⟨fun j => ∑ i : Fin (β + 1), if e i = j then a i else 0, ?_⟩
  intro ℓ hℓ
  let ℓ' : Fin (β + 1) := ⟨ℓ, Nat.lt_succ_of_le hℓ⟩
  have hcoord : Matrix.vecMul a (Matrix.vandermonde q) ℓ' = y ℓ' := by
    simpa using congr_fun ha ℓ'
  calc
    ∑ j : Fin (k + 1), (∑ i : Fin (β + 1), if e i = j then a i else 0) * p j ^ ℓ
        = Matrix.vecMul a (Matrix.vandermonde q) ℓ' := by
          simp only [Matrix.vecMul, dotProduct, Matrix.vandermonde_apply, q, ℓ']
          simp_rw [Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.sum_eq_single (e i)]
          · simp
          · intro j _ hj
            simp [hj.symm]
          · intro he
            exact (he (Finset.mem_univ (e i))).elim
    _ = if ℓ = 0 then (0 : ℝ) else 1 := by
          simpa [y, ℓ']

/-- The primal set is nonempty whenever the moment system is solvable. -/
theorem primalNormSet_nonempty (hp : Function.Injective p) (hβ : β ≤ k) :
    (primalNormSet p β).Nonempty := by
  rcases momentSol_nonempty (p := p) hp hβ with ⟨w, hw⟩
  exact ⟨∑ j, |w j|, w, hw, rfl⟩

end Causalean.Mathlib.Analysis.FiniteDimL1LinfDuality
