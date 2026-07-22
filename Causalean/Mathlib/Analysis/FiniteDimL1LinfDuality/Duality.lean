/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Mathlib.Analysis.FiniteDimL1LinfDuality.StrongDuality

/-!
# Finite-dimensional ℓ¹/ℓ∞ duality — the main identity

Assembles weak duality (`sSup_dual_le_sInf_primal`) and strong duality
(`sInf_primal_le_sSup_dual`) into the min-norm-representation `=` dual-sup
identity for the node-sampling map, plus the squared corollary used downstream.
-/

open Polynomial

namespace Causalean.Mathlib.Analysis.FiniteDimL1LinfDuality

variable {k β : ℕ} {p : Fin (k + 1) → ℝ}

/-- **Finite-dimensional ℓ¹/ℓ∞ duality.**  For `k + 1` distinct nodes
`p : Fin (k+1) → ℝ` and `β ≤ k`, the smallest ℓ¹ norm of a weight vector that
reproduces the endpoint contrast `r ↦ r.eval 1 - r.eval 0` of every degree-`≤ β`
polynomial (via the node values) equals the largest such contrast over
degree-`≤ β` polynomials bounded by `1` at the nodes:

`sInf (primalNormSet p β) = sSup (dualValSet p β)`.

This is the min-norm-representation `=` dual-sup identity — the ℓ¹/ℓ∞ pairing on
`ℝ^{k+1}` specialised to node-sampling — combining weak duality (representation
identity + triangle inequality) with strong duality (Hahn–Banach extension). -/
theorem l1_repr_eq_sup_dual (hp : Function.Injective p) (hβ : β ≤ k) :
    sInf (primalNormSet p β) = sSup (dualValSet p β) :=
  le_antisymm (sInf_primal_le_sSup_dual hp hβ) (sSup_dual_le_sInf_primal hp hβ)

/-- **Squared form.**  The square of the min-norm-representation value equals the
square of the dual sup.  This is the shape consumed downstream (the amplification
constant is the squared dual sup). -/
theorem l1_repr_sq_eq_sup_dual_sq (hp : Function.Injective p) (hβ : β ≤ k) :
    (sInf (primalNormSet p β)) ^ 2 = (sSup (dualValSet p β)) ^ 2 := by
  rw [l1_repr_eq_sup_dual hp hβ]

end Causalean.Mathlib.Analysis.FiniteDimL1LinfDuality
