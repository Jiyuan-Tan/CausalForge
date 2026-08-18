/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Mathlib.Analysis.Normed.Ring.Units

/-!
# Quantitative inverse perturbation bound

The interior local-polynomial variance rate `(M⁻¹)₀₀ = O(1/(Nh))` is obtained by concentrating
the random design moment matrix `M` (entrywise, via the iid Chebyshev bound) around a fixed
positive-definite population matrix and transporting the bound through the matrix inverse. The
quantitative tool for that transport is the **resolvent (first-resolvent) inequality**

`‖a⁻¹ − b⁻¹‖ ≤ ‖a⁻¹‖ · ‖b⁻¹‖ · ‖a − b‖`,

valid for any two units `a, b` of a normed ring (`a⁻¹ − b⁻¹ = a⁻¹ (b − a) b⁻¹` and
submultiplicativity of the norm). This is the explicit-constant companion to Mathlib's
asymptotic `inverse_continuousAt` / `inverse_add_norm_diff_first_order`.
-/

namespace Causalean.Stat.Concentration

open scoped BigOperators

/-- **Resolvent inequality.** For [a seminormed ring `R`](hyp:R) and [units `a`
and `b` of `R`](hyp:a,b), [the norm of the difference of their inverses is
bounded above by the product of the norms of the two inverses and the norm of
their difference](goal). -/
theorem norm_unitInv_sub_unitInv_le {R : Type*} [SeminormedRing R] (a b : Rˣ) :
    ‖(↑a⁻¹ : R) - ↑b⁻¹‖ ≤ ‖(↑a⁻¹ : R)‖ * ‖(↑b⁻¹ : R)‖ * ‖(↑a : R) - ↑b‖ := by
  have hid : (↑a⁻¹ : R) - ↑b⁻¹ = ↑a⁻¹ * (↑b - ↑a) * ↑b⁻¹ := by
    have h1 : (↑a⁻¹ : R) * ↑a = 1 := by exact_mod_cast a.inv_mul
    have h2 : (↑b : R) * ↑b⁻¹ = 1 := by exact_mod_cast b.mul_inv
    calc
      (↑a⁻¹ : R) - ↑b⁻¹
          = (↑a⁻¹ : R) * ((↑b : R) * ↑b⁻¹) - ((↑a⁻¹ : R) * ↑a) * ↑b⁻¹ := by
              simp [h1, h2]
      _ = ↑a⁻¹ * (↑b - ↑a) * ↑b⁻¹ := by
              noncomm_ring
  calc ‖(↑a⁻¹ : R) - ↑b⁻¹‖
      = ‖(↑a⁻¹ : R) * (↑b - ↑a) * ↑b⁻¹‖ := by rw [hid]
    _ ≤ ‖(↑a⁻¹ : R) * (↑b - ↑a)‖ * ‖(↑b⁻¹ : R)‖ := norm_mul_le _ _
    _ ≤ ‖(↑a⁻¹ : R)‖ * ‖(↑b : R) - ↑a‖ * ‖(↑b⁻¹ : R)‖ := by
        gcongr; exact norm_mul_le _ _
    _ = ‖(↑a⁻¹ : R)‖ * ‖(↑b⁻¹ : R)‖ * ‖(↑a : R) - ↑b‖ := by
        rw [norm_sub_rev (↑b : R) (↑a : R)]; ring

end Causalean.Stat.Concentration
