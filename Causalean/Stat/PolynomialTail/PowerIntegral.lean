/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Power-law interval integrals `∫ t^{-κ}` on a positive window

Pure real-analysis evaluation of the threshold integrals that the polynomial
lower-tail bounds reduce to.  No measure theory beyond `intervalIntegral`.  Two cases:

* `integral_rpow_neg_Ioc` (κ ≠ 1):  `∫ t in (a,b], t^{-κ} = (b^{1-κ} − a^{1-κ})/(1−κ)`.
* `integral_inv_neg_Ioc` (κ = 1):  `∫ t in (a,b], t^{-1} = log b − log a`.

Both require `0 < a ≤ b` (so `0 ∉ [[a,b]]`).  These feed the `λ^{κ-1}` / `log(1/λ)`
trichotomy once `a = t₀⁻¹`, `b = λ⁻¹`.
-/

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Power-law interval integrals

This module evaluates the deterministic interval integrals that appear after the polynomial-tail
layer-cake reduction.  The helper `zero_notMem_uIcc` supplies the positivity side condition needed
by `intervalIntegral` on a window `0 < a <= b`.

The two public evaluations are `integral_rpow_neg_Ioc`, for the non-logarithmic case
`kappa != 1`, and `integral_inv_neg_Ioc`, for the boundary case `kappa = 1`.  Together they
convert the threshold integral over `(t0^(-1), lam^(-1)]` into the
`lam^(kappa - 1)` / `log (1 / lam)` alternatives used by the `J` and `I` moment bounds.
-/

namespace Causalean.Stat.PolynomialTail

open MeasureTheory Set intervalIntegral

variable {κ : ℝ}

/-- `0 ∉ [[a,b]]` when `0 < a ≤ b`. -/
theorem zero_notMem_uIcc {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (0 : ℝ) ∉ Set.uIcc a b := by
  rw [Set.uIcc_of_le hab, Set.mem_Icc]
  exact fun h => absurd h.1 (not_le.mpr ha)

/-- **Power integral, `κ ≠ 1`.** If [the exponent `κ` is not equal to `1`](hyp:hκ), [`a` is
positive](hyp:ha), and [`a` is at most `b`](hyp:hab), then [the interval integral of `t ↦ t^{-κ}`
over `(a, b]` equals `(b^{1-κ} − a^{1-κ})/(1−κ)`](goal). -/
theorem integral_rpow_neg_Ioc (hκ : κ ≠ 1) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ t in Ioc a b, t ^ (-κ) = (b ^ (1 - κ) - a ^ (1 - κ)) / (1 - κ) := by
  rw [← intervalIntegral.integral_of_le hab,
    integral_rpow (Or.inr ⟨fun h => hκ (neg_inj.mp h), zero_notMem_uIcc ha hab⟩),
    show (-κ + 1 : ℝ) = 1 - κ from by ring]

/-- **Power integral, `κ = 1`.**  `∫ t in (a,b], t^{-1} = log b − log a`. -/
theorem integral_inv_neg_Ioc {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ t in Ioc a b, t ^ (-(1 : ℝ)) = Real.log b - Real.log a := by
  have hcongr : EqOn (fun t : ℝ => t ^ (-(1 : ℝ))) (fun t => t⁻¹) (Ioc a b) :=
    fun t _ => by simp [Real.rpow_neg_one]
  rw [setIntegral_congr_fun measurableSet_Ioc hcongr, ← intervalIntegral.integral_of_le hab,
    integral_inv (zero_notMem_uIcc ha hab),
    Real.log_div (ne_of_gt (lt_of_lt_of_le ha hab)) (ne_of_gt ha)]

end Causalean.Stat.PolynomialTail
