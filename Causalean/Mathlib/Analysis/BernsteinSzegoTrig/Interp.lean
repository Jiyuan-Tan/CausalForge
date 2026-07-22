/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Mathlib

/-!
# The Szegő comparison interpolant

For the Szegő differential inequality one compares the trigonometric transform
`Q(t) = R(cos t)` with the *comparison interpolant* at a base point `t₀`,

`S(t) = Q₀ · cos(β(t − t₀)) + (Q₁/β) · sin(β(t − t₀))`,

where `Q₀ = Q(t₀)` and `Q₁ = Q'(t₀)`.  For `β ≥ 1` this `S` matches value and
derivative of `Q` at `t₀`, has constant amplitude `A = √(Q₀² + (Q₁/β)²)`, and is
an "elementary wave" `A · cos(β(t − t₀) − φ)`.  This file collects those purely
analytic facts (no zero-counting); the trigonometric-polynomial membership of `S`
and the final comparison live in `Szego`.

* `szegoInterp` — the interpolant.
* `szegoInterp_self` — `S(t₀) = Q₀`.
* `szegoInterp_hasDerivAt` — `S'(t₀) = Q₁` (for `β ≥ 1`).
* `szegoInterp_amplitude` — `S(t) = A · cos(β(t − t₀) − φ)` for a phase `φ`.
* `szegoInterp_abs_le` — `|S(t)| ≤ A`.

## Standard reference
Szegő's inequality; Rivlin, *The Chebyshev Polynomials* (1974); DeVore–Lorentz,
*Constructive Approximation* (1993), Ch. 4 (Bernstein–Szegő).
-/

open Real

namespace Causalean.Mathlib.Analysis.BernsteinSzegoTrig

/-- The **Szegő comparison interpolant** at base point `t₀` matching prescribed
value `Q₀` and derivative `Q₁`:
`S(t) = Q₀ · cos(β(t − t₀)) + (Q₁/β) · sin(β(t − t₀))`.
For `β ≥ 1` it satisfies `S(t₀) = Q₀`, `S'(t₀) = Q₁`, and is a trigonometric
wave with constant amplitude `√(Q₀² + (Q₁/β)²)`.  The degree-`≤ β`
trigonometric-polynomial statement is proved later as `szegoInterp_isTrigPolyLE`
in `Szego`. -/
noncomputable def szegoInterp (β : ℕ) (Q₀ Q₁ t₀ : ℝ) (t : ℝ) : ℝ :=
  Q₀ * Real.cos ((β : ℝ) * (t - t₀)) + (Q₁ / (β : ℝ)) * Real.sin ((β : ℝ) * (t - t₀))

/-- The Szegő interpolant reproduces its prescribed value at the base point:
`S(t₀) = Q₀`. -/
theorem szegoInterp_self (β : ℕ) (Q₀ Q₁ t₀ : ℝ) :
    szegoInterp β Q₀ Q₁ t₀ t₀ = Q₀ := by
  simp [szegoInterp]

/-- The Szegő interpolant reproduces its prescribed derivative at the base point:
`S'(t₀) = Q₁` (needs `β ≥ 1` so the factor `β` produced by the chain rule cancels
the `1/β` in the sine coefficient).

Concretely `S'(t) = -Q₀·β·sin(β(t−t₀)) + Q₁·cos(β(t−t₀))`, which at `t = t₀`
evaluates to `Q₁`. -/
theorem szegoInterp_hasDerivAt (β : ℕ) (hβ : 1 ≤ β) (Q₀ Q₁ t₀ : ℝ) :
    HasDerivAt (fun t => szegoInterp β Q₀ Q₁ t₀ t) Q₁ t₀ := by
  let c : ℝ := β
  have hc : c ≠ 0 := by
    have hβne : β ≠ 0 := Nat.one_le_iff_ne_zero.mp hβ
    have hβneR : (β : ℝ) ≠ 0 := by exact_mod_cast hβne
    simpa [c] using hβneR
  have hu : HasDerivAt (fun t : ℝ => c * (t - t₀)) c t₀ := by
    simpa [c] using (((hasDerivAt_id t₀).sub_const t₀).const_mul c)
  have hcos : HasDerivAt (fun t : ℝ => Real.cos (c * (t - t₀))) 0 t₀ := by
    have h := (Real.hasDerivAt_cos (c * (t₀ - t₀))).comp t₀ hu
    simpa using h
  have hsin : HasDerivAt (fun t : ℝ => Real.sin (c * (t - t₀))) c t₀ := by
    have h := (Real.hasDerivAt_sin (c * (t₀ - t₀))).comp t₀ hu
    simpa using h
  have hsum : HasDerivAt
      (fun t : ℝ =>
        Q₀ * Real.cos (c * (t - t₀)) + (Q₁ / c) * Real.sin (c * (t - t₀))) Q₁ t₀ := by
    have h := (hcos.const_mul Q₀).add (hsin.const_mul (Q₁ / c))
    simpa [hc] using h
  simpa [szegoInterp, c] using hsum

/-- The Szegő interpolant is an elementary wave of amplitude
`A = √(Q₀² + (Q₁/β)²)`: there is a phase `φ` with
`S(t) = A · cos(β(t − t₀) − φ)` for all `t`.

(Write the point `(Q₀, Q₁/β)` in polar form `A·(cos φ, sin φ)` and expand
`cos(β(t−t₀) − φ)` by the angle-subtraction formula.) -/
theorem szegoInterp_amplitude (β : ℕ) (Q₀ Q₁ t₀ : ℝ) :
    ∃ φ : ℝ, ∀ t, szegoInterp β Q₀ Q₁ t₀ t
      = Real.sqrt (Q₀ ^ 2 + (Q₁ / (β : ℝ)) ^ 2)
        * Real.cos ((β : ℝ) * (t - t₀) - φ) := by
  let q : ℝ := Q₁ / (β : ℝ)
  let z : ℂ := ⟨Q₀, q⟩
  refine ⟨Complex.arg z, ?_⟩
  intro t
  let x : ℝ := (β : ℝ) * (t - t₀)
  have hnorm : ‖z‖ = Real.sqrt (Q₀ ^ 2 + q ^ 2) := by
    simp [z, Complex.norm_def, Complex.normSq_mk, pow_two]
  have hcos : ‖z‖ * Real.cos (Complex.arg z) = Q₀ := by
    simp [z]
  have hsin : ‖z‖ * Real.sin (Complex.arg z) = q := by
    simp [z]
  calc
    szegoInterp β Q₀ Q₁ t₀ t = Q₀ * Real.cos x + q * Real.sin x := by
      simp [szegoInterp, q, x]
    _ = (‖z‖ * Real.cos (Complex.arg z)) * Real.cos x
        + (‖z‖ * Real.sin (Complex.arg z)) * Real.sin x := by
      rw [hcos, hsin]
    _ = ‖z‖ * Real.cos (x - Complex.arg z) := by
      rw [Real.cos_sub]
      ring
    _ = Real.sqrt (Q₀ ^ 2 + (Q₁ / (β : ℝ)) ^ 2)
        * Real.cos ((β : ℝ) * (t - t₀) - Complex.arg z) := by
      rw [hnorm]

/-- The Szegő interpolant is bounded in absolute value by its amplitude
`A = √(Q₀² + (Q₁/β)²)`. -/
theorem szegoInterp_abs_le (β : ℕ) (Q₀ Q₁ t₀ t : ℝ) :
    |szegoInterp β Q₀ Q₁ t₀ t| ≤ Real.sqrt (Q₀ ^ 2 + (Q₁ / (β : ℝ)) ^ 2) := by
  obtain ⟨φ, hφ⟩ := szegoInterp_amplitude β Q₀ Q₁ t₀
  rw [hφ t, abs_mul]
  have hA : 0 ≤ Real.sqrt (Q₀ ^ 2 + (Q₁ / (β : ℝ)) ^ 2) := Real.sqrt_nonneg _
  calc |Real.sqrt (Q₀ ^ 2 + (Q₁ / (β : ℝ)) ^ 2)| * |Real.cos ((β : ℝ) * (t - t₀) - φ)|
      ≤ |Real.sqrt (Q₀ ^ 2 + (Q₁ / (β : ℝ)) ^ 2)| * 1 := by
        apply mul_le_mul_of_nonneg_left (abs_cos_le_one _) (abs_nonneg _)
    _ = Real.sqrt (Q₀ ^ 2 + (Q₁ / (β : ℝ)) ^ 2) := by rw [mul_one, abs_of_nonneg hA]

end Causalean.Mathlib.Analysis.BernsteinSzegoTrig
