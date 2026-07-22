/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Order-2 U-statistics and the Hoeffding decomposition

The reusable statistical primitive underlying variance estimators, rank/sign
statistics, and kernel two-sample tests.  For a symmetric kernel `h : X → X → ℝ`
and an i.i.d. sample `S`, the order-2 U-statistic is

  Uₙ = (n(n−1))⁻¹ Σ_{i ≠ j, i,j < n} h(Zᵢ, Zⱼ).

The **Hoeffding decomposition** writes the kernel as

  h(x, y) = θ + h₁(x) + h₁(y) + g(x, y),

where `θ = ∬ h dP dP` is the population mean, `h₁(x) = ∫ h(x, ·) dP − θ` is the
first projection (centered), and `g` is the degenerate second-order kernel,
characterised by `∫ g(x, ·) dP = 0` for every `x`.  This file proves the
decomposition identity and the two mean-zero facts (`∫ h₁ dP = 0` and the
degeneracy of `g`); the CLT and variance bounds live in sibling files.
-/

import Causalean.Stat.Sample
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Order-2 U-statistics

This module defines the ordered off-diagonal order-2 statistic `uStatistic`, its
population mean `uMean`, first projection `uProj`, and degenerate residual
`uDegen`.  It proves the algebraic Hoeffding identity `hoeffding_decomp`, the
centering and integrability facts for the first projection, and
`uDegen_integral_right_eq_zero`, the one-coordinate degeneracy property of the
second-order residual.

Sibling files build the variance and asymptotic-normality theory on top of these
definitions; this file supplies the reusable decomposition substrate.
-/

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X}

/-! ## Definitions -/

/-- The order-2 U-statistic with kernel `h` over the first `n` sample points:
`(n(n−1))⁻¹ Σ_{(i,j) ∈ offDiag (range n)} h(Zᵢ, Zⱼ)`.  The off-diagonal sum
ranges over ordered pairs `i ≠ j`; for a symmetric kernel this is the usual
`(n choose 2)⁻¹ Σ_{i<j}`. -/
noncomputable def uStatistic (S : IIDSample Ω X μ P) (h : X → X → ℝ) (n : ℕ) :
    Ω → ℝ :=
  fun ω => ((n : ℝ) * ((n : ℝ) - 1))⁻¹ *
    ∑ p ∈ (Finset.range n).offDiag, h (S.Z p.1 ω) (S.Z p.2 ω)

/-- Population mean of the kernel: `θ = ∬ h dP dP`. -/
noncomputable def uMean (h : X → X → ℝ) (P : Measure X) : ℝ :=
  ∫ x, (∫ y, h x y ∂P) ∂P

/-- First Hoeffding projection (centered): `h₁(x) = ∫ h(x, ·) dP − θ`. -/
noncomputable def uProj (h : X → X → ℝ) (P : Measure X) : X → ℝ :=
  fun x => (∫ y, h x y ∂P) - uMean h P

/-- Degenerate second-order kernel: `g(x, y) = h(x, y) − θ − h₁(x) − h₁(y)`. -/
noncomputable def uDegen (h : X → X → ℝ) (P : Measure X) : X → X → ℝ :=
  fun x y => h x y - uMean h P - uProj h P x - uProj h P y

/-! ## Hoeffding decomposition -/

/-- **Hoeffding decomposition (pointwise identity).**
`h(x, y) = θ + h₁(x) + h₁(y) + g(x, y)`.  Purely algebraic. -/
theorem hoeffding_decomp (h : X → X → ℝ) (P : Measure X) (x y : X) :
    h x y = uMean h P + uProj h P x + uProj h P y + uDegen h P x y := by
  simp only [uDegen]; ring

/-- The first projection integrates to zero: `∫ h₁ dP = 0`. -/
theorem uProj_integral_eq_zero [IsProbabilityMeasure P] {h : X → X → ℝ}
    (hint : Integrable (fun x => ∫ y, h x y ∂P) P) :
    ∫ x, uProj h P x ∂P = 0 := by
  unfold uProj
  rw [integral_sub hint (integrable_const _), integral_const]
  simp [uMean]

/-- The first projection is integrable whenever `x ↦ ∫ h(x, ·) dP` is. -/
theorem uProj_integrable [IsProbabilityMeasure P] {h : X → X → ℝ}
    (hint : Integrable (fun x => ∫ y, h x y ∂P) P) :
    Integrable (uProj h P) P := by
  unfold uProj
  exact hint.sub (integrable_const _)

/-- **Degeneracy of the second-order kernel.**  For every fixed `x`,
`∫ g(x, ·) dP = 0`.  This is the defining property that makes the U-statistic's
quadratic remainder negligible at the `√n` scale. -/
theorem uDegen_integral_right_eq_zero [IsProbabilityMeasure P] {h : X → X → ℝ}
    (hint : Integrable (fun x => ∫ y, h x y ∂P) P)
    (x : X) (hx : Integrable (fun y => h x y) P) :
    ∫ y, uDegen h P x y ∂P = 0 := by
  have hproj_int : Integrable (uProj h P) P := uProj_integrable hint
  have hproj_zero : ∫ y, uProj h P y ∂P = 0 := uProj_integral_eq_zero hint
  have hconst : Integrable (fun _ : X => uMean h P + uProj h P x) P := integrable_const _
  have hib : Integrable (fun y => h x y - uProj h P y) P := hx.sub hproj_int
  have key : ∫ y, uDegen h P x y ∂P
      = (∫ y, h x y ∂P) - (∫ y, uProj h P y ∂P) - (uMean h P + uProj h P x) := by
    rw [show (fun y => uDegen h P x y)
          = (fun y => (h x y - uProj h P y) - (uMean h P + uProj h P x))
        from funext fun y => by simp only [uDegen]; ring]
    rw [integral_sub hib hconst, integral_sub hx hproj_int, integral_const,
        probReal_univ, one_smul]
  rw [key, hproj_zero]
  -- goal: (∫ h x y dP) - 0 - (θ + h₁ x) = 0, where h₁ x = (∫ h x y dP) - θ
  unfold uProj
  ring

end Causalean.Stat
