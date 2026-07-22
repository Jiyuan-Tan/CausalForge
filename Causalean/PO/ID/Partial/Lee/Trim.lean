/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Lee bounds: finite-support trim weights and trimmed means

Implements def:po-lee-trim from `Basic Concepts.tex`:

* selected-cell probabilities `p0`, `p1`, ratio `rho`;
* observable selected-treated outcome density `f1 y`;
* `LeeTrimWeight` -- the optimization variable: a non-negative weight
  bounded by 1, supported on a finite outcome set 𝒴, with weighted-mass
  constraint `∑ w(y) f1(y) = rho`;
* trimmed mean `Mw` of a weight, and the lower / upper trimmed means
  `lowerTrimMean`, `upperTrimMean` as `sInf` / `sSup` over feasible weights;
* the observable selected-control outcome mean `m0`.

This file contains *only definitions* -- no theorems are proved here.
-/

import Causalean.PO.ID.Partial.Lee.Setup

/-! # Lee Finite-Support Trim Functionals

This file defines the observable finite-support functionals used in Lee sample
selection bounds. It introduces the selected-cell probabilities `p0` and `p1`,
the trimming ratio `rho`, the selected-treated outcome mass function `f1`,
feasible `LeeTrimWeight`s, their mean functional `Mw`, the lower and upper
trimmed means `lowerTrimMean` and `upperTrimMean`, and the selected-control
mean `m0`.

The constructed always-selected trim weight and its identification theorem live
in `TrimWeight.lean` and `TrimMean.lean`. -/

namespace Causalean
namespace PO

open MeasureTheory

namespace POLeeSystem

variable {P : POSystem} (S : POLeeSystem P)

/-- Conditional selection probability `p_a := P(Sel = true | A = a)`
expressed via the event-conditional expectation of the selection
indicator. -/
noncomputable def pSelGivenA (a : Bool) : ℝ :=
  eventCondExp P.μ (S.aEvent a) (S.selVar.indicator true)

/-- `p₀ = P(Sel = true | A = false)`. -/
noncomputable def p0 : ℝ := S.pSelGivenA false

/-- `p₁ = P(Sel = true | A = true)`. -/
noncomputable def p1 : ℝ := S.pSelGivenA true

/-- The trimming ratio `ρ := p₀ / p₁`. -/
noncomputable def rho : ℝ := S.p0 / S.p1

/-- Observable conditional density of the outcome at `y` among selected
treated units: `f₁(y) := P(Y = y | A = true, Sel = true)`. -/
noncomputable def f1 (y : ℝ) : ℝ :=
  eventCondExp P.μ S.selectedTreated
    (fun ω => if S.factualY ω = y then (1 : ℝ) else 0)

/-- A Lee trim weight on a finite outcome support 𝒴 -- def:po-lee-trim.

Encodes a sub-distribution of total mass `ρ` dominated by the selected-
treated outcome density: a non-negative function `w : ℝ → ℝ`, bounded by
1, supported on `𝒴`, with weighted mass against `f₁` equal to `ρ`. -/
structure LeeTrimWeight (𝒴 : Finset ℝ) where
  w : ℝ → ℝ
  nonneg : ∀ y, 0 ≤ w y
  le_one : ∀ y, w y ≤ 1
  zero_off : ∀ y, y ∉ 𝒴 → w y = 0
  sum_eq : ∑ y ∈ 𝒴, w y * S.f1 y = S.rho

/-- The trimmed mean associated with a Lee trim weight:
`M(w) := ρ⁻¹ · ∑_{y ∈ 𝒴} y · w(y) · f₁(y)`. -/
noncomputable def Mw {𝒴 : Finset ℝ} (wt : S.LeeTrimWeight 𝒴) : ℝ :=
  (S.rho)⁻¹ * ∑ y ∈ 𝒴, y * wt.w y * S.f1 y

/-- Lower trimmed mean `underline_m₁ := inf_{w} M(w)` ranging over Lee trim
weights on `𝒴`. -/
noncomputable def lowerTrimMean (𝒴 : Finset ℝ) : ℝ :=
  sInf (Set.range (fun wt : S.LeeTrimWeight 𝒴 => S.Mw wt))

/-- Upper trimmed mean `overline_m₁ := sup_{w} M(w)` ranging over Lee trim
weights on `𝒴`. -/
noncomputable def upperTrimMean (𝒴 : Finset ℝ) : ℝ :=
  sSup (Set.range (fun wt : S.LeeTrimWeight 𝒴 => S.Mw wt))

/-- Observable selected-control outcome mean
`m₀ := E[Y | A = false, Sel = true]`. -/
noncomputable def m0 : ℝ :=
  eventCondExp P.μ S.selectedControl S.factualY

end POLeeSystem

end PO
end Causalean
