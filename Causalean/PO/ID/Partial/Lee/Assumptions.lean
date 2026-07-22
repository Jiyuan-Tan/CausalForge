/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Lee bounds: assumption bundles

`BaseAssumptions` collects the common data needed by prop:po-lee-bounds:

* `consistency` -- the standard PO consistency axiom;
* `randAssign` -- pair-level random assignment
  `A ⫫ (Y(a), Sel(a))` for each `a ∈ {0,1}`.
  This is the minimal shape that still carries the *distributional*
  information Lee trimming consumes (mean independence is **not**
  enough -- see the discussion in the plan file).  The doc's full
  4-tuple joint independence implies this pair form by `IndepFun.comp`;
* positivity of the two selected cells `selectedTreated`,
  `selectedControl` (and finiteness, used in arithmetic on `.toReal`);
* integrability of `Y(0)`, `Y(1)`, and the factual outcome.

`MonotoneSelection` is a separate `Prop` capturing
`Sel(0) ≤ Sel(1)` a.s. -- it is a shape restriction, not a randomness
hypothesis, and pairs with `BaseAssumptions` in the main theorem.
-/

import Causalean.PO.ID.Partial.Lee.Setup
import Causalean.PO.Conditioning.CondExpTooling

/-! # Lee Bounds Assumptions

This file defines the assumptions used for Lee sample-selection bounds. The
baseline bundle contains consistency, pair-level random assignment, positivity,
finiteness, and integrability conditions, while monotone selection is kept as a
separate shape restriction.

The structure `BaseAssumptions` stores the consistency axiom, distributional
random-assignment condition for `(Y(a), Sel(a))`, positive selected cells and
treatment arms, finiteness of selected-cell measures, and integrability of the
two potential outcomes. Its helper lemmas `integrable_YofA` and `integrableY`
recover binary-indexed arm integrability and factual-outcome integrability. The
structure `MonotoneSelection` records the Lee monotonicity condition
`Sel(0) <= Sel(1)` almost surely. -/

namespace Causalean
namespace PO

open MeasureTheory ProbabilityTheory

namespace POLeeSystem

variable {P : POSystem}

/-- Lee sample-selection baseline assumptions -- def:po-lee-assumptions. -/
structure BaseAssumptions (S : POLeeSystem P) where
  /-- The PO system satisfies the consistency axiom. -/
  consistency : P.Consistency
  /-- Pair-level random assignment: for each `a : Bool`, the factual
  treatment `A` is independent of the pair `(Y(a), Sel(a))`. This is
  weaker than the doc's 4-tuple joint indep but strictly stronger than
  mean independence; it carries the full conditional distribution of
  `(Y(a), Sel(a))` given `A`, which Lee trimming requires. -/
  randAssign : ∀ a : Bool,
    IndepFun S.factualA (fun ω => (S.YofA a ω, S.SelOfA a ω)) P.μ
  /-- Selected-treated cell `{A = true, Sel = true}` has positive measure. -/
  posSelectedTreated : P.μ S.selectedTreated ≠ 0
  /-- Selected-control cell `{A = false, Sel = true}` has positive measure. -/
  posSelectedControl : P.μ S.selectedControl ≠ 0
  /-- The treated arm `{A = true}` has positive measure (denominator of `p₁`). -/
  posATrue : P.μ (S.aEvent true) ≠ 0
  /-- The control arm `{A = false}` has positive measure (denominator of `p₀`). -/
  posAFalse : P.μ (S.aEvent false) ≠ 0
  /-- Selected-treated cell has finite measure. -/
  posSelTrFinite : P.μ S.selectedTreated ≠ ⊤
  /-- Selected-control cell has finite measure. -/
  posSelCtFinite : P.μ S.selectedControl ≠ ⊤
  /-- `Y(1)` is integrable. -/
  integrableY1 : Integrable (S.YofA true) P.μ
  /-- `Y(0)` is integrable. -/
  integrableY0 : Integrable (S.YofA false) P.μ

namespace BaseAssumptions

variable {S : POLeeSystem P}

/-- Binary-folded form of `integrableY1` / `integrableY0`. -/
lemma integrable_YofA (hA : S.BaseAssumptions) (a : Bool) :
    Integrable (S.YofA a) P.μ := by
  cases a
  · exact hA.integrableY0
  · exact hA.integrableY1

/-- The factual outcome `Y` is integrable.  Derived from arm integrability via
consistency (`factualY = Σ_a Y(a)·1{A=a}` a.e.), so it need not be assumed
separately. -/
lemma integrableY (hA : S.BaseAssumptions) :
    Integrable S.factualY P.μ := by
  have hY1_ind :
      Integrable (fun ω => S.YofA true ω * S.aVar.indicator true ω) P.μ :=
    S.aVar.integrable_mul_indicator true hA.integrableY1 (S.measurable_YofA true)
  have hY0_ind :
      Integrable (fun ω => S.YofA false ω * S.aVar.indicator false ω) P.μ :=
    S.aVar.integrable_mul_indicator false hA.integrableY0 (S.measurable_YofA false)
  refine (hY1_ind.add hY0_ind).congr ?_
  filter_upwards with ω
  have htrue := congr_fun
    (POVar.factual_mul_indicator_eq_cfUnder_mul_indicator_fn
      hA.consistency S.yVar S.aVar true (Ne.symm S.hAY)) ω
  have hfalse := congr_fun
    (POVar.factual_mul_indicator_eq_cfUnder_mul_indicator_fn
      hA.consistency S.yVar S.aVar false (Ne.symm S.hAY)) ω
  have htrue' : S.YofA true ω * S.aVar.indicator true ω =
      S.factualY ω * S.aVar.indicator true ω := by
    simpa [POLeeSystem.YofA, POLeeSystem.factualY] using htrue.symm
  have hfalse' : S.YofA false ω * S.aVar.indicator false ω =
      S.factualY ω * S.aVar.indicator false ω := by
    simpa [POLeeSystem.YofA, POLeeSystem.factualY] using hfalse.symm
  have hsum := S.aVar.indicator_add_indicator_not ω
  calc
    S.YofA true ω * S.aVar.indicator true ω
        + S.YofA false ω * S.aVar.indicator false ω
        = S.factualY ω * S.aVar.indicator true ω
          + S.factualY ω * S.aVar.indicator false ω := by rw [htrue', hfalse']
    _ = S.factualY ω * (S.aVar.indicator true ω + S.aVar.indicator false ω) := by ring
    _ = S.factualY ω := by rw [hsum, mul_one]

end BaseAssumptions

/-- Monotone sample selection -- def:po-lee-assumptions, item 3.
`Sel(0) ≤ Sel(1)` almost surely (with `≤` interpreted on `Bool` via the
canonical `false ≤ true` order). -/
structure MonotoneSelection (S : POLeeSystem P) : Prop where
  monotone : ∀ᵐ ω ∂P.μ, S.SelOfA false ω ≤ S.SelOfA true ω

end POLeeSystem

end PO
end Causalean
