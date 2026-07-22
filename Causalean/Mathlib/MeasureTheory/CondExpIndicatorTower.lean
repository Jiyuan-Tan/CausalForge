/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator

/-!
# Conditioning ↔ inner-regression weighting across a σ-algebra tower

The theorem `condExp_setIndicator_condExp_of_le` is a generic
conditional-expectation identity (no probability/causal content): for a tower of
σ-algebras `m ≤ m'`, an `m'`-measurable set `s`, and integrable `f`, conditioning the
masked outcome `1_s · f` on the coarse `m` is the same as first replacing `f` by its
inner regression `μ[f | m']` and then conditioning on `m`:

    μ[1_s · f | m]  =ᵐ  μ[1_s · μ[f | m'] | m].

This is the measure-theoretic kernel behind "regression adjustment = inverse-
propensity weighting": with `m = σ(X)`, `m' = σ(D, X)`, `s = {D = d}`, dividing both
sides by `μ[1_s | m] = P[D=d | σX]` turns the left side into the IPW/adjustment
functional and the right side into the outcome regression. It recurs across ATE /
ATT / DTR back-door arguments, so it is factored out here as a reusable lemma and a
candidate Mathlib contribution.

Proof is the inner `condExp_indicator` (`s` is `m'`-measurable) followed by the
tower `condExp_condExp_of_le`.
-/


open MeasureTheory

namespace MeasureTheory

variable {Ω : Type*} {m m' m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Conditioning a masked outcome equals conditioning its inner regression.**
For `m ≤ m' ≤ m0`, an `m'`-measurable set `s`, and integrable `f`,

    μ[s.indicator f | m]  =ᵐ[μ]  μ[s.indicator (μ[f | m']) | m].

(Here `s.indicator g = 1_s · g`.) The right-hand `μ[f | m']` is the inner
regression on the finer σ-algebra; masking and projecting to the coarser `m`
commute with passing to it. -/
theorem condExp_setIndicator_condExp_of_le
    (hm : m ≤ m') (hm' : m' ≤ m0) [SigmaFinite (μ.trim hm')]
    {s : Set Ω} (hs : MeasurableSet[m'] s) {f : Ω → ℝ} (hf : Integrable f μ) :
    (μ[s.indicator f | m]) =ᵐ[μ] (μ[s.indicator (μ[f | m']) | m]) := by
  exact (MeasureTheory.condExp_condExp_of_le (μ := μ) (f := s.indicator f) hm hm').symm.trans
    (MeasureTheory.condExp_congr_ae (m := m) (μ := μ)
      (MeasureTheory.condExp_indicator (m := m') (μ := μ) hf hs))

end MeasureTheory
