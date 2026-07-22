/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Adaptive (sequential) experimental designs

In an **adaptive experiment** the treatment-assignment rule evolves with the accumulating data: the
probability of treating the unit arriving at time `t + 1` may depend on everything observed through
time `t`, but not on information revealed at assignment time or later.  The formal convention in
this file is Mathlib's discrete predictability convention: the initial propensity is measurable from
initial information, and the propensity at `t + 1` is measurable from the prior information
filtration at `t`.  Adaptivity is exactly what breaks fixed-design and i.i.d. inference and is the
reason valid sequential inference is built on the martingale layer (`Ville`, `AnytimeValid`): under
an adaptive design the inverse-propensity residuals form a martingale-difference sequence, so their
cumulative wealth is a supermartingale to which Ville's inequality applies.  This file records the
design abstraction and the positivity (overlap) condition that inverse-propensity weighting
requires.
-/

import Mathlib.Probability.Process.Predictable

/-! # Adaptive sequential designs

Adaptive experiments use assignment probabilities that are predictable from the pre-assignment
history: the time-zero propensity is initial-information measurable, and the time-`t + 1`
propensity is measurable from the information available at time `t`.

The structure `AdaptiveExperiment` packages the filtration and predictable propensity process,
while `AdaptiveExperiment.HasOverlap` records the positivity margin `δ ≤ propensity t ω ≤ 1 - δ`
needed for inverse-propensity weighting.  The lemma `propensity_pos_of_overlap` extracts strict
positivity from that overlap condition.
-/

open MeasureTheory

namespace Causalean
namespace Experimentation
namespace Sequential

/-- An adaptive sequential experiment consists of a measurable outcome space, a time-indexed
information flow, and treatment probabilities that are predictable from the pre-assignment history:
the initial propensity is initial-information measurable, and the propensity at time `t + 1` is
measurable using only the information available at time `t`.

Each recorded propensity is also bounded between zero and one. -/
structure AdaptiveExperiment (Ω : Type*) (m0 : MeasurableSpace Ω) where
  /-- The data-collection filtration: time `t` represents the information available after observing
  the time-`t` history and before the next assignment is made. -/
  ℱ : Filtration ℕ m0
  /-- The propensity process: `propensity t ω` is the probability of treating the time-`t` unit on
  history `ω`. -/
  propensity : ℕ → Ω → ℝ
  /-- The propensity is predictable: `propensity 0` is initial-information measurable, and
  `propensity (t + 1)` is determined by the information available at time `t`. -/
  propensity_predictable : IsPredictable ℱ propensity
  /-- Propensities are nonnegative. -/
  propensity_nonneg : ∀ t ω, 0 ≤ propensity t ω
  /-- Propensities are at most one. -/
  propensity_le_one : ∀ t ω, propensity t ω ≤ 1

namespace AdaptiveExperiment

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

/-- The experiment satisfies **overlap with margin `δ`** when every propensity stays at least `δ`
away from the boundary: `δ ≤ propensity t ω ≤ 1 − δ`.  This is the positivity condition that makes
inverse-propensity weighting (and hence the martingale construction underlying valid inference)
well-behaved. -/
def HasOverlap (E : AdaptiveExperiment Ω m0) (δ : ℝ) : Prop :=
  0 < δ ∧ ∀ t ω, δ ≤ E.propensity t ω ∧ E.propensity t ω ≤ 1 - δ

/-- Under overlap with margin `δ`, every propensity is at least `δ`, hence strictly positive — so
inverse-propensity weights are finite. -/
lemma propensity_pos_of_overlap {E : AdaptiveExperiment Ω m0} {δ : ℝ} (h : E.HasOverlap δ)
    (t : ℕ) (ω : Ω) : 0 < E.propensity t ω :=
  lt_of_lt_of_le h.1 (h.2 t ω).1

end AdaptiveExperiment

end Sequential
end Experimentation
end Causalean
