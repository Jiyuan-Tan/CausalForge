/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Anytime-valid tests and confidence sequences

The inferential payoff of Ville's inequality.  An **anytime-valid test** at level `α` rejects the
null the first time a test supermartingale's wealth reaches `1/α`; because Ville's inequality bounds
the probability that the wealth *ever* reaches `1/α`, the test's type-I error is at most `α` no
matter when the analyst chooses to stop — inference remains valid under optional stopping.  Dually, a
**confidence sequence** is a time-indexed family of sets that covers the true parameter at all times
simultaneously with probability at least `1 − α`; inverting a family of test supermartingales (keep
the parameter values whose wealth has not yet reached `1/α`) yields one, with miscoverage controlled
by Ville's inequality.
-/

import Causalean.Experimentation.Sequential.Ville

/-!
# Anytime-valid tests and confidence sequences

This file turns Ville's inequality for test supermartingales into reusable sequential-inference
objects.  `rejectionRegion` is the event that wealth ever crosses `1/α`, `IsAnytimeValid` states
level-`α` type-I error control, and `isAnytimeValid_rejectionRegion` proves that control from
Ville's inequality.  The confidence-sequence side defines `IsConfidenceSequence`,
`confSeqOfWealth`, and `isConfidenceSequence_confSeqOfWealth`, the inverted coverage theorem.
-/

open MeasureTheory
open scoped NNReal ENNReal ProbabilityTheory

namespace Causalean
namespace Experimentation
namespace Sequential

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℕ m0}

/-! ### Anytime-valid testing -/

/-- The **rejection region** of the sequential test driven by wealth `M` at level `α`: the test
rejects on the event that `M` ever reaches `1/α`. -/
def rejectionRegion (M : ℕ → Ω → ℝ) (α : ℝ) : Set Ω := {ω | ∃ n, 1 / α ≤ M n ω}

/-- A rejection region is **anytime-valid at level `α`** under `μ` when its probability is at most
`α`. -/
def IsAnytimeValid (R : Set Ω) (μ : Measure Ω) (α : ℝ) : Prop := μ R ≤ ENNReal.ofReal α

/-- **Anytime-valid type-I error control.** The event that a test supermartingale's wealth ever
reaches `1/α` has probability at most `α`. -/
theorem isAnytimeValid_rejectionRegion [IsFiniteMeasure μ] {M : ℕ → Ω → ℝ}
    (hM : IsTestSupermartingale M ℱ μ) {α : ℝ} (hα : 0 < α) :
    IsAnytimeValid (rejectionRegion M α) μ α :=
  ville_test hM hα

/-! ### Confidence sequences -/

/-- A predicate `cover : ℕ → Ω → Prop` (with `cover n ω` meaning "the target lies in the time-`n`
set on outcome `ω`") is a **confidence sequence at level `α`** when the miscoverage probability —
that the cover ever fails — is at most `α`. -/
def IsConfidenceSequence (cover : ℕ → Ω → Prop) (μ : Measure Ω) (α : ℝ) : Prop :=
  μ {ω | ∃ n, ¬ cover n ω} ≤ ENNReal.ofReal α

/-- The wealth-based cover predicate obtained by inversion.  At time `n`, the cover holds exactly
when the wealth `M n` has not yet reached `1/α`. -/
def confSeqOfWealth (M : ℕ → Ω → ℝ) (α : ℝ) : ℕ → Ω → Prop := fun n ω => M n ω < 1 / α

/-- **Confidence-sequence coverage.** The cover obtained by requiring a test supermartingale's
wealth to stay below `1/α` fails at some time with probability at most `α`. -/
theorem isConfidenceSequence_confSeqOfWealth [IsFiniteMeasure μ] {M : ℕ → Ω → ℝ}
    (hM : IsTestSupermartingale M ℱ μ) {α : ℝ} (hα : 0 < α) :
    IsConfidenceSequence (confSeqOfWealth M α) μ α := by
  have hset : {ω | ∃ n, ¬ confSeqOfWealth M α n ω} = {ω | ∃ n, 1 / α ≤ M n ω} := by
    ext ω; simp only [confSeqOfWealth, Set.mem_setOf_eq, not_lt]
  rw [IsConfidenceSequence, hset]
  exact ville_test hM hα

end Sequential
end Experimentation
end Causalean
