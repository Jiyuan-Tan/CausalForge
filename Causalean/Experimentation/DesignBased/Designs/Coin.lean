/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Experimentation.DesignBased.DesignCore

/-! # Single-coin randomization design

This file defines the canonical two-point Bernoulli design and its expectation formula.
Product Bernoulli designs and paper-specific experimentation developments reuse this common
one-coordinate layer.
-/

open scoped BigOperators
open Finset

namespace Causalean
namespace Experimentation
namespace DesignBased

/-- The single-unit **coin design** on `Bool`: treatment (`true`) with probability `p`, control
(`false`) with probability `1 − p`. -/
def coinDesign (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : FiniteDesign Bool where
  p := fun b => cond b p (1 - p)
  p_nonneg := by
    intro b
    cases b
    · exact sub_nonneg.mpr hp1
    · exact hp0
  p_sum := by
    rw [Fintype.sum_bool]
    change p + (1 - p) = 1
    ring

/-- The expectation of a function of a single coin is its probability-weighted two-point sum. -/
lemma coinDesign_E (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (g : Bool → ℝ) :
    (coinDesign p hp0 hp1).E g = p * g true + (1 - p) * g false := by
  simp only [FiniteDesign.E, coinDesign, Fintype.sum_bool, cond_true, cond_false]

end DesignBased
end Experimentation
end Causalean
