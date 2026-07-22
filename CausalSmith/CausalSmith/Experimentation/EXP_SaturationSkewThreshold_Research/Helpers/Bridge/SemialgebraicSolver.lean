/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import CausalSmith.Experimentation.EXP_SaturationSkewThreshold_Research.Basic
import Mathlib.Topology.Order.Compact

namespace CausalSmith.Experimentation.SaturationSkew
open MeasureTheory
open scoped BigOperators

-- @node: lem:semialgebraic-optimization-algorithms
/-- SUBSTRATE-GATE (Tarski–Seidenberg / cylindrical algebraic decomposition),
realized as a threaded `Prop` assumption (NOT a discharged lemma): a continuous
objective over a nonempty compact semialgebraic feasible set attains a minimizer
via a terminating exact procedure. Consumer
(`thm:constructive-optimal-design-algorithm`) takes this as an inline hypothesis.
Visible substrate debt; excluded from the theorem manifest. -/
def SemialgebraicOptimizationAlgorithms : Prop :=
  ∀ {n : ℕ} (S : Set (Fin n → ℝ)), IsCompact S → S.Nonempty →
    ∀ (obj : (Fin n → ℝ) → ℝ), Continuous obj → ∃ x ∈ S, ∀ y ∈ S, obj x ≤ obj y

end CausalSmith.Experimentation.SaturationSkew
