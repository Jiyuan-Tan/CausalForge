/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import CausalSmith.Experimentation.EXP_DesignPm1ExactnessBoundaryV1_Research.Helpers.SimplexActiveSetDefs
import CausalSmith.Experimentation.EXP_DesignPm1ExactnessBoundaryV1_Research.Helpers.WeightedSimplexCS
import Causalean.Mathlib.Optimization.WeightedSimplexKKT

/-! # `WeightedSimplexKKT` (re-export shim)

Promoted to `Causalean.Mathlib.Optimization.WeightedSimplexKKT`. This file re-exports those
declarations into the paper namespace so the two-block design proofs keep
referencing them unqualified. -/

namespace CausalSmith.Experimentation.DesignPm1

export Causalean.Mathlib.Optimization (activeSet_denom_pos activeSetPoint_pos_iff activeSetPoint_mem activeSetPoint_normSq activeSetPoint_value activeSetPoint_strict_min)

end CausalSmith.Experimentation.DesignPm1
