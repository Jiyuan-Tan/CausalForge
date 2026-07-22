/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import CausalSmith.Experimentation.EXP_DesignPm1ExactnessBoundaryV1_Research.Helpers.SimplexActiveSetDefs
import Causalean.Mathlib.Optimization.WeightedSimplexExists

/-! # `WeightedSimplexExists` (re-export shim)

Promoted to `Causalean.Mathlib.Optimization.WeightedSimplexExists`. This file re-exports those
declarations into the paper namespace so the two-block design proofs keep
referencing them unqualified. -/

namespace CausalSmith.Experimentation.DesignPm1

export Causalean.Mathlib.Optimization (kktThreshold continuous_kktThreshold exists_admissible)

end CausalSmith.Experimentation.DesignPm1
