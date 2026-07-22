/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Mathlib.Optimization.SimplexActiveSetDefs

/-! # `SimplexActiveSetDefs` (re-export shim)

Promoted to `Causalean.Mathlib.Optimization.SimplexActiveSetDefs`. This file re-exports those
declarations into the paper namespace so the two-block design proofs keep
referencing them unqualified. -/

namespace CausalSmith.Experimentation.DesignPm1

export Causalean.Mathlib.Optimization (wsObj InSimplex IsAdmissibleSupport activeSetPoint exposedMinFace)

end CausalSmith.Experimentation.DesignPm1
