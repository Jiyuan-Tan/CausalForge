/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Mathlib.LinearAlgebra.VandermondeSynthesis

/-!
# Compatibility reexports for Vandermonde synthesis

The reusable synthesis map and kernel-dimension computation live in Causalean.
-/

namespace CausalSmith.ExactID.EID_LingamDirectionMinOrderV1

export Causalean.Mathlib.LinearAlgebra
  (endpointOrderSynthesis endpointOrderSynthesis_ker_finrank)

end CausalSmith.ExactID.EID_LingamDirectionMinOrderV1
