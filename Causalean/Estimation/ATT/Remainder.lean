/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# AIPW second-order remainder bound (ATT) — umbrella module

This file is the public entry point for the ATT AIPW remainder package.  The
population remainder identity sits in `Remainder/Identity.lean`, and the
quantitative L²-product bound plus its `o_p(n^{-1/2})` corollary sit in
`Remainder/Bound.lean`.  Mirrors `Estimation/ATE/Remainder.lean`.
-/

import Causalean.Estimation.ATT.Remainder.Identity
import Causalean.Estimation.ATT.Remainder.Bound

/-!
Roll-up for the ATT second-order AIPW remainder development. It re-exports
`aipw_remainder_identity_ATT`, which rewrites the population moment error as the
single cross-product of control-regression and propensity errors, and
`aipw_remainder_bound_ATT`, which bounds that identity by the corresponding
`L²(P_X)` product under one-sided overlap.

The stochastic corollary `aipw_remainder_op_ATT` packages the same product-rate
condition as an `o_p(n^{-1/2})` remainder for ATT double machine learning.
-/

namespace Causalean
namespace Estimation
namespace ATT

namespace TreatedEstimationSystem

-- Re-export module layout for convenience.

end TreatedEstimationSystem

end ATT
end Estimation
end Causalean
