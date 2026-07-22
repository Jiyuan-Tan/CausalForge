/- 
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# AIPW second-order remainder bound

This file is the public entry point for the AIPW remainder package.  The
population remainder identity sits in `Remainder/Identity.lean`, and the
rate/big-O corollary sits in `Remainder/Bound.lean`.
-/

import Causalean.Estimation.ATE.Remainder.Identity
import Causalean.Estimation.ATE.Remainder.Bound

/-!
Public entry point for the AIPW second-order remainder theory for back-door
average treatment effect estimation.

It re-exports the exact population identity `aipw_remainder_identity`, the
plug-in bias bound `plugin_bias_le_eLpNorm`, the quantitative L² product bound
`aipw_remainder_bound`, and the stochastic product-rate corollary
`aipw_remainder_op` used in double machine learning.
-/

namespace Causalean
namespace Estimation
namespace ATE

namespace BackdoorEstimationSystem

-- Re-export module layout for convenience.

end BackdoorEstimationSystem

end ATE
end Estimation
end Causalean
