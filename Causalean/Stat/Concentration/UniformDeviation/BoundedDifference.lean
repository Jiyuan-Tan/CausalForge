/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Bounded-difference inequalities for the uniform deviation
  (thin re-export of `FoML.BoundedDifference`)

Thin re-export of `FoML.BoundedDifference` (and the auxiliary
`bounded_difference_of_bounded` lemma from `FoML.Rademacher`). Original
lived under `auto-res/lean-rademacher`, MIT License — see the FoML
package (`/<home>/lean-rademacher/`) for full provenance and
`LICENSE`.

The FoML symbols (`uniformDeviation_bounded_difference`,
`bounded_difference_of_bounded`) live in the root namespace and are
re-imported here for unqualified use.
-/

import Causalean.Stat.Concentration.Rademacher.Rademacher
import FoML.BoundedDifference
import FoML.Rademacher

/-! # Bounded differences for uniform deviations

This file re-exports FoML bounded-difference tools used to turn uniform
deviation functionals into high-probability bounds. The imported public
lemmas include `uniformDeviation_bounded_difference` and
`bounded_difference_of_bounded`, which handle empirical criteria whose value
changes by a controlled amount when one sample coordinate is replaced.
-/

namespace Causalean
namespace Stat
namespace Concentration

end Concentration
end Stat
end Causalean
