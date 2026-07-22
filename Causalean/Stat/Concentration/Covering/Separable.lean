/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Countable-dense lifting for `sup` over uncountable separable index
  (thin re-export of `FoML.SeparableSpaceSup`)

Thin re-export of `FoML.SeparableSpaceSup`. Original lived under
`auto-res/lean-rademacher`, MIT License — see the FoML package
(`/<home>/lean-rademacher/`) for full provenance and `LICENSE`.

The FoML symbols (`separableSpaceSup_eq`, `separableSpaceSup_eq_real`)
live in the root namespace; downstream code accesses them unqualified.
-/

import FoML.SeparableSpaceSup

/-!
This file exposes countable-dense reductions for suprema over separable
function classes, letting empirical-process bounds stated on countable
subclasses apply to the full class of candidate estimators.
-/

namespace Causalean
namespace Stat
namespace Concentration

end Concentration
end Stat
end Causalean
