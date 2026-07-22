/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Symmetrization bound (thin re-export of `FoML.Rademacher`)

Thin re-export of `_root_.expectation_le_rademacher` (Wainwright Theorem
4.10), defined in the MIT-licensed FoML development; see the FoML package
metadata for provenance and license terms.

The FoML headline (`expectation_le_rademacher`) lives in the root
namespace; downstream code accesses it unqualified.
-/

import FoML.Symmetrization
import FoML.Rademacher

/-!
This file exposes the symmetrization inequality used to replace empirical
process fluctuations by a Rademacher comparison, a standard step in deriving
uniform deviation bounds for estimators. The imported headline theorem is
`expectation_le_rademacher`, which lives in the root namespace as supplied by
FoML; this module keeps the Causalean concentration import tree self-contained
without introducing a duplicate alias.
-/

namespace Causalean
namespace Stat
namespace Concentration

end Concentration
end Stat
end Causalean
