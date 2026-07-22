/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# McDiarmid's bounded-difference inequality (thin re-export of `FoML.McDiarmid`)

Thin re-export of `FoML.McDiarmid`. Original lived under
`auto-res/lean-rademacher`, MIT License — see the FoML package
(`/<home>/lean-rademacher/`) for full provenance and `LICENSE`.

The FoML symbols (`mcdiarmid_inequality_pos`, `mcdiarmid_inequality_neg`,
`mcdiarmid_inequality_pos'`, `mcdiarmid_inequality_aux`) live in the root
namespace and are re-imported here for unqualified use.
-/

import FoML.McDiarmid

/-! # McDiarmid bounded-difference inequalities

This file re-exports FoML's McDiarmid bounded-difference concentration
lemmas for use by the Causalean concentration hierarchy. The available FoML
theorems include `mcdiarmid_inequality_pos`, `mcdiarmid_inequality_neg`,
`mcdiarmid_inequality_pos'`, and `mcdiarmid_inequality_aux`, which control
deviations of functions whose value changes only modestly when one coordinate
of the sample is changed.
-/

namespace Causalean
namespace Stat
namespace Concentration

end Concentration
end Stat
end Causalean
