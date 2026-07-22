/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Re-export: `Causalean.Mathlib.CondIndep`

Aggregates the three sub-modules so that existing `import Causalean.Mathlib.CondIndep`
statements continue to work without change.

Sub-modules:
* `CondIndep.CondExp`      — condExp drop-of-conditioning + product factorization,
                             `condIndepFun_weak_union_of_prodMk`,
                             `condIndepFun_prodMk_of_measurable_left`
* `CondIndep.AELift`       — ae-equality/inequality lifts under overlap
* `CondIndep.Integrability` — indicator-condExp positivity + integrability
-/

import Causalean.Mathlib.CondIndep.CondExp
import Causalean.Mathlib.CondIndep.AELift
import Causalean.Mathlib.CondIndep.Integrability

/-!
This file gathers conditional-independence tools used across the causal library,
including conditional-expectation identities, almost-everywhere transfer under
overlap, and integrability facts.

It re-exports `CondIndep.CondExp` for drop-of-conditioning, product
factorization, weak union, extension, and contraction lemmas; `CondIndep.AELift`
for restricted-arm equality and bound transfers under overlap; and
`CondIndep.Integrability` for positivity and integrability consequences of
conditional-expectation indicator identities.
-/
