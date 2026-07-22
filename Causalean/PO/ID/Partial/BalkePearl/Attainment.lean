/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Balke-Pearl IV bounds: the attainment layer

Re-exports the witness tables used to show the Balke-Pearl closed-form endpoints
are attained:

- `Attainment/Basic`  — the observed cells form a distribution per instrument value
- `Attainment/Lower`  — eight witnesses attaining the lower expressions
- `Attainment/Upper`  — eight witnesses attaining the upper expressions

`ClosedFormAttainment.lean` assembles these into the sharpness statements
`csInf_BPIdentifiedInterval_eq_bpLower` and `csSup_BPIdentifiedInterval_eq_bpUpper`.
-/

import Causalean.PO.ID.Partial.BalkePearl.Attainment.Basic
import Causalean.PO.ID.Partial.BalkePearl.Attainment.Lower
import Causalean.PO.ID.Partial.BalkePearl.Attainment.Upper

/-! # The Balke-Pearl attainment layer

This module collects the explicit latent tables witnessing that each of the
sixteen Balke-Pearl closed-form expressions is achieved by an observationally
equivalent model, on the region of observed distributions where that expression
is the extremal one. Together with the validity result these give sharpness of
the closed-form interval for the average treatment effect.
-/
