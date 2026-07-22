/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Balke-Pearl sharp ATE bounds for a binary IV (prop:po-iv-balke-pearl)

Re-exports the full Balke-Pearl sub-library:
- `Setup`       — `POBalkePearlSystem`, `ATE`, `cellProb`, `boolToReal`
- `Assumptions` — `BaseAssumptions` (consistency, exclusion, exogeneity, posZ)
- `LatentTable` — `latentProb`, `ATE_eq_sum_latent`, `cellProb_eq_sum_latent`
- `Main`        — `BPFeasible`, `BPObjective`, `ATE_mem_BPIdentifiedInterval`
- `Sharp`       — canonical model construction, `balkePearl_sharp`,
                   `balkePearl_sharp_of_mem`
- `IntervalForm` — closed-interval (`Set.Icc`) form of necessity via the
                   SandwichInterval engine bridge
- `ClosedForm`  — the explicit LP endpoints `bpLower`/`bpUpper` as a max/min of
                   eight affine functions of the observed cell probabilities
- `Attainment`  — the sixteen witness tables attaining the individual closed-form
                   expressions (`Basic`, `Lower`, `Upper`)
- `ClosedFormAttainment` — assembles them into `sInf = bpLower`, `sSup = bpUpper`
-/

import Causalean.PO.ID.Partial.BalkePearl.Setup
import Causalean.PO.ID.Partial.BalkePearl.Assumptions
import Causalean.PO.ID.Partial.BalkePearl.LatentTable
import Causalean.PO.ID.Partial.BalkePearl.Main
import Causalean.PO.ID.Partial.BalkePearl.Sharp
import Causalean.PO.ID.Partial.BalkePearl.IntervalForm
import Causalean.PO.ID.Partial.BalkePearl.ClosedForm
import Causalean.PO.ID.Partial.BalkePearl.Attainment
import Causalean.PO.ID.Partial.BalkePearl.ClosedFormAttainment

/-! # Balke-Pearl bounds for a binary instrument

This module re-exports the Balke-Pearl partial-identification development for
the average treatment effect in a binary instrumental-variable design. It
includes the binary-IV data layer `POBalkePearlSystem`, the structural
assumptions `BaseAssumptions`, the 16-cell latent response-type table, the
linear-program objective and feasible set, the necessity theorem
`ATE_mem_BPIdentifiedInterval`, the sharpness theorem `balkePearl_sharp`, the
closed-interval statement `ATE_mem_Icc_csInf_csSup`, the closed-form endpoints
`bpLower`/`bpUpper` computable directly from the observed data, and the proof
that these endpoints are exactly the linear-program minimum and maximum, so the
closed-form interval is sharp.
-/
