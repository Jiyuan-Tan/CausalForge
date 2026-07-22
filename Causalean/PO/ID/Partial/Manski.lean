/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Manski bound family — umbrella re-export

Aggregates the partial-identification results for the ATE under a
discrete instrumental variable (PO framework) described in
`doc/Basic Concepts.tex`, subsections `subsec:po-iv-manski`,
`subsec:po-iv-manski-shape`, and `rem:manski-bound-family`.

The submodules provide:

* `Setup` — `POManskiIVSystem` data + bound functionals.
* `Assumptions` — `BaseAssumptions` + the shape-restriction propositions
  `MeanIndep`, `MTR`, `MTS`, `MIV`.
* `Helpers` — shared measurability/integrability utilities and the
  mean-independence-free conditional stratum bounds.
* `NonAsp` — baseline Manski bounds (prop:po-iv-manski).
* `MTR` — monotone-treatment-response sharpening (prop:po-iv-mtr).
* `MTS` — monotone-treatment-selection sharpening (prop:po-iv-mts).
* `MIV` — monotone-IV envelope bounds (prop:po-iv-miv).
* `Combined` — MTR+MTS and MTR+MIV corollaries.
* `IntervalForm` — `Set.Icc` restatements of the ATE sandwiches.
-/

import Causalean.PO.ID.Partial.Manski.NonAsp
import Causalean.PO.ID.Partial.Manski.MTR
import Causalean.PO.ID.Partial.Manski.MTS
import Causalean.PO.ID.Partial.Manski.MIV
import Causalean.PO.ID.Partial.Manski.Combined
import Causalean.PO.ID.Partial.Manski.IntervalForm

/-!
This file is the umbrella module for the Manski partial-identification bound
family for treatment effects with a discrete instrument. It re-exports the data
layer and bound functionals from `Setup`, the reusable assumption bundles from
`Assumptions`, helper lemmas for stratum-wise bounds, and the theorem modules
for the baseline Manski sandwich, monotone treatment response, monotone
treatment selection, monotone instrumental variables, combined restrictions,
and interval-valued restatements.

Important exported results include the baseline `manski_bounds_ATE`,
the monotonicity sharpenings `mtr_nonneg_ATE` and
`mts_bounds_ATE`, the monotone-instrument envelope `miv_bounds_ATE`,
the combined bounds `mtr_mts_bounds_ATE` and `mtr_miv_bounds_ATE`, and the
closed-interval forms such as `manski_ATE_mem_Icc` and
`mtr_miv_ATE_mem_Icc`.
-/
