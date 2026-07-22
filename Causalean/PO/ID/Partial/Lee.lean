/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Lee bounds — umbrella re-export

Aggregates the partial-identification result of `subsec:po-lee-bounds`
in `doc/Basic Concepts.tex`: a sandwich bound for the always-selected
ATT under sample selection, given monotone selection plus pair-level
random assignment plus a finite-support restriction on the
selected-treated outcome.

The submodules provide:

* `Setup` — `POLeeSystem` data + factual / counterfactual accessors +
  observable cells `selectedTreated`, `selectedControl`.
* `Assumptions` — `BaseAssumptions` (consistency, pair-level random
  assignment, positivity, integrability) + `MonotoneSelection`.
* `Trim` — selected-cell probabilities, ratio `ρ`, observable density
  `f₁`, `LeeTrimWeight`, mean `Mw`, trimmed means
  `lowerTrimMean` / `upperTrimMean`, observable selected-control mean `m₀`.
* `PrincipalStrata` — latent events `alwaysSelected`, `helpedSelected`,
  `harmedSelected`, plus the monotone-selection a.s. identities
  collapsing latent events to observables.
* `ControlMean` — Step A: identifies `m₀ = E[Y(0) | alwaysSelected]`.
* `MixtureIdentity` — Step B/B'/indicator: latent decomposition of the
  selected-treated cell.
* `LatentSupport` — finite outcome support transfers to the latent
  strata under monotone selection.
* `TrimWeight` — `f1AS` density + `alwaysSelectedTrimWeight` witness
  (the four field proofs `nonneg`, `le_one`, `zero_off`, `sum_eq`).
* `TrimMean` — `Mw_alwaysSelectedTrimWeight_eq_condExp_Y1_AS`: the
  witness's trimmed mean equals `E[Y(1)|alwaysSelected]`.
* `TrimBound` — `trimmed_bounds_condExp_Y1_AS`: sandwich bound for
  `E[Y(1)|alwaysSelected]` between `lowerTrimMean` and `upperTrimMean`.
* `Main` — `lee_bounds_ATT_AS` (prop:po-lee-bounds): final assembly.

Quantile form (rem:po-lee-quantile) is deferred to a follow-on file.
-/

import Causalean.PO.ID.Partial.Lee.Setup
import Causalean.PO.ID.Partial.Lee.Assumptions
import Causalean.PO.ID.Partial.Lee.Trim
import Causalean.PO.ID.Partial.Lee.PrincipalStrata
import Causalean.PO.ID.Partial.Lee.ControlMean
import Causalean.PO.ID.Partial.Lee.MixtureIdentity
import Causalean.PO.ID.Partial.Lee.LatentSupport
import Causalean.PO.ID.Partial.Lee.TrimWeight
import Causalean.PO.ID.Partial.Lee.TrimMean
import Causalean.PO.ID.Partial.Lee.TrimBound
import Causalean.PO.ID.Partial.Lee.Main

/-! # Lee Bounds

This file re-exports the Lee bounds development for treatment effects under
sample selection. The subtree starts from `POLeeSystem`, observable selected
treated/control cells, baseline assumptions, and monotone selection; builds the
latent principal strata `alwaysSelected`, `helpedSelected`, and `harmedSelected`;
defines selected-cell probabilities, the Lee trimming ratio, trimmed treated
means, and the selected-control mean; and proves the final finite-support Lee
bound.

The final theorem is `POLeeSystem.lee_bounds_ATT_AS`: under consistency,
pair-level random assignment, selected-cell positivity, integrability, monotone
selection, and finite observed support for selected treated outcomes, the
always-selected ATT lies between `lowerTrimMean 𝒴 - m0` and
`upperTrimMean 𝒴 - m0`.
-/
