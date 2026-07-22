/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Estimation.NPIV.Primal.EmpiricalProcessEvent.EventAssembly

/-!
# Assembling `empirical_process_event` from `localized_uniform_deviation`

This umbrella module re-exports the localized empirical-process discharge
for the primal TRAE rate theorem.  The implementation is split by topic:

* `Core` re-exports the localized-regime structures and deterministic setup.
* `Algebra` contains the Young/AM-GM envelope used to absorb cross terms.
* `LocalizedEventF`, `LocalizedEventH`, and `LocalizedEventHF` transport
  per-class localized deviations to Ω-events.
* `EPMasterEvent` assembles the raw localized empirical-process event.
* `EPPerN` removes the empirical sup-objective excess at a fixed sample size.
* `EPInequality` proves the explicit empirical-process inequality.
* `Regulariser` proves the centred empirical regulariser bound.
* `EventAssembly` combines the empirical-process and regularizer bounds and
  exposes the final Rate.lean-shaped theorem.
-/
