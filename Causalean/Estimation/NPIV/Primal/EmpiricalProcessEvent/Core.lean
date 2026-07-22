/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Estimation.NPIV.Primal.EmpiricalProcessEvent.Regime

/-!
Re-exports the localized-regime structures used by the NPIV empirical-process
discharge. Downstream modules consume the bundled interpolation, critical
radius, closedness, and peeling hypotheses from `Regime` when constructing the
localized Ω-events and the final primal-rate event.
-/
