/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Estimation.NPIV.Primal.EmpiricalProcessEvent.EPPerN

/-!
Re-exports the explicit empirical-process inequality for the primal NPIV rate
argument. The imported `EPPerN` module provides
`ep_pop_inner_at_closedness_witness`,
`ep_per_n_inequality_from_deviations`, and
`ep_inequality_from_localized`, which convert the localized master event into
the weak-norm excess inequality used before the centered-regularizer discharge.
-/
