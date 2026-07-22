/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Estimation.NPIV.Primal.EmpiricalProcessEvent.LocalizedEventH
import Causalean.Estimation.NPIV.Primal.EmpiricalProcessEvent.LocalizedEventHF
import Causalean.Estimation.NPIV.Primal.EmpiricalProcessEvent.LocalizedEventMF
import Causalean.Estimation.NPIV.Primal.EmpiricalProcessEvent.LocalizedEventF

/-!
# Concrete Localized Deviation Events for Primal NPIV

This import module collects the Ω-side localized deviation events for the four
concrete function classes used by the primal NPIV empirical-process discharge:
candidate functions `H`, critic functions `F`, product losses `H · F`, and
moment-critic losses `m ∘ F`.  Importing this file exposes the single-index,
pair-gap, and peeled pair-gap event lemmas needed by the regularizer and rate
proofs without requiring callers to import each class-specific event file
separately.
-/
