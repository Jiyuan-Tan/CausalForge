/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.Basic
import CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.Collapse
import CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.ForbiddenSign
import CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.FourCohort
import CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.Helpers
import CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.Helpers.FiniteCollapse
import CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.Helpers.Frontier
import CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.Helpers.FrontierSign
import CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.Helpers.PoissonArgmaxDerivative
import CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.Helpers.WeightedFWL
import CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.Helpers.WeightedFWLContinuity
import CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.Homogeneous
import CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.PrimitiveFrontier
import CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.Projection
import Causalean.Stat.MEstimation.ArgmaxStability
import Causalean.Stat.MEstimation.FinitePoisson
import Causalean.Stat.MEstimation.FinitePoissonConsistency
import Causalean.Stat.MEstimation.FinitePoissonDerivative
import Causalean.Stat.MEstimation.FinitePoissonSign

/-! # Run barrel (auto-generated)

Aggregates every module of this causalsmith run so the whole run is ONE buildable target
(`lake build <this module>`). Research modules are not reachable from the top-level
`CausalSmith.lean` barrel, so the default lake target skips them and reports green on stale
oleans. Rewritten from the run's module set on every F-stage entry — do not hand-edit. -/
