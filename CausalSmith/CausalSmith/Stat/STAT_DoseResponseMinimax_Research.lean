/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.Basic
import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.Frontier
import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.Helpers
import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.Helpers.Divergence
import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.Helpers.FrontierBracket
import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.Helpers.RateAlgebra
import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.Helpers.TwoPointConstruction
import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.Helpers.UpperBoundCited
import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.Helpers.Witness
import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.Helpers.Witness.Base
import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.Helpers.Witness.BumpHolder
import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.Helpers.Witness.Channel
import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.Helpers.Witness.Core
import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.Helpers.Witness.HolderAux
import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.Helpers.Witness.KL
import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.Helpers.Witness.Measure
import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.Helpers.Witness.Membership
import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.Helpers.Witness.PiCond
import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.Helpers.Witness.Regression
import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.Helpers.Witness.Theta
import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.T_CertifiedPartialBetaFrontier
import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.T_FrontierBracketDeficient
import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.T_OracleRegimeReduction
import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.T_SharpMinimaxSmoothCovariate
import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.T_SharpPointwiseLowerBound

/-! # Run barrel (auto-generated)

Aggregates every module of this causalsmith run so the whole run is ONE buildable target
(`lake build <this module>`). Research modules are not reachable from the top-level
`CausalSmith.lean` barrel, so the default lake target skips them and reports green on stale
oleans. Rewritten from the run's module set on every F-stage entry — do not hand-edit. -/
