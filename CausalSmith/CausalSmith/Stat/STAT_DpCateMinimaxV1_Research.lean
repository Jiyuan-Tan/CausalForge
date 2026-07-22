/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Basic
import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers
import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.ArmDisintegration
import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.ArmDisintegrationTV
import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.Bandwidth
import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.Bracket
import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.BumpHolder
import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.BumpHolderAux
import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.CateWitness
import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.CausalLowerBound
import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.CausalNullLaw
import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.DivergenceLocalized
import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.DivergenceProduct
import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.DpContraction
import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.DpContractionAux
import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.EqualSmoothnessAlgebra
import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.HolderInterpolation
import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.MinimaxReduction
import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.PopulationBias
import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.PopulationDesign
import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.PopulationGram
import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.PrivateMechanism
import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.PrivateRisk
import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.PrivateRiskBound
import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.PrivateUpperBound
import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.PrivateUpperEndpoint
import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.PrivateWitness
import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.RandomizedLeCam
import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.RateAlgebra
import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.RegressionCalibrationBounds
import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.RegressionEmbedding
import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.TVSharp
import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.TwoPointDivergence
import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.TwoPointDivergenceAux
import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.T_CausalDpTwoPointBarrier

/-! # Run barrel (auto-generated)

Aggregates every module of this causalsmith research run so the whole run is ONE buildable target
(`lake build <this module>`). Research modules are not reachable from the top-level
`CausalSmith.lean` barrel, so the default lake target skips them and reports green on stale
oleans. Rewritten from the run's module set on every F-stage entry — do not hand-edit. -/
