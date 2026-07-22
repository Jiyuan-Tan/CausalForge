/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# CausalSmith umbrella

Auto-generated theorem package. Each subdir corresponds to a theorem-substrate
cluster used by the `causalsmith research` pipeline:

* `CausalSmith.Panel.*` — panel / linear-projection theorems
* `CausalSmith.ExactID.*` — exact identification (backdoor, frontdoor, IV, DID,
  DTR, LATE, mediation) — populated as proposals graduate.
* `CausalSmith.PartialID.*` — partial identification / bounds (Manski,
  Balke–Pearl, IV bounds, sensitivity, shape restrictions, missing-data) —
  populated as proposals graduate.
* `CausalSmith.Stat.*` — minimax-rate / efficiency / limit-law theorems for
  causal estimands — populated as proposals graduate.
* `CausalSmith.Experimentation.*` — design-based randomization-inference
  theorems (CLT / asymptotic normality + Wald coverage for design-based causal
  estimands), built on `Causalean/Experimentation/` — populated as proposals
  graduate.
* `CausalSmith.Mathlib.*` — Mathlib-shaped helpers staged in CausalSmith
  before any promotion to `Causalean/Mathlib/`.

This umbrella imports every completed auto-generated research module so
`lake -d CausalSmith build` type-checks the completed corpus. Active research
runs are deliberately excluded until they finish. Causalean never imports
anything from this package.
-/

import CausalSmith.Research


-- Stat — minimax-rate / efficiency / limit-law theorems. T1 and T2 transitively
-- cover the cluster Basic, Helpers, Helpers_Part1–5, and the reachable
-- CausalSmith.Mathlib helpers (BernoulliKL, KLBind, IntegralBind, MemLp).
-- [d-stage-test hidden] import CausalSmith.Stat.STAT_AteOverlapDecay_Research.T1
-- [d-stage-test hidden] import CausalSmith.Stat.STAT_AteOverlapDecay_Research.T2

-- Stat — policy-regret rate under coupled margin / one-sided overlap decay.
-- The three T-files transitively cover the cluster Basic and Helpers.
import CausalSmith.Stat.STAT_PolicyRegretMarginOverlap_Research.T_minimax_lower
import CausalSmith.Stat.STAT_PolicyRegretMarginOverlap_Research.T_feasible_upper
import CausalSmith.Stat.STAT_PolicyRegretMarginOverlap_Research.T_feasible_tight

-- Mathlib-shaped substrate for the central-DP CATE minimax run: convex/Loewner
-- projection, monomial Gram positive-definiteness, multivariate Hölder–Taylor
-- monomial approximation, i.i.d. empirical-mean L² deviation.
import Causalean.Mathlib.Analysis.ConvexProjection
import Causalean.Mathlib.Analysis.MonomialGram
import Causalean.Stat.Nonparametric.Approximation.HolderTaylorMonomial
import Causalean.Mathlib.Probability.IidMeanVariance

-- Central-DP CATE minimax: the achievability (private local-polynomial) substrate.
import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.PopulationBias
import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.PrivateMechanism
import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.PrivateRiskBound
import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.Bracket

-- Causalean minimax helpers not yet reachable from any theorem (Le Cam
-- two-point converse infrastructure); imported here so bare `lake build`
-- still type-checks them through the CausalSmith umbrella.
import Causalean.Stat.Minimax.LeCamTwoPoint
