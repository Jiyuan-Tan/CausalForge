/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Experimentation.DesignBased
import Causalean.Experimentation.Sequential
import Causalean.Experimentation.ExposureMappingInterference
import Causalean.Experimentation.TwoStageInterference
import Causalean.Experimentation.UnknownInterference
import Causalean.Experimentation.MatchedPairDesign
import Causalean.Experimentation.BettingMean
import Causalean.Experimentation.ClusterRandomizedHT
import Causalean.Experimentation.FinitePopulationMoments
import Causalean.Experimentation.SuperPopulation

/-!
# Experimentation — randomization, sequential, and network inference

Umbrella for the experimentation cluster: shared finite-design/randomization-inference
substrates, anytime-valid sequential inference, interference-aware estimators, and
super-population network asymptotics.  Paper-specific modules record their bibliographic
attribution in their own docstrings.

* `DesignBased` — paper-agnostic substrate (`FiniteDesign` `E`/`Var`/`Cov`, exposure mappings,
  Horvitz–Thompson estimators, Chebyshev, the edge-sum variance bound, normal-CDF facts, the
  finite-design→measure bridge).
* `Sequential` — measure-theoretic substrate for adaptive / sequential experiments with valid
  inference: test supermartingales and Ville's inequality, anytime-valid tests and confidence
  sequences, and the adaptive-design abstraction.
* `ExposureMappingInterference` — exposure-mapping average effects under general interference,
  formalizing Aronow & Samii (2017).
* `TwoStageInterference` — two-stage / partial-interference designs and their large-sample layer,
  formalizing Hudgens & Halloran (2008) and Liu & Hudgens (2014).
* `UnknownInterference` — Bernoulli-design EATE estimation under unknown interference, formalizing
  the core of Sävje, Aronow & Hudgens (2021).
* `MatchedPairDesign` — matched-pair randomized trials, formalizing the design-based optimality
  results from Bai (2022).
* `BettingMean` — betting confidence sequences for bounded means, after Waudby-Smith & Ramdas
  (2024), as a worked application of the anytime-valid substrate.
* `ClusterRandomizedHT` — Horvitz–Thompson estimation for cluster-randomized experiments,
  formalizing Middleton & Aronow (2015).
* `FinitePopulationMoments` — exact simple-random-sample mean moments, after Li & Ding (2017).
* `SuperPopulation` — model-based (super-population) inference under network dependence: the
  locally-dependent network field (the m-dependent sibling of an i.i.d. sample), m-dependent CLTs
  for network sums and means via the Stein dependency-graph CLT, the network-HAC variance
  estimator, and HAC consistency theorems for the same asymptotic regime.

Further experimentation papers should be placed under method-facing module names, with the
bibliographic attribution in the module docstring.
-/
