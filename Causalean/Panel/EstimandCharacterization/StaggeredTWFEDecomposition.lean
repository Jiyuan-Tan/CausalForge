/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Goodman-Bacon (2021): staggered-timing TWFE decomposition — facade
-/

import Causalean.Panel.EstimandCharacterization.StaggeredTWFEDecomposition.CausalDecomposition
import Causalean.Panel.EstimandCharacterization.StaggeredTWFEDecomposition.PopulationBridge

/-!
# Goodman-Bacon (2021): staggered-timing TWFE decomposition — folder entry point

This folder formalizes the Goodman-Bacon decomposition of a two-way
fixed-effects (TWFE) coefficient estimated on a staggered-adoption panel. It is
organized in three layers, all resting on one finite base:

    FinitePanel.lean          finite base — CohortPanel record, weights, contrasts
                              (plain ℝ numbers; no probability space, no potential outcomes)
      │
      ├─ Pairwise.lean                 finite-algebra support (covariance → pairwise reduction)
      │   └─ AlgebraicDecomposition.lean   ★ ALGEBRAIC HEADLINE: TWFE = Σ weightᵢ · contrastᵢ
      │
      ├─ Causal.lean                   causal layer — potential-outcome corollaries
      │   └─ CausalDecomposition.lean      ★ CAUSAL HEADLINE (the paper's main result):
      │                                      TWFE = Σ weightᵢ · ATT-window-contrastᵢ,
      │                                      late-vs-early bad-comparison term explicit
      │
      └─ Support/{Basic,Integrals,Orthogonality,Partition,PerCell}.lean
          └─ PopulationBridge.lean         POPULATION BRIDGE: a real probability space Ω
                                           (random vars D, Y, G, T) under a balanced
                                           cohort-period law reproduces the finite numbers.
                                           Statistical (population), *not* causal, meaning.

**Where to start.** The two ★ theorems are the results:
`CausalDecomposition.lean` is the causal decomposition (what the paper is about),
`AlgebraicDecomposition.lean` is its assumption-free algebraic skeleton.
`PopulationBridge.lean` is the independent endpoint tying the finite algebra to a
genuine probability model.

Layers are labelled A (finite algebra: `FinitePanel`, `Pairwise`,
`AlgebraicDecomposition`), B (measure-theoretic bridge: `Support/`,
`PopulationBridge`), and C (causal: `Causal`, `CausalDecomposition`) in the
per-file docstrings.

NL artifact:
`doc/basic_concepts/po/estimand_characterization/goodman_bacon_twfe_timing.md`.
-/
