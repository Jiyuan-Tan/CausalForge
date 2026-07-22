/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Finite-design Slutsky/CDF transfer helper (re-export)

The generic CDF-level converging-together step `finiteDesign_cdf_converging_together` was promoted to
`Causalean.Experimentation.DesignBased.Slutsky`. This file re-exports it so the bipartite experiment
sees it under the `Causalean.Experimentation.DesignBased` namespace it already opens.
-/

import Causalean.Experimentation.DesignBased.Slutsky
