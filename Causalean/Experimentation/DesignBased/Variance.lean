/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Experimentation.DesignBased.Variance.Conservative

/-!
# Variance estimation

This namespace collects variance-estimation tools for finite design-based experiments.

* `Variance.Conservative` defines conservative variance estimators, proves basic certification
  lemmas, and derives a Chebyshev tail bound using an expected variance-estimator upper bound.
-/
