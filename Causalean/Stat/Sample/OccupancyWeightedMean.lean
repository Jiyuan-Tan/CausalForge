/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Stat.Sample.OccupancyWeightedMean.Variance

/-!
# Occupancy-weighted within-group means

This module provides totalized occupancy-weighted differences of within-group
sample means and a weak-second-moment variance bound under fixed overlap. The
API covers empty samples, empty group types, zero-mass groups, and empirical
zero-count boundaries without imposing bounded outcomes.
-/
