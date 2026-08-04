/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Experimentation.DesignBased.Designs.Bernoulli
import Causalean.Experimentation.DesignBased.Designs.BernoulliMoments
import Causalean.Experimentation.DesignBased.Designs.CompleteRandomization
import Causalean.Experimentation.DesignBased.Designs.Stratified
import Causalean.Experimentation.DesignBased.Designs.ClusterRandomization

/-!
# The design zoo

Canonical, paper-agnostic randomization designs with their inclusion probabilities computed once,
ready to plug into the design-based estimation and optimality layers.

* `Bernoulli` — independent per-unit coin flips (`bernoulliDesign`); first/second-order inclusion
  probabilities `p i`, `p i · p j`, treatment-indicator variance `p i (1 − p i)`, and cross-unit
  independence.
* `CompleteRandomization` — exactly `n₁` of `N` units treated, uniform over size-`n₁` subsets
  (`completeRandomization`); inclusion probabilities `n₁ / N` and `n₁(n₁−1) / (N(N−1))`.
* `Stratified` — independent complete randomization within each stratum (`stratifiedDesign`);
  per-stratum inclusion probability `n₁ k / N k` and cross-stratum independence.
* `ClusterRandomization` — treatment assigned at the cluster level (`clusterDesign`); a unit's
  inclusion probability is its cluster's rate, with same-cluster perfect dependence and
  cross-cluster independence.
-/
