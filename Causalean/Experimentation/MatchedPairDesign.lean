/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Experimentation.MatchedPairDesign.MatchedPair
import Causalean.Experimentation.MatchedPairDesign.Estimator
import Causalean.Experimentation.MatchedPairDesign.Variance

/-!
# Bai (2022): fixed-pair matched-pair randomization

Worked application of the design-based randomization substrate to the fixed-pair matched-pair design
from Bai (2022), "Optimality of Matched-Pair Designs in Randomized Controlled Trials" (American
Economic Review).  The files define the design, estimator, unbiasedness result, and fixed-pairing
variance formula; they do not compare alternative pairings or prove Bai's optimal matching theorem.

* `MatchedPair` — the matched-pair design (a fair coin per pair selecting the treated position) and
  its inclusion structure: each unit treated with probability `½`, perfect within-pair negative
  dependence, and cross-pair independence — the negative dependence that lowers the
  difference-in-means variance.
* `Estimator` — the matched-pair difference-in-means estimator and its unbiasedness for the sample
  average treatment effect.
* `Variance` — the key result: `Var(τ̂) = (1/4N²) ∑ₚ (within-pair imbalance)²`, so the variance is
  determined by the fixed pairing's within-pair imbalances in `y1 + y0`.
-/
