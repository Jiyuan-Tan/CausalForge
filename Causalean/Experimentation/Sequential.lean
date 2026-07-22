/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Experimentation.Sequential.Ville
import Causalean.Experimentation.Sequential.AnytimeValid
import Causalean.Experimentation.Sequential.AdaptiveDesign

/-!
# Adaptive (sequential) experiments with valid inference

The anytime-valid inference substrate for adaptive / sequential experiments, where the
treatment-assignment rule evolves with the accumulating data.  Probability comes from the
data-generating process and the time dimension is modeled by a filtration, so — unlike the finite,
fixed-design `DesignBased` substrate — this layer is measure-theoretic and rests on Mathlib's
martingale theory.

* `Ville` — test supermartingales and Ville's inequality (the time-uniform maximal inequality), the
  probabilistic engine of anytime-valid inference.
* `AnytimeValid` — anytime-valid tests (type-I error controlled under optional stopping) and
  confidence sequences (time-uniform coverage), both via Ville's inequality.
* `AdaptiveDesign` — the adaptive-experiment abstraction: a predictable propensity process, with
  the overlap (positivity) condition.
-/
