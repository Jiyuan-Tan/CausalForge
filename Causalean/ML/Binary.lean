/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.ML.Binary.Logistic
import Causalean.ML.Binary.FisherConsistency
import Causalean.ML.Binary.Rate

/-! # `Causalean.ML.Binary` — logistic losses and rates

Roll-up of the logistic part of `Causalean.ML`: convexity and compact-set
existence for empirical logistic risk, pointwise Fisher consistency of the
Bernoulli cross-entropy loss, and the root-n L² estimation rate for an
L²-regularized logistic quasi-score M-estimator. The rate file allows a
real-valued response coordinate, so this namespace is about logistic prediction
and binary-loss geometry rather than only zero-one classification.
-/
