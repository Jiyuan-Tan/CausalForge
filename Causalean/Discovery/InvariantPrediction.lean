/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Discovery.InvariantPrediction.Model
import Causalean.Discovery.InvariantPrediction.Invariance
import Causalean.Discovery.InvariantPrediction.IdentifiedSet
import Causalean.Discovery.InvariantPrediction.Soundness
import Causalean.Discovery.InvariantPrediction.LinearGaussian

/-!
# Invariant Causal Prediction — umbrella

Entry point for the formalization of Peters, Bühlmann & Meinshausen, *Causal
inference using invariant prediction: identification and confidence intervals*
(JRSS-B 2016, `arXiv:1501.01332`).  Import this file to get the whole
development.  This is the third identification engine in `Causalean.Discovery`,
beside non-Gaussianity (`LiNGAM`) and interventions-plus-second-moments
(`LinearDisentanglement`): here causal structure is identified from the
**invariance of the causal mechanism across interventional environments**.

## Main results

* `EnvFamily` (`Model.lean`) — the model: a `Fintype`-indexed family of SCMs over
  common observed/latent variables that share the target's mechanism, parents and
  noise law (no environment intervenes on the target), each carrying its
  intervention's fixed values.
* `EnvFamily.Invariant` (`Invariance.lean`) — a predictor set `S` is invariant
  when the conditional law of the target given `X_S` is the same in every
  environment; `mechanism_invariant` shows the target's observed parents are
  always invariant.
* `EnvFamily.icp_sound` (`Soundness.lean`) — **Theorem 1 (soundness).** The
  identified set `S(E) = ⋂{invariant S}` is contained in the target's observed
  parents `PA(Y)`: ICP never selects a non-parent.  The formal theorem is stated
  in the nonparametric SCM setting, faithful to the paper's Assumption 1
  (`εᵉ ⊥ Xᵉ_{S*}` exogeneity, conditioning on `X_{PA(Y)}` regardless of
  intervention status).

## Status

Theorem 1 (soundness) is formalized in the nonparametric SCM setting. **Theorem
2 (completeness, `S(E) = PA(Y)`)** is established by the paper for linear
Gaussian SEMs and lives in the dedicated linear-Gaussian sub-development
`LinearGaussian/`, including the theorem `icp_complete_linearGaussian` and its
intermediate lemmas.
-/
