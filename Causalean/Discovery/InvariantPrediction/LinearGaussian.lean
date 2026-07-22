/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Discovery.InvariantPrediction.LinearGaussian.Model
import Causalean.Discovery.InvariantPrediction.LinearGaussian.Regression
import Causalean.Discovery.InvariantPrediction.LinearGaussian.Helpers.Moments
import Causalean.Discovery.InvariantPrediction.LinearGaussian.Completeness

/-!
# Invariant Causal Prediction — linear-Gaussian completeness (umbrella)

Self-contained linear-Gaussian formalization of the **completeness** half of
Invariant Causal Prediction (Peters, Bühlmann & Meinshausen, JRSS-B 2016,
`arXiv:1501.01332`, Theorem `prop:1`(i), the **do-intervention** version).

Unlike the sibling nonparametric SWIG/kernel development (which proves
soundness, `S(E) ⊆ PA(Y)`, in full generality), this sub-development works in the
paper's **linear-Gaussian** framework — the only setting in which the paper
establishes the converse `S(E) ⊇ PA(Y)` — using a random-variable encoding.

## Files

* `Model.lean` — the observational linear-Gaussian SEM (`ObsSEM`), interventional
  environments with do-interventions (`Env`), and the environment family
  (`EnvFamily`), all in random-variable form with a `DAG` for the graph.
* `Regression.lean` — the regression residual, the regression-invariance null
  `H_{0,S}` (`InvarianceNull`), and the identified set `S(E)` (`identifiedSet`).
* `Helpers/Moments.lean` — Gaussian-noise moments: `εⱼ` is integrable with
  `E[εⱼ] = 0`.
* `Helpers/Residual.lean` — with the causal coefficient `γ* = β₀,·`, the residual
  equals the target noise `ε₀` a.e. in every environment.
* `Helpers/Invariance.lean` — non-descendant invariance: under `do(X_{k₀}=a)`,
  every non-descendant of `k₀` keeps its observational value a.e.
* `Completeness.lean` — the do-intervention hypotheses, soundness /
  youngest-node / mean-shift intermediate lemmas, and the main theorem
  `icp_complete_linearGaussian : S(E) = PA(Y)`. Soundness uses the paper's
  Assumption-1 exogeneity carried as `ObsSEM.hYexo` / `Env.hExo`.
-/
