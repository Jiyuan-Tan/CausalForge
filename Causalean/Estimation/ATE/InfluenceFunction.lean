/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# AIPW influence function for the back-door ATE — umbrella

Re-exports the influence-function submodules into a single import target consumed by
`PlugIn.lean` and `DML.lean`. Each sub-module is kept under ~300 lines:

* `Setup.lean`          — `BackdoorEstimationSystem`, `P_X`, `factualZ`, `P_Z`,
                          `θ₀`, `θ₀_eq_ATE`, `StrictOverlap`.
* `Score/AIPWMoment.lean`     — `aipwMoment`, `ψ_AIPW`, `NuisanceVec` + algebraic
                          instances, `H_ε`, `aipwMomentFunctional`.
* `Score/MeanZero.lean`       — `lem:est-aipw-mean-zero` and helpers
                          (`cond_exp_residual_zero`, `theta_zero_factualX_integral`,
                          `aipw_mean_zero`).
* `Score/ScorePullout.lean`    — shared pull-out and residual lemmas
                          (`e_val_label`, `weighted_residual_integral_zero`,
                          `indicator_to_propScore_integral`).
* `Score/FiniteVar.lean`      — `lem:est-aipw-finite-var` (proved).

The Gâteaux-derivative Neyman orthogonality witness (`Neyman.lean` and the
`NeymanAux/` helpers) was archived under `Archived/` after the 2026-05-06
refactor of `aipw_dml_isAsymLinear`, which now uses the per-η̂ bilinear
remainder route directly without going through `aipw_neyman` /
`aipw_neymanOrthog`.

References (NL doc):
* `def:est-ate-nuisance`         — value-space `(μ, e)`.
* `def:est-aipw-moment`          — `m_AIPW`.
* `def:est-aipw-nuisance-space`  — overlap-bounded set `H_ε`.
* `lem:est-aipw-mean-zero`       — `E[ψ_AIPW] = 0`.
* `lem:est-aipw-finite-var`      — `E[ψ_AIPW²] < ∞`.
-/

import Causalean.Estimation.ATE.Setup
import Causalean.Estimation.ATE.Score.AIPWMoment
import Causalean.Estimation.ATE.Score.MeanZero
import Causalean.Estimation.ATE.Score.ScorePullout
import Causalean.Estimation.ATE.Score.FiniteVar

/-!
This file collects the influence-function setup for augmented
inverse-probability-weighted average-treatment-effect estimation. It re-exports
the back-door estimation system and observed-data law, the AIPW moment and
nuisance space, the mean-zero theorem for the score, the shared pull-out lemmas,
and the finite-variance theorem used by plug-in and double-machine-learning
results.
-/
