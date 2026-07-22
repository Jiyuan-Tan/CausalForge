import Causalean.Estimation.ATT.Setup
import Causalean.Estimation.ATT.Score.AIPWMoment
import Causalean.Estimation.ATT.Score.MeanZero
import Causalean.Estimation.ATT.Score.ScorePullout
import Causalean.Estimation.ATT.Score.FiniteVar

/-!
Collects the average-treatment-effect-on-the-treated AIPW interface in one
import. The re-exported development defines `TreatedEstimationSystem`,
`OneSidedOverlap`, the observed laws `P_X` and `P_Z`, the ATT target `θ₀`, the
un-normalized moment `aipwMomentATT`, the influence function `ψ_ATT`, the
treated nuisance space `TreatedNuisanceVec`, and its overlap class `H_ε`.

It also exposes the main population facts used downstream: the mean-zero theorem
`aipw_mean_zero_ATT`, pull-out identities for ATT residuals, finite-variance and
IPW-integrability results, the exact second-order remainder identity and bound,
and the L² score-continuity theorem for ATT double machine learning.
-/

/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# AIPW influence function for the back-door ATT — umbrella

Re-exports the ATT AIPW sub-modules into a single import target consumed by
`DML.lean` and `ATTInstance.lean`. Each sub-module is kept under ~300 lines:

* `Setup.lean`          — `TreatedEstimationSystem`, `OneSidedOverlap`, `P_X`,
                          `factualZ`, `P_Z`, `π_val`, `θ₀`, `θ₀_eq_ATT`.
* `Score/AIPWMoment.lean`     — `aipwMomentATT`, `ψ_ATT`, `TreatedNuisanceVec` +
                          algebraic instances, `H_ε`, `aipwMomentATTFunctional`,
                          `measurable_aipwMomentATTFunctional`, `η₀`.
* `Score/MeanZero.lean`       — `aipw_mean_zero_ATT` (`lem:est-aipw-mean-zero-att`)
                          and measurability helpers.
* `Score/ScorePullout.lean`   — shared pull-out and residual lemmas for the ATT
                          AIPW form (`(1−A)·e/(1−e)` weight, treated-arm `A`).
* `Score/FiniteVar.lean`      — `aipw_finite_var_ATT` (`lem:est-aipw-finite-var-att`).

Mirrors `Estimation/ATE/InfluenceFunction.lean` for the ATT version.

References (NL doc):
* `def:est-att-nuisance`         — value-space `(μ₀, e)`.
* `def:est-aipw-moment-att`      — `m_AIPW^ATT`.
* `def:est-aipw-nuisance-space-att` — one-sided overlap-bounded set `H_ε`.
* `lem:est-aipw-mean-zero-att`   — `E[ψ_ATT] = 0`.
* `lem:est-aipw-finite-var-att`  — `E[ψ_ATT²] < ∞`.
-/
