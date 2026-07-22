/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Liu–Hudgens (2014): large-sample theory for the direct-effect contrast estimator

Umbrella for the large-sample (groups → ∞) layer over the Hudgens–Halloran two-stage design.

* `Setup` — the sequence-of-experiments bundle `LHExperiment`, carrying the two-stage design and
  its known design propensities, with the reusable unbiasedness (`E_estD`) and variance
  (`var_estD`) bridges.
* `Consistency` — the estimator converges in probability to the population average
  treatment-minus-control direct-effect contrast as the number of groups grows (Chebyshev, since
  the design variance vanishes).
* `CLT` — asymptotic normality (Liu–Hudgens Prop 5.1) of the studentized direct-contrast estimator
  via the mixture-lifting argument, conditional on the uniform conditional-CLT regularity.
* `Identical` — discharges the analytic homogeneity hypothesis of the CLT bundle from literally
  identical groups: a coordinate-permutation relabeling proves the conditional studentized CDF is
  selection-symmetric (`hhom_of_identical`), yielding `directEffect_clt_identical`, the CLT resting
  only on identical groups + bounded outcomes + the many-groups rate (no `hhom` assumption).
* `Wald` — asymptotic (oracle) Wald confidence-interval coverage: the interval `D̂E ± z·√directVar`
  has coverage at least `1 − γ`, from the CLT limits and standard-normal CDF symmetry.
* `WaldFeasible` — the feasible analogue: the interval `D̂E ± z·√V̂` using an *estimated* variance
  attains coverage at least `1 − γ` whenever the estimator is conservative-consistent.
-/

import Causalean.Experimentation.TwoStageInterference.Asymptotic.Setup
import Causalean.Experimentation.TwoStageInterference.Asymptotic.Consistency
import Causalean.Experimentation.TwoStageInterference.Asymptotic.CLT
import Causalean.Experimentation.TwoStageInterference.Asymptotic.CLTDischarge
import Causalean.Experimentation.TwoStageInterference.Asymptotic.CLTDischargeMain
import Causalean.Experimentation.TwoStageInterference.Asymptotic.Identical
import Causalean.Experimentation.TwoStageInterference.Asymptotic.Wald
import Causalean.Experimentation.TwoStageInterference.Asymptotic.WaldFeasible

/-! # Two-stage interference asymptotics

Two-stage interference asymptotics cover consistency, central limit theorems, and Wald intervals
for the treatment-minus-control direct-effect contrast in Liu-Hudgens sequences of two-stage
experiments.

This roll-up imports:

* `Setup`, defining `LHExperiment`, the joint design `jointD`, the contrast estimator `estD`, the
  estimand `DEbar`, the closed-form variance `directVar`, and the bridges `E_estD` / `var_estD`.
* `Consistency`, proving `estDirect_consistent` from vanishing `directVar`.
* `CLT`, proving the mixture-lifting theorem `directEffect_clt` from uniform conditional
  studentized CDF convergence.
* `CLTDischarge` and `CLTDischargeMain`, which package homogeneity in `Homogeneous` and prove the
  fully primitive theorem `directEffect_clt_homogeneous`.
* `Identical`, deriving the homogeneity hypothesis from literal identical-group symmetry and
  proving `directEffect_clt_identical`.
* `Wald` and `WaldFeasible`, proving oracle and conservative-feasible Wald coverage.
-/
