/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Experimentation.DesignBased
import Causalean.Experimentation.ExposureMappingInterference.Variance.Conservative
import Causalean.Experimentation.ExposureMappingInterference.Asymptotics.Consistency
import Causalean.Experimentation.ExposureMappingInterference.Asymptotics.SteinCLT
import Causalean.Experimentation.ExposureMappingInterference.Asymptotics.Intervals
import Causalean.Experimentation.ExposureMappingInterference.Asymptotics.SteinInstance
import Causalean.Experimentation.ExposureMappingInterference.Asymptotics.VarianceConsistency
import Causalean.Experimentation.ExposureMappingInterference.Asymptotics.VarEstQuadBound
import Causalean.Experimentation.ExposureMappingInterference.Asymptotics.VarEstConsistencyConditions

/-!
# Aronow & Samii (2017) — average causal effects under general interference

Formalization of Aronow & Samii (2017, AOAS), "Estimating Average Causal Effects Under General
Interference" (arXiv:1305.6156), built on the shared `Experimentation.DesignBased` substrate.

This aggregate module imports the exposure-mapping definitions, conservative variance-estimation
results, and asymptotic theory for Horvitz-Thompson estimators under general interference.

* `Variance.Conservative` formalizes the section 5 conservative variance estimator.
* `Asymptotics.Consistency` contains the `Experiment` sequence bundle and HT consistency theorem.
* `Asymptotics.SteinCLT` and `Asymptotics.SteinInstance` provide the dependency-graph CLT interface
  and its discharge from primitive conditions.
* `Asymptotics.Intervals` derives oracle and feasible Wald coverage.
* `Asymptotics.VarianceConsistency`, `Asymptotics.VarEstQuadBound`, and
  `Asymptotics.VarEstConsistencyConditions` connect variance-estimator consistency to primitive
  bounds and assumptions.
-/
