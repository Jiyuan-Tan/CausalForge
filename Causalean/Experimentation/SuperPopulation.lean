/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Experimentation.SuperPopulation.Basic
import Causalean.Experimentation.SuperPopulation.CLT
import Causalean.Experimentation.SuperPopulation.HAC
import Causalean.Experimentation.SuperPopulation.HACConsistency
import Causalean.Experimentation.SuperPopulation.MeanCLT

/-!
# Super-population experimentation

Super-population modules collect network-dependent sampling CLTs and HAC variance tools.

This roll-up imports the basic `NetworkDependence` setup, the network-sum CLT
`networkSum_clt`, the network-HAC estimator `NetworkDependence.netHACVarEst` and its unbiasedness
identity, the HAC consistency theorems, and the mean-CLT bridge.  Together these modules cover
locally dependent network fields, standard-normal limits for network sums and means, and
network-HAC variance estimation for the same super-population asymptotic regime.
-/
