/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Experimentation.SuperPopulation.HACConsistency.VarianceBound
import Causalean.Experimentation.SuperPopulation.HACConsistency.Consistency

/-!
# Network-HAC variance-estimator consistency

This roll-up imports the variance bound for the network-HAC estimator and the Chebyshev
consistency theorem.  The variance side provides `netHACVarEst_eq_locProd`,
`netHACVarEst_variance_le`, and `netHACVarEst_variance_tendsto_zero`; the consistency side provides
`netHACVarEst_memLp` and `netHAC_consistent`.  Together they show that the empirical neighborhood
cross-product estimator converges in probability to the variance of the m-dependent network sum
under the CLT-rate boundedness conditions.
-/
