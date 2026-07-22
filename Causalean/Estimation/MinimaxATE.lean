/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Structure-agnostic optimality of doubly-robust ATE estimation — entry point

Roll-up module for the `Estimation/MinimaxATE/` development (Jin–Syrgkanis 2024,
*Structure-agnostic Optimality of Doubly Robust Learning for Treatment Effect Estimation*,
arXiv:2402.14264).  **Import this file** to pull in the whole development; the index below
says where each headline result lives so you do not have to hunt through the 28 leaf files.

The finite observed-data model (`Obs`, `obsLaw`, `productLaw`, `ate`, `l2sq`, `nMiss`,
`minimaxMiss`) is in `MinimaxATE/Model.lean`.  Everything is a finite PMF; budgets
`εg, εm` are squared-`L²(P_X)` nuisance errors around a fixed center `(mhat, ghat)`.

## Headline results

### Converse — no estimator beats the doubly-robust product rate `√(εg·εm)`

* `minimax_lower_bound` in `ConstCenterHalf/ChiSquaredCore.lean`: base case,
  constant center `(m̂,ĝ) ≡ ½`.
* `minimax_lower_bound_gen` in `ConstCenterGeneral/LowerBound.lean`: arbitrary
  constant center `(m₀,g₀,g₁) ∈ (0,1)³`.
* `minimax_lower_bound_var` in `VaryingCenterCase1/LowerBound.lean`: cell-varying
  center, Case 1 (`εg ≳ εm`, outcome budget dominates), used by the capstone.
* `minimax_lower_bound_var2` in `VaryingCenterCase2/LowerBound.lean`:
  cell-varying center, Case 2 (`εm > εg`, propensity budget dominates), the
  symmetric construction covering the regime `VaryingCenterCase1` does not.
* `two_point_lower_bound_continuous` in `ConstCenterHalf/ContinuousX.lean`:
  continuous covariate via ancillarity reduction.
* `parametric_lower_bound` in `ConstCenterHalf/Parametric.lean`: the additive
  `1/n` parametric-variance floor.
* `minimax_lower_bound_mse` and `minimax_lower_bound_mse_gen` in
  `ConstCenterHalf/MSE.lean` and `ConstCenterGeneral/MSE.lean`: weaker
  expected-risk (MSE) forms.

Each says `1/4 ≤ minimaxMiss mhat ghat εg εm n est s` at separation `s ≍ √(εg·εm)`: every
measurable estimator misses the true ATE by `s` with probability `≥ 1/4` somewhere in the class.

### Achievability — the DR/AIPW estimator attains the rate

* `aipw_minimaxMiss_le` in `Optimality.lean`: worst-case miss of the fixed-center
  AIPW estimator `estAIPW` is bounded by the Chebyshev expression
  `((1+2/ε)²/n)/(s − ε⁻¹·2√εg√εm)²` for any
  `s > ε⁻¹·2√εg√εm`, and tends to zero as `n·εg·εm → ∞`.

### Capstone — the minimax rate is `Θ(√(εg·εm))`, attained by AIPW

* `aipw_attains_minimax_rate` in `Optimality.lean` bundles the `_var` converse
  and the AIPW achievability into a `MinimaxRateThreshold`: every estimator
  misses at `s ≍ √(εg·εm)` with probability at least `1/4`, while AIPW's
  worst-case miss vanishes at a separation of the same order.  This is
  constant-factor, not constant-sharp, rate optimality.

## Folder layout

* `Reduction/` — `Witness`, `WitnessMixture`, `Bump`: Le Cam two-point / Rademacher-mixture
  reduction and the `l2sq` bump algebra.
* `ConstCenterHalf/` — the base pipeline (constant nuisance center `½`): `Construction`,
  `Gap`, `Membership`, `ChiSqOverlap`, `ExplicitWitness`, `Ingster`, `ChiSquaredCore`
  (holds the base lower bound), plus the base-variant headlines `ContinuousX`, `MSE`,
  `Parametric`.
* `ConstCenterGeneral/` — arbitrary **constant** center `(m₀,g₀,g₁)`: `Construction`,
  `Gap`, `Membership`, `ChiSqOverlap`, `LowerBound`, `MSE`.
* `VaryingCenterCase1/` — **cell-varying** center, **Case 1** (`εg ≳ εm`): `Construction`,
  `Gap`, `Membership`, `ChiSqOverlap`, `Ingster` (the non-uniform per-pair χ²), `LowerBound`.
* `VaryingCenterCase2/` — **cell-varying** center, **Case 2** (`εm > εg`): the symmetric
  second construction (`mλ = m₀(1+αg₁Δ)D`, `gλ(1) = g₁/D`, `D = 1+(β/g₁)Δ−αβ`), reusing
  `VaryingCenterCase1/Ingster`.  Files `Construction`, `Gap`, `Membership`, `ChiSqOverlap`,
  `LowerBound`.
* `Achievability/` — `AIPWEstimator`: the AIPW score/estimator + bias & variance bounds.
* `Optimality.lean`, `Model.lean` — the capstone and the finite observed-data model (top level).
-/

import Causalean.Estimation.MinimaxATE.ConstCenterHalf.ChiSquaredCore
import Causalean.Estimation.MinimaxATE.ConstCenterHalf.ContinuousX
import Causalean.Estimation.MinimaxATE.ConstCenterGeneral.LowerBound
import Causalean.Estimation.MinimaxATE.VaryingCenterCase1.LowerBound
import Causalean.Estimation.MinimaxATE.VaryingCenterCase2.LowerBound
import Causalean.Estimation.MinimaxATE.ConstCenterHalf.MSE
import Causalean.Estimation.MinimaxATE.ConstCenterGeneral.MSE
import Causalean.Estimation.MinimaxATE.ConstCenterHalf.Parametric
import Causalean.Estimation.MinimaxATE.Achievability.AIPWEstimator
import Causalean.Estimation.MinimaxATE.Optimality
import Causalean.Estimation.MinimaxATE.Causal.Bridge
import Causalean.Estimation.MinimaxATE.Causal.Minimax

/-!
This file is the entry point for the structure-agnostic optimality development
for doubly robust average-treatment-effect estimation.  Importing it brings in
the finite observed-data model, the constant-center and cell-varying minimax
lower bounds, the finite fixed-center AIPW achievability theorem, the capstone
rate comparison, and the causal re-centering of the cell-varying lower bounds.

The main lower-bound declarations are `minimax_lower_bound`,
`minimax_lower_bound_gen`, `minimax_lower_bound_var`,
`minimax_lower_bound_var2`, `two_point_lower_bound_continuous`,
`parametric_lower_bound`, `minimax_lower_bound_mse`, and
`minimax_lower_bound_mse_gen`.  The achievability side is centered on
`aipw_minimaxMiss_le`, and `aipw_attains_minimax_rate` packages the converse and
AIPW upper bound as a constant-factor minimax-rate statement.

## Causal grounding (`Causal/`)

The observed-data contrast `ate g = E_X[g(1,·) − g(0,·)]` on which the proof
machinery computes is identified with a genuine potential-outcome ATE.
`Causal/Construction.lean` builds, from a finite DGP `(m, g)`, a concrete
backdoor SCM (`Un → Xc → A → Y`, `Xc → Y`, latent noises `Ea, Ey`) and lifts it
through `POSystem.ofSCM` to a `POBackdoorSystem`; `Causal/Bridge.lean` defines
`causalATE m g := (dgpBackdoor m g).ATE = ∫ (Y(1) − Y(0)) dμ` and proves
`causalATE_eq_ate : causalATE m g = ate g` (under strict overlap), so the
minimax lower bound is a bound on the causal estimand `E[Y(1) − Y(0)]`,
identified by backdoor adjustment, not merely a regression contrast.
`Causal/Minimax.lean` contains the causal-centered miss probability
`minimaxMissCausal` and the Case-1 and Case-2 causal lower bounds
`minimax_lower_bound_var_causal` and `minimax_lower_bound_var2_causal`.
-/
