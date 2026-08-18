/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Experimentation.ExposureMappingInterference.Variance.Conservative
import Causalean.Experimentation.ExposureMappingInterference.Asymptotics.Consistency
import Causalean.Experimentation.DesignBased.GaussianCDF
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Local-dependence CLT interface (Aronow-Samii 2017, via Chen-Shao 2004)

Asymptotic normality of the Horvitz–Thompson effect estimator under interference rests on a
central limit theorem for locally dependent random fields, proved via Stein's method
(Chen & Shao 2004, Thm 2.7).  The `LocalDependenceCLT` structure packages the exact convergence
statement consumed by the interval theorem, while `SteinInstance.lean` connects this interface to
the dependency-graph Stein CLT developed elsewhere in the library.
-/


open scoped BigOperators Topology
open Filter MeasureTheory

namespace Causalean
namespace Experimentation
namespace ExposureMappingInterference

open Causalean.Experimentation.DesignBased

namespace Experiment

variable (E : Experiment)

/-- The studentized HT effect statistic: centered at `τ`, scaled by the true standard error
`√Var[τ̂]`. -/
noncomputable def studentizedEffect (dk dl : E.Δ) (z : E.Ω) : ℝ :=
  (htEffect E.D E.y E.f E.θ dk dl z - tauTrue E.y dk dl)
    / Real.sqrt (E.D.Var (htEffect E.D E.y E.f E.θ dk dl))

end Experiment

/-- **Chen-Shao local-dependence CLT interface, bounded-neighborhood case.** Along a sequence of
experiments `Exp` with a chosen pair of exposure levels `dk`, `dl` at each sample size, this
records that [the design probability that the studentized Horvitz–Thompson effect statistic
falls below any fixed threshold converges, as the sample size grows, to the standard normal CDF
at that threshold](hyp:tendsto_cdf).

The bounded-summand and bounded-degree
conditions that imply this interface are connected to the dependency-graph Stein CLT in
`SteinInstance.lean`. -/
structure LocalDependenceCLT (Exp : ℕ → Experiment) (dk dl : ∀ n, (Exp n).Δ) : Prop where
  /-- Convergence in distribution of the studentized statistic to `𝒩(0,1)`, via the CDF. -/
  tendsto_cdf : ∀ t : ℝ, Tendsto
    (fun n => (Exp n).D.Pr (fun z => (Exp n).studentizedEffect (dk n) (dl n) z ≤ t))
    atTop (𝓝 (stdNormalCdf t))

end ExposureMappingInterference
end Experimentation
end Causalean
