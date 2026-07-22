/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Sample-split plug-in ERM for an `LearningSystem`

* `empRiskFoldB S S_iid split n ω θ g` — empirical risk on the estimation
  fold `B(n)` at parameter `θ` and nuisance `g`,
  `(1 / |B(n)|) · Σ_{i ∈ B(n)} ℓ (Z_i ω) θ g`.
* `SampleSplitPluginERM S S_iid split θ̂ ĝ r_opt` — predicate on a
  sample-indexed estimator `θ̂ : ℕ → Ω → Θ` saying it is an
  `r_opt n`-approximate minimizer of the fold-B empirical risk evaluated
  at the plug-in nuisance `ĝ n ω`.

See `doc/basic_concepts/po/estimation/orthogonal_statistical_learning.tex`,
`def:est-osl-plugin-erm`.
-/

import Causalean.Estimation.OrthogonalLearning.Setup
import Causalean.Stat.SampleSplit.OneShot

/-! # Sample-Split Plug-In ERM

This file defines the empirical risk on the estimation fold of a sample split
and the predicate that an estimator approximately minimizes that empirical risk
after plugging in a nuisance estimate. These objects are the estimation-side
inputs to the orthogonal statistical-learning oracle inequality.

The main declarations are `empRiskFoldB`, the fold-B empirical risk, and
`SampleSplitPluginERM`, the approximate empirical-risk-minimization predicate
for a sample-indexed target estimator and plug-in nuisance estimate. -/

namespace Causalean
namespace Estimation
namespace OrthogonalLearning

open MeasureTheory ProbabilityTheory Filter Topology Causalean.Stat

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
         {Z : Type*} [MeasurableSpace Z] {P_Z : MeasureTheory.Measure Z}
         {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ]
         {G : Type*} [AddCommGroup G] [Module ℝ G]

/-- Empirical risk on the estimation fold `B(n)`:
`(1 / |B(n)|) · Σ_{i ∈ B(n)} ℓ (Z_i ω) θ g`. -/
noncomputable def empRiskFoldB
    (S : LearningSystem Ω μ Z P_Z Θ G)
    (S_iid : IIDSample Ω Z μ P_Z)
    (split : OneShotSplit S_iid)
    (n : ℕ) (ω : Ω) (θ : Θ) (g : G) : ℝ :=
  ((split.foldB n).card : ℝ)⁻¹
    * ∑ i ∈ split.foldB n, S.ℓ (S_iid.Z i ω) θ g

/-- Sample-split plug-in ERM predicate.

Given:
* `θ̂ : ℕ → Ω → Θ` — estimator (sample-size indexed, depending on
  randomness on `Ω`),
* `ĝ : ℕ → Ω → G` — plug-in nuisance estimate (typically computed on the
  nuisance fold `A(n)`; here we only require its values),
* `r_opt : ℕ → ℝ`  — non-negative optimisation slack,

the predicate says that for every `n` and every `ω`, `θ̂ n ω ∈ Θ_set` and
its fold-B empirical risk at `ĝ n ω` is within `r_opt n` of the infimum
over `Θ_set`.

`r_opt_nonneg` is part of the predicate so consumers carrying the bundle
do not need to thread it separately. -/
structure SampleSplitPluginERM
    (S : LearningSystem Ω μ Z P_Z Θ G)
    (S_iid : IIDSample Ω Z μ P_Z)
    (split : OneShotSplit S_iid)
    (θhat : ℕ → Ω → Θ)
    (ghat : ℕ → Ω → G)
    (r_opt : ℕ → ℝ) : Prop where
  r_opt_nonneg : ∀ n, 0 ≤ r_opt n
  mem_Θ_set    : ∀ n ω, θhat n ω ∈ S.Θ_set
  /-- ε-minimizer form: equivalent to `≤ inf + r_opt` and avoids the
  conditional-completeness pitfall on `ℝ` (where `⨅` defaults to `0` when
  the set is empty or unbounded below). -/
  approx_min   : ∀ n ω, ∀ θ' ∈ S.Θ_set,
    empRiskFoldB S S_iid split n ω (θhat n ω) (ghat n ω)
      ≤ empRiskFoldB S S_iid split n ω θ' (ghat n ω) + r_opt n

end OrthogonalLearning
end Estimation
end Causalean
