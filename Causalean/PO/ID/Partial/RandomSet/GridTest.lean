/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Finite-grid support-process tail tests

Built directly on the finite-grid support-process CLT
`setValued_supportProcess_clt` (`SupportProcess.lean`).  Beresteanu & Molinari
(2008, Thm 2.2) motivate a specification test of the null

    H₀ : E[F] = EF

for a set-valued random variable `F`.  This file formalizes the algebraic
finite-grid proxy built from the normalized sum of the centered support process.
Over a fixed grid of `k` directions `p₀,…,p_{k-1}` the statistic is the `ℓ^∞`
functional of those normalized support-process coordinates.  When the separate
Minkowski-mean bridge hypotheses are available, this proxy can be related to

    Tₙ = maxⱼ √n · |s(pⱼ, F̄ₙ) − s(pⱼ, EF)|,

but the declarations below state and prove results for the normalized
support-process statistic itself.  Under the mean-zero / Artstein hypothesis
`∫ ψ = 0` of the support process, the CLT gives convergence to `‖z‖_∞` over the
grid for the finite-dimensional Gaussian limit `z`, so the rejection probability
converges to the limit-law tail `L(c, ∞)`.  Choosing `c` as the `(1−α)`-quantile
of the limit law `L` (a
continuity point, so `L{c} = 0`) delivers an asymptotic level-`α` test.

## Main definitions

* `gridTestStat` — the two-sided normalized support-process statistic.
* `gridTestReject` — the rejection region `{ω | c < Tₙ ω}` at critical value `c`.

## Main results

* `gridTestStat_clt` — under the mean-zero hypothesis, the statistic converges
  in distribution to the law
  `(gaussianLimit ψ).map maxAbsK` of `maxⱼ |z(pⱼ)|`; a thin restatement of
  `setValued_supportProcess_clt`.
* `gridTest_asymptotic_level` — under `H₀`, at any continuity point `c` of the
  limit law, the rejection probability `μ (gridTestReject … c)` converges to the
  limit-law tail `L(c, ∞)`.  Proved by portmanteau on the open half-line `Ioi c`.
-/

import Causalean.PO.ID.Partial.RandomSet.SupportProcess

/-! # Finite-Grid Specification Tests for Random Sets

This file formulates finite-grid specification tests for the Aumann expectation
of a set-valued random variable using the normalized centered support process.
The statistic is the gridwise supremum of that normalized support-process sum,
and its asymptotic level follows from the finite-direction support-process
central limit theorem.

Main declarations:
* `gridTestStat` is the finite-grid `l^\infty` statistic applied to the
  normalized centered support-process sum.
* `gridTestReject` is the rejection region `{T_n > c}`.
* `gridTestStat_clt` transports the support-process CLT through the grid
  supremum functional.
* `gridTest_asymptotic_level` identifies the limiting rejection probability at
  continuity points of the Gaussian limit law.
-/

open MeasureTheory ProbabilityTheory Filter Topology Causalean.Stat

namespace Causalean.PartialID.RandomSet

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
  {k : ℕ} [NeZero k]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The finite-grid test statistic is the grid supremum of the normalized
centered support-process sum.

It applies the `ℓ^∞` functional `maxAbsK` to the normalized sum of the centered
support process.  This declaration is the algebraic normalized-sum statistic;
identifying it with empirical Minkowski-average support deviations requires the
separate body-valued bridge assumptions from `supportProcess_normalizedSum_apply`. -/
-- TODO(faithfulness): Beresteanu-Molinari grid test — expose the body-valued
-- Hausdorff-over-grid empirical-Minkowski statistic in the test API and prove
-- its equality to this normalized support-process proxy under the bridge
-- hypotheses.
noncomputable def gridTestStat (S : IIDSample Ω X μ P) (F : X → Set V) (EF : Set V)
    (p : Fin k → V) : ℕ → Ω → ℝ :=
  fun n ω => maxAbsK (IsAsymLinearVec.normalizedSum S (supportProcess F EF p)
    (fun m => Finset.range m) n ω)

/-- **The rejection region** of the finite-grid test at critical value `c`:
reject `H₀ : E[F] = EF` when the statistic `Tₙ` exceeds `c`. -/
def gridTestReject (S : IIDSample Ω X μ P) (F : X → Set V) (EF : Set V)
    (p : Fin k → V) (n : ℕ) (c : ℝ) : Set Ω :=
  {ω | c < gridTestStat S F EF p n ω}

section CLT

variable (S : IIDSample Ω X μ P) (F : X → Set V) (EF : Set V) (p : Fin k → V)
  (hψ : Measurable (supportProcess F EF p))
  (hvar : Integrable (fun x => ‖supportProcess F EF p x‖ ^ 2) P)
  (hint : Integrable (supportProcess F EF p) P)
  (hmean : ∫ x, supportProcess F EF p x ∂P = 0)
  (hSum_meas : ∀ n, AEMeasurable
    (IsAsymLinearVec.normalizedSum S (supportProcess F EF p)
      (fun m => Finset.range m) n) μ)

include hint hmean in
/-- The normalized finite-grid support-process statistic converges to the grid
supremum of its Gaussian limit.

Under the mean-zero / Artstein hypothesis `∫ ψ = 0`, the finite-grid statistic
`gridTestStat` converges in distribution to the law
`(gaussianLimit ψ).map maxAbsK` of `maxⱼ |z(pⱼ)|` for the finite-dimensional
Gaussian limit `z` of the support process.  A thin restatement of
`setValued_supportProcess_clt`. -/
theorem gridTestStat_clt :
    Tendsto_dist_vec (gridTestStat S F EF p)
      ((gaussianLimit hψ hvar).map maxAbsK) μ
      (fun n => measurable_maxAbsK.comp_aemeasurable (hSum_meas n)) :=
  setValued_supportProcess_clt S F EF p hψ hvar hint hmean hSum_meas

include hint hmean hSum_meas in
/-- The tail probability of the normalized finite-grid support-process statistic
converges to the corresponding Gaussian-limit tail.

Under the mean-zero hypothesis, at any continuity point `c` of the limit law
`L = (gaussianLimit ψ).map maxAbsK` (i.e. `L{c} = 0`), the rejection probability
converges to the limit-law tail:

    μ (gridTestReject … c)  →  L(c, ∞).

Choosing `c` as the `(1−α)`-quantile of `L` (a continuity point) makes the right
side `α`, giving an asymptotic level-`α` test.  Proof: the rejection event is
`{Tₙ ∈ Ioi c}`, so the conclusion is portmanteau
(`tendsto_measure_of_null_frontier_of_tendsto'`) on the open half-line `Ioi c`,
whose frontier `{c}` is null by the continuity-point hypothesis. -/
theorem gridTest_asymptotic_level {c : ℝ}
    (hfront : ((gaussianLimit hψ hvar).map maxAbsK) {c} = 0) :
    Tendsto (fun n => μ (gridTestReject S F EF p n c)) atTop
      (𝓝 (((gaussianLimit hψ hvar).map maxAbsK) (Set.Ioi c))) := by
  have hclt := gridTestStat_clt S F EF p hψ hvar hint hmean hSum_meas
  unfold Tendsto_dist_vec at hclt
  have hport := MeasureTheory.ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    hclt (E := Set.Ioi c) (by rw [frontier_Ioi]; exact hfront)
  refine hport.congr' ?_
  filter_upwards with n
  -- the per-`n` rejection probability equals the pushforward mass of `Ioi c`
  change (μ.map (gridTestStat S F EF p n)) (Set.Ioi c) = μ (gridTestReject S F EF p n c)
  have hmeas : AEMeasurable (gridTestStat S F EF p n) μ :=
    measurable_maxAbsK.comp_aemeasurable (hSum_meas n)
  rw [Measure.map_apply_of_aemeasurable hmeas measurableSet_Ioi]
  rfl

end CLT

end Causalean.PartialID.RandomSet
