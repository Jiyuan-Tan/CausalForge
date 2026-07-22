/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Consistency of extremum (M-)estimators

The workhorse consistency theorem for econometric extremum estimators
(Newey & McFadden 1994, Theorem 2.1; van der Vaart 1998, Theorem 5.7).  An
estimator `θ̂ₙ` that maximizes a sample criterion `θ ↦ Pₙ m(θ, ·)` is consistent
for the population maximizer `θ₀` of `θ ↦ P m(θ, ·)` provided

1. **uniform convergence** of the criterion (a Glivenko–Cantelli condition on
   the class `{m(θ, ·) : θ ∈ Θ}`), and
2. a **well-separated maximum**: outside every `ε`-ball around `θ₀` the
   population criterion stays bounded away from its value at `θ₀`.

The proof is the classical sandwich

    M(θ₀) − M(θ̂ₙ)
      = (M(θ₀) − Mₙ(θ₀)) + (Mₙ(θ₀) − Mₙ(θ̂ₙ)) + (Mₙ(θ̂ₙ) − M(θ̂ₙ))
      ≤ 2 · sup_θ |Mₙ(θ) − M(θ)|,

(the middle term is `≤ 0` because `θ̂ₙ` maximizes `Mₙ`), combined with the
separation gap `η`.  This file **consumes** the `GlivenkoCantelli` engine from
`GlivenkoCantelli.lean`: the uniform-convergence hypothesis is exactly that
predicate for the criterion class `m`.
-/

import Causalean.Stat.EmpiricalProcess.GlivenkoCantelli
import Mathlib.Topology.MetricSpace.Basic

/-! # M-Estimator Consistency

This file proves consistency for extremum estimators from uniform convergence of the
sample criterion and a well-separated population maximum. It is the empirical-process
bridge from Glivenko-Cantelli classes to econometric consistency theorems.  The
theorem `mEstimator_consistent_of_glivenkoCantelli` consumes an abstract uniform
law, while `mEstimator_consistent_of_bracketing` supplies that law from finite
`L¹(P)` bracketing. -/

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X}

/-- **Consistency of extremum estimators** (Newey–McFadden 1994, Thm 2.1).

Let `m : Θ → X → ℝ` be a criterion indexed by a (pseudo-)metric parameter space
`Θ`, with population objective `M θ = ∫ m θ dP` and sample objective
`Mₙ θ = Pₙ m θ = S.sampleMean (m θ) n`.  Suppose

* `hGC`     — the criterion class is **Glivenko–Cantelli** (uniform LLN);
* `hArgmax` — the estimator `θ̂ₙ` does at least as well as `θ₀` on the sample
              objective, `Mₙ(θ₀) ≤ Mₙ(θ̂ₙ)` (it suffices that `θ̂ₙ` be a sample
              maximizer; only domination over `θ₀` is used);
* `hSep`    — the population maximum is **well separated** at `θ₀`: for every
              `ε > 0` there is a gap `η > 0` with `M θ + η ≤ M θ₀` whenever
              `dist θ θ₀ ≥ ε`.

Then `θ̂ₙ` is **consistent**: for every `ε > 0`, the probability that
`dist (θ̂ₙ) θ₀ ≥ ε` tends to `0`. -/
theorem mEstimator_consistent_of_glivenkoCantelli
    {Θ : Type*} [PseudoMetricSpace Θ]
    (S : IIDSample Ω X μ P) (m : Θ → X → ℝ) (θ₀ : Θ)
    (thetaHat : ℕ → Ω → Θ)
    (hGC : GlivenkoCantelli S m)
    (hArgmax : ∀ n ω,
      S.sampleMean (m θ₀) n ω ≤ S.sampleMean (m (thetaHat n ω)) n ω)
    (hSep : ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧
      ∀ θ : Θ, ε ≤ dist θ θ₀ → (∫ x, m θ x ∂P) + η ≤ ∫ x, m θ₀ x ∂P) :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => μ {ω | ε ≤ dist (thetaHat n ω) θ₀}) atTop (𝓝 0) := by
  intro ε hε
  obtain ⟨η, hη, hsep⟩ := hSep ε hε
  have hη2 : 0 < η / 2 := by linarith
  -- the "θ̂ₙ far from θ₀" event is covered by a uniform-deviation event of size η/2
  have hsub : ∀ n, {ω | ε ≤ dist (thetaHat n ω) θ₀}
      ⊆ {ω | ∃ θ, η / 2 ≤ |S.sampleMean (m θ) n ω - ∫ x, m θ x ∂P|} := by
    intro n ω hω
    have hfar : ε ≤ dist (thetaHat n ω) θ₀ := hω
    by_contra hcon
    simp only [Set.mem_setOf_eq, not_exists, not_le] at hcon
    -- every coordinate deviates by < η/2
    have h0 := abs_lt.mp (hcon θ₀)
    have h1 := abs_lt.mp (hcon (thetaHat n ω))
    have ha := hArgmax n ω
    have hs := hsep (thetaHat n ω) hfar
    -- contradiction with the separation gap
    linarith [h0.1, h0.2, h1.1, h1.2, ha, hs]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (hGC (η / 2) hη2) (Eventually.of_forall fun n => zero_le _)
    (Eventually.of_forall fun n => measure_mono (hsub n))

/-- **Bracketing corollary** (the econometrician's headline).  A criterion class
with finite `L¹(P)` bracketing numbers and a well-separated population maximum
yields a **consistent** extremum estimator.  Pure composition of
`glivenkoCantelli_of_hasL1Bracketing` (which discharges the uniform-LLN
hypothesis) with `mEstimator_consistent_of_glivenkoCantelli`. -/
theorem mEstimator_consistent_of_bracketing
    {Θ : Type*} [PseudoMetricSpace Θ] [IsProbabilityMeasure P]
    (S : IIDSample Ω X μ P) (m : Θ → X → ℝ) (θ₀ : Θ)
    (thetaHat : ℕ → Ω → Θ)
    (hmeas : ∀ θ, Measurable (m θ))
    (hbr : HasL1Bracketing m P)
    (hArgmax : ∀ n ω,
      S.sampleMean (m θ₀) n ω ≤ S.sampleMean (m (thetaHat n ω)) n ω)
    (hSep : ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧
      ∀ θ : Θ, ε ≤ dist θ θ₀ → (∫ x, m θ x ∂P) + η ≤ ∫ x, m θ₀ x ∂P) :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => μ {ω | ε ≤ dist (thetaHat n ω) θ₀}) atTop (𝓝 0) :=
  mEstimator_consistent_of_glivenkoCantelli S m θ₀ thetaHat
    (glivenkoCantelli_of_hasL1Bracketing S m hmeas hbr) hArgmax hSep

end Causalean.Stat
