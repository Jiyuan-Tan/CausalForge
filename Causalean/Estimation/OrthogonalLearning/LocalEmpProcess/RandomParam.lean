/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Cross-fit conditioning keystone: random fold-A parameter into fold-B events

`randomParam_event_le` is the measure-theoretic heart of the cross-fitting
argument.  Suppose:

* `Y : Ω → β` is the fold-B coordinate map, with law `μ.map Y = ν`;
* `m_A` is the fold-A sub-σ-algebra, independent of `σ(Y)` (`Indep m_A σ(Y) μ`);
* `Bad : Ω → Set β` is a family of "bad" events whose `ω`-dependence is
  `m_A`-measurable (jointly measurable as a set in `Ω × β`), each of `ν`-mass
  `≤ δ`.

Then the *random* event `{ω : Y ω ∈ Bad ω}` — where the bad set is selected by
the fold-A-measurable randomness at the very `ω` where the fold-B sample is read
— still has `μ`-mass `≤ δ`.

This is exactly "condition on fold A, the fold-B sample is fresh i.i.d., apply
the fixed-parameter bound, integrate".  It lets a fixed-nuisance
high-probability event (e.g. the empirical-process modulus event, which is a
`σ(foldB)`-preimage) be lifted to a *random cross-fitted nuisance* `ĥ n ω` that
is `σ(foldA)`-measurable, with no loss in the probability budget.

Proof: `indep_trim_prod_map_eq` (from `Causalean/Mathlib/IIDCenteredSum.lean`)
factorises `μ.map (ω ↦ (ω, Y ω)) = (μ.trim m_A).prod ν`; then `Measure.prod_apply`
(Tonelli) integrates the `ν`-section `Bad ω` against the fold-A marginal, and
`∫ (≤ δ) = ≤ δ` since `μ.trim` is a probability measure.
-/

import Causalean.Mathlib.IIDCenteredSum

/-! # Cross-Fit Random Parameter Conditioning

This file supplies the measure-theoretic conditioning step used in cross-fitting.
It shows that a fold-A-measurable random choice of a fold-B event inherits the
same probability bound as each fixed fold-B event, using independence between
the training and validation folds.

The main theorem `randomParam_event_le` is the cross-fit conditioning lemma:
if the fold-B coordinate map has law `ν`, the fold-A sigma-algebra is
independent of that coordinate block, and every selected bad set has
`ν`-mass at most `δ`, then the random event selected by fold-A data has
`μ`-mass at most `δ`. -/

namespace Causalean
namespace Estimation
namespace OrthogonalLearning

open MeasureTheory ProbabilityTheory

/-- **Cross-fit conditioning keystone.** A fold-A-measurable random selection of
a fold-B event of `ν`-mass `≤ δ` has `μ`-mass `≤ δ`. -/
theorem randomParam_event_le
    {Ω β : Type*} [mΩ : MeasurableSpace Ω] [mβ : MeasurableSpace β]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Y : Ω → β} (hY : @Measurable Ω β mΩ mβ Y)
    {ν : Measure β} [IsProbabilityMeasure ν] (hY_law : μ.map Y = ν)
    (m_A : MeasurableSpace Ω) (hm_A_le : m_A ≤ mΩ)
    (hindep : @Indep Ω m_A (MeasurableSpace.comap Y mβ) mΩ μ)
    {δ : ℝ}
    (Bad : Ω → Set β)
    (hBad : @MeasurableSet (Ω × β) (m_A.prod mβ) {p : Ω × β | p.2 ∈ Bad p.1})
    (hsec : ∀ ω, ν (Bad ω) ≤ ENNReal.ofReal δ) :
    μ {ω | Y ω ∈ Bad ω} ≤ ENNReal.ofReal δ := by
  classical
  have hJ_meas : @Measurable Ω (Ω × β) mΩ (m_A.prod mβ) (fun ω => (ω, Y ω)) := by
    apply Measurable.prod
    · exact measurable_id'' hm_A_le
    · exact hY
  -- Product factorisation `μ.map (ω ↦ (ω, Y ω)) = (μ.trim m_A).prod ν`.
  have hmap : @Measure.map Ω (Ω × β) mΩ (m_A.prod mβ)
        (fun ω => (ω, Y ω)) μ
      = @Measure.prod Ω β m_A mβ (μ.trim hm_A_le) ν := by
    have h := @Causalean.Mathlib.indep_trim_prod_map_eq Ω β mΩ mβ μ _ m_A hm_A_le Y hY hindep
    rw [hY_law] at h
    exact h
  -- The random event is the `(ω ↦ (ω, Y ω))`-preimage of the joint bad set.
  have hmass :
      μ {ω | Y ω ∈ Bad ω}
        = (@Measure.prod Ω β m_A mβ (μ.trim hm_A_le) ν) {p : Ω × β | p.2 ∈ Bad p.1} := by
    have hpre : {ω | Y ω ∈ Bad ω}
        = (fun ω => (ω, Y ω)) ⁻¹' {p : Ω × β | p.2 ∈ Bad p.1} := rfl
    rw [hpre,
      ← @Measure.map_apply Ω (Ω × β) mΩ (m_A.prod mβ) μ
        (fun ω => (ω, Y ω)) hJ_meas {p : Ω × β | p.2 ∈ Bad p.1} hBad,
      hmap]
  rw [hmass,
    @Measure.prod_apply Ω β m_A mβ (μ.trim hm_A_le) ν _ {p : Ω × β | p.2 ∈ Bad p.1} hBad]
  -- Integrate the section bound against the fold-A probability marginal.
  have hsec' : ∀ ω, ν (Prod.mk ω ⁻¹' {p : Ω × β | p.2 ∈ Bad p.1}) ≤ ENNReal.ofReal δ := by
    intro ω
    have he : Prod.mk ω ⁻¹' {p : Ω × β | p.2 ∈ Bad p.1} = Bad ω := by
      ext s; simp
    rw [he]; exact hsec ω
  calc
    ∫⁻ ω, ν (Prod.mk ω ⁻¹' {p : Ω × β | p.2 ∈ Bad p.1}) ∂(μ.trim hm_A_le)
        ≤ ∫⁻ _ : Ω, ENNReal.ofReal δ ∂(μ.trim hm_A_le) := lintegral_mono hsec'
    _ = ENNReal.ofReal δ * (μ.trim hm_A_le) Set.univ := by rw [lintegral_const]
    _ = ENNReal.ofReal δ := by
        rw [trim_measurableSet_eq hm_A_le MeasurableSet.univ, measure_univ, mul_one]

end OrthogonalLearning
end Estimation
end Causalean
