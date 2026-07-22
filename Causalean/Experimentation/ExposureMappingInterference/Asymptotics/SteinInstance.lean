/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Experimentation.ExposureMappingInterference.Asymptotics.SteinCLT
import Causalean.Experimentation.DesignBased.GaussianCDF
import Causalean.Experimentation.DesignBased.FiniteDesignMeasure
import Causalean.Experimentation.ExposureMappingInterference.Asymptotics.Intervals
import Causalean.Experimentation.DesignBased.HT.Unbiased
import Causalean.Mathlib.Probability.SteinMethod.CLT
import Causalean.Mathlib.Probability.SteinMethod.DepGraphCLT

/-!
# Discharging `LocalDependenceCLT` via the abstract Stein CLT

This file bridges the finite-design Horvitz-Thompson effect statistic to the measure-theoretic
dependency-graph Stein CLT.  The studentized effect statistic is written as a sum of per-unit
summands

    Xₙᵢ = (rawᵢ − E[rawᵢ]) / (N · σₙ),   σₙ = √(Var[τ̂]),

where `rawᵢ = 1(Dᵢ=dk)Yᵢ/πᵢ(dk) − 1(Dᵢ=dl)Yᵢ/πᵢ(dl)` is unit `i`'s contribution to `N·τ̂`.
Then `∑ᵢ Xₙᵢ = studentizedEffect`, the summands are mean-zero with `Var(∑Xₙᵢ)=1`, and the
abstract dependency-graph CLT `stein_cdf_clt` yields `P[studentizedEffect ≤ t] → Φ(t)`, i.e.
`LocalDependenceCLT`.

The main public results are `localDependenceCLT_of_stein`, which assumes the Stein negligibility
limits directly, `localDependenceCLT_of_conditions`, which derives those limits from a bounded
dependency graph and uniformly negligible summands, and `localDependenceCLT_of_paper_conditions`,
which packages the Aronow-Samii boundedness, positive-propensity, population-growth, and
variance-growth conditions.  The corresponding `wald_coverage_of_*` theorems compose these CLT
discharges with the oracle Wald-coverage theorem.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Real Topology

namespace Causalean
namespace Experimentation
namespace ExposureMappingInterference

open Causalean.Experimentation.DesignBased
namespace Experiment

variable (E : Experiment)

/-- This is one unit's inverse-propensity-weighted contribution to the unnormalized Horvitz-Thompson
effect estimator.

It is the difference between that unit's weighted observed outcome under the two target exposure
conditions. -/
noncomputable def effRaw (dk dl : E.Δ) (i : E.ι) (z : E.Ω) : ℝ :=
  expoInd E.f E.θ i dk z * Yobs E.y E.f E.θ i z / prop E.D E.f E.θ i dk
    - expoInd E.f E.θ i dl z * Yobs E.y E.f E.θ i z / prop E.D E.f E.θ i dl

/-- This is the centered and standardized per-unit summand used to form the studentized
Horvitz-Thompson effect statistic. -/
noncomputable def effSummand (dk dl : E.Δ) (i : E.ι) (z : E.Ω) : ℝ :=
  (effRaw E dk dl i z - E.D.E (effRaw E dk dl i))
    / ((Fintype.card E.ι : ℝ) * Real.sqrt (E.D.Var (htEffect E.D E.y E.f E.θ dk dl)))

/-- The sum of the per-unit raw contributions is `N · τ̂`. -/
private lemma sum_effRaw (dk dl : E.Δ) (z : E.Ω) :
    ∑ i, E.effRaw dk dl i z
      = (Fintype.card E.ι : ℝ) * htEffect E.D E.y E.f E.θ dk dl z := by
  have hsum : ∑ i, E.effRaw dk dl i z
      = htTotal E.D E.y E.f E.θ dk z - htTotal E.D E.y E.f E.θ dl z := by
    unfold effRaw htTotal
    rw [Finset.sum_sub_distrib]
  rw [hsum, htEffect, htMean, htMean]
  by_cases hN : (Fintype.card E.ι : ℝ) = 0
  · have hempty : (Finset.univ : Finset E.ι) = ∅ :=
      Finset.univ_eq_empty_iff.mpr (Fintype.card_eq_zero_iff.mp (by exact_mod_cast hN))
    rw [hN, htTotal, htTotal, hempty]
    simp only [Finset.sum_empty, zero_mul, sub_self]
  · field_simp

/-- The design expectation of the per-unit raw contribution sum is `N · τ` when both target
exposure propensities are nonzero for every unit. -/
private lemma E_sum_effRaw (dk dl : E.Δ)
    (hk : ∀ i, prop E.D E.f E.θ i dk ≠ 0) (hl : ∀ i, prop E.D E.f E.θ i dl ≠ 0) :
    ∑ i, E.D.E (E.effRaw dk dl i)
      = (Fintype.card E.ι : ℝ) * tauTrue E.y dk dl := by
  rw [← FiniteDesign.E_sum]
  rw [show (fun z => ∑ i, E.effRaw dk dl i z)
        = (fun z => (Fintype.card E.ι : ℝ) * htEffect E.D E.y E.f E.θ dk dl z) from
      funext (fun z => E.sum_effRaw dk dl z)]
  rw [FiniteDesign.E_const_mul, E_htEffect E.D E.y E.f E.θ dk dl hk hl]

/-- **Step A.** The dependency-graph standardized sum equals the studentized HT effect when both
target exposure propensities are nonzero for every unit. -/
private lemma depSum_effSummand (dk dl : E.Δ)
    (hk : ∀ i, prop E.D E.f E.θ i dk ≠ 0) (hl : ∀ i, prop E.D E.f E.θ i dl ≠ 0) :
    SteinMethod.depSum (fun i => E.effSummand dk dl i) = E.studentizedEffect dk dl := by
  funext z
  unfold SteinMethod.depSum effSummand studentizedEffect
  set N : ℝ := (Fintype.card E.ι : ℝ) with hNdef
  set σ : ℝ := Real.sqrt (E.D.Var (htEffect E.D E.y E.f E.θ dk dl)) with hσdef
  set he : ℝ := htEffect E.D E.y E.f E.θ dk dl z with hedef
  set τ : ℝ := tauTrue E.y dk dl with hτdef
  -- The sum splits into the centered numerators over the common denominator `N·σ`.
  have hsplit : (∑ i, (E.effRaw dk dl i z - E.D.E (E.effRaw dk dl i)) / (N * σ))
      = (∑ i, E.effRaw dk dl i z - ∑ i, E.D.E (E.effRaw dk dl i)) / (N * σ) := by
    rw [← Finset.sum_div, Finset.sum_sub_distrib]
  rw [hsplit, E.sum_effRaw dk dl z, E.E_sum_effRaw dk dl hk hl]
  rw [← hedef, ← hτdef]
  by_cases hN : N = 0
  · -- Degenerate population: both sides vanish.
    have hcard : Fintype.card E.ι = 0 := by
      have h := hN; rw [hNdef] at h; exact_mod_cast h
    have hempty : (Finset.univ : Finset E.ι) = ∅ :=
      Finset.univ_eq_empty_iff.mpr (Fintype.card_eq_zero_iff.mp hcard)
    have hhe : he = 0 := by
      rw [hedef, htEffect, htMean, htMean, htTotal, htTotal, hempty]
      simp only [Finset.sum_empty, zero_div, sub_self]
    have hτ0 : τ = 0 := by
      rw [hτdef, tauTrue, muTrue, muTrue, hempty]
      simp only [Finset.sum_empty, zero_div, sub_self]
    rw [hN, hhe, hτ0]; simp
  · -- Generic case: cancel `N`.
    rw [show N * he - N * τ = N * (he - τ) by ring,
      mul_div_mul_left _ _ hN]

/-- Each centered standardized summand has zero design expectation. -/
private lemma E_effSummand (dk dl : E.Δ) (i : E.ι) :
    E.D.E (E.effSummand dk dl i) = 0 := by
  unfold effSummand
  set c : ℝ := (Fintype.card E.ι : ℝ)
    * Real.sqrt (E.D.Var (htEffect E.D E.y E.f E.θ dk dl)) with hc
  have hrw : (fun z => (E.effRaw dk dl i z - E.D.E (E.effRaw dk dl i)) / c)
      = (fun z => c⁻¹ * (E.effRaw dk dl i z - E.D.E (E.effRaw dk dl i))) := by
    funext z; rw [div_eq_inv_mul]
  rw [hrw, FiniteDesign.E_const_mul, FiniteDesign.E_sub, FiniteDesign.E_const, sub_self,
    mul_zero]

/-- **Step B (variance).** The design variance of the standardized statistic equals one
(equivalently `∫ studentizedEffect² = 1`), under nonzero true variance and nonzero target
exposure propensities. -/
private lemma E_studentizedEffect_sq (dk dl : E.Δ)
    (hVar : 0 < E.D.Var (htEffect E.D E.y E.f E.θ dk dl))
    (hk : ∀ i, prop E.D E.f E.θ i dk ≠ 0) (hl : ∀ i, prop E.D E.f E.θ i dl ≠ 0) :
    E.D.E (fun z => (E.studentizedEffect dk dl z) ^ 2) = 1 := by
  set V : ℝ := E.D.Var (htEffect E.D E.y E.f E.θ dk dl) with hV
  set σ : ℝ := Real.sqrt V with hσ
  have hσ2 : σ ^ 2 = V := by rw [hσ, Real.sq_sqrt hVar.le]
  have hσne : σ ≠ 0 := by
    rw [hσ]; exact Real.sqrt_ne_zero'.mpr hVar
  have hτ : tauTrue E.y dk dl = E.D.E (htEffect E.D E.y E.f E.θ dk dl) :=
    (E_htEffect E.D E.y E.f E.θ dk dl hk hl).symm
  have hrw : (fun z => (E.studentizedEffect dk dl z) ^ 2)
      = (fun z => σ⁻¹ ^ 2
          * (htEffect E.D E.y E.f E.θ dk dl z
              - E.D.E (htEffect E.D E.y E.f E.θ dk dl)) ^ 2) := by
    funext z
    unfold studentizedEffect
    rw [hτ, ← hV, ← hσ, div_pow, div_eq_inv_mul, ← inv_pow]
  rw [hrw, FiniteDesign.E_const_mul]
  have hVardef : E.D.E (fun z => (htEffect E.D E.y E.f E.θ dk dl z
      - E.D.E (htEffect E.D E.y E.f E.θ dk dl)) ^ 2) = V := rfl
  rw [hVardef]
  rw [inv_pow, hσ2]
  field_simp

/-- Equip a finite assignment space with the top σ-algebra (every set measurable), so the design
measure and the measure-theoretic CLT machinery apply with no extra hypotheses. -/
instance instMeasurableSpaceΩ (E : Experiment) : MeasurableSpace E.Ω := ⊤

/-- The top sigma-algebra on a finite assignment space makes every singleton measurable. -/
instance instMeasurableSingletonΩ (E : Experiment) : MeasurableSingletonClass E.Ω :=
  ⟨fun _ => trivial⟩

end Experiment

/-- The studentized Horvitz-Thompson effect statistic converges in distribution to a standard normal
under the abstract Stein local-dependence conditions.

The assumptions provide bounded summands with a vanishing bound, dependency neighborhoods,
nonzero variance, positive propensities, and the two Stein negligibility limits. -/
theorem localDependenceCLT_of_stein (Exp : ℕ → Experiment) (dk dl : ∀ n, (Exp n).Δ)
    (N : ∀ n, (Exp n).ι → Finset ((Exp n).ι))
    (hself : ∀ n i, i ∈ N n i)
    (hVar : ∀ n, 0 < (Exp n).D.Var
      (htEffect (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (dk n) (dl n)))
    (hposk : ∀ n i, prop (Exp n).D (Exp n).f (Exp n).θ i (dk n) ≠ 0)
    (hposl : ∀ n i, prop (Exp n).D (Exp n).f (Exp n).θ i (dl n) ≠ 0)
    (B : ℕ → ℝ) (hB : ∀ n, 0 ≤ B n) (hB0 : Tendsto B atTop (𝓝 0))
    (hbound : ∀ n i z, |(Exp n).effSummand (dk n) (dl n) i z| ≤ B n)
    (hindep : ∀ n i, IndepFun
      ((Exp n).effSummand (dk n) (dl n) i)
      (fun z => ∑ j ∈ Finset.univ \ N n i, (Exp n).effSummand (dk n) (dl n) j z)
      (Exp n).D.toMeasure)
    (herr1 : Tendsto (fun n => (Exp n).D.Var
      (fun z => ∑ i, (Exp n).effSummand (dk n) (dl n) i z
        * ∑ j ∈ N n i, (Exp n).effSummand (dk n) (dl n) j z)) atTop (𝓝 0))
    (herr2 : Tendsto (fun n => ∑ i, (Exp n).D.E
      (fun z => |(Exp n).effSummand (dk n) (dl n) i z|
        * (∑ j ∈ N n i, (Exp n).effSummand (dk n) (dl n) j z) ^ 2)) atTop (𝓝 0)) :
    LocalDependenceCLT Exp dk dl := by
  classical
  -- Abbreviations matching `stein_cdf_clt`.
  set μ : ∀ n, Measure (Exp n).Ω := fun n => (Exp n).D.toMeasure with hμ
  set X : ∀ n, (Exp n).ι → (Exp n).Ω → ℝ :=
    fun n i => (Exp n).effSummand (dk n) (dl n) i with hX
  -- Each summand is measurable (the assignment space carries the top σ-algebra).
  have hmeas : ∀ n i, Measurable (X n i) := fun n i => measurable_from_top
  -- Mean-zero: `∫ Xₙᵢ ∂μₙ = D.E (effSummand) = 0`.
  have hmean : ∀ n i, ∫ z, X n i z ∂(μ n) = 0 := by
    intro n i
    rw [hμ, hX, FiniteDesign.integral_toMeasure, Experiment.E_effSummand]
  -- `depSum (Xₙ) = studentizedEffect`.
  have hdep : ∀ n, SteinMethod.depSum (X n) = (Exp n).studentizedEffect (dk n) (dl n) :=
    fun n => Experiment.depSum_effSummand _ _ _ (hposk n) (hposl n)
  -- Unit total variance: `∫ (depSum Xₙ)² ∂μₙ = 1`.
  have hvar : ∀ n, ∫ z, (SteinMethod.depSum (X n) z) ^ 2 ∂(μ n) = 1 := by
    intro n
    rw [hdep n, hμ, FiniteDesign.integral_toMeasure,
      Experiment.E_studentizedEffect_sq _ _ _ (hVar n) (hposk n) (hposl n)]
  -- The two Stein error limits, transported through the measure bridge.
  have herr1' : Tendsto
      (fun n => variance
        (fun z => ∑ i, X n i z * SteinMethod.nbhdSum (X n) (N n) i z) (μ n)) atTop (𝓝 0) := by
    refine herr1.congr (fun n => ?_)
    rw [hμ, FiniteDesign.variance_toMeasure]
    rfl
  have herr2' : Tendsto
      (fun n => ∑ i, ∫ z, |X n i z| * (SteinMethod.nbhdSum (X n) (N n) i z) ^ 2 ∂(μ n)) atTop
      (𝓝 0) := by
    refine herr2.congr (fun n => ?_)
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hμ, FiniteDesign.integral_toMeasure]
    rfl
  -- Assemble the abstract Stein CLT, evaluated at each threshold.
  refine ⟨fun t => ?_⟩
  have hclt := SteinMethod.stein_cdf_clt μ X N hmeas B hB hbound hmean hself hindep hvar
    herr1' herr2' t
  -- Rewrite the limit point: `Φ(t) = (gaussianReal 0 1).real (Iic t)` by definition.
  rw [show stdNormalCdf t = (gaussianReal 0 1).real (Set.Iic t) from rfl]
  -- Match the prelimit sequences pointwise.
  refine hclt.congr (fun n => ?_)
  -- `D.Pr {studentized ≤ t} = (μₙ.map (depSum Xₙ)).real (Iic t)`.
  have hWmeas : Measurable (SteinMethod.depSum (X n)) := by
    rw [hdep n]; exact measurable_from_top
  have hset : {z | (Exp n).studentizedEffect (dk n) (dl n) z ≤ t}
      = (SteinMethod.depSum (X n)) ⁻¹' Set.Iic t := by
    rw [hdep n]; rfl
  rw [hμ] at *
  rw [← FiniteDesign.toMeasure_real_setOf, hset,
    MeasureTheory.map_measureReal_apply hWmeas measurableSet_Iic]

/-- The Aronow-Samii oracle Wald interval has asymptotic coverage at least the nominal level under
the primitive Stein-discharge conditions.

This composes the discharged local-dependence central limit theorem with the existing Wald coverage
theorem, so no separate central-limit premise remains. -/
theorem wald_coverage_of_stein (Exp : ℕ → Experiment) (dk dl : ∀ n, (Exp n).Δ)
    (N : ∀ n, (Exp n).ι → Finset ((Exp n).ι))
    (hself : ∀ n i, i ∈ N n i)
    (hVar : ∀ n, 0 < (Exp n).D.Var
      (htEffect (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (dk n) (dl n)))
    (hposk : ∀ n i, prop (Exp n).D (Exp n).f (Exp n).θ i (dk n) ≠ 0)
    (hposl : ∀ n i, prop (Exp n).D (Exp n).f (Exp n).θ i (dl n) ≠ 0)
    (B : ℕ → ℝ) (hB : ∀ n, 0 ≤ B n) (hB0 : Tendsto B atTop (𝓝 0))
    (hbound : ∀ n i z, |(Exp n).effSummand (dk n) (dl n) i z| ≤ B n)
    (hindep : ∀ n i, IndepFun
      ((Exp n).effSummand (dk n) (dl n) i)
      (fun z => ∑ j ∈ Finset.univ \ N n i, (Exp n).effSummand (dk n) (dl n) j z)
      (Exp n).D.toMeasure)
    (herr1 : Tendsto (fun n => (Exp n).D.Var
      (fun z => ∑ i, (Exp n).effSummand (dk n) (dl n) i z
        * ∑ j ∈ N n i, (Exp n).effSummand (dk n) (dl n) j z)) atTop (𝓝 0))
    (herr2 : Tendsto (fun n => ∑ i, (Exp n).D.E
      (fun z => |(Exp n).effSummand (dk n) (dl n) i z|
        * (∑ j ∈ N n i, (Exp n).effSummand (dk n) (dl n) j z) ^ 2)) atTop (𝓝 0))
    {α : ℝ} (zq : ℝ) (hzq0 : 0 ≤ zq) (hzq : stdNormalCdf zq = 1 - α / 2) :
    1 - α ≤ Filter.liminf
      (fun n => (Exp n).D.Pr (fun z =>
        |htEffect (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (dk n) (dl n) z
            - tauTrue (Exp n).y (dk n) (dl n)|
          ≤ zq * Real.sqrt ((Exp n).D.Var
              (htEffect (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (dk n) (dl n)))))
      Filter.atTop :=
  wald_coverage Exp dk dl
    (localDependenceCLT_of_stein Exp dk dl N hself hVar hposk hposl B hB hB0 hbound hindep
      herr1 herr2)
    hVar zq hzq0 hzq

/-- The local-dependence central limit theorem follows from a bounded-degree dependency graph and
the primitive Aronow-Samii rate conditions.

The Stein negligibility limits are derived from the uniformly negligible bounded summands, rather
than assumed separately. -/
theorem localDependenceCLT_of_conditions (Exp : ℕ → Experiment) (dk dl : ∀ n, (Exp n).Δ)
    (Dg : ∀ n, SteinMethod.DepGraph (fun i => (Exp n).effSummand (dk n) (dl n) i)
      (Exp n).D.toMeasure)
    (m : ℕ) (hdeg : ∀ n i, ((Dg n).nbhd i).card ≤ m)
    (hVar : ∀ n, 0 < (Exp n).D.Var
      (htEffect (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (dk n) (dl n)))
    (hposk : ∀ n i, prop (Exp n).D (Exp n).f (Exp n).θ i (dk n) ≠ 0)
    (hposl : ∀ n i, prop (Exp n).D (Exp n).f (Exp n).θ i (dl n) ≠ 0)
    (B : ℕ → ℝ) (hB : ∀ n, 0 ≤ B n)
    (hbound : ∀ n i z, |(Exp n).effSummand (dk n) (dl n) i z| ≤ B n)
    (hB0 : Tendsto B atTop (𝓝 0))
    (hNB3 : Tendsto (fun n => (Fintype.card (Exp n).ι : ℝ) * (B n) ^ 3) atTop (𝓝 0)) :
    LocalDependenceCLT Exp dk dl := by
  classical
  -- Abbreviations matching `stein_cdf_clt_of_depGraph`.
  set μ : ∀ n, Measure (Exp n).Ω := fun n => (Exp n).D.toMeasure with hμ
  set X : ∀ n, (Exp n).ι → (Exp n).Ω → ℝ :=
    fun n i => (Exp n).effSummand (dk n) (dl n) i with hX
  -- Each summand is measurable (the assignment space carries the top σ-algebra).
  have hmeas : ∀ n i, Measurable (X n i) := fun n i => measurable_from_top
  -- Mean-zero: `∫ Xₙᵢ ∂μₙ = D.E (effSummand) = 0`.
  have hmean : ∀ n i, ∫ z, X n i z ∂(μ n) = 0 := by
    intro n i
    rw [hμ, hX, FiniteDesign.integral_toMeasure, Experiment.E_effSummand]
  -- `depSum (Xₙ) = studentizedEffect`.
  have hdep : ∀ n, SteinMethod.depSum (X n) = (Exp n).studentizedEffect (dk n) (dl n) :=
    fun n => Experiment.depSum_effSummand _ _ _ (hposk n) (hposl n)
  -- Unit total variance: `∫ (depSum Xₙ)² ∂μₙ = 1`.
  have hvar : ∀ n, ∫ z, (SteinMethod.depSum (X n) z) ^ 2 ∂(μ n) = 1 := by
    intro n
    rw [hdep n, hμ, FiniteDesign.integral_toMeasure,
      Experiment.E_studentizedEffect_sq _ _ _ (hVar n) (hposk n) (hposl n)]
  -- Assemble the dependency-graph Stein CLT (negligibility derived internally), at each threshold.
  refine ⟨fun t => ?_⟩
  have hclt := SteinMethod.stein_cdf_clt_of_depGraph μ X Dg hmeas m hdeg B hB hbound hB0 hNB3
    hmean hvar t
  -- Rewrite the limit point: `Φ(t) = (gaussianReal 0 1).real (Iic t)` by definition.
  rw [show stdNormalCdf t = (gaussianReal 0 1).real (Set.Iic t) from rfl]
  -- Match the prelimit sequences pointwise.
  refine hclt.congr (fun n => ?_)
  -- `D.Pr {studentized ≤ t} = (μₙ.map (depSum Xₙ)).real (Iic t)`.
  have hWmeas : Measurable (SteinMethod.depSum (X n)) := by
    rw [hdep n]; exact measurable_from_top
  have hset : {z | (Exp n).studentizedEffect (dk n) (dl n) z ≤ t}
      = (SteinMethod.depSum (X n)) ⁻¹' Set.Iic t := by
    rw [hdep n]; rfl
  rw [hμ] at *
  rw [← FiniteDesign.toMeasure_real_setOf, hset,
    MeasureTheory.map_measureReal_apply hWmeas measurableSet_Iic]

/-- The Aronow-Samii oracle Wald interval has asymptotic coverage at least the nominal level under
the bounded-degree primitive conditions.

This combines the primitive local-dependence central limit theorem with the existing Wald coverage
result, without assuming a separate central-limit theorem or Stein-negligibility limits. -/
theorem wald_coverage_of_conditions (Exp : ℕ → Experiment) (dk dl : ∀ n, (Exp n).Δ)
    (Dg : ∀ n, SteinMethod.DepGraph (fun i => (Exp n).effSummand (dk n) (dl n) i)
      (Exp n).D.toMeasure)
    (m : ℕ) (hdeg : ∀ n i, ((Dg n).nbhd i).card ≤ m)
    (hVar : ∀ n, 0 < (Exp n).D.Var
      (htEffect (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (dk n) (dl n)))
    (hposk : ∀ n i, prop (Exp n).D (Exp n).f (Exp n).θ i (dk n) ≠ 0)
    (hposl : ∀ n i, prop (Exp n).D (Exp n).f (Exp n).θ i (dl n) ≠ 0)
    (B : ℕ → ℝ) (hB : ∀ n, 0 ≤ B n)
    (hbound : ∀ n i z, |(Exp n).effSummand (dk n) (dl n) i z| ≤ B n)
    (hB0 : Tendsto B atTop (𝓝 0))
    (hNB3 : Tendsto (fun n => (Fintype.card (Exp n).ι : ℝ) * (B n) ^ 3) atTop (𝓝 0))
    {α : ℝ} (zq : ℝ) (hzq0 : 0 ≤ zq) (hzq : stdNormalCdf zq = 1 - α / 2) :
    1 - α ≤ Filter.liminf
      (fun n => (Exp n).D.Pr (fun z =>
        |htEffect (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (dk n) (dl n) z
            - tauTrue (Exp n).y (dk n) (dl n)|
          ≤ zq * Real.sqrt ((Exp n).D.Var
              (htEffect (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (dk n) (dl n)))))
      Filter.atTop :=
  wald_coverage Exp dk dl
    (localDependenceCLT_of_conditions Exp dk dl Dg m hdeg hVar hposk hposl B hB hbound hB0 hNB3)
    hVar zq hzq0 hzq

/-- Absolute value of a design expectation is bounded by a uniform pointwise bound on the
random variable: `(∀ z, |g z| ≤ C) → |D.E g| ≤ C`. -/
private lemma abs_E_le {Ω : Type} [Fintype Ω] (D : FiniteDesign Ω) {g : Ω → ℝ} {C : ℝ}
    (h : ∀ z, |g z| ≤ C) : |D.E g| ≤ C := by
  unfold FiniteDesign.E
  calc |∑ z, D.p z * g z| ≤ ∑ z, |D.p z * g z| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ z, D.p z * |g z| := by
        apply Finset.sum_congr rfl; intro z _; rw [abs_mul, abs_of_nonneg (D.p_nonneg z)]
    _ ≤ ∑ z, D.p z * C := by
        apply Finset.sum_le_sum; intro z _; exact mul_le_mul_of_nonneg_left (h z) (D.p_nonneg z)
    _ = C := by rw [← Finset.sum_mul, D.p_sum, one_mul]

/-- Pointwise bound on a single inverse-propensity-weighted outcome term: under bounded outcomes
(`|y i d| ≤ c₁`) and bounded inverse propensities (`1/c₂ ≤ π`, `π > 0`, `c₂ > 0`), the term
`1(expo i = d)·Yobs i / π_i(d)` is bounded in absolute value by `c₁·c₂`. -/
private lemma abs_effTerm_le (E : Experiment) (d : E.Δ) (i : E.ι) (z : E.Ω)
    (c1 : ℝ) (hy : |E.y i d| ≤ c1) (c2 : ℝ) (hc2 : 0 < c2)
    (hπ : 1 / c2 ≤ prop E.D E.f E.θ i d) :
    |expoInd E.f E.θ i d z * Yobs E.y E.f E.θ i z / prop E.D E.f E.θ i d| ≤ c1 * c2 := by
  set p : ℝ := prop E.D E.f E.θ i d with hp
  have hppos : 0 < p := lt_of_lt_of_le (by positivity) hπ
  have hpc : 1 / p ≤ c2 := by
    have := one_div_le_one_div_of_le (by positivity : (0:ℝ) < 1 / c2) hπ
    rwa [one_div_one_div] at this
  rw [expoInd_mul_Yobs]
  set a : ℝ := expoInd E.f E.θ i d z with ha
  have ha0 : 0 ≤ a := FiniteDesign.ind_nonneg _ z
  have ha1 : a ≤ 1 := FiniteDesign.ind_le_one _ z
  have hc1 : 0 ≤ c1 := le_trans (abs_nonneg _) hy
  calc |a * E.y i d / p|
      = a * |E.y i d| * (1 / p) := by
        rw [abs_div, abs_mul, abs_of_nonneg ha0, abs_of_pos hppos]; ring
    _ ≤ 1 * c1 * c2 := by gcongr
    _ = c1 * c2 := by ring

/-- Pointwise bound on a unit's raw HT contribution `effRaw`, the difference of two
inverse-propensity-weighted outcome terms: under Condition 1 it is bounded by `2·c₁·c₂`. -/
private lemma abs_effRaw_le (E : Experiment) (dk dl : E.Δ) (i : E.ι) (z : E.Ω)
    (c1 : ℝ) (hyk : |E.y i dk| ≤ c1) (hyl : |E.y i dl| ≤ c1)
    (c2 : ℝ) (hc2 : 0 < c2)
    (hπk : 1 / c2 ≤ prop E.D E.f E.θ i dk) (hπl : 1 / c2 ≤ prop E.D E.f E.θ i dl) :
    |E.effRaw dk dl i z| ≤ 2 * c1 * c2 := by
  unfold Experiment.effRaw
  calc |expoInd E.f E.θ i dk z * Yobs E.y E.f E.θ i z / prop E.D E.f E.θ i dk
          - expoInd E.f E.θ i dl z * Yobs E.y E.f E.θ i z / prop E.D E.f E.θ i dl|
      ≤ |expoInd E.f E.θ i dk z * Yobs E.y E.f E.θ i z / prop E.D E.f E.θ i dk|
          + |expoInd E.f E.θ i dl z * Yobs E.y E.f E.θ i z / prop E.D E.f E.θ i dl| :=
        abs_sub _ _
    _ ≤ c1 * c2 + c1 * c2 :=
        add_le_add (abs_effTerm_le E dk i z c1 hyk c2 hc2 hπk)
          (abs_effTerm_le E dl i z c1 hyl c2 hc2 hπl)
    _ = 2 * c1 * c2 := by ring

/-- The local-dependence central limit theorem follows from the literal Aronow-Samii boundedness,
dependency-graph, and variance-growth conditions.

The summand-bound rates are derived from bounded outcomes, bounded inverse propensities, growing
population size, and a positive limit for population size times effect-estimator variance. -/
theorem localDependenceCLT_of_paper_conditions (Exp : ℕ → Experiment) (dk dl : ∀ n, (Exp n).Δ)
    (Dg : ∀ n, SteinMethod.DepGraph (fun i => (Exp n).effSummand (dk n) (dl n) i)
      (Exp n).D.toMeasure)
    (m : ℕ) (hdeg : ∀ n i, ((Dg n).nbhd i).card ≤ m)
    (c1 : ℝ) (hyk : ∀ n i, |(Exp n).y i (dk n)| ≤ c1) (hyl : ∀ n i, |(Exp n).y i (dl n)| ≤ c1)
    (c2 : ℝ) (hc2 : 0 < c2)
    (hπk : ∀ n i, 1 / c2 ≤ prop (Exp n).D (Exp n).f (Exp n).θ i (dk n))
    (hπl : ∀ n i, 1 / c2 ≤ prop (Exp n).D (Exp n).f (Exp n).θ i (dl n))
    (hN : Tendsto (fun n => (Fintype.card (Exp n).ι : ℝ)) atTop atTop)
    (hVar : ∀ n, 0 < (Exp n).D.Var
      (htEffect (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (dk n) (dl n)))
    (cVar : ℝ) (hcVar : 0 < cVar)
    (hCond4 : Tendsto (fun n => (Fintype.card (Exp n).ι : ℝ)
      * (Exp n).D.Var (htEffect (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (dk n) (dl n)))
      atTop (𝓝 cVar)) :
    LocalDependenceCLT Exp dk dl := by
  classical
  -- Abbreviations.
  set card : ℕ → ℝ := fun n => (Fintype.card (Exp n).ι : ℝ) with hcard
  set Var : ℕ → ℝ := fun n =>
    (Exp n).D.Var (htEffect (Exp n).D (Exp n).y (Exp n).f (Exp n).θ (dk n) (dl n)) with hVardef
  set σ : ℕ → ℝ := fun n => Real.sqrt (Var n) with hσdef
  set B : ℕ → ℝ := fun n => 4 * c1 * c2 / (card n * σ n) with hBdef
  -- Basic positivity facts.
  have hcard_nonneg : ∀ n, 0 ≤ card n := fun n => by positivity
  have hσ_nonneg : ∀ n, 0 ≤ σ n := fun n => Real.sqrt_nonneg _
  have hden_nonneg : ∀ n, 0 ≤ card n * σ n := fun n => mul_nonneg (hcard_nonneg n) (hσ_nonneg n)
  -- `0 ≤ c1` whenever the population is nonempty (an outcome witness exists).
  have hc1_of : ∀ n (i : (Exp n).ι), 0 ≤ c1 := fun n i => le_trans (abs_nonneg _) (hyk n i)
  -- `hposk`/`hposl`: positive propensities ⇒ nonzero.
  have hposk : ∀ n i, prop (Exp n).D (Exp n).f (Exp n).θ i (dk n) ≠ 0 := by
    intro n i
    exact ne_of_gt (lt_of_lt_of_le (by positivity) (hπk n i))
  have hposl : ∀ n i, prop (Exp n).D (Exp n).f (Exp n).θ i (dl n) ≠ 0 := by
    intro n i
    exact ne_of_gt (lt_of_lt_of_le (by positivity) (hπl n i))
  -- `hB`: `0 ≤ B n`. Nonempty population gives `c1 ≥ 0`; empty gives `card n = 0` so `B n = 0`.
  have hB : ∀ n, 0 ≤ B n := by
    intro n
    rcases isEmpty_or_nonempty (Exp n).ι with he | hne
    · have hc0 : card n = 0 := by
        rw [hcard]; simp [Fintype.card_eq_zero]
      simp [hBdef, hc0]
    · obtain ⟨i⟩ := hne
      exact div_nonneg (by have := hc1_of n i; positivity) (hden_nonneg n)
  -- `hbound`: each centered standardized summand is bounded by `B n`.
  have hbound : ∀ n i z, |(Exp n).effSummand (dk n) (dl n) i z| ≤ B n := by
    intro n i z
    have hraw : ∀ z', |(Exp n).effRaw (dk n) (dl n) i z'| ≤ 2 * c1 * c2 := fun z' =>
      abs_effRaw_le (Exp n) (dk n) (dl n) i z' c1 (hyk n i) (hyl n i) c2 hc2 (hπk n i) (hπl n i)
    have hEraw : |(Exp n).D.E ((Exp n).effRaw (dk n) (dl n) i)| ≤ 2 * c1 * c2 :=
      abs_E_le (Exp n).D hraw
    have hnum : |(Exp n).effRaw (dk n) (dl n) i z
        - (Exp n).D.E ((Exp n).effRaw (dk n) (dl n) i)| ≤ 4 * c1 * c2 := by
      calc |(Exp n).effRaw (dk n) (dl n) i z
              - (Exp n).D.E ((Exp n).effRaw (dk n) (dl n) i)|
          ≤ |(Exp n).effRaw (dk n) (dl n) i z|
              + |(Exp n).D.E ((Exp n).effRaw (dk n) (dl n) i)| := abs_sub _ _
        _ ≤ 2 * c1 * c2 + 2 * c1 * c2 := add_le_add (hraw z) hEraw
        _ = 4 * c1 * c2 := by ring
    change |((Exp n).effRaw (dk n) (dl n) i z - (Exp n).D.E ((Exp n).effRaw (dk n) (dl n) i))
        / (card n * σ n)| ≤ 4 * c1 * c2 / (card n * σ n)
    rw [abs_div, abs_of_nonneg (hden_nonneg n)]
    gcongr
  -- `card n * σ n = √(card n ^ 2 * Var n)`: the denominator as one square root.
  have hdenom_sqrt : ∀ n, card n * σ n = Real.sqrt (card n ^ 2 * Var n) := by
    intro n
    rw [hσdef, Real.sqrt_mul (by positivity), Real.sqrt_sq (hcard_nonneg n)]
  -- `card n ^ 2 * Var n → atTop` (from `card → ∞` and `card·Var → cVar > 0`).
  have hcard2Var : Tendsto (fun n => card n ^ 2 * Var n) atTop atTop := by
    have heq : (fun n => card n ^ 2 * Var n) = fun n => card n * (card n * Var n) := by
      funext n; ring
    rw [heq]
    exact hN.atTop_mul_pos hcVar hCond4
  -- `card n * σ n → atTop`.
  have hdenom_atTop : Tendsto (fun n => card n * σ n) atTop atTop := by
    have : (fun n => card n * σ n) = fun n => Real.sqrt (card n ^ 2 * Var n) := funext hdenom_sqrt
    rw [this]
    exact Real.tendsto_sqrt_atTop.comp hcard2Var
  -- `hB0`: `B → 0`.
  have hB0 : Tendsto B atTop (𝓝 0) := hdenom_atTop.const_div_atTop (4 * c1 * c2)
  -- `card n * B n ^ 3 = (4 c1 c2)^3 / (card n ^ 2 * σ n ^ 3)`.
  have hNB3eq : ∀ n, card n * B n ^ 3
      = (4 * c1 * c2) ^ 3 / (card n ^ 2 * σ n ^ 3) := by
    intro n
    by_cases hd : card n * σ n = 0
    · -- degenerate: `card = 0` or `σ = 0`, both sides vanish.
      rcases mul_eq_zero.mp hd with hc0 | hs0
      · simp [hBdef, hc0]
      · simp [hBdef, hs0]
    · rw [hBdef]
      field_simp
  -- `card n ^ 2 * σ n ^ 3 = (√(card n * Var n)) ^ 3 * √(card n)`.
  have hpow_sqrt : ∀ n, card n ^ 2 * σ n ^ 3
      = (Real.sqrt (card n * Var n)) ^ 3 * Real.sqrt (card n) := by
    intro n
    rw [hσdef]
    rw [Real.sqrt_mul (hcard_nonneg n)]
    have hcs : Real.sqrt (card n) ^ 2 = card n := Real.sq_sqrt (hcard_nonneg n)
    rw [mul_pow]
    ring_nf
    rw [show Real.sqrt (card n) ^ 4 = (Real.sqrt (card n) ^ 2) ^ 2 by ring, hcs]
    ring
  -- `card n ^ 2 * σ n ^ 3 → atTop`.
  have hpow_atTop : Tendsto (fun n => card n ^ 2 * σ n ^ 3) atTop atTop := by
    have heq : (fun n => card n ^ 2 * σ n ^ 3)
        = fun n => (Real.sqrt (card n * Var n)) ^ 3 * Real.sqrt (card n) := funext hpow_sqrt
    rw [heq]
    have hsqrtcardVar : Tendsto (fun n => Real.sqrt (card n * Var n)) atTop
        (𝓝 (Real.sqrt cVar)) := (Real.continuous_sqrt.tendsto cVar).comp hCond4
    have hcube : Tendsto (fun n => (Real.sqrt (card n * Var n)) ^ 3) atTop
        (𝓝 ((Real.sqrt cVar) ^ 3)) := hsqrtcardVar.pow 3
    have hcubepos : 0 < (Real.sqrt cVar) ^ 3 := by positivity
    have hsqrtcard : Tendsto (fun n => Real.sqrt (card n)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp hN
    exact hcube.pos_mul_atTop hcubepos hsqrtcard
  -- `hNB3`: `card · B³ → 0`.
  have hNB3 : Tendsto (fun n => card n * B n ^ 3) atTop (𝓝 0) := by
    have heq : (fun n => card n * B n ^ 3)
        = fun n => (4 * c1 * c2) ^ 3 / (card n ^ 2 * σ n ^ 3) := funext hNB3eq
    rw [heq]
    exact hpow_atTop.const_div_atTop ((4 * c1 * c2) ^ 3)
  -- Assemble.
  exact localDependenceCLT_of_conditions Exp dk dl Dg m hdeg hVar hposk hposl B hB hbound hB0 hNB3

end ExposureMappingInterference
end Experimentation
end Causalean
