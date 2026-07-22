/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Stat.Coupling.ProductLossMonotoneCoupling.PIT

/-!
# Couplings and the explicit monotone couplings

A **coupling** of two real probability measures `μ, ν` is a probability measure
`π` on `ℝ × ℝ` whose two marginals are `μ` and `ν`. This file:

* defines `IsCoupling π μ ν` (probability measure with `π.map Prod.fst = μ`,
  `π.map Prod.snd = ν`), the Fréchet class `Π(μ,ν)`;
* defines the two extremal couplings built from the quantile transform:
  * `comonotoneCoupling μ ν` — pushforward of `Unif(0,1)` under
    `u ↦ (quantile μ u, quantile ν u)` (the *comonotone* / quantile coupling);
  * `countermonotoneCoupling μ ν` — pushforward under
    `u ↦ (quantile μ u, quantile ν (1 - u))` (the *countermonotone* coupling);
* proves each is genuinely a coupling of `(μ, ν)` (marginals via the PIT
  `quantile_map_uniform`, plus that `u ↦ 1 - u` preserves `Unif(0,1)`).

These are the optimizers whose optimality is established downstream.
-/

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Set
open Causalean.Stat

/-- `IsCoupling π μ ν` states that `π` is a coupling of `μ` and `ν`: it is a
probability measure on `ℝ × ℝ` whose first marginal is `μ` and whose second
marginal is `ν`. This is membership in the Fréchet class `Π(μ, ν)`. -/
structure IsCoupling (π : Measure (ℝ × ℝ)) (μ ν : Measure ℝ) : Prop where
  /-- A coupling is a probability measure. -/
  isProbabilityMeasure : IsProbabilityMeasure π
  /-- The first marginal of `π` is `μ`. -/
  map_fst : π.map Prod.fst = μ
  /-- The second marginal of `π` is `ν`. -/
  map_snd : π.map Prod.snd = ν

/-- The **comonotone (quantile) coupling** of `μ` and `ν`: the pushforward of
the uniform measure on `(0,1)` under `u ↦ (quantile μ u, quantile ν u)`. Both
coordinates are driven by the *same* uniform draw, giving the maximal positive
dependence within `Π(μ, ν)`. -/
noncomputable def comonotoneCoupling (μ ν : Measure ℝ) : Measure (ℝ × ℝ) :=
  unifOI.map (fun u => (quantile μ u, quantile ν u))

/-- The **countermonotone coupling** of `μ` and `ν`: the pushforward of the
uniform measure on `(0,1)` under `u ↦ (quantile μ u, quantile ν (1 - u))`. The
reflection `u ↦ 1 - u` on the second coordinate produces the maximal negative
dependence within `Π(μ, ν)`. -/
noncomputable def countermonotoneCoupling (μ ν : Measure ℝ) : Measure (ℝ × ℝ) :=
  unifOI.map (fun u => (quantile μ u, quantile ν (1 - u)))

/-- The reflection `u ↦ 1 - u` preserves the uniform measure on `(0,1)`:
`unifOI.map (fun u => 1 - u) = unifOI`. -/
lemma map_one_sub_unifOI : unifOI.map (fun u : ℝ => 1 - u) = unifOI := by
  let f : ℝ → ℝ := fun u => 1 - u
  have hf : Measurable f := measurable_const.sub measurable_id
  have hvol : Measure.map f (volume : Measure ℝ) = volume := by
    have hneg : Measure.map (fun u : ℝ => (-1 : ℝ) * u) (volume : Measure ℝ) = volume := by
      simpa using (Real.map_volume_mul_left (a := (-1 : ℝ)) (by norm_num))
    have hadd : Measure.map (fun u : ℝ => (1 : ℝ) + u) (volume : Measure ℝ) = volume :=
      (measurePreserving_add_left (volume : Measure ℝ) (1 : ℝ)).map_eq
    calc
      Measure.map f (volume : Measure ℝ)
          = Measure.map (fun u : ℝ => (1 : ℝ) + u)
              (Measure.map (fun u : ℝ => (-1 : ℝ) * u) volume) := by
            rw [Measure.map_map]
            · congr 1
              funext u
              dsimp [f]
              ring
            · exact (measurable_const.add measurable_id)
            · exact (measurable_const.mul measurable_id)
      _ = volume := by rw [hneg, hadd]
  have hpre : f ⁻¹' Ioo (0 : ℝ) 1 = Ioo (0 : ℝ) 1 := by
    ext u
    simp [f]
  have hrestrict := Measure.restrict_map (μ := (volume : Measure ℝ)) (f := f) hf
      (s := Ioo (0 : ℝ) 1) measurableSet_Ioo
  simpa [unifOI, hvol, hpre] using hrestrict.symm

/-- The comonotone coupling **is** a coupling of `(μ, ν)`. Its marginals are
computed by `Measure.map_map` composing with `Prod.fst`/`Prod.snd`, which
reduces each to `unifOI.map (quantile ·)`, equal to the corresponding measure by
the probability integral transform `quantile_map_uniform`. -/
theorem isCoupling_comonotoneCoupling (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    IsCoupling (comonotoneCoupling μ ν) μ ν := by
  let hμ : AEMeasurable (quantile μ) unifOI := aemeasurable_quantile_unifOI μ
  let hν : AEMeasurable (quantile ν) unifOI := aemeasurable_quantile_unifOI ν
  refine ⟨?_, ?_, ?_⟩
  · unfold comonotoneCoupling
    exact Measure.isProbabilityMeasure_map (hμ.prodMk hν)
  · unfold comonotoneCoupling
    calc
      (unifOI.map (fun u => (quantile μ u, quantile ν u))).map Prod.fst
          = unifOI.map (Prod.fst ∘ fun u => (quantile μ u, quantile ν u)) := by
            rw [AEMeasurable.map_map_of_aemeasurable measurable_fst.aemeasurable
              (hμ.prodMk hν)]
      _ = μ := by
            simpa using (quantile_map_uniform μ)
  · unfold comonotoneCoupling
    calc
      (unifOI.map (fun u => (quantile μ u, quantile ν u))).map Prod.snd
          = unifOI.map (Prod.snd ∘ fun u => (quantile μ u, quantile ν u)) := by
            rw [AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable
              (hμ.prodMk hν)]
      _ = ν := by
            simpa using (quantile_map_uniform ν)

/-- The countermonotone coupling **is** a coupling of `(μ, ν)`. The first
marginal is `μ` by the PIT; the second marginal is `unifOI.map (quantile ν ∘
(1 - ·))`, which equals `ν` because `u ↦ 1 - u` preserves `unifOI`
(`map_one_sub_unifOI`) followed by the PIT for `ν`. -/
theorem isCoupling_countermonotoneCoupling (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    IsCoupling (countermonotoneCoupling μ ν) μ ν := by
  let r : ℝ → ℝ := fun u => 1 - u
  have hr : Measurable r := measurable_const.sub measurable_id
  let hμ : AEMeasurable (quantile μ) unifOI := aemeasurable_quantile_unifOI μ
  have hνmap : AEMeasurable (quantile ν) (unifOI.map r) := by
    simpa [r, map_one_sub_unifOI] using (aemeasurable_quantile_unifOI ν)
  let hνr : AEMeasurable (fun u : ℝ => quantile ν (1 - u)) unifOI := by
    simpa [r, Function.comp_def] using hνmap.comp_measurable hr
  refine ⟨?_, ?_, ?_⟩
  · unfold countermonotoneCoupling
    exact Measure.isProbabilityMeasure_map (hμ.prodMk hνr)
  · unfold countermonotoneCoupling
    calc
      (unifOI.map (fun u => (quantile μ u, quantile ν (1 - u)))).map Prod.fst
          = unifOI.map (Prod.fst ∘ fun u => (quantile μ u, quantile ν (1 - u))) := by
            rw [AEMeasurable.map_map_of_aemeasurable measurable_fst.aemeasurable
              (hμ.prodMk hνr)]
      _ = μ := by
            simpa using (quantile_map_uniform μ)
  · unfold countermonotoneCoupling
    calc
      (unifOI.map (fun u => (quantile μ u, quantile ν (1 - u)))).map Prod.snd
          = unifOI.map (Prod.snd ∘ fun u => (quantile μ u, quantile ν (1 - u))) := by
            rw [AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable
              (hμ.prodMk hνr)]
      _ = (unifOI.map r).map (quantile ν) := by
            rw [AEMeasurable.map_map_of_aemeasurable hνmap hr.aemeasurable]
            rfl
      _ = ν := by
            rw [map_one_sub_unifOI]
            exact quantile_map_uniform ν

end Causalean.Stat
