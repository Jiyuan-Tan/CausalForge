/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Mathlib.Probability.Kernel.Disintegration.CondCDF

/-!
# Measurable conditional quantile selection

This file constructs a measurable conditional quantile from Mathlib's regular conditional
CDF `condCDF ρ : α → StieltjesFunction ℝ`.  Given a measurable target level
`τ : α → ℝ` with `0 < τ a < 1`, the conditional quantile is the generalized inverse
`condQuantile ρ τ a = inf {x | τ a ≤ condCDF ρ a x}`.

The key measurability identity is
`{a | condQuantile ρ τ a ≤ t} = {a | τ a ≤ condCDF ρ a t}`, using monotonicity,
right-continuity, and the `atBot`/`atTop` limits of `condCDF`.  The theorem
`measurable_condQuantile_and_attains` proves that `condQuantile ρ τ` is measurable and,
when every conditional CDF is continuous, attains the requested level:
`condCDF ρ a (condQuantile ρ τ a) = τ a`.
-/

namespace Causalean.Mathlib

open MeasureTheory ProbabilityTheory Filter Topology

variable {α : Type*} [MeasurableSpace α]

/-- The **conditional quantile** at level `τ`: the generalized inverse of the conditional CDF,
`q(a) = inf { x : ℝ | τ(a) ≤ condCDF ρ a x }`. -/
noncomputable def condQuantile (ρ : Measure (α × ℝ)) (τ : α → ℝ) (a : α) : ℝ :=
  sInf {x : ℝ | τ a ≤ condCDF ρ a x}

private lemma condQuantileSet_up_closed {ρ : Measure (α × ℝ)} {τ : α → ℝ} {a : α}
    {x x' : ℝ} (hx : x ∈ {y : ℝ | τ a ≤ condCDF ρ a y}) (hxx' : x ≤ x') :
    x' ∈ {y : ℝ | τ a ≤ condCDF ρ a y} :=
  le_trans hx ((condCDF ρ a).mono hxx')

private lemma bddBelow_condQuantileSet {ρ : Measure (α × ℝ)} {τ : α → ℝ} {a : α}
    (hτ0 : 0 < τ a) : BddBelow {x : ℝ | τ a ≤ condCDF ρ a x} := by
  obtain ⟨N, hN⟩ :=
    Filter.eventually_atBot.mp ((tendsto_condCDF_atBot ρ a).eventually_lt_const hτ0)
  refine ⟨N, fun s hs => ?_⟩
  by_contra hlt
  push_neg at hlt
  exact absurd hs (not_le.mpr (hN s hlt.le))

private lemma nonempty_condQuantileSet {ρ : Measure (α × ℝ)} {τ : α → ℝ} {a : α}
    (hτ1 : τ a < 1) : ({x : ℝ | τ a ≤ condCDF ρ a x}).Nonempty := by
  obtain ⟨N, hN⟩ :=
    Filter.eventually_atTop.mp ((tendsto_condCDF_atTop ρ a).eventually_const_lt hτ1)
  exact ⟨N, (hN N le_rfl).le⟩

private lemma le_condCDF_condQuantile {ρ : Measure (α × ℝ)} {τ : α → ℝ} {a : α}
    (hτ1 : τ a < 1) : τ a ≤ condCDF ρ a (condQuantile ρ τ a) := by
  set q := condQuantile ρ τ a with hq
  have hne : ({x : ℝ | τ a ≤ condCDF ρ a x}).Nonempty := nonempty_condQuantileSet hτ1
  have hgt : ∀ x, q < x → τ a ≤ condCDF ρ a x := by
    intro x hx
    obtain ⟨s, hs, hsx⟩ := exists_lt_of_csInf_lt hne hx
    exact condQuantileSet_up_closed hs hsx.le
  have htends : Tendsto (condCDF ρ a) (𝓝[Set.Ioi q] q) (𝓝 (condCDF ρ a q)) :=
    ((condCDF ρ a).right_continuous q).mono_left
      (nhdsWithin_mono q Set.Ioi_subset_Ici_self)
  have hev : ∀ᶠ x in 𝓝[Set.Ioi q] q, τ a ≤ condCDF ρ a x := by
    filter_upwards [self_mem_nhdsWithin] with x hx using hgt x hx
  exact ge_of_tendsto htends hev

private lemma le_condCDF_of_condQuantile_le {ρ : Measure (α × ℝ)} {τ : α → ℝ}
    {a : α} {x : ℝ} (hτ1 : τ a < 1) (hx : condQuantile ρ τ a ≤ x) :
    τ a ≤ condCDF ρ a x :=
  le_trans (le_condCDF_condQuantile (ρ := ρ) (τ := τ) (a := a) hτ1)
    ((condCDF ρ a).mono hx)

private lemma condQuantile_le_of_le_condCDF {ρ : Measure (α × ℝ)} {τ : α → ℝ}
    {a : α} {x : ℝ} (hτ0 : 0 < τ a) (hx : τ a ≤ condCDF ρ a x) :
    condQuantile ρ τ a ≤ x :=
  csInf_le (bddBelow_condQuantileSet (ρ := ρ) (τ := τ) (a := a) hτ0) hx

private lemma condQuantile_le_iff {ρ : Measure (α × ℝ)} {τ : α → ℝ} {a : α}
    {x : ℝ} (hτ0 : 0 < τ a) (hτ1 : τ a < 1) :
    condQuantile ρ τ a ≤ x ↔ τ a ≤ condCDF ρ a x :=
  ⟨le_condCDF_of_condQuantile_le (ρ := ρ) (τ := τ) (a := a) hτ1,
    condQuantile_le_of_le_condCDF (ρ := ρ) (τ := τ) (a := a) hτ0⟩

/-- **Measurable conditional quantile (selection).** For a finite measure `ρ` on `α × ℝ`
and a measurable target level `τ : α → ℝ` with `τ ∈ (0,1)`, if every conditional law
is atomless (`condCDF ρ a` continuous), the conditional quantile `condQuantile ρ τ` is
measurable and attains the level:
`condCDF ρ a (condQuantile ρ τ a) = τ a` for all `a`.

This is the conditional analogue of an unconditional generalized inverse, with measurability
of the selection in the conditioning variable. -/
theorem measurable_condQuantile_and_attains (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ]
    (τ : α → ℝ) (hτ : Measurable τ) (hτ0 : ∀ a, 0 < τ a) (hτ1 : ∀ a, τ a < 1)
    (hcont : ∀ a, Continuous (condCDF ρ a)) :
    Measurable (condQuantile ρ τ) ∧
      ∀ a, condCDF ρ a (condQuantile ρ τ a) = τ a := by
  constructor
  · refine measurable_of_Iic (α := ℝ) (fun t => ?_)
    have hset : (condQuantile ρ τ) ⁻¹' Set.Iic t = {a | τ a ≤ condCDF ρ a t} := by
      ext a
      exact condQuantile_le_iff (ρ := ρ) (τ := τ) (a := a) (x := t) (hτ0 a) (hτ1 a)
    rw [hset]
    exact measurableSet_le hτ (measurable_condCDF ρ t)
  · intro a
    have hge : τ a ≤ condCDF ρ a (condQuantile ρ τ a) :=
      le_condCDF_condQuantile (ρ := ρ) (τ := τ) (a := a) (hτ1 a)
    have hle : condCDF ρ a (condQuantile ρ τ a) ≤ τ a := by
      by_contra hnot
      have hlt : τ a < condCDF ρ a (condQuantile ρ τ a) := lt_of_not_ge hnot
      let q := condQuantile ρ τ a
      have hnear : ∀ᶠ y in 𝓝 q, τ a < condCDF ρ a y := by
        simpa [q] using ((hcont a).continuousAt.tendsto.eventually_const_lt hlt)
      obtain ⟨ε, hεpos, hε⟩ := Metric.eventually_nhds_iff.mp hnear
      let x := q - ε / 2
      have hxlt : x < q := sub_lt_self q (half_pos hεpos)
      have hdist : dist x q < ε := by
        rw [Real.dist_eq]
        have hhalf_pos : 0 < ε / 2 := half_pos hεpos
        have hcalc : x - q = -(ε / 2) := by simp [x]
        rw [hcalc, abs_neg, abs_of_pos hhalf_pos]
        linarith
      have hxS : τ a ≤ condCDF ρ a x := (hε hdist).le
      have hq_le_x : q ≤ x := by
        change condQuantile ρ τ a ≤ x
        exact condQuantile_le_of_le_condCDF (ρ := ρ) (τ := τ) (a := a) (hτ0 a) hxS
      exact not_lt_of_ge hq_le_x hxlt
    exact le_antisymm hle hge

end Causalean.Mathlib
