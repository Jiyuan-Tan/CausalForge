/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Scheffé's identity for total variation distance

For probability measures `μ ≪ ν` with Radon–Nikodym density `p = dμ/dν`, the
total variation distance is controlled by the `L¹(ν)` distance of the density to
`1`:

  `tvDist μ ν ≤ (1/2) * ∫ x, |(μ.rnDeriv ν x).toReal − 1| ∂ν`.

This is the `≤` direction of Scheffé's theorem.  It is the workhorse consumed by
the minimax lower-bound layer: the χ²-divergence route applies Cauchy–Schwarz to
get `TV ≤ ½√χ²`, and Pinsker's inequality applies the scalar bound
`klFun_lower_bound` to the same integral.

Main results (under `[IsProbabilityMeasure μ] [IsProbabilityMeasure ν]`,
`hac : μ ≪ ν`):

* `measureReal_sub_eq_setIntegral_rnDeriv_sub_one` — the signed gap
  `μ.real A − ν.real A` equals `∫ x in A, (p x − 1) ∂ν`;
* `tvDist_le_half_integral_abs_rnDeriv` — **Scheffé's inequality** (the `≤`
  direction).

The helper `abs_setIntegral_le_half_integral_abs_of_integral_eq_zero` (any
integrable `f` with `∫ f = 0` satisfies `|∫_A f| ≤ ½∫|f|`) is project-agnostic
and a candidate for upstream contribution.
-/

import Causalean.Stat.Minimax.TotalVariation
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv

/-! # Scheffe Bound for Total Variation

This file proves the one-sided Scheffe inequality relating total variation
distance to the integral absolute deviation of a Radon-Nikodym density from one.
It supplies the analytic bridge used to convert density-based divergence bounds
into minimax testing bounds. -/

namespace Causalean.Stat

open MeasureTheory
open scoped ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ ν : Measure Ω}

/-- For an integrable function `f` whose integral vanishes, the integral over any
measurable set is bounded in absolute value by half the `L¹` norm of `f`.

Proof: `∫_A f + ∫_{Aᶜ} f = ∫ f = 0`, so `∫_A f = −∫_{Aᶜ} f`.  Bounding each piece
by the corresponding integral of `|f|` gives `2∫_A f ≤ ∫|f|` and `−2∫_A f ≤ ∫|f|`. -/
theorem abs_setIntegral_le_half_integral_abs_of_integral_eq_zero
    {f : Ω → ℝ} (hf : Integrable f ν) (hf0 : ∫ x, f x ∂ν = 0)
    {A : Set Ω} (hA : MeasurableSet A) :
    |∫ x in A, f x ∂ν| ≤ (1/2) * ∫ x, |f x| ∂ν := by
  have hfA : IntegrableOn f A ν := hf.integrableOn
  have hfAc : IntegrableOn f Aᶜ ν := hf.integrableOn
  -- `∫_A f + ∫_{Aᶜ} f = 0`
  have hsplit : ∫ x in A, f x ∂ν + ∫ x in Aᶜ, f x ∂ν = 0 := by
    rw [MeasureTheory.integral_add_compl hA hf, hf0]
  have hcompl : ∫ x in Aᶜ, f x ∂ν = -(∫ x in A, f x ∂ν) := by linarith
  -- `∫|f| = ∫_A |f| + ∫_{Aᶜ} |f|`
  have habs : Integrable (fun x => |f x|) ν := hf.abs
  have hsplitabs :
      ∫ x, |f x| ∂ν = (∫ x in A, |f x| ∂ν) + ∫ x in Aᶜ, |f x| ∂ν :=
    (MeasureTheory.integral_add_compl hA habs).symm
  -- bound each piece of `f` by `|f|`
  have hbA : ∫ x in A, f x ∂ν ≤ ∫ x in A, |f x| ∂ν :=
    integral_mono_ae hfA habs.integrableOn (Filter.Eventually.of_forall fun x => le_abs_self _)
  have hbAc : ∫ x in Aᶜ, f x ∂ν ≤ ∫ x in Aᶜ, |f x| ∂ν :=
    integral_mono_ae hfAc habs.integrableOn (Filter.Eventually.of_forall fun x => le_abs_self _)
  have hbAneg : -(∫ x in A, f x ∂ν) ≤ ∫ x in A, |f x| ∂ν := by
    have : ∫ x in A, (-f x) ∂ν ≤ ∫ x in A, |f x| ∂ν :=
      integral_mono_ae hfA.neg habs.integrableOn
        (Filter.Eventually.of_forall fun x => (neg_le_abs _))
    rwa [integral_neg] at this
  have hbAcneg : -(∫ x in Aᶜ, f x ∂ν) ≤ ∫ x in Aᶜ, |f x| ∂ν := by
    have : ∫ x in Aᶜ, (-f x) ∂ν ≤ ∫ x in Aᶜ, |f x| ∂ν :=
      integral_mono_ae hfAc.neg habs.integrableOn
        (Filter.Eventually.of_forall fun x => (neg_le_abs _))
    rwa [integral_neg] at this
  rw [abs_le, hsplitabs]
  constructor
  · -- `-(½(∫_A|f| + ∫_{Aᶜ}|f|)) ≤ ∫_A f`
    nlinarith [hbAneg, hbAc, hcompl]
  · -- `∫_A f ≤ ½(∫_A|f| + ∫_{Aᶜ}|f|)`
    nlinarith [hbA, hbAcneg, hcompl]

variable [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- With density `p = dμ/dν` and `μ ≪ ν`, the signed gap `μ.real A − ν.real A`
equals `∫ x in A, (p x − 1) ∂ν`. -/
theorem measureReal_sub_eq_setIntegral_rnDeriv_sub_one (hac : μ ≪ ν)
    {A : Set Ω} (_hA : MeasurableSet A) :
    μ.real A - ν.real A
      = ∫ x in A, ((μ.rnDeriv ν x).toReal - 1) ∂ν := by
  have hp : ∫ x in A, (μ.rnDeriv ν x).toReal ∂ν = μ.real A :=
    Measure.setIntegral_toReal_rnDeriv hac A
  have hint : IntegrableOn (fun x => (μ.rnDeriv ν x).toReal) A ν :=
    (Measure.integrable_toReal_rnDeriv).integrableOn
  have hc : IntegrableOn (fun _ : Ω => (1:ℝ)) A ν := (integrable_const 1).integrableOn
  have h1 : ∫ _ in A, (1:ℝ) ∂ν = ν.real A := by
    rw [setIntegral_const, smul_eq_mul, mul_one, measureReal_def]
  rw [integral_sub hint hc, hp, h1]

/-- **Scheffé's inequality (≤ direction).**  For probability measures `μ ≪ ν`,
the total variation distance is at most half the `L¹(ν)` distance of the
Radon–Nikodym density to `1`. -/
theorem tvDist_le_half_integral_abs_rnDeriv (μ ν : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hac : μ ≪ ν) :
    tvDist μ ν ≤ (1/2) * ∫ x, |(μ.rnDeriv ν x).toReal - 1| ∂ν := by
  set f : Ω → ℝ := fun x => (μ.rnDeriv ν x).toReal - 1 with hf_def
  have hint_p : Integrable (fun x => (μ.rnDeriv ν x).toReal) ν :=
    Measure.integrable_toReal_rnDeriv
  have hf : Integrable f ν := hint_p.sub (integrable_const 1)
  -- `∫ f = μ.real univ − ν.real univ = 0`
  have hf0 : ∫ x, f x ∂ν = 0 := by
    rw [hf_def]
    rw [integral_sub hint_p (integrable_const 1)]
    rw [Measure.integral_toReal_rnDeriv hac]
    simp only [integral_const, smul_eq_mul, mul_one]
    rw [measureReal_def]
    simp [measure_univ]
  -- supremum is over measurable sets; bound each term
  refine ciSup_le fun A => ?_
  obtain ⟨A, hA⟩ := A
  have hgap : μ.real A - ν.real A = ∫ x in A, f x ∂ν :=
    measureReal_sub_eq_setIntegral_rnDeriv_sub_one hac hA
  rw [hgap]
  exact abs_setIntegral_le_half_integral_abs_of_integral_eq_zero hf hf0 hA

end Causalean.Stat
