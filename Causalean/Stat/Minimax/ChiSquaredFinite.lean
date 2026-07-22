/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Finite and product specializations of the χ²-divergence

Three foundational measure-theory lemmas supporting the finite/discrete χ²-route to
minimax lower bounds:

* `rnDeriv_mul_measure_singleton` — the discrete Radon–Nikodym bridge: on a measurable
  singleton, `ν {x} · (dμ/dν)(x) = μ {x}` whenever `μ ≪ ν`. This fills a genuine
  Mathlib gap (the pointwise inversion of the density on atoms).
* `finite_one_add_chiSqDiv` — on a finite sample space, `1 + χ²(μ‖ν)` is the explicit
  sum `∑ₓ (μ{x})² / (ν{x})` of squared point-mass ratios.
* `pi_real_singleton` — the real-valued product point mass: under `Measure.pi`, the
  mass of a single point factorizes as `∏ᵢ (μ i){ωᵢ}`.
-/

import Causalean.Stat.Minimax.ChiSquared
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Real

/-! # Finite Chi-Squared Identities

This file proves discrete and product-measure identities for chi-squared
divergence on finite sample spaces. These identities turn Radon-Nikodym formulas
into point-mass sums and product point masses for finite minimax constructions. -/

namespace Causalean.Stat

open MeasureTheory
open scoped ENNReal BigOperators

/-- **Discrete Radon–Nikodym bridge.** On a measurable singleton `{x}`, the
Radon–Nikodym density scaled by the base mass recovers the numerator mass:
`ν {x} · (dμ/dν)(x) = μ {x}`, for `μ ≪ ν`. Proved by integrating the density over
`{x}` (via `setLIntegral_rnDeriv`) and collapsing the singleton integral with
`restrict_singleton`/`lintegral_dirac'`. -/
theorem rnDeriv_mul_measure_singleton {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (μ ν : Measure Ω) [SFinite ν]
    [μ.HaveLebesgueDecomposition ν] (hac : μ ≪ ν) (x : Ω) :
    ν {x} * μ.rnDeriv ν x = μ {x} := by
  have h1 : μ {x} = ∫⁻ y in {x}, μ.rnDeriv ν y ∂ν :=
    (Measure.setLIntegral_rnDeriv hac {x}).symm
  have h2 : ∫⁻ y in {x}, μ.rnDeriv ν y ∂ν = ν {x} * μ.rnDeriv ν x := by
    rw [Measure.restrict_singleton, lintegral_smul_measure,
      lintegral_dirac' x (Measure.measurable_rnDeriv μ ν), smul_eq_mul]
  rw [h1, h2]

/-- **Finite χ²-divergence formula.** On a finite sample space, for probability
measures `μ ≪ ν`, the (shifted) χ²-divergence is the explicit sum of squared point-mass
ratios `1 + χ²(μ‖ν) = ∑ₓ (μ{x})² / (ν{x})`. Combines `chiSqDiv_eq`, the finite
integral formula `integral_fintype`, and the discrete RN bridge above. -/
theorem finite_one_add_chiSqDiv {Ω : Type*} [MeasurableSpace Ω] [Fintype Ω]
    [MeasurableSingletonClass Ω] (μ ν : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hac : μ ≪ ν) :
    1 + chiSqDiv μ ν = ∑ x, (μ.real {x}) ^ 2 / (ν.real {x}) := by
  have hexp : 1 + chiSqDiv μ ν = ∫ x, ((μ.rnDeriv ν x).toReal) ^ 2 ∂ν := by
    rw [chiSqDiv_eq hac (Integrable.of_finite)]; ring
  rw [hexp, integral_fintype _ (Integrable.of_finite)]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : ν {x} = 0
  · -- `ν {x} = 0` forces `μ {x} = 0` (absolute continuity); both sides vanish.
    have hνr : ν.real {x} = 0 := by rw [measureReal_def, h, ENNReal.toReal_zero]
    have hμr : μ.real {x} = 0 := by rw [measureReal_def, hac h, ENNReal.toReal_zero]
    rw [hνr, hμr]; simp
  · have hνtop : ν {x} ≠ ⊤ := measure_ne_top ν {x}
    have hνr0 : ν.real {x} ≠ 0 := by
      rw [measureReal_def]; exact ENNReal.toReal_ne_zero.2 ⟨h, hνtop⟩
    -- Invert the density on the atom `{x}` via the discrete RN bridge.
    have hrn : (μ.rnDeriv ν x).toReal = μ.real {x} / ν.real {x} := by
      have hc := congrArg ENNReal.toReal (rnDeriv_mul_measure_singleton μ ν hac x)
      rw [ENNReal.toReal_mul, ← measureReal_def, ← measureReal_def] at hc
      rw [eq_div_iff hνr0, mul_comm, hc]
    rw [hrn, smul_eq_mul]
    field_simp

/-- **Real-valued product point mass.** Under the product measure `Measure.pi μ` of a
family of probability measures, the mass of a single point factorizes as the product of
the marginal point masses: `(Measure.pi μ).real {ω} = ∏ᵢ (μ i).real {ωᵢ}`. Rewrites the
singleton as `Set.univ.pi (fun i => {ωᵢ})`, applies `Measure.pi_pi`, then distributes
`toReal` over the finite product. -/
theorem pi_real_singleton {ι : Type*} [Fintype ι] {Ω : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] [∀ i, MeasurableSingletonClass (Ω i)]
    (μ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)] (ω : ∀ i, Ω i) :
    (Measure.pi μ).real {ω} = ∏ i, (μ i).real {ω i} := by
  have hset : ({ω} : Set (∀ i, Ω i)) = Set.univ.pi (fun i => {ω i}) := by
    ext f
    simp [Set.mem_pi, funext_iff]
  rw [measureReal_def, hset, Measure.pi_pi, ENNReal.toReal_prod]
  simp only [measureReal_def]

end Causalean.Stat
