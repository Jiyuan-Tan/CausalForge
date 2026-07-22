/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# χ²-divergence and the Cauchy–Schwarz link to total variation

For measures `μ ≪ ν` with Radon–Nikodym density `p = dμ/dν`, this file uses the
finite real χ² functional

  `chiSqDiv μ ν = ∫ x, (p x − 1)² ∂ν`.

Applying Cauchy–Schwarz (Hölder with `p = q = 2`) to Scheffé's `L¹` bound
`tvDist μ ν ≤ ½ ∫ |p − 1| ∂ν` turns the `L¹` distance into the `L²` distance:

  `tvDist μ ν ≤ ½ √(chiSqDiv μ ν)`,

since `ν` is a probability measure (`∫ 1² ∂ν = 1`).  This is the χ²-route input to
the minimax lower-bound layer (an alternative to Pinsker's inequality).

Main results:

* `chiSqDiv_nonneg` — the χ²-divergence is nonnegative;
* `tvDist_le_half_sqrt_chiSqDiv` — **the headline** `TV ≤ ½√χ²`;
* `chiSqDiv_eq` — the expansion `χ² = ∫ p² ∂ν − 1` under `μ ≪ ν`.
-/

import Causalean.Stat.Minimax.Scheffe
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Constructions.Pi

/-! # Chi-squared divergence

This module defines the real chi-squared divergence `chiSqDiv` from the squared
deviation of the Radon-Nikodym density and proves its main minimax testing
interfaces.  The base results include `chiSqDiv_nonneg`,
`tvDist_le_half_sqrt_chiSqDiv`, and `chiSqDiv_eq`; the tensorization layer gives
`chiSqDiv_prod`, `one_add_chiSqDiv_pi_iid`,
`one_add_chiSqDiv_pi_iid_general`, and `chiSqDiv_prod_ancillary`; and the
testing layer culminates in `testing_error_lower_of_chi` and
`le_cam_two_point_chisq`.
-/

namespace Causalean.Stat

open MeasureTheory
open scoped ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ ν : Measure Ω}

/-- The finite real χ² functional `∫ (dμ/dν − 1)² dν` of `μ` relative to `ν`. -/
noncomputable def chiSqDiv (μ ν : Measure Ω) : ℝ :=
  ∫ x, ((μ.rnDeriv ν x).toReal - 1) ^ 2 ∂ν

/-- The χ²-divergence is nonnegative: its integrand is a square. -/
theorem chiSqDiv_nonneg : 0 ≤ chiSqDiv μ ν :=
  integral_nonneg fun _ => sq_nonneg _

/-- **Cauchy–Schwarz on Scheffé.** For probability measures `μ ≪ ν` whose squared
density deviation is integrable, the total variation distance is bounded by half
the square root of the χ²-divergence. -/
theorem tvDist_le_half_sqrt_chiSqDiv (μ ν : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hac : μ ≪ ν)
    (hint : Integrable (fun x => ((μ.rnDeriv ν x).toReal - 1) ^ 2) ν) :
    tvDist μ ν ≤ (1/2) * Real.sqrt (chiSqDiv μ ν) := by
  -- Density deviation `f = p − 1`.
  set f : Ω → ℝ := fun x => (μ.rnDeriv ν x).toReal - 1 with hf_def
  have hmeas : AEStronglyMeasurable f ν :=
    (Measure.measurable_rnDeriv μ ν).ennreal_toReal.aestronglyMeasurable.sub
      aestronglyMeasurable_const
  -- `f ∈ L²(ν)` since `f²` is integrable.
  have hfL2 : MemLp f 2 ν := (memLp_two_iff_integrable_sq hmeas).2 hint
  -- `|f| ∈ L²(ν)` (same norm) and `1 ∈ L²(ν)` (`ν` probability).
  have habsL2 : MemLp (fun x => |f x|) (ENNReal.ofReal 2) ν := by
    have h := hfL2.norm
    simp only [Real.norm_eq_abs] at h
    simpa using h
  have honeL2 : MemLp (fun _ : Ω => (1:ℝ)) (ENNReal.ofReal 2) ν := by
    simpa using (memLp_const (1:ℝ) : MemLp (fun _ : Ω => (1:ℝ)) 2 ν)
  -- Hölder with `p = q = 2`: `∫ |f|·1 ≤ (∫ |f|²)^½ · (∫ 1²)^½`.
  have hholder :
      ∫ x, |f x| * (1:ℝ) ∂ν
        ≤ (∫ x, |f x| ^ (2:ℝ) ∂ν) ^ (1 / (2:ℝ))
          * (∫ x, (1:ℝ) ^ (2:ℝ) ∂ν) ^ (1 / (2:ℝ)) :=
    integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
      (Filter.Eventually.of_forall fun x => abs_nonneg _)
      (Filter.Eventually.of_forall fun _ => zero_le_one) habsL2 honeL2
  -- Simplify the right-hand factors.
  have hone : (∫ x, (1:ℝ) ^ (2:ℝ) ∂ν) ^ (1 / (2:ℝ)) = 1 := by
    simp
  have hLHS : ∫ x, |f x| * (1:ℝ) ∂ν = ∫ x, |f x| ∂ν := by simp
  -- `∫ |f|² = chiSqDiv μ ν` (rewrite real power 2 to `^2`).
  have hsq : ∫ x, |f x| ^ (2:ℝ) ∂ν = chiSqDiv μ ν := by
    rw [chiSqDiv]
    apply integral_congr_ae
    refine Filter.Eventually.of_forall fun x => ?_
    change |f x| ^ (2:ℝ) = (f x) ^ 2
    rw [Real.rpow_two, sq_abs]
  -- `∫ |f| ≤ √(chiSqDiv μ ν)`.
  have hint_abs : ∫ x, |f x| ∂ν ≤ Real.sqrt (chiSqDiv μ ν) := by
    rw [hLHS, hsq, hone, mul_one] at hholder
    have hrw : (chiSqDiv μ ν) ^ (1 / (2:ℝ)) = Real.sqrt (chiSqDiv μ ν) :=
      (Real.sqrt_eq_rpow (chiSqDiv μ ν)).symm
    rwa [hrw] at hholder
  -- Combine with Scheffé.
  have hscheffe := tvDist_le_half_integral_abs_rnDeriv μ ν hac
  calc tvDist μ ν ≤ (1/2) * ∫ x, |f x| ∂ν := hscheffe
    _ ≤ (1/2) * Real.sqrt (chiSqDiv μ ν) := by
        apply mul_le_mul_of_nonneg_left hint_abs (by norm_num)

/-- Expansion of the χ²-divergence: `χ²(μ‖ν) = ∫ (dμ/dν)² ∂ν − 1` when `μ ≪ ν`. -/
theorem chiSqDiv_eq [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hac : μ ≪ ν)
    (hint : Integrable (fun x => ((μ.rnDeriv ν x).toReal - 1) ^ 2) ν) :
    chiSqDiv μ ν = (∫ x, ((μ.rnDeriv ν x).toReal) ^ 2 ∂ν) - 1 := by
  set p : Ω → ℝ := fun x => (μ.rnDeriv ν x).toReal with hp_def
  have hmeas : AEStronglyMeasurable p ν :=
    (Measure.measurable_rnDeriv μ ν).ennreal_toReal.aestronglyMeasurable
  have hp_int : Integrable p ν := Measure.integrable_toReal_rnDeriv
  -- `p²` integrable, since `(p − 1)²` is and `p² = (p−1)² + 2p − 1`.
  have hp_sq : Integrable (fun x => p x ^ 2) ν := by
    have hexp : (fun x => p x ^ 2)
        = fun x => (p x - 1) ^ 2 + (2 * p x - 1) := by
      funext x; ring
    rw [hexp]
    exact hint.add ((hp_int.const_mul 2).sub (integrable_const 1))
  -- Expand `(p − 1)² = p² − 2p + 1` under the integral.
  have h2p : Integrable (fun x => 2 * p x) ν := hp_int.const_mul 2
  have hsub : ∫ x, (p x ^ 2 - 2 * p x) ∂ν
      = (∫ x, p x ^ 2 ∂ν) - 2 * (∫ x, p x ∂ν) := by
    rw [integral_sub hp_sq h2p, integral_const_mul]
  have hadd : ∫ x, ((p x ^ 2 - 2 * p x) + 1) ∂ν
      = (∫ x, (p x ^ 2 - 2 * p x) ∂ν) + (∫ _ : Ω, (1:ℝ) ∂ν) :=
    integral_add (hp_sq.sub h2p) (integrable_const 1)
  have hexp : chiSqDiv μ ν
      = (∫ x, p x ^ 2 ∂ν) - 2 * (∫ x, p x ∂ν) + (∫ _ : Ω, (1:ℝ) ∂ν) := by
    have hcongr : ∀ x, ((μ.rnDeriv ν x).toReal - 1) ^ 2
        = (p x ^ 2 - 2 * p x) + 1 := by
      intro x; rw [hp_def]; ring
    rw [chiSqDiv, integral_congr_ae (Filter.Eventually.of_forall hcongr), hadd, hsub]
  -- `∫ p ∂ν = 1` and `∫ 1 ∂ν = 1`.
  have hp1 : ∫ x, p x ∂ν = 1 := by
    rw [hp_def, Measure.integral_toReal_rnDeriv hac]
    rw [measureReal_def, measure_univ]; simp
  have hone : (∫ _ : Ω, (1:ℝ) ∂ν) = 1 := by simp
  rw [hexp, hp1, hone]; ring

section Tensorization

variable {α : Type*} {mα : MeasurableSpace α} {β : Type*} {mβ : MeasurableSpace β}

/-- **Product density factorization.** For `μ₁ ≪ ν₁` and `μ₂ ≪ ν₂`, the Radon–Nikodym
density of the product is (a.e.) the product of the marginal densities. -/
theorem rnDeriv_prod_eq (μ₁ ν₁ : Measure α) (μ₂ ν₂ : Measure β)
    [SigmaFinite ν₁] [SigmaFinite ν₂] [SFinite ν₂]
    [μ₁.HaveLebesgueDecomposition ν₁] [μ₂.HaveLebesgueDecomposition ν₂]
    (h₁ : μ₁ ≪ ν₁) (h₂ : μ₂ ≪ ν₂) :
    (μ₁.prod μ₂).rnDeriv (ν₁.prod ν₂)
      =ᵐ[ν₁.prod ν₂]
        fun z => μ₁.rnDeriv ν₁ z.1 * μ₂.rnDeriv ν₂ z.2 := by
  -- Rewrite `μᵢ = νᵢ.withDensity (rnDeriv μᵢ νᵢ)` and use `prod_withDensity₀`.
  have hfac : μ₁.prod μ₂
      = (ν₁.prod ν₂).withDensity (fun z => μ₁.rnDeriv ν₁ z.1 * μ₂.rnDeriv ν₂ z.2) := by
    conv_lhs =>
      rw [← Measure.withDensity_rnDeriv_eq _ _ h₁, ← Measure.withDensity_rnDeriv_eq _ _ h₂]
    exact prod_withDensity₀ (Measure.measurable_rnDeriv _ _).aemeasurable
      (Measure.measurable_rnDeriv _ _).aemeasurable
  calc (μ₁.prod μ₂).rnDeriv (ν₁.prod ν₂)
      =ᵐ[ν₁.prod ν₂]
        ((ν₁.prod ν₂).withDensity
          (fun z => μ₁.rnDeriv ν₁ z.1 * μ₂.rnDeriv ν₂ z.2)).rnDeriv (ν₁.prod ν₂) := by
        rw [hfac]
    _ =ᵐ[ν₁.prod ν₂] fun z => μ₁.rnDeriv ν₁ z.1 * μ₂.rnDeriv ν₂ z.2 :=
        Measure.rnDeriv_withDensity₀ _
          (((Measure.measurable_rnDeriv _ _).comp measurable_fst).mul
            ((Measure.measurable_rnDeriv _ _).comp measurable_snd)).aemeasurable

/-- **Binary tensorization of the χ²-divergence.** For probability measures with
`μ₁ ≪ ν₁` and `μ₂ ≪ ν₂` and integrable squared density deviations, the χ²-divergence
tensorizes multiplicatively:
`1 + χ²(μ₁⊗μ₂ ‖ ν₁⊗ν₂) = (1 + χ²(μ₁‖ν₁))·(1 + χ²(μ₂‖ν₂))`. -/
theorem chiSqDiv_prod (μ₁ ν₁ : Measure α) (μ₂ ν₂ : Measure β)
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure ν₁]
    [IsProbabilityMeasure μ₂] [IsProbabilityMeasure ν₂]
    (h₁ : μ₁ ≪ ν₁) (h₂ : μ₂ ≪ ν₂)
    (hint₁ : Integrable (fun x => ((μ₁.rnDeriv ν₁ x).toReal - 1) ^ 2) ν₁)
    (hint₂ : Integrable (fun y => ((μ₂.rnDeriv ν₂ y).toReal - 1) ^ 2) ν₂) :
    1 + chiSqDiv (μ₁.prod μ₂) (ν₁.prod ν₂)
      = (1 + chiSqDiv μ₁ ν₁) * (1 + chiSqDiv μ₂ ν₂) := by
  -- Marginal densities (as ℝ) and their squares.
  set p₁ : α → ℝ := fun x => (μ₁.rnDeriv ν₁ x).toReal with hp₁_def
  set p₂ : β → ℝ := fun y => (μ₂.rnDeriv ν₂ y).toReal with hp₂_def
  -- `pᵢ` integrable; `pᵢ²` integrable (from `(pᵢ−1)²` integrable).
  have hp₁_int : Integrable p₁ ν₁ := Measure.integrable_toReal_rnDeriv
  have hp₂_int : Integrable p₂ ν₂ := Measure.integrable_toReal_rnDeriv
  have hp₁_sq : Integrable (fun x => p₁ x ^ 2) ν₁ := by
    have hexp : (fun x => p₁ x ^ 2) = fun x => (p₁ x - 1) ^ 2 + (2 * p₁ x - 1) := by
      funext x; ring
    rw [hexp]; exact hint₁.add ((hp₁_int.const_mul 2).sub (integrable_const 1))
  have hp₂_sq : Integrable (fun y => p₂ y ^ 2) ν₂ := by
    have hexp : (fun y => p₂ y ^ 2) = fun y => (p₂ y - 1) ^ 2 + (2 * p₂ y - 1) := by
      funext y; ring
    rw [hexp]; exact hint₂.add ((hp₂_int.const_mul 2).sub (integrable_const 1))
  -- Product squared density (as ℝ), a.e. equal to `p₁(z.1)²·p₂(z.2)²`.
  set P : α × β → ℝ := fun z => ((μ₁.prod μ₂).rnDeriv (ν₁.prod ν₂) z).toReal with hP_def
  have hdens : (μ₁.prod μ₂).rnDeriv (ν₁.prod ν₂)
      =ᵐ[ν₁.prod ν₂] fun z => μ₁.rnDeriv ν₁ z.1 * μ₂.rnDeriv ν₂ z.2 :=
    rnDeriv_prod_eq μ₁ ν₁ μ₂ ν₂ h₁ h₂
  have hPeq : (fun z => P z ^ 2)
      =ᵐ[ν₁.prod ν₂] fun z => (p₁ z.1 ^ 2) * (p₂ z.2 ^ 2) := by
    filter_upwards [hdens] with z hz
    rw [hP_def]
    simp only [hz, ENNReal.toReal_mul, hp₁_def, hp₂_def]
    ring
  -- Product of squared densities is integrable over the product measure.
  have hPint : Integrable (fun z => (p₁ z.1 ^ 2) * (p₂ z.2 ^ 2)) (ν₁.prod ν₂) :=
    Integrable.mul_prod hp₁_sq hp₂_sq
  have hPint' : Integrable (fun z => P z ^ 2) (ν₁.prod ν₂) :=
    hPint.congr hPeq.symm
  -- `(P−1)²` integrable over the product (needed for `chiSqDiv_eq`).
  have hP_int : Integrable P (ν₁.prod ν₂) := Measure.integrable_toReal_rnDeriv
  have hPdev : Integrable (fun z => (P z - 1) ^ 2) (ν₁.prod ν₂) := by
    have hexp : (fun z => (P z - 1) ^ 2)
        = fun z => P z ^ 2 + (-(2 * P z) + 1) := by
      funext z; ring
    rw [hexp]; exact hPint'.add (((hP_int.const_mul 2).neg).add (integrable_const 1))
  -- Apply the expansion `χ² = ∫ p² − 1` to all three.
  have hprod_ac : μ₁.prod μ₂ ≪ ν₁.prod ν₂ := h₁.prod h₂
  have e0 : chiSqDiv (μ₁.prod μ₂) (ν₁.prod ν₂)
      = (∫ z, P z ^ 2 ∂(ν₁.prod ν₂)) - 1 :=
    chiSqDiv_eq hprod_ac hPdev
  have e1 : chiSqDiv μ₁ ν₁ = (∫ x, p₁ x ^ 2 ∂ν₁) - 1 := chiSqDiv_eq h₁ hint₁
  have e2 : chiSqDiv μ₂ ν₂ = (∫ y, p₂ y ^ 2 ∂ν₂) - 1 := chiSqDiv_eq h₂ hint₂
  -- Fubini: `∫ P² = (∫ p₁²)·(∫ p₂²)`.
  have hfubini : (∫ z, P z ^ 2 ∂(ν₁.prod ν₂))
      = (∫ x, p₁ x ^ 2 ∂ν₁) * (∫ y, p₂ y ^ 2 ∂ν₂) := by
    rw [integral_congr_ae hPeq]
    exact integral_prod_mul (fun x => p₁ x ^ 2) (fun y => p₂ y ^ 2)
  rw [e0, e1, e2, hfubini]; ring

/-- **χ²-divergence is invariant under a measurable equivalence.** Pushing both
measures forward through `e : Ω ≃ᵐ Ω'` leaves the χ²-divergence unchanged. -/
theorem chiSqDiv_map_measurableEquiv {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (e : Ω ≃ᵐ Ω') (μ ν : Measure Ω) [SigmaFinite μ] [SigmaFinite ν] :
    chiSqDiv (μ.map e) (ν.map e) = chiSqDiv μ ν := by
  rw [chiSqDiv, chiSqDiv]
  rw [integral_map_equiv e (fun y => (((μ.map e).rnDeriv (ν.map e) y).toReal - 1) ^ 2)]
  apply integral_congr_ae
  have hrn := e.measurableEmbedding.rnDeriv_map μ ν
  filter_upwards [hrn] with x hx
  simp only [hx]

end Tensorization

/-- The χ²-divergence of a (sigma-finite) measure against itself is zero. -/
theorem chiSqDiv_self {Ω : Type*} [MeasurableSpace Ω] (ρ : Measure Ω) [SigmaFinite ρ] :
    chiSqDiv ρ ρ = 0 := by
  rw [chiSqDiv]
  rw [integral_eq_zero_of_ae]
  filter_upwards [ρ.rnDeriv_self] with x hx
  simp [hx]

/-- The `n`-fold product of `μ` is absolutely continuous w.r.t. that of `ν` whenever
`μ ≪ ν` (for sigma-finite factors). Proved by induction via the
`piFinSuccAbove` equivalence and the binary `AbsolutelyContinuous.prod`. -/
theorem pi_iid_absolutelyContinuous {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [SigmaFinite μ] [SigmaFinite ν] (hac : μ ≪ ν) (n : ℕ) :
    Measure.pi (fun _ : Fin n => μ) ≪ Measure.pi (fun _ : Fin n => ν) := by
  induction n with
  | zero =>
    rw [Measure.pi_of_empty (fun _ : Fin 0 => μ), Measure.pi_of_empty (fun _ : Fin 0 => ν)]
  | succ n ih =>
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Ω) 0 with he
    have hμ := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).map_eq
    have hν := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => ν) 0).map_eq
    have hprod : μ.prod (Measure.pi (fun _ : Fin n => μ))
        ≪ ν.prod (Measure.pi (fun _ : Fin n => ν)) := hac.prod ih
    have hmap : (Measure.pi (fun _ : Fin (n + 1) => μ)).map e
        ≪ (Measure.pi (fun _ : Fin (n + 1) => ν)).map e := by
      rw [hμ, hν]; exact hprod
    have hmapped := hmap.map (f := e.symm) e.symm.measurable
    rwa [Measure.map_map e.symm.measurable e.measurable,
      MeasurableEquiv.symm_comp_self, Measure.map_id,
      Measure.map_map e.symm.measurable e.measurable,
      MeasurableEquiv.symm_comp_self, Measure.map_id] at hmapped

set_option linter.unusedFintypeInType false in
/-- **`n`-fold i.i.d. tensorization of the χ²-divergence** on a finite sample space.
For probability measures `μ ≪ ν` on a finite `Ω`, the χ²-divergence of the `n`-fold
product satisfies `1 + χ²(μ^⊗n ‖ ν^⊗n) = (1 + χ²(μ‖ν))^n`.

The `[Fintype Ω]` hypothesis is kept deliberately: together with
`[MeasurableSingletonClass Ω]` it makes every integrability side-condition free
(via `Integrable.of_finite`), which is the whole point of the finite-sample form. -/
theorem one_add_chiSqDiv_pi_iid {Ω : Type*} [MeasurableSpace Ω] [Fintype Ω]
    [MeasurableSingletonClass Ω] (μ ν : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hac : μ ≪ ν) (n : ℕ) :
    1 + chiSqDiv (Measure.pi (fun _ : Fin n => μ)) (Measure.pi (fun _ : Fin n => ν))
      = (1 + chiSqDiv μ ν) ^ n := by
  induction n with
  | zero =>
    rw [Measure.pi_of_empty (fun _ : Fin 0 => μ),
      Measure.pi_of_empty (fun _ : Fin 0 => ν), chiSqDiv_self]
    simp
  | succ n ih =>
    have hμ := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).map_eq
    have hν := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => ν) 0).map_eq
    rw [← chiSqDiv_map_measurableEquiv
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Ω) 0), hμ, hν]
    have hac_pi : Measure.pi (fun _ : Fin n => μ) ≪ Measure.pi (fun _ : Fin n => ν) :=
      pi_iid_absolutelyContinuous μ ν hac n
    rw [chiSqDiv_prod μ ν (Measure.pi (fun _ : Fin n => μ)) (Measure.pi (fun _ : Fin n => ν))
        hac hac_pi
        (Integrable.of_finite) (Integrable.of_finite), ih, pow_succ]
    ring

/-- Integrability of the squared density deviation `(dμ/dν − 1)²` propagates from one
sample to the `n`-fold i.i.d. product `(d(μ^⊗n)/d(ν^⊗n) − 1)²`.  On a general (possibly
continuous) measurable space this is the side-condition that makes `chiSqDiv_prod`
applicable inside the tensorization induction — it is free on a finite space
(`Integrable.of_finite`) but must be derived here, by `L²(ν)`-tensorization of the
single-sample density `dμ/dν`. -/
theorem pi_iid_integrable_sq_dev {S : Type*} [MeasurableSpace S] (μ ν : Measure S)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hac : μ ≪ ν)
    (hint : Integrable (fun x => ((μ.rnDeriv ν x).toReal - 1) ^ 2) ν) (n : ℕ) :
    Integrable (fun x => (((Measure.pi (fun _ : Fin n => μ)).rnDeriv
        (Measure.pi (fun _ : Fin n => ν)) x).toReal - 1) ^ 2)
        (Measure.pi (fun _ : Fin n => ν)) := by
  induction n with
  | zero =>
    rw [Measure.pi_of_empty (fun _ : Fin 0 => μ),
      Measure.pi_of_empty (fun _ : Fin 0 => ν)]
    exact Integrable.of_finite
  | succ n ih =>
    set μπ : Measure (Fin n → S) := Measure.pi (fun _ : Fin n => μ) with hμπ_def
    set νπ : Measure (Fin n → S) := Measure.pi (fun _ : Fin n => ν) with hνπ_def
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => S) 0 with he
    set p : S → ℝ := fun x => (μ.rnDeriv ν x).toReal with hp_def
    set pn : (Fin n → S) → ℝ := fun y => (μπ.rnDeriv νπ y).toReal with hpn_def
    have hp_int : Integrable p ν := by
      simpa [hp_def] using (Measure.integrable_toReal_rnDeriv :
        Integrable (fun x => (μ.rnDeriv ν x).toReal) ν)
    have hpn_int : Integrable pn νπ := by
      simpa [hpn_def] using (Measure.integrable_toReal_rnDeriv :
        Integrable (fun y => (μπ.rnDeriv νπ y).toReal) νπ)
    have hp_sq : Integrable (fun x => p x ^ 2) ν := by
      have hdev : Integrable (fun x => (p x - 1) ^ 2) ν := by
        simpa [hp_def] using hint
      have hexp : (fun x => p x ^ 2) = fun x => (p x - 1) ^ 2 + (2 * p x - 1) := by
        funext x; ring
      rw [hexp]; exact hdev.add ((hp_int.const_mul 2).sub (integrable_const 1))
    have hpn_sq : Integrable (fun y => pn y ^ 2) νπ := by
      have hdev : Integrable (fun y => (pn y - 1) ^ 2) νπ := by
        simpa [hμπ_def, hνπ_def, hpn_def] using ih
      have hexp : (fun y => pn y ^ 2) = fun y => (pn y - 1) ^ 2 + (2 * pn y - 1) := by
        funext y; ring
      rw [hexp]; exact hdev.add ((hpn_int.const_mul 2).sub (integrable_const 1))
    have hac_pi : μπ ≪ νπ := by
      rw [hμπ_def, hνπ_def]
      exact pi_iid_absolutelyContinuous μ ν hac n
    set P : S × (Fin n → S) → ℝ :=
      fun z => ((μ.prod μπ).rnDeriv (ν.prod νπ) z).toReal with hP_def
    have hdens : (μ.prod μπ).rnDeriv (ν.prod νπ)
        =ᵐ[ν.prod νπ] fun z => μ.rnDeriv ν z.1 * μπ.rnDeriv νπ z.2 :=
      rnDeriv_prod_eq μ ν μπ νπ hac hac_pi
    have hPeq : (fun z => P z ^ 2)
        =ᵐ[ν.prod νπ] fun z => (p z.1 ^ 2) * (pn z.2 ^ 2) := by
      filter_upwards [hdens] with z hz
      rw [hP_def]
      simp only [hz, ENNReal.toReal_mul, hp_def, hpn_def]
      ring
    have hPint : Integrable (fun z => (p z.1 ^ 2) * (pn z.2 ^ 2)) (ν.prod νπ) :=
      Integrable.mul_prod hp_sq hpn_sq
    have hPint' : Integrable (fun z => P z ^ 2) (ν.prod νπ) :=
      hPint.congr hPeq.symm
    have hP_int : Integrable P (ν.prod νπ) := by
      simpa [hP_def] using (Measure.integrable_toReal_rnDeriv :
        Integrable (fun z => ((μ.prod μπ).rnDeriv (ν.prod νπ) z).toReal) (ν.prod νπ))
    have hprod_int : Integrable (fun z => (P z - 1) ^ 2) (ν.prod νπ) := by
      have hexp : (fun z => (P z - 1) ^ 2)
          = fun z => P z ^ 2 + (-(2 * P z) + 1) := by
        funext z; ring
      rw [hexp]; exact hPint'.add (((hP_int.const_mul 2).neg).add (integrable_const 1))
    have hμ_map := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).map_eq
    have hν_map := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => ν) 0).map_eq
    have hprod_map : Integrable (fun z => (P z - 1) ^ 2)
        (Measure.map e (Measure.pi (fun _ : Fin (n + 1) => ν))) := by
      rw [hν_map]
      simpa [hνπ_def] using hprod_int
    have hcomp : Integrable ((fun z => (P z - 1) ^ 2) ∘ e)
        (Measure.pi (fun _ : Fin (n + 1) => ν)) :=
      (integrable_map_equiv e (fun z => (P z - 1) ^ 2)).1 hprod_map
    refine hcomp.congr ?_
    have hrn := e.measurableEmbedding.rnDeriv_map
      (Measure.pi (fun _ : Fin (n + 1) => μ))
      (Measure.pi (fun _ : Fin (n + 1) => ν))
    filter_upwards [hrn] with x hx
    change (P (e x) - 1) ^ 2 =
      ((((Measure.pi (fun _ : Fin (n + 1) => μ)).rnDeriv
        (Measure.pi (fun _ : Fin (n + 1) => ν)) x).toReal - 1) ^ 2)
    rw [hP_def, ← hμ_map, ← hν_map, ← he]
    simp only [hx]

/-- **`n`-fold i.i.d. tensorization of the χ²-divergence on a GENERAL measurable space.**
For probability measures `μ ≪ ν` on any measurable space `S` whose single-sample squared
density deviation `(dμ/dν − 1)²` is `ν`-integrable, the χ²-divergence of the `n`-fold
i.i.d. product tensorizes multiplicatively:
`1 + χ²(μ^⊗n ‖ ν^⊗n) = (1 + χ²(μ‖ν))^n`.
This is the general-space analogue of `one_add_chiSqDiv_pi_iid` (whose `[Fintype S]`
hypothesis only serves to discharge integrability for free); the proof is the same
`chiSqDiv_prod` induction with the integrability side-conditions supplied by `hint` and
`pi_iid_integrable_sq_dev`.  It is the form needed by minimax two-point lower bounds whose
sample space is a continuum (e.g. a covariate space), where the finite-sample form does
not apply. -/
theorem one_add_chiSqDiv_pi_iid_general {S : Type*} [MeasurableSpace S] (μ ν : Measure S)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hac : μ ≪ ν)
    (hint : Integrable (fun x => ((μ.rnDeriv ν x).toReal - 1) ^ 2) ν) (n : ℕ) :
    1 + chiSqDiv (Measure.pi (fun _ : Fin n => μ)) (Measure.pi (fun _ : Fin n => ν))
      = (1 + chiSqDiv μ ν) ^ n := by
  induction n with
  | zero =>
    rw [Measure.pi_of_empty (fun _ : Fin 0 => μ),
      Measure.pi_of_empty (fun _ : Fin 0 => ν), chiSqDiv_self]
    simp
  | succ n ih =>
    have hμ := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).map_eq
    have hν := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => ν) 0).map_eq
    rw [← chiSqDiv_map_measurableEquiv
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => S) 0), hμ, hν]
    have hac_pi : Measure.pi (fun _ : Fin n => μ) ≪ Measure.pi (fun _ : Fin n => ν) :=
      pi_iid_absolutelyContinuous μ ν hac n
    rw [chiSqDiv_prod μ ν (Measure.pi (fun _ : Fin n => μ)) (Measure.pi (fun _ : Fin n => ν))
        hac hac_pi hint (pi_iid_integrable_sq_dev μ ν hac hint n), ih, pow_succ]
    ring

/-- **Ancillary product factor leaves the χ²-divergence unchanged.**  Tensoring both
measures with a *common* probability measure `ρ` (an ancillary coordinate, whose law is
the same under `μ` and `ν`) does not change the χ²-divergence:
`χ²(μ⊗ρ ‖ ν⊗ρ) = χ²(μ‖ν)`.  This is the formal content of "an ancillary observation
carries no information": its contribution is `1 + χ²(ρ‖ρ) = 1`.  It is the bridge from
the finite-cell lower bound to the continuous-covariate one (the within-cell position is
ancillary). -/
theorem chiSqDiv_prod_ancillary {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ ν : Measure α) (ρ : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ρ] (hac : μ ≪ ν)
    (hint : Integrable (fun x => ((μ.rnDeriv ν x).toReal - 1) ^ 2) ν) :
    chiSqDiv (μ.prod ρ) (ν.prod ρ) = chiSqDiv μ ν := by
  have hint₂ : Integrable (fun y => ((ρ.rnDeriv ρ y).toReal - 1) ^ 2) ρ := by
    refine (integrable_zero β ℝ ρ).congr ?_
    filter_upwards [ρ.rnDeriv_self] with y hy
    simp [hy]
  have h := chiSqDiv_prod μ ν ρ ρ hac (Measure.AbsolutelyContinuous.refl ρ) hint hint₂
  rw [chiSqDiv_self] at h
  simp only [add_zero, mul_one] at h
  linarith

/-- **Cauchy–Schwarz mass transfer under a χ²-budget.**  For probability measures `P ≪ Q`
whose squared density deviation `(dP/dQ − 1)²` is `Q`-integrable, and whose χ²-divergence is
at most `C`, the `P`-mass of any measurable set `A` is controlled by its `Q`-mass through
`P(A) ≤ √((C + 1)·Q(A))`.  This is the Cauchy–Schwarz step underlying the two-point testing
floor: a set that is small under the reference measure `Q` cannot be large under `P` when the
χ²-budget is finite. -/
lemma rnDeriv_setIntegral_le_sqrt_chi {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hac : P ≪ Q)
    (hint : Integrable (fun x => ((P.rnDeriv Q x).toReal - 1) ^ 2) Q)
    {C : ℝ} (hchi : chiSqDiv P Q ≤ C)
    {A : Set Ω} (hA : MeasurableSet A) :
    P.real A ≤ Real.sqrt ((C + 1) * Q.real A) := by
  set p : Ω → ℝ := fun x => (P.rnDeriv Q x).toReal with hp_def
  have hp_meas : AEStronglyMeasurable p Q :=
    (Measure.measurable_rnDeriv P Q).ennreal_toReal.aestronglyMeasurable
  have hp_int : Integrable p Q := by
    simpa [hp_def] using
      (Measure.integrable_toReal_rnDeriv :
        Integrable (fun x => (P.rnDeriv Q x).toReal) Q)
  have hdev : Integrable (fun x => (p x - 1) ^ 2) Q := by
    simpa [hp_def] using hint
  have hp_sq_int : Integrable (fun x => p x ^ 2) Q := by
    have hexp :
        (fun x => p x ^ 2) = fun x => (p x - 1) ^ 2 + (2 * p x - 1) := by
      funext x
      ring
    rw [hexp]
    exact hdev.add ((hp_int.const_mul 2).sub (integrable_const 1))
  have hp_sq_eq : ∫ x, p x ^ 2 ∂Q = chiSqDiv P Q + 1 := by
    have h := chiSqDiv_eq (μ := P) (ν := Q) hac hint
    simp only at h
    linarith
  have hp_sq_le : ∫ x, p x ^ 2 ∂Q ≤ C + 1 := by
    linarith
  let ind : Ω → ℝ := A.indicator (fun _ => (1 : ℝ))
  have hind_meas : AEStronglyMeasurable ind Q :=
    (measurable_const.indicator hA).aestronglyMeasurable
  have hind_sq_meas : AEStronglyMeasurable (fun x => ind x ^ 2) Q :=
    hind_meas.pow 2
  have hind_int_sq : Integrable (fun x => ind x ^ 2) Q := by
    refine Integrable.of_bound hind_sq_meas 1 ?_
    filter_upwards with x
    by_cases hx : x ∈ A <;> simp [ind, hx]
  have hind_L2 : MemLp ind (ENNReal.ofReal 2) Q := by
    simpa using (memLp_two_iff_integrable_sq hind_meas).2 hind_int_sq
  have hp_L2 : MemLp p (ENNReal.ofReal 2) Q := by
    simpa using (memLp_two_iff_integrable_sq hp_meas).2 hp_sq_int
  have hind_nonneg : ∀ᵐ x ∂Q, 0 ≤ ind x := by
    filter_upwards with x
    by_cases hx : x ∈ A <;> simp [ind, hx]
  have hp_nonneg : ∀ᵐ x ∂Q, 0 ≤ p x := by
    filter_upwards with x
    rw [hp_def]
    exact ENNReal.toReal_nonneg
  have hholder :
      ∫ x, ind x * p x ∂Q ≤
        (∫ x, ind x ^ (2 : ℝ) ∂Q) ^ (1 / (2 : ℝ)) *
          (∫ x, p x ^ (2 : ℝ) ∂Q) ^ (1 / (2 : ℝ)) := by
    exact integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
      hind_nonneg hp_nonneg hind_L2 hp_L2
  have hind_sq_eq : ∫ x, ind x ^ (2 : ℝ) ∂Q = Q.real A := by
    calc
      ∫ x, ind x ^ (2 : ℝ) ∂Q = ∫ x, ind x ∂Q := by
        apply integral_congr_ae
        filter_upwards with x
        by_cases hx : x ∈ A <;> simp [ind, hx]
      _ = Q.real A := by
        simpa [ind] using integral_indicator_one (μ := Q) hA
  have hp_sq_eq_rpow : ∫ x, p x ^ (2 : ℝ) ∂Q = ∫ x, p x ^ 2 ∂Q := by
    apply integral_congr_ae
    filter_upwards with x
    rw [Real.rpow_two]
  have hPA : P.real A = ∫ x, ind x * p x ∂Q := by
    rw [← Measure.setIntegral_toReal_rnDeriv hac A]
    rw [← integral_indicator hA]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ A <;> simp [ind, hx, hp_def]
  have hnonK : 0 ≤ C + 1 := by
    have hchi_non : 0 ≤ chiSqDiv P Q :=
      chiSqDiv_nonneg
    linarith
  rw [hPA]
  calc
    ∫ x, ind x * p x ∂Q
        ≤ (∫ x, ind x ^ (2 : ℝ) ∂Q) ^ (1 / (2 : ℝ)) *
          (∫ x, p x ^ (2 : ℝ) ∂Q) ^ (1 / (2 : ℝ)) := hholder
    _ = Real.sqrt (Q.real A) * Real.sqrt (∫ x, p x ^ 2 ∂Q) := by
      rw [hind_sq_eq, hp_sq_eq_rpow]
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    _ ≤ Real.sqrt (Q.real A) * Real.sqrt (C + 1) := by
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hp_sq_le) (Real.sqrt_nonneg _)
    _ = Real.sqrt ((C + 1) * Q.real A) := by
      rw [Real.sqrt_mul hnonK]
      ring

/-- **Two-point testing-error floor from a finite χ²-budget.**  For probability measures
`P ≪ Q` with `Q`-integrable squared density deviation and χ²-divergence at most `C ≥ 0`, every
measurable test region `A` incurs a combined error at least `1/(4(C + 1))`:
`P(Aᶜ) + Q(A) ≥ 1/(4(C + 1))`.  This is the positive two-point testing floor that powers
χ²-budget minimax lower bounds — no test can separate `P` from `Q` better than this when their
χ²-divergence is bounded. -/
lemma testing_error_lower_of_chi {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hac : P ≪ Q)
    (hint : Integrable (fun x => ((P.rnDeriv Q x).toReal - 1) ^ 2) Q)
    {C : ℝ} (hC : 0 ≤ C) (hchi : chiSqDiv P Q ≤ C)
    {A : Set Ω} (hA : MeasurableSet A) :
    P.real Aᶜ + Q.real A ≥ 1 / (4 * (C + 1)) := by
  let e : ℝ := P.real Aᶜ + Q.real A
  let K : ℝ := C + 1
  have hKpos : 0 < K := by
    dsimp [K]
    linarith
  have hKge1 : 1 ≤ K := by
    dsimp [K]
    linarith
  have hQ_nonneg : 0 ≤ Q.real A := measureReal_nonneg
  have hPcomp_nonneg : 0 ≤ P.real Aᶜ := measureReal_nonneg
  have hcs : P.real A ≤ Real.sqrt (K * Q.real A) := by
    simpa [K] using rnDeriv_setIntegral_le_sqrt_chi P Q hac hint hchi hA
  have hcomp : P.real Aᶜ = 1 - P.real A := by
    rw [measureReal_compl hA, probReal_univ]
  have hgap : 1 - e ≤ Real.sqrt (K * Q.real A) := by
    dsimp [e]
    rw [hcomp]
    linarith [hcs, hQ_nonneg]
  by_contra hnot
  have hlt : e < 1 / (4 * K) := by
    exact lt_of_not_ge (by simpa [e, K] using hnot)
  have hQ_le_e : Q.real A ≤ e := by
    dsimp [e]
    linarith
  have hQ_lt : Q.real A < 1 / (4 * K) := lt_of_le_of_lt hQ_le_e hlt
  have hKQ_lt : K * Q.real A < 1 / 4 := by
    calc
      K * Q.real A < K * (1 / (4 * K)) := mul_lt_mul_of_pos_left hQ_lt hKpos
      _ = 1 / 4 := by field_simp [hKpos.ne']
  have hsqrt_lt : Real.sqrt (K * Q.real A) < 1 / 2 := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1 / 2)]
    norm_num
    exact hKQ_lt
  have hc_le_quarter : 1 / (4 * K) ≤ 1 / 4 := by
    have hden : 0 < 4 * K := mul_pos (by norm_num) hKpos
    rw [one_div_le_one_div hden (by norm_num : (0 : ℝ) < 4)]
    nlinarith
  have he_lt_quarter : e < 1 / 4 := lt_of_lt_of_le hlt hc_le_quarter
  have hleft_gt : 1 / 2 < 1 - e := by
    linarith
  have hleft_lt : 1 - e < 1 / 2 := lt_of_le_of_lt hgap hsqrt_lt
  linarith

/-- **Le Cam two-point testing floor under a χ²-budget (uniform-constant form).**  Two
statements with the same structure.  (1) For every χ²-budget `C ≥ 0` there is a single floor
constant `c > 0` such that EVERY pair of probability laws `Pp ≪ Pm` (on any measurable space)
with `Q`-integrable squared density deviation and `χ²(Pp‖Pm) ≤ C` satisfies
`Pp(Aᶜ) + Pm(A) ≥ c` for every measurable test region `A`; the floor constant is quantified
above the laws, so it does not degrade as the least-favorable pair changes.  (2) The
per-observation route: for every per-observation budget `c0 ≥ 0` there is a single floor
`c' > 0` such that whenever the single-observation divergence obeys `χ²(Pp‖Pm) ≤ c0/m`, the
`m`-fold i.i.d. product experiment retains the SAME constant testing floor
`(Pp^{⊗m})(Aᶜ) + (Pm^{⊗m})(A) ≥ c'`, via the product χ²-identity
`1 + χ²(Pp^{⊗m}‖Pm^{⊗m}) = (1 + χ²)^m ≤ exp(c0)`.

This is exactly the form consumed by minimax two-point lower bounds whose least-favorable laws
change with the sample size: the uniform `c = c(C)` (resp. `c' = c'(c0)`) cannot degrade. -/
lemma le_cam_two_point_chisq :
    (∀ Cchi : ℝ, 0 ≤ Cchi →
      ∃ c : ℝ, 0 < c ∧
        ∀ {Ω : Type} [MeasurableSpace Ω]
          (Pp Pm : Measure Ω) [IsProbabilityMeasure Pp] [IsProbabilityMeasure Pm],
          Pp ≪ Pm →
            Integrable (fun x => ((Pp.rnDeriv Pm x).toReal - 1) ^ 2) Pm →
            chiSqDiv Pp Pm ≤ Cchi →
            ∀ A : Set Ω, MeasurableSet A → Pp.real Aᶜ + Pm.real A ≥ c) ∧
    (∀ c0 : ℝ, 0 ≤ c0 →
        ∃ c' : ℝ, 0 < c' ∧
          ∀ {Ω : Type} [MeasurableSpace Ω]
            (Pp Pm : Measure Ω) [IsProbabilityMeasure Pp] [IsProbabilityMeasure Pm],
            Pp ≪ Pm →
              Integrable (fun x => ((Pp.rnDeriv Pm x).toReal - 1) ^ 2) Pm →
              ∀ (m : ℕ), 0 < m →
                chiSqDiv Pp Pm ≤ c0 / (m : ℝ) →
                ∀ A : Set (Fin m → Ω), MeasurableSet A →
                  (Measure.pi (fun _ : Fin m => Pp)).real Aᶜ
                    + (Measure.pi (fun _ : Fin m => Pm)).real A ≥ c')
    := by
  constructor
  · intro Cchi hCchi
    refine ⟨1 / (4 * (Cchi + 1)), by positivity, ?_⟩
    intro Ω _ Pp Pm _ _ hac hint hchi A hA
    exact testing_error_lower_of_chi Pp Pm hac hint hCchi hchi hA
  · intro c0 hc0
    refine ⟨1 / (4 * Real.exp c0), by positivity, ?_⟩
    intro Ω _ Pp Pm _ _ hac hint m hm hchi A hA
    let Pprod : Measure (Fin m → Ω) := Measure.pi (fun _ : Fin m => Pp)
    let Qprod : Measure (Fin m → Ω) := Measure.pi (fun _ : Fin m => Pm)
    have hac_prod : Pprod ≪ Qprod := by
      dsimp [Pprod, Qprod]
      exact pi_iid_absolutelyContinuous Pp Pm hac m
    have hint_prod :
        Integrable (fun x => ((Pprod.rnDeriv Qprod x).toReal - 1) ^ 2) Qprod := by
      dsimp [Pprod, Qprod]
      exact pi_iid_integrable_sq_dev Pp Pm hac hint m
    have hchi_non : 0 ≤ chiSqDiv Pp Pm :=
      chiSqDiv_nonneg
    have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
    have hmul : (m : ℝ) * chiSqDiv Pp Pm ≤ c0 := by
      have := mul_le_mul_of_nonneg_left hchi (le_of_lt hmR)
      field_simp [hmR.ne'] at this
      exact this
    have hpow :
        (1 + chiSqDiv Pp Pm) ^ m ≤
          Real.exp ((m : ℝ) * chiSqDiv Pp Pm) := by
      calc
        (1 + chiSqDiv Pp Pm) ^ m
            ≤ (Real.exp (chiSqDiv Pp Pm)) ^ m := by
              exact pow_le_pow_left₀ (by linarith)
                (by
                  linarith [Real.add_one_le_exp (chiSqDiv Pp Pm)])
                m
        _ = Real.exp ((m : ℝ) * chiSqDiv Pp Pm) := by
            rw [← Real.exp_nat_mul]
    have hexp_le :
        Real.exp ((m : ℝ) * chiSqDiv Pp Pm) ≤ Real.exp c0 := by
      exact Real.exp_le_exp.mpr hmul
    have hprod_eq :
        1 + chiSqDiv Pprod Qprod =
          (1 + chiSqDiv Pp Pm) ^ m := by
      dsimp [Pprod, Qprod]
      exact one_add_chiSqDiv_pi_iid_general Pp Pm hac hint m
    have hchi_prod : chiSqDiv Pprod Qprod ≤ Real.exp c0 - 1 := by
      have hone : 1 + chiSqDiv Pprod Qprod ≤ Real.exp c0 := by
        rw [hprod_eq]
        exact hpow.trans hexp_le
      linarith
    have hCprod_nonneg : 0 ≤ Real.exp c0 - 1 := by
      have h1 : 1 ≤ Real.exp c0 := by
        have := Real.add_one_le_exp c0
        linarith
      linarith
    have htest :=
      testing_error_lower_of_chi Pprod Qprod hac_prod hint_prod hCprod_nonneg hchi_prod hA
    have hconst : 1 / (4 * ((Real.exp c0 - 1) + 1)) = 1 / (4 * Real.exp c0) := by
      ring_nf
    simpa [Pprod, Qprod, hconst] using htest

end Causalean.Stat
