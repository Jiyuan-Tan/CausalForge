/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Stat.Concentration.Covering.VCLocalizedRegime

/-!
Finite-VC localized uniform-deviation bounds derived from the sharp localized empirical-process
theorem.

For a finite-VC binary-indexed function class, with high probability the localized empirical
process deviates from its mean by at most 8ρ * ‖f‖ + 5ρ² uniformly over the class, with
critical radius ρ of order sqrt(d * log n / n) -- derived by instantiating
`localized_uniform_deviation_sharp` with the finite-VC localized envelope.

This file is the finite-VC specialization layer for the sharp localized uniform deviation
theorem.  The empirical-process content is supplied by `VCLocalizedRegime.lean`; the only
application-specific arithmetic left to callers is the peeling/log domination condition.
It exports the VC-dimension event `vc_localized_deviation_event`, the direct
growth-cardinality variant `vc_localized_deviation_event_of_card`, and the
measurability/integrability bridges needed to instantiate the sharp theorem.
-/

namespace Causalean
namespace Stat
namespace Concentration

open MeasureTheory ProbabilityTheory

universe u v

section Helpers

variable {ι : Type u} {𝒳 : Type v}

/-- The critical radius of a positive linear envelope is exactly its slope. -/
private lemma criticalRadius_linear_eq {C : ℝ} (hC : 0 < C) :
    criticalRadius (fun r : ℝ => C * r) = C := by
  apply le_antisymm
  · exact criticalRadius_linear_le hC
  · rw [criticalRadius]
    apply le_csInf
    · exact ⟨C, hC, by rw [pow_two]⟩
    · rintro δ ⟨hδ_pos, hδ⟩
      have hδ' : C * δ ≤ δ * δ := by
        simpa [pow_two] using hδ
      nlinarith [hδ', hδ_pos]

/-- The finite-VC linear envelope attains the fixed-point inequality at its
critical radius. -/
private lemma vcLocalizedPsi_criticalRadius_fp {K : ℝ} {d n : ℕ}
    (hK : 0 ≤ K) (hn : 0 < n) :
    vcLocalizedPsi K d n (criticalRadius (vcLocalizedPsi K d n))
      ≤ (criticalRadius (vcLocalizedPsi K d n)) ^ 2 := by
  let ρ := vcLocalizedSlope K d n
  have hρ_pos : 0 < ρ := vcLocalizedSlope_pos hK hn
  have hcrit_eq : criticalRadius (vcLocalizedPsi K d n) = ρ := by
    unfold vcLocalizedPsi
    exact criticalRadius_linear_eq hρ_pos
  rw [hcrit_eq]
  unfold vcLocalizedPsi ρ
  rw [pow_two]

/-- Star-hull zero-out terms inherit the uniform envelope bound. -/
private lemma abs_starHullZeroOut_le_bound
    (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ) {b r : ℝ}
    (hb : 0 ≤ b) (hbound : ∀ i x, |F i x| ≤ b)
    (p : starHullParam ι) (x : 𝒳) :
    |starHullZeroOut F norm r p x| ≤ b := by
  unfold starHullZeroOut
  by_cases hp : norm (starHullEval F p) ≤ r
  · have hα_nonneg : 0 ≤ p.1.val := p.1.property.1
    have hα_le_one : p.1.val ≤ 1 := p.1.property.2
    have hα_abs_le : |p.1.val| ≤ 1 := by
      rw [abs_of_nonneg hα_nonneg]
      exact hα_le_one
    calc
      |starHullZeroOut F norm r p x| = |starHullEval F p x| := by
        simp [starHullZeroOut, hp]
      _ = |p.1.val| * |F p.2 x| := by
        simp [starHullEval, abs_mul]
      _ ≤ 1 * b := mul_le_mul hα_abs_le (hbound p.2 x) (abs_nonneg _) (by norm_num)
      _ = b := one_mul b
  · simpa [hp] using hb

/-- The sharp-deviation bridge only needs a finite upper bound on each
sample/sign supremum.  In the identity-sample setup, the class envelope gives
`b` as an explicit upper bound. -/
private lemma starHullZeroOut_rademacher_bddAbove_of_bound
    {n : ℕ} (hn : 0 < n)
    (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ) {b r : ℝ}
    (hb : 0 ≤ b) (hbound : ∀ i x, |F i x| ≤ b) :
    ∀ S : Fin n → 𝒳, ∀ σ : Signs n,
      BddAbove (Set.range fun p : starHullParam ι =>
        |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) *
          starHullZeroOut F norm r p (S k)|) := by
  intro S σ
  rw [bddAbove_def]
  refine ⟨b, ?_⟩
  intro y hy
  rcases hy with ⟨p, rfl⟩
  have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hsum_abs :
      |∑ k : Fin n, (σ k : ℝ) * starHullZeroOut F norm r p (S k)|
        ≤ ∑ _k : Fin n, b := by
    calc
      |∑ k : Fin n, (σ k : ℝ) * starHullZeroOut F norm r p (S k)|
          ≤ ∑ k : Fin n,
              |(σ k : ℝ) * starHullZeroOut F norm r p (S k)| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : Fin n, b := by
        refine Finset.sum_le_sum ?_
        intro k _
        calc
          |(σ k : ℝ) * starHullZeroOut F norm r p (S k)|
              = |starHullZeroOut F norm r p (S k)| := by
                simp [abs_mul, Signs.apply_abs']
          _ ≤ b := abs_starHullZeroOut_le_bound F norm hb hbound p (S k)
  have hscaled :
      (n : ℝ)⁻¹ *
          |∑ k : Fin n, (σ k : ℝ) * starHullZeroOut F norm r p (S k)|
        ≤ (n : ℝ)⁻¹ * ∑ _k : Fin n, b :=
    mul_le_mul_of_nonneg_left hsum_abs (inv_nonneg.mpr (le_of_lt hn_pos))
  have hcard : (n : ℝ)⁻¹ * ∑ _k : Fin n, b = b := by
    simp [Finset.sum_const, hn_pos.ne']
  calc
    |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) *
        starHullZeroOut F norm r p (S k)|
        = (n : ℝ)⁻¹ *
          |∑ k : Fin n, (σ k : ℝ) * starHullZeroOut F norm r p (S k)| := by
            rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (le_of_lt hn_pos))]
    _ ≤ (n : ℝ)⁻¹ * ∑ _k : Fin n, b := hscaled
    _ = b := hcard

private lemma ciSup_prod_eq_of_bddAbove {A B : Type*} [Nonempty A] [Nonempty B]
    (f : A → B → ℝ)
    (hb : BddAbove (Set.range fun p : A × B => f p.1 p.2)) :
    (⨆ p : A × B, f p.1 p.2) = ⨆ b : B, ⨆ a : A, f a b := by
  classical
  have hinner_bdd : ∀ b : B, BddAbove (Set.range fun a : A => f a b) := by
    intro b
    rcases hb with ⟨M, hM⟩
    refine ⟨M, ?_⟩
    rintro _ ⟨a, rfl⟩
    exact hM ⟨(a, b), rfl⟩
  have houter_bdd : BddAbove (Set.range fun b : B => ⨆ a : A, f a b) := by
    rcases hb with ⟨M, hM⟩
    refine ⟨M, ?_⟩
    rintro _ ⟨b, rfl⟩
    exact ciSup_le fun a => hM ⟨(a, b), rfl⟩
  apply le_antisymm
  · refine ciSup_le ?_
    intro p
    exact le_trans (le_ciSup (hinner_bdd p.2) p.1) (le_ciSup houter_bdd p.2)
  · refine ciSup_le ?_
    intro b
    refine ciSup_le ?_
    intro a
    exact le_ciSup hb (a, b)

private lemma ciSup_mul_const_of_Icc {A : Type*} [Nonempty A]
    (c : A → ℝ) (b : ℝ) (hc_le : ∀ a, c a ≤ 1) (hb : 0 ≤ b) :
    (⨆ a : A, c a * b) = (⨆ a : A, c a) * b := by
  classical
  have hc_bdd : BddAbove (Set.range c) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨a, rfl⟩
    exact hc_le a
  have hcb_bdd : BddAbove (Set.range fun a : A => c a * b) := by
    refine ⟨b, ?_⟩
    rintro _ ⟨a, rfl⟩
    calc
      c a * b ≤ 1 * b := mul_le_mul_of_nonneg_right (hc_le a) hb
      _ = b := one_mul b
  apply le_antisymm
  · refine ciSup_le ?_
    intro a
    exact mul_le_mul_of_nonneg_right (le_ciSup hc_bdd a) hb
  · by_cases hb0 : b = 0
    · simp [hb0]
    · have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
      have hsup_le : (⨆ a : A, c a) ≤ (⨆ a : A, c a * b) / b := by
        refine ciSup_le ?_
        intro a
        exact (le_div_iff₀ hbpos).mpr (le_ciSup hcb_bdd a)
      exact (le_div_iff₀ hbpos).mp hsup_le

/-- Residual measurability bridge for the empirical Rademacher process of the
finite-VC localized star hull.

  The scale parameter in `starHullParam ι = Set.Icc 0 1 × ι` is uncountable.
  For measurability we first take its deterministic supremum, producing one
  constant coefficient for each countable `i : ι`, and then use the standard
  countable `Measurable.iSup` bridge. -/
  lemma vc_starHullZeroOut_empirical_rademacher_aemeasurable_residual
      [MeasurableSpace 𝒳] [Nonempty ι] [Countable ι]
      (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
      (hF_meas : ∀ i, Measurable (F i))
      (μ : Measure 𝒳) [IsProbabilityMeasure μ]
      (b r : ℝ) (hb : 0 ≤ b) (hbound : ∀ i x, |F i x| ≤ b)
      (n : ℕ) (hn : 0 < n) :
        AEMeasurable
          (fun ω : Fin n → 𝒳 =>
            empiricalRademacherComplexity n (starHullZeroOut F norm r) (id ∘ ω))
          (Measure.pi (fun _ => μ)) := by
    classical
    apply Measurable.aemeasurable
    unfold empiricalRademacherComplexity
    apply measurable_const.mul
    apply Finset.univ.measurable_sum
    intro σ _
    have hsup_eq :
        (fun ω : Fin n → 𝒳 =>
          ⨆ p : starHullParam ι,
            |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) *
              starHullZeroOut F norm r p ((id ∘ ω) k)|) =
        fun ω : Fin n → 𝒳 =>
          ⨆ i : ι,
            starHullZeroOutScaleCoeff F norm r i *
              |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * F i (ω k)| := by
      funext ω
      have hbdd :
          BddAbove (Set.range fun p : starHullParam ι =>
            |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) *
              starHullZeroOut F norm r p ((id ∘ ω) k)|) := by
        simpa using
          starHullZeroOut_rademacher_bddAbove_of_bound
            (n := n) hn F norm hb hbound (id ∘ ω) σ
      calc
        (⨆ p : starHullParam ι,
            |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) *
              starHullZeroOut F norm r p ((id ∘ ω) k)|)
            = ⨆ i : ι, ⨆ a : Set.Icc (0 : ℝ) 1,
                |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) *
                  starHullZeroOut F norm r (a, i) (ω k)| := by
              unfold starHullParam
              simpa [Function.comp_def] using
                ciSup_prod_eq_of_bddAbove
                  (fun a : Set.Icc (0 : ℝ) 1 => fun i : ι =>
                    |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) *
                      starHullZeroOut F norm r (a, i) (ω k)|)
                  (by simpa [Function.comp_def] using hbdd)
        _ = ⨆ i : ι,
              starHullZeroOutScaleCoeff F norm r i *
                |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * F i (ω k)| := by
              congr
              ext i
              exact starHullZeroOut_inner_sup_eq F norm r ω σ i
    rw [hsup_eq]
    apply Measurable.iSup
    intro i
    apply measurable_const.mul
    apply Measurable.abs
    apply measurable_const.mul
    apply Finset.univ.measurable_sum
    intro k _
    apply measurable_const.mul
    exact (hF_meas i).comp (measurable_pi_apply k)

/-- Measurability wrapper for the localized star-hull empirical Rademacher
complexity. This packages the residual measurability lemma under the standard
finite-class assumptions used by the VC localized-deviation theorem. -/
  lemma vc_starHullZeroOut_empirical_rademacher_aemeasurable
      [MeasurableSpace 𝒳] [Nonempty ι] [Countable ι]
      (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
      (hF_meas : ∀ i, Measurable (F i))
      (μ : Measure 𝒳) [IsProbabilityMeasure μ]
      (b r : ℝ) (hb : 0 ≤ b) (hbound : ∀ i x, |F i x| ≤ b)
      (n : ℕ) (hn : 0 < n) :
        AEMeasurable
          (fun ω : Fin n → 𝒳 =>
            empiricalRademacherComplexity n (starHullZeroOut F norm r) (id ∘ ω))
          (Measure.pi (fun _ => μ)) :=
    vc_starHullZeroOut_empirical_rademacher_aemeasurable_residual
      F norm hF_meas μ b r hb hbound n hn

/-- Integrability of the finite-VC localized star-hull empirical Rademacher
process follows from the deterministic linear envelope once the residual
measurability bridge above is available. -/
  lemma vc_starHullZeroOut_empirical_rademacher_integrable
      [MeasurableSpace 𝒳] [Nonempty ι] [Countable ι]
      (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
      (μ : Measure 𝒳) [IsProbabilityMeasure μ]
      (hF_meas : ∀ i, Measurable (F i))
      (b : ℝ) (hb : 0 ≤ b) (hbound : ∀ i x, |F i x| ≤ b)
      (K : ℝ) (d n : ℕ) (hK : (1 : ℝ) ≤ K) (hn : 0 < n)
      (Hvc : BinaryFactoredVCClass F d)
      (Hloc : LocalizedVCDudleyHypotheses F norm) :
    ∀ r : ℝ, vcLocalizedSlope K d n ≤ r →
      Integrable
        (fun ω : Fin n → 𝒳 =>
          empiricalRademacherComplexity n (starHullZeroOut F norm r) (id ∘ ω))
        (Measure.pi (fun _ => μ)) := by
  intro r hr
  let g : (Fin n → 𝒳) → ℝ :=
    fun ω => empiricalRademacherComplexity n (starHullZeroOut F norm r) (id ∘ ω)
  have hr_nonneg : 0 ≤ r :=
    le_trans (vcLocalizedSlope_nonneg K d n) hr
  have hg_meas :
      AEMeasurable g (Measure.pi (fun _ : Fin n => μ)) := by
      simpa [g] using
        vc_starHullZeroOut_empirical_rademacher_aemeasurable
          F norm hF_meas μ b r hb hbound n hn
  have hg_nonneg : ∀ᵐ ω : Fin n → 𝒳 ∂(Measure.pi (fun _ : Fin n => μ)),
      0 ≤ g ω := by
    exact Filter.Eventually.of_forall fun ω => by
      dsimp [g]
      unfold empiricalRademacherComplexity
      refine mul_nonneg ?_ ?_
      · positivity
      · refine Finset.sum_nonneg ?_
        intro σ _
        refine Real.iSup_nonneg ?_
        intro p
        exact abs_nonneg _
  have hg_upper : ∀ᵐ ω : Fin n → 𝒳 ∂(Measure.pi (fun _ : Fin n => μ)),
      g ω ≤ vcLocalizedPsi K d n r := by
    exact Filter.Eventually.of_forall fun ω => by
      dsimp [g]
      simpa using
        vc_starHullZeroOut_empirical_rademacher_le_linear
          F norm K d n hK Hvc Hloc (id ∘ ω) r hr_nonneg
  have hg_Icc : ∀ᵐ ω : Fin n → 𝒳 ∂(Measure.pi (fun _ : Fin n => μ)),
      g ω ∈ Set.Icc 0 (vcLocalizedPsi K d n r) := by
    filter_upwards [hg_nonneg, hg_upper] with ω h0 h1
    exact ⟨h0, h1⟩
  exact integrable_bounded 0 (vcLocalizedPsi K d n r) hg_meas hg_Icc

/-- Cardinality-bound variant of the integrability bridge for the localized
star-hull empirical Rademacher process. -/
  lemma vc_starHullZeroOut_empirical_rademacher_integrable_of_card
      [MeasurableSpace 𝒳] [Nonempty ι] [Countable ι]
      (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
      (π : ι → 𝒳 → Bool)
      (μ : Measure 𝒳) [IsProbabilityMeasure μ]
      (hF_meas : ∀ i, Measurable (F i))
      (b : ℝ) (hb : 0 ≤ b) (hbound : ∀ i x, |F i x| ≤ b)
      (hfactor : ∀ {m : ℕ} (S : Fin m → 𝒳), ∃ φ : Fin m → Bool → ℝ,
        ∀ i j, F i (S j) = φ j (π i (S j)))
      (K : ℝ) (dPi n : ℕ) (hK : (1 : ℝ) ≤ K) (hn : 0 < n)
      (hcard : ∀ (m : ℕ) (S : Fin m → 𝒳),
        (growthFamily π S).card ≤ (m + 1) ^ dPi)
    (Hloc : LocalizedVCDudleyHypotheses F norm) :
    ∀ r : ℝ, vcLocalizedSlope K dPi n ≤ r →
      Integrable
        (fun ω : Fin n → 𝒳 =>
          empiricalRademacherComplexity n (starHullZeroOut F norm r) (id ∘ ω))
        (Measure.pi (fun _ => μ)) := by
  intro r hr
  let g : (Fin n → 𝒳) → ℝ :=
    fun ω => empiricalRademacherComplexity n (starHullZeroOut F norm r) (id ∘ ω)
  have hr_nonneg : 0 ≤ r :=
    le_trans (vcLocalizedSlope_nonneg K dPi n) hr
  have hg_meas :
      AEMeasurable g (Measure.pi (fun _ : Fin n => μ)) := by
      simpa [g] using
        vc_starHullZeroOut_empirical_rademacher_aemeasurable
          F norm hF_meas μ b r hb hbound n hn
  have hg_nonneg : ∀ᵐ ω : Fin n → 𝒳 ∂(Measure.pi (fun _ : Fin n => μ)),
      0 ≤ g ω := by
    exact Filter.Eventually.of_forall fun ω => by
      dsimp [g]
      unfold empiricalRademacherComplexity
      refine mul_nonneg ?_ ?_
      · positivity
      · refine Finset.sum_nonneg ?_
        intro σ _
        refine Real.iSup_nonneg ?_
        intro p
        exact abs_nonneg _
  have hg_upper : ∀ᵐ ω : Fin n → 𝒳 ∂(Measure.pi (fun _ : Fin n => μ)),
      g ω ≤ vcLocalizedPsi K dPi n r := by
    exact Filter.Eventually.of_forall fun ω => by
      dsimp [g]
      simpa using
        vc_starHullZeroOut_empirical_rademacher_le_linear_of_card
          F norm π hfactor K dPi n hK hcard Hloc (id ∘ ω) r hr_nonneg
  have hg_Icc : ∀ᵐ ω : Fin n → 𝒳 ∂(Measure.pi (fun _ : Fin n => μ)),
      g ω ∈ Set.Icc 0 (vcLocalizedPsi K dPi n r) := by
    filter_upwards [hg_nonneg, hg_upper] with ω h0 h1
    exact ⟨h0, h1⟩
  exact integrable_bounded 0 (vcLocalizedPsi K dPi n r) hg_meas hg_Icc

end Helpers

section Main

variable {ι : Type u} {𝒳 : Type v} [MeasurableSpace 𝒳]
variable [Nonempty 𝒳] [Nonempty ι] [Countable ι]

/-- Finite-VC localized uniform deviation event.

For `ρ = vcLocalizedSlope K d n` and `Rmax = R.b = b`, where `R` is the
finite-VC localized regime built by `vcLocalizedRegime`, there is an event of
probability at least `1 - δ` on which every function in the class with
`0 ≤ norm (F i) ≤ b` satisfies the sharp localized deviation bound
`8 * ρ * norm (F i) + 5 * ρ ^ 2`.

The arithmetic side condition `hδ_dom` is the peeling/log domination condition
from `localized_uniform_deviation_sharp`. -/
theorem vc_localized_deviation_event
    (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
    (μ : Measure 𝒳) [IsProbabilityMeasure μ]
    (hF_meas : ∀ i, Measurable (F i))
    (b : ℝ) (hb : 0 ≤ b) (hbound : ∀ i x, |F i x| ≤ b)
    (K : ℝ) (d n : ℕ) (hK : (1 : ℝ) ≤ K) (hn : 0 < n)
    (Hvc : BinaryFactoredVCClass F d)
    (Hloc : LocalizedVCDudleyHypotheses F norm)
    {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1)
    (hρ_le_b : vcLocalizedSlope K d n ≤ b)
    (hδ_dom : ∀ L : ℕ,
      b ≤ vcLocalizedSlope K d n * (2 : ℝ) ^ L →
      b * Real.sqrt
          (2 * Real.log (2 * ((L : ℝ) + 1) / δ) / n)
        ≤ (vcLocalizedSlope K d n) ^ 2) :
    ∃ E : Set (Fin n → 𝒳), MeasurableSet E ∧
      Measure.pi (fun _ => μ) E ≥ 1 - ENNReal.ofReal δ ∧
      ∀ ω ∈ E, ∀ i : ι,
        0 ≤ norm (F i) →
        norm (F i) ≤ b →
        |(n : ℝ)⁻¹ * (Finset.univ.sum fun k : Fin n => F i (ω k))
            - μ[fun x => F i x]|
          ≤ 8 * vcLocalizedSlope K d n * norm (F i)
            + 5 * (vcLocalizedSlope K d n) ^ 2 := by
  classical
  have hK0 : 0 ≤ K := le_trans zero_le_one hK
  let R : LocalizedRegime 𝒳 ι 𝒳 F norm μ id :=
    vcLocalizedRegime F norm μ id b hb (by simpa using hbound) K d hK Hvc Hloc
  let ρ : ℝ := vcLocalizedSlope K d n
  have hρ_pos : 0 < ρ := vcLocalizedSlope_pos hK0 hn
  have hcrit_eq : criticalRadius (R.ψ n) = ρ := by
    dsimp [R, vcLocalizedRegime, vcLocalizedPsi, ρ]
    exact criticalRadius_linear_eq hρ_pos
  have hcrit_le_ρ : criticalRadius (R.ψ n) ≤ ρ := by
    rw [hcrit_eq]
  have hcrit_pos : 0 < criticalRadius (R.ψ n) := by
    rw [hcrit_eq]
    exact hρ_pos
  have hcrit_fp : R.ψ n (criticalRadius (R.ψ n)) ≤
      (criticalRadius (R.ψ n)) ^ 2 := by
    dsimp [R, vcLocalizedRegime]
    exact vcLocalizedPsi_criticalRadius_fp hK0 hn
  have hrad_bdd : ∀ r : ℝ, ρ ≤ r →
      ∀ S : Fin n → 𝒳, ∀ σ : Signs n,
        BddAbove (Set.range fun p : starHullParam ι =>
          |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) *
            starHullZeroOut F norm r p (S k)|) := by
    intro r _hr
    exact starHullZeroOut_rademacher_bddAbove_of_bound hn F norm hb hbound
  have hrad_int : ∀ r : ℝ, ρ ≤ r →
      Integrable
        (fun ω : Fin n → 𝒳 =>
          empiricalRademacherComplexity n (starHullZeroOut F norm r) (id ∘ ω))
        (Measure.pi (fun _ => μ)) := by
    intro r hr
    exact vc_starHullZeroOut_empirical_rademacher_integrable
      F norm μ hF_meas b hb hbound K d n hK hn Hvc Hloc r hr
  rcases localized_uniform_deviation_sharp
      F norm μ id measurable_id hF_meas R hδ hδ' n hn
      (ρ := ρ) (Rmax := b)
      hcrit_le_ρ hρ_pos (by simpa [ρ] using hρ_le_b)
      hcrit_pos hcrit_fp hrad_bdd hrad_int
      (by simpa [R, ρ] using hδ_dom) with
    ⟨E, hE_meas, hE_prob, hE_bound⟩
  refine ⟨E, hE_meas, hE_prob, ?_⟩
  intro ω hω i hi_nonneg hi_b
  simpa [R, ρ] using hE_bound ω hω i hi_nonneg hi_b

/-- Growth-cardinality localized uniform deviation event.

This variant takes a direct cardinality bound on the binary trace family,
`#growthFamily π S ≤ (m + 1)^dPi`, matching finite policy trace bounds that
control growth functions without first packaging the class as a VC-dimension
bound. -/
theorem vc_localized_deviation_event_of_card
    (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
    (π : ι → 𝒳 → Bool)
    (μ : Measure 𝒳) [IsProbabilityMeasure μ]
    (hF_meas : ∀ i, Measurable (F i))
    (b : ℝ) (hb : 0 ≤ b) (hbound : ∀ i x, |F i x| ≤ b)
    (hfactor : ∀ {m : ℕ} (S : Fin m → 𝒳), ∃ φ : Fin m → Bool → ℝ,
      ∀ i j, F i (S j) = φ j (π i (S j)))
    (K : ℝ) (dPi n : ℕ) (hK : (1 : ℝ) ≤ K) (hn : 0 < n)
    (hcard : ∀ (m : ℕ) (S : Fin m → 𝒳),
      (growthFamily π S).card ≤ (m + 1) ^ dPi)
    (Hloc : LocalizedVCDudleyHypotheses F norm)
    {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1)
    (hρ_le_b : vcLocalizedSlope K dPi n ≤ b)
    (hδ_dom : ∀ L : ℕ,
      b ≤ vcLocalizedSlope K dPi n * (2 : ℝ) ^ L →
      b * Real.sqrt
          (2 * Real.log (2 * ((L : ℝ) + 1) / δ) / n)
        ≤ (vcLocalizedSlope K dPi n) ^ 2) :
    ∃ E : Set (Fin n → 𝒳), MeasurableSet E ∧
      Measure.pi (fun _ => μ) E ≥ 1 - ENNReal.ofReal δ ∧
      ∀ ω ∈ E, ∀ i : ι,
        0 ≤ norm (F i) →
        norm (F i) ≤ b →
        |(n : ℝ)⁻¹ * (Finset.univ.sum fun k : Fin n => F i (ω k))
            - μ[fun x => F i x]|
          ≤ 8 * vcLocalizedSlope K dPi n * norm (F i)
            + 5 * (vcLocalizedSlope K dPi n) ^ 2 := by
  classical
  have hK0 : 0 ≤ K := le_trans zero_le_one hK
  let R : LocalizedRegime 𝒳 ι 𝒳 F norm μ id :=
    vcLocalizedRegime_of_card
      F norm π μ id b hb (by simpa using hbound)
      hfactor K dPi hK hcard Hloc
  let ρ : ℝ := vcLocalizedSlope K dPi n
  have hρ_pos : 0 < ρ := vcLocalizedSlope_pos hK0 hn
  have hcrit_eq : criticalRadius (R.ψ n) = ρ := by
    dsimp [R, vcLocalizedRegime_of_card, vcLocalizedPsi, ρ]
    exact criticalRadius_linear_eq hρ_pos
  have hcrit_le_ρ : criticalRadius (R.ψ n) ≤ ρ := by
    rw [hcrit_eq]
  have hcrit_pos : 0 < criticalRadius (R.ψ n) := by
    rw [hcrit_eq]
    exact hρ_pos
  have hcrit_fp : R.ψ n (criticalRadius (R.ψ n)) ≤
      (criticalRadius (R.ψ n)) ^ 2 := by
    dsimp [R, vcLocalizedRegime_of_card]
    exact vcLocalizedPsi_criticalRadius_fp hK0 hn
  have hrad_bdd : ∀ r : ℝ, ρ ≤ r →
      ∀ S : Fin n → 𝒳, ∀ σ : Signs n,
        BddAbove (Set.range fun p : starHullParam ι =>
          |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) *
            starHullZeroOut F norm r p (S k)|) := by
    intro r _hr
    exact starHullZeroOut_rademacher_bddAbove_of_bound hn F norm hb hbound
  have hrad_int : ∀ r : ℝ, ρ ≤ r →
      Integrable
        (fun ω : Fin n → 𝒳 =>
          empiricalRademacherComplexity n (starHullZeroOut F norm r) (id ∘ ω))
        (Measure.pi (fun _ => μ)) := by
    intro r hr
    exact vc_starHullZeroOut_empirical_rademacher_integrable_of_card
      F norm π μ hF_meas b hb hbound hfactor K dPi n hK hn hcard Hloc r hr
  rcases localized_uniform_deviation_sharp
      F norm μ id measurable_id hF_meas R hδ hδ' n hn
      (ρ := ρ) (Rmax := b)
      hcrit_le_ρ hρ_pos (by simpa [ρ] using hρ_le_b)
      hcrit_pos hcrit_fp hrad_bdd hrad_int
      (by simpa [R, ρ] using hδ_dom) with
    ⟨E, hE_meas, hE_prob, hE_bound⟩
  refine ⟨E, hE_meas, hE_prob, ?_⟩
  intro ω hω i hi_nonneg hi_b
  simpa [R, ρ] using hE_bound ω hω i hi_nonneg hi_b

end Main

end Concentration
end Stat
end Causalean
