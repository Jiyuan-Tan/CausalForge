/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import CausalSmith.Stat.STAT_PolicyRegretMarginOverlap_Research.Helpers.OffsetControl

/-! Provides the localized VC self-bound helper. -/

namespace CausalSmith.Stat.PolicyRegretMarginOverlap

open MeasureTheory
open scoped BigOperators

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

-- @node: lem:localized-vc-self-bound
/-- `lem:localized-vc-self-bound`. EXPECTED-risk self-localized selection bound
from the offset-control node. With `ρ_n = (B²/n)^{A_α}(log n)^p`, `B ≥ 1`, the
EXPECTED pooled offset positive-part supremum controlled by `ρ_n` (the bound
supplied by `crossfit_localized_offset_control`, `hoff`), and any data-dependent
`Π`-valued selector `π̃` satisfying the SAMPLE-WISE selection inequality
`R_P(π̃(sample)) ≤ 2|G_cf(sample, π̃(sample))| + δ`, the EXPECTED regret obeys
`E_P R_P(π̃) ≤ C{ρ_n + δ}`, and if `δ ≤ 1/n` the `δ` term is absorbed into
`C ρ_n`. -/
lemma localized_vc_self_bound {n K : ℕ} (P : ObservedLaw 𝒳)
    (policySet : Set (Policy 𝒳)) (α B δ Coff p : ℝ)
    (g : Fin K → Policy 𝒳 → Observation 𝒳 → ℝ) (assign : Fin n → Fin K)
    (πt : (Fin n → Observation 𝒳) → Policy 𝒳)
    (hprob : IsProbabilityMeasure P.dataMeasure)
    (hB : 1 ≤ B) (hn : 0 < n) (hp : 0 ≤ p) (hδ_nonneg : 0 ≤ δ)
    (hmem : ∀ sample, πt sample ∈ policySet)
    (hoff : expectedPooledOffsetSup P g assign policySet
              ≤ Coff * ((B ^ 2 / (n : ℝ)) ^ (Aalpha α) * (Real.log n) ^ p))
    (hlarge : (n : ℝ)⁻¹
              ≤ Coff * ((B ^ 2 / (n : ℝ)) ^ (Aalpha α) * (Real.log n) ^ p))
    (hInt_regret : Integrable (fun sample : Fin n → Observation 𝒳 =>
        lawRegret P (πt sample)) (Measure.pi (fun _ : Fin n => P.dataMeasure)))
    (hInt_offset : Integrable (fun sample : Fin n → Observation 𝒳 =>
        sSup ((fun π =>
          max 0 (2 * |pooledCrossfitProcess P g assign sample π| -
            lawRegret P π / 4)) '' policySet))
        (Measure.pi (fun _ : Fin n => P.dataMeasure)))
    (hbdd_offset : ∀ sample : Fin n → Observation 𝒳,
        BddAbove ((fun π =>
          max 0 (2 * |pooledCrossfitProcess P g assign sample π| -
            lawRegret P π / 4)) '' policySet))
    (hsel : ∀ sample, lawRegret P (πt sample)
              ≤ 2 * |pooledCrossfitProcess P g assign sample (πt sample)| + δ) :
    0 < (8 / 3 : ℝ) ∧
      ∫ sample, lawRegret P (πt sample)
            ∂(Measure.pi (fun _ : Fin n => P.dataMeasure))
          ≤ (8 / 3 : ℝ) *
              (Coff * ((B ^ 2 / (n : ℝ)) ^ (Aalpha α) * (Real.log n) ^ p) + δ) ∧
      (δ ≤ (n : ℝ)⁻¹ →
        ∫ sample, lawRegret P (πt sample)
              ∂(Measure.pi (fun _ : Fin n => P.dataMeasure))
            ≤ (8 / 3 : ℝ) *
                (Coff * ((B ^ 2 / (n : ℝ)) ^ (Aalpha α) * (Real.log n) ^ p)))
    := by
  classical
  letI : IsProbabilityMeasure P.dataMeasure := hprob
  let μn : Measure (Fin n → Observation 𝒳) :=
    Measure.pi (fun _ : Fin n => P.dataMeasure)
  let ρ : ℝ := Coff * ((B ^ 2 / (n : ℝ)) ^ (Aalpha α) * (Real.log n) ^ p)
  let offset : (Fin n → Observation 𝒳) → ℝ := fun sample =>
    sSup ((fun π =>
      max 0 (2 * |pooledCrossfitProcess P g assign sample π| -
        lawRegret P π / 4)) '' policySet)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hρ_pos : 0 < ρ := lt_of_lt_of_le (inv_pos.mpr hnR) (by simpa [ρ] using hlarge)
  have hρ_nonneg : 0 ≤ ρ := hρ_pos.le
  have hselected_le_offset :
      ∀ sample : Fin n → Observation 𝒳,
        max 0 (2 * |pooledCrossfitProcess P g assign sample (πt sample)| -
            lawRegret P (πt sample) / 4) ≤ offset sample := by
    intro sample
    dsimp [offset]
    exact le_csSup (hbdd_offset sample) ⟨πt sample, hmem sample, rfl⟩
  have hpoint :
      ∀ sample : Fin n → Observation 𝒳,
        lawRegret P (πt sample) ≤
          (4 / 3 : ℝ) * offset sample + (4 / 3 : ℝ) * δ := by
    intro sample
    let R : ℝ := lawRegret P (πt sample)
    let z : ℝ := pooledCrossfitProcess P g assign sample (πt sample)
    let a : ℝ := 2 * |z| - R / 4
    have hsel' : R ≤ 2 * |z| + δ := by
      simpa [R, z] using hsel sample
    have hthree_quarters : (3 / 4 : ℝ) * R ≤ a + δ := by
      dsimp [a]
      nlinarith
    have hcore : R ≤ (4 / 3 : ℝ) * max 0 a + (4 / 3 : ℝ) * δ := by
      by_cases ha : 0 ≤ a
      · have hmax : max 0 a = a := max_eq_right ha
        calc
          R = (4 / 3 : ℝ) * ((3 / 4 : ℝ) * R) := by ring
          _ ≤ (4 / 3 : ℝ) * (a + δ) := by nlinarith
          _ = (4 / 3 : ℝ) * max 0 a + (4 / 3 : ℝ) * δ := by
                rw [hmax]
                ring
      · have ha_lt : a < 0 := lt_of_not_ge ha
        have hmax : max 0 a = 0 := max_eq_left (le_of_lt ha_lt)
        have hthree_quarters_delta : (3 / 4 : ℝ) * R ≤ δ := by
          nlinarith
        calc
          R = (4 / 3 : ℝ) * ((3 / 4 : ℝ) * R) := by ring
          _ ≤ (4 / 3 : ℝ) * δ := by nlinarith
          _ = (4 / 3 : ℝ) * max 0 a + (4 / 3 : ℝ) * δ := by
                rw [hmax]
                ring
    have hoff_le := hselected_le_offset sample
    calc
      lawRegret P (πt sample) = R := rfl
      _ ≤ (4 / 3 : ℝ) * max 0 a + (4 / 3 : ℝ) * δ := hcore
      _ ≤ (4 / 3 : ℝ) * offset sample + (4 / 3 : ℝ) * δ := by
            nlinarith
  have hInt_rhs : Integrable
      (fun sample : Fin n → Observation 𝒳 =>
        (4 / 3 : ℝ) * offset sample + (4 / 3 : ℝ) * δ) μn := by
    simpa [offset, μn] using
      ((hInt_offset.const_mul (4 / 3 : ℝ)).add (integrable_const ((4 / 3 : ℝ) * δ)))
  have hmono :
      ∫ sample, lawRegret P (πt sample) ∂μn
        ≤ ∫ sample, ((4 / 3 : ℝ) * offset sample + (4 / 3 : ℝ) * δ) ∂μn :=
    integral_mono (by simpa [μn] using hInt_regret) hInt_rhs hpoint
  have hoffρ : ∫ sample, offset sample ∂μn ≤ ρ := by
    simpa [expectedPooledOffsetSup, offset, μn, ρ] using hoff
  have hrhs_eval :
      ∫ sample, ((4 / 3 : ℝ) * offset sample + (4 / 3 : ℝ) * δ) ∂μn
        = (4 / 3 : ℝ) * ∫ sample, offset sample ∂μn + (4 / 3 : ℝ) * δ := by
    rw [integral_add]
    · rw [integral_const_mul]
      simp [μn, offset]
    · exact hInt_offset.const_mul (4 / 3 : ℝ)
    · exact integrable_const ((4 / 3 : ℝ) * δ)
  have hmain :
      ∫ sample, lawRegret P (πt sample) ∂μn
        ≤ (4 / 3 : ℝ) * ρ + (4 / 3 : ℝ) * δ := by
    calc
      ∫ sample, lawRegret P (πt sample) ∂μn
          ≤ ∫ sample, ((4 / 3 : ℝ) * offset sample + (4 / 3 : ℝ) * δ) ∂μn :=
            hmono
      _ = (4 / 3 : ℝ) * ∫ sample, offset sample ∂μn + (4 / 3 : ℝ) * δ :=
            hrhs_eval
      _ ≤ (4 / 3 : ℝ) * ρ + (4 / 3 : ℝ) * δ := by nlinarith
  refine ⟨by norm_num, ?_, ?_⟩
  · calc
      ∫ sample, lawRegret P (πt sample) ∂(Measure.pi (fun _ : Fin n => P.dataMeasure))
          = ∫ sample, lawRegret P (πt sample) ∂μn := rfl
      _ ≤ (4 / 3 : ℝ) * ρ + (4 / 3 : ℝ) * δ := hmain
      _ = (4 / 3 : ℝ) * (ρ + δ) := by ring
      _ ≤ (8 / 3 : ℝ) * (ρ + δ) := by
            have hρδ : 0 ≤ ρ + δ := add_nonneg hρ_nonneg hδ_nonneg
            nlinarith
      _ = (8 / 3 : ℝ) *
            (Coff * ((B ^ 2 / (n : ℝ)) ^ (Aalpha α) * (Real.log n) ^ p) + δ) := by
            simp [ρ]
  · intro hδ_le
    calc
      ∫ sample, lawRegret P (πt sample) ∂(Measure.pi (fun _ : Fin n => P.dataMeasure))
          = ∫ sample, lawRegret P (πt sample) ∂μn := rfl
      _ ≤ (4 / 3 : ℝ) * ρ + (4 / 3 : ℝ) * δ := hmain
      _ ≤ (4 / 3 : ℝ) * ρ + (4 / 3 : ℝ) * (n : ℝ)⁻¹ := by nlinarith
      _ ≤ (4 / 3 : ℝ) * ρ + (4 / 3 : ℝ) * ρ := by
            have hlarge' : (n : ℝ)⁻¹ ≤ ρ := by simpa [ρ] using hlarge
            nlinarith
      _ = (8 / 3 : ℝ) * ρ := by ring
      _ = (8 / 3 : ℝ) *
            (Coff * ((B ^ 2 / (n : ℝ)) ^ (Aalpha α) * (Real.log n) ^ p)) := by
            simp [ρ, mul_assoc]


end CausalSmith.Stat.PolicyRegretMarginOverlap
