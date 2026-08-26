/- Fixed-selector heavy/light risk assembly for the polynomial program. -/

import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.PolynomialUpper.HeavyRisk
import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.PolynomialUpper.FixedLightRisk

namespace CausalSmith.Stat.DiscreteAteHeterogeneityFrontier

open MeasureTheory ProbabilityTheory
open Causalean.Stat
open Causalean.Stat.FiniteStratumMarkedRatioMse

-- @node: polynomialFixedBranchNormalizedError
/-- The normalized error of a deterministic heavy set and its complementary
light set, both evaluated on one independent block. -/
noncomputable def polynomialFixedBranchNormalizedError {d m K : ℕ}
    (P : RealLaw d) (M B : ℝ) (H : Finset (Fin d))
    (z : Fin m → Obs d) : ℝ :=
  (fixedStratumMarkedRatio (fun o : Obs d => o.x) (fun o => o.a)
      (fun o => o.y) H z -
    fixedStratumMarkedTarget P.observedLaw (fun o : Obs d => o.x)
      (fun o => o.a) (fun o => o.y) H) / M +
  (allBlockMarkedPolynomialSum M B K (Finset.univ \ H) z -
    ∑ k ∈ Finset.univ \ H, P.cellMass k * cellEffect P k / M)

-- @node: polynomialFixedBranchNormalizedError_sq_integrable
/-- [Every deterministic normalized branch has an integrable square under the finite product
  law](goal). -/
lemma polynomialFixedBranchNormalizedError_sq_integrable {d m K : ℕ}
    {epsilon M sigma B : ℝ} (P : ModelClass d epsilon M sigma)
    (H : Finset (Fin d)) :
    Integrable (fun z : Fin m → Obs d =>
      (polynomialFixedBranchNormalizedError (K := K) P.law M B H z) ^ 2)
      (productLaw m P.law) := by
  let heavy : (Fin m → Obs d) → ℝ := fun z =>
    (fixedStratumMarkedRatio (fun o : Obs d => o.x) (fun o => o.a)
        (fun o => o.y) H z -
      fixedStratumMarkedTarget P.law.observedLaw (fun o : Obs d => o.x)
        (fun o => o.a) (fun o => o.y) H) / M
  let light : (Fin m → Obs d) → ℝ := fun z =>
    allBlockMarkedPolynomialSum M B K (Finset.univ \ H) z -
      ∑ k ∈ Finset.univ \ H, P.law.cellMass k * cellEffect P.law k / M
  have htuple : Measurable (fun o : Obs d => (o.x, o.a, o.y)) :=
    measurable_iff_comap_le.mpr le_rfl
  have hx : Measurable (fun o : Obs d => o.x) := measurable_fst.comp htuple
  have ha : Measurable (fun o : Obs d => o.a) :=
    measurable_fst.comp (measurable_snd.comp htuple)
  have hy : Measurable (fun o : Obs d => o.y) :=
    measurable_snd.comp (measurable_snd.comp htuple)
  have hheavyLp : MemLp heavy 2 (productLaw m P.law) := by
    have hratio : MemLp (fun z : Fin m → Obs d =>
        fixedStratumMarkedRatio (fun o : Obs d => o.x) (fun o => o.a)
            (fun o => o.y) H z -
          fixedStratumMarkedTarget P.law.observedLaw
            (fun o : Obs d => o.x) (fun o => o.a) (fun o => o.y) H)
        2 (productLaw m P.law) := by
      unfold productLaw
      exact (fixedStratumMarkedRatio_memLp_two (m := m) P.law.observedLaw
        (fun o : Obs d => o.x) (fun o => o.a) (fun o => o.y)
        (polynomialSupportedCenter P.law) H hx ha hy
        (polynomialSupportedCenter_residual_memLp P)).sub (memLp_const _)
    simpa [heavy, div_eq_mul_inv, mul_comm] using hratio.const_mul (M⁻¹)
  have hlightLp : MemLp light 2 (productLaw m P.law) :=
    (memLp_allBlockMarkedPolynomialSum_finite P (Finset.univ \ H)).sub
      (memLp_const _)
  change Integrable (fun z => (heavy z + light z) ^ 2) _
  exact (hheavyLp.add hlightLp).integrable_sq

-- @node: polynomialFixedBranchNormalizedError_sq_integral_le
/-- [The fixed-heavy marked-ratio bound and fixed-light factorial-moment bound combine into a
  single deterministic-selector risk inequality](goal). -/
lemma polynomialFixedBranchNormalizedError_sq_integral_le :
    ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 / 2 →
    ∃ C_epsilon : ℝ, 0 < C_epsilon ∧
    ∀ d m K : ℕ, ∀ M sigma B lowerBand : ℝ,
      ∀ P : ModelClass d epsilon M sigma, ∀ H : Finset (Fin d),
      2 ≤ K → 0 < B → 0 < lowerBand →
      (∀ k ∈ H, lowerBand ≤ P.law.cellMass k) →
      (∀ k ∉ H, P.law.cellMass k ≤ B / 4) →
      4 * (K + 2) ^ 2 ≤ m →
      (4 : ℝ) * (K + 2) / m ≤ 3 * B / 4 →
      ∫ z : Fin m → Obs d,
          (polynomialFixedBranchNormalizedError (K := K) P.law M B H z) ^ 2
          ∂(productLaw m P.law) ≤
        8 * (8 * (∑ k ∈ H, P.law.cellMass k) /
              (safeSampleSize m * epsilon) +
            6 / safeSampleSize m +
            4 * (lowerMassMissingEnvelope P.law.observedLaw
              (fun o : Obs d => o.x) m epsilon lowerBand H) ^ 2) +
        2 * (C_epsilon / m + C_epsilon * 6 ^ (2 * K) *
          ((d : ℝ) * B ^ 2 + (d : ℝ) ^ 2 * K ^ 2 * B ^ 2 / m) +
          (((Finset.univ \ H).card : ℝ) *
            (B / (epsilon * (K : ℝ) ^ 2))) ^ 2) := by
  intro epsilon hepsilon hepsilon_half
  obtain ⟨C_epsilon, hC, hlight⟩ :=
    fixedLightMarkedPolynomial_error_sq_le epsilon hepsilon hepsilon_half
  refine ⟨C_epsilon, hC, ?_⟩
  intro d m K M sigma B lowerBand P H hK hB hlower hheavy hlightMass hm hshift
  let heavy : (Fin m → Obs d) → ℝ := fun z =>
    (fixedStratumMarkedRatio (fun o : Obs d => o.x) (fun o => o.a)
        (fun o => o.y) H z -
      fixedStratumMarkedTarget P.law.observedLaw (fun o : Obs d => o.x)
        (fun o => o.a) (fun o => o.y) H) / M
  let light : (Fin m → Obs d) → ℝ := fun z =>
    allBlockMarkedPolynomialSum M B K (Finset.univ \ H) z -
      ∑ k ∈ Finset.univ \ H,
        P.law.cellMass k * cellEffect P.law k / M
  have hM : M ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one P.M_ge_one)
  have hheavyRisk := fixedHeavyMarkedRatio_error_sq_le (m := m) P H hheavy
  have hmass (k : Fin d) :
      categoryMass P.law.observedLaw
          (fun o : Obs d => o.x) k = P.law.cellMass k := by
    simpa [categoryMass, categoryEvent, groupEvent, realMass] using
      (P.law.cellMass_eq k).symm
  simp_rw [hmass] at hheavyRisk
  have hheavyNorm :
      ∫ z : Fin m → Obs d, (heavy z) ^ 2 ∂(productLaw m P.law) ≤
        4 * (8 * (∑ k ∈ H, P.law.cellMass k) /
              (safeSampleSize m * epsilon) +
            6 / safeSampleSize m +
            4 * (lowerMassMissingEnvelope P.law.observedLaw
              (fun o : Obs d => o.x) m epsilon lowerBand H) ^ 2) := by
    dsimp [heavy]
    simp_rw [div_pow]
    simp_rw [div_eq_mul_inv]
    rw [integral_mul_const]
    have hM2 : 0 < M ^ 2 := sq_pos_of_ne_zero hM
    let R : ℝ := 8 * (∑ k ∈ H, P.law.cellMass k) /
          (safeSampleSize m * epsilon) +
        6 / safeSampleSize m +
        4 * (lowerMassMissingEnvelope P.law.observedLaw
          (fun o : Obs d => o.x) m epsilon lowerBand H) ^ 2
    have hrisk :
        ∫ z : Fin m → Obs d,
            (fixedStratumMarkedRatio (fun o : Obs d => o.x) (fun o => o.a)
                (fun o => o.y) H z -
              fixedStratumMarkedTarget P.law.observedLaw
                (fun o : Obs d => o.x) (fun o => o.a)
                (fun o => o.y) H) ^ 2 ∂(productLaw m P.law) ≤
          4 * M ^ 2 * R := by
      simpa [R] using hheavyRisk
    change (∫ z : Fin m → Obs d,
        (fixedStratumMarkedRatio (fun o : Obs d => o.x) (fun o => o.a)
            (fun o => o.y) H z -
          fixedStratumMarkedTarget P.law.observedLaw
            (fun o : Obs d => o.x) (fun o => o.a)
            (fun o => o.y) H) ^ 2 ∂(productLaw m P.law)) * (M ^ 2)⁻¹ ≤ 4 * R
    calc
      (∫ z : Fin m → Obs d,
          (fixedStratumMarkedRatio (fun o : Obs d => o.x) (fun o => o.a)
              (fun o => o.y) H z -
            fixedStratumMarkedTarget P.law.observedLaw
              (fun o : Obs d => o.x) (fun o => o.a)
              (fun o => o.y) H) ^ 2 ∂(productLaw m P.law)) * (M ^ 2)⁻¹ ≤
          (4 * M ^ 2 * R) * (M ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_right hrisk (inv_nonneg.mpr (sq_nonneg M))
      _ = 4 * R * (M ^ 2 * (M ^ 2)⁻¹) := by ring
      _ = 4 * R := by rw [mul_inv_cancel₀ hM2.ne', mul_one]
  have hlightSet : ∀ k ∈ Finset.univ \ H,
      P.law.cellMass k ≤ B / 4 := by
    intro k hk
    exact hlightMass k (Finset.mem_sdiff.mp hk).2
  have hlightRisk := hlight d m K M sigma B P (Finset.univ \ H)
    hK hB hlightSet hm hshift
  have htuple : Measurable (fun o : Obs d => (o.x, o.a, o.y)) :=
    measurable_iff_comap_le.mpr le_rfl
  have hx : Measurable (fun o : Obs d => o.x) := measurable_fst.comp htuple
  have ha : Measurable (fun o : Obs d => o.a) :=
    measurable_fst.comp (measurable_snd.comp htuple)
  have hy : Measurable (fun o : Obs d => o.y) :=
    measurable_snd.comp (measurable_snd.comp htuple)
  have hheavyLp : MemLp heavy 2 (productLaw m P.law) := by
    have hratio : MemLp (fun z : Fin m → Obs d =>
        fixedStratumMarkedRatio (fun o : Obs d => o.x) (fun o => o.a)
            (fun o => o.y) H z -
          fixedStratumMarkedTarget P.law.observedLaw
            (fun o : Obs d => o.x) (fun o => o.a) (fun o => o.y) H)
        2 (productLaw m P.law) := by
      unfold productLaw
      exact (fixedStratumMarkedRatio_memLp_two (m := m) P.law.observedLaw
        (fun o : Obs d => o.x) (fun o => o.a) (fun o => o.y)
        (polynomialSupportedCenter P.law) H hx ha hy
        (polynomialSupportedCenter_residual_memLp P)).sub
          (memLp_const (fixedStratumMarkedTarget P.law.observedLaw
            (fun o : Obs d => o.x) (fun o => o.a) (fun o => o.y) H))
    simpa [heavy, div_eq_mul_inv, mul_comm] using hratio.const_mul (M⁻¹)
  have hlightLp : MemLp light 2 (productLaw m P.law) :=
    (memLp_allBlockMarkedPolynomialSum_finite P (Finset.univ \ H)).sub
      (memLp_const _)
  have hsumInt : Integrable (fun z => (heavy z + light z) ^ 2)
      (productLaw m P.law) := (hheavyLp.add hlightLp).integrable_sq
  have hrightInt : Integrable
      (fun z => 2 * heavy z ^ 2 + 2 * light z ^ 2)
      (productLaw m P.law) :=
    hheavyLp.integrable_sq.const_mul 2 |>.add
      (hlightLp.integrable_sq.const_mul 2)
  change (∫ z : Fin m → Obs d, (heavy z + light z) ^ 2
      ∂(productLaw m P.law)) ≤ _
  calc
    (∫ z : Fin m → Obs d, (heavy z + light z) ^ 2
        ∂(productLaw m P.law)) ≤
        ∫ z : Fin m → Obs d, 2 * heavy z ^ 2 + 2 * light z ^ 2
          ∂(productLaw m P.law) := by
      apply integral_mono hsumInt hrightInt
      intro z
      nlinarith [sq_nonneg (heavy z - light z)]
    _ = 2 * (∫ z : Fin m → Obs d, heavy z ^ 2
          ∂(productLaw m P.law)) +
        2 * (∫ z : Fin m → Obs d, light z ^ 2
          ∂(productLaw m P.law)) := by
      rw [integral_add, integral_const_mul, integral_const_mul]
      · exact hheavyLp.integrable_sq.const_mul 2
      · exact hlightLp.integrable_sq.const_mul 2
    _ ≤ _ := by nlinarith [hheavyNorm, hlightRisk]

end CausalSmith.Stat.DiscreteAteHeterogeneityFrontier
