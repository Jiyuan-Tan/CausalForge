/- Uniform deterministic-branch simplification of the fixed heavy/light risk. -/

import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.PolynomialUpper.SelectorRisk

namespace CausalSmith.Stat.DiscreteAteHeterogeneityFrontier

open MeasureTheory Causalean.Stat
open Causalean.Stat.FiniteStratumMarkedRatioMse

-- @node: polynomial_fixedBranch_uniform_bound
/-- [every fixed heavy-set branch of the polynomial estimator obeys the stated uniform
  normalized-risk bound](goal). -/
lemma polynomial_fixedBranch_uniform_bound :
    ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 / 2 →
    ∃ C_epsilon : ℝ, 0 < C_epsilon ∧
    ∀ n d : ℕ, ∀ M sigma lowerBand upperBand : ℝ,
      ∀ P : ModelClass d epsilon M sigma, ∀ H : Finset (Fin d),
      polynomialSelectorEligible P.law lowerBand upperBand H →
      2 ≤ polynomialDegree n → 0 < lowerBand → 2 ≤ n →
      upperBand ≤ (4096 * logEN n / (n - n / 2 : ℕ)) / 4 →
      4 * (polynomialDegree n + 2) ^ 2 ≤ n - n / 2 →
      (4 : ℝ) * (polynomialDegree n + 2) / (n - n / 2 : ℕ) ≤
        3 * (4096 * logEN n / (n - n / 2 : ℕ)) / 4 →
      ∫ z : Fin (n - n / 2) → Obs d,
          (polynomialFixedBranchNormalizedError (K := polynomialDegree n)
            P.law M (4096 * logEN n / (n - n / 2 : ℕ)) H z) ^ 2
          ∂(productLaw (n - n / 2) P.law) ≤
        8 * (8 / (((n - n / 2 : ℕ) : ℝ) * epsilon) +
          6 / (n - n / 2 : ℕ) +
          4 * ((d : ℝ) /
            (((((n - n / 2 - 2 : ℕ) : ℝ) / 2 * epsilon) ^ 2) *
              lowerBand)) ^ 2) +
        2 * (C_epsilon / (n - n / 2 : ℕ) +
          C_epsilon * 6 ^ (2 * polynomialDegree n) *
            ((d : ℝ) * (4096 * logEN n / (n - n / 2 : ℕ)) ^ 2 +
              (d : ℝ) ^ 2 * polynomialDegree n ^ 2 *
                (4096 * logEN n / (n - n / 2 : ℕ)) ^ 2 /
                  (n - n / 2 : ℕ)) +
          ((d : ℝ) * ((4096 * logEN n / (n - n / 2 : ℕ)) /
            (epsilon * (polynomialDegree n : ℝ) ^ 2))) ^ 2) := by
  intro epsilon hepsilon hepsilon_half
  obtain ⟨C, hC, hfixed⟩ :=
    polynomialFixedBranchNormalizedError_sq_integral_le epsilon hepsilon
      hepsilon_half
  refine ⟨C, hC, ?_⟩
  intro n d M sigma lowerBand upperBand P H helig hK hlower hn
    hupper hm hshift
  let m := n - n / 2
  let B := 4096 * logEN n / (n - n / 2 : ℕ)
  have hmpos : 0 < m := by dsimp [m]; omega
  have hm3 : 3 ≤ m := by
    have hk4 : 4 ≤ polynomialDegree n + 2 := by omega
    have hsquare : 16 ≤ (polynomialDegree n + 2) ^ 2 := by
      nlinarith [Nat.mul_self_le_mul_self hk4]
    have h64 : 64 ≤ 4 * (polynomialDegree n + 2) ^ 2 := by omega
    exact (by omega : 3 ≤ 64).trans (h64.trans hm)
  have hB : 0 < B := by
    dsimp [B]
    exact polynomial_lightScale_pos (by omega)
  have hheavy : ∀ k ∈ H, lowerBand ≤ P.law.cellMass k := helig.1
  have hlight : ∀ k ∉ H, P.law.cellMass k ≤ B / 4 := by
    intro k hk
    exact (helig.2 k hk).trans hupper
  have hbase := hfixed d m (polynomialDegree n) M sigma B lowerBand P H
    hK hB hlower hheavy hlight hm hshift
  apply hbase.trans
  have hmass : ∑ k ∈ H, P.law.cellMass k ≤ 1 := by
    rw [← sum_cellMass_eq_one P.law]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ H)
      (fun k _ _ => (P.law.cellMass_range k).1)
  have hcardH : (H.card : ℝ) ≤ d := by
    have hc := Finset.card_le_card (Finset.subset_univ H)
    simpa using hc
  have hcardLight : ((Finset.univ \ H).card : ℝ) ≤ d := by
    have hc := Finset.card_le_card (Finset.sdiff_subset (s := Finset.univ) (t := H))
    simpa using hc
  have hden : 0 < (((((m - 2 : ℕ) : ℝ) / 2 * epsilon) ^ 2) * lowerBand) := by
    have : 0 < m - 2 := by omega
    positivity
  have henv : lowerMassMissingEnvelope P.law.observedLaw
      (fun o : Obs d => o.x) m epsilon lowerBand H ≤
      (d : ℝ) / (((((m - 2 : ℕ) : ℝ) / 2 * epsilon) ^ 2) * lowerBand) := by
    rw [lowerMassMissingEnvelope_eq_of_pos P.law.observedLaw
      (fun o : Obs d => o.x) H hm3 hepsilon hlower]
    exact (div_le_div_iff_of_pos_right hden).2 hcardH
  have henv0 : 0 ≤ lowerMassMissingEnvelope P.law.observedLaw
      (fun o : Obs d => o.x) m epsilon lowerBand H := by
    rw [lowerMassMissingEnvelope_eq_of_pos P.law.observedLaw
      (fun o : Obs d => o.x) H hm3 hepsilon hlower]
    positivity
  have hsafe : safeSampleSize m = (m : ℝ) := by
    unfold safeSampleSize
    rw [max_eq_right (by omega)]
  rw [hsafe]
  dsimp [m, B] at hmass hcardLight henv henv0 hden ⊢
  gcongr
  · nlinarith

end CausalSmith.Stat.DiscreteAteHeterogeneityFrontier
