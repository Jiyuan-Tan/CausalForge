/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Envelope evaluation for the unbounded dispersion certificate
-/

import CausalSmith.Experimentation.EXP_BipartiteMinimaxDesign_Research.Helpers.DispersionDesign

set_option linter.style.longLine false

open scoped BigOperators
open Finset

namespace CausalSmith.Experimentation.BipartiteMinimaxDesign

-- @node: dispersionHomogeneous_envelope
/-- Gives the exact variance-envelope value of the homogeneous dispersion design. -/
lemma dispersionHomogeneous_envelope (n : ℕ) (ε : ℝ) :
    (dispersionExperiment n).varEnvelope (dispersionHomogeneousDesign n ε) / 4 =
      (Fintype.card (DispersionOutcome n) : ℝ)⁻¹ *
        ((dispersionD n : ℝ) ^ 2 *
            ((dispersionRho ε)⁻¹ ^ dispersionD n +
              (1 - dispersionRho ε)⁻¹ ^ dispersionD n) +
          (2 * dispersionD n : ℕ) * (dispersionT n : ℝ) ^ 2 *
            reciprocalBarrier (dispersionRho ε)) := by
  classical
  have hcore (i j : Fin (dispersionD n)) :
      (dispersionExperiment n).r1 (dispersionHomogeneousDesign n ε) (Sum.inl i) (Sum.inl j) +
          (dispersionExperiment n).r0 (dispersionHomogeneousDesign n ε) (Sum.inl i) (Sum.inl j) +
          2 * (dispersionExperiment n).r10 (Sum.inl i) (Sum.inl j) =
        (dispersionRho ε)⁻¹ ^ dispersionD n +
          (1 - dispersionRho ε)⁻¹ ^ dispersionD n := by
    unfold BipartiteExperiment.r1 BipartiteExperiment.r0 BipartiteExperiment.r10
    simp [dispersionExperiment_shared_core, dispersionHomogeneousDesign, dispersionCore,
      dispersionD_pos]
    ring
  have hcross (i : Fin (dispersionD n))
      (f : Fin (2 * dispersionD n)) (r : Fin (dispersionT n)) :
      (dispersionExperiment n).r1 (dispersionHomogeneousDesign n ε) (Sum.inl i) (Sum.inr (f, r)) +
          (dispersionExperiment n).r0 (dispersionHomogeneousDesign n ε) (Sum.inl i) (Sum.inr (f, r)) +
          2 * (dispersionExperiment n).r10 (Sum.inl i) (Sum.inr (f, r)) = 0 := by
    simp [BipartiteExperiment.r1, BipartiteExperiment.r0, BipartiteExperiment.r10,
      dispersionExperiment_shared_core_filler]
  have hcross' (f : Fin (2 * dispersionD n)) (r : Fin (dispersionT n))
      (i : Fin (dispersionD n)) :
      (dispersionExperiment n).r1 (dispersionHomogeneousDesign n ε) (Sum.inr (f, r)) (Sum.inl i) +
          (dispersionExperiment n).r0 (dispersionHomogeneousDesign n ε) (Sum.inr (f, r)) (Sum.inl i) +
          2 * (dispersionExperiment n).r10 (Sum.inr (f, r)) (Sum.inl i) = 0 := by
    simp [BipartiteExperiment.r1, BipartiteExperiment.r0, BipartiteExperiment.r10,
      dispersionExperiment_shared_filler_core]
  have hfiller (f g : Fin (2 * dispersionD n))
      (r s : Fin (dispersionT n)) :
      (dispersionExperiment n).r1 (dispersionHomogeneousDesign n ε) (Sum.inr (f, r)) (Sum.inr (g, s)) +
          (dispersionExperiment n).r0 (dispersionHomogeneousDesign n ε) (Sum.inr (f, r)) (Sum.inr (g, s)) +
          2 * (dispersionExperiment n).r10 (Sum.inr (f, r)) (Sum.inr (g, s)) =
        if f = g then reciprocalBarrier (dispersionRho ε) else 0 := by
    by_cases h : f = g
    · subst g
      simp [BipartiteExperiment.r1, BipartiteExperiment.r0, BipartiteExperiment.r10,
        dispersionExperiment_shared_filler, dispersionHomogeneousDesign, reciprocalBarrier]
      ring
    · simp [BipartiteExperiment.r1, BipartiteExperiment.r0, BipartiteExperiment.r10,
        dispersionExperiment_shared_filler, h]
  unfold BipartiteExperiment.varEnvelope
  rw [Fintype.sum_sum_type]
  simp_rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp_rw [hcore, hcross, hcross', hfiller]
  simp
  ring

-- @node: dispersionComparison_envelope
/-- Gives the exact variance-envelope value of the clique-and-filler comparison design. -/
lemma dispersionComparison_envelope (n : ℕ) (ε : ℝ) :
    (dispersionExperiment n).varEnvelope (dispersionComparisonDesign n ε) / 4 =
      (Fintype.card (DispersionOutcome n) : ℝ)⁻¹ *
        ((dispersionD n : ℝ) ^ 2 * (2 : ℝ) ^ (dispersionD n + 1) +
          (2 * dispersionD n : ℕ) * (dispersionT n : ℝ) ^ 2 *
            reciprocalBarrier (dispersionFillerRho ε)) := by
  classical
  have hcore (i j : Fin (dispersionD n)) :
      (dispersionExperiment n).r1 (dispersionComparisonDesign n ε) (Sum.inl i) (Sum.inl j) +
          (dispersionExperiment n).r0 (dispersionComparisonDesign n ε) (Sum.inl i) (Sum.inl j) +
          2 * (dispersionExperiment n).r10 (Sum.inl i) (Sum.inl j) =
        (2 : ℝ) ^ (dispersionD n + 1) := by
    unfold BipartiteExperiment.r1 BipartiteExperiment.r0 BipartiteExperiment.r10
    simp [dispersionExperiment_shared_core, dispersionComparisonDesign, dispersionCore,
      dispersionD_pos]
    rw [← inv_pow]
    norm_num
    rw [pow_succ]
    ring_nf
    rw [mul_comm ((2 : ℝ) ^ dispersionD n) 2, two_mul]
    rfl
  have hcross (i : Fin (dispersionD n))
      (f : Fin (2 * dispersionD n)) (r : Fin (dispersionT n)) :
      (dispersionExperiment n).r1 (dispersionComparisonDesign n ε) (Sum.inl i) (Sum.inr (f, r)) +
          (dispersionExperiment n).r0 (dispersionComparisonDesign n ε) (Sum.inl i) (Sum.inr (f, r)) +
          2 * (dispersionExperiment n).r10 (Sum.inl i) (Sum.inr (f, r)) = 0 := by
    simp [BipartiteExperiment.r1, BipartiteExperiment.r0, BipartiteExperiment.r10,
      dispersionExperiment_shared_core_filler]
  have hcross' (f : Fin (2 * dispersionD n)) (r : Fin (dispersionT n))
      (i : Fin (dispersionD n)) :
      (dispersionExperiment n).r1 (dispersionComparisonDesign n ε) (Sum.inr (f, r)) (Sum.inl i) +
          (dispersionExperiment n).r0 (dispersionComparisonDesign n ε) (Sum.inr (f, r)) (Sum.inl i) +
          2 * (dispersionExperiment n).r10 (Sum.inr (f, r)) (Sum.inl i) = 0 := by
    simp [BipartiteExperiment.r1, BipartiteExperiment.r0, BipartiteExperiment.r10,
      dispersionExperiment_shared_filler_core]
  have hfiller (f g : Fin (2 * dispersionD n))
      (r s : Fin (dispersionT n)) :
      (dispersionExperiment n).r1 (dispersionComparisonDesign n ε) (Sum.inr (f, r)) (Sum.inr (g, s)) +
          (dispersionExperiment n).r0 (dispersionComparisonDesign n ε) (Sum.inr (f, r)) (Sum.inr (g, s)) +
          2 * (dispersionExperiment n).r10 (Sum.inr (f, r)) (Sum.inr (g, s)) =
        if f = g then reciprocalBarrier (dispersionFillerRho ε) else 0 := by
    by_cases h : f = g
    · subst g
      simp [BipartiteExperiment.r1, BipartiteExperiment.r0, BipartiteExperiment.r10,
        dispersionExperiment_shared_filler, dispersionComparisonDesign, reciprocalBarrier]
      ring
    · simp [BipartiteExperiment.r1, BipartiteExperiment.r0, BipartiteExperiment.r10,
        dispersionExperiment_shared_filler, h]
  unfold BipartiteExperiment.varEnvelope
  rw [Fintype.sum_sum_type]
  simp_rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp_rw [hcore, hcross, hcross', hfiller]
  simp
  ring

-- @node: reciprocalBarrier_pos
/-- The reciprocal barrier is strictly positive for every propensity strictly between zero and one. -/
lemma reciprocalBarrier_pos {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    0 < reciprocalBarrier x := by
  unfold reciprocalBarrier
  exact add_pos (inv_pos.mpr hx0) (inv_pos.mpr (sub_pos.mpr hx1))

-- @node: dispersion_envMin_pos
/-- The minimum envelope value in the dispersion construction is strictly positive. -/
lemma dispersion_envMin_pos (n : ℕ) {ε : ℝ} (hε : EpsilonAdmissible ε) :
    0 < envMin (dispersionExperiment n) ε (dispersionBudget n ε) := by
  let E := dispersionExperiment n
  let B := dispersionBudget n ε
  let po := optimalDesign E ε B
  have hB := dispersionBudget_admissible n hε
  have hopt := optimalDesign_feasible_minimizes E ε B hε.1 hε.2 hB
  have hsand := (surrogate_certificate E ε B (dispersionD n : ℝ) hε.1 hε.2
    (dispersionExperiment_boundedOutcomeDegree n) hB).1 po hopt.1
  have hp0 : ∀ k, 0 < po k := fun k => lt_of_lt_of_le hε.1 (hopt.1.floor k).1
  have hp1 : ∀ k, po k < 1 := fun k => by
    linarith [(hopt.1.floor k).2, hε.1]
  let k0 : DispersionIntervention n := Sum.inl ⟨0, dispersionD_pos n⟩
  have hsum : 0 < ∑ k, reciprocalBarrier (po k) := by
    apply Finset.sum_pos
    · intro k hk
      exact reciprocalBarrier_pos (hp0 k) (hp1 k)
    · exact ⟨k0, mem_univ k0⟩
  have hA : 0 < E.surrogateObjective po := by
    rw [dispersion_surrogateObjective_eq_weighted_sum]
    have hO : Nonempty (DispersionOutcome n) :=
      ⟨Sum.inl ⟨0, dispersionD_pos n⟩⟩
    exact mul_pos
      (mul_pos (inv_pos.mpr (Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr hO)))
        (Nat.cast_pos.mpr (dispersionD_pos n))) hsum
  unfold envMin
  change 0 < E.varEnvelope po
  nlinarith [hsand.1]

-- @node: dispersion_approxRatio_ge_envelopeRatio
/-- The dispersion approximation ratio is at least the ratio of the homogeneous design's envelope to the comparison design's envelope. -/
lemma dispersion_approxRatio_ge_envelopeRatio (n : ℕ) {ε : ℝ}
    (hε : EpsilonAdmissible ε) :
    (dispersionExperiment n).varEnvelope (dispersionHomogeneousDesign n ε) /
        (dispersionExperiment n).varEnvelope (dispersionComparisonDesign n ε) ≤
      approxRatio (dispersionExperiment n) ε (dispersionBudget n ε) := by
  let E := dispersionExperiment n
  let B := dispersionBudget n ε
  have hminpos := dispersion_envMin_pos n hε
  have hopt := optimalDesign_feasible_minimizes E ε B hε.1 hε.2
    (dispersionBudget_admissible n hε)
  have hcmp := dispersionComparisonDesign_feasible n hε
  have hminle : envMin E ε B ≤ E.varEnvelope (dispersionComparisonDesign n ε) := by
    exact hopt.2 _ hcmp
  have hcmppos : 0 < E.varEnvelope (dispersionComparisonDesign n ε) :=
    lt_of_lt_of_le hminpos hminle
  have hhomnonneg : 0 ≤ E.varEnvelope (dispersionHomogeneousDesign n ε) := by
    rw [show E.varEnvelope (dispersionHomogeneousDesign n ε) =
      4 * (E.varEnvelope (dispersionHomogeneousDesign n ε) / 4) by ring,
      dispersionHomogeneous_envelope]
    have hr := dispersionRho_bounds hε
    have hr0 : 0 < dispersionRho ε := lt_trans hε.1 hr.1
    have hr1 : dispersionRho ε < 1 := lt_trans hr.2 (by norm_num)
    have hO : Nonempty (DispersionOutcome n) :=
      ⟨Sum.inl ⟨0, dispersionD_pos n⟩⟩
    have hc : 0 ≤ (Fintype.card (DispersionOutcome n) : ℝ)⁻¹ :=
      (inv_pos.mpr (Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr hO))).le
    have hmain : 0 ≤ (dispersionD n : ℝ) ^ 2 *
        ((dispersionRho ε)⁻¹ ^ dispersionD n +
          (1 - dispersionRho ε)⁻¹ ^ dispersionD n) := by
      exact mul_nonneg (sq_nonneg _) (add_nonneg
        (pow_nonneg (inv_nonneg.mpr hr0.le) _)
        (pow_nonneg (inv_nonneg.mpr (sub_nonneg.mpr hr1.le)) _))
    have hfill : 0 ≤ (2 * dispersionD n : ℕ) * (dispersionT n : ℝ) ^ 2 *
        reciprocalBarrier (dispersionRho ε) := by
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
        (reciprocalBarrier_pos hr0 hr1).le
    exact mul_nonneg (by norm_num) (mul_nonneg hc (add_nonneg hmain hfill))
  unfold approxRatio
  rw [if_pos hminpos, dispersion_surrogateDesign_eq_homogeneous n hε]
  exact div_le_div_of_nonneg_left hhomnonneg hminpos hminle

-- @node: dispersion_approxRatio_lower_bound
/-- The dispersion approximation ratio admits the stated explicit lower bound. -/
lemma dispersion_approxRatio_lower_bound (n : ℕ) {ε : ℝ}
    (hε : EpsilonAdmissible ε) :
    (dispersionRho ε)⁻¹ ^ dispersionD n /
        ((2 : ℝ) ^ (dispersionD n + 1) +
          2 * reciprocalBarrier (dispersionFillerRho ε)) ≤
      approxRatio (dispersionExperiment n) ε (dispersionBudget n ε) := by
  have hratio := dispersion_approxRatio_ge_envelopeRatio n hε
  apply le_trans ?_ hratio
  let E := dispersionExperiment n
  let ph := dispersionHomogeneousDesign n ε
  let pc := dispersionComparisonDesign n ε
  have hpc : 0 < E.varEnvelope pc := by
    have hm := dispersion_envMin_pos n hε
    have ho := optimalDesign_feasible_minimizes E ε (dispersionBudget n ε)
      hε.1 hε.2 (dispersionBudget_admissible n hε)
    exact lt_of_lt_of_le hm (ho.2 pc (dispersionComparisonDesign_feasible n hε))
  have hden : 0 < (2 : ℝ) ^ (dispersionD n + 1) +
      2 * reciprocalBarrier (dispersionFillerRho ε) := by
    have hf := dispersionFillerRho_bounds hε
    have hf1 : dispersionFillerRho ε < 1 := lt_trans hf.2 (by norm_num)
    exact add_pos (pow_pos (by norm_num) _)
      (mul_pos (by norm_num) (reciprocalBarrier_pos (lt_trans hε.1 hf.1) hf1))
  rw [div_le_div_iff₀ hden hpc]
  rw [show E.varEnvelope pc = 4 * (E.varEnvelope pc / 4) by ring,
    show E.varEnvelope ph = 4 * (E.varEnvelope ph / 4) by ring,
    dispersionComparison_envelope, dispersionHomogeneous_envelope]
  have hr := dispersionRho_bounds hε
  have hr0 : 0 < dispersionRho ε := lt_trans hε.1 hr.1
  have hr1 : dispersionRho ε < 1 := lt_trans hr.2 (by norm_num)
  have hcoef : 0 < (Fintype.card (DispersionOutcome n) : ℝ)⁻¹ *
      (dispersionD n : ℝ) ^ 2 := by
    have hO : Nonempty (DispersionOutcome n) :=
      ⟨Sum.inl ⟨0, dispersionD_pos n⟩⟩
    exact mul_pos (inv_pos.mpr (Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr hO)))
      (sq_pos_of_pos (Nat.cast_pos.mpr (dispersionD_pos n)))
  have hd : (dispersionD n : ℝ) = (dispersionT n : ℝ) ^ 2 := by
    simp [dispersionD]
  rw [show (2 * dispersionD n : ℕ) * (dispersionT n : ℝ) ^ 2 =
    2 * (dispersionD n : ℝ) ^ 2 by push_cast; rw [hd]; ring]
  have hY : 0 ≤ (1 - dispersionRho ε)⁻¹ ^ dispersionD n :=
    pow_nonneg (inv_nonneg.mpr (sub_nonneg.mpr hr1.le)) _
  have hR : 0 ≤ reciprocalBarrier (dispersionRho ε) :=
    (reciprocalBarrier_pos hr0 hr1).le
  have hnum : (dispersionRho ε)⁻¹ ^ dispersionD n ≤
      (dispersionRho ε)⁻¹ ^ dispersionD n +
        (1 - dispersionRho ε)⁻¹ ^ dispersionD n +
          2 * reciprocalBarrier (dispersionRho ε) := by
    nlinarith
  have hscaled := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hnum (by positivity :
      0 ≤ 4 * ((Fintype.card (DispersionOutcome n) : ℝ)⁻¹ *
        (dispersionD n : ℝ) ^ 2))) hden.le
  convert hscaled using 1 <;> ring

end CausalSmith.Experimentation.BipartiteMinimaxDesign
