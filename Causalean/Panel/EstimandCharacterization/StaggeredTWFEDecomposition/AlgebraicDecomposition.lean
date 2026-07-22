/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Goodman-Bacon (2021): TWFE decomposition under staggered timing — Layer A theorems

**Role in the folder.** ★ *Algebraic headline.* Pure finite-cell algebra, no
causal content: expresses the TWFE coefficient as a totalized weighted sum of
2x2 comparison contrasts. Its causal refinement (potential outcomes) is the
sibling headline `CausalDecomposition.lean`. See `StaggeredTWFEDecomposition.lean`
for the folder layer-map.

The five Layer A propositions (NL doc A5.1–A5.5):

* `weights_nonneg` — `λ_TN, λ_EL, λ_LE ≥ 0`.
* `raw_weight_sum_eq_VD` — denominator identity `Λ P = V_D P`.
* `twfe_numerator_eq_lambda_delta_sum` — numerator identity.
* `weights_sum_one` — normalized weights sum to one (uses `hVD_pos`).
* `twfe_eq_weighted_avg` — weighted-average identity under positive residualized
  treatment variance.

NL artifact:
`doc/basic_concepts/po/estimand_characterization/goodman_bacon_twfe_timing.md`.
Source LaTeX:
`doc/basic_concepts/po/estimand_characterization/goodman_bacon_twfe_timing.tex`.

Layer C (causal characterization, NL doc A6) is now implemented: the three
causal-characterization corollaries live in `Causal.lean` (`Δ_TN_eq_ATT`,
`Δ_EL_eq_ATT`, `Δ_LE_eq_bad_comparison`) and are fused with the weighted-sum
identity below in `CausalDecomposition.lean`.
-/

import Causalean.Panel.EstimandCharacterization.StaggeredTWFEDecomposition.Pairwise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
/-! # Goodman-Bacon Decomposition

This file establishes the finite staggered-adoption Goodman-Bacon algebraic
decomposition of a two-way fixed effects coefficient into admissible two-group
comparisons. It proves nonnegativity of the raw comparison weights, the
denominator and numerator identities, normalization of the weights under
positive residualized-treatment variance, and the corresponding weighted-average
identity. -/

namespace Causalean
namespace Panel.EstimandCharacterization
namespace StaggeredTWFEDecomposition

open Finset

variable {𝒢 : Type*} [Fintype 𝒢] [DecidableEq 𝒢] {T : ℕ}

/-- **Prop A5.1 (`weights_nonneg`).** Every admissible raw weight is
nonnegative. Pure algebra: uses `0 ≤ p_g`, `0 ≤ \overline{D}_g ≤ 1`, and
`0 ≤ q_{eℓ} ≤ 1`. -/
theorem weights_nonneg (P : CohortPanel 𝒢 T) (k : CompTag × 𝒢 × 𝒢) :
    0 ≤ lambdaWeight P k := by
  unfold lambdaWeight
  have hTpos : 0 < (T : ℝ) := by exact_mod_cast P.T_pos
  have hTnonneg : 0 ≤ (T : ℝ) := le_of_lt hTpos
  have hTne : (T : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt P.T_pos)
  have hbar_nonneg : ∀ g : 𝒢, 0 ≤ barD P g := by
    intro g
    unfold barD
    have hsum_nonneg : 0 ≤ ∑ t : Fin T, D P g t := by
      refine Finset.sum_nonneg' ?_
      intro t
      by_cases hD : AdoptionDate.le (P.A g) t
      · simp [D, hD]
      · simp [D, hD]
    simpa using (mul_nonneg (inv_nonneg.mpr hTnonneg) hsum_nonneg)
  have hbar_le_one : ∀ g : 𝒢, barD P g ≤ 1 := by
    intro g
    unfold barD
    have hsum_le : ∑ t : Fin T, D P g t ≤ (T : ℝ) := by
      have hsum_le' : (∑ t : Fin T, D P g t) ≤ (∑ t : Fin T, (1 : ℝ)) := by
        refine Finset.sum_le_sum ?_
        intro t ht
        by_cases hD : AdoptionDate.le (P.A g) t
        · simp [D, hD]
        · simp [D, hD]
      simpa using hsum_le'
    have hsum_le'' : (∑ t, D P g t) ≤ (T : ℝ) := by simpa using hsum_le
    have htmp : (T : ℝ)⁻¹ * (∑ t, D P g t) ≤ (T : ℝ)⁻¹ * (T : ℝ) :=
      mul_le_mul_of_nonneg_left hsum_le'' (inv_nonneg.mpr hTnonneg)
    simpa [barD, inv_mul_cancel₀ hTne] using htmp
  by_cases h : admissible P k
  · simp only [h, if_true]
    rcases k with ⟨tag, g, u⟩
    cases tag with
    | TN =>
        rcases h with ⟨_, _, hpg, hpu⟩
        have hmul : 0 ≤ (P.p g * P.p u) * (barD P g * (1 - barD P g)) := by
          exact mul_nonneg (mul_nonneg (le_of_lt hpg) (le_of_lt hpu))
            (mul_nonneg (hbar_nonneg g) (sub_nonneg.mpr (hbar_le_one g)))
        simpa [lambdaTN, mul_assoc, mul_left_comm, mul_comm] using hmul
    | EL =>
        rcases h with ⟨hlt, _, hpg, hpu⟩
        have hbar_mono : barD P u ≤ barD P g := by
          unfold barD
          have hsum_le : (∑ t : Fin T, D P u t) ≤ (∑ t : Fin T, D P g t) := by
            refine Finset.sum_le_sum ?_
            intro t ht
            by_cases htu : AdoptionDate.le (P.A u) t
            · have htg : AdoptionDate.le (P.A g) t :=
                le_of_lt (lt_of_lt_of_le hlt htu)
              simp [D, htu, htg]
            · by_cases htg : AdoptionDate.le (P.A g) t
              · simp [D, htu, htg]
              · simp [D, htu, htg]
          have hsum_le' : (∑ t : Fin T, D P u t) ≤ (∑ t : Fin T, D P g t) := by
            simpa using hsum_le
          exact mul_le_mul_of_nonneg_left hsum_le' (inv_nonneg.mpr hTnonneg)
        have hq_nonneg : 0 ≤ q P g u := by
          unfold q
          exact sub_nonneg.mpr hbar_mono
        have hq_le_barD : q P g u ≤ barD P g := by
          unfold q
          nlinarith [hbar_mono, hbar_nonneg u]
        have hq_le_one : q P g u ≤ 1 := le_trans hq_le_barD (hbar_le_one g)
        have h1mq_nonneg : 0 ≤ 1 - q P g u := sub_nonneg.mpr hq_le_one
        have hmu_nonneg : 0 ≤ mu P g u := by
          unfold mu
          exact div_nonneg (sub_nonneg.mpr (hbar_le_one g)) h1mq_nonneg
        have hnum_le_den : 1 - barD P g ≤ 1 - q P g u := by
          have hlu_nonneg : 0 ≤ barD P u := hbar_nonneg u
          unfold q
          linarith
        have hmu_le_one : mu P g u ≤ 1 := by
          by_cases hden : 1 - q P g u = 0
          · have hqeq : q P g u = 1 := by linarith
            simp [mu, hqeq]
          · have hden_pos : 0 < 1 - q P g u :=
              lt_of_le_of_ne h1mq_nonneg (Ne.symm hden)
            have hdiv : (1 - barD P g) / (1 - q P g u) ≤ 1 :=
              (div_le_one₀ hden_pos).2 hnum_le_den
            simpa [mu] using hdiv
        have h1m_nonneg : 0 ≤ 1 - mu P g u := sub_nonneg.mpr hmu_le_one
        have hmul : 0 ≤ P.p g * P.p u * (q P g u * (1 - q P g u) * mu P g u) := by
          have hmul1 : 0 ≤ P.p g * P.p u := mul_nonneg (le_of_lt hpg) (le_of_lt hpu)
          have hmul2 : 0 ≤ q P g u * (1 - q P g u) := mul_nonneg hq_nonneg h1mq_nonneg
          have hmul3 : 0 ≤ q P g u * (1 - q P g u) * mu P g u := mul_nonneg hmul2 hmu_nonneg
          exact mul_nonneg hmul1 hmul3
        simpa [lambdaEL, mul_assoc, mul_left_comm, mul_comm] using hmul
    | LE =>
        rcases h with ⟨hlt, _, hpg, hpu⟩
        have hbar_mono : barD P u ≤ barD P g := by
          unfold barD
          have hsum_le : (∑ t : Fin T, D P u t) ≤ (∑ t : Fin T, D P g t) := by
            refine Finset.sum_le_sum ?_
            intro t ht
            by_cases htu : AdoptionDate.le (P.A u) t
            · have htg : AdoptionDate.le (P.A g) t :=
                le_of_lt (lt_of_lt_of_le hlt htu)
              simp [D, htu, htg]
            · by_cases htg : AdoptionDate.le (P.A g) t
              · simp [D, htu, htg]
              · simp [D, htu, htg]
          have hsum_le' : (∑ t : Fin T, D P u t) ≤ (∑ t : Fin T, D P g t) := by
            simpa using hsum_le
          exact mul_le_mul_of_nonneg_left hsum_le' (inv_nonneg.mpr hTnonneg)
        have hq_nonneg : 0 ≤ q P g u := by
          unfold q
          exact sub_nonneg.mpr hbar_mono
        have hq_le_barD : q P g u ≤ barD P g := by
          unfold q
          nlinarith [hbar_mono, hbar_nonneg u]
        have hq_le_one : q P g u ≤ 1 := le_trans hq_le_barD (hbar_le_one g)
        have h1mq_nonneg : 0 ≤ 1 - q P g u := sub_nonneg.mpr hq_le_one
        have hmu_nonneg : 0 ≤ mu P g u := by
          unfold mu
          exact div_nonneg (sub_nonneg.mpr (hbar_le_one g)) h1mq_nonneg
        have hnum_le_den : 1 - barD P g ≤ 1 - q P g u := by
          have hlu_nonneg : 0 ≤ barD P u := hbar_nonneg u
          unfold q
          linarith
        have hmu_le_one : mu P g u ≤ 1 := by
          by_cases hden : 1 - q P g u = 0
          · have hqeq : q P g u = 1 := by linarith
            simp [mu, hqeq]
          · have hden_pos : 0 < 1 - q P g u :=
              lt_of_le_of_ne h1mq_nonneg (Ne.symm hden)
            have hdiv : (1 - barD P g) / (1 - q P g u) ≤ 1 := by
              exact (div_le_one₀ hden_pos).2 hnum_le_den
            simpa [mu] using hdiv
        have h1m_nonneg : 0 ≤ 1 - mu P g u := sub_nonneg.mpr hmu_le_one
        have hmul : 0 ≤ P.p g * P.p u * (q P g u * (1 - q P g u) * (1 - mu P g u)) := by
          have hmul1 : 0 ≤ P.p g * P.p u := mul_nonneg (le_of_lt hpg) (le_of_lt hpu)
          have hmul2 : 0 ≤ q P g u * (1 - q P g u) := mul_nonneg hq_nonneg h1mq_nonneg
          have hmul3 : 0 ≤ q P g u * (1 - q P g u) * (1 - mu P g u) := mul_nonneg hmul2 h1m_nonneg
          exact mul_nonneg hmul1 hmul3
        simpa [lambdaLE, mul_assoc, mul_left_comm, mul_comm] using hmul
  · simp [h]

private lemma barD_eq_zero_of_isInf (P : CohortPanel 𝒢 T) {g : 𝒢}
    (hg : AdoptionDate.isInf (P.A g)) : barD P g = 0 := by
  unfold barD D AdoptionDate.isInf AdoptionDate.le at *
  simp [hg]

private lemma lambdaTN_eq_gap_of_isInf (P : CohortPanel 𝒢 T) {g u : 𝒢}
    (hu : AdoptionDate.isInf (P.A u)) :
    lambdaTN P g u = P.p g * P.p u * q P g u * (1 - q P g u) := by
  unfold lambdaTN q
  rw [barD_eq_zero_of_isInf P hu]
  ring

private lemma lambdaEL_add_lambdaLE_eq_gap (P : CohortPanel 𝒢 T) (e ℓ : 𝒢) :
    lambdaEL P e ℓ + lambdaLE P e ℓ =
      P.p e * P.p ℓ * q P e ℓ * (1 - q P e ℓ) := by
  unfold lambdaEL lambdaLE
  ring

open Classical in
private lemma Lambda_eq_gap_sums (P : CohortPanel 𝒢 T) :
    Lambda P =
      (∑ g, ∑ u, if AdoptionDate.isFin (P.A g) ∧ AdoptionDate.isInf (P.A u) then
              P.p g * P.p u * q P g u * (1 - q P g u) else 0)
      + (∑ e, ∑ ℓ, if P.A e < P.A ℓ ∧ AdoptionDate.isFin (P.A ℓ) then
                P.p e * P.p ℓ * q P e ℓ * (1 - q P e ℓ) else 0) := by
  unfold Lambda
  congr 1
  · refine Finset.sum_congr rfl ?_
    intro g _hg
    refine Finset.sum_congr rfl ?_
    intro u _hu
    by_cases h : AdoptionDate.isFin (P.A g) ∧ AdoptionDate.isInf (P.A u)
    · simp [h, lambdaTN_eq_gap_of_isInf P h.2]
    · simp [h]
  · refine Finset.sum_congr rfl ?_
    intro e _he
    refine Finset.sum_congr rfl ?_
    intro ℓ _hℓ
    by_cases h : P.A e < P.A ℓ ∧ AdoptionDate.isFin (P.A ℓ)
    · simp [h, lambdaEL_add_lambdaLE_eq_gap P e ℓ]
    · simp [h]

private lemma D_eq_of_A_eq (P : CohortPanel 𝒢 T) {g u : 𝒢}
    (hA : P.A g = P.A u) (t : Fin T) : D P g t = D P u t := by
  unfold D
  rw [hA]

private lemma barD_eq_of_A_eq (P : CohortPanel 𝒢 T) {g u : 𝒢}
    (hA : P.A g = P.A u) : barD P g = barD P u := by
  unfold barD
  congr 1
  refine Finset.sum_congr rfl ?_
  intro t _ht
  exact D_eq_of_A_eq P hA t

private lemma centeredD_eq_of_A_eq (P : CohortPanel 𝒢 T) {g u : 𝒢}
    (hA : P.A g = P.A u) (t : Fin T) :
    centeredD P g t = centeredD P u t := by
  unfold centeredD
  rw [D_eq_of_A_eq P hA t, barD_eq_of_A_eq P hA]

private lemma vdPairContribution_eq_zero_of_A_eq (P : CohortPanel 𝒢 T) {g u : 𝒢}
    (hA : P.A g = P.A u) : vdPairContribution P g u = 0 := by
  unfold vdPairContribution
  have hsum : (∑ t : Fin T, (centeredD P g t - centeredD P u t) ^ 2) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro t _ht
    rw [centeredD_eq_of_A_eq P hA t]
    ring
  rw [hsum]
  ring

private lemma numPairContribution_eq_zero_of_A_eq (P : CohortPanel 𝒢 T) {g u : 𝒢}
    (hA : P.A g = P.A u) : numPairContribution P g u = 0 := by
  unfold numPairContribution
  have hsum :
      (∑ t : Fin T,
        (centeredD P g t - centeredD P u t) * (P.Y g t - P.Y u t)) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro t _ht
    rw [centeredD_eq_of_A_eq P hA t]
    ring
  rw [hsum]
  ring

private lemma adoption_pair_cases (P : CohortPanel 𝒢 T) (g u : 𝒢) :
    P.A g = P.A u ∨
      (AdoptionDate.isFin (P.A g) ∧ AdoptionDate.isInf (P.A u)) ∨
      (AdoptionDate.isFin (P.A u) ∧ AdoptionDate.isInf (P.A g)) ∨
      (P.A g < P.A u ∧ AdoptionDate.isFin (P.A u)) ∨
      (P.A u < P.A g ∧ AdoptionDate.isFin (P.A g)) := by
  rcases lt_trichotomy (P.A g) (P.A u) with hlt | heq | hgt
  · by_cases hu : AdoptionDate.isInf (P.A u)
    · right; left
      constructor
      · intro hg
        unfold AdoptionDate.isInf at hu
        rw [hg, hu] at hlt
        exact (lt_irrefl (⊤ : WithTop (Fin T))) hlt
      · exact hu
    · right; right; right; left
      exact ⟨hlt, hu⟩
  · left
    exact heq
  · by_cases hg : AdoptionDate.isInf (P.A g)
    · right; right; left
      constructor
      · intro hu
        unfold AdoptionDate.isInf at hg
        rw [hu, hg] at hgt
        exact (lt_irrefl (⊤ : WithTop (Fin T))) hgt
      · exact hg
    · right; right; right; right
      exact ⟨hgt, hg⟩

open Classical in
private lemma adoption_pair_pointwise (P : CohortPanel 𝒢 T) (f : 𝒢 → 𝒢 → ℝ)
    (hzero : ∀ g u, P.A g = P.A u → f g u = 0) (g u : 𝒢) :
    f g u =
      (if AdoptionDate.isFin (P.A g) ∧ AdoptionDate.isInf (P.A u) then f g u else 0) +
      (if AdoptionDate.isFin (P.A u) ∧ AdoptionDate.isInf (P.A g) then f g u else 0) +
      (if P.A g < P.A u ∧ AdoptionDate.isFin (P.A u) then f g u else 0) +
      (if P.A u < P.A g ∧ AdoptionDate.isFin (P.A g) then f g u else 0) := by
  rcases adoption_pair_cases P g u with hEq | hTN | hNT | hLT | hGT
  · rw [hzero g u hEq]
    simp [hEq, AdoptionDate.isFin, AdoptionDate.isInf]
  · rcases hTN with ⟨hgf, hui⟩
    unfold AdoptionDate.isFin at hgf
    unfold AdoptionDate.isInf at hui
    simp [AdoptionDate.isFin, AdoptionDate.isInf, hgf, hui]
  · rcases hNT with ⟨huf, hgi⟩
    unfold AdoptionDate.isFin at huf
    unfold AdoptionDate.isInf at hgi
    simp [AdoptionDate.isFin, AdoptionDate.isInf, huf, hgi]
  · rcases hLT with ⟨hlt, huf⟩
    unfold AdoptionDate.isFin at huf
    have hgf : P.A g ≠ ⊤ := by
      intro hgi
      rw [hgi] at hlt
      exact not_top_lt hlt
    simp [AdoptionDate.isFin, AdoptionDate.isInf, hlt, huf, hgf, not_lt_of_gt hlt]
  · rcases hGT with ⟨hgt, hgf⟩
    unfold AdoptionDate.isFin at hgf
    have huf : P.A u ≠ ⊤ := by
      intro hui
      rw [hui] at hgt
      exact not_top_lt hgt
    simp [AdoptionDate.isFin, AdoptionDate.isInf, hgt, huf, hgf, not_lt_of_gt hgt]

open Classical in
private lemma adoption_pair_sum_decomp (P : CohortPanel 𝒢 T) (f : 𝒢 → 𝒢 → ℝ)
    (hzero : ∀ g u, P.A g = P.A u → f g u = 0) :
    (∑ g, ∑ u, f g u) =
      (∑ g, ∑ u,
        if AdoptionDate.isFin (P.A g) ∧ AdoptionDate.isInf (P.A u) then f g u else 0) +
      (∑ g, ∑ u,
        if AdoptionDate.isFin (P.A u) ∧ AdoptionDate.isInf (P.A g) then f g u else 0) +
      (∑ g, ∑ u,
        if P.A g < P.A u ∧ AdoptionDate.isFin (P.A u) then f g u else 0) +
      (∑ g, ∑ u,
        if P.A u < P.A g ∧ AdoptionDate.isFin (P.A g) then f g u else 0) := by
  calc
    (∑ g, ∑ u, f g u)
        = ∑ g, ∑ u,
            ((if AdoptionDate.isFin (P.A g) ∧ AdoptionDate.isInf (P.A u) then f g u else 0) +
            (if AdoptionDate.isFin (P.A u) ∧ AdoptionDate.isInf (P.A g) then f g u else 0) +
            (if P.A g < P.A u ∧ AdoptionDate.isFin (P.A u) then f g u else 0) +
            (if P.A u < P.A g ∧ AdoptionDate.isFin (P.A g) then f g u else 0)) := by
              refine Finset.sum_congr rfl ?_
              intro g _hg
              refine Finset.sum_congr rfl ?_
              intro u _hu
              exact adoption_pair_pointwise P f hzero g u
    _ = _ := by simp [Finset.sum_add_distrib, add_assoc]

omit [DecidableEq 𝒢] in
private lemma sum_swap₂ (f : 𝒢 → 𝒢 → ℝ) :
    (∑ g, ∑ u, f u g) = ∑ g, ∑ u, f g u := by
  rw [Finset.sum_comm]

open Classical in
private lemma TN_sum_pair (P : CohortPanel 𝒢 T) (f : 𝒢 → 𝒢 → ℝ) :
    (∑ g, ∑ u,
        if AdoptionDate.isFin (P.A g) ∧ AdoptionDate.isInf (P.A u) then f g u + f u g else 0) =
      (∑ g, ∑ u,
        if AdoptionDate.isFin (P.A g) ∧ AdoptionDate.isInf (P.A u) then f g u else 0) +
      (∑ g, ∑ u,
        if AdoptionDate.isFin (P.A u) ∧ AdoptionDate.isInf (P.A g) then f g u else 0) := by
  calc
    (∑ g, ∑ u,
        if AdoptionDate.isFin (P.A g) ∧ AdoptionDate.isInf (P.A u) then f g u + f u g else 0)
        = ∑ g, ∑ u,
            ((if AdoptionDate.isFin (P.A g) ∧ AdoptionDate.isInf (P.A u) then f g u else 0) +
             (if AdoptionDate.isFin (P.A g) ∧ AdoptionDate.isInf (P.A u) then f u g else 0)) := by
              refine Finset.sum_congr rfl ?_
              intro g _hg
              refine Finset.sum_congr rfl ?_
              intro u _hu
              by_cases h : AdoptionDate.isFin (P.A g) ∧ AdoptionDate.isInf (P.A u) <;> simp [h]
    _ = (∑ g, ∑ u,
          if AdoptionDate.isFin (P.A g) ∧ AdoptionDate.isInf (P.A u) then f g u else 0) +
        (∑ g, ∑ u,
          if AdoptionDate.isFin (P.A g) ∧ AdoptionDate.isInf (P.A u) then f u g else 0) := by
          simp [Finset.sum_add_distrib]
    _ = (∑ g, ∑ u,
          if AdoptionDate.isFin (P.A g) ∧ AdoptionDate.isInf (P.A u) then f g u else 0) +
        (∑ g, ∑ u,
          if AdoptionDate.isFin (P.A u) ∧ AdoptionDate.isInf (P.A g) then f g u else 0) := by
          rw [sum_swap₂ (fun g u =>
            if AdoptionDate.isFin (P.A u) ∧ AdoptionDate.isInf (P.A g) then f g u else 0)]

open Classical in
private lemma TT_sum_pair (P : CohortPanel 𝒢 T) (f : 𝒢 → 𝒢 → ℝ) :
    (∑ e, ∑ ℓ,
        if P.A e < P.A ℓ ∧ AdoptionDate.isFin (P.A ℓ) then f e ℓ + f ℓ e else 0) =
      (∑ g, ∑ u,
        if P.A g < P.A u ∧ AdoptionDate.isFin (P.A u) then f g u else 0) +
      (∑ g, ∑ u,
        if P.A u < P.A g ∧ AdoptionDate.isFin (P.A g) then f g u else 0) := by
  calc
    (∑ e, ∑ ℓ,
        if P.A e < P.A ℓ ∧ AdoptionDate.isFin (P.A ℓ) then f e ℓ + f ℓ e else 0)
        = ∑ e, ∑ ℓ,
            ((if P.A e < P.A ℓ ∧ AdoptionDate.isFin (P.A ℓ) then f e ℓ else 0) +
             (if P.A e < P.A ℓ ∧ AdoptionDate.isFin (P.A ℓ) then f ℓ e else 0)) := by
              refine Finset.sum_congr rfl ?_
              intro e _he
              refine Finset.sum_congr rfl ?_
              intro ℓ _hℓ
              by_cases h : P.A e < P.A ℓ ∧ AdoptionDate.isFin (P.A ℓ) <;> simp [h]
    _ = (∑ e, ∑ ℓ,
          if P.A e < P.A ℓ ∧ AdoptionDate.isFin (P.A ℓ) then f e ℓ else 0) +
        (∑ e, ∑ ℓ,
          if P.A e < P.A ℓ ∧ AdoptionDate.isFin (P.A ℓ) then f ℓ e else 0) := by
          simp [Finset.sum_add_distrib]
    _ = (∑ g, ∑ u,
          if P.A g < P.A u ∧ AdoptionDate.isFin (P.A u) then f g u else 0) +
        (∑ g, ∑ u,
          if P.A u < P.A g ∧ AdoptionDate.isFin (P.A g) then f g u else 0) := by
          rw [sum_swap₂ (fun g u =>
            if P.A u < P.A g ∧ AdoptionDate.isFin (P.A g) then f g u else 0)]

open Classical in
private lemma adoption_pair_sum_grouped (P : CohortPanel 𝒢 T) (f : 𝒢 → 𝒢 → ℝ)
    (hzero : ∀ g u, P.A g = P.A u → f g u = 0) :
    (∑ g, ∑ u, f g u) =
      (∑ g, ∑ u,
        if AdoptionDate.isFin (P.A g) ∧ AdoptionDate.isInf (P.A u) then f g u + f u g else 0) +
      (∑ e, ∑ ℓ,
        if P.A e < P.A ℓ ∧ AdoptionDate.isFin (P.A ℓ) then f e ℓ + f ℓ e else 0) := by
  have hdecomp := adoption_pair_sum_decomp P f hzero
  rw [TN_sum_pair P f, TT_sum_pair P f]
  linarith

open Classical in
private lemma gap_sums_eq_VD (P : CohortPanel 𝒢 T) :
    (∑ g, ∑ u, if AdoptionDate.isFin (P.A g) ∧ AdoptionDate.isInf (P.A u) then
              P.p g * P.p u * q P g u * (1 - q P g u) else 0)
      + (∑ e, ∑ ℓ, if P.A e < P.A ℓ ∧ AdoptionDate.isFin (P.A ℓ) then
                P.p e * P.p ℓ * q P e ℓ * (1 - q P e ℓ) else 0)
      = VD P := by
  -- Remaining denominator algebra: expand `VD`, use `P.p_sum_one`, and group
  -- the pairwise variance of monotone adoption indicators by adoption-date
  -- order. This is the finite-sum manipulation described in the NL A5.2 doc.
  rw [VD_eq_pairwise_centeredD P]
  rw [adoption_pair_sum_grouped P (vdPairContribution P)
    (fun g u hA => vdPairContribution_eq_zero_of_A_eq P hA)]
  congr 1
  · refine Finset.sum_congr rfl ?_
    intro g _hg
    refine Finset.sum_congr rfl ?_
    intro u _hu
    by_cases h : AdoptionDate.isFin (P.A g) ∧ AdoptionDate.isInf (P.A u)
    · simp [h, TN_pair_vd_contribution_eq_gap P h.1 h.2]
    · simp [h]
  · refine Finset.sum_congr rfl ?_
    intro e _he
    refine Finset.sum_congr rfl ?_
    intro ℓ _hℓ
    by_cases h : P.A e < P.A ℓ ∧ AdoptionDate.isFin (P.A ℓ)
    · simp [h, TT_pair_vd_contribution_eq_gap P h.1 h.2]
    · simp [h]

/-- **Prop A5.2 (`raw_weight_sum_eq_VD`).** The aggregate raw-weight
denominator equals the residualized treatment variance:
`Λ P = V_D P`. Key denominator identity in
`thm:po-estimand-goodman-bacon-decomposition`. -/
theorem raw_weight_sum_eq_VD (P : CohortPanel 𝒢 T) :
    Lambda P = VD P := by
  rw [Lambda_eq_gap_sums]
  exact gap_sums_eq_VD P

open Classical in
/-- **Prop A5.3 (`twfe_numerator_eq_lambda_delta_sum`).** The TWFE numerator
decomposes by unordered cohort pairs into raw-weight times 2x2 DID
contrast contributions. -/
theorem twfe_numerator_eq_lambda_delta_sum (P : CohortPanel 𝒢 T) :
    (∑ g, ∑ t, (P.p g / (T : ℝ)) * Dtilde P g t * P.Y g t)
      = (∑ g, ∑ u, if AdoptionDate.isFin (P.A g) ∧ AdoptionDate.isInf (P.A u)
                    then lambdaTN P g u * Δ_TN P g u else 0)
        + (∑ e, ∑ ℓ, if P.A e < P.A ℓ ∧ AdoptionDate.isFin (P.A ℓ)
                      then lambdaEL P e ℓ * Δ_EL P e ℓ
                            + lambdaLE P e ℓ * Δ_LE P e ℓ else 0) := by
  rw [twfe_numerator_eq_pairwise_centeredD_Y P]
  rw [adoption_pair_sum_grouped P (numPairContribution P)
    (fun g u hA => numPairContribution_eq_zero_of_A_eq P hA)]
  congr 1
  · refine Finset.sum_congr rfl ?_
    intro g _hg
    refine Finset.sum_congr rfl ?_
    intro u _hu
    by_cases h : AdoptionDate.isFin (P.A g) ∧ AdoptionDate.isInf (P.A u)
    · simp [h, TN_pair_contribution_eq_lambda_delta P h.1 h.2]
    · simp [h]
  · refine Finset.sum_congr rfl ?_
    intro e _he
    refine Finset.sum_congr rfl ?_
    intro ℓ _hℓ
    by_cases h : P.A e < P.A ℓ ∧ AdoptionDate.isFin (P.A ℓ)
    · simp [h, TT_pair_contribution_eq_lambda_delta_sum P h.1 h.2]
    · simp [h]

private lemma sum_compTag (f : CompTag → ℝ) :
    (∑ tag, f tag) = f CompTag.TN + f CompTag.EL + f CompTag.LE := by
  rw [show (Finset.univ : Finset CompTag) = {CompTag.TN, CompTag.EL, CompTag.LE} by
    ext tag
    cases tag <;> simp]
  simp [add_assoc]

private lemma if_dup (c : Prop) [Decidable c] (x : ℝ) :
    (if c then if c then x else 0 else 0) = if c then x else 0 := by
  by_cases h : c <;> simp [h]

private lemma if_mul_dup (c : Prop) [Decidable c] (x y : ℝ) :
    (if c then (if c then x else 0) * (if c then y else 0) else 0) =
      if c then x * y else 0 := by
  by_cases h : c <;> simp [h]

private lemma sum_lambdaWeight_eq_Lambda (P : CohortPanel 𝒢 T) :
    ∑ k ∈ 𝒦 P, lambdaWeight P k = Lambda P := by
  classical
  rw [show (∑ k ∈ 𝒦 P, lambdaWeight P k)
      = ∑ k, if admissible P k then lambdaWeight P k else 0 by
    simp [𝒦, Finset.sum_filter]]
  rw [Fintype.sum_prod_type]
  rw [sum_compTag]
  simp only [lambdaWeight, admissible, P.p_pos, true_and]
  simp_rw [if_dup]
  simp_rw [Fintype.sum_prod_type]
  simp only [and_true]
  have hELLE :
      (∑ e, ∑ ℓ, if P.A e < P.A ℓ ∧ AdoptionDate.isFin (P.A ℓ) then
        lambdaEL P e ℓ else 0)
        + (∑ e, ∑ ℓ, if P.A e < P.A ℓ ∧ AdoptionDate.isFin (P.A ℓ) then
          lambdaLE P e ℓ else 0)
      = ∑ e, ∑ ℓ, if P.A e < P.A ℓ ∧ AdoptionDate.isFin (P.A ℓ) then
        lambdaEL P e ℓ + lambdaLE P e ℓ else 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro e he
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro ℓ hℓ
    by_cases h : P.A e < P.A ℓ ∧ AdoptionDate.isFin (P.A ℓ) <;> simp [h]
  unfold Lambda
  rw [← hELLE]
  rw [add_assoc]

open Classical in
private lemma sum_lambdaWeight_mul_contrast_eq (P : CohortPanel 𝒢 T) :
    ∑ k ∈ 𝒦 P, lambdaWeight P k * contrast P k =
      (∑ g, ∑ u, if AdoptionDate.isFin (P.A g) ∧ AdoptionDate.isInf (P.A u)
                    then lambdaTN P g u * Δ_TN P g u else 0)
        + (∑ e, ∑ ℓ, if P.A e < P.A ℓ ∧ AdoptionDate.isFin (P.A ℓ)
                      then lambdaEL P e ℓ * Δ_EL P e ℓ
                            + lambdaLE P e ℓ * Δ_LE P e ℓ else 0) := by
  classical
  rw [show (∑ k ∈ 𝒦 P, lambdaWeight P k * contrast P k)
      = ∑ k, if admissible P k then lambdaWeight P k * contrast P k else 0 by
    simp [𝒦, Finset.sum_filter]]
  rw [Fintype.sum_prod_type]
  rw [sum_compTag]
  simp only [lambdaWeight, contrast, admissible, P.p_pos, true_and]
  simp_rw [if_mul_dup]
  simp_rw [Fintype.sum_prod_type]
  simp only [and_true]
  have hELLE :
      (∑ e, ∑ ℓ, if P.A e < P.A ℓ ∧ AdoptionDate.isFin (P.A ℓ) then
        lambdaEL P e ℓ * Δ_EL P e ℓ else 0)
        + (∑ e, ∑ ℓ, if P.A e < P.A ℓ ∧ AdoptionDate.isFin (P.A ℓ) then
          lambdaLE P e ℓ * Δ_LE P e ℓ else 0)
      = ∑ e, ∑ ℓ, if P.A e < P.A ℓ ∧ AdoptionDate.isFin (P.A ℓ) then
        lambdaEL P e ℓ * Δ_EL P e ℓ + lambdaLE P e ℓ * Δ_LE P e ℓ else 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro e he
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro ℓ hℓ
    by_cases h : P.A e < P.A ℓ ∧ AdoptionDate.isFin (P.A ℓ) <;> simp [h]
  rw [← hELLE]
  rw [add_assoc]

/-- **Prop A5.4 (`weights_sum_one`).** Under positivity of the residualized
treatment variance, the normalized comparison weights sum to one. -/
theorem weights_sum_one (P : CohortPanel 𝒢 T) (hVD_pos : 0 < VD P) :
    ∑ k ∈ 𝒦 P, weight P k = 1 := by
  classical
  have hL_ne : Lambda P ≠ 0 := by
    rw [raw_weight_sum_eq_VD P]
    exact ne_of_gt hVD_pos
  have hsum_lambda : ∑ k ∈ 𝒦 P, lambdaWeight P k = Lambda P := by
    exact sum_lambdaWeight_eq_Lambda P
  calc
    ∑ k ∈ 𝒦 P, weight P k = ∑ k ∈ 𝒦 P, lambdaWeight P k / Lambda P := by
      refine Finset.sum_congr rfl ?_
      intro k hk
      have hk' : admissible P k := by
        simpa [𝒦] using hk
      rcases k with ⟨tag, pair⟩
      rcases pair with ⟨g, u⟩
      cases tag <;> simp [weight, lambdaWeight, w_TN, w_EL, w_LE, hk']
    _ = (∑ k ∈ 𝒦 P, lambdaWeight P k) / Lambda P := by
      simp [div_eq_mul_inv, Finset.mul_sum, mul_comm]
    _ = Lambda P / Lambda P := by rw [hsum_lambda]
    _ = 1 := by exact div_self hL_ne

/-- **Theorem A5.5 (`twfe_eq_weighted_avg`,
`thm:po-estimand-goodman-bacon-decomposition`).** When the residualized treatment
has strictly positive variance, the TWFE coefficient equals the normalized
Goodman-Bacon weighted average of admissible two-by-two DID contrasts.

The positivity hypothesis is the nondegenerate condition that makes
`weight P k = lambdaWeight P k / Lambda P` a normalized coefficient system:
`weights_sum_one` then shows the weights sum to one. It also rules out the
totalized zero-variance cases where the algebraic ratio still has a Lean value
but no coefficient interpretation. -/
theorem twfe_eq_weighted_avg (P : CohortPanel 𝒢 T) (hVD_pos : 0 < VD P) :
    betaTWFE P = ∑ k ∈ 𝒦 P, weight P k * contrast P k := by
  classical
  have _ := hVD_pos
  have hnum := twfe_numerator_eq_lambda_delta_sum P
  have hsum :
      ∑ k ∈ 𝒦 P, lambdaWeight P k * contrast P k =
        (∑ g, ∑ u, if AdoptionDate.isFin (P.A g) ∧ AdoptionDate.isInf (P.A u)
                      then lambdaTN P g u * Δ_TN P g u else 0)
          + (∑ e, ∑ ℓ, if P.A e < P.A ℓ ∧ AdoptionDate.isFin (P.A ℓ)
                        then lambdaEL P e ℓ * Δ_EL P e ℓ
                              + lambdaLE P e ℓ * Δ_LE P e ℓ else 0) :=
    sum_lambdaWeight_mul_contrast_eq P
  have hweighted :
      ∑ k ∈ 𝒦 P, weight P k * contrast P k =
        (∑ k ∈ 𝒦 P, lambdaWeight P k * contrast P k) / Lambda P := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hk' : admissible P k := by
      simpa [𝒦] using hk
    rcases k with ⟨tag, pair⟩
    rcases pair with ⟨g, u⟩
    cases tag <;> simp [weight, lambdaWeight, w_TN, w_EL, w_LE, hk',
      div_eq_mul_inv, mul_left_comm, mul_comm]
  calc
    betaTWFE P
        = ((∑ k ∈ 𝒦 P, lambdaWeight P k * contrast P k) / Lambda P) := by
          unfold betaTWFE
          rw [hnum]
          rw [← hsum]
          rw [← raw_weight_sum_eq_VD P]
    _ = ∑ k ∈ 𝒦 P, weight P k * contrast P k := by
          rw [hweighted]

end StaggeredTWFEDecomposition
end Panel.EstimandCharacterization
end Causalean
