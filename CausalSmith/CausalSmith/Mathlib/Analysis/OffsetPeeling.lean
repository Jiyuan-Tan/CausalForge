/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Mathlib.Analysis.MeanInequalities

/-!
# Offset (Young / weighted-AM-GM) peeling inequalities

The deterministic peeling step `sup_{t ≥ 0} (a·t^θ − c·t) ≤ C(c,θ)·a^{1/(1−θ)}`
underlying every offset/localization rate proof, with explicit constant
`C(c,θ) = (1−θ)·(θ/c)^{θ/(1−θ)}`.  Staged here (CausalSmith side) out of the
policy-regret rate derivation; pure real analysis with no statistical model.
Promotion to `Causalean/` is gated on a second consumer.

* `offset_peeling_coeff` — general coefficient `c`.
* `offset_peeling` — the `c = 1/4` specialization used for the AIPW oracle offset.
* `max_two_split` — split a clipped two-term offset across its summands.
-/

namespace CausalSmith.Mathlib.OffsetPeeling

/-- Offset-peeling constant for the `c = 1/4` offset:
`(1 − θ)·(4θ)^{θ/(1−θ)}`. -/
noncomputable def offsetPeelingConstant (θ : ℝ) : ℝ :=
  (1 - θ) * (4 * θ) ^ (θ / (1 - θ))

/-- Peeling constant with a general offset coefficient `c`:
`(1 − θ)·(θ/c)^{θ/(1−θ)}` (the `c = 1/4` case is `offsetPeelingConstant`). -/
noncomputable def offsetPeelingConstantC (c θ : ℝ) : ℝ :=
  (1 - θ) * (θ / c) ^ (θ / (1 - θ))

lemma offsetPeelingConstant_nonneg
    (θ : ℝ) (hθ_nonneg : 0 ≤ θ) (hθ_lt : θ < 1) :
    0 ≤ offsetPeelingConstant θ := by
  have hsub_nonneg : 0 ≤ 1 - θ := sub_nonneg.mpr (le_of_lt hθ_lt)
  have hfourθ_nonneg : 0 ≤ 4 * θ := mul_nonneg (by norm_num) hθ_nonneg
  dsimp [offsetPeelingConstant]
  exact mul_nonneg hsub_nonneg (Real.rpow_nonneg hfourθ_nonneg _)

/-- Deterministic Young/AM-GM peeling for the `c = 1/4` oracle-offset.

The constant is the actual supremum of `a·t^θ − t/4` over `t ≥ 0`:
`(1 − θ)·(4θ)^{θ/(1−θ)}`. -/
lemma offset_peeling
    (θ a t : ℝ) (hθ_pos : 0 < θ) (hθ_lt : θ < 1)
    (ha : 0 ≤ a) (ht : 0 ≤ t) :
    max 0 (a * t ^ θ - (1 / 4 : ℝ) * t)
      ≤ offsetPeelingConstant θ * a ^ (1 / (1 - θ)) := by
  have hθ_nonneg : 0 ≤ θ := le_of_lt hθ_pos
  have hone_sub_nonneg : 0 ≤ 1 - θ := sub_nonneg.mpr (le_of_lt hθ_lt)
  have hone_sub_pos : 0 < 1 - θ := sub_pos.mpr hθ_lt
  have hfourθ_nonneg : 0 ≤ 4 * θ := mul_nonneg (by norm_num) hθ_nonneg
  have hfourθ_pos : 0 < 4 * θ := mul_pos (by norm_num) hθ_pos
  let p₁ : ℝ := t / (4 * θ)
  let p₂ : ℝ :=
    (4 * θ) ^ (θ / (1 - θ)) * a ^ (1 / (1 - θ))
  have hp₁ : 0 ≤ p₁ := div_nonneg ht hfourθ_nonneg
  have hp₂ : 0 ≤ p₂ :=
    mul_nonneg (Real.rpow_nonneg hfourθ_nonneg _) (Real.rpow_nonneg ha _)
  have hw : θ + (1 - θ) = 1 := by ring
  have hamg :=
    Real.geom_mean_le_arith_mean2_weighted
      hθ_nonneg hone_sub_nonneg hp₁ hp₂ hw
  have hrhs :
      θ * p₁ + (1 - θ) * p₂ =
        (1 / 4 : ℝ) * t +
          offsetPeelingConstant θ * a ^ (1 / (1 - θ)) := by
    dsimp [p₁, p₂, offsetPeelingConstant]
    field_simp [ne_of_gt hθ_pos, ne_of_gt hone_sub_pos]
  have hlhs : p₁ ^ θ * p₂ ^ (1 - θ) = a * t ^ θ := by
    dsimp [p₁, p₂]
    rw [Real.mul_rpow
      (Real.rpow_nonneg hfourθ_nonneg _) (Real.rpow_nonneg ha _)]
    rw [← Real.rpow_mul hfourθ_nonneg]
    rw [← Real.rpow_mul ha]
    have hpow₁ : θ / (1 - θ) * (1 - θ) = θ := by
      field_simp [ne_of_gt hone_sub_pos]
    have hpow₂ : 1 / (1 - θ) * (1 - θ) = 1 := by
      field_simp [ne_of_gt hone_sub_pos]
    rw [hpow₁, hpow₂, Real.rpow_one]
    rw [← mul_assoc]
    rw [← Real.mul_rpow hp₁ hfourθ_nonneg]
    have hdiv : t / (4 * θ) * (4 * θ) = t := by
      field_simp [ne_of_gt hfourθ_pos]
    rw [hdiv]
    ring
  have hmain :
      a * t ^ θ ≤
        (1 / 4 : ℝ) * t +
          offsetPeelingConstant θ * a ^ (1 / (1 - θ)) := by
    rw [← hlhs]
    simpa [hrhs] using hamg
  have hR_nonneg :
      0 ≤ offsetPeelingConstant θ * a ^ (1 / (1 - θ)) := by
    dsimp [offsetPeelingConstant]
    exact mul_nonneg
      (mul_nonneg hone_sub_nonneg (Real.rpow_nonneg hfourθ_nonneg _))
      (Real.rpow_nonneg ha _)
  exact max_le (by simpa using hR_nonneg) (by linarith)

lemma offset_peeling_nonneg_theta
    (θ a t : ℝ) (hθ_nonneg : 0 ≤ θ) (hθ_lt : θ < 1)
    (ha : 0 ≤ a) (ht : 0 ≤ t) :
    max 0 (a * t ^ θ - (1 / 4 : ℝ) * t)
      ≤ offsetPeelingConstant θ * a ^ (1 / (1 - θ)) := by
  by_cases hθ_zero : θ = 0
  · subst θ
    have hpow : t ^ (0 : ℝ) = 1 := by simp
    have hconst : offsetPeelingConstant 0 = 1 := by
      unfold offsetPeelingConstant
      norm_num
    have hR : offsetPeelingConstant 0 * a ^ (1 / (1 - 0)) = a := by
      rw [hconst]
      norm_num
    have hsub : a * t ^ (0 : ℝ) - (1 / 4 : ℝ) * t ≤ a := by
      rw [hpow]
      nlinarith
    simpa [hconst] using max_le ha hsub
  · have hθ_pos : 0 < θ := lt_of_le_of_ne hθ_nonneg (Ne.symm hθ_zero)
    exact offset_peeling θ a t hθ_pos hθ_lt ha ht

/-- Generalized offset peeling at coefficient `c`: for `0 < c`, `0 < θ < 1`,
`max 0 (a·t^θ − c·t) ≤ offsetPeelingConstantC c θ · a^{1/(1−θ)}` (weighted AM-GM). -/
lemma offset_peeling_coeff
    (c θ a t : ℝ) (hc_pos : 0 < c) (hθ_pos : 0 < θ) (hθ_lt : θ < 1)
    (ha : 0 ≤ a) (ht : 0 ≤ t) :
    max 0 (a * t ^ θ - c * t)
      ≤ offsetPeelingConstantC c θ * a ^ (1 / (1 - θ)) := by
  have hθ_nonneg : 0 ≤ θ := le_of_lt hθ_pos
  have hone_sub_nonneg : 0 ≤ 1 - θ := sub_nonneg.mpr (le_of_lt hθ_lt)
  have hone_sub_pos : 0 < 1 - θ := sub_pos.mpr hθ_lt
  have hθc_pos : 0 < θ / c := div_pos hθ_pos hc_pos
  have hθc_nonneg : 0 ≤ θ / c := le_of_lt hθc_pos
  let p₁ : ℝ := c * t / θ
  let p₂ : ℝ := (θ / c) ^ (θ / (1 - θ)) * a ^ (1 / (1 - θ))
  have hp₁ : 0 ≤ p₁ := div_nonneg (mul_nonneg (le_of_lt hc_pos) ht) hθ_nonneg
  have hp₂ : 0 ≤ p₂ :=
    mul_nonneg (Real.rpow_nonneg hθc_nonneg _) (Real.rpow_nonneg ha _)
  have hw : θ + (1 - θ) = 1 := by ring
  have hamg :=
    Real.geom_mean_le_arith_mean2_weighted
      hθ_nonneg hone_sub_nonneg hp₁ hp₂ hw
  have hrhs :
      θ * p₁ + (1 - θ) * p₂ =
        c * t + offsetPeelingConstantC c θ * a ^ (1 / (1 - θ)) := by
    dsimp [p₁, p₂, offsetPeelingConstantC]
    field_simp [ne_of_gt hθ_pos, ne_of_gt hone_sub_pos, ne_of_gt hc_pos]
  have hlhs : p₁ ^ θ * p₂ ^ (1 - θ) = a * t ^ θ := by
    dsimp [p₁, p₂]
    rw [Real.mul_rpow
      (Real.rpow_nonneg hθc_nonneg _) (Real.rpow_nonneg ha _)]
    rw [← Real.rpow_mul hθc_nonneg]
    rw [← Real.rpow_mul ha]
    have hpow₁ : θ / (1 - θ) * (1 - θ) = θ := by
      field_simp [ne_of_gt hone_sub_pos]
    have hpow₂ : 1 / (1 - θ) * (1 - θ) = 1 := by
      field_simp [ne_of_gt hone_sub_pos]
    rw [hpow₁, hpow₂, Real.rpow_one]
    rw [← mul_assoc]
    rw [← Real.mul_rpow hp₁ hθc_nonneg]
    have hdiv : c * t / θ * (θ / c) = t := by
      field_simp [ne_of_gt hθ_pos, ne_of_gt hc_pos]
    rw [hdiv]
    ring
  have hmain :
      a * t ^ θ ≤
        c * t + offsetPeelingConstantC c θ * a ^ (1 / (1 - θ)) := by
    rw [← hlhs]
    simpa [hrhs] using hamg
  have hR_nonneg :
      0 ≤ offsetPeelingConstantC c θ * a ^ (1 / (1 - θ)) := by
    dsimp [offsetPeelingConstantC]
    exact mul_nonneg
      (mul_nonneg hone_sub_nonneg (Real.rpow_nonneg hθc_nonneg _))
      (Real.rpow_nonneg ha _)
  exact max_le (by simpa using hR_nonneg) (by linarith)

lemma offsetPeelingConstantC_nonneg
    (c θ : ℝ) (hc_pos : 0 < c) (hθ_nonneg : 0 ≤ θ) (hθ_lt : θ < 1) :
    0 ≤ offsetPeelingConstantC c θ := by
  have hsub : 0 ≤ 1 - θ := sub_nonneg.mpr (le_of_lt hθ_lt)
  have hbase : 0 ≤ θ / c := div_nonneg hθ_nonneg (le_of_lt hc_pos)
  unfold offsetPeelingConstantC
  exact mul_nonneg hsub (Real.rpow_nonneg hbase _)

lemma offset_peeling_coeff_nonneg_theta
    (c θ a t : ℝ) (hc_pos : 0 < c) (hθ_nonneg : 0 ≤ θ) (hθ_lt : θ < 1)
    (ha : 0 ≤ a) (ht : 0 ≤ t) :
    max 0 (a * t ^ θ - c * t)
      ≤ offsetPeelingConstantC c θ * a ^ (1 / (1 - θ)) := by
  by_cases hθ_zero : θ = 0
  · subst θ
    have hconst : offsetPeelingConstantC c 0 = 1 := by
      unfold offsetPeelingConstantC
      simp
    have hsub : a * t ^ (0 : ℝ) - c * t ≤ a := by
      rw [Real.rpow_zero]
      nlinarith [mul_nonneg (le_of_lt hc_pos) ht]
    simpa [hconst] using max_le ha hsub
  · exact offset_peeling_coeff c θ a t hc_pos
      (lt_of_le_of_ne hθ_nonneg (Ne.symm hθ_zero)) hθ_lt ha ht

/-- Split a clipped two-term offset across its summands:
`max 0 (a − 2r) ≤ max 0 (b − r) + max 0 (c − r)` when `a ≤ b + c` and `0 ≤ r`. -/
lemma max_two_split (a b c r : ℝ) (h : a ≤ b + c) (hr : 0 ≤ r) :
    max 0 (a - 2 * r) ≤ max 0 (b - r) + max 0 (c - r) := by
  have hb : b - r ≤ max 0 (b - r) := le_max_right _ _
  have hc : c - r ≤ max 0 (c - r) := le_max_right _ _
  have hb0 : 0 ≤ max 0 (b - r) := le_max_left _ _
  have hc0 : 0 ≤ max 0 (c - r) := le_max_left _ _
  apply max_le
  · linarith
  · linarith

end CausalSmith.Mathlib.OffsetPeeling
