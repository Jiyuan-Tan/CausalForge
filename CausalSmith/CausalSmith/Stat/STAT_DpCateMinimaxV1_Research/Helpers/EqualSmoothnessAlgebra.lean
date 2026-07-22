/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Algebra for the equal-smoothness private CATE corollary
-/

import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.RateAlgebra

namespace CausalSmith.Stat.DpCateMinimax

-- @node: nonprivateCateRate_equal_smoothness
lemma nonprivateCateRate_equal_smoothness {d : ℕ} (n : ℕ) (alpha beta gamma : ℝ)
    (halpha : 0 < alpha) (hgamma : 0 < gamma) (hbg : beta = gamma) :
    nonprivateCateRate n alpha beta gamma d =
      (n : ℝ) ^ (-(gamma / (2 * gamma + (d : ℝ)))) := by
  subst beta
  unfold nonprivateCateRate
  have hd : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  have hαγ : 0 < alpha + gamma := add_pos halpha hgamma
  have hD1 : 0 < 2 + (d : ℝ) / gamma := by positivity
  have hD2 : 0 < 1 + (d : ℝ) / (2 * gamma) + (d : ℝ) / (2 * (alpha + gamma)) := by
    positivity
  have hfrac :
      1 / (2 + (d : ℝ) / gamma) ≤
        1 / (1 + (d : ℝ) / (2 * gamma) + (d : ℝ) / (2 * (alpha + gamma))) := by
    rw [one_div_le_one_div hD1 hD2]
    have hterm : (d : ℝ) / (2 * (alpha + gamma)) ≤ (d : ℝ) / (2 * gamma) := by
      gcongr
      linarith
    have hhalf : (d : ℝ) / (2 * gamma) + (d : ℝ) / (2 * gamma) = (d : ℝ) / gamma := by
      field_simp
      ring
    linarith
  rw [min_eq_left hfrac]
  congr 2
  field_simp

-- @node: equal_smoothness_rate_boundary
lemma equal_smoothness_rate_boundary {d : ℕ} (n : ℕ) (gamma : ℝ)
    (hgamma : 0 < gamma) (hn : 1 ≤ n) :
    (∀ e : ℝ, 0 < e →
        ((n : ℝ) ^ (-(gamma / (2 * gamma + (d : ℝ))))
            = ((n : ℝ) * e) ^ (-(gamma / (gamma + (d : ℝ))))
          ↔ e = (n : ℝ) ^ (-(gamma / (2 * gamma + (d : ℝ)))))) ∧
    (∀ e : ℝ, (n : ℝ) ^ (-(gamma / (2 * gamma + (d : ℝ)))) < e →
        ((n : ℝ) * e) ^ (-(gamma / (gamma + (d : ℝ))))
          ≤ (n : ℝ) ^ (-(gamma / (2 * gamma + (d : ℝ))))) ∧
    (∀ e : ℝ, 0 < e → e < (n : ℝ) ^ (-(gamma / (2 * gamma + (d : ℝ)))) →
        (n : ℝ) ^ (-(gamma / (2 * gamma + (d : ℝ))))
          ≤ ((n : ℝ) * e) ^ (-(gamma / (gamma + (d : ℝ))))) := by
  let x : ℝ := n
  let a : ℝ := gamma / (2 * gamma + (d : ℝ))
  let b : ℝ := gamma / (gamma + (d : ℝ))
  let t : ℝ := x ^ (-a)
  have hx : 0 < x := by
    dsimp [x]
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hd : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  have hdena : 0 < 2 * gamma + (d : ℝ) := by positivity
  have hdenb : 0 < gamma + (d : ℝ) := by positivity
  have ha : 0 < a := div_pos hgamma hdena
  have hb : 0 < b := div_pos hgamma hdenb
  have ht : 0 < t := Real.rpow_pos_of_pos hx _
  have hab : a * b = b - a := by
    dsimp [a, b]
    field_simp
    ring
  have hexp : -b + (-a) * (-b) = -a := by linarith
  have hthreshold : (x * t) ^ (-b) = x ^ (-a) := by
    calc
      (x * t) ^ (-b) = x ^ (-b) * t ^ (-b) := Real.mul_rpow hx.le ht.le
      _ = x ^ (-b) * x ^ ((-a) * (-b)) := by
        rw [Real.rpow_mul hx.le]
      _ = x ^ (-b + (-a) * (-b)) := (Real.rpow_add hx (-b) ((-a) * (-b))).symm
      _ = x ^ (-a) := by rw [hexp]
  have hfactor (e : ℝ) (he : 0 < e) :
      (x * e) ^ (-b) = x ^ (-b) * e ^ (-b) := Real.mul_rpow hx.le he.le
  have hq : 0 < x ^ (-b) := Real.rpow_pos_of_pos hx _
  change (∀ e : ℝ, 0 < e → (x ^ (-a) = (x * e) ^ (-b) ↔ e = x ^ (-a))) ∧
    (∀ e : ℝ, x ^ (-a) < e → (x * e) ^ (-b) ≤ x ^ (-a)) ∧
    (∀ e : ℝ, 0 < e → e < x ^ (-a) → x ^ (-a) ≤ (x * e) ^ (-b))
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    constructor
    · intro h
      have hpowers : e ^ (-b) = t ^ (-b) := by
        have heq : (x * e) ^ (-b) = (x * t) ^ (-b) := h.symm.trans hthreshold.symm
        rw [hfactor e he, hfactor t ht] at heq
        apply mul_left_cancel₀ hq.ne'
        exact heq
      exact (Real.rpow_left_inj he.le ht.le (neg_ne_zero.mpr hb.ne')).mp hpowers
    · intro het
      change e = t at het
      rw [het]
      exact hthreshold.symm
  · intro e he
    have hepos : 0 < e := lt_trans ht he
    have hpowers : e ^ (-b) ≤ t ^ (-b) :=
      (Real.rpow_le_rpow_iff_of_neg hepos ht (neg_lt_zero.mpr hb)).2 he.le
    rw [hfactor e hepos, ← hthreshold, hfactor t ht]
    exact mul_le_mul_of_nonneg_left hpowers hq.le
  · intro e he het
    have hpowers : t ^ (-b) ≤ e ^ (-b) :=
      (Real.rpow_le_rpow_iff_of_neg ht he (neg_lt_zero.mpr hb)).2 het.le
    rw [← hthreshold, hfactor t ht, hfactor e he]
    exact mul_le_mul_of_nonneg_left hpowers hq.le

end CausalSmith.Stat.DpCateMinimax
