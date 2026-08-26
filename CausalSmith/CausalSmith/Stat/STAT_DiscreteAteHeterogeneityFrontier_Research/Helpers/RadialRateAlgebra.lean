/- Rate algebra for the capped radial hard family. -/

import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.LowerTransfer

namespace CausalSmith.Stat.DiscreteAteHeterogeneityFrontier

open Set

-- @node: cappedRadial_sourceRate_dominates
/-- If [the sample size satisfies the stated lower bound](hyp:hn) and [the alphabet is
  nonempty](hyp:hd) and [the radial cap satisfies its stated bound](hyp:hb) and [the radial cap is
  at most one quarter](hyp:hb4) and [the scalar satisfies the stated range condition](hyp:hx),
  [capping the source alphabet at half of `b n log(en)` retains, up to the explicit factor
  `b²/16`, the ambient capped polynomial component](goal). -/
lemma cappedRadial_sourceRate_dominates {n d : ℕ} {b : ℝ}
    (hn : 3 ≤ n) (hd : 0 < d) (hb : 0 < b) (hb4 : b ≤ 4)
    (hx : 1 ≤ (b / 2) * (n : ℝ) * logEN n) :
    let m := min d (max 1
      (Nat.floor ((b / 2) * (n : ℝ) * logEN n)))
    b ^ 2 / 16 * min 1 (polynomialComponent n d) ≤
      CausalSmith.Stat.DiscreteAteMinimaxLoggap.minimaxRate n m := by
  dsimp only
  let L : ℝ := logEN n
  let x : ℝ := (b / 2) * (n : ℝ) * L
  let m : ℕ := min d (max 1 (Nat.floor x))
  have hnR : 0 < (n : ℝ) := by positivity
  have hlogn : 0 < Real.log (n : ℝ) := by
    exact Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hL : 0 < L := by
    dsimp [L, logEN]
    rw [Real.log_mul (Real.exp_ne_zero 1) hnR.ne', Real.log_exp]
    positivity
  have hx' : 1 ≤ x := by simpa [x, L] using hx
  have hfloor_pos : 0 < Nat.floor x := Nat.floor_pos.mpr hx'
  have hmax : max 1 (Nat.floor x) = Nat.floor x := by omega
  have hmpos : 0 < m := by
    dsimp [m]
    rw [hmax]
    exact (Nat.lt_min).2 ⟨hd, hfloor_pos⟩
  have hfloor_half : x / 2 ≤ (Nat.floor x : ℝ) :=
    half_le_natFloor_of_one_le hx'
  have hratio : b / 4 * min 1 ((d : ℝ) / ((n : ℝ) * L)) ≤
      (m : ℝ) / ((n : ℝ) * L) := by
    by_cases hsmall : d ≤ Nat.floor x
    · have hm : m = d := by simp [m, hmax, hsmall]
      rw [hm]
      have hbquarter : b / 4 ≤ 1 := by linarith
      have hq : 0 ≤ (d : ℝ) / ((n : ℝ) * L) := by positivity
      have hmin0 : 0 ≤ min 1 ((d : ℝ) / ((n : ℝ) * L)) := by positivity
      calc
        b / 4 * min 1 ((d : ℝ) / ((n : ℝ) * L)) ≤
            1 * min 1 ((d : ℝ) / ((n : ℝ) * L)) := by gcongr
        _ ≤ (d : ℝ) / ((n : ℝ) * L) := by simpa using
          (min_le_right (1 : ℝ) ((d : ℝ) / ((n : ℝ) * L)))
    · have hm : m = Nat.floor x := by
        simp [m, hmax, Nat.le_of_not_ge hsmall]
      have hden : 0 < (n : ℝ) * L := mul_pos hnR hL
      have hcap : b / 4 ≤ (m : ℝ) / ((n : ℝ) * L) := by
        rw [hm]
        apply (le_div_iff₀ hden).2
        dsimp [x] at hfloor_half
        nlinarith
      have hmin : min 1 ((d : ℝ) / ((n : ℝ) * L)) ≤ 1 := min_le_left _ _
      exact (mul_le_mul_of_nonneg_left hmin (by positivity : 0 ≤ b / 4)).trans
        (by simpa using hcap)
  have hsquare : b ^ 2 / 16 *
        min 1 ((d : ℝ) ^ 2 / ((n : ℝ) ^ 2 * L ^ 2)) ≤
      (m : ℝ) ^ 2 / ((n : ℝ) ^ 2 * L ^ 2) := by
    have hq0 : 0 ≤ (d : ℝ) / ((n : ℝ) * L) := by positivity
    have hm0 : 0 ≤ (m : ℝ) / ((n : ℝ) * L) := by positivity
    have hleft0 : 0 ≤ b / 4 * min 1 ((d : ℝ) / ((n : ℝ) * L)) := by
      positivity
    have hsq := (sq_le_sq₀ hleft0 hm0).2 hratio
    have hminsq : (min 1 ((d : ℝ) / ((n : ℝ) * L))) ^ 2 =
        min 1 ((d : ℝ) ^ 2 / ((n : ℝ) ^ 2 * L ^ 2)) := by
      have hquot : ((d : ℝ) / ((n : ℝ) * L)) ^ 2 =
          (d : ℝ) ^ 2 / ((n : ℝ) ^ 2 * L ^ 2) := by ring
      rw [← hquot]
      by_cases hq1 : (d : ℝ) / ((n : ℝ) * L) ≤ 1
      · rw [min_eq_right hq1, min_eq_right]
        nlinarith
      · have hq1' : 1 ≤ (d : ℝ) / ((n : ℝ) * L) := le_of_not_ge hq1
        have hsq1 : (1 : ℝ) ≤ ((d : ℝ) / ((n : ℝ) * L)) ^ 2 := by
          simpa using (sq_le_sq₀ zero_le_one hq0).2 hq1'
        rw [min_eq_left hq1', min_eq_left hsq1]
        norm_num
    rw [mul_pow, hminsq] at hsq
    calc
      b ^ 2 / 16 * min 1 ((d : ℝ) ^ 2 / ((n : ℝ) ^ 2 * L ^ 2)) =
          (b / 4) ^ 2 * min 1 ((d : ℝ) ^ 2 / ((n : ℝ) ^ 2 * L ^ 2)) := by ring
      _ ≤ ((m : ℝ) / ((n : ℝ) * L)) ^ 2 := hsq
      _ = (m : ℝ) ^ 2 / ((n : ℝ) ^ 2 * L ^ 2) := by ring
  have hlog_le : Real.log (n : ℝ) ≤ L := by
    dsimp [L, logEN]
    rw [Real.log_mul (Real.exp_ne_zero 1) hnR.ne', Real.log_exp]
    linarith
  have hden_le : (n : ℝ) ^ 2 * Real.log n ^ 2 ≤
      (n : ℝ) ^ 2 * L ^ 2 := by
    gcongr
  have hfrac : (m : ℝ) ^ 2 / ((n : ℝ) ^ 2 * L ^ 2) ≤
      (m : ℝ) ^ 2 / ((n : ℝ) ^ 2 * Real.log n ^ 2) := by
    exact div_le_div_of_nonneg_left (sq_nonneg (m : ℝ))
      (by positivity) hden_le
  unfold polynomialComponent
  unfold CausalSmith.Stat.DiscreteAteMinimaxLoggap.minimaxRate
  change b ^ 2 / 16 * min 1
      ((d : ℝ) ^ 2 / ((n : ℝ) ^ 2 * L ^ 2)) ≤ _
  exact hsquare.trans (hfrac.trans (le_add_of_nonneg_left (by positivity)))

-- @node: cappedRadial_transportScale
/-- If [the sample size satisfies the stated lower bound](hyp:hn) and [the alphabet is
  nonempty](hyp:hd) and [the transport scale satisfies the stated condition](hyp:ha) and [the
  radial cap satisfies its stated bound](hyp:hb) and [the radial cap is at most one
  quarter](hyp:hb4) and [the scalar satisfies the stated range condition](hyp:hx), [after the
  Bernoulli channel scales the source target by `M σ / 2`, the capped source lower bound supplies
  the ambient radial term with the explicit constant `a b² / 128`](goal). -/
lemma cappedRadial_transportScale {n d : ℕ} {a b M sigma : ℝ}
    (hn : 3 ≤ n) (hd : 0 < d) (ha : 0 ≤ a) (hb : 0 < b) (hb4 : b ≤ 4)
    (hx : 1 ≤ (b / 2) * (n : ℝ) * logEN n) :
    let m := min d (max 1
      (Nat.floor ((b / 2) * (n : ℝ) * logEN n)))
    (a * b ^ 2 / 128) * M ^ 2 * sigma ^ 2 *
        min 1 (polynomialComponent n d) ≤
      (M * sigma / 2) ^ 2 *
        (a / 2 * CausalSmith.Stat.DiscreteAteMinimaxLoggap.minimaxRate n m) := by
  dsimp only
  have hrate := cappedRadial_sourceRate_dominates hn hd hb hb4 hx
  have hnonneg : 0 ≤ (M * sigma / 2) ^ 2 * (a / 2) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hrate hnonneg
  nlinarith [hmul]

end CausalSmith.Stat.DiscreteAteHeterogeneityFrontier
