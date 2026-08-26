/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Stat.UStatistic.OrderM.MixedOrderCovariance
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Mixed-order falling-factorial normalization bounds

This module supplies uniform bounds for overlap normalizations and for the
size-zero disjoint correction.  The statements are symmetric in the two orders
and depend only on a common upper bound `R`.
-/

namespace Causalean.Stat

private theorem orderedFactorialMatchingRatio_le {n r s h : ℕ}
    (hrs : r ≤ s) (hn : 4 * s ^ 2 ≤ n) (hh : h ≤ s) :
    (n.descFactorial (r + s - h) : ℝ) /
        ((n.descFactorial r : ℝ) * (n.descFactorial s : ℝ)) ≤
      Real.exp 1 / (n : ℝ) ^ h := by
  by_cases hs0 : s = 0
  · subst s
    have hr0 : r = 0 := by omega
    have hh0 : h = 0 := by omega
    subst r
    subst h
    norm_num
  have hspos : 0 < s := Nat.pos_of_ne_zero hs0
  have hnpos : 0 < n := lt_of_lt_of_le (by positivity : 0 < 4 * s ^ 2) hn
  have hsn : s ≤ n := by nlinarith [sq_nonneg (s : ℝ)]
  have hsubpos : 0 < n - s := by
    have : s < n := by nlinarith
    omega
  let u : ℕ := n - s
  have hu_pos : 0 < u := by simpa [u] using hsubpos
  have hnumNat : n.descFactorial (r + s - h) ≤ n ^ (r + s - h) :=
    Nat.descFactorial_le_pow n _
  have hlowS : u ^ s ≤ n.descFactorial s := by
    calc
      u ^ s ≤ (n + 1 - s) ^ s := Nat.pow_le_pow_left (by simp [u]; omega) s
      _ ≤ n.descFactorial s := Nat.pow_sub_le_descFactorial n s
  have hur : u ≤ n + 1 - r := by
    simp only [u]
    omega
  have hlowR : u ^ r ≤ n.descFactorial r := by
    calc
      u ^ r ≤ (n + 1 - r) ^ r := Nat.pow_le_pow_left hur r
      _ ≤ n.descFactorial r := Nat.pow_sub_le_descFactorial n r
  have hdenNat : u ^ (r + s) ≤ n.descFactorial r * n.descFactorial s := by
    rw [pow_add]
    exact Nat.mul_le_mul hlowR hlowS
  have hrsum : r + s ≤ 2 * s := by omega
  have hratio_exp : ((n : ℝ) / u) ^ (r + s) ≤ Real.exp 1 := by
    have huR : (0 : ℝ) < u := by exact_mod_cast hu_pos
    have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
    have hratio_pos : (0 : ℝ) < (n : ℝ) / u := div_pos hnR huR
    have hratio_eq : (n : ℝ) / u = 1 + (s : ℝ) / u := by
      have hnu : n = u + s := by simp [u, Nat.sub_add_cancel hsn]
      rw [hnu, Nat.cast_add, add_div]
      simp [huR.ne']
    have hlog : Real.log ((n : ℝ) / u) ≤ (s : ℝ) / u := by
      calc
        Real.log ((n : ℝ) / u) ≤ (n : ℝ) / u - 1 :=
          Real.log_le_sub_one_of_pos hratio_pos
        _ = (s : ℝ) / u := by rw [hratio_eq]; ring
    have hfrac : ((r + s : ℕ) : ℝ) * ((s : ℝ) / u) ≤ 1 := by
      have huLowerNat : 2 * s ^ 2 ≤ u := by
        have hs_sq : s ≤ 2 * s ^ 2 := by
          calc
            s = s * 1 := by omega
            _ ≤ s * s := Nat.mul_le_mul_left s (Nat.succ_le_iff.mpr hspos)
            _ ≤ 2 * s ^ 2 := by nlinarith
        dsimp [u]
        omega
      have hrsumR : ((r + s : ℕ) : ℝ) ≤ 2 * s := by exact_mod_cast hrsum
      have hsR : (0 : ℝ) ≤ s := by positivity
      have huR' : (0 : ℝ) < u := by exact_mod_cast hu_pos
      calc
        ((r + s : ℕ) : ℝ) * ((s : ℝ) / u) =
            (((r + s : ℕ) : ℝ) * s) / u := by ring
        _ ≤ 1 := (div_le_one huR').2 (by
          calc
            ((r + s : ℕ) : ℝ) * s ≤ (2 * s : ℝ) * s :=
              mul_le_mul_of_nonneg_right hrsumR hsR
            _ ≤ u := by
              norm_cast
              convert huLowerNat using 1 <;> simp [pow_two, mul_assoc])
    have hlogN : ((r + s : ℕ) : ℝ) * Real.log ((n : ℝ) / u) ≤ 1 :=
      (mul_le_mul_of_nonneg_left hlog (by positivity)).trans hfrac
    calc
      ((n : ℝ) / u) ^ (r + s) =
          Real.exp (((r + s : ℕ) : ℝ) * Real.log ((n : ℝ) / u)) := by
        rw [← Real.log_pow, Real.exp_log (pow_pos hratio_pos _)]
      _ ≤ Real.exp 1 := Real.exp_le_exp.mpr hlogN
  have hpow_ratio : (n : ℝ) ^ (r + s) / (u : ℝ) ^ (r + s) ≤ Real.exp 1 := by
    simpa [div_pow] using hratio_exp
  have hdenpos : (0 : ℝ) < (n.descFactorial r : ℝ) * n.descFactorial s := by
    have hrn : r ≤ n := hrs.trans hsn
    have hrp : (0 : ℝ) < n.descFactorial r := by
      exact_mod_cast (Nat.descFactorial_pos.mpr hrn)
    have hsp : (0 : ℝ) < n.descFactorial s := by
      exact_mod_cast (Nat.descFactorial_pos.mpr hsn)
    exact mul_pos hrp hsp
  have huPowPos : (0 : ℝ) < (u : ℝ) ^ (r + s) := by positivity
  have hnPowPos : (0 : ℝ) < (n : ℝ) ^ h := by positivity
  have hnum : (n.descFactorial (r + s - h) : ℝ) ≤
      (n : ℝ) ^ (r + s - h) := by exact_mod_cast hnumNat
  have hden : (u : ℝ) ^ (r + s) ≤
      (n.descFactorial r : ℝ) * n.descFactorial s := by exact_mod_cast hdenNat
  calc
    (n.descFactorial (r + s - h) : ℝ) /
        ((n.descFactorial r : ℝ) * n.descFactorial s) ≤
        (n : ℝ) ^ (r + s - h) / (u : ℝ) ^ (r + s) := by
      calc
        (n.descFactorial (r + s - h) : ℝ) /
            ((n.descFactorial r : ℝ) * n.descFactorial s) ≤
            (n : ℝ) ^ (r + s - h) /
              ((n.descFactorial r : ℝ) * n.descFactorial s) :=
          div_le_div_of_nonneg_right hnum hdenpos.le
        _ ≤ (n : ℝ) ^ (r + s - h) / (u : ℝ) ^ (r + s) :=
          div_le_div_of_nonneg_left (by positivity) huPowPos hden
    _ = ((n : ℝ) ^ (r + s) / (u : ℝ) ^ (r + s)) / (n : ℝ) ^ h := by
      have hhsum : h ≤ r + s := hh.trans (Nat.le_add_left s r)
      rw [← pow_sub_mul_pow (n : ℝ) hhsum]
      field_simp
    _ ≤ Real.exp 1 / (n : ℝ) ^ h :=
      div_le_div_of_nonneg_right hpow_ratio hnPowPos.le

private theorem orderedFactorialDisjointCorrection_le {n r s : ℕ}
    (hrs : r ≤ s) (hn : 4 * s ^ 2 ≤ n) :
    |(n.descFactorial (r + s) : ℝ) /
        ((n.descFactorial r : ℝ) * (n.descFactorial s : ℝ)) - 1| ≤
      2 * (s : ℝ) ^ 2 / n := by
  by_cases hs0 : s = 0
  · subst s
    have hr0 : r = 0 := by omega
    subst r
    norm_num
  have hspos : 0 < s := Nat.pos_of_ne_zero hs0
  have hnpos : 0 < n := lt_of_lt_of_le (by positivity : 0 < 4 * s ^ 2) hn
  have hsn : s ≤ n := by nlinarith [sq_nonneg (s : ℝ)]
  have h2sn : 2 * s ≤ n := by
    have hs_sq' : s ≤ s ^ 2 := by
      calc
        s = s * 1 := by omega
        _ ≤ s * s := Nat.mul_le_mul_left s (Nat.succ_le_iff.mpr hspos)
        _ = s ^ 2 := by ring
    omega
  have hrn : r ≤ n := hrs.trans hsn
  have hfac : (n - r).descFactorial s * n.descFactorial r =
      n.descFactorial (r + s) := by
    simpa using Nat.descFactorial_mul_descFactorial (n := n)
      (k := r) (m := r + s) (Nat.le_add_right r s)
  have hfrpos : (0 : ℝ) < n.descFactorial r := by
    exact_mod_cast (Nat.descFactorial_pos.mpr hrn)
  have hfspos : (0 : ℝ) < n.descFactorial s := by
    exact_mod_cast (Nat.descFactorial_pos.mpr hsn)
  have hratio_eq : (n.descFactorial (r + s) : ℝ) /
        ((n.descFactorial r : ℝ) * n.descFactorial s) =
      (n - r).descFactorial s / (n.descFactorial s : ℝ) := by
    rw [← hfac]
    push_cast
    field_simp
  have hratio_le_one : (n.descFactorial (r + s) : ℝ) /
        ((n.descFactorial r : ℝ) * n.descFactorial s) ≤ 1 := by
    rw [hratio_eq]
    apply (div_le_one hfspos).2
    exact_mod_cast Nat.descFactorial_le s (Nat.sub_le n r)
  have hbaseNat : n - 2 * s ≤ n - r + 1 - s := by omega
  have hlowNumNat : (n - 2 * s) ^ s ≤ (n - r).descFactorial s := by
    calc
      (n - 2 * s) ^ s ≤ (n - r + 1 - s) ^ s := Nat.pow_le_pow_left hbaseNat s
      _ ≤ (n - r).descFactorial s := Nat.pow_sub_le_descFactorial (n - r) s
  have hdenUpperNat : n.descFactorial s ≤ n ^ s := Nat.descFactorial_le_pow n s
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hratio_lower : ((n : ℝ) - 2 * s) ^ s / (n : ℝ) ^ s ≤
      (n.descFactorial (r + s) : ℝ) /
        ((n.descFactorial r : ℝ) * n.descFactorial s) := by
    rw [hratio_eq]
    have hnumR : ((n : ℝ) - 2 * s) ^ s ≤ ((n - r).descFactorial s : ℝ) := by
      have hcast : ((n - 2 * s : ℕ) : ℝ) = (n : ℝ) - 2 * s := by
        rw [Nat.cast_sub h2sn]
        push_cast
        ring
      rw [← hcast]
      exact_mod_cast hlowNumNat
    have hdenR : (n.descFactorial s : ℝ) ≤ (n : ℝ) ^ s := by
      exact_mod_cast hdenUpperNat
    calc
      ((n : ℝ) - 2 * s) ^ s / (n : ℝ) ^ s ≤
          ((n - r).descFactorial s : ℝ) / (n : ℝ) ^ s :=
        div_le_div_of_nonneg_right hnumR (by positivity)
      _ ≤ ((n - r).descFactorial s : ℝ) / n.descFactorial s :=
        div_le_div_of_nonneg_left (by positivity) hfspos hdenR
  have hbern : 1 - 2 * (s : ℝ) ^ 2 / n ≤
      ((n : ℝ) - 2 * s) ^ s / (n : ℝ) ^ s := by
    have hx : (-1 : ℝ) ≤ -2 * (s : ℝ) / n := by
      apply (le_div_iff₀ hnR).2
      have h2snR : (2 : ℝ) * s ≤ n := by exact_mod_cast h2sn
      nlinarith
    have hb := one_add_mul_le_pow ((by norm_num : (-2 : ℝ) ≤ -1).trans hx) s
    have heq : (1 + (-2 * (s : ℝ) / n)) ^ s =
        ((n : ℝ) - 2 * s) ^ s / (n : ℝ) ^ s := by
      rw [← div_pow]
      congr 1
      field_simp
      ring
    rw [← heq]
    exact le_trans (le_of_eq (by ring)) hb
  rw [abs_of_nonpos (sub_nonpos.mpr hratio_le_one)]
  linarith [hbern.trans hratio_lower]

/-- For [sample size `n`, orders `r` and `s`, common order bound `R`, and overlap
size `h`](hyp:n,r,s,R,h), if [the first order is at most `R`](hyp:hr), [the
second order is at most `R`](hyp:hs), [the sample size is at least four times
`R` squared](hyp:hn), and [the overlap fits inside both orders](hyp:hh), [the
mixed falling-factorial ratio is at most `exp(1)` divided by `n` to the overlap
size](goal). -/
theorem factorialMatchingRatio_le {n r s R h : ℕ}
    (hr : r ≤ R) (hs : s ≤ R) (hn : 4 * R ^ 2 ≤ n) (hh : h ≤ min r s) :
    (n.descFactorial (r + s - h) : ℝ) /
        ((n.descFactorial r : ℝ) * (n.descFactorial s : ℝ)) ≤
      Real.exp 1 / (n : ℝ) ^ h := by
  rcases le_total r s with hrs | hsr
  · exact orderedFactorialMatchingRatio_le hrs (by nlinarith) (hh.trans (min_le_right _ _))
  · simpa [Nat.add_comm, mul_comm] using
      (orderedFactorialMatchingRatio_le hsr (by nlinarith)
        (hh.trans (min_le_left _ _)))

/-- For [sample size `n`, orders `r` and `s`, common order bound `R`, and overlap
size `h`](hyp:n,r,s,R,h), [a partial matching](hyp:M) has normalization at most
`exp(1)` divided by `n` to the overlap size when [the first order is at most
`R`](hyp:hr), [the second order is at most `R`](hyp:hs), [the sample size is at
least four times `R` squared](hyp:hn), and [the matching has size `h`](hyp:hM)
[as claimed](goal). -/
theorem matchingNormalization_le {n r s R h : ℕ} {M : PartialMatching r s}
    (hr : r ≤ R) (hs : s ≤ R) (hn : 4 * R ^ 2 ≤ n)
    (hM : M ∈ partialMatchingsOfSize r s h) :
    matchingNormalization n M ≤ Real.exp 1 / (n : ℝ) ^ h := by
  have hh : h ≤ min r s := by
    simpa [(mem_partialMatchingsOfSize M).mp hM] using M.size_le_min
  rw [matchingNormalization_of_mem hM]
  exact factorialMatchingRatio_le hr hs hn hh

/-- For [sample size `n`, orders `r` and `s`, and common order bound `R`](hyp:n,r,s,R),
if [the first order is at most `R`](hyp:hr), [the second order is at most
`R`](hyp:hs), and [the sample size is at least four times `R` squared](hyp:hn),
[the absolute disjoint normalization correction is at most twice `R` squared
divided by `n`](goal). -/
theorem factorialDisjointCorrection_le {n r s R : ℕ}
    (hr : r ≤ R) (hs : s ≤ R) (hn : 4 * R ^ 2 ≤ n) :
    |(n.descFactorial (r + s) : ℝ) /
        ((n.descFactorial r : ℝ) * (n.descFactorial s : ℝ)) - 1| ≤
      2 * (R : ℝ) ^ 2 / n := by
  rcases le_total r s with hrs | hsr
  · calc
      |(n.descFactorial (r + s) : ℝ) /
          ((n.descFactorial r : ℝ) * (n.descFactorial s : ℝ)) - 1| ≤
          2 * (s : ℝ) ^ 2 / n := orderedFactorialDisjointCorrection_le hrs (by nlinarith)
      _ ≤ 2 * (R : ℝ) ^ 2 / n := by
        have hnum : 2 * s ^ 2 ≤ 2 * R ^ 2 :=
          Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hs 2)
        apply div_le_div_of_nonneg_right (by exact_mod_cast hnum) (by positivity)
  · calc
      |(n.descFactorial (r + s) : ℝ) /
          ((n.descFactorial r : ℝ) * (n.descFactorial s : ℝ)) - 1| =
          |(n.descFactorial (s + r) : ℝ) /
            ((n.descFactorial s : ℝ) * (n.descFactorial r : ℝ)) - 1| := by
              simp [Nat.add_comm, mul_comm]
      _ ≤ 2 * (r : ℝ) ^ 2 / n := orderedFactorialDisjointCorrection_le hsr (by nlinarith)
      _ ≤ 2 * (R : ℝ) ^ 2 / n := by
        have hnum : 2 * r ^ 2 ≤ 2 * R ^ 2 :=
          Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hr 2)
        apply div_le_div_of_nonneg_right (by exact_mod_cast hnum) (by positivity)

/-- For [sample size `n`, orders `r` and `s`, and common order bound `R`](hyp:n,r,s,R),
if [the first order is at most `R`](hyp:hr), [the second order is at most
`R`](hyp:hs), and [the sample size is at least four times `R` squared](hyp:hn),
[the empty partial matching's normalization differs from one by at most twice
`R` squared divided by `n`](goal). -/
theorem emptyMatchingNormalization_sub_one_le {n r s R : ℕ}
    (hr : r ≤ R) (hs : s ≤ R) (hn : 4 * R ^ 2 ≤ n) :
    |matchingNormalization n (PartialMatching.empty r s) - 1| ≤
      2 * (R : ℝ) ^ 2 / n := by
  rw [matchingNormalization]
  simp only [PartialMatching.empty_size, Nat.sub_zero]
  exact factorialDisjointCorrection_le hr hs hn

end Causalean.Stat
