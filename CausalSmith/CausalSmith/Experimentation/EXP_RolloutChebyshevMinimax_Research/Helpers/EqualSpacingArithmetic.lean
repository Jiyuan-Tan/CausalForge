/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Equal-spacing arithmetic helpers
-/

import CausalSmith.Experimentation.EXP_RolloutChebyshevMinimax_Research.Helpers.ScheduleGrid
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Choose.Basic

open scoped BigOperators

namespace CausalSmith.Experimentation.RolloutChebyshev

-- @node: prod_Iic_erase_abs_sub_eq_factorial
lemma prod_Iic_erase_abs_sub_eq_factorial (beta i : ℕ) (hi : i ≤ beta) :
    (∏ m ∈ (Finset.Iic beta).erase i, |(i : ℝ) - (m : ℝ)|) =
      (i.factorial : ℝ) * ((beta - i).factorial : ℝ) := by
  classical
  have hunion : (Finset.Iic beta).erase i = Finset.range i ∪ Finset.Ioc i beta := by
    ext m
    simp only [Finset.mem_erase, Finset.mem_Iic, Finset.mem_union, Finset.mem_range,
      Finset.mem_Ioc]
    omega
  have hdisjoint : Disjoint (Finset.range i) (Finset.Ioc i beta) := by
    rw [Finset.disjoint_iff_ne]
    intro a ha b hb
    have hai : a < i := Finset.mem_range.mp ha
    have hib : i < b := (Finset.mem_Ioc.mp hb).1
    omega
  have hleft :
      (∏ m ∈ Finset.range i, |(i : ℝ) - (m : ℝ)|) = (i.factorial : ℝ) := by
    calc
      (∏ m ∈ Finset.range i, |(i : ℝ) - (m : ℝ)|)
          = ∏ m ∈ Finset.range i, (((i - 1 - m) + 1 : ℕ) : ℝ) := by
            refine Finset.prod_congr rfl ?_
            intro m hm
            have hmi : m < i := Finset.mem_range.mp hm
            have hmi_real : (m : ℝ) ≤ (i : ℝ) := by exact_mod_cast Nat.le_of_lt hmi
            have hnonneg : 0 ≤ (i : ℝ) - (m : ℝ) := by linarith
            rw [abs_of_nonneg hnonneg]
            have hn : i - m = (i - 1 - m) + 1 := by omega
            have hsub_eq : (i : ℝ) - (m : ℝ) = ((i - m : ℕ) : ℝ) := by
              have h := Nat.sub_add_cancel (Nat.le_of_lt hmi)
              have hreal : ((i - m : ℕ) : ℝ) + (m : ℝ) = (i : ℝ) := by exact_mod_cast h
              linarith
            rw [hsub_eq]
            exact_mod_cast hn
      _ = ∏ m ∈ Finset.range i, (((m + 1 : ℕ) : ℝ)) := by
            rw [Finset.prod_range_reflect (fun m => (((m + 1 : ℕ) : ℝ))) i]
      _ = (i.factorial : ℝ) := by
            exact_mod_cast Finset.prod_range_add_one_eq_factorial i
  have hright :
      (∏ m ∈ Finset.Ioc i beta, |(i : ℝ) - (m : ℝ)|) =
        ((beta - i).factorial : ℝ) := by
    have hIoc : Finset.Ioc i beta = Finset.Ico (i + 1) (beta + 1) := by
      ext m
      simp only [Finset.mem_Ioc, Finset.mem_Ico]
      omega
    calc
      (∏ m ∈ Finset.Ioc i beta, |(i : ℝ) - (m : ℝ)|)
          = ∏ m ∈ Finset.Ico (i + 1) (beta + 1), |(i : ℝ) - (m : ℝ)| := by
            rw [hIoc]
      _ = ∏ r ∈ Finset.range (beta + 1 - (i + 1)),
            |(i : ℝ) - ((i + 1 + r : ℕ) : ℝ)| := by
            rw [Finset.prod_Ico_eq_prod_range]
      _ = ∏ r ∈ Finset.range (beta - i), (((r + 1 : ℕ) : ℝ)) := by
            refine Finset.prod_congr ?_ ?_
            · congr 1
              omega
            · intro r hr
              have hnonpos : (i : ℝ) - ((i + 1 + r : ℕ) : ℝ) ≤ 0 := by
                have hle : (i : ℝ) ≤ ((i + 1 + r : ℕ) : ℝ) := by
                  exact_mod_cast (by omega : i ≤ i + 1 + r)
                linarith
              rw [abs_of_nonpos hnonpos]
              have hcast : ((i + 1 + r : ℕ) : ℝ) = (i : ℝ) + 1 + (r : ℝ) := by
                norm_num
              have hr : ((r + 1 : ℕ) : ℝ) = (r : ℝ) + 1 := by norm_num
              linarith
      _ = ((beta - i).factorial : ℝ) := by
            exact_mod_cast Finset.prod_range_add_one_eq_factorial (beta - i)
  rw [hunion, Finset.prod_union hdisjoint, hleft, hright]

-- @node: two_pow_le_two_mul_factorial
lemma two_pow_le_two_mul_factorial (n : ℕ) (hn : 1 ≤ n) : 2 ^ n ≤ 2 * n.factorial := by
  induction n with
  | zero => omega
  | succ n ih =>
      cases n with
      | zero => norm_num
      | succ n =>
          have hprev : 2 ^ (n + 1) ≤ 2 * (n + 1).factorial := ih (by omega)
          calc
            2 ^ (n + 2) = 2 * 2 ^ (n + 1) := by ring
            _ ≤ 2 * (2 * (n + 1).factorial) := Nat.mul_le_mul_left 2 hprev
            _ ≤ 2 * (n + 2).factorial := by
              have hmul : 2 * (n + 1).factorial ≤ (n + 2) * (n + 1).factorial :=
                Nat.mul_le_mul_right _ (by omega)
              have hfact : (n + 2).factorial = (n + 2) * (n + 1).factorial := by
                rw [show n + 2 = Nat.succ (n + 1) by omega, Nat.factorial_succ]
              rw [hfact]
              exact Nat.mul_le_mul_left 2 hmul

-- @node: factorial_reciprocal_sum_le_two
lemma factorial_reciprocal_sum_le_two (beta : ℕ) (hbeta : 1 ≤ beta) :
    (∑ j : Fin (beta + 1),
      (1 : ℝ) / ((j.val.factorial : ℝ) * ((beta - j.val).factorial : ℝ))) ≤ 2 := by
  classical
  let f : ℕ → ℝ := fun j =>
    (1 : ℝ) / ((j.factorial : ℝ) * ((beta - j).factorial : ℝ))
  have hterm : ∀ j ∈ Finset.range (beta + 1),
      f j = (beta.choose j : ℝ) / (beta.factorial : ℝ) := by
    intro j hj
    have hjle : j ≤ beta := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    have hchoose :
        (beta.choose j : ℝ) * (j.factorial : ℝ) * ((beta - j).factorial : ℝ) =
          (beta.factorial : ℝ) := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hjle
    have hden_pos : 0 < (j.factorial : ℝ) * ((beta - j).factorial : ℝ) := by positivity
    have hfac_pos : 0 < (beta.factorial : ℝ) := by positivity
    dsimp [f]
    field_simp [ne_of_gt hden_pos, ne_of_gt hfac_pos]
    nlinarith
  have hsum :
      (∑ j ∈ Finset.range (beta + 1), f j) =
        (2 : ℝ) ^ beta / (beta.factorial : ℝ) := by
    calc
      (∑ j ∈ Finset.range (beta + 1), f j)
          = ∑ j ∈ Finset.range (beta + 1), (beta.choose j : ℝ) / (beta.factorial : ℝ) := by
            exact Finset.sum_congr rfl hterm
      _ = (∑ j ∈ Finset.range (beta + 1), (beta.choose j : ℝ)) /
            (beta.factorial : ℝ) := by
            simp [div_eq_mul_inv, Finset.sum_mul]
      _ = (2 : ℝ) ^ beta / (beta.factorial : ℝ) := by
            have hchoose_sum :
                (∑ j ∈ Finset.range (beta + 1), (beta.choose j : ℕ) : ℕ) = 2 ^ beta :=
              Nat.sum_range_choose beta
            have hchoose_sum_real :
                (∑ j ∈ Finset.range (beta + 1), (beta.choose j : ℝ)) =
                  ((2 ^ beta : ℕ) : ℝ) := by
              exact_mod_cast hchoose_sum
            rw [hchoose_sum_real]
            norm_num
  rw [Fin.sum_univ_eq_sum_range f (beta + 1)]
  rw [hsum]
  have hpow_fact_nat := two_pow_le_two_mul_factorial beta hbeta
  have hpow_fact_real : ((2 ^ beta : ℕ) : ℝ) ≤ ((2 * beta.factorial : ℕ) : ℝ) := by
    exact_mod_cast hpow_fact_nat
  have hfac_pos : 0 < (beta.factorial : ℝ) := by positivity
  rw [div_le_iff₀ hfac_pos]
  norm_num at hpow_fact_real ⊢
  exact hpow_fact_real

end CausalSmith.Experimentation.RolloutChebyshev
