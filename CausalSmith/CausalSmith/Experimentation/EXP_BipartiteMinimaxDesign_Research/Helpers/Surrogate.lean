/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Surrogate-certificate finite product and envelope-sandwich helpers
-/

import CausalSmith.Experimentation.EXP_BipartiteMinimaxDesign_Research.Envelope
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

open scoped BigOperators
open Finset

namespace CausalSmith.Experimentation.BipartiteMinimaxDesign

variable {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I]

-- @node: average_le_prod_of_one_le
/-- For positive factors all at least one, their arithmetic average does not exceed their product. -/
lemma average_le_prod_of_one_le (S : Finset I) (a : I → ℝ)
    (hS : 0 < S.card) (ha : ∀ k ∈ S, 1 ≤ a k) :
    (S.card : ℝ)⁻¹ * (∑ k ∈ S, a k) ≤ ∏ k ∈ S, a k := by
  classical
  have hsingle : ∀ k ∈ S, a k ≤ ∏ l ∈ S, a l := by
    intro k hk
    rw [Finset.prod_eq_mul_prod_diff_singleton_of_mem hk]
    have hprod : 1 ≤ ∏ l ∈ S \ {k}, a l := by
      have hcmp : (∏ l ∈ S \ {k}, (1 : ℝ)) ≤ ∏ l ∈ S \ {k}, a l := by
        refine Finset.prod_le_prod ?_ ?_
        · intro l hl
          exact zero_le_one
        · intro l hl
          exact ha l (Finset.mem_sdiff.mp hl).1
      simpa using hcmp
    have hak : 0 ≤ a k := le_trans zero_le_one (ha k hk)
    calc
      a k = a k * 1 := by ring
      _ ≤ a k * (∏ l ∈ S \ {k}, a l) := mul_le_mul_of_nonneg_left hprod hak
  have hsum : (∑ k ∈ S, a k) ≤ ∑ k ∈ S, (∏ l ∈ S, a l) :=
    Finset.sum_le_sum (fun k hk => hsingle k hk)
  have hcard_nonneg : 0 ≤ (S.card : ℝ)⁻¹ := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hsum hcard_nonneg
  calc
    (S.card : ℝ)⁻¹ * (∑ k ∈ S, a k)
        ≤ (S.card : ℝ)⁻¹ * (∑ k ∈ S, (∏ l ∈ S, a l)) := hscaled
    _ = (∏ l ∈ S, a l) := by
      have hcard_ne : (S.card : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hS)
      simp [hcard_ne]

-- @node: prod_le_const_mul_average
/-- If removing any one nonnegative factor leaves a product bounded by a constant, the full product is bounded by that constant times the factors' average. -/
lemma prod_le_const_mul_average (S : Finset I) (a : I → ℝ) (K : ℝ)
    (hS : 0 < S.card) (ha0 : ∀ k ∈ S, 0 ≤ a k)
    (hK : ∀ k ∈ S, ∏ l ∈ S \ {k}, a l ≤ K) :
    ∏ k ∈ S, a k ≤ K * ((S.card : ℝ)⁻¹ * (∑ k ∈ S, a k)) := by
  classical
  have hpoint : ∀ k ∈ S, (∏ l ∈ S, a l) ≤ a k * K := by
    intro k hk
    rw [Finset.prod_eq_mul_prod_diff_singleton_of_mem hk]
    exact mul_le_mul_of_nonneg_left (hK k hk) (ha0 k hk)
  have hsum : (∑ k ∈ S, (∏ l ∈ S, a l)) ≤ ∑ k ∈ S, a k * K :=
    Finset.sum_le_sum (fun k hk => hpoint k hk)
  have hcard_ne : (S.card : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hS)
  have hcard_nonneg : 0 ≤ (S.card : ℝ)⁻¹ := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hsum hcard_nonneg
  calc
    ∏ k ∈ S, a k = (S.card : ℝ)⁻¹ * (∑ k ∈ S, (∏ l ∈ S, a l)) := by
      simp [hcard_ne]
    _ ≤ (S.card : ℝ)⁻¹ * (∑ k ∈ S, a k * K) := hscaled
    _ = K * ((S.card : ℝ)⁻¹ * (∑ k ∈ S, a k)) := by
      rw [← Finset.sum_mul]
      ring

-- @node: prod_sdiff_le_inv_pow_card_sub_one
/-- If every propensity is at least the design floor, the product of reciprocals after omitting one member of a set is bounded by the floor raised to minus the set size plus one. -/
lemma prod_sdiff_le_inv_pow_card_sub_one (S : Finset I) (a : I → ℝ) (ε : ℝ)
    (ha0 : ∀ k ∈ S, 0 ≤ a k) (haε : ∀ k ∈ S, a k ≤ ε⁻¹)
    {k : I} (hk : k ∈ S) :
    ∏ l ∈ S \ {k}, a l ≤ ε⁻¹ ^ (S.card - 1) := by
  classical
  have hcmp : (∏ l ∈ S \ {k}, a l) ≤ ∏ l ∈ S \ {k}, ε⁻¹ := by
    refine Finset.prod_le_prod ?_ ?_
    · intro l hl
      exact ha0 l (Finset.mem_sdiff.mp hl).1
    · intro l hl
      exact haε l (Finset.mem_sdiff.mp hl).1
  calc
    ∏ l ∈ S \ {k}, a l ≤ ∏ l ∈ S \ {k}, ε⁻¹ := hcmp
    _ = ε⁻¹ ^ (S.card - 1) := by
      rw [Finset.prod_const]
      congr 1
      rw [Finset.card_sdiff_of_subset]
      · simp
      · simpa using (Finset.singleton_subset_iff.mpr hk)

-- @node: inv_pow_card_sub_one_le_certificate
/-- For a nonempty set whose size is at most the degree bound, the reciprocal-power bound is no larger than the stated degree-based certificate. -/
lemma inv_pow_card_sub_one_le_certificate (ε dbar : ℝ) (S : Finset I)
    (hε0 : 0 < ε) (hε2 : ε < 1 / 2) (hS : 0 < S.card)
    (hSle : (S.card : ℝ) ≤ dbar) :
    ε⁻¹ ^ (S.card - 1) ≤ max 1 (ε ^ (-(dbar - 1))) := by
  have hεle1 : ε ≤ 1 := by nlinarith
  have hcast : ((S.card - 1 : ℕ) : ℝ) = (S.card : ℝ) - 1 := Nat.cast_pred hS
  have hbase : ε⁻¹ ^ (S.card - 1) = ε ^ (-(((S.card - 1 : ℕ) : ℝ))) := by
    rw [Real.rpow_neg_eq_inv_rpow, Real.rpow_natCast]
  rw [hbase]
  have hexp : -(dbar - 1) ≤ -(((S.card - 1 : ℕ) : ℝ)) := by
    rw [hcast]
    linarith
  have hpow : ε ^ (-(((S.card - 1 : ℕ) : ℝ))) ≤ ε ^ (-(dbar - 1)) :=
    Real.rpow_le_rpow_of_exponent_ge hε0 hεle1 hexp
  exact hpow.trans (le_max_right _ _)

-- @node: surrogateObjective_eq_pairAverage
/-- The surrogate objective equals the average, over outcome pairs sharing an intervention, of the reciprocal treatment and control probabilities. -/
lemma surrogateObjective_eq_pairAverage (E : BipartiteExperiment I O) (q : I → ℝ) :
    E.surrogateObjective q =
      ∑ i : O, ∑ j : O,
        ∑ k ∈ E.shared i j,
          (Fintype.card O : ℝ)⁻¹ *
            (((E.shared i j).card : ℝ)⁻¹ * ((q k)⁻¹ + (1 - q k)⁻¹)) := by
  classical
  unfold BipartiteExperiment.surrogateObjective BipartiteExperiment.hWeight
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  trans ∑ k : I, if k ∈ E.shared i j then
      (Fintype.card O : ℝ)⁻¹ *
        (((E.shared i j).card : ℝ)⁻¹ * ((q k)⁻¹ + (1 - q k)⁻¹)) else 0
  · apply Finset.sum_congr rfl
    intro k _
    by_cases hk : k ∈ E.shared i j <;> simp [hk]
    ring
  · simpa using (Finset.sum_ite_mem (s := (Finset.univ : Finset I)) (t := E.shared i j)
      (f := fun k => (Fintype.card O : ℝ)⁻¹ *
        (((E.shared i j).card : ℝ)⁻¹ * ((q k)⁻¹ + (1 - q k)⁻¹))))

-- @node: varEnvelope_div_four_eq_pairSum
/-- One quarter of the variance envelope equals the sum over outcome pairs of their normalized envelope kernels. -/
lemma varEnvelope_div_four_eq_pairSum (E : BipartiteExperiment I O) (q : I → ℝ) :
    E.varEnvelope q / 4 =
      ∑ i : O, ∑ j : O,
        (Fintype.card O : ℝ)⁻¹ * (E.r1 q i j + E.r0 q i j + 2 * E.r10 i j) := by
  unfold BipartiteExperiment.varEnvelope
  rw [div_eq_mul_inv]
  calc
    (4 * (Fintype.card O : ℝ)⁻¹ * ∑ i : O, ∑ j : O,
        (E.r1 q i j + E.r0 q i j + 2 * E.r10 i j)) * 4⁻¹
        = (Fintype.card O : ℝ)⁻¹ * ∑ i : O, ∑ j : O,
            (E.r1 q i j + E.r0 q i j + 2 * E.r10 i j) := by ring
    _ = ∑ i : O, ∑ j : O,
        (Fintype.card O : ℝ)⁻¹ * (E.r1 q i j + E.r0 q i j + 2 * E.r10 i j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]

-- @node: pairAverage_le_envelopeKernel
/-- For any feasible design, the average reciprocal propensity over a pair's shared interventions is no larger than that pair's envelope kernel. -/
lemma pairAverage_le_envelopeKernel (E : BipartiteExperiment I O)
    (ε B : ℝ) (hε0 : 0 < ε) (q : I → ℝ) (hq : FeasibleDesign ε B q) (i j : O) :
    ((E.shared i j).card : ℝ)⁻¹ *
        (∑ k ∈ E.shared i j, ((q k)⁻¹ + (1 - q k)⁻¹))
      ≤ E.r1 q i j + E.r0 q i j + 2 * E.r10 i j := by
  classical
  by_cases hS : 0 < (E.shared i j).card
  · have ha : ∀ k ∈ E.shared i j, 1 ≤ (q k)⁻¹ := by
      intro k _
      have hqpos : 0 < q k := lt_of_lt_of_le hε0 (hq.floor k).1
      exact (one_le_inv₀ hqpos).mpr (hq.prob k).2
    have hb : ∀ k ∈ E.shared i j, 1 ≤ (1 - q k)⁻¹ := by
      intro k _
      have hq_lt_one : q k < 1 := by linarith [(hq.floor k).2, hε0]
      have hpos : 0 < 1 - q k := sub_pos.mpr hq_lt_one
      have hle : 1 - q k ≤ 1 := by linarith [(hq.prob k).1]
      exact (one_le_inv₀ hpos).mpr hle
    have hA := average_le_prod_of_one_le (E.shared i j) (fun k => (q k)⁻¹) hS ha
    have hB := average_le_prod_of_one_le (E.shared i j) (fun k => (1 - q k)⁻¹) hS hb
    unfold BipartiteExperiment.r1 BipartiteExperiment.r0 BipartiteExperiment.r10
    rw [if_pos hS, if_pos hS, if_pos hS]
    have hsumsplit :
        ((E.shared i j).card : ℝ)⁻¹ *
            (∑ k ∈ E.shared i j, ((q k)⁻¹ + (1 - q k)⁻¹))
          = ((E.shared i j).card : ℝ)⁻¹ * (∑ k ∈ E.shared i j, (q k)⁻¹)
            + ((E.shared i j).card : ℝ)⁻¹ * (∑ k ∈ E.shared i j, (1 - q k)⁻¹) := by
      rw [Finset.sum_add_distrib]
      ring
    rw [hsumsplit]
    linarith
  · have hEmpty : E.shared i j = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_not_pos hS)
    simp [BipartiteExperiment.r1, BipartiteExperiment.r0, BipartiteExperiment.r10, hEmpty]

-- @node: envelopeKernel_le_certificate_pairAverage
/-- Under the degree and floor conditions, each envelope kernel is bounded by a degree-based certificate times the shared-intervention reciprocal average. -/
lemma envelopeKernel_le_certificate_pairAverage (E : BipartiteExperiment I O)
    (ε B dbar : ℝ) (hε0 : 0 < ε) (hε2 : ε < 1 / 2)
    (hdeg : BoundedOutcomeDegree E dbar) (q : I → ℝ) (hq : FeasibleDesign ε B q) (i j : O) :
    E.r1 q i j + E.r0 q i j + 2 * E.r10 i j
      ≤ max 1 (ε ^ (-(dbar - 1))) *
        (((E.shared i j).card : ℝ)⁻¹ *
          (∑ k ∈ E.shared i j, ((q k)⁻¹ + (1 - q k)⁻¹))) := by
  classical
  let C : ℝ := max 1 (ε ^ (-(dbar - 1)))
  by_cases hS : 0 < (E.shared i j).card
  · have hSle : ((E.shared i j).card : ℝ) ≤ dbar := by
      have hnat : (E.shared i j).card ≤ (E.N i).card :=
        Finset.card_le_card Finset.inter_subset_left
      have hreal : ((E.shared i j).card : ℝ) ≤ ((E.N i).card : ℝ) := by exact_mod_cast hnat
      exact hreal.trans (hdeg.2 i)
    have hcert := inv_pow_card_sub_one_le_certificate ε dbar (E.shared i j) hε0 hε2 hS hSle
    have ha0 : ∀ k ∈ E.shared i j, 0 ≤ (q k)⁻¹ := by
      intro k _
      exact inv_nonneg.mpr (hq.prob k).1
    have hb0 : ∀ k ∈ E.shared i j, 0 ≤ (1 - q k)⁻¹ := by
      intro k _
      have hnonneg : 0 ≤ 1 - q k := by linarith [(hq.prob k).2]
      exact inv_nonneg.mpr hnonneg
    have haε : ∀ k ∈ E.shared i j, (q k)⁻¹ ≤ ε⁻¹ := by
      intro k _
      have hqpos : 0 < q k := lt_of_lt_of_le hε0 (hq.floor k).1
      exact (inv_le_inv₀ hqpos hε0).mpr (hq.floor k).1
    have hbε : ∀ k ∈ E.shared i j, (1 - q k)⁻¹ ≤ ε⁻¹ := by
      intro k _
      have hq_lt_one : q k < 1 := by linarith [(hq.floor k).2, hε0]
      have hpos : 0 < 1 - q k := sub_pos.mpr hq_lt_one
      have hfloor : ε ≤ 1 - q k := by linarith [(hq.floor k).2]
      exact (inv_le_inv₀ hpos hε0).mpr hfloor
    have hKa : ∀ k ∈ E.shared i j, ∏ l ∈ E.shared i j \ {k}, (q l)⁻¹ ≤ C := by
      intro k hk
      exact (prod_sdiff_le_inv_pow_card_sub_one (E.shared i j) (fun l => (q l)⁻¹) ε ha0 haε hk).trans hcert
    have hKb : ∀ k ∈ E.shared i j, ∏ l ∈ E.shared i j \ {k}, (1 - q l)⁻¹ ≤ C := by
      intro k hk
      exact (prod_sdiff_le_inv_pow_card_sub_one (E.shared i j) (fun l => (1 - q l)⁻¹) ε hb0 hbε hk).trans hcert
    have hA := prod_le_const_mul_average (E.shared i j) (fun k => (q k)⁻¹) C hS ha0 hKa
    have hB := prod_le_const_mul_average (E.shared i j) (fun k => (1 - q k)⁻¹) C hS hb0 hKb
    unfold BipartiteExperiment.r1 BipartiteExperiment.r0 BipartiteExperiment.r10
    rw [if_pos hS, if_pos hS, if_pos hS]
    have hsumsplit :
        ((E.shared i j).card : ℝ)⁻¹ *
            (∑ k ∈ E.shared i j, ((q k)⁻¹ + (1 - q k)⁻¹))
          = ((E.shared i j).card : ℝ)⁻¹ * (∑ k ∈ E.shared i j, (q k)⁻¹)
            + ((E.shared i j).card : ℝ)⁻¹ * (∑ k ∈ E.shared i j, (1 - q k)⁻¹) := by
      rw [Finset.sum_add_distrib]
      ring
    rw [hsumsplit]
    linarith
  · have hEmpty : E.shared i j = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_not_pos hS)
    simp [BipartiteExperiment.r1, BipartiteExperiment.r0, BipartiteExperiment.r10, hEmpty]

end CausalSmith.Experimentation.BipartiteMinimaxDesign
