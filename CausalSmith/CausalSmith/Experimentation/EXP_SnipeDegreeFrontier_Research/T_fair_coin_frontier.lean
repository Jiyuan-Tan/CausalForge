import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Basic
import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.T_bounded_outcome_frontier

/-!
# Fair-coin energy frontier

At probability one half the even Bernoulli contrasts cancel, leaving four
times the sum of the eligible odd binomial coefficients.
-/

open scoped BigOperators

namespace CausalSmith.Experimentation.SnipeDegreeFrontier

/-- Largest odd integer no greater than `k`, with zero at `k = 0`. -/
noncomputable def largestOddLE (k : ℕ) : ℕ :=
  let odds : Finset ℕ := (Finset.Icc 1 k).filter Odd
  if h : odds.Nonempty then odds.max' h else 0

/-- At a fair coin, the Bernoulli contrast vanishes exactly at even orders. -/
lemma fairCoinContrast (r : ℕ) :
    bernoulliContrast (1 / 2 : ℝ) r =
      if Odd r then 2 ^ (1 - (r : ℤ)) else 0 := by
  rw [bernoulliContrast]
  norm_num only [one_div, one_sub_div, one_mul, OfNat.ofNat]
  rw [show -(1 / 2 : ℝ) = (-1) * (1 / 2 : ℝ) by ring, mul_pow]
  by_cases hodd : Odd r
  · rw [if_pos hodd, hodd.neg_one_pow]
    rw [neg_one_mul]
    have hpow : (2 : ℝ) ^ (1 - (r : ℤ)) = 2 * ((2 : ℝ) ^ r)⁻¹ := by
      rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one, zpow_natCast]
      simp only [div_eq_mul_inv]
    rw [hpow, one_div_pow]
    ring
  · rw [if_neg hodd]
    have heven : Even r := Nat.not_odd_iff_even.mp hodd
    rw [heven.neg_one_pow]
    ring

/-- Each exposed fair-coin order contributes four times its binomial count. -/
lemma fairCoinEnergy (β d : ℕ) :
    blockEnergy β (1 / 2 : ℝ) d =
      4 * ∑ r ∈ (Finset.Icc 1 (effBeta β d)).filter Odd,
        (Nat.choose d r : ℝ) := by
  have hterm (r : ℕ) (hr : 1 ≤ r) :
      (Nat.choose d r : ℝ) * (bernoulliContrast (1 / 2 : ℝ) r) ^ 2 /
          ((1 / 2 : ℝ) * (1 - 1 / 2)) ^ r =
        if Odd r then 4 * (Nat.choose d r : ℝ) else 0 := by
    rw [fairCoinContrast r]
    by_cases hodd : Odd r
    · rw [if_pos hodd, if_pos hodd]
      norm_num only [one_div, one_sub_div, one_mul]
      rw [show (2 : ℝ) ^ (1 - (r : ℤ)) =
          2 * ((2 : ℝ) ^ r)⁻¹ by
            rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one, zpow_natCast]
            simp only [div_eq_mul_inv]]
      rw [one_div_pow]
      field_simp
      have hfour : (4 : ℝ) ^ r = 2 ^ (r * 2) := by
        calc
          (4 : ℝ) ^ r = ((2 : ℝ) ^ 2) ^ r := by norm_num
          _ = 2 ^ (2 * r) := (pow_mul 2 2 r).symm
          _ = 2 ^ (r * 2) := by rw [Nat.mul_comm]
      have htwo : ((2 : ℝ) ^ r) ^ 2 = 2 ^ (r * 2) :=
        (pow_mul 2 r 2).symm
      rw [hfour, htwo]
      ring
    · rw [if_neg hodd, if_neg hodd]
      ring
  rw [blockEnergy, Finset.mul_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro r hr
  rw [hterm r (Finset.mem_Icc.mp hr).1]

/-- The largest exposed fair-coin order is the largest eligible odd order. -/
lemma fairCoinKStar (d β : ℕ) :
    kStar d β (1 / 2 : ℝ) = largestOddLE (effBeta β d) := by
  have hset :
      (Finset.Icc 1 (effBeta β d)).filter
          (fun r => bernoulliContrast (1 / 2 : ℝ) r ≠ 0) =
        (Finset.Icc 1 (effBeta β d)).filter Odd := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_Icc]
    by_cases hr : 1 ≤ r ∧ r ≤ effBeta β d
    · simp only [hr, true_and]
      rw [fairCoinContrast r]
      by_cases hodd : Odd r
      · simp [hodd, zpow_ne_zero (1 - (r : ℤ)) (by norm_num : (2 : ℝ) ≠ 0)]
      · simp [hodd]
    · simp [hr]
  unfold kStar largestOddLE
  rw [hset]

/-- The fair-coin cancellation identity and its linear-interference frontier. -/
-- @node: thm:fair-coin-energy-frontier
theorem fair_coin_energy_frontier :
    (∀ (n d β : ℕ) (B : ℝ),
      1 ≤ n → 1 ≤ d → DegreeIndex (Fin n) d → 1 ≤ β → 0 ≤ B →
      (∀ r : ℕ, 1 ≤ r →
        bernoulliContrast (1 / 2 : ℝ) r =
          if Odd r then 2 ^ (1 - (r : ℤ)) else 0) ∧
      blockEnergy β (1 / 2 : ℝ) d =
        4 * ∑ r ∈ (Finset.Icc 1 (effBeta β d)).filter Odd,
          (Nat.choose d r : ℝ) ∧
      kStar d β (1 / 2 : ℝ) = largestOddLE (effBeta β d)) ∧
    ∃ cLower cUpper : ℝ,
      0 < cLower ∧ cLower ≤ cUpper ∧
      ∀ (n d : ℕ) (B : ℝ),
        1 ≤ n → 1 ≤ d → DegreeIndex (Fin n) d → 0 ≤ B →
        blockEnergy 1 (1 / 2 : ℝ) d = 4 * d ∧
        cLower * B ^ 2 * min 1 ((d : ℝ) ^ 2 / n) ≤
          minimaxRisk (V := Fin n) (1 / 2 : ℝ) (by norm_num) (by norm_num)
            d 1 B ∧
        minimaxRisk (V := Fin n) (1 / 2 : ℝ) (by norm_num) (by norm_num)
            d 1 B =
          minimaxRiskL1 (V := Fin n) (1 / 2 : ℝ) (by norm_num) (by norm_num)
            d 1 B ∧
        minimaxRiskL1 (V := Fin n) (1 / 2 : ℝ) (by norm_num) (by norm_num)
            d 1 B ≤
          minimaxRiskBddOutcome (V := Fin n) (1 / 2 : ℝ)
            (by norm_num) (by norm_num) d 1 B ∧
        minimaxRiskBddOutcome (V := Fin n) (1 / 2 : ℝ)
            (by norm_num) (by norm_num) d 1 B ≤
          cUpper * B ^ 2 * min 1 ((d : ℝ) ^ 2 / n) ∧
        (d ∣ n →
          worstRisk (V := Fin n) (1 / 2 : ℝ) (by norm_num) (by norm_num)
              d 1 B (snipeEstimator 1 (1 / 2 : ℝ)) =
            4 * B ^ 2 * d ^ 2 / n ∧
          worstRiskBdd (V := Fin n) (1 / 2 : ℝ) (by norm_num) (by norm_num)
              d 1 B (snipeEstimator 1 (1 / 2 : ℝ)) =
            4 * B ^ 2 * d ^ 2 / n) := by
  constructor
  · intro n d β B _hn _hd _hdeg _hβ _hB
    exact ⟨fun r _hr => fairCoinContrast r, fairCoinEnergy β d,
      fairCoinKStar d β⟩
  · obtain ⟨cLower, cUpper, hcLower, hconstants, hfrontier⟩ :=
      bounded_outcome_degree_frontier 1 (1 / 2 : ℝ)
        (by omega) (by norm_num) (by norm_num)
    refine ⟨cLower, 4 * cUpper, hcLower, ?_, ?_⟩
    · have hcUpper : 0 < cUpper := lt_of_lt_of_le hcLower hconstants
      nlinarith
    · intro n d B hn hd hdeg hB
      let D : Causalean.Experimentation.DesignBased.FiniteDesign (Fin n → Bool) :=
        blockDesign n (1 / 2 : ℝ) (by norm_num) (by norm_num)
      have hD : IsProductBernoulli D (1 / 2 : ℝ) := by
        refine ⟨by norm_num, by norm_num, ?_⟩
        refine ⟨fun _ => by norm_num, fun _ => by norm_num, ?_⟩
        rfl
      obtain ⟨_hinc, _hstrict, hlower, hriskEq, hclassMono,
          hbddToWorst, hworstUpper, _hl1Upper, _hunbiasedL1, _hunbiasedBdd,
          _hsnipeL1, _hsnipeBdd, _hlocalL1, _hlocalBdd, _hchooseLower,
          _hchooseUpper, hexact, _hmixture⟩ :=
        hfrontier n D d B hn hdeg hB hD
      have henergy : blockEnergy 1 (1 / 2 : ℝ) d = 4 * d := by
        rw [fairCoinEnergy]
        rw [show effBeta 1 d = 1 by simp [effBeta, Nat.min_eq_left hd]]
        have hfilter : (Finset.Icc 1 1).filter Odd = {1} := by
          ext r
          simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
          constructor
          · exact fun h => Nat.le_antisymm h.1.2 h.1.1
          · intro hr
            subst r
            exact ⟨⟨le_rfl, le_rfl⟩, by decide⟩
        rw [hfilter]
        simp
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
      let x : ℝ := (d : ℝ) ^ 2 / n
      have hx : 0 ≤ x := by
        dsimp [x]
        positivity
      have henergyArg :
          (d : ℝ) * blockEnergy 1 (1 / 2 : ℝ) d / n = 4 * x := by
        rw [henergy]
        dsimp [x]
        ring
      have hminLower : min 1 x ≤ min 1 (4 * x) := by
        exact min_le_min_left 1 (by nlinarith)
      have hminUpper : min 1 (4 * x) ≤ 4 * min 1 x := by
        by_cases hx1 : x ≤ 1
        · rw [min_eq_right hx1]
          by_cases h4x : 4 * x ≤ 1
          · rw [min_eq_right h4x]
          · rw [min_eq_left (le_of_not_ge h4x)]
            nlinarith
        · rw [min_eq_left (le_of_not_ge hx1)]
          exact min_le_of_left_le (by norm_num)
      have hcoef : 0 ≤ cLower * B ^ 2 := by positivity
      have hlower' :
          cLower * B ^ 2 * min 1 x ≤
            minimaxRisk (V := Fin n) (1 / 2 : ℝ)
              (by norm_num) (by norm_num) d 1 B := by
        calc
          cLower * B ^ 2 * min 1 x ≤
              cLower * B ^ 2 * min 1 (4 * x) :=
            mul_le_mul_of_nonneg_left hminLower hcoef
          _ = cLower * B ^ 2 *
                min 1 ((d : ℝ) * blockEnergy 1 (1 / 2 : ℝ) d / n) := by
              rw [henergyArg]
          _ ≤ minimaxRiskL1 (V := Fin n) (1 / 2 : ℝ)
                (by norm_num) (by norm_num) d 1 B := hlower
          _ = minimaxRisk (V := Fin n) (1 / 2 : ℝ)
                (by norm_num) (by norm_num) d 1 B := hriskEq
      have hcUpper : 0 ≤ cUpper := le_of_lt (lt_of_lt_of_le hcLower hconstants)
      have hupper' :
          minimaxRiskBddOutcome (V := Fin n) (1 / 2 : ℝ)
              (by norm_num) (by norm_num) d 1 B ≤
            (4 * cUpper) * B ^ 2 * min 1 x := by
        calc
          minimaxRiskBddOutcome (V := Fin n) (1 / 2 : ℝ)
                (by norm_num) (by norm_num) d 1 B ≤
              worstRiskBdd (V := Fin n) (1 / 2 : ℝ)
                (by norm_num) (by norm_num) d 1 B
                (snipeClippedBdd B 1 (1 / 2 : ℝ)) := hbddToWorst
          _ ≤ cUpper * B ^ 2 *
                min 1 ((d : ℝ) * blockEnergy 1 (1 / 2 : ℝ) d / n) :=
              hworstUpper
          _ = cUpper * B ^ 2 * min 1 (4 * x) := by rw [henergyArg]
          _ ≤ cUpper * B ^ 2 * (4 * min 1 x) :=
              mul_le_mul_of_nonneg_left hminUpper (by positivity)
          _ = (4 * cUpper) * B ^ 2 * min 1 x := by ring
      refine ⟨henergy, ?_, hriskEq, hclassMono, hupper', ?_⟩
      · simpa [x] using hlower'
      · intro hdiv
        obtain ⟨_hfixedL1, _hfixedBdd, hglobalL1, hglobalBdd, hratio⟩ :=
          hexact hd hdiv
        constructor
        · rw [hglobalL1, hratio, henergy]
          ring
        · rw [hglobalBdd, hratio, henergy]
          ring

/-- The bounded-outcome minimax mean-squared risk is unchanged when the assignment
probability, its bounds, the degree and interaction parameters, and the outcome bound are
replaced by equal values. -/
add_decl_doc minimaxRiskBddOutcome.congr_simp

end CausalSmith.Experimentation.SnipeDegreeFrontier
