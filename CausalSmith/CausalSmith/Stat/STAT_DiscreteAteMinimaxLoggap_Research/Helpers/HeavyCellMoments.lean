import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Basic
import Causalean.Stat.UStatistic.OrderM.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Probability.Distributions.SetBernoulli

namespace CausalSmith.Stat.DiscreteAteMinimaxLoggap

open MeasureTheory
open ProbabilityTheory
open scoped BigOperators ENNReal

/-! Probability and finite-sample algebra used by the ratio branch.  These
lemmas are deliberately stated independently of the calibrated estimator, so
that the handling of an empty empirical treatment arm can be reused. -/

/-- The elementary pointwise inequality behind the inverse-binomial bound.
The indicator is written explicitly to match Lean's total division convention. -/
lemma inverse_count_indicator_le (D : ℕ) :
    (if 0 < D then (D : ℝ)⁻¹ else 0) ≤ 2 * ((D : ℝ) + 1)⁻¹ := by
  by_cases hD : 0 < D
  · simp only [hD, if_true]
    have hDR : (1 : ℝ) ≤ D := by exact_mod_cast hD
    have hDpos : (0 : ℝ) < D := by positivity
    have hD1pos : (0 : ℝ) < (D : ℝ) + 1 := by positivity
    have hfrac : 1 / (D : ℝ) ≤ 2 / ((D : ℝ) + 1) :=
      (div_le_div_iff₀ hDpos hD1pos).2 (by nlinarith)
    simpa only [one_div, div_eq_mul_inv, one_mul] using hfrac
  · have hDz : D = 0 := Nat.eq_zero_of_not_pos hD
    simp [hDz]

/-- Multiplying a binomial coefficient by the reciprocal count shifts the
coefficient from row `t` to row `t+1`. -/
lemma choose_div_succ (t k : ℕ) :
    (Nat.choose t k : ℝ) / (k + 1 : ℕ) =
      (Nat.choose (t + 1) (k + 1) : ℝ) / (t + 1 : ℕ) := by
  have ht : (0 : ℝ) < (t + 1 : ℕ) := by positivity
  have hk : (0 : ℝ) < (k + 1 : ℕ) := by positivity
  apply (div_eq_div_iff (ne_of_gt hk) (ne_of_gt ht)).2
  have hcast : ((t + 1 : ℕ) : ℝ) * (Nat.choose t k : ℝ) =
      (Nat.choose (t + 1) (k + 1) : ℝ) * (k + 1 : ℕ) := by
    exact_mod_cast Nat.add_one_mul_choose_eq t k
  simpa [mul_comm] using hcast

/-- Exact finite-binomial reciprocal identity.  This is equation (2) of the
heavy-cell proof before dropping the numerator. -/
lemma binomial_succ_reciprocal_sum (t : ℕ) (rho : ℝ) (hrho : rho ≠ 0) :
    (∑ k ∈ Finset.range (t + 1),
        (Nat.choose t k : ℝ) * rho ^ k * (1 - rho) ^ (t - k) /
          (k + 1 : ℕ)) =
      (1 - (1 - rho) ^ (t + 1)) / ((t + 1 : ℕ) * rho) := by
  have hrow :
      (∑ k ∈ Finset.range (t + 1),
          (Nat.choose (t + 1) (k + 1) : ℝ) * rho ^ (k + 1) *
            (1 - rho) ^ (t - k)) =
        1 - (1 - rho) ^ (t + 1) := by
    have hbin := add_pow rho (1 - rho) (t + 1)
    rw [show rho + (1 - rho) = 1 by ring, one_pow,
      Finset.sum_range_succ'] at hbin
    have hbin' :
        1 = (∑ k ∈ Finset.range (t + 1),
          (Nat.choose (t + 1) (k + 1) : ℝ) * rho ^ (k + 1) *
            (1 - rho) ^ (t - k)) + (1 - rho) ^ (t + 1) := by
      simpa [Nat.add_sub_add_right, mul_comm, mul_left_comm, mul_assoc] using hbin
    linarith
  apply (eq_div_iff (mul_ne_zero (by positivity) hrho)).2
  rw [Finset.sum_mul]
  calc
    (∑ k ∈ Finset.range (t + 1),
        ((Nat.choose t k : ℝ) * rho ^ k * (1 - rho) ^ (t - k) /
          (k + 1 : ℕ)) * ((t + 1 : ℕ) * rho)) =
        ∑ k ∈ Finset.range (t + 1),
          (Nat.choose (t + 1) (k + 1) : ℝ) * rho ^ (k + 1) *
            (1 - rho) ^ (t - k) := by
      apply Finset.sum_congr rfl
      intro k hk
      calc
        (Nat.choose t k : ℝ) * rho ^ k * (1 - rho) ^ (t - k) /
              (k + 1 : ℕ) * ((t + 1 : ℕ) * rho) =
            ((Nat.choose t k : ℝ) / (k + 1 : ℕ)) * rho ^ k *
              (1 - rho) ^ (t - k) * ((t + 1 : ℕ) * rho) := by ring
        _ = ((Nat.choose (t + 1) (k + 1) : ℝ) / (t + 1 : ℕ)) *
              rho ^ k * (1 - rho) ^ (t - k) * ((t + 1 : ℕ) * rho) := by
            rw [choose_div_succ]
        _ = (Nat.choose (t + 1) (k + 1) : ℝ) * rho ^ (k + 1) *
              (1 - rho) ^ (t - k) := by
            have ht : (((t + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
            field_simp [ht]
            ring
    _ = 1 - (1 - rho) ^ (t + 1) := hrow

/-- The inverse-binomial estimate used for conditional ratio variance. -/
lemma binomial_inverse_count_bound (t : ℕ) (rho : ℝ)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) :
    (∑ k ∈ Finset.range (t + 1),
        (Nat.choose t k : ℝ) * rho ^ k * (1 - rho) ^ (t - k) *
          (if 0 < k then (k : ℝ)⁻¹ else 0)) ≤
      2 / ((t + 1 : ℕ) * rho) := by
  have hnonneg : 0 ≤ 1 - rho := sub_nonneg.mpr hrho1
  have hden : 0 < ((t + 1 : ℕ) : ℝ) * rho := mul_pos (by positivity) hrho
  calc
    (∑ k ∈ Finset.range (t + 1),
        (Nat.choose t k : ℝ) * rho ^ k * (1 - rho) ^ (t - k) *
          (if 0 < k then (k : ℝ)⁻¹ else 0)) ≤
        ∑ k ∈ Finset.range (t + 1),
          (Nat.choose t k : ℝ) * rho ^ k * (1 - rho) ^ (t - k) *
            (2 * ((k : ℝ) + 1)⁻¹) := by
      apply Finset.sum_le_sum
      intro k hk
      apply mul_le_mul_of_nonneg_left (inverse_count_indicator_le k)
      positivity
    _ = 2 * (∑ k ∈ Finset.range (t + 1),
        (Nat.choose t k : ℝ) * rho ^ k * (1 - rho) ^ (t - k) /
          (k + 1 : ℕ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      norm_num [div_eq_mul_inv]
      ring
    _ = 2 * ((1 - (1 - rho) ^ (t + 1)) /
        ((t + 1 : ℕ) * rho)) := by
      rw [binomial_succ_reciprocal_sum t rho (ne_of_gt hrho)]
    _ ≤ 2 / ((t + 1 : ℕ) * rho) := by
      have hpow : 0 ≤ (1 - rho) ^ (t + 1) := pow_nonneg hnonneg _
      have hnum : 1 - (1 - rho) ^ (t + 1) ≤ 1 := by linarith
      rw [show 2 / (((t + 1 : ℕ) : ℝ) * rho) =
          2 * (1 / (((t + 1 : ℕ) : ℝ) * rho)) by ring]
      gcongr

/-- First moment of the finite binomial weights. -/
lemma binomial_first_moment (m : ℕ) (p : ℝ) :
    (∑ t ∈ Finset.range (m + 1),
      (Nat.choose m t : ℝ) * p ^ t * (1 - p) ^ (m - t) * t) =
      (m : ℝ) * p := by
  cases m with
  | zero => simp
  | succ M =>
      rw [Finset.sum_range_succ']
      simp only [Nat.choose_zero_right, pow_zero, Nat.cast_zero, mul_zero,
        zero_add, add_zero, Nat.cast_add, Nat.cast_one]
      calc
        (∑ k ∈ Finset.range (M + 1),
            (Nat.choose (M + 1) (k + 1) : ℝ) * p ^ (k + 1) *
              (1 - p) ^ (M + 1 - (k + 1)) * ((k : ℝ) + 1)) =
            ((M : ℝ) + 1) * p *
              ∑ k ∈ Finset.range (M + 1),
                (Nat.choose M k : ℝ) * p ^ k * (1 - p) ^ (M - k) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          have hkM : k ≤ M := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
          have hchoose :
              (Nat.choose (M + 1) (k + 1) : ℝ) * (k + 1 : ℕ) =
                (M + 1 : ℕ) * (Nat.choose M k : ℝ) := by
            exact_mod_cast (Nat.add_one_mul_choose_eq M k).symm
          norm_num only [Nat.cast_add, Nat.cast_one] at hchoose
          rw [Nat.add_sub_add_right]
          rw [pow_succ]
          calc
            (Nat.choose (M + 1) (k + 1) : ℝ) * (p ^ k * p) *
                (1 - p) ^ (M - k) * ((k : ℝ) + 1) =
              ((Nat.choose (M + 1) (k + 1) : ℝ) * ((k : ℝ) + 1)) *
                p ^ k * p * (1 - p) ^ (M - k) := by ring
            _ = (((M : ℝ) + 1) * (Nat.choose M k : ℝ)) *
                p ^ k * p * (1 - p) ^ (M - k) := by rw [hchoose]
            _ = ((M : ℝ) + 1) * p *
                ((Nat.choose M k : ℝ) * p ^ k *
                  (1 - p) ^ (M - k)) := by ring
        _ = ((M : ℝ) + 1) * p * (p + (1 - p)) ^ M := by
          congr 1
          rw [add_pow]
          apply Finset.sum_congr rfl
          intro k hk
          ring
        _ = ((M : ℝ) + 1) * p := by ring

/-- Pure nested-binomial ratio bound.  This is the complete analytic
calculation after conditioning a category count `N` to equal `t`: the arm
count is binomial with success probability `rho`, and the outer category
count is binomial with success probability `p`. -/
lemma nested_binomial_ratio_bound (m : ℕ) (p rho : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hrho : 0 < rho) (hrho1 : rho ≤ 1) :
    (∑ t ∈ Finset.range (m + 1),
      (Nat.choose m t : ℝ) * p ^ t * (1 - p) ^ (m - t) * (t : ℝ) ^ 2 *
        (∑ l ∈ Finset.range (t + 1),
          (Nat.choose t l : ℝ) * rho ^ l * (1 - rho) ^ (t - l) *
            (if 0 < l then (l : ℝ)⁻¹ else 0))) ≤
      2 * (m : ℝ) * p / rho := by
  calc
    _ ≤ ∑ t ∈ Finset.range (m + 1),
      (Nat.choose m t : ℝ) * p ^ t * (1 - p) ^ (m - t) * (t : ℝ) ^ 2 *
        (2 / ((t + 1 : ℕ) * rho)) := by
      apply Finset.sum_le_sum
      intro t ht
      have hq0 : 0 ≤ 1 - p := sub_nonneg.mpr hp1
      have hbase :
          0 ≤ (Nat.choose m t : ℝ) * p ^ t * (1 - p) ^ (m - t) := by
        positivity
      have hcoef :
          0 ≤ (Nat.choose m t : ℝ) * p ^ t * (1 - p) ^ (m - t) *
            (t : ℝ) ^ 2 := mul_nonneg hbase (sq_nonneg _)
      exact mul_le_mul_of_nonneg_left
        (binomial_inverse_count_bound t rho hrho hrho1) hcoef
    _ ≤ ∑ t ∈ Finset.range (m + 1),
      (Nat.choose m t : ℝ) * p ^ t * (1 - p) ^ (m - t) *
        ((2 / rho) * t) := by
      apply Finset.sum_le_sum
      intro t ht
      have hq0 : 0 ≤ 1 - p := sub_nonneg.mpr hp1
      have hbase :
          0 ≤ (Nat.choose m t : ℝ) * p ^ t * (1 - p) ^ (m - t) := by
        positivity
      have ht0 : (0 : ℝ) ≤ t := by positivity
      have hden : (0 : ℝ) < (t + 1 : ℕ) * rho := by positivity
      calc
        (Nat.choose m t : ℝ) * p ^ t * (1 - p) ^ (m - t) *
            (t : ℝ) ^ 2 * (2 / ((t + 1 : ℕ) * rho)) =
          ((Nat.choose m t : ℝ) * p ^ t * (1 - p) ^ (m - t)) *
            ((t : ℝ) ^ 2 * (2 / ((t + 1 : ℕ) * rho))) := by ring
        _ ≤ ((Nat.choose m t : ℝ) * p ^ t * (1 - p) ^ (m - t)) *
            ((2 / rho) * t) := by
          apply mul_le_mul_of_nonneg_left _ hbase
          calc
            (t : ℝ) ^ 2 * (2 / ((t + 1 : ℕ) * rho)) =
            (2 / rho) * (t ^ 2 / (t + 1 : ℕ)) := by
              field_simp <;> ring
            _ ≤ (2 / rho) * t := by
              gcongr
              apply (div_le_iff₀
                (by positivity : (0 : ℝ) < (t + 1 : ℕ))).2
              norm_num only [Nat.cast_add, Nat.cast_one]
              nlinarith
    _ = (2 / rho) *
        (∑ t ∈ Finset.range (m + 1),
          (Nat.choose m t : ℝ) * p ^ t * (1 - p) ^ (m - t) * t) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      ring
    _ = (2 / rho) * ((m : ℝ) * p) := by
      rw [binomial_first_moment]
    _ = 2 * (m : ℝ) * p / rho := by ring

/-- Exact inverse-cardinality expectation for a Bernoulli random subset of a
fixed finite set.  This supplies the conditional arm-count law without any
abstract regular-conditional-probability API. -/
lemma setBernoulli_inverse_ncard {J : Type*} [Fintype J] [DecidableEq J]
    (U : Finset J) (rho : ℝ) (hr0 : 0 ≤ rho) (hr1 : rho ≤ 1) :
    ∫ S : Set J, (if 0 < S.ncard then (S.ncard : ℝ)⁻¹ else 0)
        ∂setBer((U : Set J), (⟨rho, hr0, hr1⟩ : unitInterval)) =
      ∑ l ∈ Finset.range (U.card + 1),
        (Nat.choose U.card l : ℝ) * rho ^ l * (1 - rho) ^ (U.card - l) *
          (if 0 < l then (l : ℝ)⁻¹ else 0) := by
  classical
  rw [integral_fintype _ Integrable.of_finite]
  let q : unitInterval := ⟨rho, hr0, hr1⟩
  let e : Finset J ↪ Set J :=
    ⟨fun V => (V : Set J), fun V W h => Finset.coe_injective h⟩
  have hzero (S : Set J) (hS : ¬ S ⊆ (U : Set J)) :
      setBer((U : Set J), q).real {S} = 0 := by
    have hae := setBernoulli_ae_subset (u := (U : Set J)) (p := q)
    have hnull :
        setBer((U : Set J), q) {T : Set J | ¬ T ⊆ (U : Set J)} = 0 := by
      exact mem_ae_iff.mp hae
    have hsingle :
        ({S} : Set (Set J)) ⊆ {T : Set J | ¬ T ⊆ (U : Set J)} := by
      intro T hT
      simpa only [Set.mem_singleton_iff, Set.mem_setOf_eq] using hT ▸ hS
    rw [measureReal_def, measure_mono_null hsingle hnull]
    rfl
  have hfilter :
      ((Finset.univ : Finset (Set J)).filter fun S => S ⊆ (U : Set J)) =
        U.powerset.map e := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Finset.mem_powerset]
    constructor
    · intro hS
      let V : Finset J := S.toFinite.toFinset
      refine ⟨V, ?_, ?_⟩
      · simpa [V] using hS
      · ext j
        simp [e, V]
    · rintro ⟨V, hVU, rfl⟩
      simpa [e] using hVU
  calc
    (∑ S : Set J, setBer((U : Set J), q).real {S} •
        (if 0 < S.ncard then (S.ncard : ℝ)⁻¹ else 0)) =
      ∑ S ∈ (Finset.univ : Finset (Set J)).filter
          (fun S => S ⊆ (U : Set J)),
        setBer((U : Set J), q).real {S} *
          (if 0 < S.ncard then (S.ncard : ℝ)⁻¹ else 0) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro S hS
      by_cases hsub : S ⊆ (U : Set J)
      · simp [hsub, smul_eq_mul]
      · simp [hsub, hzero S hsub, smul_eq_mul]
    _ = ∑ V ∈ U.powerset,
        setBer((U : Set J), q).real {(V : Set J)} *
          (if 0 < V.card then (V.card : ℝ)⁻¹ else 0) := by
      rw [hfilter, Finset.sum_map]
      apply Finset.sum_congr rfl
      intro V hV
      simp [e, Set.ncard_coe_finset]
    _ = ∑ V ∈ U.powerset,
        rho ^ V.card * (1 - rho) ^ (U.card - V.card) *
          (if 0 < V.card then (V.card : ℝ)⁻¹ else 0) := by
      apply Finset.sum_congr rfl
      intro V hV
      have hVU : (V : Set J) ⊆ (U : Set J) := by
        simpa using Finset.mem_powerset.mp hV
      have hVUfin : V ⊆ U := Finset.coe_subset.mp hVU
      have hdiff : ((U : Set J) \ (V : Set J)).ncard = U.card - V.card := by
        rw [← Finset.coe_sdiff, Set.ncard_coe_finset,
          Finset.card_sdiff_of_subset hVUfin]
      rw [show setBer((U : Set J), q).real {(V : Set J)} =
          rho ^ V.card * (1 - rho) ^ (U.card - V.card) by
        rw [measureReal_def,
          setBernoulli_singleton (u := (U : Set J)) (p := q)
            (s := (V : Set J)) hVU (Set.toFinite (U : Set J)), hdiff]
        simp [q, Set.ncard_coe_finset]]
    _ = ∑ l ∈ Finset.range (U.card + 1),
        (Nat.choose U.card l : ℝ) * rho ^ l * (1 - rho) ^ (U.card - l) *
          (if 0 < l then (l : ℝ)⁻¹ else 0) := by
      let f : ℕ → ℝ := fun l =>
        rho ^ l * (1 - rho) ^ (U.card - l) *
          (if 0 < l then (l : ℝ)⁻¹ else 0)
      change (∑ V ∈ U.powerset, f V.card) = _
      rw [Finset.sum_powerset_apply_card f]
      simp only [nsmul_eq_mul]
      apply Finset.sum_congr rfl
      intro l hl
      simp only [f]
      ring

/-- Conditional inverse arm-count bound on a fixed active category set. -/
lemma setBernoulli_inverse_ncard_le {J : Type*} [Fintype J] [DecidableEq J]
    (U : Finset J) (rho : ℝ) (hrho : 0 < rho) (hrho1 : rho ≤ 1) :
    ∫ S : Set J, (if 0 < S.ncard then (S.ncard : ℝ)⁻¹ else 0)
        ∂setBer((U : Set J), (⟨rho, hrho.le, hrho1⟩ : unitInterval)) ≤
      2 / ((U.card + 1 : ℕ) * rho) := by
  rw [setBernoulli_inverse_ncard U rho hrho.le hrho1]
  exact binomial_inverse_count_bound U.card rho hrho hrho1

/-- Elementary exponential envelope used after the exact missing-arm moments
have been counted. -/
lemma one_sub_pow_le_exp_neg_mul (r : ℝ) (m : ℕ)
    (hr1 : r ≤ 1) :
    (1 - r) ^ m ≤ Real.exp (-(m : ℝ) * r) := by
  calc
    (1 - r) ^ m ≤ (Real.exp (-r)) ^ m := by
      exact pow_le_pow_left₀ (sub_nonneg.mpr hr1)
        (Real.one_sub_le_exp_neg r) m
    _ = Real.exp ((m : ℝ) * (-r)) := (Real.exp_nat_mul (-r) m).symm
    _ = Real.exp (-(m : ℝ) * r) := by congr 1 <;> ring

/-- Exponential upper bound for the exact diagonal missing-arm second-moment
formula.  No asymptotics or independence approximation enters this step. -/
lemma missing_arm_second_moment_exp_bound (m : ℕ) (r s : ℝ)
    (hr1 : r ≤ 1) (hs0 : 0 ≤ s) :
    (m : ℝ) * s * (1 - r) ^ (m - 1) +
        (m.descFactorial 2 : ℝ) * s ^ 2 * (1 - r) ^ (m - 2) ≤
      (m : ℝ) * s * Real.exp (-(m - 1 : ℕ) * r) +
        (m.descFactorial 2 : ℝ) * s ^ 2 *
          Real.exp (-(m - 2 : ℕ) * r) := by
  apply add_le_add
  · gcongr
    simpa using one_sub_pow_le_exp_neg_mul r (m - 1) hr1
  · gcongr
    simpa using one_sub_pow_le_exp_neg_mul r (m - 2) hr1

/-- Overlap substitution in the missing-arm exponential envelope. -/
lemma missing_arm_exp_overlap_bound (m : ℕ) (r p epsilon : ℝ)
    (hr : epsilon * p ≤ r) :
    Real.exp (-(m : ℝ) * r) ≤ Real.exp (-(m : ℝ) * epsilon * p) := by
  apply Real.exp_le_exp.mpr
  have hm : (0 : ℝ) ≤ m := by positivity
  nlinarith

/-- A quadratic envelope for exponential decay.  This is the analytic step
that converts the heavy-cell mass lower bound into the extra logarithm in the
aggregate missing-arm term. -/
lemma exp_neg_le_inv_sq (t : ℝ) (ht : 0 < t) :
    Real.exp (-t) ≤ (t ^ 2)⁻¹ := by
  have hlin : t ≤ Real.exp (t / 2) := by
    convert Real.two_mul_le_exp (x := t / 2) using 1 <;> ring
  have hsq : t ^ 2 ≤ Real.exp t := by
    calc
      t ^ 2 ≤ (Real.exp (t / 2)) ^ 2 := pow_le_pow_left₀ ht.le hlin 2
      _ = Real.exp t := by rw [← Real.exp_nat_mul]; congr 1 <;> ring
  rw [Real.exp_neg]
  exact inv_anti₀ (sq_pos_of_pos ht) hsq

/-- Aggregate exponential envelope on a set of cells whose masses are all at
least `B`.  With `u` of order the estimation-fold size and `B` of order
`log n / n`, this is exactly the `d / (n log n)` term. -/
lemma sum_mass_mul_exp_neg_mul_le {J : Type*} [Fintype J] [DecidableEq J]
    (H : Finset J) (p : J → ℝ) (u B : ℝ) (hu : 0 < u) (hB : 0 < B)
    (hp : ∀ k ∈ H, B ≤ p k) :
    ∑ k ∈ H, p k * Real.exp (-u * p k) ≤
      H.card / (u ^ 2 * B) := by
  calc
    ∑ k ∈ H, p k * Real.exp (-u * p k) ≤
        ∑ _k ∈ H, 1 / (u ^ 2 * B) := by
      apply Finset.sum_le_sum
      intro k hk
      have hpk : 0 < p k := hB.trans_le (hp k hk)
      have hut : 0 < u * p k := mul_pos hu hpk
      calc
        p k * Real.exp (-u * p k) ≤ p k * ((u * p k) ^ 2)⁻¹ := by
          gcongr
          simpa only [neg_mul] using exp_neg_le_inv_sq (u * p k) hut
        _ = 1 / (u ^ 2 * p k) := by
          field_simp [hu.ne', hpk.ne']
        _ ≤ 1 / (u ^ 2 * B) := by
          apply one_div_le_one_div_of_le
          · positivity
          · gcongr
            exact hp k hk
    _ = H.card / (u ^ 2 * B) := by
      simp [div_eq_mul_inv]

/-- The observed success mass in one treatment arm factors into its arm mass
and conditional outcome mean.  The statement also handles a zero-mass arm,
where Lean's totalized conditional mean is zero. -/
lemma jointMass_true_eq_outcomeMean_mul_armMass {d : ℕ} (P : DiscreteLaw d)
    (k : Fin d) (a : Bool) :
    jointMass P k a true = outcomeMean P a k * armMass P k a := by
  by_cases h : armMass P k a = 0
  · have h0 := (jointMass_mem_unitInterval P k a false).1
    have h1 := (jointMass_mem_unitInterval P k a true).1
    have hy : jointMass P k a true = 0 := by
      simp [armMass] at h
      linarith
    simp [h, hy]
  · rw [outcomeMean]
    field_simp

/-- One-observation outcome residual for a specified category and arm. -/
noncomputable def armOutcomeResidual {d : ℕ} (P : DiscreteLaw d)
    (k : Fin d) (a : Fin 2) (z : Obs d) : ℝ :=
  if z.1 = k ∧ z.2.1 = finTwoEquiv a then
    (if z.2.2 then 1 else 0) - outcomeMean P (finTwoEquiv a) k
  else 0

/-- The category-arm outcome residual is centered under one observation. -/
lemma integral_armOutcomeResidual_eq_zero {d : ℕ} (P : DiscreteLaw d)
    (k : Fin d) (a : Fin 2) :
    ∫ z, armOutcomeResidual P k a z ∂obsLaw P = 0 := by
  rw [show obsLaw P = P.pmf.toMeasure by rfl, PMF.integral_eq_sum]
  unfold armOutcomeResidual
  simp only [Fintype.sum_prod_type]
  fin_cases a
  · simp only [finTwoEquiv, Fin.isValue, Bool.false_eq_true, and_false,
      ite_false, Bool.if_false_right, Bool.if_false_left, Bool.if_true_right,
      Bool.if_true_left]
    simp [jointMass]
    have hy : (P.pmf (k, false, true)).toReal =
        outcomeMean P false k *
          ((P.pmf (k, false, true)).toReal +
            (P.pmf (k, false, false)).toReal) := by
      simpa [jointMass, armMass] using
        jointMass_true_eq_outcomeMean_mul_armMass P k false
    nlinarith
  · simp only [finTwoEquiv, Fin.isValue, Bool.true_eq_false, and_false,
      ite_false, Bool.if_false_right, Bool.if_false_left, Bool.if_true_right,
      Bool.if_true_left]
    simp [jointMass]
    have hy : (P.pmf (k, true, true)).toReal =
        outcomeMean P true k *
          ((P.pmf (k, true, true)).toReal +
            (P.pmf (k, true, false)).toReal) := by
      simpa [jointMass, armMass] using
        jointMass_true_eq_outcomeMean_mul_armMass P k true
    nlinarith

/-- A multiplier depending on an observation only through its category and
treatment design preserves residual centering. -/
lemma integral_designWeight_mul_armOutcomeResidual_eq_zero {d : ℕ}
    (P : DiscreteLaw d) (k : Fin d) (a : Fin 2) (q : Obs d → ℝ)
    (hq : ∀ (l : Fin d) (b y y' : Bool), q (l, b, y) = q (l, b, y')) :
    ∫ z, q z * armOutcomeResidual P k a z ∂obsLaw P = 0 := by
  rw [show obsLaw P = P.pmf.toMeasure by rfl, PMF.integral_eq_sum]
  unfold armOutcomeResidual
  simp only [Fintype.sum_prod_type]
  fin_cases a
  · simp only [finTwoEquiv, Fin.isValue, Bool.false_eq_true, and_false,
      ite_false, Bool.if_false_right, Bool.if_false_left, Bool.if_true_right,
      Bool.if_true_left]
    rw [Finset.sum_eq_single k]
    · simp [finTwoEquiv, jointMass]
      have hqk := hq k false true false
      have hy : (P.pmf (k, false, true)).toReal =
          outcomeMean P false k *
            ((P.pmf (k, false, true)).toReal +
              (P.pmf (k, false, false)).toReal) := by
        simpa [jointMass, armMass] using
          jointMass_true_eq_outcomeMean_mul_armMass P k false
      rw [hqk]
      linear_combination q (k, false, false) * hy
    · intro l hl hlk
      simp [hlk]
    · simp
  · simp only [finTwoEquiv, Fin.isValue, Bool.true_eq_false, and_false,
      ite_false, Bool.if_false_right, Bool.if_false_left, Bool.if_true_right,
      Bool.if_true_left]
    rw [Finset.sum_eq_single k]
    · simp [finTwoEquiv, jointMass]
      have hqk := hq k true true false
      have hy : (P.pmf (k, true, true)).toReal =
          outcomeMean P true k *
            ((P.pmf (k, true, true)).toReal +
              (P.pmf (k, true, false)).toReal) := by
        simpa [jointMass, armMass] using
          jointMass_true_eq_outcomeMean_mul_armMass P k true
      rw [hqk]
      linear_combination q (k, true, false) * hy
    · intro l hl hlk
      simp [hlk]
    · simp

/-- Replace only the outcome coordinate of observation i. -/
noncomputable def replaceOutcome {I : Type*} [DecidableEq I] {d : ℕ}
    (z : I → Obs d) (i : I) (y : Bool) : I → Obs d :=
  Function.update z i ((z i).1, (z i).2.1, y)

lemma replaceOutcome_apply_same {I : Type*} [DecidableEq I] {d : ℕ}
    (z : I → Obs d) (i : I) (y : Bool) :
    replaceOutcome z i y i = ((z i).1, (z i).2.1, y) := by
  simp [replaceOutcome]

lemma replaceOutcome_apply_ne {I : Type*} [DecidableEq I] {d : ℕ}
    (z : I → Obs d) (i j : I) (hji : j ≠ i) (y : Bool) :
    replaceOutcome z i y j = z j := by
  simp [replaceOutcome, hji]

/-- Finite-product conditional-centering lemma.  Any sample multiplier that is
unchanged when only outcome i is replaced is orthogonal to the centered
category-arm residual at i. -/
lemma integral_coordinate_designWeight_residual_eq_zero
    {I : Type*} [Fintype I] [DecidableEq I] {d : ℕ}
    (P : DiscreteLaw d) (i : I) (k : Fin d) (a : Fin 2)
    (F : (I → Obs d) → ℝ)
    (hF : ∀ z y, F (replaceOutcome z i y) = F z) :
    ∫ z : I → Obs d, F z * armOutcomeResidual P k a (z i)
      ∂(Measure.pi (fun _ : I => obsLaw P)) = 0 := by
  classical
  let p : I → Prop := fun j => j ≠ i
  let E := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : I => Obs d) p
  let μrest : Measure ({j : I // p j} → Obs d) :=
    Measure.pi (fun _ : {j : I // p j} => obsLaw P)
  let μone : Measure ({j : I // ¬ p j} → Obs d) :=
    Measure.pi (fun _ : {j : I // ¬ p j} => obsLaw P)
  let g : (({j : I // p j} → Obs d) ×
      ({j : I // ¬ p j} → Obs d)) → ℝ :=
    fun uv => F (E.symm uv) * armOutcomeResidual P k a (E.symm uv i)
  have hmp := measurePreserving_piEquivPiSubtypeProd
    (fun _ : I => obsLaw P) p
  have hcomp : (fun z : I → Obs d =>
      F z * armOutcomeResidual P k a (z i)) = fun z => g (E z) := by
    funext z
    simp [g, E]
  rw [hcomp, hmp.integral_comp E.measurableEmbedding g]
  rw [integral_prod g Integrable.of_finite]
  apply integral_eq_zero_of_ae
  filter_upwards with u
  let i0 : {j : I // ¬ p j} := ⟨i, by simp [p]⟩
  let q : Obs d → ℝ := fun x =>
    F (E.symm (u, fun _ => x))
  have hq : ∀ (l : Fin d) (b y y' : Bool),
      q (l, b, y) = q (l, b, y') := by
    intro l b y y'
    let z := E.symm (u, fun _ => (l, b, y'))
    have hz : replaceOutcome z i y =
        E.symm (u, fun _ => (l, b, y)) := by
      funext j
      by_cases hji : j = i
      · subst j
        simp [replaceOutcome, z, E, p,
          MeasurableEquiv.piEquivPiSubtypeProd,
          Equiv.piEquivPiSubtypeProd]
      · simp [replaceOutcome, hji, z, E, p,
          MeasurableEquiv.piEquivPiSubtypeProd,
          Equiv.piEquivPiSubtypeProd]
    change F (E.symm (u, fun _ => (l, b, y))) =
      F (E.symm (u, fun _ => (l, b, y')))
    rw [← hz, hF]
  have hinner : (fun v => g (u, v)) = fun v =>
      q (v i0) * armOutcomeResidual P k a (v i0) := by
    funext v
    have hvfun : v = fun _ => v i0 := by
      funext t
      congr 1
      apply Subtype.ext
      exact (not_ne_iff.mp t.2).trans (by rfl)
    rw [hvfun]
    simp [g, q, E, p, i0, MeasurableEquiv.piEquivPiSubtypeProd,
      Equiv.piEquivPiSubtypeProd]
  have heval := Causalean.Stat.integral_pi_eval_eq (P := obsLaw P) i0
    (f := fun x => q x * armOutcomeResidual P k a x)
    Integrable.of_finite
  rw [hinner, heval]
  exact integral_designWeight_mul_armOutcomeResidual_eq_zero P k a q hq

/-- The one-observation residual second moment is bounded by the probability
of its category-arm.  This is the diagonal input for the ratio variance. -/
lemma integral_armOutcomeResidual_sq_le_armMass {d : ℕ} (P : DiscreteLaw d)
    (k : Fin d) (a : Fin 2) :
    ∫ z, (armOutcomeResidual P k a z) ^ 2 ∂obsLaw P ≤
      armMass P k (finTwoEquiv a) := by
  rw [show obsLaw P = P.pmf.toMeasure by rfl, PMF.integral_eq_sum]
  unfold armOutcomeResidual
  have hmu (b : Bool) := outcomeMean_mem_unitInterval P b k
  fin_cases a
  · simp only [Fintype.sum_prod_type, finTwoEquiv, Fin.isValue,
      Bool.false_eq_true, and_false, ite_false, Bool.if_false_right,
      Bool.if_false_left, Bool.if_true_right, Bool.if_true_left]
    simp [jointMass]
    have hy : (P.pmf (k, false, true)).toReal =
        outcomeMean P false k * armMass P k false := by
      simpa [jointMass] using
        jointMass_true_eq_outcomeMean_mul_armMass P k false
    have hs : armMass P k false =
        (P.pmf (k, false, false)).toReal +
          (P.pmf (k, false, true)).toReal := by
      simp [armMass, jointMass]
      ring
    have hvar :
        (P.pmf (k, false, false)).toReal *
            (0 - outcomeMean P false k) ^ 2 +
          (P.pmf (k, false, true)).toReal *
            (1 - outcomeMean P false k) ^ 2 =
          armMass P k false * outcomeMean P false k *
            (1 - outcomeMean P false k) := by
      rw [hy]
      nlinarith
    have harm : 0 ≤ armMass P k false := by
      unfold armMass
      exact Finset.sum_nonneg fun y _ =>
        (jointMass_mem_unitInterval P k false y).1
    calc
      (P.pmf (k, false, true)).toReal *
            (1 - outcomeMean P false k) ^ 2 +
          (P.pmf (k, false, false)).toReal *
            outcomeMean P false k ^ 2 =
          (P.pmf (k, false, false)).toReal *
              (0 - outcomeMean P false k) ^ 2 +
            (P.pmf (k, false, true)).toReal *
              (1 - outcomeMean P false k) ^ 2 := by ring
      _ = armMass P k false * outcomeMean P false k *
            (1 - outcomeMean P false k) := hvar
      _ ≤ armMass P k false := by
        nlinarith [mul_nonneg harm
          (mul_nonneg (hmu false).1 (sub_nonneg.mpr (hmu false).2))]
  · simp only [Fintype.sum_prod_type, finTwoEquiv, Fin.isValue,
      Bool.true_eq_false, and_false, ite_false, Bool.if_false_right,
      Bool.if_false_left, Bool.if_true_right, Bool.if_true_left]
    simp [jointMass]
    have hy : (P.pmf (k, true, true)).toReal =
        outcomeMean P true k * armMass P k true := by
      simpa [jointMass] using
        jointMass_true_eq_outcomeMean_mul_armMass P k true
    have hs : armMass P k true =
        (P.pmf (k, true, false)).toReal +
          (P.pmf (k, true, true)).toReal := by
      simp [armMass, jointMass]
      ring
    have hvar :
        (P.pmf (k, true, false)).toReal *
            (0 - outcomeMean P true k) ^ 2 +
          (P.pmf (k, true, true)).toReal *
            (1 - outcomeMean P true k) ^ 2 =
          armMass P k true * outcomeMean P true k *
            (1 - outcomeMean P true k) := by
      rw [hy]
      nlinarith
    have harm : 0 ≤ armMass P k true := by
      unfold armMass
      exact Finset.sum_nonneg fun y _ =>
        (jointMass_mem_unitInterval P k true y).1
    calc
      (P.pmf (k, true, true)).toReal *
            (1 - outcomeMean P true k) ^ 2 +
          (P.pmf (k, true, false)).toReal *
            outcomeMean P true k ^ 2 =
          (P.pmf (k, true, false)).toReal *
              (0 - outcomeMean P true k) ^ 2 +
            (P.pmf (k, true, true)).toReal *
              (1 - outcomeMean P true k) ^ 2 := by ring
      _ = armMass P k true * outcomeMean P true k *
            (1 - outcomeMean P true k) := hvar
      _ ≤ armMass P k true := by
        nlinarith [mul_nonneg harm
          (mul_nonneg (hmu true).1 (sub_nonneg.mpr (hmu true).2))]

/-- The one-observation event that the confounder equals the given category. -/
noncomputable def categorySet {d : ℕ} (k : Fin d) : Set (Obs d) :=
  {z | z.1 = k}

/-- The nested one-observation category and treatment-arm event. -/
noncomputable def categoryArmSet {d : ℕ} (k : Fin d) (a : Bool) :
    Set (Obs d) :=
  {z | z.1 = k ∧ z.2.1 = a}

/-- The arm probability inside a positive-mass category, totalized at zero. -/
noncomputable def armPropensity {d : ℕ} (P : DiscreteLaw d)
    (k : Fin d) (a : Bool) : ℝ :=
  armMass P k a / cellMass P k

lemma armMass_add_eq_cellMass {d : ℕ} (P : DiscreteLaw d) (k : Fin d) :
    armMass P k false + armMass P k true = cellMass P k := by
  simp [armMass, cellMass]
  ring

lemma armMass_nonneg {d : ℕ} (P : DiscreteLaw d) (k : Fin d)
    (a : Bool) : 0 ≤ armMass P k a := by
  unfold armMass
  exact Finset.sum_nonneg fun y _ ↦ (jointMass_mem_unitInterval P k a y).1

lemma armMass_le_cellMass {d : ℕ} (P : DiscreteLaw d) (k : Fin d)
    (a : Bool) : armMass P k a ≤ cellMass P k := by
  rw [← armMass_add_eq_cellMass]
  cases a
  · exact le_add_of_nonneg_right (armMass_nonneg P k true)
  · exact le_add_of_nonneg_left (armMass_nonneg P k false)

/-- Shows that arm Propensity mem unit Interval lies in the stated set or interval. -/
lemma armPropensity_mem_unitInterval {d : ℕ} (P : DiscreteLaw d)
    (k : Fin d) (a : Bool) : armPropensity P k a ∈ Set.Icc (0 : ℝ) 1 := by
  exact ⟨div_nonneg (armMass_nonneg P k a)
      (cellMass_mem_unitInterval P k).1,
    div_le_one_of_le₀ (armMass_le_cellMass P k a)
      (cellMass_mem_unitInterval P k).1⟩

/-- Establishes the stated equality relating arm Mass eq cell Mass mul arm Propensity. -/
lemma armMass_eq_cellMass_mul_armPropensity {d : ℕ}
    (P : DiscreteLaw d) (k : Fin d) (a : Bool)
    (hp : 0 < cellMass P k) :
    armMass P k a = cellMass P k * armPropensity P k a := by
  unfold armPropensity
  field_simp

/-- Establishes the stated equality relating arm Propensity eq true. -/
lemma armPropensity_eq_true {d : ℕ} (P : DiscreteLaw d)
    (k : Fin d) : armPropensity P k true = propensity P k := rfl

/-- Establishes the stated equality relating arm Propensity eq false. -/
lemma armPropensity_eq_false {d : ℕ} (P : DiscreteLaw d)
    (k : Fin d) (hp : 0 < cellMass P k) :
    armPropensity P k false = 1 - propensity P k := by
  have hsum := armMass_add_eq_cellMass P k
  rw [armPropensity, propensity]
  field_simp
  linarith

/-- Overlap supplies the same lower bound for either arm probability. -/
lemma armPropensity_lower_of_overlap {d : ℕ} {epsilon : ℝ}
    (P : DiscreteLaw d) (hOverlap : Overlap epsilon P)
    (k : Fin d) (a : Bool) (hp : 0 < cellMass P k) :
    epsilon ≤ armPropensity P k a := by
  rcases hOverlap k hp with ⟨hlo, hhi⟩
  cases a
  · rw [armPropensity_eq_false P k hp]
    linarith
  · exact hlo

/-- The category event has exactly its model cell mass. -/
lemma obsLaw_categorySet_mass {d : ℕ} (P : DiscreteLaw d) (k : Fin d) :
    (obsLaw P).real (categorySet k) = cellMass P k := by
  rw [measureReal_def, obsLaw,
    PMF.toMeasure_apply P.pmf MeasurableSet.of_discrete]
  rw [tsum_fintype, ENNReal.toReal_sum (fun x _ => by
    by_cases hx : x ∈ categorySet k <;> simp [hx, P.pmf.apply_ne_top])]
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single k]
  · simp [categorySet, cellMass, jointMass]
  · intro b _hb hbk
    simp [categorySet, hbk]
  · simp

/-- The nested category-arm event has exactly its joint arm mass. -/
lemma obsLaw_categoryArmSet_mass {d : ℕ} (P : DiscreteLaw d) (k : Fin d)
    (a : Bool) :
    (obsLaw P).real (categoryArmSet k a) = armMass P k a := by
  rw [measureReal_def, obsLaw,
    PMF.toMeasure_apply P.pmf MeasurableSet.of_discrete]
  rw [tsum_fintype, ENNReal.toReal_sum (fun x _ => by
    by_cases hx : x ∈ categoryArmSet k a <;>
      simp [hx, P.pmf.apply_ne_top])]
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single k]
  · cases a <;> simp [categoryArmSet, armMass, jointMass]
  · intro b _hb hbk
    simp [categoryArmSet, hbk]
  · simp

lemma categoryArmSet_subset_categorySet {d : ℕ} (k : Fin d) (a : Bool) :
    categoryArmSet k a ⊆ categorySet k := by
  intro z hz
  exact hz.1

/-- Establishes the stated property of obs Law category Arm diff mass in the discrete average-treatment-effect construction. -/
lemma obsLaw_categoryArm_diff_mass {d : ℕ} (P : DiscreteLaw d)
    (k : Fin d) (a : Bool) (hp : 0 < cellMass P k) :
    (obsLaw P).real (categorySet k \ categoryArmSet k a) =
      cellMass P k * (1 - armPropensity P k a) := by
  rw [measureReal_diff (categoryArmSet_subset_categorySet k a)
      MeasurableSet.of_discrete,
    obsLaw_categorySet_mass, obsLaw_categoryArmSet_mass,
    armMass_eq_cellMass_mul_armPropensity P k a hp]
  ring

/-- Establishes the stated property of obs Law category Set compl mass in the discrete average-treatment-effect construction. -/
lemma obsLaw_categorySet_compl_mass {d : ℕ} (P : DiscreteLaw d)
    (k : Fin d) :
    (obsLaw P).real (categorySet k)ᶜ = 1 - cellMass P k := by
  rw [measureReal_compl MeasurableSet.of_discrete, measureReal_univ_eq_one,
    obsLaw_categorySet_mass]

/-- A design-only multiplier factors out of the one-observation residual
second moment on its unique category-arm support. -/
lemma integral_designWeight_mul_residual_sq_factor {d : ℕ}
    (P : DiscreteLaw d) (k : Fin d) (a : Fin 2) (q : Obs d → ℝ)
    (hq : ∀ (l : Fin d) (b y y' : Bool), q (l, b, y) = q (l, b, y')) :
    ∫ z, q z * (armOutcomeResidual P k a z) ^ 2 ∂obsLaw P =
      q (k, finTwoEquiv a, false) *
        ∫ z, (armOutcomeResidual P k a z) ^ 2 ∂obsLaw P := by
  rw [show obsLaw P = P.pmf.toMeasure by rfl]
  rw [PMF.integral_eq_sum, PMF.integral_eq_sum]
  unfold armOutcomeResidual
  simp only [Fintype.sum_prod_type]
  fin_cases a
  · simp only [finTwoEquiv, Fin.isValue, Bool.false_eq_true, and_false,
      ite_false, Bool.if_false_right, Bool.if_false_left, Bool.if_true_right,
      Bool.if_true_left]
    rw [Finset.sum_eq_single k, Finset.sum_eq_single k]
    · simp [finTwoEquiv]
      rw [hq k false true false]
      ring
    · intro l hl hlk; simp [hlk]
    · simp
    · intro l hl hlk; simp [hlk]
    · simp
  · simp only [finTwoEquiv, Fin.isValue, Bool.true_eq_false, and_false,
      ite_false, Bool.if_false_right, Bool.if_false_left, Bool.if_true_right,
      Bool.if_true_left]
    rw [Finset.sum_eq_single k, Finset.sum_eq_single k]
    · simp [finTwoEquiv]
      rw [hq k true true false]
      ring
    · intro l hl hlk; simp [hlk]
    · simp
    · intro l hl hlk; simp [hlk]
    · simp

/-- Evaluates or bounds the stated integral involving integral design Weight mul arm Indicator factor. -/
lemma integral_designWeight_mul_armIndicator_factor {d : ℕ}
    (P : DiscreteLaw d) (k : Fin d) (a : Fin 2) (q : Obs d → ℝ)
    (hq : ∀ (l : Fin d) (b y y' : Bool), q (l, b, y) = q (l, b, y')) :
    ∫ z, q z * (categoryArmSet k (finTwoEquiv a)).indicator
        (fun _ => (1 : ℝ)) z ∂obsLaw P =
      q (k, finTwoEquiv a, false) * armMass P k (finTwoEquiv a) := by
  classical
  rw [show obsLaw P = P.pmf.toMeasure by rfl, PMF.integral_eq_sum]
  simp only [Fintype.sum_prod_type]
  fin_cases a
  · simp [categoryArmSet, finTwoEquiv, armMass, jointMass, Set.indicator]
    rw [hq k false true false]
    ring
  · simp [categoryArmSet, finTwoEquiv, armMass, jointMass, Set.indicator]
    rw [hq k true true false]
    ring

/-- Conditional Bernoulli variance bound with an arbitrary nonnegative
design-only multiplier. -/
lemma integral_designWeight_mul_residual_sq_le_indicator {d : ℕ}
    (P : DiscreteLaw d) (k : Fin d) (a : Fin 2) (q : Obs d → ℝ)
    (hq : ∀ (l : Fin d) (b y y' : Bool), q (l, b, y) = q (l, b, y'))
    (hq0 : ∀ z, 0 ≤ q z) :
    ∫ z, q z * (armOutcomeResidual P k a z) ^ 2 ∂obsLaw P ≤
      ∫ z, q z * (categoryArmSet k (finTwoEquiv a)).indicator
        (fun _ => (1 : ℝ)) z ∂obsLaw P := by
  rw [integral_designWeight_mul_residual_sq_factor P k a q hq,
    integral_designWeight_mul_armIndicator_factor P k a q hq]
  exact mul_le_mul_of_nonneg_left
    (integral_armOutcomeResidual_sq_le_armMass P k a) (hq0 _)

/-- Product-sample conditional variance bound at one coordinate, for any
nonnegative multiplier unchanged by replacing that coordinate's outcome. -/
lemma integral_coordinate_designWeight_residual_sq_le_indicator
    {I : Type*} [Fintype I] [DecidableEq I] {d : ℕ}
    (P : DiscreteLaw d) (i : I) (k : Fin d) (a : Fin 2)
    (F : (I → Obs d) → ℝ)
    (hF : ∀ z y, F (replaceOutcome z i y) = F z)
    (hF0 : ∀ z, 0 ≤ F z) :
    ∫ z : I → Obs d, F z * (armOutcomeResidual P k a (z i)) ^ 2
        ∂(Measure.pi (fun _ : I => obsLaw P)) ≤
      ∫ z : I → Obs d, F z *
          (categoryArmSet k (finTwoEquiv a)).indicator
            (fun _ => (1 : ℝ)) (z i)
        ∂(Measure.pi (fun _ : I => obsLaw P)) := by
  classical
  let p : I → Prop := fun j => j ≠ i
  let E := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : I => Obs d) p
  let g1 : (({j : I // p j} → Obs d) ×
      ({j : I // ¬ p j} → Obs d)) → ℝ :=
    fun uv => F (E.symm uv) * (armOutcomeResidual P k a (E.symm uv i)) ^ 2
  let g2 : (({j : I // p j} → Obs d) ×
      ({j : I // ¬ p j} → Obs d)) → ℝ :=
    fun uv => F (E.symm uv) *
      (categoryArmSet k (finTwoEquiv a)).indicator
        (fun _ => (1 : ℝ)) (E.symm uv i)
  have hmp := measurePreserving_piEquivPiSubtypeProd
    (fun _ : I => obsLaw P) p
  have hcomp1 : (fun z : I → Obs d =>
      F z * (armOutcomeResidual P k a (z i)) ^ 2) = fun z => g1 (E z) := by
    funext z
    simp [g1, E]
  have hcomp2 : (fun z : I → Obs d => F z *
      (categoryArmSet k (finTwoEquiv a)).indicator
        (fun _ => (1 : ℝ)) (z i)) =
      fun z => g2 (E z) := by
    funext z
    simp [g2, E]
  rw [hcomp1, hmp.integral_comp E.measurableEmbedding g1]
  rw [hcomp2, hmp.integral_comp E.measurableEmbedding g2]
  rw [integral_prod g1 Integrable.of_finite,
    integral_prod g2 Integrable.of_finite]
  apply integral_mono Integrable.of_finite Integrable.of_finite
  intro u
  let i0 : {j : I // ¬ p j} := ⟨i, by simp [p]⟩
  let q : Obs d → ℝ := fun x => F (E.symm (u, fun _ => x))
  have hq : ∀ (l : Fin d) (b y y' : Bool),
      q (l, b, y) = q (l, b, y') := by
    intro l b y y'
    let z := E.symm (u, fun _ => (l, b, y'))
    have hz : replaceOutcome z i y =
        E.symm (u, fun _ => (l, b, y)) := by
      funext j
      by_cases hji : j = i
      · subst j
        simp [replaceOutcome, z, E, p,
          MeasurableEquiv.piEquivPiSubtypeProd,
          Equiv.piEquivPiSubtypeProd]
      · simp [replaceOutcome, hji, z, E, p,
          MeasurableEquiv.piEquivPiSubtypeProd,
          Equiv.piEquivPiSubtypeProd]
    change F (E.symm (u, fun _ => (l, b, y))) =
      F (E.symm (u, fun _ => (l, b, y')))
    rw [← hz, hF]
  have hq0 : ∀ x, 0 ≤ q x := fun x => hF0 _
  have hinner1 : (fun v => g1 (u, v)) = fun v =>
      q (v i0) * (armOutcomeResidual P k a (v i0)) ^ 2 := by
    funext v
    have hvfun : v = fun _ => v i0 := by
      funext t
      congr 1
      apply Subtype.ext
      exact (not_ne_iff.mp t.2).trans (by rfl)
    rw [hvfun]
    simp [g1, q, E, p, i0, MeasurableEquiv.piEquivPiSubtypeProd,
      Equiv.piEquivPiSubtypeProd]
  have hinner2 : (fun v => g2 (u, v)) = fun v =>
      q (v i0) * (categoryArmSet k (finTwoEquiv a)).indicator
        (fun _ => (1 : ℝ)) (v i0) := by
    funext v
    have hvfun : v = fun _ => v i0 := by
      funext t
      congr 1
      apply Subtype.ext
      exact (not_ne_iff.mp t.2).trans (by rfl)
    rw [hvfun]
    simp [g2, q, E, p, i0, MeasurableEquiv.piEquivPiSubtypeProd,
      Equiv.piEquivPiSubtypeProd]
  simp only
  rw [hinner1, hinner2]
  rw [Causalean.Stat.integral_pi_eval_eq (P := obsLaw P) i0
    (f := fun x => q x * (armOutcomeResidual P k a x) ^ 2)
    Integrable.of_finite]
  rw [Causalean.Stat.integral_pi_eval_eq (P := obsLaw P) i0
    (f := fun x => q x * (categoryArmSet k (finTwoEquiv a)).indicator
      (fun _ => (1 : ℝ)) x) Integrable.of_finite]
  exact integral_designWeight_mul_residual_sq_le_indicator P k a q hq hq0

/-- Product of three constants over a nested two-set partition. -/
lemma prod_nested_partition {I : Type*} [Fintype I] [DecidableEq I]
    (U V : Finset I) (hVU : V ⊆ U) (r s q : ℝ) :
    (∏ i : I, if i ∈ V then r else if i ∈ U then s else q) =
      r ^ V.card * s ^ (U.card - V.card) *
        q ^ (Fintype.card I - U.card) := by
  classical
  change (∏ i ∈ (Finset.univ : Finset I),
    if i ∈ V then r else if i ∈ U then s else q) = _
  rw [Finset.prod_ite]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [Finset.prod_ite]
  have hA : ((Finset.univ : Finset I).filter (fun i => i ∉ V)).filter
      (fun i => i ∈ U) = U \ V := by
    ext i
    simp [and_comm]
  have hB : ((Finset.univ : Finset I).filter (fun i => i ∉ V)).filter
      (fun i => i ∉ U) = (Finset.univ : Finset I) \ U := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · intro hiU
      exact ⟨fun hiV => hiU (hVU hiV), hiU⟩
  rw [hA, hB]
  simp [Finset.prod_const, Finset.card_sdiff_of_subset hVU,
    Finset.card_sdiff_of_subset (Finset.subset_univ U)]
  ring

/-- Indices whose observations land in a measurable or nonmeasurable set. -/
noncomputable def indexSet {I A : Type*} [Fintype I] [DecidableEq I]
    (z : I → A) (S : Set A) : Finset I := by
  classical
  exact Finset.univ.filter fun i => z i ∈ S

/-- Joint event fixing the index set in `C` and its nested sub-index-set in
`R`. -/
def nestedIndexEvent {I A : Type*} [Fintype I] [DecidableEq I]
    (C R : Set A) (U V : Finset I) : Set (I → A) :=
  {z | indexSet z C = U ∧ indexSet z R = V}

lemma nestedIndexEvent_eq_pi {I A : Type*} [Fintype I] [DecidableEq I]
    (C R : Set A) (hRC : R ⊆ C) (U V : Finset I) (hVU : V ⊆ U) :
    nestedIndexEvent C R U V =
      Set.univ.pi
        (fun i => if i ∈ V then R else if i ∈ U then C \ R else Cᶜ) := by
  classical
  ext z
  simp only [nestedIndexEvent, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ,
    forall_true_left]
  constructor
  · rintro ⟨hC, hR⟩ i
    have hCi : (z i ∈ C ↔ i ∈ U) := by
      have hi := congrArg (fun W : Finset I => i ∈ W) hC
      simpa [indexSet] using hi
    have hRi : (z i ∈ R ↔ i ∈ V) := by
      have hi := congrArg (fun W : Finset I => i ∈ W) hR
      simpa [indexSet] using hi
    by_cases hiV : i ∈ V
    · simp [hiV, hRi.mpr hiV]
    · by_cases hiU : i ∈ U
      · simp [hiV, hiU, hCi.mpr hiU, hRi.not.mpr hiV]
      · simp [hiV, hiU, hCi.not.mpr hiU]
  · intro h
    constructor
    · apply Finset.ext
      intro i
      simp only [indexSet, Finset.mem_filter, Finset.mem_univ, true_and]
      have hi := h i
      by_cases hiV : i ∈ V
      · have hiU := hVU hiV
        simp only [hiV, if_true] at hi
        exact ⟨fun _ => hiU, fun _ => hRC hi⟩
      · by_cases hiU : i ∈ U
        · simp only [hiV, if_false, hiU, if_true, Set.mem_diff] at hi
          exact ⟨fun _ => hiU, fun _ => hi.1⟩
        · simp only [hiV, if_false, hiU, Set.mem_compl_iff] at hi
          exact ⟨fun hC => (hi hC).elim, fun hmem => (hiU hmem).elim⟩
    · apply Finset.ext
      intro i
      simp only [indexSet, Finset.mem_filter, Finset.mem_univ, true_and]
      have hi := h i
      by_cases hiV : i ∈ V
      · simp only [hiV, if_true] at hi
        exact ⟨fun _ => hiV, fun _ => hi⟩
      · by_cases hiU : i ∈ U
        · simp only [hiV, if_false, hiU, if_true, Set.mem_diff] at hi
          exact ⟨fun hRmem => (hi.2 hRmem).elim,
            fun hmem => (hiV hmem).elim⟩
        · simp only [hiV, if_false, hiU, Set.mem_compl_iff] at hi
          exact ⟨fun hRmem => (hi (hRC hRmem)).elim,
            fun hmem => (hiV hmem).elim⟩

/-- Exact finite-product mass of a nested pair of index sets.  This is the
finite symmetry/counting bridge used in place of a conditional-law API. -/
lemma measure_nestedIndexEvent {I A : Type*} [Fintype I] [DecidableEq I]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (P : Measure A) [IsProbabilityMeasure P]
    (C R : Set A) (hC : MeasurableSet C) (hR : MeasurableSet R)
    (hRC : R ⊆ C) (U V : Finset I) (hVU : V ⊆ U) :
    (Measure.pi (fun _ : I => P)).real (nestedIndexEvent C R U V) =
      (P R).toReal ^ V.card * (P (C \ R)).toReal ^ (U.card - V.card) *
        (P Cᶜ).toReal ^ (Fintype.card I - U.card) := by
  rw [nestedIndexEvent_eq_pi C R hRC U V hVU, measureReal_def,
    Measure.pi_pi, ENNReal.toReal_prod]
  have hfun :
      (fun i : I =>
        (P (if i ∈ V then R else if i ∈ U then C \ R else Cᶜ)).toReal) =
      fun i => if i ∈ V then (P R).toReal
        else if i ∈ U then (P (C \ R)).toReal else (P Cᶜ).toReal := by
    funext i
    by_cases hiV : i ∈ V <;> by_cases hiU : i ∈ U <;> simp [hiV, hiU]
  rw [hfun]
  exact prod_nested_partition U V hVU _ _ _

/-- Establishes the stated property of index Set mono in the discrete average-treatment-effect construction. -/
lemma indexSet_mono {I A : Type*} [Fintype I] [DecidableEq I]
    (z : I → A) {R C : Set A} (hRC : R ⊆ C) :
    indexSet z R ⊆ indexSet z C := by
  classical
  intro i hi
  simp only [indexSet, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact hRC hi

/-- Exact finite-product nested-count identity.  In particular, this proves
algebraically that the arm count conditional on a category count `t` has the
binomial weights with parameter `rho`. -/
lemma nested_count_ratio_integral_eq {I A : Type*} [Fintype I]
    [DecidableEq I] [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A]
    (P : Measure A) [IsProbabilityMeasure P]
    (C R : Set A) (hC : MeasurableSet C) (hR : MeasurableSet R)
    (hRC : R ⊆ C) (p rho : ℝ)
    (hpC : (P C).toReal = p) (hpR : (P R).toReal = p * rho)
    (hpDiff : (P (C \ R)).toReal = p * (1 - rho))
    (hpCompl : (P Cᶜ).toReal = 1 - p) :
    ∫ z : I → A, ((indexSet z C).card : ℝ) ^ 2 *
        (if 0 < (indexSet z R).card then
          ((indexSet z R).card : ℝ)⁻¹ else 0)
        ∂(Measure.pi (fun _ : I => P)) =
      ∑ t ∈ Finset.range (Fintype.card I + 1),
        (Nat.choose (Fintype.card I) t : ℝ) * p ^ t *
          (1 - p) ^ (Fintype.card I - t) * (t : ℝ) ^ 2 *
          (∑ l ∈ Finset.range (t + 1),
            (Nat.choose t l : ℝ) * rho ^ l * (1 - rho) ^ (t - l) *
              (if 0 < l then (l : ℝ)⁻¹ else 0)) := by
  classical
  letI : MeasurableSpace (Finset I) := ⊤
  let pairMap : (I → A) → Finset I × Finset I := fun z =>
    (indexSet z C, indexSet z R)
  let f : Finset I × Finset I → ℝ := fun uv =>
    (uv.1.card : ℝ) ^ 2 *
      (if 0 < uv.2.card then (uv.2.card : ℝ)⁻¹ else 0)
  have hmap : Measurable pairMap := measurable_of_finite _
  have hf : Measurable f := measurable_of_finite _
  rw [show (∫ z : I → A, ((indexSet z C).card : ℝ) ^ 2 *
        (if 0 < (indexSet z R).card then
          ((indexSet z R).card : ℝ)⁻¹ else 0)
        ∂(Measure.pi (fun _ : I => P))) =
      ∫ uv, f uv ∂((Measure.pi (fun _ : I => P)).map pairMap) by
        rw [integral_map hmap.aemeasurable hf.aestronglyMeasurable]]
  rw [integral_fintype _ Integrable.of_finite]
  simp only [Fintype.sum_prod_type, smul_eq_mul]
  have hmass (U V : Finset I) :
      ((Measure.pi (fun _ : I => P)).map pairMap).real {(U, V)} =
        (Measure.pi (fun _ : I => P)).real
          (nestedIndexEvent C R U V) := by
    rw [map_measureReal_apply hmap (MeasurableSet.singleton (U, V))]
    congr 1
    ext z
    simp [pairMap, nestedIndexEvent]
  simp_rw [hmass]
  have hzero (U V : Finset I) (hnot : ¬ V ⊆ U) :
      (Measure.pi (fun _ : I => P)).real
          (nestedIndexEvent C R U V) = 0 := by
    have hempty : nestedIndexEvent C R U V = ∅ := by
      ext z
      simp only [nestedIndexEvent, Set.mem_setOf_eq,
        Set.mem_empty_iff_false, iff_false]
      intro hz
      exact hnot (hz.2 ▸ hz.1 ▸ indexSet_mono z hRC)
    simp [hempty]
  calc
    (∑ U : Finset I, ∑ V : Finset I,
      (Measure.pi (fun _ : I => P)).real (nestedIndexEvent C R U V) *
        f (U, V)) =
      ∑ U ∈ (Finset.univ : Finset (Finset I)),
        ∑ V ∈ U.powerset,
          (Measure.pi (fun _ : I => P)).real
            (nestedIndexEvent C R U V) * f (U, V) := by
      apply Finset.sum_congr rfl
      intro U hU
      apply (Finset.sum_subset (s₁ := U.powerset)
        (s₂ := (Finset.univ : Finset (Finset I)))
        (Finset.subset_univ _) ?_).symm
      intro V hV hnotmem
      have hnot : ¬ V ⊆ U := by simpa using hnotmem
      simp [hzero U V hnot]
    _ = ∑ U ∈ (Finset.univ : Finset (Finset I)),
        ∑ V ∈ U.powerset,
          (p * rho) ^ V.card *
            (p * (1 - rho)) ^ (U.card - V.card) *
            (1 - p) ^ (Fintype.card I - U.card) *
            ((U.card : ℝ) ^ 2 *
              (if 0 < V.card then (V.card : ℝ)⁻¹ else 0)) := by
      apply Finset.sum_congr rfl
      intro U hU
      apply Finset.sum_congr rfl
      intro V hV
      have hVU := Finset.mem_powerset.mp hV
      rw [measure_nestedIndexEvent P C R hC hR hRC U V hVU,
        hpR, hpDiff, hpCompl]
    _ = ∑ U ∈ (Finset.univ : Finset (Finset I)),
        p ^ U.card * (1 - p) ^ (Fintype.card I - U.card) *
          (U.card : ℝ) ^ 2 *
          (∑ V ∈ U.powerset,
            rho ^ V.card * (1 - rho) ^ (U.card - V.card) *
              (if 0 < V.card then (V.card : ℝ)⁻¹ else 0)) := by
      apply Finset.sum_congr rfl
      intro U hU
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro V hV
      have hVU := Finset.mem_powerset.mp hV
      have hcard : V.card + (U.card - V.card) = U.card :=
        Nat.add_sub_of_le (Finset.card_le_card hVU)
      rw [mul_pow, mul_pow]
      calc
        p ^ V.card * rho ^ V.card *
              (p ^ (U.card - V.card) *
                (1 - rho) ^ (U.card - V.card)) *
              (1 - p) ^ (Fintype.card I - U.card) *
              ((U.card : ℝ) ^ 2 *
                (if 0 < V.card then (V.card : ℝ)⁻¹ else 0)) =
          (p ^ V.card * p ^ (U.card - V.card)) *
            (1 - p) ^ (Fintype.card I - U.card) *
            (U.card : ℝ) ^ 2 *
            (rho ^ V.card * (1 - rho) ^ (U.card - V.card) *
              (if 0 < V.card then (V.card : ℝ)⁻¹ else 0)) := by ring
        _ = p ^ U.card * (1 - p) ^ (Fintype.card I - U.card) *
            (U.card : ℝ) ^ 2 *
            (rho ^ V.card * (1 - rho) ^ (U.card - V.card) *
              (if 0 < V.card then (V.card : ℝ)⁻¹ else 0)) := by
          rw [← pow_add, hcard]
    _ = ∑ U ∈ (Finset.univ : Finset (Finset I)),
        p ^ U.card * (1 - p) ^ (Fintype.card I - U.card) *
          (U.card : ℝ) ^ 2 *
          (∑ l ∈ Finset.range (U.card + 1),
            (Nat.choose U.card l : ℝ) * rho ^ l *
              (1 - rho) ^ (U.card - l) *
              (if 0 < l then (l : ℝ)⁻¹ else 0)) := by
      apply Finset.sum_congr rfl
      intro U hU
      congr 1
      let g : ℕ → ℝ := fun l =>
        rho ^ l * (1 - rho) ^ (U.card - l) *
          (if 0 < l then (l : ℝ)⁻¹ else 0)
      change (∑ V ∈ U.powerset, g V.card) = _
      rw [Finset.sum_powerset_apply_card g]
      simp only [nsmul_eq_mul, g]
      apply Finset.sum_congr rfl
      intro l hl
      ring
    _ = ∑ t ∈ Finset.range (Fintype.card I + 1),
        (Nat.choose (Fintype.card I) t : ℝ) * p ^ t *
          (1 - p) ^ (Fintype.card I - t) * (t : ℝ) ^ 2 *
          (∑ l ∈ Finset.range (t + 1),
            (Nat.choose t l : ℝ) * rho ^ l *
              (1 - rho) ^ (t - l) *
              (if 0 < l then (l : ℝ)⁻¹ else 0)) := by
      let G : ℕ → ℝ := fun t =>
        p ^ t * (1 - p) ^ (Fintype.card I - t) * (t : ℝ) ^ 2 *
          (∑ l ∈ Finset.range (t + 1),
            (Nat.choose t l : ℝ) * rho ^ l *
              (1 - rho) ^ (t - l) *
              (if 0 < l then (l : ℝ)⁻¹ else 0))
      change (∑ U : Finset I, G U.card) = _
      have huniv : (Finset.univ : Finset (Finset I)) =
          (Finset.univ : Finset I).powerset := by ext U; simp
      rw [huniv, Finset.sum_powerset_apply_card G]
      simp only [Finset.card_univ, nsmul_eq_mul, G]
      apply Finset.sum_congr rfl
      intro t ht
      ring

/-- The finite-product nested-count identity, combined with the sharp
inverse-binomial calculation.  This is the unconditional design bound needed
for the heavy-cell variance calculation. -/
lemma nested_count_ratio_integral_le {I A : Type*} [Fintype I]
    [DecidableEq I] [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A]
    (P : Measure A) [IsProbabilityMeasure P]
    (C R : Set A) (hC : MeasurableSet C) (hR : MeasurableSet R)
    (hRC : R ⊆ C) (p rho : ℝ)
    (hpC : (P C).toReal = p) (hpR : (P R).toReal = p * rho)
    (hpDiff : (P (C \ R)).toReal = p * (1 - rho))
    (hpCompl : (P Cᶜ).toReal = 1 - p)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hrho : 0 < rho)
    (hrho1 : rho ≤ 1) :
    ∫ z : I → A, ((indexSet z C).card : ℝ) ^ 2 *
        (if 0 < (indexSet z R).card then
          ((indexSet z R).card : ℝ)⁻¹ else 0)
        ∂(Measure.pi (fun _ : I ↦ P)) ≤
      2 * (Fintype.card I : ℝ) * p / rho := by
  rw [nested_count_ratio_integral_eq P C R hC hR hRC p rho
    hpC hpR hpDiff hpCompl]
  exact nested_binomial_ratio_bound (Fintype.card I) p rho
    hp0 hp1 hrho hrho1

/-- Specialization of the nested-count theorem to one discrete-ATE category
and either treatment arm.  Overlap replaces the arm probability denominator
by the uniform lower bound epsilon. -/
lemma ate_nested_count_ratio_integral_le {I : Type*} [Fintype I]
    [DecidableEq I] {d : ℕ} {epsilon : ℝ}
    (P : DiscreteLaw d) (hOverlap : Overlap epsilon P) (hepsilon : 0 < epsilon)
    (k : Fin d) (a : Bool) (hp : 0 < cellMass P k) :
    ∫ z : I → Obs d, ((indexSet z (categorySet k)).card : ℝ) ^ 2 *
        (if 0 < (indexSet z (categoryArmSet k a)).card then
          ((indexSet z (categoryArmSet k a)).card : ℝ)⁻¹ else 0)
        ∂(Measure.pi (fun _ : I ↦ obsLaw P)) ≤
      2 * (Fintype.card I : ℝ) * cellMass P k / epsilon := by
  have hrhoLower := armPropensity_lower_of_overlap P hOverlap k a hp
  have hrhoPos : 0 < armPropensity P k a := lt_of_lt_of_le hepsilon hrhoLower
  have hbase := nested_count_ratio_integral_le (I := I) (P := obsLaw P)
    (categorySet k) (categoryArmSet k a) MeasurableSet.of_discrete
    MeasurableSet.of_discrete (categoryArmSet_subset_categorySet k a)
    (cellMass P k) (armPropensity P k a)
    (obsLaw_categorySet_mass P k)
    ((obsLaw_categoryArmSet_mass P k a).trans
      (armMass_eq_cellMass_mul_armPropensity P k a hp))
    (obsLaw_categoryArm_diff_mass P k a hp)
    (obsLaw_categorySet_compl_mass P k)
    (cellMass_mem_unitInterval P k).1 (cellMass_mem_unitInterval P k).2
    hrhoPos (armPropensity_mem_unitInterval P k a).2
  calc
    _ ≤ 2 * (Fintype.card I : ℝ) * cellMass P k /
        armPropensity P k a := hbase
    _ ≤ 2 * (Fintype.card I : ℝ) * cellMass P k / epsilon := by
      exact div_le_div_of_nonneg_left (by positivity) hepsilon hrhoLower

/-- Ratio coefficient multiplying one category's residual sum. -/
noncomputable def tupleRatioCoeff {I : Type*} [Fintype I] [DecidableEq I]
    {d : ℕ} (z : I → Obs d) (k : Fin d) (a : Fin 2) : ℝ :=
  ((indexSet z (categorySet k)).card : ℝ) *
    (if 0 < (indexSet z (categoryArmSet k (finTwoEquiv a))).card then
      ((indexSet z (categoryArmSet k (finTwoEquiv a))).card : ℝ)⁻¹ else 0)

/-- Aggregate centered ratio residual over a fixed category set. -/
noncomputable def fixedRatioResidual {I : Type*} [Fintype I]
    [DecidableEq I] {d : ℕ} (P : DiscreteLaw d) (z : I → Obs d)
    (H : Finset (Fin d)) (a : Fin 2) : ℝ :=
  ∑ k ∈ H, tupleRatioCoeff z k a *
    ∑ i : I, armOutcomeResidual P k a (z i)

lemma indexSet_replaceOutcome_category {I : Type*} [Fintype I]
    [DecidableEq I] {d : ℕ} (z : I → Obs d) (i : I) (y : Bool)
    (k : Fin d) :
    indexSet (replaceOutcome z i y) (categorySet k) =
      indexSet z (categorySet k) := by
  classical
  ext j
  by_cases hji : j = i
  · subst j
    simp [indexSet, categorySet, replaceOutcome]
  · simp [indexSet, categorySet, replaceOutcome, hji]

/-- Establishes the stated property of index Set replace Outcome arm in the discrete average-treatment-effect construction. -/
lemma indexSet_replaceOutcome_arm {I : Type*} [Fintype I]
    [DecidableEq I] {d : ℕ} (z : I → Obs d) (i : I) (y : Bool)
    (k : Fin d) (a : Fin 2) :
    indexSet (replaceOutcome z i y)
        (categoryArmSet k (finTwoEquiv a)) =
      indexSet z (categoryArmSet k (finTwoEquiv a)) := by
  classical
  ext j
  by_cases hji : j = i
  · subst j
    simp [indexSet, categoryArmSet, replaceOutcome]
  · simp [indexSet, categoryArmSet, replaceOutcome, hji]

/-- Establishes the stated upper bound for tuple Ratio Coeff replace Outcome. -/
lemma tupleRatioCoeff_replaceOutcome {I : Type*} [Fintype I]
    [DecidableEq I] {d : ℕ} (z : I → Obs d) (i : I) (y : Bool)
    (k : Fin d) (a : Fin 2) :
    tupleRatioCoeff (replaceOutcome z i y) k a =
      tupleRatioCoeff z k a := by
  unfold tupleRatioCoeff
  rw [indexSet_replaceOutcome_category, indexSet_replaceOutcome_arm]

/-- Evaluates or bounds the stated integral involving integral ratio Residual cross coordinates eq zero. -/
lemma integral_ratioResidual_cross_coordinates_eq_zero
    {I : Type*} [Fintype I] [DecidableEq I] {d : ℕ}
    (P : DiscreteLaw d) (i j : I) (hij : i ≠ j)
    (k l : Fin d) (a : Fin 2) :
    ∫ z : I → Obs d,
        (tupleRatioCoeff z k a * tupleRatioCoeff z l a *
          armOutcomeResidual P l a (z j)) *
          armOutcomeResidual P k a (z i)
        ∂(Measure.pi (fun _ : I => obsLaw P)) = 0 := by
  apply integral_coordinate_designWeight_residual_eq_zero P i k a
  intro z y
  rw [tupleRatioCoeff_replaceOutcome, tupleRatioCoeff_replaceOutcome,
    replaceOutcome_apply_ne _ _ _ hij.symm]

/-- Establishes the stated equality relating arm Outcome Residual mul eq zero of ne. -/
lemma armOutcomeResidual_mul_eq_zero_of_ne {d : ℕ}
    (P : DiscreteLaw d) (k l : Fin d) (hkl : k ≠ l) (a : Fin 2)
    (x : Obs d) :
    armOutcomeResidual P k a x * armOutcomeResidual P l a x = 0 := by
  unfold armOutcomeResidual
  by_cases hk : x.1 = k
  · have hl : x.1 ≠ l := fun h => hkl (hk.symm.trans h)
    simp [hk, hkl]
  · simp [hk]

/-- Evaluates or bounds the stated integral involving integral ratio Residual diagonal le. -/
lemma integral_ratioResidual_diagonal_le
    {I : Type*} [Fintype I] [DecidableEq I] {d : ℕ}
    (P : DiscreteLaw d) (i : I) (k : Fin d) (a : Fin 2) :
    ∫ z : I → Obs d,
        (tupleRatioCoeff z k a) ^ 2 *
          (armOutcomeResidual P k a (z i)) ^ 2
        ∂(Measure.pi (fun _ : I => obsLaw P)) ≤
      ∫ z : I → Obs d,
        (tupleRatioCoeff z k a) ^ 2 *
          (categoryArmSet k (finTwoEquiv a)).indicator
            (fun _ => (1 : ℝ)) (z i)
        ∂(Measure.pi (fun _ : I => obsLaw P)) := by
  apply integral_coordinate_designWeight_residual_sq_le_indicator P i k a
  · intro z y
    rw [tupleRatioCoeff_replaceOutcome]
  · intro z
    positivity

/-- Evaluates or bounds the stated integral involving integral ratio Residual pair eq zero of ne. -/
lemma integral_ratioResidual_pair_eq_zero_of_ne
    {I : Type*} [Fintype I] [DecidableEq I] {d : ℕ}
    (P : DiscreteLaw d) (i j : I) (k l : Fin d) (a : Fin 2)
    (hne : k ≠ l ∨ i ≠ j) :
    ∫ z : I → Obs d,
        (tupleRatioCoeff z k a * armOutcomeResidual P k a (z i)) *
          (tupleRatioCoeff z l a * armOutcomeResidual P l a (z j))
        ∂(Measure.pi (fun _ : I => obsLaw P)) = 0 := by
  rcases hne with hkl | hij
  · by_cases hij : i = j
    · subst j
      apply integral_eq_zero_of_ae
      filter_upwards with z
      rw [show (tupleRatioCoeff z k a * armOutcomeResidual P k a (z i)) *
          (tupleRatioCoeff z l a * armOutcomeResidual P l a (z i)) =
          (tupleRatioCoeff z k a * tupleRatioCoeff z l a) *
            (armOutcomeResidual P k a (z i) *
              armOutcomeResidual P l a (z i)) by ring,
        armOutcomeResidual_mul_eq_zero_of_ne P k l hkl]
      change tupleRatioCoeff z k a * tupleRatioCoeff z l a * 0 = (0 : ℝ)
      ring
    · rw [show (fun z : I → Obs d =>
          (tupleRatioCoeff z k a * armOutcomeResidual P k a (z i)) *
            (tupleRatioCoeff z l a * armOutcomeResidual P l a (z j))) =
          fun z => (tupleRatioCoeff z k a * tupleRatioCoeff z l a *
            armOutcomeResidual P l a (z j)) *
              armOutcomeResidual P k a (z i) by
          funext z; ring]
      exact integral_ratioResidual_cross_coordinates_eq_zero
        P i j hij k l a
  · rw [show (fun z : I → Obs d =>
        (tupleRatioCoeff z k a * armOutcomeResidual P k a (z i)) *
          (tupleRatioCoeff z l a * armOutcomeResidual P l a (z j))) =
        fun z => (tupleRatioCoeff z k a * tupleRatioCoeff z l a *
          armOutcomeResidual P l a (z j)) *
            armOutcomeResidual P k a (z i) by
        funext z; ring]
    exact integral_ratioResidual_cross_coordinates_eq_zero
      P i j hij k l a

/-- All off-diagonal residual terms cancel exactly, across both observations
and distinct categories. -/
lemma integral_fixedRatioResidual_sq_eq_diagonal
    {I : Type*} [Fintype I] [DecidableEq I] {d : ℕ}
    (P : DiscreteLaw d) (H : Finset (Fin d)) (a : Fin 2) :
    ∫ z : I → Obs d, (fixedRatioResidual P z H a) ^ 2
        ∂(Measure.pi (fun _ : I => obsLaw P)) =
      ∑ k ∈ H, ∑ i : I,
        ∫ z : I → Obs d,
          (tupleRatioCoeff z k a) ^ 2 *
            (armOutcomeResidual P k a (z i)) ^ 2
          ∂(Measure.pi (fun _ : I => obsLaw P)) := by
  classical
  let S : Finset (Fin d × I) := H.product Finset.univ
  let f : (Fin d × I) → (I → Obs d) → ℝ := fun ki z =>
    tupleRatioCoeff z ki.1 a * armOutcomeResidual P ki.1 a (z ki.2)
  have hfixed (z : I → Obs d) :
      fixedRatioResidual P z H a = ∑ ki ∈ S, f ki z := by
    unfold fixedRatioResidual
    rw [show (∑ ki ∈ S, f ki z) =
        ∑ k ∈ H, ∑ i ∈ (Finset.univ : Finset I), f (k, i) z by
      simpa only [S] using
        (Finset.sum_product H (Finset.univ : Finset I) (fun ki => f ki z))]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mul_sum]
  have hsquare (z : I → Obs d) :
      (fixedRatioResidual P z H a) ^ 2 =
        ∑ ki ∈ S, ∑ lj ∈ S, f ki z * f lj z := by
    rw [hfixed, sq, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro ki hki
    rw [Finset.mul_sum]
  simp_rw [hsquare]
  rw [integral_finset_sum S (fun _ _ => Integrable.of_finite)]
  simp_rw [integral_finset_sum S (fun _ _ => Integrable.of_finite)]
  have hinner (ki : Fin d × I) (hki : ki ∈ S) :
      (∑ lj ∈ S,
        ∫ z : I → Obs d, f ki z * f lj z
          ∂(Measure.pi (fun _ : I => obsLaw P))) =
        ∫ z : I → Obs d,
          (tupleRatioCoeff z ki.1 a) ^ 2 *
            (armOutcomeResidual P ki.1 a (z ki.2)) ^ 2
          ∂(Measure.pi (fun _ : I => obsLaw P)) := by
    rw [Finset.sum_eq_single ki]
    · apply integral_congr_ae
      filter_upwards with z
      simp [f]
      ring
    · intro lj hlj hne
      have hpair : ki.1 ≠ lj.1 ∨ ki.2 ≠ lj.2 := by
        by_contra h
        push_neg at h
        exact hne (Prod.ext h.1.symm h.2.symm)
      exact integral_ratioResidual_pair_eq_zero_of_ne
        P ki.2 lj.2 ki.1 lj.1 a hpair
    · intro hnot
      exact (hnot hki).elim
  calc
    (∑ ki ∈ S, ∑ lj ∈ S,
        ∫ z : I → Obs d, f ki z * f lj z
          ∂(Measure.pi (fun _ : I => obsLaw P))) =
      ∑ ki ∈ S,
        ∫ z : I → Obs d,
          (tupleRatioCoeff z ki.1 a) ^ 2 *
            (armOutcomeResidual P ki.1 a (z ki.2)) ^ 2
          ∂(Measure.pi (fun _ : I => obsLaw P)) := by
      apply Finset.sum_congr rfl
      intro ki hki
      exact hinner ki hki
    _ = ∑ k ∈ H, ∑ i : I,
        ∫ z : I → Obs d,
          (tupleRatioCoeff z k a) ^ 2 *
            (armOutcomeResidual P k a (z i)) ^ 2
          ∂(Measure.pi (fun _ : I => obsLaw P)) := by
      simpa only [S] using
        (Finset.sum_product H (Finset.univ : Finset I)
          (fun ki =>
            ∫ z : I → Obs d,
              (tupleRatioCoeff z ki.1 a) ^ 2 *
                (armOutcomeResidual P ki.1 a (z ki.2)) ^ 2
              ∂(Measure.pi (fun _ : I => obsLaw P))))

/-- Summing the squared ratio coefficient over observations in its arm
produces exactly the nested count-ratio integrand. -/
lemma sum_tupleRatioCoeff_sq_armIndicator_eq
    {I : Type*} [Fintype I] [DecidableEq I] {d : ℕ}
    (z : I → Obs d) (k : Fin d) (a : Fin 2) :
    (∑ i : I, (tupleRatioCoeff z k a) ^ 2 *
      (categoryArmSet k (finTwoEquiv a)).indicator
        (fun _ => (1 : ℝ)) (z i)) =
      ((indexSet z (categorySet k)).card : ℝ) ^ 2 *
        (if 0 < (indexSet z (categoryArmSet k (finTwoEquiv a))).card then
          ((indexSet z
            (categoryArmSet k (finTwoEquiv a))).card : ℝ)⁻¹ else 0) := by
  classical
  let D := (indexSet z (categoryArmSet k (finTwoEquiv a))).card
  have hsum : (∑ i : I,
      (categoryArmSet k (finTwoEquiv a)).indicator
        (fun _ => (1 : ℝ)) (z i)) = (D : ℝ) := by
    unfold D indexSet
    rw [show (((Finset.univ : Finset I).filter
        (fun i => z i ∈ categoryArmSet k (finTwoEquiv a))).card : ℝ) =
      ∑ i ∈ (Finset.univ : Finset I).filter
        (fun i => z i ∈ categoryArmSet k (finTwoEquiv a)), (1 : ℝ) by simp]
    rw [Finset.sum_filter]
    simp [Set.indicator]
  rw [← Finset.mul_sum, hsum]
  unfold tupleRatioCoeff
  by_cases hD : 0 < D
  · simp only [D] at hD ⊢
    rw [if_pos hD]
    have hDR : (D : ℝ) ≠ 0 := by positivity
    field_simp
  · have hDz : D = 0 := Nat.eq_zero_of_not_pos hD
    simp [D] at hDz
    simp [D, hD, hDz]

/-- Aggregate fixed-set residual variance.  Cross-cell cancellation preserves
the parametric order and the only overlap loss is one factor epsilon inverse. -/
lemma integral_fixedRatioResidual_sq_le
    {I : Type*} [Fintype I] [DecidableEq I] {d : ℕ} {epsilon : ℝ}
    (P : DiscreteLaw d) (hOverlap : Overlap epsilon P) (hepsilon : 0 < epsilon)
    (H : Finset (Fin d)) (a : Fin 2)
    (hp : ∀ k ∈ H, 0 < cellMass P k) :
    ∫ z : I → Obs d, (fixedRatioResidual P z H a) ^ 2
        ∂(Measure.pi (fun _ : I => obsLaw P)) ≤
      (2 * (Fintype.card I : ℝ) / epsilon) *
        ∑ k ∈ H, cellMass P k := by
  rw [integral_fixedRatioResidual_sq_eq_diagonal]
  calc
    (∑ k ∈ H, ∑ i : I,
        ∫ z : I → Obs d,
          (tupleRatioCoeff z k a) ^ 2 *
            (armOutcomeResidual P k a (z i)) ^ 2
          ∂(Measure.pi (fun _ : I => obsLaw P))) ≤
      ∑ k ∈ H, 2 * (Fintype.card I : ℝ) * cellMass P k / epsilon := by
      apply Finset.sum_le_sum
      intro k hk
      calc
        (∑ i : I,
            ∫ z : I → Obs d,
              (tupleRatioCoeff z k a) ^ 2 *
                (armOutcomeResidual P k a (z i)) ^ 2
              ∂(Measure.pi (fun _ : I => obsLaw P))) ≤
          ∑ i : I,
            ∫ z : I → Obs d,
              (tupleRatioCoeff z k a) ^ 2 *
                (categoryArmSet k (finTwoEquiv a)).indicator
                  (fun _ => (1 : ℝ)) (z i)
              ∂(Measure.pi (fun _ : I => obsLaw P)) := by
            apply Finset.sum_le_sum
            intro i hi
            exact integral_ratioResidual_diagonal_le P i k a
        _ = ∫ z : I → Obs d,
            ∑ i : I, (tupleRatioCoeff z k a) ^ 2 *
              (categoryArmSet k (finTwoEquiv a)).indicator
                (fun _ => (1 : ℝ)) (z i)
            ∂(Measure.pi (fun _ : I => obsLaw P)) := by
              rw [integral_finset_sum Finset.univ
                (fun _ _ => Integrable.of_finite)]
        _ = ∫ z : I → Obs d,
            ((indexSet z (categorySet k)).card : ℝ) ^ 2 *
              (if 0 < (indexSet z
                  (categoryArmSet k (finTwoEquiv a))).card then
                ((indexSet z
                  (categoryArmSet k (finTwoEquiv a))).card : ℝ)⁻¹ else 0)
            ∂(Measure.pi (fun _ : I => obsLaw P)) := by
              apply integral_congr_ae
              filter_upwards with z
              exact sum_tupleRatioCoeff_sq_armIndicator_eq z k a
        _ ≤ 2 * (Fintype.card I : ℝ) * cellMass P k / epsilon :=
          ate_nested_count_ratio_integral_le P hOverlap hepsilon k
            (finTwoEquiv a) (hp k hk)
    _ = (2 * (Fintype.card I : ℝ) / epsilon) *
        ∑ k ∈ H, cellMass P k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring

section MissingLabel

variable {I A : Type*} [Fintype I] [DecidableEq I]
  [MeasurableSpace A] [MeasurableSingletonClass A]

private lemma prod_one_distinguished (i : I) (a b : ℝ≥0∞) :
    (∏ j : I, if j = i then a else b) =
      a * b ^ (Fintype.card I - 1) := by
  rw [Fintype.prod_eq_mul_prod_compl i]
  simp only [if_pos]
  have hprod : (∏ j ∈ ({i}ᶜ : Finset I), if j = i then a else b) =
      b ^ (Fintype.card I - 1) := by
    rw [show (∏ j ∈ ({i}ᶜ : Finset I), if j = i then a else b) =
        ∏ _j ∈ ({i}ᶜ : Finset I), b by
      apply Finset.prod_congr rfl
      intro j hj
      simp only [Finset.mem_compl, Finset.mem_singleton] at hj
      simp [hj]]
    rw [Finset.prod_const]
    congr 1
    rw [Finset.card_compl]
    simp
  rw [hprod]

private lemma prod_two_distinguished (i j : I) (a b c : ℝ≥0∞)
    (hij : i ≠ j) :
    (∏ l : I, if l = i then a else if l = j then b else c) =
      a * b * c ^ (Fintype.card I - 2) := by
  rw [Fintype.prod_eq_mul_prod_compl i]
  simp only [if_pos]
  have hjmem : j ∈ ({i}ᶜ : Finset I) := by simp [hij.symm]
  rw [Finset.prod_eq_mul_prod_diff_singleton_of_mem hjmem]
  simp only [hij.symm, if_false, if_pos]
  have hprod :
      (∏ l ∈ ({i}ᶜ : Finset I) \ {j},
          if l = i then a else if l = j then b else c) =
        c ^ (Fintype.card I - 2) := by
    rw [show (∏ l ∈ ({i}ᶜ : Finset I) \ {j},
        if l = i then a else if l = j then b else c) =
        ∏ _l ∈ (({i}ᶜ : Finset I) \ {j}), c by
      apply Finset.prod_congr rfl
      intro l hl
      simp only [Finset.mem_sdiff, Finset.mem_compl, Finset.mem_singleton] at hl
      simp [hl.1, hl.2]]
    rw [Finset.prod_const]
    congr 1
    have hcard : (({i}ᶜ : Finset I).erase j).card = Fintype.card I - 2 := by
      rw [Finset.card_erase_of_mem hjmem]
      rw [Finset.card_compl]
      simp only [Finset.card_singleton]
      omega
    simpa only [Finset.sdiff_singleton_eq_erase] using hcard
  rw [hprod]
  ring

/-- One selected observation has label `s`, while every observation avoids the
forbidden label `r`. -/
def oneSelectedAvoidEvent (i : I) (s r : A) : Set (I → A) :=
  {z | z i = s ∧ ∀ j, z j ≠ r}

lemma oneSelectedAvoidEvent_eq_pi (i : I) (s r : A) (hsr : s ≠ r) :
    oneSelectedAvoidEvent i s r =
      Set.univ.pi (fun j => if j = i then {s} else ({r} : Set A)ᶜ) := by
  ext z
  simp only [oneSelectedAvoidEvent, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ,
    forall_true_left]
  constructor
  · rintro ⟨hzi, hav⟩ j
    by_cases hji : j = i
    · subst j
      simp [hzi]
    · simp [hji, hav j]
  · intro h
    have hi := h i
    simp only [if_pos, Set.mem_singleton_iff] at hi
    refine ⟨hi, ?_⟩
    intro j hjr
    have hj := h j
    by_cases hji : j = i
    · subst j
      exact hsr (hi.symm.trans hjr)
    · simpa [hji, hjr] using hj

/-- Exact product probability of one selected non-forbidden label and no
forbidden labels among the remaining observations. -/
lemma measure_oneSelectedAvoidEvent (P : Measure A) [IsProbabilityMeasure P]
    (i : I) (s r : A) (hsr : s ≠ r) :
    (Measure.pi (fun _ : I => P)) (oneSelectedAvoidEvent i s r) =
      P {s} * P ({r}ᶜ) ^ (Fintype.card I - 1) := by
  rw [oneSelectedAvoidEvent_eq_pi i s r hsr, Measure.pi_pi]
  classical
  have hfun : (fun l : I => P (if l = i then {s} else ({r} : Set A)ᶜ)) =
      fun l => if l = i then P {s} else P ({r}ᶜ) := by
    funext l
    by_cases hli : l = i <;> simp [hli]
  rw [hfun]
  exact prod_one_distinguished i (P {s}) (P ({r}ᶜ))

/-- Two distinct selected observations have prescribed labels while the whole
sample avoids a third, forbidden label. -/
def twoSelectedAvoidEvent (i j : I) (s t r : A) : Set (I → A) :=
  {z | z i = s ∧ z j = t ∧ ∀ l, z l ≠ r}

lemma twoSelectedAvoidEvent_eq_pi (i j : I) (s t r : A)
    (hij : i ≠ j) (hsr : s ≠ r) (htr : t ≠ r) :
    twoSelectedAvoidEvent i j s t r =
      Set.univ.pi (fun l =>
        if l = i then {s} else if l = j then {t} else ({r} : Set A)ᶜ) := by
  ext z
  simp only [twoSelectedAvoidEvent, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ,
    forall_true_left]
  constructor
  · rintro ⟨hzi, hzj, hav⟩ l
    by_cases hli : l = i
    · subst l
      simp [hzi]
    · by_cases hlj : l = j
      · subst l
        simp [hli, hzj]
      · simp [hli, hlj, hav l]
  · intro h
    have hi := h i
    have hj := h j
    simp only [if_pos, Set.mem_singleton_iff] at hi
    simp only [hij.symm, if_false, if_pos, Set.mem_singleton_iff] at hj
    refine ⟨hi, hj, ?_⟩
    intro l hlr
    have hl := h l
    by_cases hli : l = i
    · subst l
      exact hsr (hi.symm.trans hlr)
    · by_cases hlj : l = j
      · subst l
        exact htr (hj.symm.trans hlr)
      · simpa [hli, hlj, hlr] using hl

/-- Exact missing-label two-selection probability, the cross-cell term in
equation (4) of the heavy-cell proof. -/
lemma measure_twoSelectedAvoidEvent (P : Measure A) [IsProbabilityMeasure P]
    (i j : I) (s t r : A) (hij : i ≠ j) (hsr : s ≠ r) (htr : t ≠ r) :
    (Measure.pi (fun _ : I => P)) (twoSelectedAvoidEvent i j s t r) =
      P {s} * P {t} * P ({r}ᶜ) ^ (Fintype.card I - 2) := by
  rw [twoSelectedAvoidEvent_eq_pi i j s t r hij hsr htr, Measure.pi_pi]
  classical
  have hfun : (fun l : I =>
      P (if l = i then {s} else if l = j then {t} else ({r} : Set A)ᶜ)) =
      fun l => if l = i then P {s} else if l = j then P {t} else P ({r}ᶜ) := by
    funext l
    by_cases hli : l = i
    · simp [hli]
    · by_cases hlj : l = j
      · have hji : j ≠ i := fun h => hli (hlj.trans h)
        simp [hli, hlj, hji]
      · simp only [hli, hlj, if_false]
  rw [hfun]
  exact prod_two_distinguished i j (P {s}) (P {t}) (P ({r}ᶜ)) hij

/-- Set-valued version used for an entire treatment arm: the selected
observation belongs to `S`, and every observation avoids the disjoint set `R`. -/
def oneSelectedAvoidSetEvent (i : I) (S R : Set A) : Set (I → A) :=
  {z | z i ∈ S ∧ ∀ j, z j ∉ R}

lemma oneSelectedAvoidSetEvent_eq_pi (i : I) (S R : Set A)
    (hSR : Disjoint S R) :
    oneSelectedAvoidSetEvent i S R =
      Set.univ.pi (fun j => if j = i then S else Rᶜ) := by
  ext z
  simp only [oneSelectedAvoidSetEvent, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ,
    forall_true_left]
  constructor
  · rintro ⟨hzi, hav⟩ j
    by_cases hji : j = i
    · simpa [hji] using hzi
    · simp [hji, hav j]
  · intro h
    have hi := h i
    simp only [if_pos] at hi
    refine ⟨hi, ?_⟩
    intro j hjR
    have hj := h j
    by_cases hji : j = i
    · subst j
      exact Set.disjoint_left.1 hSR hi hjR
    · simpa [hji, hjR] using hj

/-- Exact one-selection/no-forbidden-set product probability. -/
lemma measure_oneSelectedAvoidSetEvent (P : Measure A) [IsProbabilityMeasure P]
    (i : I) (S R : Set A) (hS : MeasurableSet S) (hR : MeasurableSet R)
    (hSR : Disjoint S R) :
    (Measure.pi (fun _ : I => P)) (oneSelectedAvoidSetEvent i S R) =
      P S * P (Rᶜ) ^ (Fintype.card I - 1) := by
  rw [oneSelectedAvoidSetEvent_eq_pi i S R hSR, Measure.pi_pi]
  classical
  have hfun : (fun l : I => P (if l = i then S else Rᶜ)) =
      fun l => if l = i then P S else P (Rᶜ) := by
    funext l
    by_cases hli : l = i <;> simp [hli]
  rw [hfun]
  exact prod_one_distinguished i (P S) (P (Rᶜ))

/-- Number of observations in a category when its specified nested arm is
entirely missing. -/
noncomputable def missingIndexCount (z : I → A) (C R : Set A) : ℕ :=
  if (indexSet z R).card = 0 then (indexSet z C).card else 0

/-- A missing-arm category count is the sum of one-selected/no-forbidden-arm
indicators. -/
lemma missingIndexCount_eq_sum_indicator (z : I → A) (C R : Set A)
    (hRC : R ⊆ C) :
    (missingIndexCount z C R : ℝ) =
      ∑ i : I, (oneSelectedAvoidSetEvent i (C \ R) R).indicator
        (fun _ => (1 : ℝ)) z := by
  classical
  by_cases hzero : (indexSet z R).card = 0
  · have hav : ∀ i, z i ∉ R := by
      intro i hi
      have himem : i ∈ indexSet z R := by simp [indexSet, hi]
      have hne : (indexSet z R).card ≠ 0 :=
        Finset.card_ne_zero.mpr ⟨i, himem⟩
      exact hne hzero
    simp only [missingIndexCount, hzero, if_true, Nat.cast_sum,
      oneSelectedAvoidSetEvent, Set.indicator, Set.mem_setOf_eq]
    unfold indexSet
    simp only [Finset.card_filter, Finset.sum_filter, Finset.sum_const_zero,
      Finset.sum_ite_irrel, Finset.mem_univ, true_and]
    rw [Nat.cast_sum]
    simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hiC : z i ∈ C
    · have hiR : z i ∉ R := hav i
      simp [hiC, hiR, hav]
    · simp [hiC]
  · have hex : ∃ i, z i ∈ R := by
      have hcard : 0 < (indexSet z R).card := Nat.pos_of_ne_zero hzero
      obtain ⟨i, hi⟩ := Finset.card_pos.mp hcard
      exact ⟨i, by simpa [indexSet] using hi⟩
    rcases hex with ⟨i0, hi0⟩
    simp only [missingIndexCount, hzero, if_false, Nat.cast_zero]
    symm
    apply Finset.sum_eq_zero
    intro i hi
    simp only [Set.indicator]
    rw [if_neg]
    intro hevent
    exact hevent.2 i0 hi0

/-- Two ordered, distinct selected observations belong to `S`, while all
observations avoid the disjoint forbidden set `R`. -/
def twoSelectedAvoidSetEvent (i j : I) (S R : Set A) : Set (I → A) :=
  {z | z i ∈ S ∧ z j ∈ S ∧ ∀ l, z l ∉ R}

lemma twoSelectedAvoidSetEvent_eq_pi (i j : I) (S R : Set A)
    (hij : i ≠ j) (hSR : Disjoint S R) :
    twoSelectedAvoidSetEvent i j S R =
      Set.univ.pi (fun l => if l = i then S else if l = j then S else Rᶜ) := by
  ext z
  simp only [twoSelectedAvoidSetEvent, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ,
    forall_true_left]
  constructor
  · rintro ⟨hzi, hzj, hav⟩ l
    by_cases hli : l = i
    · simpa [hli] using hzi
    · by_cases hlj : l = j
      · simpa [hli, hlj] using hzj
      · simp [hli, hlj, hav l]
  · intro h
    have hi := h i
    have hj := h j
    simp only [if_pos] at hi
    simp only [hij.symm, if_false, if_pos] at hj
    refine ⟨hi, hj, ?_⟩
    intro l hlR
    have hl := h l
    by_cases hli : l = i
    · subst l
      exact Set.disjoint_left.1 hSR hi hlR
    · by_cases hlj : l = j
      · subst l
        exact Set.disjoint_left.1 hSR hj hlR
      · simpa [hli, hlj, hlR] using hl

/-- Exact ordered-pair/no-forbidden-set probability.  Summing this lemma over
ordered distinct indices produces the `(m)_2 s^2 (1-r)^(m-2)` term in the
missing-arm second moment. -/
lemma measure_twoSelectedAvoidSetEvent (P : Measure A) [IsProbabilityMeasure P]
    (i j : I) (S R : Set A) (hij : i ≠ j)
    (hS : MeasurableSet S) (hR : MeasurableSet R) (hSR : Disjoint S R) :
    (Measure.pi (fun _ : I => P)) (twoSelectedAvoidSetEvent i j S R) =
      P S * P S * P (Rᶜ) ^ (Fintype.card I - 2) := by
  rw [twoSelectedAvoidSetEvent_eq_pi i j S R hij hSR, Measure.pi_pi]
  classical
  have hfun : (fun l : I =>
      P (if l = i then S else if l = j then S else Rᶜ)) =
      fun l => if l = i then P S else if l = j then P S else P (Rᶜ) := by
    funext l
    by_cases hli : l = i
    · simp [hli]
    · by_cases hlj : l = j
      · have hji : j ≠ i := fun h => hli (hlj.trans h)
        simp [hli, hlj, hji]
      · simp only [hli, hlj, if_false]
  rw [hfun]
  exact prod_two_distinguished i j (P S) (P S) (P (Rᶜ)) hij

/-- Summed diagonal part of the exact missing-arm second moment. -/
lemma sum_measure_oneSelectedAvoidSetEvent (P : Measure A)
    [IsProbabilityMeasure P] (S R : Set A) (hS : MeasurableSet S)
    (hR : MeasurableSet R) (hSR : Disjoint S R) :
    (∑ i : I, (Measure.pi (fun _ : I => P))
        (oneSelectedAvoidSetEvent i S R)) =
      (Fintype.card I : ℝ≥0∞) * P S * P (Rᶜ) ^ (Fintype.card I - 1) := by
  simp_rw [measure_oneSelectedAvoidSetEvent P _ S R hS hR hSR]
  simp [mul_assoc]

/-- Exact first moment of the missing-arm category count in the discrete ATE
model. -/
lemma integral_missingIndexCount_eq {d : ℕ} (P : DiscreteLaw d)
    (k : Fin d) (a : Bool) (hp : 0 < cellMass P k) :
    ∫ z : I → Obs d,
        (missingIndexCount z (categorySet k) (categoryArmSet k a) : ℝ)
        ∂(Measure.pi (fun _ : I => obsLaw P)) =
      (Fintype.card I : ℝ) *
        (cellMass P k * (1 - armPropensity P k a)) *
        (1 - cellMass P k * armPropensity P k a) ^
          (Fintype.card I - 1) := by
  have hpoint : (fun z : I → Obs d =>
      (missingIndexCount z (categorySet k) (categoryArmSet k a) : ℝ)) =
      fun z => ∑ i : I,
        (oneSelectedAvoidSetEvent i
          (categorySet k \ categoryArmSet k a) (categoryArmSet k a)).indicator
          (fun _ => (1 : ℝ)) z := by
    funext z
    exact missingIndexCount_eq_sum_indicator z _ _
      (categoryArmSet_subset_categorySet k a)
  rw [hpoint, integral_finset_sum Finset.univ
    (fun _ _ => Integrable.of_finite)]
  have hint (i : I) :
      ∫ z : I → Obs d,
          (oneSelectedAvoidSetEvent i
            (categorySet k \ categoryArmSet k a) (categoryArmSet k a)).indicator
            (fun _ => (1 : ℝ)) z
          ∂(Measure.pi (fun _ : I => obsLaw P)) =
        (Measure.pi (fun _ : I => obsLaw P)).real
          (oneSelectedAvoidSetEvent i
            (categorySet k \ categoryArmSet k a) (categoryArmSet k a)) := by
    simpa only [Pi.one_apply] using
      (integral_indicator_one (MeasurableSet.of_discrete :
        MeasurableSet (oneSelectedAvoidSetEvent i
          (categorySet k \ categoryArmSet k a) (categoryArmSet k a))))
  simp_rw [hint]
  simp_rw [measureReal_def]
  simp_rw [measure_oneSelectedAvoidSetEvent (obsLaw P) _
    (categorySet k \ categoryArmSet k a) (categoryArmSet k a)
    MeasurableSet.of_discrete MeasurableSet.of_discrete Set.disjoint_sdiff_left]
  simp_rw [ENNReal.toReal_mul, ENNReal.toReal_pow]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [show (obsLaw P (categorySet k \ categoryArmSet k a)).toReal =
      cellMass P k * (1 - armPropensity P k a) by
        exact obsLaw_categoryArm_diff_mass P k a hp]
  rw [show (obsLaw P (categoryArmSet k a)ᶜ).toReal =
      1 - cellMass P k * armPropensity P k a by
        change (obsLaw P).real (categoryArmSet k a)ᶜ = _
        rw [measureReal_compl MeasurableSet.of_discrete,
          measureReal_univ_eq_one, obsLaw_categoryArmSet_mass,
          armMass_eq_cellMass_mul_armPropensity P k a hp]]
  ring

/-- Summed ordered-pair part of the exact missing-arm second moment.  Together
with `sum_measure_oneSelectedAvoidSetEvent`, this is precisely equation (4)'s
`m s (1-r)^(m-1) + (m)_2 s^2 (1-r)^(m-2)` decomposition. -/
lemma sum_measure_twoSelectedAvoidSetEvent (P : Measure A)
    [IsProbabilityMeasure P] (S R : Set A) (hS : MeasurableSet S)
    (hR : MeasurableSet R) (hSR : Disjoint S R) :
    (∑ i : I, ∑ j ∈ (Finset.univ : Finset I).erase i,
        (Measure.pi (fun _ : I => P))
          (twoSelectedAvoidSetEvent i j S R)) =
      ((Fintype.card I).descFactorial 2 : ℝ≥0∞) *
        P S * P S * P (Rᶜ) ^ (Fintype.card I - 2) := by
  classical
  have hexact :
      (∑ i : I, ∑ j ∈ (Finset.univ : Finset I).erase i,
          (Measure.pi (fun _ : I => P))
            (twoSelectedAvoidSetEvent i j S R)) =
        ∑ i : I, ∑ _j ∈ (Finset.univ : Finset I).erase i,
          P S * P S * P (Rᶜ) ^ (Fintype.card I - 2) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    exact measure_twoSelectedAvoidSetEvent P i j S R
      (Finset.ne_of_mem_erase hj).symm hS hR hSR
  rw [hexact]
  simp only [Finset.sum_const, Finset.card_erase_of_mem, Finset.mem_univ,
    nsmul_eq_mul, Finset.card_univ]
  have hdesc : (Fintype.card I).descFactorial 2 =
      Fintype.card I * (Fintype.card I - 1) := by
    cases Fintype.card I <;> simp [Nat.descFactorial, Nat.mul_comm]
  rw [hdesc, Nat.cast_mul]
  ring

/-- Establishes the stated upper bound for one Selected indicator sq. -/
lemma oneSelected_indicator_sq (z : I → A) (i : I) (S R : Set A) :
    ((oneSelectedAvoidSetEvent i S R).indicator (fun _ => (1 : ℝ)) z) ^ 2 =
      (oneSelectedAvoidSetEvent i S R).indicator (fun _ => (1 : ℝ)) z := by
  by_cases h : z ∈ oneSelectedAvoidSetEvent i S R <;> simp [Set.indicator, h]

/-- Establishes the stated upper bound for one Selected indicator mul. -/
lemma oneSelected_indicator_mul (z : I → A) (i j : I) (S R : Set A) :
    (oneSelectedAvoidSetEvent i S R).indicator (fun _ => (1 : ℝ)) z *
        (oneSelectedAvoidSetEvent j S R).indicator (fun _ => (1 : ℝ)) z =
      (twoSelectedAvoidSetEvent i j S R).indicator (fun _ => (1 : ℝ)) z := by
  by_cases hi : z ∈ oneSelectedAvoidSetEvent i S R
  · by_cases hj : z ∈ oneSelectedAvoidSetEvent j S R
    · have ht : z ∈ twoSelectedAvoidSetEvent i j S R := ⟨hi.1, hj.1, hi.2⟩
      simp [Set.indicator, hi, hj, ht]
    · have ht : z ∉ twoSelectedAvoidSetEvent i j S R :=
        fun h => hj ⟨h.2.1, h.2.2⟩
      simp [Set.indicator, hi, hj, ht]
  · have ht : z ∉ twoSelectedAvoidSetEvent i j S R :=
      fun h => hi ⟨h.1, h.2.2⟩
    simp [Set.indicator, hi, ht]

/-- Exact pointwise diagonal/off-diagonal expansion of a squared missing-arm
category count. -/
lemma missingIndexCount_sq_eq_sum_indicator (z : I → A) (C R : Set A)
    (hRC : R ⊆ C) :
    (missingIndexCount z C R : ℝ) ^ 2 =
      ∑ i : I, (oneSelectedAvoidSetEvent i (C \ R) R).indicator
          (fun _ => (1 : ℝ)) z +
        ∑ i : I, ∑ j ∈ (Finset.univ : Finset I).erase i,
          (twoSelectedAvoidSetEvent i j (C \ R) R).indicator
            (fun _ => (1 : ℝ)) z := by
  classical
  rw [missingIndexCount_eq_sum_indicator z C R hRC, sq, Finset.sum_mul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum, ← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  rw [add_comm]
  congr 1
  · simpa [sq] using oneSelected_indicator_sq z i (C \ R) R
  · apply Finset.sum_congr rfl
    intro j hj
    exact oneSelected_indicator_mul z i j (C \ R) R

/-- Exact second moment of one cell's category count on the event that a
specified treatment arm is absent. -/
lemma integral_missingIndexCount_sq_eq {d : ℕ} (P : DiscreteLaw d)
    (k : Fin d) (a : Bool) (hp : 0 < cellMass P k) :
    ∫ z : I → Obs d,
        (missingIndexCount z (categorySet k) (categoryArmSet k a) : ℝ) ^ 2
        ∂(Measure.pi (fun _ : I => obsLaw P)) =
      (Fintype.card I : ℝ) *
          (cellMass P k * (1 - armPropensity P k a)) *
          (1 - cellMass P k * armPropensity P k a) ^ (Fintype.card I - 1) +
        ((Fintype.card I).descFactorial 2 : ℝ) *
          (cellMass P k * (1 - armPropensity P k a)) ^ 2 *
          (1 - cellMass P k * armPropensity P k a) ^ (Fintype.card I - 2) := by
  classical
  let S := categorySet k \ categoryArmSet k a
  let R := categoryArmSet k a
  rw [show (fun z : I → Obs d =>
      (missingIndexCount z (categorySet k) (categoryArmSet k a) : ℝ) ^ 2) =
      fun z =>
        ∑ i : I, (oneSelectedAvoidSetEvent i S R).indicator
            (fun _ => (1 : ℝ)) z +
          ∑ i : I, ∑ j ∈ (Finset.univ : Finset I).erase i,
            (twoSelectedAvoidSetEvent i j S R).indicator
              (fun _ => (1 : ℝ)) z by
    funext z
    exact missingIndexCount_sq_eq_sum_indicator z _ _
      (categoryArmSet_subset_categorySet k a)]
  rw [integral_add Integrable.of_finite Integrable.of_finite]
  simp_rw [integral_finset_sum Finset.univ (fun _ _ => Integrable.of_finite)]
  simp_rw [integral_finset_sum ((Finset.univ : Finset I).erase _)
    (fun _ _ => Integrable.of_finite)]
  have hint1 (i : I) :
      ∫ z : I → Obs d,
          (oneSelectedAvoidSetEvent i S R).indicator
            (fun _ => (1 : ℝ)) z
          ∂(Measure.pi (fun _ : I => obsLaw P)) =
        (Measure.pi (fun _ : I => obsLaw P)).real
          (oneSelectedAvoidSetEvent i S R) := by
    simpa only [Pi.one_apply] using
      (integral_indicator_one (MeasurableSet.of_discrete :
        MeasurableSet (oneSelectedAvoidSetEvent i S R)))
  have hint2 (i j : I) :
      ∫ z : I → Obs d,
          (twoSelectedAvoidSetEvent i j S R).indicator
            (fun _ => (1 : ℝ)) z
          ∂(Measure.pi (fun _ : I => obsLaw P)) =
        (Measure.pi (fun _ : I => obsLaw P)).real
          (twoSelectedAvoidSetEvent i j S R) := by
    simpa only [Pi.one_apply] using
      (integral_indicator_one (MeasurableSet.of_discrete :
        MeasurableSet (twoSelectedAvoidSetEvent i j S R)))
  simp_rw [hint1, hint2]
  simp_rw [measureReal_def]
  have hcross :
      (∑ i : I, ∑ j ∈ (Finset.univ : Finset I).erase i,
          ((Measure.pi (fun _ : I => obsLaw P))
            (twoSelectedAvoidSetEvent i j S R)).toReal) =
        (∑ i : I, ∑ j ∈ (Finset.univ : Finset I).erase i,
          (Measure.pi (fun _ : I => obsLaw P))
            (twoSelectedAvoidSetEvent i j S R)).toReal := by
    rw [ENNReal.toReal_sum]
    · apply Finset.sum_congr rfl
      intro i hi
      rw [ENNReal.toReal_sum]
      intro j hj
      exact measure_ne_top _ _
    · intro i hi
      rw [ENNReal.sum_ne_top]
      intro j hj
      exact measure_ne_top _ _
  have hfirst :
      (∑ i : I, ((Measure.pi (fun _ : I => obsLaw P))
          (oneSelectedAvoidSetEvent i S R)).toReal) =
        (∑ i : I, (Measure.pi (fun _ : I => obsLaw P))
          (oneSelectedAvoidSetEvent i S R)).toReal := by
    rw [ENNReal.toReal_sum]
    intro i hi
    exact measure_ne_top _ _
  rw [hfirst, hcross]
  rw [sum_measure_oneSelectedAvoidSetEvent (obsLaw P) S R
      MeasurableSet.of_discrete MeasurableSet.of_discrete Set.disjoint_sdiff_left]
  rw [sum_measure_twoSelectedAvoidSetEvent (obsLaw P) S R
      MeasurableSet.of_discrete MeasurableSet.of_discrete Set.disjoint_sdiff_left]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast]
  rw [show (obsLaw P S).toReal =
      cellMass P k * (1 - armPropensity P k a) by
        exact obsLaw_categoryArm_diff_mass P k a hp]
  rw [show (obsLaw P Rᶜ).toReal =
      1 - cellMass P k * armPropensity P k a by
        change (obsLaw P).real (categoryArmSet k a)ᶜ = _
        rw [measureReal_compl MeasurableSet.of_discrete,
          measureReal_univ_eq_one, obsLaw_categoryArmSet_mass,
          armMass_eq_cellMass_mul_armPropensity P k a hp]]
  ring

/-- Cross-category event: the two selected observations may belong to
different sets, and the full sample avoids a common forbidden set. -/
def twoSelectedAvoidSetsEvent (i j : I) (S T R : Set A) : Set (I → A) :=
  {z | z i ∈ S ∧ z j ∈ T ∧ ∀ l, z l ∉ R}

lemma twoSelectedAvoidSetsEvent_eq_pi (i j : I) (S T R : Set A)
    (hij : i ≠ j) (hSR : Disjoint S R) (hTR : Disjoint T R) :
    twoSelectedAvoidSetsEvent i j S T R =
      Set.univ.pi (fun l => if l = i then S else if l = j then T else Rᶜ) := by
  ext z
  simp only [twoSelectedAvoidSetsEvent, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ,
    forall_true_left]
  constructor
  · rintro ⟨hzi, hzj, hav⟩ l
    by_cases hli : l = i
    · simpa [hli] using hzi
    · by_cases hlj : l = j
      · have hji : j ≠ i := hij.symm
        simpa [hji, hlj] using hzj
      · simp [hli, hlj, hav l]
  · intro h
    have hi := h i
    have hj := h j
    simp only [if_pos] at hi
    simp only [hij.symm, if_false, if_pos] at hj
    refine ⟨hi, hj, ?_⟩
    intro l hlR
    have hl := h l
    by_cases hli : l = i
    · subst l
      exact Set.disjoint_left.1 hSR hi hlR
    · by_cases hlj : l = j
      · subst l
        exact Set.disjoint_left.1 hTR hj hlR
      · simpa [hli, hlj, hlR] using hl

/-- Exact cross-category ordered-pair probability.  Taking `R` to be the
union of the two treated-arm atoms gives the second line of equation (4). -/
lemma measure_twoSelectedAvoidSetsEvent (P : Measure A) [IsProbabilityMeasure P]
    (i j : I) (S T R : Set A) (hij : i ≠ j)
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hR : MeasurableSet R)
    (hSR : Disjoint S R) (hTR : Disjoint T R) :
    (Measure.pi (fun _ : I => P)) (twoSelectedAvoidSetsEvent i j S T R) =
      P S * P T * P (Rᶜ) ^ (Fintype.card I - 2) := by
  rw [twoSelectedAvoidSetsEvent_eq_pi i j S T R hij hSR hTR, Measure.pi_pi]
  classical
  have hfun : (fun l : I =>
      P (if l = i then S else if l = j then T else Rᶜ)) =
      fun l => if l = i then P S else if l = j then P T else P (Rᶜ) := by
    funext l
    by_cases hli : l = i
    · simp [hli]
    · by_cases hlj : l = j
      · have hji : j ≠ i := fun h => hli (hlj.trans h)
        simp [hli, hlj, hji]
      · simp only [hli, hlj, if_false]
  rw [hfun]
  exact prod_two_distinguished i j (P S) (P T) (P (Rᶜ)) hij

/-- Summed cross-category ordered-pair term. -/
lemma sum_measure_twoSelectedAvoidSetsEvent (P : Measure A)
    [IsProbabilityMeasure P] (S T R : Set A) (hS : MeasurableSet S)
    (hT : MeasurableSet T) (hR : MeasurableSet R)
    (hSR : Disjoint S R) (hTR : Disjoint T R) :
    (∑ i : I, ∑ j ∈ (Finset.univ : Finset I).erase i,
        (Measure.pi (fun _ : I => P))
          (twoSelectedAvoidSetsEvent i j S T R)) =
      ((Fintype.card I).descFactorial 2 : ℝ≥0∞) *
        P S * P T * P (Rᶜ) ^ (Fintype.card I - 2) := by
  classical
  have hexact :
      (∑ i : I, ∑ j ∈ (Finset.univ : Finset I).erase i,
          (Measure.pi (fun _ : I => P))
            (twoSelectedAvoidSetsEvent i j S T R)) =
        ∑ i : I, ∑ _j ∈ (Finset.univ : Finset I).erase i,
          P S * P T * P (Rᶜ) ^ (Fintype.card I - 2) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    exact measure_twoSelectedAvoidSetsEvent P i j S T R
      (Finset.ne_of_mem_erase hj).symm hS hT hR hSR hTR
  rw [hexact]
  simp only [Finset.sum_const, Finset.card_erase_of_mem, Finset.mem_univ,
    nsmul_eq_mul, Finset.card_univ]
  have hdesc : (Fintype.card I).descFactorial 2 =
      Fintype.card I * (Fintype.card I - 1) := by
    cases Fintype.card I <;> simp [Nat.descFactorial, Nat.mul_comm]
  rw [hdesc, Nat.cast_mul]
  ring

/-- Establishes the stated upper bound for one Selected indicator mul cross. -/
lemma oneSelected_indicator_mul_cross (z : I → A) (i j : I)
    (S T R Q : Set A) :
    (oneSelectedAvoidSetEvent i S R).indicator (fun _ => (1 : ℝ)) z *
        (oneSelectedAvoidSetEvent j T Q).indicator (fun _ => (1 : ℝ)) z =
      (twoSelectedAvoidSetsEvent i j S T (R ∪ Q)).indicator
        (fun _ => (1 : ℝ)) z := by
  by_cases hi : z ∈ oneSelectedAvoidSetEvent i S R
  · by_cases hj : z ∈ oneSelectedAvoidSetEvent j T Q
    · have ht : z ∈ twoSelectedAvoidSetsEvent i j S T (R ∪ Q) := by
        refine ⟨hi.1, hj.1, ?_⟩
        intro l hl
        exact hl.elim (hi.2 l) (hj.2 l)
      simp [Set.indicator, hi, hj, ht]
    · have ht : z ∉ twoSelectedAvoidSetsEvent i j S T (R ∪ Q) :=
        fun h => hj ⟨h.2.1, fun l hl => h.2.2 l (Or.inr hl)⟩
      simp [Set.indicator, hi, hj, ht]
  · have ht : z ∉ twoSelectedAvoidSetsEvent i j S T (R ∪ Q) :=
      fun h => hi ⟨h.1, fun l hl => h.2.2 l (Or.inl hl)⟩
    simp [Set.indicator, hi, ht]

/-- Establishes the stated upper bound for one Selected indicator mul zero of disjoint. -/
lemma oneSelected_indicator_mul_zero_of_disjoint (z : I → A) (i : I)
    (S T R Q : Set A) (hST : Disjoint S T) :
    (oneSelectedAvoidSetEvent i S R).indicator (fun _ => (1 : ℝ)) z *
        (oneSelectedAvoidSetEvent i T Q).indicator (fun _ => (1 : ℝ)) z = 0 := by
  by_cases hi : z ∈ oneSelectedAvoidSetEvent i S R
  · have hj : z ∉ oneSelectedAvoidSetEvent i T Q := fun h =>
      Set.disjoint_left.1 hST hi.1 h.1
    simp [Set.indicator, hi, hj]
  · simp [Set.indicator, hi]

/-- Distinct categories cannot contribute through the same observation, so
their missing-arm product is an ordered-pair cross-event sum. -/
lemma missingIndexCount_mul_eq_sum_cross (z : I → A)
    (C D R Q : Set A) (hRC : R ⊆ C) (hQD : Q ⊆ D)
    (hCD : Disjoint C D) :
    (missingIndexCount z C R : ℝ) * (missingIndexCount z D Q : ℝ) =
      ∑ i : I, ∑ j ∈ (Finset.univ : Finset I).erase i,
        (twoSelectedAvoidSetsEvent i j (C \ R) (D \ Q) (R ∪ Q)).indicator
          (fun _ => (1 : ℝ)) z := by
  classical
  rw [missingIndexCount_eq_sum_indicator z C R hRC,
    missingIndexCount_eq_sum_indicator z D Q hQD, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum, ← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  rw [oneSelected_indicator_mul_zero_of_disjoint z i (C \ R) (D \ Q) R Q
    (hCD.mono Set.diff_subset Set.diff_subset), add_zero]
  apply Finset.sum_congr rfl
  intro j hj
  exact oneSelected_indicator_mul_cross z i j (C \ R) (D \ Q) R Q

/-- Establishes the stated property of category Set disjoint of ne in the discrete average-treatment-effect construction. -/
lemma categorySet_disjoint_of_ne {d : ℕ} (k l : Fin d) (hkl : k ≠ l) :
    Disjoint (categorySet k) (categorySet l) := by
  rw [Set.disjoint_left]
  intro x hxk hxl
  exact hkl (hxk.symm.trans hxl)

/-- Exact cross moment of the missing-arm counts in two distinct categories. -/
lemma integral_missingIndexCount_mul_eq {d : ℕ} (P : DiscreteLaw d)
    (k l : Fin d) (a : Bool) (hkl : k ≠ l)
    (hpk : 0 < cellMass P k) (hpl : 0 < cellMass P l) :
    ∫ z : I → Obs d,
        (missingIndexCount z (categorySet k) (categoryArmSet k a) : ℝ) *
          (missingIndexCount z (categorySet l) (categoryArmSet l a) : ℝ)
        ∂(Measure.pi (fun _ : I => obsLaw P)) =
      ((Fintype.card I).descFactorial 2 : ℝ) *
        (cellMass P k * (1 - armPropensity P k a)) *
        (cellMass P l * (1 - armPropensity P l a)) *
        (1 - cellMass P k * armPropensity P k a -
          cellMass P l * armPropensity P l a) ^ (Fintype.card I - 2) := by
  classical
  let C := categorySet k
  let D := categorySet l
  let R := categoryArmSet k a
  let Q := categoryArmSet l a
  let S := C \ R
  let T := D \ Q
  let U := R ∪ Q
  have hCD : Disjoint C D := categorySet_disjoint_of_ne k l hkl
  have hRQ : Disjoint R Q := hCD.mono
    (categoryArmSet_subset_categorySet k a)
    (categoryArmSet_subset_categorySet l a)
  have hSU : Disjoint S U := by
    rw [Set.disjoint_left]
    intro x hx hxu
    rcases hxu with hxR | hxQ
    · exact hx.2 hxR
    · exact Set.disjoint_left.1 hCD hx.1
        (categoryArmSet_subset_categorySet l a hxQ)
  have hTU : Disjoint T U := by
    rw [Set.disjoint_left]
    intro x hx hxu
    rcases hxu with hxR | hxQ
    · exact Set.disjoint_left.1 hCD
        (categoryArmSet_subset_categorySet k a hxR) hx.1
    · exact hx.2 hxQ
  rw [show (fun z : I → Obs d =>
      (missingIndexCount z C R : ℝ) * (missingIndexCount z D Q : ℝ)) =
      fun z => ∑ i : I, ∑ j ∈ (Finset.univ : Finset I).erase i,
        (twoSelectedAvoidSetsEvent i j S T U).indicator
          (fun _ => (1 : ℝ)) z by
    funext z
    exact missingIndexCount_mul_eq_sum_cross z C D R Q
      (categoryArmSet_subset_categorySet k a)
      (categoryArmSet_subset_categorySet l a) hCD]
  simp_rw [integral_finset_sum Finset.univ (fun _ _ => Integrable.of_finite)]
  simp_rw [integral_finset_sum ((Finset.univ : Finset I).erase _)
    (fun _ _ => Integrable.of_finite)]
  have hint (i j : I) :
      ∫ z : I → Obs d,
          (twoSelectedAvoidSetsEvent i j S T U).indicator
            (fun _ => (1 : ℝ)) z
          ∂(Measure.pi (fun _ : I => obsLaw P)) =
        (Measure.pi (fun _ : I => obsLaw P)).real
          (twoSelectedAvoidSetsEvent i j S T U) := by
    simpa only [Pi.one_apply] using
      (integral_indicator_one (MeasurableSet.of_discrete :
        MeasurableSet (twoSelectedAvoidSetsEvent i j S T U)))
  simp_rw [hint, measureReal_def]
  have hcross :
      (∑ i : I, ∑ j ∈ (Finset.univ : Finset I).erase i,
          ((Measure.pi (fun _ : I => obsLaw P))
            (twoSelectedAvoidSetsEvent i j S T U)).toReal) =
        (∑ i : I, ∑ j ∈ (Finset.univ : Finset I).erase i,
          (Measure.pi (fun _ : I => obsLaw P))
            (twoSelectedAvoidSetsEvent i j S T U)).toReal := by
    rw [ENNReal.toReal_sum]
    · apply Finset.sum_congr rfl
      intro i hi
      rw [ENNReal.toReal_sum]
      intro j hj
      exact measure_ne_top _ _
    · intro i hi
      rw [ENNReal.sum_ne_top]
      intro j hj
      exact measure_ne_top _ _
  rw [hcross]
  rw [sum_measure_twoSelectedAvoidSetsEvent (obsLaw P) S T U
    MeasurableSet.of_discrete MeasurableSet.of_discrete MeasurableSet.of_discrete
    hSU hTU]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast]
  rw [show (obsLaw P S).toReal =
      cellMass P k * (1 - armPropensity P k a) by
    exact obsLaw_categoryArm_diff_mass P k a hpk]
  rw [show (obsLaw P T).toReal =
      cellMass P l * (1 - armPropensity P l a) by
    exact obsLaw_categoryArm_diff_mass P l a hpl]
  rw [show (obsLaw P Uᶜ).toReal =
      1 - cellMass P k * armPropensity P k a -
        cellMass P l * armPropensity P l a by
    change (obsLaw P).real (R ∪ Q)ᶜ = _
    rw [measureReal_compl MeasurableSet.of_discrete, measureReal_univ_eq_one,
      measureReal_union hRQ MeasurableSet.of_discrete,
      obsLaw_categoryArmSet_mass, armMass_eq_cellMass_mul_armPropensity P k a hpk,
      obsLaw_categoryArmSet_mass, armMass_eq_cellMass_mul_armPropensity P l a hpl]
    ring]

/-- Defines fixed Missing Count, the stated quantity or construction used in the discrete average-treatment-effect estimator. -/
noncomputable def fixedMissingCount {J : Type*} [Fintype J] [DecidableEq J]
    {d : ℕ} (z : J → Obs d) (H : Finset (Fin d)) (a : Bool) : ℝ :=
  ∑ k ∈ H, (missingIndexCount z (categorySet k) (categoryArmSet k a) : ℝ)

/-- Defines fixed Missing Outcome Bias, the stated quantity or construction used in the discrete average-treatment-effect estimator. -/
noncomputable def fixedMissingOutcomeBias {J : Type*} [Fintype J]
    [DecidableEq J] {d : ℕ} (P : DiscreteLaw d) (z : J → Obs d)
    (H : Finset (Fin d)) (a : Fin 2) : ℝ :=
  ∑ k ∈ H, outcomeMean P (finTwoEquiv a) k *
    (missingIndexCount z (categorySet k)
      (categoryArmSet k (finTwoEquiv a)) : ℝ)

/-- Establishes the stated upper bound for abs fixed Missing Outcome Bias le. -/
lemma abs_fixedMissingOutcomeBias_le {J : Type*} [Fintype J]
    [DecidableEq J] {d : ℕ} (P : DiscreteLaw d) (z : J → Obs d)
    (H : Finset (Fin d)) (a : Fin 2) :
    |fixedMissingOutcomeBias P z H a| ≤
      fixedMissingCount z H (finTwoEquiv a) := by
  classical
  calc
    |fixedMissingOutcomeBias P z H a| ≤
        ∑ k ∈ H, |outcomeMean P (finTwoEquiv a) k *
          (missingIndexCount z (categorySet k)
            (categoryArmSet k (finTwoEquiv a)) : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ H,
        (missingIndexCount z (categorySet k)
          (categoryArmSet k (finTwoEquiv a)) : ℝ) := by
      apply Finset.sum_le_sum
      intro k hk
      have hmu := outcomeMean_mem_unitInterval P (finTwoEquiv a) k
      rw [abs_mul, abs_of_nonneg hmu.1,
        abs_of_nonneg (by positivity :
          0 ≤ (missingIndexCount z (categorySet k)
            (categoryArmSet k (finTwoEquiv a)) : ℝ))]
      exact mul_le_of_le_one_left (by positivity) hmu.2
    _ = fixedMissingCount z H (finTwoEquiv a) := rfl

/-- Establishes the stated upper bound for fixed Missing Outcome Bias sq le. -/
lemma fixedMissingOutcomeBias_sq_le {J : Type*} [Fintype J]
    [DecidableEq J] {d : ℕ} (P : DiscreteLaw d) (z : J → Obs d)
    (H : Finset (Fin d)) (a : Fin 2) :
    (fixedMissingOutcomeBias P z H a) ^ 2 ≤
      (fixedMissingCount z H (finTwoEquiv a)) ^ 2 := by
  have hcount : 0 ≤ fixedMissingCount z H (finTwoEquiv a) := by
    unfold fixedMissingCount
    positivity
  rw [← sq_abs (fixedMissingOutcomeBias P z H a),
    ← sq_abs (fixedMissingCount z H (finTwoEquiv a)),
    abs_of_nonneg hcount]
  exact pow_le_pow_left₀ (abs_nonneg _)
    (abs_fixedMissingOutcomeBias_le P z H a) 2

/-- Establishes the stated property of fixed Missing Count sq expand in the discrete average-treatment-effect construction. -/
lemma fixedMissingCount_sq_expand {J : Type*} [Fintype J] [DecidableEq J]
    {d : ℕ} (z : J → Obs d) (H : Finset (Fin d)) (a : Bool) :
    (fixedMissingCount z H a) ^ 2 =
      ∑ k ∈ H, (missingIndexCount z (categorySet k) (categoryArmSet k a) : ℝ) ^ 2 +
        ∑ k ∈ H, ∑ l ∈ H.erase k,
          (missingIndexCount z (categorySet k) (categoryArmSet k a) : ℝ) *
            (missingIndexCount z (categorySet l) (categoryArmSet l a) : ℝ) := by
  classical
  unfold fixedMissingCount
  rw [sq, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mul_sum, ← Finset.sum_erase_add _ _ hk, add_comm]
  rw [pow_two]

/-- Exact aggregate missing-arm second moment on a fixed category set. -/
lemma integral_fixedMissingCount_sq_eq {J : Type*} [Fintype J] [DecidableEq J]
    {d : ℕ} (P : DiscreteLaw d) (H : Finset (Fin d)) (a : Bool)
    (hp : ∀ k ∈ H, 0 < cellMass P k) :
    ∫ z : J → Obs d, (fixedMissingCount z H a) ^ 2
        ∂(Measure.pi (fun _ : J => obsLaw P)) =
      ∑ k ∈ H,
        ((Fintype.card J : ℝ) *
            (cellMass P k * (1 - armPropensity P k a)) *
            (1 - cellMass P k * armPropensity P k a) ^ (Fintype.card J - 1) +
          ((Fintype.card J).descFactorial 2 : ℝ) *
            (cellMass P k * (1 - armPropensity P k a)) ^ 2 *
            (1 - cellMass P k * armPropensity P k a) ^ (Fintype.card J - 2)) +
        ∑ k ∈ H, ∑ l ∈ H.erase k,
          ((Fintype.card J).descFactorial 2 : ℝ) *
            (cellMass P k * (1 - armPropensity P k a)) *
            (cellMass P l * (1 - armPropensity P l a)) *
            (1 - cellMass P k * armPropensity P k a -
              cellMass P l * armPropensity P l a) ^ (Fintype.card J - 2) := by
  classical
  rw [show (fun z : J → Obs d => (fixedMissingCount z H a) ^ 2) =
      fun z =>
        ∑ k ∈ H, (missingIndexCount z (categorySet k) (categoryArmSet k a) : ℝ) ^ 2 +
          ∑ k ∈ H, ∑ l ∈ H.erase k,
            (missingIndexCount z (categorySet k) (categoryArmSet k a) : ℝ) *
              (missingIndexCount z (categorySet l) (categoryArmSet l a) : ℝ) by
    funext z
    exact fixedMissingCount_sq_expand z H a]
  rw [integral_add Integrable.of_finite Integrable.of_finite]
  simp_rw [integral_finset_sum H (fun _ _ => Integrable.of_finite)]
  simp_rw [integral_finset_sum (H.erase _) (fun _ _ => Integrable.of_finite)]
  apply congrArg₂ (.+.)
  · apply Finset.sum_congr rfl
    intro k hk
    exact integral_missingIndexCount_sq_eq P k a (hp k hk)
  · apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro l hl
    exact integral_missingIndexCount_mul_eq P k l a
      (Finset.ne_of_mem_erase hl).symm (hp k hk)
      (hp l (Finset.mem_of_mem_erase hl))

end MissingLabel

/-- Establishes the stated upper bound for desc Factorial two cast le sq. -/
lemma descFactorial_two_cast_le_sq (m : ℕ) :
    (m.descFactorial 2 : ℝ) ≤ (m : ℝ) ^ 2 := by
  have hdesc : m.descFactorial 2 = m * (m - 1) := by
    cases m <;> simp [Nat.descFactorial, Nat.mul_comm]
  rw [hdesc, Nat.cast_mul]
  have hsub : ((m - 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast Nat.sub_le m 1
  nlinarith [show 0 ≤ (m : ℝ) by positivity]

/-- Establishes the stated property of missing diag envelope in the discrete average-treatment-effect construction. -/
lemma missing_diag_envelope (m : ℕ) (p rho epsilon : ℝ)
    (hm : 2 ≤ m) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hr0 : 0 ≤ rho) (hr1 : rho ≤ 1) (he : epsilon * p ≤ p * rho) :
    (m : ℝ) * (p * (1 - rho)) * (1 - p * rho) ^ (m - 1) +
        (m.descFactorial 2 : ℝ) * (p * (1 - rho)) ^ 2 *
          (1 - p * rho) ^ (m - 2) ≤
      (m : ℝ) * p + (m : ℝ) ^ 2 *
        (p * Real.exp (-((m - 2 : ℕ) : ℝ) / 2 * epsilon * p)) ^ 2 := by
  have hq0 : 0 ≤ p * rho := mul_nonneg hp0 hr0
  have hq1 : p * rho ≤ 1 := (mul_le_of_le_one_right hp0 hr1).trans hp1
  have hb0 : 0 ≤ 1 - p * rho := sub_nonneg.mpr hq1
  have hb1 : 1 - p * rho ≤ 1 := by linarith
  have hs0 : 0 ≤ p * (1 - rho) := mul_nonneg hp0 (sub_nonneg.mpr hr1)
  have hsp : p * (1 - rho) ≤ p := by nlinarith
  have hpow1 : (1 - p * rho) ^ (m - 1) ≤ 1 :=
    pow_le_one₀ hb0 hb1
  have hpow2 : (1 - p * rho) ^ (m - 2) ≤
      Real.exp (-((m - 2 : ℕ) : ℝ) * epsilon * p) := by
    calc
      _ ≤ Real.exp (-((m - 2 : ℕ) : ℝ) * (p * rho)) :=
        one_sub_pow_le_exp_neg_mul (p * rho) (m - 2) hq1
      _ ≤ Real.exp (-((m - 2 : ℕ) : ℝ) * epsilon * p) := by
        apply Real.exp_le_exp.mpr
        have hu : 0 ≤ ((m - 2 : ℕ) : ℝ) := by positivity
        nlinarith
  have hfirst : (m : ℝ) * (p * (1 - rho)) *
      (1 - p * rho) ^ (m - 1) ≤ (m : ℝ) * p := by
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc
      p * (1 - rho) * (1 - p * rho) ^ (m - 1) ≤
          p * (1 - p * rho) ^ (m - 1) := by
        exact mul_le_mul_of_nonneg_right hsp (by positivity)
      _ ≤ p * 1 := mul_le_mul_of_nonneg_left hpow1 hp0
      _ = p := mul_one p
  have hsecond : (m.descFactorial 2 : ℝ) * (p * (1 - rho)) ^ 2 *
      (1 - p * rho) ^ (m - 2) ≤
      (m : ℝ) ^ 2 * p ^ 2 *
        Real.exp (-((m - 2 : ℕ) : ℝ) * epsilon * p) := by
    have hd := descFactorial_two_cast_le_sq m
    have hs2 : (p * (1 - rho)) ^ 2 ≤ p ^ 2 := by
      exact pow_le_pow_left₀ hs0 hsp 2
    gcongr
  calc
    _ ≤ (m : ℝ) * p + (m : ℝ) ^ 2 * p ^ 2 *
        Real.exp (-((m - 2 : ℕ) : ℝ) * epsilon * p) :=
      add_le_add hfirst hsecond
    _ = (m : ℝ) * p + (m : ℝ) ^ 2 *
        (p * Real.exp (-((m - 2 : ℕ) : ℝ) / 2 * epsilon * p)) ^ 2 := by
      have hexp :
          Real.exp (-((m - 2 : ℕ) : ℝ) / 2 * epsilon * p) ^ 2 =
            Real.exp (-((m - 2 : ℕ) : ℝ) * epsilon * p) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      rw [mul_pow, hexp]
      ring

/-- Establishes the stated property of missing cross envelope in the discrete average-treatment-effect construction. -/
lemma missing_cross_envelope (m : ℕ)
    (p q rho sigma epsilon : ℝ)
    (hp0 : 0 ≤ p) (hq0 : 0 ≤ q) (hr0 : 0 ≤ rho) (hs0 : 0 ≤ sigma)
    (hr1 : rho ≤ 1) (hs1 : sigma ≤ 1) (he0 : 0 ≤ epsilon)
    (heP : epsilon * p ≤ p * rho) (heQ : epsilon * q ≤ q * sigma)
    (hsum : p * rho + q * sigma ≤ 1) :
    (m.descFactorial 2 : ℝ) * (p * (1 - rho)) * (q * (1 - sigma)) *
        (1 - p * rho - q * sigma) ^ (m - 2) ≤
      (m : ℝ) ^ 2 *
        (p * Real.exp (-((m - 2 : ℕ) : ℝ) / 2 * epsilon * p)) *
        (q * Real.exp (-((m - 2 : ℕ) : ℝ) / 2 * epsilon * q)) := by
  let u : ℝ := ((m - 2 : ℕ) : ℝ)
  have hbase0 : 0 ≤ 1 - (p * rho + q * sigma) := sub_nonneg.mpr hsum
  have hbase : 1 - p * rho - q * sigma = 1 - (p * rho + q * sigma) := by ring
  have hpow : (1 - p * rho - q * sigma) ^ (m - 2) ≤
      Real.exp (-u * (epsilon * p + epsilon * q)) := by
    rw [hbase]
    calc
      _ ≤ Real.exp (-u * (p * rho + q * sigma)) :=
        one_sub_pow_le_exp_neg_mul (p * rho + q * sigma) (m - 2) hsum
      _ ≤ Real.exp (-u * (epsilon * p + epsilon * q)) := by
        apply Real.exp_le_exp.mpr
        have hu : 0 ≤ u := by dsimp [u]; positivity
        nlinarith
  have hsp : p * (1 - rho) ≤ p := by nlinarith
  have hsq : q * (1 - sigma) ≤ q := by nlinarith
  have hsp0 : 0 ≤ p * (1 - rho) := mul_nonneg hp0 (sub_nonneg.mpr hr1)
  have hsq0 : 0 ≤ q * (1 - sigma) := mul_nonneg hq0 (sub_nonneg.mpr hs1)
  have hraw :
      (m.descFactorial 2 : ℝ) * (p * (1 - rho)) * (q * (1 - sigma)) *
          (1 - p * rho - q * sigma) ^ (m - 2) ≤
        (m : ℝ) ^ 2 * p * q *
          Real.exp (-u * (epsilon * p + epsilon * q)) := by
    have hd := descFactorial_two_cast_le_sq m
    have hpow0 : 0 ≤ (1 - p * rho - q * sigma) ^ (m - 2) := by
      rw [hbase]
      positivity
    gcongr
  have hexp : Real.exp (-u * (epsilon * p + epsilon * q)) ≤
      Real.exp (-u / 2 * epsilon * p) * Real.exp (-u / 2 * epsilon * q) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hu : 0 ≤ u := by dsimp [u]; positivity
    have hsumep : 0 ≤ epsilon * p + epsilon * q :=
      add_nonneg (mul_nonneg he0 hp0) (mul_nonneg he0 hq0)
    have hhalf : u / 2 ≤ u := by nlinarith
    have hmul := mul_le_mul_of_nonneg_right hhalf hsumep
    nlinarith
  calc
    _ ≤ (m : ℝ) ^ 2 * p * q *
        Real.exp (-u * (epsilon * p + epsilon * q)) := hraw
    _ ≤ (m : ℝ) ^ 2 * p * q *
        (Real.exp (-u / 2 * epsilon * p) * Real.exp (-u / 2 * epsilon * q)) := by
      gcongr
    _ = (m : ℝ) ^ 2 *
        (p * Real.exp (-((m - 2 : ℕ) : ℝ) / 2 * epsilon * p)) *
        (q * Real.exp (-((m - 2 : ℕ) : ℝ) / 2 * epsilon * q)) := by
      dsimp [u]
      ring

/-- Aggregate second-moment bound for the missing-arm count on a fixed set of
heavy categories.  The diagonal contributes at most `m`; the off-diagonal
and exponentially small part of the diagonal combine into the square of one
mass-exponential sum. -/
lemma integral_fixedMissingCount_sq_le {J : Type*} [Fintype J] [DecidableEq J]
    {d : ℕ} {epsilon B : ℝ} (P : DiscreteLaw d) (H : Finset (Fin d))
    (a : Bool) (hm : 3 ≤ Fintype.card J) (hOverlap : Overlap epsilon P)
    (hepsilon : 0 < epsilon) (hB : 0 < B)
    (hp : ∀ k ∈ H, B ≤ cellMass P k) :
    ∫ z : J → Obs d, (fixedMissingCount z H a) ^ 2
        ∂(Measure.pi (fun _ : J => obsLaw P)) ≤
      (Fintype.card J : ℝ) + (Fintype.card J : ℝ) ^ 2 *
        (H.card /
          (((((Fintype.card J - 2 : ℕ) : ℝ) / 2 * epsilon) ^ 2) * B)) ^ 2 := by
  classical
  let m := Fintype.card J
  let u : ℝ := ((m - 2 : ℕ) : ℝ) / 2 * epsilon
  let f : Fin d → ℝ := fun k =>
    cellMass P k * Real.exp (-u * cellMass P k)
  have hm2 : 2 ≤ m := le_trans (by omega : 2 ≤ 3) hm
  have hsub : 0 < m - 2 := by omega
  have hu : 0 < u := by
    dsimp [u]
    positivity
  have hpPos : ∀ k ∈ H, 0 < cellMass P k := by
    intro k hk
    exact hB.trans_le (hp k hk)
  have hdiag : ∀ k ∈ H,
      (m : ℝ) * (cellMass P k * (1 - armPropensity P k a)) *
            (1 - cellMass P k * armPropensity P k a) ^ (m - 1) +
          (m.descFactorial 2 : ℝ) *
            (cellMass P k * (1 - armPropensity P k a)) ^ 2 *
            (1 - cellMass P k * armPropensity P k a) ^ (m - 2) ≤
        (m : ℝ) * cellMass P k + (m : ℝ) ^ 2 * (f k) ^ 2 := by
    intro k hk
    have hrho := armPropensity_mem_unitInterval P k a
    have heLower := armPropensity_lower_of_overlap P hOverlap k a (hpPos k hk)
    have heMul : epsilon * cellMass P k ≤
        cellMass P k * armPropensity P k a := by
      simpa [mul_comm] using
        mul_le_mul_of_nonneg_left heLower (cellMass_mem_unitInterval P k).1
    convert
      missing_diag_envelope m (cellMass P k) (armPropensity P k a) epsilon
        hm2 (cellMass_mem_unitInterval P k).1
        (cellMass_mem_unitInterval P k).2 hrho.1 hrho.2 heMul using 1 <;>
      dsimp [m, u, f] <;> ring
  have hcross : ∀ k ∈ H, ∀ l ∈ H.erase k,
      (m.descFactorial 2 : ℝ) *
            (cellMass P k * (1 - armPropensity P k a)) *
            (cellMass P l * (1 - armPropensity P l a)) *
            (1 - cellMass P k * armPropensity P k a -
              cellMass P l * armPropensity P l a) ^ (m - 2) ≤
        (m : ℝ) ^ 2 * f k * f l := by
    intro k hk l hl
    have hlH : l ∈ H := Finset.mem_of_mem_erase hl
    have hkl : k ≠ l := (Finset.ne_of_mem_erase hl).symm
    have hrho := armPropensity_mem_unitInterval P k a
    have hsigma := armPropensity_mem_unitInterval P l a
    have heLowerK := armPropensity_lower_of_overlap P hOverlap k a (hpPos k hk)
    have heLowerL := armPropensity_lower_of_overlap P hOverlap l a (hpPos l hlH)
    have heMulK : epsilon * cellMass P k ≤
        cellMass P k * armPropensity P k a := by
      simpa [mul_comm] using
        mul_le_mul_of_nonneg_left heLowerK (cellMass_mem_unitInterval P k).1
    have heMulL : epsilon * cellMass P l ≤
        cellMass P l * armPropensity P l a := by
      simpa [mul_comm] using
        mul_le_mul_of_nonneg_left heLowerL (cellMass_mem_unitInterval P l).1
    have hpq : cellMass P k + cellMass P l ≤ 1 := by
      have hdisj := categorySet_disjoint_of_ne k l hkl
      calc
        cellMass P k + cellMass P l =
            (obsLaw P).real (categorySet k ∪ categorySet l) := by
          rw [measureReal_union hdisj MeasurableSet.of_discrete,
            obsLaw_categorySet_mass,
            obsLaw_categorySet_mass]
        _ ≤ (obsLaw P).real Set.univ :=
          measureReal_mono (Set.subset_univ _)
        _ = 1 := measureReal_univ_eq_one
    have hsum : cellMass P k * armPropensity P k a +
        cellMass P l * armPropensity P l a ≤ 1 := by
      have hkprod : cellMass P k * armPropensity P k a ≤ cellMass P k :=
        mul_le_of_le_one_right (cellMass_mem_unitInterval P k).1 hrho.2
      have hlprod : cellMass P l * armPropensity P l a ≤ cellMass P l :=
        mul_le_of_le_one_right (cellMass_mem_unitInterval P l).1 hsigma.2
      linarith
    convert
      missing_cross_envelope m (cellMass P k) (cellMass P l)
        (armPropensity P k a) (armPropensity P l a) epsilon
        (cellMass_mem_unitInterval P k).1 (cellMass_mem_unitInterval P l).1
        hrho.1 hsigma.1 hrho.2 hsigma.2 hepsilon.le heMulK heMulL hsum using 1 <;>
      dsimp [m, u, f] <;> ring
  have hmassSum : ∑ k ∈ H, cellMass P k ≤ 1 := by
    calc
      ∑ k ∈ H, cellMass P k ≤ ∑ k : Fin d, cellMass P k := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        intro k _hk _hnot
        exact (cellMass_mem_unitInterval P k).1
      _ = 1 := by
        have htotal : ∑ z : Obs d, (P.pmf z).toReal = 1 := by
          simpa using
            (PMF.integral_eq_sum P.pmf (fun _ : Obs d => (1 : ℝ))).symm
        calc
          ∑ k : Fin d, cellMass P k = ∑ z : Obs d, (P.pmf z).toReal := by
            simp [cellMass, jointMass, Fintype.sum_prod_type]
          _ = 1 := htotal
  have hfSum : ∑ k ∈ H, f k ≤ H.card / (u ^ 2 * B) := by
    exact sum_mass_mul_exp_neg_mul_le H (fun k => cellMass P k) u B hu hB hp
  have hsquare : (∑ k ∈ H, f k) ^ 2 =
      ∑ k ∈ H, (f k) ^ 2 +
        ∑ k ∈ H, ∑ l ∈ H.erase k, f k * f l := by
    rw [sq, Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mul_sum, ← Finset.sum_erase_add _ _ hk, add_comm]
    rw [pow_two]
  rw [integral_fixedMissingCount_sq_eq P H a hpPos]
  calc
    _ ≤ ∑ k ∈ H, ((m : ℝ) * cellMass P k + (m : ℝ) ^ 2 * (f k) ^ 2) +
          ∑ k ∈ H, ∑ l ∈ H.erase k, (m : ℝ) ^ 2 * f k * f l := by
      apply add_le_add
      · exact Finset.sum_le_sum fun k hk => hdiag k hk
      · exact Finset.sum_le_sum fun k hk =>
          Finset.sum_le_sum fun l hl => hcross k hk l hl
    _ = (m : ℝ) * (∑ k ∈ H, cellMass P k) +
          (m : ℝ) ^ 2 * (∑ k ∈ H, f k) ^ 2 := by
      have hmassFactor : ∑ k ∈ H, (m : ℝ) * cellMass P k =
          (m : ℝ) * (∑ k ∈ H, cellMass P k) := by
        rw [Finset.mul_sum]
      have hdiagFactor : ∑ k ∈ H, (m : ℝ) ^ 2 * (f k) ^ 2 =
          (m : ℝ) ^ 2 * (∑ k ∈ H, (f k) ^ 2) := by
        rw [Finset.mul_sum]
      have hcrossFactor : ∑ k ∈ H, ∑ l ∈ H.erase k, (m : ℝ) ^ 2 * f k * f l =
          (m : ℝ) ^ 2 * (∑ k ∈ H, ∑ l ∈ H.erase k, f k * f l) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l hl
        ring
      rw [Finset.sum_add_distrib, hmassFactor, hdiagFactor, hcrossFactor,
        hsquare]
      ring
    _ ≤ (m : ℝ) + (m : ℝ) ^ 2 * (H.card / (u ^ 2 * B)) ^ 2 := by
      have hm0 : (0 : ℝ) ≤ m := by positivity
      have hf0 : 0 ≤ ∑ k ∈ H, f k := by
        apply Finset.sum_nonneg
        intro k hk
        dsimp [f]
        exact mul_nonneg (cellMass_mem_unitInterval P k).1 (Real.exp_pos _).le
      have hfirst := mul_le_mul_of_nonneg_left hmassSum hm0
      have hsquares : (∑ k ∈ H, f k) ^ 2 ≤
          (H.card / (u ^ 2 * B)) ^ 2 :=
        pow_le_pow_left₀ hf0 hfSum 2
      have hsecond := mul_le_mul_of_nonneg_left hsquares (sq_nonneg (m : ℝ))
      exact add_le_add (by simpa using hfirst) hsecond
    _ = (Fintype.card J : ℝ) + (Fintype.card J : ℝ) ^ 2 *
        (H.card /
          (((((Fintype.card J - 2 : ℕ) : ℝ) / 2 * epsilon) ^ 2) * B)) ^ 2 := by
      rfl

end CausalSmith.Stat.DiscreteAteMinimaxLoggap

/-- The aggregate centered ratio residual is unchanged when the distribution, observations,
selected categories, and treatment arm are replaced by equal values. -/
add_decl_doc CausalSmith.Stat.DiscreteAteMinimaxLoggap.fixedRatioResidual.congr_simp

/-- The count of category observations with a completely missing nested arm is unchanged when
the observations and the category and arm sets are replaced by equal values. -/
add_decl_doc CausalSmith.Stat.DiscreteAteMinimaxLoggap.missingIndexCount.congr_simp

/-- The event that two sets of sample indices equal specified category and nested-category index
sets is unchanged when all its sets and index targets are replaced by equal values. -/
add_decl_doc CausalSmith.Stat.DiscreteAteMinimaxLoggap.nestedIndexEvent.congr_simp

/-- A category's ratio coefficient is unchanged when the sample, category, and treatment arm are
replaced by equal values. -/
add_decl_doc CausalSmith.Stat.DiscreteAteMinimaxLoggap.tupleRatioCoeff.congr_simp
