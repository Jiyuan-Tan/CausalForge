import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.OneArmQuantitativePredictive

/-!
# Logarithmic degree calibration for the one-arm converse

This file records the elementary ceiling and Taylor-budget estimates used by
the shifted finite-grid construction.
-/

namespace CausalSmith.Stat.DiscreteAteMinimaxLoggap

/-- The deliberately loose logarithmic moment-matching degree. -/
noncomputable def oneArmLogDegree (n : ℕ) : ℕ :=
  Nat.ceil (8 * Real.log n / Real.log 2)

/-- The chosen degree is at least the real number it rounds up, namely
8·log n / log 2 (base-2 logarithm scaled by 8), whenever the sample size is at
least 2.  This is the lower half of the ceiling sandwich used to convert degree
budgets into logarithmic rates. -/
lemma oneArmLogDegree_lower {n : ℕ} (hn : 2 ≤ n) :
    8 * Real.log n / Real.log 2 ≤ (oneArmLogDegree n : ℝ) := by
  exact Nat.le_ceil _

/-- The chosen degree is strictly less than 8·log n / log 2 plus one, for sample
size at least 2.  This is the upper half of the ceiling sandwich, so the degree
never exceeds its target by more than a single unit. -/
lemma oneArmLogDegree_upper {n : ℕ} (hn : 2 ≤ n) :
    (oneArmLogDegree n : ℝ) < 8 * Real.log n / Real.log 2 + 1 := by
  apply Nat.ceil_lt_add_one
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (le_trans (by omega : 1 ≤ 2) hn)
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg hn1
  positivity

/-- The chosen degree is strictly positive once the sample size is at least 2,
so the moment-matching construction always has at least one moment to match. -/
lemma oneArmLogDegree_pos {n : ℕ} (hn : 2 ≤ n) :
    0 < oneArmLogDegree n := by
  apply Nat.ceil_pos.mpr
  have hlogn : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
  positivity

/-- A coarse upper comparison sufficient to replace the selected degree by
the target logarithm in the final rate calculation. -/
lemma oneArmLogDegree_le_twenty_log {n : ℕ} (hn : 3 ≤ n) :
    (oneArmLogDegree n : ℝ) ≤ 20 * Real.log n := by
  have hn2 : 2 ≤ n := hn.trans' (by omega)
  have hupper := oneArmLogDegree_upper hn2
  have hlogn : 1 < Real.log (n : ℝ) := by
    have hlog3 : 1 < Real.log (3 : ℝ) := by
      nlinarith [Real.log_three_gt_d9]
    exact hlog3.trans_le (Real.log_le_log (by norm_num) (by exact_mod_cast hn))
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2large : (1 / 2 : ℝ) < Real.log 2 := by
    nlinarith [Real.log_two_gt_d9]
  have hquot : 8 * Real.log n / Real.log 2 ≤ 16 * Real.log n := by
    rw [div_le_iff₀ hlog2]
    nlinarith
  linarith

/-- With Poisson mean `2n`, scale `D/(64n)`, and predictive parameter `n²`,
the Taylor-tail logarithmic budget holds uniformly for every grid point in
`[0,1]`. -/
lemma oneArmLogDegree_taylor_budget {n : ℕ} (hn : 2 ≤ n)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    4 * ((2 * (n : ℝ)) *
          (((oneArmLogDegree n : ℝ) / (64 * (n : ℝ))) * x)) +
        2 * Real.log ((n : ℝ) ^ 2) ≤
      (((oneArmLogDegree n + 1 : ℕ) : ℝ) * Real.log 2) := by
  let D : ℝ := oneArmLogDegree n
  have hn0 : (0 : ℝ) < n := by positivity
  have hlogn : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hD0 : 0 ≤ D := by positivity
  have hDlower : 8 * Real.log n ≤ D * Real.log 2 := by
    have h := oneArmLogDegree_lower hn
    rw [div_le_iff₀ hlog2] at h
    simpa [D] using h
  have hxterm :
      4 * ((2 * (n : ℝ)) * ((D / (64 * (n : ℝ))) * x)) ≤ D / 8 := by
    have hident :
        4 * ((2 * (n : ℝ)) * ((D / (64 * (n : ℝ))) * x)) = D * x / 8 := by
      field_simp [ne_of_gt hn0]
      <;> ring
    rw [hident]
    exact div_le_div_of_nonneg_right
      (mul_le_of_le_one_right hD0 hx.2) (by norm_num)
  have hlog2sq : Real.log ((n : ℝ) ^ 2) = 2 * Real.log n := by
    rw [Real.log_pow]
    norm_num
  rw [hlog2sq]
  have hlog2large : (1 / 2 : ℝ) < Real.log 2 := by
    nlinarith [Real.log_two_gt_d9]
  have hcast : (((oneArmLogDegree n + 1 : ℕ) : ℝ)) = D + 1 := by
    simp [D]
  rw [hcast]
  have hD8 : D / 8 ≤ D * Real.log 2 / 2 := by
    nlinarith
  have hfourlog : 4 * Real.log n ≤ D * Real.log 2 / 2 := by
    linarith
  nlinarith

/-- Equivalent calibration with raw sample scale `4n`.  Halving the active
mass scale leaves every Poisson rate, and hence the Taylor budget, unchanged;
the larger total mean supplies uniform de-Poissonization slack. -/
lemma oneArmLogDegree_taylor_budget_four_n {n : ℕ} (hn : 2 ≤ n)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    4 * ((4 * (n : ℝ)) *
          (((oneArmLogDegree n : ℝ) / (128 * (n : ℝ))) * x)) +
        2 * Real.log ((n : ℝ) ^ 2) ≤
      (((oneArmLogDegree n + 1 : ℕ) : ℝ) * Real.log 2) := by
  have h := oneArmLogDegree_taylor_budget hn hx
  convert h using 1 <;> ring

end CausalSmith.Stat.DiscreteAteMinimaxLoggap
