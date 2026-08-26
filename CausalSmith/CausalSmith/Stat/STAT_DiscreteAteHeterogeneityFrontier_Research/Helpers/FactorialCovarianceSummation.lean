/- Binomial summation of the positive partial-matching normalizations. -/

import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.FactorialCovarianceMoments

namespace CausalSmith.Stat.DiscreteAteHeterogeneityFrontier

open scoped BigOperators

-- @node: matchingNormalization_sum_le_asymmetric
/-- If [the first order satisfies its stated bound](hyp:hu) and [the second order satisfies its
  stated bound](hyp:hv) and [the stated condition on the source size or matching order
  holds](hyp:hm), [the size-`h` normalization sum retains one binomial coefficient instead of
  replacing both by powers. This is the form that sums to a shifted intensity](goal). -/
lemma matchingNormalization_sum_le_asymmetric {m u v R h : ℕ}
    (hu : u ≤ R) (hv : v ≤ R) (hm : 4 * R ^ 2 ≤ m) :
    ∑ N ∈ Causalean.Stat.partialMatchingsOfSize u v h,
        Causalean.Stat.matchingNormalization m N ≤
      (Nat.choose u h : ℝ) * (v : ℝ) ^ h *
        (Real.exp 1 / (m : ℝ) ^ h) := by
  classical
  have hnorm : ∀ N ∈ Causalean.Stat.partialMatchingsOfSize u v h,
      Causalean.Stat.matchingNormalization m N ≤
        Real.exp 1 / (m : ℝ) ^ h := by
    intro N hN
    exact Causalean.Stat.matchingNormalization_le hu hv hm hN
  have hcard :
      ((Causalean.Stat.partialMatchingsOfSize u v h).card : ℝ) ≤
        (Nat.choose u h : ℝ) * (v : ℝ) ^ h := by
    rw [Causalean.Stat.card_partialMatchingsOfSize]
    push_cast
    have hhfac : (0 : ℝ) < h.factorial := by positivity
    have hvchoose : (Nat.choose v h : ℝ) ≤
        (v : ℝ) ^ h / h.factorial := Nat.choose_le_pow_div h v
    have hnonneg : (0 : ℝ) ≤ Nat.choose u h := by positivity
    calc
      (Nat.choose u h : ℝ) * Nat.choose v h * h.factorial ≤
          (Nat.choose u h : ℝ) *
              ((v : ℝ) ^ h / h.factorial) * h.factorial := by
        gcongr
      _ = (Nat.choose u h : ℝ) * (v : ℝ) ^ h := by
        field_simp
  calc
    ∑ N ∈ Causalean.Stat.partialMatchingsOfSize u v h,
        Causalean.Stat.matchingNormalization m N ≤
        ∑ _N ∈ Causalean.Stat.partialMatchingsOfSize u v h,
          (Real.exp 1 / (m : ℝ) ^ h) := by
      exact Finset.sum_le_sum fun N hN => hnorm N hN
    _ = ((Causalean.Stat.partialMatchingsOfSize u v h).card : ℝ) *
          (Real.exp 1 / (m : ℝ) ^ h) := by simp [mul_comm]
    _ ≤ ((Nat.choose u h : ℝ) * (v : ℝ) ^ h) *
          (Real.exp 1 / (m : ℝ) ^ h) := by
      gcongr
    _ = (Nat.choose u h : ℝ) * (v : ℝ) ^ h *
          (Real.exp 1 / (m : ℝ) ^ h) := rfl

-- @node: positiveMatchingNormalization_weighted_sum_le
/-- If [the first order satisfies its stated bound](hyp:hu) and [the second order satisfies its
  stated bound](hyp:hv) and [the stated condition on the source size or matching order
  holds](hyp:hm) and [the probability lies in the stated range](hyp:hp), [after weighting a
  size-`h` overlap by the remaining cell-mass power, all positive overlap sizes are bounded by the
  binomially shifted intensity `p + v / m`](goal). -/
lemma positiveMatchingNormalization_weighted_sum_le
    {m u v R : ℕ} (hu : u ≤ R) (hv : v ≤ R)
    (hm : 4 * R ^ 2 ≤ m) {p : ℝ} (hp : 0 ≤ p) :
    ∑ h ∈ (Finset.range (min u v + 1)).filter (fun h => 0 < h),
        (∑ N ∈ Causalean.Stat.partialMatchingsOfSize u v h,
          Causalean.Stat.matchingNormalization m N) * p ^ (u + v - h) ≤
      Real.exp 1 * p ^ v * (p + (v : ℝ) / m) ^ u := by
  classical
  by_cases hR : R = 0
  · subst R
    have hu0 : u = 0 := Nat.eq_zero_of_le_zero hu
    have hv0 : v = 0 := Nat.eq_zero_of_le_zero hv
    subst u
    subst v
    have hempty : (Finset.range (min 0 0 + 1)).filter (fun h => 0 < h) = ∅ := by
      ext h
      simp
    rw [hempty]
    simp
    positivity
  have hmpos : (0 : ℝ) < m := by
    have hRpos : 0 < R := Nat.pos_of_ne_zero hR
    exact_mod_cast (lt_of_lt_of_le (by positivity : 0 < 4 * R ^ 2) hm)
  calc
    ∑ h ∈ (Finset.range (min u v + 1)).filter (fun h => 0 < h),
        (∑ N ∈ Causalean.Stat.partialMatchingsOfSize u v h,
          Causalean.Stat.matchingNormalization m N) * p ^ (u + v - h) ≤
      ∑ h ∈ (Finset.range (min u v + 1)).filter (fun h => 0 < h),
        ((Nat.choose u h : ℝ) * (v : ℝ) ^ h *
          (Real.exp 1 / (m : ℝ) ^ h)) * p ^ (u + v - h) := by
      apply Finset.sum_le_sum
      intro h hh
      exact mul_le_mul_of_nonneg_right
        (matchingNormalization_sum_le_asymmetric hu hv hm)
        (pow_nonneg hp _)
    _ = ∑ h ∈ (Finset.range (min u v + 1)).filter (fun h => 0 < h),
        Real.exp 1 * p ^ v *
          ((Nat.choose u h : ℝ) * p ^ (u - h) *
            ((v : ℝ) / m) ^ h) := by
      apply Finset.sum_congr rfl
      intro h hh
      simp only [Finset.mem_filter, Finset.mem_range] at hh
      have hhmin : h ≤ min u v := by omega
      have hhv : h ≤ v := hhmin.trans (min_le_right _ _)
      rw [show u + v - h = (u - h) + v by omega, pow_add]
      rw [div_pow]
      field_simp
    _ ≤ ∑ h ∈ Finset.range (u + 1),
        Real.exp 1 * p ^ v *
          ((Nat.choose u h : ℝ) * p ^ (u - h) *
            ((v : ℝ) / m) ^ h) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro h hh
        simp only [Finset.mem_filter, Finset.mem_range] at hh
        have hhmin : h ≤ min u v := by omega
        exact Finset.mem_range.mpr
          (Nat.lt_succ_of_le (hhmin.trans (min_le_left _ _)))
      · intro h hh _
        positivity
    _ = Real.exp 1 * p ^ v * (p + (v : ℝ) / m) ^ u := by
      rw [← Finset.mul_sum]
      congr 1
      rw [add_comm p]
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (add_pow ((v : ℝ) / m) p u).symm

end CausalSmith.Stat.DiscreteAteHeterogeneityFrontier
