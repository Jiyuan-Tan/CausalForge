namespace Causalean.Mathlib.Probability

open scoped BigOperators

/-- The real binomial weight of count `j` among `m` trials with success
parameter `p`. -/
def binomialWeight (m : Nat) (p : Real) (j : Nat) : Real :=
  (Nat.choose m j : Real) * p ^ j * (1 - p) ^ (m - j)

/-- [The reciprocal of a positive integer, totalized to zero at the
origin, is at most twice the reciprocal of its successor](goal). -/
lemma totalized_inverse_count_le (j : Nat) :
    (if 0 < j then (j : Real)⁻¹ else 0) ≤ 2 * ((j : Real) + 1)⁻¹ := by
  by_cases hj : 0 < j
  · rw [if_pos hj, ← div_eq_mul_inv]
    have hjR : (0 : Real) < j := by
      exact_mod_cast hj
    have hj1R : (0 : Real) < (j : Real) + 1 := by positivity
    apply (le_div_iff₀ hj1R).2
    calc
      (j : Real)⁻¹ * ((j : Real) + 1) = 1 + (j : Real)⁻¹ := by
        field_simp
      _ ≤ 2 := by
        have hinv : (j : Real)⁻¹ ≤ 1 :=
          (inv_le_one₀ hjR).2 (by exact_mod_cast hj)
        linarith
  · simp [hj]
    positivity

/-- When [the success probability is positive and at most one](hyp:hp,hp1),
[the binomial expectation of the zero-safe inverse success count is at most
twice the reciprocal of the trial count plus one times that probability](goal). -/
lemma binomial_totalized_inverse_count_le (m : Nat) (p : Real)
    (hp : 0 < p) (hp1 : p ≤ 1) :
    (∑ j ∈ Finset.range (m + 1), binomialWeight m p j *
      (if 0 < j then (j : Real)⁻¹ else 0)) ≤
      2 / (((m + 1 : Nat) : Real) * p) := by
  -- Proof route: compare `1/j` with `2/(j+1)`, shift `choose m j`,
  -- and evaluate the resulting binomial row by `add_pow`.
  let d : Real := ((m + 1 : Nat) : Real) * p
  let S : Real := ∑ j ∈ Finset.range (m + 1),
    binomialWeight m p j * ((j : Real) + 1)⁻¹
  have hq : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  have hd : 0 < d := by
    dsimp [d]
    positivity
  have hterm (j : Nat) (hj : j ∈ Finset.range (m + 1)) :
      d * (binomialWeight m p j * ((j : Real) + 1)⁻¹) =
        (Nat.choose (m + 1) (j + 1) : Real) * p ^ (j + 1) *
          (1 - p) ^ ((m + 1) - (j + 1)) := by
    have hjlt : j < m + 1 := Finset.mem_range.mp hj
    have hsub : (m + 1) - (j + 1) = m - j := by omega
    have hc : (((m + 1 : Nat) : Real) * (Nat.choose m j : Real)) =
        (Nat.choose (m + 1) (j + 1) : Real) * ((j + 1 : Nat) : Real) := by
      exact_mod_cast Nat.add_one_mul_choose_eq m j
    dsimp [d]
    rw [binomialWeight, hsub, pow_succ]
    field_simp
    calc
      ((m + 1 : Nat) : Real) * (Nat.choose m j : Real) * (1 - p) ^ (m - j) =
          ((((m + 1 : Nat) : Real) * (Nat.choose m j : Real)) *
            (1 - p) ^ (m - j)) := by ring
      _ = (((Nat.choose (m + 1) (j + 1) : Real) * ((j + 1 : Nat) : Real)) *
            (1 - p) ^ (m - j)) := by rw [hc]
      _ = (1 - p) ^ (m - j) * ((j : Real) + 1) *
            (Nat.choose (m + 1) (j + 1) : Real) := by push_cast; ring
  have hid : d * S = 1 - (1 - p) ^ (m + 1) := by
    dsimp [S]
    rw [Finset.mul_sum]
    calc
      (∑ j ∈ Finset.range (m + 1),
          d * (binomialWeight m p j * ((j : Real) + 1)⁻¹)) =
          ∑ j ∈ Finset.range (m + 1),
            p ^ (j + 1) * (1 - p) ^ ((m + 1) - (j + 1)) *
              (Nat.choose (m + 1) (j + 1) : Real) := by
                apply Finset.sum_congr rfl
                intro j hj
                rw [hterm j hj]
                ring
      _ = (p + (1 - p)) ^ (m + 1) - (1 - p) ^ (m + 1) := by
        rw [add_pow]
        rw [Finset.sum_range_succ' (fun k =>
          p ^ k * (1 - p) ^ ((m + 1) - k) *
            (Nat.choose (m + 1) k : Real)) (m + 1)]
        simp
      _ = 1 - (1 - p) ^ (m + 1) := by ring
  have hS : S ≤ 1 / d := by
    apply (le_div_iff₀ hd).2
    rw [mul_comm S d, hid]
    have hpow := pow_nonneg hq (m + 1)
    linarith
  calc
    (∑ j ∈ Finset.range (m + 1), binomialWeight m p j *
        (if 0 < j then (j : Real)⁻¹ else 0)) ≤
        ∑ j ∈ Finset.range (m + 1), binomialWeight m p j *
          (2 * ((j : Real) + 1)⁻¹) := by
            apply Finset.sum_le_sum
            intro j hj
            apply mul_le_mul_of_nonneg_left (totalized_inverse_count_le j)
            dsimp [binomialWeight]
            positivity
    _ = 2 * S := by
      dsimp [S]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ ≤ 2 * (1 / d) := by nlinarith
    _ = 2 / (((m + 1 : Nat) : Real) * p) := by
      dsimp [d]
      ring

/-- If [the overlap margin is positive](hyp:hepsilon) and [the success
probability lies between that margin and one minus the margin](hyp:hlo,hhi),
[the binomial expectation of the two inverse arm counts on the interior event
is at most four divided by the trial count plus one times the margin](goal). -/
lemma binomial_inverse_two_arms_interior_le (m : Nat) (p epsilon : Real)
    (hepsilon : 0 < epsilon) (hlo : epsilon ≤ p)
    (hhi : p ≤ 1 - epsilon) :
    (∑ j ∈ Finset.range (m + 1), binomialWeight m p j *
      (if 0 < j ∧ j < m then
        (j : Real)⁻¹ + ((m - j : Nat) : Real)⁻¹
      else 0)) ≤
      4 / (((m + 1 : Nat) : Real) * epsilon) := by
  -- Apply the preceding estimate to successes with parameter `p` and to
  -- failures with parameter `1-p`; deleting the two endpoints only lowers
  -- the nonnegative sums.  Then use both overlap inequalities.
  have hp : 0 < p := lt_of_lt_of_le hepsilon hlo
  have hp1 : p ≤ 1 := by linarith
  have hq : 0 < 1 - p := by linarith
  have hq1 : 1 - p ≤ 1 := by linarith
  have hinter (j : Nat) :
      (if 0 < j ∧ j < m then
          (j : Real)⁻¹ + ((m - j : Nat) : Real)⁻¹
        else 0) ≤
        (if 0 < j then (j : Real)⁻¹ else 0) +
          (if 0 < m - j then ((m - j : Nat) : Real)⁻¹ else 0) := by
    by_cases hj : 0 < j ∧ j < m
    · have hmj : 0 < m - j := Nat.sub_pos_of_lt hj.2
      simp [hj, hmj]
    · rw [if_neg hj]
      positivity
  have hfail :
      (∑ j ∈ Finset.range (m + 1), binomialWeight m p j *
        (if 0 < m - j then ((m - j : Nat) : Real)⁻¹ else 0)) =
      ∑ j ∈ Finset.range (m + 1), binomialWeight m (1 - p) j *
        (if 0 < j then (j : Real)⁻¹ else 0) := by
    rw [← Finset.sum_range_reflect (fun j => binomialWeight m p j *
      (if 0 < m - j then ((m - j : Nat) : Real)⁻¹ else 0)) (m + 1)]
    apply Finset.sum_congr rfl
    intro j hj
    have hjlt : j < m + 1 := Finset.mem_range.mp hj
    have hjle : j ≤ m := by omega
    have hreflect : m + 1 - 1 - j = m - j := by omega
    have hcancel : m - (m - j) = j := by omega
    rw [hreflect, binomialWeight, binomialWeight, hcancel, Nat.choose_symm hjle]
    congr 1
    ring
  have hsuccess := binomial_totalized_inverse_count_le m p hp hp1
  have hfailure := binomial_totalized_inverse_count_le m (1 - p) hq hq1
  have hn : (0 : Real) < ((m + 1 : Nat) : Real) := by positivity
  have hnepsilon :
      ((m + 1 : Nat) : Real) * epsilon ≤ ((m + 1 : Nat) : Real) * p :=
    mul_le_mul_of_nonneg_left hlo hn.le
  have hnqepsilon :
      ((m + 1 : Nat) : Real) * epsilon ≤
        ((m + 1 : Nat) : Real) * (1 - p) := by
    apply mul_le_mul_of_nonneg_left _ hn.le
    linarith
  have hinvp :
      1 / (((m + 1 : Nat) : Real) * p) ≤
        1 / (((m + 1 : Nat) : Real) * epsilon) :=
    one_div_le_one_div_of_le (mul_pos hn hepsilon) hnepsilon
  have hinvq :
      1 / (((m + 1 : Nat) : Real) * (1 - p)) ≤
        1 / (((m + 1 : Nat) : Real) * epsilon) :=
    one_div_le_one_div_of_le (mul_pos hn hepsilon) hnqepsilon
  calc
    (∑ j ∈ Finset.range (m + 1), binomialWeight m p j *
      (if 0 < j ∧ j < m then
        (j : Real)⁻¹ + ((m - j : Nat) : Real)⁻¹
      else 0)) ≤
      ∑ j ∈ Finset.range (m + 1), binomialWeight m p j *
        ((if 0 < j then (j : Real)⁻¹ else 0) +
          (if 0 < m - j then ((m - j : Nat) : Real)⁻¹ else 0)) := by
            apply Finset.sum_le_sum
            intro j hj
            apply mul_le_mul_of_nonneg_left (hinter j)
            dsimp [binomialWeight]
            positivity
    _ = (∑ j ∈ Finset.range (m + 1), binomialWeight m p j *
          (if 0 < j then (j : Real)⁻¹ else 0)) +
        ∑ j ∈ Finset.range (m + 1), binomialWeight m p j *
          (if 0 < m - j then ((m - j : Nat) : Real)⁻¹ else 0) := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro j hj
            ring
    _ ≤ 2 / (((m + 1 : Nat) : Real) * p) +
        2 / (((m + 1 : Nat) : Real) * (1 - p)) := by
          rw [hfail]
          linarith
    _ ≤ 4 / (((m + 1 : Nat) : Real) * epsilon) := by
      rw [show 2 / (((m + 1 : Nat) : Real) * p) =
          2 * (1 / (((m + 1 : Nat) : Real) * p)) by ring,
        show 2 / (((m + 1 : Nat) : Real) * (1 - p)) =
          2 * (1 / (((m + 1 : Nat) : Real) * (1 - p))) by ring,
        show 4 / (((m + 1 : Nat) : Real) * epsilon) =
          4 * (1 / (((m + 1 : Nat) : Real) * epsilon)) by ring]
      linarith

end Causalean.Mathlib.Probability
