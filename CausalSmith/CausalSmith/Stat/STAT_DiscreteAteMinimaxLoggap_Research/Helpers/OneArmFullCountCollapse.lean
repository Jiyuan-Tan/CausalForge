import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.OneArmPoissonPredictive

namespace CausalSmith.Stat.DiscreteAteMinimaxLoggap

open scoped BigOperators

/-!
# Full count-space collapse for one-arm Poisson mixtures

This file combines the finite low-count Taylor bound with the high-count
complement and collapses both pieces to one exponential-series tail.
-/

/-- Triple count vectors whose total count is at most `D`. -/
noncomputable def tripleCountLow (D : ℕ) : Finset (Fin 3 → ℕ) :=
  (Fintype.piFinset fun _ : Fin 3 => Finset.range (D + 1)).filter
    (fun c => c 0 + c 1 + c 2 ≤ D)

lemma mem_tripleCountLow_iff {D : ℕ} {c : Fin 3 → ℕ} :
    c ∈ tripleCountLow D ↔ c 0 + c 1 + c 2 ≤ D := by
  simp only [tripleCountLow, Finset.mem_filter, Fintype.mem_piFinset,
    Finset.mem_range, and_iff_right_iff_imp]
  intro h q
  fin_cases q <;> simp_all <;> omega

private def tripleCountIndex (D : ℕ) :=
  ((Finset.range (D + 1)).sigma fun k => Finset.range (k + 1)).sigma
    fun ki => Finset.range (ki.1 - ki.2 + 1)

private lemma sum_tripleCountLow_eq
    (D : ℕ) (f : (Fin 3 → ℕ) → ℝ) :
    ∑ c ∈ tripleCountLow D, f c =
      ∑ k ∈ Finset.range (D + 1),
        ∑ i ∈ Finset.range (k + 1),
          ∑ j ∈ Finset.range (k - i + 1), f ![i, j, k - i - j] := by
  classical
  have hrhs :
      (∑ k ∈ Finset.range (D + 1),
        ∑ i ∈ Finset.range (k + 1),
          ∑ j ∈ Finset.range (k - i + 1), f ![i, j, k - i - j]) =
        ∑ z ∈ tripleCountIndex D,
          f ![z.1.2, z.2, z.1.1 - z.1.2 - z.2] := by
    unfold tripleCountIndex
    rw [Finset.sum_sigma', Finset.sum_sigma']
  rw [hrhs]
  refine Finset.sum_bij'
    (fun c _ => ⟨⟨c 0 + c 1 + c 2, c 0⟩, c 1⟩)
    (fun z _ => ![z.1.2, z.2, z.1.1 - z.1.2 - z.2]) ?_ ?_ ?_ ?_ ?_
  · intro c hc
    simp only [tripleCountIndex, Finset.mem_sigma, Finset.mem_range]
    rw [mem_tripleCountLow_iff] at hc
    have hc1 : c 1 ≤ c 0 + c 1 + c 2 - c 0 :=
      Nat.le_sub_of_add_le (by omega)
    exact ⟨⟨by omega, by omega⟩, by omega⟩
  · rintro ⟨⟨k, i⟩, j⟩ hz
    simp only [tripleCountIndex, Finset.mem_sigma, Finset.mem_range] at hz
    rw [mem_tripleCountLow_iff]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_succ, Function.comp_apply]
    omega
  · intro c hc
    ext q
    fin_cases q <;> simp <;> omega
  · rintro ⟨⟨k, i⟩, j⟩ hz
    simp only [tripleCountIndex, Finset.mem_sigma, Finset.mem_range] at hz
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_succ, Function.comp_apply]
    ext <;> simp <;> omega
  · intro c hc
    congr 1
    ext q
    fin_cases q <;> simp <;> omega

/-- The low-count coefficient sum is the initial segment of the scalar
exponential series at the total Poisson mean. -/
lemma sum_tripleCountLow_coefficient_eq
    (sampleScale p pi mu : ℝ) (D : ℕ) :
    ∑ c ∈ tripleCountLow D,
        triplePoissonCoefficient sampleScale p pi mu c =
      ∑ k ∈ Finset.range (D + 1), expSeriesCoeff (sampleScale * p) k := by
  rw [sum_tripleCountLow_eq]
  apply Finset.sum_congr rfl
  intro k _
  exact triplePoissonTotalCoefficient_eq sampleScale p pi mu k

/-- The low-count Taylor remainders have exactly the finite part occurring in
the triple-count collapse. -/
lemma sum_tripleCountLow_coefficient_mul_tail_eq
    (sampleScale p pi mu : ℝ) (D : ℕ) :
    ∑ c ∈ tripleCountLow D,
        triplePoissonCoefficient sampleScale p pi mu c *
          expSeriesTail (sampleScale * p)
            (D + 1 - (c 0 + c 1 + c 2)) =
      ∑ k ∈ Finset.range (D + 1),
        triplePoissonTotalCoefficient sampleScale p pi mu k *
          expSeriesTail (sampleScale * p) (D + 1 - k) := by
  rw [sum_tripleCountLow_eq]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_succ, Function.comp_apply]
  have hkD : k ≤ D := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have htail : ∀ i ∈ Finset.range (k + 1), ∀ j ∈ Finset.range (k - i + 1),
      expSeriesTail (sampleScale * p)
          (D + 1 - (i + j + (k - i - j))) =
        expSeriesTail (sampleScale * p) (D + 1 - k) := by
    intro i hi j hj
    have hik : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have hjik : j ≤ k - i := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    congr 2 <;> omega
  unfold triplePoissonTotalCoefficient
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [htail i hi j hj]

/-- A valid mixed triple-Poisson mass is nonnegative pointwise. -/
lemma mixedTriplePoissonMass_nonneg
    {ι : Type*} [Fintype ι] (ω : PMF ι) {sampleScale : ℝ}
    (p pi mu : ι → ℝ) (hs : 0 ≤ sampleScale) (hp : ∀ r, 0 ≤ p r)
    (hpi : ∀ r, pi r ∈ Set.Icc (0 : ℝ) 1)
    (hmu : ∀ r, mu r ∈ Set.Icc (0 : ℝ) 1) (c : Fin 3 → ℕ) :
    0 ≤ mixedTriplePoissonMass ω sampleScale p pi mu c := by
  unfold mixedTriplePoissonMass triplePoissonMass
  exact Finset.sum_nonneg fun r _ => mul_nonneg ENNReal.toReal_nonneg
    (mul_nonneg (Real.exp_pos _).le
      (triplePoissonCoefficient_nonneg hs (hp r) (hpi r) (hmu r) c))

/-- The low-count part of one prior's Taylor bound is its prior average of
the finite triple-count remainder. -/
lemma sum_tripleCountLow_mixed_tail_eq
    {ι : Type*} [Fintype ι] (ω : PMF ι) (sampleScale : ℝ)
    (p pi mu : ι → ℝ) (D : ℕ) :
    ∑ c ∈ tripleCountLow D, ∑ r, (ω r).toReal *
        (triplePoissonCoefficient sampleScale (p r) (pi r) (mu r) c *
          expSeriesTail (sampleScale * p r)
            (D + 1 - (c 0 + c 1 + c 2))) =
      ∑ r, (ω r).toReal *
        (∑ k ∈ Finset.range (D + 1),
          triplePoissonTotalCoefficient sampleScale (p r) (pi r) (mu r) k *
            expSeriesTail (sampleScale * p r) (D + 1 - k)) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  rw [← Finset.mul_sum]
  exact congrArg (fun z => (ω r).toReal * z)
    (sum_tripleCountLow_coefficient_mul_tail_eq
      sampleScale (p r) (pi r) (mu r) D)

/-- Under unit total mass, the high-count complement is bounded by the high
piece used in `tripleCountTaylorRemainder`. -/
lemma tsum_mixedTriplePoissonMass_compl_le
    {ι : Type*} [Fintype ι] (ω : PMF ι) {sampleScale : ℝ}
    (p pi mu : ι → ℝ) (hs : 0 ≤ sampleScale) (hp : ∀ r, 0 ≤ p r)
    (hpi : ∀ r, pi r ∈ Set.Icc (0 : ℝ) 1)
    (hmu : ∀ r, mu r ∈ Set.Icc (0 : ℝ) 1) (D : ℕ)
    (hmass : Summable (mixedTriplePoissonMass ω sampleScale p pi mu))
    (htotal : ∑' c, mixedTriplePoissonMass ω sampleScale p pi mu c = 1) :
    ∑' c : {c // c ∉ tripleCountLow D},
        mixedTriplePoissonMass ω sampleScale p pi mu c ≤
      ∑ r, (ω r).toReal *
        (expSeriesTail (sampleScale * p r) (D + 1) *
          Real.exp (sampleScale * p r)) := by
  have hsplit := hmass.sum_add_tsum_compl (s := tripleCountLow D)
  rw [htotal] at hsplit
  change (∑ c ∈ tripleCountLow D,
      mixedTriplePoissonMass ω sampleScale p pi mu c) +
      (∑' c : {c // c ∉ tripleCountLow D},
        mixedTriplePoissonMass ω sampleScale p pi mu c) = 1 at hsplit
  have hlow :
      ∑ c ∈ tripleCountLow D,
          mixedTriplePoissonMass ω sampleScale p pi mu c =
        ∑ r, (ω r).toReal *
          (Real.exp (-(sampleScale * p r)) *
            ∑ k ∈ Finset.range (D + 1),
              expSeriesCoeff (sampleScale * p r) k) := by
    unfold mixedTriplePoissonMass triplePoissonMass
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    rw [← Finset.mul_sum, ← Finset.mul_sum,
      sum_tripleCountLow_coefficient_eq]
  rw [hlow] at hsplit
  have hweight : ∑ r, (ω r).toReal = 1 := by
    have h := congrArg ENNReal.toReal (ω.tsum_coe)
    rw [ENNReal.tsum_toReal_eq (fun r => ω.apply_ne_top r), tsum_fintype] at h
    simpa using h
  have hcompl :
      (∑' c : {c // c ∉ tripleCountLow D},
          mixedTriplePoissonMass ω sampleScale p pi mu c) =
        (∑ r, (ω r).toReal * 1) -
          ∑ r, (ω r).toReal *
            (Real.exp (-(sampleScale * p r)) *
              ∑ k ∈ Finset.range (D + 1),
                expSeriesCoeff (sampleScale * p r) k) := by
    calc
      _ = 1 - ∑ r, (ω r).toReal *
          (Real.exp (-(sampleScale * p r)) *
            ∑ k ∈ Finset.range (D + 1),
              expSeriesCoeff (sampleScale * p r) k) := by linarith [hsplit]
      _ = _ := by simp [hweight]
  rw [hcompl]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro r _
  have hx : 0 ≤ sampleScale * p r := mul_nonneg hs (hp r)
  have htail : 0 ≤ expSeriesTail (sampleScale * p r) (D + 1) := by
    unfold expSeriesTail
    exact tsum_nonneg fun t => div_nonneg (pow_nonneg hx _) (Nat.cast_nonneg _)
  rw [expSeriesTail_eq_exp_sub_sum] at htail ⊢
  have hexp : Real.exp (-(sampleScale * p r)) * Real.exp (sampleScale * p r) = 1 := by
    rw [← Real.exp_add]
    simp
  have he : Real.exp (-(sampleScale * p r)) ≤ Real.exp (sampleScale * p r) :=
    Real.exp_le_exp.mpr (by linarith)
  have hid :
      1 - Real.exp (-(sampleScale * p r)) *
          (∑ k ∈ Finset.range (D + 1), expSeriesCoeff (sampleScale * p r) k) =
        Real.exp (-(sampleScale * p r)) *
          (Real.exp (sampleScale * p r) -
            ∑ k ∈ Finset.range (D + 1), expSeriesCoeff (sampleScale * p r) k) := by
    nlinarith
  calc
    (ω r).toReal * 1 - (ω r).toReal *
        (Real.exp (-(sampleScale * p r)) *
          ∑ k ∈ Finset.range (D + 1), expSeriesCoeff (sampleScale * p r) k) =
        (ω r).toReal *
          (1 - Real.exp (-(sampleScale * p r)) *
            ∑ k ∈ Finset.range (D + 1), expSeriesCoeff (sampleScale * p r) k) := by ring
    _ = (ω r).toReal * (Real.exp (-(sampleScale * p r)) *
          (Real.exp (sampleScale * p r) -
            ∑ k ∈ Finset.range (D + 1), expSeriesCoeff (sampleScale * p r) k)) := by rw [hid]
    _ ≤ (ω r).toReal * (Real.exp (sampleScale * p r) *
          (Real.exp (sampleScale * p r) -
            ∑ k ∈ Finset.range (D + 1), expSeriesCoeff (sampleScale * p r) k)) := by
      gcongr
    _ = (ω r).toReal *
        ((Real.exp (sampleScale * p r) -
            ∑ k ∈ Finset.range (D + 1), expSeriesCoeff (sampleScale * p r) k) *
          Real.exp (sampleScale * p r)) := by ring

private lemma sum_prior_count_remainder_eq
    {ι : Type*} [Fintype ι] (ω : PMF ι) (sampleScale : ℝ)
    (p pi mu : ι → ℝ) (D : ℕ) :
    (∑ r, (ω r).toReal *
        (∑ k ∈ Finset.range (D + 1),
          triplePoissonTotalCoefficient sampleScale (p r) (pi r) (mu r) k *
            expSeriesTail (sampleScale * p r) (D + 1 - k))) +
      ∑ r, (ω r).toReal *
        (expSeriesTail (sampleScale * p r) (D + 1) * Real.exp (sampleScale * p r)) =
      ∑ r, (ω r).toReal *
        expSeriesTail (2 * (sampleScale * p r)) (D + 1) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  rw [← mul_add]
  apply congrArg (fun z => (ω r).toReal * z)
  simpa [tripleCountTaylorRemainder, triplePoissonTotalCoefficient] using
    tripleCountTaylorRemainder_eq_expSeriesTail_two_mul
      sampleScale (p r) (pi r) (mu r) D

/-- Unnormalized log-budget calibration for the full count-space collapse. -/
lemma expSeriesTail_two_mul_le_inv_sq_of_log_budget
    {x n : ℝ} (hx : 0 ≤ x) (hn : 0 < n) (L : ℕ)
    (hbudget : 4 * x + 2 * Real.log n ≤ (L : ℝ) * Real.log 2) :
    expSeriesTail (2 * x) L ≤ n⁻¹ ^ 2 := by
  have hbase := exp_neg_mul_expSeriesTail_le_exp_div_two_pow
    (2 * x) (mul_nonneg (by norm_num) hx) L
  have hscaled : Real.exp (2 * x) *
      (Real.exp (-(2 * x)) * expSeriesTail (2 * x) L) ≤
      Real.exp (2 * x) * (Real.exp (2 * x) / (2 : ℝ) ^ L) :=
    mul_le_mul_of_nonneg_left hbase (Real.exp_pos _).le
  have hleft : Real.exp (2 * x) *
      (Real.exp (-(2 * x)) * expSeriesTail (2 * x) L) =
      expSeriesTail (2 * x) L := by
    rw [← mul_assoc, ← Real.exp_add]
    simp
  rw [hleft] at hscaled
  refine hscaled.trans ?_
  have hright : Real.exp (2 * x) * (Real.exp (2 * x) / (2 : ℝ) ^ L) =
      Real.exp (4 * x) / (2 : ℝ) ^ L := by
    calc
      _ = (Real.exp (2 * x) * Real.exp (2 * x)) / (2 : ℝ) ^ L := by ring
      _ = Real.exp (2 * x + 2 * x) / (2 : ℝ) ^ L := by rw [Real.exp_add]
      _ = _ := by congr 2 <;> ring
  rw [hright, div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ L)]
  have hexp := Real.exp_le_exp.mpr hbudget
  rw [Real.exp_add, Real.exp_nat_mul,
    Real.exp_log (by norm_num : (0 : ℝ) < 2)] at hexp
  have hninv : 0 < n⁻¹ ^ 2 := sq_pos_of_pos (inv_pos.mpr hn)
  have hcancel : n⁻¹ ^ 2 * Real.exp (2 * Real.log n) = 1 := by
    rw [show 2 * Real.log n = Real.log n + Real.log n by ring,
      Real.exp_add, Real.exp_log hn]
    field_simp
  calc
    Real.exp (4 * x) = n⁻¹ ^ 2 *
        (Real.exp (4 * x) * Real.exp (2 * Real.log n)) := by
      symm
      calc
        _ = Real.exp (4 * x) *
            (n⁻¹ ^ 2 * Real.exp (2 * Real.log n)) := by ring
        _ = _ := by rw [hcancel, mul_one]
    _ ≤ n⁻¹ ^ 2 * (2 : ℝ) ^ L :=
      mul_le_mul_of_nonneg_left hexp hninv.le

/-- Full count-space `ℓ¹` collapse for two moment-matched one-arm
triple-Poisson mixtures. -/
lemma tsum_abs_mixedTriplePoissonMass_sub_le_tails_of_moments
    {ι₀ ι₁ : Type*} [Fintype ι₀] [Fintype ι₁]
    (ω₀ : PMF ι₀) (ω₁ : PMF ι₁) {sampleScale : ℝ}
    (p₀ pi₀ mu₀ : ι₀ → ℝ) (p₁ pi₁ mu₁ : ι₁ → ℝ)
    (hs : 0 ≤ sampleScale) (hp₀ : ∀ r, 0 ≤ p₀ r) (hp₁ : ∀ r, 0 ≤ p₁ r)
    (hpi₀ : ∀ r, pi₀ r ∈ Set.Icc (0 : ℝ) 1)
    (hpi₁ : ∀ r, pi₁ r ∈ Set.Icc (0 : ℝ) 1)
    (hmu₀ : ∀ r, mu₀ r ∈ Set.Icc (0 : ℝ) 1)
    (hmu₁ : ∀ r, mu₁ r ∈ Set.Icc (0 : ℝ) 1) (D : ℕ)
    (hmoment : ∀ i j k : ℕ, i + j + k ≤ D →
      ∑ r, (ω₀ r).toReal *
          (p₀ r ^ i * (p₀ r * pi₀ r) ^ j * (p₀ r * pi₀ r * mu₀ r) ^ k) =
        ∑ r, (ω₁ r).toReal *
          (p₁ r ^ i * (p₁ r * pi₁ r) ^ j * (p₁ r * pi₁ r * mu₁ r) ^ k))
    (hmass₀ : Summable (mixedTriplePoissonMass ω₀ sampleScale p₀ pi₀ mu₀))
    (hmass₁ : Summable (mixedTriplePoissonMass ω₁ sampleScale p₁ pi₁ mu₁))
    (htotal₀ : ∑' c, mixedTriplePoissonMass ω₀ sampleScale p₀ pi₀ mu₀ c = 1)
    (htotal₁ : ∑' c, mixedTriplePoissonMass ω₁ sampleScale p₁ pi₁ mu₁ c = 1) :
    ∑' c, |mixedTriplePoissonMass ω₀ sampleScale p₀ pi₀ mu₀ c -
        mixedTriplePoissonMass ω₁ sampleScale p₁ pi₁ mu₁ c| ≤
      (∑ r, (ω₀ r).toReal *
        expSeriesTail (2 * (sampleScale * p₀ r)) (D + 1)) +
      ∑ r, (ω₁ r).toReal *
        expSeriesTail (2 * (sampleScale * p₁ r)) (D + 1) := by
  let f₀ := mixedTriplePoissonMass ω₀ sampleScale p₀ pi₀ mu₀
  let f₁ := mixedTriplePoissonMass ω₁ sampleScale p₁ pi₁ mu₁
  have hsplit := tsum_abs_sub_le_sum_add_compl f₀ f₁ (tripleCountLow D)
    hmass₀ hmass₁
    (mixedTriplePoissonMass_nonneg ω₀ p₀ pi₀ mu₀ hs hp₀ hpi₀ hmu₀)
    (mixedTriplePoissonMass_nonneg ω₁ p₁ pi₁ mu₁ hs hp₁ hpi₁ hmu₁)
  have hdegree : ∀ c ∈ tripleCountLow D,
      (D + 1 - (c 0 + c 1 + c 2)) + c 0 + c 1 + c 2 ≤ D + 1 := by
    intro c hc
    rw [mem_tripleCountLow_iff] at hc
    omega
  have hlow := sum_abs_mixedTriplePoissonMass_sub_le_two_tails_of_moments
    ω₀ ω₁ p₀ pi₀ mu₀ p₁ pi₁ mu₁ hs hp₀ hp₁ hpi₀ hpi₁ hmu₀ hmu₁ D
    (tripleCountLow D) (fun c => D + 1 - (c 0 + c 1 + c 2)) hmoment hdegree
  simp_rw [sum_tripleCountLow_coefficient_mul_tail_eq] at hlow
  have hcomp₀ := tsum_mixedTriplePoissonMass_compl_le
    ω₀ p₀ pi₀ mu₀ hs hp₀ hpi₀ hmu₀ D hmass₀ htotal₀
  have hcomp₁ := tsum_mixedTriplePoissonMass_compl_le
    ω₁ p₁ pi₁ mu₁ hs hp₁ hpi₁ hmu₁ D hmass₁ htotal₁
  have hcomp :
      ∑' c : {c // c ∉ tripleCountLow D}, (f₀ c + f₁ c) ≤
        (∑ r, (ω₀ r).toReal *
          (expSeriesTail (sampleScale * p₀ r) (D + 1) * Real.exp (sampleScale * p₀ r))) +
        ∑ r, (ω₁ r).toReal *
          (expSeriesTail (sampleScale * p₁ r) (D + 1) * Real.exp (sampleScale * p₁ r)) := by
    change (∑' c : {c // c ∉ tripleCountLow D},
      (mixedTriplePoissonMass ω₀ sampleScale p₀ pi₀ mu₀ c +
        mixedTriplePoissonMass ω₁ sampleScale p₁ pi₁ mu₁ c)) ≤ _
    have hs₀ : Summable (fun c : {c // c ∉ tripleCountLow D} =>
        mixedTriplePoissonMass ω₀ sampleScale p₀ pi₀ mu₀ c) := hmass₀.subtype _
    have hs₁ : Summable (fun c : {c // c ∉ tripleCountLow D} =>
        mixedTriplePoissonMass ω₁ sampleScale p₁ pi₁ mu₁ c) := hmass₁.subtype _
    rw [hs₀.tsum_add hs₁]
    exact add_le_add hcomp₀ hcomp₁
  refine hsplit.trans (add_le_add hlow hcomp) |>.trans_eq ?_
  calc
    _ = ((∑ r, (ω₀ r).toReal *
          (∑ k ∈ Finset.range (D + 1),
            triplePoissonTotalCoefficient sampleScale (p₀ r) (pi₀ r) (mu₀ r) k *
              expSeriesTail (sampleScale * p₀ r) (D + 1 - k))) +
        ∑ r, (ω₀ r).toReal *
          (expSeriesTail (sampleScale * p₀ r) (D + 1) * Real.exp (sampleScale * p₀ r))) +
      ((∑ r, (ω₁ r).toReal *
          (∑ k ∈ Finset.range (D + 1),
            triplePoissonTotalCoefficient sampleScale (p₁ r) (pi₁ r) (mu₁ r) k *
              expSeriesTail (sampleScale * p₁ r) (D + 1 - k))) +
        ∑ r, (ω₁ r).toReal *
          (expSeriesTail (sampleScale * p₁ r) (D + 1) * Real.exp (sampleScale * p₁ r))) := by ring
    _ = _ := by rw [sum_prior_count_remainder_eq, sum_prior_count_remainder_eq]

end CausalSmith.Stat.DiscreteAteMinimaxLoggap
