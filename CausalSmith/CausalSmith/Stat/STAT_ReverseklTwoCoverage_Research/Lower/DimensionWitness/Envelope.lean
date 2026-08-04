import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Lower.DimensionWitness.Event

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedVariables false

namespace CausalSmith.Stat.ReverseKLTwoCoverage

open MeasureTheory
open scoped BigOperators ENNReal Topology

def dwZeroCoefficient {d : ℕ} (j : Fin d) (theta : Fin d → ℝ) :
    Fin d → ℝ :=
  fun i => if i = j then 0 else theta i

noncomputable def dwZeroPrediction (d : ℕ) (hd : 4 ≤ d)
    (j : Fin d) (theta : Fin d → ℝ) :
    Prediction (𝒳 := Fin d) (𝒜 := Fin 2) :=
  fun x a => ∑ i, (dwExperiment d hd).feature x a i *
    dwZeroCoefficient j theta i

lemma dwZeroPrediction_at (d : ℕ) (hd : 4 ≤ d)
    (j : Fin d) (theta : Fin d → ℝ) (a : Fin 2) :
    dwZeroPrediction d hd j theta j a = 0 := by
  classical
  unfold dwZeroPrediction
  rw [Finset.sum_eq_single j]
  · simp [dwZeroCoefficient]
  · intro i _ hi
    simp [dwExperiment, dwFeature, dwZeroCoefficient, hi, Ne.symm hi]
  · simp

lemma dwZeroPrediction_away (d : ℕ) (hd : 4 ≤ d)
    (j : Fin d) (theta : Fin d → ℝ) (x : Fin d) (a : Fin 2)
    (hx : x ≠ j) :
    dwZeroPrediction d hd j theta x a =
      ∑ i, (dwExperiment d hd).feature x a i * theta i := by
  classical
  unfold dwZeroPrediction
  apply Finset.sum_congr rfl
  intro i _
  by_cases hij : i = j
  · subst i
    simp [dwZeroCoefficient, dwExperiment, dwFeature, hx]
  · simp [dwZeroCoefficient, hij]

lemma dw_radius_lower (d : ℕ) (hd : 4 ≤ d) :
    3 * (d : ℝ) / (d ^ 2 : ℕ) ≤
      64 * ((d : ℝ) * Real.log (Real.exp 1 * (d ^ 2 : ℕ)) +
        Real.log (2 * ((d ^ 2 : ℕ) : ℝ) ^ 2)) / (d ^ 2 : ℕ) := by
  have hnpos : (0 : ℝ) < (d ^ 2 : ℕ) := by positivity
  have hn1 : (1 : ℝ) ≤ (d ^ 2 : ℕ) := by
    exact_mod_cast
      (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 2 (by omega : d ≠ 0)))
  have hlogn : 0 ≤ Real.log ((d ^ 2 : ℕ) : ℝ) :=
    Real.log_nonneg hn1
  have hlogfirst :
      1 ≤ Real.log (Real.exp 1 * ((d ^ 2 : ℕ) : ℝ)) := by
    rw [Real.log_mul (Real.exp_ne_zero 1) (ne_of_gt hnpos), Real.log_exp]
    linarith
  have hlogsecond :
      0 ≤ Real.log (2 * ((d ^ 2 : ℕ) : ℝ) ^ 2) := by
    apply Real.log_nonneg
    nlinarith [sq_nonneg (((d ^ 2 : ℕ) : ℝ) - 1)]
  apply (div_le_div_iff_of_pos_right hnpos).2
  nlinarith

lemma dw_cellCount_cast (d : ℕ)
    (sample : LoggedSample (d ^ 2) (Fin d) (Fin 2)) (j : Fin d) :
    (cellCount (dwContextSample sample) j : ℝ) =
      ∑ i : Fin (d ^ 2), if (sample i).context = j then 1 else 0 := by
  simp only [cellCount, Finset.cast_card]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  simp [dwContextSample]

lemma dw_zeroPrediction_mem_confidence (d : ℕ) (hd : 4 ≤ d)
    (sample : LoggedSample (d ^ 2) (Fin d) (Fin 2))
    (hcount : dwCountGood d sample) (j : Fin d) :
    ∃ f ∈ confidencePolytope (dwExperiment d hd) 64 sample,
      ∀ a, f j a = 0 := by
  have hsel :=
    LinearExactShellTypeFit.selectedERM_isLexicographicERM
      (dwExperiment d hd) sample
  rcases hsel.1 with ⟨hbounded, theta, htheta⟩
  let f := dwZeroPrediction d hd j theta
  have hfvalue :
      ∀ x a, f x a =
        if x = j then 0 else selectedERM (dwExperiment d hd) sample x a := by
    intro x a
    by_cases hx : x = j
    · subst x
      simp [f, dwZeroPrediction_at]
    · rw [if_neg hx]
      change dwZeroPrediction d hd j theta x a =
        selectedERM (dwExperiment d hd) sample x a
      rw [dwZeroPrediction_away d hd j theta x a hx]
      exact (htheta x a).symm
  have hfpoly : f ∈ predictionPolytope (dwExperiment d hd) := by
    constructor
    · intro x a
      rw [hfvalue]
      by_cases hx : x = j
      · simp [hx]
      · simpa [hx] using hbounded x a
    · exact ⟨dwZeroCoefficient j theta, fun _ _ => rfl⟩
  have hterm : ∀ i : Fin (d ^ 2),
      (f (sample i).context (sample i).action -
        selectedERM (dwExperiment d hd) sample
          (sample i).context (sample i).action) ^ 2 ≤
        if (sample i).context = j then 1 else 0 := by
    intro i
    rw [hfvalue]
    by_cases hx : (sample i).context = j
    · rw [if_pos hx, if_pos hx]
      have hb := hbounded (sample i).context (sample i).action
      have hprod : 0 ≤
          (1 - selectedERM (dwExperiment d hd) sample
            (sample i).context (sample i).action) *
          (1 + selectedERM (dwExperiment d hd) sample
            (sample i).context (sample i).action) :=
        mul_nonneg (sub_nonneg.mpr hb.2) (by linarith [hb.1])
      nlinarith
    · simp [hx]
  have hsum :
      ∑ i : Fin (d ^ 2),
          (f (sample i).context (sample i).action -
            selectedERM (dwExperiment d hd) sample
              (sample i).context (sample i).action) ^ 2 ≤
        cellCount (dwContextSample sample) j := by
    calc
      (∑ i : Fin (d ^ 2),
          (f (sample i).context (sample i).action -
            selectedERM (dwExperiment d hd) sample
              (sample i).context (sample i).action) ^ 2) ≤
          ∑ i : Fin (d ^ 2),
            if (sample i).context = j then 1 else 0 :=
        Finset.sum_le_sum fun i _ => hterm i
      _ = cellCount (dwContextSample sample) j := by
        rw [← dw_cellCount_cast]
  have hcountj : cellCount (dwContextSample sample) j ≤ 3 * d := by
    by_contra h
    exact hcount ⟨j, Nat.lt_of_not_ge h⟩
  refine ⟨f, ?_, fun a => dwZeroPrediction_at d hd j theta a⟩
  refine ⟨hfpoly, ?_⟩
  unfold empiricalSeminormSq
  have hninv : 0 ≤ (((d ^ 2 : ℕ) : ℝ)⁻¹) := by positivity
  calc
    ((d ^ 2 : ℕ) : ℝ)⁻¹ *
        ∑ i : Fin (d ^ 2),
          (f (sample i).context (sample i).action -
            selectedERM (dwExperiment d hd) sample
              (sample i).context (sample i).action) ^ 2 ≤
        ((d ^ 2 : ℕ) : ℝ)⁻¹ *
          (cellCount (dwContextSample sample) j : ℝ) :=
      mul_le_mul_of_nonneg_left hsum hninv
    _ ≤ 3 * (d : ℝ) / (d ^ 2 : ℕ) := by
      rw [div_eq_inv_mul]
      gcongr
      exact_mod_cast hcountj
    _ ≤ 64 * ((d : ℝ) * Real.log (Real.exp 1 * (d ^ 2 : ℕ)) +
        Real.log (2 * (((d ^ 2 : ℕ) : ℝ) ^ 2))) / (d ^ 2 : ℕ) :=
      dw_radius_lower d hd

lemma dw_lowerEnvelope_zero (d : ℕ) (hd : 4 ≤ d)
    (sample : LoggedSample (d ^ 2) (Fin d) (Fin 2))
    (hcount : dwCountGood d sample) (x : Fin d) (a : Fin 2) :
    lowerEnvelope (dwExperiment d hd) 64 sample x a = 0 := by
  obtain ⟨f0, hf0, hzero⟩ :=
    dw_zeroPrediction_mem_confidence d hd sample hcount x
  let values : Set ℝ :=
    {r | ∃ f ∈ confidencePolytope (dwExperiment d hd) 64 sample,
      r = f x a}
  have hvalues_nonempty : values.Nonempty := ⟨0, f0, hf0, (hzero a).symm⟩
  have hvalues_bdd : BddBelow values := by
    refine ⟨0, ?_⟩
    rintro r ⟨f, hf, rfl⟩
    exact hf.1.1 x a |>.1
  have hzero_mem : (0 : ℝ) ∈ values :=
    ⟨f0, hf0, (hzero a).symm⟩
  unfold lowerEnvelope
  change sInf values = 0
  exact le_antisymm
    (csInf_le hvalues_bdd hzero_mem)
    (le_csInf hvalues_nonempty fun r hr =>
      match hr with
      | ⟨f, hf, hrf⟩ => hrf.symm ▸ hf.1.1 x a |>.1)

lemma dw_lowerEnvelopePolicy_eq_reference (d : ℕ) (hd : 4 ≤ d)
    (sample : LoggedSample (d ^ 2) (Fin d) (Fin 2))
    (hgood : sample ∈ dwGoodEvent d hd) :
    lowerEnvelopePolicy (dwExperiment d hd) 64 sample =
      (dwExperiment d hd).reference := by
  funext x a
  have hcount := hgood.1
  unfold lowerEnvelopePolicy
  simp_rw [dw_lowerEnvelope_zero d hd sample hcount]
  simp [(dwExperiment d hd).reference_isPolicy.2 x]

end CausalSmith.Stat.ReverseKLTwoCoverage
