/- Pilot-sandwich interface for the heavy/light polynomial program. -/

import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.PolynomialUpper.Calibration
import Causalean.Stat.SampleSplit.FiniteCategoryPilot

namespace CausalSmith.Stat.DiscreteAteHeterogeneityFrontier

open MeasureTheory ProbabilityTheory

-- @node: polynomialPilotLowerBand
/-- Population-mass lower band certified for cells selected as heavy. -/
noncomputable def polynomialPilotLowerBand (n : ℕ) : ℝ :=
  128 * logEN n / (n / 2 : ℕ)

-- @node: polynomialPilotUpperBand
/-- Population-mass upper band certified for cells selected as light. -/
noncomputable def polynomialPilotUpperBand (n : ℕ) : ℝ :=
  512 * logEN n / (n / 2 : ℕ)

-- @node: polynomialPilotUpperBand_le_lightScale_quarter
/-- If [the sample size satisfies the stated lower bound](hyp:hn), [from sample size two onward,
  the pilot light-band lies below one quarter of the polynomial scale used on the independent
  estimation half](goal). -/
lemma polynomialPilotUpperBand_le_lightScale_quarter {n : ℕ} (hn : 2 ≤ n) :
    polynomialPilotUpperBand n ≤
      (4096 * logEN n / (n - n / 2 : ℕ)) / 4 := by
  have hnpos : 0 < n := by omega
  have hm0 : 0 < n / 2 := Nat.div_pos (by omega) (by norm_num)
  have hm1 : 0 < n - n / 2 := Nat.sub_pos_of_lt (Nat.div_lt_self hnpos (by norm_num))
  have hlog : 0 < logEN n := by
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hnpos
    rw [logEN, Real.log_mul (Real.exp_ne_zero 1) hnR.ne', Real.log_exp]
    have hone : 1 ≤ (n : ℝ) := by exact_mod_cast hnpos
    nlinarith [Real.log_nonneg hone]
  have hhalf : n - n / 2 ≤ 2 * (n / 2) := by omega
  have hm0R : 0 < ((n / 2 : ℕ) : ℝ) := by exact_mod_cast hm0
  have hm1R : 0 < ((n - n / 2 : ℕ) : ℝ) := by exact_mod_cast hm1
  unfold polynomialPilotUpperBand
  have hrhs : 4096 * logEN n / ((n - n / 2 : ℕ) : ℝ) / 4 =
      1024 * logEN n / ((n - n / 2 : ℕ) : ℝ) := by ring
  rw [hrhs]
  apply (div_le_div_iff₀ hm0R hm1R).2
  have hhalfR : ((n - n / 2 : ℕ) : ℝ) ≤
      2 * ((n / 2 : ℕ) : ℝ) := by exact_mod_cast hhalf
  nlinarith

-- @node: polynomialPilotCount_eq_finiteCategoryPilotCount
/-- [The estimator's pilot count is exactly the generic finite-category count on the first half of
  the infinite iid realization](goal). -/
lemma polynomialPilotCount_eq_finiteCategoryPilotCount {n d : ℕ}
    (P : RealLaw d) (k : Fin d) (ω : ℕ → Obs d) :
    pilotCount (fun i : Fin n => ω i) k =
      Causalean.Stat.pilotCategoryCount
        (Causalean.Stat.iidSample_infinitePi P.observedLaw)
        (fun o : Obs d => o.x) (Finset.range (n / 2)) k ω := by
  unfold pilotCount Causalean.Stat.pilotCategoryCount inPilot
  apply Finset.card_bij (fun i _ => i.val)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      decide_eq_true_eq] at hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi.1, hi.2⟩
  · intro i₁ _ i₂ _ hij
    exact Fin.ext hij
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj
    let i : Fin n := ⟨j, lt_of_lt_of_le hj.1 (Nat.div_le_self n 2)⟩
    refine ⟨i, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      decide_eq_true_eq]
    exact ⟨hj.1, hj.2⟩

-- @node: polynomialPilotGood
/-- Simultaneous pilot event: every selected-heavy cell has the stated lower
mass and every selected-light cell has the stated upper mass. -/
noncomputable def polynomialPilotGood {n d : ℕ} (P : RealLaw d)
    (lowerBand upperBand : ℝ) : Set (ℕ → Obs d) :=
  Causalean.Stat.finiteCategoryPilotGood
    (Causalean.Stat.iidSample_infinitePi P.observedLaw)
    (fun o : Obs d => o.x) (Finset.range (n / 2))
    (256 * logEN n) lowerBand upperBand

-- @node: polynomialPilotGood_measurable
/-- [The paper-local simultaneous pilot event is measurable](goal). -/
lemma polynomialPilotGood_measurable {n d : ℕ} (P : RealLaw d)
    (lowerBand upperBand : ℝ) :
    MeasurableSet (polynomialPilotGood (n := n) P lowerBand upperBand) := by
  apply Causalean.Stat.measurableSet_finiteCategoryPilotGood
  exact measurable_fst.comp (measurable_iff_comap_le.mpr le_rfl)

-- @node: polynomialPilotGood_selectedHeavy_lower
/-- If [the pilot event is good](hyp:hgood) and [the stated condition on the cell holds](hyp:hk),
  [on the simultaneous pilot event, every cell selected by the concrete heavy threshold has
  population mass at least the declared lower band](goal). -/
lemma polynomialPilotGood_selectedHeavy_lower {n d : ℕ} (P : RealLaw d)
    {lowerBand upperBand : ℝ} {omega : ℕ → Obs d}
    (hgood : omega ∈ polynomialPilotGood (n := n) P lowerBand upperBand)
    (k : Fin d)
    (hk : 256 * logEN n < pilotCount (fun i : Fin n => omega i) k) :
    lowerBand ≤ P.cellMass k := by
  have hkCount :
      256 * logEN n <
        (Causalean.Stat.pilotCategoryCount
          (Causalean.Stat.iidSample_infinitePi P.observedLaw)
          (fun o : Obs d => o.x) (Finset.range (n / 2)) k omega : ℝ) := by
    simpa [polynomialPilotCount_eq_finiteCategoryPilotCount P k omega] using hk
  have hkSelected : k ∈ Causalean.Stat.pilotSelected
      (Causalean.Stat.iidSample_infinitePi P.observedLaw)
      (fun o : Obs d => o.x) (Finset.range (n / 2))
      (256 * logEN n) omega := by
    simpa [Causalean.Stat.pilotSelected] using hkCount
  have hmass := hgood.1 k hkSelected
  have hset : (fun o : Obs d => o.x) ⁻¹' ({k} : Set (Fin d)) =
      {o : Obs d | o.x = k} := by ext o; simp
  unfold Causalean.Stat.categoryMass at hmass
  rw [hset] at hmass
  rw [P.cellMass_eq k]
  simpa [polynomialPilotGood, Causalean.Stat.categoryMass, Measure.real,
    realMass] using hmass

-- @node: polynomialPilotGood_selectedLight_upper
/-- If [the pilot event is good](hyp:hgood) and [the stated condition on the cell holds](hyp:hk),
  [on the simultaneous pilot event, every cell rejected by the concrete heavy threshold has
  population mass at most the declared upper band](goal). -/
lemma polynomialPilotGood_selectedLight_upper {n d : ℕ} (P : RealLaw d)
    {lowerBand upperBand : ℝ} {omega : ℕ → Obs d}
    (hgood : omega ∈ polynomialPilotGood (n := n) P lowerBand upperBand)
    (k : Fin d)
    (hk : ¬ 256 * logEN n < pilotCount (fun i : Fin n => omega i) k) :
    P.cellMass k ≤ upperBand := by
  have hkCount : ¬
      256 * logEN n <
        (Causalean.Stat.pilotCategoryCount
          (Causalean.Stat.iidSample_infinitePi P.observedLaw)
          (fun o : Obs d => o.x) (Finset.range (n / 2)) k omega : ℝ) := by
    simpa [polynomialPilotCount_eq_finiteCategoryPilotCount P k omega] using hk
  have hkRejected : k ∉ Causalean.Stat.pilotSelected
      (Causalean.Stat.iidSample_infinitePi P.observedLaw)
      (fun o : Obs d => o.x) (Finset.range (n / 2))
      (256 * logEN n) omega := by
    simpa [Causalean.Stat.pilotSelected] using hkCount
  have hmass := hgood.2 k hkRejected
  have hset : (fun o : Obs d => o.x) ⁻¹' ({k} : Set (Fin d)) =
      {o : Obs d | o.x = k} := by ext o; simp
  unfold Causalean.Stat.categoryMass at hmass
  rw [hset] at hmass
  rw [P.cellMass_eq k]
  simpa [polynomialPilotGood, Causalean.Stat.categoryMass, Measure.real,
    realMass] using hmass

-- @node: polynomialPilotGood_compl_probability_le
/-- If [the sample is nonempty](hyp:hn), [the generic logarithmic two-sided pilot bound
  specialized to the exact threshold and balanced first block used by `rawPolyEstimator`](goal). -/
lemma polynomialPilotGood_compl_probability_le {n d : ℕ} (P : RealLaw d)
    (hn : 0 < n) (lowerBand upperBand : ℝ) :
    (Measure.infinitePi fun _ : ℕ => P.observedLaw).real
        (polynomialPilotGood (n := n) P lowerBand upperBand)ᶜ ≤
      (d : ℝ) *
        (Real.exp (-Real.log 2 * (256 * logEN n) +
          ((Finset.range (n / 2)).card : ℝ) * lowerBand) +
        Real.exp (Real.log 2 * (256 * logEN n) -
          ((Finset.range (n / 2)).card : ℝ) * upperBand / 2)) := by
  unfold polynomialPilotGood
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hlog : 0 < logEN n := by
    rw [logEN, Real.log_mul (Real.exp_ne_zero 1) hnR.ne', Real.log_exp]
    have hn_one : 1 ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith [Real.log_nonneg hn_one]
  have ht : 0 < 256 * logEN n := by positivity
  simpa using Causalean.Stat.finiteCategoryPilot_bad_probability_log_two
    (Causalean.Stat.iidSample_infinitePi P.observedLaw)
    (label := fun o : Obs d => o.x)
    (measurable_fst.comp (measurable_iff_comap_le.mpr le_rfl))
    (Finset.range (n / 2)) (t := 256 * logEN n) ht lowerBand upperBand

-- @node: polynomialPilotGood_compl_probability_calibrated_le
/-- If [the sample size satisfies the stated lower bound](hyp:hn), [at the declared pilot bands,
  the two Chernoff exponents both dominate `32 * log(en)`, giving a directly usable bad-selector
  probability bound](goal). -/
lemma polynomialPilotGood_compl_probability_calibrated_le {n d : ℕ}
    (P : RealLaw d) (hn : 2 ≤ n) :
    (Measure.infinitePi fun _ : ℕ => P.observedLaw).real
        (polynomialPilotGood (n := n) P
          (polynomialPilotLowerBand n) (polynomialPilotUpperBand n))ᶜ ≤
      2 * (d : ℝ) * Real.exp (-32 * logEN n) := by
  have hnpos : 0 < n := by omega
  have hm0 : 0 < n / 2 := Nat.div_pos (by omega) (by norm_num)
  have hm0R : 0 < ((n / 2 : ℕ) : ℝ) := by exact_mod_cast hm0
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hlog : 0 < logEN n := by
    rw [logEN, Real.log_mul (Real.exp_ne_zero 1) hnR.ne', Real.log_exp]
    have hone : 1 ≤ (n : ℝ) := by exact_mod_cast hnpos
    nlinarith [Real.log_nonneg hone]
  have hbase := polynomialPilotGood_compl_probability_le P hnpos
    (polynomialPilotLowerBand n) (polynomialPilotUpperBand n)
  apply hbase.trans
  simp only [Finset.card_range]
  unfold polynomialPilotLowerBand polynomialPilotUpperBand
  have hcancelLower :
      ((n / 2 : ℕ) : ℝ) * (128 * logEN n / ((n / 2 : ℕ) : ℝ)) =
        128 * logEN n := by field_simp
  have hcancelUpper :
      ((n / 2 : ℕ) : ℝ) * (512 * logEN n / ((n / 2 : ℕ) : ℝ)) / 2 =
        256 * logEN n := by field_simp; ring
  rw [hcancelLower, hcancelUpper]
  have hlogTwoLower : (5 / 8 : ℝ) ≤ Real.log 2 := by
    exact le_trans (by norm_num) Real.log_two_gt_d9.le
  have hlogTwoUpper : Real.log 2 ≤ (7 / 8 : ℝ) := by
    exact Real.log_two_lt_d9.le.trans (by norm_num)
  have hfirst :
      -Real.log 2 * (256 * logEN n) + 128 * logEN n ≤
        -32 * logEN n := by nlinarith
  have hsecond :
      Real.log 2 * (256 * logEN n) - 256 * logEN n ≤
        -32 * logEN n := by nlinarith
  have hexpFirst := Real.exp_le_exp.mpr hfirst
  have hexpSecond := Real.exp_le_exp.mpr hsecond
  have hd0 : 0 ≤ (d : ℝ) := by positivity
  calc
    (d : ℝ) *
        (Real.exp (-Real.log 2 * (256 * logEN n) + 128 * logEN n) +
          Real.exp (Real.log 2 * (256 * logEN n) - 256 * logEN n)) ≤
        (d : ℝ) * (Real.exp (-32 * logEN n) +
          Real.exp (-32 * logEN n)) := by gcongr
    _ = 2 * (d : ℝ) * Real.exp (-32 * logEN n) := by ring

end CausalSmith.Stat.DiscreteAteHeterogeneityFrontier
