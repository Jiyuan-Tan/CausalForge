/-
# Regular-cell risk engine

Leaf lemmas for the honesty and variance half of the regular finite-cell
attainment argument.  The ambient covariate carrier remains arbitrary: every
finite calculation is scoped to the injected support supplied by
`RegularFiniteCellClass`.
-/

import CausalSmith.Stat.STAT_TransportedLateStrengthFrontier_Research.Helpers.InversionRisk
import CausalSmith.Stat.STAT_TransportedLateStrengthFrontier_Research.Helpers.Witness
import CausalSmith.Stat.STAT_TransportedLateStrengthFrontier_Research.T_CompactCausalRange
import CausalSmith.Stat.STAT_TransportedLateStrengthFrontier_Research.Helpers.RegularCellRisk_Part1
import CausalSmith.Stat.STAT_TransportedLateStrengthFrontier_Research.Helpers.RegularCellRisk_Part2
import CausalSmith.Stat.STAT_TransportedLateStrengthFrontier_Research.Helpers.RegularCellRisk_Part3
import CausalSmith.Stat.STAT_TransportedLateStrengthFrontier_Research.Helpers.RegularCellRisk_Part4
import Causalean.Stat.Sample.EmpiricalMass

namespace CausalSmith.Stat.TransportedLateStrengthFrontier

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology

variable {𝒳 : Type*} [MeasurableSpace 𝒳]
/-! ## Statistics and deterministic constants -/
/-- Eventually and uniformly over the regular class, both cross moments obey
the exact paper variance constant; the receipt moment is centered at the
transported first stage. -/
lemma regularCell_eventually_uniform_moment_variance
    (N k : ℕ → ℕ) (c epsilon cminus cplus : ℝ)
    (hc : 0 < c)
    (hepsilon : 0 < epsilon ∧ epsilon < 1 / 2)
    (hcminus : 0 < cminus ∧ cminus ≤ 1)
    (hcplus : 1 ≤ cplus)
    (hN : Tendsto (fun n : ℕ => (N n : ℝ) / (n : ℝ)) atTop (𝓝 c))
    (hkPos : ∀ n, 0 < k n)
    (hkRoot : Tendsto (fun n : ℕ => (k n : ℝ) / Real.sqrt n)
      atTop (𝓝 0)) :
    ∀ᶠ n in atTop, ∀ P : TransportedArray 𝒳,
      RegularFiniteCellClass P N k c epsilon cminus cplus n →
      variance
          (fun s : TwoSample 𝒳 n (N n) =>
            regularCellContrastMoment (sourceCellMass P n)
              (P.propensity n) (targetCACE P n) s.1 s.2)
          (twoSampleLaw P N n) ≤
        regularCellVarianceConstant epsilon c * kishDispersion P n / n ∧
      variance
          (fun s : TwoSample 𝒳 n (N n) =>
            regularCellReceiptMoment (sourceCellMass P n)
              (P.propensity n) s.1 s.2)
          (twoSampleLaw P N n) ≤
        regularCellVarianceConstant epsilon c * kishDispersion P n / n ∧
      (∫ s : TwoSample 𝒳 n (N n),
          regularCellReceiptMoment (sourceCellMass P n)
            (P.propensity n) s.1 s.2 ∂twoSampleLaw P N n) =
        transportedFirstStage P n := by
  have hsqrtTop :
      Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hinvSqrt :
      Tendsto (fun n : ℕ => (Real.sqrt (n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hsqrtTop
  have hkn : Tendsto (fun n : ℕ => (k n : ℝ) / (n : ℝ))
      atTop (𝓝 0) := by
    have heq : (fun n : ℕ => (k n : ℝ) / (n : ℝ)) =
        fun n => ((k n : ℝ) / Real.sqrt n) * (Real.sqrt n)⁻¹ := by
      funext n
      by_cases hn : n = 0
      · simp [hn]
      · have hs : Real.sqrt (n : ℝ) ≠ 0 := by positivity
        rw [div_eq_mul_inv, div_eq_mul_inv]
        field_simp [hs, Real.sq_sqrt (Nat.cast_nonneg n)]
        rw [Real.sq_sqrt (Nat.cast_nonneg n)]
    rw [heq]
    simpa using hkRoot.mul hinvSqrt
  have hNratio :
      ∀ᶠ n : ℕ in atTop, c / 2 < (N n : ℝ) / (n : ℝ) :=
    (tendsto_order.1 hN).1 _ (by linarith)
  have hnpos : ∀ᶠ n : ℕ in atTop, 0 < n :=
    eventually_atTop.2 ⟨1, fun n hn => Nat.zero_lt_of_lt hn⟩
  have hkOverN :
      Tendsto (fun n : ℕ => (k n : ℝ) / (N n : ℝ)) atTop (𝓝 0) := by
    have hquot := hkn.div hN hc.ne'
    have hquot' :
        Tendsto
          ((fun n : ℕ => (k n : ℝ) / (n : ℝ)) /
            fun n => (N n : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
      simpa [hc.ne'] using hquot
    apply hquot'.congr'
    filter_upwards [hnpos, hNratio] with n hn hratio
    have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
    have hNreal : 0 < (N n : ℝ) := by
      have hp : 0 < (N n : ℝ) / (n : ℝ) :=
        lt_trans (half_pos hc) hratio
      rcases (div_pos_iff.mp hp) with h | h
      · exact h.1
      · exact (not_lt_of_ge hnreal.le h.2).elim
    change
      ((k n : ℝ) / (n : ℝ)) / ((N n : ℝ) / (n : ℝ)) =
        (k n : ℝ) / (N n : ℝ)
    field_simp [hnreal.ne', hNreal.ne']
  have hkSmall :
      ∀ᶠ n : ℕ in atTop, (k n : ℝ) / (N n : ℝ) < cminus :=
    (tendsto_order.1 hkOverN).2 _ hcminus.1
  filter_upwards [hnpos, hNratio, hkSmall] with n hn hratio hkSmallN
  intro P hP
  classical
  rcases hP with
    ⟨hIV, hk, hcm, hcmOne, hcp, cell, hcell, hrange, hmass⟩
  letI : IsProbabilityMeasure (sourceObsLaw P n) :=
    hIV.twoSampleArray.2.1 n
  letI : IsProbabilityMeasure (sourceXLaw P n) := by
    unfold sourceXLaw
    exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  letI : IsProbabilityMeasure (targetXLaw P n) :=
    hIV.twoSampleArray.2.2.1 n
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hNreal : 0 < (N n : ℝ) := by
    have hp : 0 < (N n : ℝ) / (n : ℝ) :=
      lt_trans (half_pos hc) hratio
    rcases (div_pos_iff.mp hp) with h | h
    · exact h.1
    · exact (not_lt_of_ge hnreal.le h.2).elim
  have hNpos : 0 < N n := by exact_mod_cast hNreal
  have hqpos (i : Fin (k n)) :
      0 < sourceCellMass P n (cell i) :=
    lt_of_lt_of_le (div_pos hcm (by exact_mod_cast hk)) (hmass i).1
  have hRleOne :
      (k n : ℝ) / (cminus * (N n : ℝ)) ≤ 1 := by
    have hkdiv :
        (k n : ℝ) / (N n : ℝ) < cminus := hkSmallN
    rw [div_le_iff₀ (mul_pos hcm hNreal)]
    rw [div_lt_iff₀ hNreal] at hkdiv
    nlinarith
  have hfourN : 4 / (N n : ℝ) ≤ 8 / (c * (n : ℝ)) := by
    have hlower : c / 2 * (n : ℝ) < (N n : ℝ) := by
      exact (lt_div_iff₀ hnreal).1 hratio
    apply (div_le_div_iff₀ hNreal (mul_pos hc hnreal)).2
    nlinarith
  have hAssignmentInt :
      Integrable (P.assignmentContrast n true) (sourceXLaw P n) :=
    integrable_of_finite_support (sourceXLaw P n) cell hcell hrange _
      (P.assignmentContrast_measurable n true).stronglyMeasurable
  have hReceiptInt :
      Integrable (P.receiptContrast n true) (sourceXLaw P n) :=
    integrable_of_finite_support (sourceXLaw P n) cell hcell hrange _
      (P.receiptContrast_measurable n true).stronglyMeasurable
  have hTheta : targetCACE P n ∈ parameterSpace := by
    rcases compact_causal_range P N k c epsilon n
      hAssignmentInt hReceiptInt hIV with ⟨_, _, _, _, _, htheta⟩
    exact htheta
  let i0 : Fin (k n) := ⟨0, hk⟩
  let target0 : TargetSample 𝒳 (N n) := fun _ => cell i0
  have hScoreCore :=
    regularCell_source_conditional_mean_variance_for_witness
      P N k c epsilon cminus cplus (targetCACE P n) n target0 hn
      hIV hk hcm hcmOne hcp cell hcell hrange hmass hTheta
  have hScoreMean := hScoreCore.2.2.2.1
  have hScoreMem := hScoreCore.2.2.2.2.1
  have hScoreBound := hScoreCore.2.2.2.2.2
  have hInstrumentMeasurable : Measurable (instrumentScore P n) := by
    have hz : Measurable fun o : SourceObs 𝒳 => o.2.1 := by fun_prop
    have he : Measurable fun o : SourceObs 𝒳 => P.propensity n o.1 :=
      (P.propensity_measurable n).comp measurable_fst
    unfold instrumentScore
    exact Measurable.ite (hz (MeasurableSet.singleton true))
      (measurable_const.div he)
      (measurable_const.neg.div (measurable_const.sub he))
  have hBoolMeasurable :
      Measurable (fun o : SourceObs 𝒳 => boolReal o.2.2.1) := by
    unfold boolReal
    have hd : Measurable fun o : SourceObs 𝒳 => o.2.2.1 := by fun_prop
    exact Measurable.ite (hd (MeasurableSet.singleton true))
      measurable_const measurable_const
  have hScoreMeas :
      Measurable (regularCellScore (P.propensity n) (targetCACE P n)) := by
    change Measurable (fun o : SourceObs 𝒳 =>
      instrumentScore P n o *
        (o.2.2.2 - targetCACE P n * boolReal o.2.2.1))
    have hy : Measurable fun o : SourceObs 𝒳 => o.2.2.2 := by fun_prop
    exact hInstrumentMeasurable.mul
      (hy.sub (measurable_const.mul hBoolMeasurable))
  have hTargetScore :=
    regularCell_target_score_mean_variance_for_witness
      P N k c epsilon cminus cplus n hIV hk hcm hcmOne hcp
      cell hcell hrange hmass
  have hMulti :=
    regularCell_multinomial_second_moment_for_witness
      P N k c epsilon cminus cplus n hNpos hIV hk hcm hcmOne hcp
      cell hcell hrange hmass
  have hContrastRaw :=
    weighted_two_sample_variance P N n hn cell hcell hrange
      (regularCellScore (P.propensity n) (targetCACE P n))
      (regularCellScoreMean P n (targetCACE P n))
      (2 / epsilon) (4 / (N n : ℝ))
      ((k n : ℝ) / (cminus * (N n : ℝ))) 0
      (div_nonneg (by norm_num) hepsilon.1.le) hScoreMeas hScoreMem
      hScoreBound hqpos hScoreMean hTargetScore.2.1 hTargetScore.1
      hTargetScore.2.2 hMulti.2.2 hMulti.2.1
  have hkish : 1 ≤ kishDispersion P n :=
    one_le_regularCell_kish P N k c epsilon n hIV cell hcell hrange
  have hRleKish :
      (k n : ℝ) / (cminus * (N n : ℝ)) ≤ kishDispersion P n :=
    hRleOne.trans hkish
  have hContrast :
      variance
          (fun s : TwoSample 𝒳 n (N n) =>
            regularCellContrastMoment (sourceCellMass P n)
              (P.propensity n) (targetCACE P n) s.1 s.2)
          (twoSampleLaw P N n) ≤
        regularCellVarianceConstant epsilon c * kishDispersion P n / n := by
    have hraw : variance
          (fun s : TwoSample 𝒳 n (N n) =>
            regularCellContrastMoment (sourceCellMass P n)
              (P.propensity n) (targetCACE P n) s.1 s.2)
          (twoSampleLaw P N n) ≤
        (2 / epsilon) ^ 2 / n *
            (kishDispersion P n +
              (k n : ℝ) / (cminus * (N n : ℝ))) +
          4 / (N n : ℝ) := by
      simpa only [regularCell_crossAverage_identity] using hContrastRaw.1
    have hcond :
        (2 / epsilon) ^ 2 / n *
            (kishDispersion P n +
              (k n : ℝ) / (cminus * (N n : ℝ))) ≤
          8 * epsilon⁻¹ ^ 2 * kishDispersion P n / n := by
      have hsum : kishDispersion P n +
          (k n : ℝ) / (cminus * (N n : ℝ)) ≤
          2 * kishDispersion P n := by linarith
      calc
        _ ≤ (2 / epsilon) ^ 2 / n * (2 * kishDispersion P n) := by
          gcongr
        _ = 8 * epsilon⁻¹ ^ 2 * kishDispersion P n / n := by
          field_simp [hepsilon.1.ne', hnreal.ne']
          <;> ring
    have htarget :
        4 / (N n : ℝ) ≤
          8 * c⁻¹ * kishDispersion P n / n := by
      calc
        4 / (N n : ℝ) ≤ 8 / (c * (n : ℝ)) := hfourN
        _ ≤ 8 * c⁻¹ * kishDispersion P n / n := by
          field_simp [hc.ne', hnreal.ne']
          nlinarith
    calc
      _ ≤ (2 / epsilon) ^ 2 / n *
            (kishDispersion P n +
              (k n : ℝ) / (cminus * (N n : ℝ))) +
          4 / (N n : ℝ) := hraw
      _ ≤ 8 * epsilon⁻¹ ^ 2 * kishDispersion P n / n +
          8 * c⁻¹ * kishDispersion P n / n :=
        add_le_add hcond htarget
      _ = regularCellVarianceConstant epsilon c *
          kishDispersion P n / n := by
        unfold regularCellVarianceConstant
        ring
  let Gd : SourceObs 𝒳 → ℝ := fun o =>
    oracleInstrumentScore (P.propensity n) o * boolReal o.2.2.1
  have hGdMeas : Measurable Gd := by
    change Measurable (fun o : SourceObs 𝒳 =>
      instrumentScore P n o * boolReal o.2.2.1)
    exact hInstrumentMeasurable.mul hBoolMeasurable
  have hInstrumentBound : ∀ᵐ o ∂sourceObsLaw P n,
      |instrumentScore P n o| ≤ 1 / epsilon := by
    have hoverlap : ∀ᵐ o ∂sourceObsLaw P n,
        epsilon ≤ P.propensity n o.1 ∧
          P.propensity n o.1 ≤ 1 - epsilon := by
      have hx := hIV.instrumentOverlap.2.2
      unfold sourceXLaw at hx
      exact ae_of_ae_map measurable_fst.aemeasurable hx
    filter_upwards [hoverlap] with o ho
    rcases o with ⟨x, z, d, y⟩
    cases z
    · simp only [instrumentScore, Bool.false_eq_true, ↓reduceIte, abs_neg,
        abs_div, abs_one]
      rw [abs_of_pos (sub_pos.mpr (lt_of_le_of_lt ho.2
        (by linarith [hIV.instrumentOverlap.1])))]
      exact one_div_le_one_div_of_le hIV.instrumentOverlap.1
        (by linarith [ho.2])
    · simp only [instrumentScore, ↓reduceIte, abs_div, abs_one]
      rw [abs_of_pos (lt_of_lt_of_le hIV.instrumentOverlap.1 ho.1)]
      exact one_div_le_one_div_of_le hIV.instrumentOverlap.1 ho.1
  have hGdBound : ∀ᵐ o ∂sourceObsLaw P n, |Gd o| ≤ 1 / epsilon := by
    filter_upwards [hInstrumentBound] with o ho
    have hd : |boolReal o.2.2.1| ≤ 1 := by
      cases o.2.2.1 <;> simp [boolReal]
    change |instrumentScore P n o * boolReal o.2.2.1| ≤ 1 / epsilon
    rw [abs_mul]
    exact (mul_le_mul ho hd (abs_nonneg _)
      (one_div_nonneg.mpr hepsilon.1.le)).trans_eq (mul_one _)
  have hGdMem : MemLp Gd 2 (sourceObsLaw P n) :=
    MemLp.of_bound hGdMeas.aestronglyMeasurable (1 / epsilon)
      (hGdBound.mono fun o ho => by simpa [Real.norm_eq_abs] using ho)
  have hGdMean (i : Fin (k n)) :
      (∫ o in {o | o.1 = cell i}, Gd o ∂sourceObsLaw P n) /
          sourceCellMass P n (cell i) = P.deltaD n (cell i) := by
    have hReceiptSet :=
      (sourceObservationFacts_of_class P N k c epsilon n hIV).2.2.2.2.2.2.2.1
        ({cell i} : Set 𝒳) (hcell i)
    change
      (∫ o in {o | o.1 ∈ ({cell i} : Set 𝒳)},
        instrumentScore P n o * boolReal o.2.2.1
          ∂sourceObsLaw P n) / sourceCellMass P n (cell i) =
        P.deltaD n (cell i)
    rw [hReceiptSet,
      integral_singleton' (P.deltaD_measurable n).stronglyMeasurable]
    change
      (sourceCellMass P n (cell i) * P.deltaD n (cell i)) /
          sourceCellMass P n (cell i) = P.deltaD n (cell i)
    field_simp [(hqpos i).ne']
  have hTargetD :=
    target_receipt_mean_variance_for_witness
      P N k c epsilon cminus cplus n hNpos hIV hk hcm cell
      hcell hrange hmass
  have hReceiptRaw :=
    weighted_two_sample_variance P N n hn cell hcell hrange
      Gd (P.deltaD n) (1 / epsilon) (1 / (N n : ℝ))
      ((k n : ℝ) / (cminus * (N n : ℝ)))
      (transportedFirstStage P n)
      (one_div_nonneg.mpr hepsilon.1.le) hGdMeas hGdMem hGdBound
      hqpos hGdMean hTargetD.2.1 hTargetD.1 hTargetD.2.2
      hMulti.2.2 hMulti.2.1
  have hReceipt :
      variance
          (fun s : TwoSample 𝒳 n (N n) =>
            regularCellReceiptMoment (sourceCellMass P n)
              (P.propensity n) s.1 s.2)
          (twoSampleLaw P N n) ≤
        regularCellVarianceConstant epsilon c * kishDispersion P n / n := by
    have hraw : variance
          (fun s : TwoSample 𝒳 n (N n) =>
            regularCellReceiptMoment (sourceCellMass P n)
              (P.propensity n) s.1 s.2)
          (twoSampleLaw P N n) ≤
        (1 / epsilon) ^ 2 / n *
            (kishDispersion P n +
              (k n : ℝ) / (cminus * (N n : ℝ))) +
          1 / (N n : ℝ) := by
      simpa only [regularCellReceiptMoment, crossAverage_eq_empirical,
        Gd] using hReceiptRaw.1
    have hrawle :
        (1 / epsilon) ^ 2 / n *
            (kishDispersion P n +
              (k n : ℝ) / (cminus * (N n : ℝ))) +
          1 / (N n : ℝ) ≤
        (2 / epsilon) ^ 2 / n *
            (kishDispersion P n +
              (k n : ℝ) / (cminus * (N n : ℝ))) +
          4 / (N n : ℝ) := by
      have hsum0 : 0 ≤ kishDispersion P n +
          (k n : ℝ) / (cminus * (N n : ℝ)) := by positivity
      have hcoef :
          (1 / epsilon) ^ 2 / n ≤ (2 / epsilon) ^ 2 / n := by
        apply div_le_div_of_nonneg_right _ hnreal.le
        have hs := sq_nonneg (1 / epsilon)
        convert (show (1 / epsilon) ^ 2 ≤ 4 * (1 / epsilon) ^ 2 by
          nlinarith) using 1 <;> ring
      have htarget : 1 / (N n : ℝ) ≤ 4 / (N n : ℝ) := by
        exact div_le_div_of_nonneg_right (by norm_num) hNreal.le
      exact add_le_add (mul_le_mul_of_nonneg_right hcoef hsum0) htarget
    have hbudget :
        (2 / epsilon) ^ 2 / n *
            (kishDispersion P n +
              (k n : ℝ) / (cminus * (N n : ℝ))) +
          4 / (N n : ℝ) ≤
        regularCellVarianceConstant epsilon c * kishDispersion P n / n := by
      have hsum : kishDispersion P n +
          (k n : ℝ) / (cminus * (N n : ℝ)) ≤
          2 * kishDispersion P n := by linarith
      have hcond :
          (2 / epsilon) ^ 2 / n *
              (kishDispersion P n +
                (k n : ℝ) / (cminus * (N n : ℝ))) ≤
            8 * epsilon⁻¹ ^ 2 * kishDispersion P n / n := by
        calc
          _ ≤ (2 / epsilon) ^ 2 / n * (2 * kishDispersion P n) := by
            gcongr
          _ = 8 * epsilon⁻¹ ^ 2 * kishDispersion P n / n := by
            field_simp [hepsilon.1.ne', hnreal.ne']
            <;> ring
      have htarget :
          4 / (N n : ℝ) ≤
            8 * c⁻¹ * kishDispersion P n / n := by
        calc
          4 / (N n : ℝ) ≤ 8 / (c * (n : ℝ)) := hfourN
          _ ≤ 8 * c⁻¹ * kishDispersion P n / n := by
            field_simp [hc.ne', hnreal.ne']
            nlinarith
      calc
        _ ≤ 8 * epsilon⁻¹ ^ 2 * kishDispersion P n / n +
            8 * c⁻¹ * kishDispersion P n / n :=
          add_le_add hcond htarget
        _ = regularCellVarianceConstant epsilon c *
            kishDispersion P n / n := by
          unfold regularCellVarianceConstant
          ring
    exact hraw.trans (hrawle.trans hbudget)
  refine ⟨hContrast, hReceipt, ?_⟩
  simpa only [regularCellReceiptMoment, crossAverage_eq_empirical, Gd] using
    hReceiptRaw.2

/-! ## R1.7b: square-integrability of the statistics Chebyshev is applied to -/

private lemma abs_targetEmpiricalMass_le_one
    {N : ℕ} (hN : 0 < N) (target : TargetSample 𝒳 N) (x : 𝒳) :
    |targetEmpiricalMass target x| ≤ 1 := by
  exact Causalean.Stat.abs_empiricalMass_le_one target x

/-- Under the regular finite-cell witness conditions, the weighted cross-sample average of a bounded measurable source score is square-integrable. -/
lemma regularCell_cross_memLp_for_witness
    (P : TransportedArray 𝒳) (N k : ℕ → ℕ)
    (c epsilon : ℝ) (n : ℕ)
    (hn : 0 < n) (hNpos : 0 < N n)
    (hIV : TransportedIVClass P N k c epsilon n)
    {m : ℕ} (hm : 0 < m) (cminus : ℝ) (hcminus : 0 < cminus)
    (cell : Fin m ↪ 𝒳)
    (hcell : ∀ i, MeasurableSet {cell i})
    (hrange : sourceXLaw P n (Set.range cell) = 1)
    (hmass : ∀ i : Fin m,
      cminus / (m : ℝ) ≤ sourceCellMass P n (cell i))
    (G : SourceObs 𝒳 → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hGmeas : Measurable G)
    (hGbound : ∀ᵐ o ∂sourceObsLaw P n, |G o| ≤ C) :
    MemLp
      (fun s : TwoSample 𝒳 n (N n) =>
        (n : ℝ)⁻¹ * ∑ r,
          (targetEmpiricalMass s.2 (s.1 r).1 /
            sourceCellMass P n (s.1 r).1) * G (s.1 r)) 2
      (twoSampleLaw P N n) := by
  classical
  letI : IsProbabilityMeasure (sourceObsLaw P n) :=
    hIV.twoSampleArray.2.1 n
  letI : IsProbabilityMeasure (sourceXLaw P n) := by
    unfold sourceXLaw
    exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  letI : IsProbabilityMeasure (targetXLaw P n) :=
    hIV.twoSampleArray.2.2.1 n
  letI : IsProbabilityMeasure (twoSampleLaw P N n) := by
    unfold twoSampleLaw
    infer_instance
  let μS := Measure.pi (fun _ : Fin n => sourceObsLaw P n)
  let μT := Measure.pi (fun _ : Fin (N n) => targetXLaw P n)
  have hAE :=
    weighted_cross_aestronglyMeasurable P N n cell hcell hrange G hGmeas
  have hrangeMeas : MeasurableSet (Set.range cell) := by
    rw [show Set.range cell = ⋃ i, {cell i} by
      ext x
      simp]
    exact MeasurableSet.iUnion hcell
  have hRangeObs : ∀ᵐ o ∂sourceObsLaw P n, o.1 ∈ Set.range cell := by
    have hx : ∀ᵐ x ∂sourceXLaw P n, x ∈ Set.range cell := by
      change Set.range cell ∈ ae (sourceXLaw P n)
      rw [mem_ae_iff]
      rw [measure_compl hrangeMeas (measure_ne_top _ _), hrange, measure_univ]
      simp
    unfold sourceXLaw at hx
    exact ae_of_ae_map measurable_fst.aemeasurable hx
  have hGoodObs : ∀ᵐ o ∂sourceObsLaw P n,
      o.1 ∈ Set.range cell ∧ |G o| ≤ C :=
    hRangeObs.and hGbound
  have hGoodSource :
      ∀ᵐ source ∂μS, ∀ r, (source r).1 ∈ Set.range cell ∧
        |G (source r)| ≤ C := by
    rw [ae_all_iff]
    intro r
    have hx : ∀ᵐ o ∂Measure.map
        (fun source : SourceSample 𝒳 n => source r) μS,
        o.1 ∈ Set.range cell ∧ |G o| ≤ C := by
      rw [(measurePreserving_eval
        (fun _ : Fin n => sourceObsLaw P n) r).map_eq]
      exact hGoodObs
    exact ae_of_ae_map (measurable_pi_apply r).aemeasurable hx
  have hGoodProd :
      ∀ᵐ s ∂μS.prod μT, ∀ r, (s.1 r).1 ∈ Set.range cell ∧
        |G (s.1 r)| ≤ C := by
    have hx : ∀ᵐ source ∂Measure.map
        (fun s : TwoSample 𝒳 n (N n) => s.1) (μS.prod μT),
        ∀ r, (source r).1 ∈ Set.range cell ∧ |G (source r)| ≤ C := by
      rw [(show MeasurePreserving
          (fun s : TwoSample 𝒳 n (N n) => s.1) (μS.prod μT) μS from
        measurePreserving_fst).map_eq]
      exact hGoodSource
    exact ae_of_ae_map measurable_fst.aemeasurable hx
  refine MemLp.of_bound hAE (C * (m : ℝ) / cminus) ?_
  unfold twoSampleLaw at hGoodProd ⊢
  filter_upwards [hGoodProd] with s hs
  rw [Real.norm_eq_abs]
  have hmreal : 0 < (m : ℝ) := by exact_mod_cast hm
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hcmreal : 0 < cminus / (m : ℝ) := div_pos hcminus hmreal
  calc
    |(n : ℝ)⁻¹ * ∑ r,
        (targetEmpiricalMass s.2 (s.1 r).1 /
          sourceCellMass P n (s.1 r).1) * G (s.1 r)| ≤
        (n : ℝ)⁻¹ * ∑ _r : Fin n, (m : ℝ) / cminus * C := by
      rw [abs_mul, abs_of_pos (inv_pos.mpr hnreal)]
      gcongr
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro r hr
      obtain ⟨i, hi⟩ := hs r |>.1
      have hq : cminus / (m : ℝ) ≤
          sourceCellMass P n ((s.1 r).1) := by
        rw [← hi]
        exact hmass i
      have hqpos : 0 < sourceCellMass P n ((s.1 r).1) :=
        hcmreal.trans_le hq
      rw [abs_mul, abs_div, abs_of_pos hqpos]
      calc
        |targetEmpiricalMass s.2 (s.1 r).1| /
              sourceCellMass P n (s.1 r).1 * |G (s.1 r)| ≤
            ((m : ℝ) / cminus) * C := by
          apply mul_le_mul
          · calc
              _ ≤ 1 / sourceCellMass P n (s.1 r).1 := by
                gcongr
                exact abs_targetEmpiricalMass_le_one hNpos _ _
              _ ≤ (m : ℝ) / cminus := by
                calc
                  1 / sourceCellMass P n (s.1 r).1 ≤
                      1 / (cminus / (m : ℝ)) :=
                    one_div_le_one_div_of_le hcmreal hq
                  _ = (m : ℝ) / cminus := by
                    field_simp [hcminus.ne', hmreal.ne']
          · exact (hs r).2
          · exact abs_nonneg _
          · positivity
        _ = (m : ℝ) / cminus * C := rfl
    _ = C * (m : ℝ) / cminus := by
      simp [hnreal.ne']
      ring

end CausalSmith.Stat.TransportedLateStrengthFrontier
