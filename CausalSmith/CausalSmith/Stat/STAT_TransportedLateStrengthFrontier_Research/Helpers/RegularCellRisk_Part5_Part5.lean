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
import CausalSmith.Stat.STAT_TransportedLateStrengthFrontier_Research.Helpers.RegularCellRisk_Part5_Part1
import CausalSmith.Stat.STAT_TransportedLateStrengthFrontier_Research.Helpers.RegularCellRisk_Part5_Part2
import CausalSmith.Stat.STAT_TransportedLateStrengthFrontier_Research.Helpers.RegularCellRisk_Part5_Part3
import CausalSmith.Stat.STAT_TransportedLateStrengthFrontier_Research.Helpers.RegularCellRisk_Part5_Part4

namespace CausalSmith.Stat.TransportedLateStrengthFrontier

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology

variable {𝒳 : Type*} [MeasurableSpace 𝒳]
/-- The empirical first stage misses half its positive mean with probability
at most `4 B / t`, eventually and uniformly. -/
lemma regularCell_firstStage_bad_probability
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
      (twoSampleLaw P N n
        {s | transportedFirstStage P n / 2 <
          |regularCellReceiptMoment (sourceCellMass P n)
              (P.propensity n) s.1 s.2 -
            transportedFirstStage P n|}).toReal ≤
        4 * regularCellVarianceConstant epsilon c /
          effectiveStrength P n := by
  have hvar := regularCell_eventually_uniform_moment_variance
    (𝒳 := 𝒳) N k c epsilon cminus cplus hc hepsilon hcminus hcplus
      hN hkPos hkRoot
  have hnpos : ∀ᶠ n : ℕ in atTop, 0 < n :=
    eventually_atTop.2 ⟨1, fun n hn => Nat.zero_lt_of_lt hn⟩
  have hNratio :
      ∀ᶠ n : ℕ in atTop, c / 2 < (N n : ℝ) / (n : ℝ) :=
    (tendsto_order.1 hN).1 _ (by linarith)
  filter_upwards [hvar, hnpos, hNratio] with n hvarn hn hratio
  intro P hP
  classical
  rcases hP with
    ⟨hIV, hk, hcm, hcmOne, hcp, cell, hcell, hrange, hmass⟩
  have hPfull : RegularFiniteCellClass P N k c epsilon cminus cplus n :=
    ⟨hIV, hk, hcm, hcmOne, hcp, cell, hcell, hrange, hmass⟩
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
  have hAssignmentInt :
      Integrable (P.assignmentContrast n true) (sourceXLaw P n) :=
    integrable_of_finite_support (sourceXLaw P n) cell hcell hrange _
      (P.assignmentContrast_measurable n true).stronglyMeasurable
  have hReceiptInt :
      Integrable (P.receiptContrast n true) (sourceXLaw P n) :=
    integrable_of_finite_support (sourceXLaw P n) cell hcell hrange _
      (P.receiptContrast_measurable n true).stronglyMeasurable
  have hcompact := compact_causal_range P N k c epsilon n
    hAssignmentInt hReceiptInt hIV
  have hfirstEq :
      transportedFirstStage P n = targetComplierShare P n :=
    hcompact.2.2.2.1
  have htheta : targetCACE P n ∈ parameterSpace :=
    hcompact.2.2.2.2.2
  have hfirst : 0 < transportedFirstStage P n := by
    rw [hfirstEq]
    exact hIV.targetComplierPositivity
  have hmoment := hvarn P hPfull
  have hNpos : 0 < N n := by
    have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
    have : 0 < (N n : ℝ) / (n : ℝ) :=
      lt_trans (half_pos hc) hratio
    have hNreal : 0 < (N n : ℝ) := by
      rcases div_pos_iff.mp this with h | h
      · exact h.1
      · exact (not_lt_of_ge hnreal.le h.2).elim
    exact_mod_cast hNreal
  have hmem := (regularCell_moments_memLp
    P N k c epsilon cminus cplus (targetCACE P n) n hn hNpos
      hPfull htheta).2.1
  have hcheb := meas_ge_le_variance_div_sq hmem (half_pos hfirst)
  have hset :
      {s : TwoSample 𝒳 n (N n) |
        transportedFirstStage P n / 2 <
          |regularCellReceiptMoment (sourceCellMass P n)
              (P.propensity n) s.1 s.2 -
            transportedFirstStage P n|} ⊆
      {s |
        transportedFirstStage P n / 2 ≤
          |regularCellReceiptMoment (sourceCellMass P n)
              (P.propensity n) s.1 s.2 -
            ∫ t, regularCellReceiptMoment (sourceCellMass P n)
              (P.propensity n) t.1 t.2 ∂twoSampleLaw P N n|} := by
    intro s hs
    rw [hmoment.2.2]
    change transportedFirstStage P n / 2 <
      |regularCellReceiptMoment (sourceCellMass P n)
          (P.propensity n) s.1 s.2 - transportedFirstStage P n| at hs
    exact hs.le
  calc
    _ ≤ (twoSampleLaw P N n
        {s | transportedFirstStage P n / 2 ≤
          |regularCellReceiptMoment (sourceCellMass P n)
              (P.propensity n) s.1 s.2 -
            ∫ t, regularCellReceiptMoment (sourceCellMass P n)
              (P.propensity n) t.1 t.2 ∂twoSampleLaw P N n|}).toReal :=
      measureReal_mono hset
    _ ≤ (ENNReal.ofReal
        (variance
          (fun s : TwoSample 𝒳 n (N n) =>
            regularCellReceiptMoment (sourceCellMass P n)
              (P.propensity n) s.1 s.2)
          (twoSampleLaw P N n) /
            (transportedFirstStage P n / 2) ^ 2)).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hcheb
    _ = variance
          (fun s : TwoSample 𝒳 n (N n) =>
            regularCellReceiptMoment (sourceCellMass P n)
              (P.propensity n) s.1 s.2)
          (twoSampleLaw P N n) /
            (transportedFirstStage P n / 2) ^ 2 := by
      rw [ENNReal.toReal_ofReal]
      exact div_nonneg (variance_nonneg _ _) (sq_nonneg _)
    _ ≤ (regularCellVarianceConstant epsilon c *
          kishDispersion P n / n) /
            (transportedFirstStage P n / 2) ^ 2 := by
      gcongr
      exact hmoment.2.1
    _ = 4 * regularCellVarianceConstant epsilon c /
          effectiveStrength P n := by
      have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
      have hkappa := one_le_regularCell_kish
        P N k c epsilon n hIV cell hcell hrange
      have hkappaPos : 0 < kishDispersion P n :=
        lt_of_lt_of_le zero_lt_one hkappa
      unfold effectiveStrength
      field_simp [hnreal.ne', hfirst.ne', hkappaPos.ne']
      ring

/-- `Khat` has mean `1 + kappa`, bounded by `2 kappa`; the latter uses the
probability-density lower bound `kappa ≥ 1`. -/
lemma regularCell_Khat_mean
    (P : TransportedArray 𝒳) (N k : ℕ → ℕ)
    (c epsilon cminus cplus : ℝ) (n : ℕ)
    (hNtwo : 2 ≤ N n)
    (hP : RegularFiniteCellClass P N k c epsilon cminus cplus n) :
    (∫ target : TargetSample 𝒳 (N n),
        regularCellKhat (sourceCellMass P n) target
        ∂Measure.pi (fun _ : Fin (N n) => targetXLaw P n)) =
      1 + kishDispersion P n ∧
    1 + kishDispersion P n ≤ 2 * kishDispersion P n := by
  classical
  have hcoll := regularCell_collision_moments
    P N k c epsilon cminus cplus n hNtwo hP
  rcases hP with
    ⟨hIV, hk, hcm, hcmOne, hcp, cell, hcell, hrange, hmass⟩
  letI : IsProbabilityMeasure (sourceObsLaw P n) :=
    hIV.twoSampleArray.2.1 n
  letI : IsProbabilityMeasure (sourceXLaw P n) := by
    unfold sourceXLaw
    exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  letI : IsProbabilityMeasure (targetXLaw P n) :=
    hIV.twoSampleArray.2.2.1 n
  have hmem := collisionScale_memLp_for_witness
    P N k c epsilon n (lt_of_lt_of_le (by omega) hNtwo)
      hIV hk cminus hcm cell hcell hrange (fun i => (hmass i).1)
  constructor
  · unfold regularCellKhat
    rw [integral_add]
    · simp [hcoll.1]
    · exact integrable_const 1
    · exact hmem.integrable (by norm_num)
  · have hkappa := one_le_regularCell_kish
      P N k c epsilon n hIV cell hcell hrange
    linarith

end CausalSmith.Stat.TransportedLateStrengthFrontier
