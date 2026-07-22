import CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.Collapse
import CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.Helpers.Frontier
import CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research.Helpers.FrontierSign
import Causalean.Stat.MEstimation.FinitePoissonSign
import Mathlib.Tactic.NormNum

/-! The nuisance-free global frontier and the distinct counterfactual-share PTT target. -/

open scoped BigOperators
open Causalean.Stat

set_option maxHeartbeats 1000000

namespace CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research

/-- The treated supported cells. -/
noncomputable def treatedCells (T : ℕ) (C : Finset (Cohort T)) : Finset (SupportedCell T C) :=
  Finset.univ.filter fun z => treatmentIndicator T z.1.1 z.2 = 1
  -- @realizes H(set of treated supported cells)

/-- Observed-population untreated baseline formed from period one and never-treated means. -/
noncomputable def observedCounterfactualBaseline (T : ℕ) (hT : 0 < T)
    (m : Cell T → ℝ) (g : Cohort T) (t : Fin T) : ℝ :=
  m (g, ⟨0, hT⟩) * m (⊤, t) / m (⊤, ⟨0, hT⟩)
  -- @realizes Bobs_gt(observed-data untreated mean proxy)

/-- The observed-population untreated baseline is unchanged when the panel horizon, observed
cell means, cohort, and period are replaced by equal values. -/
add_decl_doc observedCounterfactualBaseline.congr_simp

/-- The granular observed proportional effect. -/
noncomputable def granularTau (T : ℕ) (hT : 0 < T) (m : Cell T → ℝ)
    (g : Cohort T) (t : Fin T) : ℝ :=
  m (g, t) / observedCounterfactualBaseline T hT m g t - 1
  -- @realizes tau_gt(granular observed proportional effect)

/-- Counterfactual-share normalizing constant. -/
noncomputable def pttNormalizer (T : ℕ) (C : Finset (Cohort T)) (hT : 0 < T)
    (pi : Cohort T → OpenUnit) (m : Cell T → ℝ) : ℝ :=
  ∑ z ∈ treatedCells T C,
    limitingCellMass T pi z.1.1 * observedCounterfactualBaseline T hT m z.1.1 z.2
  -- @realizes Z(counterfactual-share normalizing constant)

/-- Counterfactual-share weight on a treated cell. -/
noncomputable def pttWeight (T : ℕ) (C : Finset (Cohort T)) (hT : 0 < T)
    (pi : Cohort T → OpenUnit) (m : Cell T → ℝ) (z : SupportedCell T C) : ℝ :=
  limitingCellMass T pi z.1.1 * observedCounterfactualBaseline T hT m z.1.1 z.2 /
    pttNormalizer T C hT pi m
  -- @realizes omega_gt(counterfactual-share weight on a treated cell)

/-- The counterfactual-share weight assigned to a supported cell is unchanged when the panel,
cohort support, shares, observed means, and cell are replaced by equal values. -/
add_decl_doc pttWeight.congr_simp

/-- The distinct counterfactual-share proportional treatment effect target. -/
noncomputable def counterfactualSharePTT (T : ℕ) (C : Finset (Cohort T)) (hT : 0 < T)
    (pi : Cohort T → OpenUnit) (m : Cell T → ℝ) : ℝ :=
  ∑ z ∈ treatedCells T C,
    pttWeight T C hT pi m z * granularTau T hT m z.1.1 z.2
  -- @realizes PTT(counterfactual-share proportional treatment effect on the treated)

/-- Four-period multiplier family used for the exact threshold calculation. -/
noncomputable def fourMultiplierEffects (x y : ℝ) (z : Cell 4) : ℝ :=
  if treatmentIndicator 4 z.1 z.2 = 1 then
    if z.1 = ((⟨1, by decide⟩ : Fin 4) : Cohort 4) ∧ z.2 = ⟨3, by decide⟩
    then Real.log y else Real.log x
  else 0

-- @node: thm:primitive-global-frontier
/-- Phi has exactly the sign of the pseudo-true beta and yields the stated PTT diagnosis. -/
theorem primitive_global_frontier (T : ℕ) (C : Finset (Cohort T))
    (hT : 0 < T) (hHorizon : ValidPanelHorizon T) -- @realizes T(standing 4 ≤ T premise)
    (hSupport : ValidCohortSupport T C) -- @realizes C(paper cohort-support premise)
    (Omega : ℕ → Type*) (P : ∀ N, SamplingLaw (Omega N))
    (Y : ∀ N, Fin N → Fin T → Fin 2 → Omega N → ℝ)
    (G : ∀ N, Fin N → Cohort T) (b : ∀ N, Fin N → PosReal)
    (pi : Cohort T → OpenUnit) (barB : Cohort T → PosReal)
    (gamma : Fin T → ℝ) (delta : Cell T → ℝ)
    (hGSupport : ∀ N i, G N i ∈ C) -- @realizes G_i(every deterministic label lies in C)
    (hShare : CohortShareLimit T C G pi)
    (hMean : UnitUntreatedExponentialMean T Omega P Y b gamma)
    (hBaseline : WithinCohortBaselineLimit T C G b barB)
    (hEffects : ProportionalEffects T Omega P Y G delta)
    (hRank : CollapsedDesignRank T C pi)
    (hScope : MulticohortFrontierScope T C)
    (hPositive : StrictPositiveEffects T C delta) :
    let Phi := frontierEliminationHandle T C pi barB gamma delta
    let m : Cell T → ℝ := fun z => observedCohortMean T barB gamma delta z.1 z.2
    (betaStar T C pi barB gamma delta < 0 ↔ Phi < 0) ∧
    (betaStar T C pi barB gamma delta = 0 ↔ Phi = 0) ∧
    (0 < betaStar T C pi barB gamma delta ↔ 0 < Phi) ∧
    ((restrictSignReversalPrimitive T C pi barB gamma delta ∈
      signReversalRegion T C gamma) ↔ Phi < 0) ∧
    (∀ x y : ℝ, 1 < x → 1 < y →
      frontierEliminationHandle 4 fourCohortSupport fourCohortShare
        fourCohortLimitBaseline fourCohortGamma (fourMultiplierEffects x y) =
          (5 * x ^ 2 + 12 * x - 2 * y - 15) / 16) ∧
    ((5 * ((101 : ℝ) / 100) ^ 2 + 12 * ((101 : ℝ) / 100) - 15) / 2 =
      (4441 : ℝ) / 4000) ∧
    frontierEliminationHandle 4 fourCohortSupport fourCohortShare
      fourCohortLimitBaseline fourCohortGamma fourCohortDelta = -(11559 : ℝ) / 32000 ∧
    (∀ z ∈ treatedCells T C,
      observedCounterfactualBaseline T hT m z.1.1 z.2 = untreatedMean T barB gamma z.1.1 z.2 ∧
      granularTau T hT m z.1.1 z.2 = Real.exp (delta (z.1.1, z.2)) - 1 ∧
      0 < pttWeight T C hT pi m z) ∧
    (∑ z ∈ treatedCells T C, pttWeight T C hT pi m z) = 1 ∧
    counterfactualSharePTT T C hT pi m =
      (∑ z ∈ treatedCells T C, limitingCellMass T pi z.1.1 * m (z.1.1, z.2)) /
        (∑ z ∈ treatedCells T C, limitingCellMass T pi z.1.1 *
          observedCounterfactualBaseline T hT m z.1.1 z.2) - 1 ∧
    (Phi < 0 → betaStar T C pi barB gamma delta < 0 ∧
      0 < counterfactualSharePTT T C hT pi m) := by
  dsimp only
  have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) hHorizon
  have hsign := betaStar_sign_frontierEliminationHandle T C hTpos hSupport.1
    pi barB gamma delta hRank
  have hDzero (g : Cohort T) (hg : g ∈ C) :
      treatmentIndicator T g ⟨0, hT⟩ = 0 := by
    induction g using WithTop.recTopCoe with
    | top => simp [treatmentIndicator, Causalean.Panel.AdoptionPath.absorbingTreatment_eq]
    | coe g =>
        have hg0 := hSupport.2 g hg
        rw [treatmentIndicator, Causalean.Panel.AdoptionPath.absorbingTreatment_eq]
        simp only [ite_eq_right_iff]
        intro hle
        have hle' : g ≤ (⟨0, hT⟩ : Fin T) := by simpa using hle
        have hval := Fin.le_iff_val_le_val.mp hle'
        have hzero : (⟨0, hT⟩ : Fin T).val = 0 := rfl
        have : g.val = 0 := Nat.eq_zero_of_le_zero (by simpa [hzero] using hval)
        exact (hg0 this).elim
  have hDtop (t : Fin T) : treatmentIndicator T ⊤ t = 0 := by
    simp [treatmentIndicator, Causalean.Panel.AdoptionPath.absorbingTreatment_eq]
  have hgamma0 : gamma ⟨0, hT⟩ = 0 := hMean.2 _ rfl
  have hbase (g : Cohort T) (hg : g ∈ C) (t : Fin T) :
      observedCounterfactualBaseline T hT
          (fun z => observedCohortMean T barB gamma delta z.1 z.2) g t =
        untreatedMean T barB gamma g t := by
    unfold observedCounterfactualBaseline observedCohortMean untreatedMean
    dsimp only
    rw [hDzero g hg, hDtop t, hDtop ⟨0, hT⟩, hgamma0]
    simp only [zero_mul, Real.exp_zero, mul_one]
    field_simp [ne_of_gt (barB ⊤).property]
  have htreated : (treatedCells T C).Nonempty := by
    obtain ⟨g, hgval, hgC⟩ := hScope.1
    let t : Fin T := ⟨1, by omega⟩
    have hD : treatmentIndicator T (g : Cohort T) t = 1 := by
      rw [treatmentIndicator, Causalean.Panel.AdoptionPath.absorbingTreatment_eq]
      have hle : (g : Cohort T) ≤ (t : Cohort T) := by
        simp only [WithTop.coe_le_coe]
        apply Fin.le_iff_val_le_val.mpr
        simp [t, hgval]
      simp [hle]
    refine ⟨(⟨(g : Cohort T), hgC⟩, t), ?_⟩
    simp [treatedCells, hD]
  have hnormalizer : 0 < pttNormalizer T C hT pi
      (fun z => observedCohortMean T barB gamma delta z.1 z.2) := by
    unfold pttNormalizer
    apply Finset.sum_pos'
    · intro z hz
      exact mul_nonneg
        (div_nonneg (pi z.1.1).property.1.le (by exact_mod_cast hTpos.le))
        (by rw [hbase z.1.1 z.1.2 z.2]; exact (mul_pos
          (barB z.1.1).property (Real.exp_pos _)).le)
    · obtain ⟨z, hz⟩ := htreated
      refine ⟨z, hz, mul_pos ?_ ?_⟩
      · exact div_pos (pi z.1.1).property.1 (by exact_mod_cast hTpos)
      · rw [hbase z.1.1 z.1.2 z.2]
        exact mul_pos (barB z.1.1).property (Real.exp_pos _)
  refine ⟨hsign.1, hsign.2.1, hsign.2.2, ?_, ?_, by norm_num, ?_, ?_, ?_, ?_, ?_⟩
  · constructor
    · intro hmem
      have hb := hmem.2.2.2.2.2.2.2
      rw [primitiveBetaStar_restrict] at hb
      exact hsign.1.mp hb
    · intro hPhi
      unfold signReversalRegion
      refine ⟨hHorizon, hSupport, hScope,
        cohortShareLimit_sum_eq_one T C G pi hGSupport hShare, ?_, ?_, ?_, ?_⟩
      · refine ⟨fun g => barB g.1, ?_⟩
        intro z
        rfl
      · intro z
        exact hPositive z.1.1.1 z.1.1.2 z.1.2 z.2
      · intro a ha
        rw [Fintype.sum_prod_type]
        change 0 < ∑ z : ↑C, ∑ t : Fin T, (pi z.1 : ℝ) / T *
          collapsedIndex T C (collapsedRegressor T C z.1 t) a ^ 2
        have hr := hRank a ha
        rw [show (∑ z : ↑C, ∑ t : Fin T,
            (pi z.1 : ℝ) / T *
              collapsedIndex T C (collapsedRegressor T C z.1 t) a ^ 2) =
            ∑ g ∈ C, ∑ t : Fin T, (pi g : ℝ) / T *
              collapsedIndex T C (collapsedRegressor T C g t) a ^ 2 by
          simpa using Finset.sum_attach (s := C) (f := fun g => ∑ t : Fin T,
            (pi g : ℝ) / T *
              collapsedIndex T C (collapsedRegressor T C g t) a ^ 2)]
        simpa [limitingCellMass] using hr
      · rw [primitiveBetaStar_restrict]
        exact hsign.1.mpr hPhi
  · intro x y hx hy
    simp [frontierEliminationHandle, primitiveTotal, primitiveTreatedTotal,
      primitiveRow, primitiveColumn, primitiveH, fourCohortSupport, fourCohortShare,
      fourCohortLimitBaseline, fourCohortGamma, fourMultiplierEffects,
      untreatedMean, treatmentIndicator,
      Causalean.Panel.AdoptionPath.absorbingTreatment_eq]
    norm_num [Fin.sum_univ_succ]
    simp [Real.exp_log (lt_trans zero_lt_one hx),
      Real.exp_log (lt_trans zero_lt_one hy)]
    ring
  · have hp := show frontierEliminationHandle 4 fourCohortSupport fourCohortShare
        fourCohortLimitBaseline fourCohortGamma
          (fourMultiplierEffects ((101 : ℝ) / 100) 4) =
        (5 * ((101 : ℝ) / 100) ^ 2 + 12 * ((101 : ℝ) / 100) - 2 * 4 - 15) / 16 by
      simp [frontierEliminationHandle, primitiveTotal, primitiveTreatedTotal,
        primitiveRow, primitiveColumn, primitiveH, fourCohortSupport, fourCohortShare,
        fourCohortLimitBaseline, fourCohortGamma, fourMultiplierEffects,
        untreatedMean, treatmentIndicator,
        Causalean.Panel.AdoptionPath.absorbingTreatment_eq]
      norm_num [Fin.sum_univ_succ]
      simp [Real.exp_log (by norm_num : (0 : ℝ) < 101 / 100),
        Real.exp_log (by norm_num : (0 : ℝ) < 4)]
      ring
    rw [show fourCohortDelta = fourMultiplierEffects ((101 : ℝ) / 100) 4 by
      funext z
      simp [fourCohortDelta, fourMultiplierEffects]]
    rw [hp]
    norm_num
  · intro z hz
    have hD : treatmentIndicator T z.1.1 z.2 = 1 :=
      (Finset.mem_filter.mp hz).2
    refine ⟨hbase z.1.1 z.1.2 z.2, ?_, ?_⟩
    · unfold granularTau
      rw [hbase z.1.1 z.1.2 z.2]
      unfold observedCohortMean
      dsimp only
      rw [hD, one_mul]
      have hB : untreatedMean T barB gamma z.1.1 z.2 ≠ 0 := by
        exact ne_of_gt (mul_pos (barB z.1.1).property (Real.exp_pos _))
      field_simp
    · unfold pttWeight
      exact div_pos (mul_pos
        (div_pos (pi z.1.1).property.1 (by exact_mod_cast hTpos))
        (by rw [hbase z.1.1 z.1.2 z.2]; exact
          mul_pos (barB z.1.1).property (Real.exp_pos _))) hnormalizer
  · unfold pttWeight
    rw [← Finset.sum_div]
    change pttNormalizer T C hT pi
      (fun z => observedCohortMean T barB gamma delta z.1 z.2) /
        pttNormalizer T C hT pi
          (fun z => observedCohortMean T barB gamma delta z.1 z.2) = 1
    exact div_self (ne_of_gt hnormalizer)
  · unfold counterfactualSharePTT pttWeight pttNormalizer granularTau
    have hZ : (∑ z ∈ treatedCells T C,
        limitingCellMass T pi z.1.1 *
          observedCounterfactualBaseline T hT
            (fun z => observedCohortMean T barB gamma delta z.1 z.2) z.1.1 z.2) ≠ 0 :=
      ne_of_gt hnormalizer
    rw [show (∑ z ∈ treatedCells T C,
        limitingCellMass T pi z.1.1 *
            observedCounterfactualBaseline T hT
              (fun z => observedCohortMean T barB gamma delta z.1 z.2) z.1.1 z.2 /
              (∑ w ∈ treatedCells T C, limitingCellMass T pi w.1.1 *
                observedCounterfactualBaseline T hT
                  (fun z => observedCohortMean T barB gamma delta z.1 z.2) w.1.1 w.2) *
          (observedCohortMean T barB gamma delta z.1.1 z.2 /
              observedCounterfactualBaseline T hT
                (fun z => observedCohortMean T barB gamma delta z.1 z.2) z.1.1 z.2 - 1)) =
        (∑ z ∈ treatedCells T C,
          (limitingCellMass T pi z.1.1 *
            observedCohortMean T barB gamma delta z.1.1 z.2 /
              (∑ w ∈ treatedCells T C, limitingCellMass T pi w.1.1 *
                observedCounterfactualBaseline T hT
                  (fun z => observedCohortMean T barB gamma delta z.1 z.2) w.1.1 w.2) -
           limitingCellMass T pi z.1.1 *
            observedCounterfactualBaseline T hT
              (fun z => observedCohortMean T barB gamma delta z.1 z.2) z.1.1 z.2 /
              (∑ w ∈ treatedCells T C, limitingCellMass T pi w.1.1 *
                observedCounterfactualBaseline T hT
                  (fun z => observedCohortMean T barB gamma delta z.1 z.2) w.1.1 w.2))) by
      apply Finset.sum_congr rfl
      intro z hz
      have hB : observedCounterfactualBaseline T hT
          (fun z => observedCohortMean T barB gamma delta z.1 z.2) z.1.1 z.2 ≠ 0 := by
        rw [hbase z.1.1 z.1.2 z.2]
        exact ne_of_gt (mul_pos (barB z.1.1).property (Real.exp_pos _))
      field_simp
      ]
    rw [Finset.sum_sub_distrib]
    rw [← Finset.sum_div, ← Finset.sum_div]
    rw [div_self hZ]
  · intro hPhi
    refine ⟨hsign.1.mpr hPhi, ?_⟩
    unfold counterfactualSharePTT
    apply Finset.sum_pos'
    · intro z hz
      have hD : treatmentIndicator T z.1.1 z.2 = 1 := (Finset.mem_filter.mp hz).2
      have hw : 0 < pttWeight T C hT pi
          (fun z => observedCohortMean T barB gamma delta z.1 z.2) z := by
        unfold pttWeight
        exact div_pos (mul_pos
          (div_pos (pi z.1.1).property.1 (by exact_mod_cast hTpos))
          (by rw [hbase z.1.1 z.1.2 z.2]; exact
            mul_pos (barB z.1.1).property (Real.exp_pos _))) hnormalizer
      have htau : 0 < granularTau T hT
          (fun z => observedCohortMean T barB gamma delta z.1 z.2) z.1.1 z.2 := by
        unfold granularTau
        rw [hbase z.1.1 z.1.2 z.2]
        unfold observedCohortMean
        dsimp only
        rw [hD, one_mul]
        have hd := hPositive z.1.1 z.1.2 z.2 hD
        have he : 1 < Real.exp (delta (z.1.1, z.2)) := by simpa using Real.exp_lt_exp.mpr hd
        have hB : untreatedMean T barB gamma z.1.1 z.2 ≠ 0 := by
          exact ne_of_gt (mul_pos (barB z.1.1).property (Real.exp_pos _))
        field_simp
        exact sub_pos.mpr he
      exact (mul_pos hw htau).le
    · obtain ⟨z, hz⟩ := htreated
      refine ⟨z, hz, ?_⟩
      have hD : treatmentIndicator T z.1.1 z.2 = 1 := (Finset.mem_filter.mp hz).2
      have hw : 0 < pttWeight T C hT pi
          (fun z => observedCohortMean T barB gamma delta z.1 z.2) z := by
        unfold pttWeight
        exact div_pos (mul_pos
          (div_pos (pi z.1.1).property.1 (by exact_mod_cast hTpos))
          (by rw [hbase z.1.1 z.1.2 z.2]; exact
            mul_pos (barB z.1.1).property (Real.exp_pos _))) hnormalizer
      have hd := hPositive z.1.1 z.1.2 z.2 hD
      have he : 1 < Real.exp (delta (z.1.1, z.2)) := by simpa using Real.exp_lt_exp.mpr hd
      unfold granularTau
      rw [hbase z.1.1 z.1.2 z.2]
      unfold observedCohortMean
      dsimp only
      rw [hD, one_mul]
      have hB : untreatedMean T barB gamma z.1.1 z.2 ≠ 0 := by
        exact ne_of_gt (mul_pos (barB z.1.1).property (Real.exp_pos _))
      field_simp
      exact mul_pos hw (sub_pos.mpr he)

end CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research
