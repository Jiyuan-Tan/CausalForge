import CausalSmith.Stat.STAT_SaPlmCumulantConverse_Research.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-!
# Degeneracy of the simultaneous bounded-outcome Gaussian intersection
-/

noncomputable section

open Set MeasureTheory ProbabilityTheory

namespace CausalSmith.Stat.SaPlmCumulantConverse

variable {Xspace : Type*} [MeasurableSpace Xspace]

/-- A bounded conditional-mean PLM with nondegenerate Gaussian treatment noise
cannot have a nonzero treatment coefficient. -/
lemma gaussianClass_theta_eq_zero (p : Parameters)
    (m : Model (Xspace := Xspace) p) (h : GaussianClass p p.n m) : m.theta0 = 0 := by
  have hXT : xTSigma (Xspace := Xspace) ≤
      (inferInstance : MeasurableSpace (Obs Xspace)) := by
    rw [xTSigma]
    exact Measurable.comap_le (show Measurable
      (fun o : Obs Xspace ↦ (o.1, o.2.1)) by fun_prop)
  have hq_int : Integrable (fun o : Obs Xspace ↦ m.q0 (covariate o)) m.P := by
    exact integrable_condExp.congr m.q0_condMean
  have hg_int : Integrable (fun o : Obs Xspace ↦ m.g0 (covariate o)) m.P := by
    exact integrable_condExp.congr m.g0_condMean
  have heta_int : Integrable (eta p m) m.P :=
    m.treatment_integrable.sub hg_int
  have hpair : Measurable[xTSigma (Xspace := Xspace)]
      (fun o : Obs Xspace ↦ (covariate o, treatment o)) := comap_measurable _
  have hq_meas : StronglyMeasurable[xTSigma (Xspace := Xspace)]
      (fun o : Obs Xspace ↦ m.q0 (covariate o)) := by
    apply Measurable.stronglyMeasurable
    have hproj : Measurable (fun xt : Xspace × ℝ ↦ m.q0 xt.1) :=
      m.q0_measurable.comp measurable_fst
    exact hproj.comp hpair
  have heta_meas : StronglyMeasurable[xTSigma (Xspace := Xspace)] (eta p m) := by
    apply Measurable.stronglyMeasurable
    change Measurable[xTSigma (Xspace := Xspace)]
      (fun o : Obs Xspace ↦ treatment o - m.g0 (covariate o))
    have hproj : Measurable (fun xt : Xspace × ℝ ↦ xt.2 - m.g0 xt.1) :=
      measurable_snd.sub (m.g0_measurable.comp measurable_fst)
    exact hproj.comp hpair
  have hthetaeta_int : Integrable (fun o ↦ m.theta0 * eta p m o) m.P :=
    heta_int.const_mul m.theta0
  have hthetaeta_meas : StronglyMeasurable[xTSigma (Xspace := Xspace)]
      (fun o ↦ m.theta0 * eta p m o) := heta_meas.const_mul _
  have hq_cond : (@condExp (Obs Xspace) ℝ (xTSigma (Xspace := Xspace))
      inferInstance _ _ m.P (fun o ↦ m.q0 (covariate o))) =ᵐ[m.P]
      (fun o ↦ m.q0 (covariate o)) := by
    exact Filter.Eventually.of_forall fun o ↦
      congrFun (condExp_of_stronglyMeasurable hXT hq_meas hq_int) o
  have heta_cond : (@condExp (Obs Xspace) ℝ (xTSigma (Xspace := Xspace))
      inferInstance _ _ m.P (fun o ↦ m.theta0 * eta p m o)) =ᵐ[m.P]
      (fun o ↦ m.theta0 * eta p m o) := by
    exact Filter.Eventually.of_forall fun o ↦
      congrFun (condExp_of_stronglyMeasurable hXT hthetaeta_meas hthetaeta_int) o
  have hsub1 := condExp_sub m.outcome_integrable hq_int
    (xTSigma (Xspace := Xspace))
  have hsub2 := condExp_sub (m.outcome_integrable.sub hq_int) hthetaeta_int
    (xTSigma (Xspace := Xspace))
  have hmean : (@condExp (Obs Xspace) ℝ (xTSigma (Xspace := Xspace))
      inferInstance _ _ m.P outcome) =ᵐ[m.P]
      (fun o ↦ m.q0 (covariate o) + m.theta0 * eta p m o) := by
    filter_upwards [h.outcomeMeanIndependence.2, hsub1, hsub2, hq_cond, heta_cond]
      with o hxi hs1 hs2 hq he
    simp only [Pi.sub_apply] at hs1 hs2
    change m.P[(fun o ↦ outcome o - m.q0 (covariate o) -
      m.theta0 * eta p m o) | xTSigma] o = 0 at hxi
    have hxs : m.P[(fun o ↦ outcome o - m.q0 (covariate o) -
        m.theta0 * eta p m o) | xTSigma] o =
        m.P[(fun o ↦ outcome o - m.q0 (covariate o)) | xTSigma] o -
          m.P[(fun o ↦ m.theta0 * eta p m o) | xTSigma] o := by
      exact hs2
    have hqs : m.P[(fun o ↦ outcome o - m.q0 (covariate o)) | xTSigma] o =
        m.P[outcome | xTSigma] o -
          m.P[(fun o ↦ m.q0 (covariate o)) | xTSigma] o := by
      exact hs1
    linarith
  have hy_lower : (fun _ : Obs Xspace ↦ -p.Cq) ≤ᵐ[m.P] outcome := by
    filter_upwards [h.boundedGaussianOutcome] with o ho
    exact neg_le_of_abs_le ho
  have hy_upper : outcome ≤ᵐ[m.P] (fun _ : Obs Xspace ↦ p.Cq) := by
    filter_upwards [h.boundedGaussianOutcome] with o ho
    exact le_of_abs_le ho
  have hconst_int : Integrable (fun _ : Obs Xspace ↦ p.Cq) m.P := integrable_const _
  have hnconst_int : Integrable (fun _ : Obs Xspace ↦ -p.Cq) m.P := integrable_const _
  have hcq_cond : (@condExp (Obs Xspace) ℝ (xTSigma (Xspace := Xspace))
      inferInstance _ _ m.P (fun _ ↦ p.Cq)) = (fun _ ↦ p.Cq) :=
    condExp_const hXT p.Cq
  have hncq_cond : (@condExp (Obs Xspace) ℝ (xTSigma (Xspace := Xspace))
      inferInstance _ _ m.P (fun _ ↦ -p.Cq)) = (fun _ ↦ -p.Cq) :=
    condExp_const hXT (-p.Cq)
  have hmean_lower := condExp_mono hnconst_int m.outcome_integrable hy_lower
    (m := xTSigma (Xspace := Xspace))
  have hmean_upper := condExp_mono m.outcome_integrable hconst_int hy_upper
    (m := xTSigma (Xspace := Xspace))
  have hlinear_bdd : ∀ᵐ o ∂m.P,
      |m.q0 (covariate o) + m.theta0 * eta p m o| ≤ p.Cq := by
    filter_upwards [hmean, hmean_lower, hmean_upper] with o hm hlo hhi
    rw [congrFun hncq_cond o] at hlo
    rw [congrFun hcq_cond o] at hhi
    have hm' : m.P[(fun o ↦ o.2.2) | xTSigma] o =
        m.q0 (covariate o) + m.theta0 * eta p m o := by
      exact hm
    rw [hm'] at hlo hhi
    exact abs_le.2 ⟨hlo, hhi⟩
  have hX : MeasurableSpace.comap covariate inferInstance ≤
      (inferInstance : MeasurableSpace (Obs Xspace)) := by
    exact Measurable.comap_le (measurable_fst :
      Measurable (fun o : Obs Xspace ↦ o.1))
  have hcq_cond_X : (@condExp (Obs Xspace) ℝ
      (MeasurableSpace.comap covariate inferInstance) inferInstance _ _ m.P
      (fun _ ↦ p.Cq)) = (fun _ ↦ p.Cq) := condExp_const hX p.Cq
  have hncq_cond_X : (@condExp (Obs Xspace) ℝ
      (MeasurableSpace.comap covariate inferInstance) inferInstance _ _ m.P
      (fun _ ↦ -p.Cq)) = (fun _ ↦ -p.Cq) := condExp_const hX (-p.Cq)
  have hq_lower := condExp_mono hnconst_int m.outcome_integrable hy_lower
    (m := MeasurableSpace.comap covariate inferInstance)
  have hq_upper := condExp_mono m.outcome_integrable hconst_int hy_upper
    (m := MeasurableSpace.comap covariate inferInstance)
  have hq_bdd : ∀ᵐ o ∂m.P, |m.q0 (covariate o)| ≤ p.Cq := by
    filter_upwards [m.q0_condMean, hq_lower, hq_upper] with o hqo hlo hhi
    rw [congrFun hncq_cond_X o] at hlo
    rw [congrFun hcq_cond_X o] at hhi
    have hqo' : m.P[(fun o ↦ o.2.2) |
        MeasurableSpace.comap covariate inferInstance] o = m.q0 (covariate o) := by
      exact hqo
    rw [hqo'] at hlo hhi
    exact abs_le.2 ⟨hlo, hhi⟩
  have hthetaeta_bdd : ∀ᵐ o ∂m.P,
      |m.theta0 * eta p m o| ≤ 2 * p.Cq := by
    filter_upwards [hlinear_bdd, hq_bdd] with o hlin hq
    calc
      |m.theta0 * eta p m o| =
          |(m.q0 (covariate o) + m.theta0 * eta p m o) - m.q0 (covariate o)| := by
            ring_nf
      _ ≤ |m.q0 (covariate o) + m.theta0 * eta p m o| +
          |m.q0 (covariate o)| := abs_sub _ _
      _ ≤ p.Cq + p.Cq := add_le_add hlin hq
      _ = 2 * p.Cq := by ring
  by_contra htheta
  have habs : 0 < |m.theta0| := abs_pos.2 htheta
  let B := 2 * p.Cq / |m.theta0|
  have heta_bdd : ∀ᵐ o ∂m.P, |eta p m o| ≤ B := by
    filter_upwards [hthetaeta_bdd] with o ho
    rw [show B = 2 * p.Cq / |m.theta0| by rfl]
    apply (le_div_iff₀ habs).2
    simpa [abs_mul, mul_comm] using ho
  have hprezero : m.P (eta p m ⁻¹' Ioi B) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [heta_bdd] with o ho
    simp only [mem_preimage, mem_Ioi, not_lt]
    exact le_trans (le_abs_self _) ho
  have heta_meas_full : Measurable (eta p m) := by
    change Measurable (fun o : Obs Xspace ↦ o.2.1 - m.g0 o.1)
    exact measurable_snd.fst.sub (m.g0_measurable.comp measurable_fst)
  have hgausszero : gaussianReal 0 ⟨p.sigma ^ 2, sq_nonneg p.sigma⟩ (Ioi B) = 0 := by
    rw [← h.gaussianTreatmentNoise,
      Measure.map_apply_of_aemeasurable heta_meas_full.aemeasurable measurableSet_Ioi]
    exact hprezero
  have hv : (⟨p.sigma ^ 2, sq_nonneg p.sigma⟩ : NNReal) ≠ 0 := by
    intro hv0
    have hsquare : p.sigma ^ 2 = 0 := congrArg (fun x : NNReal ↦ (x : ℝ)) hv0
    exact (pow_ne_zero 2 (ne_of_gt p.constants_pos.2.2.2.2.2.2)) hsquare
  have hvolzero : (volume : Measure ℝ) (Ioi B) = 0 :=
    (gaussianReal_absolutelyContinuous' 0 hv) hgausszero
  rw [Real.volume_Ioi] at hvolzero
  exact ENNReal.top_ne_zero hvolzero

/-- The generalized lower quantile of the identically zero loss is zero at
the paper's interior probability level. -/
lemma generalizedQuantile_zero (p : Parameters) (m : Model (Xspace := Xspace) p) :
    generalizedQuantile p p.n m (fun _ ↦ 0) = 0 := by
  have htau0 : 0 < 1 - p.gamma := sub_pos.mpr p.gamma_mem.2
  have htau1 : 1 - p.gamma < 1 :=
    sub_lt_self 1 (lt_trans (by norm_num) p.gamma_mem.1)
  have hiid : iidLaw m p.n Set.univ = 1 := by simp [iidLaw]
  have hmap : Measure.map (fun _ : Fin p.n → Obs Xspace ↦ (0 : ℝ)) (iidLaw m p.n) =
      Measure.dirac 0 := by
    rw [Measure.map_const]
    simp [hiid]
  change Causalean.Stat.quantile
    (Measure.map (fun _ : Fin p.n → Obs Xspace ↦ (0 : ℝ)) (iidLaw m p.n))
      (1 - p.gamma) = 0
  rw [hmap]
  apply le_antisymm
  · apply (Causalean.Stat.quantile_le_iff htau0 htau1).2
    rw [cdf_eq_real]
    simp [measureReal_def]
    exact le_of_lt (lt_trans (by norm_num) p.gamma_mem.1)
  · by_contra hnle
    have hlt : Causalean.Stat.quantile (Measure.dirac 0) (1 - p.gamma) < 0 :=
      lt_of_not_ge hnle
    have hcdf := (Causalean.Stat.quantile_le_iff htau0 htau1).1
      (show Causalean.Stat.quantile (Measure.dirac 0) (1 - p.gamma) ≤ _ from le_rfl)
    rw [cdf_eq_real] at hcdf
    simp [measureReal_def, hlt] at hcdf
    linarith [p.gamma_mem.2]

/-- [The simultaneous bounded-outcome Gaussian class is degenerate: every model in it has
treatment coefficient exactly zero, so for any supplied pair of treatment- and outcome-code
sequences that the class can match, both the minimax mean squared error and the minimax
generalized-quantile error over that class are exactly zero](goal) — the estimator that always
reports zero is perfect there.

The mechanism is a conflict between two of the class's requirements: a bounded outcome forces
the treatment term to be bounded, while Gaussian treatment noise has unbounded support, and the
only coefficient compatible with both is zero. The consequence is that no positive minimax
lower bound can come from this class, so a converse must be sought elsewhere. -/
-- @node: prop:bounded-outcome-gaussian-degeneracy
theorem bounded_outcome_gaussian_degeneracy (p : Parameters) :
    (∀ m : Model (Xspace := Xspace) p, GaussianClass p p.n m → m.theta0 = 0) ∧
    (∀ gcode qcode : ℕ → Xspace → ℝ,
      ({m : Model (Xspace := Xspace) p |
        GaussianClass p p.n m ∧
          barG p m p.n = clippedTreatmentCode p gcode p.n ∧
          barQ p m p.n = clippedOutcomeCode p qcode p.n}).Nonempty →
      minimaxRiskG p p.n gcode qcode = 0 ∧
      minimaxQuantileRiskG p p.n gcode qcode = 0) := by
  constructor
  · exact fun m hm ↦ gaussianClass_theta_eq_zero p m hm
  · intro gcode qcode _hne
    constructor
    · change minimaxRiskOn p p.n
        {m : Model (Xspace := Xspace) p |
          GaussianClass p p.n m ∧
            barG p m p.n = clippedTreatmentCode p gcode p.n ∧
            barQ p m p.n = clippedOutcomeCode p qcode p.n} = 0
      apply le_antisymm
      · calc
          minimaxRiskOn p p.n
              {m : Model (Xspace := Xspace) p |
                GaussianClass p p.n m ∧
                  barG p m p.n = clippedTreatmentCode p gcode p.n ∧
                  barQ p m p.n = clippedOutcomeCode p qcode p.n} ≤
              ⨆ m : Model (Xspace := Xspace) p,
                  ⨆ (_ : GaussianClass p p.n m ∧
                    barG p m p.n = clippedTreatmentCode p gcode p.n ∧
                    barQ p m p.n = clippedOutcomeCode p qcode p.n),
                  mseRisk m p.n (fun _ ↦ 0) := by
                    apply iInf_le_of_le ⟨(fun _ ↦ 0), measurable_const⟩
                    exact le_rfl
          _ = 0 := by
            apply le_antisymm
            · apply iSup_le
              intro m
              apply iSup_le
              intro hm
              simp [mseRisk, gaussianClass_theta_eq_zero p m hm.1]
            · exact bot_le
      · exact bot_le
    · change minimaxQuantileRiskGOn p p.n gcode qcode = 0
      apply le_antisymm
      · calc
          minimaxQuantileRiskGOn p p.n gcode qcode ≤
              ⨆ m : Model (Xspace := Xspace) p,
                ⨆ (_ : GaussianClass p p.n m ∧
                    barG p m p.n = clippedTreatmentCode p gcode p.n ∧
                    barQ p m p.n = clippedOutcomeCode p qcode p.n),
                  ENNReal.ofReal (generalizedQuantile p p.n m
                    (fun _ ↦ |(0 : ℝ) - m.theta0|)) := by
                      apply iInf_le_of_le ⟨(fun _ ↦ 0), measurable_const⟩
                      exact le_rfl
          _ = 0 := by
            apply le_antisymm
            · apply iSup_le
              intro m
              apply iSup_le
              intro hm
              rw [gaussianClass_theta_eq_zero p m hm.1]
              simp only [sub_zero, abs_zero]
              rw [generalizedQuantile_zero]
              simp
            · exact bot_le
      · exact bot_le

end CausalSmith.Stat.SaPlmCumulantConverse
