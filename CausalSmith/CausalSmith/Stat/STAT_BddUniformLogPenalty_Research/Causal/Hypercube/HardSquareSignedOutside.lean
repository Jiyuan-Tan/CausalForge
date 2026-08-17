import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Causal.Hypercube.HardSquareSignedSuccess

/-!
# Exact localization for signed hard-cell observations

This module complements the signed hard-cell KL estimate with exact equality
of the two raw observation measures away from the positive short-radius window.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace CausalSmith.Stat.BddUniformLogPenalty

/-- Enabling one hard-cell bit changes its raw signed-observation measure only
inside the positive short-radius window. -/
-- @node: causalHardCellSignedObservationMeasure_restrict_compl_enable_eq
lemma causalHardCellSignedObservationMeasure_restrict_compl_enable_eq
    {M : ℕ} (j : Fin M) {b cA delta w : ℝ}
    (centers : Fin M → Score) (omega : Fin M → Bool)
    (hbEq : b = 1 / 16) (hb : 0 < b) (hscale : 0 < cA * delta)
    (hcA : 8 ≤ cA) (hdelta : 0 < delta) (hdeltaSmall : delta ≤ 1 / 16)
    (hw : 0 < w) (hwHalf : w ≤ 1 / 2)
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
    (hcenter : centers j ∈ causalHardBottomEdge)
    (hcell : ∀ k, causalHardCell (centers k) w ⊆ causalHardSquare)
    (hj : omega j = false) :
    let omega' := Function.update omega j true
    let P := causalHardA1A2Law b cA delta w centers omega hb hscale hcA
      hdelta hw hsep hcell
    let P' := causalHardA1A2Law b cA delta w centers omega' hb hscale hcA
      hdelta hw hsep hcell
    (causalHardCellSignedObservationMeasure P (centers j) w).restrict
        {yd | ¬ (0 < yd.2 ∧ yd.2 < 2 * (cA * delta) / b)} =
      (causalHardCellSignedObservationMeasure P' (centers j) w).restrict
        {yd | ¬ (0 < yd.2 ∧ yd.2 < 2 * (cA * delta) / b)} := by
  dsimp only
  let omega' := Function.update omega j true
  let nu := (causalHardScoreMeasure b cA delta w centers omega).restrict
    (causalHardCell (centers j) w)
  let nu' := (causalHardScoreMeasure b cA delta w centers omega').restrict
    (causalHardCell (centers j) w)
  let p := causalHardObservedSuccessProfile delta w centers omega
  let p' := causalHardObservedSuccessProfile delta w centers omega'
  let q := fun x => max (1 / 4 : ℝ) (min (3 / 4 : ℝ) (p x))
  let q' := fun x => max (1 / 4 : ℝ) (min (3 / 4 : ℝ) (p' x))
  let stat := causalHardSignedStatistic (centers j)
  let E := Ioo 0 (2 * (cA * delta) / b)
  letI : IsProbabilityMeasure
      (causalHardScoreMeasure b cA delta w centers omega) :=
    causalHardScoreMeasure_isProbabilityMeasure centers omega hb hscale hcA
      hdelta hw hsep hcell
  letI : IsProbabilityMeasure
      (causalHardScoreMeasure b cA delta w centers omega') :=
    causalHardScoreMeasure_isProbabilityMeasure centers omega' hb hscale hcA
      hdelta hw hsep hcell
  have hp := causalHardObservedSuccessProfile_measurable delta w centers omega
  have hp' := causalHardObservedSuccessProfile_measurable delta w centers omega'
  have hq : Measurable q := measurable_const.max (measurable_const.min hp)
  have hq' : Measurable q' := measurable_const.max (measurable_const.min hp')
  have hq0 : ∀ x, (1 / 4 : ℝ) ≤ q x := fun x => le_max_left _ _
  have hq1 : ∀ x, q x ≤ (3 / 4 : ℝ) := by
    intro x
    exact max_le (by norm_num) (min_le_left _ _)
  have hq0' : ∀ x, (1 / 4 : ℝ) ≤ q' x := fun x => le_max_left _ _
  have hq1' : ∀ x, q' x ≤ (3 / 4 : ℝ) := by
    intro x
    exact max_le (by norm_num) (min_le_left _ _)
  have hqp : q =ᵐ[nu] p := by
    filter_upwards [ae_restrict_mem Metric.isClosed_closedBall.measurableSet] with x hx
    have hm := causalHardObservedSuccessProfile_mem_middleHalf hdelta.le hdeltaSmall
      hw hsep omega (hcell j hx)
    dsimp [q]
    rw [min_eq_right hm.2, max_eq_right hm.1]
  have hqp' : q' =ᵐ[nu'] p' := by
    filter_upwards [ae_restrict_mem Metric.isClosed_closedBall.measurableSet] with x hx
    have hm := causalHardObservedSuccessProfile_mem_middleHalf hdelta.le hdeltaSmall
      hw hsep omega' (hcell j hx)
    dsimp [q']
    rw [min_eq_right hm.2, max_eq_right hm.1]
  have hmap := causalHardScoreMeasure_restrict_map_signedStatistic_eq j centers
    omega omega' hb hscale hcA hdelta hw hwHalf hsep hcenter (hcell j)
  have hdiff : ∀ B : Set ℝ, MeasurableSet B →
      |(∫ x in {x | stat x ∈ B}, q x ∂nu) -
        ∫ x in {x | stat x ∈ B}, q' x ∂nu'| ≤
          delta * (Measure.map stat nu (B ∩ E)).toReal := by
    intro B hB
    have heq : (∫ x in {x | stat x ∈ B}, q x ∂nu) =
        ∫ x in {x | stat x ∈ B}, p x ∂nu := by
      apply integral_congr_ae
      exact ae_restrict_of_ae hqp
    have heq' : (∫ x in {x | stat x ∈ B}, q' x ∂nu') =
        ∫ x in {x | stat x ∈ B}, p' x ∂nu' := by
      apply integral_congr_ae
      exact ae_restrict_of_ae hqp'
    rw [heq, heq']
    exact causalHardSignedSuccess_localized_setwise_bound j centers omega hbEq hb
      hscale hcA hdelta hdeltaSmall hw hwHalf hsep hcenter (hcell j) hj hB
  have hout := statisticBernoulliOutcome_restrict_compl_eq_of_localized_success_bound
    nu nu' q q' stat hq hq' (causalHardSignedStatistic_measurable _)
    hq0 hq1 hq0' hq1' hmap hdelta.le measurableSet_Ioo hdiff
  have hk : commonStatisticBernoulliKernel q hq =ᵐ[nu]
      causalSelectedBernoulliKernel p hp := by
    filter_upwards [hqp] with x hx
    simp [commonStatisticBernoulliKernel, causalSelectedBernoulliKernel, hx]
  have hk' : commonStatisticBernoulliKernel q' hq' =ᵐ[nu']
      causalSelectedBernoulliKernel p' hp' := by
    filter_upwards [hqp'] with x hx
    simp [commonStatisticBernoulliKernel, causalSelectedBernoulliKernel, hx]
  letI : IsMarkovKernel (commonStatisticBernoulliKernel q hq) :=
    commonStatisticBernoulliKernel_isMarkovKernel q hq
      (fun x => by linarith [hq0 x]) (fun x => by linarith [hq1 x])
  letI : IsMarkovKernel (commonStatisticBernoulliKernel q' hq') :=
    commonStatisticBernoulliKernel_isMarkovKernel q' hq'
      (fun x => by linarith [hq0' x]) (fun x => by linarith [hq1' x])
  have hpunit : ∀ x, 0 ≤ p x ∧ p x ≤ 1 := by
    intro x
    have hprof := causalHardProfiles_mem_unitInterval delta w centers omega x
    dsimp [p, causalHardObservedSuccessProfile]
    split_ifs <;> simp_all
  have hpunit' : ∀ x, 0 ≤ p' x ∧ p' x ≤ 1 := by
    intro x
    have hprof := causalHardProfiles_mem_unitInterval delta w centers omega' x
    dsimp [p', causalHardObservedSuccessProfile]
    split_ifs <;> simp_all
  letI : IsMarkovKernel (causalSelectedBernoulliKernel p hp) :=
    causalSelectedBernoulliKernel_isMarkovKernel p hp
      (fun x => (hpunit x).1) (fun x => (hpunit x).2)
  letI : IsMarkovKernel (causalSelectedBernoulliKernel p' hp') :=
    causalSelectedBernoulliKernel_isMarkovKernel p' hp'
      (fun x => (hpunit' x).1) (fun x => (hpunit' x).2)
  rw [Measure.compProd_congr hk, Measure.compProd_congr hk'] at hout
  rw [← causalHardCellSignedObservationMeasure_eq_scoreBernoulli j b cA delta w
      centers omega hb hscale hcA hdelta hw hsep hcell,
    ← causalHardCellSignedObservationMeasure_eq_scoreBernoulli j b cA delta w
      centers omega' hb hscale hcA hdelta hw hsep hcell] at hout
  simpa [E] using hout

end CausalSmith.Stat.BddUniformLogPenalty
