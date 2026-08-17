import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Causal.Hypercube.HardSquareSignedKL

/-!
# Quantitative signed-observation certificate for the hard square

This file specializes the common-statistic Bernoulli comparison to the
normalized hard-cell laws.  The first step identifies the signed-radius
marginal by angular cancellation on every measurable fibre.
-/

open MeasureTheory Set
open scoped ENNReal

namespace CausalSmith.Stat.BddUniformLogPenalty

/-- Every measurable signed-radius slice of a complete hard cell has its
uniform-background mass, independently of the active bit. -/
-- @node: causalHardScoreMeasure_signedSlice_eq_uniform
lemma causalHardScoreMeasure_signedSlice_eq_uniform
    {M : ℕ} (j : Fin M) {b cA delta w : ℝ}
    (centers : Fin M → Score) (omega : Fin M → Bool)
    (hb : 0 < b) (hscale : 0 < cA * delta) (hcA : 8 ≤ cA)
    (hdelta : 0 < delta) (hw : 0 < w) (hwHalf : w ≤ 1 / 2)
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
    (hcenter : centers j ∈ causalHardBottomEdge)
    (hcell : causalHardCell (centers j) w ⊆ causalHardSquare)
    {A : Set ℝ} (hA : MeasurableSet A) :
    causalHardScoreMeasure b cA delta w centers omega
        (causalHardCell (centers j) w ∩
          {x | causalHardSignedStatistic (centers j) x ∈ A}) =
      ENNReal.ofReal (1 / 36 : ℝ) *
        volume (causalHardCell (centers j) w ∩
          {x | causalHardSignedStatistic (centers j) x ∈ A}) := by
  let C : Set Score := causalHardCell (centers j) w ∩
    {x | causalHardSignedStatistic (centers j) x ∈ A}
  have hstat := causalHardSignedStatistic_measurable (centers j)
  have hC : MeasurableSet C :=
    Metric.isClosed_closedBall.measurableSet.inter (hA.preimage hstat)
  have hcompact : IsCompact (causalHardCell (centers j) w) :=
    isCompact_closedBall (centers j) w
  have hpoint : ∀ x ∈ C,
      packingAngularDensity b cA delta w centers omega x =
        1 + if omega j then
          packingAngularTerm b cA delta w (centers j) x else 0 := by
    intro x hx
    let omega' : Fin M → Bool := fun k => if k = j then omega j else false
    rw [packingAngularDensity_eq_on_cell hw hsep
      (omega' := omega') (j := j) (by simp [omega']) hx.1]
    simp only [packingAngularDensity, omega']
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hkj
      simp [hkj]
    · simp
  have hint : IntegrableOn
      (packingAngularDensity b cA delta w centers omega) C volume :=
    ((packingAngularDensity_continuous hb hscale centers omega).continuousOn.integrableOn_compact
      hcompact).mono_set inter_subset_left
  have hterm : IntegrableOn
      (fun x : Score => if omega j then
        packingAngularTerm b cA delta w (centers j) x else 0) C := by
    by_cases hj : omega j = true
    · simpa [hj] using
        (((packingAngularTerm_continuous hb hscale (centers j)).continuousOn.integrableOn_compact
          hcompact).mono_set inter_subset_left)
    · have hjf : omega j = false := Bool.eq_false_of_not_eq_true hj
      simpa [hjf] using (integrableOn_const : IntegrableOn (fun _ : Score => (0 : ℝ)) C)
  have hdensityIntegral :
      (∫ x in C, packingAngularDensity b cA delta w centers omega x) =
        (volume C).toReal := by
    rw [setIntegral_congr_fun hC hpoint]
    have hone : IntegrableOn (fun _ : Score => (1 : ℝ)) C :=
      (continuous_const.continuousOn.integrableOn_compact hcompact).mono_set
        inter_subset_left
    rw [integral_add hone hterm, integral_const]
    simp only [Measure.real, Measure.restrict_apply_univ]
    have hz : (∫ x in C, if omega j then
        packingAngularTerm b cA delta w (centers j) x else 0) = 0 := by
      by_cases hj : omega j = true
      · simpa [C, hj] using
          scoreCenter_causalHardSignedStatistic_angularTerm_integral_eq_zero
            hcenter b cA delta w hwHalf hA
      · have hjf : omega j = false := Bool.eq_false_of_not_eq_true hj
        simp [hjf]
    rw [hz, add_zero]
    simp
  unfold causalHardScoreMeasure
  rw [withDensity_apply _ hC]
  have hsquare : ∀ x ∈ C, x ∈ causalHardSquare :=
    fun x hx => hcell hx.1
  have heq : (fun x => ENNReal.ofReal (causalHardSquare.indicator
      (causalHardScoreDensity b cA delta w centers omega) x)) =ᵐ[volume.restrict C]
      fun x => ENNReal.ofReal ((1 / 36 : ℝ) *
        packingAngularDensity b cA delta w centers omega x) := by
    filter_upwards [ae_restrict_mem hC] with x hx
    rw [indicator_of_mem (hsquare x hx)]
    rfl
  rw [lintegral_congr_ae heq]
  have hnonneg : 0 ≤ᵐ[volume.restrict C]
      fun x => (1 / 36 : ℝ) *
        packingAngularDensity b cA delta w centers omega x := by
    filter_upwards with x
    exact mul_nonneg (by norm_num)
      ((packingAngularDensity_mem_Icc hcA hdelta hw hsep omega x).1.trans'
        (by norm_num))
  have hint' : IntegrableOn (fun x => (1 / 36 : ℝ) *
      packingAngularDensity b cA delta w centers omega x) C :=
    hint.const_mul (1 / 36 : ℝ)
  rw [← ofReal_integral_eq_lintegral_ofReal hint' hnonneg]
  rw [integral_const_mul, hdensityIntegral, ENNReal.ofReal_mul (by norm_num)]
  rw [ENNReal.ofReal_toReal (ne_of_lt
    ((measure_mono inter_subset_left).trans_lt hcompact.measure_lt_top))]

/-- The signed-radius marginal of the restricted score law is independent of
the hard-cell bit. -/
-- @node: causalHardScoreMeasure_restrict_map_signedStatistic_eq
lemma causalHardScoreMeasure_restrict_map_signedStatistic_eq
    {M : ℕ} (j : Fin M) {b cA delta w : ℝ}
    (centers : Fin M → Score) (omega omega' : Fin M → Bool)
    (hb : 0 < b) (hscale : 0 < cA * delta) (hcA : 8 ≤ cA)
    (hdelta : 0 < delta) (hw : 0 < w) (hwHalf : w ≤ 1 / 2)
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
    (hcenter : centers j ∈ causalHardBottomEdge)
    (hcell : causalHardCell (centers j) w ⊆ causalHardSquare) :
    Measure.map (causalHardSignedStatistic (centers j))
        ((causalHardScoreMeasure b cA delta w centers omega).restrict
          (causalHardCell (centers j) w)) =
      Measure.map (causalHardSignedStatistic (centers j))
        ((causalHardScoreMeasure b cA delta w centers omega').restrict
          (causalHardCell (centers j) w)) := by
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply (causalHardSignedStatistic_measurable _) hA,
    Measure.map_apply (causalHardSignedStatistic_measurable _) hA,
    Measure.restrict_apply (hA.preimage (causalHardSignedStatistic_measurable _)),
    Measure.restrict_apply (hA.preimage (causalHardSignedStatistic_measurable _))]
  have hset : causalHardSignedStatistic (centers j) ⁻¹' A ∩
      causalHardCell (centers j) w =
      causalHardCell (centers j) w ∩
        {x | causalHardSignedStatistic (centers j) x ∈ A} := by
    ext x
    simp [and_comm]
  rw [hset,
    causalHardScoreMeasure_signedSlice_eq_uniform j centers omega hb hscale
      hcA hdelta hw hwHalf hsep hcenter hcell hA,
    causalHardScoreMeasure_signedSlice_eq_uniform j centers omega' hb hscale
      hcA hdelta hw hwHalf hsep hcenter hcell hA]

/-- The positive short signed-radius interval in a complete hard cell has at
most its uniform-background disk mass. -/
-- @node: causalHardScoreMeasure_signedStatistic_Ioo_le
lemma causalHardScoreMeasure_signedStatistic_Ioo_le
    {M : ℕ} (j : Fin M) {b cA delta w R : ℝ}
    (centers : Fin M → Score) (omega : Fin M → Bool)
    (hb : 0 < b) (hscale : 0 < cA * delta) (hcA : 8 ≤ cA)
    (hdelta : 0 < delta) (hw : 0 < w) (hwHalf : w ≤ 1 / 2)
    (hR : 0 ≤ R)
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
    (hcenter : centers j ∈ causalHardBottomEdge)
    (hcell : causalHardCell (centers j) w ⊆ causalHardSquare) :
    Measure.map (causalHardSignedStatistic (centers j))
        ((causalHardScoreMeasure b cA delta w centers omega).restrict
          (causalHardCell (centers j) w)) (Ioo 0 R) ≤
      ENNReal.ofReal (Real.pi * R ^ 2 / 36) := by
  rw [Measure.map_apply (causalHardSignedStatistic_measurable _)
    measurableSet_Ioo]
  rw [Measure.restrict_apply
    (measurableSet_Ioo.preimage (causalHardSignedStatistic_measurable _))]
  have hset : causalHardSignedStatistic (centers j) ⁻¹' Ioo 0 R ∩
      causalHardCell (centers j) w =
      causalHardCell (centers j) w ∩
        {x | causalHardSignedStatistic (centers j) x ∈ Ioo 0 R} := by
    ext x
    simp [and_comm]
  rw [hset, causalHardScoreMeasure_signedSlice_eq_uniform j centers omega
    hb hscale hcA hdelta hw hwHalf hsep hcenter hcell measurableSet_Ioo]
  have hsubset : causalHardCell (centers j) w ∩
      {x | causalHardSignedStatistic (centers j) x ∈ Ioo 0 R} ⊆
      Metric.closedBall (centers j) R := by
    intro x hx
    have hsigned := causalHardSignedStatistic_eq_verticalSignedRadius_on_cell
      hcenter hwHalf hx.1
    rw [Metric.mem_closedBall]
    have hmem := hx.2
    change causalHardSignedStatistic (centers j) x ∈ Ioo 0 R at hmem
    rw [hsigned] at hmem
    split at hmem
    · exact hmem.2.le
    · linarith [show 0 ≤ dist x (centers j) from dist_nonneg, hmem.1]
  calc
    ENNReal.ofReal (1 / 36 : ℝ) *
        volume (causalHardCell (centers j) w ∩
          {x | causalHardSignedStatistic (centers j) x ∈ Ioo 0 R}) ≤
        ENNReal.ofReal (1 / 36 : ℝ) *
          volume (Metric.closedBall (centers j) R) :=
      mul_le_mul_right (measure_mono hsubset) _
    _ = ENNReal.ofReal (Real.pi * R ^ 2 / 36) := by
      rw [EuclideanSpace.volume_closedBall_fin_two, ← ENNReal.ofReal_pow hR,
        ← ENNReal.ofReal_mul (sq_nonneg R),
        ← ENNReal.ofReal_mul (by norm_num : 0 ≤ (1 / 36 : ℝ))]
      congr 1
      ring

end CausalSmith.Stat.BddUniformLogPenalty
