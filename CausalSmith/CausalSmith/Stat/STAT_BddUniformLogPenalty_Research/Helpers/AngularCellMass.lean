import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Helpers.AngularDesign

/-!
# Common cell masses for the angular packing

This module proves that angular tilting does not change the mass of any
grid-centered half-disc.  It isolates the cell-mass part of the finite hard
family certificate from the later joint-law and KL arguments.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace CausalSmith.Stat.BddUniformLogPenalty

/-- The angular density integrates over a grid cell to the cell's Lebesgue
volume, independently of the packing vertex. -/
-- @node: packingAngularDensity_integral_gridCell
lemma packingAngularDensity_integral_gridCell {M : ℕ} (j : Fin M)
    {b cA delta w : ℝ} (hb : 0 < b) (hscale : 0 < cA * delta)
    (hw0 : 0 < w) (hw : w ≤ 1 / 4)
    (hsep : ∀ i k : Fin M, i ≠ k →
      3 * w ≤ dist (angularGridCenter M i) (angularGridCenter M k))
    (omega : Fin M → Bool) :
    (∫ x : Score in
      Metric.closedBall (angularGridCenter M j) w ∩ scoreCube (1 / 2),
      packingAngularDensity b cA delta w (angularGridCenter M) omega x) =
      (volume (Metric.closedBall (angularGridCenter M j) w ∩
        scoreCube (1 / 2))).toReal := by
  let C := Metric.closedBall (angularGridCenter M j) w ∩ scoreCube (1 / 2)
  let omega' : Fin M → Bool := fun k => if k = j then omega j else false
  have hpoint : ∀ x ∈ C,
      packingAngularDensity b cA delta w (angularGridCenter M) omega x =
        1 + if omega j then
          packingAngularTerm b cA delta w (angularGridCenter M j) x else 0 := by
    intro x hx
    rw [packingAngularDensity_eq_on_cell hw0 hsep
      (omega' := omega') (j := j) (by simp [omega']) hx.1]
    simp only [packingAngularDensity, omega']
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hkj
      simp [hkj]
    · simp
  rw [setIntegral_congr_fun (Metric.isClosed_closedBall.measurableSet.inter
    (scoreCube_measurableSet _)) hpoint]
  have hconst : IntegrableOn (fun _ : Score => (1 : ℝ)) C := by
    exact continuous_const.continuousOn.integrableOn_compact
      ((isCompact_closedBall (angularGridCenter M j) w).inter_right
        packingScoreCube_isCompact.isClosed)
  have hterm : IntegrableOn
      (fun x : Score => if omega j then
        packingAngularTerm b cA delta w (angularGridCenter M j) x else 0) C := by
    by_cases hj : omega j = true
    · simpa [hj] using
        ((packingAngularTerm_continuous hb hscale
          (angularGridCenter M j)).continuousOn.integrableOn_compact
            ((isCompact_closedBall (angularGridCenter M j) w).inter_right
              packingScoreCube_isCompact.isClosed) :
          IntegrableOn
            (packingAngularTerm b cA delta w (angularGridCenter M j)) C volume)
    · have hjf : omega j = false := Bool.eq_false_of_not_eq_true hj
      simpa [hjf] using
        (continuous_const.continuousOn.integrableOn_compact
          ((isCompact_closedBall (angularGridCenter M j) w).inter_right
            packingScoreCube_isCompact.isClosed) :
          IntegrableOn (fun _ : Score => (0 : ℝ)) C volume)
  rw [integral_add hconst hterm, integral_const]
  simp only [Measure.real, Measure.restrict_apply_univ, C]
  have hz : (∫ x : Score in C,
      if omega j then
        packingAngularTerm b cA delta w (angularGridCenter M j) x else 0) = 0 := by
    by_cases hj : omega j = true
    · simpa [C, hj] using
        (packingAngularTerm_integral_gridCell (b := b) (cA := cA)
          (delta := delta) j hw)
    · have hjf : omega j = false := Bool.eq_false_of_not_eq_true hj
      simp [hjf]
  rw [hz]
  simp

/-- Every angular design assigns a grid cell exactly its Lebesgue volume;
in particular, its mass is independent of the Boolean packing vertex. -/
-- @node: angularDesignMeasure_gridCell_eq_volume
lemma angularDesignMeasure_gridCell_eq_volume {M : ℕ} (j : Fin M)
    {b cA delta w : ℝ} (hb : 0 < b) (hscale : 0 < cA * delta)
    (hcA : 8 ≤ cA) (hdelta : 0 < delta) (hw0 : 0 < w)
    (hw : w ≤ 1 / 4)
    (hsep : ∀ i k : Fin M, i ≠ k →
      3 * w ≤ dist (angularGridCenter M i) (angularGridCenter M k))
    (omega : Fin M → Bool) :
    angularDesignMeasure b cA delta w (angularGridCenter M) omega
        (Metric.closedBall (angularGridCenter M j) w ∩ scoreCube (1 / 2)) =
      volume (Metric.closedBall (angularGridCenter M j) w ∩ scoreCube (1 / 2)) := by
  let C := Metric.closedBall (angularGridCenter M j) w ∩ scoreCube (1 / 2)
  have hC : MeasurableSet C :=
    Metric.isClosed_closedBall.measurableSet.inter (scoreCube_measurableSet _)
  rw [angularDesignMeasure, withDensity_apply _ hC]
  have hint : IntegrableOn
      (packingAngularDensity b cA delta w (angularGridCenter M) omega) C volume :=
    (packingAngularDensity_continuous hb hscale
      (angularGridCenter M) omega).continuousOn.integrableOn_compact
        ((isCompact_closedBall (angularGridCenter M j) w).inter_right
          packingScoreCube_isCompact.isClosed)
  have hnonneg : 0 ≤ᵐ[volume.restrict C]
      packingAngularDensity b cA delta w (angularGridCenter M) omega := by
    filter_upwards with x
    exact (packingAngularDensity_mem_Icc hcA hdelta hw0 hsep omega x).1.trans'
      (by norm_num)
  have heq : (fun x => ENNReal.ofReal
      (angularDesignDensity b cA delta w (angularGridCenter M) omega x)) =ᵐ[volume.restrict C]
      fun x => ENNReal.ofReal
        (packingAngularDensity b cA delta w (angularGridCenter M) omega x) := by
    filter_upwards [ae_restrict_mem hC] with x hx
    rw [angularDesignDensity_eq_on_square hx.2]
  rw [lintegral_congr_ae heq]
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnonneg]
  rw [show (∫ x : Score in C,
      packingAngularDensity b cA delta w (angularGridCenter M) omega x) =
        (volume C).toReal by
    exact packingAngularDensity_integral_gridCell j hb hscale hw0 hw hsep omega]
  exact ENNReal.ofReal_toReal
    (((isCompact_closedBall (angularGridCenter M j) w).inter_right
      packingScoreCube_isCompact.isClosed).measure_lt_top.ne)

end CausalSmith.Stat.BddUniformLogPenalty
