import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Helpers.AngularRadialOutcome

/-!
# Pointwise algebra for angular radial fibres

This module isolates the pointwise product identity behind the radial-outcome
cancellation.  It evaluates the regression and design density in the changed
cell before the later integral argument discards the purely angular terms.
-/

open Set

namespace CausalSmith.Stat.BddUniformLogPenalty

/-- Before the cutoff is fully active, the uncancelled radial success-mass
increment is exactly the bump amplitude times the complementary cutoff. -/
-- @node: angularRadialSuccessIncrement_identity
lemma angularRadialSuccessIncrement_identity
    {b cA delta w r : ℝ} (hb : 0 < b) (hscale : 0 < cA * delta)
    :
    delta * angularRadialProfile w r +
        (b * r * angularTilt b cA delta w r) / 2 =
      delta * angularRadialProfile w r *
        (1 - angularCutoff b cA delta r) := by
  by_cases hcut : angularCutoff b cA delta r = 0
  · rw [angularTilt, hcut]
    simp
  · have hbr : cA * delta < b * r := by
      by_contra h
      have hle : b * r ≤ cA * delta := le_of_not_gt h
      exact hcut (angularCutoff_eq_zero hscale hle)
    have hmax : max (b * r) (cA * delta) = b * r := max_eq_left hbr.le
    have hbr0 : b * r ≠ 0 := ne_of_gt (hscale.trans hbr)
    have hr0 : r ≠ 0 := by
      intro hrzero
      exact hbr0 (by simp [hrzero])
    rw [angularTilt, hmax]
    field_simp [hbr0, hr0]
    ring

/-- The uncancelled radial success-mass increment has absolute value at most
the bump amplitude.  This is the pointwise input to the exceptional-radius
Bernoulli KL estimate. -/
-- @node: angularRadialSuccessIncrement_abs_le
lemma angularRadialSuccessIncrement_abs_le
    {b cA delta w r : ℝ} (hb : 0 < b) (hscale : 0 < cA * delta)
    (hdelta : 0 ≤ delta) :
    |delta * angularRadialProfile w r +
        (b * r * angularTilt b cA delta w r) / 2| ≤ delta := by
  rw [angularRadialSuccessIncrement_identity hb hscale]
  have hp := angularRadialProfile_mem_Icc w r
  have hc := angularCutoff_mem_Icc b cA delta r
  have hcomp : 0 ≤ 1 - angularCutoff b cA delta r := sub_nonneg.mpr hc.2
  have hcomp1 : 1 - angularCutoff b cA delta r ≤ 1 := by linarith [hc.1]
  have hprod :
      angularRadialProfile w r * (1 - angularCutoff b cA delta r) ≤ 1 := by
    exact mul_le_one₀ hp.2 hcomp hcomp1
  rw [show delta * angularRadialProfile w r *
      (1 - angularCutoff b cA delta r) =
        delta * (angularRadialProfile w r *
          (1 - angularCutoff b cA delta r)) by ring,
    abs_of_nonneg (mul_nonneg hdelta (mul_nonneg hp.1 hcomp))]
  nlinarith [mul_nonneg hdelta
    (show 0 ≤ angularRadialProfile w r *
      (1 - angularCutoff b cA delta r) from mul_nonneg hp.1 hcomp)]

/-- Inside the changed cell, a true packing bit contributes exactly its radial
bump, while its flipped false bit contributes only the affine baseline. -/
-- @node: packingRegression_mul_density_flip_cell_identity
lemma packingRegression_mul_density_flip_cell_identity
    {M : ℕ} (j : Fin M) {b cA delta w : ℝ}
    (hw : 0 < w)
    (hsep : ∀ i k : Fin M, i ≠ k →
      3 * w ≤ dist (angularGridCenter M i) (angularGridCenter M k))
    (omega : Fin M → Bool) (hj : omega j = true) {x : Score}
    (hx : x ∈ Metric.closedBall (angularGridCenter M j) w) :
    packingRegression b delta w (angularGridCenter M) omega x *
          packingAngularDensity b cA delta w (angularGridCenter M) omega x -
        packingRegression b delta w (angularGridCenter M)
            (Causalean.Stat.flipBit j omega) x *
          packingAngularDensity b cA delta w (angularGridCenter M)
            (Causalean.Stat.flipBit j omega) x =
      localizedPackingBump delta w (angularGridCenter M j) x +
        (packingAffineBaseline b x +
            localizedPackingBump delta w (angularGridCenter M j) x) *
          packingAngularTerm b cA delta w (angularGridCenter M j) x := by
  have hfar : ∀ i : Fin M, i ≠ j →
      w ≤ dist x (angularGridCenter M i) := by
    intro i hij
    have htri : dist (angularGridCenter M i) (angularGridCenter M j) ≤
        dist (angularGridCenter M i) x +
          dist x (angularGridCenter M j) := dist_triangle _ _ _
    have hs := hsep i j hij
    rw [Metric.mem_closedBall] at hx
    rw [dist_comm (angularGridCenter M i) x] at htri
    linarith
  have hreg : packingRegression b delta w (angularGridCenter M) omega x =
      packingAffineBaseline b x +
        localizedPackingBump delta w (angularGridCenter M j) x := by
    unfold packingRegression
    rw [Finset.sum_eq_single j]
    · simp [hj]
    · intro i _ hij
      rw [localizedPackingBump_eq_zero_of_bandwidth_le_dist hw (hfar i hij)]
      simp
    · simp
  have hregFlip : packingRegression b delta w (angularGridCenter M)
      (Causalean.Stat.flipBit j omega) x = packingAffineBaseline b x := by
    unfold packingRegression
    rw [Finset.sum_eq_zero]
    · simp
    · intro i _
      by_cases hij : i = j
      · subst i
        simp [Causalean.Stat.flipBit, hj]
      · rw [localizedPackingBump_eq_zero_of_bandwidth_le_dist hw (hfar i hij)]
        simp
  have hdens : packingAngularDensity b cA delta w (angularGridCenter M) omega x =
      1 + packingAngularTerm b cA delta w (angularGridCenter M j) x := by
    unfold packingAngularDensity
    rw [Finset.sum_eq_single j]
    · simp [hj]
    · intro i _ hij
      rw [packingAngularTerm_eq_zero_of_bandwidth_le_dist hw (hfar i hij)]
      simp
    · simp
  have hdensFlip : packingAngularDensity b cA delta w (angularGridCenter M)
      (Causalean.Stat.flipBit j omega) x = 1 := by
    unfold packingAngularDensity
    rw [Finset.sum_eq_zero]
    · simp
    · intro i _
      by_cases hij : i = j
      · subst i
        simp [Causalean.Stat.flipBit, hj]
      · rw [packingAngularTerm_eq_zero_of_bandwidth_le_dist hw (hfar i hij)]
        simp
  rw [hreg, hregFlip, hdens, hdensFlip]
  ring

/-- The cell product identity in the radial-profile and direction-cosine
coordinates consumed by the polar cancellation lemmas. -/
-- @node: packingRegression_mul_density_flip_cell_radial_identity
lemma packingRegression_mul_density_flip_cell_radial_identity
    {M : ℕ} (j : Fin M) {b cA delta w : ℝ}
    (hw : 0 < w)
    (hsep : ∀ i k : Fin M, i ≠ k →
      3 * w ≤ dist (angularGridCenter M i) (angularGridCenter M k))
    (omega : Fin M → Bool) (hj : omega j = true) {x : Score}
    (hx : x ∈ Metric.closedBall (angularGridCenter M j) w) :
    packingRegression b delta w (angularGridCenter M) omega x *
          packingAngularDensity b cA delta w (angularGridCenter M) omega x -
        packingRegression b delta w (angularGridCenter M)
            (Causalean.Stat.flipBit j omega) x *
          packingAngularDensity b cA delta w (angularGridCenter M)
            (Causalean.Stat.flipBit j omega) x =
      delta * angularRadialProfile w (dist x (angularGridCenter M j)) +
        (packingAffineBaseline b x +
            delta * angularRadialProfile w (dist x (angularGridCenter M j))) *
          angularTilt b cA delta w (dist x (angularGridCenter M j)) *
          ((scoreCoordinates x - scoreCoordinates (angularGridCenter M j)).1 /
            dist x (angularGridCenter M j)) := by
  rw [packingRegression_mul_density_flip_cell_identity j hw hsep omega hj hx,
    localizedPackingBump_eq_delta_mul_angularRadialProfile]
  rw [packingAngularTerm, packingDirectionCos_eq_planarFirst_div_radius]
  rw [planarRadius_scoreCoordinates_sub]
  ring

end CausalSmith.Stat.BddUniformLogPenalty
