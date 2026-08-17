import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Helpers.BumpHolder
import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Helpers.AngularCoordinates
import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Helpers.Polar
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Angular density profile for the square packing

This file defines the smooth radial cutoff and cosine tilt used to perturb the
design density inside a packing cell.  It proves the cutoff identities, the
uniform tilt envelope, and the zero-mass polar cancellation.  The denominator
is clipped below by the cutoff scale; on the region where the cutoff is one it
is exactly the paper's `b r` denominator.
-/

open Set MeasureTheory

namespace CausalSmith.Stat.BddUniformLogPenalty

/-- Smooth cutoff which is zero when `b r ≤ cA δ` and one when
`2 cA δ ≤ b r`. -/
-- @node: angularCutoff
noncomputable def angularCutoff (b cA delta r : ℝ) : ℝ :=
  Real.smoothTransition (b * r / (cA * delta) - 1)

/-- The angular cutoff always takes values in the unit interval. -/
-- @node: angularCutoff_mem_Icc
lemma angularCutoff_mem_Icc (b cA delta r : ℝ) :
    angularCutoff b cA delta r ∈ Icc (0 : ℝ) 1 := by
  exact ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

/-- The angular cutoff vanishes below its inner radial threshold. -/
-- @node: angularCutoff_eq_zero
lemma angularCutoff_eq_zero {b cA delta r : ℝ} (hscale : 0 < cA * delta)
    (h : b * r ≤ cA * delta) : angularCutoff b cA delta r = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  rw [sub_nonpos, div_le_one hscale]
  exact h

/-- The angular cutoff equals one beyond twice its inner radial threshold. -/
-- @node: angularCutoff_eq_one
lemma angularCutoff_eq_one {b cA delta r : ℝ} (hscale : 0 < cA * delta)
    (h : 2 * (cA * delta) ≤ b * r) : angularCutoff b cA delta r = 1 := by
  apply Real.smoothTransition.one_of_one_le
  rw [le_sub_iff_add_le, ← two_mul, le_div_iff₀ hscale]
  simpa [two_mul] using h

/-- The cutoff is a continuous function of the radius. -/
-- @node: angularCutoff_continuous
lemma angularCutoff_continuous (b cA delta : ℝ) :
    Continuous (angularCutoff b cA delta) := by
  unfold angularCutoff
  fun_prop

/-- The radial bump profile appearing in the angular density correction. -/
-- @node: angularRadialProfile
noncomputable def angularRadialProfile (w r : ℝ) : ℝ :=
  packingBump (w⁻¹ • scorePoint r 0)

/-- The radial profile takes values in the unit interval. -/
-- @node: angularRadialProfile_mem_Icc
lemma angularRadialProfile_mem_Icc (w r : ℝ) :
    angularRadialProfile w r ∈ Icc (0 : ℝ) 1 := by
  exact packingBump_mem_Icc _

/-- A positive-bandwidth radial profile vanishes at every radius outside its
bandwidth. -/
-- @node: angularRadialProfile_eq_zero_of_bandwidth_le_abs
lemma angularRadialProfile_eq_zero_of_bandwidth_le_abs {w r : ℝ}
    (hw : 0 < w) (hr : w ≤ |r|) : angularRadialProfile w r = 0 := by
  apply packingBump_eq_zero_of_one_le_norm
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hw]
  have hnorm : ‖scorePoint r 0‖ = |r| := by
    rw [← dist_zero_right]
    rw [show (0 : Score) = scorePoint 0 0 by
      ext i
      fin_cases i <;> simp [scorePoint]]
    simpa using dist_scorePoint_same_second r 0 0
  rw [hnorm, inv_mul_eq_div, one_le_div hw]
  exact hr

/-- The radial profile is continuous. -/
-- @node: angularRadialProfile_continuous
lemma angularRadialProfile_continuous (w : ℝ) :
    Continuous (angularRadialProfile w) := by
  unfold angularRadialProfile
  apply packingBump_contDiff.continuous.comp
  apply Continuous.fun_const_smul
  unfold scorePoint
  apply (EuclideanSpace.equiv (Fin 2) ℝ).symm.continuous.comp
  apply continuous_pi
  intro i
  fin_cases i
  · exact continuous_id
  · exact continuous_const

/-- The scaled Euclidean bump used in the regression is exactly the radial
profile used in the angular cancellation formula. -/
-- @node: localizedPackingBump_eq_delta_mul_angularRadialProfile
lemma localizedPackingBump_eq_delta_mul_angularRadialProfile
    {delta w : ℝ} (center x : Score) :
    localizedPackingBump delta w center x =
      delta * angularRadialProfile w (dist x center) := by
  simpa [angularRadialProfile] using
    (localizedPackingBump_eq_delta_mul_radial (delta := delta) (w := w) center x)

/-- The clipped angular tilt.  Clipping only regularizes the denominator in
the transition region; once the cutoff is one this is exactly
`-2 δ φ(r/w) / (b r)`. -/
-- @node: angularTilt
noncomputable def angularTilt (b cA delta w r : ℝ) : ℝ :=
  -(2 * delta * angularRadialProfile w r * angularCutoff b cA delta r) /
    max (b * r) (cA * delta)

/-- The angular tilt is continuous in the radius at every positive cutoff
scale. -/
-- @node: angularTilt_continuous
lemma angularTilt_continuous {b cA delta w : ℝ} (hscale : 0 < cA * delta) :
    Continuous (angularTilt b cA delta w) := by
  unfold angularTilt
  apply Continuous.div
  · exact (((continuous_const.mul (angularRadialProfile_continuous w)).mul
      (angularCutoff_continuous b cA delta))).neg
  · exact (continuous_const.mul continuous_id).max continuous_const
  · intro r
    exact (lt_of_lt_of_le hscale (le_max_right _ _)).ne'

/-- At envelope parameter `cA`, the angular tilt has absolute value at most
`2/cA`. -/
-- @node: angularTilt_abs_le
lemma angularTilt_abs_le {b cA delta w r : ℝ} (hcA : 0 < cA)
    (hdelta : 0 < delta) : |angularTilt b cA delta w r| ≤ 2 / cA := by
  have hscale : 0 < cA * delta := mul_pos hcA hdelta
  have hden : 0 < max (b * r) (cA * delta) :=
    hscale.trans_le (le_max_right _ _)
  have hprofile := angularRadialProfile_mem_Icc w r
  have hcutoff := angularCutoff_mem_Icc b cA delta r
  have hprod :
      angularRadialProfile w r * angularCutoff b cA delta r ≤ 1 := by
    calc
      angularRadialProfile w r * angularCutoff b cA delta r ≤ 1 * 1 :=
        mul_le_mul hprofile.2 hcutoff.2 hcutoff.1 (by norm_num)
      _ = 1 := by ring
  rw [angularTilt, abs_div, abs_neg, abs_of_pos hden]
  have hnum :
      |2 * delta * angularRadialProfile w r * angularCutoff b cA delta r| ≤
        2 * delta := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_of_pos hdelta, abs_of_nonneg hprofile.1, abs_of_nonneg hcutoff.1]
    nlinarith
  calc
    _ ≤ (2 * delta) / max (b * r) (cA * delta) :=
      div_le_div_of_nonneg_right hnum hden.le
    _ ≤ (2 * delta) / (cA * delta) := by
      exact div_le_div_of_nonneg_left (by positivity) hscale
        (le_max_right _ _)
    _ = 2 / cA := by field_simp

/-- With the paper's choice `cA ≥ 8`, the density tilt is bounded by one
quarter. -/
-- @node: angularTilt_abs_le_quarter
lemma angularTilt_abs_le_quarter {b cA delta w r : ℝ} (hcA : 8 ≤ cA)
    (hdelta : 0 < delta) : |angularTilt b cA delta w r| ≤ 1 / 4 := by
  have hcA0 : 0 < cA := lt_of_lt_of_le (by norm_num) hcA
  exact (angularTilt_abs_le hcA0 hdelta).trans <| by
    rw [div_le_iff₀ hcA0]
    nlinarith

/-- The multiplicative density factor in polar coordinates. -/
-- @node: angularDensityFactor
noncomputable def angularDensityFactor
    (b cA delta w r theta : ℝ) : ℝ :=
  1 + angularTilt b cA delta w r * Real.cos theta

/-- The paper's choice `cA ≥ 8` keeps the angular density factor in
`[3/4, 5/4]`, uniformly over radius and angle. -/
-- @node: angularDensityFactor_mem_Icc
lemma angularDensityFactor_mem_Icc {b cA delta w r theta : ℝ}
    (hcA : 8 ≤ cA) (hdelta : 0 < delta) :
    angularDensityFactor b cA delta w r theta ∈
      Icc (3 / 4 : ℝ) (5 / 4 : ℝ) := by
  have htilt := angularTilt_abs_le_quarter (b := b) (w := w) (r := r) hcA hdelta
  have hcos : |Real.cos theta| ≤ (1 : ℝ) :=
    abs_le.mpr ⟨Real.neg_one_le_cos theta, Real.cos_le_one theta⟩
  have hprod :
      |angularTilt b cA delta w r * Real.cos theta| ≤ (1 / 4 : ℝ) := by
    rw [abs_mul]
    calc
      |angularTilt b cA delta w r| * |Real.cos theta| ≤ (1 / 4) * 1 :=
        mul_le_mul htilt hcos (abs_nonneg _) (by norm_num)
      _ = 1 / 4 := by ring
  rw [abs_le] at hprod
  constructor <;> unfold angularDensityFactor <;> linarith

/-- In particular, every angular density factor is strictly positive. -/
-- @node: angularDensityFactor_pos
lemma angularDensityFactor_pos {b cA delta w r theta : ℝ}
    (hcA : 8 ≤ cA) (hdelta : 0 < delta) :
    0 < angularDensityFactor b cA delta w r theta := by
  have h := angularDensityFactor_mem_Icc (b := b) (w := w) (r := r)
    (theta := theta) hcA hdelta
  exact (by norm_num : (0 : ℝ) < 3 / 4).trans_le h.1

/-- The cosine of the polar direction around a packing center, with the value
at the center fixed to zero.  This coordinate formula avoids choosing a
global angle on the score plane. -/
-- @node: packingDirectionCos
noncomputable def packingDirectionCos (center x : Score) : ℝ :=
  if dist x center = 0 then 0 else (x 0 - center 0) / dist x center

/-- The coordinate direction cosine has absolute value at most one. -/
-- @node: packingDirectionCos_abs_le_one
lemma packingDirectionCos_abs_le_one (center x : Score) :
    |packingDirectionCos center x| ≤ 1 := by
  by_cases hdist : dist x center = 0
  · simp [packingDirectionCos, hdist]
  · rw [packingDirectionCos, if_neg hdist, abs_div]
    have hcoord : |x 0 - center 0| ≤ dist x center := by
      simpa [dist_eq_norm, Real.norm_eq_abs] using
        (PiLp.norm_apply_le (x - center) (0 : Fin 2))
    rw [abs_of_nonneg dist_nonneg]
    exact (div_le_one (lt_of_le_of_ne dist_nonneg (Ne.symm hdist))).2 hcoord

/-- One center's signed angular correction to the design density. -/
-- @node: packingAngularTerm
noncomputable def packingAngularTerm
    (b cA delta w : ℝ) (center x : Score) : ℝ :=
  angularTilt b cA delta w (dist x center) * packingDirectionCos center x

/-- The cutoff removes the apparent directional singularity at the center,
so each angular correction is continuous on the whole score plane. -/
-- @node: packingAngularTerm_continuous
lemma packingAngularTerm_continuous {b cA delta w : ℝ} (hb : 0 < b)
    (hscale : 0 < cA * delta) (center : Score) :
    Continuous (packingAngularTerm b cA delta w center) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = center
  · subst x
    have hR : 0 < (cA * delta) / b := div_pos hscale hb
    have hevent : ∀ᶠ y in nhds center, dist y center < (cA * delta) / b :=
      (continuousAt_id.dist continuousAt_const).eventually_lt continuousAt_const
        (by simpa)
    have heq : packingAngularTerm b cA delta w center =ᶠ[nhds center]
        (fun _ => 0) := by
      filter_upwards [hevent] with y hy
      rw [packingAngularTerm, angularTilt, angularCutoff_eq_zero hscale]
      · simp
      · simpa [mul_comm] using ((lt_div_iff₀ hb).mp hy).le
    exact continuousAt_const.congr_of_eventuallyEq heq
  · have hdist : dist x center ≠ 0 := by
      simpa [dist_eq_zero] using hx
    have hevent : ∀ᶠ y in nhds x, dist y center ≠ 0 :=
      (continuousAt_id.dist continuousAt_const).eventually_ne hdist
    have htilt : ContinuousAt
        (fun y : Score => angularTilt b cA delta w (dist y center)) x :=
      (angularTilt_continuous hscale).continuousAt.comp'
        (continuousAt_id.dist continuousAt_const)
    have hcoord : ContinuousAt (fun y : Score => y 0 - center 0) x := by
      fun_prop
    have hraw : ContinuousAt
        (fun y : Score => angularTilt b cA delta w (dist y center) *
          ((y 0 - center 0) / dist y center)) x := by
      exact htilt.mul
        (hcoord.div (continuousAt_id.dist continuousAt_const) hdist)
    apply hraw.congr_of_eventuallyEq
    filter_upwards [hevent] with y hy
    simp [packingAngularTerm, packingDirectionCos, hy]

/-- Each active angular correction is uniformly bounded by one quarter. -/
-- @node: packingAngularTerm_abs_le_quarter
lemma packingAngularTerm_abs_le_quarter {b cA delta w : ℝ}
    (hcA : 8 ≤ cA) (hdelta : 0 < delta) (center x : Score) :
    |packingAngularTerm b cA delta w center x| ≤ 1 / 4 := by
  rw [packingAngularTerm, abs_mul]
  calc
    |angularTilt b cA delta w (dist x center)| * |packingDirectionCos center x| ≤
        (1 / 4 : ℝ) * 1 :=
      mul_le_mul (angularTilt_abs_le_quarter hcA hdelta)
        (packingDirectionCos_abs_le_one center x) (abs_nonneg _) (by norm_num)
    _ = 1 / 4 := by ring

/-- A center contributes no angular density correction outside its packing
bandwidth. -/
-- @node: packingAngularTerm_eq_zero_of_bandwidth_le_dist
lemma packingAngularTerm_eq_zero_of_bandwidth_le_dist {b cA delta w : ℝ}
    {center x : Score} (hw : 0 < w) (hx : w ≤ dist x center) :
    packingAngularTerm b cA delta w center x = 0 := by
  rw [packingAngularTerm, angularTilt,
    angularRadialProfile_eq_zero_of_bandwidth_le_abs hw (by simpa using hx)]
  simp

/-- The design density obtained by summing the active disjoint angular
corrections over the packing grid. -/
-- @node: packingAngularDensity
noncomputable def packingAngularDensity {M : ℕ} (b cA delta w : ℝ)
    (centers : Fin M → Score) (omega : Fin M → Bool) (x : Score) : ℝ :=
  1 + ∑ j, if omega j then packingAngularTerm b cA delta w (centers j) x else 0

/-- The finite angularly tilted design density is continuous. -/
-- @node: packingAngularDensity_continuous
lemma packingAngularDensity_continuous {M : ℕ} {b cA delta w : ℝ}
    (hb : 0 < b) (hscale : 0 < cA * delta) (centers : Fin M → Score)
    (omega : Fin M → Bool) :
    Continuous (packingAngularDensity b cA delta w centers omega) := by
  unfold packingAngularDensity
  apply continuous_const.add
  apply continuous_finset_sum
  intro j _
  by_cases hj : omega j = true
  · simpa [hj] using packingAngularTerm_continuous hb hscale (centers j)
  · have hjf : omega j = false := Bool.eq_false_of_not_eq_true hj
    simpa [hjf] using (continuous_const : Continuous (fun _ : Score => (0 : ℝ)))

/-- The finite angularly tilted design density is Borel measurable. -/
-- @node: packingAngularDensity_measurable
lemma packingAngularDensity_measurable {M : ℕ} {b cA delta w : ℝ}
    (hb : 0 < b) (hscale : 0 < cA * delta) (centers : Fin M → Score)
    (omega : Fin M → Bool) :
    Measurable (packingAngularDensity b cA delta w centers omega) :=
  (packingAngularDensity_continuous hb hscale centers omega).measurable

/-- Three-bandwidth separation ensures that at most one angular correction is
nonzero at any score point, so summing the family does not enlarge its
pointwise envelope. -/
-- @node: packingAngularDensity_sum_abs_le_quarter
lemma packingAngularDensity_sum_abs_le_quarter {M : ℕ} {b cA delta w : ℝ}
    (hcA : 8 ≤ cA) (hdelta : 0 < delta) (hw : 0 < w)
    {centers : Fin M → Score}
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
    (omega : Fin M → Bool) (x : Score) :
    |∑ j, if omega j then packingAngularTerm b cA delta w (centers j) x else 0| ≤
      1 / 4 := by
  by_cases hex : ∃ j, omega j = true ∧
      packingAngularTerm b cA delta w (centers j) x ≠ 0
  · obtain ⟨j, hjbit, hjne⟩ := hex
    rw [Finset.sum_eq_single j]
    · simp only [hjbit, if_true]
      exact packingAngularTerm_abs_le_quarter hcA hdelta (centers j) x
    · intro i _ hij
      have hzero : packingAngularTerm b cA delta w (centers i) x = 0 := by
        by_contra hine
        have hxi : dist x (centers i) < w := by
          apply lt_of_not_ge
          intro hfar
          exact hine (packingAngularTerm_eq_zero_of_bandwidth_le_dist hw hfar)
        have hxj : dist x (centers j) < w := by
          apply lt_of_not_ge
          intro hfar
          exact hjne (packingAngularTerm_eq_zero_of_bandwidth_le_dist hw hfar)
        have htri : dist (centers i) (centers j) ≤
            dist (centers i) x + dist x (centers j) := dist_triangle _ _ _
        have hs := hsep i j hij
        rw [dist_comm (centers i) x] at htri
        linarith
      simp [hzero]
    · simp
  · have hzero : ∀ j : Fin M,
        (if omega j then packingAngularTerm b cA delta w (centers j) x else 0) = 0 := by
      intro j
      by_cases hj : omega j = true
      · simp only [hj, if_true]
        by_contra hjne
        exact hex ⟨j, hj, hjne⟩
      · have hjfalse : omega j = false := Bool.eq_false_of_not_eq_true hj
        simp [hjfalse]
    rw [Finset.sum_eq_zero fun j _ => hzero j, abs_zero]
    norm_num

/-- The angularly tilted design density remains in the paper's uniform
density envelope. -/
-- @node: packingAngularDensity_mem_Icc
lemma packingAngularDensity_mem_Icc {M : ℕ} {b cA delta w : ℝ}
    (hcA : 8 ≤ cA) (hdelta : 0 < delta) (hw : 0 < w)
    {centers : Fin M → Score}
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
    (omega : Fin M → Bool) (x : Score) :
    packingAngularDensity b cA delta w centers omega x ∈
      Icc (3 / 4 : ℝ) (5 / 4 : ℝ) := by
  have hsum := packingAngularDensity_sum_abs_le_quarter (b := b)
    hcA hdelta hw hsep omega x
  rw [abs_le] at hsum
  unfold packingAngularDensity
  constructor <;> linarith

/-- Inside one closed packing ball, the angular density depends on the bit
vector only through that ball's coordinate. -/
-- @node: packingAngularDensity_eq_on_cell
lemma packingAngularDensity_eq_on_cell {M : ℕ} {b cA delta w : ℝ}
    (hw : 0 < w) {centers : Fin M → Score}
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
    {omega omega' : Fin M → Bool} {j : Fin M} (hbit : omega j = omega' j)
    {x : Score} (hx : x ∈ Metric.closedBall (centers j) w) :
    packingAngularDensity b cA delta w centers omega x =
      packingAngularDensity b cA delta w centers omega' x := by
  unfold packingAngularDensity
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases hij : i = j
  · subst i
    rw [hbit]
  · have hfar : w ≤ dist x (centers i) := by
      have htri : dist (centers i) (centers j) ≤
          dist (centers i) x + dist x (centers j) := dist_triangle _ _ _
      have hs := hsep i j hij
      rw [Metric.mem_closedBall] at hx
      rw [dist_comm (centers i) x] at htri
      linarith
    rw [packingAngularTerm_eq_zero_of_bandwidth_le_dist hw hfar]
    simp

/-- Away from every closed packing ball, all angular corrections vanish and
the design density is the common unit baseline. -/
-- @node: packingAngularDensity_eq_one_off_cells
lemma packingAngularDensity_eq_one_off_cells {M : ℕ} {b cA delta w : ℝ}
    (hw : 0 < w) {centers : Fin M → Score} (omega : Fin M → Bool)
    {x : Score} (hx : ∀ j, x ∉ Metric.closedBall (centers j) w) :
    packingAngularDensity b cA delta w centers omega x = 1 := by
  unfold packingAngularDensity
  rw [Finset.sum_eq_zero]
  · simp
  · intro j _
    have hfar : w ≤ dist x (centers j) := by
      have hlt : w < dist x (centers j) := by
        simpa [Metric.mem_closedBall, not_le] using hx j
      exact hlt.le
    rw [packingAngularTerm_eq_zero_of_bandwidth_le_dist hw hfar]
    simp

/-- Below the inner cutoff radius the angular tilt vanishes identically. -/
-- @node: angularTilt_eq_zero_of_le
lemma angularTilt_eq_zero_of_le {b cA delta w r : ℝ}
    (hscale : 0 < cA * delta) (h : b * r ≤ cA * delta) :
    angularTilt b cA delta w r = 0 := by
  rw [angularTilt, angularCutoff_eq_zero hscale h]
  simp

/-- Beyond twice the cutoff radius the clipped tilt agrees with the paper's
unclipped cancellation formula. -/
-- @node: angularTilt_eq_formula
lemma angularTilt_eq_formula {b cA delta w r : ℝ}
    (hscale : 0 < cA * delta) (h : 2 * (cA * delta) ≤ b * r) :
    angularTilt b cA delta w r =
      -(2 * delta * angularRadialProfile w r) / (b * r) := by
  have hmax : max (b * r) (cA * delta) = b * r := by
    rw [max_eq_left]
    linarith
  rw [angularTilt, angularCutoff_eq_one hscale h, hmax]
  ring

/-- Outside the bump bandwidth the angular density perturbation vanishes. -/
-- @node: angularTilt_eq_zero_of_bandwidth_le_abs
lemma angularTilt_eq_zero_of_bandwidth_le_abs {b cA delta w r : ℝ}
    (hw : 0 < w) (hr : w ≤ |r|) : angularTilt b cA delta w r = 0 := by
  rw [angularTilt, angularRadialProfile_eq_zero_of_bandwidth_le_abs hw hr]
  simp

/-- Outside the bump bandwidth the perturbed polar density factor is exactly
the common baseline density. -/
-- @node: angularDensityFactor_eq_one_of_bandwidth_le_abs
lemma angularDensityFactor_eq_one_of_bandwidth_le_abs {b cA delta w r theta : ℝ}
    (hw : 0 < w) (hr : w ≤ |r|) :
    angularDensityFactor b cA delta w r theta = 1 := by
  rw [angularDensityFactor, angularTilt_eq_zero_of_bandwidth_le_abs hw hr]
  simp

/-- Once the cutoff is fully active, the radial bump contribution and the
affine-times-angular contribution cancel after integrating over the half-circle. -/
-- @node: angularOutcomeCancellation_identity
lemma angularOutcomeCancellation_identity {b cA delta w r : ℝ}
    (hscale : 0 < cA * delta) (h : 2 * (cA * delta) ≤ b * r) :
    Real.pi * delta * angularRadialProfile w r +
        (Real.pi / 2) * (b * r) * angularTilt b cA delta w r = 0 := by
  rw [angularTilt_eq_formula hscale h]
  have hbr : b * r ≠ 0 := by
    have : 0 < b * r := lt_of_lt_of_le (mul_pos (by positivity) (by positivity)) h
    exact this.ne'
  rcases mul_ne_zero_iff.mp hbr with ⟨hb, hr⟩
  field_simp [hb, hr]
  ring

/-- The cosine angular density correction has zero total mass on every upper
half-disc. -/
-- @node: angularTilt_halfDisc_mass_cancellation
lemma angularTilt_halfDisc_mass_cancellation (b cA delta w R : ℝ) :
    (∫ z : ℝ × ℝ in {z | 0 < z.2 ∧ planarRadius z ≤ R},
      angularTilt b cA delta w (planarRadius z) *
        Real.cos (planarAngle z)) = 0 := by
  exact halfDisc_weighted_cos_cancellation (angularTilt b cA delta w) R

/-- The direction cosine used by the angular density is the Cartesian first
coordinate divided by Euclidean radius after passing to centered planar
coordinates. -/
-- @node: packingDirectionCos_eq_planarFirst_div_radius
lemma packingDirectionCos_eq_planarFirst_div_radius (center x : Score) :
    packingDirectionCos center x =
      (scoreCoordinates x - scoreCoordinates center).1 /
        planarRadius (scoreCoordinates x - scoreCoordinates center) := by
  rw [planarRadius_scoreCoordinates_sub]
  by_cases h : dist x center = 0
  · simp [packingDirectionCos, h]
  · simp [packingDirectionCos, scoreCoordinates, h]

/-- Each angular correction integrates to zero on its square-truncated grid
cell.  This is the normalization bridge for every tilted design vertex. -/
-- @node: packingAngularTerm_integral_gridCell
lemma packingAngularTerm_integral_gridCell {M : ℕ} (j : Fin M)
    {b cA delta w : ℝ} (hw : w ≤ 1 / 4) :
    (∫ x : Score in
      Metric.closedBall (angularGridCenter M j) w ∩ scoreCube (1 / 2),
      packingAngularTerm b cA delta w (angularGridCenter M j) x) = 0 := by
  let c := scoreCoordinates (angularGridCenter M j)
  let D : Set (ℝ × ℝ) :=
    {z | 0 ≤ (z - c).2 ∧ planarRadius (z - c) ≤ w}
  have himage : scoreCoordinates ''
      (Metric.closedBall (angularGridCenter M j) w ∩ scoreCube (1 / 2)) = D := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (mem_angularGrid_packingCell_iff_closedUpperHalfDisc j hw x).mp hx
    · intro hz
      let x : Score := scorePoint z.1 z.2
      have hcoord : scoreCoordinates x = z := by
        ext <;> simp [x, scoreCoordinates, scorePoint_apply_zero,
          scorePoint_apply_one]
      refine ⟨x, ?_, hcoord⟩
      apply (mem_angularGrid_packingCell_iff_closedUpperHalfDisc j hw x).mpr
      simpa [D, c, hcoord] using hz
  have hterm : packingAngularTerm b cA delta w (angularGridCenter M j) =
      fun x => angularTilt b cA delta w
          (planarRadius (scoreCoordinates x - scoreCoordinates (angularGridCenter M j))) *
        ((scoreCoordinates x - scoreCoordinates (angularGridCenter M j)).1 /
          planarRadius (scoreCoordinates x - scoreCoordinates (angularGridCenter M j))) := by
    funext x
    rw [packingAngularTerm,
      packingDirectionCos_eq_planarFirst_div_radius,
      planarRadius_scoreCoordinates_sub]
  rw [hterm]
  rw [← scoreCoordinates_measurePreserving.setIntegral_image_emb
    scoreCoordinates_measurableEmbedding
    (fun z : ℝ × ℝ =>
      angularTilt b cA delta w
          (planarRadius (z - scoreCoordinates (angularGridCenter M j))) *
        ((z - scoreCoordinates (angularGridCenter M j)).1 /
          planarRadius (z - scoreCoordinates (angularGridCenter M j))))
    (Metric.closedBall (angularGridCenter M j) w ∩ scoreCube (1 / 2))]
  rw [himage]
  change (∫ z : ℝ × ℝ in D,
    angularTilt b cA delta w (planarRadius (z - c)) *
      ((z - c).1 / planarRadius (z - c))) = 0
  exact translatedClosedHalfDisc_weighted_first_div_radius_cancellation
    (angularTilt b cA delta w) w c

end CausalSmith.Stat.BddUniformLogPenalty
