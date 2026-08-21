import CausalSmith.Stat.STAT_SaPlmCumulantConverse_Research.Helpers.SpectralEstimator

/-! # Certification of the clipped represented output -/

noncomputable section

open Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic

namespace CausalSmith.Stat.SaPlmCumulantConverse

/-- The interval name obtained from the absolute-value clipping formula is
nested, has the inherited effective width modulus, and contains its exact
real value. -/
-- @node: projectedOutputName_certified
lemma projectedOutputName_certified (cStar : PositiveCertifiedReal) (y : ℚ) :
    (projectedOutputName cStar y).IsCertified
      ((|((y : ℚ) : ℝ) + cStar.name.value| -
        |((y : ℚ) : ℝ) - cStar.name.value|) / 2) := by
  have habs_sound : ∀ (I : RatInterval) (x : ℝ), I.Contains x →
      (rationalAbsInterval I).Contains |x| := by
    intro I x hx
    unfold rationalAbsInterval
    split_ifs with hlo hhi
    · have hlor : (0 : ℝ) ≤ (I.lo : ℝ) := by exact_mod_cast hlo
      have hxnonneg : 0 ≤ x := hlor.trans hx.1
      simpa [abs_of_nonneg hxnonneg] using hx
    · have hxnonpos : x ≤ 0 := hx.2.trans (by exact_mod_cast hhi)
      simpa [abs_of_nonpos hxnonpos] using RatInterval.neg_sound hx
    · have hlo' : (I.lo : ℝ) < 0 := by exact_mod_cast lt_of_not_ge hlo
      have hhi' : 0 < (I.hi : ℝ) := by exact_mod_cast lt_of_not_ge hhi
      simp only [RatInterval.Contains, Rat.cast_zero, Rat.cast_max, Rat.cast_neg]
      refine ⟨abs_nonneg x, (abs_le).2 ⟨?_, ?_⟩⟩
      · have hmax : -(max (-(I.lo : ℝ)) (I.hi : ℝ)) ≤ (I.lo : ℝ) := by
          linarith [le_max_left (-(I.lo : ℝ)) (I.hi : ℝ)]
        exact hmax.trans hx.1
      · exact hx.2.trans (le_max_right _ _)
  have habs_mono : ∀ {I J : RatInterval}, I.Subinterval J →
      (rationalAbsInterval I).Subinterval (rationalAbsInterval J) := by
    intro I J hIJ
    rcases hIJ with ⟨hIJlo, hIJhi⟩
    have hIJ : I.Subinterval J := ⟨hIJlo, hIJhi⟩
    by_cases hIlo : 0 ≤ I.lo
    · rw [rationalAbsInterval, dif_pos hIlo]
      by_cases hJlo : 0 ≤ J.lo
      · rw [rationalAbsInterval, dif_pos hJlo]
        exact hIJ
      · rw [rationalAbsInterval, dif_neg hJlo]
        by_cases hJhi : J.hi ≤ 0
        · rw [dif_pos hJhi]
          change (-J.hi ≤ I.lo ∧ I.hi ≤ -J.lo)
          constructor <;> linarith [I.lo_le_hi, J.lo_le_hi]
        · rw [dif_neg hJhi]
          exact ⟨hIlo, hIJ.2.trans (le_max_right _ _)⟩
    · rw [rationalAbsInterval, dif_neg hIlo]
      by_cases hIhi : I.hi ≤ 0
      · rw [dif_pos hIhi]
        by_cases hJlo : 0 ≤ J.lo
        · rw [rationalAbsInterval, dif_pos hJlo]
          change (J.lo ≤ -I.hi ∧ -I.lo ≤ J.hi)
          constructor <;> linarith [I.lo_le_hi, J.lo_le_hi]
        · rw [rationalAbsInterval, dif_neg hJlo]
          by_cases hJhi : J.hi ≤ 0
          · rw [dif_pos hJhi]
            exact RatInterval.neg_mono hIJ
          · rw [dif_neg hJhi]
            exact ⟨by change 0 ≤ -I.hi; exact neg_nonneg.mpr hIhi,
              by simpa [RatInterval.neg] using
                (neg_le_neg hIJ.1).trans (le_max_left _ _)⟩
      · rw [dif_neg hIhi]
        by_cases hJlo : 0 ≤ J.lo
        · exfalso
          linarith [hIJ.1]
        · rw [rationalAbsInterval, dif_neg hJlo]
          by_cases hJhi : J.hi ≤ 0
          · exfalso
            linarith [hIJ.2]
          · rw [dif_neg hJhi]
            exact ⟨le_rfl, max_le_max (neg_le_neg hIJ.1) hIJ.2⟩
  have habs_width : ∀ I : RatInterval,
      (rationalAbsInterval I).width ≤ I.width := by
    intro I
    unfold rationalAbsInterval
    split_ifs with hlo hhi
    · exact le_rfl
    · simpa [RatInterval.width_neg]
    · simp only [RatInterval.width, RatInterval.neg]
      simp only [sub_zero]
      apply max_le
      · linarith [I.lo_le_hi]
      · linarith [I.lo_le_hi]
  constructor
  · intro fuel
    dsimp [projectedOutputName, projectedOutputApprox]
    apply RatInterval.mul_mono (RatInterval.subinterval_refl _)
    apply RatInterval.sub_mono
    · apply habs_mono
      exact RatInterval.add_mono (RatInterval.subinterval_refl _) (cStar.name.nested fuel)
    · apply habs_mono
      exact RatInterval.sub_mono (RatInterval.subinterval_refl _) (cStar.name.nested fuel)
  · constructor
    · intro e
      dsimp [projectedOutputName, projectedOutputApprox]
      have hplus := habs_width
        ((RatInterval.point y).add (cStar.name.approx (cStar.name.modulus e)))
      have hminus := habs_width
        ((RatInterval.point y).sub (cStar.name.approx (cStar.name.modulus e)))
      rw [RatInterval.width_add] at hplus
      rw [RatInterval.width_sub] at hminus
      have hpointWidth : (RatInterval.point y).width = 0 := by
        simp [RatInterval.width, RatInterval.point]
      rw [hpointWidth, zero_add] at hplus hminus
      have hinside : ((rationalAbsInterval
            ((RatInterval.point y).add (cStar.name.approx (cStar.name.modulus e)))).sub
          (rationalAbsInterval
            ((RatInterval.point y).sub (cStar.name.approx (cStar.name.modulus e))))).width ≤
          2 * (cStar.name.approx (cStar.name.modulus e)).width := by
        rw [RatInterval.width_sub]
        calc
          _ ≤ (cStar.name.approx (cStar.name.modulus e)).width +
              (cStar.name.approx (cStar.name.modulus e)).width :=
            add_le_add hplus hminus
          _ = _ := by ring
      have hmul : ∀ I : RatInterval,
          ((RatInterval.point (1 / 2)).mul I).width = I.width / 2 := by
        intro I
        simp only [RatInterval.mul, RatInterval.point, RatInterval.width]
        norm_num
        rw [min_eq_left, max_eq_right] <;> linarith [I.lo_le_hi]
      rw [hmul]
      calc
        _ ≤ (2 * (cStar.name.approx (cStar.name.modulus e)).width) / 2 :=
          div_le_div_of_nonneg_right hinside (by norm_num)
        _ = (cStar.name.approx (cStar.name.modulus e)).width := by ring
        _ ≤ e.1 := cStar.name.width_modulus e
    · intro fuel
      dsimp [projectedOutputName, projectedOutputApprox]
      convert RatInterval.mul_sound (RatInterval.point_sound (1 / 2))
        (RatInterval.sub_sound
          (habs_sound _ _ (RatInterval.add_sound (RatInterval.point_sound y)
            (cStar.name.contains fuel)))
          (habs_sound _ _ (RatInterval.sub_sound (RatInterval.point_sound y)
            (cStar.name.contains fuel)))) using 1 <;> ring

end CausalSmith.Stat.SaPlmCumulantConverse
