import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Causal.Hypercube.HardSquareSignedCertificate

/-!
# Signed hard-cell success-mass localization

This module converts the half-disc angular cancellation into the setwise
success-mass estimate needed by the common-statistic Bernoulli KL argument.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace CausalSmith.Stat.BddUniformLogPenalty


-- @node: causalHardObservedSuccess_setIntegral_scoreMeasure
/-- This declaration establishes the displayed property of the stated causal construction under its listed assumptions. -/
lemma causalHardObservedSuccess_setIntegral_scoreMeasure {M : ℕ} {b cA delta w : ℝ}
    (centers : Fin M → Score) (omega : Fin M → Bool)
    (hb : 0 < b) (hscale : 0 < cA * delta)
    (hcA : 8 ≤ cA) (hdelta : 0 < delta) (hw : 0 < w)
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
    {D : Set Score} (hD : MeasurableSet D) :
    (∫ x in D, causalHardObservedSuccessProfile delta w centers omega x
      ∂(causalHardScoreMeasure b cA delta w centers omega)) =
      (1 / 36 : ℝ) * ∫ x in D ∩ causalHardSquare,
        causalHardObservedSuccessProfile delta w centers omega x *
          packingAngularDensity b cA delta w centers omega x := by
  rw [causalHardScoreMeasure]
  change (∫ x in D, causalHardObservedSuccessProfile delta w centers omega x
      ∂volume.withDensity (ENNReal.ofReal ∘ causalHardSquare.indicator
        (causalHardScoreDensity b cA delta w centers omega))) = _
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul₀
    ((ENNReal.measurable_ofReal.comp
      ((causalHardScoreDensity_continuous centers omega hb hscale).measurable.indicator
        causalHardSquare_measurableSet)).aemeasurable)
    (by simp) _ hD]
  rw [← integral_const_mul]
  rw [← integral_indicator hD,
    ← integral_indicator (hD.inter causalHardSquare_measurableSet)]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hxD : x ∈ D
  · by_cases hxS : x ∈ causalHardSquare
    · rw [Set.indicator_of_mem hxD, Set.indicator_of_mem
          (show x ∈ D ∩ causalHardSquare from ⟨hxD, hxS⟩)]
      have hdens0 : 0 ≤ causalHardScoreDensity b cA delta w centers omega x :=
        mul_nonneg (by norm_num) ((packingAngularDensity_mem_Icc
          (b := b) (cA := cA) (delta := delta) (w := w)
          (centers := centers) (omega := omega) (x := x) hcA
          hdelta hw hsep).1.trans' (by norm_num))
      have hpack0 : 0 ≤ packingAngularDensity b cA delta w centers omega x :=
        (packingAngularDensity_mem_Icc (b := b) hcA hdelta hw hsep omega x).1.trans'
          (by norm_num)
      simp [Function.comp_apply, hxS, ENNReal.toReal_ofReal hpack0,
        causalHardScoreDensity]
      ring
    · rw [Set.indicator_of_mem hxD, Set.indicator_of_notMem (by simp [hxS])]
      simp [Function.comp_apply, hxS]
  · rw [Set.indicator_of_notMem hxD, Set.indicator_of_notMem (by simp [hxD])]

-- @node: packingAngularDensity_enable_cell_sub
/-- This declaration establishes the displayed property of the stated causal construction under its listed assumptions. -/
lemma packingAngularDensity_enable_cell_sub {M : ℕ} (j : Fin M)
    {b cA delta w : ℝ} (centers : Fin M → Score)
    (hw : 0 < w)
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
    (omega : Fin M → Bool) (hj : omega j = false) {x : Score}
    (hx : x ∈ causalHardCell (centers j) w) :
    packingAngularDensity b cA delta w centers (Function.update omega j true) x -
      packingAngularDensity b cA delta w centers omega x =
        packingAngularTerm b cA delta w (centers j) x := by
  have hfar : ∀ i : Fin M, i ≠ j → w ≤ dist x (centers i) := by
    intro i hij
    have htri : dist (centers i) (centers j) ≤
        dist (centers i) x + dist x (centers j) := dist_triangle _ _ _
    have hs := hsep i j hij
    change dist x (centers j) ≤ w at hx
    rw [dist_comm (centers i) x] at htri
    linarith
  unfold packingAngularDensity
  rw [Finset.sum_eq_single j, Finset.sum_eq_zero]
  · simp
  · intro i _
    by_cases hij : i = j
    · subst i
      simp [hj]
    · rw [packingAngularTerm_eq_zero_of_bandwidth_le_dist hw (hfar i hij)]
      simp
  · intro i _ hij
    rw [packingAngularTerm_eq_zero_of_bandwidth_le_dist hw (hfar i hij)]
    simp [Function.update, hij]
  · simp

set_option maxHeartbeats 800000 in
-- @node: causalHardSignedSuccess_setIntegral_abs_le_cellArea
/-- Under the stated assumptions, the theorem gives the displayed quantitative upper or lower bound. -/
lemma causalHardSignedSuccess_setIntegral_abs_le_cellArea
    {M : ℕ} (j : Fin M) {b cA delta w : ℝ}
    (centers : Fin M → Score) (omega : Fin M → Bool)
    (hbEq : b = 1 / 16)
    (hb : 0 < b) (hscale : 0 < cA * delta) (hcA : 8 ≤ cA)
    (hdelta : 0 < delta) (hdeltaSmall : delta ≤ 1 / 16)
    (hw : 0 < w) (hwHalf : w ≤ 1 / 2)
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
    (hcenter : centers j ∈ causalHardBottomEdge)
    (hcell : causalHardCell (centers j) w ⊆ causalHardSquare)
    (hj : omega j = false) {B : Set ℝ} (hB : MeasurableSet B) :
    let omega' := Function.update omega j true
    let nu := (causalHardScoreMeasure b cA delta w centers omega).restrict
      (causalHardCell (centers j) w)
    let nu' := (causalHardScoreMeasure b cA delta w centers omega').restrict
      (causalHardCell (centers j) w)
    let p := causalHardObservedSuccessProfile delta w centers omega
    let p' := causalHardObservedSuccessProfile delta w centers omega'
    let stat := causalHardSignedStatistic (centers j)
    let Dloc := {x | 0 < (scoreCoordinates x - scoreCoordinates (centers j)).2 ∧
      dist x (centers j) ≤ w} ∩
        {x | dist x (centers j) ∈ B ∩ Iio (2 * (cA * delta) / b)}
    |∫ x in {x | stat x ∈ B}, p' x ∂nu' -
      ∫ x in {x | stat x ∈ B}, p x ∂nu| ≤
        (delta / 36) * (volume Dloc).toReal := by
  dsimp only
  let c := centers j
  let omega' := Function.update omega j true
  let stat := causalHardSignedStatistic c
  let S : Set Score := {x | stat x ∈ B}
  let C : Set Score := causalHardCell c w ∩ S
  let D : Set Score :=
    {x | 0 < (scoreCoordinates x - scoreCoordinates c).2 ∧ dist x c ≤ w} ∩
      {x | dist x c ∈ B}
  let Dloc : Set Score :=
    {x | 0 < (scoreCoordinates x - scoreCoordinates c).2 ∧ dist x c ≤ w} ∩
      {x | dist x c ∈ B ∩ Iio (2 * (cA * delta) / b)}
  let Lw : Set Score :=
    {x | (scoreCoordinates x - scoreCoordinates c).2 ≤ 0 ∧ dist x c ≤ w} ∩
      {x | -dist x c ∈ B}
  let p := causalHardObservedSuccessProfile delta w centers omega
  let p' := causalHardObservedSuccessProfile delta w centers omega'
  let dens := packingAngularDensity b cA delta w centers omega
  let dens' := packingAngularDensity b cA delta w centers omega'
  let f := fun x : Score => p x * dens x
  let f' := fun x : Score => p' x * dens' x
  have hS : MeasurableSet S := hB.preimage (causalHardSignedStatistic_measurable c)
  have hC : MeasurableSet C := Metric.isClosed_closedBall.measurableSet.inter hS
  have hf : IntegrableOn f C := by
    apply Measure.integrableOn_of_bounded (M := 2)
      (ne_of_lt ((measure_mono inter_subset_left).trans_lt
        (isCompact_closedBall c w).measure_lt_top))
      ((causalHardObservedSuccessProfile_measurable delta w centers omega).fun_mul
        (packingAngularDensity_continuous hb hscale centers omega).measurable).aestronglyMeasurable
    filter_upwards [ae_restrict_mem hC] with x hx
    have hp01 := causalHardProfiles_mem_unitInterval delta w centers omega x
    have hd := packingAngularDensity_mem_Icc (b := b) hcA hdelta hw hsep omega x
    have hpabs : |p x| ≤ 1 := by
      dsimp [p, causalHardObservedSuccessProfile]
      split_ifs <;> rw [abs_of_nonneg] <;>
        linarith [hp01.1.1, hp01.1.2, hp01.2.1, hp01.2.2]
    have hdabs : |dens x| ≤ 2 := by
      dsimp [dens]
      rw [abs_of_nonneg] <;> linarith [hd.1, hd.2]
    rw [Real.norm_eq_abs, abs_mul]
    nlinarith [abs_nonneg (p x), abs_nonneg (dens x)]
  have hf' : IntegrableOn f' C := by
    apply Measure.integrableOn_of_bounded (M := 2)
      (ne_of_lt ((measure_mono inter_subset_left).trans_lt
        (isCompact_closedBall c w).measure_lt_top))
      ((causalHardObservedSuccessProfile_measurable delta w centers omega').fun_mul
        (packingAngularDensity_continuous hb hscale centers omega').measurable).aestronglyMeasurable
    filter_upwards [ae_restrict_mem hC] with x hx
    have hp01 := causalHardProfiles_mem_unitInterval delta w centers omega' x
    have hd := packingAngularDensity_mem_Icc (b := b) hcA hdelta hw hsep omega' x
    have hpabs : |p' x| ≤ 1 := by
      dsimp [p', causalHardObservedSuccessProfile]
      split_ifs <;> rw [abs_of_nonneg] <;>
        linarith [hp01.1.1, hp01.1.2, hp01.2.1, hp01.2.2]
    have hdabs : |dens' x| ≤ 2 := by
      dsimp [dens']
      rw [abs_of_nonneg] <;> linarith [hd.1, hd.2]
    rw [Real.norm_eq_abs, abs_mul]
    nlinarith [abs_nonneg (p' x), abs_nonneg (dens' x)]
  have hraw : |∫ x in C, f' x - f x| ≤ delta * (volume Dloc).toReal := by
    have hboundary : (volume : Measure Score)
        {x | (scoreCoordinates x - scoreCoordinates c).2 = 0} = 0 := by
      have hpre : {x : Score | (scoreCoordinates x - scoreCoordinates c).2 = 0} =
          scoreCoordinates ⁻¹' {z : ℝ × ℝ | z.2 = (scoreCoordinates c).2} := by
        ext x
        change (scoreCoordinates x).2 - (scoreCoordinates c).2 = 0 ↔
          (scoreCoordinates x).2 = (scoreCoordinates c).2
        constructor <;> intro h <;> linarith
      rw [hpre, scoreCoordinates_measurePreserving.measure_preimage_emb
        scoreCoordinates_measurableEmbedding]
      have hset : {z : ℝ × ℝ | z.2 = (scoreCoordinates c).2} =
          Set.univ ×ˢ {(scoreCoordinates c).2} := by ext z; simp
      rw [hset, Measure.volume_eq_prod,
        Measure.prod_apply (MeasurableSet.univ.prod
          (measurableSet_singleton (scoreCoordinates c).2))]
      simp
    have hD : MeasurableSet D := by
      have hv : Measurable (fun x : Score =>
          (scoreCoordinates x - scoreCoordinates c).2) := by fun_prop
      have hr : Measurable (fun x : Score => dist x c) := by fun_prop
      exact ((measurableSet_lt measurable_const hv).inter
        (measurableSet_le hr measurable_const)).inter (hB.preimage hr)
    have hLw : MeasurableSet Lw := by
      have hv : Measurable (fun x : Score =>
          (scoreCoordinates x - scoreCoordinates c).2) := by fun_prop
      have hr : Measurable (fun x : Score => dist x c) := by fun_prop
      exact ((measurableSet_le hv measurable_const).inter
        (measurableSet_le hr measurable_const)).inter
          (hB.preimage hr.neg)
    let upper : Score → ℝ := fun x =>
      delta * angularRadialProfile w (dist x c) +
        (packingAffineBaseline b x + delta * angularRadialProfile w (dist x c)) *
          angularTilt b cA delta w (dist x c) *
          ((scoreCoordinates x - scoreCoordinates c).1 / dist x c)
    let lower : Score → ℝ := fun x =>
      (1 / 2 : ℝ) * packingAngularTerm b cA delta w c x
    have hae : ∀ᵐ x ∂(volume : Measure Score),
        C.indicator (fun x => f' x - f x) x =
          D.indicator upper x + Lw.indicator lower x := by
      filter_upwards [compl_mem_ae_iff.mpr hboundary] with x hx0
      by_cases hxC : x ∈ C
      · have hxcell := hxC.1
        have hstat := causalHardSignedStatistic_eq_verticalSignedRadius_on_cell
          hcenter hwHalf hxcell
        change causalHardSignedStatistic c x =
          (if 0 ≤ (scoreCoordinates x - scoreCoordinates c).2 then dist x c
            else -dist x c) at hstat
        have hsq := hcell hxcell
        by_cases hxup : 0 < (scoreCoordinates x - scoreCoordinates c).2
        · have hxD : x ∈ D := by
            refine ⟨⟨hxup, ?_⟩, ?_⟩
            · exact hxcell
            · have hm := hxC.2
              change causalHardSignedStatistic c x ∈ B at hm
              rw [hstat, if_pos hxup.le] at hm
              exact hm
          have hxnotL : x ∉ Lw := by
            intro hxL
            exact (not_le_of_gt hxup) hxL.1.1
          rw [Set.indicator_of_mem hxC, Set.indicator_of_mem hxD,
            Set.indicator_of_notMem hxnotL, add_zero]
          have hA1 : x ∈ causalHardArmOne := by
            have hv : 0 ≤ (scoreCoordinates x - scoreCoordinates c).2 := hxup.le
            have hs := causalHardSignedStatistic_eq_verticalSignedRadius_on_cell
              hcenter hwHalf hxcell
            -- The geometry proof of the signed-statistic identity already places
            -- the positive half-cell in arm one.
            have hc1 : c 1 = 0 := hcenter.2.2
            have hcoord (i : Fin 2) : |x i - c i| ≤ dist x c := by
              simpa [dist_eq_norm, Real.norm_eq_abs] using PiLp.norm_apply_le (x - c) i
            have hdcell : dist x c ≤ w := hxcell
            have hx0lo : -1 ≤ x 0 := by
              have hh := hcoord 0
              rw [abs_le] at hh
              have hc0lo : -1 / 2 ≤ c 0 := by simpa [c] using hcenter.1
              linarith [hc0lo, hdcell, hwHalf]
            have hx0hi : x 0 ≤ 1 := by
              have hh := hcoord 0
              rw [abs_le] at hh
              have hc0hi : c 0 ≤ 1 / 2 := by simpa [c] using hcenter.2.1
              linarith [hc0hi, hdcell, hwHalf]
            have hx1lo : 0 ≤ x 1 := by
              change 0 ≤ x 1 - c 1 at hv
              linarith
            have hx1hi : x 1 ≤ 2 := by
              have hd : dist x c ≤ w := hxcell
              have hh := hcoord 1
              rw [hc1, sub_zero, abs_le] at hh
              linarith
            exact ⟨hx0lo, hx0hi, hx1lo, hx1hi⟩
          have hpOn : p' x = packingRegression b delta w centers omega' x := by
            dsimp [p', causalHardObservedSuccessProfile]
            rw [if_pos hA1]
            simpa [hbEq] using
              causalHardTreatmentProfile_eq_packingRegression_on_square
                hdelta.le hdeltaSmall hw hsep omega' hsq
          have hpOff : p x = packingRegression b delta w centers omega x := by
            dsimp [p, causalHardObservedSuccessProfile]
            rw [if_pos hA1]
            simpa [hbEq] using
              causalHardTreatmentProfile_eq_packingRegression_on_square
                hdelta.le hdeltaSmall hw hsep omega hsq
          dsimp [f', f, dens', dens, upper]
          rw [hpOn, hpOff]
          simpa [c, omega', hbEq] using
            packingRegression_mul_density_enable_cell_radial_identity j centers
              hw hsep omega hj hxcell
        · have hxdown : (scoreCoordinates x - scoreCoordinates c).2 < 0 :=
            have hxne : (scoreCoordinates x - scoreCoordinates c).2 ≠ 0 := by
              simpa using hx0
            lt_of_le_of_ne (le_of_not_gt hxup) hxne
          have hxL : x ∈ Lw := by
            refine ⟨⟨hxdown.le, hxcell⟩, ?_⟩
            have hm := hxC.2
            change causalHardSignedStatistic c x ∈ B at hm
            rw [hstat, if_neg (not_le.mpr hxdown)] at hm
            exact hm
          have hxnotD : x ∉ D := by
            intro hxD
            exact (not_lt_of_ge hxdown.le) hxD.1.1
          rw [Set.indicator_of_mem hxC, Set.indicator_of_notMem hxnotD,
            Set.indicator_of_mem hxL, zero_add]
          have hA1 : x ∉ causalHardArmOne := by
            intro hA
            have hc1 : c 1 = 0 := hcenter.2.2
            have : 0 ≤ (scoreCoordinates x - scoreCoordinates c).2 := by
              change 0 ≤ x 1 - c 1
              linarith [hA.2.2.1]
            linarith
          dsimp [f', f, p', p, dens', dens, lower,
            causalHardObservedSuccessProfile]
          rw [if_neg hA1, if_neg hA1]
          dsimp [causalHardControlProfile]
          have hdens := packingAngularDensity_enable_cell_sub (b := b) (cA := cA)
            (delta := delta) j centers hw hsep omega hj hxcell
          change packingAngularDensity b cA delta w centers omega' x -
            packingAngularDensity b cA delta w centers omega x = _ at hdens
          rw [← hdens]
          ring
      · rw [Set.indicator_of_notMem hxC]
        have hxnotD : x ∉ D := by
          intro hxD
          apply hxC
          refine ⟨hxD.1.2, ?_⟩
          change stat x ∈ B
          dsimp [stat]
          rw [causalHardSignedStatistic_eq_verticalSignedRadius_on_cell
            hcenter hwHalf hxD.1.2]
          rw [if_pos hxD.1.1.le]
          exact hxD.2
        have hxnotL : x ∉ Lw := by
          intro hxL
          apply hxC
          refine ⟨hxL.1.2, ?_⟩
          change stat x ∈ B
          dsimp [stat]
          rw [causalHardSignedStatistic_eq_verticalSignedRadius_on_cell
            hcenter hwHalf hxL.1.2]
          have hxneg : (scoreCoordinates x - scoreCoordinates c).2 < 0 := by
            have hxne : (scoreCoordinates x - scoreCoordinates c).2 ≠ 0 := by
              simpa using hx0
            exact lt_of_le_of_ne hxL.1.1 hxne
          rw [if_neg (not_le.mpr hxneg)]
          exact hxL.2
        simp [hxnotD, hxnotL]
    rw [← integral_indicator hC, integral_congr_ae hae]
    have hu : IntegrableOn upper D := by
      have hDsubC : D ⊆ C := by
        intro x hx
        refine ⟨hx.1.2, ?_⟩
        change stat x ∈ B
        dsimp [stat]
        rw [causalHardSignedStatistic_eq_verticalSignedRadius_on_cell
          hcenter hwHalf hx.1.2]
        rw [if_pos hx.1.1.le]
        exact hx.2
      have hbase : IntegrableOn (fun x => f' x - f x) C := hf'.sub hf
      apply Integrable.congr (hbase.mono_set hDsubC)
      filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem hD] with x heq hx
      have hxC := hDsubC hx
      have hxnotL : x ∉ Lw := by
        intro hxL
        exact (not_le_of_gt hx.1.1) hxL.1.1
      rw [Set.indicator_of_mem hxC, Set.indicator_of_mem hx,
        Set.indicator_of_notMem hxnotL, add_zero] at heq
      exact heq
    have hl : IntegrableOn lower Lw := by
      exact (((continuous_const.mul
        (packingAngularTerm_continuous hb hscale c)).continuousOn.integrableOn_compact
          (isCompact_closedBall c w)).mono_set (fun x hx => hx.1.2))
    rw [integral_add (hu.integrable_indicator hD) (hl.integrable_indicator hLw),
      integral_indicator hD, integral_indicator hLw]
    have hlzero : (∫ x in Lw, lower x) = 0 := by
      have hnegB : MeasurableSet ((fun r : ℝ => -r) ⁻¹' B) :=
        hB.preimage (by fun_prop)
      have hz := scoreCenter_closedLowerHalf_radial_angularTerm_integral_eq_zero
        c b cA delta w hnegB
      dsimp [Lw, lower]
      rw [integral_const_mul]
      convert congrArg (fun z : ℝ => (1 / 2 : ℝ) * z) hz using 1 <;>
        simp [preimage, and_assoc]
    rw [hlzero, add_zero]
    have hquant := scoreCenter_radialSet_angular_outcome_abs_le
      (w := w) c hb hscale hdelta.le hB
    dsimp only at hquant
    let main : Score → ℝ := fun x =>
      delta * angularRadialProfile w (dist x c) +
        b * (scoreCoordinates x - scoreCoordinates c).1 *
          angularTilt b cA delta w (dist x c) *
          ((scoreCoordinates x - scoreCoordinates c).1 / dist x c)
    let extra : Score → ℝ := fun x =>
      (1 / 2 + b * c 0 + delta * angularRadialProfile w (dist x c)) *
        angularTilt b cA delta w (dist x c) *
        ((scoreCoordinates x - scoreCoordinates c).1 / dist x c)
    have hextra : (∫ x in D, extra x) = 0 := by
      let Dc : Set Score :=
        {x | 0 ≤ (scoreCoordinates x - scoreCoordinates c).2 ∧ dist x c ≤ w} ∩
          {x | dist x c ∈ B}
      let g : ℝ → ℝ := fun r =>
        (1 / 2 + b * c 0 + delta * angularRadialProfile w r) *
          angularTilt b cA delta w r
      have hzClosed : (∫ x in Dc, extra x) = 0 := by
        have himage : scoreCoordinates '' Dc =
            ({z : ℝ × ℝ | 0 ≤ (z - scoreCoordinates c).2 ∧
                planarRadius (z - scoreCoordinates c) ≤ w} ∩
              {z | planarRadius (z - scoreCoordinates c) ∈ B}) := by
          ext z
          constructor
          · rintro ⟨x, hx, rfl⟩
            simpa [Dc, planarRadius_scoreCoordinates_sub] using hx
          · intro hz
            let x : Score := scorePoint z.1 z.2
            have hcoord : scoreCoordinates x = z := by
              ext <;> simp [x, scoreCoordinates, scorePoint_apply_zero,
                scorePoint_apply_one]
            refine ⟨x, ?_, hcoord⟩
            simpa [Dc, hcoord, ← planarRadius_scoreCoordinates_sub] using hz
        have hextraForm : extra = fun x =>
            g (planarRadius (scoreCoordinates x - scoreCoordinates c)) *
              ((scoreCoordinates x - scoreCoordinates c).1 /
                planarRadius (scoreCoordinates x - scoreCoordinates c)) := by
          funext x
          dsimp [extra, g]
          rw [planarRadius_scoreCoordinates_sub]
        rw [hextraForm]
        rw [← scoreCoordinates_measurePreserving.setIntegral_image_emb
          scoreCoordinates_measurableEmbedding
          (fun z : ℝ × ℝ => g (planarRadius (z - scoreCoordinates c)) *
            ((z - scoreCoordinates c).1 /
              planarRadius (z - scoreCoordinates c))) Dc, himage]
        simpa [extra, g, planarRadius_scoreCoordinates_sub] using
          translatedClosedHalfDisc_radialSet_weighted_first_div_radius_cancellation
            g w (scoreCoordinates c) hB
      have haeDC : D.indicator extra =ᵐ[volume] Dc.indicator extra := by
        filter_upwards [compl_mem_ae_iff.mpr hboundary] with x hx0
        by_cases hxD : x ∈ D
        · have hxDc : x ∈ Dc := ⟨⟨hxD.1.1.le, hxD.1.2⟩, hxD.2⟩
          simp [hxD, hxDc]
        · have hxDc : x ∉ Dc := by
            intro hxDc
            apply hxD
            refine ⟨⟨lt_of_le_of_ne hxDc.1.1 ?_, hxDc.1.2⟩, hxDc.2⟩
            intro hz
            apply hx0
            simpa [hz]
          simp [hxD, hxDc]
      rw [← integral_indicator hD, integral_congr_ae haeDC,
        integral_indicator (by
          have hv : Measurable (fun x : Score =>
            (scoreCoordinates x - scoreCoordinates c).2) := by fun_prop
          have hr : Measurable (fun x : Score => dist x c) := by fun_prop
          exact ((measurableSet_le measurable_const hv).inter
            (measurableSet_le hr measurable_const)).inter (hB.preimage hr))]
      exact hzClosed
    have hsplit : (∫ x in D, upper x) =
        (∫ x in D, delta * angularRadialProfile w (dist x c)) +
          ∫ x in D,
            b * (scoreCoordinates x - scoreCoordinates c).1 *
              angularTilt b cA delta w (dist x c) *
              ((scoreCoordinates x - scoreCoordinates c).1 / dist x c) := by
      have hdecomp : upper = main + extra := by
        funext x
        dsimp [upper, main, extra, packingAffineBaseline]
        have hxf : (scoreCoordinates x).1 = x 0 := rfl
        have hcf : (scoreCoordinates c).1 = c 0 := rfl
        rw [hxf, hcf]
        ring
      rw [hdecomp]
      have hextraInt : IntegrableOn extra D := by
        have heq : extra = fun x =>
            (1 / 2 + b * c 0 + delta * angularRadialProfile w (dist x c)) *
              packingAngularTerm b cA delta w c x := by
          funext x
          dsimp [extra]
          rw [packingAngularTerm,
            packingDirectionCos_eq_planarFirst_div_radius,
            planarRadius_scoreCoordinates_sub]
          have hcoord : (scoreCoordinates x - scoreCoordinates c).1 = x 0 - c 0 := rfl
          have hxf : (scoreCoordinates x).1 = x 0 := rfl
          have hcf : (scoreCoordinates c).1 = c 0 := rfl
          rw [hcoord, hxf, hcf]
          ring
        rw [heq]
        exact (((continuous_const.add (continuous_const.mul
          ((angularRadialProfile_continuous w).comp
            (continuous_id.dist continuous_const)))).mul
              (packingAngularTerm_continuous hb hscale c)).continuousOn.integrableOn_compact
                (isCompact_closedBall c w)).mono_set (fun x hx => hx.1.2)
      have hmain : IntegrableOn main D := by
        have heq : main = upper - extra := by
          rw [hdecomp]
          funext x
          simp
        rw [heq]
        exact hu.sub hextraInt
      have hfirst : IntegrableOn
          (fun x : Score => delta * angularRadialProfile w (dist x c)) D := by
        exact (((continuous_const.mul
          ((angularRadialProfile_continuous w).comp
            (continuous_id.dist continuous_const)))).continuousOn.integrableOn_compact
              (isCompact_closedBall c w)).mono_set (fun x hx => hx.1.2)
      have hsecond : IntegrableOn
          (fun x : Score =>
            b * (scoreCoordinates x - scoreCoordinates c).1 *
              angularTilt b cA delta w (dist x c) *
              ((scoreCoordinates x - scoreCoordinates c).1 / dist x c)) D := by
        have heq : (fun x : Score =>
            b * (scoreCoordinates x - scoreCoordinates c).1 *
              angularTilt b cA delta w (dist x c) *
              ((scoreCoordinates x - scoreCoordinates c).1 / dist x c)) = fun x =>
            main x - delta * angularRadialProfile w (dist x c) := by
          funext x
          dsimp [main]
          ring
        rw [heq]
        exact hmain.sub hfirst
      calc
        (∫ x in D, (main + extra) x) =
            (∫ x in D, main x) + ∫ x in D, extra x :=
          integral_add hmain hextraInt
        _ = ∫ x in D, main x := by rw [hextra, add_zero]
        _ = (∫ x in D, delta * angularRadialProfile w (dist x c)) +
              ∫ x in D,
                b * (scoreCoordinates x - scoreCoordinates c).1 *
                  angularTilt b cA delta w (dist x c) *
                  ((scoreCoordinates x - scoreCoordinates c).1 / dist x c) := by
          dsimp [main]
          exact integral_add hfirst hsecond
    rw [hsplit]
    simpa [D, Dloc] using hquant
  have hbridge := causalHardObservedSuccess_setIntegral_scoreMeasure centers omega hb hscale hcA hdelta hw hsep hC
  have hbridge' := causalHardObservedSuccess_setIntegral_scoreMeasure centers omega' hb hscale hcA hdelta hw hsep hC
  rw [Measure.restrict_restrict hS, Measure.restrict_restrict hS]
  have hSC : S ∩ causalHardCell (centers j) w = C := by
    ext x
    simp [C, c, and_comm]
  rw [hSC]
  change |∫ x in C, p' x ∂causalHardScoreMeasure b cA delta w centers omega' -
      ∫ x in C, p x ∂causalHardScoreMeasure b cA delta w centers omega| ≤ _
  rw [hbridge', hbridge]
  have hCsq : C ∩ causalHardSquare = C := by
    apply inter_eq_left.mpr
    exact fun x hx => hcell hx.1
  rw [hCsq]
  rw [integral_sub hf' hf] at hraw
  dsimp [f, f', p, p', dens, dens', omega', Dloc, c] at hraw ⊢
  rw [← mul_sub, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 36)]
  nlinarith


-- @node: causalHardSignedSuccess_localized_setwise_bound
/-- Under the stated assumptions, the theorem gives the displayed quantitative upper or lower bound. -/
lemma causalHardSignedSuccess_localized_setwise_bound {M : ℕ} (j : Fin M) {b cA delta w : ℝ}
    (centers : Fin M → Score) (omega : Fin M → Bool)
    (hbEq : b = 1 / 16) (hb : 0 < b) (hscale : 0 < cA * delta)
    (hcA : 8 ≤ cA) (hdelta : 0 < delta) (hdeltaSmall : delta ≤ 1 / 16)
    (hw : 0 < w) (hwHalf : w ≤ 1 / 2)
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
    (hcenter : centers j ∈ causalHardBottomEdge)
    (hcell : causalHardCell (centers j) w ⊆ causalHardSquare)
    (hj : omega j = false) {B : Set ℝ} (hB : MeasurableSet B) :
    let omega' := Function.update omega j true
    let nu := (causalHardScoreMeasure b cA delta w centers omega).restrict
      (causalHardCell (centers j) w)
    let nu' := (causalHardScoreMeasure b cA delta w centers omega').restrict
      (causalHardCell (centers j) w)
    let p := causalHardObservedSuccessProfile delta w centers omega
    let p' := causalHardObservedSuccessProfile delta w centers omega'
    let stat := causalHardSignedStatistic (centers j)
    let E := Ioo 0 (2 * (cA * delta) / b)
    |(∫ x in {x | stat x ∈ B}, p x ∂nu) -
      ∫ x in {x | stat x ∈ B}, p' x ∂nu'| ≤
        delta * (Measure.map stat nu (B ∩ E)).toReal := by
  dsimp only
  let omega' := Function.update omega j true
  let stat := causalHardSignedStatistic (centers j)
  let E := Ioo 0 (2 * (cA * delta) / b)
  have harea := causalHardSignedSuccess_setIntegral_abs_le_cellArea j centers omega
    hbEq hb hscale hcA hdelta hdeltaSmall hw hwHalf hsep hcenter hcell hj hB
  rw [abs_sub_comm]
  apply harea.trans
  rw [Measure.map_apply (causalHardSignedStatistic_measurable _) (hB.inter measurableSet_Ioo)]
  rw [Measure.restrict_apply ((hB.inter measurableSet_Ioo).preimage
    (causalHardSignedStatistic_measurable _))]
  have hset : stat ⁻¹' (B ∩ E) ∩ causalHardCell (centers j) w =
      causalHardCell (centers j) w ∩ {x | stat x ∈ B ∩ E} := by
    ext x
    simp [and_comm]
  rw [hset, causalHardScoreMeasure_signedSlice_eq_uniform j centers omega hb hscale
    hcA hdelta hw hwHalf hsep hcenter hcell (hB.inter measurableSet_Ioo)]
  have hvoltop : volume (causalHardCell (centers j) w ∩
      {x | stat x ∈ B ∩ E}) ≠ ∞ := ne_of_lt
    ((measure_mono inter_subset_left).trans_lt
      (isCompact_closedBall (centers j) w).measure_lt_top)
  rw [ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 36)]
  have hsubset :
      {x | 0 < (scoreCoordinates x - scoreCoordinates (centers j)).2 ∧
        dist x (centers j) ≤ w} ∩
          {x | dist x (centers j) ∈ B ∩ Iio (2 * (cA * delta) / b)} ⊆
        causalHardCell (centers j) w ∩ {x | stat x ∈ B ∩ E} := by
    intro x hx
    have hxcell : x ∈ causalHardCell (centers j) w := hx.1.2
    refine ⟨hxcell, ?_⟩
    change causalHardSignedStatistic (centers j) x ∈
      B ∩ Ioo 0 (2 * (cA * delta) / b)
    rw [causalHardSignedStatistic_eq_verticalSignedRadius_on_cell
      hcenter hwHalf hxcell, if_pos hx.1.1.le]
    refine ⟨hx.2.1, ⟨dist_pos.mpr ?_, hx.2.2⟩⟩
    intro heq
    subst x
    simp at hx
  have hreal := ENNReal.toReal_mono hvoltop (measure_mono hsubset)
  calc
    delta / 36 *
        (volume
          ({x | 0 < (scoreCoordinates x - scoreCoordinates (centers j)).2 ∧
              dist x (centers j) ≤ w} ∩
            {x | dist x (centers j) ∈ B ∩
              Iio (2 * (cA * delta) / b)})).toReal ≤
        delta / 36 *
          (volume (causalHardCell (centers j) w ∩
            {x | stat x ∈ B ∩ E})).toReal :=
      mul_le_mul_of_nonneg_left hreal (by positivity)
    _ = delta * (1 / 36 *
          (volume (causalHardCell (centers j) w ∩
            {x | stat x ∈ B ∩ E})).toReal) := by ring


-- @node: causalHardCellSignedObservationMeasure_klDiv_enable_le
/-- Under the stated assumptions, the theorem gives the displayed quantitative upper or lower bound. -/
lemma causalHardCellSignedObservationMeasure_klDiv_enable_le {M : ℕ} (j : Fin M) {b cA delta w : ℝ}
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
    (InformationTheory.klDiv
        (causalHardCellSignedObservationMeasure P (centers j) w)
        (causalHardCellSignedObservationMeasure P' (centers j) w) ≤
      ENNReal.ofReal (4 * delta ^ 2) *
        Measure.map (causalHardSignedStatistic (centers j))
          ((causalHardScoreMeasure b cA delta w centers omega).restrict
            (causalHardCell (centers j) w))
          (Ioo 0 (2 * (cA * delta) / b))) ∧
    (InformationTheory.klDiv
        (causalHardCellSignedObservationMeasure P' (centers j) w)
        (causalHardCellSignedObservationMeasure P (centers j) w) ≤
      ENNReal.ofReal (4 * delta ^ 2) *
        Measure.map (causalHardSignedStatistic (centers j))
          ((causalHardScoreMeasure b cA delta w centers omega).restrict
            (causalHardCell (centers j) w))
          (Ioo 0 (2 * (cA * delta) / b))) := by
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
    dsimp [q]
    exact max_le (by norm_num) (min_le_left _ _)
  have hq0' : ∀ x, (1 / 4 : ℝ) ≤ q' x := fun x => le_max_left _ _
  have hq1' : ∀ x, q' x ≤ (3 / 4 : ℝ) := by
    intro x
    dsimp [q']
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
          delta * (Measure.map stat nu
            (B ∩ Ioo 0 (2 * (cA * delta) / b))).toReal := by
    intro B hB
    have heq : (∫ x in {x | stat x ∈ B}, q x ∂nu) =
        ∫ x in {x | stat x ∈ B}, p x ∂nu := by
      apply MeasureTheory.integral_congr_ae
      exact ae_restrict_of_ae hqp
    have heq' : (∫ x in {x | stat x ∈ B}, q' x ∂nu') =
        ∫ x in {x | stat x ∈ B}, p' x ∂nu' := by
      apply MeasureTheory.integral_congr_ae
      exact ae_restrict_of_ae hqp'
    rw [heq, heq']
    exact causalHardSignedSuccess_localized_setwise_bound j centers omega hbEq hb
      hscale hcA hdelta hdeltaSmall hw hwHalf hsep hcenter (hcell j) hj hB
  have hkl := statisticBernoulliOutcome_klDiv_le_of_localized_success_bound
    nu nu' q q' stat hq hq' (causalHardSignedStatistic_measurable _)
    hq0 hq1 hq0' hq1' hmap hdelta.le measurableSet_Ioo hdiff
  have hdiff' : ∀ B : Set ℝ, MeasurableSet B →
      |(∫ x in {x | stat x ∈ B}, q' x ∂nu') -
        ∫ x in {x | stat x ∈ B}, q x ∂nu| ≤
          delta * (Measure.map stat nu' (B ∩ Ioo 0 (2 * (cA * delta) / b))).toReal := by
    intro B hB
    rw [← hmap]
    simpa only [abs_sub_comm] using hdiff B hB
  have hkl' := statisticBernoulliOutcome_klDiv_le_of_localized_success_bound
    nu' nu q' q stat hq' hq (causalHardSignedStatistic_measurable _)
    hq0' hq1' hq0 hq1 hmap.symm hdelta.le measurableSet_Ioo hdiff'
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
  rw [MeasureTheory.Measure.compProd_congr hk,
    MeasureTheory.Measure.compProd_congr hk'] at hkl
  rw [MeasureTheory.Measure.compProd_congr hk',
    MeasureTheory.Measure.compProd_congr hk] at hkl'
  rw [← causalHardCellSignedObservationMeasure_eq_scoreBernoulli j b cA delta w
      centers omega hb hscale hcA hdelta hw hsep hcell,
    ← causalHardCellSignedObservationMeasure_eq_scoreBernoulli j b cA delta w
      centers omega' hb hscale hcA hdelta hw hsep hcell] at hkl
  rw [← causalHardCellSignedObservationMeasure_eq_scoreBernoulli j b cA delta w
      centers omega' hb hscale hcA hdelta hw hsep hcell,
    ← causalHardCellSignedObservationMeasure_eq_scoreBernoulli j b cA delta w
      centers omega hb hscale hcA hdelta hw hsep hcell] at hkl'
  rw [← hmap] at hkl'
  exact ⟨hkl, hkl'⟩


end CausalSmith.Stat.BddUniformLogPenalty
