import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Helpers.AngularRadialFibre

/-!
# Assembly of angular radial-fibre cancellation

This module turns the polar cancellation identity for the changed half-disc
into equality of the complete radius--outcome laws beyond an active cutoff.
-/

open MeasureTheory ProbabilityTheory Set

namespace CausalSmith.Stat.BddUniformLogPenalty

/-- For a true changed bit, the conditional-mean mass of every fully active
radial slice is unchanged by flipping that bit. -/
-- @node: angularPacking_flip_setIntegral_eq_of_active
lemma angularPacking_flip_setIntegral_eq_of_active
    {M : ℕ} (j : Fin M) {b cA delta w : ℝ}
    (hb : 0 < b) (hbSmall : |b| ≤ 1 / 4)
    (hscale : 0 < cA * delta) (hcA : 8 ≤ cA)
    (hdelta : 0 < delta) (hdeltaSmall : delta ≤ 1 / 8)
    (hw : 0 < w) (hwQuarter : w ≤ 1 / 4)
    (hsep : ∀ i k : Fin M, i ≠ k →
      3 * w ≤ dist (angularGridCenter M i) (angularGridCenter M k))
    (omega : Fin M → Bool) (hj : omega j = true)
    {A : Set ℝ} (hA : MeasurableSet A)
    (hactive : ∀ r ∈ A, 2 * (cA * delta) ≤ b * r) :
    (∫ x in {x | dist x (angularGridCenter M j) ∈ A},
        clippedPackingRegression b delta w (angularGridCenter M) omega x
        ∂(angularDesignMeasure b cA delta w (angularGridCenter M) omega)) =
      ∫ x in {x | dist x (angularGridCenter M j) ∈ A},
        clippedPackingRegression b delta w (angularGridCenter M)
          (Causalean.Stat.flipBit j omega) x
        ∂(angularDesignMeasure b cA delta w (angularGridCenter M)
          (Causalean.Stat.flipBit j omega)) := by
  let c := angularGridCenter M j
  let S : Set Score := {x | dist x c ∈ A}
  let D : Set Score :=
    {x | 0 < (scoreCoordinates x - scoreCoordinates c).2 ∧ dist x c ≤ w} ∩ S
  let f : Score → ℝ := fun x =>
    packingRegression b delta w (angularGridCenter M) omega x *
      packingAngularDensity b cA delta w (angularGridCenter M) omega x
  let f' : Score → ℝ := fun x =>
    packingRegression b delta w (angularGridCenter M)
        (Causalean.Stat.flipBit j omega) x *
      packingAngularDensity b cA delta w (angularGridCenter M)
        (Causalean.Stat.flipBit j omega) x
  have hS : MeasurableSet S := hA.preimage (by fun_prop)
  rw [clippedPackingRegression_setIntegral_angularDesignMeasure hb hbSmall hcA
      hscale hdelta hdeltaSmall hw hsep omega hS,
    clippedPackingRegression_setIntegral_angularDesignMeasure hb hbSmall hcA
      hscale hdelta hdeltaSmall hw hsep (Causalean.Stat.flipBit j omega) hS]
  change (∫ x in S ∩ scoreCube (1 / 2 : ℝ), f x) =
    ∫ x in S ∩ scoreCube (1 / 2 : ℝ), f' x
  have hf : IntegrableOn f (S ∩ scoreCube (1 / 2 : ℝ)) := by
    exact (((packingRegression_contDiff b delta w (angularGridCenter M) omega).continuous.mul
      (packingAngularDensity_continuous hb hscale
        (angularGridCenter M) omega)).continuousOn.integrableOn_compact
          packingScoreCube_isCompact).mono_set inter_subset_right
  have hf' : IntegrableOn f' (S ∩ scoreCube (1 / 2 : ℝ)) := by
    exact (((packingRegression_contDiff b delta w (angularGridCenter M)
      (Causalean.Stat.flipBit j omega)).continuous.mul
      (packingAngularDensity_continuous hb hscale (angularGridCenter M)
        (Causalean.Stat.flipBit j omega))).continuousOn.integrableOn_compact
          packingScoreCube_isCompact).mono_set inter_subset_right
  rw [← sub_eq_zero, ← integral_sub hf hf']
  have hboundary : (volume : Measure Score)
      {x | (scoreCoordinates x - scoreCoordinates c).2 = 0} = 0 := by
    have hpre : {x : Score | (scoreCoordinates x - scoreCoordinates c).2 = 0} =
        scoreCoordinates ⁻¹'
          {z : ℝ × ℝ | z.2 = (scoreCoordinates c).2} := by
      ext x
      change (scoreCoordinates x).2 - (scoreCoordinates c).2 = 0 ↔
        (scoreCoordinates x).2 = (scoreCoordinates c).2
      constructor <;> intro h <;> linarith
    rw [hpre, scoreCoordinates_measurePreserving.measure_preimage_emb
      scoreCoordinates_measurableEmbedding]
    have hset : {z : ℝ × ℝ | z.2 = (scoreCoordinates c).2} =
        Set.univ ×ˢ {(scoreCoordinates c).2} := by
      ext z
      simp
    rw [hset, Measure.volume_eq_prod,
      Measure.prod_apply (MeasurableSet.univ.prod
        (measurableSet_singleton (scoreCoordinates c).2))]
    simp
  have hae : ∀ᵐ x ∂(volume : Measure Score),
      (S ∩ scoreCube (1 / 2 : ℝ)).indicator (fun x => f x - f' x) x =
        D.indicator (fun x => f x - f' x) x := by
    filter_upwards [compl_mem_ae_iff.mpr hboundary] with x hxboundary
    by_cases hxD : x ∈ D
    · have hxCell : x ∈ Metric.closedBall c w ∩ scoreCube (1 / 2 : ℝ) := by
        apply (mem_angularGrid_packingCell_iff_closedUpperHalfDisc j hwQuarter x).mpr
        exact ⟨le_of_lt hxD.1.1, by
          simpa [c, planarRadius_scoreCoordinates_sub] using hxD.1.2⟩
      have hxS : x ∈ S := hxD.2
      rw [Set.indicator_of_mem hxD,
        Set.indicator_of_mem (show x ∈ S ∩ scoreCube (1 / 2 : ℝ) from
          ⟨hxS, hxCell.2⟩)]
    · rw [Set.indicator_of_notMem hxD]
      by_cases hxSS : x ∈ S ∩ scoreCube (1 / 2 : ℝ)
      · rw [Set.indicator_of_mem hxSS]
        have hxOutside : x ∉ Metric.closedBall c w := by
          intro hxBall
          have hxLower := hxSS.2 (1 : Fin 2)
          have hcLower : c 1 = -(1 / 2 : ℝ) := by
            dsimp [c]
            simpa [div_eq_mul_inv] using angularGridCenter_apply_one M j
          have hnonneg : 0 ≤ (scoreCoordinates x - scoreCoordinates c).2 := by
            dsimp [scoreCube] at hxLower
            simp only [scoreCoordinates, Prod.snd_sub]
            rw [hcLower]
            have hlower := neg_le_of_abs_le hxLower
            linarith
          have hpos : 0 < (scoreCoordinates x - scoreCoordinates c).2 :=
            lt_of_le_of_ne hnonneg (Ne.symm hxboundary)
          exact hxD ⟨⟨hpos, by simpa [c, Metric.mem_closedBall] using hxBall⟩, hxSS.1⟩
        have hfar : w ≤ dist x c := by
          exact le_of_lt (by simpa [Metric.mem_closedBall, not_le] using hxOutside)
        have hreg : packingRegression b delta w (angularGridCenter M) omega x =
            packingRegression b delta w (angularGridCenter M)
              (Causalean.Stat.flipBit j omega) x := by
          unfold packingRegression
          congr 1
          apply Finset.sum_congr rfl
          intro k _
          by_cases hkj : k = j
          · subst k
            rw [localizedPackingBump_eq_zero_of_bandwidth_le_dist hw hfar]
            simp
          · simp [Causalean.Stat.flipBit, hkj]
        have hdens : packingAngularDensity b cA delta w (angularGridCenter M) omega x =
            packingAngularDensity b cA delta w (angularGridCenter M)
              (Causalean.Stat.flipBit j omega) x := by
          unfold packingAngularDensity
          congr 1
          apply Finset.sum_congr rfl
          intro k _
          by_cases hkj : k = j
          · subst k
            rw [packingAngularTerm_eq_zero_of_bandwidth_le_dist hw hfar]
            simp
          · simp [Causalean.Stat.flipBit, hkj]
        simp [f, f', hreg, hdens]
      · rw [Set.indicator_of_notMem hxSS]
  rw [← integral_indicator (hS.inter (scoreCube_measurableSet _)),
    integral_congr_ae hae]
  have hD : MeasurableSet D := by
    dsimp [D]
    have hv : Measurable (fun x : Score =>
        (scoreCoordinates x - scoreCoordinates c).2) := by fun_prop
    have hr : Measurable (fun x : Score => dist x c) := by fun_prop
    exact ((measurableSet_lt measurable_const hv).inter
      (measurableSet_le hr measurable_const)).inter hS
  rw [integral_indicator hD]
  change (∫ x in D, f x - f' x) = 0
  simpa [D, S, c, f, f'] using
    packingRegression_density_flip_integral_eq_zero_of_active j hb hscale hw
      hsep omega hj hA hactive

/-- If the angular cutoff is fully active beyond `R`, flipping a bit leaves
the complete radius--outcome law unchanged on that tail. -/
-- @node: angularPackingCtyLaw_flip_restrict_Ici_eq_of_active
lemma angularPackingCtyLaw_flip_restrict_Ici_eq_of_active
    {M : ℕ} (j : Fin M) {b cA delta w R : ℝ}
    (hb : 0 < b) (hbSmall : |b| ≤ 1 / 4)
    (hscale : 0 < cA * delta) (hcA : 8 ≤ cA)
    (hdelta : 0 < delta) (hdeltaSmall : delta ≤ 1 / 8)
    (hw : 0 < w) (hwQuarter : w ≤ 1 / 4)
    (hsep : ∀ i k : Fin M, i ≠ k →
      3 * w ≤ dist (angularGridCenter M i) (angularGridCenter M k))
    (omega : Fin M → Bool)
    (hactive : ∀ r ∈ Ici R, 2 * (cA * delta) ≤ b * r) :
    (onePointDistanceLaw
        (angularPackingCtyLaw b cA delta w omega hb hscale hcA hdelta hw
          hwQuarter hsep) (angularGridCenter M j)).restrict {z | R ≤ z.2} =
      (onePointDistanceLaw
        (angularPackingCtyLaw b cA delta w (Causalean.Stat.flipBit j omega)
          hb hscale hcA hdelta hw hwQuarter hsep)
        (angularGridCenter M j)).restrict {z | R ≤ z.2} := by
  apply angularPackingCtyLaw_restrict_Ici_eq_of_radial_slices hb hscale hcA
    hdelta hw hwQuarter hsep omega (Causalean.Stat.flipBit j omega) j
  intro A B hA hB
  let S : Set Score :=
    {x | dist x (angularGridCenter M j) ∈ B ∩ Ici R}
  have hS : MeasurableSet S := (hB.inter measurableSet_Ici).preimage (by fun_prop)
  have hmap := angularDesignMeasure_map_distance_eq j hb hscale hcA hdelta hw
    hwQuarter hsep omega (Causalean.Stat.flipBit j omega)
      (by intro k hkj; simp [Causalean.Stat.flipBit, hkj])
  letI : IsProbabilityMeasure
      (angularDesignMeasure b cA delta w (angularGridCenter M) omega) :=
    angularDesignMeasure_isProbabilityMeasure hb hscale hcA hdelta hw
      hwQuarter hsep omega
  letI : IsProbabilityMeasure
      (angularDesignMeasure b cA delta w (angularGridCenter M)
        (Causalean.Stat.flipBit j omega)) :=
    angularDesignMeasure_isProbabilityMeasure hb hscale hcA hdelta hw
      hwQuarter hsep (Causalean.Stat.flipBit j omega)
  have hmass := radialSlice_mass_eq_of_map_distance_eq
    (angularDesignMeasure b cA delta w (angularGridCenter M) omega)
    (angularDesignMeasure b cA delta w (angularGridCenter M)
      (Causalean.Stat.flipBit j omega))
    (angularGridCenter M j) hmap (A := B ∩ Ici R)
      (hB.inter measurableSet_Ici)
  apply bernoulliGaussianKernel_setLIntegral_eq_of_mass_and_mean
    (angularDesignMeasure b cA delta w (angularGridCenter M) omega)
    (angularDesignMeasure b cA delta w (angularGridCenter M)
      (Causalean.Stat.flipBit j omega))
    (clippedPackingRegression b delta w (angularGridCenter M) omega)
    (clippedPackingRegression b delta w (angularGridCenter M)
      (Causalean.Stat.flipBit j omega))
    (clippedPackingRegression_measurable b delta w (angularGridCenter M) omega)
    (clippedPackingRegression_measurable b delta w (angularGridCenter M)
      (Causalean.Stat.flipBit j omega))
    (fun x => (clippedPackingRegression_mem_Icc b delta w
      (angularGridCenter M) omega x).1)
    (fun x => (clippedPackingRegression_mem_Icc b delta w
      (angularGridCenter M) omega x).2)
    (fun x => (clippedPackingRegression_mem_Icc b delta w
      (angularGridCenter M) (Causalean.Stat.flipBit j omega) x).1)
    (fun x => (clippedPackingRegression_mem_Icc b delta w
      (angularGridCenter M) (Causalean.Stat.flipBit j omega) x).2)
    (D := S) hmass
  by_cases hj : omega j = true
  · exact angularPacking_flip_setIntegral_eq_of_active j hb hbSmall hscale hcA
      hdelta hdeltaSmall hw hwQuarter hsep omega hj (hB.inter measurableSet_Ici)
      (fun r hr => hactive r hr.2)
  · have hjf : omega j = false := Bool.eq_false_of_not_eq_true hj
    have htrue : (Causalean.Stat.flipBit j omega) j = true := by
      simp [Causalean.Stat.flipBit, hjf]
    symm
    simpa [S, Causalean.Stat.flipBit_involutive j omega] using
      angularPacking_flip_setIntegral_eq_of_active j hb hbSmall hscale hcA
        hdelta hdeltaSmall hw hwQuarter hsep
        (Causalean.Stat.flipBit j omega) htrue (hB.inter measurableSet_Ici)
        (fun r hr => hactive r hr.2)

end CausalSmith.Stat.BddUniformLogPenalty
