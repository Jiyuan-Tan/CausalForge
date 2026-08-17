import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Helpers.AngularLaw

/-!
# Cellwise locality of the angular hard family

This module lifts locality of the score design and regression kernel to
locality of the faithful joint Bernoulli--Gaussian law.  It then applies that
bridge to one square-truncated packing cell.
-/

open MeasureTheory ProbabilityTheory Set

namespace CausalSmith.Stat.BddUniformLogPenalty

/-- Two Bernoulli--Gaussian joint laws have identical restrictions over a
measurable score cell when their restricted score designs agree and their
Bernoulli parameters agree throughout that cell. -/
-- @node: jointBernoulliGaussianLaw_restrict_score_eq
lemma jointBernoulliGaussianLaw_restrict_score_eq
    (nu nu' : Measure Score) [SFinite nu] [SFinite nu']
    (p p' : Score → ℝ) (hp : Measurable p) (hp' : Measurable p')
    (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∀ x, p x ≤ 1)
    (hp0' : ∀ x, 0 ≤ p' x) (hp1' : ∀ x, p' x ≤ 1)
    {C : Set Score} (hC : MeasurableSet C)
    (hnu : nu.restrict C = nu'.restrict C)
    (hparam : ∀ x ∈ C, p x = p' x) :
    (jointBernoulliGaussianLaw nu p hp).restrict {o | o.2 ∈ C} =
      (jointBernoulliGaussianLaw nu' p' hp').restrict {o | o.2 ∈ C} := by
  letI : IsMarkovKernel (bernoulliGaussianKernel p hp) :=
    bernoulliGaussianKernel_isMarkovKernel p hp hp0 hp1
  letI : IsMarkovKernel (bernoulliGaussianKernel p' hp') :=
    bernoulliGaussianKernel_isMarkovKernel p' hp' hp0' hp1'
  ext s hs
  rw [Measure.restrict_apply hs, Measure.restrict_apply hs]
  unfold jointBernoulliGaussianLaw
  have hE : MeasurableSet (s ∩ {o : Observation | o.2 ∈ C}) :=
    hs.inter (hC.preimage measurable_snd)
  rw [Measure.map_apply measurable_swap hE,
    Measure.map_apply measurable_swap hE]
  have hpre : MeasurableSet
      (Prod.swap ⁻¹' (s ∩ {o : Observation | o.2 ∈ C})) :=
    hE.preimage measurable_swap
  rw [Measure.compProd_apply hpre, Measure.compProd_apply hpre]
  have hsupp : Function.support (fun x ↦
      (bernoulliGaussianKernel p hp x)
        (Prod.mk x ⁻¹' (Prod.swap ⁻¹' (s ∩ {o : Observation | o.2 ∈ C})))) ⊆ C := by
    intro x hx
    by_contra hxC
    apply hx
    simp [hxC]
  have hsupp' : Function.support (fun x ↦
      (bernoulliGaussianKernel p' hp' x)
        (Prod.mk x ⁻¹' (Prod.swap ⁻¹' (s ∩ {o : Observation | o.2 ∈ C})))) ⊆ C := by
    intro x hx
    by_contra hxC
    apply hx
    simp [hxC]
  rw [← setLIntegral_eq_of_support_subset hsupp,
    ← setLIntegral_eq_of_support_subset hsupp']
  rw [hnu]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem hC] with x hx
  change (bernoulliGaussianLaw (p x))
      (Prod.mk x ⁻¹' (Prod.swap ⁻¹' (s ∩ {o : Observation | o.2 ∈ C}))) =
    (bernoulliGaussianLaw (p' x))
      (Prod.mk x ⁻¹' (Prod.swap ⁻¹' (s ∩ {o : Observation | o.2 ∈ C})))
  rw [hparam x hx]

/-- The joint law restricted to a packing cell depends on the Boolean vertex
only through the bit indexing that cell. -/
-- @node: angularPackingCtyLaw_restrict_cell_eq
lemma angularPackingCtyLaw_restrict_cell_eq {M : ℕ} {b cA delta w : ℝ}
    (hb : 0 < b) (hbSmall : |b| ≤ 1 / 4)
    (hscale : 0 < cA * delta) (hcA : 8 ≤ cA)
    (hdelta : 0 < delta) (hdeltaSmall : delta ≤ 1 / 8)
    (hw : 0 < w) (hwQuarter : w ≤ 1 / 4)
    (hsep : ∀ i k : Fin M, i ≠ k →
      3 * w ≤ dist (angularGridCenter M i) (angularGridCenter M k))
    {omega omega' : Fin M → Bool} {j : Fin M}
    (hbit : omega j = omega' j) :
    (angularPackingCtyLaw b cA delta w omega hb hscale hcA hdelta hw
      hwQuarter hsep).law.restrict
        {o | o.2 ∈ packingCell (angularGridCenter M) w j} =
      (angularPackingCtyLaw b cA delta w omega' hb hscale hcA hdelta hw
        hwQuarter hsep).law.restrict
          {o | o.2 ∈ packingCell (angularGridCenter M) w j} := by
  letI : IsProbabilityMeasure
      (angularDesignMeasure b cA delta w (angularGridCenter M) omega) :=
    angularDesignMeasure_isProbabilityMeasure hb hscale hcA hdelta hw
      hwQuarter hsep omega
  letI : IsProbabilityMeasure
      (angularDesignMeasure b cA delta w (angularGridCenter M) omega') :=
    angularDesignMeasure_isProbabilityMeasure hb hscale hcA hdelta hw
      hwQuarter hsep omega'
  let C := packingCell (angularGridCenter M) w j
  have hC : MeasurableSet C :=
    Metric.isClosed_closedBall.measurableSet.inter
      packingSquare_isCompact.isClosed.measurableSet
  have hnu := angularDesignMeasure_restrict_cell_eq
    (b := b) (cA := cA) (delta := delta) hw hsep hbit
  have hp : ∀ x ∈ C,
      clippedPackingRegression b delta w (angularGridCenter M) omega x =
        clippedPackingRegression b delta w (angularGridCenter M) omega' x := by
    intro x hx
    exact clippedPackingRegression_eq_on_cell hbSmall hdelta.le hdeltaSmall
      hw hsep hbit hx
  simpa only [angularPackingCtyLaw, bernoulliGaussianCtyLaw] using
    jointBernoulliGaussianLaw_restrict_score_eq
      (angularDesignMeasure b cA delta w (angularGridCenter M) omega)
      (angularDesignMeasure b cA delta w (angularGridCenter M) omega')
      (clippedPackingRegression b delta w (angularGridCenter M) omega)
      (clippedPackingRegression b delta w (angularGridCenter M) omega')
      (clippedPackingRegression_measurable b delta w (angularGridCenter M) omega)
      (clippedPackingRegression_measurable b delta w (angularGridCenter M) omega')
      (fun x ↦ (clippedPackingRegression_mem_Icc b delta w
        (angularGridCenter M) omega x).1)
      (fun x ↦ (clippedPackingRegression_mem_Icc b delta w
        (angularGridCenter M) omega x).2)
      (fun x ↦ (clippedPackingRegression_mem_Icc b delta w
        (angularGridCenter M) omega' x).1)
      (fun x ↦ (clippedPackingRegression_mem_Icc b delta w
        (angularGridCenter M) omega' x).2)
      hC hnu hp

/-- The joint law outside all square-truncated packing cells is independent of
the Boolean packing vertex. -/
-- @node: angularPackingCtyLaw_restrict_off_cells_eq
lemma angularPackingCtyLaw_restrict_off_cells_eq {M : ℕ}
    {b cA delta w : ℝ}
    (hb : 0 < b) (hbSmall : |b| ≤ 1 / 4)
    (hscale : 0 < cA * delta) (hcA : 8 ≤ cA)
    (hdelta : 0 < delta) (hdeltaSmall : delta ≤ 1 / 8)
    (hw : 0 < w) (hwQuarter : w ≤ 1 / 4)
    (hsep : ∀ i k : Fin M, i ≠ k →
      3 * w ≤ dist (angularGridCenter M i) (angularGridCenter M k))
    (omega omega' : Fin M → Bool) :
    (angularPackingCtyLaw b cA delta w omega hb hscale hcA hdelta hw
      hwQuarter hsep).law.restrict
        {o | o.2 ∈ packingSquare \ ⋃ j,
          packingCell (angularGridCenter M) w j} =
      (angularPackingCtyLaw b cA delta w omega' hb hscale hcA hdelta hw
        hwQuarter hsep).law.restrict
          {o | o.2 ∈ packingSquare \ ⋃ j,
            packingCell (angularGridCenter M) w j} := by
  letI : IsProbabilityMeasure
      (angularDesignMeasure b cA delta w (angularGridCenter M) omega) :=
    angularDesignMeasure_isProbabilityMeasure hb hscale hcA hdelta hw
      hwQuarter hsep omega
  letI : IsProbabilityMeasure
      (angularDesignMeasure b cA delta w (angularGridCenter M) omega') :=
    angularDesignMeasure_isProbabilityMeasure hb hscale hcA hdelta hw
      hwQuarter hsep omega'
  let C := packingSquare \ ⋃ j,
    packingCell (angularGridCenter M) w j
  have hC : MeasurableSet C :=
    packingSquare_isCompact.isClosed.measurableSet.diff
      (MeasurableSet.iUnion fun _ =>
        Metric.isClosed_closedBall.measurableSet.inter
          packingSquare_isCompact.isClosed.measurableSet)
  have hnu := angularDesignMeasure_restrict_off_cells_eq
    (b := b) (cA := cA) (delta := delta) hw
      (centers := angularGridCenter M) omega omega'
  have hp : ∀ x ∈ C,
      clippedPackingRegression b delta w (angularGridCenter M) omega x =
        clippedPackingRegression b delta w (angularGridCenter M) omega' x := by
    intro x hx
    have hxBalls : ∀ j, x ∉ Metric.closedBall (angularGridCenter M j) w := by
      intro j hxj
      exact hx.2 (Set.mem_iUnion.2 ⟨j, hxj, hx.1⟩)
    rw [clippedPackingRegression_eq_on_square hbSmall hdelta.le hdeltaSmall
      hw hsep omega hx.1,
      clippedPackingRegression_eq_on_square hbSmall hdelta.le hdeltaSmall
        hw hsep omega' hx.1,
      packingRegression_eq_off_cells hw omega hxBalls,
      packingRegression_eq_off_cells hw omega' hxBalls]
  exact jointBernoulliGaussianLaw_restrict_score_eq
      (angularDesignMeasure b cA delta w (angularGridCenter M) omega)
      (angularDesignMeasure b cA delta w (angularGridCenter M) omega')
      (clippedPackingRegression b delta w (angularGridCenter M) omega)
      (clippedPackingRegression b delta w (angularGridCenter M) omega')
      (clippedPackingRegression_measurable b delta w (angularGridCenter M) omega)
      (clippedPackingRegression_measurable b delta w (angularGridCenter M) omega')
      (fun x ↦ (clippedPackingRegression_mem_Icc b delta w
        (angularGridCenter M) omega x).1)
      (fun x ↦ (clippedPackingRegression_mem_Icc b delta w
        (angularGridCenter M) omega x).2)
      (fun x ↦ (clippedPackingRegression_mem_Icc b delta w
        (angularGridCenter M) omega' x).1)
      (fun x ↦ (clippedPackingRegression_mem_Icc b delta w
        (angularGridCenter M) omega' x).2)
      hC hnu hp

end CausalSmith.Stat.BddUniformLogPenalty
