import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Helpers.AngularRadialOnePointKL
import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Helpers.AngularRadialQuantitative
import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Helpers.AngularScaledDelta
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Construction-specific one-point KL bound

This module connects the common-radius KL interface to the angular packing,
including its middle-half parameter clipping and short-radius mass bound.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace CausalSmith.Stat.BddUniformLogPenalty

/-- Pointwise clipping to the middle half of the Bernoulli parameter range. -/
-- @node: middleHalfClip
noncomputable def middleHalfClip (f : Score → ℝ) : Score → ℝ :=
  fun x => max (1 / 4 : ℝ) (min (3 / 4 : ℝ) (f x))

-- @node: middleHalfClip_measurable
/-- The stated statistic is a measurable function of the observed data, so it is a valid random quantity. -/
lemma middleHalfClip_measurable {f : Score → ℝ} (hf : Measurable f) :
    Measurable (middleHalfClip f) := by
  unfold middleHalfClip
  fun_prop

-- @node: middleHalfClip_mem_Icc
/-- The clipped success parameter lies in the displayed closed interval. -/
lemma middleHalfClip_mem_Icc (f : Score → ℝ) (x : Score) :
    middleHalfClip f x ∈ Icc (1 / 4 : ℝ) (3 / 4 : ℝ) := by
  unfold middleHalfClip
  constructor <;> simp <;> norm_num

/-- On an admissible angular design, middle-half clipping is silent almost
everywhere because the design is supported on the packing square. -/
-- @node: middleHalfClip_clippedPackingRegression_ae_eq
lemma middleHalfClip_clippedPackingRegression_ae_eq
    {M : ℕ} {b cA delta w : ℝ}
    (hb : 0 < b) (hbSmall : |b| ≤ 1 / 4)
    (hscale : 0 < cA * delta) (hcA : 8 ≤ cA)
    (hdelta : 0 < delta) (hdeltaSmall : delta ≤ 1 / 8)
    (hw : 0 < w)
    (hsep : ∀ i k : Fin M, i ≠ k →
      3 * w ≤ dist (angularGridCenter M i) (angularGridCenter M k))
    (omega : Fin M → Bool) :
    middleHalfClip (clippedPackingRegression b delta w
      (angularGridCenter M) omega) =ᵐ[
        angularDesignMeasure b cA delta w (angularGridCenter M) omega]
      clippedPackingRegression b delta w (angularGridCenter M) omega := by
  have hsupp := angularDesignMeasure_support hb hscale hcA hdelta hw hsep omega
  have hmem : scoreCube (1 / 2 : ℝ) ∈ ae
      (angularDesignMeasure b cA delta w (angularGridCenter M) omega) := by
    rw [← hsupp]
    exact Measure.support_mem_ae
  filter_upwards [hmem] with x hx
  have hp := packingRegression_mem_Icc hbSmall hdelta.le hdeltaSmall hw hsep omega hx
  unfold middleHalfClip
  rw [clippedPackingRegression_eq_on_square hbSmall hdelta.le hdeltaSmall hw
    hsep omega hx]
  rw [min_eq_right hp.2, max_eq_right hp.1]

/-- The radius marginal of an admissible angular design assigns at most the
density envelope times the enclosing planar disk area to a short interval. -/
-- @node: angularDesignMeasure_radial_Iio_le
lemma angularDesignMeasure_radial_Iio_le
    {M : ℕ} (j : Fin M) {b cA delta w R : ℝ}
    (hcA : 8 ≤ cA) (hdelta : 0 < delta) (hw : 0 < w) (hR : 0 ≤ R)
    (hsep : ∀ i k : Fin M, i ≠ k →
      3 * w ≤ dist (angularGridCenter M i) (angularGridCenter M k))
    (omega : Fin M → Bool) :
    Measure.map (fun x : Score => dist x (angularGridCenter M j))
        (angularDesignMeasure b cA delta w (angularGridCenter M) omega)
        (Iio R) ≤ ENNReal.ofReal (5 * R ^ 2) := by
  rw [Measure.map_apply (by fun_prop) measurableSet_Iio,
    angularDesignMeasure_eq_restrict_withDensity,
    withDensity_apply _ (measurableSet_Iio.preimage (by fun_prop))]
  calc
    (∫⁻ x in {x | dist x (angularGridCenter M j) ∈ Iio R},
        ENNReal.ofReal
          (packingAngularDensity b cA delta w (angularGridCenter M) omega x)
        ∂volume.restrict (scoreCube (1 / 2))) ≤
        ∫⁻ _x in {x | dist x (angularGridCenter M j) ∈ Iio R},
          ENNReal.ofReal (5 / 4 : ℝ)
          ∂volume.restrict (scoreCube (1 / 2)) := by
      apply lintegral_mono
      intro x
      exact ENNReal.ofReal_le_ofReal
        (packingAngularDensity_mem_Icc hcA hdelta hw hsep omega x).2
    _ = ENNReal.ofReal (5 / 4 : ℝ) *
        (volume.restrict (scoreCube (1 / 2)))
          {x | dist x (angularGridCenter M j) ∈ Iio R} :=
      setLIntegral_const _ _
    _ ≤ ENNReal.ofReal (5 / 4 : ℝ) *
        volume (Metric.closedBall (angularGridCenter M j) R) := by
      apply mul_le_mul_right
      calc
        (volume.restrict (scoreCube (1 / 2)))
            {x | dist x (angularGridCenter M j) ∈ Iio R} ≤
            volume {x | dist x (angularGridCenter M j) ∈ Iio R} :=
          Measure.restrict_apply_le _ _
        _ ≤ volume (Metric.closedBall (angularGridCenter M j) R) := by
          apply measure_mono
          intro x hx
          simpa [Metric.mem_closedBall] using hx.le
    _ ≤ ENNReal.ofReal (5 * R ^ 2) := by
      rw [EuclideanSpace.volume_closedBall_fin_two, ← ENNReal.ofReal_pow hR,
        ← ENNReal.ofReal_mul (sq_nonneg R),
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ (5 / 4 : ℝ))]
      apply ENNReal.ofReal_le_ofReal
      nlinarith [Real.pi_pos.le, Real.pi_le_four, sq_nonneg R]

/-- For the fixed angular constants, one changed bit has one-observation
radius--outcome KL at most the declared fourth-order envelope. -/
-- @node: angularPacking_radialOutcome_klDiv_le
lemma angularPacking_radialOutcome_klDiv_le
    {M : ℕ} (j : Fin M) {delta w : ℝ}
    (hdelta : 0 < delta) (hdeltaSmall : delta ≤ 1 / 8)
    (hw : 0 < w) (hwQuarter : w ≤ 1 / 4)
    (hsep : ∀ i k : Fin M, i ≠ k →
      3 * w ≤ dist (angularGridCenter M i) (angularGridCenter M k))
    (omega : Fin M → Bool) :
    let nu := angularDesignMeasure (1 / 8) 8 delta w
      (angularGridCenter M) omega
    let omega' := Causalean.Stat.flipBit j omega
    let nu' := angularDesignMeasure (1 / 8) 8 delta w
      (angularGridCenter M) omega'
    let p := clippedPackingRegression (1 / 8) delta w
      (angularGridCenter M) omega
    let p' := clippedPackingRegression (1 / 8) delta w
      (angularGridCenter M) omega'
    InformationTheory.klDiv
        (Measure.map (fun z : Score × ℝ =>
          (z.2, dist z.1 (angularGridCenter M j)))
          (Measure.compProd nu (bernoulliGaussianKernel p
            (clippedPackingRegression_measurable (1 / 8) delta w
              (angularGridCenter M) omega))))
        (Measure.map (fun z : Score × ℝ =>
          (z.2, dist z.1 (angularGridCenter M j)))
          (Measure.compProd nu' (bernoulliGaussianKernel p'
            (clippedPackingRegression_measurable (1 / 8) delta w
              (angularGridCenter M) omega')))) ≤
      ENNReal.ofReal (angularPackingOnePointKLConstant * delta ^ 4) := by
  dsimp only
  let omega' := Causalean.Stat.flipBit j omega
  let nu := angularDesignMeasure (1 / 8) 8 delta w (angularGridCenter M) omega
  let nu' := angularDesignMeasure (1 / 8) 8 delta w (angularGridCenter M) omega'
  let p := clippedPackingRegression (1 / 8) delta w (angularGridCenter M) omega
  let p' := clippedPackingRegression (1 / 8) delta w (angularGridCenter M) omega'
  let pm := middleHalfClip p
  let pm' := middleHalfClip p'
  let hp := clippedPackingRegression_measurable (1 / 8) delta w
    (angularGridCenter M) omega
  let hp' := clippedPackingRegression_measurable (1 / 8) delta w
    (angularGridCenter M) omega'
  let hpm : Measurable pm := middleHalfClip_measurable hp
  let hpm' : Measurable pm' := middleHalfClip_measurable hp'
  letI : IsProbabilityMeasure nu := angularDesignMeasure_isProbabilityMeasure
    (by norm_num) (mul_pos (by norm_num) hdelta) (by norm_num) hdelta hw
      hwQuarter hsep omega
  letI : IsProbabilityMeasure nu' := angularDesignMeasure_isProbabilityMeasure
    (by norm_num) (mul_pos (by norm_num) hdelta) (by norm_num) hdelta hw
      hwQuarter hsep omega'
  letI : IsMarkovKernel (bernoulliGaussianKernel p hp) :=
    bernoulliGaussianKernel_isMarkovKernel p hp
      (fun x => (clippedPackingRegression_mem_Icc (1 / 8) delta w
        (angularGridCenter M) omega x).1)
      (fun x => (clippedPackingRegression_mem_Icc (1 / 8) delta w
        (angularGridCenter M) omega x).2)
  letI : IsMarkovKernel (bernoulliGaussianKernel p' hp') :=
    bernoulliGaussianKernel_isMarkovKernel p' hp'
      (fun x => (clippedPackingRegression_mem_Icc (1 / 8) delta w
        (angularGridCenter M) omega' x).1)
      (fun x => (clippedPackingRegression_mem_Icc (1 / 8) delta w
        (angularGridCenter M) omega' x).2)
  letI : IsMarkovKernel (bernoulliGaussianKernel pm hpm) :=
    bernoulliGaussianKernel_isMarkovKernel pm hpm
      (fun x => by linarith [(middleHalfClip_mem_Icc p x).1])
      (fun x => by linarith [(middleHalfClip_mem_Icc p x).2])
  letI : IsMarkovKernel (bernoulliGaussianKernel pm' hpm') :=
    bernoulliGaussianKernel_isMarkovKernel pm' hpm'
      (fun x => by linarith [(middleHalfClip_mem_Icc p' x).1])
      (fun x => by linarith [(middleHalfClip_mem_Icc p' x).2])
  have heq : pm =ᵐ[nu] p := by
    exact middleHalfClip_clippedPackingRegression_ae_eq (by norm_num)
      (by norm_num) (mul_pos (by norm_num) hdelta) (by norm_num) hdelta
      hdeltaSmall hw hsep omega
  have heq' : pm' =ᵐ[nu'] p' := by
    exact middleHalfClip_clippedPackingRegression_ae_eq (by norm_num)
      (by norm_num) (mul_pos (by norm_num) hdelta) (by norm_num) hdelta
      hdeltaSmall hw hsep omega'
  have hk : bernoulliGaussianKernel p hp =ᵐ[nu]
      bernoulliGaussianKernel pm hpm := by
    filter_upwards [heq] with x hx
    ext A hA
    simp [bernoulliGaussianKernel, hx]
  have hk' : bernoulliGaussianKernel p' hp' =ᵐ[nu']
      bernoulliGaussianKernel pm' hpm' := by
    filter_upwards [heq'] with x hx
    ext A hA
    simp [bernoulliGaussianKernel, hx]
  change InformationTheory.klDiv
      (Measure.map (fun z : Score × ℝ =>
        (z.2, dist z.1 (angularGridCenter M j)))
        (Measure.compProd nu (bernoulliGaussianKernel p hp)))
      (Measure.map (fun z : Score × ℝ =>
        (z.2, dist z.1 (angularGridCenter M j)))
        (Measure.compProd nu' (bernoulliGaussianKernel p' hp'))) ≤ _
  rw [Measure.compProd_congr hk, Measure.compProd_congr hk']
  have hmap : Measure.map (fun x : Score => dist x (angularGridCenter M j)) nu =
      Measure.map (fun x : Score => dist x (angularGridCenter M j)) nu' := by
    dsimp [nu, nu', omega']
    exact angularDesignMeasure_map_distance_eq j (by norm_num)
      (mul_pos (by norm_num) hdelta) (by norm_num) hdelta hw hwQuarter hsep
      omega (Causalean.Stat.flipBit j omega)
      (by intro k hkj; simp [Causalean.Stat.flipBit, hkj])
  have hraw := radialOutcomeLaw_klDiv_le_of_localized_success_bound
    nu nu' pm pm' hpm hpm'
    (fun x => (middleHalfClip_mem_Icc p x).1)
    (fun x => (middleHalfClip_mem_Icc p x).2)
    (fun x => (middleHalfClip_mem_Icc p' x).1)
    (fun x => (middleHalfClip_mem_Icc p' x).2)
    (angularGridCenter M j) hmap (D := 2 * delta) (by positivity)
    (E := Iio (128 * delta)) measurableSet_Iio
    (by
      intro A hA
      rw [integral_congr_ae (ae_restrict_of_ae heq),
        integral_congr_ae (ae_restrict_of_ae heq')]
      dsimp [p, p', nu, nu', omega']
      have hd := angularPacking_flip_success_setIntegral_abs_le
        (b := (1 / 8 : ℝ)) (cA := 8) (delta := delta) (w := w) j
        (by norm_num) (by norm_num) (mul_pos (by norm_num) hdelta)
        (by norm_num) hdelta hdeltaSmall hw hwQuarter hsep omega hA
      have hrewrite : 2 * (8 * delta) / (1 / 8 : ℝ) = 128 * delta := by ring
      rw [hrewrite] at hd
      exact hd.trans (by
        have hm : 0 ≤ (Measure.map
          (fun x : Score => dist x (angularGridCenter M j))
            (angularDesignMeasure (1 / 8) 8 delta w (angularGridCenter M) omega)
            (A ∩ Iio (128 * delta))).toReal := ENNReal.toReal_nonneg
        nlinarith))
  have hmass : Measure.map (fun x : Score => dist x (angularGridCenter M j)) nu
      (Iio (128 * delta)) ≤ ENNReal.ofReal (5 * (128 * delta) ^ 2) := by
    dsimp [nu]
    exact angularDesignMeasure_radial_Iio_le j (by norm_num) hdelta hw
      (by positivity) hsep omega
  apply hraw.trans
  calc
    ENNReal.ofReal (4 * (2 * delta) ^ 2) *
        Measure.map (fun x : Score => dist x (angularGridCenter M j)) nu
          (Iio (128 * delta)) ≤
      ENNReal.ofReal (4 * (2 * delta) ^ 2) *
        ENNReal.ofReal (5 * (128 * delta) ^ 2) := mul_le_mul_right hmass _
    _ = ENNReal.ofReal (angularPackingOnePointKLConstant * delta ^ 4) := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 4 * (2 * delta) ^ 2)]
      apply congrArg ENNReal.ofReal
      unfold angularPackingOnePointKLConstant
      ring

end CausalSmith.Stat.BddUniformLogPenalty
