import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Helpers.AngularLaw
import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Helpers.AngularRadial

/-!
# Radial outcome representation for the angular packing

This module rewrites the one-observation distance-compressed law of an angular
packing vertex directly as the pushforward of its score-first disintegration.
The representation is the bridge from radial cancellation to the exceptional-
radius equality and one-point KL estimates used by the final certificate.
-/

open MeasureTheory ProbabilityTheory Set

namespace CausalSmith.Stat.BddUniformLogPenalty

/-- Equality of radius pushforwards gives equality of the base mass on every
measurable radial slice.  This is the mass half of the Bernoulli--Gaussian
radial-fibre comparison. -/
-- @node: radialSlice_mass_eq_of_map_distance_eq
lemma radialSlice_mass_eq_of_map_distance_eq
    (nu nu' : Measure Score) (center : Score)
    (hmap : Measure.map (fun x : Score => dist x center) nu =
      Measure.map (fun x : Score => dist x center) nu')
    {A : Set ℝ} (hA : MeasurableSet A) :
    nu {x | dist x center ∈ A} = nu' {x | dist x center ∈ A} := by
  have hradial : Measurable (fun x : Score => dist x center) := by fun_prop
  change nu ((fun x : Score => dist x center) ⁻¹' A) =
    nu' ((fun x : Score => dist x center) ⁻¹' A)
  rw [← Measure.map_apply hradial hA, ← Measure.map_apply hradial hA, hmap]

/-- A rectangle under a radius--outcome pushforward of a composition product
is the fibre probability integrated over the corresponding radial slice of
the base measure.  This is the rectangle-level disintegration identity used
to turn the setwise polar cancellation lemmas into equality of radial-outcome
measures. -/
-- @node: map_radiusOutcome_compProd_apply_prod
lemma map_radiusOutcome_compProd_apply_prod
    (nu : Measure Score) [SFinite nu] (k : Kernel Score ℝ)
    [IsSFiniteKernel k] (center : Score) {A B : Set ℝ}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (Measure.map (fun z : Score × ℝ => (z.2, dist z.1 center))
      (Measure.compProd nu k)) (A ×ˢ B) =
      ∫⁻ x in {x | dist x center ∈ B}, k x A ∂nu := by
  rw [Measure.map_apply (by fun_prop) (hA.prod hB),
    Measure.compProd_apply ((hA.prod hB).preimage (by fun_prop))]
  rw [← lintegral_indicator (show MeasurableSet
    {x : Score | dist x center ∈ B} from hB.preimage (by fun_prop))]
  congr 1
  funext x
  by_cases hx : dist x center ∈ B
  · have hx' : x ∈ {x : Score | dist x center ∈ B} := hx
    rw [Set.indicator_of_mem hx']
    congr 1
    ext y
    simp [hx]
  · have hx' : x ∉ {x : Score | dist x center ∈ B} := hx
    rw [Set.indicator_of_notMem hx']
    have hset : Prod.mk x ⁻¹'
        ((fun z : Score × ℝ => (z.2, dist z.1 center)) ⁻¹' (A ×ˢ B)) = ∅ := by
      ext y
      simp [hx]
    rw [hset]
    simp

/-- Equality of all outcome probabilities on all radial slices beyond `R`
assembles into equality of the two restricted radius--outcome laws.  The
hypothesis is deliberately rectangle-level, matching the output of the polar
integral calculations. -/
-- @node: map_radiusOutcome_compProd_restrict_Ici_eq
lemma map_radiusOutcome_compProd_restrict_Ici_eq
    (nu nu' : Measure Score) [IsFiniteMeasure nu] [IsFiniteMeasure nu']
    (k k' : Kernel Score ℝ) [IsFiniteKernel k] [IsFiniteKernel k']
    (center : Score) (R : ℝ)
    (hslices : ∀ (A B : Set ℝ), MeasurableSet A → MeasurableSet B →
      (∫⁻ x in {x | dist x center ∈ B ∩ Ici R}, k x A ∂nu) =
        ∫⁻ x in {x | dist x center ∈ B ∩ Ici R}, k' x A ∂nu') :
    (Measure.map (fun z : Score × ℝ => (z.2, dist z.1 center))
        (Measure.compProd nu k)).restrict {z | R ≤ z.2} =
      (Measure.map (fun z : Score × ℝ => (z.2, dist z.1 center))
        (Measure.compProd nu' k')).restrict {z | R ≤ z.2} := by
  apply Measure.ext_prod
  intro A B hA hB
  rw [Measure.restrict_apply (hA.prod hB),
    Measure.restrict_apply (hA.prod hB)]
  have hset : (A ×ˢ B) ∩ {z : ℝ × ℝ | R ≤ z.2} = A ×ˢ (B ∩ Ici R) := by
    ext z
    simp [and_left_comm, and_comm]
  rw [hset,
    map_radiusOutcome_compProd_apply_prod nu k center hA
      (hB.inter measurableSet_Ici),
    map_radiusOutcome_compProd_apply_prod nu' k' center hA
      (hB.inter measurableSet_Ici)]
  exact hslices A B hA hB

/-- The one-point radial-outcome law of an angular packing vertex is the
pushforward of the explicit score design and Bernoulli--Gaussian fibre kernel.
This keeps the score first until the final map, exposing the radial fibres used
by the cancellation argument. -/
-- @node: angularPackingCtyLaw_onePointDistanceLaw_eq_map_compProd
lemma angularPackingCtyLaw_onePointDistanceLaw_eq_map_compProd
    {M : ℕ} {b cA delta w : ℝ} (hb : 0 < b)
    (hscale : 0 < cA * delta) (hcA : 8 ≤ cA) (hdelta : 0 < delta)
    (hw0 : 0 < w) (hw : w ≤ 1 / 4)
    (hsep : ∀ i k : Fin M, i ≠ k →
      3 * w ≤ dist (angularGridCenter M i) (angularGridCenter M k))
    (omega : Fin M → Bool) (center : Score) :
    onePointDistanceLaw
        (angularPackingCtyLaw b cA delta w omega hb hscale hcA hdelta hw0 hw hsep)
        center =
      Measure.map (fun z : Score × ℝ => (z.2, dist z.1 center))
        (Measure.compProd
          (angularDesignMeasure b cA delta w (angularGridCenter M) omega)
          (bernoulliGaussianKernel
            (clippedPackingRegression b delta w (angularGridCenter M) omega)
            (clippedPackingRegression_measurable b delta w
              (angularGridCenter M) omega))) := by
  let nu := angularDesignMeasure b cA delta w (angularGridCenter M) omega
  let p := clippedPackingRegression b delta w (angularGridCenter M) omega
  letI : IsProbabilityMeasure nu :=
    angularDesignMeasure_isProbabilityMeasure hb hscale hcA hdelta hw0 hw hsep omega
  have h0 : ∀ x, 0 ≤ p x := fun x =>
    (clippedPackingRegression_mem_Icc b delta w (angularGridCenter M) omega x).1
  have h1 : ∀ x, p x ≤ 1 := fun x =>
    (clippedPackingRegression_mem_Icc b delta w (angularGridCenter M) omega x).2
  unfold onePointDistanceLaw angularPackingCtyLaw bernoulliGaussianCtyLaw
  dsimp only
  unfold jointBernoulliGaussianLaw
  rw [Measure.map_map (by fun_prop) measurable_swap]
  rfl

/-- Rectangle probabilities of the angular radial-outcome law are obtained by
integrating its explicit Bernoulli--Gaussian fibre over a radial slice of the
angular score design. -/
-- @node: angularPackingCtyLaw_onePointDistanceLaw_apply_prod
lemma angularPackingCtyLaw_onePointDistanceLaw_apply_prod
    {M : ℕ} {b cA delta w : ℝ} (hb : 0 < b)
    (hscale : 0 < cA * delta) (hcA : 8 ≤ cA) (hdelta : 0 < delta)
    (hw0 : 0 < w) (hw : w ≤ 1 / 4)
    (hsep : ∀ i k : Fin M, i ≠ k →
      3 * w ≤ dist (angularGridCenter M i) (angularGridCenter M k))
    (omega : Fin M → Bool) (center : Score) {A B : Set ℝ}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    onePointDistanceLaw
        (angularPackingCtyLaw b cA delta w omega hb hscale hcA hdelta hw0 hw hsep)
        center (A ×ˢ B) =
      ∫⁻ x in {x | dist x center ∈ B},
        bernoulliGaussianKernel
          (clippedPackingRegression b delta w (angularGridCenter M) omega)
          (clippedPackingRegression_measurable b delta w
            (angularGridCenter M) omega) x A
        ∂(angularDesignMeasure b cA delta w (angularGridCenter M) omega) := by
  letI : IsProbabilityMeasure
      (angularDesignMeasure b cA delta w (angularGridCenter M) omega) :=
    angularDesignMeasure_isProbabilityMeasure hb hscale hcA hdelta hw0 hw
      hsep omega
  letI : IsMarkovKernel
      (bernoulliGaussianKernel
        (clippedPackingRegression b delta w (angularGridCenter M) omega)
        (clippedPackingRegression_measurable b delta w
          (angularGridCenter M) omega)) :=
    bernoulliGaussianKernel_isMarkovKernel _ _
      (fun x => (clippedPackingRegression_mem_Icc b delta w
        (angularGridCenter M) omega x).1)
      (fun x => (clippedPackingRegression_mem_Icc b delta w
        (angularGridCenter M) omega x).2)
  rw [angularPackingCtyLaw_onePointDistanceLaw_eq_map_compProd hb hscale hcA
    hdelta hw0 hw hsep omega center]
  exact map_radiusOutcome_compProd_apply_prod _ _ center hA hB

/-- The fully-active angular outcome cancellation, transported from planar
coordinates to the Euclidean score space at a lower-edge grid center.  This
is the score-space form consumed by the radial fibre-law comparison. -/
-- @node: angularGridCenter_radialSet_angular_outcome_cancellation
lemma angularGridCenter_radialSet_angular_outcome_cancellation
    {M : ℕ} (j : Fin M) {b cA delta w : ℝ}
    (hscale : 0 < cA * delta) {A : Set ℝ} (hA : MeasurableSet A)
    (hactive : ∀ r ∈ A, 2 * (cA * delta) ≤ b * r) :
    let c := angularGridCenter M j
    let D : Set Score :=
      {x | 0 < (scoreCoordinates x - scoreCoordinates c).2 ∧ dist x c ≤ w} ∩
        {x | dist x c ∈ A}
    (∫ x in D, delta * angularRadialProfile w (dist x c)) +
      (∫ x in D,
        b * (scoreCoordinates x - scoreCoordinates c).1 *
          angularTilt b cA delta w (dist x c) *
          ((scoreCoordinates x - scoreCoordinates c).1 / dist x c)) = 0 := by
  dsimp only
  let c : Score := angularGridCenter M j
  let cp : ℝ × ℝ := scoreCoordinates c
  let D : Set Score :=
    {x | 0 < (scoreCoordinates x - scoreCoordinates c).2 ∧ dist x c ≤ w} ∩
      {x | dist x c ∈ A}
  let E : Set (ℝ × ℝ) :=
    {z | 0 < (z - cp).2 ∧ planarRadius (z - cp) ≤ w} ∩
      {z | planarRadius (z - cp) ∈ A}
  have himage : scoreCoordinates '' D = E := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa [D, E, cp, c, planarRadius_scoreCoordinates_sub] using hx
    · intro hz
      let x : Score := scorePoint z.1 z.2
      have hcoord : scoreCoordinates x = z := by
        ext <;> simp [x, scoreCoordinates, scorePoint_apply_zero,
          scorePoint_apply_one]
      have hdist : dist x c = planarRadius (z - scoreCoordinates c) := by
        rw [← planarRadius_scoreCoordinates_sub]
        rw [hcoord]
      refine ⟨x, ?_, hcoord⟩
      simpa [D, E, cp, c, hcoord, hdist] using hz
  have hfirst : (fun x : Score =>
      delta * angularRadialProfile w (dist x c)) =
      fun x => delta * angularRadialProfile w
        (planarRadius (scoreCoordinates x - scoreCoordinates c)) := by
    funext x
    rw [planarRadius_scoreCoordinates_sub]
  have hsecond : (fun x : Score =>
      b * (scoreCoordinates x - scoreCoordinates c).1 *
        angularTilt b cA delta w (dist x c) *
        ((scoreCoordinates x - scoreCoordinates c).1 / dist x c)) =
      fun x =>
        b * (scoreCoordinates x - scoreCoordinates c).1 *
          angularTilt b cA delta w
            (planarRadius (scoreCoordinates x - scoreCoordinates c)) *
          ((scoreCoordinates x - scoreCoordinates c).1 /
            planarRadius (scoreCoordinates x - scoreCoordinates c)) := by
    funext x
    rw [planarRadius_scoreCoordinates_sub]
  rw [hfirst, hsecond]
  rw [← scoreCoordinates_measurePreserving.setIntegral_image_emb
      scoreCoordinates_measurableEmbedding
      (fun z : ℝ × ℝ =>
        delta * angularRadialProfile w (planarRadius (z - scoreCoordinates c))) D,
    ← scoreCoordinates_measurePreserving.setIntegral_image_emb
      scoreCoordinates_measurableEmbedding
      (fun z : ℝ × ℝ =>
        b * (z - scoreCoordinates c).1 *
          angularTilt b cA delta w (planarRadius (z - scoreCoordinates c)) *
          ((z - scoreCoordinates c).1 / planarRadius (z - scoreCoordinates c))) D]
  rw [himage]
  simpa [E, cp, c] using
    translatedHalfDisc_radialSet_angular_outcome_cancellation
      (w := w) (R := w) hscale (scoreCoordinates (angularGridCenter M j)) hA hactive

/-- On a fixed score slice, a Bernoulli--Gaussian mixture is determined by
the slice mass and the slice integral of its Bernoulli parameter.  This is the
measure-theoretic bridge from the two polar cancellation identities to
equality of radial outcome fibres. -/
-- @node: bernoulliGaussianKernel_setLIntegral_eq_of_mass_and_mean
lemma bernoulliGaussianKernel_setLIntegral_eq_of_mass_and_mean
    (nu nu' : Measure Score) [IsFiniteMeasure nu] [IsFiniteMeasure nu']
    (p p' : Score → ℝ) (hp : Measurable p) (hp' : Measurable p')
    (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∀ x, p x ≤ 1)
    (hp0' : ∀ x, 0 ≤ p' x) (hp1' : ∀ x, p' x ≤ 1)
    {D : Set Score} (hmass : nu D = nu' D)
    (hmean : ∫ x in D, p x ∂nu = ∫ x in D, p' x ∂nu')
    (A : Set ℝ) :
    (∫⁻ x in D, bernoulliGaussianKernel p hp x A ∂nu) =
      ∫⁻ x in D, bernoulliGaussianKernel p' hp' x A ∂nu' := by
  have hpInt : IntegrableOn p D nu := by
    apply Measure.integrableOn_of_bounded (measure_ne_top nu D) hp.aestronglyMeasurable
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [hp0 x], hp1 x⟩
  have hpInt' : IntegrableOn p' D nu' := by
    apply Measure.integrableOn_of_bounded (measure_ne_top nu' D) hp'.aestronglyMeasurable
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [hp0' x], hp1' x⟩
  have hqInt : IntegrableOn (fun x => 1 - p x) D nu :=
    (integrableOn_const (s := D) (C := (1 : ℝ))).sub hpInt
  have hqInt' : IntegrableOn (fun x => 1 - p' x) D nu' :=
    (integrableOn_const (s := D) (C := (1 : ℝ))).sub hpInt'
  have hpL : (∫⁻ x in D, ENNReal.ofReal (p x) ∂nu) =
      ∫⁻ x in D, ENNReal.ofReal (p' x) ∂nu' := by
    rw [← ofReal_integral_eq_lintegral_ofReal hpInt
      (Filter.Eventually.of_forall fun x => hp0 x),
      ← ofReal_integral_eq_lintegral_ofReal hpInt'
        (Filter.Eventually.of_forall fun x => hp0' x), hmean]
  have hqmean : ∫ x in D, (1 - p x) ∂nu =
      ∫ x in D, (1 - p' x) ∂nu' := by
    rw [integral_sub (integrableOn_const (s := D) (C := (1 : ℝ))) hpInt,
      integral_sub (integrableOn_const (s := D) (C := (1 : ℝ))) hpInt']
    simp only [integral_const, Measure.real_def]
    rw [Measure.restrict_apply_univ, Measure.restrict_apply_univ]
    rw [hmass, hmean]
  have hqL : (∫⁻ x in D, ENNReal.ofReal (1 - p x) ∂nu) =
      ∫⁻ x in D, ENNReal.ofReal (1 - p' x) ∂nu' := by
    rw [← ofReal_integral_eq_lintegral_ofReal hqInt
      (Filter.Eventually.of_forall fun x => sub_nonneg.mpr (hp1 x)),
      ← ofReal_integral_eq_lintegral_ofReal hqInt'
        (Filter.Eventually.of_forall fun x => sub_nonneg.mpr (hp1' x)), hqmean]
  simp only [bernoulliGaussianKernel, Kernel.coe_mk,
    bernoulliGaussianLaw_eq_gaussian_mixture, Measure.add_apply,
    Measure.smul_apply, smul_eq_mul]
  change (∫⁻ x, ENNReal.ofReal (p x) * (gaussianReal 1 1) A +
      ENNReal.ofReal (1 - p x) * (gaussianReal 0 1) A ∂( nu.restrict D)) =
    ∫⁻ x, ENNReal.ofReal (p' x) * (gaussianReal 1 1) A +
      ENNReal.ofReal (1 - p' x) * (gaussianReal 0 1) A ∂(nu'.restrict D)
  rw [lintegral_add_left
      (show Measurable (fun x => ENNReal.ofReal (p x) *
        (gaussianReal 1 1) A) by fun_prop) _,
    lintegral_add_left
      (show Measurable (fun x => ENNReal.ofReal (p' x) *
        (gaussianReal 1 1) A) by fun_prop) _]
  simp_rw [mul_comm (ENNReal.ofReal (p _)), mul_comm (ENNReal.ofReal (1 - p _)),
    mul_comm (ENNReal.ofReal (p' _)), mul_comm (ENNReal.ofReal (1 - p' _))]
  have hmulP : (∫⁻ x in D, (gaussianReal 1 1) A * ENNReal.ofReal (p x) ∂nu) =
      (gaussianReal 1 1) A * ∫⁻ x in D, ENNReal.ofReal (p x) ∂nu := by
    exact lintegral_const_mul _ (by fun_prop)
  have hmulQ : (∫⁻ x in D, (gaussianReal 0 1) A * ENNReal.ofReal (1 - p x) ∂nu) =
      (gaussianReal 0 1) A * ∫⁻ x in D, ENNReal.ofReal (1 - p x) ∂nu := by
    exact lintegral_const_mul _ (by fun_prop)
  have hmulP' : (∫⁻ x in D, (gaussianReal 1 1) A * ENNReal.ofReal (p' x) ∂nu') =
      (gaussianReal 1 1) A * ∫⁻ x in D, ENNReal.ofReal (p' x) ∂nu' := by
    exact lintegral_const_mul _ (by fun_prop)
  have hmulQ' : (∫⁻ x in D, (gaussianReal 0 1) A * ENNReal.ofReal (1 - p' x) ∂nu') =
      (gaussianReal 0 1) A * ∫⁻ x in D, ENNReal.ofReal (1 - p' x) ∂nu' := by
    exact lintegral_const_mul _ (by fun_prop)
  rw [hmulP, hmulQ, hmulP', hmulQ', hpL, hqL]

/-- Rectangle-level radial fibre identities for two angular vertices imply
equality of their complete radius--outcome laws beyond the stated cutoff.
This packages the explicit score-first disintegrations with the product-set
extension argument, so the packing theorem only has to supply the polar slice
calculation. -/
-- @node: angularPackingCtyLaw_restrict_Ici_eq_of_radial_slices
lemma angularPackingCtyLaw_restrict_Ici_eq_of_radial_slices
    {M : ℕ} {b cA delta w R : ℝ}
    (hb : 0 < b) (hscale : 0 < cA * delta) (hcA : 8 ≤ cA)
    (hdelta : 0 < delta) (hw0 : 0 < w) (hw : w ≤ 1 / 4)
    (hsep : ∀ i k : Fin M, i ≠ k →
      3 * w ≤ dist (angularGridCenter M i) (angularGridCenter M k))
    (omega omega' : Fin M → Bool) (j : Fin M)
    (hslices : ∀ (A B : Set ℝ), MeasurableSet A → MeasurableSet B →
      (∫⁻ x in {x | dist x (angularGridCenter M j) ∈ B ∩ Ici R},
          bernoulliGaussianKernel
            (clippedPackingRegression b delta w (angularGridCenter M) omega)
            (clippedPackingRegression_measurable b delta w
              (angularGridCenter M) omega) x A
          ∂(angularDesignMeasure b cA delta w (angularGridCenter M) omega)) =
        ∫⁻ x in {x | dist x (angularGridCenter M j) ∈ B ∩ Ici R},
          bernoulliGaussianKernel
            (clippedPackingRegression b delta w (angularGridCenter M) omega')
            (clippedPackingRegression_measurable b delta w
              (angularGridCenter M) omega') x A
          ∂(angularDesignMeasure b cA delta w (angularGridCenter M) omega')) :
    (onePointDistanceLaw
        (angularPackingCtyLaw b cA delta w omega hb hscale hcA hdelta hw0 hw hsep)
        (angularGridCenter M j)).restrict {z | R ≤ z.2} =
      (onePointDistanceLaw
        (angularPackingCtyLaw b cA delta w omega' hb hscale hcA hdelta hw0 hw hsep)
        (angularGridCenter M j)).restrict {z | R ≤ z.2} := by
  let nu := angularDesignMeasure b cA delta w (angularGridCenter M) omega
  let nu' := angularDesignMeasure b cA delta w (angularGridCenter M) omega'
  let p := clippedPackingRegression b delta w (angularGridCenter M) omega
  let p' := clippedPackingRegression b delta w (angularGridCenter M) omega'
  let hp := clippedPackingRegression_measurable b delta w
    (angularGridCenter M) omega
  let hp' := clippedPackingRegression_measurable b delta w
    (angularGridCenter M) omega'
  let k := bernoulliGaussianKernel p hp
  let k' := bernoulliGaussianKernel p' hp'
  letI : IsProbabilityMeasure nu :=
    angularDesignMeasure_isProbabilityMeasure hb hscale hcA hdelta hw0 hw hsep omega
  letI : IsProbabilityMeasure nu' :=
    angularDesignMeasure_isProbabilityMeasure hb hscale hcA hdelta hw0 hw hsep omega'
  letI : IsMarkovKernel k := bernoulliGaussianKernel_isMarkovKernel p hp
    (fun x => (clippedPackingRegression_mem_Icc b delta w
      (angularGridCenter M) omega x).1)
    (fun x => (clippedPackingRegression_mem_Icc b delta w
      (angularGridCenter M) omega x).2)
  letI : IsMarkovKernel k' := bernoulliGaussianKernel_isMarkovKernel p' hp'
    (fun x => (clippedPackingRegression_mem_Icc b delta w
      (angularGridCenter M) omega' x).1)
    (fun x => (clippedPackingRegression_mem_Icc b delta w
      (angularGridCenter M) omega' x).2)
  rw [angularPackingCtyLaw_onePointDistanceLaw_eq_map_compProd hb hscale hcA
      hdelta hw0 hw hsep omega (angularGridCenter M j),
    angularPackingCtyLaw_onePointDistanceLaw_eq_map_compProd hb hscale hcA
      hdelta hw0 hw hsep omega' (angularGridCenter M j)]
  apply map_radiusOutcome_compProd_restrict_Ici_eq nu nu' k k'
    (angularGridCenter M j) R
  simpa [nu, nu', p, p', hp, hp', k, k'] using hslices

end CausalSmith.Stat.BddUniformLogPenalty
