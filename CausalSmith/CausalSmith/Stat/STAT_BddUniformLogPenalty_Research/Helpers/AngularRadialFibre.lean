import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Helpers.AngularRadialAlgebra

/-!
# Radial fibre cancellation for adjacent angular packing laws

This module assembles the pointwise product identity and polar cancellation
leaves needed by the eventual equality of radial outcome fibres.
-/

open MeasureTheory ProbabilityTheory Set

namespace CausalSmith.Stat.BddUniformLogPenalty

/-- Integrating the clipped regression under an angular design is exactly
Lebesgue integration of the untruncated regression times its design density
on the part of the set lying in the packing square.  This is the bookkeeping
bridge between the faithful score law and the polar cancellation identities. -/
-- @node: clippedPackingRegression_setIntegral_angularDesignMeasure
lemma clippedPackingRegression_setIntegral_angularDesignMeasure
    {M : ℕ} {b cA delta w : ℝ}
    (hb : 0 < b) (hbSmall : |b| ≤ 1 / 4) (hcA : 8 ≤ cA)
    (hscale : 0 < cA * delta)
    (hdelta : 0 < delta) (hdeltaSmall : delta ≤ 1 / 8)
    (hw : 0 < w)
    (hsep : ∀ i k : Fin M, i ≠ k →
      3 * w ≤ dist (angularGridCenter M i) (angularGridCenter M k))
    (omega : Fin M → Bool) {D : Set Score} (hD : MeasurableSet D) :
    (∫ x in D,
        clippedPackingRegression b delta w (angularGridCenter M) omega x
          ∂(angularDesignMeasure b cA delta w (angularGridCenter M) omega)) =
      ∫ x in D ∩ scoreCube (1 / 2 : ℝ),
        packingRegression b delta w (angularGridCenter M) omega x *
          packingAngularDensity b cA delta w (angularGridCenter M) omega x := by
  rw [angularDesignMeasure_eq_restrict_withDensity]
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul₀
    ((packingAngularDensity_measurable hb hscale
      (angularGridCenter M) omega).ennreal_ofReal.aemeasurable)
    (by simp) _ hD]
  rw [Measure.restrict_restrict hD, inter_comm]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem ((scoreCube_measurableSet _).inter hD)]
    with x hx
  rw [clippedPackingRegression_eq_on_square hbSmall hdelta.le hdeltaSmall hw
    hsep omega hx.1]
  have hdens0 : 0 ≤ packingAngularDensity b cA delta w
      (angularGridCenter M) omega x := by
    have hlo := (packingAngularDensity_mem_Icc (b := b) hcA hdelta hw
      hsep omega x).1
    linarith
  simp [ENNReal.toReal_ofReal hdens0, mul_comm]

/-- At a lower-edge grid center, a radial weight times the horizontal
direction cosine integrates to zero on every open-half-disc radial slice. -/
-- @node: angularGridCenter_openRadialSet_weighted_direction_cancellation
lemma angularGridCenter_openRadialSet_weighted_direction_cancellation
    {M : ℕ} (j : Fin M) (g : ℝ → ℝ) (w : ℝ)
    {A : Set ℝ} (hA : MeasurableSet A) :
    let c := angularGridCenter M j
    let D : Set Score :=
      {x | 0 < (scoreCoordinates x - scoreCoordinates c).2 ∧ dist x c ≤ w} ∩
        {x | dist x c ∈ A}
    (∫ x in D, g (dist x c) *
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
      refine ⟨x, ?_, hcoord⟩
      simpa [D, E, cp, c, hcoord, ← planarRadius_scoreCoordinates_sub] using hz
  have hfun : (fun x : Score => g (dist x c) *
      ((scoreCoordinates x - scoreCoordinates c).1 / dist x c)) =
      fun x => g (planarRadius (scoreCoordinates x - scoreCoordinates c)) *
        ((scoreCoordinates x - scoreCoordinates c).1 /
          planarRadius (scoreCoordinates x - scoreCoordinates c)) := by
    funext x
    rw [planarRadius_scoreCoordinates_sub]
  rw [hfun]
  rw [← scoreCoordinates_measurePreserving.setIntegral_image_emb
      scoreCoordinates_measurableEmbedding
      (fun z : ℝ × ℝ => g (planarRadius (z - scoreCoordinates c)) *
        ((z - scoreCoordinates c).1 / planarRadius (z - scoreCoordinates c))) D,
    himage]
  let T : (ℝ × ℝ) → (ℝ × ℝ) := fun u => cp + u
  let E0 : Set (ℝ × ℝ) :=
    {u | 0 < u.2 ∧ planarRadius u ≤ w} ∩ planarRadius ⁻¹' A
  have hT : MeasurableEmbedding T := (Homeomorph.addLeft cp).measurableEmbedding
  have hmp : MeasurePreserving T (volume : Measure (ℝ × ℝ)) volume :=
    measurePreserving_add_left volume cp
  have hE : E = T '' E0 := by
    ext z
    constructor
    · rintro ⟨hz, hAz⟩
      refine ⟨z - cp, ⟨?_, ?_⟩, by simp [T]⟩
      · simpa [E, E0] using hz
      · simpa [E, E0] using hAz
    · rintro ⟨u, ⟨hu, hAu⟩, rfl⟩
      simpa [E, E0, T] using And.intro hu hAu
  rw [hE, hmp.setIntegral_image_emb hT]
  have heq : (fun u : ℝ × ℝ =>
      g (planarRadius (T u - scoreCoordinates c)) *
        ((T u - scoreCoordinates c).1 /
          planarRadius (T u - scoreCoordinates c))) =
      fun u => g (planarRadius u) * (u.1 / planarRadius u) := by
    funext u
    simp [T, cp]
  rw [heq]
  simpa [E0] using
    halfDisc_radialSet_weighted_first_div_radius_cancellation g w hA

/-- For a true bit, the outcome-weighted design-density difference integrates
to zero on every fully active radial slice of its cell. -/
-- @node: packingRegression_density_flip_integral_eq_zero_of_active
lemma packingRegression_density_flip_integral_eq_zero_of_active
    {M : ℕ} (j : Fin M) {b cA delta w : ℝ}
    (hb : 0 < b) (hscale : 0 < cA * delta) (hw : 0 < w)
    (hsep : ∀ i k : Fin M, i ≠ k →
      3 * w ≤ dist (angularGridCenter M i) (angularGridCenter M k))
    (omega : Fin M → Bool) (hj : omega j = true)
    {A : Set ℝ} (hA : MeasurableSet A)
    (hactive : ∀ r ∈ A, 2 * (cA * delta) ≤ b * r) :
    let c := angularGridCenter M j
    let D : Set Score :=
      {x | 0 < (scoreCoordinates x - scoreCoordinates c).2 ∧ dist x c ≤ w} ∩
        {x | dist x c ∈ A}
    (∫ x in D,
      packingRegression b delta w (angularGridCenter M) omega x *
          packingAngularDensity b cA delta w (angularGridCenter M) omega x -
        packingRegression b delta w (angularGridCenter M)
            (Causalean.Stat.flipBit j omega) x *
          packingAngularDensity b cA delta w (angularGridCenter M)
            (Causalean.Stat.flipBit j omega) x) = 0 := by
  dsimp only
  let c := angularGridCenter M j
  let D : Set Score :=
    {x | 0 < (scoreCoordinates x - scoreCoordinates c).2 ∧ dist x c ≤ w} ∩
      {x | dist x c ∈ A}
  have hDsub : D ⊆ Metric.closedBall c w := by
    intro x hx
    simpa [D, Metric.mem_closedBall] using hx.1.2
  have hfirst : IntegrableOn
      (fun x : Score => delta * angularRadialProfile w (dist x c)) D :=
    (((continuous_const.mul
      ((angularRadialProfile_continuous w).comp
        (continuous_id.dist continuous_const))).continuousOn.integrableOn_compact
          (isCompact_closedBall c w)).mono_set hDsub)
  have hbase : Continuous (packingAffineBaseline b) := by
    unfold packingAffineBaseline
    fun_prop
  have hsecond : IntegrableOn
      (fun x : Score =>
        (packingAffineBaseline b x +
            delta * angularRadialProfile w (dist x c)) *
          angularTilt b cA delta w (dist x c) *
          ((scoreCoordinates x - scoreCoordinates c).1 / dist x c)) D := by
    have hcont : Continuous (fun x : Score =>
        (packingAffineBaseline b x + localizedPackingBump delta w c x) *
          packingAngularTerm b cA delta w c x) :=
      (hbase.add (localizedPackingBump_contDiff delta w c).continuous).mul
        (packingAngularTerm_continuous hb hscale c)
    have hintClosed : IntegrableOn
        (fun x : Score =>
          (packingAffineBaseline b x + localizedPackingBump delta w c x) *
            packingAngularTerm b cA delta w c x)
        (Metric.closedBall c w) volume :=
      hcont.continuousOn.integrableOn_compact (isCompact_closedBall c w)
    have hint := hintClosed.mono_set hDsub
    convert hint using 1
    ext x
    rw [localizedPackingBump_eq_delta_mul_angularRadialProfile,
      packingAngularTerm, packingDirectionCos_eq_planarFirst_div_radius,
      planarRadius_scoreCoordinates_sub]
    ring
  have hD : MeasurableSet D := by
    dsimp [D]
    have hv : Measurable (fun x : Score =>
        (scoreCoordinates x - scoreCoordinates c).2) := by fun_prop
    have hr : Measurable (fun x : Score => dist x c) := by fun_prop
    exact ((measurableSet_lt measurable_const hv).inter
      (measurableSet_le hr measurable_const)).inter (hA.preimage hr)
  rw [integral_congr_ae (ae_restrict_of_forall_mem hD fun x hx =>
    packingRegression_mul_density_flip_cell_radial_identity j hw hsep omega hj
      (hDsub hx))]
  rw [integral_add hfirst hsecond]
  have hsplit : (∫ x in D,
      (packingAffineBaseline b x +
          delta * angularRadialProfile w (dist x c)) *
        angularTilt b cA delta w (dist x c) *
        ((scoreCoordinates x - scoreCoordinates c).1 / dist x c)) =
      (∫ x in D,
        b * (scoreCoordinates x - scoreCoordinates c).1 *
          angularTilt b cA delta w (dist x c) *
          ((scoreCoordinates x - scoreCoordinates c).1 / dist x c)) := by
    let g : ℝ → ℝ := fun r =>
      (1 / 2 + b * (angularGridCenter M j) 0 +
        delta * angularRadialProfile w r) * angularTilt b cA delta w r
    have hz := angularGridCenter_openRadialSet_weighted_direction_cancellation
      j g w hA
    dsimp only at hz
    have hz' : (∫ x in D, g (dist x c) *
        ((scoreCoordinates x - scoreCoordinates c).1 / dist x c)) = 0 := by
      simpa [D, c] using hz
    have hright : IntegrableOn
        (fun x : Score =>
          b * (scoreCoordinates x - scoreCoordinates c).1 *
            angularTilt b cA delta w (dist x c) *
            ((scoreCoordinates x - scoreCoordinates c).1 / dist x c)) D := by
      have hc : Continuous (fun x : Score =>
          b * (scoreCoordinates x - scoreCoordinates c).1 *
            packingAngularTerm b cA delta w c x) := by
        apply Continuous.mul
        · fun_prop
        · exact packingAngularTerm_continuous hb hscale c
      have hiClosed : IntegrableOn (fun x : Score =>
          b * (scoreCoordinates x - scoreCoordinates c).1 *
            packingAngularTerm b cA delta w c x)
          (Metric.closedBall c w) volume :=
        hc.continuousOn.integrableOn_compact (isCompact_closedBall c w)
      have hi := hiClosed.mono_set hDsub
      convert hi using 1
      ext x
      rw [packingAngularTerm, packingDirectionCos_eq_planarFirst_div_radius,
        planarRadius_scoreCoordinates_sub]
      ring
    have hzeroInt : IntegrableOn
        (fun x : Score => g (dist x c) *
          ((scoreCoordinates x - scoreCoordinates c).1 / dist x c)) D := by
      have hc : Continuous (fun x : Score =>
          (1 / 2 + b * c 0 + delta * angularRadialProfile w (dist x c)) *
            packingAngularTerm b cA delta w c x) := by
        apply Continuous.mul
        · exact continuous_const.add
            (continuous_const.mul ((angularRadialProfile_continuous w).comp
              (continuous_id.dist continuous_const)))
        · exact packingAngularTerm_continuous hb hscale c
      have hiClosed : IntegrableOn (fun x : Score =>
          (1 / 2 + b * c 0 + delta * angularRadialProfile w (dist x c)) *
            packingAngularTerm b cA delta w c x)
          (Metric.closedBall c w) volume :=
        hc.continuousOn.integrableOn_compact (isCompact_closedBall c w)
      have hi := hiClosed.mono_set hDsub
      convert hi using 1
      ext x
      dsimp [g]
      rw [packingAngularTerm, packingDirectionCos_eq_planarFirst_div_radius,
        planarRadius_scoreCoordinates_sub]
      simp only [Prod.fst_sub]
      ring
    rw [show (fun x : Score =>
        (packingAffineBaseline b x +
            delta * angularRadialProfile w (dist x c)) *
          angularTilt b cA delta w (dist x c) *
          ((scoreCoordinates x - scoreCoordinates c).1 / dist x c)) =
        (fun x =>
          b * (scoreCoordinates x - scoreCoordinates c).1 *
            angularTilt b cA delta w (dist x c) *
            ((scoreCoordinates x - scoreCoordinates c).1 / dist x c) +
          g (dist x c) *
            ((scoreCoordinates x - scoreCoordinates c).1 / dist x c)) by
      funext x
      dsimp [g, packingAffineBaseline, c, scoreCoordinates]
      ring]
    rw [integral_add hright hzeroInt, hz', add_zero]
  rw [hsplit]
  exact angularGridCenter_radialSet_angular_outcome_cancellation
    (w := w) j hscale hA hactive

end CausalSmith.Stat.BddUniformLogPenalty
