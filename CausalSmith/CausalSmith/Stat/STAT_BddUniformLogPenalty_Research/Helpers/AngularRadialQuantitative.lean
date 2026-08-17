import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Helpers.AngularRadialAssembly

/-!
# Quantitative angular radial cancellation

This module strengthens the exact active-tail cancellation with the localized
absolute bound needed for the one-point KL estimate.
-/

open MeasureTheory ProbabilityTheory Set

namespace CausalSmith.Stat.BddUniformLogPenalty

/-- The one-dimensional polar success increment is bounded by the bump
amplitude after multiplication by the nonnegative half-circle Jacobian. -/
-- @node: angularRadialSuccessIncrement_setIntegral_abs_le
lemma angularRadialSuccessIncrement_setIntegral_abs_le
    {b cA delta w R : ℝ} (hb : 0 < b) (hscale : 0 < cA * delta)
    (hdelta : 0 ≤ delta) {A : Set ℝ} (hA : MeasurableSet A) :
    |∫ r in Ioc 0 R, Real.pi * r * A.indicator
        (fun s => delta * angularRadialProfile w s +
          (b * s * angularTilt b cA delta w s) / 2) r| ≤
      delta * ∫ r in Ioc 0 R, Real.pi * r *
        (A ∩ Iio (2 * (cA * delta) / b)).indicator (fun _ => (1 : ℝ)) r := by
  let inc : ℝ → ℝ := fun r => delta * angularRadialProfile w r +
    (b * r * angularTilt b cA delta w r) / 2
  let jac : ℝ → ℝ := fun r => Real.pi * r
  have hinc : Continuous inc := by
    dsimp [inc]
    exact (continuous_const.mul (angularRadialProfile_continuous w)).add
      ((((continuous_const.mul continuous_id).mul
        (angularTilt_continuous hscale)).div_const 2))
  have hjac : Continuous jac := by
    dsimp [jac]
    fun_prop
  have hf : IntegrableOn (fun r => jac r * A.indicator inc r) (Ioc 0 R) := by
    have hbase : IntegrableOn (fun r => jac r * inc r) (Ioc 0 R) :=
      ((hjac.mul hinc).continuousOn.integrableOn_compact isCompact_Icc).mono_set
        Ioc_subset_Icc_self
    exact (hbase.indicator hA).congr
      (Filter.Eventually.of_forall fun r => by
        by_cases hr : r ∈ A <;> simp [Set.indicator, hr])
  have hg : IntegrableOn
      (fun r => delta * (jac r *
        (A ∩ Iio (2 * (cA * delta) / b)).indicator (fun _ => (1 : ℝ)) r))
      (Ioc 0 R) := by
    have hbase : IntegrableOn (fun r => delta * jac r) (Ioc 0 R) :=
      ((continuous_const.mul hjac).continuousOn.integrableOn_compact
        isCompact_Icc).mono_set Ioc_subset_Icc_self
    exact (hbase.indicator
        (hA.inter (measurableSet_Iio (a := 2 * (cA * delta) / b)))).congr
      (Filter.Eventually.of_forall fun r => by
        by_cases hr : r ∈ A ∩ Iio (2 * (cA * delta) / b)
        · simp only [Set.indicator_of_mem hr]
          ring
        · simp only [Set.indicator_of_notMem hr]
          ring)
  calc
    |∫ r in Ioc 0 R, jac r * A.indicator inc r| ≤
        ∫ r in Ioc 0 R, |jac r * A.indicator inc r| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ r in Ioc 0 R,
        delta * (jac r *
          (A ∩ Iio (2 * (cA * delta) / b)).indicator (fun _ => (1 : ℝ)) r) := by
      apply integral_mono_ae hf.abs hg
      exact ae_restrict_of_forall_mem measurableSet_Ioc (fun r hr => by
        have hj0 : 0 ≤ jac r := mul_nonneg Real.pi_pos.le hr.1.le
        by_cases hrA : r ∈ A
        · by_cases hrE : r ∈ Iio (2 * (cA * delta) / b)
          · simp only [Set.indicator_of_mem hrA,
              Set.indicator_of_mem (show r ∈ A ∩ Iio _ from ⟨hrA, hrE⟩), mul_one]
            rw [abs_mul, abs_of_nonneg hj0]
            simpa [inc, mul_comm] using mul_le_mul_of_nonneg_left
              (angularRadialSuccessIncrement_abs_le (w := w) (r := r)
                hb hscale hdelta) hj0
          · have hactive : 2 * (cA * delta) ≤ b * r := by
              have hrge : 2 * (cA * delta) / b ≤ r := le_of_not_gt hrE
              apply (div_le_iff₀ hb).mp at hrge
              nlinarith
            have hzero : inc r = 0 := by
              dsimp [inc]
              rw [angularRadialSuccessIncrement_identity hb hscale,
                angularCutoff_eq_one hscale hactive]
              ring
            simp [Set.indicator_of_mem hrA,
              Set.indicator_of_notMem (show r ∉ A ∩ Iio _ from fun h => hrE h.2),
              hzero]
        · have hrnot : r ∉ A ∩ Iio (2 * (cA * delta) / b) :=
            fun h => hrA h.1
          simp [Set.indicator_of_notMem hrA, Set.indicator_of_notMem hrnot])
    _ = delta * ∫ r in Ioc 0 R,
        jac r * (A ∩ Iio (2 * (cA * delta) / b)).indicator
          (fun _ => (1 : ℝ)) r := by
      rw [integral_const_mul]

/-- On any measurable radial slice of an upper half-disc, the combined bump
and cosine-squared success-mass increment is bounded by the bump amplitude
times the slice area. -/
-- @node: halfDisc_radialSet_angular_outcome_abs_le
lemma halfDisc_radialSet_angular_outcome_abs_le
    {b cA delta w R : ℝ} (hb : 0 < b) (hscale : 0 < cA * delta)
    (hdelta : 0 ≤ delta) {A : Set ℝ} (hA : MeasurableSet A) :
    let D : Set (ℝ × ℝ) :=
      {z | 0 < z.2 ∧ planarRadius z ≤ R} ∩ planarRadius ⁻¹' A
    |(∫ z in D, delta * angularRadialProfile w (planarRadius z)) +
      (∫ z in D, b * z.1 * angularTilt b cA delta w (planarRadius z) *
        (z.1 / planarRadius z))| ≤ delta *
      (volume ({z | 0 < z.2 ∧ planarRadius z ≤ R} ∩
        planarRadius ⁻¹' (A ∩ Iio (2 * (cA * delta) / b)))).toReal := by
  classical
  dsimp only
  let D0 : Set (ℝ × ℝ) := {z | 0 < z.2 ∧ planarRadius z ≤ R}
  let E : Set (ℝ × ℝ) := planarRadius ⁻¹' A
  let Eloc : Set (ℝ × ℝ) :=
    planarRadius ⁻¹' (A ∩ Iio (2 * (cA * delta) / b))
  have hD0 : MeasurableSet D0 :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le planarRadius_measurable measurable_const)
  have hE : MeasurableSet E := hA.preimage planarRadius_measurable
  have hEloc : MeasurableSet Eloc :=
    (hA.inter measurableSet_Iio).preimage planarRadius_measurable
  have hfirst := halfDisc_radial_integral
    (fun r => A.indicator (fun s => delta * angularRadialProfile w s) r) R
  have hsecond := halfDisc_weighted_cos_sq
    (fun r => A.indicator (fun s => b * r * angularTilt b cA delta w r) r) R
  have harea := halfDisc_radial_integral
    (fun r => (A ∩ Iio (2 * (cA * delta) / b)).indicator
      (fun _ => (1 : ℝ)) r) R
  have hfirst' :
      (∫ z : ℝ × ℝ in D0 ∩ E,
        delta * angularRadialProfile w (planarRadius z)) =
        ∫ r : ℝ in Ioc 0 R, Real.pi * r * A.indicator
          (fun s => delta * angularRadialProfile w s) r := by
    rw [inter_comm, ← Measure.restrict_restrict hE, ← integral_indicator hE]
    calc
      _ = ∫ z : ℝ × ℝ in D0,
          A.indicator (fun s => delta * angularRadialProfile w s)
            (planarRadius z) := by
        apply integral_congr_ae
        filter_upwards with z
        by_cases hz : planarRadius z ∈ A <;> simp [E, hz]
      _ = _ := by simpa [D0] using hfirst
  have hsecond' :
      (∫ z : ℝ × ℝ in D0 ∩ E,
        b * z.1 * angularTilt b cA delta w (planarRadius z) *
          (z.1 / planarRadius z)) =
        (∫ r : ℝ in Ioc 0 R,
          r * A.indicator
            (fun s => b * s * angularTilt b cA delta w s) r) *
          (Real.pi / 2) := by
    rw [inter_comm, ← Measure.restrict_restrict hE, ← integral_indicator hE]
    calc
      _ = ∫ z : ℝ × ℝ in D0,
          A.indicator (fun s => b * planarRadius z *
            angularTilt b cA delta w (planarRadius z)) (planarRadius z) *
              Real.cos (planarAngle z) ^ 2 := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem hD0] with z hzD
        by_cases hz : planarRadius z ∈ A
        · rw [Set.indicator_of_mem (show z ∈ E from hz),
            Set.indicator_of_mem hz]
          have hr := planarFirst_div_radius_eq_cos z hzD.1
          have hr0 : planarRadius z ≠ 0 := by
            intro hzero
            have hs : z.1 ^ 2 + z.2 ^ 2 ≤ 0 :=
              Real.sqrt_eq_zero'.mp (by simpa [planarRadius] using hzero)
            nlinarith [hzD.1, sq_nonneg z.1, sq_nonneg z.2]
          field_simp [hr0] at hr ⊢
          rw [hr]
          ring
        · simp [Set.indicator_of_notMem (show z ∉ E from hz), hz]
      _ = _ := hsecond
  have harea' : (volume (D0 ∩ Eloc)).toReal =
      ∫ r : ℝ in Ioc 0 R,
        Real.pi * r * (A ∩ Iio (2 * (cA * delta) / b)).indicator
          (fun _ => (1 : ℝ)) r := by
    have hone : (∫ z : ℝ × ℝ in D0 ∩ Eloc, (1 : ℝ)) =
        ∫ r : ℝ in Ioc 0 R,
          Real.pi * r * (A ∩ Iio (2 * (cA * delta) / b)).indicator
            (fun _ => (1 : ℝ)) r := by
      rw [inter_comm, ← Measure.restrict_restrict hEloc,
        ← integral_indicator hEloc]
      calc
        _ = ∫ z : ℝ × ℝ in D0,
            (A ∩ Iio (2 * (cA * delta) / b)).indicator
              (fun _ => (1 : ℝ)) (planarRadius z) := by
          apply integral_congr_ae
          filter_upwards with z
          by_cases hz : planarRadius z ∈ A ∩ Iio (2 * (cA * delta) / b)
          · have hz' : z ∈ Eloc := hz
            rw [Set.indicator_of_mem hz', Set.indicator_of_mem hz]
          · have hz' : z ∉ Eloc := hz
            rw [Set.indicator_of_notMem hz', Set.indicator_of_notMem hz]
        _ = _ := by simpa [D0] using harea
    simpa [integral_const, Measure.real_def] using hone
  change _ ≤ delta * (volume (D0 ∩ Eloc)).toReal
  rw [hfirst', hsecond', harea']
  have hfint : IntegrableOn
      (fun r : ℝ => Real.pi * r * A.indicator
        (fun s => delta * angularRadialProfile w s) r) (Ioc 0 R) := by
    have hc : Continuous (fun r : ℝ =>
        Real.pi * r * (delta * angularRadialProfile w r)) :=
      (continuous_const.mul continuous_id).mul
        (continuous_const.mul (angularRadialProfile_continuous w))
    exact ((((hc.continuousOn.integrableOn_compact isCompact_Icc).mono_set
        Ioc_subset_Icc_self).indicator hA)).congr
      (Filter.Eventually.of_forall fun r => by
        by_cases hr : r ∈ A <;> simp [Set.indicator, hr])
  have hgint : IntegrableOn
      (fun r : ℝ => r * A.indicator
        (fun s => b * s * angularTilt b cA delta w s) r) (Ioc 0 R) := by
    have hc : Continuous (fun r : ℝ =>
        r * (b * r * angularTilt b cA delta w r)) :=
      continuous_id.mul ((continuous_const.mul continuous_id).mul
        (angularTilt_continuous hscale))
    exact ((((hc.continuousOn.integrableOn_compact isCompact_Icc).mono_set
        Ioc_subset_Icc_self).indicator hA)).congr
      (Filter.Eventually.of_forall fun r => by
        by_cases hr : r ∈ A <;> simp [Set.indicator, hr])
  rw [← integral_mul_const, ← integral_add hfint
    (hgint.mul_const (Real.pi / 2))]
  have hcombine :
      (∫ r in Ioc 0 R,
        Real.pi * r * A.indicator
            (fun s => delta * angularRadialProfile w s) r +
          r * A.indicator
            (fun s => b * s * angularTilt b cA delta w s) r *
              (Real.pi / 2)) =
      ∫ r in Ioc 0 R, Real.pi * r * A.indicator
        (fun s => delta * angularRadialProfile w s +
          (b * s * angularTilt b cA delta w s) / 2) r := by
    apply integral_congr_ae
    filter_upwards with r
    by_cases hrA : r ∈ A <;> simp [hrA] <;> ring
  rw [hcombine]
  exact angularRadialSuccessIncrement_setIntegral_abs_le
    (w := w) (R := R) hb hscale hdelta hA

/-- Translation of the quantitative half-disc bound to a lower-edge angular
grid center in score coordinates. -/
-- @node: angularGridCenter_radialSet_angular_outcome_abs_le
lemma angularGridCenter_radialSet_angular_outcome_abs_le
    {M : ℕ} (j : Fin M) {b cA delta w : ℝ}
    (hb : 0 < b) (hscale : 0 < cA * delta) (hdelta : 0 ≤ delta)
    {A : Set ℝ} (hA : MeasurableSet A) :
    let c := angularGridCenter M j
    let D : Set Score :=
      {x | 0 < (scoreCoordinates x - scoreCoordinates c).2 ∧ dist x c ≤ w} ∩
        {x | dist x c ∈ A}
    let Dloc : Set Score :=
      {x | 0 < (scoreCoordinates x - scoreCoordinates c).2 ∧ dist x c ≤ w} ∩
        {x | dist x c ∈ A ∩ Iio (2 * (cA * delta) / b)}
    |(∫ x in D, delta * angularRadialProfile w (dist x c)) +
      (∫ x in D,
        b * (scoreCoordinates x - scoreCoordinates c).1 *
          angularTilt b cA delta w (dist x c) *
          ((scoreCoordinates x - scoreCoordinates c).1 / dist x c))| ≤
      delta * (volume Dloc).toReal := by
  dsimp only
  let c : Score := angularGridCenter M j
  let cp : ℝ × ℝ := scoreCoordinates c
  let D : Set Score :=
    {x | 0 < (scoreCoordinates x - scoreCoordinates c).2 ∧ dist x c ≤ w} ∩
      {x | dist x c ∈ A}
  let Dloc : Set Score :=
    {x | 0 < (scoreCoordinates x - scoreCoordinates c).2 ∧ dist x c ≤ w} ∩
      {x | dist x c ∈ A ∩ Iio (2 * (cA * delta) / b)}
  let E : Set (ℝ × ℝ) :=
    {z | 0 < (z - cp).2 ∧ planarRadius (z - cp) ≤ w} ∩
      {z | planarRadius (z - cp) ∈ A}
  let Eloc : Set (ℝ × ℝ) :=
    {z | 0 < (z - cp).2 ∧ planarRadius (z - cp) ≤ w} ∩
      {z | planarRadius (z - cp) ∈ A ∩ Iio (2 * (cA * delta) / b)}
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
  have himageLoc : scoreCoordinates '' Dloc = Eloc := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa [Dloc, Eloc, cp, c, planarRadius_scoreCoordinates_sub] using hx
    · intro hz
      let x : Score := scorePoint z.1 z.2
      have hcoord : scoreCoordinates x = z := by
        ext <;> simp [x, scoreCoordinates, scorePoint_apply_zero,
          scorePoint_apply_one]
      refine ⟨x, ?_, hcoord⟩
      simpa [Dloc, Eloc, cp, c, hcoord,
        ← planarRadius_scoreCoordinates_sub] using hz
  change |(∫ x in D, delta * angularRadialProfile w (dist x c)) +
      (∫ x in D, b * (scoreCoordinates x - scoreCoordinates c).1 *
        angularTilt b cA delta w (dist x c) *
        ((scoreCoordinates x - scoreCoordinates c).1 / dist x c))| ≤
    delta * (volume Dloc).toReal
  have hfirst : (fun x : Score => delta * angularRadialProfile w (dist x c)) =
      fun x => delta * angularRadialProfile w
        (planarRadius (scoreCoordinates x - scoreCoordinates c)) := by
    funext x
    rw [planarRadius_scoreCoordinates_sub]
  have hsecond : (fun x : Score =>
      b * (scoreCoordinates x - scoreCoordinates c).1 *
        angularTilt b cA delta w (dist x c) *
        ((scoreCoordinates x - scoreCoordinates c).1 / dist x c)) =
      fun x => b * (scoreCoordinates x - scoreCoordinates c).1 *
        angularTilt b cA delta w
          (planarRadius (scoreCoordinates x - scoreCoordinates c)) *
        ((scoreCoordinates x - scoreCoordinates c).1 /
          planarRadius (scoreCoordinates x - scoreCoordinates c)) := by
    funext x
    rw [planarRadius_scoreCoordinates_sub]
  rw [hfirst, hsecond]
  change |(∫ x in D, (fun z : ℝ × ℝ =>
      delta * angularRadialProfile w (planarRadius (z - scoreCoordinates c)))
        (scoreCoordinates x)) +
    (∫ x in D, (fun z : ℝ × ℝ =>
      b * (z - scoreCoordinates c).1 *
        angularTilt b cA delta w (planarRadius (z - scoreCoordinates c)) *
        ((z - scoreCoordinates c).1 / planarRadius (z - scoreCoordinates c)))
          (scoreCoordinates x))| ≤ delta * (volume Dloc).toReal
  rw [← scoreCoordinates_measurePreserving.setIntegral_image_emb
      scoreCoordinates_measurableEmbedding
      (fun z : ℝ × ℝ => delta * angularRadialProfile w
        (planarRadius (z - scoreCoordinates c))) D,
    ← scoreCoordinates_measurePreserving.setIntegral_image_emb
      scoreCoordinates_measurableEmbedding
      (fun z : ℝ × ℝ => b * (z - scoreCoordinates c).1 *
        angularTilt b cA delta w (planarRadius (z - scoreCoordinates c)) *
        ((z - scoreCoordinates c).1 / planarRadius (z - scoreCoordinates c))) D]
  have hvolScore : (volume Dloc).toReal =
      (volume (scoreCoordinates '' Dloc)).toReal := by
    have h := scoreCoordinates_measurePreserving.setIntegral_image_emb
      scoreCoordinates_measurableEmbedding (fun _ : ℝ × ℝ => (1 : ℝ)) Dloc
    simpa [integral_const, Measure.real_def] using h.symm
  rw [hvolScore]
  rw [himage, himageLoc]
  let T : (ℝ × ℝ) → (ℝ × ℝ) := fun u => cp + u
  let E0 : Set (ℝ × ℝ) :=
    {u | 0 < u.2 ∧ planarRadius u ≤ w} ∩ planarRadius ⁻¹' A
  let E0loc : Set (ℝ × ℝ) :=
    {u | 0 < u.2 ∧ planarRadius u ≤ w} ∩
      planarRadius ⁻¹' (A ∩ Iio (2 * (cA * delta) / b))
  have hT : MeasurableEmbedding T := (Homeomorph.addLeft cp).measurableEmbedding
  have hmp : MeasurePreserving T (volume : Measure (ℝ × ℝ)) volume :=
    measurePreserving_add_left volume cp
  have hE : E = T '' E0 := by
    ext z
    constructor
    · rintro ⟨hz, hAz⟩
      refine ⟨z - cp, ⟨?_, ?_⟩, by simp [T]⟩
      · simpa [E0] using hz
      · simpa [E0] using hAz
    · rintro ⟨u, ⟨hu, hAu⟩, rfl⟩
      simpa [E, E0, T] using And.intro hu hAu
  have hEloc : Eloc = T '' E0loc := by
    ext z
    constructor
    · rintro ⟨hz, hAz⟩
      refine ⟨z - cp, ⟨?_, ?_⟩, by simp [T]⟩
      · simpa [E0loc] using hz
      · simpa [E0loc] using hAz
    · rintro ⟨u, ⟨hu, hAu⟩, rfl⟩
      simpa [Eloc, E0loc, T] using And.intro hu hAu
  rw [hE, hmp.setIntegral_image_emb hT, hmp.setIntegral_image_emb hT]
  rw [hEloc]
  have hvol : (volume (T '' E0loc)).toReal = (volume E0loc).toReal := by
    have h := hmp.setIntegral_image_emb hT (fun _ : ℝ × ℝ => (1 : ℝ)) E0loc
    simpa [integral_const, Measure.real_def] using h
  rw [hvol]
  simpa [T, cp, c, E0, E0loc] using
    halfDisc_radialSet_angular_outcome_abs_le
      (w := w) (R := w) hb hscale hdelta hA

/-- For a true changed bit, the success-weighted mass difference on any
radial slice is bounded by the amplitude times the area of that slice inside
the changed half-disc. -/
-- @node: angularPacking_flip_setIntegral_abs_le_cellArea
lemma angularPacking_flip_setIntegral_abs_le_cellArea
    {M : ℕ} (j : Fin M) {b cA delta w : ℝ}
    (hb : 0 < b) (hbSmall : |b| ≤ 1 / 4)
    (hscale : 0 < cA * delta) (hcA : 8 ≤ cA)
    (hdelta : 0 < delta) (hdeltaSmall : delta ≤ 1 / 8)
    (hw : 0 < w) (hwQuarter : w ≤ 1 / 4)
    (hsep : ∀ i k : Fin M, i ≠ k →
      3 * w ≤ dist (angularGridCenter M i) (angularGridCenter M k))
    (omega : Fin M → Bool) (hj : omega j = true)
    {A : Set ℝ} (hA : MeasurableSet A) :
    let c := angularGridCenter M j
    let D : Set Score :=
      {x | 0 < (scoreCoordinates x - scoreCoordinates c).2 ∧ dist x c ≤ w} ∩
        {x | dist x c ∈ A}
    let Dloc : Set Score :=
      {x | 0 < (scoreCoordinates x - scoreCoordinates c).2 ∧ dist x c ≤ w} ∩
        {x | dist x c ∈ A ∩ Iio (2 * (cA * delta) / b)}
    |(∫ x in {x | dist x c ∈ A},
        clippedPackingRegression b delta w (angularGridCenter M) omega x
        ∂(angularDesignMeasure b cA delta w (angularGridCenter M) omega)) -
      ∫ x in {x | dist x c ∈ A},
        clippedPackingRegression b delta w (angularGridCenter M)
          (Causalean.Stat.flipBit j omega) x
        ∂(angularDesignMeasure b cA delta w (angularGridCenter M)
          (Causalean.Stat.flipBit j omega))| ≤
      delta * (volume Dloc).toReal := by
  dsimp only
  let c := angularGridCenter M j
  let S : Set Score := {x | dist x c ∈ A}
  let D : Set Score :=
    {x | 0 < (scoreCoordinates x - scoreCoordinates c).2 ∧ dist x c ≤ w} ∩ S
  let Dloc : Set Score :=
    {x | 0 < (scoreCoordinates x - scoreCoordinates c).2 ∧ dist x c ≤ w} ∩
      {x | dist x c ∈ A ∩ Iio (2 * (cA * delta) / b)}
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
  change |(∫ x in S ∩ scoreCube (1 / 2 : ℝ), f x) -
    ∫ x in S ∩ scoreCube (1 / 2 : ℝ), f' x| ≤ delta * (volume Dloc).toReal
  have hf : IntegrableOn f (S ∩ scoreCube (1 / 2 : ℝ)) :=
    (((packingRegression_contDiff b delta w (angularGridCenter M) omega).continuous.mul
      (packingAngularDensity_continuous hb hscale
        (angularGridCenter M) omega)).continuousOn.integrableOn_compact
          packingScoreCube_isCompact).mono_set inter_subset_right
  have hf' : IntegrableOn f' (S ∩ scoreCube (1 / 2 : ℝ)) :=
    (((packingRegression_contDiff b delta w (angularGridCenter M)
      (Causalean.Stat.flipBit j omega)).continuous.mul
      (packingAngularDensity_continuous hb hscale (angularGridCenter M)
        (Causalean.Stat.flipBit j omega))).continuousOn.integrableOn_compact
          packingScoreCube_isCompact).mono_set inter_subset_right
  rw [← integral_sub hf hf']
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
  have hae : ∀ᵐ x ∂(volume : Measure Score),
      (S ∩ scoreCube (1 / 2 : ℝ)).indicator (fun x => f x - f' x) x =
        D.indicator (fun x => f x - f' x) x := by
    filter_upwards [compl_mem_ae_iff.mpr hboundary] with x hxboundary
    by_cases hxD : x ∈ D
    · have hxCell : x ∈ Metric.closedBall c w ∩ scoreCube (1 / 2 : ℝ) := by
        apply (mem_angularGrid_packingCell_iff_closedUpperHalfDisc j hwQuarter x).mpr
        exact ⟨le_of_lt hxD.1.1, by
          simpa [c, planarRadius_scoreCoordinates_sub] using hxD.1.2⟩
      rw [Set.indicator_of_mem hxD,
        Set.indicator_of_mem (show x ∈ S ∩ scoreCube (1 / 2 : ℝ) from
          ⟨hxD.2, hxCell.2⟩)]
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
          exact hxD ⟨⟨lt_of_le_of_ne hnonneg (Ne.symm hxboundary),
            by simpa [c, Metric.mem_closedBall] using hxBall⟩, hxSS.1⟩
        have hfar : w ≤ dist x c :=
          le_of_lt (by simpa [Metric.mem_closedBall, not_le] using hxOutside)
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
  have hD : MeasurableSet D := by
    have hv : Measurable (fun x : Score =>
        (scoreCoordinates x - scoreCoordinates c).2) := by fun_prop
    have hr : Measurable (fun x : Score => dist x c) := by fun_prop
    exact ((measurableSet_lt measurable_const hv).inter
      (measurableSet_le hr measurable_const)).inter hS
  rw [← integral_indicator (hS.inter (scoreCube_measurableSet _)),
    integral_congr_ae hae, integral_indicator hD]
  change |∫ x in D, f x - f' x| ≤ delta * (volume Dloc).toReal
  have hDsub : D ⊆ Metric.closedBall c w := by
    intro x hx
    simpa [D, Metric.mem_closedBall] using hx.1.2
  have hpoint : ∀ x ∈ D, f x - f' x =
      delta * angularRadialProfile w (dist x c) +
      (packingAffineBaseline b x + delta * angularRadialProfile w (dist x c)) *
        angularTilt b cA delta w (dist x c) *
        ((scoreCoordinates x - scoreCoordinates c).1 / dist x c) := by
    intro x hx
    simpa [c, f, f'] using
      packingRegression_mul_density_flip_cell_radial_identity j hw hsep omega hj
        (hDsub hx)
  rw [integral_congr_ae (ae_restrict_of_forall_mem hD hpoint)]
  let g : ℝ → ℝ := fun r =>
    (1 / 2 + b * c 0 + delta * angularRadialProfile w r) *
      angularTilt b cA delta w r
  have hz := angularGridCenter_openRadialSet_weighted_direction_cancellation
    j g w hA
  dsimp only at hz
  have hz' : (∫ x in D, g (dist x c) *
      ((scoreCoordinates x - scoreCoordinates c).1 / dist x c)) = 0 := by
    simpa [D, c] using hz
  have hfirst : IntegrableOn
      (fun x : Score => delta * angularRadialProfile w (dist x c)) D :=
    ((((continuous_const.mul ((angularRadialProfile_continuous w).comp
      (continuous_id.dist continuous_const))).continuousOn.integrableOn_compact
        (isCompact_closedBall c w)).mono_set hDsub))
  have hright : IntegrableOn (fun x : Score =>
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
  have hzeroInt : IntegrableOn (fun x : Score => g (dist x c) *
      ((scoreCoordinates x - scoreCoordinates c).1 / dist x c)) D := by
    have hc : Continuous (fun x : Score =>
        (1 / 2 + b * c 0 + delta * angularRadialProfile w (dist x c)) *
          packingAngularTerm b cA delta w c x) :=
      (continuous_const.add (continuous_const.mul
        ((angularRadialProfile_continuous w).comp
          (continuous_id.dist continuous_const)))).mul
            (packingAngularTerm_continuous hb hscale c)
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
  have hdecomp : (fun x : Score =>
      delta * angularRadialProfile w (dist x c) +
      (packingAffineBaseline b x + delta * angularRadialProfile w (dist x c)) *
        angularTilt b cA delta w (dist x c) *
        ((scoreCoordinates x - scoreCoordinates c).1 / dist x c)) = fun x =>
      delta * angularRadialProfile w (dist x c) +
        (b * (scoreCoordinates x - scoreCoordinates c).1 *
          angularTilt b cA delta w (dist x c) *
          ((scoreCoordinates x - scoreCoordinates c).1 / dist x c) +
          g (dist x c) *
          ((scoreCoordinates x - scoreCoordinates c).1 / dist x c)) := by
    funext x
    dsimp [g, packingAffineBaseline, c, scoreCoordinates]
    ring
  rw [hdecomp]
  have hsum : (∫ x in D,
      delta * angularRadialProfile w (dist x c) +
        (b * (scoreCoordinates x - scoreCoordinates c).1 *
          angularTilt b cA delta w (dist x c) *
          ((scoreCoordinates x - scoreCoordinates c).1 / dist x c) +
          g (dist x c) *
          ((scoreCoordinates x - scoreCoordinates c).1 / dist x c))) =
      (∫ x in D, delta * angularRadialProfile w (dist x c)) +
        ((∫ x in D, b * (scoreCoordinates x - scoreCoordinates c).1 *
          angularTilt b cA delta w (dist x c) *
          ((scoreCoordinates x - scoreCoordinates c).1 / dist x c)) +
        ∫ x in D, g (dist x c) *
          ((scoreCoordinates x - scoreCoordinates c).1 / dist x c)) := by
    let u : Score → ℝ := fun x =>
      b * (scoreCoordinates x - scoreCoordinates c).1 *
        angularTilt b cA delta w (dist x c) *
        ((scoreCoordinates x - scoreCoordinates c).1 / dist x c)
    let v : Score → ℝ := fun x => g (dist x c) *
      ((scoreCoordinates x - scoreCoordinates c).1 / dist x c)
    have hu : IntegrableOn u D := hright
    have hv : IntegrableOn v D := hzeroInt
    change (∫ x in D, delta * angularRadialProfile w (dist x c) +
      (u x + v x)) = (∫ x in D, delta * angularRadialProfile w (dist x c)) +
        ((∫ x in D, u x) + ∫ x in D, v x)
    have hs1 : (∫ x in D, delta * angularRadialProfile w (dist x c) +
        (u x + v x)) =
        (∫ x in D, delta * angularRadialProfile w (dist x c)) +
          ∫ x in D, u x + v x := by
      simpa only [Pi.add_apply] using integral_add hfirst (hu.add hv)
    have hs2 : (∫ x in D, u x + v x) =
        (∫ x in D, u x) + ∫ x in D, v x := by
      simpa only [Pi.add_apply] using integral_add hu hv
    rw [hs1, hs2]
  rw [hsum, hz', add_zero]
  exact angularGridCenter_radialSet_angular_outcome_abs_le j hb hscale hdelta.le hA

/-- The cell-area bound is dominated by the common radius marginal on the
same measurable radial set. -/
-- @node: angularPacking_flip_setIntegral_abs_le_radialMass
lemma angularPacking_flip_setIntegral_abs_le_radialMass
    {M : ℕ} (j : Fin M) {b cA delta w : ℝ}
    (hb : 0 < b) (hbSmall : |b| ≤ 1 / 4)
    (hscale : 0 < cA * delta) (hcA : 8 ≤ cA)
    (hdelta : 0 < delta) (hdeltaSmall : delta ≤ 1 / 8)
    (hw : 0 < w) (hwQuarter : w ≤ 1 / 4)
    (hsep : ∀ i k : Fin M, i ≠ k →
      3 * w ≤ dist (angularGridCenter M i) (angularGridCenter M k))
    (omega : Fin M → Bool) (hj : omega j = true)
    {A : Set ℝ} (hA : MeasurableSet A) :
    |(∫ x in {x | dist x (angularGridCenter M j) ∈ A},
        clippedPackingRegression b delta w (angularGridCenter M) omega x
        ∂(angularDesignMeasure b cA delta w (angularGridCenter M) omega)) -
      ∫ x in {x | dist x (angularGridCenter M j) ∈ A},
        clippedPackingRegression b delta w (angularGridCenter M)
          (Causalean.Stat.flipBit j omega) x
        ∂(angularDesignMeasure b cA delta w (angularGridCenter M)
          (Causalean.Stat.flipBit j omega))| ≤
      delta * (Measure.map (fun x : Score => dist x (angularGridCenter M j))
        (angularDesignMeasure b cA delta w (angularGridCenter M) omega)
          (A ∩ Iio (2 * (cA * delta) / b))).toReal := by
  let c := angularGridCenter M j
  let Aloc : Set ℝ := A ∩ Iio (2 * (cA * delta) / b)
  let D : Set Score :=
    {x | 0 < (scoreCoordinates x - scoreCoordinates c).2 ∧ dist x c ≤ w} ∩
      {x | dist x c ∈ Aloc}
  have hbase := angularPacking_flip_setIntegral_abs_le_cellArea j hb hbSmall
    hscale hcA hdelta hdeltaSmall hw hwQuarter hsep omega hj hA
  dsimp only at hbase
  apply hbase.trans
  apply mul_le_mul_of_nonneg_left _ hdelta.le
  change (volume D).toReal ≤ _
  have hDsub : D ⊆
      (Metric.closedBall c w ∩ scoreCube (1 / 2)) ∩ {x | dist x c ∈ Aloc} := by
    intro x hx
    refine ⟨?_, hx.2⟩
    apply (mem_angularGrid_packingCell_iff_closedUpperHalfDisc j hwQuarter x).mpr
    exact ⟨hx.1.1.le, by simpa [c, planarRadius_scoreCoordinates_sub] using hx.1.2⟩
  have hcell := angularDesignMeasure_gridCell_radialSet_eq_volume j hb hscale hcA
    hdelta hw hwQuarter hsep omega (A := Aloc) (by
      dsimp [Aloc]
      exact hA.inter measurableSet_Iio)
  letI : IsProbabilityMeasure
      (angularDesignMeasure b cA delta w (angularGridCenter M) omega) :=
    angularDesignMeasure_isProbabilityMeasure hb hscale hcA hdelta hw
      hwQuarter hsep omega
  have hmeas : MeasurableSet Aloc := by
    dsimp [Aloc]
    exact hA.inter measurableSet_Iio
  rw [Measure.map_apply (by fun_prop) hmeas]
  have hDfinite : volume D ≠ ⊤ := ne_of_lt
    ((measure_mono hDsub).trans (measure_mono inter_subset_left) |>.trans_lt
      ((isCompact_closedBall c w).inter_right
        packingScoreCube_isCompact.isClosed |>.measure_lt_top))
  apply (ENNReal.toReal_le_toReal hDfinite (measure_ne_top _ _)).2
  exact calc
    volume D ≤ volume ((Metric.closedBall c w ∩ scoreCube (1 / 2)) ∩
        {x | dist x c ∈ Aloc}) := measure_mono hDsub
    _ = angularDesignMeasure b cA delta w (angularGridCenter M) omega
        ((Metric.closedBall c w ∩ scoreCube (1 / 2)) ∩
          {x | dist x c ∈ Aloc}) := hcell.symm
    _ ≤ angularDesignMeasure b cA delta w (angularGridCenter M) omega
        {x | dist x c ∈ Aloc} := measure_mono inter_subset_right

/-- The localized success-mass estimate holds in either orientation of the
changed packing bit. -/
-- @node: angularPacking_flip_success_setIntegral_abs_le
lemma angularPacking_flip_success_setIntegral_abs_le
    {M : ℕ} (j : Fin M) {b cA delta w : ℝ}
    (hb : 0 < b) (hbSmall : |b| ≤ 1 / 4)
    (hscale : 0 < cA * delta) (hcA : 8 ≤ cA)
    (hdelta : 0 < delta) (hdeltaSmall : delta ≤ 1 / 8)
    (hw : 0 < w) (hwQuarter : w ≤ 1 / 4)
    (hsep : ∀ i k : Fin M, i ≠ k →
      3 * w ≤ dist (angularGridCenter M i) (angularGridCenter M k))
    (omega : Fin M → Bool) {A : Set ℝ} (hA : MeasurableSet A) :
    |(∫ x in {x | dist x (angularGridCenter M j) ∈ A},
        clippedPackingRegression b delta w (angularGridCenter M) omega x
        ∂(angularDesignMeasure b cA delta w (angularGridCenter M) omega)) -
      ∫ x in {x | dist x (angularGridCenter M j) ∈ A},
        clippedPackingRegression b delta w (angularGridCenter M)
          (Causalean.Stat.flipBit j omega) x
        ∂(angularDesignMeasure b cA delta w (angularGridCenter M)
          (Causalean.Stat.flipBit j omega))| ≤
      delta * (Measure.map (fun x : Score => dist x (angularGridCenter M j))
        (angularDesignMeasure b cA delta w (angularGridCenter M) omega)
          (A ∩ Iio (2 * (cA * delta) / b))).toReal := by
  by_cases hj : omega j = true
  · exact angularPacking_flip_setIntegral_abs_le_radialMass j hb hbSmall
      hscale hcA hdelta hdeltaSmall hw hwQuarter hsep omega hj hA
  · have hjf : omega j = false := Bool.eq_false_of_not_eq_true hj
    have htrue : (Causalean.Stat.flipBit j omega) j = true := by
      simp [Causalean.Stat.flipBit, hjf]
    have hbound := angularPacking_flip_setIntegral_abs_le_radialMass j hb hbSmall
      hscale hcA hdelta hdeltaSmall hw hwQuarter hsep
      (Causalean.Stat.flipBit j omega) htrue hA
    have hmap := angularDesignMeasure_map_distance_eq j hb hscale hcA hdelta hw
      hwQuarter hsep omega (Causalean.Stat.flipBit j omega)
        (by intro k hkj; simp [Causalean.Stat.flipBit, hkj])
    rw [← hmap] at hbound
    simpa [Causalean.Stat.flipBit_involutive j omega, abs_sub_comm] using hbound

end CausalSmith.Stat.BddUniformLogPenalty
