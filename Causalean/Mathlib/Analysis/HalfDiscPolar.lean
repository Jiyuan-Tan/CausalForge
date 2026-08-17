import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Polar integration and cancellation on half-discs

This module derives weighted polar-integration formulas on upper half-discs,
including radial mass identities, odd-angular cancellation, quadratic angular
moments, and translation-invariant variants.
-/

open MeasureTheory Set
open scoped Interval

namespace Causalean.Mathlib.Analysis

/-- The Euclidean radius on the real coordinate plane. This is explicit because
the product type `ℝ × ℝ` carries the max product norm, not the Euclidean norm. -/
-- @node: planarRadius
noncomputable def planarRadius (z : ℝ × ℝ) : ℝ :=
  Real.sqrt (z.1 ^ 2 + z.2 ^ 2)

/-- The Euclidean radius on the coordinate plane is Borel measurable. -/
-- @node: planarRadius_measurable
lemma planarRadius_measurable : Measurable planarRadius := by
  exact ((measurable_fst.pow_const 2).add
    (measurable_snd.pow_const 2)).sqrt

/-- The polar angle of a nonzero point, using Mathlib's polar-coordinate
chart. Only its values on the open upper half-plane are used below. -/
-- @node: planarAngle
noncomputable def planarAngle (z : ℝ × ℝ) : ℝ :=
  (polarCoord z).2

/-- The cosine has zero integral on a half-circle. -/
lemma integral_cos_zero_to_pi :
    (∫ θ : ℝ in Ioc 0 Real.pi, Real.cos θ) = 0 := by
  rw [← intervalIntegral.integral_of_le Real.pi_pos.le]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => Real.hasDerivAt_sin x)
    (Real.continuous_cos.intervalIntegrable 0 Real.pi)]
  simp

/-- The quadratic cosine moment on a half-circle is `π / 2`. -/
-- @node: integral_cos_sq_zero_to_pi
lemma integral_cos_sq_zero_to_pi :
    (∫ θ : ℝ in Ioc 0 Real.pi, Real.cos θ ^ 2) = Real.pi / 2 := by
  rw [← intervalIntegral.integral_of_le Real.pi_pos.le]
  simp

/-- Weighted polar integration on an upper half-disc factors into a radial
integral and an angular integral. -/
-- @node: halfDisc_weighted_polar_integral
lemma halfDisc_weighted_polar_integral
    (g h : ℝ → ℝ) (r : ℝ) :
    (∫ z : ℝ × ℝ in {z | 0 < z.2 ∧ planarRadius z ≤ r},
        g (planarRadius z) * h (planarAngle z)) =
      (∫ s : ℝ in Ioc 0 r, s * g s) *
        (∫ θ : ℝ in Ioo 0 Real.pi, h θ) := by
  let D : Set (ℝ × ℝ) := {z | 0 < z.2 ∧ planarRadius z ≤ r}
  let E : Set (ℝ × ℝ) := Ioc 0 r ×ˢ Ioo 0 Real.pi
  have hD : MeasurableSet D := by
    exact (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le
        ((measurable_fst.pow_const 2).add (measurable_snd.pow_const 2)).sqrt
        measurable_const)
  have hE : MeasurableSet E := measurableSet_Ioc.prod measurableSet_Ioo
  change (∫ z : ℝ × ℝ in D,
      g (planarRadius z) * h (planarAngle z)) = _
  rw [← integral_indicator hD, ← integral_comp_polarCoord_symm]
  rw [show (∫ p in polarCoord.target,
      p.1 • D.indicator
        (fun z => g (planarRadius z) * h (planarAngle z))
        (polarCoord.symm p)) =
      ∫ p in E, (p.1 * g p.1) * h p.2 by
    rw [← integral_indicator polarCoord.open_target.measurableSet,
      ← integral_indicator hE]
    apply integral_congr_ae
    filter_upwards with p
    by_cases hp : p ∈ polarCoord.target
    · have hptarget := hp
      simp only [polarCoord_target, mem_prod, mem_Ioi, mem_Ioo] at hp
      have hinv := polarCoord.right_inv hp
      have hrs : planarRadius (polarCoord.symm p) = p.1 :=
        congrArg Prod.fst hinv
      have htheta : planarAngle (polarCoord.symm p) = p.2 :=
        congrArg Prod.snd hinv
      have hsin : 0 < Real.sin p.2 ↔ 0 < p.2 := by
        constructor
        · intro hs
          by_contra hn
          exact (not_lt_of_ge (Real.sin_nonpos_of_nonpos_of_neg_pi_le
            (le_of_not_gt hn) hp.2.1.le)) hs
        · intro htheta0
          exact Real.sin_pos_of_pos_of_lt_pi htheta0 hp.2.2
      have hy : 0 < p.1 * Real.sin p.2 ↔ 0 < p.2 :=
        (mul_pos_iff_of_pos_left hp.1).trans hsin
      have hmem : polarCoord.symm p ∈ D ↔ p ∈ E := by
        change (0 < (polarCoord.symm p).2 ∧
            planarRadius (polarCoord.symm p) ≤ r) ↔
          (0 < p.1 ∧ p.1 ≤ r) ∧ 0 < p.2 ∧ p.2 < Real.pi
        rw [hrs]
        simp only [polarCoord_symm_apply]
        rw [hy]
        constructor
        · rintro ⟨hptheta, hpr⟩
          exact ⟨⟨hp.1, hpr⟩, hptheta, hp.2.2⟩
        · rintro ⟨⟨_, hpr⟩, hptheta0, _⟩
          exact ⟨hptheta0, hpr⟩
      by_cases hmemD : polarCoord.symm p ∈ D
      · rw [indicator_of_mem hptarget, indicator_of_mem hmemD,
          indicator_of_mem (hmem.mp hmemD), hrs, htheta]
        simp [smul_eq_mul]
        ring
      · rw [indicator_of_mem hptarget]
        simp only [Set.indicator]
        rw [if_neg hmemD, if_neg (mt hmem.mpr hmemD)]
        simp
    · have hpE : p ∉ E := by
        rintro ⟨⟨hp0, _⟩, hptheta0, hpthetapi⟩
        apply hp
        simp only [polarCoord_target, mem_prod, mem_Ioi, mem_Ioo]
        exact ⟨hp0, lt_trans (neg_lt_zero.mpr Real.pi_pos) hptheta0, hpthetapi⟩
      simp only [Set.indicator]
      rw [if_neg hp, if_neg hpE]
  ]
  change (∫ p in Ioc 0 r ×ˢ Ioo 0 Real.pi,
    (p.1 * g p.1) * h p.2) = _
  rw [Measure.volume_eq_prod]
  exact setIntegral_prod_mul (μ := volume) (ν := volume)
    (fun s : ℝ => s * g s) h (Ioc 0 r) (Ioo 0 Real.pi)

/-- A cosine angular tilt has zero integral against every radial weight on an
upper half-disc. -/
-- @node: halfDisc_weighted_cos_cancellation
lemma halfDisc_weighted_cos_cancellation (g : ℝ → ℝ) (r : ℝ) :
    (∫ z : ℝ × ℝ in {z | 0 < z.2 ∧ planarRadius z ≤ r},
      g (planarRadius z) * Real.cos (planarAngle z)) = 0 := by
  rw [halfDisc_weighted_polar_integral]
  have hcos : (∫ θ : ℝ in Ioo 0 Real.pi, Real.cos θ) = 0 := by
    rw [← integral_Ioc_eq_integral_Ioo]
    exact integral_cos_zero_to_pi
  rw [hcos, mul_zero]

/-- A cosine angular tilt has zero mass on every measurable radial subset of
an upper half-disc.  This is the setwise interface used to identify radial
pushforwards, rather than merely their total masses. -/
-- @node: halfDisc_radialSet_weighted_cos_cancellation
lemma halfDisc_radialSet_weighted_cos_cancellation
    (g : ℝ → ℝ) (r : ℝ) {A : Set ℝ} (hA : MeasurableSet A) :
    (∫ z : ℝ × ℝ in
      {z | 0 < z.2 ∧ planarRadius z ≤ r} ∩ planarRadius ⁻¹' A,
      g (planarRadius z) * Real.cos (planarAngle z)) = 0 := by
  let D : Set (ℝ × ℝ) := {z | 0 < z.2 ∧ planarRadius z ≤ r}
  let R : Set (ℝ × ℝ) := planarRadius ⁻¹' A
  have hR : MeasurableSet R := hA.preimage planarRadius_measurable
  have hcancel := halfDisc_weighted_cos_cancellation (A.indicator g) r
  change (∫ z : ℝ × ℝ in D ∩ R,
    g (planarRadius z) * Real.cos (planarAngle z)) = 0
  rw [← hcancel]
  have hDR : D ∩ R = R ∩ D := inter_comm D R
  rw [hDR]
  rw [← Measure.restrict_restrict hR]
  rw [← integral_indicator hR]
  apply integral_congr_ae
  filter_upwards with z
  simp only [R, Set.indicator, mem_preimage]
  split_ifs <;> simp_all

/-- On the open upper half-plane, the first coordinate divided by the radius
is the cosine of the polar angle. -/
-- @node: planarFirst_div_radius_eq_cos
lemma planarFirst_div_radius_eq_cos (z : ℝ × ℝ) (hz : 0 < z.2) :
    z.1 / planarRadius z = Real.cos (planarAngle z) := by
  have hsource : z ∈ polarCoord.source := by
    simp only [polarCoord_source, mem_union, mem_setOf_eq]
    exact Or.inr hz.ne'
  have hinv := polarCoord.left_inv hsource
  have hx := congrArg Prod.fst hinv
  have hr : planarRadius z = (polarCoord z).1 := rfl
  simp only [polarCoord_symm_apply] at hx
  rw [hr]
  unfold planarAngle
  have hpos : 0 < (polarCoord z).1 := by
    simpa only [polarCoord_target, mem_prod, mem_Ioi, mem_Ioo] using
      (polarCoord.map_source hsource).1
  apply (div_eq_iff hpos.ne').2
  rw [← hx]
  ring

/-- A radial weight times the Cartesian direction cosine has zero integral on
an open upper half-disc. -/
-- @node: halfDisc_weighted_first_div_radius_cancellation
lemma halfDisc_weighted_first_div_radius_cancellation
    (g : ℝ → ℝ) (r : ℝ) :
    (∫ z : ℝ × ℝ in {z | 0 < z.2 ∧ planarRadius z ≤ r},
      g (planarRadius z) * (z.1 / planarRadius z)) = 0 := by
  have heq : (∫ z : ℝ × ℝ in {z | 0 < z.2 ∧ planarRadius z ≤ r},
      g (planarRadius z) * (z.1 / planarRadius z)) =
      ∫ z : ℝ × ℝ in {z | 0 < z.2 ∧ planarRadius z ≤ r},
        g (planarRadius z) * Real.cos (planarAngle z) := by
    apply integral_congr_ae
    have hD : MeasurableSet {z : ℝ × ℝ | 0 < z.2 ∧ planarRadius z ≤ r} := by
      exact (measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_le
          ((measurable_fst.pow_const 2).add (measurable_snd.pow_const 2)).sqrt
          measurable_const)
    exact ae_restrict_of_forall_mem hD fun z hz => by
      change g (planarRadius z) * (z.1 / planarRadius z) =
        g (planarRadius z) * Real.cos (planarAngle z)
      rw [planarFirst_div_radius_eq_cos z hz.1]
  rw [heq]
  exact halfDisc_weighted_cos_cancellation g r

/-- Replacing the open diameter of an upper half-disc by the closed diameter
does not affect the Cartesian cosine integral. -/
-- @node: closedHalfDisc_weighted_first_div_radius_cancellation
lemma closedHalfDisc_weighted_first_div_radius_cancellation
    (g : ℝ → ℝ) (r : ℝ) :
    (∫ z : ℝ × ℝ in {z | 0 ≤ z.2 ∧ planarRadius z ≤ r},
      g (planarRadius z) * (z.1 / planarRadius z)) = 0 := by
  rw [setIntegral_congr_set (show
      {z : ℝ × ℝ | 0 ≤ z.2 ∧ planarRadius z ≤ r} =ᵐ[volume]
        {z | 0 < z.2 ∧ planarRadius z ≤ r} by
    show ∀ᵐ z ∂(volume : Measure (ℝ × ℝ)),
      (0 ≤ z.2 ∧ planarRadius z ≤ r) = (0 < z.2 ∧ planarRadius z ≤ r)
    rw [ae_iff]
    apply measure_mono_null (t := {z : ℝ × ℝ | z.2 = 0})
    · intro z hz
      simp only [mem_setOf_eq]
      by_contra hy
      apply hz
      apply propext
      constructor
      · rintro ⟨hy0, hr⟩
        exact ⟨lt_of_le_of_ne hy0 (Ne.symm hy), hr⟩
      · rintro ⟨hy0, hr⟩
        exact ⟨hy0.le, hr⟩
    · rw [Measure.volume_eq_prod]
      rw [show {z : ℝ × ℝ | z.2 = 0} = Set.univ ×ˢ ({0} : Set ℝ) by
        ext z
        simp]
      rw [Measure.prod_prod]
      simp)]
  exact halfDisc_weighted_first_div_radius_cancellation g r

/-- Translation preserves the zero Cartesian-cosine integral over a closed
upper half-disc. -/
-- @node: translatedClosedHalfDisc_weighted_first_div_radius_cancellation
lemma translatedClosedHalfDisc_weighted_first_div_radius_cancellation
    (g : ℝ → ℝ) (r : ℝ) (c : ℝ × ℝ) :
    (∫ z : ℝ × ℝ in
      {z | 0 ≤ (z - c).2 ∧ planarRadius (z - c) ≤ r},
      g (planarRadius (z - c)) * ((z - c).1 / planarRadius (z - c))) = 0 := by
  let D : Set (ℝ × ℝ) := {u | 0 ≤ u.2 ∧ planarRadius u ≤ r}
  let T : (ℝ × ℝ) → (ℝ × ℝ) := fun u => c + u
  have hT : MeasurableEmbedding T :=
    (Homeomorph.addLeft c).measurableEmbedding
  have hmp : MeasurePreserving T (volume : Measure (ℝ × ℝ)) volume :=
    measurePreserving_add_left volume c
  have hset : {z : ℝ × ℝ | 0 ≤ (z - c).2 ∧ planarRadius (z - c) ≤ r} =
      T '' D := by
    ext z
    constructor
    · intro hz
      refine ⟨z - c, ?_, ?_⟩
      · exact hz
      · simp [T]
    · rintro ⟨u, hu, rfl⟩
      simpa [T, D] using hu
  rw [hset, hmp.setIntegral_image_emb hT]
  have hfun : (fun u : ℝ × ℝ =>
      g (planarRadius (T u - c)) * ((T u - c).1 / planarRadius (T u - c))) =
      fun u => g (planarRadius u) * (u.1 / planarRadius u) := by
    funext u
    simp [T]
  rw [hfun]
  exact closedHalfDisc_weighted_first_div_radius_cancellation g r

/-- The cosine-squared angular moment converts a radial weight into the
nonzero `π/2` factor used to cancel the affine regression term. -/
-- @node: halfDisc_weighted_cos_sq
lemma halfDisc_weighted_cos_sq (g : ℝ → ℝ) (r : ℝ) :
    (∫ z : ℝ × ℝ in {z | 0 < z.2 ∧ planarRadius z ≤ r},
      g (planarRadius z) * Real.cos (planarAngle z) ^ 2) =
        (∫ s : ℝ in Ioc 0 r, s * g s) * (Real.pi / 2) := by
  have hcosSq : (∫ θ : ℝ in Ioo 0 Real.pi, Real.cos θ ^ 2) = Real.pi / 2 := by
    rw [← integral_Ioc_eq_integral_Ioo]
    exact integral_cos_sq_zero_to_pi
  calc
    _ = (∫ s : ℝ in Ioc 0 r, s * g s) *
          (∫ θ : ℝ in Ioo 0 Real.pi, Real.cos θ ^ 2) :=
      halfDisc_weighted_polar_integral g (fun θ => Real.cos θ ^ 2) r
    _ = _ := by rw [hcosSq]

/-- A radial integrand on a half-disc admits the expected polar-coordinate
decomposition. -/
-- @node: halfDisc_radial_integral
lemma halfDisc_radial_integral
    (g : ℝ → ℝ) (r : ℝ) :
    (∫ z : ℝ × ℝ in
        {z | 0 < z.2 ∧ planarRadius z ≤ r}, g (planarRadius z)) =
      ∫ s : ℝ in Ioc 0 r, Real.pi * s * g s := by
  let D : Set (ℝ × ℝ) := {z | 0 < z.2 ∧ planarRadius z ≤ r}
  let E : Set (ℝ × ℝ) := Ioc 0 r ×ˢ Ioo 0 Real.pi
  have hD : MeasurableSet D := by
    exact (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le
        ((measurable_fst.pow_const 2).add (measurable_snd.pow_const 2)).sqrt
        measurable_const)
  have hE : MeasurableSet E := measurableSet_Ioc.prod measurableSet_Ioo
  change (∫ z : ℝ × ℝ in D, g (planarRadius z)) = _
  rw [← integral_indicator hD, ← integral_comp_polarCoord_symm]
  rw [show (∫ p in polarCoord.target,
      p.1 • D.indicator (fun z => g (planarRadius z)) (polarCoord.symm p)) =
      ∫ p in E, p.1 * g p.1 by
    rw [← integral_indicator polarCoord.open_target.measurableSet,
      ← integral_indicator hE]
    apply integral_congr_ae
    filter_upwards with p
    by_cases hp : p ∈ polarCoord.target
    · have hptarget := hp
      simp only [polarCoord_target, mem_prod, mem_Ioi, mem_Ioo] at hp
      have hrs : planarRadius (polarCoord.symm p) = p.1 := by
        exact congrArg Prod.fst (polarCoord.right_inv hp)
      have hsin : 0 < Real.sin p.2 ↔ 0 < p.2 := by
        constructor
        · intro hs
          by_contra hn
          exact (not_lt_of_ge (Real.sin_nonpos_of_nonpos_of_neg_pi_le
            (le_of_not_gt hn) hp.2.1.le)) hs
        · intro htheta
          exact Real.sin_pos_of_pos_of_lt_pi htheta hp.2.2
      have hy : 0 < p.1 * Real.sin p.2 ↔ 0 < p.2 :=
        (mul_pos_iff_of_pos_left hp.1).trans hsin
      have hmem : polarCoord.symm p ∈ D ↔ p ∈ E := by
        change (0 < (polarCoord.symm p).2 ∧
            planarRadius (polarCoord.symm p) ≤ r) ↔
          (0 < p.1 ∧ p.1 ≤ r) ∧ 0 < p.2 ∧ p.2 < Real.pi
        rw [hrs]
        simp only [polarCoord_symm_apply]
        rw [hy]
        constructor
        · rintro ⟨hptheta, hpr⟩
          exact ⟨⟨hp.1, hpr⟩, hptheta, hp.2.2⟩
        · rintro ⟨⟨_, hpr⟩, hptheta, _⟩
          exact ⟨hptheta, hpr⟩
      by_cases h : polarCoord.symm p ∈ D
      · rw [indicator_of_mem hptarget, indicator_of_mem h,
          indicator_of_mem (hmem.mp h), hrs]
        rfl
      · rw [indicator_of_mem hptarget]
        simp only [Set.indicator]
        rw [if_neg h, if_neg (mt hmem.mpr h)]
        simp
    · have hpE : p ∉ E := by
        rintro ⟨⟨hp0, _⟩, hptheta0, hpthetapi⟩
        apply hp
        simp only [polarCoord_target, mem_prod, mem_Ioi, mem_Ioo]
        exact ⟨hp0, lt_trans (neg_lt_zero.mpr Real.pi_pos) hptheta0, hpthetapi⟩
      simp only [Set.indicator]
      rw [if_neg hp, if_neg hpE]
  ]
  rw [show (fun p : ℝ × ℝ => p.1 * g p.1) =
      fun p => (p.1 * g p.1) * (1 : ℝ) by funext p; ring]
  change (∫ p in Ioc 0 r ×ˢ Ioo 0 Real.pi,
    (p.1 * g p.1) * (1 : ℝ)) = _
  rw [Measure.volume_eq_prod]
  rw [setIntegral_prod_mul (μ := volume) (ν := volume)
    (fun s : ℝ => s * g s) (fun _ : ℝ => (1 : ℝ)) (Ioc 0 r) (Ioo 0 Real.pi)]
  rw [setIntegral_one_eq_measureReal, Measure.real_def, Real.volume_Ioo]
  simp only [sub_zero, ENNReal.toReal_ofReal Real.pi_pos.le]
  rw [mul_comm, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with s
  ring

/-- Multiplication by cosine contributes zero after angular integration on
every radial shell. -/
lemma halfDisc_cos_radial_cancellation
    (g : ℝ → ℝ) (r : ℝ) :
    (∫ s : ℝ in Ioc 0 r,
      s * g s * (∫ θ : ℝ in Ioc 0 Real.pi, Real.cos θ)) = 0 := by
  rw [integral_cos_zero_to_pi]
  simp

/-- Translating an upper half-disc does not change the cosine cancellation. -/
-- @node: translatedHalfDisc_weighted_cos_cancellation
lemma translatedHalfDisc_weighted_cos_cancellation
    (g : ℝ → ℝ) (r : ℝ) (c : ℝ × ℝ) :
    (∫ z : ℝ × ℝ in
        (fun u : ℝ × ℝ => c + u) ''
          {u | 0 < u.2 ∧ planarRadius u ≤ r},
      g (planarRadius (z - c)) * Real.cos (planarAngle (z - c))) = 0 := by
  let D : Set (ℝ × ℝ) := {u | 0 < u.2 ∧ planarRadius u ≤ r}
  let T : (ℝ × ℝ) → (ℝ × ℝ) := fun u => c + u
  have hT : MeasurableEmbedding T :=
    (Homeomorph.addLeft c).measurableEmbedding
  have hmp : MeasurePreserving T (volume : Measure (ℝ × ℝ)) volume :=
    measurePreserving_add_left volume c
  rw [show (fun u : ℝ × ℝ => c + u) = T by rfl]
  rw [hmp.setIntegral_image_emb hT
    (fun z => g (planarRadius (z - c)) * Real.cos (planarAngle (z - c))) D]
  have hpoint : (fun u : ℝ × ℝ =>
      g (planarRadius (T u - c)) * Real.cos (planarAngle (T u - c))) =
      fun u => g (planarRadius u) * Real.cos (planarAngle u) := by
    funext u
    simp [T]
  rw [hpoint]
  exact halfDisc_weighted_cos_cancellation g r

/-- Translation preserves cosine cancellation on every measurable radial
subset of a half-disc. -/
-- @node: translatedHalfDisc_radialSet_weighted_cos_cancellation
lemma translatedHalfDisc_radialSet_weighted_cos_cancellation
    (g : ℝ → ℝ) (r : ℝ) (c : ℝ × ℝ)
    {A : Set ℝ} (hA : MeasurableSet A) :
    (∫ z : ℝ × ℝ in
      ((fun u : ℝ × ℝ => c + u) ''
        {u | 0 < u.2 ∧ planarRadius u ≤ r}) ∩
          {z | planarRadius (z - c) ∈ A},
      g (planarRadius (z - c)) * Real.cos (planarAngle (z - c))) = 0 := by
  let D : Set (ℝ × ℝ) :=
    (fun u : ℝ × ℝ => c + u) '' {u | 0 < u.2 ∧ planarRadius u ≤ r}
  let R : Set (ℝ × ℝ) := {z | planarRadius (z - c) ∈ A}
  have hR : MeasurableSet R := by
    exact hA.preimage (planarRadius_measurable.comp (by fun_prop))
  have hcancel :=
    translatedHalfDisc_weighted_cos_cancellation (A.indicator g) r c
  change (∫ z : ℝ × ℝ in D ∩ R,
    g (planarRadius (z - c)) * Real.cos (planarAngle (z - c))) = 0
  rw [← hcancel]
  have hDR : D ∩ R = R ∩ D := inter_comm D R
  rw [hDR]
  rw [← Measure.restrict_restrict hR]
  rw [← integral_indicator hR]
  apply integral_congr_ae
  filter_upwards with z
  simp only [R, Set.indicator, mem_setOf_eq]
  split_ifs <;> simp_all

end Causalean.Mathlib.Analysis
