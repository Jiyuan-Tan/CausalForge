import CausalSmith.Stat.STAT_SaPlmCumulantConverse_Research.Helpers.SpectralMeasurability
import CausalSmith.Stat.STAT_SaPlmCumulantConverse_Research.Helpers.ProjectedOutputCertification
import Causalean.Mathlib.Analysis.ArgumentPrincipleCircle.Basic
import Mathlib.MeasureTheory.Function.Floor

/-! # Soundness of the one bounded-domain option-A selector -/

noncomputable section

open MeasureTheory Set
open Causalean.Mathlib.Analysis.ArgumentPrincipleCircle
open Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic
open Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Complex

namespace CausalSmith.Stat.SaPlmCumulantConverse

variable {Xspace : Type*} [MeasurableSpace Xspace]

private lemma measurable_canonicalDyadicInterval (precision : ℕ) :
    Measurable (fun x : ℝ ↦ canonicalDyadicInterval x precision) := by
  let floorMap : ℝ → ℤ := fun x ↦
    ⌊(2 : ℝ) ^ (precision + 1) * x⌋
  have hfloor : Measurable floorMap := by
    dsimp [floorMap]
    exact (measurable_const.mul measurable_id).floor
  let assemble : ℤ → RatInterval := fun z ↦
    let scale : ℚ := (2 : ℚ) ^ (precision + 1)
    let lower : ℚ := z / scale
    ⟨lower, lower + 1 / scale, le_add_of_nonneg_right (by positivity)⟩
  have hassemble : Measurable assemble := measurable_of_countable assemble
  exact hassemble.comp hfloor

private lemma measurable_ratCast_real : Measurable (fun q : ℚ ↦ (q : ℝ)) :=
  measurable_of_countable _

/-- Every mesh endpoint consumed by trapezoidal quadrature is evaluated by
the bounded adapter. -/
def EndpointComplete (schedule :
    Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Complex.Schedule) : Prop :=
  ∀ k, k ∈ List.range (schedule.mesh + 1) ↔ k ≤ schedule.mesh

/-- [Every quadrature schedule enumerates exactly the mesh endpoints it needs:
an index appears in the enumerated list of nodes precisely when it does not
exceed the schedule's mesh count](goal), so the bounded adapter evaluates the
integrand at all of them and at nothing else. -/
lemma endpointComplete (schedule :
    Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Complex.Schedule) :
    EndpointComplete schedule := by
  intro k
  simp

/-- Exact precision and fuel facts required by every schedule actually used
by the bounded program.  `amplification` is the interval-map envelope; it is
separate from `schedule.magnitude`, which remains the contour Lipschitz
constant used only by the mesh bound. -/
def ExactSpectralSchedule (schedule : Schedule) (amplification : ℚ) : Prop :=
  schedule.inputPrecision =
      circleInputPrecision 1 (spectralNodeTarget schedule.tolerance) ∧
    circleExpFuel 1 schedule.mesh (spectralNodeTarget schedule.tolerance) ≤
      schedule.fuel ∧
    spectralEmpiricalMapFuel (spectralNodeTarget schedule.tolerance)
      schedule.operationCount amplification ≤ schedule.fuel ∧
    spectralNormFuel (spectralNodeTarget schedule.tolerance) ≤ schedule.fuel ∧
    spectralSqrtFuel (spectralNodeTarget schedule.tolerance) ≤ schedule.fuel ∧
    spectralEndpointFuel schedule.operationCount ≤ schedule.fuel ∧
    spectralDerivedFuel (spectralNodeTarget schedule.tolerance)
      schedule.operationCount amplification ≤ schedule.fuel

private lemma exactSpectralSchedule_spectralSchedule
    (tolerance : PosRat) (operations : ℕ) (lipschitz amplification : ℚ)
    (hL : 0 ≤ lipschitz) (hAmp : 0 ≤ amplification) :
    ExactSpectralSchedule
      (spectralSchedule tolerance operations lipschitz amplification hL hAmp)
      amplification := by
  refine ⟨rfl, spectralSchedule_circleExpFuel_le _ _ _ _ _ _,
    spectralSchedule_empiricalMapFuel_le _ _ _ _ _ _,
    spectralSchedule_normFuel_le _ _ _ _ _ _,
    spectralSchedule_sqrtFuel_le _ _ _ _ _ _,
    spectralSchedule_endpointFuel_le _ _ _ _ _ _, ?_⟩
  exact spectralSchedule_derivedFuel_le _ _ _ _ _ _

private lemma spectralEmpiricalMapFuel_le_natAmplification
    (e : PosRat) {operations operations' A : ℕ} {L : ℚ}
    (hoperations : operations ≤ operations') (hA : L.num.natAbs ≤ A) :
    spectralEmpiricalMapFuel e operations L ≤
      spectralEmpiricalMapFuel e operations' (A : ℚ) := by
  unfold spectralEmpiricalMapFuel
  norm_num
  gcongr

private lemma boundedComplexMap_eval_subinterval_of_le
    {box : ComplexRatInterval} (map : BoundedComplexMap box)
    (hvalid : map.Valid) {K : ComplexRatInterval} {z : ℂ}
    (hbox : K.Subinterval box) (hz : K.Contains z) {m n : ℕ} (hmn : m ≤ n) :
    (map.eval K n).Subinterval (map.eval K m) := by
  have hnested := (hvalid.2.2 hbox hz).2.1
  induction n, hmn using Nat.le_induction with
  | base => exact ⟨RatInterval.subinterval_refl _, RatInterval.subinterval_refl _⟩
  | succ n h ih =>
      exact ⟨RatInterval.subinterval_trans (hnested n).1 ih.1,
        RatInterval.subinterval_trans (hnested n).2 ih.2⟩

private lemma boundedComplexMap_eval_width_of_precision_le
    {box : ComplexRatInterval} (map : BoundedComplexMap box)
    (hvalid : map.Valid) {K : ComplexRatInterval} {z : ℂ}
    (hbox : K.Subinterval box) (hz : K.Contains z) (e : PosRat) (fuel : ℕ)
    (hle : map.precision e ≤ fuel) :
    (map.eval K fuel).width ≤ map.derivativeEnvelope * K.width + e.1 := by
  exact (complexRectangle_width_mono
      (boundedComplexMap_eval_subinterval_of_le map hvalid hbox hz hle)).trans
    ((hvalid.2.2 hbox hz).2.2 e)

private lemma rectangle_subinterval_symmetric_of_contains_width
    (I : ComplexRatInterval) (z : ℂ) (U : ℕ)
    (hz : I.Contains z)
    (hre : |z.re| ≤ (U : ℝ)) (him : |z.im| ≤ (U : ℝ))
    (hw : I.width ≤ 2) :
    I.Subinterval
      ⟨⟨-(U : ℚ) - 2, (U : ℚ) + 2, by
          linarith⟩,
        ⟨-(U : ℚ) - 2, (U : ℚ) + 2, by
          linarith⟩⟩ := by
  have hrew : I.re.width ≤ 2 := (le_max_left _ _).trans hw
  have himw : I.im.width ≤ 2 := (le_max_right _ _).trans hw
  rw [abs_le] at hre him
  change (-(U : ℚ) - 2 ≤ I.re.lo ∧ I.re.hi ≤ (U : ℚ) + 2) ∧
    (-(U : ℚ) - 2 ≤ I.im.lo ∧ I.im.hi ≤ (U : ℚ) + 2)
  constructor
  · unfold RatInterval.width at hrew
    rcases hz.1 with ⟨hzlo, hzhi⟩
    rcases hre with ⟨hzlower, hzupper⟩
    constructor
    · exact_mod_cast (show (-(U : ℝ) - 2) ≤ (I.re.lo : ℝ) by
        have hrewR : (I.re.hi : ℝ) - I.re.lo ≤ 2 := by exact_mod_cast hrew
        linarith)
    · exact_mod_cast (show (I.re.hi : ℝ) ≤ (U : ℝ) + 2 by
        have hrewR : (I.re.hi : ℝ) - I.re.lo ≤ 2 := by exact_mod_cast hrew
        linarith)
  · unfold RatInterval.width at himw
    rcases hz.2 with ⟨hzlo, hzhi⟩
    rcases him with ⟨hzlower, hzupper⟩
    constructor
    · exact_mod_cast (show (-(U : ℝ) - 2) ≤ (I.im.lo : ℝ) by
        have himwR : (I.im.hi : ℝ) - I.im.lo ≤ 2 := by exact_mod_cast himw
        linarith)
    · exact_mod_cast (show (I.im.hi : ℝ) ≤ (U : ℝ) + 2 by
        have himwR : (I.im.hi : ℝ) - I.im.lo ≤ 2 := by exact_mod_cast himw
        linarith)

private lemma postArith_W_bound {R C A l t e : ℚ}
    (hR : 0 ≤ R) (hC : 0 ≤ C) (hA : 0 ≤ A) (hl : 0 < l)
    (ht : 0 ≤ t) (he : 0 ≤ e) (he16 : 16 * e ≤ 1)
    (hCA : C ^ 2 ≤ A) :
    let M := C + 1
    let T := 36 * R * (1 + e)
    let tw := 2 * (9 * t + 4 * R * (1 + e) * t)
    let δ := l ^ 2 / 4
    let W := 2 * ((2 * M ^ 2 / δ) * tw +
      T * (8 * M ^ 3 * (M * t) / δ ^ 2 + 4 * M * (M * t) / δ))
    let J := 576 * (1 + A) / l ^ 2 + 2720 * R * (1 + A) / l ^ 2 +
      39168 * R * (1 + A) ^ 2 / l ^ 4
    W ≤ t * J := by
  dsimp only
  have hM2 : (C + 1) ^ 2 ≤ 2 * (1 + A) := by
    nlinarith [sq_nonneg (C - 1)]
  have hM4 : (C + 1) ^ 4 ≤ 4 * (1 + A) ^ 2 := by
    have hs := mul_self_le_mul_self (sq_nonneg (C + 1)) hM2
    nlinarith
  have hRe : R * (1 + e) ≤ 17 * R / 16 := by
    have := mul_le_mul_of_nonneg_left he16 hR
    nlinarith
  have hReM2 : R * (1 + e) * (C + 1) ^ 2 ≤
      (17 * R / 16) * (2 * (1 + A)) := by
    exact mul_le_mul hRe hM2 (sq_nonneg _) (by positivity)
  have hReM4 : R * (1 + e) * (C + 1) ^ 4 ≤
      (17 * R / 16) * (4 * (1 + A) ^ 2) := by
    exact mul_le_mul hRe hM4 (by positivity) (by positivity)
  have hM2_l2_t := mul_le_mul_of_nonneg_left hM2
    (mul_nonneg ht (sq_nonneg l))
  have hReM2_l2_t := mul_le_mul_of_nonneg_left hReM2
    (mul_nonneg ht (sq_nonneg l))
  have hReM4_t := mul_le_mul_of_nonneg_left hReM4 ht
  field_simp [ne_of_gt hl]
  nlinarith [hM2_l2_t, hReM2_l2_t, hReM4_t]
private lemma postArith_combine_J {A R l Q : ℚ} (hl : 0 < l)
    (h0 : 16 * (1 + A) * l ^ 4 ≤ Q)
    (h1 : 16 * (R * (1 + A)) * l ^ 4 ≤ Q)
    (h2 : 16 * (R * (1 + A) ^ 2) * l ^ 2 ≤ Q) :
    16 * (576 * (1 + A) / l ^ 2 + 2720 * R * (1 + A) / l ^ 2 +
      39168 * R * (1 + A) ^ 2 / l ^ 4) * l ^ 6 ≤ 42464 * Q := by
  have hw0 := mul_le_mul_of_nonneg_left h0 (by norm_num : (0 : ℚ) ≤ 576)
  have hw1 := mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℚ) ≤ 2720)
  have hw2 := mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℚ) ≤ 39168)
  have hw := add_le_add (add_le_add hw0 hw1) hw2
  have hl62 : l ^ 6 / l ^ 2 = l ^ 4 := by field_simp [ne_of_gt hl]
  have hl64 : l ^ 6 / l ^ 4 = l ^ 2 := by field_simp [ne_of_gt hl]
  have heq0 : 16 * (576 * (1 + A) / l ^ 2) * l ^ 6 =
      576 * (16 * (1 + A) * l ^ 4) := by
    calc
      _ = 576 * (16 * (1 + A) * (l ^ 6 / l ^ 2)) := by ring
      _ = _ := by rw [hl62]
  have heq1 : 16 * (2720 * R * (1 + A) / l ^ 2) * l ^ 6 =
      2720 * (16 * (R * (1 + A)) * l ^ 4) := by
    calc
      _ = 2720 * (16 * (R * (1 + A)) * (l ^ 6 / l ^ 2)) := by ring
      _ = _ := by rw [hl62]
  have heq2 : 16 * (39168 * R * (1 + A) ^ 2 / l ^ 4) * l ^ 6 =
      39168 * (16 * (R * (1 + A) ^ 2) * l ^ 2) := by
    calc
      _ = 39168 * (16 * (R * (1 + A) ^ 2) * (l ^ 6 / l ^ 4)) := by ring
      _ = _ := by rw [hl64]
  calc
    _ = 576 * (16 * (1 + A) * l ^ 4) +
        2720 * (16 * (R * (1 + A)) * l ^ 4) +
        39168 * (16 * (R * (1 + A) ^ 2) * l ^ 2) := by
          rw [mul_add, mul_add, add_mul, add_mul, heq0, heq1, heq2]
    _ ≤ 576 * Q + 2720 * Q + 39168 * Q := hw
    _ = 42464 * Q := by ring

private lemma postArith_cancel_J {b l D : ℚ} (hl : 0 < l) (hD : 0 < D) :
    (b * l ^ 4 / (1 + l) ^ 4 /
        (16384 * D * (1 + l⁻¹ + l⁻¹ ^ 2))) *
      (42464 * D * (1 + l) ^ 4 * (l ^ 2 + l + 1) / (16 * l ^ 6)) =
      (42464 / (64 * 256 * 16)) * b := by
  field_simp [ne_of_gt hl, ne_of_gt hD]
  <;> ring

private lemma postArith_divide_J {J Q l : ℚ} (hl : 0 < l)
    (h : 16 * J * l ^ 6 ≤ Q) : J ≤ Q / (16 * l ^ 6) := by
  apply (le_div_iff₀ (by positivity)).2
  simpa only [mul_assoc, mul_left_comm, mul_comm] using h

private lemma postArith_J_nonneg {R A l : ℚ} (hR : 0 ≤ R) (hA : 0 ≤ A)
    (hl : 0 < l) : 0 ≤ 576 * (1 + A) / l ^ 2 +
      2720 * R * (1 + A) / l ^ 2 +
      39168 * R * (1 + A) ^ 2 / l ^ 4 := by
  positivity

private lemma postArith_tUpper_nonneg {b l D G : ℚ} (hb : 0 < b) (hl : 0 < l)
    (hD : 0 < D) (hG : 0 < G) :
    0 ≤ (b * l ^ 4 / (1 + l) ^ 4) / (16384 * D * G) := by
  positivity

set_option maxHeartbeats 1000000 in
private lemma postArith_tJ_bound {R A S l r t b : ℚ}
    (hR : 0 ≤ R) (hA : 0 ≤ A) (hl : 0 < l) (hr : 0 < r)
    (ht0 : 0 < t) (hb : 0 < b) (hb1 : b ≤ 1)
    (hguard : r ≤ b * l ^ 2 / (1 + l) ^ 2)
    (hscale : 256 * (1 + R) * (1 + A) ^ 2 *
      (1 + l⁻¹ + l⁻¹ ^ 2) ≤ S)
    (ht : 64 * S * t = r ^ 2) :
    let J := 576 * (1 + A) / l ^ 2 + 2720 * R * (1 + A) / l ^ 2 +
      39168 * R * (1 + A) ^ 2 / l ^ 4
    t * J ≤ (42464 / (64 * 256 * 16)) * b := by
  dsimp only
  let D : ℚ := (1 + R) * (1 + A) ^ 2
  let K : ℚ := l ^ 2 + l + 1
  let P : ℚ := (1 + l) ^ 4
  have hD0 : 0 < D := by dsimp [D]; positivity
  have hK0 : 0 < K := by dsimp [K]; nlinarith [sq_nonneg l]
  have hP0 : 0 < P := by dsimp [P]; positivity
  have hl20 : 0 < l ^ 2 := sq_pos_of_pos hl
  have hl60 : 0 < l ^ 6 := by positivity
  have hq0 : 0 ≤ b * l ^ 2 / (1 + l) ^ 2 := by positivity
  have hguardSq : r ^ 2 ≤ (b * l ^ 2 / (1 + l) ^ 2) ^ 2 :=
    by simpa [pow_two] using mul_self_le_mul_self hr.le hguard
  have hbSq : b ^ 2 ≤ b := by
    nlinarith [mul_nonneg hb.le (sub_nonneg.mpr hb1)]
  have hr2 : r ^ 2 ≤ b * l ^ 4 / (1 + l) ^ 4 := by
    calc
      r ^ 2 ≤ (b * l ^ 2 / (1 + l) ^ 2) ^ 2 := hguardSq
      _ = b ^ 2 * l ^ 4 / (1 + l) ^ 4 := by
        field_simp [show 1 + l ≠ 0 by positivity]
      _ ≤ b * l ^ 4 / (1 + l) ^ 4 := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hbSq (by positivity)) (by positivity)
  let G : ℚ := 1 + l⁻¹ + l⁻¹ ^ 2
  have hG0 : 0 < G := by dsimp [G]; positivity
  have hden0 : 0 < 16384 * D * G := by positivity
  have hscale_t := mul_le_mul_of_nonneg_right hscale
    (show (0 : ℚ) ≤ 64 * t by positivity)
  have htScale : t ≤ r ^ 2 / (16384 * D * G) := by
    apply (le_div_iff₀ hden0).2
    dsimp [D, G]
    nlinarith [hscale_t, ht]
  have htUpper : t ≤
      (b * l ^ 4 / (1 + l) ^ 4) / (16384 * D * G) :=
    htScale.trans (div_le_div_of_nonneg_right hr2 hden0.le)
  have hfour : 4 * l ≤ (1 + l) ^ 2 := by nlinarith [sq_nonneg (l - 1)]
  have h16 : 16 * l ^ 2 ≤ P := by
    have hs := mul_self_le_mul_self (by positivity : (0 : ℚ) ≤ 4 * l) hfour
    dsimp [P]
    nlinarith
  have hshape2 : 16 * l ^ 2 ≤ P * K := by
    have hK1 : 1 ≤ K := by dsimp [K]; nlinarith [sq_nonneg l]
    calc
      16 * l ^ 2 ≤ P := h16
      _ = P * 1 := by ring
      _ ≤ P * K := mul_le_mul_of_nonneg_left hK1 hP0.le
  have hshape4 : 16 * l ^ 4 ≤ P * K := by
    have hKl2 : l ^ 2 ≤ K := by dsimp [K]; linarith
    have hmul := mul_le_mul_of_nonneg_right h16 (sq_nonneg l)
    calc
      16 * l ^ 4 = (16 * l ^ 2) * l ^ 2 := by ring
      _ ≤ P * l ^ 2 := hmul
      _ ≤ P * K := mul_le_mul_of_nonneg_left hKl2 hP0.le
  have hDA : 1 + A ≤ D := by
    have hA1 : (1 : ℚ) ≤ 1 + A := by linarith
    have hA0 : (0 : ℚ) ≤ 1 + A := by linarith
    have hAsq : 1 + A ≤ (1 + A) ^ 2 := by
      simpa [pow_two] using mul_le_mul_of_nonneg_left hA1 hA0
    calc
      1 + A ≤ (1 + A) ^ 2 := hAsq
      _ ≤ D := by
        dsimp [D]
        simpa using mul_le_mul_of_nonneg_right
          (by linarith : (1 : ℚ) ≤ 1 + R) (sq_nonneg (1 + A))
  have hDRA : R * (1 + A) ≤ D := by
    have hA1 : (1 : ℚ) ≤ 1 + A := by linarith
    have hA0 : (0 : ℚ) ≤ 1 + A := by linarith
    have hAsq : 1 + A ≤ (1 + A) ^ 2 := by
      simpa [pow_two] using mul_le_mul_of_nonneg_left hA1 hA0
    calc
      R * (1 + A) ≤ R * (1 + A) ^ 2 :=
        mul_le_mul_of_nonneg_left hAsq hR
      _ ≤ D := by
        dsimp [D]
        exact mul_le_mul_of_nonneg_right (by linarith : R ≤ 1 + R) (sq_nonneg _)
  have hDRA2 : R * (1 + A) ^ 2 ≤ D := by
    dsimp [D]
    exact mul_le_mul_of_nonneg_right (by linarith : R ≤ 1 + R) (sq_nonneg _)
  have hterm0 := mul_le_mul hDA hshape4 (by positivity) (by positivity)
  have hterm1 := mul_le_mul hDRA hshape4 (by positivity) (by positivity)
  have hterm2 := mul_le_mul hDRA2 hshape2 (by positivity) (by positivity)
  have hterm0' : 16 * (1 + A) * l ^ 4 ≤ D * P * K := by
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hterm0
  have hterm1' : 16 * (R * (1 + A)) * l ^ 4 ≤ D * P * K := by
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hterm1
  have hterm2' : 16 * (R * (1 + A) ^ 2) * l ^ 2 ≤ D * P * K := by
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hterm2
  have hJshape : 16 *
      (576 * (1 + A) / l ^ 2 + 2720 * R * (1 + A) / l ^ 2 +
        39168 * R * (1 + A) ^ 2 / l ^ 4) * l ^ 6 ≤
      42464 * D * P * K := by
    simpa only [mul_assoc] using
      (postArith_combine_J hl hterm0' hterm1' hterm2')
  have hJUpper :
      576 * (1 + A) / l ^ 2 + 2720 * R * (1 + A) / l ^ 2 +
      39168 * R * (1 + A) ^ 2 / l ^ 4 ≤
      42464 * D * P * K / (16 * l ^ 6) := by
    exact postArith_divide_J hl hJshape
  have hprod := mul_le_mul htUpper hJUpper
    (postArith_J_nonneg hR hA hl)
    (postArith_tUpper_nonneg hb hl hD0 hG0)
  calc
    _ ≤ (b * l ^ 4 / (1 + l) ^ 4 /
          (16384 * D * (1 + l⁻¹ + l⁻¹ ^ 2))) *
        (42464 * D * (1 + l) ^ 4 * (l ^ 2 + l + 1) / (16 * l ^ 6)) := by
      simpa only [D, K, P, G] using hprod
    _ = _ := postArith_cancel_J hl hD0
private lemma postArith_H_finish {R C b l D t : ℚ}
    (hl : 0 < l) (hb : 0 < b) (hD : 0 < D) (ht0 : 0 < t)
    (hRC : R * C ≤ D)
    (htUpper : t ≤ (b * l ^ 4 / (1 + l) ^ 4) /
      (16384 * D * (1 + l⁻¹ + l⁻¹ ^ 2))) :
    (R * C / (16 * l)) * t ≤ b / (1024 * 256) := by
  have hl5PK : l ^ 5 ≤ (1 + l) ^ 4 * (l ^ 2 + l + 1) := by
    calc
      l ^ 5 ≤ l ^ 5 + (1 + 5 * l + 11 * l ^ 2 + 14 * l ^ 3 +
          11 * l ^ 4 + 4 * l ^ 5 + l ^ 6) :=
        le_add_of_nonneg_right (by positivity)
      _ = (1 + l) ^ 4 * (l ^ 2 + l + 1) := by ring
  have hprod := mul_le_mul hRC htUpper (by positivity) (by positivity)
  field_simp [ne_of_gt hl] at hprod
  have hprod' : (16384 * R * C * t) *
      ((1 + l) ^ 4 * (l ^ 2 + l + 1)) ≤ b * l ^ 6 := by
    nlinarith [hprod]
  have hright : b * l ^ 6 ≤ (b * l) *
      ((1 + l) ^ 4 * (l ^ 2 + l + 1)) := by
    have hm := mul_le_mul_of_nonneg_left hl5PK (mul_nonneg hb.le hl.le)
    nlinarith [hm]
  have hall := hprod'.trans hright
  have hPK0 : 0 < (1 + l) ^ 4 * (l ^ 2 + l + 1) := by positivity
  have hcore : 16384 * R * C * t ≤ b * l :=
    le_of_mul_le_mul_right hall hPK0
  field_simp [ne_of_gt hl]
  nlinarith [hcore]

private lemma postArith_Ht_bound {R C A S l r t b : ℚ}
    (hR : 0 ≤ R) (hC : 0 ≤ C) (hA : 0 ≤ A) (hl : 0 < l)
    (hr : 0 < r) (ht0 : 0 < t) (hb : 0 < b) (hb1 : b ≤ 1)
    (hCA : C ^ 2 ≤ A)
    (hguard : r ≤ b * l ^ 2 / (1 + l) ^ 2)
    (hscale : 256 * (1 + R) * (1 + A) ^ 2 *
      (1 + l⁻¹ + l⁻¹ ^ 2) ≤ S)
    (ht : 64 * S * t = r ^ 2) :
    (R * C / (16 * l)) * t ≤ b / (1024 * 256) := by
  have hC1A : C ≤ 1 + A := by nlinarith [sq_nonneg (C - 1)]
  have hRC : R * C ≤ (1 + R) * (1 + A) ^ 2 := by
    have hA1 : 1 + A ≤ (1 + A) ^ 2 := by
      have h1 : (1 : ℚ) ≤ 1 + A := by linarith
      simpa [pow_two] using
        mul_le_mul_of_nonneg_left h1 (by linarith : 0 ≤ 1 + A)
    calc
      R * C ≤ R * (1 + A) := mul_le_mul_of_nonneg_left hC1A hR
      _ ≤ R * (1 + A) ^ 2 := mul_le_mul_of_nonneg_left hA1 hR
      _ ≤ (1 + R) * (1 + A) ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
  have hguardSq : r ^ 2 ≤ (b * l ^ 2 / (1 + l) ^ 2) ^ 2 := by
    simpa [pow_two] using mul_self_le_mul_self hr.le hguard
  have hbSq : b ^ 2 ≤ b := by
    nlinarith [mul_nonneg hb.le (sub_nonneg.mpr hb1)]
  have hr2 : r ^ 2 ≤ b * l ^ 4 / (1 + l) ^ 4 := by
    calc
      r ^ 2 ≤ (b * l ^ 2 / (1 + l) ^ 2) ^ 2 := hguardSq
      _ = b ^ 2 * l ^ 4 / (1 + l) ^ 4 := by field_simp [show 1 + l ≠ 0 by positivity]
      _ ≤ b * l ^ 4 / (1 + l) ^ 4 := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hbSq (by positivity)) (by positivity)
  let D : ℚ := (1 + R) * (1 + A) ^ 2
  let G : ℚ := 1 + l⁻¹ + l⁻¹ ^ 2
  have hD0 : 0 < D := by dsimp [D]; positivity
  have hG0 : 0 < G := by dsimp [G]; positivity
  have hscale_t := mul_le_mul_of_nonneg_right hscale (show (0 : ℚ) ≤ 64 * t by positivity)
  have htUpper : t ≤ (b * l ^ 4 / (1 + l) ^ 4) / (16384 * D * G) := by
    have htScale : t ≤ r ^ 2 / (16384 * D * G) := by
      apply (le_div_iff₀ (by positivity)).2
      dsimp [D, G]
      nlinarith [hscale_t, ht]
    exact htScale.trans (div_le_div_of_nonneg_right hr2 (by positivity))
  simpa only [D, G] using postArith_H_finish hl hb hD0 ht0 hRC htUpper
set_option maxHeartbeats 2400000 in
-- This is the raw-rectangle form of `CertifiedComplex.norm_width_at_precision`.
private lemma normInterval_width_of_width_maxAbs
    (K : ComplexRatInterval) (ε η : PosRat) (M : ℚ) (k : ℕ)
    (hM : 0 ≤ M) (hA : K.maxAbs ≤ M)
    (hη : η.1 ≤ ε.1)
    (hKw : K.width ≤ ε.1 ^ 2 / (16 * (M + 1)))
    (hkN : 64 * (η.1.den + 1) * (M.num.natAbs + 2) ^ 2 ≤ k) :
    (K.normInterval k).width ≤ ε.1 := by
  let D := K.normSq
  have hreA : K.re.maxAbs ≤ M := (le_max_left _ _).trans hA
  have himA : K.im.maxAbs ≤ M := (le_max_right _ _).trans hA
  have hrew : K.re.width ≤ ε.1 ^ 2 / (16 * (M + 1)) :=
    (le_max_left _ _).trans hKw
  have himw : K.im.width ≤ ε.1 ^ 2 / (16 * (M + 1)) :=
    (le_max_right _ _).trans hKw
  have hDw : D.width ≤ 4 * M * (ε.1 ^ 2 / (16 * (M + 1))) := by
    rw [show D.width = K.re.sq.width + K.im.sq.width by
      simp [D, ComplexRatInterval.normSq, RatInterval.width_add]]
    have hre := ComplexRatInterval.rat_sq_width_le K.re
    have him := ComplexRatInterval.rat_sq_width_le K.im
    have hre0 : 0 ≤ K.re.maxAbs := (abs_nonneg K.re.lo).trans (le_max_left _ _)
    have him0 : 0 ≤ K.im.maxAbs := (abs_nonneg K.im.lo).trans (le_max_left _ _)
    have hδ0 : 0 ≤ ε.1 ^ 2 / (16 * (M + 1)) := by positivity
    nlinarith [mul_le_mul hreA hrew (RatInterval.width_nonneg K.re) hM,
      mul_le_mul himA himw (RatInterval.width_nonneg K.im) hM]
  have hDwε : D.width ≤ ε.1 ^ 2 / 4 := by
    refine hDw.trans ?_
    have hMp : 0 < M + 1 := by linarith
    rw [show 4 * M * (ε.1 ^ 2 / (16 * (M + 1))) =
      (M * ε.1 ^ 2) / (4 * (M + 1)) by
        field_simp [ne_of_gt hMp]
        ring]
    apply (div_le_iff₀ (by positivity : (0 : ℚ) < 4 * (M + 1))).2
    nlinarith [sq_nonneg ε.1]
  have hDhi : D.hi ≤ 2 * M ^ 2 := by
    change K.re.sq.hi + K.im.sq.hi ≤ 2 * M ^ 2
    have hrehi := ComplexRatInterval.rat_sq_hi_le K.re
    have himhi := ComplexRatInterval.rat_sq_hi_le K.im
    have hre0 : 0 ≤ K.re.maxAbs := (abs_nonneg K.re.lo).trans (le_max_left _ _)
    have him0 : 0 ≤ K.im.maxAbs := (abs_nonneg K.im.lo).trans (le_max_left _ _)
    nlinarith [mul_self_le_mul_self hre0 hreA, mul_self_le_mul_self him0 himA]
  have hMle : M ≤ (M.num.natAbs : ℕ) := by
    have hnum0 : 0 ≤ M.num := Rat.num_nonneg.mpr hM
    calc
      M = (M.num : ℚ) / (M.den : ℕ) := (Rat.num_div_den M).symm
      _ ≤ (M.num : ℚ) := div_le_self (by exact_mod_cast hnum0)
        (by exact_mod_cast Rat.den_pos M)
      _ = (M.num.natAbs : ℕ) := by
        have hi : (M.num.natAbs : ℤ) = M.num := Int.natAbs_of_nonneg hnum0
        exact (congrArg (fun x : ℤ => (x : ℚ)) hi).symm
  have hηden : (1 : ℚ) ≤ η.1 * (η.1.den : ℕ) := by
    have hnumpos : 0 < η.1.num := (Rat.num_pos).2 η.2
    have hrepr := Rat.num_div_den η.1
    have hdenpos : (0 : ℚ) < η.1.den := by exact_mod_cast Rat.den_pos η.1
    have heq : (η.1.num : ℚ) = η.1 * (η.1.den : ℕ) :=
      (div_eq_iff hdenpos.ne').mp hrepr
    rw [← heq]
    exact_mod_cast hnumpos
  have hrate : (D.hi + 1) / (k + 1) ≤ η.1 / 4 := by
    have hDcoarse : 4 * (D.hi + 1) ≤ 8 * (M.num.natAbs + 2 : ℕ) ^ 2 := by
      have hp : (M : ℚ) ≤ (M.num.natAbs : ℕ) := hMle
      have hMsq := mul_self_le_mul_self hM hp
      have hMsq' : M ^ 2 ≤ (M.num.natAbs : ℚ) ^ 2 := by
        simpa [pow_two] using hMsq
      calc
        4 * (D.hi + 1) ≤ 4 * (2 * M ^ 2 + 1) := by nlinarith [hDhi]
        _ ≤ 8 * (M.num.natAbs + 2 : ℕ) ^ 2 := by
          push_cast
          nlinarith [hMsq', sq_nonneg (M.num.natAbs : ℚ)]
    have hkcast : (64 * (η.1.den + 1) * (M.num.natAbs + 2) ^ 2 : ℕ) ≤
        k + 1 := hkN.trans (Nat.le_add_right k 1)
    have hkcast' : (64 * (η.1.den + 1) *
        (M.num.natAbs + 2) ^ 2 : ℚ) ≤ k + 1 := by exact_mod_cast hkcast
    have hηfac : 1 ≤ η.1 * (η.1.den + 1 : ℕ) :=
      hηden.trans (mul_le_mul_of_nonneg_left (by norm_num) η.2.le)
    have hP : (0 : ℚ) ≤ (M.num.natAbs + 2 : ℕ) ^ 2 := by positivity
    have h64 : 64 * (M.num.natAbs + 2 : ℕ) ^ 2 ≤
        η.1 * (64 * (η.1.den + 1) * (M.num.natAbs + 2) ^ 2 : ℕ) := by
      push_cast
      have hh : 64 * (M.num.natAbs + 2 : ℚ) ^ 2 * 1 ≤
          64 * (M.num.natAbs + 2 : ℚ) ^ 2 *
            (η.1 * (η.1.den + 1 : ℕ)) :=
        mul_le_mul_of_nonneg_left hηfac
          (by positivity : (0 : ℚ) ≤ 64 * (M.num.natAbs + 2 : ℚ) ^ 2)
      calc
        64 * (M.num.natAbs + 2 : ℚ) ^ 2 =
            64 * (M.num.natAbs + 2 : ℚ) ^ 2 * 1 := by ring
        _ ≤
            64 * (M.num.natAbs + 2 : ℚ) ^ 2 *
              (η.1 * (η.1.den + 1 : ℕ)) := hh
        _ = η.1 * (64 * (η.1.den + 1) *
            (M.num.natAbs + 2 : ℚ) ^ 2) := by
          norm_num only [Nat.cast_add, Nat.cast_one]
          ring
    have hbig : 8 * (M.num.natAbs + 2 : ℕ) ^ 2 ≤ η.1 * (k + 1) := by
      push_cast at hDcoarse ⊢
      nlinarith [mul_le_mul_of_nonneg_left hkcast' η.2.le, h64]
    apply (div_le_iff₀ (by positivity : (0 : ℚ) < k + 1)).2
    nlinarith
  have hsqrtspan : Real.sqrt (D.hi : ℝ) - Real.sqrt (D.lo : ℝ) ≤
      (ε.1 : ℝ) / 2 := by
    have hlo0 : (0 : ℝ) ≤ D.lo := by
      exact_mod_cast ComplexRatInterval.normSq_lo_nonneg K
    have hDcast : (D.lo : ℝ) ≤ D.hi := by exact_mod_cast D.lo_le_hi
    have hhi0 : (0 : ℝ) ≤ D.hi := hlo0.trans hDcast
    have hslo := Real.sq_sqrt hlo0
    have hshi := Real.sq_sqrt hhi0
    have hsord := Real.sqrt_le_sqrt hDcast
    have hw : (D.hi : ℝ) - D.lo ≤ (ε.1 : ℝ) ^ 2 / 4 := by
      exact_mod_cast hDwε
    have hεr : (0 : ℝ) < ε.1 := by exact_mod_cast ε.2
    have hspan0 : 0 ≤ Real.sqrt (D.hi : ℝ) - Real.sqrt (D.lo : ℝ) :=
      sub_nonneg.mpr hsord
    apply (sq_le_sq₀ hspan0 (by positivity : (0 : ℝ) ≤ (ε.1 : ℝ) / 2)).mp
    calc
      (Real.sqrt (D.hi : ℝ) - Real.sqrt (D.lo : ℝ)) ^ 2 ≤
          (D.hi : ℝ) - D.lo := by
        nlinarith [mul_nonneg (Real.sqrt_nonneg (D.lo : ℝ))
          (Real.sqrt_nonneg (D.hi : ℝ))]
      _ ≤ (ε.1 : ℝ) ^ 2 / 4 := hw
      _ = ((ε.1 : ℝ) / 2) ^ 2 := by ring
  rw [ComplexRatInterval.normInterval, RatInterval.sqrtInterval_width]
  have hblo := RatInterval.sqrt_iterates_sound D.lo
    (ComplexRatInterval.normSq_lo_nonneg K) k
  have hbhi := RatInterval.sqrt_iterates_sound D.hi
    ((ComplexRatInterval.normSq_lo_nonneg K).trans D.lo_le_hi) k
  have hrlo := RatInterval.sqrt_gap_rate D.lo
    (ComplexRatInterval.normSq_lo_nonneg K) k
  have hrhi := RatInterval.sqrt_gap_rate D.hi
    ((ComplexRatInterval.normSq_lo_nonneg K).trans D.lo_le_hi) k
  have hrate_lo : (D.lo + 1) / (k + 1) ≤ η.1 / 4 :=
    (div_le_div_of_nonneg_right (by linarith [D.lo_le_hi]) (by positivity)).trans hrate
  exact_mod_cast (show
    (RatInterval.sqrtUpper D.hi k : ℝ) - RatInterval.sqrtLower D.lo k ≤
      (ε.1 : ℝ) by
    have hrlo' : ((RatInterval.sqrtUpper D.lo k -
        RatInterval.sqrtLower D.lo k : ℚ) : ℝ) ≤ η.1 / 4 := by
      exact_mod_cast hrlo.trans hrate_lo
    have hrhi' : ((RatInterval.sqrtUpper D.hi k -
        RatInterval.sqrtLower D.hi k : ℚ) : ℝ) ≤ η.1 / 4 := by
      exact_mod_cast hrhi.trans hrate
    norm_num at hrlo' hrhi'
    have huhi : (RatInterval.sqrtUpper D.hi k : ℝ) - Real.sqrt D.hi ≤
        η.1 / 4 := by linarith [hrhi', hbhi.1]
    have hllo : Real.sqrt D.lo - (RatInterval.sqrtLower D.lo k : ℝ) ≤
        η.1 / 4 := by linarith [hrlo', hblo.2]
    have hηr : (η.1 : ℝ) ≤ ε.1 := by exact_mod_cast hη
    linarith [huhi, hllo, hsqrtspan, hηr])

/-- A represented spectral input is *canonical* when it is the record actually
produced by the estimator's data-encoding step: there exist certified bank
inputs, a certified range input, a treatment-regression code sequence, and a
sample of observations on the covariate space such that the input is the
canonical encoding built from them.

This is the standing regularity assumption under which the certified evaluators
in this file are sound: it rules out hand-crafted records whose observation
names are not the floor-dyadic encodings of real data. -/
def CanonicalRepresentedSpectralInput (X : Type*) [MeasurableSpace X]
    (input : RepresentedSpectralInput p) : Prop :=
  ∃ (pStar : CertifiedBankInputs p) (cStar : CertifiedRangeInput p)
      (gcode : ℕ → X → ℝ) (data : Fin p.n → Obs X),
    input = canonicalRepresentedInput p pStar cStar gcode data

/-- Full-box validity of the empirical denominator map on canonical
floor-dyadic represented inputs.  The exponential and derivative envelopes
use `spectralFullBoxRadius B`, not the smaller selected-circle radius. -/
lemma spectralDenominatorMap_valid_of_canonical
    (input : RepresentedSpectralInput p) (B : ContourBankData)
    (I : Finset (Fin p.n)) (derivative : ℕ)
    (hcanonical : CanonicalRepresentedSpectralInput Xspace input) :
    (spectralDenominatorMap input B I derivative).Valid := by
  refine ⟨empiricalFDerivativeBound_nonneg input (spectralFullBoxRadius B) derivative,
    mul_nonneg (by norm_num) (empiricalFWidthBound_nonneg input
      (spectralFullBoxRadius B) derivative (spectralFullBoxRadius_nonneg B)), ?_⟩
  intro K z hK hz
  have hraw : ∀ fuel,
      (spectralDenominatorRawEval input I derivative K fuel).Contains
        ((spectralDenominatorMap input B I derivative).value z) :=
    fun fuel ↦ spectralDenominatorRawEval_sound_of_canonical input B I derivative
      hcanonical hK hz fuel
  refine ⟨fun fuel ↦ (tightenAcrossFuel_spec _ _ hraw fuel).1,
    fun fuel ↦ (tightenAcrossFuel_spec _ _ hraw fuel).2.1, ?_⟩
  intro e
  exact (complexRectangle_width_mono
    (tightenAcrossFuel_spec _ _ hraw
      ((spectralDenominatorMap input B I derivative).precision e)).2.2).trans
    (spectralDenominatorRawEval_width_of_canonical input B I derivative
      hcanonical K hK e)

/-- Full-box validity of the empirical numerator map on canonical
floor-dyadic represented inputs. -/
lemma spectralNumeratorMap_valid_of_canonical
    (input : RepresentedSpectralInput p) (B : ContourBankData)
    (I : Finset (Fin p.n)) (derivative : ℕ)
    (hcanonical : CanonicalRepresentedSpectralInput Xspace input) :
    (spectralNumeratorMap input B I derivative).Valid := by
  refine ⟨empiricalGDerivativeBound_nonneg input (spectralFullBoxRadius B) derivative,
    mul_nonneg (by norm_num) (empiricalGWidthBound_nonneg input
      (spectralFullBoxRadius B) derivative (spectralFullBoxRadius_nonneg B)), ?_⟩
  intro K z hK hz
  have hraw : ∀ fuel,
      (spectralNumeratorRawEval input I derivative K fuel).Contains
        ((spectralNumeratorMap input B I derivative).value z) :=
    fun fuel ↦ spectralNumeratorRawEval_sound_of_canonical input B I derivative
      hcanonical hK hz fuel
  refine ⟨fun fuel ↦ (tightenAcrossFuel_spec _ _ hraw fuel).1,
    fun fuel ↦ (tightenAcrossFuel_spec _ _ hraw fuel).2.1, ?_⟩
  intro e
  exact (complexRectangle_width_mono
    (tightenAcrossFuel_spec _ _ hraw
      ((spectralNumeratorMap input B I derivative).precision e)).2.2).trans
    (spectralNumeratorRawEval_width_of_canonical input B I derivative
      hcanonical K hK e)

private lemma contourBank_rho_pos_le_UR (p : Parameters)
    (pStar : CertifiedBankInputs p)
    (j : Fin ((contourBank p pStar).JBase + 1)) :
    0 < (contourBank p pStar).rho j ∧
      (contourBank p pStar).rho j ≤ (contourBank p pStar).UR := by
  have hj : (j : ℕ) ≤ 2 ^
      (4 * positiveCeil
          (CertifiedReal.refine pStar.psietaName.name errorOne).hi ^ 2 *
        (positiveCeil
          (CertifiedReal.refine pStar.R1Name.name errorOne).hi + 2) ^ 3 + 2) :=
    Nat.le_of_lt_succ j.isLt
  have hq := rat_grid_lt_one
    (4 * positiveCeil
        (CertifiedReal.refine pStar.psietaName.name errorOne).hi ^ 2 *
      (positiveCeil
        (CertifiedReal.refine pStar.R1Name.name errorOne).hi + 2) ^ 3 + 2)
    (j : ℕ) hj
  have hq' :
      (1 / 4 : ℚ) + (j : ℕ) * (1 / 2 : ℚ) ^
        (4 * positiveCeil
            (CertifiedReal.refine pStar.psietaName.name errorOne).hi ^ 2 *
          (positiveCeil
            (CertifiedReal.refine pStar.R1Name.name errorOne).hi + 2) ^ 3 + 3) < 1 := by
    simpa [Nat.add_assoc] using hq
  have hR1hi : pStar.R1Name.name.value ≤
      (CertifiedReal.refine pStar.R1Name.name errorOne).hi :=
    (CertifiedReal.refine_contains pStar.R1Name.name errorOne).2
  have hhiUR : (CertifiedReal.refine pStar.R1Name.name errorOne).hi ≤
      (positiveCeil
        (CertifiedReal.refine pStar.R1Name.name errorOne).hi : ℕ) := by
    exact_mod_cast rat_le_positiveCeil
      (CertifiedReal.refine pStar.R1Name.name errorOne).hi
  dsimp [contourBank, CertifiedReal.add, CertifiedReal.ofRat]
  constructor
  · have hR0pos : 0 < pStar.R0Name.name.value :=
      lt_of_lt_of_le (by exact_mod_cast pStar.R0Name.lower_pos)
        pStar.R0Name.lower_le_value
    positivity
  ·
    have hqR : (((1 / 4 : ℚ) + (j : ℕ) * (1 / 2 : ℚ) ^
        (4 * positiveCeil
            (CertifiedReal.refine pStar.psietaName.name errorOne).hi ^ 2 *
          (positiveCeil
            (CertifiedReal.refine pStar.R1Name.name errorOne).hi + 2) ^ 3 + 3) : ℚ) : ℝ) < 1 :=
      by exact_mod_cast hq'
    have hltR1 : pStar.R0Name.name.value +
        (((1 / 4 : ℚ) + (j : ℕ) * (1 / 2 : ℚ) ^
          (4 * positiveCeil
              (CertifiedReal.refine pStar.psietaName.name errorOne).hi ^ 2 *
            (positiveCeil
              (CertifiedReal.refine pStar.R1Name.name errorOne).hi + 2) ^ 3 + 3) : ℚ) : ℝ) <
        pStar.R1Name.name.value := by
      rw [pStar.R1_value, pStar.searchRadius_contract, ← pStar.R0_value]
      linarith
    have hhiURR : ((CertifiedReal.refine pStar.R1Name.name errorOne).hi : ℝ) ≤
        (positiveCeil (CertifiedReal.refine pStar.R1Name.name errorOne).hi : ℕ) := by
      exact_mod_cast hhiUR
    exact (le_of_lt hltR1).trans (hR1hi.trans hhiURR)

private lemma spectralDenominatorMap_hasDerivAt
    (input : RepresentedSpectralInput p) (B : ContourBankData)
    (I : Finset (Fin p.n)) (d : ℕ) (z : ℂ) :
    HasDerivAt (spectralDenominatorMap input B I d).value
      ((spectralDenominatorMap input B I (d + 1)).value z) z := by
  have hsum : HasDerivAt
      (fun z : ℂ ↦ ∑ i ∈ I,
        (((representedResidual input i).value ^ d : ℝ) : ℂ) *
          Complex.exp (z * (representedResidual input i).value))
      (∑ i ∈ I, (((representedResidual input i).value ^ (d + 1) : ℝ) : ℂ) *
        Complex.exp (z * (representedResidual input i).value)) z := by
    have hsum' : HasDerivAt
        (∑ i ∈ I, fun z : ℂ ↦
          (((representedResidual input i).value ^ d : ℝ) : ℂ) *
            Complex.exp (z * (representedResidual input i).value))
        (∑ i ∈ I, (((representedResidual input i).value ^ (d + 1) : ℝ) : ℂ) *
          Complex.exp (z * (representedResidual input i).value)) z := by
      apply HasDerivAt.sum
      intro i hi
      let x : ℝ := (representedResidual input i).value
      refine ((hasDerivAt_const z (((x ^ d : ℝ) : ℂ))).fun_mul
          ((Complex.hasDerivAt_exp (z * x)).comp z
            ((hasDerivAt_id z).mul_const (x : ℂ)))).congr_deriv ?_
      simp only [x, Function.comp_apply, id_eq]
      push_cast
      ring
    convert hsum' using 1 <;> ext w <;> simp only [Finset.sum_apply]
  have h := (hasDerivAt_const z (((max I.card 1 : ℝ)⁻¹ : ℂ))).fun_mul hsum
  simpa only [spectralDenominatorMap, zero_mul, zero_add] using h

private lemma spectralNumeratorMap_hasDerivAt
    (input : RepresentedSpectralInput p) (B : ContourBankData)
    (I : Finset (Fin p.n)) (d : ℕ) (z : ℂ) :
    HasDerivAt (spectralNumeratorMap input B I d).value
      ((spectralNumeratorMap input B I (d + 1)).value z) z := by
  have hsum : HasDerivAt
      (fun z : ℂ ↦ ∑ i ∈ I,
        (((input.observations i).yName.value *
          (representedResidual input i).value ^ d : ℝ) : ℂ) *
          Complex.exp (z * (representedResidual input i).value))
      (∑ i ∈ I, (((input.observations i).yName.value *
        (representedResidual input i).value ^ (d + 1) : ℝ) : ℂ) *
        Complex.exp (z * (representedResidual input i).value)) z := by
    have hsum' : HasDerivAt
        (∑ i ∈ I, fun z : ℂ ↦
          (((input.observations i).yName.value *
            (representedResidual input i).value ^ d : ℝ) : ℂ) *
            Complex.exp (z * (representedResidual input i).value))
        (∑ i ∈ I, (((input.observations i).yName.value *
          (representedResidual input i).value ^ (d + 1) : ℝ) : ℂ) *
          Complex.exp (z * (representedResidual input i).value)) z := by
      apply HasDerivAt.sum
      intro i hi
      let x : ℝ := (representedResidual input i).value
      let y : ℝ := (input.observations i).yName.value
      refine ((hasDerivAt_const z (((y * x ^ d : ℝ) : ℂ))).fun_mul
          ((Complex.hasDerivAt_exp (z * x)).comp z
            ((hasDerivAt_id z).mul_const (x : ℂ)))).congr_deriv ?_
      simp only [x, y, Function.comp_apply, id_eq]
      push_cast
      ring
    convert hsum' using 1 <;> ext w <;> simp only [Finset.sum_apply]
  have h := (hasDerivAt_const z (((max I.card 1 : ℝ)⁻¹ : ℂ))).fun_mul hsum
  simpa only [spectralNumeratorMap, zero_mul, zero_add] using h

private lemma abs_value_le_interval_maxAbs {I : RatInterval} {x : ℝ}
    (hx : I.Contains x) : |x| ≤ (I.maxAbs : ℚ) := by
  rw [abs_le]
  constructor
  · have hlo : (-(I.maxAbs : ℚ) : ℝ) ≤ I.lo := by
      have hloQ : -I.maxAbs ≤ I.lo := by
        unfold RatInterval.maxAbs
        exact (neg_le_neg (le_max_left _ _)).trans (neg_abs_le _)
      exact_mod_cast hloQ
    exact hlo.trans hx.1
  · have hhi : (I.hi : ℝ) ≤ I.maxAbs := by
      exact_mod_cast (le_abs_self I.hi).trans (le_max_right _ _)
    exact hx.2.trans hhi

private lemma residual_value_abs_le (input : RepresentedSpectralInput p) (i : Fin p.n) :
    |(representedResidual input i).value| ≤ residualUpper input i := by
  exact abs_value_le_interval_maxAbs
    ((representedResidual input i).contains
      ((representedResidual input i).modulus errorOne))

private lemma outcome_value_abs_le (input : RepresentedSpectralInput p) (i : Fin p.n) :
    |(input.observations i).yName.value| ≤ outcomeUpper input i := by
  exact abs_value_le_interval_maxAbs
    ((input.observations i).yName.contains
      ((input.observations i).yName.modulus errorOne))

private lemma complexExp_mul_norm_le_rationalExpEnvelope
    {z : ℂ} {x : ℝ} {rho S : ℚ}
    (hrho : 0 ≤ rho) (hS : 0 ≤ S) (hz : ‖z‖ ≤ rho) (hx : |x| ≤ S) :
    ‖Complex.exp (z * x)‖ ≤ rationalExpEnvelope rho S := by
  let q : ℚ := max 0 (rho * S)
  let k : ℤ := ⌈q⌉
  let n : ℕ := k.toNat
  have hq0 : 0 ≤ q := le_max_left _ _
  have hqk : q ≤ (k : ℚ) := Int.le_ceil q
  have hk0 : 0 ≤ k := by
    exact_mod_cast hq0.trans hqk
  have hqn : q ≤ (n : ℚ) := by
    have hkn : (n : ℤ) = k := Int.toNat_of_nonneg hk0
    rw [← hkn] at hqk
    exact_mod_cast hqk
  have hre : (z * (x : ℂ)).re ≤ (n : ℕ) := by
    calc
      (z * (x : ℂ)).re ≤ ‖z * (x : ℂ)‖ := Complex.re_le_norm _
      _ = ‖z‖ * |x| := by simp
      _ ≤ (rho : ℝ) * S := mul_le_mul hz (by exact_mod_cast hx)
        (abs_nonneg _) (by exact_mod_cast hrho)
      _ ≤ q := by exact_mod_cast le_max_right (0 : ℚ) (rho * S)
      _ ≤ n := by exact_mod_cast hqn
  have hpow : Real.exp (n : ℝ) ≤ (3 : ℝ) ^ n := by
    rw [← Real.exp_one_pow]
    exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le n
  rw [Complex.norm_exp]
  exact (Real.exp_le_exp.mpr hre).trans (by
    simpa [rationalExpEnvelope, q, k, n] using hpow)

private lemma spectralDenominatorMap_norm_le
    (input : RepresentedSpectralInput p) (B : ContourBankData)
    (I : Finset (Fin p.n)) (d : ℕ) {z : ℂ} {rho : ℚ}
    (hrho : 0 ≤ rho) (hz : ‖z‖ ≤ rho) :
    ‖(spectralDenominatorMap input B I d).value z‖ ≤
      empiricalFDerivativeBound input rho d := by
  have hscale : ‖(((max I.card 1 : ℝ)⁻¹ : ℂ))‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
    exact inv_le_one₀ (by positivity) |>.2 (by exact_mod_cast Nat.le_max_right I.card 1)
  have hterm : ∀ i : Fin p.n,
      ‖((((representedResidual input i).value ^ d : ℝ) : ℂ) *
        Complex.exp (z * (representedResidual input i).value))‖ ≤
        (residualUpper input i ^ d *
          rationalExpEnvelope rho (residualUpper input i) : ℚ) := by
    intro i
    push_cast
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul
      (pow_le_pow_left₀ (abs_nonneg _) (residual_value_abs_le input i) d)
      (complexExp_mul_norm_le_rationalExpEnvelope hrho
        (residualUpper_nonneg input i) hz (residual_value_abs_le input i))
      (norm_nonneg _) (pow_nonneg (by
        exact_mod_cast residualUpper_nonneg input i) d)
  unfold spectralDenominatorMap empiricalFDerivativeBound
  rw [norm_mul]
  calc
    ‖(((max I.card 1 : ℝ)⁻¹ : ℂ))‖ *
        ‖∑ i ∈ I, (((representedResidual input i).value ^ d : ℝ) : ℂ) *
          Complex.exp (z * (representedResidual input i).value)‖ ≤
        ‖∑ i ∈ I, (((representedResidual input i).value ^ d : ℝ) : ℂ) *
          Complex.exp (z * (representedResidual input i).value)‖ := by
      simpa using mul_le_mul_of_nonneg_right hscale (norm_nonneg _)
    _ ≤ ∑ i ∈ I, ‖((((representedResidual input i).value ^ d : ℝ) : ℂ) *
          Complex.exp (z * (representedResidual input i).value))‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ I, (residualUpper input i ^ d *
          rationalExpEnvelope rho (residualUpper input i) : ℚ) := by
      push_cast
      apply Finset.sum_le_sum
      intro i hi
      convert hterm i using 1 <;> push_cast <;> rfl
    _ ≤ ∑ i, (residualUpper input i ^ d *
          rationalExpEnvelope rho (residualUpper input i) : ℚ) := by
      push_cast
      apply Finset.sum_le_univ_sum_of_nonneg
      intro i
      apply mul_nonneg
      · exact pow_nonneg (by exact_mod_cast residualUpper_nonneg input i) d
      · unfold rationalExpEnvelope
        positivity
    _ = _ := by push_cast; rfl

private lemma spectralNumeratorMap_norm_le
    (input : RepresentedSpectralInput p) (B : ContourBankData)
    (I : Finset (Fin p.n)) (d : ℕ) {z : ℂ} {rho : ℚ}
    (hrho : 0 ≤ rho) (hz : ‖z‖ ≤ rho) :
    ‖(spectralNumeratorMap input B I d).value z‖ ≤
      empiricalGDerivativeBound input rho d := by
  have hscale : ‖(((max I.card 1 : ℝ)⁻¹ : ℂ))‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
    exact inv_le_one₀ (by positivity) |>.2 (by exact_mod_cast Nat.le_max_right I.card 1)
  have hterm : ∀ i : Fin p.n,
      ‖((((input.observations i).yName.value *
        (representedResidual input i).value ^ d : ℝ) : ℂ) *
        Complex.exp (z * (representedResidual input i).value))‖ ≤
        (outcomeUpper input i * residualUpper input i ^ d *
          rationalExpEnvelope rho (residualUpper input i) : ℚ) := by
    intro i
    push_cast
    rw [norm_mul, norm_mul, norm_pow]
    simp only [Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul
      (mul_le_mul (outcome_value_abs_le input i)
        (pow_le_pow_left₀ (abs_nonneg _) (residual_value_abs_le input i) d)
        (pow_nonneg (abs_nonneg _) d)
        (by exact_mod_cast outcomeUpper_nonneg input i))
      (complexExp_mul_norm_le_rationalExpEnvelope hrho
        (residualUpper_nonneg input i) hz (residual_value_abs_le input i))
      (norm_nonneg _) (mul_nonneg
        (by exact_mod_cast outcomeUpper_nonneg input i)
        (pow_nonneg (by exact_mod_cast residualUpper_nonneg input i) d))
  unfold spectralNumeratorMap empiricalGDerivativeBound
  rw [norm_mul]
  calc
    ‖(((max I.card 1 : ℝ)⁻¹ : ℂ))‖ *
        ‖∑ i ∈ I, (((input.observations i).yName.value *
          (representedResidual input i).value ^ d : ℝ) : ℂ) *
          Complex.exp (z * (representedResidual input i).value)‖ ≤
        ‖∑ i ∈ I, (((input.observations i).yName.value *
          (representedResidual input i).value ^ d : ℝ) : ℂ) *
          Complex.exp (z * (representedResidual input i).value)‖ := by
      simpa using mul_le_mul_of_nonneg_right hscale (norm_nonneg _)
    _ ≤ ∑ i ∈ I, ‖((((input.observations i).yName.value *
          (representedResidual input i).value ^ d : ℝ) : ℂ) *
          Complex.exp (z * (representedResidual input i).value))‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ I, (outcomeUpper input i * residualUpper input i ^ d *
          rationalExpEnvelope rho (residualUpper input i) : ℚ) := by
      push_cast
      apply Finset.sum_le_sum
      intro i hi
      convert hterm i using 1 <;> push_cast <;> rfl
    _ ≤ ∑ i, (outcomeUpper input i * residualUpper input i ^ d *
          rationalExpEnvelope rho (residualUpper input i) : ℚ) := by
      push_cast
      apply Finset.sum_le_univ_sum_of_nonneg
      intro i
      apply mul_nonneg
      · apply mul_nonneg
        · exact_mod_cast outcomeUpper_nonneg input i
        · exact pow_nonneg (by exact_mod_cast residualUpper_nonneg input i) d
      · unfold rationalExpEnvelope
        positivity
    _ = _ := by push_cast; rfl

private lemma spectralDenominatorMap_lipschitzOn_disk
    (input : RepresentedSpectralInput p) (B : ContourBankData)
    (I : Finset (Fin p.n)) (d : ℕ) {rho : ℚ} (hrho : 0 ≤ rho)
    {z w : ℂ} (hz : ‖z‖ ≤ rho) (hw : ‖w‖ ≤ rho) :
    ‖(spectralDenominatorMap input B I d).value z -
        (spectralDenominatorMap input B I d).value w‖ ≤
      (empiricalFDerivativeBound input rho (d + 1) : ℝ) * ‖z - w‖ := by
  have hz' : z ∈ Metric.closedBall (0 : ℂ) (rho : ℝ) := by simpa using hz
  have hw' : w ∈ Metric.closedBall (0 : ℂ) (rho : ℝ) := by simpa using hw
  have hmv := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le (𝕜 := ℂ)
      (f := (spectralDenominatorMap input B I d).value)
      (f' := fun x ↦ ContinuousLinearMap.toSpanSingleton ℂ
        ((spectralDenominatorMap input B I (d + 1)).value x))
      (x := w) (y := z) (C := (empiricalFDerivativeBound input rho (d + 1) : ℝ))
      (fun x hx ↦ HasFDerivAt.hasFDerivWithinAt
        (spectralDenominatorMap_hasDerivAt input B I d x).hasFDerivAt)
      (fun x hx ↦ by
        simp only [ContinuousLinearMap.norm_toSpanSingleton]
        exact spectralDenominatorMap_norm_le input B I (d + 1) hrho (by simpa using hx))
      (convex_closedBall (0 : ℂ) (rho : ℝ))
      hw' hz'
  simpa [norm_sub_rev] using hmv

private lemma spectralNumeratorMap_lipschitzOn_disk
    (input : RepresentedSpectralInput p) (B : ContourBankData)
    (I : Finset (Fin p.n)) (d : ℕ) {rho : ℚ} (hrho : 0 ≤ rho)
    {z w : ℂ} (hz : ‖z‖ ≤ rho) (hw : ‖w‖ ≤ rho) :
    ‖(spectralNumeratorMap input B I d).value z -
        (spectralNumeratorMap input B I d).value w‖ ≤
      (empiricalGDerivativeBound input rho (d + 1) : ℝ) * ‖z - w‖ := by
  have hz' : z ∈ Metric.closedBall (0 : ℂ) (rho : ℝ) := by simpa using hz
  have hw' : w ∈ Metric.closedBall (0 : ℂ) (rho : ℝ) := by simpa using hw
  have hmv := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le (𝕜 := ℂ)
      (f := (spectralNumeratorMap input B I d).value)
      (f' := fun x ↦ ContinuousLinearMap.toSpanSingleton ℂ
        ((spectralNumeratorMap input B I (d + 1)).value x))
      (x := w) (y := z) (C := (empiricalGDerivativeBound input rho (d + 1) : ℝ))
      (fun x hx ↦ HasFDerivAt.hasFDerivWithinAt
        (spectralNumeratorMap_hasDerivAt input B I d x).hasFDerivAt)
      (fun x hx ↦ by
        simp only [ContinuousLinearMap.norm_toSpanSingleton]
        exact spectralNumeratorMap_norm_le input B I (d + 1) hrho (by simpa using hx))
      (convex_closedBall (0 : ℂ) (rho : ℝ))
      hw' hz'
  simpa [norm_sub_rev] using hmv

private lemma norm_exp_real_mul_I_sub_le (a b : ℝ) :
    ‖Complex.exp (a * Complex.I) - Complex.exp (b * Complex.I)‖ ≤ |a - b| := by
  have hfactor : Complex.exp (a * Complex.I) - Complex.exp (b * Complex.I) =
      Complex.exp (b * Complex.I) *
        (Complex.exp ((a - b) * Complex.I) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    ring
  rw [hfactor, norm_mul]
  have hb : ‖Complex.exp (b * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  rw [hb, one_mul]
  have harg : (((a : ℂ) - (b : ℂ))) * Complex.I =
      Complex.I * ((a - b : ℝ) : ℂ) := by push_cast; ring
  rw [harg, Complex.norm_exp_I_mul_ofReal_sub_one, norm_mul]
  have hsin : 2 * |Real.sin ((a - b) / 2)| ≤ |a - b| := by
    calc
      2 * |Real.sin ((a - b) / 2)| ≤ 2 * |(a - b) / 2| :=
        mul_le_mul_of_nonneg_left Real.abs_sin_le_abs (by norm_num)
      _ = |a - b| := by rw [abs_div]; norm_num; ring
  simpa [Complex.norm_real, Real.norm_eq_abs] using hsin

private lemma circleMap_sub_norm_le (r : ℝ) (hr : 0 ≤ r) (s t : ℝ) :
    ‖CircleMesh.circleMap 0 r s - CircleMesh.circleMap 0 r t‖ ≤
      8 * r * |s - t| := by
  have hexp := norm_exp_real_mul_I_sub_le (2 * Real.pi * s) (2 * Real.pi * t)
  simp only [CircleMesh.circleMap, zero_add, ← mul_sub, norm_mul]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
  calc
    r * ‖Complex.exp ((2 * Real.pi * s) * Complex.I) -
        Complex.exp ((2 * Real.pi * t) * Complex.I)‖
        ≤ r * |2 * Real.pi * s - 2 * Real.pi * t| :=
          mul_le_mul_of_nonneg_left (by
            convert hexp using 1 <;> push_cast <;> rfl) hr
    _ = r * (2 * Real.pi) * |s - t| := by
      rw [show 2 * Real.pi * s - 2 * Real.pi * t = (2 * Real.pi) * (s - t) by ring,
        abs_mul, abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
      ring
    _ = (2 * Real.pi) * (r * |s - t|) := by ring
    _ ≤ 8 * (r * |s - t|) := by
      exact mul_le_mul_of_nonneg_right (by nlinarith [Real.pi_le_four])
        (mul_nonneg hr (abs_nonneg _))
    _ = 8 * r * |s - t| := by ring

private lemma circleTangent_norm_le (r : ℝ) (hr : 0 ≤ r) (u : ℝ) :
    ‖CircleMesh.circleTangent r u‖ ≤ 8 * r := by
  have hexp : ‖Complex.exp ((2 * Real.pi * u) * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp]
    norm_num
  have hcoef : ‖(2 : ℂ) * (Real.pi : ℂ)‖ = 2 * Real.pi := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    norm_num
  rw [CircleMesh.circleTangent, norm_mul, norm_mul, norm_mul, hexp, hcoef,
    Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
  simp only [mul_one]
  have hpi : 2 * Real.pi ≤ (8 : ℝ) := by nlinarith [Real.pi_le_four]
  nlinarith

private lemma circleTangent_sub_norm_le (r : ℝ) (hr : 0 ≤ r) (s t : ℝ) :
    ‖CircleMesh.circleTangent r s - CircleMesh.circleTangent r t‖ ≤
      64 * r * |s - t| := by
  have hexp := norm_exp_real_mul_I_sub_le (2 * Real.pi * s) (2 * Real.pi * t)
  unfold CircleMesh.circleTangent
  rw [← mul_sub]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hr, Complex.norm_I, one_mul]
  have hexp' :
      ‖Complex.exp ((2 * (Real.pi : ℂ) * (s : ℂ)) * Complex.I) -
          Complex.exp ((2 * (Real.pi : ℂ) * (t : ℂ)) * Complex.I)‖ ≤
        |2 * Real.pi * s - 2 * Real.pi * t| := by
    convert hexp using 1 <;> push_cast <;> rfl
  have hcoef : ‖(2 : ℂ) * (Real.pi : ℂ)‖ = 2 * Real.pi := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    norm_num
  norm_num [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  calc
    (2 * Real.pi) * r *
        ‖Complex.exp ((2 * (Real.pi : ℂ) * (s : ℂ)) * Complex.I) -
          Complex.exp ((2 * (Real.pi : ℂ) * (t : ℂ)) * Complex.I)‖
        ≤ (2 * Real.pi) * r * |2 * Real.pi * s - 2 * Real.pi * t| := by
          exact mul_le_mul_of_nonneg_left hexp'
            (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) hr)
    _ = (2 * Real.pi) ^ 2 * r * |s - t| := by
      rw [show 2 * Real.pi * s - 2 * Real.pi * t = (2 * Real.pi) * (s - t) by ring,
        abs_mul, abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
      ring
    _ ≤ 64 * r * |s - t| := by
      have hsq : (2 * Real.pi) ^ 2 ≤ (8 : ℝ) ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg (by norm_num) Real.pi_pos.le)
          (by nlinarith [Real.pi_le_four]) 2
      have hsq' : (2 * Real.pi) ^ 2 ≤ (64 : ℝ) := by
        norm_num at hsq ⊢
        exact hsq
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hsq' hr)
        (abs_nonneg _)

private lemma pilotMap_norm_lipschitz
    (input : RepresentedSpectralInput p) (B : ContourBankData)
    (I : Finset (Fin p.n)) {r : ℝ} {rho : ℚ}
    (hr : 0 ≤ r) (hrrho : r ≤ rho) (s t : ℝ) :
    |‖(spectralDenominatorMap input B I 0).value
          (CircleMesh.circleMap 0 r s)‖ -
        ‖(spectralDenominatorMap input B I 0).value
          (CircleMesh.circleMap 0 r t)‖| ≤
      (pilotCircleLipschitzBound input rho : ℝ) * |s - t| := by
  have hzs : ‖CircleMesh.circleMap 0 r s‖ ≤ (rho : ℝ) := by
    simpa [CircleMesh.circleMap, Complex.norm_exp, abs_of_nonneg hr] using hrrho
  have hzt : ‖CircleMesh.circleMap 0 r t‖ ≤ (rho : ℝ) := by
    simpa [CircleMesh.circleMap, Complex.norm_exp, abs_of_nonneg hr] using hrrho
  have hmap := spectralDenominatorMap_lipschitzOn_disk input B I 0
    (by exact_mod_cast hr.trans hrrho) hzs hzt
  have hreverse := abs_norm_sub_norm_le
    ((spectralDenominatorMap input B I 0).value (CircleMesh.circleMap 0 r s))
    ((spectralDenominatorMap input B I 0).value (CircleMesh.circleMap 0 r t))
  calc
    |‖(spectralDenominatorMap input B I 0).value (CircleMesh.circleMap 0 r s)‖ -
        ‖(spectralDenominatorMap input B I 0).value (CircleMesh.circleMap 0 r t)‖|
        ≤ ‖(spectralDenominatorMap input B I 0).value (CircleMesh.circleMap 0 r s) -
            (spectralDenominatorMap input B I 0).value (CircleMesh.circleMap 0 r t)‖ := hreverse
    _ ≤ (empiricalFDerivativeBound input rho 1 : ℝ) *
          ‖CircleMesh.circleMap 0 r s - CircleMesh.circleMap 0 r t‖ := hmap
    _ ≤ (empiricalFDerivativeBound input rho 1 : ℝ) * (8 * r * |s - t|) := by
      exact mul_le_mul_of_nonneg_left (circleMap_sub_norm_le r hr s t)
        (by exact_mod_cast empiricalFDerivativeBound_nonneg input rho 1)
    _ = 8 * r * (empiricalFDerivativeBound input rho 1 : ℝ) * |s - t| := by ring
    _ ≤ 8 * (rho : ℝ) * (empiricalFDerivativeBound input rho 1 : ℝ) * |s - t| := by
      gcongr
      exact_mod_cast empiricalFDerivativeBound_nonneg input rho 1
    _ = (pilotCircleLipschitzBound input rho : ℝ) * |s - t| := by
      unfold pilotCircleLipschitzBound
      push_cast
      ring

private lemma quotient_sub_norm_le
    {ns nt ds dt : ℂ} {A N D m delta : ℝ}
    (hm : 0 < m) (hdelta : 0 ≤ delta)
    (hns : ‖ns‖ ≤ A) (hnt : ‖nt‖ ≤ A)
    (hds : m ≤ ‖ds‖) (hdt : m ≤ ‖dt‖)
    (hn : ‖ns - nt‖ ≤ N * delta) (hd : ‖ds - dt‖ ≤ D * delta)
    (hA : 0 ≤ A) (hN : 0 ≤ N) (hD : 0 ≤ D) :
    ‖ns / ds - nt / dt‖ ≤ (N / m + A * D / m ^ 2) * delta := by
  have hds0 : 0 < ‖ds‖ := hm.trans_le hds
  have hdt0 : 0 < ‖dt‖ := hm.trans_le hdt
  have hdsne : ds ≠ 0 := norm_pos_iff.mp hds0
  have hdtne : dt ≠ 0 := norm_pos_iff.mp hdt0
  have hid : ns / ds - nt / dt =
      (ns - nt) / ds + nt * (dt - ds) / (ds * dt) := by
    field_simp [hdsne, hdtne]
    ring
  rw [hid]
  calc
    ‖(ns - nt) / ds + nt * (dt - ds) / (ds * dt)‖ ≤
        ‖(ns - nt) / ds‖ + ‖nt * (dt - ds) / (ds * dt)‖ := norm_add_le _ _
    _ = ‖ns - nt‖ / ‖ds‖ + ‖nt‖ * ‖dt - ds‖ / (‖ds‖ * ‖dt‖) := by
      rw [norm_div, norm_div, norm_mul, norm_mul]
    _ ≤ (N * delta) / m + A * (D * delta) / (m * m) := by
      apply add_le_add
      · rw [div_le_div_iff₀ hds0 hm]
        calc
          ‖ns - nt‖ * m ≤ (N * delta) * m :=
            mul_le_mul_of_nonneg_right hn hm.le
          _ ≤ (N * delta) * ‖ds‖ :=
            mul_le_mul_of_nonneg_left hds (mul_nonneg hN hdelta)
      · have hnum : ‖nt‖ * ‖dt - ds‖ ≤ A * (D * delta) :=
          mul_le_mul hnt (by simpa [norm_sub_rev] using hd)
            (norm_nonneg _) hA
        have hden : m * m ≤ ‖ds‖ * ‖dt‖ :=
          mul_le_mul hds hdt hm.le (norm_nonneg _)
        rw [div_le_div_iff₀ (mul_pos hds0 hdt0) (mul_pos hm hm)]
        calc
          ‖nt‖ * ‖dt - ds‖ * (m * m) ≤ A * (D * delta) * (m * m) :=
            mul_le_mul_of_nonneg_right hnum (mul_nonneg hm.le hm.le)
          _ ≤ A * (D * delta) * (‖ds‖ * ‖dt‖) :=
            mul_le_mul_of_nonneg_left hden
              (mul_nonneg hA (mul_nonneg hD hdelta))
    _ = (N / m + A * D / m ^ 2) * delta := by
      field_simp [ne_of_gt hm]

private lemma circleIntegrand_quotient_lipschitz
    (num den : ℂ → ℂ) {r rho A N D m : ℝ}
    (hr : 0 ≤ r) (hrrho : r ≤ rho) (hm : 0 < m)
    (hA : 0 ≤ A) (hN : 0 ≤ N) (hD : 0 ≤ D)
    (hnumBound : ∀ z, ‖z‖ ≤ rho → ‖num z‖ ≤ A)
    (hnumLip : ∀ z, ‖z‖ ≤ rho → ∀ w, ‖w‖ ≤ rho →
      ‖num z - num w‖ ≤ N * ‖z - w‖)
    (hdenLip : ∀ z, ‖z‖ ≤ rho → ∀ w, ‖w‖ ≤ rho →
      ‖den z - den w‖ ≤ D * ‖z - w‖)
    (s t : ℝ)
    (hdenLowerS : m ≤ ‖den (CircleMesh.circleMap 0 r s)‖)
    (hdenLowerT : m ≤ ‖den (CircleMesh.circleMap 0 r t)‖) :
    ‖CircleMesh.circleIntegrand (fun z ↦ num z / den z) 0 r s -
        CircleMesh.circleIntegrand (fun z ↦ num z / den z) 0 r t‖ ≤
      64 * (r * A / m + r ^ 2 * (N / m + A * D / m ^ 2)) * |s - t| := by
  let zs := CircleMesh.circleMap 0 r s
  let zt := CircleMesh.circleMap 0 r t
  let Ts := CircleMesh.circleTangent r s
  let Tt := CircleMesh.circleTangent r t
  have hzs : ‖zs‖ ≤ rho := by
    dsimp [zs]
    simpa [CircleMesh.circleMap, Complex.norm_exp, abs_of_nonneg hr] using hrrho
  have hzt : ‖zt‖ ≤ rho := by
    dsimp [zt]
    simpa [CircleMesh.circleMap, Complex.norm_exp, abs_of_nonneg hr] using hrrho
  have hdelta : 0 ≤ |s - t| := abs_nonneg _
  have hzst := circleMap_sub_norm_le r hr s t
  have hn := hnumLip zs hzs zt hzt
  have hd := hdenLip zs hzs zt hzt
  have hns := hnumBound zs hzs
  have hnt := hnumBound zt hzt
  have hds := hdenLowerS
  have hdt := hdenLowerT
  have hqdiff : ‖num zs / den zs - num zt / den zt‖ ≤
      (N / m + A * D / m ^ 2) * (8 * r * |s - t|) := by
    exact (quotient_sub_norm_le hm (mul_nonneg (mul_nonneg (by norm_num) hr) hdelta)
      hns hnt hds hdt
      (hn.trans (mul_le_mul_of_nonneg_left hzst hN))
      (hd.trans (mul_le_mul_of_nonneg_left hzst hD)) hA hN hD)
  have hqs : ‖num zs / den zs‖ ≤ A / m := by
    rw [norm_div]
    rw [div_le_div_iff₀ (hm.trans_le hds) hm]
    exact (mul_le_mul_of_nonneg_right hns hm.le).trans
      (mul_le_mul_of_nonneg_left hds hA)
  have hTs := circleTangent_sub_norm_le r hr s t
  have hTt := circleTangent_norm_le r hr t
  have hid : num zs / den zs * Ts - num zt / den zt * Tt =
      num zs / den zs * (Ts - Tt) +
        (num zs / den zs - num zt / den zt) * Tt := by ring
  simp only [CircleMesh.circleIntegrand, zs, zt, Ts, Tt]
  rw [hid]
  calc
    ‖num zs / den zs * (Ts - Tt) +
        (num zs / den zs - num zt / den zt) * Tt‖ ≤
      ‖num zs / den zs * (Ts - Tt)‖ +
        ‖(num zs / den zs - num zt / den zt) * Tt‖ := norm_add_le _ _
    _ = ‖num zs / den zs‖ * ‖Ts - Tt‖ +
        ‖num zs / den zs - num zt / den zt‖ * ‖Tt‖ := by rw [norm_mul, norm_mul]
    _ ≤ (A / m) * (64 * r * |s - t|) +
        ((N / m + A * D / m ^ 2) * (8 * r * |s - t|)) * (8 * r) := by
      exact add_le_add
        (mul_le_mul hqs hTs (norm_nonneg _) (by positivity))
        (mul_le_mul hqdiff hTt (norm_nonneg _) (by positivity))
    _ = 64 * (r * A / m + r ^ 2 * (N / m + A * D / m ^ 2)) * |s - t| := by
      field_simp [ne_of_gt hm]
      ring

private lemma certifiedRadius_value_le_radiusUpper
    (B : ContourBankData) (j : Fin (B.JBase + 1)) :
    (B.rhoName j).value ≤ (radiusUpper B j : ℝ) := by
  exact (le_abs_self (B.rhoName j).value).trans
    (abs_value_le_interval_maxAbs
      ((B.rhoName j).contains ((B.rhoName j).modulus errorOne)))

private lemma winding_circleIntegrand_lipschitz
    (input : RepresentedSpectralInput p) (B : ContourBankData)
    (j : Fin (B.JBase + 1)) (lower : PosRat)
    (hr : 0 ≤ (B.rhoName j).value)
    (hdenLower : ∀ u ∈ Set.Icc (0 : ℝ) 1, (lower.1 : ℝ) ≤
      ‖(spectralDenominatorMap input B (spectralFold p.n 0) 0).value
        (CircleMesh.circleMap 0 (B.rhoName j).value u)‖)
    (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖CircleMesh.circleIntegrand
        (fun z ↦ (spectralDenominatorMap input B (spectralFold p.n 0) 1).value z /
          (spectralDenominatorMap input B (spectralFold p.n 0) 0).value z)
        0 (B.rhoName j).value s -
      CircleMesh.circleIntegrand
        (fun z ↦ (spectralDenominatorMap input B (spectralFold p.n 0) 1).value z /
          (spectralDenominatorMap input B (spectralFold p.n 0) 0).value z)
        0 (B.rhoName j).value t‖ ≤
      (windingLipschitzBound input (radiusUpper B j) lower.1 : ℝ) * |s - t| := by
  let rho := radiusUpper B j
  let A := empiricalFDerivativeBound input rho 1
  let N := empiricalFDerivativeBound input rho 2
  have h := circleIntegrand_quotient_lipschitz
    (num := (spectralDenominatorMap input B (spectralFold p.n 0) 1).value)
    (den := (spectralDenominatorMap input B (spectralFold p.n 0) 0).value)
    hr (certifiedRadius_value_le_radiusUpper B j) (by exact_mod_cast lower.2)
    (by exact_mod_cast empiricalFDerivativeBound_nonneg input rho 1)
    (by exact_mod_cast empiricalFDerivativeBound_nonneg input rho 2)
    (by exact_mod_cast empiricalFDerivativeBound_nonneg input rho 1)
    (fun z hz ↦ spectralDenominatorMap_norm_le input B (spectralFold p.n 0) 1
      (radiusUpper_nonneg B j) hz)
    (fun z hz w hw ↦ spectralDenominatorMap_lipschitzOn_disk input B
      (spectralFold p.n 0) 1 (radiusUpper_nonneg B j) hz hw)
    (fun z hz w hw ↦ spectralDenominatorMap_lipschitzOn_disk input B
      (spectralFold p.n 0) 0 (radiusUpper_nonneg B j) hz hw)
    s t (hdenLower s hs) (hdenLower t ht)
  have hrle := certifiedRadius_value_le_radiusUpper B j
  have hA0 : 0 ≤ (A : ℝ) := by
    exact_mod_cast empiricalFDerivativeBound_nonneg input rho 1
  have hN0 : 0 ≤ (N : ℝ) := by
    exact_mod_cast empiricalFDerivativeBound_nonneg input rho 2
  have hm0 : 0 ≤ (lower.1 : ℝ) := (by exact_mod_cast lower.2.le)
  have hinner : 0 ≤
      (empiricalFDerivativeBound input rho 2 : ℝ) / lower.1 +
        (empiricalFDerivativeBound input rho 1 : ℝ) ^ 2 / lower.1 ^ 2 := by
    exact add_nonneg (div_nonneg hN0 hm0)
      (div_nonneg (sq_nonneg _) (sq_nonneg _))
  have hfirst : (B.rhoName j).value * (A : ℝ) / lower.1 ≤
      (rho : ℝ) * (A : ℝ) / lower.1 :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hrle hA0) hm0
  have hsquare : (B.rhoName j).value ^ 2 ≤ (rho : ℝ) ^ 2 :=
    pow_le_pow_left₀ hr hrle 2
  have hbase : (B.rhoName j).value * (A : ℝ) / lower.1 +
        (B.rhoName j).value ^ 2 *
          ((N : ℝ) / lower.1 + (A : ℝ) ^ 2 / lower.1 ^ 2) ≤
      (rho : ℝ) * (A : ℝ) / lower.1 +
        (rho : ℝ) ^ 2 *
          ((N : ℝ) / lower.1 + (A : ℝ) ^ 2 / lower.1 ^ 2) :=
    add_le_add hfirst (mul_le_mul_of_nonneg_right hsquare hinner)
  calc
    _ ≤ 64 * ((B.rhoName j).value * (A : ℝ) / lower.1 +
        (B.rhoName j).value ^ 2 *
          ((N : ℝ) / lower.1 + (A : ℝ) ^ 2 / lower.1 ^ 2)) * |s - t| := by
            simpa [A, N, pow_two] using h
    _ ≤ 64 * ((rho : ℝ) * (A : ℝ) / lower.1 +
        (rho : ℝ) ^ 2 *
          ((N : ℝ) / lower.1 + (A : ℝ) ^ 2 / lower.1 ^ 2)) * |s - t| := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hbase (by norm_num)) (abs_nonneg _)
    _ = _ := by
      simp only [windingLipschitzBound, rho, A, N]
      push_cast
      ring

private lemma moment_circleIntegrand_lipschitz
    (input : RepresentedSpectralInput p) (B : ContourBankData)
    (j : Fin (B.JBase + 1)) (Ncount : ℕ) (lower : PosRat)
    (hr : 0 ≤ (B.rhoName j).value)
    (hdenLower : ∀ u ∈ Set.Icc (0 : ℝ) 1, (lower.1 : ℝ) ≤
      ‖(spectralDenominatorMap input B (spectralFold p.n 1) 0).value
        (CircleMesh.circleMap 0 (B.rhoName j).value u)‖)
    (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖CircleMesh.circleIntegrand
        (fun z ↦ (spectralNumeratorMap input B (spectralFold p.n 1) 0).value z /
          (spectralDenominatorMap input B (spectralFold p.n 1) 0).value z)
        0 (B.rhoName j).value s -
      CircleMesh.circleIntegrand
        (fun z ↦ (spectralNumeratorMap input B (spectralFold p.n 1) 0).value z /
          (spectralDenominatorMap input B (spectralFold p.n 1) 0).value z)
        0 (B.rhoName j).value t‖ ≤
      (momentLipschitzBound input (radiusUpper B j) lower.1 Ncount : ℝ) * |s - t| := by
  let rho := radiusUpper B j
  let A := empiricalGDerivativeBound input rho 0
  let N := empiricalGDerivativeBound input rho 1
  let D := empiricalFDerivativeBound input rho 1
  have h := circleIntegrand_quotient_lipschitz
    (num := (spectralNumeratorMap input B (spectralFold p.n 1) 0).value)
    (den := (spectralDenominatorMap input B (spectralFold p.n 1) 0).value)
    hr (certifiedRadius_value_le_radiusUpper B j) (by exact_mod_cast lower.2)
    (by exact_mod_cast empiricalGDerivativeBound_nonneg input rho 0)
    (by exact_mod_cast empiricalGDerivativeBound_nonneg input rho 1)
    (by exact_mod_cast empiricalFDerivativeBound_nonneg input rho 1)
    (fun z hz ↦ spectralNumeratorMap_norm_le input B (spectralFold p.n 1) 0
      (radiusUpper_nonneg B j) hz)
    (fun z hz w hw ↦ spectralNumeratorMap_lipschitzOn_disk input B
      (spectralFold p.n 1) 0 (radiusUpper_nonneg B j) hz hw)
    (fun z hz w hw ↦ spectralDenominatorMap_lipschitzOn_disk input B
      (spectralFold p.n 1) 0 (radiusUpper_nonneg B j) hz hw)
    s t (hdenLower s hs) (hdenLower t ht)
  have hrle := certifiedRadius_value_le_radiusUpper B j
  have hA0 : 0 ≤ (A : ℝ) := by
    exact_mod_cast empiricalGDerivativeBound_nonneg input rho 0
  have hN0 : 0 ≤ (N : ℝ) := by
    exact_mod_cast empiricalGDerivativeBound_nonneg input rho 1
  have hD0 : 0 ≤ (D : ℝ) := by
    exact_mod_cast empiricalFDerivativeBound_nonneg input rho 1
  have hm0 : 0 ≤ (lower.1 : ℝ) := (by exact_mod_cast lower.2.le)
  have hinner : 0 ≤ (N : ℝ) / lower.1 + (A : ℝ) * D / lower.1 ^ 2 := by
    exact add_nonneg (div_nonneg hN0 hm0)
      (div_nonneg (mul_nonneg hA0 hD0) (sq_nonneg _))
  have hfirst : (B.rhoName j).value * (A : ℝ) / lower.1 ≤
      (rho : ℝ) * (A : ℝ) / lower.1 :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hrle hA0) hm0
  have hsquare : (B.rhoName j).value ^ 2 ≤ (rho : ℝ) ^ 2 :=
    pow_le_pow_left₀ hr hrle 2
  have hbase : (B.rhoName j).value * (A : ℝ) / lower.1 +
        (B.rhoName j).value ^ 2 *
          ((N : ℝ) / lower.1 + (A : ℝ) * D / lower.1 ^ 2) ≤
      (rho : ℝ) * (A : ℝ) / lower.1 +
        (rho : ℝ) ^ 2 *
          ((N : ℝ) / lower.1 + (A : ℝ) * D / lower.1 ^ 2) :=
    add_le_add hfirst (mul_le_mul_of_nonneg_right hsquare hinner)
  calc
    _ ≤ 64 * ((B.rhoName j).value * (A : ℝ) / lower.1 +
        (B.rhoName j).value ^ 2 *
          ((N : ℝ) / lower.1 + (A : ℝ) * D / lower.1 ^ 2)) * |s - t| := by
            simpa [A, N, D] using h
    _ ≤ 64 * ((rho : ℝ) * (A : ℝ) / lower.1 +
        (rho : ℝ) ^ 2 *
          ((N : ℝ) / lower.1 + (A : ℝ) * D / lower.1 ^ 2)) * |s - t| := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hbase (by norm_num)) (abs_nonneg _)
    _ = _ := by
      simp only [momentLipschitzBound, rho, A, N, D]
      push_cast
      ring

private lemma pilot_denominator_precision_le
    (input : RepresentedSpectralInput p) (B : ContourBankData)
    (a : Fin 2) (j : Fin (B.JBase + 1)) :
    (spectralDenominatorMap input B (spectralFold p.n a) 0).precision
        (spectralNodeTarget (pilotSchedule input B a j).tolerance) ≤
      (pilotSchedule input B a j).fuel := by
  let e := spectralNodeTarget (pilotSchedule input B a j).tolerance
  let Q := empiricalFWidthBound input (spectralFullBoxRadius B) 0
  let L := (128 * max 1 Q) ^ 2
  let operations := spectralNodeOperationCount .pilot (spectralFold p.n a).card
  change spectralEmpiricalMapFuel e (12 * (spectralFold p.n a).card + 8 + 0) L ≤
    (pilotSchedule input B a j).fuel
  calc
    _ ≤ spectralEmpiricalMapFuel e operations (pilotScheduleMagnitude input B j) := by
      apply spectralEmpiricalMapFuel_le_natAmplification
      · dsimp [operations, spectralNodeOperationCount]
        omega
      · dsimp [pilotScheduleMagnitude, L, Q]
        exact le_rfl
    _ ≤ (pilotSchedule input B a j).fuel := by
      exact spectralSchedule_empiricalMapFuel_le
          (estimatorNodePrecision (pilotNodeTolerance B)
            (spectralNodeScale B j (pilotScheduleMagnitude input B j)
              ⟨1, by norm_num⟩ 1 operations))
          operations (pilotCircleLipschitzBound input (radiusUpper B j))
          (pilotScheduleMagnitude input B j)
          (pilotCircleLipschitzBound_nonneg input (radiusUpper_nonneg B j))
          (pilotScheduleMagnitude_nonneg input B j)

private lemma circleNode_width_le_target_of_exact
    (schedule : Schedule) (amplification : ℚ)
    (hexact : ExactSpectralSchedule schedule amplification)
    {k : ℕ} (hk : k ≤ schedule.mesh) :
    (circleNode 1 schedule k).width ≤ (spectralNodeTarget schedule.tolerance).1 := by
  exact circleNode_width_at_selected_precision 1 (by norm_num) schedule
    (spectralNodeTarget schedule.tolerance) hexact.1 hexact.2.1 hk

private lemma circleNode_maxAbs_le_one_add_target
    (schedule : Schedule) (amplification : ℚ)
    (hexact : ExactSpectralSchedule schedule amplification)
    {k : ℕ} (hk : k ≤ schedule.mesh) :
    (circleNode 1 schedule k).maxAbs ≤
      1 + (spectralNodeTarget schedule.tolerance).1 := by
  have hc := circleNode_sound 1 schedule hk
  have hnorm : ‖exactCircleNode 1 schedule k‖ = 1 := by
    simp [exactCircleNode, Complex.norm_exp]
  have hcoords : max |(exactCircleNode 1 schedule k).re|
      |(exactCircleNode 1 schedule k).im| ≤ (1 : ℝ) := by
    rw [← hnorm]
    exact max_le (Complex.abs_re_le_norm _) (Complex.abs_im_le_norm _)
  exact ComplexRatInterval.maxAbs_le_of_contains_width (C := (1 : ℚ)) hc (by
      norm_num
      exact ⟨(le_max_left _ _).trans hcoords, (le_max_right _ _).trans hcoords⟩)
    (circleNode_width_le_target_of_exact schedule amplification hexact hk)

private lemma bankRadiusRect_maxAbs_le_slack
    (B : ContourBankData) (j : Fin (B.JBase + 1)) (precision : PosRat)
    (hprecision : precision.1 ≤ 1) :
    (bankRadiusRect (B.rhoName j) precision).maxAbs ≤ radiusSlackUpper B j := by
  have hc := bankRadiusRect_sound (B.rhoName j) precision
  have habs := abs_value_le_interval_maxAbs
    ((B.rhoName j).contains ((B.rhoName j).modulus errorOne))
  have hcoords : max |(((B.rhoName j).value : ℝ) : ℂ).re|
      |(((B.rhoName j).value : ℝ) : ℂ).im| ≤ (radiusUpper B j : ℝ) := by
    norm_num [max_eq_left (abs_nonneg (B.rhoName j).value)]
    exact habs
  simpa [radiusSlackUpper] using
    ComplexRatInterval.maxAbs_le_of_contains_width hc hcoords
      ((bankRadiusRect_width (B.rhoName j) precision).trans hprecision)

private lemma winding_denominator_precision_le
    (input : RepresentedSpectralInput p) (B : ContourBankData)
    (j : Fin (B.JBase + 1)) (lower : PosRat) :
    let ev := spectralWindingEvaluator input B j lower
    ev.denominator.precision (spectralNodeTarget ev.schedule.tolerance) ≤ ev.mapFuel := by
  let I := spectralFold p.n 0
  let Q0 := empiricalFWidthBound input (spectralFullBoxRadius B) 0
  let Q1 := empiricalFWidthBound input (spectralFullBoxRadius B) 1
  let A0 := ((128 * max 1 Q0) ^ 2).num.natAbs
  let A1 := ((128 * max 1 Q1) ^ 2).num.natAbs
  let operations := spectralNodeOperationCount .winding I.card
  let ev := spectralWindingEvaluator input B j lower
  let e := spectralNodeTarget ev.schedule.tolerance
  change spectralEmpiricalMapFuel e (12 * I.card + 8 + 0)
      ((128 * max 1 Q0) ^ 2) ≤ ev.mapFuel
  calc
    _ ≤ spectralEmpiricalMapFuel e operations (windingScheduleMagnitude input B j lower) := by
      apply spectralEmpiricalMapFuel_le_natAmplification
      · dsimp [operations, spectralNodeOperationCount]
        omega
      · dsimp [windingScheduleMagnitude, A0, A1]
        exact le_max_left _ _
    _ ≤ ev.mapFuel := by
      exact spectralSchedule_empiricalMapFuel_le
          (estimatorNodePrecision (guardedNodeTolerance windingNodeTolerance lower)
            (spectralNodeScale B j (windingScheduleMagnitude input B j lower)
              lower 1 operations))
          operations (windingLipschitzBound input (radiusUpper B j) lower.1)
          (windingScheduleMagnitude input B j lower)
          (windingLipschitzBound_nonneg input (radiusUpper_nonneg B j) lower.2)
          (windingScheduleMagnitude_nonneg input B j lower)

private lemma winding_numerator_precision_le
    (input : RepresentedSpectralInput p) (B : ContourBankData)
    (j : Fin (B.JBase + 1)) (lower : PosRat) :
    let ev := spectralWindingEvaluator input B j lower
    ev.numerator.precision (spectralNodeTarget ev.schedule.tolerance) ≤ ev.mapFuel := by
  let I := spectralFold p.n 0
  let Q0 := empiricalFWidthBound input (spectralFullBoxRadius B) 0
  let Q1 := empiricalFWidthBound input (spectralFullBoxRadius B) 1
  let A0 := ((128 * max 1 Q0) ^ 2).num.natAbs
  let A1 := ((128 * max 1 Q1) ^ 2).num.natAbs
  let operations := spectralNodeOperationCount .winding I.card
  let ev := spectralWindingEvaluator input B j lower
  let e := spectralNodeTarget ev.schedule.tolerance
  change spectralEmpiricalMapFuel e (12 * I.card + 8 + 1)
      ((128 * max 1 Q1) ^ 2) ≤ ev.mapFuel
  calc
    _ ≤ spectralEmpiricalMapFuel e operations (windingScheduleMagnitude input B j lower) := by
      apply spectralEmpiricalMapFuel_le_natAmplification
      · dsimp [operations, spectralNodeOperationCount]
        omega
      · dsimp [windingScheduleMagnitude, A0, A1]
        exact le_max_right _ _
    _ ≤ ev.mapFuel := by
      exact spectralSchedule_empiricalMapFuel_le
          (estimatorNodePrecision (guardedNodeTolerance windingNodeTolerance lower)
            (spectralNodeScale B j (windingScheduleMagnitude input B j lower)
              lower 1 operations))
          operations (windingLipschitzBound input (radiusUpper B j) lower.1)
          (windingScheduleMagnitude input B j lower)
          (windingLipschitzBound_nonneg input (radiusUpper_nonneg B j) lower.2)
          (windingScheduleMagnitude_nonneg input B j lower)

private lemma evaluation_denominator_precision_le
    (input : RepresentedSpectralInput p) (B : ContourBankData)
    (j : Fin (B.JBase + 1)) (Ncount : ℕ) (lower : PosRat) :
    let ev := spectralEvaluationEvaluator input B j Ncount lower
    ev.denominator.precision (spectralNodeTarget ev.schedule.tolerance) ≤ ev.mapFuel := by
  let I := spectralFold p.n 1
  let QF := empiricalFWidthBound input (spectralFullBoxRadius B) 0
  let QG := empiricalGWidthBound input (spectralFullBoxRadius B) 0
  let AF := ((128 * max 1 QF) ^ 2).num.natAbs
  let AG := ((256 * max 1 QG) ^ 2).num.natAbs
  let operations := spectralNodeOperationCount .evaluation I.card
  let ev := spectralEvaluationEvaluator input B j Ncount lower
  let e := spectralNodeTarget ev.schedule.tolerance
  change spectralEmpiricalMapFuel e (12 * I.card + 8 + 0)
      ((128 * max 1 QF) ^ 2) ≤ ev.mapFuel
  calc
    _ ≤ spectralEmpiricalMapFuel e operations
        (evaluationScheduleMagnitude input B j Ncount lower) := by
      apply spectralEmpiricalMapFuel_le_natAmplification
      · dsimp [operations, spectralNodeOperationCount]
        omega
      · dsimp [evaluationScheduleMagnitude, AF, AG]
        exact le_max_left _ _
    _ ≤ ev.mapFuel := by
      exact spectralSchedule_empiricalMapFuel_le
          (estimatorNodePrecision (guardedNodeTolerance (evaluationNodeTolerance p) lower)
            (spectralNodeScale B j (evaluationScheduleMagnitude input B j Ncount lower)
              lower (max Ncount 1) operations))
          operations (momentLipschitzBound input (radiusUpper B j) lower.1 Ncount)
          (evaluationScheduleMagnitude input B j Ncount lower)
          (momentLipschitzBound_nonneg input Ncount (radiusUpper_nonneg B j) lower.2)
          (evaluationScheduleMagnitude_nonneg input B j Ncount lower)

private lemma evaluation_numerator_precision_le
    (input : RepresentedSpectralInput p) (B : ContourBankData)
    (j : Fin (B.JBase + 1)) (Ncount : ℕ) (lower : PosRat) :
    let ev := spectralEvaluationEvaluator input B j Ncount lower
    ev.numerator.precision (spectralNodeTarget ev.schedule.tolerance) ≤ ev.mapFuel := by
  let I := spectralFold p.n 1
  let QF := empiricalFWidthBound input (spectralFullBoxRadius B) 0
  let QG := empiricalGWidthBound input (spectralFullBoxRadius B) 0
  let AF := ((128 * max 1 QF) ^ 2).num.natAbs
  let AG := ((256 * max 1 QG) ^ 2).num.natAbs
  let operations := spectralNodeOperationCount .evaluation I.card
  let ev := spectralEvaluationEvaluator input B j Ncount lower
  let e := spectralNodeTarget ev.schedule.tolerance
  change spectralEmpiricalMapFuel e (14 * I.card + 8 + 0)
      ((256 * max 1 QG) ^ 2) ≤ ev.mapFuel
  calc
    _ ≤ spectralEmpiricalMapFuel e operations
        (evaluationScheduleMagnitude input B j Ncount lower) := by
      apply spectralEmpiricalMapFuel_le_natAmplification
      · dsimp [operations, spectralNodeOperationCount]
        omega
      · dsimp [evaluationScheduleMagnitude, AF, AG]
        exact le_max_right _ _
    _ ≤ ev.mapFuel := by
      exact spectralSchedule_empiricalMapFuel_le
          (estimatorNodePrecision (guardedNodeTolerance (evaluationNodeTolerance p) lower)
            (spectralNodeScale B j (evaluationScheduleMagnitude input B j Ncount lower)
              lower (max Ncount 1) operations))
          operations (momentLipschitzBound input (radiusUpper B j) lower.1 Ncount)
          (evaluationScheduleMagnitude input B j Ncount lower)
          (momentLipschitzBound_nonneg input Ncount (radiusUpper_nonneg B j) lower.2)
          (evaluationScheduleMagnitude_nonneg input B j Ncount lower)

set_option maxHeartbeats 2400000 in
set_option maxRecDepth 4096 in
private lemma empiricalFDerivativeBound_zero_le_widthBound
    (input : RepresentedSpectralInput p) (rho : ℚ) (hrho : 0 ≤ rho) :
    empiricalFDerivativeBound input rho 0 ≤ empiricalFWidthBound input rho 0 := by
  unfold empiricalFDerivativeBound empiricalFWidthBound
  apply Finset.sum_le_sum
  intro i hi
  let E := rationalExpEnvelope rho (residualUpper input i)
  let C := (rho + 1) * (0 + 1) *
    (2 * max 1 (residualUpper input i)) ^ (0 + 1) * E
  have hE : 1 ≤ E := by
    dsimp [E, rationalExpEnvelope]
    exact one_le_pow₀ (by norm_num)
  have hEC : E ≤ C := by
    dsimp [C]
    have hm : 1 ≤ 2 * max 1 (residualUpper input i) := by
      nlinarith [le_max_left (1 : ℚ) (residualUpper input i)]
    have hr1 : 1 ≤ rho + 1 := by linarith
    calc
      E = 1 * E := by ring
      _ ≤ (2 * max 1 (residualUpper input i)) * E :=
        mul_le_mul_of_nonneg_right hm (by linarith)
      _ = 1 * ((2 * max 1 (residualUpper input i)) * E) := by ring
      _ ≤ (rho + 1) * ((2 * max 1 (residualUpper input i)) * E) :=
        mul_le_mul_of_nonneg_right hr1 (by positivity)
      _ = (rho + 1) * (0 + 1) *
          (2 * max 1 (residualUpper input i)) ^ (0 + 1) * E := by
        norm_num
        ring
  have hC : 1 ≤ C := hE.trans hEC
  simpa [E, C] using hEC.trans (le_self_pow₀ hC (by norm_num : 8 ≠ 0))

private lemma empiricalFDerivativeBound_one_le_widthBound
    (input : RepresentedSpectralInput p) (rho : ℚ) (hrho : 0 ≤ rho) :
    empiricalFDerivativeBound input rho 1 ≤ empiricalFWidthBound input rho 1 := by
  unfold empiricalFDerivativeBound empiricalFWidthBound
  apply Finset.sum_le_sum
  intro i hi
  let U := residualUpper input i
  let E := rationalExpEnvelope rho U
  let C := (rho + 1) * (1 + 1) * (2 * max 1 U) ^ (1 + 1) * E
  have hU : 0 ≤ U := residualUpper_nonneg input i
  have hE : 1 ≤ E := by
    dsimp [E, rationalExpEnvelope]
    exact one_le_pow₀ (by norm_num)
  have hbase : 1 ≤ 2 * max 1 U := by
    nlinarith [le_max_left (1 : ℚ) U]
  have hUC : U * E ≤ C := by
    dsimp [C]
    have hUmax : U ≤ max 1 U := le_max_right _ _
    have hpow : max 1 U ≤ (2 * max 1 U) ^ 2 := by
      have hm : 1 ≤ 2 * max 1 U := hbase
      nlinarith [le_self_pow₀ hm (by norm_num : 2 ≠ 0)]
    have hr1 : 1 ≤ rho + 1 := by linarith
    have hnonneg : 0 ≤ E := zero_le_one.trans hE
    calc
      U * E ≤ max 1 U * E := mul_le_mul_of_nonneg_right hUmax hnonneg
      _ ≤ (2 * max 1 U) ^ 2 * E := mul_le_mul_of_nonneg_right hpow hnonneg
      _ ≤ (rho + 1) * 2 * (2 * max 1 U) ^ 2 * E := by
        have hf : 1 ≤ (rho + 1) * 2 := by nlinarith
        have hprod : 0 ≤ (2 * max 1 U) ^ 2 * E :=
          mul_nonneg (sq_nonneg (2 * max 1 U)) hnonneg
        simpa only [one_mul, mul_assoc] using
          mul_le_mul_of_nonneg_right hf hprod
      _ = C := by ring
  have hC : 1 ≤ C := by
    dsimp [C]
    have hnonneg : 0 ≤ E := zero_le_one.trans hE
    have hp : 1 ≤ (2 * max 1 U) ^ 2 := one_le_pow₀ hbase
    nlinarith [mul_le_mul_of_nonneg_right hp hnonneg]
  simpa [U, E, C] using hUC.trans (le_self_pow₀ hC (by norm_num : 8 ≠ 0))

private lemma empiricalGDerivativeBound_zero_le_widthBound
    (input : RepresentedSpectralInput p) (rho : ℚ) (hrho : 0 ≤ rho) :
    empiricalGDerivativeBound input rho 0 ≤ empiricalGWidthBound input rho 0 := by
  unfold empiricalGDerivativeBound empiricalGWidthBound
  apply Finset.sum_le_sum
  intro i hi
  let Y := outcomeUpper input i
  let E := rationalExpEnvelope rho (residualUpper input i)
  let C := max 1 Y * (rho + 1) * (0 + 1) *
    (2 * max 1 (residualUpper input i)) ^ (0 + 1) * E
  have hY : 0 ≤ Y := outcomeUpper_nonneg input i
  have hE : 1 ≤ E := by
    dsimp [E, rationalExpEnvelope]
    exact one_le_pow₀ (by norm_num)
  have hYC : Y * E ≤ C := by
    dsimp [C]
    have hymax : Y ≤ max 1 Y := le_max_right _ _
    have hr1 : 1 ≤ rho + 1 := by linarith
    have hm : 1 ≤ 2 * max 1 (residualUpper input i) := by
      nlinarith [le_max_left (1 : ℚ) (residualUpper input i)]
    have hnonneg : 0 ≤ E := zero_le_one.trans hE
    have hy0 : 0 ≤ max 1 Y := zero_le_one.trans (le_max_left _ _)
    have hm0 : 0 ≤ 2 * max 1 (residualUpper input i) := zero_le_one.trans hm
    calc
      Y * E ≤ max 1 Y * E := mul_le_mul_of_nonneg_right hymax hnonneg
      _ ≤ max 1 Y * (2 * max 1 (residualUpper input i)) * E := by
        exact mul_le_mul_of_nonneg_right
          (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hm hy0) hnonneg
      _ ≤ max 1 Y * (rho + 1) *
          (2 * max 1 (residualUpper input i)) * E := by
        have hleft : max 1 Y * (2 * max 1 (residualUpper input i)) ≤
            max 1 Y * (rho + 1) * (2 * max 1 (residualUpper input i)) := by
          calc
            max 1 Y * (2 * max 1 (residualUpper input i)) =
                max 1 Y * 1 * (2 * max 1 (residualUpper input i)) := by ring
            _ ≤ max 1 Y * (rho + 1) *
                (2 * max 1 (residualUpper input i)) := by gcongr
        exact mul_le_mul_of_nonneg_right hleft hnonneg
      _ = C := by norm_num; ring
  have hC : 1 ≤ C := by
    dsimp [C]
    have hy1 : 1 ≤ max 1 Y := le_max_left _ _
    have hr1 : 1 ≤ rho + 1 := by linarith
    have hm : 1 ≤ 2 * max 1 (residualUpper input i) := by
      nlinarith [le_max_left (1 : ℚ) (residualUpper input i)]
    have h1 : 1 ≤ max 1 Y * (rho + 1) :=
      one_le_mul_of_one_le_of_one_le hy1 hr1
    have h2 : 1 ≤ max 1 Y * (rho + 1) *
        (2 * max 1 (residualUpper input i)) :=
      one_le_mul_of_one_le_of_one_le h1 hm
    simpa only [zero_add, zero_mul, one_mul, mul_one, pow_one] using
      one_le_mul_of_one_le_of_one_le h2 hE
  simpa [Y, E, C] using hYC.trans (le_self_pow₀ hC (by norm_num : 8 ≠ 0))

private lemma rat_le_num_natAbs {q : ℚ} (hq : 0 ≤ q) :
    q ≤ (q.num.natAbs : ℕ) := by
  have hnum0 : 0 ≤ q.num := Rat.num_nonneg.mpr hq
  calc
    q = (q.num : ℚ) / (q.den : ℕ) := (Rat.num_div_den q).symm
    _ ≤ (q.num : ℚ) := div_le_self (by exact_mod_cast hnum0)
      (by exact_mod_cast Rat.den_pos q)
    _ = (q.num.natAbs : ℕ) := by
      have hi : (q.num.natAbs : ℤ) = q.num := Int.natAbs_of_nonneg hnum0
      exact (congrArg (fun x : ℤ => (x : ℚ)) hi).symm

private lemma pilot_widthBound_le_scheduleMagnitude
    (input : RepresentedSpectralInput p) (B : ContourBankData)
    (j : Fin (B.JBase + 1)) :
    empiricalFWidthBound input (spectralFullBoxRadius B) 0 ≤
      pilotScheduleMagnitude input B j := by
  let Q := empiricalFWidthBound input (spectralFullBoxRadius B) 0
  let A := (128 * max 1 Q) ^ 2
  have hQ : 0 ≤ Q := empiricalFWidthBound_nonneg input _ 0
    (spectralFullBoxRadius_nonneg B)
  have hQA : Q ≤ A := by
    have hm : Q ≤ max 1 Q := le_max_right _ _
    have hbase : 1 ≤ 128 * max 1 Q := by
      nlinarith [le_max_left (1 : ℚ) Q]
    dsimp [A]
    exact hm.trans ((by nlinarith : max 1 Q ≤ 128 * max 1 Q).trans
      (le_self_pow₀ hbase (by norm_num)))
  exact hQA.trans (by
    dsimp [pilotScheduleMagnitude, Q, A]
    exact rat_le_num_natAbs (by positivity))

private lemma winding_denominator_widthBound_le_scheduleMagnitude
    (input : RepresentedSpectralInput p) (B : ContourBankData)
    (j : Fin (B.JBase + 1)) (lower : PosRat) :
    empiricalFWidthBound input (spectralFullBoxRadius B) 0 ≤
      windingScheduleMagnitude input B j lower := by
  let Q := empiricalFWidthBound input (spectralFullBoxRadius B) 0
  let C := (128 * max 1 Q) ^ 2
  have hQ : 0 ≤ Q := empiricalFWidthBound_nonneg input _ 0
    (spectralFullBoxRadius_nonneg B)
  have hQC : Q ≤ C := by
    have hm : Q ≤ max 1 Q := le_max_right _ _
    have hb : 1 ≤ 128 * max 1 Q := by
      nlinarith [le_max_left (1 : ℚ) Q]
    exact hm.trans ((by nlinarith : max 1 Q ≤ 128 * max 1 Q).trans
      (le_self_pow₀ hb (by norm_num)))
  calc
    Q ≤ C := hQC
    _ ≤ (C.num.natAbs : ℕ) := rat_le_num_natAbs (by positivity)
    _ ≤ windingScheduleMagnitude input B j lower := by
      let A0 : ℕ :=
        ((128 * max 1 (empiricalFWidthBound input (spectralFullBoxRadius B) 0)).num ^
          (2 : ℕ)).natAbs
      let A1 : ℕ :=
        ((128 * max 1 (empiricalFWidthBound input (spectralFullBoxRadius B) 1)).num ^
          (2 : ℕ)).natAbs
      change (A0 : ℚ) ≤ (max A0 A1 : ℕ)
      exact_mod_cast (le_max_left A0 A1)

private lemma evaluation_denominator_widthBound_le_scheduleMagnitude
    (input : RepresentedSpectralInput p) (B : ContourBankData)
    (j : Fin (B.JBase + 1)) (N : ℕ) (lower : PosRat) :
    empiricalFWidthBound input (spectralFullBoxRadius B) 0 ≤
      evaluationScheduleMagnitude input B j N lower := by
  let Q := empiricalFWidthBound input (spectralFullBoxRadius B) 0
  let C := (128 * max 1 Q) ^ 2
  have hQ : 0 ≤ Q := empiricalFWidthBound_nonneg input _ 0
    (spectralFullBoxRadius_nonneg B)
  have hQC : Q ≤ C := by
    have hm : Q ≤ max 1 Q := le_max_right _ _
    have hb : 1 ≤ 128 * max 1 Q := by
      nlinarith [le_max_left (1 : ℚ) Q]
    exact hm.trans ((by nlinarith : max 1 Q ≤ 128 * max 1 Q).trans
      (le_self_pow₀ hb (by norm_num)))
  calc
    Q ≤ C := hQC
    _ ≤ (C.num.natAbs : ℕ) := rat_le_num_natAbs (by positivity)
    _ ≤ evaluationScheduleMagnitude input B j N lower := by
      let A0 : ℕ :=
        ((128 * max 1 (empiricalFWidthBound input (spectralFullBoxRadius B) 0)).num ^
          (2 : ℕ)).natAbs
      let A1 : ℕ :=
        ((256 * max 1 (empiricalGWidthBound input (spectralFullBoxRadius B) 0)).num ^
          (2 : ℕ)).natAbs
      change (A0 : ℚ) ≤ (max A0 A1 : ℕ)
      exact_mod_cast (le_max_left A0 A1)

private lemma spectralNodeScale_core_le
    (B : ContourBankData) (j : Fin (B.JBase + 1))
    (amplification : ℚ) (lower : PosRat) (count operations : ℕ) :
    64 * (1 + max 0 (radiusSlackUpper B j)) *
        (1 + max 0 amplification) ^ 2 ≤
      spectralNodeScale B j amplification lower count operations := by
  unfold spectralNodeScale
  apply le_max_of_le_right
  have hop : (1 : ℚ) ≤ operations + 1 := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
  have hinv : 0 ≤ lower.1⁻¹ := inv_nonneg.mpr lower.2.le
  have hlower : 1 ≤ 1 + lower.1⁻¹ + lower.1⁻¹ ^ 2 := by
    nlinarith [sq_nonneg lower.1⁻¹]
  have hnorm : 1 ≤ spectralNormalizationAmplification count := by
    unfold spectralNormalizationAmplification
    dsimp only
    have hc : (0 : ℚ) ≤ max (count : ℚ) 1 :=
      le_max_of_le_right (by norm_num)
    have hmax : 0 ≤ (boundedContourDivisor count 0).maxAbs :=
      (abs_nonneg _).trans ((le_max_left _ _).trans (le_max_left _ _))
    have hinv' : 0 ≤ |(boundedContourDivisor count 0).normSq.lo|⁻¹ :=
      inv_nonneg.mpr (abs_nonneg _)
    nlinarith [sq_nonneg |(boundedContourDivisor count 0).normSq.lo|⁻¹]
  have hbase : 0 ≤ 64 * (1 + max 0 (radiusSlackUpper B j)) *
      (1 + max 0 amplification) ^ 2 := by positivity
  have hfac : 0 ≤ (1 + max 0 (radiusSlackUpper B j)) *
      (1 + max 0 amplification) ^ 2 := by positivity
  have hup := mul_le_mul_of_nonneg_right (show (64 : ℚ) ≤ 256 by norm_num) hfac
  calc
    _ ≤ 256 * ((1 + max 0 (radiusSlackUpper B j)) *
        (1 + max 0 amplification) ^ 2) := by simpa [mul_assoc] using hup
    _ = 1 * (256 * (1 + max 0 (radiusSlackUpper B j)) *
        (1 + max 0 amplification) ^ 2) * 1 * 1 := by ring
    _ ≤ (operations + 1) * (256 * (1 + max 0 (radiusSlackUpper B j)) *
        (1 + max 0 amplification) ^ 2) * 1 * 1 := by gcongr
    _ ≤ (operations + 1) * (256 * (1 + max 0 (radiusSlackUpper B j)) *
        (1 + max 0 amplification) ^ 2) *
          (1 + lower.1⁻¹ + lower.1⁻¹ ^ 2) *
            spectralNormalizationAmplification count := by
      gcongr
    _ = 256 * (operations + 1) * (1 + max 0 (radiusSlackUpper B j)) *
        (1 + max 0 amplification) ^ 2 *
          (1 + lower.1⁻¹ + lower.1⁻¹ ^ 2) *
            spectralNormalizationAmplification count := by ring

set_option maxHeartbeats 800000 in
-- Clearing the conservative rational products is nonlinear-arithmetic heavy.
private lemma quadratic_node_map_width_budget
    {r R Q A S t e rp nw w : ℚ}
    (hr0 : 0 < r) (hr1 : r ≤ 1) (hR : 0 ≤ R) (hQ : 0 ≤ Q)
    (hA : 0 ≤ A) (hQA : Q ≤ A)
    (hcore : 64 * (1 + R) * (1 + A) ^ 2 ≤ S)
    (ht0 : 0 ≤ t) (he0 : 0 ≤ e) (hrp0 : 0 ≤ rp) (hnw0 : 0 ≤ nw)
    (ht : 64 * S * t = r ^ 2) (he : 16 * e = t ^ 2)
    (hrp : (1 + e) * rp ≤ t / 4)
    (hnw : nw ≤ 2 * (R * e + (1 + e) * rp))
    (hw : w ≤ 128 * Q * nw + e) :
    w ≤ r ^ 2 / (32 * (A + 1)) := by
  have hAp : 0 < A + 1 := by linarith
  have hfacA : 1 ≤ (1 + A) ^ 2 := by nlinarith [sq_nonneg A]
  have hfacR : 1 ≤ 1 + R := by linarith
  have hS64 : 64 ≤ S := by
    calc
      64 ≤ 64 * (1 + R) * (1 + A) ^ 2 := by nlinarith
      _ ≤ S := hcore
  have hSt : 64 * t ≤ S * t :=
    mul_le_mul_of_nonneg_right hS64 ht0
  have hrSq : r ^ 2 ≤ 1 := by nlinarith [sq_nonneg r, sq_nonneg (1 - r)]
  have ht1 : t ≤ 1 := by nlinarith [ht]
  have htSq : t ^ 2 ≤ t := by nlinarith [sq_nonneg t, sq_nonneg (1 - t)]
  have he_le : e ≤ t / 16 := by nlinarith [he]
  have hSR : R ≤ S := by
    have hRA : R ≤ 64 * (1 + R) * (1 + A) ^ 2 := by nlinarith
    exact hRA.trans hcore
  have hRt : R * t ≤ S * t := mul_le_mul_of_nonneg_right hSR ht0
  have hRt1 : R * t ≤ 1 := by nlinarith [ht, hrSq]
  have hRe : R * e ≤ t / 16 := by
    have hmul := mul_le_mul_of_nonneg_left he_le hR
    have hprod : R * t ^ 2 ≤ t := by
      nlinarith [mul_le_mul_of_nonneg_right hRt1 ht0]
    nlinarith
  have hnwt : nw ≤ t := by nlinarith [hnw, hrp, hRe]
  have het : e ≤ t := by linarith
  have hwt : w ≤ (128 * Q + 1) * t := by
    have hmul : 128 * Q * nw ≤ 128 * Q * t :=
      mul_le_mul_of_nonneg_left hnwt (mul_nonneg (by norm_num) hQ)
    nlinarith [hw]
  have hSA : 64 * (1 + A) ^ 2 ≤ S := by
    have hmul : 64 * (1 + A) ^ 2 ≤
        (1 + R) * (64 * (1 + A) ^ 2) :=
      by simpa only [one_mul] using (mul_le_mul_of_nonneg_right hfacR
        (by positivity : (0 : ℚ) ≤ 64 * (1 + A) ^ 2))
    nlinarith [hcore]
  have hcoeff : (128 * Q + 1) * (A + 1) ≤ 2 * S := by
    have hqcoeff : 128 * Q + 1 ≤ 128 * (A + 1) := by nlinarith
    have hmul := mul_le_mul_of_nonneg_right hqcoeff hAp.le
    nlinarith [hSA, sq_nonneg (A + 1)]
  have hfinal : 32 * (A + 1) * w ≤ r ^ 2 := by
    have hmulw : 32 * (A + 1) * w ≤
        32 * (A + 1) * ((128 * Q + 1) * t) :=
      mul_le_mul_of_nonneg_left hwt (mul_nonneg (by norm_num) hAp.le)
    have hmult : ((128 * Q + 1) * (A + 1)) * t ≤ (2 * S) * t :=
      mul_le_mul_of_nonneg_right hcoeff ht0
    calc
      32 * (A + 1) * w ≤
          32 * (A + 1) * ((128 * Q + 1) * t) := hmulw
      _ = 32 * (((128 * Q + 1) * (A + 1)) * t) := by ring
      _ ≤ 32 * ((2 * S) * t) := mul_le_mul_of_nonneg_left hmult (by norm_num)
      _ = 64 * S * t := by ring
      _ = r ^ 2 := ht
  apply (le_div_iff₀ (mul_pos (by norm_num) hAp)).2
  simpa [mul_assoc, mul_comm, mul_left_comm] using hfinal

private lemma quadratic_node_width_le_tolerance
    {r R A S t e rp nw : ℚ}
    (hr0 : 0 < r) (hr1 : r ≤ 1) (hR : 0 ≤ R) (hA : 0 ≤ A)
    (hcore : 64 * (1 + R) * (1 + A) ^ 2 ≤ S)
    (ht0 : 0 ≤ t) (hrp0 : 0 ≤ rp)
    (ht : 64 * S * t = r ^ 2) (he : 16 * e = t ^ 2)
    (hrp : (1 + e) * rp ≤ t / 4)
    (hnw : nw ≤ 2 * (R * e + (1 + e) * rp)) : nw ≤ t := by
  have hS64 : 64 ≤ S := by
    calc
      64 ≤ 64 * (1 + R) * (1 + A) ^ 2 := by
        nlinarith [sq_nonneg A]
      _ ≤ S := hcore
  have hSt : 64 * t ≤ S * t := mul_le_mul_of_nonneg_right hS64 ht0
  have hrSq : r ^ 2 ≤ 1 := by nlinarith [sq_nonneg r, sq_nonneg (1 - r)]
  have ht1 : t ≤ 1 := by nlinarith [ht]
  have htSq : t ^ 2 ≤ t := by nlinarith [sq_nonneg t, sq_nonneg (1 - t)]
  have he_le : e ≤ t / 16 := by nlinarith [he]
  have hSR : R ≤ S := by
    have hfacA : 1 ≤ (1 + A) ^ 2 := by nlinarith [sq_nonneg A]
    have hRA : R ≤ 64 * (1 + R) * (1 + A) ^ 2 := by nlinarith
    exact hRA.trans hcore
  have hRt : R * t ≤ S * t := mul_le_mul_of_nonneg_right hSR ht0
  have hRt1 : R * t ≤ 1 := by nlinarith [ht, hrSq]
  have hRe : R * e ≤ t / 16 := by
    have hmul := mul_le_mul_of_nonneg_left he_le hR
    have hprod : R * t ^ 2 ≤ t := by
      nlinarith [mul_le_mul_of_nonneg_right hRt1 ht0]
    nlinarith
  nlinarith [hnw, hrp, hRe]

private lemma quadratic_node_width_le_one
    {r R A S t e rp nw : ℚ}
    (hr0 : 0 < r) (hr1 : r ≤ 1) (hR : 0 ≤ R) (hA : 0 ≤ A)
    (hcore : 64 * (1 + R) * (1 + A) ^ 2 ≤ S)
    (ht0 : 0 ≤ t) (hrp0 : 0 ≤ rp)
    (ht : 64 * S * t = r ^ 2) (he : 16 * e = t ^ 2)
    (hrp : (1 + e) * rp ≤ t / 4)
    (hnw : nw ≤ 2 * (R * e + (1 + e) * rp)) : nw ≤ 1 := by
  have hnwt := quadratic_node_width_le_tolerance hr0 hr1 hR hA hcore ht0 hrp0
    ht he hrp hnw
  have hS64 : 64 ≤ S := by
    calc
      64 ≤ 64 * (1 + R) * (1 + A) ^ 2 := by
        nlinarith [sq_nonneg A]
      _ ≤ S := hcore
  have hSt : 64 * t ≤ S * t := mul_le_mul_of_nonneg_right hS64 ht0
  have hrSq : r ^ 2 ≤ 1 := by nlinarith [sq_nonneg r, sq_nonneg (1 - r)]
  have ht1 : t ≤ 1 := by nlinarith [ht]
  exact hnwt.trans ht1

private lemma estimatorNodePrecision_scale_eq (requested : PosRat) (scale : ℚ)
    (hscale : 1 ≤ scale) :
    64 * scale * (estimatorNodePrecision requested scale).1 = requested.1 ^ 2 := by
  unfold estimatorNodePrecision
  change 64 * scale * (requested.1 ^ 2 / (64 * max 1 scale)) = requested.1 ^ 2
  rw [max_eq_right hscale]
  field_simp [ne_of_gt (lt_of_lt_of_le zero_lt_one hscale)]

private lemma contourBank_UR_le_spectralFullBoxRadius (B : ContourBankData) :
    (B.UR : ℚ) ≤ spectralFullBoxRadius B := by
  have hU : (0 : ℚ) ≤ (B.UR : ℚ) + 2 := by positivity
  dsimp [spectralFullBoxRadius, spectralDiskBox,
    ComplexRatInterval.maxAbs, RatInterval.maxAbs]
  rw [abs_of_nonpos (neg_nonpos.mpr hU), abs_of_nonneg hU]
  norm_num
  linarith

private lemma spectralSchedule_rawNormFuel_nat_succ
    (tolerance : PosRat) (operations : ℕ) (L : ℚ) (n : ℕ)
    (hL : 0 ≤ L) :
    64 * ((spectralSchedule tolerance operations L (n : ℚ) hL (by positivity)).tolerance.1.den + 1) *
      ((((n : ℚ) + 1).num.natAbs + 2) ^ 2) ≤
      (spectralSchedule tolerance operations L (n : ℚ) hL (by positivity)).fuel := by
  change 64 * (tolerance.1.den + 1) *
      ((((n : ℚ) + 1).num.natAbs + 2) ^ 2) ≤
    (spectralSchedule tolerance operations L (n : ℚ) hL (by positivity)).fuel
  have hnum : ((n : ℚ) + 1).num.natAbs = n + 1 := by
    rw [show (n : ℚ) + 1 = ((n + 1 : ℕ) : ℚ) by norm_num]
    simp only [Rat.num_natCast]
    rfl
  rw [hnum]
  norm_num
  exact spectralSchedule_rawNormFuel_le tolerance operations L (n : ℚ) hL (by positivity)

private lemma scheduledRadiusNode_data
    (B : ContourBankData) (j : Fin (B.JBase + 1))
    (requested lower : PosRat) (count operations : ℕ) (L A : ℚ)
    (hL : 0 ≤ L) (hA : 0 ≤ A) (hrequested : requested.1 ≤ 1)
    (hrho : 0 < B.rho j ∧ B.rho j ≤ B.UR) :
    let S := spectralNodeScale B j A lower count operations
    let tolerance := estimatorNodePrecision requested S
    let schedule := spectralSchedule tolerance operations L A hL hA
    let e := spectralNodeTarget tolerance
    let radiusPrecision := bankRadiusPrecision tolerance e.1
    ∀ k ≤ schedule.mesh,
      (certifiedRadiusNode (B.rhoName j) radiusPrecision schedule k).Contains
        (CircleMesh.circleMap 0 (B.rho j)
          (CircleMesh.meshPoint schedule.mesh k)) ∧
      (certifiedRadiusNode (B.rhoName j) radiusPrecision schedule k).Subinterval
        (spectralDiskBox B) ∧
      (bankRadiusRect (B.rhoName j) radiusPrecision).maxAbs ≤ radiusSlackUpper B j ∧
      (certifiedRadiusNode (B.rhoName j) radiusPrecision schedule k).width ≤
        2 * (radiusSlackUpper B j * e.1 +
          (1 + e.1) * radiusPrecision.1) ∧
      (certifiedRadiusNode (B.rhoName j) radiusPrecision schedule k).width ≤
        schedule.tolerance.1 := by
  dsimp only
  intro k hk
  let S := spectralNodeScale B j A lower count operations
  let tolerance := estimatorNodePrecision requested S
  let schedule := spectralSchedule tolerance operations L A hL hA
  let e := spectralNodeTarget tolerance
  let radiusPrecision := bankRadiusPrecision tolerance e.1
  have hexact : ExactSpectralSchedule schedule A := by
    dsimp [schedule]
    exact exactSpectralSchedule_spectralSchedule _ _ _ _ _ _
  have hsound : (certifiedRadiusNode (B.rhoName j) radiusPrecision schedule k).Contains
      (CircleMesh.circleMap 0 (B.rho j) (CircleMesh.meshPoint schedule.mesh k)) := by
    simpa only [B.rho_value] using
      certifiedRadiusNode_sound (B.rhoName j) radiusPrecision schedule hk
  have hcircleWidth := circleNode_width_le_target_of_exact schedule A hexact hk
  have hcircleMax := circleNode_maxAbs_le_one_add_target schedule A hexact hk
  have hrp1 : radiusPrecision.1 ≤ 1 := min_le_left _ _
  have hbank := bankRadiusRect_maxAbs_le_slack B j radiusPrecision hrp1
  have hnodeWidth : (certifiedRadiusNode (B.rhoName j) radiusPrecision schedule k).width ≤
      2 * (radiusSlackUpper B j * e.1 +
        (1 + e.1) * radiusPrecision.1) :=
    certifiedRadiusNode_width (B.rhoName j) radiusPrecision schedule
      (radiusSlackUpper B j) e.1 hk hbank hcircleWidth hcircleMax
  let r := requested.1
  let R := radiusSlackUpper B j
  let t := schedule.tolerance.1
  have hR0 : 0 ≤ R := by
    dsimp [R, radiusSlackUpper]
    linarith [radiusUpper_nonneg B j]
  have hcore : 64 * (1 + R) * (1 + A) ^ 2 ≤ S := by
    simpa [R, S, max_eq_right hR0, max_eq_right hA] using
      spectralNodeScale_core_le B j A lower count operations
  have htEq : 64 * S * t = r ^ 2 := by
    have hS1 : 1 ≤ S := by
      dsimp [S, spectralNodeScale]
      exact le_max_left _ _
    change 64 * S * tolerance.1 = requested.1 ^ 2
    exact estimatorNodePrecision_scale_eq requested S hS1
  have heEq : 16 * e.1 = t ^ 2 := by
    change 16 * (spectralNodeTarget tolerance).1 = tolerance.1 ^ 2
    dsimp [spectralNodeTarget]
    ring
  have hrpBudget : (1 + e.1) * radiusPrecision.1 ≤ t / 4 := by
    have he0 : 0 ≤ e.1 := e.2.le
    have hp := min_le_right (1 : ℚ)
      (schedule.tolerance.1 / (4 * (1 + max 0 e.1)))
    change radiusPrecision.1 ≤ schedule.tolerance.1 /
      (4 * (1 + max 0 e.1)) at hp
    rw [max_eq_right he0] at hp
    calc
      (1 + e.1) * radiusPrecision.1 ≤
          (1 + e.1) * (t / (4 * (1 + e.1))) := by
        simpa [t] using mul_le_mul_of_nonneg_left hp (by linarith)
      _ = t / 4 := by field_simp [ne_of_gt (by linarith [e.2] : 0 < 1 + e.1)]
  have hnodeSmall :
      (certifiedRadiusNode (B.rhoName j) radiusPrecision schedule k).width ≤ 1 := by
    apply quadratic_node_width_le_one (r := r) (R := R) (A := A) (S := S)
      (t := t) (e := e.1) (rp := radiusPrecision.1)
    · exact requested.2
    · exact hrequested
    · exact hR0
    · exact hA
    · exact hcore
    · exact schedule.tolerance.2.le
    · exact radiusPrecision.2.le
    · exact htEq
    · exact heEq
    · exact hrpBudget
    · simpa [R, e, radiusPrecision] using hnodeWidth
  have hbox : (certifiedRadiusNode (B.rhoName j) radiusPrecision schedule k).Subinterval
      (spectralDiskBox B) := by
    let z := CircleMesh.circleMap 0 (B.rho j)
      (CircleMesh.meshPoint schedule.mesh k)
    have hnorm : ‖z‖ = B.rho j := by
      simp [z, CircleMesh.circleMap, Complex.norm_exp, abs_of_pos hrho.1]
    have hre : |z.re| ≤ (B.UR : ℝ) := by
      calc
        |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
        _ = B.rho j := hnorm
        _ ≤ B.UR := hrho.2
    have him : |z.im| ≤ (B.UR : ℝ) := by
      calc
        |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
        _ = B.rho j := hnorm
        _ ≤ B.UR := hrho.2
    convert rectangle_subinterval_symmetric_of_contains_width
      _ z B.UR hsound hre him (hnodeSmall.trans (by norm_num)) using 1 <;>
      simp [spectralDiskBox] <;> ring
  have hnodeTolerance :
      (certifiedRadiusNode (B.rhoName j) radiusPrecision schedule k).width ≤ t := by
    apply quadratic_node_width_le_tolerance (r := r) (R := R) (A := A) (S := S)
      (t := t) (e := e.1) (rp := radiusPrecision.1)
    · exact requested.2
    · exact hrequested
    · exact hR0
    · exact hA
    · exact hcore
    · exact schedule.tolerance.2.le
    · exact radiusPrecision.2.le
    · exact htEq
    · exact heEq
    · exact hrpBudget
    · simpa [R, e, radiusPrecision] using hnodeWidth
  exact ⟨hsound, hbox, hbank, hnodeWidth, by simpa [t] using hnodeTolerance⟩

private lemma scheduledDenominatorNode_data
    (input : RepresentedSpectralInput p) (B : ContourBankData)
    (I : Finset (Fin p.n)) (j : Fin (B.JBase + 1))
    (requested lower : PosRat) (count operations : ℕ) (L A : ℚ)
    (hL : 0 ≤ L) (hA : 0 ≤ A) (hrequested : requested.1 ≤ 1)
    (hrho : 0 < B.rho j ∧ B.rho j ≤ B.UR)
    (hcanonical : CanonicalRepresentedSpectralInput Xspace input)
    (hQA : empiricalFWidthBound input (spectralFullBoxRadius B) 0 ≤ A)
    (hAnat : ∃ n : ℕ, A = n)
    (hprecision :
      let S := spectralNodeScale B j A lower count operations
      let tolerance := estimatorNodePrecision requested S
      let schedule := spectralSchedule tolerance operations L A hL hA
      (spectralDenominatorMap input B I 0).precision
        (spectralNodeTarget schedule.tolerance) ≤ schedule.fuel) :
    let S := spectralNodeScale B j A lower count operations
    let tolerance := estimatorNodePrecision requested S
    let schedule := spectralSchedule tolerance operations L A hL hA
    let e := spectralNodeTarget tolerance
    let radiusPrecision := bankRadiusPrecision tolerance e.1
    let map := spectralDenominatorMap input B I 0
    ∀ k ≤ schedule.mesh,
      (certifiedRadiusNode (B.rhoName j) radiusPrecision schedule k).Contains
        (CircleMesh.circleMap 0 (B.rho j)
          (CircleMesh.meshPoint schedule.mesh k)) ∧
      (certifiedRadiusNode (B.rhoName j) radiusPrecision schedule k).Subinterval
        (spectralDiskBox B) ∧
      (map.eval (certifiedRadiusNode (B.rhoName j) radiusPrecision schedule k)
        schedule.fuel).width ≤ map.derivativeEnvelope *
          (certifiedRadiusNode (B.rhoName j) radiusPrecision schedule k).width + e.1 ∧
      ((map.eval (certifiedRadiusNode (B.rhoName j) radiusPrecision schedule k)
        schedule.fuel).normInterval schedule.fuel).width ≤ requested.1 := by
  dsimp only
  intro k hk
  let S := spectralNodeScale B j A lower count operations
  let tolerance := estimatorNodePrecision requested S
  let schedule := spectralSchedule tolerance operations L A hL hA
  let e := spectralNodeTarget tolerance
  let radiusPrecision := bankRadiusPrecision tolerance e.1
  let map := spectralDenominatorMap input B I 0
  let node := certifiedRadiusNode (B.rhoName j) radiusPrecision schedule k
  have hgeom := scheduledRadiusNode_data B j requested lower count operations L A
    hL hA hrequested hrho k hk
  have hsound : node.Contains (CircleMesh.circleMap 0 (B.rho j)
      (CircleMesh.meshPoint schedule.mesh k)) := by simpa [node, schedule, radiusPrecision] using hgeom.1
  have hbox : node.Subinterval (spectralDiskBox B) := by
    simpa [node, schedule, radiusPrecision] using hgeom.2.1
  have hnodeWidth : node.width ≤ 2 * (radiusSlackUpper B j * e.1 +
      (1 + e.1) * radiusPrecision.1) := by
    simpa [node, schedule, radiusPrecision, e] using hgeom.2.2.2.1
  have hvalid := spectralDenominatorMap_valid_of_canonical input B I 0 hcanonical
  have hmapWidth : (map.eval node schedule.fuel).width ≤
      map.derivativeEnvelope * node.width + e.1 :=
    boundedComplexMap_eval_width_of_precision_le map hvalid hbox hsound e
      schedule.fuel (by exact hprecision)
  let Q := empiricalFWidthBound input (spectralFullBoxRadius B) 0
  have hQ0 : 0 ≤ Q := empiricalFWidthBound_nonneg input _ 0
    (spectralFullBoxRadius_nonneg B)
  have hmapWidth' : (map.eval node schedule.fuel).width ≤
      128 * Q * node.width + e.1 := by
    simpa [map, spectralDenominatorMap, Q] using hmapWidth
  let r := requested.1
  let R := radiusSlackUpper B j
  let t := schedule.tolerance.1
  have hR0 : 0 ≤ R := by
    dsimp [R, radiusSlackUpper]
    linarith [radiusUpper_nonneg B j]
  have hcore : 64 * (1 + R) * (1 + A) ^ 2 ≤ S := by
    simpa [R, S, max_eq_right hR0, max_eq_right hA] using
      spectralNodeScale_core_le B j A lower count operations
  have htEq : 64 * S * t = r ^ 2 := by
    have hS1 : 1 ≤ S := by
      dsimp [S, spectralNodeScale]
      exact le_max_left _ _
    change 64 * S * tolerance.1 = requested.1 ^ 2
    exact estimatorNodePrecision_scale_eq requested S hS1
  have heEq : 16 * e.1 = t ^ 2 := by
    change 16 * (spectralNodeTarget tolerance).1 = tolerance.1 ^ 2
    dsimp [spectralNodeTarget]
    ring
  have hrpBudget : (1 + e.1) * radiusPrecision.1 ≤ t / 4 := by
    have he0 : 0 ≤ e.1 := e.2.le
    have hp := min_le_right (1 : ℚ)
      (schedule.tolerance.1 / (4 * (1 + max 0 e.1)))
    change radiusPrecision.1 ≤ schedule.tolerance.1 /
      (4 * (1 + max 0 e.1)) at hp
    rw [max_eq_right he0] at hp
    calc
      (1 + e.1) * radiusPrecision.1 ≤
          (1 + e.1) * (t / (4 * (1 + e.1))) := by
        simpa [t] using mul_le_mul_of_nonneg_left hp (by linarith)
      _ = t / 4 := by field_simp [ne_of_gt (by linarith [e.2] : 0 < 1 + e.1)]
  have hwidthBudget : (map.eval node schedule.fuel).width ≤
      r ^ 2 / (32 * (A + 1)) := by
    apply quadratic_node_map_width_budget (r := r) (R := R) (Q := Q)
      (A := A) (S := S) (t := t) (e := e.1)
      (rp := radiusPrecision.1) (nw := node.width)
    · exact requested.2
    · exact hrequested
    · exact hR0
    · exact hQ0
    · exact hA
    · exact hQA
    · exact hcore
    · exact schedule.tolerance.2.le
    · exact e.2.le
    · exact radiusPrecision.2.le
    · exact (RatInterval.width_nonneg node.re).trans (le_max_left _ _)
    · exact htEq
    · exact heEq
    · exact hrpBudget
    · exact hnodeWidth
    · exact hmapWidth'
  have hwidthOne : (map.eval node schedule.fuel).width ≤ 1 := by
    refine hwidthBudget.trans ?_
    apply (div_le_one (by positivity : (0 : ℚ) < 32 * (A + 1))).2
    have hprod : 0 ≤ r * (1 - r) :=
      mul_nonneg requested.2.le (by linarith)
    nlinarith
  let z := CircleMesh.circleMap 0 (B.rho j)
    (CircleMesh.meshPoint schedule.mesh k)
  have hzNorm : ‖z‖ = B.rho j := by
    simp [z, CircleMesh.circleMap, Complex.norm_exp, abs_of_pos hrho.1]
  have hURfull : B.UR ≤ spectralFullBoxRadius B :=
    contourBank_UR_le_spectralFullBoxRadius B
  have hzFull : ‖z‖ ≤ spectralFullBoxRadius B := by
    rw [hzNorm]
    exact hrho.2.trans (by exact_mod_cast hURfull)
  have hzValue : (map.eval node schedule.fuel).Contains (map.value z) := by
    exact (hvalid.2.2 hbox hsound).1 schedule.fuel
  have hvalueA : ‖map.value z‖ ≤ (A : ℝ) := by
    have hv := spectralDenominatorMap_norm_le input B I 0
      (spectralFullBoxRadius_nonneg B) hzFull
    have hd := empiricalFDerivativeBound_zero_le_widthBound input
      (spectralFullBoxRadius B) (spectralFullBoxRadius_nonneg B)
    exact hv.trans (by exact_mod_cast hd.trans hQA)
  have hmapMax : (map.eval node schedule.fuel).maxAbs ≤ A + 1 := by
    apply ComplexRatInterval.maxAbs_le_of_contains_width hzValue
    · exact max_le ((Complex.abs_re_le_norm _).trans hvalueA)
        ((Complex.abs_im_le_norm _).trans hvalueA)
    · exact hwidthOne
  have hwidthRaw : (map.eval node schedule.fuel).width ≤
      r ^ 2 / (16 * ((A + 1) + 1)) := by
    refine hwidthBudget.trans ?_
    apply (div_le_div_iff₀ (by positivity : (0 : ℚ) < 32 * (A + 1))
      (by positivity : (0 : ℚ) < 16 * ((A + 1) + 1))).2
    nlinarith [sq_nonneg r]
  have ht_le_r : t ≤ r := by
    have hS64 : 64 ≤ S := by
      nlinarith [hcore, sq_nonneg A]
    nlinarith [htEq, requested.2, hrequested, schedule.tolerance.2]
  have hrawFuel : 64 * (schedule.tolerance.1.den + 1) *
      ((A + 1).num.natAbs + 2) ^ 2 ≤ schedule.fuel := by
    obtain ⟨n, rfl⟩ := hAnat
    simpa [schedule] using
      spectralSchedule_rawNormFuel_nat_succ tolerance operations L n hL
  refine ⟨hsound, hbox, hmapWidth, ?_⟩
  exact normInterval_width_of_width_maxAbs _ requested schedule.tolerance
    (A + 1) schedule.fuel (by linarith) hmapMax ht_le_r hwidthRaw hrawFuel

private lemma twoPiIRect_maxAbs_le_nine (precision : ℕ) :
    (twoPiIRect precision).maxAbs ≤ 9 := by
  have hsub : (Transcendental.piInterval precision).Subinterval
      (Transcendental.piInterval 0) := by
    simpa [Transcendental.piName] using
      CertifiedReal.approx_mono Transcendental.piName (Nat.zero_le precision)
  have hmul : ((RatInterval.point 2).mul
      (Transcendental.piInterval precision)).Subinterval
      ((RatInterval.point 2).mul (Transcendental.piInterval 0)) :=
    RatInterval.mul_mono ⟨le_rfl, le_rfl⟩ hsub
  have hmax := ComplexRatInterval.rat_maxAbs_mono hmul
  calc
    (twoPiIRect precision).maxAbs =
        ((RatInterval.point 2).mul
          (Transcendental.piInterval precision)).maxAbs := by
      simp [twoPiIRect, ComplexRatInterval.maxAbs, RatInterval.point,
        RatInterval.maxAbs]
    _ ≤ ((RatInterval.point 2).mul
          (Transcendental.piInterval 0)).maxAbs := hmax
    _ ≤ 9 := by
      norm_num [Transcendental.piInterval, Transcendental.piRaw,
        Transcendental.atanRaw, Transcendental.atanPartial,
        Transcendental.atanError, RatInterval.mul, RatInterval.add,
        RatInterval.sub, RatInterval.neg, RatInterval.point, RatInterval.maxAbs]

private lemma twoPiIRect_width_le_two_pi_width (precision : ℕ) :
    (twoPiIRect precision).width ≤
      2 * (Transcendental.piInterval precision).width := by
  have hlo0 : 0 < (Transcendental.piInterval precision).lo := by
    have hzero : 0 < (Transcendental.piInterval 0).lo := by
      norm_num [Transcendental.piInterval, Transcendental.piRaw,
        Transcendental.atanRaw, Transcendental.atanPartial,
        Transcendental.atanError, RatInterval.mul, RatInterval.sub,
        RatInterval.add, RatInterval.neg, RatInterval.point]
    have hsub : (Transcendental.piInterval precision).Subinterval
        (Transcendental.piInterval 0) := by
      simpa [Transcendental.piName] using
        CertifiedReal.approx_mono Transcendental.piName (Nat.zero_le precision)
    exact hzero.trans_le hsub.1
  have hlohi := (Transcendental.piInterval precision).lo_le_hi
  unfold twoPiIRect ComplexRatInterval.width RatInterval.width RatInterval.mul
  simp [RatInterval.point, hlo0.le, hlohi]
  linarith

private lemma tangentNode_width_bound
    (B : ContourBankData) (j : Fin (B.JBase + 1))
    (radiusPrecision : PosRat) (piPrecision : ℕ) (schedule : Schedule)
    (k : ℕ)
    (hnodeMax : (certifiedRadiusNode (B.rhoName j) radiusPrecision schedule k).maxAbs ≤
      2 * radiusSlackUpper B j * (1 + (spectralNodeTarget schedule.tolerance).1)) :
    (tangentNode (B.rhoName j) radiusPrecision piPrecision schedule k).width ≤
      2 * (9 * (certifiedRadiusNode (B.rhoName j) radiusPrecision schedule k).width +
        2 * radiusSlackUpper B j *
          (1 + (spectralNodeTarget schedule.tolerance).1) *
          (2 * (Transcendental.piInterval piPrecision).width)) := by
  have hraw := ComplexRatInterval.mul_width (twoPiIRect piPrecision)
    (certifiedRadiusNode (B.rhoName j) radiusPrecision schedule k)
  have hpiMax := twoPiIRect_maxAbs_le_nine piPrecision
  have hpiWidth := twoPiIRect_width_le_two_pi_width piPrecision
  have hn0 : 0 ≤ (certifiedRadiusNode (B.rhoName j) radiusPrecision schedule k).maxAbs :=
    (abs_nonneg _).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hp0 : 0 ≤ (twoPiIRect piPrecision).maxAbs :=
    (abs_nonneg _).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hnwidth0 : 0 ≤
      (certifiedRadiusNode (B.rhoName j) radiusPrecision schedule k).width :=
    (RatInterval.width_nonneg _).trans (le_max_left _ _)
  have hpwidth0 : 0 ≤ (twoPiIRect piPrecision).width :=
    (RatInterval.width_nonneg _).trans (le_max_left _ _)
  have hR0 : 0 ≤ radiusSlackUpper B j := by
    dsimp [radiusSlackUpper]
    linarith [radiusUpper_nonneg B j]
  have hnodeEnvelope0 : 0 ≤ 2 * radiusSlackUpper B j *
      (1 + (spectralNodeTarget schedule.tolerance).1) :=
    mul_nonneg (mul_nonneg (by norm_num) hR0)
      (by linarith [(spectralNodeTarget schedule.tolerance).2])
  unfold tangentNode
  calc
    ((twoPiIRect piPrecision).mul
        (certifiedRadiusNode (B.rhoName j) radiusPrecision schedule k)).width ≤
        2 * ((twoPiIRect piPrecision).maxAbs *
          (certifiedRadiusNode (B.rhoName j) radiusPrecision schedule k).width +
          (certifiedRadiusNode (B.rhoName j) radiusPrecision schedule k).maxAbs *
            (twoPiIRect piPrecision).width) := hraw
    _ ≤ 2 * (9 *
          (certifiedRadiusNode (B.rhoName j) radiusPrecision schedule k).width +
        2 * radiusSlackUpper B j *
          (1 + (spectralNodeTarget schedule.tolerance).1) *
            (2 * (Transcendental.piInterval piPrecision).width)) := by
      gcongr

private lemma pilotScheduleWitness (input : RepresentedSpectralInput p)
    (pStar : CertifiedBankInputs p)
    (hcanonical : CanonicalRepresentedSpectralInput Xspace input) :
    let B := contourBank p pStar
    ∀ (a : Fin 2) (j : Fin (B.JBase + 1)),
      let schedule := pilotSchedule input B a j
      let map := spectralDenominatorMap input B (spectralFold p.n a) 0
      let L := pilotCircleLipschitzBound input (radiusUpper B j)
      let amplification := pilotScheduleMagnitude input B j
      let unitWidth := (spectralNodeTarget schedule.tolerance).1
      let radiusPrecision := bankRadiusPrecision schedule.tolerance unitWidth
      ExactSpectralSchedule schedule amplification ∧ schedule.magnitude = L ∧ map.Valid ∧
        map.precision (spectralNodeTarget schedule.tolerance) ≤ schedule.fuel ∧
        radiusPrecision.1 ≤ 1 ∧
        ∀ k ≤ schedule.mesh,
          (spectralRadiusNode B j schedule k).Contains
            (CircleMesh.circleMap 0 (B.rho j) (CircleMesh.meshPoint schedule.mesh k)) ∧
          (spectralRadiusNode B j schedule k).Subinterval (spectralDiskBox B) ∧
          (bankRadiusRect (B.rhoName j) radiusPrecision).maxAbs ≤ radiusSlackUpper B j ∧
          (spectralRadiusNode B j schedule k).width ≤
            2 * (radiusSlackUpper B j * unitWidth +
              (1 + unitWidth) * radiusPrecision.1) ∧
          (map.eval (spectralRadiusNode B j schedule k) schedule.fuel).width ≤
            map.derivativeEnvelope * (spectralRadiusNode B j schedule k).width +
              (spectralNodeTarget schedule.tolerance).1 ∧
          ((map.eval (spectralRadiusNode B j schedule k) schedule.fuel).normInterval
            schedule.fuel).width ≤ (pilotNodeTolerance B).1 := by
  let B := contourBank p pStar
  dsimp only
  intro a j
  refine ⟨?_, rfl,
    spectralDenominatorMap_valid_of_canonical input B (spectralFold p.n a) 0 hcanonical,
    pilot_denominator_precision_le input B a j, ?_, ?_⟩
  · unfold pilotSchedule
    exact exactSpectralSchedule_spectralSchedule _ _ _ _ _ _
  · exact min_le_left _ _
  · intro k hk
    let schedule := pilotSchedule input B a j
    let map := spectralDenominatorMap input B (spectralFold p.n a) 0
    let e := spectralNodeTarget schedule.tolerance
    let radiusPrecision := bankRadiusPrecision schedule.tolerance e.1
    have hexact : ExactSpectralSchedule schedule
        (pilotScheduleMagnitude input B j) := by
      unfold schedule pilotSchedule
      exact exactSpectralSchedule_spectralSchedule _ _ _ _ _ _
    have hsound : (spectralRadiusNode B j schedule k).Contains
        (CircleMesh.circleMap 0 (B.rho j)
          (CircleMesh.meshPoint schedule.mesh k)) := by
      exact certifiedRadiusNode_sound (B.rhoName j) radiusPrecision schedule hk
    have hcircleWidth : (circleNode 1 schedule k).width ≤ e.1 :=
      circleNode_width_le_target_of_exact schedule
        (pilotScheduleMagnitude input B j) hexact hk
    have hcircleMax : (circleNode 1 schedule k).maxAbs ≤ 1 + e.1 :=
      circleNode_maxAbs_le_one_add_target schedule
        (pilotScheduleMagnitude input B j) hexact hk
    have hbank : (bankRadiusRect (B.rhoName j) radiusPrecision).maxAbs ≤
        radiusSlackUpper B j :=
      bankRadiusRect_maxAbs_le_slack B j radiusPrecision (min_le_left _ _)
    have hnodeWidth : (spectralRadiusNode B j schedule k).width ≤
        2 * (radiusSlackUpper B j * e.1 +
          (1 + e.1) * radiusPrecision.1) := by
      simpa [spectralRadiusNode] using certifiedRadiusNode_width
        (B.rhoName j) radiusPrecision schedule (radiusSlackUpper B j) e.1 hk
        hbank hcircleWidth hcircleMax
    let r := (pilotNodeTolerance B).1
    let R := radiusSlackUpper B j
    let A := pilotScheduleMagnitude input B j
    let S := spectralNodeScale B j A ⟨1, by norm_num⟩ 1
      (spectralNodeOperationCount .pilot (spectralFold p.n a).card)
    let t := schedule.tolerance.1
    have hr1 : r ≤ 1 := by
      have ha : B.aStarRat ≤ 1 := by
        dsimp [B, contourBank]
        exact pow_le_one₀ (by norm_num) (by norm_num)
      dsimp [r, pilotNodeTolerance]
      nlinarith
    have hcore : 64 * (1 + R) * (1 + A) ^ 2 ≤ S := by
      have hR0 : 0 ≤ R := by
        dsimp [R, radiusSlackUpper]
        linarith [radiusUpper_nonneg B j]
      have hA0 := pilotScheduleMagnitude_nonneg input B j
      simpa [R, A, S, max_eq_right hR0, max_eq_right hA0] using
        spectralNodeScale_core_le B j A ⟨1, by norm_num⟩ 1
          (spectralNodeOperationCount .pilot (spectralFold p.n a).card)
    have htEq : 64 * S * t = r ^ 2 := by
      have hS1 : 1 ≤ S := by
        dsimp [S, spectralNodeScale]
        exact le_max_left _ _
      exact estimatorNodePrecision_scale_eq (pilotNodeTolerance B) S hS1
    have heEq : 16 * e.1 = t ^ 2 := by
      dsimp [e, spectralNodeTarget, t]
      ring
    have hrpBudget : (1 + e.1) * radiusPrecision.1 ≤ t / 4 := by
      have he0 : 0 ≤ e.1 := e.2.le
      have hp := min_le_right (1 : ℚ)
        (schedule.tolerance.1 / (4 * (1 + max 0 e.1)))
      change radiusPrecision.1 ≤ schedule.tolerance.1 /
        (4 * (1 + max 0 e.1)) at hp
      rw [max_eq_right he0] at hp
      have hfac : 0 ≤ 1 + e.1 := by linarith
      have hfacpos : 0 < 1 + e.1 := by linarith [e.2]
      calc
        (1 + e.1) * radiusPrecision.1 ≤
            (1 + e.1) * (t / (4 * (1 + e.1))) := by
          simpa [t] using mul_le_mul_of_nonneg_left hp hfac
        _ = t / 4 := by field_simp [hfacpos.ne']
    have hnodeSmall : (spectralRadiusNode B j schedule k).width ≤ 1 := by
      apply quadratic_node_width_le_one (r := r) (R := R) (A := A) (S := S)
        (t := t) (e := e.1) (rp := radiusPrecision.1)
      · exact (pilotNodeTolerance B).2
      · exact hr1
      · dsimp [R, radiusSlackUpper]; linarith [radiusUpper_nonneg B j]
      · exact pilotScheduleMagnitude_nonneg input B j
      · exact hcore
      · exact schedule.tolerance.2.le
      · exact radiusPrecision.2.le
      · exact htEq
      · exact heEq
      · exact hrpBudget
      · simpa [R, t, e, radiusPrecision] using hnodeWidth
    have hbox : (spectralRadiusNode B j schedule k).Subinterval
        (spectralDiskBox B) := by
      let z := CircleMesh.circleMap 0 (B.rho j)
        (CircleMesh.meshPoint schedule.mesh k)
      have hrho : 0 < B.rho j ∧ B.rho j ≤ (B.UR : ℝ) := by
        simpa [B] using contourBank_rho_pos_le_UR p pStar j
      have hnorm : ‖z‖ = B.rho j := by
        simp [z, CircleMesh.circleMap, Complex.norm_exp]
        exact hrho.1.le
      have hre : |z.re| ≤ (B.UR : ℝ) := by
        calc
          |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
          _ = B.rho j := hnorm
          _ ≤ B.UR := hrho.2
      have him : |z.im| ≤ (B.UR : ℝ) := by
        calc
          |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
          _ = B.rho j := hnorm
          _ ≤ B.UR := hrho.2
      convert rectangle_subinterval_symmetric_of_contains_width
        (spectralRadiusNode B j schedule k) z B.UR hsound hre him
          (hnodeSmall.trans (by norm_num)) using 1 <;>
        simp [spectralDiskBox] <;> ring
    have hmapWidth : (map.eval (spectralRadiusNode B j schedule k)
        schedule.fuel).width ≤ map.derivativeEnvelope *
          (spectralRadiusNode B j schedule k).width + e.1 := by
      exact boundedComplexMap_eval_width_of_precision_le map
        (spectralDenominatorMap_valid_of_canonical input B (spectralFold p.n a) 0
        hcanonical) hbox hsound e schedule.fuel
        (pilot_denominator_precision_le input B a j)
    let Q := empiricalFWidthBound input (spectralFullBoxRadius B) 0
    have hQ0 : 0 ≤ Q := empiricalFWidthBound_nonneg input _ 0
      (spectralFullBoxRadius_nonneg B)
    have hQA : Q ≤ A := by
      simpa [Q, A] using pilot_widthBound_le_scheduleMagnitude input B j
    have hmapWidth' : (map.eval (spectralRadiusNode B j schedule k)
        schedule.fuel).width ≤ 128 * Q *
          (spectralRadiusNode B j schedule k).width + e.1 := by
      simpa [map, spectralDenominatorMap, Q] using hmapWidth
    have hwidthBudget : (map.eval (spectralRadiusNode B j schedule k)
        schedule.fuel).width ≤ r ^ 2 / (32 * (A + 1)) := by
      apply quadratic_node_map_width_budget (r := r) (R := R) (Q := Q)
        (A := A) (S := S) (t := t) (e := e.1)
        (rp := radiusPrecision.1)
        (nw := (spectralRadiusNode B j schedule k).width)
      · exact (pilotNodeTolerance B).2
      · exact hr1
      · dsimp [R, radiusSlackUpper]; linarith [radiusUpper_nonneg B j]
      · exact hQ0
      · exact pilotScheduleMagnitude_nonneg input B j
      · exact hQA
      · exact hcore
      · exact schedule.tolerance.2.le
      · exact e.2.le
      · exact radiusPrecision.2.le
      · exact (RatInterval.width_nonneg _).trans (le_max_left _ _)
      · exact htEq
      · exact heEq
      · exact hrpBudget
      · simpa [R, t, e, radiusPrecision] using hnodeWidth
      · exact hmapWidth'
    have hwidthOne : (map.eval (spectralRadiusNode B j schedule k)
        schedule.fuel).width ≤ 1 := by
      refine hwidthBudget.trans ?_
      apply (div_le_one (by
        have hA0 := pilotScheduleMagnitude_nonneg input B j
        positivity : (0 : ℚ) < 32 * (A + 1))).2
      have hprod : 0 ≤ r * (1 - r) :=
        mul_nonneg (pilotNodeTolerance B).2.le (by linarith)
      nlinarith
    let z := CircleMesh.circleMap 0 (B.rho j)
      (CircleMesh.meshPoint schedule.mesh k)
    have hzNorm : ‖z‖ = B.rho j := by
      simp [z, CircleMesh.circleMap, Complex.norm_exp]
      simpa [B] using (contourBank_rho_pos_le_UR p pStar j).1.le
    have hURfull : B.UR ≤ spectralFullBoxRadius B :=
      contourBank_UR_le_spectralFullBoxRadius B
    have hzFull : ‖z‖ ≤ spectralFullBoxRadius B := by
      rw [hzNorm]
      exact (contourBank_rho_pos_le_UR p pStar j).2.trans
        (by exact_mod_cast hURfull)
    have hzValue : (map.eval (spectralRadiusNode B j schedule k)
        schedule.fuel).Contains (map.value z) := by
      exact ((spectralDenominatorMap_valid_of_canonical input B
        (spectralFold p.n a) 0 hcanonical).2.2 hbox hsound).1 schedule.fuel
    have hvalueA : ‖map.value z‖ ≤ (A : ℝ) := by
      have hv := spectralDenominatorMap_norm_le input B (spectralFold p.n a) 0
        (spectralFullBoxRadius_nonneg B) hzFull
      have hd := empiricalFDerivativeBound_zero_le_widthBound input
        (spectralFullBoxRadius B) (spectralFullBoxRadius_nonneg B)
      exact hv.trans ((by exact_mod_cast hd.trans hQA))
    have hmapMax : (map.eval (spectralRadiusNode B j schedule k)
        schedule.fuel).maxAbs ≤ A + 1 := by
      apply ComplexRatInterval.maxAbs_le_of_contains_width hzValue
      · exact max_le ((Complex.abs_re_le_norm _).trans hvalueA)
          ((Complex.abs_im_le_norm _).trans hvalueA)
      · exact hwidthOne
    have hwidthRaw : (map.eval (spectralRadiusNode B j schedule k)
        schedule.fuel).width ≤ r ^ 2 / (16 * ((A + 1) + 1)) := by
      refine hwidthBudget.trans ?_
      have hA0 := pilotScheduleMagnitude_nonneg input B j
      apply (div_le_div_iff₀ (by positivity : (0 : ℚ) < 32 * (A + 1))
        (by positivity : (0 : ℚ) < 16 * ((A + 1) + 1))).2
      nlinarith [sq_nonneg r]
    have ht_le_r : t ≤ r := by
      have hS64 : 64 ≤ S := by
        have hA0 := pilotScheduleMagnitude_nonneg input B j
        have hR0 : 0 ≤ R := by
          dsimp [R, radiusSlackUpper]
          linarith [radiusUpper_nonneg B j]
        nlinarith [hcore, sq_nonneg A]
      nlinarith [htEq, (pilotNodeTolerance B).2, hr1, schedule.tolerance.2]
    have hrawFuel : 64 * (schedule.tolerance.1.den + 1) *
        ((A + 1).num.natAbs + 2) ^ 2 ≤ schedule.fuel := by
      let tolerance := estimatorNodePrecision (pilotNodeTolerance B) S
      let q : ℕ := ((128 * max 1
        (empiricalFWidthBound input (spectralFullBoxRadius B) 0)) ^ 2).num.natAbs
      have hfuel := spectralSchedule_rawNormFuel_nat_succ tolerance
        (spectralNodeOperationCount .pilot (spectralFold p.n a).card)
        (pilotCircleLipschitzBound input (radiusUpper B j)) q
        (pilotCircleLipschitzBound_nonneg input (radiusUpper_nonneg B j))
      simpa [schedule, pilotSchedule, tolerance, S, A, pilotScheduleMagnitude, q]
        using hfuel
    refine ⟨hsound, hbox, hbank, hnodeWidth, hmapWidth, ?_⟩
    exact normInterval_width_of_width_maxAbs _ (pilotNodeTolerance B)
      schedule.tolerance (A + 1) schedule.fuel
      (by linarith [pilotScheduleMagnitude_nonneg input B j]) hmapMax ht_le_r
      hwidthRaw hrawFuel

private lemma pilotModulus_lo_le_denominator_norm
    (input : RepresentedSpectralInput p) (pStar : CertifiedBankInputs p)
    (hcanonical : CanonicalRepresentedSpectralInput Xspace input)
    (a : Fin 2) (j : Fin ((contourBank p pStar).JBase + 1))
    (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    ((pilotModulus input (contourBank p pStar) a j).lo : ℝ) ≤
      ‖(spectralDenominatorMap input (contourBank p pStar)
        (spectralFold p.n a) 0).value
          (CircleMesh.circleMap 0 ((contourBank p pStar).rho j) u)‖ := by
  let B := contourBank p pStar
  let schedule := pilotSchedule input B a j
  let map := spectralDenominatorMap input B (spectralFold p.n a) 0
  let f : ℝ → ℝ := fun s ↦ ‖map.value
    (CircleMesh.circleMap 0 (B.rho j) s)‖
  have hs := pilotScheduleWitness input pStar hcanonical a j
  have hnodes : ∀ k ≤ schedule.mesh,
      ((map.eval (spectralRadiusNode B j schedule k) schedule.fuel).normInterval
        schedule.fuel).Contains (f (CircleMesh.meshPoint schedule.mesh k)) := by
    intro k hk
    have hkdata := hs.2.2.2.2.2 k hk
    have hmapContains := (hs.2.2.1.2.2 hkdata.2.1 hkdata.1).1 schedule.fuel
    exact ComplexRatInterval.normInterval_sound hmapContains schedule.fuel
  have hinf : (pilotModulus input B a j).Contains
      (sInf (f '' Set.Icc (0 : ℝ) 1)) := by
    dsimp [pilotModulus]
    apply CircleMesh.infEnclosure_sound
    · intro s hs' t ht'
      exact pilotMap_norm_lipschitz input B (spectralFold p.n a)
        (by exact_mod_cast (contourBank_rho_pos_le_UR p pStar j).1.le)
        (certifiedRadius_value_le_radiusUpper B j) s t
    · simpa [schedule, map, f] using hnodes
  have hbdd : BddBelow (f '' Set.Icc (0 : ℝ) 1) := by
    refine ⟨0, ?_⟩
    rintro y ⟨s, hs', rfl⟩
    exact norm_nonneg _
  have hle := (hinf.1.trans (csInf_le hbdd ⟨u, hu, rfl⟩))
  simpa [B, map, f] using hle

set_option maxHeartbeats 2400000 in
set_option maxRecDepth 4096 in
private lemma guardedNodeTolerance_le_one (requested lower : PosRat)
    (hrequested : requested.1 ≤ 1) :
    (guardedNodeTolerance requested lower).1 ≤ 1 := by
  have hfrac : lower.1 ^ 2 / (1 + lower.1) ^ 2 ≤ 1 := by
    apply (div_le_one (sq_pos_of_pos (by linarith [lower.2]))).2
    nlinarith [lower.2, sq_nonneg lower.1]
  have hmin := min_le_right (lower.1 / 8)
    (requested.1 * lower.1 ^ 2 / (1 + lower.1) ^ 2)
  change (guardedNodeTolerance requested lower).1 ≤ 1
  dsimp [guardedNodeTolerance]
  calc
    min (lower.1 / 8)
        (requested.1 * lower.1 ^ 2 / (1 + lower.1) ^ 2) ≤
        requested.1 * lower.1 ^ 2 / (1 + lower.1) ^ 2 := hmin
    _ ≤ 1 := by
      calc
        requested.1 * lower.1 ^ 2 / (1 + lower.1) ^ 2 =
            requested.1 * (lower.1 ^ 2 / (1 + lower.1) ^ 2) := by ring
        _ ≤ 1 * 1 := mul_le_mul hrequested hfrac (by positivity) (by positivity)
        _ = 1 := one_mul 1

private lemma winding_node_specification
    (input : RepresentedSpectralInput p) (pStar : CertifiedBankInputs p)
    (hcanonical : CanonicalRepresentedSpectralInput Xspace input)
    (j : Fin ((contourBank p pStar).JBase + 1))
    (lower : PosRat)
    (hlower : lower.1 = (pilotModulus input (contourBank p pStar) 0 j).lo)
    (k : ℕ)
    (hk : k ≤ (spectralWindingEvaluator input (contourBank p pStar) j lower).schedule.mesh) :
    let B := contourBank p pStar
    let ev := spectralWindingEvaluator input B j lower
    lower.1 / 2 ≤
        ((ev.denominator.eval
          (certifiedRadiusNode ev.radius ev.radiusPrecision ev.schedule k)
          ev.mapFuel).normInterval ev.mapFuel).lo ∧
      (ev.denominator.eval
        (certifiedRadiusNode ev.radius ev.radiusPrecision ev.schedule k)
        ev.mapFuel).normSq.AwayFromZero ∧
      (ev.numerator.eval
        (certifiedRadiusNode ev.radius ev.radiusPrecision ev.schedule k)
        ev.mapFuel).width ≤ ev.numerator.derivativeEnvelope *
          (certifiedRadiusNode ev.radius ev.radiusPrecision ev.schedule k).width +
          (spectralNodeTarget ev.schedule.tolerance).1 ∧
      (ev.denominator.eval
        (certifiedRadiusNode ev.radius ev.radiusPrecision ev.schedule k)
        ev.mapFuel).width ≤ ev.denominator.derivativeEnvelope *
          (certifiedRadiusNode ev.radius ev.radiusPrecision ev.schedule k).width +
          (spectralNodeTarget ev.schedule.tolerance).1 ∧
      (tangentNode ev.radius ev.radiusPrecision ev.piPrecision ev.schedule k).width ≤
        2 * (9 *
          (certifiedRadiusNode ev.radius ev.radiusPrecision ev.schedule k).width +
          2 * radiusSlackUpper B j *
            (1 + (spectralNodeTarget ev.schedule.tolerance).1) *
            (2 * (Transcendental.piInterval ev.piPrecision).width)) := by
  dsimp only
  let B := contourBank p pStar
  let ev := spectralWindingEvaluator input B j lower
  let requested := guardedNodeTolerance windingNodeTolerance lower
  let operations := spectralNodeOperationCount .winding (spectralFold p.n 0).card
  let A := windingScheduleMagnitude input B j lower
  let L := windingLipschitzBound input (radiusUpper B j) lower.1
  have hL : 0 ≤ L := windingLipschitzBound_nonneg input
    (radiusUpper_nonneg B j) lower.2
  have hA : 0 ≤ A := windingScheduleMagnitude_nonneg input B j lower
  have hreq1 : requested.1 ≤ 1 :=
    guardedNodeTolerance_le_one windingNodeTolerance lower
      (by norm_num [windingNodeTolerance])
  have hAnat : ∃ n : ℕ, A = n := by
    refine ⟨max
      (((128 * max 1 (empiricalFWidthBound input (spectralFullBoxRadius B) 0)) ^ 2).num.natAbs)
      (((128 * max 1 (empiricalFWidthBound input (spectralFullBoxRadius B) 1)) ^ 2).num.natAbs), ?_⟩
    rfl
  have hden := scheduledDenominatorNode_data input B (spectralFold p.n 0) j
    requested lower 1 operations L A hL hA hreq1
    (contourBank_rho_pos_le_UR p pStar j) hcanonical
    (winding_denominator_widthBound_le_scheduleMagnitude input B j lower)
    hAnat (winding_denominator_precision_le input B j lower) k (by exact hk)
  have hsound : (certifiedRadiusNode ev.radius ev.radiusPrecision ev.schedule k).Contains
      (CircleMesh.circleMap 0 (B.rho j) (CircleMesh.meshPoint ev.schedule.mesh k)) := by
    simpa [ev, spectralWindingEvaluator, requested, operations, A, L] using hden.1
  have hbox : (certifiedRadiusNode ev.radius ev.radiusPrecision ev.schedule k).Subinterval
      (spectralDiskBox B) := by
    simpa [ev, spectralWindingEvaluator, requested, operations, A, L] using hden.2.1
  have hdenWidth := hden.2.2.1
  have hnormWidth := hden.2.2.2
  have hnumValid := spectralDenominatorMap_valid_of_canonical input B
    (spectralFold p.n 0) 1 hcanonical
  have hnumWidth : (ev.numerator.eval
      (certifiedRadiusNode ev.radius ev.radiusPrecision ev.schedule k)
      ev.mapFuel).width ≤ ev.numerator.derivativeEnvelope *
        (certifiedRadiusNode ev.radius ev.radiusPrecision ev.schedule k).width +
        (spectralNodeTarget ev.schedule.tolerance).1 := by
    apply boundedComplexMap_eval_width_of_precision_le ev.numerator hnumValid hbox hsound
    exact winding_numerator_precision_le input B j lower
  let z := CircleMesh.circleMap 0 (B.rho j) (CircleMesh.meshPoint ev.schedule.mesh k)
  have hsem : (lower.1 : ℝ) ≤ ‖ev.denominator.value z‖ := by
    rw [hlower]
    simpa [B, ev, spectralWindingEvaluator, z] using
      pilotModulus_lo_le_denominator_norm input pStar hcanonical 0 j
        (CircleMesh.meshPoint ev.schedule.mesh k)
        (CircleMesh.meshPoint_mem ev.schedule.mesh_pos (by exact hk))
  have hdenContains : (ev.denominator.eval
      (certifiedRadiusNode ev.radius ev.radiusPrecision ev.schedule k)
      ev.mapFuel).Contains (ev.denominator.value z) :=
    (spectralDenominatorMap_valid_of_canonical input B (spectralFold p.n 0) 0
      hcanonical).2.2 hbox hsound |>.1 ev.mapFuel
  have hnormContains := ComplexRatInterval.normInterval_sound hdenContains ev.mapFuel
  have hrequestedLower : requested.1 ≤ lower.1 / 8 := by
    exact min_le_left _ _
  have hlo : lower.1 / 2 ≤
      ((ev.denominator.eval
        (certifiedRadiusNode ev.radius ev.radiusPrecision ev.schedule k)
        ev.mapFuel).normInterval ev.mapFuel).lo := by
    have hcLo := hnormContains.1
    have hcHi := hnormContains.2
    have hw := hnormWidth
    unfold RatInterval.width at hw
    exact_mod_cast (show (lower.1 : ℝ) / 2 ≤
      (((ev.denominator.eval
        (certifiedRadiusNode ev.radius ev.radiusPrecision ev.schedule k)
        ev.mapFuel).normInterval ev.mapFuel).lo : ℝ) by
      have hrequestedLowerR : (requested.1 : ℝ) ≤ (lower.1 : ℝ) / 8 := by
        exact_mod_cast hrequestedLower
      have hwR : ((((ev.denominator.eval
          (certifiedRadiusNode ev.radius ev.radiusPrecision ev.schedule k)
          ev.mapFuel).normInterval ev.mapFuel).hi : ℚ) : ℝ) -
          (((ev.denominator.eval
          (certifiedRadiusNode ev.radius ev.radiusPrecision ev.schedule k)
          ev.mapFuel).normInterval ev.mapFuel).lo : ℝ) ≤ requested.1 := by
        exact_mod_cast hw
      nlinarith)
  have haway : (ev.denominator.eval
      (certifiedRadiusNode ev.radius ev.radiusPrecision ev.schedule k)
      ev.mapFuel).normSq.AwayFromZero := by
    right
    let J := ev.denominator.eval
      (certifiedRadiusNode ev.radius ev.radiusPrecision ev.schedule k) ev.mapFuel
    have hJnonneg := ComplexRatInterval.normSq_lo_nonneg J
    have hnormLoPos : 0 < (J.normInterval ev.mapFuel).lo := by
      dsimp [J]
      linarith [lower.2]
    by_contra hnot
    have hzero : J.normSq.lo = 0 := le_antisymm (not_lt.mp hnot) hJnonneg
    rw [ComplexRatInterval.normInterval, RatInterval.sqrtInterval] at hnormLoPos
    change 0 < RatInterval.sqrtLower J.normSq.lo ev.mapFuel at hnormLoPos
    simp [RatInterval.sqrtLower, hzero] at hnormLoPos
  have hgeom := scheduledRadiusNode_data B j requested lower 1 operations L A
    hL hA hreq1 (contourBank_rho_pos_le_UR p pStar j) k (by exact hk)
  have hbank := hgeom.2.2.1
  have hexact : ExactSpectralSchedule ev.schedule A := by
    dsimp [ev, spectralWindingEvaluator]
    exact exactSpectralSchedule_spectralSchedule _ _ _ _ _ _
  have hcircleMax := circleNode_maxAbs_le_one_add_target ev.schedule A hexact
    (by exact hk)
  have hnodeMax : (certifiedRadiusNode ev.radius ev.radiusPrecision ev.schedule k).maxAbs ≤
      2 * radiusSlackUpper B j * (1 + (spectralNodeTarget ev.schedule.tolerance).1) := by
    dsimp [certifiedRadiusNode]
    refine (ComplexRatInterval.mul_maxAbs _ _).trans ?_
    have hR0 : 0 ≤ radiusSlackUpper B j := by
      dsimp [radiusSlackUpper]
      linarith [radiusUpper_nonneg B j]
    have he0 : 0 ≤ (spectralNodeTarget ev.schedule.tolerance).1 :=
      (spectralNodeTarget ev.schedule.tolerance).2.le
    have hcircle0 : 0 ≤ (circleNode 1 ev.schedule k).maxAbs :=
      (abs_nonneg _).trans ((le_max_left _ _).trans (le_max_left _ _))
    have hbank' : (bankRadiusRect ev.radius ev.radiusPrecision).maxAbs ≤
        radiusSlackUpper B j := by simpa [ev, spectralWindingEvaluator] using hbank
    exact mul_le_mul (mul_le_mul_of_nonneg_left hbank' (by norm_num)) hcircleMax
      hcircle0 (mul_nonneg (by norm_num) hR0)
  have htangent := tangentNode_width_bound B j ev.radiusPrecision ev.piPrecision
    ev.schedule k hnodeMax
  exact ⟨hlo, haway, hnumWidth, by
    exact hdenWidth,
    htangent⟩

private lemma spectralWindingEvaluator_valid
    (input : RepresentedSpectralInput p) (pStar : CertifiedBankInputs p)
    (hcanonical : CanonicalRepresentedSpectralInput Xspace input)
    (j : Fin ((contourBank p pStar).JBase + 1)) (lower : PosRat)
    (hlower : lower.1 = (pilotModulus input (contourBank p pStar) 0 j).lo) :
    (spectralWindingEvaluator input (contourBank p pStar) j lower).Valid := by
  let B := contourBank p pStar
  let ev := spectralWindingEvaluator input B j lower
  have hnumValid := spectralDenominatorMap_valid_of_canonical input B
    (spectralFold p.n 0) 1 hcanonical
  have hdenValid := spectralDenominatorMap_valid_of_canonical input B
    (spectralFold p.n 0) 0 hcanonical
  refine ⟨hnumValid, hdenValid, ?_, ?_⟩
  · intro k hk
    have hnode := winding_node_specification input pStar hcanonical j lower
      hlower k (by exact hk)
    let requested := guardedNodeTolerance windingNodeTolerance lower
    let operations := spectralNodeOperationCount .winding (spectralFold p.n 0).card
    let A := windingScheduleMagnitude input B j lower
    let L := windingLipschitzBound input (radiusUpper B j) lower.1
    have hgeom := scheduledRadiusNode_data B j requested lower 1 operations L A
      (windingLipschitzBound_nonneg input (radiusUpper_nonneg B j) lower.2)
      (windingScheduleMagnitude_nonneg input B j lower)
      (guardedNodeTolerance_le_one windingNodeTolerance lower
        (by norm_num [windingNodeTolerance]))
      (contourBank_rho_pos_le_UR p pStar j) k (by exact hk)
    exact ⟨by exact hgeom.2.1, hnode.2.1⟩
  · intro s hs t ht
    exact winding_circleIntegrand_lipschitz input B j lower
      (by exact (contourBank_rho_pos_le_UR p pStar j).1.le)
      (by
        intro u hu
        rw [hlower]
        exact pilotModulus_lo_le_denominator_norm input pStar hcanonical 0 j u hu)
      s hs t ht

private lemma evaluation_node_specification
    (input : RepresentedSpectralInput p) (pStar : CertifiedBankInputs p)
    (hcanonical : CanonicalRepresentedSpectralInput Xspace input)
    (j : Fin ((contourBank p pStar).JBase + 1)) (N : ℕ)
    (lower : PosRat)
    (hlower : lower.1 = (pilotModulus input (contourBank p pStar) 1 j).lo)
    (k : ℕ)
    (hk : k ≤ (spectralEvaluationEvaluator input (contourBank p pStar) j N lower).schedule.mesh) :
    let B := contourBank p pStar
    let ev := spectralEvaluationEvaluator input B j N lower
    lower.1 / 2 ≤ ((ev.denominator.eval
      (certifiedRadiusNode ev.radius ev.radiusPrecision ev.schedule k)
      ev.mapFuel).normInterval ev.mapFuel).lo ∧
    (ev.denominator.eval
      (certifiedRadiusNode ev.radius ev.radiusPrecision ev.schedule k)
      ev.mapFuel).normSq.AwayFromZero ∧
    (ev.numerator.eval
      (certifiedRadiusNode ev.radius ev.radiusPrecision ev.schedule k)
      ev.mapFuel).width ≤ ev.numerator.derivativeEnvelope *
        (certifiedRadiusNode ev.radius ev.radiusPrecision ev.schedule k).width +
        (spectralNodeTarget ev.schedule.tolerance).1 ∧
    (ev.denominator.eval
      (certifiedRadiusNode ev.radius ev.radiusPrecision ev.schedule k)
      ev.mapFuel).width ≤ ev.denominator.derivativeEnvelope *
        (certifiedRadiusNode ev.radius ev.radiusPrecision ev.schedule k).width +
        (spectralNodeTarget ev.schedule.tolerance).1 ∧
    (tangentNode ev.radius ev.radiusPrecision ev.piPrecision ev.schedule k).width ≤
      2 * (9 * (certifiedRadiusNode ev.radius ev.radiusPrecision ev.schedule k).width +
        2 * radiusSlackUpper B j *
          (1 + (spectralNodeTarget ev.schedule.tolerance).1) *
          (2 * (Transcendental.piInterval ev.piPrecision).width)) := by
  dsimp only
  let B := contourBank p pStar
  let ev := spectralEvaluationEvaluator input B j N lower
  let requested := guardedNodeTolerance (evaluationNodeTolerance p) lower
  let operations := spectralNodeOperationCount .evaluation (spectralFold p.n 1).card
  let A := evaluationScheduleMagnitude input B j N lower
  let L := momentLipschitzBound input (radiusUpper B j) lower.1 N
  have hL : 0 ≤ L := momentLipschitzBound_nonneg input N
    (radiusUpper_nonneg B j) lower.2
  have hA : 0 ≤ A := evaluationScheduleMagnitude_nonneg input B j N lower
  have hbase1 : (evaluationNodeTolerance p).1 ≤ 1 := by
    dsimp [evaluationNodeTolerance]
    have hn : (1 : ℚ) ≤ max (p.n : ℚ) 1 := le_max_right _ _
    rw [one_div]
    exact (inv_le_one₀ (by positivity : (0 : ℚ) < 2 * max (p.n : ℚ) 1)).2
      (by nlinarith)
  have hreq1 := guardedNodeTolerance_le_one (evaluationNodeTolerance p) lower hbase1
  have hAnat : ∃ n : ℕ, A = n := by
    refine ⟨max
      (((128 * max 1 (empiricalFWidthBound input (spectralFullBoxRadius B) 0)) ^ 2).num.natAbs)
      (((256 * max 1 (empiricalGWidthBound input (spectralFullBoxRadius B) 0)) ^ 2).num.natAbs), rfl⟩
  have hden := scheduledDenominatorNode_data input B (spectralFold p.n 1) j
    requested lower (max N 1) operations L A hL hA hreq1
    (contourBank_rho_pos_le_UR p pStar j) hcanonical
    (evaluation_denominator_widthBound_le_scheduleMagnitude input B j N lower)
    hAnat (evaluation_denominator_precision_le input B j N lower) k
    (by exact hk)
  have hsound : (certifiedRadiusNode ev.radius ev.radiusPrecision ev.schedule k).Contains
      (CircleMesh.circleMap 0 (B.rho j) (CircleMesh.meshPoint ev.schedule.mesh k)) := by
    simpa [ev, spectralEvaluationEvaluator, requested, operations, A, L] using hden.1
  have hbox : (certifiedRadiusNode ev.radius ev.radiusPrecision ev.schedule k).Subinterval
      (spectralDiskBox B) := by
    simpa [ev, spectralEvaluationEvaluator, requested, operations, A, L] using hden.2.1
  have hnumWidth : (ev.numerator.eval
      (certifiedRadiusNode ev.radius ev.radiusPrecision ev.schedule k)
      ev.mapFuel).width ≤ ev.numerator.derivativeEnvelope *
        (certifiedRadiusNode ev.radius ev.radiusPrecision ev.schedule k).width +
        (spectralNodeTarget ev.schedule.tolerance).1 := by
    apply boundedComplexMap_eval_width_of_precision_le ev.numerator
      (spectralNumeratorMap_valid_of_canonical input B (spectralFold p.n 1) 0 hcanonical)
      hbox hsound
    exact evaluation_numerator_precision_le input B j N lower
  let z := CircleMesh.circleMap 0 (B.rho j) (CircleMesh.meshPoint ev.schedule.mesh k)
  have hsem : (lower.1 : ℝ) ≤ ‖ev.denominator.value z‖ := by
    rw [hlower]
    simpa [B, ev, spectralEvaluationEvaluator, z] using
      pilotModulus_lo_le_denominator_norm input pStar hcanonical 1 j
        (CircleMesh.meshPoint ev.schedule.mesh k)
        (CircleMesh.meshPoint_mem ev.schedule.mesh_pos (by exact hk))
  have hdenContains : (ev.denominator.eval
      (certifiedRadiusNode ev.radius ev.radiusPrecision ev.schedule k)
      ev.mapFuel).Contains (ev.denominator.value z) :=
    (spectralDenominatorMap_valid_of_canonical input B (spectralFold p.n 1) 0
      hcanonical).2.2 hbox hsound |>.1 ev.mapFuel
  have hnormContains := ComplexRatInterval.normInterval_sound hdenContains ev.mapFuel
  have hreqLower : requested.1 ≤ lower.1 / 8 := min_le_left _ _
  have hlo : lower.1 / 2 ≤ ((ev.denominator.eval
      (certifiedRadiusNode ev.radius ev.radiusPrecision ev.schedule k)
      ev.mapFuel).normInterval ev.mapFuel).lo := by
    have hcLo := hnormContains.1
    have hcHi := hnormContains.2
    have hw := hden.2.2.2
    unfold RatInterval.width at hw
    exact_mod_cast (show (lower.1 : ℝ) / 2 ≤
      (((ev.denominator.eval
        (certifiedRadiusNode ev.radius ev.radiusPrecision ev.schedule k)
        ev.mapFuel).normInterval ev.mapFuel).lo : ℝ) by
      have hrequestedLowerR : (requested.1 : ℝ) ≤ (lower.1 : ℝ) / 8 := by
        exact_mod_cast hreqLower
      have hwR :
          (((ev.denominator.eval
            (certifiedRadiusNode ev.radius ev.radiusPrecision ev.schedule k)
            ev.mapFuel).normInterval ev.mapFuel).hi : ℝ) -
          (((ev.denominator.eval
            (certifiedRadiusNode ev.radius ev.radiusPrecision ev.schedule k)
            ev.mapFuel).normInterval ev.mapFuel).lo : ℝ) ≤
            (requested.1 : ℝ) := by
        exact_mod_cast hw
      nlinarith [hsem])
  have haway : (ev.denominator.eval
      (certifiedRadiusNode ev.radius ev.radiusPrecision ev.schedule k)
      ev.mapFuel).normSq.AwayFromZero := by
    right
    let J := ev.denominator.eval
      (certifiedRadiusNode ev.radius ev.radiusPrecision ev.schedule k) ev.mapFuel
    have hJnonneg := ComplexRatInterval.normSq_lo_nonneg J
    have hnormLoPos : 0 < (J.normInterval ev.mapFuel).lo := by
      dsimp [J]
      linarith [lower.2]
    by_contra hnot
    have hzero : J.normSq.lo = 0 := le_antisymm (not_lt.mp hnot) hJnonneg
    rw [ComplexRatInterval.normInterval, RatInterval.sqrtInterval] at hnormLoPos
    change 0 < RatInterval.sqrtLower J.normSq.lo ev.mapFuel at hnormLoPos
    simp [RatInterval.sqrtLower, hzero] at hnormLoPos
  have hgeom := scheduledRadiusNode_data B j requested lower (max N 1) operations L A
    hL hA hreq1 (contourBank_rho_pos_le_UR p pStar j) k (by exact hk)
  have hbank := hgeom.2.2.1
  have hexact : ExactSpectralSchedule ev.schedule A := by
    dsimp [ev, spectralEvaluationEvaluator]
    exact exactSpectralSchedule_spectralSchedule _ _ _ _ _ _
  have hcircle := circleNode_maxAbs_le_one_add_target ev.schedule A hexact
    (by exact hk)
  have hnodeMax : (certifiedRadiusNode ev.radius ev.radiusPrecision ev.schedule k).maxAbs ≤
      2 * radiusSlackUpper B j * (1 + (spectralNodeTarget ev.schedule.tolerance).1) := by
    dsimp [certifiedRadiusNode]
    refine (ComplexRatInterval.mul_maxAbs _ _).trans ?_
    have hR0 : 0 ≤ radiusSlackUpper B j := by
      dsimp [radiusSlackUpper]
      linarith [radiusUpper_nonneg B j]
    have he0 : 0 ≤ (spectralNodeTarget ev.schedule.tolerance).1 :=
      (spectralNodeTarget ev.schedule.tolerance).2.le
    have hcircle0 : 0 ≤ (circleNode 1 ev.schedule k).maxAbs :=
      (abs_nonneg _).trans ((le_max_left _ _).trans (le_max_left _ _))
    have hbank' : (bankRadiusRect ev.radius ev.radiusPrecision).maxAbs ≤
        radiusSlackUpper B j := by simpa [ev, spectralEvaluationEvaluator] using hbank
    exact mul_le_mul (mul_le_mul_of_nonneg_left hbank' (by norm_num)) hcircle
      hcircle0 (mul_nonneg (by norm_num) hR0)
  exact ⟨hlo, haway, hnumWidth, by
    exact hden.2.2.1,
    tangentNode_width_bound B j ev.radiusPrecision ev.piPrecision ev.schedule k hnodeMax⟩

private lemma spectralEvaluationEvaluator_valid
    (input : RepresentedSpectralInput p) (pStar : CertifiedBankInputs p)
    (hcanonical : CanonicalRepresentedSpectralInput Xspace input)
    (j : Fin ((contourBank p pStar).JBase + 1)) (N : ℕ) (lower : PosRat)
    (hlower : lower.1 = (pilotModulus input (contourBank p pStar) 1 j).lo) :
    (spectralEvaluationEvaluator input (contourBank p pStar) j N lower).Valid := by
  let B := contourBank p pStar
  let ev := spectralEvaluationEvaluator input B j N lower
  refine ⟨spectralNumeratorMap_valid_of_canonical input B (spectralFold p.n 1) 0 hcanonical,
    spectralDenominatorMap_valid_of_canonical input B (spectralFold p.n 1) 0 hcanonical,
    ?_, ?_⟩
  · intro k hk
    have hn := evaluation_node_specification input pStar hcanonical j N lower hlower k
      (by exact hk)
    let requested := guardedNodeTolerance (evaluationNodeTolerance p) lower
    let operations := spectralNodeOperationCount .evaluation (spectralFold p.n 1).card
    let A := evaluationScheduleMagnitude input B j N lower
    let L := momentLipschitzBound input (radiusUpper B j) lower.1 N
    have hbase1 : (evaluationNodeTolerance p).1 ≤ 1 := by
      dsimp [evaluationNodeTolerance]
      have hn : (1 : ℚ) ≤ max (p.n : ℚ) 1 := le_max_right _ _
      rw [one_div]
      exact (inv_le_one₀ (by positivity : (0 : ℚ) < 2 * max (p.n : ℚ) 1)).2
        (by nlinarith)
    have hg := scheduledRadiusNode_data B j requested lower (max N 1) operations L A
      (momentLipschitzBound_nonneg input N (radiusUpper_nonneg B j) lower.2)
      (evaluationScheduleMagnitude_nonneg input B j N lower)
      (guardedNodeTolerance_le_one (evaluationNodeTolerance p) lower hbase1)
      (contourBank_rho_pos_le_UR p pStar j) k (by exact hk)
    exact ⟨by exact hg.2.1, hn.2.1⟩
  · intro s hs t ht
    exact moment_circleIntegrand_lipschitz input B j N lower
      (by exact (contourBank_rho_pos_le_UR p pStar j).1.le)
      (by
        intro u hu
        rw [hlower]
        exact pilotModulus_lo_le_denominator_norm input pStar hcanonical 1 j u hu)
      s hs t ht

private lemma boundedComplexMap_eval_sharp_bounds
    {box : ComplexRatInterval} (map : BoundedComplexMap box)
    (hvalid : map.Valid) (K : ComplexRatInterval) (z : ℂ)
    (e : PosRat) (fuel : ℕ) (C t : ℚ)
    (hbox : K.Subinterval box) (hz : K.Contains z)
    (hprecision : map.precision e ≤ fuel)
    (hC : 0 ≤ C) (ht : 0 ≤ t) (htC : (C + 1) * t ≤ 1)
    (hderivative : map.derivativeEnvelope ≤ C)
    (hvalue : ‖map.value z‖ ≤ (C : ℝ))
    (hKw : K.width ≤ t) (he : e.1 ≤ t) :
    (map.eval K fuel).width ≤ (C + 1) * t ∧
      (map.eval K fuel).maxAbs ≤ C + 1 := by
  have hraw := boundedComplexMap_eval_width_of_precision_le map hvalid hbox hz e fuel
    hprecision
  have hwidth : (map.eval K fuel).width ≤ (C + 1) * t := by
    have hKw0 : 0 ≤ K.width :=
      (RatInterval.width_nonneg K.re).trans (le_max_left _ _)
    have hmul := mul_le_mul hderivative hKw hKw0 hC
    nlinarith [hraw]
  have hcontains := (hvalid.2.2 hbox hz).1 fuel
  have hmax := ComplexRatInterval.maxAbs_le_of_contains_width hcontains
    (max_le ((Complex.abs_re_le_norm _).trans hvalue)
      ((Complex.abs_im_le_norm _).trans hvalue)) hwidth
  exact ⟨hwidth, by nlinarith [hmax, htC]⟩

private lemma evaluation_map_node_bounds
    (input : RepresentedSpectralInput p) (pStar : CertifiedBankInputs p)
    (hcanonical : CanonicalRepresentedSpectralInput Xspace input)
    (j : Fin ((contourBank p pStar).JBase + 1)) (N : ℕ) (lower : PosRat)
    (k : ℕ) (hk : k ≤
      (spectralEvaluationEvaluator input (contourBank p pStar) j N lower).schedule.mesh) :
    let B := contourBank p pStar
    let ev := spectralEvaluationEvaluator input B j N lower
    let QF := empiricalFWidthBound input (spectralFullBoxRadius B) 0
    let QG := empiricalGWidthBound input (spectralFullBoxRadius B) 0
    let C := max (128 * QF) (256 * QG)
    let t := ev.schedule.tolerance.1
    let node := certifiedRadiusNode ev.radius ev.radiusPrecision ev.schedule k
    (ev.denominator.eval node ev.mapFuel).width ≤ (C + 1) * t ∧
      (ev.denominator.eval node ev.mapFuel).maxAbs ≤ C + 1 ∧
      (ev.numerator.eval node ev.mapFuel).width ≤ (C + 1) * t ∧
      (ev.numerator.eval node ev.mapFuel).maxAbs ≤ C + 1 := by
  dsimp only
  let B := contourBank p pStar
  let ev := spectralEvaluationEvaluator input B j N lower
  let QF := empiricalFWidthBound input (spectralFullBoxRadius B) 0
  let QG := empiricalGWidthBound input (spectralFullBoxRadius B) 0
  let C := max (128 * QF) (256 * QG)
  let A := evaluationScheduleMagnitude input B j N lower
  let requested := guardedNodeTolerance (evaluationNodeTolerance p) lower
  let operations := spectralNodeOperationCount .evaluation (spectralFold p.n 1).card
  let L := momentLipschitzBound input (radiusUpper B j) lower.1 N
  let S := spectralNodeScale B j A lower (max N 1) operations
  let t := ev.schedule.tolerance.1
  let e := spectralNodeTarget ev.schedule.tolerance
  let node := certifiedRadiusNode ev.radius ev.radiusPrecision ev.schedule k
  have hQF : 0 ≤ QF := empiricalFWidthBound_nonneg input _ 0
    (spectralFullBoxRadius_nonneg B)
  have hQG : 0 ≤ QG := empiricalGWidthBound_nonneg input _ 0
    (spectralFullBoxRadius_nonneg B)
  have hC : 0 ≤ C := le_max_of_le_left (mul_nonneg (by norm_num) hQF)
  have hA : 0 ≤ A := evaluationScheduleMagnitude_nonneg input B j N lower
  have hCA : C ^ 2 ≤ A := by
    have hleft : (128 * QF) ^ 2 ≤ A := by
      calc
        (128 * QF) ^ 2 ≤ (128 * max 1 QF) ^ 2 := by gcongr; exact le_max_right _ _
        _ ≤ ((((128 * max 1 QF) ^ 2).num.natAbs : ℕ) : ℚ) :=
          rat_le_num_natAbs (by positivity)
        _ ≤ A := by
          dsimp [A, evaluationScheduleMagnitude, QF, QG]
          exact_mod_cast (show
            ((128 * max 1 (empiricalFWidthBound input (spectralFullBoxRadius B) 0)) ^ 2).num.natAbs ≤
              max
                (((128 * max 1 (empiricalFWidthBound input (spectralFullBoxRadius B) 0)) ^ 2).num.natAbs)
                (((256 * max 1 (empiricalGWidthBound input (spectralFullBoxRadius B) 0)) ^ 2).num.natAbs)
            from le_max_left _ _)
    have hright : (256 * QG) ^ 2 ≤ A := by
      calc
        (256 * QG) ^ 2 ≤ (256 * max 1 QG) ^ 2 := by gcongr; exact le_max_right _ _
        _ ≤ ((((256 * max 1 QG) ^ 2).num.natAbs : ℕ) : ℚ) :=
          rat_le_num_natAbs (by positivity)
        _ ≤ A := by
          dsimp [A, evaluationScheduleMagnitude, QF, QG]
          exact_mod_cast (show
            ((256 * max 1 (empiricalGWidthBound input (spectralFullBoxRadius B) 0)) ^ 2).num.natAbs ≤
              max
                (((128 * max 1 (empiricalFWidthBound input (spectralFullBoxRadius B) 0)) ^ 2).num.natAbs)
                (((256 * max 1 (empiricalGWidthBound input (spectralFullBoxRadius B) 0)) ^ 2).num.natAbs)
            from le_max_right _ _)
    by_cases hle : 128 * QF ≤ 256 * QG
    · simpa [C, max_eq_right hle] using hright
    · simpa [C, max_eq_left (le_of_not_ge hle)] using hleft
  have hbase1 : (evaluationNodeTolerance p).1 ≤ 1 := by
    dsimp [evaluationNodeTolerance]
    have hn : (1 : ℚ) ≤ max (p.n : ℚ) 1 := le_max_right _ _
    rw [one_div]
    exact (inv_le_one₀ (by positivity : (0 : ℚ) < 2 * max (p.n : ℚ) 1)).2
      (by nlinarith)
  have hreq1 := guardedNodeTolerance_le_one (evaluationNodeTolerance p) lower hbase1
  have hR0 : 0 ≤ radiusSlackUpper B j := by
    dsimp [radiusSlackUpper]; linarith [radiusUpper_nonneg B j]
  have hcore : 64 * (1 + radiusSlackUpper B j) * (1 + A) ^ 2 ≤ S := by
    simpa [S, max_eq_right hR0, max_eq_right hA] using
      spectralNodeScale_core_le B j A lower (max N 1) operations
  have htEq : 64 * S * t = requested.1 ^ 2 := by
    have hS1 : 1 ≤ S := by dsimp [S, spectralNodeScale]; exact le_max_left _ _
    exact estimatorNodePrecision_scale_eq requested S hS1
  have ht0 : 0 ≤ t := ev.schedule.tolerance.2.le
  have ht1 : t ≤ 1 := by
    have hS64 : 64 ≤ S := by nlinarith [hcore, sq_nonneg A]
    nlinarith [htEq, requested.2, hreq1]
  have htC : (C + 1) * t ≤ 1 := by
    have hCle : C ≤ A + 1 := by nlinarith [hCA, sq_nonneg (C - 1)]
    have hS : 64 * (1 + A) ^ 2 ≤ S := by nlinarith [hcore]
    have hCS : C + 1 ≤ 64 * S := by
      nlinarith [sq_nonneg A]
    have hmul := mul_le_mul_of_nonneg_right hCS ht0
    nlinarith [htEq, hreq1, requested.2.le]
  have he : e.1 ≤ t := by
    have heq : 16 * e.1 = t ^ 2 := by dsimp [e, spectralNodeTarget, t]; ring
    nlinarith [sq_nonneg t]
  have hgeom := scheduledRadiusNode_data B j requested lower (max N 1) operations L A
    (momentLipschitzBound_nonneg input N (radiusUpper_nonneg B j) lower.2) hA hreq1
    (contourBank_rho_pos_le_UR p pStar j) k (by exact hk)
  have hsound : node.Contains (CircleMesh.circleMap 0 (B.rho j)
      (CircleMesh.meshPoint ev.schedule.mesh k)) := by
    simpa [node, ev, spectralEvaluationEvaluator, requested, operations, A, L] using hgeom.1
  have hbox : node.Subinterval (spectralDiskBox B) := by
    simpa [node, ev, spectralEvaluationEvaluator, requested, operations, A, L] using hgeom.2.1
  have hnodew : node.width ≤ t := by
    simpa [node, ev, spectralEvaluationEvaluator, requested, operations, A, L, t]
      using hgeom.2.2.2.2
  let z := CircleMesh.circleMap 0 (B.rho j) (CircleMesh.meshPoint ev.schedule.mesh k)
  have hzNorm : ‖z‖ = B.rho j := by
    have hrho0 : (0 : ℝ) ≤ B.rho j := by
      exact_mod_cast (contourBank_rho_pos_le_UR p pStar j).1.le
    simp [z, CircleMesh.circleMap, Complex.norm_exp, abs_of_nonneg hrho0]
  have hURfull : B.UR ≤ spectralFullBoxRadius B := by
    exact contourBank_UR_le_spectralFullBoxRadius B
  have hzFull : ‖z‖ ≤ spectralFullBoxRadius B := by
    rw [hzNorm]
    have hrhoUR : (B.rho j : ℝ) ≤ B.UR := by
      exact_mod_cast (contourBank_rho_pos_le_UR p pStar j).2
    have hURfullR : (B.UR : ℝ) ≤ (spectralFullBoxRadius B : ℝ) := by
      exact_mod_cast hURfull
    exact hrhoUR.trans hURfullR
  have hdenValue : ‖ev.denominator.value z‖ ≤ (C : ℝ) := by
    have hv := spectralDenominatorMap_norm_le input B (spectralFold p.n 1) 0
      (spectralFullBoxRadius_nonneg B) hzFull
    have hd := empiricalFDerivativeBound_zero_le_widthBound input _
      (spectralFullBoxRadius_nonneg B)
    have hq : QF ≤ C := by
      have := le_max_left (128 * QF) (256 * QG)
      nlinarith [hQF]
    exact hv.trans (by exact_mod_cast hd.trans hq)
  have hnumValue : ‖ev.numerator.value z‖ ≤ (C : ℝ) := by
    have hv := spectralNumeratorMap_norm_le input B (spectralFold p.n 1) 0
      (spectralFullBoxRadius_nonneg B) hzFull
    have hd := empiricalGDerivativeBound_zero_le_widthBound input _
      (spectralFullBoxRadius_nonneg B)
    have hq : QG ≤ C := by
      have := le_max_right (128 * QF) (256 * QG)
      nlinarith [hQG]
    exact hv.trans (by exact_mod_cast hd.trans hq)
  have hden := boundedComplexMap_eval_sharp_bounds ev.denominator
    (spectralDenominatorMap_valid_of_canonical input B (spectralFold p.n 1) 0 hcanonical)
    node z e ev.mapFuel C t hbox hsound
    (evaluation_denominator_precision_le input B j N lower) hC ht0 htC
    (by dsimp [ev, spectralEvaluationEvaluator, C, QF]; exact le_max_left _ _)
    hdenValue hnodew he
  have hnum := boundedComplexMap_eval_sharp_bounds ev.numerator
    (spectralNumeratorMap_valid_of_canonical input B (spectralFold p.n 1) 0 hcanonical)
    node z e ev.mapFuel C t hbox hsound
    (evaluation_numerator_precision_le input B j N lower) hC ht0 htC
    (by dsimp [ev, spectralEvaluationEvaluator, C, QG]; exact le_max_right _ _)
    hnumValue hnodew he
  exact ⟨hden.1, hden.2, hnum.1, hnum.2⟩

private lemma image_circleMesh_circleMap_Icc (r : ℝ) (hr : 0 < r) :
    CircleMesh.circleMap 0 r '' Set.Icc (0 : ℝ) 1 = Metric.sphere (0 : ℂ) r := by
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [Metric.mem_sphere]
    simp [CircleMesh.circleMap, Complex.norm_exp, abs_of_pos hr]
  · intro hz
    have hz' : z ∈ Metric.sphere (0 : ℂ) |r| := by
      simpa [abs_of_pos hr] using hz
    rw [← image_circleMap_Ioc] at hz'
    rcases hz' with ⟨theta, htheta, rfl⟩
    refine ⟨theta / (2 * Real.pi), ?_, ?_⟩
    · constructor
      · exact div_nonneg htheta.1.le Real.two_pi_pos.le
      · exact (div_le_one Real.two_pi_pos).2 htheta.2
    · simp only [CircleMesh.circleMap, circleMap, zero_add]
      congr 2
      push_cast
      field_simp [ne_of_gt Real.two_pi_pos]

/-- Explicit post-quadrature width contract.  It exposes the guarded-division
amplification and requires the actual normalized rectangle, not merely its
fuel, to meet the branch target. -/
def PostNormalizationWidthContract (I : ComplexRatInterval)
    (count piPrecision : ℕ) (target : ℚ) : Prop :=
  ∃ δ : ℚ, 0 < δ ∧
    δ ≤ (boundedContourDivisor count piPrecision).normSq.lo ∧
    boundedContourNormalizationWidthBound I count piPrecision δ < target ∧
    (boundedContourNormalize I count piPrecision).width < target

private lemma postNormalizationWidthContract_of_bounds
    (I : ComplexRatInterval) (count piPrecision : ℕ) (target M w : ℚ)
    (hM : I.maxAbs ≤ M) (hw : I.width ≤ w)
    (hbound :
      let D := boundedContourDivisor count piPrecision
      2 * M * D.maxAbs * D.normSq.width / D.normSq.lo ^ 2 +
        2 * (M * D.width + D.maxAbs * w) / D.normSq.lo < target) :
    PostNormalizationWidthContract I count piPrecision target := by
  let D := boundedContourDivisor count piPrecision
  have hpilo : 0 < (Transcendental.piInterval piPrecision).lo := by
    have hzero : 0 < (Transcendental.piInterval 0).lo := by
      norm_num [Transcendental.piInterval, Transcendental.piRaw,
        Transcendental.atanRaw, Transcendental.atanPartial,
        Transcendental.atanError, RatInterval.mul, RatInterval.sub,
        RatInterval.add, RatInterval.neg, RatInterval.point]
    have hsub : (Transcendental.piInterval piPrecision).Subinterval
        (Transcendental.piInterval 0) := by
      simpa [Transcendental.piName] using
        CertifiedReal.approx_mono Transcendental.piName (Nat.zero_le piPrecision)
    exact hzero.trans_le hsub.1
  have hd : 0 < D.normSq.lo := by
    have hcount : (0 : ℚ) < max count 1 := by positivity
    have hpile := (Transcendental.piInterval piPrecision).lo_le_hi
    have hDim : 0 < D.im.lo := by
      dsimp [D, boundedContourDivisor, twoPiIRect, ComplexRatInterval.smulRat]
      simp [RatInterval.point, RatInterval.mul, min_eq_left, max_eq_right,
        hpile, hpilo.le, hcount.le]
      positivity
    have hre : 0 ≤ D.re.sq.lo := by
      unfold RatInterval.sq
      split_ifs <;> dsimp <;> positivity
    have him : 0 < D.im.sq.lo := by
      have hhi : 0 ≤ D.im.hi := hDim.le.trans D.im.lo_le_hi
      simp [RatInterval.sq, not_lt_of_ge hhi, hDim]
    simpa [ComplexRatInterval.normSq, RatInterval.add] using
      add_pos_of_nonneg_of_pos hre him
  have hDA0 : 0 ≤ D.maxAbs :=
    (abs_nonneg _).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hDw0 : 0 ≤ D.width :=
    (RatInterval.width_nonneg D.re).trans (le_max_left _ _)
  have hIw0 : 0 ≤ I.width :=
    (RatInterval.width_nonneg I.re).trans (le_max_left _ _)
  have hM0 : 0 ≤ M :=
    ((abs_nonneg _).trans ((le_max_left _ _).trans (le_max_left _ _))).trans hM
  have hprodMax : (I.mul D.conj).maxAbs ≤ 2 * M * D.maxAbs := by
    have hc : D.conj.maxAbs = D.maxAbs := by
      change max D.re.maxAbs D.im.neg.maxAbs = max D.re.maxAbs D.im.maxAbs
      rw [RatInterval.maxAbs_neg]
    have hIA0 : 0 ≤ I.maxAbs :=
      (abs_nonneg I.re.lo).trans ((le_max_left _ _).trans (le_max_left _ _))
    calc
      (I.mul D.conj).maxAbs ≤ 2 * I.maxAbs * D.conj.maxAbs :=
        ComplexRatInterval.mul_maxAbs I D.conj
      _ ≤ 2 * M * D.maxAbs := by
        rw [hc]
        exact mul_le_mul (mul_le_mul_of_nonneg_left hM (by norm_num)) le_rfl
          hDA0 (mul_nonneg (by norm_num) hM0)
  have hprodWidth : (I.mul D.conj).width ≤
      2 * (M * D.width + D.maxAbs * w) := by
    have hcA : D.conj.maxAbs = D.maxAbs := by
      change max D.re.maxAbs D.im.neg.maxAbs = max D.re.maxAbs D.im.maxAbs
      rw [RatInterval.maxAbs_neg]
    have hcw : D.conj.width = D.width := by
      change max D.re.width D.im.neg.width = max D.re.width D.im.width
      rw [RatInterval.width_neg]
    have hraw := ComplexRatInterval.mul_width I D.conj
    rw [hcA, hcw] at hraw
    exact hraw.trans (mul_le_mul_of_nonneg_left (add_le_add
      (mul_le_mul hM le_rfl hDw0 hM0)
      (mul_le_mul le_rfl hw hIw0 hDA0)) (by norm_num))
  have hnormBound : boundedContourNormalizationWidthBound I count piPrecision
      D.normSq.lo < target := by
    dsimp [boundedContourNormalizationWidthBound, D]
    have hv0 := RatInterval.width_nonneg D.normSq
    have hterm1 := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hprodMax hv0) (sq_nonneg D.normSq.lo)
    have hterm2 := div_le_div_of_nonneg_right hprodWidth hd.le
    exact lt_of_le_of_lt (add_le_add hterm1 hterm2) (by simpa [D] using hbound)
  refine ⟨D.normSq.lo, hd, le_rfl, hnormBound, ?_⟩
  exact (boundedContourNormalize_width I count piPrecision D.normSq.lo hd le_rfl).trans_lt
    hnormBound

private lemma quotientTangentNode_width_bound
    (num den tangent : ComplexRatInterval) (haway : den.normSq.AwayFromZero)
    (M w T tw δ : ℚ) (hM : 0 ≤ M) (hw : 0 ≤ w) (hT : 0 ≤ T)
    (htw : 0 ≤ tw) (hδ : 0 < δ)
    (hnumA : num.maxAbs ≤ M) (hdenA : den.maxAbs ≤ M)
    (hnumw : num.width ≤ w) (hdenw : den.width ≤ w)
    (htanA : tangent.maxAbs ≤ T) (htanw : tangent.width ≤ tw)
    (hsep : δ ≤ den.normSq.lo) :
    ((num.div den haway).mul tangent).width ≤
      2 * ((2 * M ^ 2 / δ) * tw +
        T * (8 * M ^ 3 * w / δ ^ 2 + 4 * M * w / δ)) := by
  have hdenNormWidth : den.normSq.width ≤ 4 * M * w := by
    rw [show den.normSq.width = den.re.sq.width + den.im.sq.width by
      simp [ComplexRatInterval.normSq, RatInterval.width_add]]
    have hre := ComplexRatInterval.rat_sq_width_le den.re
    have him := ComplexRatInterval.rat_sq_width_le den.im
    have hreA : den.re.maxAbs ≤ M := (le_max_left _ _).trans hdenA
    have himA : den.im.maxAbs ≤ M := (le_max_right _ _).trans hdenA
    have hrew : den.re.width ≤ w := (le_max_left _ _).trans hdenw
    have himw : den.im.width ≤ w := (le_max_right _ _).trans hdenw
    nlinarith [mul_le_mul hreA hrew (RatInterval.width_nonneg den.re) hM,
      mul_le_mul himA himw (RatInterval.width_nonneg den.im) hM]
  have hprodA : (num.mul den.conj).maxAbs ≤ 2 * M ^ 2 := by
    have hc : den.conj.maxAbs = den.maxAbs := by
      change max den.re.maxAbs den.im.neg.maxAbs = max den.re.maxAbs den.im.maxAbs
      rw [RatInterval.maxAbs_neg]
    have hraw := ComplexRatInterval.mul_maxAbs num den.conj
    have hdenA0 : 0 ≤ den.maxAbs :=
      (abs_nonneg den.re.lo).trans ((le_max_left _ _).trans (le_max_left _ _))
    calc
      (num.mul den.conj).maxAbs ≤ 2 * num.maxAbs * den.conj.maxAbs := hraw
      _ ≤ 2 * M * M := by
        rw [hc]
        exact mul_le_mul (mul_le_mul_of_nonneg_left hnumA (by norm_num)) hdenA
          hdenA0 (mul_nonneg (by norm_num) hM)
      _ = 2 * M ^ 2 := by ring
  have hprodw : (num.mul den.conj).width ≤ 4 * M * w := by
    have hcA : den.conj.maxAbs = den.maxAbs := by
      change max den.re.maxAbs den.im.neg.maxAbs = max den.re.maxAbs den.im.maxAbs
      rw [RatInterval.maxAbs_neg]
    have hcw : den.conj.width = den.width := by
      change max den.re.width den.im.neg.width = max den.re.width den.im.width
      rw [RatInterval.width_neg]
    have hraw := ComplexRatInterval.mul_width num den.conj
    rw [hcA, hcw] at hraw
    have hdenWidth0 : 0 ≤ den.width :=
      (RatInterval.width_nonneg den.re).trans (le_max_left _ _)
    have hnumWidth0 : 0 ≤ num.width :=
      (RatInterval.width_nonneg num.re).trans (le_max_left _ _)
    calc
      (num.mul den.conj).width ≤
          2 * (num.maxAbs * den.width + den.maxAbs * num.width) := hraw
      _ ≤ 2 * (M * w + M * w) := by
        exact mul_le_mul_of_nonneg_left
          (add_le_add (mul_le_mul hnumA hdenw hdenWidth0 hM)
            (mul_le_mul hdenA hnumw hnumWidth0 hM)) (by norm_num)
      _ = 4 * M * w := by ring
  have hqA := ComplexRatInterval.div_maxAbs (I := num) haway hδ hsep
  have hqw := ComplexRatInterval.div_width (I := num) haway hδ hsep
  have hqA' : (num.div den haway).maxAbs ≤ 2 * M ^ 2 / δ :=
    hqA.trans (div_le_div_of_nonneg_right hprodA hδ.le)
  have hqw' : (num.div den haway).width ≤
      8 * M ^ 3 * w / δ ^ 2 + 4 * M * w / δ := by
    have hdenNormWidth0 : 0 ≤ den.normSq.width := RatInterval.width_nonneg _
    calc
      (num.div den haway).width ≤
          (num.mul den.conj).maxAbs * den.normSq.width / δ ^ 2 +
            (num.mul den.conj).width / δ := hqw
      _ ≤ (2 * M ^ 2) * (4 * M * w) / δ ^ 2 + (4 * M * w) / δ := by
        gcongr
      _ = 8 * M ^ 3 * w / δ ^ 2 + 4 * M * w / δ := by ring
  have hmul := ComplexRatInterval.mul_width (num.div den haway) tangent
  have hqA0 : 0 ≤ (num.div den haway).maxAbs :=
    (abs_nonneg _).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hqw0 : 0 ≤ (num.div den haway).width :=
    (RatInterval.width_nonneg _).trans (le_max_left _ _)
  have htw0' : 0 ≤ tangent.width :=
    (RatInterval.width_nonneg _).trans (le_max_left _ _)
  exact hmul.trans (mul_le_mul_of_nonneg_left
    (add_le_add
      (mul_le_mul hqA' htanw htw0'
        (div_nonneg (mul_nonneg (by positivity) (sq_nonneg M)) hδ.le))
      (mul_le_mul htanA hqw' hqw0 hT)) (by norm_num))

private lemma winding_width_scale_sq_le_scheduleMagnitude
    (input : RepresentedSpectralInput p) (B : ContourBankData)
    (j : Fin (B.JBase + 1)) (lower : PosRat) :
    (max
      (128 * empiricalFWidthBound input (spectralFullBoxRadius B) 0)
      (128 * empiricalFWidthBound input (spectralFullBoxRadius B) 1)) ^ 2 ≤
      windingScheduleMagnitude input B j lower := by
  let Q0 := empiricalFWidthBound input (spectralFullBoxRadius B) 0
  let Q1 := empiricalFWidthBound input (spectralFullBoxRadius B) 1
  let A := windingScheduleMagnitude input B j lower
  have hQ0 : 0 ≤ Q0 := empiricalFWidthBound_nonneg input _ 0
    (spectralFullBoxRadius_nonneg B)
  have hQ1 : 0 ≤ Q1 := empiricalFWidthBound_nonneg input _ 1
    (spectralFullBoxRadius_nonneg B)
  have hleft : (128 * Q0) ^ 2 ≤ A := by
    calc
      (128 * Q0) ^ 2 ≤ (128 * max 1 Q0) ^ 2 := by
        gcongr
        exact le_max_right (1 : ℚ) Q0
      _ ≤ ((((128 * max 1 Q0) ^ 2).num.natAbs : ℕ) : ℚ) :=
        rat_le_num_natAbs (by positivity)
      _ ≤ A := by
        dsimp [A, windingScheduleMagnitude, Q0, Q1]
        exact_mod_cast (show
          ((128 * max 1 (empiricalFWidthBound input (spectralFullBoxRadius B) 0)) ^ 2).num.natAbs ≤
            max
              (((128 * max 1 (empiricalFWidthBound input (spectralFullBoxRadius B) 0)) ^ 2).num.natAbs)
              (((128 * max 1 (empiricalFWidthBound input (spectralFullBoxRadius B) 1)) ^ 2).num.natAbs)
          from le_max_left _ _)
  have hright : (128 * Q1) ^ 2 ≤ A := by
    calc
      (128 * Q1) ^ 2 ≤ (128 * max 1 Q1) ^ 2 := by
        gcongr
        exact le_max_right (1 : ℚ) Q1
      _ ≤ ((((128 * max 1 Q1) ^ 2).num.natAbs : ℕ) : ℚ) :=
        rat_le_num_natAbs (by positivity)
      _ ≤ A := by
        dsimp [A, windingScheduleMagnitude, Q0, Q1]
        exact_mod_cast (show
          ((128 * max 1 (empiricalFWidthBound input (spectralFullBoxRadius B) 1)) ^ 2).num.natAbs ≤
            max
              (((128 * max 1 (empiricalFWidthBound input (spectralFullBoxRadius B) 0)) ^ 2).num.natAbs)
              (((128 * max 1 (empiricalFWidthBound input (spectralFullBoxRadius B) 1)) ^ 2).num.natAbs)
          from le_max_right _ _)
  by_cases hle : 128 * Q0 ≤ 128 * Q1
  · simpa [Q0, Q1, A, max_eq_right hle] using hright
  · simpa [Q0, Q1, A, max_eq_left (le_of_not_ge hle)] using hleft

set_option maxHeartbeats 800000 in
private lemma winding_map_node_bounds
    (input : RepresentedSpectralInput p) (pStar : CertifiedBankInputs p)
    (hcanonical : CanonicalRepresentedSpectralInput Xspace input)
    (j : Fin ((contourBank p pStar).JBase + 1)) (lower : PosRat)
    (k : ℕ) (hk : k ≤
      (spectralWindingEvaluator input (contourBank p pStar) j lower).schedule.mesh) :
    let B := contourBank p pStar
    let ev := spectralWindingEvaluator input B j lower
    let Q0 := empiricalFWidthBound input (spectralFullBoxRadius B) 0
    let Q1 := empiricalFWidthBound input (spectralFullBoxRadius B) 1
    let C := max (128 * Q0) (128 * Q1)
    let t := ev.schedule.tolerance.1
    let node := certifiedRadiusNode ev.radius ev.radiusPrecision ev.schedule k
    (ev.denominator.eval node ev.mapFuel).width ≤ (C + 1) * t ∧
      (ev.denominator.eval node ev.mapFuel).maxAbs ≤ C + 1 ∧
      (ev.numerator.eval node ev.mapFuel).width ≤ (C + 1) * t ∧
      (ev.numerator.eval node ev.mapFuel).maxAbs ≤ C + 1 := by
  dsimp only
  let B := contourBank p pStar
  let ev := spectralWindingEvaluator input B j lower
  let Q0 := empiricalFWidthBound input (spectralFullBoxRadius B) 0
  let Q1 := empiricalFWidthBound input (spectralFullBoxRadius B) 1
  let C := max (128 * Q0) (128 * Q1)
  let A := windingScheduleMagnitude input B j lower
  let requested := guardedNodeTolerance windingNodeTolerance lower
  let operations := spectralNodeOperationCount .winding (spectralFold p.n 0).card
  let L := windingLipschitzBound input (radiusUpper B j) lower.1
  let S := spectralNodeScale B j A lower 1 operations
  let t := ev.schedule.tolerance.1
  let e := spectralNodeTarget ev.schedule.tolerance
  let node := certifiedRadiusNode ev.radius ev.radiusPrecision ev.schedule k
  have hQ0 : 0 ≤ Q0 := empiricalFWidthBound_nonneg input _ 0
    (spectralFullBoxRadius_nonneg B)
  have hQ1 : 0 ≤ Q1 := empiricalFWidthBound_nonneg input _ 1
    (spectralFullBoxRadius_nonneg B)
  have hC : 0 ≤ C := le_max_of_le_left (mul_nonneg (by norm_num) hQ0)
  have hA : 0 ≤ A := windingScheduleMagnitude_nonneg input B j lower
  have hC_sq_A : C ^ 2 ≤ A := by
    simpa [C, A, Q0, Q1] using
      winding_width_scale_sq_le_scheduleMagnitude input B j lower
  have hR0 : 0 ≤ radiusSlackUpper B j := by
    dsimp [radiusSlackUpper]
    linarith [radiusUpper_nonneg B j]
  have hcore : 64 * (1 + radiusSlackUpper B j) * (1 + A) ^ 2 ≤ S := by
    simpa [S, max_eq_right hR0, max_eq_right hA] using
      spectralNodeScale_core_le B j A lower 1 operations
  have htEq : 64 * S * t = requested.1 ^ 2 := by
    have hS1 : 1 ≤ S := by
      dsimp [S, spectralNodeScale]
      exact le_max_left _ _
    exact estimatorNodePrecision_scale_eq requested S hS1
  have hreq1 := guardedNodeTolerance_le_one windingNodeTolerance lower
    (by norm_num [windingNodeTolerance])
  have ht0 : 0 ≤ t := ev.schedule.tolerance.2.le
  have ht1 : t ≤ 1 := by
    have hS64 : 64 ≤ S := by
      nlinarith [hcore, sq_nonneg A]
    nlinarith [htEq, requested.2, hreq1]
  have htC : (C + 1) * t ≤ 1 := by
    have hCle : C ≤ A + 1 := by nlinarith [hC_sq_A, sq_nonneg (C - 1)]
    have hS : 64 * (1 + A) ^ 2 ≤ S := by nlinarith [hcore]
    have hCS : C + 1 ≤ 64 * S := by nlinarith [sq_nonneg A]
    have hmul := mul_le_mul_of_nonneg_right hCS ht0
    nlinarith [htEq, hreq1, requested.2.le]
  have he : e.1 ≤ t := by
    have heq : 16 * e.1 = t ^ 2 := by
      dsimp [e, spectralNodeTarget, t]
      ring
    nlinarith [sq_nonneg t]
  have hgeom := scheduledRadiusNode_data B j requested lower 1 operations L A
    (windingLipschitzBound_nonneg input (radiusUpper_nonneg B j) lower.2) hA hreq1
    (contourBank_rho_pos_le_UR p pStar j) k (by exact hk)
  have hsound : node.Contains (CircleMesh.circleMap 0 (B.rho j)
      (CircleMesh.meshPoint ev.schedule.mesh k)) := by
    simpa [node, ev, spectralWindingEvaluator, requested, operations, A, L] using hgeom.1
  have hbox : node.Subinterval (spectralDiskBox B) := by
    simpa [node, ev, spectralWindingEvaluator, requested, operations, A, L] using hgeom.2.1
  have hnodew : node.width ≤ t := by
    simpa [node, ev, spectralWindingEvaluator, requested, operations, A, L, t]
      using hgeom.2.2.2.2
  let z := CircleMesh.circleMap 0 (B.rho j) (CircleMesh.meshPoint ev.schedule.mesh k)
  have hzNorm : ‖z‖ = B.rho j := by
    have hrho0 : (0 : ℝ) ≤ B.rho j := by
      exact_mod_cast (contourBank_rho_pos_le_UR p pStar j).1.le
    simp [z, CircleMesh.circleMap, Complex.norm_exp, abs_of_nonneg hrho0]
  have hURfull : B.UR ≤ spectralFullBoxRadius B := by
    exact contourBank_UR_le_spectralFullBoxRadius B
  have hzFull : ‖z‖ ≤ spectralFullBoxRadius B := by
    rw [hzNorm]
    have hrhoUR : (B.rho j : ℝ) ≤ B.UR := by
      exact_mod_cast (contourBank_rho_pos_le_UR p pStar j).2
    have hURfullR : (B.UR : ℝ) ≤ (spectralFullBoxRadius B : ℝ) := by
      exact_mod_cast hURfull
    exact hrhoUR.trans hURfullR
  have hdenValue : ‖ev.denominator.value z‖ ≤ (C : ℝ) := by
    have hv := spectralDenominatorMap_norm_le input B (spectralFold p.n 0) 0
      (spectralFullBoxRadius_nonneg B) hzFull
    have hd := empiricalFDerivativeBound_zero_le_widthBound input _
      (spectralFullBoxRadius_nonneg B)
    have hqC : Q0 ≤ C := by
      have hm := le_max_left (128 * Q0) (128 * Q1)
      nlinarith [hQ0]
    exact hv.trans (by exact_mod_cast hd.trans hqC)
  have hnumValue : ‖ev.numerator.value z‖ ≤ (C : ℝ) := by
    have hv := spectralDenominatorMap_norm_le input B (spectralFold p.n 0) 1
      (spectralFullBoxRadius_nonneg B) hzFull
    have hd := empiricalFDerivativeBound_one_le_widthBound input _
      (spectralFullBoxRadius_nonneg B)
    have hqC : Q1 ≤ C := by
      have := le_max_right (128 * Q0) (128 * Q1)
      nlinarith [hQ1]
    exact hv.trans (by exact_mod_cast hd.trans hqC)
  have hden := boundedComplexMap_eval_sharp_bounds ev.denominator
    (spectralDenominatorMap_valid_of_canonical input B (spectralFold p.n 0) 0 hcanonical)
    node z e ev.mapFuel C t hbox hsound
    (winding_denominator_precision_le input B j lower) hC ht0 htC
    (by dsimp [ev, spectralWindingEvaluator, C, Q0]; exact le_max_left _ _)
    hdenValue hnodew he
  have hnum := boundedComplexMap_eval_sharp_bounds ev.numerator
    (spectralDenominatorMap_valid_of_canonical input B (spectralFold p.n 0) 1 hcanonical)
    node z e ev.mapFuel C t hbox hsound
    (winding_numerator_precision_le input B j lower) hC ht0 htC
    (by dsimp [ev, spectralWindingEvaluator, C, Q1]; exact le_max_right _ _)
    hnumValue hnodew he
  exact ⟨hden.1, hden.2, hnum.1, hnum.2⟩

private lemma winding_contour_width_bound
    (input : RepresentedSpectralInput p) (pStar : CertifiedBankInputs p)
    (hcanonical : CanonicalRepresentedSpectralInput Xspace input)
    (j : Fin ((contourBank p pStar).JBase + 1)) (lower : PosRat)
    (hlower : lower.1 = (pilotModulus input (contourBank p pStar) 0 j).lo) :
    let B := contourBank p pStar
    let ev := spectralWindingEvaluator input B j lower
    let Q0 := empiricalFWidthBound input (spectralFullBoxRadius B) 0
    let Q1 := empiricalFWidthBound input (spectralFullBoxRadius B) 1
    let C := max (128 * Q0) (128 * Q1)
    let t := ev.schedule.tolerance.1
    let e := (spectralNodeTarget ev.schedule.tolerance).1
    let M := C + 1
    let R := radiusSlackUpper B j
    let T := 36 * R * (1 + e)
    let tw := 2 * (9 * t + 4 * R * (1 + e) * t)
    let δ := lower.1 ^ 2 / 4
    let W := 2 * ((2 * M ^ 2 / δ) * tw +
      T * (8 * M ^ 3 * (M * t) / δ ^ 2 + 4 * M * (M * t) / δ))
    (boundedContourEvaluate ev).width ≤ W + t / 3 := by
  dsimp only
  let B := contourBank p pStar
  let ev := spectralWindingEvaluator input B j lower
  let Q0 := empiricalFWidthBound input (spectralFullBoxRadius B) 0
  let Q1 := empiricalFWidthBound input (spectralFullBoxRadius B) 1
  let C := max (128 * Q0) (128 * Q1)
  let t := ev.schedule.tolerance.1
  let e := (spectralNodeTarget ev.schedule.tolerance).1
  let M := C + 1
  let R := radiusSlackUpper B j
  let T := 36 * R * (1 + e)
  let tw := 2 * (9 * t + 4 * R * (1 + e) * t)
  let δ := lower.1 ^ 2 / 4
  let W := 2 * ((2 * M ^ 2 / δ) * tw +
    T * (8 * M ^ 3 * (M * t) / δ ^ 2 + 4 * M * (M * t) / δ))
  have hvalid := spectralWindingEvaluator_valid input pStar hcanonical j lower hlower
  have hC0 : 0 ≤ C := by
    have hQ0 : 0 ≤ Q0 := empiricalFWidthBound_nonneg input _ 0
      (spectralFullBoxRadius_nonneg B)
    exact le_max_of_le_left (mul_nonneg (by norm_num) hQ0)
  have hM0 : 0 ≤ M := by dsimp [M]; linarith
  have hR0 : 0 ≤ R := by
    dsimp [R, radiusSlackUpper]
    linarith [radiusUpper_nonneg B j]
  have ht0 : 0 ≤ t := ev.schedule.tolerance.2.le
  have he0 : 0 ≤ e := (spectralNodeTarget ev.schedule.tolerance).2.le
  have hT0 : 0 ≤ T := by dsimp [T]; positivity
  have htw0 : 0 ≤ tw := by dsimp [tw]; positivity
  have hδ : 0 < δ := by
    dsimp [δ]
    exact div_pos (sq_pos_of_pos lower.2) (by norm_num)
  have hpi : 2 * (Transcendental.piInterval ev.piPrecision).width ≤ t := by
    let τ := circleInnerTolerance 1 (spectralNodeTarget ev.schedule.tolerance)
    have hp := Transcendental.piInterval_width τ
    have hprec : ev.piPrecision = Transcendental.piPrecision τ := by
      rfl
    rw [hprec]
    refine (mul_le_mul_of_nonneg_left hp (by norm_num)).trans ?_
    have hmin := min_le_left
      ((spectralNodeTarget ev.schedule.tolerance).1 / (256 * (|(1 : ℚ)| + 1)))
      (1 / 1024)
    dsimp [τ, circleInnerTolerance]
    have heq : 16 * e = t ^ 2 := by
      dsimp [e, t, spectralNodeTarget]
      ring
    have ht1 : t ≤ 1 := by
      have hreq := guardedNodeTolerance_le_one windingNodeTolerance lower
        (by norm_num [windingNodeTolerance])
      let A := windingScheduleMagnitude input B j lower
      let operations := spectralNodeOperationCount .winding (spectralFold p.n 0).card
      let S := spectralNodeScale B j A lower 1 operations
      have hS1 : 1 ≤ S := by dsimp [S, spectralNodeScale]; exact le_max_left _ _
      have hteq : 64 * S * t = (guardedNodeTolerance windingNodeTolerance lower).1 ^ 2 := by
        exact estimatorNodePrecision_scale_eq (guardedNodeTolerance windingNodeTolerance lower)
          S hS1
      have hscale : 1 ≤ 64 * S := by nlinarith
      have hmul := mul_le_mul_of_nonneg_right hscale ht0
      nlinarith [hreq, (guardedNodeTolerance windingNodeTolerance lower).2.le]
    nlinarith
  have hnode : ∀ k ≤ ev.schedule.mesh, (ev.node k).width ≤ W := by
    intro k hk
    have hmaps := winding_map_node_bounds input pStar hcanonical j lower k
      (by exact hk)
    have hspec := winding_node_specification input pStar hcanonical j lower hlower k
      (by exact hk)
    let node := certifiedRadiusNode ev.radius ev.radiusPrecision ev.schedule k
    let num := ev.numerator.eval node ev.mapFuel
    let den := ev.denominator.eval node ev.mapFuel
    let tangent := tangentNode ev.radius ev.radiusPrecision ev.piPrecision ev.schedule k
    have haway : den.normSq.AwayFromZero := by simpa [den, node] using hspec.2.1
    have hsep : δ ≤ den.normSq.lo := by
      have hlo : lower.1 / 2 ≤ (den.normInterval ev.mapFuel).lo := by
        simpa [den, node] using hspec.1
      have hsqrt := RatInterval.sqrt_iterates_sound den.normSq.lo
        (ComplexRatInterval.normSq_lo_nonneg den) ev.mapFuel
      have hreal : (lower.1 : ℝ) / 2 ≤ Real.sqrt den.normSq.lo := by
        have hloR : (lower.1 : ℝ) / 2 ≤
            ((den.normInterval ev.mapFuel).lo : ℝ) := by exact_mod_cast hlo
        exact hloR.trans hsqrt.1
      have hlo0R : (0 : ℝ) ≤ den.normSq.lo := by
        exact_mod_cast ComplexRatInterval.normSq_lo_nonneg den
      have hsq := Real.sq_sqrt hlo0R
      have hlower0R : (0 : ℝ) ≤ lower.1 := by exact_mod_cast lower.2.le
      have hrealSq := (sq_le_sq₀ (div_nonneg hlower0R (by norm_num))
        (Real.sqrt_nonneg _)).2 hreal
      exact_mod_cast (show (δ : ℝ) ≤ den.normSq.lo by
        calc
          (δ : ℝ) = ((lower.1 : ℝ) / 2) ^ 2 := by
            dsimp [δ]
            push_cast
            ring
          _ ≤ (Real.sqrt den.normSq.lo) ^ 2 := hrealSq
          _ = den.normSq.lo := hsq)
    have hgeom := scheduledRadiusNode_data B j
      (guardedNodeTolerance windingNodeTolerance lower) lower 1
      (spectralNodeOperationCount .winding (spectralFold p.n 0).card)
      (windingLipschitzBound input (radiusUpper B j) lower.1)
      (windingScheduleMagnitude input B j lower)
      (windingLipschitzBound_nonneg input (radiusUpper_nonneg B j) lower.2)
      (windingScheduleMagnitude_nonneg input B j lower)
      (guardedNodeTolerance_le_one windingNodeTolerance lower
        (by norm_num [windingNodeTolerance]))
      (contourBank_rho_pos_le_UR p pStar j) k (by exact hk)
    have hbank := hgeom.2.2.1
    have hexact : ExactSpectralSchedule ev.schedule
        (windingScheduleMagnitude input B j lower) := by
      dsimp [ev, spectralWindingEvaluator]
      exact exactSpectralSchedule_spectralSchedule _ _ _ _ _ _
    have hcircle := circleNode_maxAbs_le_one_add_target ev.schedule
      (windingScheduleMagnitude input B j lower) hexact (by exact hk)
    have hnodeA : node.maxAbs ≤ 2 * R * (1 + e) := by
      dsimp [node, certifiedRadiusNode, R, e]
      refine (ComplexRatInterval.mul_maxAbs _ _).trans ?_
      have hcircle0 : 0 ≤ (circleNode 1 ev.schedule k).maxAbs :=
        (abs_nonneg _).trans ((le_max_left _ _).trans (le_max_left _ _))
      have hbank' : (bankRadiusRect ev.radius ev.radiusPrecision).maxAbs ≤ R := by
        simpa [ev, spectralWindingEvaluator, R] using hbank
      exact mul_le_mul (mul_le_mul_of_nonneg_left hbank' (by norm_num)) hcircle
        hcircle0 (mul_nonneg (by norm_num) hR0)
    have htanA : tangent.maxAbs ≤ T := by
      dsimp [tangent, tangentNode, T]
      refine (ComplexRatInterval.mul_maxAbs _ _).trans ?_
      have hnodeA0 : 0 ≤ node.maxAbs :=
        (abs_nonneg _).trans ((le_max_left _ _).trans (le_max_left _ _))
      have hmul := mul_le_mul (twoPiIRect_maxAbs_le_nine ev.piPrecision) hnodeA
        hnodeA0 (by norm_num : (0 : ℚ) ≤ 9)
      nlinarith
    have htanw0 := tangentNode_width_bound B j ev.radiusPrecision ev.piPrecision
      ev.schedule k hnodeA
    have hnodew : node.width ≤ t := by
      simpa [node, ev, spectralWindingEvaluator, t] using hgeom.2.2.2.2
    have hpiw0 : 0 ≤ (Transcendental.piInterval ev.piPrecision).width :=
      RatInterval.width_nonneg _
    have htanw : tangent.width ≤ tw := by
      refine htanw0.trans ?_
      dsimp [tw, tangent, node, R, e]
      gcongr
      · exact hnodew
      · norm_num
    have hq := quotientTangentNode_width_bound num den tangent haway M (M * t) T tw δ
      hM0 (mul_nonneg hM0 ht0) hT0 htw0 hδ
      (by simpa [num, node, M] using hmaps.2.2.2)
      (by simpa [den, node, M] using hmaps.2.1)
      (by simpa [num, node, M] using hmaps.2.2.1)
      (by simpa [den, node, M] using hmaps.1)
      htanA htanw hsep
    dsimp [BoundedCircleEvaluator.node]
    split
    · simpa [num, den, tangent, node, W] using hq
    · rename_i hfalse
      exact (hfalse haway).elim
  have hwidth := boundedContourEvaluate_width ev hvalid W hnode
  calc
    (boundedContourEvaluate ev).width ≤ W + ev.lipschitz / ev.schedule.mesh := hwidth
    _ ≤ W + t / 3 := by
      have hm := ev.schedule.mesh_error_le
      calc
        W + ev.lipschitz / ev.schedule.mesh ≤ W + ev.schedule.meshBudget :=
          by simpa [ev, spectralWindingEvaluator] using add_le_add_left hm W
        _ = W + t / 3 := by rfl

-- The three explicit schedules require large rational normalization reductions.
private lemma evaluation_contour_width_bound
    (input : RepresentedSpectralInput p) (pStar : CertifiedBankInputs p)
    (hcanonical : CanonicalRepresentedSpectralInput Xspace input)
    (j : Fin ((contourBank p pStar).JBase + 1)) (N : ℕ) (lower : PosRat)
    (hlower : lower.1 = (pilotModulus input (contourBank p pStar) 1 j).lo) :
    let B := contourBank p pStar
    let ev := spectralEvaluationEvaluator input B j N lower
    let QF := empiricalFWidthBound input (spectralFullBoxRadius B) 0
    let QG := empiricalGWidthBound input (spectralFullBoxRadius B) 0
    let C := max (128 * QF) (256 * QG)
    let t := ev.schedule.tolerance.1
    let e := (spectralNodeTarget ev.schedule.tolerance).1
    let M := C + 1
    let R := radiusSlackUpper B j
    let T := 36 * R * (1 + e)
    let tw := 2 * (9 * t + 4 * R * (1 + e) * t)
    let δ := lower.1 ^ 2 / 4
    let W := 2 * ((2 * M ^ 2 / δ) * tw +
      T * (8 * M ^ 3 * (M * t) / δ ^ 2 + 4 * M * (M * t) / δ))
    (boundedContourEvaluate ev).width ≤ W + t / 3 := by
  dsimp only
  let B := contourBank p pStar
  let ev := spectralEvaluationEvaluator input B j N lower
  let QF := empiricalFWidthBound input (spectralFullBoxRadius B) 0
  let QG := empiricalGWidthBound input (spectralFullBoxRadius B) 0
  let C := max (128 * QF) (256 * QG)
  let t := ev.schedule.tolerance.1
  let e := (spectralNodeTarget ev.schedule.tolerance).1
  let M := C + 1
  let R := radiusSlackUpper B j
  let T := 36 * R * (1 + e)
  let tw := 2 * (9 * t + 4 * R * (1 + e) * t)
  let δ := lower.1 ^ 2 / 4
  let W := 2 * ((2 * M ^ 2 / δ) * tw +
    T * (8 * M ^ 3 * (M * t) / δ ^ 2 + 4 * M * (M * t) / δ))
  have hvalid := spectralEvaluationEvaluator_valid input pStar hcanonical j N lower hlower
  have hC0 : 0 ≤ C := by
    have hQF : 0 ≤ QF := empiricalFWidthBound_nonneg input _ 0
      (spectralFullBoxRadius_nonneg B)
    exact le_max_of_le_left (mul_nonneg (by norm_num) hQF)
  have hbase1 : (evaluationNodeTolerance p).1 ≤ 1 := by
    dsimp [evaluationNodeTolerance]
    have hn : (1 : ℚ) ≤ max (p.n : ℚ) 1 := le_max_right _ _
    rw [one_div]
    exact (inv_le_one₀ (by positivity : (0 : ℚ) < 2 * max (p.n : ℚ) 1)).2
      (by nlinarith)
  have hM0 : 0 ≤ M := by dsimp [M]; linarith
  have hR0 : 0 ≤ R := by
    dsimp [R, radiusSlackUpper]
    linarith [radiusUpper_nonneg B j]
  have ht0 : 0 ≤ t := ev.schedule.tolerance.2.le
  have he0 : 0 ≤ e := (spectralNodeTarget ev.schedule.tolerance).2.le
  have hT0 : 0 ≤ T := by dsimp [T]; positivity
  have htw0 : 0 ≤ tw := by dsimp [tw]; positivity
  have hδ : 0 < δ := by
    dsimp [δ]
    exact div_pos (sq_pos_of_pos lower.2) (by norm_num)
  have hpi : 2 * (Transcendental.piInterval ev.piPrecision).width ≤ t := by
    let τ := circleInnerTolerance 1 (spectralNodeTarget ev.schedule.tolerance)
    have hp := Transcendental.piInterval_width τ
    have hprec : ev.piPrecision = Transcendental.piPrecision τ := by
      rfl
    rw [hprec]
    refine (mul_le_mul_of_nonneg_left hp (by norm_num)).trans ?_
    have hmin := min_le_left
      ((spectralNodeTarget ev.schedule.tolerance).1 / (256 * (|(1 : ℚ)| + 1)))
      (1 / 1024)
    dsimp [τ, circleInnerTolerance]
    have heq : 16 * e = t ^ 2 := by
      dsimp [e, t, spectralNodeTarget]
      ring
    have ht1 : t ≤ 1 := by
      have hreq := guardedNodeTolerance_le_one (evaluationNodeTolerance p) lower hbase1
      let A := evaluationScheduleMagnitude input B j N lower
      let operations := spectralNodeOperationCount .evaluation (spectralFold p.n 1).card
      let S := spectralNodeScale B j A lower (max N 1) operations
      have hS1 : 1 ≤ S := by dsimp [S, spectralNodeScale]; exact le_max_left _ _
      have hteq : 64 * S * t = (guardedNodeTolerance (evaluationNodeTolerance p) lower).1 ^ 2 := by
        exact estimatorNodePrecision_scale_eq
          (guardedNodeTolerance (evaluationNodeTolerance p) lower) S hS1
      have hscale : 1 ≤ 64 * S := by nlinarith
      have hmul := mul_le_mul_of_nonneg_right hscale ht0
      nlinarith [hreq, (guardedNodeTolerance (evaluationNodeTolerance p) lower).2.le]
    nlinarith
  have hnode : ∀ k ≤ ev.schedule.mesh, (ev.node k).width ≤ W := by
    intro k hk
    have hmaps := evaluation_map_node_bounds input pStar hcanonical j N lower k
      (by exact hk)
    have hspec := evaluation_node_specification input pStar hcanonical j N lower hlower k
      (by exact hk)
    let node := certifiedRadiusNode ev.radius ev.radiusPrecision ev.schedule k
    let num := ev.numerator.eval node ev.mapFuel
    let den := ev.denominator.eval node ev.mapFuel
    let tangent := tangentNode ev.radius ev.radiusPrecision ev.piPrecision ev.schedule k
    have haway : den.normSq.AwayFromZero := by simpa [den, node] using hspec.2.1
    have hsep : δ ≤ den.normSq.lo := by
      have hlo : lower.1 / 2 ≤ (den.normInterval ev.mapFuel).lo := by
        simpa [den, node] using hspec.1
      have hsqrt := RatInterval.sqrt_iterates_sound den.normSq.lo
        (ComplexRatInterval.normSq_lo_nonneg den) ev.mapFuel
      have hreal : (lower.1 : ℝ) / 2 ≤ Real.sqrt den.normSq.lo := by
        have hloR : (lower.1 : ℝ) / 2 ≤
            ((den.normInterval ev.mapFuel).lo : ℝ) := by exact_mod_cast hlo
        exact hloR.trans hsqrt.1
      have hlo0R : (0 : ℝ) ≤ den.normSq.lo := by
        exact_mod_cast ComplexRatInterval.normSq_lo_nonneg den
      have hsq := Real.sq_sqrt hlo0R
      have hlower0R : (0 : ℝ) ≤ lower.1 := by exact_mod_cast lower.2.le
      have hrealSq := (sq_le_sq₀ (div_nonneg hlower0R (by norm_num))
        (Real.sqrt_nonneg _)).2 hreal
      exact_mod_cast (show (δ : ℝ) ≤ den.normSq.lo by
        calc
          (δ : ℝ) = ((lower.1 : ℝ) / 2) ^ 2 := by
            dsimp [δ]
            push_cast
            ring
          _ ≤ (Real.sqrt den.normSq.lo) ^ 2 := hrealSq
          _ = den.normSq.lo := hsq)
    have hgeom := scheduledRadiusNode_data B j
      (guardedNodeTolerance (evaluationNodeTolerance p) lower) lower (max N 1)
      (spectralNodeOperationCount .evaluation (spectralFold p.n 1).card)
      (momentLipschitzBound input (radiusUpper B j) lower.1 N)
      (evaluationScheduleMagnitude input B j N lower)
      (momentLipschitzBound_nonneg input N (radiusUpper_nonneg B j) lower.2)
      (evaluationScheduleMagnitude_nonneg input B j N lower)
      (guardedNodeTolerance_le_one (evaluationNodeTolerance p) lower hbase1)
      (contourBank_rho_pos_le_UR p pStar j) k (by exact hk)
    have hbank := hgeom.2.2.1
    have hexact : ExactSpectralSchedule ev.schedule
        (evaluationScheduleMagnitude input B j N lower) := by
      dsimp [ev, spectralEvaluationEvaluator]
      exact exactSpectralSchedule_spectralSchedule _ _ _ _ _ _
    have hcircle := circleNode_maxAbs_le_one_add_target ev.schedule
      (evaluationScheduleMagnitude input B j N lower) hexact (by exact hk)
    have hnodeA : node.maxAbs ≤ 2 * R * (1 + e) := by
      dsimp [node, certifiedRadiusNode, R, e]
      refine (ComplexRatInterval.mul_maxAbs _ _).trans ?_
      have hcircle0 : 0 ≤ (circleNode 1 ev.schedule k).maxAbs :=
        (abs_nonneg _).trans ((le_max_left _ _).trans (le_max_left _ _))
      have hbank' : (bankRadiusRect ev.radius ev.radiusPrecision).maxAbs ≤ R := by
        simpa [ev, spectralEvaluationEvaluator, R] using hbank
      exact mul_le_mul (mul_le_mul_of_nonneg_left hbank' (by norm_num)) hcircle
        hcircle0 (mul_nonneg (by norm_num) hR0)
    have htanA : tangent.maxAbs ≤ T := by
      dsimp [tangent, tangentNode, T]
      refine (ComplexRatInterval.mul_maxAbs _ _).trans ?_
      have hnodeA0 : 0 ≤ node.maxAbs :=
        (abs_nonneg _).trans ((le_max_left _ _).trans (le_max_left _ _))
      have hmul := mul_le_mul (twoPiIRect_maxAbs_le_nine ev.piPrecision) hnodeA
        hnodeA0 (by norm_num : (0 : ℚ) ≤ 9)
      nlinarith
    have htanw0 := tangentNode_width_bound B j ev.radiusPrecision ev.piPrecision
      ev.schedule k hnodeA
    have hnodew : node.width ≤ t := by
      simpa [node, ev, spectralEvaluationEvaluator, t] using hgeom.2.2.2.2
    have hpiw0 : 0 ≤ (Transcendental.piInterval ev.piPrecision).width :=
      RatInterval.width_nonneg _
    have htanw : tangent.width ≤ tw := by
      refine htanw0.trans ?_
      dsimp [tw, tangent, node, R, e]
      gcongr
      · exact hnodew
      · norm_num
    have hq := quotientTangentNode_width_bound num den tangent haway M (M * t) T tw δ
      hM0 (mul_nonneg hM0 ht0) hT0 htw0 hδ
      (by simpa [num, node, M] using hmaps.2.2.2)
      (by simpa [den, node, M] using hmaps.2.1)
      (by simpa [num, node, M] using hmaps.2.2.1)
      (by simpa [den, node, M] using hmaps.1)
      htanA htanw hsep
    dsimp [BoundedCircleEvaluator.node]
    split
    · simpa [num, den, tangent, node, W] using hq
    · rename_i hfalse
      exact (hfalse haway).elim
  have hwidth := boundedContourEvaluate_width ev hvalid W hnode
  calc
    (boundedContourEvaluate ev).width ≤ W + ev.lipschitz / ev.schedule.mesh := hwidth
    _ ≤ W + t / 3 := by
      have hm := ev.schedule.mesh_error_le
      calc
        W + ev.lipschitz / ev.schedule.mesh ≤ W + ev.schedule.meshBudget :=
          by simpa [ev, spectralEvaluationEvaluator] using add_le_add_left hm W
        _ = W + t / 3 := by rfl

private lemma winding_contour_value_norm_bound
    (input : RepresentedSpectralInput p) (pStar : CertifiedBankInputs p)
    (hcanonical : CanonicalRepresentedSpectralInput Xspace input)
    (j : Fin ((contourBank p pStar).JBase + 1)) (lower : PosRat)
    (hlower : lower.1 = (pilotModulus input (contourBank p pStar) 0 j).lo) :
    let B := contourBank p pStar
    let ev := spectralWindingEvaluator input B j lower
    ‖CircleMesh.circleContourIntegral
      (fun z ↦ ev.numerator.value z / ev.denominator.value z)
      0 ev.radius.value‖ ≤
      (8 * radiusUpper B j *
        empiricalFDerivativeBound input (radiusUpper B j) 1 / lower.1 : ℚ) := by
  dsimp only
  let B := contourBank p pStar
  let ev := spectralWindingEvaluator input B j lower
  let H : ℚ := 8 * radiusUpper B j *
    empiricalFDerivativeBound input (radiusUpper B j) 1 / lower.1
  have hdenLower : ∀ u ∈ Set.Icc (0 : ℝ) 1, (lower.1 : ℝ) ≤
      ‖ev.denominator.value (CircleMesh.circleMap 0 ev.radius.value u)‖ := by
    intro u hu
    rw [hlower]
    exact pilotModulus_lo_le_denominator_norm input pStar hcanonical 0 j u hu
  have hH0 : 0 ≤ H := by
    dsimp [H]
    exact div_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) (radiusUpper_nonneg B j))
        (empiricalFDerivativeBound_nonneg input (radiusUpper B j) 1))
      lower.2.le
  unfold CircleMesh.circleContourIntegral
  have hpoint : ∀ u ∈ Set.uIoc (0 : ℝ) 1,
      ‖CircleMesh.circleIntegrand
        (fun z ↦ ev.numerator.value z / ev.denominator.value z)
        0 ev.radius.value u‖ ≤ (H : ℝ) := by
    intro u hu
    have hr : 0 ≤ ev.radius.value := by
      exact (show (0 : ℝ) ≤ B.rho j by
        exact_mod_cast (contourBank_rho_pos_le_UR p pStar j).1.le)
    have hrle : ev.radius.value ≤ (radiusUpper B j : ℝ) := by
      simpa [B, ev, spectralWindingEvaluator] using certifiedRadius_value_le_radiusUpper B j
    have hz : ‖CircleMesh.circleMap 0 ev.radius.value u‖ ≤ (radiusUpper B j : ℝ) := by
      simpa [CircleMesh.circleMap, Complex.norm_exp, abs_of_nonneg hr] using hrle
    have hnum := spectralDenominatorMap_norm_le input B (spectralFold p.n 0) 1
      (radiusUpper_nonneg B j) hz
    have huIcc : u ∈ Set.Icc (0 : ℝ) 1 := by
      rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hu
      exact ⟨hu.1.le, hu.2⟩
    have hden := hdenLower u huIcc
    have hdenPos : 0 < ‖ev.denominator.value
        (CircleMesh.circleMap 0 ev.radius.value u)‖ := by
      have hlowerPosR : (0 : ℝ) < lower.1 := by exact_mod_cast lower.2
      exact hlowerPosR.trans_le hden
    have hquot : ‖ev.numerator.value
        (CircleMesh.circleMap 0 ev.radius.value u) /
        ev.denominator.value (CircleMesh.circleMap 0 ev.radius.value u)‖ ≤
      (empiricalFDerivativeBound input (radiusUpper B j) 1 : ℝ) / lower.1 := by
      rw [norm_div]
      exact div_le_div₀
        (by exact_mod_cast empiricalFDerivativeBound_nonneg input (radiusUpper B j) 1) hnum
        (by exact_mod_cast lower.2) hden
    have hquotBound0 : 0 ≤
        (empiricalFDerivativeBound input (radiusUpper B j) 1 : ℝ) / lower.1 :=
      div_nonneg
        (by exact_mod_cast empiricalFDerivativeBound_nonneg input (radiusUpper B j) 1)
        (by exact_mod_cast lower.2.le)
    have htan := circleTangent_norm_le ev.radius.value hr u
    rw [CircleMesh.circleIntegrand, norm_mul]
    calc
      _ ≤ ((empiricalFDerivativeBound input (radiusUpper B j) 1 : ℝ) / lower.1) *
          (8 * ev.radius.value) := mul_le_mul hquot htan (norm_nonneg _) hquotBound0
      _ ≤ ((empiricalFDerivativeBound input (radiusUpper B j) 1 : ℝ) / lower.1) *
          (8 * radiusUpper B j) := by
        gcongr
      _ = H := by
        dsimp [H]
        push_cast
        ring
  simpa [B, ev, H] using
    (intervalIntegral.norm_integral_le_of_norm_le_const hpoint)

private lemma boundedContourDivisor_precision_bounds (count precision : ℕ) :
    let D := boundedContourDivisor count precision
    let D0 := boundedContourDivisor count 0
    D.maxAbs ≤ D0.maxAbs ∧ D0.normSq.lo ≤ D.normSq.lo ∧
      D.width ≤ 2 * (max count 1 : ℚ) *
        (Transcendental.piInterval precision).width := by
  dsimp only
  let q : ℚ := max count 1
  let P := Transcendental.piInterval precision
  let P0 := Transcendental.piInterval 0
  have hq : 0 < q := by dsimp [q]; positivity
  have hP : P.Subinterval P0 := by
    dsimp [P, P0]
    simpa [Transcendental.piName] using
      CertifiedReal.approx_mono Transcendental.piName (Nat.zero_le precision)
  have hP0lo : 0 < P0.lo := by
    dsimp [P0]
    norm_num [Transcendental.piInterval, Transcendental.piRaw,
      Transcendental.atanRaw, Transcendental.atanPartial,
      Transcendental.atanError, RatInterval.mul, RatInterval.sub,
      RatInterval.add, RatInterval.neg, RatInterval.point]
  have hPlo : 0 < P.lo := hP0lo.trans_le hP.1
  have hPhi : 0 ≤ P.hi := hPlo.le.trans P.lo_le_hi
  have hP0hi : 0 ≤ P0.hi := hP0lo.le.trans P0.lo_le_hi
  have htwo : (0 : ℚ) ≤ 2 := by norm_num
  have himlo :
      (boundedContourDivisor count precision).im.lo = q * (2 * P.lo) := by
    dsimp [boundedContourDivisor, twoPiIRect, ComplexRatInterval.smulRat, q, P]
    simp [RatInterval.point, RatInterval.mul, min_eq_left, max_eq_right,
      hq.le, hPlo.le, P.lo_le_hi]
    ring
    exact Or.inl (by simpa [P] using P.lo_le_hi)
  have himhi :
      (boundedContourDivisor count precision).im.hi = q * (2 * P.hi) := by
    dsimp [boundedContourDivisor, twoPiIRect, ComplexRatInterval.smulRat, q, P]
    simp [RatInterval.point, RatInterval.mul, min_eq_left, max_eq_right,
      hq.le, hPlo.le, P.lo_le_hi]
    ring
    exact Or.inl (by simpa [P] using P.lo_le_hi)
  have himlo0 :
      (boundedContourDivisor count 0).im.lo = q * (2 * P0.lo) := by
    dsimp [boundedContourDivisor, twoPiIRect, ComplexRatInterval.smulRat, q, P0]
    simp [RatInterval.point, RatInterval.mul, min_eq_left, max_eq_right,
      hq.le, hP0lo.le, P0.lo_le_hi]
    ring
    exact Or.inl (by simpa [P0] using P0.lo_le_hi)
  have himhi0 :
      (boundedContourDivisor count 0).im.hi = q * (2 * P0.hi) := by
    dsimp [boundedContourDivisor, twoPiIRect, ComplexRatInterval.smulRat, q, P0]
    simp [RatInterval.point, RatInterval.mul, min_eq_left, max_eq_right,
      hq.le, hP0lo.le, P0.lo_le_hi]
    ring
    exact Or.inl (by simpa [P0] using P0.lo_le_hi)
  have hre : (boundedContourDivisor count precision).re = RatInterval.point 0 := by
    ext <;> simp [boundedContourDivisor, twoPiIRect,
      ComplexRatInterval.smulRat, RatInterval.point, RatInterval.mul]
  have hre0 : (boundedContourDivisor count 0).re = RatInterval.point 0 := by
    ext <;> simp [boundedContourDivisor, twoPiIRect,
      ComplexRatInterval.smulRat, RatInterval.point, RatInterval.mul]
  have himlo_nonneg : 0 ≤ q * (2 * P.lo) :=
    mul_nonneg hq.le (mul_nonneg (by norm_num) hPlo.le)
  have himhi_nonneg : 0 ≤ q * (2 * P.hi) :=
    mul_nonneg hq.le (mul_nonneg (by norm_num) hPhi)
  have himlo0_nonneg : 0 ≤ q * (2 * P0.lo) :=
    mul_nonneg hq.le (mul_nonneg (by norm_num) hP0lo.le)
  have himhi0_nonneg : 0 ≤ q * (2 * P0.hi) :=
    mul_nonneg hq.le (mul_nonneg (by norm_num) hP0hi)
  have himlo_pos : 0 < q * (2 * P.lo) :=
    mul_pos hq (mul_pos (by norm_num) hPlo)
  have himlo0_pos : 0 < q * (2 * P0.lo) :=
    mul_pos hq (mul_pos (by norm_num) hP0lo)
  have hnot_imhi_neg : ¬ q * (2 * P.hi) < 0 := not_lt_of_ge himhi_nonneg
  have hnot_imhi0_neg : ¬ q * (2 * P0.hi) < 0 := not_lt_of_ge himhi0_nonneg
  constructor
  · rw [ComplexRatInterval.maxAbs, ComplexRatInterval.maxAbs, hre, hre0]
    simp [RatInterval.point, RatInterval.maxAbs, himlo, himhi, himlo0, himhi0,
      abs_of_nonneg himlo_nonneg, abs_of_nonneg himhi_nonneg,
      abs_of_nonneg himlo0_nonneg, abs_of_nonneg himhi0_nonneg]
    exact Or.inr (Or.inr ⟨himhi0_nonneg,
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (P.lo_le_hi.trans hP.2) htwo) hq.le,
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hP.2 htwo) hq.le⟩)
  constructor
  · rw [ComplexRatInterval.normSq, ComplexRatInterval.normSq, hre, hre0]
    simp [RatInterval.point, RatInterval.sq, RatInterval.add, himlo, himhi,
      himlo0, himhi0, himlo_pos, himlo0_pos, hnot_imhi_neg, hnot_imhi0_neg]
    nlinarith [mul_self_le_mul_self
      (mul_nonneg hq.le (mul_nonneg htwo hP0lo.le))
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hP.1 htwo) hq.le)]
  · rw [ComplexRatInterval.width, hre]
    simp [RatInterval.point, RatInterval.width, himlo, himhi]
    constructor
    · simpa [P] using P.lo_le_hi
    · have heq : q * (2 * P.hi) =
          2 * q * (P.hi - P.lo) + q * (2 * P.lo) := by ring
      simpa [q, P] using heq.le

set_option maxHeartbeats 2400000 in
private lemma winding_post_arithmetic
    {R C A S l r t e b : ℚ}
    (hR : 0 ≤ R) (hC : 0 ≤ C) (hA : 0 ≤ A) (hl : 0 < l)
    (hr : 0 < r) (hr1 : r ≤ 1) (ht0 : 0 < t) (hb : 0 < b) (hb1 : b ≤ 1)
    (hCA : C ^ 2 ≤ A)
    (hguard : r ≤ b * l ^ 2 / (1 + l) ^ 2)
    (hscale : 256 * (1 + R) * (1 + A) ^ 2 *
      (1 + l⁻¹ + l⁻¹ ^ 2) ≤ S)
    (ht : 64 * S * t = r ^ 2) (he : 16 * e = t ^ 2) :
    let M := C + 1
    let T := 36 * R * (1 + e)
    let tw := 2 * (9 * t + 4 * R * (1 + e) * t)
    let δ := l ^ 2 / 4
    let W := 2 * ((2 * M ^ 2 / δ) * tw +
      T * (8 * M ^ 3 * (M * t) / δ ^ 2 + 4 * M * (M * t) / δ))
    let H := R * C / (16 * l)
    1300 * (H + W + t / 3) * t + 18 * (W + t / 3) < 4 * b := by
  dsimp only
  let M : ℚ := C + 1
  let T : ℚ := 36 * R * (1 + e)
  let tw : ℚ := 2 * (9 * t + 4 * R * (1 + e) * t)
  let δ : ℚ := l ^ 2 / 4
  let W : ℚ := 2 * ((2 * M ^ 2 / δ) * tw +
    T * (8 * M ^ 3 * (M * t) / δ ^ 2 + 4 * M * (M * t) / δ))
  let H : ℚ := R * C / (16 * l)
  let J : ℚ := 576 * (1 + A) / l ^ 2 + 2720 * R * (1 + A) / l ^ 2 +
    39168 * R * (1 + A) ^ 2 / l ^ 4
  change 1300 * (H + W + t / 3) * t + 18 * (W + t / 3) < 4 * b
  have hS256 : 256 ≤ S := by
    have hf : 1 ≤ 1 + l⁻¹ + l⁻¹ ^ 2 := by
      have hi : 0 ≤ l⁻¹ := inv_nonneg.mpr hl.le
      nlinarith [sq_nonneg l⁻¹]
    have ha1 : 1 ≤ (1 + A) ^ 2 := by nlinarith [sq_nonneg A]
    have hR1 : 1 ≤ 1 + R := by linarith
    calc
      256 = 256 * 1 * 1 * 1 := by ring
      _ ≤ 256 * (1 + R) * (1 + A) ^ 2 *
          (1 + l⁻¹ + l⁻¹ ^ 2) := by gcongr
      _ ≤ S := hscale
  have hrb : r < b := by
    have hgap : 0 < (1 + l) ^ 2 - l ^ 2 := by nlinarith
    have hfrac : b * l ^ 2 / (1 + l) ^ 2 < b := by
      apply (div_lt_iff₀ (show 0 < (1 + l) ^ 2 by positivity)).2
      nlinarith [mul_pos hb hgap]
    exact hguard.trans_lt hfrac
  have hrr : r ^ 2 ≤ r := by
    nlinarith [mul_nonneg hr.le (sub_nonneg.mpr hr1)]
  have htb : 16384 * t < b := by
    have hmul := mul_le_mul_of_nonneg_right hS256
      (show (0 : ℚ) ≤ 64 * t by positivity)
    nlinarith [ht, hrr, hrb]
  have ht1 : t < 1 := by nlinarith [htb, hb1]
  have he0 : 0 ≤ e := by nlinarith [he, sq_nonneg t]
  have he16 : 16 * e ≤ 1 := by nlinarith [he, mul_nonneg ht0.le (sub_nonneg.mpr ht1.le)]
  have hWJ : W ≤ t * J := by
    simpa only [W, J, M, T, tw, δ] using
      postArith_W_bound hR hC hA hl ht0.le he0 he16 hCA
  have hJb : t * J ≤ (42464 / (64 * 256 * 16)) * b := by
    simpa only [J] using
      postArith_tJ_bound hR hA hl hr ht0 hb hb1 hguard hscale ht
  have hWb : W ≤ (42464 / (64 * 256 * 16)) * b := hWJ.trans hJb
  have hHt : H * t ≤ b / (1024 * 256) := by
    simpa only [H] using
      postArith_Ht_bound hR hC hA hl hr ht0 hb hb1 hCA hguard hscale ht
  have hW0 : 0 ≤ W := by dsimp [W, M, T, tw, δ]; positivity
  have hB0 : 0 ≤ (42464 / (64 * 256 * 16) : ℚ) := by norm_num
  have htUnit : t < 1 / 16384 := by nlinarith [htb, hb]
  have hWt : W * t ≤ ((42464 / (64 * 256 * 16)) * b) / 16384 := by
    have hm := mul_le_mul_of_nonneg_left htUnit.le hW0
    nlinarith [hm, hWb, mul_pos hb (by norm_num : (0 : ℚ) < 42464 / (64 * 256 * 16))]
  have htt : t * t < b / (16384 * 16384) := by
    have h1 := mul_lt_mul_of_pos_left htUnit ht0
    have h2 := mul_lt_mul_of_pos_right (show t < b / 16384 by nlinarith [htb])
      (by norm_num : (0 : ℚ) < 1 / 16384)
    nlinarith [h1, h2]
  have hcap :
      18 * (42464 / (64 * 256 * 16)) +
        1300 * (42464 / (64 * 256 * 16)) / 16384 +
        1300 / (1024 * 256) + 1300 / (3 * 16384 * 16384) +
        6 / 16384 < (4 : ℚ) := by norm_num
  nlinarith [hWb, hWt, hHt, htt, htb,
    mul_nonneg ht0.le hW0, mul_nonneg ht0.le ht0.le,
    mul_nonneg hB0 hb.le]

private lemma evaluation_contour_value_norm_bound_fullBox
    (input : RepresentedSpectralInput p) (pStar : CertifiedBankInputs p)
    (hcanonical : CanonicalRepresentedSpectralInput Xspace input)
    (j : Fin ((contourBank p pStar).JBase + 1)) (N : ℕ) (lower : PosRat)
    (hlower : lower.1 = (pilotModulus input (contourBank p pStar) 1 j).lo) :
    let B := contourBank p pStar
    let ev := spectralEvaluationEvaluator input B j N lower
    let QF := empiricalFWidthBound input (spectralFullBoxRadius B) 0
    let QG := empiricalGWidthBound input (spectralFullBoxRadius B) 0
    let C := max (128 * QF) (256 * QG)
    let R := radiusSlackUpper B j
    let H := R * C / (16 * lower.1)
    ‖CircleMesh.circleContourIntegral
      (fun z ↦ ev.numerator.value z / ev.denominator.value z)
      0 ev.radius.value‖ ≤ (H : ℝ) := by
  dsimp only
  let B := contourBank p pStar
  let ev := spectralEvaluationEvaluator input B j N lower
  let QF := empiricalFWidthBound input (spectralFullBoxRadius B) 0
  let QG := empiricalGWidthBound input (spectralFullBoxRadius B) 0
  let C := max (128 * QF) (256 * QG)
  let R := radiusSlackUpper B j
  let H := R * C / (16 * lower.1)
  have hFQ := empiricalGDerivativeBound_zero_le_widthBound input
    (spectralFullBoxRadius B) (spectralFullBoxRadius_nonneg B)
  have hQG256 : 256 * QG ≤ C := le_max_right _ _
  have hDG0 : 0 ≤ empiricalGDerivativeBound input (spectralFullBoxRadius B) 0 :=
    empiricalGDerivativeBound_nonneg input (spectralFullBoxRadius B) 0
  have hder : empiricalGDerivativeBound input (spectralFullBoxRadius B) 0 ≤ C / 128 := by
    nlinarith [hFQ, hQG256, hDG0]
  have hCdiv0 : 0 ≤ C / 128 :=
    (empiricalGDerivativeBound_nonneg input (spectralFullBoxRadius B) 0).trans hder
  have hdenLower : ∀ u ∈ Set.Icc (0 : ℝ) 1, (lower.1 : ℝ) ≤
      ‖ev.denominator.value (CircleMesh.circleMap 0 ev.radius.value u)‖ := by
    intro u hu
    rw [hlower]
    exact pilotModulus_lo_le_denominator_norm input pStar hcanonical 1 j u hu
  unfold CircleMesh.circleContourIntegral
  have hpoint : ∀ u ∈ Set.uIoc (0 : ℝ) 1,
      ‖CircleMesh.circleIntegrand
        (fun z ↦ ev.numerator.value z / ev.denominator.value z)
        0 ev.radius.value u‖ ≤ (H : ℝ) := by
    intro u hu
    have hr0 : 0 ≤ ev.radius.value := by
      exact (show (0 : ℝ) ≤ B.rho j by
        exact_mod_cast (contourBank_rho_pos_le_UR p pStar j).1.le)
    have hrUR : ev.radius.value ≤ (B.UR : ℝ) := by
      exact (show B.rho j ≤ (B.UR : ℝ) by
        exact_mod_cast (contourBank_rho_pos_le_UR p pStar j).2)
    have hURfull : (B.UR : ℚ) ≤ spectralFullBoxRadius B :=
      contourBank_UR_le_spectralFullBoxRadius B
    have hz : ‖CircleMesh.circleMap 0 ev.radius.value u‖ ≤
        (spectralFullBoxRadius B : ℝ) := by
      simpa [CircleMesh.circleMap, Complex.norm_exp, abs_of_nonneg hr0] using
        hrUR.trans (by exact_mod_cast hURfull)
    have hnum := spectralNumeratorMap_norm_le input B (spectralFold p.n 1) 0
      (spectralFullBoxRadius_nonneg B) hz
    have huIcc : u ∈ Set.Icc (0 : ℝ) 1 := by
      rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hu
      exact ⟨hu.1.le, hu.2⟩
    have hden := hdenLower u huIcc
    have hdenPos : 0 < ‖ev.denominator.value
        (CircleMesh.circleMap 0 ev.radius.value u)‖ := by
      have hlowerPosR : (0 : ℝ) < lower.1 := by exact_mod_cast lower.2
      exact hlowerPosR.trans_le hden
    have hquot : ‖ev.numerator.value
        (CircleMesh.circleMap 0 ev.radius.value u) /
        ev.denominator.value (CircleMesh.circleMap 0 ev.radius.value u)‖ ≤
        (C / 128 : ℚ) / lower.1 := by
      rw [norm_div]
      exact div_le_div₀ (by exact_mod_cast hCdiv0)
        (hnum.trans (by exact_mod_cast hder))
        (by exact_mod_cast lower.2) hden
    have htan := circleTangent_norm_le ev.radius.value hr0 u
    have hrR : ev.radius.value ≤ (R : ℝ) := by
      have hvru := certifiedRadius_value_le_radiusUpper B j
      have hruR : radiusUpper B j ≤ R := by
        dsimp [R, radiusSlackUpper]
        linarith
      exact hvru.trans (by exact_mod_cast hruR)
    have hquotUpper0 : 0 ≤ (((C / 128 : ℚ) : ℝ) / lower.1) := by
      apply div_nonneg
      · exact_mod_cast hCdiv0
      · exact_mod_cast lower.2.le
    rw [CircleMesh.circleIntegrand, norm_mul]
    calc
      _ ≤ (((C / 128 : ℚ) : ℝ) / lower.1) * (8 * ev.radius.value) :=
        mul_le_mul hquot htan (norm_nonneg _)
          hquotUpper0
      _ ≤ (((C / 128 : ℚ) : ℝ) / lower.1) * (8 * R) := by gcongr
      _ = H := by dsimp [H]; push_cast; ring
  push_cast
  simpa [B, ev, H, R, C, QF, QG] using
    (intervalIntegral.norm_integral_le_of_norm_le_const hpoint)

private lemma winding_contour_value_norm_bound_fullBox
    (input : RepresentedSpectralInput p) (pStar : CertifiedBankInputs p)
    (hcanonical : CanonicalRepresentedSpectralInput Xspace input)
    (j : Fin ((contourBank p pStar).JBase + 1)) (lower : PosRat)
    (hlower : lower.1 = (pilotModulus input (contourBank p pStar) 0 j).lo) :
    let B := contourBank p pStar
    let ev := spectralWindingEvaluator input B j lower
    let Q0 := empiricalFWidthBound input (spectralFullBoxRadius B) 0
    let Q1 := empiricalFWidthBound input (spectralFullBoxRadius B) 1
    let C := max (128 * Q0) (128 * Q1)
    let R := radiusSlackUpper B j
    let H := R * C / (16 * lower.1)
    ‖CircleMesh.circleContourIntegral
      (fun z ↦ ev.numerator.value z / ev.denominator.value z)
      0 ev.radius.value‖ ≤ (H : ℝ) := by
  dsimp only
  let B := contourBank p pStar
  let ev := spectralWindingEvaluator input B j lower
  let Q0 := empiricalFWidthBound input (spectralFullBoxRadius B) 0
  let Q1 := empiricalFWidthBound input (spectralFullBoxRadius B) 1
  let C := max (128 * Q0) (128 * Q1)
  let R := radiusSlackUpper B j
  let H := R * C / (16 * lower.1)
  have hFQ := empiricalFDerivativeBound_one_le_widthBound input
    (spectralFullBoxRadius B) (spectralFullBoxRadius_nonneg B)
  have hQ128 : 128 * Q1 ≤ C := le_max_right _ _
  have hder : empiricalFDerivativeBound input (spectralFullBoxRadius B) 1 ≤ C / 128 := by
    nlinarith [hFQ]
  have hCdiv0 : 0 ≤ C / 128 :=
    (empiricalFDerivativeBound_nonneg input (spectralFullBoxRadius B) 1).trans hder
  have hdenLower : ∀ u ∈ Set.Icc (0 : ℝ) 1, (lower.1 : ℝ) ≤
      ‖ev.denominator.value (CircleMesh.circleMap 0 ev.radius.value u)‖ := by
    intro u hu
    rw [hlower]
    exact pilotModulus_lo_le_denominator_norm input pStar hcanonical 0 j u hu
  unfold CircleMesh.circleContourIntegral
  have hpoint : ∀ u ∈ Set.uIoc (0 : ℝ) 1,
      ‖CircleMesh.circleIntegrand
        (fun z ↦ ev.numerator.value z / ev.denominator.value z)
        0 ev.radius.value u‖ ≤ (H : ℝ) := by
    intro u hu
    have hr0 : 0 ≤ ev.radius.value := by
      exact (show (0 : ℝ) ≤ B.rho j by
        exact_mod_cast (contourBank_rho_pos_le_UR p pStar j).1.le)
    have hrUR : ev.radius.value ≤ (B.UR : ℝ) := by
      exact (show B.rho j ≤ (B.UR : ℝ) by
        exact_mod_cast (contourBank_rho_pos_le_UR p pStar j).2)
    have hURfull : (B.UR : ℚ) ≤ spectralFullBoxRadius B :=
      contourBank_UR_le_spectralFullBoxRadius B
    have hz : ‖CircleMesh.circleMap 0 ev.radius.value u‖ ≤
        (spectralFullBoxRadius B : ℝ) := by
      simpa [CircleMesh.circleMap, Complex.norm_exp, abs_of_nonneg hr0] using
        hrUR.trans (by exact_mod_cast hURfull)
    have hnum := spectralDenominatorMap_norm_le input B (spectralFold p.n 0) 1
      (spectralFullBoxRadius_nonneg B) hz
    have huIcc : u ∈ Set.Icc (0 : ℝ) 1 := by
      rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hu
      exact ⟨hu.1.le, hu.2⟩
    have hden := hdenLower u huIcc
    have hdenPos : 0 < ‖ev.denominator.value
        (CircleMesh.circleMap 0 ev.radius.value u)‖ := by
      have hlowerPosR : (0 : ℝ) < lower.1 := by exact_mod_cast lower.2
      exact hlowerPosR.trans_le hden
    have hquot : ‖ev.numerator.value
        (CircleMesh.circleMap 0 ev.radius.value u) /
        ev.denominator.value (CircleMesh.circleMap 0 ev.radius.value u)‖ ≤
        (C / 128 : ℚ) / lower.1 := by
      rw [norm_div]
      exact div_le_div₀ (by exact_mod_cast hCdiv0)
        (hnum.trans (by exact_mod_cast hder))
        (by exact_mod_cast lower.2) hden
    have htan := circleTangent_norm_le ev.radius.value hr0 u
    have hrR : ev.radius.value ≤ (R : ℝ) := by
      have hvru := certifiedRadius_value_le_radiusUpper B j
      have hruR : radiusUpper B j ≤ R := by
        dsimp [R, radiusSlackUpper]
        linarith
      exact hvru.trans (by exact_mod_cast hruR)
    have hquotUpper0 : 0 ≤ (((C / 128 : ℚ) : ℝ) / lower.1) := by
      apply div_nonneg
      · exact_mod_cast hCdiv0
      · exact_mod_cast lower.2.le
    rw [CircleMesh.circleIntegrand, norm_mul]
    calc
      _ ≤ (((C / 128 : ℚ) : ℝ) / lower.1) * (8 * ev.radius.value) :=
        mul_le_mul hquot htan (norm_nonneg _)
          hquotUpper0
      _ ≤ (((C / 128 : ℚ) : ℝ) / lower.1) * (8 * R) := by gcongr
      _ = H := by dsimp [H]; push_cast; ring
  push_cast
  simpa [B, ev, H, R, C, Q0, Q1] using
    (intervalIntegral.norm_integral_le_of_norm_le_const hpoint)

private lemma winding_schedule_C_sq_le_magnitude
    (input : RepresentedSpectralInput p) (B : ContourBankData)
    (j : Fin (B.JBase + 1)) (lower : PosRat) :
    let Q0 := empiricalFWidthBound input (spectralFullBoxRadius B) 0
    let Q1 := empiricalFWidthBound input (spectralFullBoxRadius B) 1
    let C := max (128 * Q0) (128 * Q1)
    let A := windingScheduleMagnitude input B j lower
    C ^ 2 ≤ A := by
  dsimp only
  let Q0 := empiricalFWidthBound input (spectralFullBoxRadius B) 0
  let Q1 := empiricalFWidthBound input (spectralFullBoxRadius B) 1
  let C := max (128 * Q0) (128 * Q1)
  let A := windingScheduleMagnitude input B j lower
  change C ^ 2 ≤ A
  have hQ00 : 0 ≤ Q0 := empiricalFWidthBound_nonneg input
    (spectralFullBoxRadius B) 0 (spectralFullBoxRadius_nonneg B)
  have hQ10 : 0 ≤ Q1 := empiricalFWidthBound_nonneg input
    (spectralFullBoxRadius B) 1 (spectralFullBoxRadius_nonneg B)
  by_cases hQ : Q0 ≤ Q1
  · have hC : C = 128 * Q1 := by
      dsimp [C]
      rw [max_eq_right (mul_le_mul_of_nonneg_left hQ (by norm_num))]
    rw [hC]
    exact ((pow_le_pow_left₀ (mul_nonneg (by norm_num) hQ10)
      (mul_le_mul_of_nonneg_left (le_max_right (1 : ℚ) Q1) (by norm_num)) 2)).trans
        ((rat_le_num_natAbs (by positivity)).trans (by
          let A0 : ℕ := ((128 * max 1 Q0).num ^ (2 : ℕ)).natAbs
          let A1 : ℕ := ((128 * max 1 Q1).num ^ (2 : ℕ)).natAbs
          change (A1 : ℚ) ≤ (max A0 A1 : ℕ)
          exact_mod_cast (le_max_right A0 A1)))
  · have hQ' : Q1 ≤ Q0 := le_of_not_ge hQ
    have hC : C = 128 * Q0 := by
      dsimp [C]
      rw [max_eq_left (mul_le_mul_of_nonneg_left hQ' (by norm_num))]
    rw [hC]
    exact ((pow_le_pow_left₀ (mul_nonneg (by norm_num) hQ00)
      (mul_le_mul_of_nonneg_left (le_max_right (1 : ℚ) Q0) (by norm_num)) 2)).trans
        ((rat_le_num_natAbs (by positivity)).trans (by
          let A0 : ℕ := ((128 * max 1 Q0).num ^ (2 : ℕ)).natAbs
          let A1 : ℕ := ((128 * max 1 Q1).num ^ (2 : ℕ)).natAbs
          change (A0 : ℚ) ≤ (max A0 A1 : ℕ)
          exact_mod_cast (le_max_left A0 A1)))

private lemma evaluation_schedule_C_sq_le_magnitude
    (input : RepresentedSpectralInput p) (B : ContourBankData)
    (j : Fin (B.JBase + 1)) (N : ℕ) (lower : PosRat) :
    let QF := empiricalFWidthBound input (spectralFullBoxRadius B) 0
    let QG := empiricalGWidthBound input (spectralFullBoxRadius B) 0
    let C := max (128 * QF) (256 * QG)
    let A := evaluationScheduleMagnitude input B j N lower
    C ^ 2 ≤ A := by
  dsimp only
  let QF := empiricalFWidthBound input (spectralFullBoxRadius B) 0
  let QG := empiricalGWidthBound input (spectralFullBoxRadius B) 0
  let C := max (128 * QF) (256 * QG)
  let A := evaluationScheduleMagnitude input B j N lower
  change C ^ 2 ≤ A
  have hQF0 : 0 ≤ QF := empiricalFWidthBound_nonneg input
    (spectralFullBoxRadius B) 0 (spectralFullBoxRadius_nonneg B)
  have hQG0 : 0 ≤ QG := empiricalGWidthBound_nonneg input
    (spectralFullBoxRadius B) 0 (spectralFullBoxRadius_nonneg B)
  by_cases hQ : 128 * QF ≤ 256 * QG
  · have hC : C = 256 * QG := by
      dsimp [C]
      rw [max_eq_right hQ]
    rw [hC]
    exact ((pow_le_pow_left₀ (mul_nonneg (by norm_num) hQG0)
      (mul_le_mul_of_nonneg_left (le_max_right (1 : ℚ) QG) (by norm_num)) 2)).trans
        ((rat_le_num_natAbs (by positivity)).trans (by
          let AF : ℕ := ((128 * max 1 QF).num ^ (2 : ℕ)).natAbs
          let AG : ℕ := ((256 * max 1 QG).num ^ (2 : ℕ)).natAbs
          change (AG : ℚ) ≤ (max AF AG : ℕ)
          exact_mod_cast (le_max_right AF AG)))
  · have hQ' : 256 * QG ≤ 128 * QF := le_of_not_ge hQ
    have hC : C = 128 * QF := by
      dsimp [C]
      rw [max_eq_left hQ']
    rw [hC]
    exact ((pow_le_pow_left₀ (mul_nonneg (by norm_num) hQF0)
      (mul_le_mul_of_nonneg_left (le_max_right (1 : ℚ) QF) (by norm_num)) 2)).trans
        ((rat_le_num_natAbs (by positivity)).trans (by
          let AF : ℕ := ((128 * max 1 QF).num ^ (2 : ℕ)).natAbs
          let AG : ℕ := ((256 * max 1 QG).num ^ (2 : ℕ)).natAbs
          change (AF : ℚ) ≤ (max AF AG : ℕ)
          exact_mod_cast (le_max_left AF AG)))

private lemma winding_spectralNodeScale_lower
    (input : RepresentedSpectralInput p) (B : ContourBankData)
    (j : Fin (B.JBase + 1)) (lower : PosRat) :
    let A := windingScheduleMagnitude input B j lower
    let R := radiusSlackUpper B j
    let S := spectralNodeScale B j A lower 1
      (spectralNodeOperationCount .winding (spectralFold p.n 0).card)
    256 * (1 + R) * (1 + A) ^ 2 *
      (1 + lower.1⁻¹ + lower.1⁻¹ ^ 2) ≤ S := by
  dsimp only
  let A := windingScheduleMagnitude input B j lower
  let R := radiusSlackUpper B j
  let S := spectralNodeScale B j A lower 1
    (spectralNodeOperationCount .winding (spectralFold p.n 0).card)
  change 256 * (1 + R) * (1 + A) ^ 2 *
    (1 + lower.1⁻¹ + lower.1⁻¹ ^ 2) ≤ S
  have hA0 : 0 ≤ A := windingScheduleMagnitude_nonneg input B j lower
  have hR0 : 0 ≤ R := by dsimp [R, radiusSlackUpper]; linarith [radiusUpper_nonneg B j]
  dsimp [S, spectralNodeScale]
  apply le_max_of_le_right
  rw [max_eq_right hR0, max_eq_right hA0]
  have hop : (1 : ℚ) ≤
      spectralNodeOperationCount .winding (spectralFold p.n 0).card + 1 := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
  have hnorm : 1 ≤ spectralNormalizationAmplification 1 := by
    unfold spectralNormalizationAmplification
    dsimp only
    have hc : (0 : ℚ) ≤ max (1 : ℚ) 1 := le_max_of_le_right (by norm_num)
    have hmax : 0 ≤ (boundedContourDivisor 1 0).maxAbs :=
      (abs_nonneg _).trans ((le_max_left _ _).trans (le_max_left _ _))
    have hinv : 0 ≤ |(boundedContourDivisor 1 0).normSq.lo|⁻¹ :=
      inv_nonneg.mpr (abs_nonneg _)
    nlinarith [sq_nonneg |(boundedContourDivisor 1 0).normSq.lo|⁻¹]
  have hbase : 0 ≤ 256 * (1 + R) * (1 + A) ^ 2 *
      (1 + lower.1⁻¹ + lower.1⁻¹ ^ 2) := by
    have hR1 : 0 ≤ 1 + R := by linarith
    have hi : 0 ≤ lower.1⁻¹ := inv_nonneg.mpr lower.2.le
    have hf : 0 ≤ 1 + lower.1⁻¹ + lower.1⁻¹ ^ 2 := by
      nlinarith [sq_nonneg lower.1⁻¹]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hR1) (sq_nonneg _)) hf
  calc
    _ = 1 * (256 * (1 + R) * (1 + A) ^ 2 *
        (1 + lower.1⁻¹ + lower.1⁻¹ ^ 2)) * 1 := by ring
    _ ≤ (spectralNodeOperationCount .winding (spectralFold p.n 0).card + 1) *
        (256 * (1 + R) * (1 + A) ^ 2 *
          (1 + lower.1⁻¹ + lower.1⁻¹ ^ 2)) *
          spectralNormalizationAmplification 1 := by gcongr
    _ = _ := by ring_nf

private lemma evaluation_spectralNodeScale_lower
    (input : RepresentedSpectralInput p) (B : ContourBankData)
    (j : Fin (B.JBase + 1)) (N : ℕ) (lower : PosRat) :
    let A := evaluationScheduleMagnitude input B j N lower
    let R := radiusSlackUpper B j
    let S := spectralNodeScale B j A lower (max N 1)
      (spectralNodeOperationCount .evaluation (spectralFold p.n 1).card)
    256 * (1 + R) * (1 + A) ^ 2 *
      (1 + lower.1⁻¹ + lower.1⁻¹ ^ 2) ≤ S := by
  dsimp only
  let A := evaluationScheduleMagnitude input B j N lower
  let R := radiusSlackUpper B j
  let S := spectralNodeScale B j A lower (max N 1)
    (spectralNodeOperationCount .evaluation (spectralFold p.n 1).card)
  change 256 * (1 + R) * (1 + A) ^ 2 *
    (1 + lower.1⁻¹ + lower.1⁻¹ ^ 2) ≤ S
  have hA0 : 0 ≤ A := evaluationScheduleMagnitude_nonneg input B j N lower
  have hR0 : 0 ≤ R := by dsimp [R, radiusSlackUpper]; linarith [radiusUpper_nonneg B j]
  dsimp [S, spectralNodeScale]
  apply le_max_of_le_right
  rw [max_eq_right hR0, max_eq_right hA0]
  have hop : (1 : ℚ) ≤
      spectralNodeOperationCount .evaluation (spectralFold p.n 1).card + 1 := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
  have hnorm : 1 ≤ spectralNormalizationAmplification (max N 1) := by
    unfold spectralNormalizationAmplification
    dsimp only
    have hc : (0 : ℚ) ≤ max ((max N 1 : ℕ) : ℚ) 1 :=
      le_max_of_le_right (by norm_num)
    have hmax : 0 ≤ (boundedContourDivisor (max N 1) 0).maxAbs :=
      (abs_nonneg _).trans ((le_max_left _ _).trans (le_max_left _ _))
    have hinv : 0 ≤ |(boundedContourDivisor (max N 1) 0).normSq.lo|⁻¹ :=
      inv_nonneg.mpr (abs_nonneg _)
    nlinarith [sq_nonneg |(boundedContourDivisor (max N 1) 0).normSq.lo|⁻¹]
  have hbase : 0 ≤ 256 * (1 + R) * (1 + A) ^ 2 *
      (1 + lower.1⁻¹ + lower.1⁻¹ ^ 2) := by
    have hR1 : 0 ≤ 1 + R := by linarith
    have hi : 0 ≤ lower.1⁻¹ := inv_nonneg.mpr lower.2.le
    have hf : 0 ≤ 1 + lower.1⁻¹ + lower.1⁻¹ ^ 2 := by
      nlinarith [sq_nonneg lower.1⁻¹]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hR1) (sq_nonneg _)) hf
  calc
    _ = 1 * (256 * (1 + R) * (1 + A) ^ 2 *
        (1 + lower.1⁻¹ + lower.1⁻¹ ^ 2)) * 1 := by ring
    _ ≤ (spectralNodeOperationCount .evaluation (spectralFold p.n 1).card + 1) *
        (256 * (1 + R) * (1 + A) ^ 2 *
          (1 + lower.1⁻¹ + lower.1⁻¹ ^ 2)) *
          spectralNormalizationAmplification (max N 1) := by gcongr
    _ = _ := by ring_nf


private lemma winding_post_regroup {H W t : ℚ}
    (h : 1300 * (H + W + t / 3) * t + 18 * (W + t / 3) < 1 / 4) :
    1300 * (H + (W + t / 3)) * t + 18 * (W + t / 3) < 1 / 4 := by
  nlinarith

set_option maxHeartbeats 800000 in
private lemma winding_post_normalization_contract
    (input : RepresentedSpectralInput p) (pStar : CertifiedBankInputs p)
    (hcanonical : CanonicalRepresentedSpectralInput Xspace input)
    (j : Fin ((contourBank p pStar).JBase + 1)) (lower : PosRat)
    (hlower : lower.1 = (pilotModulus input (contourBank p pStar) 0 j).lo) :
    let B := contourBank p pStar
    let ev := spectralWindingEvaluator input B j lower
    PostNormalizationWidthContract (boundedContourEvaluate ev) 1 ev.piPrecision
      (1 / 4) := by
  dsimp only
  let B := contourBank p pStar
  let ev := spectralWindingEvaluator input B j lower
  let Q0 := empiricalFWidthBound input (spectralFullBoxRadius B) 0
  let Q1 := empiricalFWidthBound input (spectralFullBoxRadius B) 1
  let C := max (128 * Q0) (128 * Q1)
  let A := windingScheduleMagnitude input B j lower
  let R := radiusSlackUpper B j
  let r := (guardedNodeTolerance windingNodeTolerance lower).1
  let t := ev.schedule.tolerance.1
  let e := (spectralNodeTarget ev.schedule.tolerance).1
  let M := C + 1
  let T := 36 * R * (1 + e)
  let tw := 2 * (9 * t + 4 * R * (1 + e) * t)
  let δ := lower.1 ^ 2 / 4
  let W := 2 * ((2 * M ^ 2 / δ) * tw +
    T * (8 * M ^ 3 * (M * t) / δ ^ 2 + 4 * M * (M * t) / δ))
  let WI := W + t / 3
  let H := R * C / (16 * lower.1)
  let MI := H + WI
  let Irect := boundedContourEvaluate ev
  let D := boundedContourDivisor 1 ev.piPrecision
  have hvalid := spectralWindingEvaluator_valid input pStar hcanonical j lower hlower
  have hIw : Irect.width ≤ WI := by
    simpa [Irect, WI, W, B, ev, Q0, Q1, C, t, e, M, R, T, tw, δ] using
      winding_contour_width_bound input pStar hcanonical j lower hlower
  have hvalueNorm : ‖CircleMesh.circleContourIntegral
      (fun z ↦ ev.numerator.value z / ev.denominator.value z)
      0 ev.radius.value‖ ≤ (H : ℝ) := by
    simpa [B, ev, Q0, Q1, C, R, H] using
      winding_contour_value_norm_bound_fullBox input pStar hcanonical j lower hlower
  have hIcontains := boundedContourEvaluate_contains ev hvalid
  have hIA : Irect.maxAbs ≤ MI := by
    have hcoords : max
        |(CircleMesh.circleContourIntegral
          (fun z ↦ ev.numerator.value z / ev.denominator.value z)
          0 ev.radius.value).re|
        |(CircleMesh.circleContourIntegral
          (fun z ↦ ev.numerator.value z / ev.denominator.value z)
          0 ev.radius.value).im| ≤ (H : ℝ) :=
      max_le ((Complex.abs_re_le_norm _).trans hvalueNorm)
        ((Complex.abs_im_le_norm _).trans hvalueNorm)
    simpa [Irect, MI] using
      ComplexRatInterval.maxAbs_le_of_contains_width hIcontains hcoords hIw
  have hdiv := boundedContourDivisor_precision_bounds 1 ev.piPrecision
  have hDmax : D.maxAbs ≤ 9 := by
    exact hdiv.1.trans (by
      norm_num [D, boundedContourDivisor, twoPiIRect,
        ComplexRatInterval.smulRat, ComplexRatInterval.maxAbs,
        RatInterval.maxAbs, RatInterval.point, RatInterval.mul,
        Transcendental.piInterval, Transcendental.piRaw,
        Transcendental.atanRaw, Transcendental.atanPartial,
        Transcendental.atanError, RatInterval.add, RatInterval.sub,
        RatInterval.neg])
  have hDlo : 1 ≤ D.normSq.lo := by
    exact (by
      norm_num [D, boundedContourDivisor, twoPiIRect,
        ComplexRatInterval.smulRat, ComplexRatInterval.normSq,
        RatInterval.sq, RatInterval.add, RatInterval.point, RatInterval.mul,
        Transcendental.piInterval, Transcendental.piRaw,
        Transcendental.atanRaw, Transcendental.atanPartial,
        Transcendental.atanError, RatInterval.sub, RatInterval.neg] :
        (1 : ℚ) ≤ (boundedContourDivisor 1 0).normSq.lo).trans hdiv.2.1
  have hpi : (Transcendental.piInterval ev.piPrecision).width ≤ t := by
    let τ := circleInnerTolerance 1 (spectralNodeTarget ev.schedule.tolerance)
    have hp := Transcendental.piInterval_width τ
    have hprec : ev.piPrecision = Transcendental.piPrecision τ := by
      dsimp [ev, spectralWindingEvaluator, spectralSchedule, τ, circleInputPrecision]
    rw [hprec]
    refine hp.trans ?_
    have hmin := min_le_left
      ((spectralNodeTarget ev.schedule.tolerance).1 / (256 * (|(1 : ℚ)| + 1)))
      (1 / 1024)
    have heq : 16 * e = t ^ 2 := by dsimp [e, t, spectralNodeTarget]; ring
    have ht1 : t ≤ 1 := by
      have hreq := guardedNodeTolerance_le_one windingNodeTolerance lower
        (by norm_num [windingNodeTolerance])
      let S := spectralNodeScale B j A lower 1
        (spectralNodeOperationCount .winding (spectralFold p.n 0).card)
      have hS1 : 1 ≤ S := by dsimp [S, spectralNodeScale]; exact le_max_left _ _
      have hteq : 64 * S * t = r ^ 2 := by
        exact estimatorNodePrecision_scale_eq (guardedNodeTolerance windingNodeTolerance lower)
          S hS1
      have hr1 : r ≤ 1 := by simpa [r] using hreq
      have hr0 : 0 < r := by
        dsimp [r]
        exact (guardedNodeTolerance windingNodeTolerance lower).2
      have ht0' : 0 < t := by dsimp [t]; exact ev.schedule.tolerance.2
      nlinarith [mul_nonneg hr0.le (sub_nonneg.mpr hr1),
        mul_pos (mul_pos (by norm_num : (0 : ℚ) < 64) (lt_of_lt_of_le zero_lt_one hS1)) ht0']
    change min (e / (256 * (|(1 : ℚ)| + 1))) (1 / 1024) ≤ t
    calc
      _ ≤ e / (256 * (|(1 : ℚ)| + 1)) := min_le_left _ _
      _ ≤ t := by
        have ht0' : 0 < t := by dsimp [t]; exact ev.schedule.tolerance.2
        norm_num
        nlinarith [heq, mul_nonneg ht0'.le (sub_nonneg.mpr ht1)]
  have hpi2 : 2 * (Transcendental.piInterval ev.piPrecision).width ≤ 2 * t :=
    mul_le_mul_of_nonneg_left hpi (by norm_num : (0 : ℚ) ≤ 2)
  have hDw : D.width ≤ 2 * t := hdiv.2.2.trans (by
    simpa [D] using hpi2)
  have hDnw : D.normSq.width ≤ 72 * t := by
    rw [show D.normSq.width = D.re.sq.width + D.im.sq.width by
      simp [ComplexRatInterval.normSq, RatInterval.width_add]]
    have hre := ComplexRatInterval.rat_sq_width_le D.re
    have him := ComplexRatInterval.rat_sq_width_le D.im
    have hreA : D.re.maxAbs ≤ 9 := (le_max_left _ _).trans hDmax
    have himA : D.im.maxAbs ≤ 9 := (le_max_right _ _).trans hDmax
    have hrew : D.re.width ≤ 2 * t := (le_max_left _ _).trans hDw
    have himw : D.im.width ≤ 2 * t := (le_max_right _ _).trans hDw
    nlinarith [mul_le_mul hreA hrew (RatInterval.width_nonneg D.re) (by norm_num),
      mul_le_mul himA himw (RatInterval.width_nonneg D.im) (by norm_num)]
  have hC0 : 0 ≤ C := by
    dsimp [C, Q0]
    exact (mul_nonneg (by norm_num)
      (empiricalFWidthBound_nonneg input (spectralFullBoxRadius B) 0
        (spectralFullBoxRadius_nonneg B))).trans (le_max_left _ _)
  have hA0 : 0 ≤ A := windingScheduleMagnitude_nonneg input B j lower
  have hR0 : 0 ≤ R := by dsimp [R, radiusSlackUpper]; linarith [radiusUpper_nonneg B j]
  have hCA : C ^ 2 ≤ A := by
    simpa [Q0, Q1, C, A] using
      winding_schedule_C_sq_le_magnitude input B j lower
  let S := spectralNodeScale B j A lower 1
    (spectralNodeOperationCount .winding (spectralFold p.n 0).card)
  have hscale : 256 * (1 + R) * (1 + A) ^ 2 *
      (1 + lower.1⁻¹ + lower.1⁻¹ ^ 2) ≤ S := by
    simpa [A, R, S] using winding_spectralNodeScale_lower input B j lower
  have htEq : 64 * S * t = r ^ 2 := by
    have hS1 : 1 ≤ S := by dsimp [S, spectralNodeScale]; exact le_max_left _ _
    exact estimatorNodePrecision_scale_eq (guardedNodeTolerance windingNodeTolerance lower)
      S hS1
  have heEq : 16 * e = t ^ 2 := by dsimp [e, t, spectralNodeTarget]; ring
  have hguard : r ≤ (1 / 16 : ℚ) * lower.1 ^ 2 / (1 + lower.1) ^ 2 := by
    exact min_le_right _ _
  have harith := winding_post_arithmetic hR0 hC0 hA0 lower.2
    (guardedNodeTolerance windingNodeTolerance lower).2
    (guardedNodeTolerance_le_one windingNodeTolerance lower
      (by norm_num [windingNodeTolerance]))
    ev.schedule.tolerance.2 (by norm_num : (0 : ℚ) < 1 / 16)
    (by norm_num : (1 / 16 : ℚ) ≤ 1) hCA hguard hscale htEq heEq
  apply postNormalizationWidthContract_of_bounds Irect 1 ev.piPrecision (1 / 4) MI WI
    hIA hIw
  dsimp only
  have hIwidth0 : 0 ≤ Irect.width := by
    unfold ComplexRatInterval.width
    exact (RatInterval.width_nonneg Irect.re).trans (le_max_left _ _)
  have hMI0 : 0 ≤ MI := by
    have hWI0 := hIwidth0.trans hIw
    have hH0 : 0 ≤ H := by
      dsimp [H]
      exact div_nonneg (mul_nonneg hR0 hC0)
        (mul_nonneg (by norm_num) lower.2.le)
    dsimp [MI]
    positivity
  have hWI0 := hIwidth0.trans hIw
  have ht0 : 0 < t := by dsimp [t]; exact ev.schedule.tolerance.2
  have hterm1 : 2 * MI * D.maxAbs * D.normSq.width / D.normSq.lo ^ 2 ≤
      1296 * MI * t := by
    apply (div_le_iff₀ (by positivity : 0 < D.normSq.lo ^ 2)).2
    have hdSq : (1 : ℚ) ≤ D.normSq.lo ^ 2 := one_le_pow₀ hDlo
    nlinarith [mul_le_mul hDmax hDnw (RatInterval.width_nonneg D.normSq)
      (by norm_num : (0 : ℚ) ≤ 9),
      mul_le_mul_of_nonneg_left hdSq
        (mul_nonneg (mul_nonneg (by norm_num : (0 : ℚ) ≤ 2) hMI0) ht0.le)]
  have hterm2 : 2 * (MI * D.width + D.maxAbs * WI) / D.normSq.lo ≤
      4 * MI * t + 18 * WI := by
    apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hDlo)).2
    nlinarith [mul_le_mul hDw le_rfl hMI0 (by positivity),
      mul_le_mul hDmax le_rfl hWI0 (by norm_num),
      mul_le_mul_of_nonneg_left hDlo (by positivity : 0 ≤ 4 * MI * t + 18 * WI)]
  have harith' : 1300 * MI * t + 18 * WI < 1 / 4 := by
    have hh := harith
    dsimp only at hh
    norm_num at hh
    have hg := winding_post_regroup hh
    simpa only [MI, WI] using hg
  exact lt_of_le_of_lt (add_le_add hterm1 hterm2) (by nlinarith [harith'])


set_option maxRecDepth 2000 in
set_option maxHeartbeats 1600000 in
private lemma evaluation_post_normalization_contract
    (input : RepresentedSpectralInput p) (pStar : CertifiedBankInputs p)
    (hcanonical : CanonicalRepresentedSpectralInput Xspace input)
    (j : Fin ((contourBank p pStar).JBase + 1)) (N : ℕ) (lower : PosRat)
    (hlower : lower.1 = (pilotModulus input (contourBank p pStar) 1 j).lo) :
    let B := contourBank p pStar
    let ev := spectralEvaluationEvaluator input B j N lower
    PostNormalizationWidthContract (boundedContourEvaluate ev) (max N 1) ev.piPrecision
      (2 / (max p.n 1 : ℚ)) := by
  dsimp only
  let B := contourBank p pStar
  let ev := spectralEvaluationEvaluator input B j N lower
  let QF := empiricalFWidthBound input (spectralFullBoxRadius B) 0
  let QG := empiricalGWidthBound input (spectralFullBoxRadius B) 0
  let C := max (128 * QF) (256 * QG)
  let A := evaluationScheduleMagnitude input B j N lower
  let R := radiusSlackUpper B j
  let r := (guardedNodeTolerance (evaluationNodeTolerance p) lower).1
  let t := ev.schedule.tolerance.1
  let e := (spectralNodeTarget ev.schedule.tolerance).1
  let M := C + 1
  let T := 36 * R * (1 + e)
  let tw := 2 * (9 * t + 4 * R * (1 + e) * t)
  let δ := lower.1 ^ 2 / 4
  let W := 2 * ((2 * M ^ 2 / δ) * tw +
    T * (8 * M ^ 3 * (M * t) / δ ^ 2 + 4 * M * (M * t) / δ))
  let WI := W + t / 3
  let H := R * C / (16 * lower.1)
  let MI := H + WI
  let Irect := boundedContourEvaluate ev
  let D := boundedContourDivisor (max N 1) ev.piPrecision
  let q : ℚ := max (N : ℚ) 1
  have hq1 : 1 ≤ q := by dsimp [q]; exact le_max_right _ _
  have hq0 : 0 ≤ q := zero_le_one.trans hq1
  have hbase1 : (evaluationNodeTolerance p).1 ≤ 1 := by
    dsimp [evaluationNodeTolerance]
    have hn : (1 : ℚ) ≤ max (p.n : ℚ) 1 := le_max_right _ _
    rw [one_div]
    exact (inv_le_one₀ (by positivity : (0 : ℚ) < 2 * max (p.n : ℚ) 1)).2
      (by nlinarith)
  have hvalid := spectralEvaluationEvaluator_valid input pStar hcanonical j N lower hlower
  have hIw : Irect.width ≤ WI := by
    simpa [Irect, WI, W, B, ev, QF, QG, C, t, e, M, R, T, tw, δ] using
      evaluation_contour_width_bound input pStar hcanonical j N lower hlower
  have hvalueNorm : ‖CircleMesh.circleContourIntegral
      (fun z ↦ ev.numerator.value z / ev.denominator.value z)
      0 ev.radius.value‖ ≤ (H : ℝ) := by
    simpa [B, ev, QF, QG, C, R, H] using
      evaluation_contour_value_norm_bound_fullBox input pStar hcanonical j N lower hlower
  have hIcontains := boundedContourEvaluate_contains ev hvalid
  have hIA : Irect.maxAbs ≤ MI := by
    have hcoords : max
        |(CircleMesh.circleContourIntegral
          (fun z ↦ ev.numerator.value z / ev.denominator.value z)
          0 ev.radius.value).re|
        |(CircleMesh.circleContourIntegral
          (fun z ↦ ev.numerator.value z / ev.denominator.value z)
          0 ev.radius.value).im| ≤ (H : ℝ) :=
      max_le ((Complex.abs_re_le_norm _).trans hvalueNorm)
        ((Complex.abs_im_le_norm _).trans hvalueNorm)
    simpa [Irect, MI] using
      ComplexRatInterval.maxAbs_le_of_contains_width hIcontains hcoords hIw
  have hdiv := boundedContourDivisor_precision_bounds (max N 1) ev.piPrecision
  have hDmax : D.maxAbs ≤ 9 * q := by
    exact hdiv.1.trans (by
      norm_num [boundedContourDivisor, twoPiIRect,
        ComplexRatInterval.smulRat, ComplexRatInterval.maxAbs,
        RatInterval.maxAbs, RatInterval.point, RatInterval.mul,
        Transcendental.piInterval, Transcendental.piRaw,
        Transcendental.atanRaw, Transcendental.atanPartial,
        Transcendental.atanError, RatInterval.add, RatInterval.sub,
        RatInterval.neg, q, abs_of_nonneg hq0] <;> nlinarith [hq0])
  have hDlo : q ^ 2 ≤ D.normSq.lo := by
    let P0 := Transcendental.piInterval 0
    have hP0lo : 0 < P0.lo := by
      dsimp [P0]
      norm_num [Transcendental.piInterval, Transcendental.piRaw,
        Transcendental.atanRaw, Transcendental.atanPartial,
        Transcendental.atanError, RatInterval.mul, RatInterval.sub,
        RatInterval.add, RatInterval.neg, RatInterval.point]
    have hP0hi : 0 ≤ P0.hi := hP0lo.le.trans P0.lo_le_hi
    have hPmul : P0.lo * 2 ≤ P0.hi * 2 :=
      mul_le_mul_of_nonneg_right P0.lo_le_hi (by norm_num)
    have himlo0 : (boundedContourDivisor (max N 1) 0).im.lo =
        q * (2 * P0.lo) := by
      dsimp [boundedContourDivisor, twoPiIRect, ComplexRatInterval.smulRat]
      simp [RatInterval.point, RatInterval.mul, min_eq_left, max_eq_right,
        q, hq0, hP0lo.le, P0.lo_le_hi, min_eq_left hPmul, max_eq_right hPmul]
      ring
      exact Or.inl (by simpa [P0] using min_eq_left hPmul)
    have himhi0 : (boundedContourDivisor (max N 1) 0).im.hi =
        q * (2 * P0.hi) := by
      dsimp [boundedContourDivisor, twoPiIRect, ComplexRatInterval.smulRat]
      simp [RatInterval.point, RatInterval.mul, min_eq_left, max_eq_right,
        q, hq0, hP0lo.le, P0.lo_le_hi, min_eq_left hPmul, max_eq_right hPmul]
      ring
      exact Or.inl (by simpa [P0] using max_eq_right hPmul)
    have hre0 : (boundedContourDivisor (max N 1) 0).re = RatInterval.point 0 := by
      ext <;> simp [boundedContourDivisor, twoPiIRect,
        ComplexRatInterval.smulRat, RatInterval.point, RatInterval.mul]
    have himlo0_pos : 0 < q * (2 * P0.lo) :=
      mul_pos (zero_lt_one.trans_le hq1) (mul_pos (by norm_num) hP0lo)
    have hnot_imhi0_neg : ¬ q * (2 * P0.hi) < 0 :=
      not_lt_of_ge (mul_nonneg hq0 (mul_nonneg (by norm_num) hP0hi))
    have hformula : (boundedContourDivisor (max N 1) 0).normSq.lo =
        (q * (2 * P0.lo)) ^ 2 := by
      rw [ComplexRatInterval.normSq, hre0]
      simp [RatInterval.point, RatInterval.sq, RatInterval.add, himlo0, himhi0,
        himlo0_pos, hnot_imhi0_neg, pow_two]
    have hpunit : 1 ≤ 2 * P0.lo := by
      dsimp [P0]
      norm_num [Transcendental.piInterval, Transcendental.piRaw,
        Transcendental.atanRaw, Transcendental.atanPartial,
        Transcendental.atanError, RatInterval.mul, RatInterval.sub,
        RatInterval.add, RatInterval.neg, RatInterval.point]
    apply (show q ^ 2 ≤ (boundedContourDivisor (max N 1) 0).normSq.lo by
      rw [hformula]
      have hqmul : q ≤ q * (2 * P0.lo) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hpunit hq0
      nlinarith [mul_self_le_mul_self hq0 hqmul]).trans
    exact hdiv.2.1
  have hpi : (Transcendental.piInterval ev.piPrecision).width ≤ t := by
    let τ := circleInnerTolerance 1 (spectralNodeTarget ev.schedule.tolerance)
    have hp := Transcendental.piInterval_width τ
    have hprec : ev.piPrecision = Transcendental.piPrecision τ := by
      dsimp [ev, spectralEvaluationEvaluator, spectralSchedule, τ, circleInputPrecision]
    rw [hprec]
    refine hp.trans ?_
    have hmin := min_le_left
      ((spectralNodeTarget ev.schedule.tolerance).1 / (256 * (|(1 : ℚ)| + 1)))
      (1 / 1024)
    have heq : 16 * e = t ^ 2 := by dsimp [e, t, spectralNodeTarget]; ring
    have ht1 : t ≤ 1 := by
      have hreq := guardedNodeTolerance_le_one (evaluationNodeTolerance p) lower hbase1
      let S := spectralNodeScale B j A lower (max N 1)
        (spectralNodeOperationCount .evaluation (spectralFold p.n 1).card)
      have hS1 : 1 ≤ S := by dsimp [S, spectralNodeScale]; exact le_max_left _ _
      have hteq : 64 * S * t = r ^ 2 := by
        exact estimatorNodePrecision_scale_eq
          (guardedNodeTolerance (evaluationNodeTolerance p) lower) S hS1
      have hr1 : r ≤ 1 := by simpa [r] using hreq
      have hr0 : 0 < r := by
        dsimp [r]
        exact (guardedNodeTolerance (evaluationNodeTolerance p) lower).2
      have ht0' : 0 < t := by dsimp [t]; exact ev.schedule.tolerance.2
      nlinarith [mul_nonneg hr0.le (sub_nonneg.mpr hr1),
        mul_pos (mul_pos (by norm_num : (0 : ℚ) < 64) (lt_of_lt_of_le zero_lt_one hS1)) ht0']
    change min (e / (256 * (|(1 : ℚ)| + 1))) (1 / 1024) ≤ t
    calc
      _ ≤ e / (256 * (|(1 : ℚ)| + 1)) := min_le_left _ _
      _ ≤ t := by
        have ht0' : 0 < t := by dsimp [t]; exact ev.schedule.tolerance.2
        norm_num
        nlinarith [heq, mul_nonneg ht0'.le (sub_nonneg.mpr ht1)]
  have hDw : D.width ≤ 2 * q * t := hdiv.2.2.trans (by
    have hmul := mul_le_mul_of_nonneg_left hpi
      (mul_nonneg (by norm_num : (0 : ℚ) ≤ 2) hq0)
    simpa [D, q, mul_assoc] using hmul)
  have hDnw : D.normSq.width ≤ 72 * q ^ 2 * t := by
    rw [show D.normSq.width = D.re.sq.width + D.im.sq.width by
      simp [ComplexRatInterval.normSq, RatInterval.width_add]]
    have hre := ComplexRatInterval.rat_sq_width_le D.re
    have him := ComplexRatInterval.rat_sq_width_le D.im
    have hreA : D.re.maxAbs ≤ 9 * q := (le_max_left _ _).trans hDmax
    have himA : D.im.maxAbs ≤ 9 * q := (le_max_right _ _).trans hDmax
    have hrew : D.re.width ≤ 2 * q * t := (le_max_left _ _).trans hDw
    have himw : D.im.width ≤ 2 * q * t := (le_max_right _ _).trans hDw
    nlinarith [mul_le_mul hreA hrew (RatInterval.width_nonneg D.re)
        (by positivity : (0 : ℚ) ≤ 9 * q),
      mul_le_mul himA himw (RatInterval.width_nonneg D.im)
        (by positivity : (0 : ℚ) ≤ 9 * q)]
  have hC0 : 0 ≤ C := by
    dsimp [C, QF]
    exact (mul_nonneg (by norm_num)
      (empiricalFWidthBound_nonneg input (spectralFullBoxRadius B) 0
        (spectralFullBoxRadius_nonneg B))).trans (le_max_left _ _)
  have hA0 : 0 ≤ A := evaluationScheduleMagnitude_nonneg input B j N lower
  have hR0 : 0 ≤ R := by dsimp [R, radiusSlackUpper]; linarith [radiusUpper_nonneg B j]
  have hCA : C ^ 2 ≤ A := by
    simpa [QF, QG, C, A] using
      evaluation_schedule_C_sq_le_magnitude input B j N lower
  let S := spectralNodeScale B j A lower (max N 1)
    (spectralNodeOperationCount .evaluation (spectralFold p.n 1).card)
  have hscale : 256 * (1 + R) * (1 + A) ^ 2 *
      (1 + lower.1⁻¹ + lower.1⁻¹ ^ 2) ≤ S := by
    simpa [A, R, S] using evaluation_spectralNodeScale_lower input B j N lower
  have htEq : 64 * S * t = r ^ 2 := by
    have hS1 : 1 ≤ S := by dsimp [S, spectralNodeScale]; exact le_max_left _ _
    exact estimatorNodePrecision_scale_eq
      (guardedNodeTolerance (evaluationNodeTolerance p) lower) S hS1
  have heEq : 16 * e = t ^ 2 := by dsimp [e, t, spectralNodeTarget]; ring
  have hguard : r ≤ (evaluationNodeTolerance p).1 * lower.1 ^ 2 /
      (1 + lower.1) ^ 2 := by
    exact min_le_right _ _
  have harith := winding_post_arithmetic hR0 hC0 hA0 lower.2
    (guardedNodeTolerance (evaluationNodeTolerance p) lower).2
    (guardedNodeTolerance_le_one (evaluationNodeTolerance p) lower hbase1)
    ev.schedule.tolerance.2 (evaluationNodeTolerance p).2
    hbase1 hCA hguard hscale htEq heEq
  apply postNormalizationWidthContract_of_bounds Irect (max N 1) ev.piPrecision
    (2 / (max p.n 1 : ℚ)) MI WI
    hIA hIw
  dsimp only
  have hIwidth0 : 0 ≤ Irect.width := by
    unfold ComplexRatInterval.width
    exact (RatInterval.width_nonneg Irect.re).trans (le_max_left _ _)
  have hMI0 : 0 ≤ MI := by
    have hWI0 := hIwidth0.trans hIw
    have hH0 : 0 ≤ H := by
      dsimp [H]
      exact div_nonneg (mul_nonneg hR0 hC0)
        (mul_nonneg (by norm_num) lower.2.le)
    dsimp [MI]
    positivity
  have hWI0 := hIwidth0.trans hIw
  have ht0 : 0 < t := by dsimp [t]; exact ev.schedule.tolerance.2
  have hqD : q ≤ D.normSq.lo := by
    have hqq : q ≤ q ^ 2 := by nlinarith [hq1, hq0]
    exact hqq.trans hDlo
  have hDlo0 : 0 < D.normSq.lo := (zero_lt_one.trans_le hq1).trans_le hqD
  have hterm1 : 2 * MI * D.maxAbs * D.normSq.width / D.normSq.lo ^ 2 ≤
      1296 * MI * t := by
    apply (div_le_iff₀ (sq_pos_of_pos hDlo0)).2
    have hprod : D.maxAbs * D.normSq.width ≤
        (9 * q) * (72 * q ^ 2 * t) :=
      mul_le_mul hDmax hDnw (RatInterval.width_nonneg D.normSq)
        (by positivity : (0 : ℚ) ≤ 9 * q)
    have hnum := mul_le_mul_of_nonneg_left hprod
      (mul_nonneg (by norm_num : (0 : ℚ) ≤ 2) hMI0)
    have hq3q4 : q ^ 3 ≤ q ^ 4 := by
      calc
        q ^ 3 = q ^ 3 * 1 := by ring
        _ ≤ q ^ 3 * q := mul_le_mul_of_nonneg_left hq1 (by positivity)
        _ = q ^ 4 := by ring
    have hdSq : q ^ 4 ≤ D.normSq.lo ^ 2 := by
      nlinarith [mul_self_le_mul_self (sq_nonneg q) hDlo]
    have hscaleD := mul_le_mul_of_nonneg_left (hq3q4.trans hdSq)
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℚ) ≤ 1296) hMI0) ht0.le)
    calc
      2 * MI * D.maxAbs * D.normSq.width =
          2 * MI * (D.maxAbs * D.normSq.width) := by ring
      _ ≤ 2 * MI * ((9 * q) * (72 * q ^ 2 * t)) := hnum
      _ = 1296 * MI * t * q ^ 3 := by ring
      _ ≤ 1296 * MI * t * D.normSq.lo ^ 2 := hscaleD
      _ = (1296 * MI * t) * D.normSq.lo ^ 2 := by ring
  have hterm2 : 2 * (MI * D.width + D.maxAbs * WI) / D.normSq.lo ≤
      4 * MI * t + 18 * WI := by
    apply (div_le_iff₀ hDlo0).2
    have hnum1 := mul_le_mul hDw le_rfl hMI0
      (by positivity : (0 : ℚ) ≤ 2 * q * t)
    have hnum2 := mul_le_mul hDmax le_rfl hWI0
      (by positivity : (0 : ℚ) ≤ 9 * q)
    have hrhs := mul_le_mul_of_nonneg_left hqD
      (by positivity : (0 : ℚ) ≤ 4 * MI * t + 18 * WI)
    have hadd := add_le_add hnum1 hnum2
    have htwo := mul_le_mul_of_nonneg_left hadd (by norm_num : (0 : ℚ) ≤ 2)
    calc
      2 * (MI * D.width + D.maxAbs * WI) ≤
          2 * (MI * (2 * q * t) + (9 * q) * WI) := by
        simpa [mul_comm] using htwo
      _ = (4 * MI * t + 18 * WI) * q := by ring
      _ ≤ (4 * MI * t + 18 * WI) * D.normSq.lo := hrhs
  have harith' : 1300 * MI * t + 18 * WI < 2 / (max p.n 1 : ℚ) := by
    have hh := harith
    dsimp only at hh
    have hrhs : 4 * (evaluationNodeTolerance p).1 =
        2 / max (p.n : ℚ) 1 := by
      norm_num [evaluationNodeTolerance, div_eq_mul_inv]
      ring
    rw [hrhs] at hh
    simpa [MI, WI, evaluationNodeTolerance, add_assoc] using hh
  exact lt_of_le_of_lt (add_le_add hterm1 hterm2) (by nlinarith [harith'])


/-- All paper-specific schedule facts are local consequences of the canonical
floor-dyadic input and the explicit schedule, never hypotheses or fields of
the generic build carrier. -/
def SpectralScheduleWitness (input : RepresentedSpectralInput p)
    (B : ContourBankData) : Prop :=
  (∀ (a : Fin 2) (j : Fin (B.JBase + 1)),
    let schedule := pilotSchedule input B a j
    let map := spectralDenominatorMap input B (spectralFold p.n a) 0
    let L := pilotCircleLipschitzBound input (radiusUpper B j)
    let amplification := pilotScheduleMagnitude input B j
    let unitWidth := (spectralNodeTarget schedule.tolerance).1
    let radiusPrecision := bankRadiusPrecision schedule.tolerance unitWidth
    ExactSpectralSchedule schedule amplification ∧ schedule.magnitude = L ∧ map.Valid ∧
      map.precision (spectralNodeTarget schedule.tolerance) ≤ schedule.fuel ∧
      radiusPrecision.1 ≤ 1 ∧
      ∀ k ≤ schedule.mesh,
        (spectralRadiusNode B j schedule k).Contains
          (CircleMesh.circleMap 0 (B.rho j) (CircleMesh.meshPoint schedule.mesh k)) ∧
        (spectralRadiusNode B j schedule k).Subinterval (spectralDiskBox B) ∧
        (bankRadiusRect (B.rhoName j) radiusPrecision).maxAbs ≤
          radiusSlackUpper B j ∧
        (spectralRadiusNode B j schedule k).width ≤
          2 * (radiusSlackUpper B j * unitWidth +
            (1 + unitWidth) * radiusPrecision.1) ∧
        (map.eval (spectralRadiusNode B j schedule k) schedule.fuel).width ≤
          map.derivativeEnvelope * (spectralRadiusNode B j schedule k).width +
            (spectralNodeTarget schedule.tolerance).1 ∧
        ((map.eval (spectralRadiusNode B j schedule k) schedule.fuel).normInterval
          schedule.fuel).width ≤ (pilotNodeTolerance B).1) ∧
  (∀ (j : Fin (B.JBase + 1)),
    let pilot := pilotModulus input B 0 j
    ∀ hpilot : 0 < pilot.lo,
      let lower : PosRat := ⟨pilot.lo, hpilot⟩
      let ev := spectralWindingEvaluator input B j lower
      let amplification := windingScheduleMagnitude input B j lower
      ExactSpectralSchedule ev.schedule amplification ∧
        ev.schedule.magnitude =
          windingLipschitzBound input (radiusUpper B j) lower.1 ∧ ev.Valid ∧
        ev.numerator.precision (spectralNodeTarget ev.schedule.tolerance) ≤ ev.mapFuel ∧
        ev.denominator.precision (spectralNodeTarget ev.schedule.tolerance) ≤ ev.mapFuel ∧
        PostNormalizationWidthContract (boundedContourEvaluate ev) 1 ev.piPrecision
          (1 / 4) ∧
        ∀ k ≤ ev.schedule.mesh,
          pilot.lo / 2 ≤
              ((ev.denominator.eval
                (certifiedRadiusNode ev.radius ev.radiusPrecision ev.schedule k)
                ev.mapFuel).normInterval ev.mapFuel).lo ∧
            (ev.denominator.eval
              (certifiedRadiusNode ev.radius ev.radiusPrecision ev.schedule k)
              ev.mapFuel).normSq.AwayFromZero ∧
            (ev.numerator.eval
              (certifiedRadiusNode ev.radius ev.radiusPrecision ev.schedule k)
              ev.mapFuel).width ≤ ev.numerator.derivativeEnvelope *
                (certifiedRadiusNode ev.radius ev.radiusPrecision ev.schedule k).width +
                (spectralNodeTarget ev.schedule.tolerance).1 ∧
            (ev.denominator.eval
              (certifiedRadiusNode ev.radius ev.radiusPrecision ev.schedule k)
              ev.mapFuel).width ≤ ev.denominator.derivativeEnvelope *
                (certifiedRadiusNode ev.radius ev.radiusPrecision ev.schedule k).width +
                (spectralNodeTarget ev.schedule.tolerance).1 ∧
            (tangentNode ev.radius ev.radiusPrecision ev.piPrecision ev.schedule k).width ≤
              2 * (9 *
                  (certifiedRadiusNode ev.radius ev.radiusPrecision ev.schedule k).width +
                2 * radiusSlackUpper B j *
                  (1 + (spectralNodeTarget ev.schedule.tolerance).1) *
                  (2 * (Transcendental.piInterval ev.piPrecision).width))) ∧
  (∀ (j : Fin (B.JBase + 1)) (N : ℕ),
    let pilot := pilotModulus input B 1 j
    ∀ hpilot : 0 < pilot.lo,
      let lower : PosRat := ⟨pilot.lo, hpilot⟩
      let ev := spectralEvaluationEvaluator input B j N lower
      let amplification := evaluationScheduleMagnitude input B j N lower
      ExactSpectralSchedule ev.schedule amplification ∧
        ev.schedule.magnitude =
          momentLipschitzBound input (radiusUpper B j) lower.1 N ∧ ev.Valid ∧
        ev.numerator.precision (spectralNodeTarget ev.schedule.tolerance) ≤ ev.mapFuel ∧
        ev.denominator.precision (spectralNodeTarget ev.schedule.tolerance) ≤ ev.mapFuel ∧
        PostNormalizationWidthContract (boundedContourEvaluate ev) (max N 1)
          ev.piPrecision (2 / (max p.n 1 : ℚ)) ∧
        ∀ k ≤ ev.schedule.mesh,
          pilot.lo / 2 ≤
              ((ev.denominator.eval
                (certifiedRadiusNode ev.radius ev.radiusPrecision ev.schedule k)
                ev.mapFuel).normInterval ev.mapFuel).lo ∧
            (ev.denominator.eval
              (certifiedRadiusNode ev.radius ev.radiusPrecision ev.schedule k)
              ev.mapFuel).normSq.AwayFromZero ∧
            (ev.numerator.eval
              (certifiedRadiusNode ev.radius ev.radiusPrecision ev.schedule k)
              ev.mapFuel).width ≤ ev.numerator.derivativeEnvelope *
                (certifiedRadiusNode ev.radius ev.radiusPrecision ev.schedule k).width +
                (spectralNodeTarget ev.schedule.tolerance).1 ∧
            (ev.denominator.eval
              (certifiedRadiusNode ev.radius ev.radiusPrecision ev.schedule k)
              ev.mapFuel).width ≤ ev.denominator.derivativeEnvelope *
                (certifiedRadiusNode ev.radius ev.radiusPrecision ev.schedule k).width +
                (spectralNodeTarget ev.schedule.tolerance).1 ∧
            (tangentNode ev.radius ev.radiusPrecision ev.piPrecision ev.schedule k).width ≤
              2 * (9 *
                  (certifiedRadiusNode ev.radius ev.radiusPrecision ev.schedule k).width +
                2 * radiusSlackUpper B j *
                  (1 + (spectralNodeTarget ev.schedule.tolerance).1) *
                  (2 * (Transcendental.piInterval ev.piPrecision).width)))

/-- The paper schedule is certified only for the floor-dyadic observation
records used by the ordinary option-A statistic.  In particular, this does
not assert a raw-fuel width contract for arbitrary supplied real names. -/
lemma spectralScheduleWitness (input : RepresentedSpectralInput p)
    (pStar : CertifiedBankInputs p)
    (hcanonical : CanonicalRepresentedSpectralInput Xspace input) :
    SpectralScheduleWitness input (contourBank p pStar) := by
  let B := contourBank p pStar
  refine ⟨pilotScheduleWitness input pStar hcanonical, ?_, ?_⟩
  · intro j
    dsimp only
    intro hpilot
    let lower : PosRat := ⟨(pilotModulus input B 0 j).lo, hpilot⟩
    let ev := spectralWindingEvaluator input B j lower
    refine ⟨?_, rfl, ?_, winding_numerator_precision_le input B j lower,
      winding_denominator_precision_le input B j lower, ?_, ?_⟩
    · dsimp [ev, spectralWindingEvaluator]
      exact exactSpectralSchedule_spectralSchedule _ _ _ _ _ _
    · exact spectralWindingEvaluator_valid input pStar hcanonical j lower rfl
    · exact winding_post_normalization_contract input pStar hcanonical j lower rfl
    · intro k hk
      simpa [ev, lower] using
        winding_node_specification input pStar hcanonical j lower rfl k hk
  · intro j N
    dsimp only
    intro hpilot
    let lower : PosRat := ⟨(pilotModulus input B 1 j).lo, hpilot⟩
    let ev := spectralEvaluationEvaluator input B j N lower
    refine ⟨?_, rfl, ?_, evaluation_numerator_precision_le input B j N lower,
      evaluation_denominator_precision_le input B j N lower, ?_, ?_⟩
    · dsimp [ev, spectralEvaluationEvaluator]
      exact exactSpectralSchedule_spectralSchedule _ _ _ _ _ _
    · exact spectralEvaluationEvaluator_valid input pStar hcanonical j N lower rfl
    · exact evaluation_post_normalization_contract input pStar hcanonical j N lower rfl
    · intro k hk
      simpa [ev, lower] using
        evaluation_node_specification input pStar hcanonical j N lower rfl k hk

/-- The pilot's finite-extremum error is the sum of a node half and a mesh
half, each bounded by `aStar/128`. -/
def FiniteExtremaContract (input : RepresentedSpectralInput p)
    (B : ContourBankData) (a : Fin 2) (j : Fin (B.JBase + 1)) : Prop :=
  let schedule := pilotSchedule input B a j
  let map := spectralDenominatorMap input B (spectralFold p.n a) 0
  let L := pilotCircleLipschitzBound input (radiusUpper B j)
  (∀ k ≤ schedule.mesh,
    ((map.eval (spectralRadiusNode B j schedule k) schedule.fuel).normInterval
      schedule.fuel).width ≤
      (pilotNodeTolerance B).1) ∧
    L / schedule.mesh ≤ (pilotMeshTolerance B).1

/-- Semantic certificate for one pilot boundary-infimum call. -/
def PilotModulusSpecification (input : RepresentedSpectralInput p) (B : ContourBankData)
    (a : Fin 2) (j : Fin (B.JBase + 1)) : Prop :=
  let I := pilotModulus input B a j
  I.Contains (sInf ((fun z ↦ ‖(spectralDenominatorMap input B
    (spectralFold p.n a) 0).value z‖) '' Metric.sphere (0 : ℂ) (B.rho j))) ∧
    I.width ≤ B.aStarRat / 64 ∧
    FiniteExtremaContract input B a j ∧ EndpointComplete (pilotSchedule input B a j)

/-- The exact complex number a bounded circle evaluator is meant to approximate:
integrate the ratio of the evaluator's numerator map to its denominator map once
around the circle of the evaluator's radius centred at the origin, then divide by
two pi times the imaginary unit times the evaluator's normalization count, where
a normalization count of zero is treated as one.

For a logarithmic-derivative integrand this is the argument-principle winding
number, so the exact value is an integer whenever the normalization is trivial. -/
def normalizedContourValue {box : ComplexRatInterval}
    (ev : BoundedCircleEvaluator box) : ℂ :=
  (((max ev.normalizationCount 1 : ℝ) : ℂ) * (2 * Real.pi : ℂ) * Complex.I)⁻¹ *
    CircleMesh.circleContourIntegral
      (fun z ↦ ev.numerator.value z / ev.denominator.value z) 0 ev.radius.value

/-- [The contour integral of a complex function around a circle as defined by
the quadrature-mesh library agrees with the standard circle integral](goal), for
any centre and any radius.

The mesh version parametrizes the circle over the unit parameter interval, the
standard version over an angle running from zero to two pi; the two agree after
the linear change of variables. -/
lemma circleContourIntegral_eq_circleIntegral (f : ℂ → ℂ) (c : ℂ) (rho : ℝ) :
    CircleMesh.circleContourIntegral f c rho = circleIntegral f c rho := by
  rw [CircleMesh.circleContourIntegral, circleIntegral]
  let g : ℝ → ℂ := fun theta ↦
    deriv (circleMap c rho) theta • f (circleMap c rho theta)
  have hpoint : CircleMesh.circleIntegrand f c rho =
      fun u ↦ (2 * Real.pi : ℝ) • g (u * (2 * Real.pi)) := by
    funext u
    dsimp [g, CircleMesh.circleIntegrand, CircleMesh.circleMap,
      CircleMesh.circleTangent]
    rw [deriv_circleMap]
    simp only [circleMap, Complex.ofReal_mul, Complex.ofReal_ofNat]
    ring_nf
  rw [hpoint]
  change (∫ u in (0 : ℝ)..1, (2 * Real.pi : ℝ) •
    g (u * (2 * Real.pi))) = ∫ theta in (0 : ℝ)..2 * Real.pi, g theta
  calc
    (∫ u in (0 : ℝ)..1, (2 * Real.pi : ℝ) •
        g (u * (2 * Real.pi))) =
        (2 * Real.pi : ℝ) • ∫ u in (0 : ℝ)..1,
          g (u * (2 * Real.pi)) :=
      intervalIntegral.integral_smul (𝕜 := ℝ) (2 * Real.pi)
        (fun u ↦ g (u * (2 * Real.pi)))
    _ = _ := by
      convert intervalIntegral.smul_integral_comp_mul_right
        (a := (0 : ℝ)) (b := 1) g (2 * Real.pi) using 1 <;> simp

/-- The winding rectangle encloses the normalized, tangent-corrected contour
integral and is narrow enough for unique integer decoding. -/
def WindingEnclosureSpecification (input : RepresentedSpectralInput p) (B : ContourBankData)
    (j : Fin (B.JBase + 1)) : Prop :=
  let I := windingEnclosure input B j
  I.re.width < 1 / 4 ∧ I.im.width < 1 / 4 ∧
    WindingDecoderContract I ∧
    (∀ h : 0 < (pilotModulus input B 0 j).lo,
      let ev := spectralWindingEvaluator input B j
        ⟨(pilotModulus input B 0 j).lo, h⟩
      ev.Valid ∧ I.Contains (normalizedContourValue ev) ∧
        PostNormalizationWidthContract (boundedContourEvaluate ev) 1 ev.piPrecision
          (1 / 4)) ∧
    EndpointComplete
      (spectralWindingEvaluator input B j ⟨1, by norm_num⟩).schedule

/-- The evaluation rectangle is normalized after quadrature and has the
paper's effective `1/max(n,1)` midpoint tolerance. -/
def EvaluationEnclosureSpecification (input : RepresentedSpectralInput p) (B : ContourBankData)
    (j : Fin (B.JBase + 1)) (N : ℕ) : Prop :=
  let I := evaluationEnclosure input B j N
  I.width ≤ 2 / (max p.n 1 : ℚ) ∧
    (∀ h : 0 < (pilotModulus input B 1 j).lo,
      let ev := spectralEvaluationEvaluator input B j N
        ⟨(pilotModulus input B 1 j).lo, h⟩
      ev.Valid ∧ I.Contains (normalizedContourValue ev) ∧
        PostNormalizationWidthContract (boundedContourEvaluate ev) (max N 1)
          ev.piPrecision (2 / (max p.n 1 : ℚ))) ∧
    EndpointComplete
      (spectralEvaluationEvaluator input B j N ⟨1, by norm_num⟩).schedule

private lemma pilotModulusSpecification_of_schedule
    (input : RepresentedSpectralInput p) (pStar : CertifiedBankInputs p)
    (hcanonical : CanonicalRepresentedSpectralInput Xspace input)
    (a : Fin 2) (j : Fin ((contourBank p pStar).JBase + 1)) :
    PilotModulusSpecification input (contourBank p pStar) a j := by
  let B := contourBank p pStar
  let schedule := pilotSchedule input B a j
  let map := spectralDenominatorMap input B (spectralFold p.n a) 0
  let L := pilotCircleLipschitzBound input (radiusUpper B j)
  let f : ℝ → ℝ := fun u ↦ ‖map.value
    (CircleMesh.circleMap 0 (B.rho j) u)‖
  have hs := pilotScheduleWitness input pStar hcanonical a j
  have hnodes : ∀ k ≤ schedule.mesh,
      ((map.eval (spectralRadiusNode B j schedule k) schedule.fuel).normInterval
        schedule.fuel).Contains (f (CircleMesh.meshPoint schedule.mesh k)) := by
    intro k hk
    have hkdata := hs.2.2.2.2.2 k hk
    have hmapContains := (hs.2.2.1.2.2 hkdata.2.1 hkdata.1).1 schedule.fuel
    exact ComplexRatInterval.normInterval_sound hmapContains schedule.fuel
  have hinfParam : (pilotModulus input B a j).Contains
      (sInf (f '' Set.Icc (0 : ℝ) 1)) := by
    dsimp [pilotModulus]
    apply CircleMesh.infEnclosure_sound
    · intro s hs' t ht'
      exact pilotMap_norm_lipschitz input B (spectralFold p.n a)
        (by exact_mod_cast (contourBank_rho_pos_le_UR p pStar j).1.le)
        (certifiedRadius_value_le_radiusUpper B j) s t
    · simpa [schedule, map, f] using hnodes
  have himage : f '' Set.Icc (0 : ℝ) 1 =
      (fun z ↦ ‖map.value z‖) '' Metric.sphere (0 : ℂ) (B.rho j) := by
    rw [← image_circleMesh_circleMap_Icc (B.rho j)
      (by exact_mod_cast (contourBank_rho_pos_le_UR p pStar j).1)]
    rw [Set.image_image]
  have hinf : (pilotModulus input B a j).Contains
      (sInf ((fun z ↦ ‖map.value z‖) '' Metric.sphere (0 : ℂ) (B.rho j))) := by
    simpa [himage] using hinfParam
  have hnodeWidths : ∀ k ≤ schedule.mesh,
      ((map.eval (spectralRadiusNode B j schedule k) schedule.fuel).normInterval
        schedule.fuel).width ≤ (pilotNodeTolerance B).1 :=
    fun k hk ↦ (hs.2.2.2.2.2 k hk).2.2.2.2.2
  have hwidth := CircleMesh.width_infEnclosure
    (pilotNodeTolerance B).2.le
    (pilotCircleLipschitzBound_nonneg input (radiusUpper_nonneg B j))
    schedule.mesh_pos hnodeWidths
  have htol : schedule.tolerance.1 ≤ (pilotNodeTolerance B).1 := by
    let S := spectralNodeScale B j (pilotScheduleMagnitude input B j)
      ⟨1, by norm_num⟩ 1
      (spectralNodeOperationCount .pilot (spectralFold p.n a).card)
    have hS1 : 1 ≤ S := by
      dsimp [S, spectralNodeScale]
      exact le_max_left _ _
    have heq : 64 * S * schedule.tolerance.1 = (pilotNodeTolerance B).1 ^ 2 := by
      exact estimatorNodePrecision_scale_eq (pilotNodeTolerance B) S hS1
    have hr1 : (pilotNodeTolerance B).1 ≤ 1 := by
      have ha : B.aStarRat ≤ 1 := by
        dsimp [B, contourBank]
        exact pow_le_one₀ (by norm_num) (by norm_num)
      dsimp [pilotNodeTolerance]
      nlinarith
    have hscale : 1 ≤ 64 * S := by nlinarith
    have hmul := mul_le_mul_of_nonneg_right hscale schedule.tolerance.2.le
    nlinarith [(pilotNodeTolerance B).2.le]
  have hmesh : L / schedule.mesh ≤ (pilotNodeTolerance B).1 := by
    calc
      L / schedule.mesh = schedule.magnitude / schedule.mesh := by rw [hs.2.1]
      _ ≤ schedule.meshBudget := schedule.mesh_error_le
      _ = schedule.tolerance.1 / 3 := rfl
      _ ≤ (pilotNodeTolerance B).1 := by nlinarith [(pilotNodeTolerance B).2]
  refine ⟨by simpa [B, map] using hinf, ?_, ?_, endpointComplete schedule⟩
  · have ha : (pilotNodeTolerance B).1 = B.aStarRat / 128 := rfl
    calc
      (pilotModulus input B a j).width ≤
          (pilotNodeTolerance B).1 + L / schedule.mesh := by
        simpa [pilotModulus, schedule, map, L] using hwidth
      _ ≤ B.aStarRat / 64 := by rw [ha]; nlinarith [hmesh]
  · exact ⟨hnodeWidths, hmesh⟩

private lemma windingEnclosureSpecification_of_schedule
    (input : RepresentedSpectralInput p) (B : ContourBankData)
    (hschedule : SpectralScheduleWitness input B)
    (j : Fin (B.JBase + 1)) : WindingEnclosureSpecification input B j := by
  let pilot := pilotModulus input B 0 j
  by_cases h : 0 < pilot.lo
  · let lower : PosRat := ⟨pilot.lo, h⟩
    let ev := spectralWindingEvaluator input B j lower
    have hs := hschedule.2.1 j h
    have hpost := hs.2.2.2.2.2.1
    have hwidth := hpost.choose_spec.2.2.2
    have hwidth' : (windingEnclosure input B j).width < 1 / 4 := by
      simpa only [windingEnclosure, pilot, h, lower, ev, if_pos, dite_true] using hwidth
    have hre : (windingEnclosure input B j).re.width < 1 / 4 := by
      exact (le_max_left _ _).trans_lt hwidth'
    have him : (windingEnclosure input B j).im.width < 1 / 4 := by
      exact (le_max_right _ _).trans_lt hwidth'
    refine ⟨hre, him, uniqueNonnegativeInteger_contract _, ?_, endpointComplete _⟩
    intro h'
    have hh : h' = h := Subsingleton.elim _ _
    cases hh
    refine ⟨by simpa [ev] using hs.2.2.1, ?_, by simpa [ev] using hpost⟩
    have hint := boundedContourEvaluate_contains ev (by simpa [ev] using hs.2.2.1)
    have hnorm := boundedContourNormalize_contains (boundedContourEvaluate ev) 1
      ev.piPrecision hint
    simpa [windingEnclosure, pilot, h, lower, ev, spectralWindingEvaluator,
      normalizedContourValue,
      div_eq_inv_mul, mul_assoc, mul_comm, mul_left_comm] using hnorm
  · have hzero : windingEnclosure input B j = ComplexRatInterval.zero := by
      simp [windingEnclosure, pilot, h]
    dsimp only [WindingEnclosureSpecification]
    rw [hzero]
    refine ⟨by norm_num [ComplexRatInterval.zero, RatInterval.width, RatInterval.point],
      by norm_num [ComplexRatInterval.zero, RatInterval.width, RatInterval.point],
      uniqueNonnegativeInteger_contract _, ?_, endpointComplete _⟩
    intro h'
    exact (h h').elim

private lemma evaluationEnclosureSpecification_of_schedule
    (input : RepresentedSpectralInput p) (B : ContourBankData)
    (hschedule : SpectralScheduleWitness input B)
    (j : Fin (B.JBase + 1)) (N : ℕ) :
    EvaluationEnclosureSpecification input B j N := by
  let pilot := pilotModulus input B 1 j
  by_cases h : 0 < pilot.lo
  · let lower : PosRat := ⟨pilot.lo, h⟩
    let ev := spectralEvaluationEvaluator input B j N lower
    have hs := hschedule.2.2 j N h
    have hpost := hs.2.2.2.2.2.1
    have hwidth := hpost.choose_spec.2.2.2
    have hwidth' : (evaluationEnclosure input B j N).width <
        2 / (max p.n 1 : ℚ) := by
      simpa only [evaluationEnclosure, pilot, h, lower, ev, if_pos, dite_true] using hwidth
    refine ⟨hwidth'.le, ?_, endpointComplete _⟩
    intro h'
    have hh : h' = h := Subsingleton.elim _ _
    cases hh
    refine ⟨by simpa [ev] using hs.2.2.1, ?_, by simpa [ev] using hpost⟩
    have hint := boundedContourEvaluate_contains ev (by simpa [ev] using hs.2.2.1)
    have hnorm := boundedContourNormalize_contains (boundedContourEvaluate ev)
      (max N 1) ev.piPrecision hint
    have hcount : ev.normalizationCount = max N 1 := rfl
    have henc : evaluationEnclosure input B j N =
        boundedContourNormalize (boundedContourEvaluate ev) (max N 1)
          ev.piPrecision := by
      simp [evaluationEnclosure, pilot, h, lower, ev]
    rw [henc]
    change (boundedContourNormalize (boundedContourEvaluate ev) (max N 1)
      ev.piPrecision).Contains (normalizedContourValue ev)
    have hcast : ((max (N : ℚ) 1 : ℚ) : ℂ) = (((max N 1 : ℕ) : ℝ) : ℂ) := by
      norm_cast
    simpa [normalizedContourValue, hcount, hcast,
      div_eq_inv_mul, mul_assoc, mul_comm, mul_left_comm] using hnorm
  · have hzero : evaluationEnclosure input B j N = ComplexRatInterval.zero := by
      simp [evaluationEnclosure, pilot, h]
    dsimp only [EvaluationEnclosureSpecification]
    rw [hzero]
    refine ⟨?_, ?_, endpointComplete _⟩
    · simp only [ComplexRatInterval.width, ComplexRatInterval.zero,
        RatInterval.width, RatInterval.point, sub_self, max_self]
      positivity
    intro h'
    exact (h h').elim

/-- Selector-side use of the decoder contract: a normalized winding rectangle
with the certified strict coordinate widths decodes the exact nonnegative
integer it contains. -/
lemma selector_decodes_exact_winding
    (input : RepresentedSpectralInput p) (B : ContourBankData)
    (j : Fin (B.JBase + 1)) (N : ℕ)
    (hspec : WindingEnclosureSpecification input B j)
    (hcontains : (windingEnclosure input B j).Contains (((N : ℝ) : ℂ))) :
    uniqueNonnegativeInteger (windingEnclosure input B j) = some N := by
  exact (hspec.2.2.1).2.1 N hcontains hspec.1 hspec.2.1

/-- The full package of node-level certificates the bounded selector relies on,
stated for a given parameter set: for every measurable covariate space and every
choice of certified bank inputs, certified range input, treatment-regression code
sequence, and sample, the canonically encoded input satisfies, at each candidate
contour radius, the two pilot boundary-modulus certificates, the winding-number
enclosure certificate, and the evaluation enclosure certificate for every
candidate integer; and the projected-output name certifies, at every rational
argument, the clipping of that argument to the range constant Ctheta.

The clipping is written in its absolute-value form: half the difference between
the distance to minus Ctheta and the distance to plus Ctheta. -/
def RepresentedNodeSpecifications (p : Parameters) : Prop :=
  ∀ {Xspace : Type*} [MeasurableSpace Xspace]
    (pStar : CertifiedBankInputs p) (cStar : CertifiedRangeInput p)
    (gcode : ℕ → Xspace → ℝ) (data : Fin p.n → Obs Xspace),
    let input := canonicalRepresentedInput p pStar cStar gcode data
    (∀ j : Fin ((contourBank p input.primitive).JBase + 1),
      PilotModulusSpecification input (contourBank p input.primitive) 0 j ∧
      PilotModulusSpecification input (contourBank p input.primitive) 1 j ∧
      WindingEnclosureSpecification input (contourBank p input.primitive) j ∧
      ∀ N, EvaluationEnclosureSpecification input (contourBank p input.primitive) j N) ∧
    ∀ y : ℚ, (projectedOutputName input.range.CthetaName y).IsCertified
      ((|((y : ℚ) : ℝ) + input.range.CthetaName.name.value| -
        |((y : ℚ) : ℝ) - input.range.CthetaName.name.value|) / 2)

/-- [Every parameter set satisfies the full package of node-level certificates:
on canonically encoded data the pilot boundary-modulus enclosures, the winding
enclosures, the evaluation enclosures, and the certified clipping of the output
to the range constant Ctheta all hold](goal), with no further assumptions on the
sample or on the treatment-regression code.

This discharges in one place every semantic obligation the selector's soundness
argument imposes on the individual certified nodes. -/
lemma representedNodeSpecifications (p : Parameters) :
    RepresentedNodeSpecifications p := by
  intro Xspace _ pStar cStar gcode data
  let input := canonicalRepresentedInput p pStar cStar gcode data
  have hcanonical : CanonicalRepresentedSpectralInput Xspace input :=
    ⟨pStar, cStar, gcode, data, rfl⟩
  have hschedule : SpectralScheduleWitness input (contourBank p pStar) :=
    spectralScheduleWitness input pStar hcanonical
  refine ⟨?_, ?_⟩
  · intro j
    refine ⟨pilotModulusSpecification_of_schedule input pStar hcanonical 0 j,
      pilotModulusSpecification_of_schedule input pStar hcanonical 1 j,
      windingEnclosureSpecification_of_schedule input (contourBank p pStar)
        hschedule j, ?_⟩
    intro N
    exact evaluationEnclosureSpecification_of_schedule input (contourBank p pStar)
      hschedule j N
  · intro y
    exact projectedOutputName_certified cStar.CthetaName y

/-- The generic complex operations used by the bounded adapter have their
actual executable semantics.  This is deliberately a predicate on a supplied
build, rather than extra fields on the weak callable carrier. -/
def GenericComplexBuildImplemented (build : complexCertifiedIntervalArithmetic) : Prop :=
  build.operations.IsCanonical ∧
  RealTranscendentalContract expTaylorInterval Real.exp expScheduleProgram ∧
  RealTranscendentalContract
    CausalSmith.Stat.SaPlmCumulantConverse.sinInterval Real.sin trigScheduleProgram ∧
  RealTranscendentalContract
    CausalSmith.Stat.SaPlmCumulantConverse.cosInterval Real.cos trigScheduleProgram ∧
  ComplexExpContract cexpScheduleProgram ∧
  CircleProgramContract circleNodeScheduleProgram circleTangentScheduleProgram ∧
  NodeEvaluationContract nodeEvaluationScheduleProgram ∧
  (∀ (I J : ComplexRatInterval) (z w : ℂ), I.Contains z → J.Contains w →
    (build.operations.complexMul I J).Contains (z * w)) ∧
  (∀ (I J : ComplexRatInterval) (z w : ℂ) (m : ℚ) (hm : 0 < m)
      (hguard : m ≤ (cxModulusSq J).lo),
    I.Contains z → J.Contains w →
      (build.operations.guardedDiv I J m hm hguard).Contains (z / w)) ∧
  (∀ (I : ComplexRatInterval) (z : ℂ) (fuel : ℕ), I.Contains z →
    (build.operations.complexExp I fuel).Contains (Complex.exp z)) ∧
  (∀ fuel, (build.operations.piInterval fuel).Contains Real.pi) ∧
  ∀ name input L e endpointOperations,
    build.operations.fuelTrace name input L e endpointOperations =
      nodeEvaluationScheduleProgram name input L e endpointOperations

/-- The supplied compiled entry points are exactly the pilot, winding, and
evaluation programs of the single bounded option-A adapter. -/
def CanonicalAdapterEntryPointsCompiled
    (compiled : CompiledBoundedSpectralAdapter) : Prop :=
  (∀ {q : Parameters} (input : RepresentedSpectralInput q)
      (B : ContourBankData) (a : Fin 2) (j : Fin (B.JBase + 1)),
    compiled.pilotBoundary input B a j = builtPilotBoundary compiled.build input B a j) ∧
  (∀ {q : Parameters} (input : RepresentedSpectralInput q)
      (B : ContourBankData) (j : Fin (B.JBase + 1)),
    compiled.windingQuadrature input B j = builtWindingQuadrature compiled.build input B j) ∧
  ∀ {q : Parameters} (input : RepresentedSpectralInput q)
      (B : ContourBankData) (j : Fin (B.JBase + 1)) (N : ℕ),
    compiled.evaluationQuadrature input B j N =
      builtEvaluationQuadrature compiled.build input B j N

/-- Complete antecedent for represented delivery on one fixed experiment.
It combines the genuine generic complex build, the compiled callable adapter,
the locally derived schedule/map/guard/containment/width/normalization facts,
and endpoint completeness.  Output certification is a conclusion derived
from the projected-output certificate, not a premise of this predicate.
None of these paper-specific facts is a field of
`CompiledBoundedSpectralAdapter`. -/
def FullCanonicalBuildAndCompilation
    (compiled : CompiledBoundedSpectralAdapter) (p : Parameters)
    (pStar : CertifiedBankInputs p) (cStar : CertifiedRangeInput p)
    (gcode : ℕ → Xspace → ℝ) : Prop :=
  GenericComplexBuildImplemented compiled.build ∧
  CanonicalAdapterEntryPointsCompiled compiled ∧
  (∀ data : Fin p.n → Obs Xspace,
    let input := canonicalRepresentedInput p pStar cStar gcode data
    let B := contourBank p pStar
    SpectralScheduleWitness input B ∧
      ∀ j : Fin (B.JBase + 1),
        PilotModulusSpecification input B 0 j ∧
        PilotModulusSpecification input B 1 j ∧
        WindingEnclosureSpecification input B j ∧
        ∀ N, EvaluationEnclosureSpecification input B j N)

private lemma instrumentedSpectralProgram_output_eq_projectedOutputName
    {p : Parameters} (input : RepresentedSpectralInput p) :
    (instrumentedSpectralProgram input).output =
      projectedOutputName input.range.CthetaName
        (instrumentedSpectralProgram input).raw := by
  unfold instrumentedSpectralProgram spectralProgramWith
  dsimp only
  split <;> try rfl
  split <;> try rfl
  split <;> rfl

private lemma clip_eq_abs_projection (C y : ℝ) (hC : 0 ≤ C) :
    min (max y (-C)) C = (|y + C| - |y - C|) / 2 := by
  symm
  by_cases hlo : y < -C
  · rw [abs_of_neg (by linarith), abs_of_neg (by linarith),
      max_eq_right hlo.le, min_eq_left (by linarith)]
    ring
  · by_cases hhi : C < y
    · rw [abs_of_pos (by linarith), abs_of_pos (by linarith),
        max_eq_left (by linarith), min_eq_right hhi.le]
      ring
    · rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith),
        max_eq_left (by linarith), min_eq_left (by linarith)]
      ring

/-- If [a compiled bounded adapter has canonical generic complex arithmetic,
canonically compiled entry points, and node certificates valid on every
sample](hyp:hfull), then [running that compiled adapter on canonically encoded
data reproduces the estimator's represented-execution contract](goal): it returns
exactly the same record as the ordinary finite-rational program, the same
execution trace, and an output name certifying the clipped point estimate.

The proof rewrites each compiled entry point into its reference enclosure and
identifies the resulting represented program with the ordinary one; the output
claim then reduces to the certified absolute-value form of clipping to the range
constant Ctheta. -/
lemma representedExecution_of_fullCanonicalBuildAndCompilation
    (compiled : CompiledBoundedSpectralAdapter) (p : Parameters)
    (pStar : CertifiedBankInputs p) (cStar : CertifiedRangeInput p)
    (gcode : ℕ → Xspace → ℝ)
    (hfull : FullCanonicalBuildAndCompilation compiled p pStar cStar gcode) :
    RepresentedExecution compiled p pStar cStar gcode := by
  change representedExecutionContract compiled p pStar cStar gcode
  intro data
  dsimp only
  have hcanonical : compiled.build.operations.IsCanonical := hfull.1.1
  have hcompiled := hfull.2.1
  have hp : ∀ {q : Parameters} (input : RepresentedSpectralInput q)
      (B : ContourBankData) (a : Fin 2) (j : Fin (B.JBase + 1)),
      compiled.pilotBoundary input B a j = pilotModulus input B a j := by
    intro q input B a j
    rw [hcompiled.1 input B a j]
    exact builtPilotBoundary_eq compiled.build hcanonical input B a j
  have hw : ∀ {q : Parameters} (input : RepresentedSpectralInput q)
      (B : ContourBankData) (j : Fin (B.JBase + 1)),
      compiled.windingQuadrature input B j = windingEnclosure input B j := by
    intro q input B j
    rw [hcompiled.2.1 input B j]
    exact builtWindingQuadrature_eq compiled.build hcanonical input B j
  have he : ∀ {q : Parameters} (input : RepresentedSpectralInput q)
      (B : ContourBankData) (j : Fin (B.JBase + 1)) (N : ℕ),
      compiled.evaluationQuadrature input B j N = evaluationEnclosure input B j N := by
    intro q input B j N
    rw [hcompiled.2.2 input B j N]
    exact builtEvaluationQuadrature_eq compiled.build hcanonical input B j N
  have heq : representedSpectralProgram compiled
        (canonicalRepresentedInput p pStar cStar gcode data) =
      instrumentedSpectralProgram
        (canonicalRepresentedInput p pStar cStar gcode data) := by
    simp only [representedSpectralProgram, instrumentedSpectralProgram,
      spectralProgramWith, hp, hw, he]
  have heq' : representedSpectralProgram compiled
        (canonicalRepresentedInput p pStar cStar gcode data) =
      ordinaryFiniteRationalResult p pStar cStar gcode data := by
    simpa [ordinaryFiniteRationalResult, ordinarySpectralProgram] using heq
  refine ⟨heq', ?_, ?_⟩
  · rw [heq']
  · rw [heq']
    have hout :
        (ordinaryFiniteRationalResult p pStar cStar gcode data).output =
          projectedOutputName cStar.CthetaName
            (ordinaryFiniteRationalResult p pStar cStar gcode data).raw := by
      exact instrumentedSpectralProgram_output_eq_projectedOutputName
        (canonicalRepresentedInput p pStar cStar gcode data)
    rw [hout]
    convert projectedOutputName_certified cStar.CthetaName
      (ordinaryFiniteRationalResult p pStar cStar gcode data).raw using 1
    unfold ordinaryThetaHatValue
    dsimp only
    have hC : 0 ≤ cStar.CthetaName.name.value := by
      rw [cStar.Ctheta_value]
      exact p.constants_pos.1.le
    exact clip_eq_abs_projection cStar.CthetaName.name.value
      ((ordinaryFiniteRationalResult p pStar cStar gcode data).raw : ℝ) hC

/-- [The estimator's reported point estimate is exactly the raw output of the
ordinary finite-rational program clipped to the interval between minus the range
constant Ctheta and plus Ctheta](goal), for any parameter set, certified records,
treatment-regression code, and sample.

This is a specification unfolding: it records that no post-processing other than
the clipping stands between the program's raw value and the reported estimate. -/
lemma thetaHatSpec_eq_clip_finite_rational
    (p : Parameters) (pStar : CertifiedBankInputs p) (cStar : CertifiedRangeInput p)
    (gcode : ℕ → Xspace → ℝ) (data : Fin p.n → Obs Xspace) :
    thetaHatSpec p pStar cStar gcode data =
      min (max ((ordinaryFiniteRationalResult p pStar cStar gcode data).raw : ℝ)
        (-p.Ctheta)) p.Ctheta := by
  unfold thetaHatSpec ordinaryThetaHatValue
  dsimp only
  rw [cStar.Ctheta_value]

/-- Finite branch endpoints, floor-dyadic maps, and the least-index search are
Borel measurable. -/
lemma instrumentedSpectralProgram_raw_measurable
    (p : Parameters) (pStar : CertifiedBankInputs p) (cStar : CertifiedRangeInput p)
    (gcode : ℕ → Xspace → ℝ) (hgcode : Measurable (gcode p.n)) :
    Measurable (fun data : Fin p.n → Obs Xspace ↦
      ((ordinaryFiniteRationalResult p pStar cStar gcode data).raw : ℝ)) := by
  exact ordinaryFiniteRationalResult_raw_measurable p pStar cStar gcode hgcode

/-- If [the treatment-regression code at the current sample size is a measurable
function of the covariate](hyp:hgcode), then [the estimator is a measurable
function of the sample](goal).

Measurability passes through the clipping, which is a composition of a minimum
and a maximum with constants, to the raw output of the finite-rational program. -/
lemma thetaHatSpec_measurable
    (p : Parameters) (pStar : CertifiedBankInputs p) (cStar : CertifiedRangeInput p)
    (gcode : ℕ → Xspace → ℝ) (hgcode : Measurable (gcode p.n)) :
    Measurable (thetaHatSpec p pStar cStar gcode) := by
  rw [show thetaHatSpec p pStar cStar gcode =
      fun data ↦ min (max
        ((ordinaryFiniteRationalResult p pStar cStar gcode data).raw : ℝ)
        (-p.Ctheta)) p.Ctheta from by
    funext data
    exact thetaHatSpec_eq_clip_finite_rational p pStar cStar gcode data]
  exact ((instrumentedSpectralProgram_raw_measurable p pStar cStar gcode hgcode).max
    measurable_const).min measurable_const

/-- [The estimator always takes values between minus the range constant Ctheta
and plus Ctheta](goal), whatever the sample, because its last step clips the raw
value to that range and the range constant is positive. -/
lemma thetaHatSpec_mem_Icc
    (p : Parameters) (pStar : CertifiedBankInputs p) (cStar : CertifiedRangeInput p)
    (gcode : ℕ → Xspace → ℝ) (data : Fin p.n → Obs Xspace) :
    thetaHatSpec p pStar cStar gcode data ∈ Set.Icc (-p.Ctheta) p.Ctheta := by
  rw [thetaHatSpec_eq_clip_finite_rational]
  constructor
  · exact le_min (le_max_right _ _) (by linarith [p.constants_pos.1])
  · exact min_le_right _ _

/-- If [a compiled bounded adapter satisfies the represented-execution
contract](hyp:hexec), then on every sample [the record it produces on canonically
encoded data equals the record produced by the ordinary finite-rational program,
its execution trace equals the estimator's full trace, and its output name
certifies the estimator's reported value](goal).

This is the form in which the soundness statement is consumed downstream: the
compiled artefact may be substituted for the specification wherever the value,
the trace, or the certified output is used. -/
lemma representedExecution_sound
    (compiled : CompiledBoundedSpectralAdapter) {p : Parameters}
    (pStar : CertifiedBankInputs p) (cStar : CertifiedRangeInput p)
    (gcode : ℕ → Xspace → ℝ)
    (hexec : RepresentedExecution compiled p pStar cStar gcode)
    (data : Fin p.n → Obs Xspace) :
    let input := canonicalRepresentedInput p pStar cStar gcode data
    let result := representedSpectralProgram compiled input
    result = ordinaryFiniteRationalResult p pStar cStar gcode data ∧
    result.trace = (thetaHatSpec p pStar cStar gcode).fullTrace data ∧
    result.output.IsCertified (thetaHatSpec p pStar cStar gcode data) := by
  simpa [RepresentedExecution, thetaHatSpec, representedExecutionContract] using (hexec data)

/-- The source good event supplies both population controls and the two
positive denominator margins.  The empirical margin is derived from
`d ≤ mu-nu`; it is not a separate assumption. -/
def CanonicalSelectorGoodEvent (p : Parameters) (pStar : CertifiedBankInputs p)
    (cStar : CertifiedRangeInput p) (gcode : ℕ → Xspace → ℝ)
    (data : Fin p.n → Obs Xspace) (F G : ℂ → ℂ)
    (d e C_G mu nu : ℝ) : Prop :=
  0 ≤ d ∧ 0 ≤ e ∧ 0 ≤ C_G ∧ 0 < mu ∧ 0 < nu ∧
  mu = 31 * ((contourBank p pStar).aStarRat : ℝ) / 64 ∧
  nu = 23 * ((contourBank p pStar).aStarRat : ℝ) / 64 ∧
  d ≤ mu - nu ∧
  let input := canonicalRepresentedInput p pStar cStar gcode data
  let B := contourBank p pStar
  ∃ (j : Fin (B.JBase + 1)) (N : ℕ),
    selectedContour input B = some j ∧
    (pilotOutcome input B j).decoded = some N ∧ 1 ≤ N ∧
    B.aStarRat / 4 ≤ (pilotModulus input B 1 j).lo ∧
    ∀ z ∈ Metric.sphere (0 : ℂ) (B.rho j),
      mu ≤ ‖F z‖ ∧ ‖G z‖ ≤ C_G ∧
      ‖semanticEmpiricalF p gcode data (spectralFold p.n 1) 0 z - F z‖ ≤ d ∧
      ‖semanticEmpiricalG p gcode data (spectralFold p.n 1) 0 z - G z‖ ≤ e

/-- Exact source perturbation scale. -/
def ordinaryContourPerturbationConstant (p : Parameters)
    (C_G mu nu : ℝ) : ℝ :=
  searchRadius p * max nu⁻¹ (C_G * (mu * nu)⁻¹)

/-- A population lower bound on a denominator transfers to its empirical
counterpart: if [the population denominator has modulus at least mu](hyp:hpopulation),
[the empirical denominator differs from it by at most d in modulus](hyp:herror),
and [the estimation error d does not exceed the gap between mu and nu](hyp:hsmall),
then [the empirical denominator has modulus at least nu](goal).

The empirical margin is therefore a consequence of the population margin and the
error bound, not an extra assumption. -/
lemma empirical_denominator_margin_of_population_margin
    {Fhat F : ℂ} {d mu nu : ℝ}
    (hpopulation : mu ≤ ‖F‖) (herror : ‖Fhat - F‖ ≤ d)
    (hsmall : d ≤ mu - nu) : nu ≤ ‖Fhat‖ := by
  have htriangle : ‖F‖ ≤ ‖Fhat - F‖ + ‖Fhat‖ := by
    calc
      ‖F‖ = ‖-(Fhat - F) + Fhat‖ := by congr 1; ring
      _ ≤ ‖-(Fhat - F)‖ + ‖Fhat‖ := norm_add_le _ _
      _ = ‖Fhat - F‖ + ‖Fhat‖ := by rw [norm_neg]
  linarith

/-- A perturbation bound for a ratio of complex numbers. Suppose [the population
denominator has modulus at least mu](hyp:hmu) and [the empirical denominator has
modulus at least nu](hyp:hnu), with [both margins strictly positive](hyp:hmu0,hnu0);
[the population numerator has modulus at most C](hyp:hG), with [C
nonnegative](hyp:hC); [the denominators differ by at most d](hyp:hF), with [d
nonnegative](hyp:hd); and [the numerators differ by at most e](hyp:hGh), with [e
nonnegative](hyp:he). Then [the two ratios differ by at most e divided by nu plus
C times d divided by the product of mu and nu](goal).

The two terms are the numerator perturbation, damped by the empirical denominator
margin, and the denominator perturbation, amplified by the numerator bound and
damped by both margins. -/
lemma norm_div_sub_div_le {Fhat Ghat F G : ℂ} {d e C mu nu : ℝ}
    (hmu : mu ≤ ‖F‖) (hnu : nu ≤ ‖Fhat‖)
    (hmu0 : 0 < mu) (hnu0 : 0 < nu) (hG : ‖G‖ ≤ C) (hC : 0 ≤ C)
    (hF : ‖Fhat - F‖ ≤ d) (hd : 0 ≤ d)
    (hGh : ‖Ghat - G‖ ≤ e) (he : 0 ≤ e) :
    ‖Ghat / Fhat - G / F‖ ≤ e / nu + C * d / (mu * nu) := by
  have hF0 : F ≠ 0 := by
    intro h
    simp [h] at hmu
    linarith
  have hFhat0 : Fhat ≠ 0 := by
    intro h
    simp [h] at hnu
    linarith
  have hfirst : ‖(Ghat - G) / Fhat‖ ≤ e / nu := by
    rw [norm_div]
    apply (div_le_div_iff₀ (norm_pos_iff.mpr hFhat0) hnu0).2
    nlinarith
  have hsecond : ‖G * (F - Fhat) / (Fhat * F)‖ ≤ C * d / (mu * nu) := by
    rw [norm_div, norm_mul, norm_mul, norm_sub_rev]
    have hnum : ‖G‖ * ‖Fhat - F‖ ≤ C * d :=
      mul_le_mul hG hF (norm_nonneg _) hC
    have hden : mu * nu ≤ ‖Fhat‖ * ‖F‖ := by
      nlinarith [mul_le_mul hnu hmu hmu0.le (norm_nonneg Fhat)]
    exact div_le_div₀ (mul_nonneg hC hd) hnum (mul_pos hmu0 hnu0) hden
  calc
    ‖Ghat / Fhat - G / F‖ =
        ‖(Ghat - G) / Fhat + G * (F - Fhat) / (Fhat * F)‖ := by
      congr 1
      field_simp
      ring
    _ ≤ ‖(Ghat - G) / Fhat‖ + ‖G * (F - Fhat) / (Fhat * F)‖ :=
      norm_add_le _ _
    _ ≤ e / nu + C * d / (mu * nu) := add_le_add hfirst hsecond

/-- The ratio perturbation bound, integrated around a circle. Consider a circle
of [nonnegative radius rho](hyp:hrho) centred at the origin, along with
[nonnegative error scales d and e and a nonnegative numerator bound
C](hyp:hd,he,hC) and [strictly positive denominator margins mu and
nu](hyp:hmu0,hnu0) satisfying [the requirement that the denominator error does
not exceed the gap between the two margins](hyp:hsmall). Suppose [the empirical
ratio is integrable around the circle](hyp:hhat), [the population ratio is
integrable around the circle](hyp:hpop), and [at every point of the circle the
population denominator has modulus at least mu, the population numerator has
modulus at most C, the denominators differ by at most d, and the numerators
differ by at most e](hyp:hboundary). Then [the two contour integrals differ by at
most the circumference of the circle times the sum of e divided by nu and C times
d divided by the product of mu and nu](goal).

The proof bounds the integrand pointwise by the ratio perturbation bound, using
that the empirical denominator inherits the margin nu from the population margin
mu and the error bound. -/
lemma circleIntegral_ratio_difference_bound
    {Fhat Ghat F G : ℂ → ℂ} {rho d e C mu nu : ℝ}
    (hrho : 0 ≤ rho) (hd : 0 ≤ d) (he : 0 ≤ e) (hC : 0 ≤ C)
    (hmu0 : 0 < mu) (hnu0 : 0 < nu) (hsmall : d ≤ mu - nu)
    (hhat : CircleIntegrable (fun z ↦ Ghat z / Fhat z) 0 rho)
    (hpop : CircleIntegrable (fun z ↦ G z / F z) 0 rho)
    (hboundary : ∀ z ∈ Metric.sphere (0 : ℂ) rho,
      mu ≤ ‖F z‖ ∧ ‖G z‖ ≤ C ∧ ‖Fhat z - F z‖ ≤ d ∧
        ‖Ghat z - G z‖ ≤ e) :
    ‖circleIntegral (fun z ↦ Ghat z / Fhat z) 0 rho -
        circleIntegral (fun z ↦ G z / F z) 0 rho‖ ≤
      2 * Real.pi * rho * (e / nu + C * d / (mu * nu)) := by
  rw [← circleIntegral.integral_sub hhat hpop]
  apply circleIntegral.norm_integral_le_of_norm_le_const hrho
  intro z hz
  rcases hboundary z hz with ⟨hmu, hG, hF, hGh⟩
  exact norm_div_sub_div_le hmu
    (empirical_denominator_margin_of_population_margin hmu hF hsmall)
    hmu0 hnu0 hG hC hF hd hGh he

/-- The selected-circle ratio bound plus the separate finite rational
midpoint error. -/
lemma thetaHatSpec_good_event_exact_contour_perturbation
    (p : Parameters) (pStar : CertifiedBankInputs p) (cStar : CertifiedRangeInput p)
    (gcode : ℕ → Xspace → ℝ) (data : Fin p.n → Obs Xspace)
    (F G : ℂ → ℂ) (d e C_G mu nu target : ℝ)
    (htarget : |target| ≤ p.Ctheta)
    (hgood : CanonicalSelectorGoodEvent p pStar cStar gcode data
      F G d e C_G mu nu)
    (hratioIntegrable : ∀ j,
      selectedContour (canonicalRepresentedInput p pStar cStar gcode data)
          (contourBank p pStar) = some j →
      CircleIntegrable
          (fun z ↦ semanticEmpiricalG p gcode data (spectralFold p.n 1) 0 z /
            semanticEmpiricalF p gcode data (spectralFold p.n 1) 0 z)
          0 ((contourBank p pStar).rho j) ∧
      CircleIntegrable (fun z ↦ G z / F z) 0 ((contourBank p pStar).rho j))
    (hidentify : ∀ j N,
      selectedContour (canonicalRepresentedInput p pStar cStar gcode data)
          (contourBank p pStar) = some j →
      (pilotOutcome (canonicalRepresentedInput p pStar cStar gcode data)
        (contourBank p pStar) j).decoded = some N →
      target = ((((N : ℂ) * (2 * Real.pi : ℂ) * Complex.I)⁻¹ *
        circleIntegral (fun z ↦ G z / F z) 0
          ((contourBank p pStar).rho j)).re)) :
    |thetaHatSpec p pStar cStar gcode data - target| ≤
      ordinaryContourPerturbationConstant p C_G mu nu * (d + e) +
        1 / (max p.n 1 : ℝ) := by
  rcases hgood with ⟨hd, he, hCG, hmu, hnu, hmuEq, hnuEq, hsmall,
    j, N, hj, hdecoded, hN, hevalMargin, hboundary⟩
  let input := canonicalRepresentedInput p pStar cStar gcode data
  let B := contourBank p pStar
  let final := evaluationEnclosure input B j N
  have hmargin : 0 < (pilotModulus input B 1 j).lo :=
    lt_of_lt_of_le (div_pos B.aStarRat_pos (by norm_num)) hevalMargin
  let ev := spectralEvaluationEvaluator input B j N
    ⟨(pilotModulus input B 1 j).lo, hmargin⟩
  have hprogram : (ordinaryFiniteRationalResult p pStar cStar gcode data).raw =
      rationalMidpoint final.re := by
    simp only [selectedContour, pilotOutcome, canonicalRepresentedInput] at hj
    simp only [pilotOutcome, canonicalRepresentedInput] at hdecoded
    simp [ordinaryFiniteRationalResult, ordinarySpectralProgram,
      instrumentedSpectralProgram, spectralProgramWith, canonicalRepresentedInput,
      input, B, hj, hdecoded, hevalMargin, final]
    rw [dif_pos (by simpa [input, B, canonicalRepresentedInput] using hevalMargin)]
  have hNmax : max N 1 = N := max_eq_left hN
  have hNmaxReal : max (N : ℝ) 1 = N := max_eq_left (by exact_mod_cast hN)
  have hspec := ((representedNodeSpecifications p) pStar cStar gcode data).1 j
  have hevalSpec := hspec.2.2.2 N
  dsimp [EvaluationEnclosureSpecification, final, input, B] at hevalSpec
  rcases hevalSpec with ⟨hwidth, hcontains, _⟩
  -- Restate with the bank in the syntactic form `contourBank p pStar` (the two
  -- spellings are definitionally equal) so that the `rho_value` rewrite in the
  -- `simpa` below can fire on it.
  have hevContains : (evaluationEnclosure input B j N).Contains
      (normalizedContourValue (spectralEvaluationEvaluator input B j N
        ⟨(pilotModulus input B 1 j).lo, hmargin⟩)) := (hcontains hmargin).2.1
  have hsemantic : final.Contains
      (((N : ℂ) * (2 * Real.pi : ℂ) * Complex.I)⁻¹ *
        circleIntegral
          (fun z ↦ semanticEmpiricalG p gcode data (spectralFold p.n 1) 0 z /
            semanticEmpiricalF p gcode data (spectralFold p.n 1) 0 z)
          0 (B.rho j)) := by
    simpa [normalizedContourValue, ev, spectralEvaluationEvaluator, input, B, hNmax,
      hNmaxReal, (contourBank p pStar).rho_value,
      spectralNumeratorMap_value_canonical, spectralDenominatorMap_value_canonical,
      circleContourIntegral_eq_circleIntegral] using hevContains
  have hmid := midpoint_error_le_half_width hsemantic.1
  have hrhoPos : 0 < B.rho j := by
    have hR0 : 0 < zeroRadius p := by
      rw [← pStar.R0_value]
      exact lt_of_lt_of_le (by exact_mod_cast pStar.R0Name.lower_pos)
        pStar.R0Name.lower_le_value
    dsimp [B, contourBank]
    simp only [CertifiedReal.add, CertifiedReal.ofRat, pStar.R0_value]
    positivity
  have hratio := circleIntegral_ratio_difference_bound
    (rho := B.rho j) (d := d) (e := e) (C := C_G) (mu := mu) (nu := nu)
    hrhoPos.le hd he hCG hmu hnu hsmall
    (hratioIntegrable j hj).1 (hratioIntegrable j hj).2 hboundary
  have hnormN : ‖((N : ℂ) * (2 * Real.pi : ℂ) * Complex.I)⁻¹‖ =
      (N * (2 * Real.pi))⁻¹ := by
    simp [hN, Real.pi_pos.le]
  have hscaled :
      ‖((N : ℂ) * (2 * Real.pi : ℂ) * Complex.I)⁻¹ *
          circleIntegral
            (fun z ↦ semanticEmpiricalG p gcode data (spectralFold p.n 1) 0 z /
              semanticEmpiricalF p gcode data (spectralFold p.n 1) 0 z) 0 (B.rho j) -
        ((N : ℂ) * (2 * Real.pi : ℂ) * Complex.I)⁻¹ *
          circleIntegral (fun z ↦ G z / F z) 0 (B.rho j)‖ ≤
        B.rho j * (e / nu + C_G * d / (mu * nu)) / N := by
    rw [← mul_sub, norm_mul, hnormN]
    calc
      (N * (2 * Real.pi))⁻¹ *
          ‖circleIntegral
              (fun z ↦ semanticEmpiricalG p gcode data (spectralFold p.n 1) 0 z /
                semanticEmpiricalF p gcode data (spectralFold p.n 1) 0 z) 0 (B.rho j) -
            circleIntegral (fun z ↦ G z / F z) 0 (B.rho j)‖ ≤
          (N * (2 * Real.pi))⁻¹ *
            (2 * Real.pi * B.rho j * (e / nu + C_G * d / (mu * nu))) := by
              gcongr
      _ = B.rho j * (e / nu + C_G * d / (mu * nu)) / N := by
        field_simp [show (N : ℝ) ≠ 0 by exact_mod_cast (Nat.ne_of_gt hN), Real.pi_ne_zero]
  have hclip : |thetaHatSpec p pStar cStar gcode data - target| ≤
      |((ordinaryFiniteRationalResult p pStar cStar gcode data).raw : ℝ) - target| := by
    rw [thetaHatSpec_eq_clip_finite_rational]
    have hC : -p.Ctheta ≤ p.Ctheta := by linarith [p.constants_pos.1]
    have htmem : target ∈ Set.Icc (-p.Ctheta) p.Ctheta :=
      ⟨neg_le_of_abs_le htarget, le_of_abs_le htarget⟩
    have hcontract := Set.abs_projIcc_sub_projIcc
      (a := -p.Ctheta) (b := p.Ctheta) hC
      (c := ((ordinaryFiniteRationalResult p pStar cStar gcode data).raw : ℝ))
      (d := target)
    rw [Set.projIcc_of_mem hC htmem] at hcontract
    simpa [Set.projIcc, max_min_distrib_left, min_comm, max_comm, hC] using hcontract
  rw [hprogram] at hclip
  have hrealScaled :
      |(((N : ℂ) * (2 * Real.pi : ℂ) * Complex.I)⁻¹ *
          circleIntegral
            (fun z ↦ semanticEmpiricalG p gcode data (spectralFold p.n 1) 0 z /
              semanticEmpiricalF p gcode data (spectralFold p.n 1) 0 z)
            0 (B.rho j)).re - target| ≤
        B.rho j * (e / nu + C_G * d / (mu * nu)) / N := by
    rw [hidentify j N hj hdecoded]
    exact (Complex.abs_re_le_norm _).trans hscaled
  let empiricalTarget : ℝ :=
    (((N : ℂ) * (2 * Real.pi : ℂ) * Complex.I)⁻¹ *
      circleIntegral
        (fun z ↦ semanticEmpiricalG p gcode data (spectralFold p.n 1) 0 z /
          semanticEmpiricalF p gcode data (spectralFold p.n 1) 0 z)
        0 (B.rho j)).re
  calc
    |thetaHatSpec p pStar cStar gcode data - target|
        ≤ |((rationalMidpoint final.re : ℚ) : ℝ) - target| := hclip
    _ ≤ |((rationalMidpoint final.re : ℚ) : ℝ) - empiricalTarget| +
          |empiricalTarget - target| := abs_sub_le _ _ _
    _ ≤ (final.re.width : ℝ) / 2 +
          B.rho j * (e / nu + C_G * d / (mu * nu)) / N :=
      add_le_add hmid hrealScaled
    _ ≤ ordinaryContourPerturbationConstant p C_G mu nu * (d + e) +
          1 / (max p.n 1 : ℝ) := by
      have hrho : B.rho j < searchRadius p := by
        dsimp [B, contourBank]
        simp only [CertifiedReal.add, CertifiedReal.ofRat, pStar.R0_value]
        rw [pStar.searchRadius_contract]
        have hjBound : (j : ℕ) ≤ 2 ^
            (4 * positiveCeil
                (certifiedIntervalArithmetic.refine pStar.psietaName.name errorOne).hi ^ 2 *
              (positiveCeil
                (certifiedIntervalArithmetic.refine pStar.R1Name.name errorOne).hi + 2) ^ 3 + 2) :=
          Nat.le_of_lt_succ j.isLt
        norm_num at hjBound ⊢
        have hq := rat_grid_lt_one
          (4 * positiveCeil
              (certifiedIntervalArithmetic.refine pStar.psietaName.name errorOne).hi ^ 2 *
            (positiveCeil
              (certifiedIntervalArithmetic.refine pStar.R1Name.name errorOne).hi + 2) ^ 3 + 2)
          (j : ℕ) hjBound
        norm_num at hq
        have hq' :
            (1 / 4 : ℚ) + (j : ℕ) * (1 / 2 : ℚ) ^
              (4 * positiveCeil
                  (certifiedIntervalArithmetic.refine pStar.psietaName.name errorOne).hi ^ 2 *
                (positiveCeil
                  (certifiedIntervalArithmetic.refine pStar.R1Name.name errorOne).hi + 2) ^ 3 + 3) < 1 := by
          simpa [Nat.add_assoc] using hq
        have hc : ((↑((1 / 4 : ℚ) + (j : ℕ) * (1 / 2 : ℚ) ^
            (4 * positiveCeil
                (certifiedIntervalArithmetic.refine pStar.psietaName.name errorOne).hi ^ 2 *
              (positiveCeil
                (certifiedIntervalArithmetic.refine pStar.R1Name.name errorOne).hi + 2) ^ 3 + 3)) : ℝ) <
            (↑(1 : ℚ) : ℝ)) := Rat.cast_lt.mpr hq'
        simpa using hc
      have hreWidthQ : final.re.width ≤ 2 / (max p.n 1 : ℚ) := by
        change max final.re.width final.im.width ≤ 2 / (max p.n 1 : ℚ) at hwidth
        exact (le_max_left _ _).trans hwidth
      have hreWidthR : (final.re.width : ℝ) ≤ 2 / (max p.n 1 : ℝ) := by
        have hcast := (Rat.cast_le (K := ℝ)).mpr hreWidthQ
        norm_num at hcast ⊢
        push_cast at hcast
        simpa using hcast
      have hwidthHalf : (final.re.width : ℝ) / 2 ≤
          1 / (max p.n 1 : ℝ) := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
        simpa [div_eq_mul_inv, mul_comm] using hreWidthR
      dsimp [ordinaryContourPerturbationConstant]
      have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
      have hratio' : B.rho j * (e / nu + C_G * d / (mu * nu)) / N ≤
          searchRadius p * max nu⁻¹ (C_G * (mu * nu)⁻¹) * (d + e) := by
        have hnuInv : 0 ≤ nu⁻¹ := inv_nonneg.mpr hnu.le
        have hmunuInv : 0 ≤ (mu * nu)⁻¹ := inv_nonneg.mpr (mul_nonneg hmu.le hnu.le)
        calc
          B.rho j * (e / nu + C_G * d / (mu * nu)) / N
              ≤ searchRadius p * (e / nu + C_G * d / (mu * nu)) := by
                have hsum : 0 ≤ e / nu + C_G * d / (mu * nu) := by positivity
                calc
                  _ ≤ B.rho j * (e / nu + C_G * d / (mu * nu)) :=
                    div_le_self (mul_nonneg hrhoPos.le hsum) hNreal
                  _ ≤ _ := mul_le_mul_of_nonneg_right hrho.le hsum
          _ ≤ _ := by
            have heBound : e / nu ≤ max nu⁻¹ (C_G * (mu * nu)⁻¹) * e := by
              rw [div_eq_mul_inv]
              simpa [mul_comm] using
                mul_le_mul_of_nonneg_right (le_max_left nu⁻¹ (C_G * (mu * nu)⁻¹)) he
            have hdBound : C_G * d / (mu * nu) ≤
                max nu⁻¹ (C_G * (mu * nu)⁻¹) * d := by
              calc
                C_G * d / (mu * nu) = (C_G * (mu * nu)⁻¹) * d := by ring
                _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right nu⁻¹
                  (C_G * (mu * nu)⁻¹)) hd
            have hR : 0 ≤ searchRadius p := by linarith [hrhoPos]
            nlinarith
      simpa [mul_inv, mul_assoc, mul_comm, mul_left_comm, add_comm] using
        add_le_add hwidthHalf hratio'
/- The previous proof script is retained for Stage 3 adaptation; the repaired
local schedule and normalized-enclosure specification change its central
soundness input.
  rcases hgood with ⟨hd, he, hCG, hmu, hnu, hmuEq, hnuEq, hsmall,
    j, N, hj, hdecoded, hN, hevalMargin, hboundary⟩
  let input := canonicalRepresentedInput p pStar cStar gcode data
  let B := contourBank p pStar
  let final := evaluationEnclosure input B j N
  have hmargin : 0 < (pilotModulus input B 1 j).lo :=
    lt_of_lt_of_le (div_pos B.aStarRat_pos (by norm_num)) hevalMargin
  let ev := spectralEvaluationEvaluator input B j N
    ⟨(pilotModulus input B 1 j).lo, hmargin⟩
  have hprogram : (ordinaryFiniteRationalResult p pStar cStar gcode data).raw =
      rationalMidpoint final.re := by
    simp only [ordinaryFiniteRationalResult, ordinarySpectralProgram,
      instrumentedSpectralProgram, selectedContour, input, B]
    rw [hj, hdecoded, dif_pos hevalMargin]
  have hNmax : max N 1 = N := max_eq_left hN
  have hspec := (representedNodeSpecifications p) pStar cStar gcode data j
  have hevalSpec := hspec.2.2.2 N
  dsimp [EvaluationEnclosureSpecification, final, input, B] at hevalSpec
  rcases hevalSpec with ⟨hwidth, hcontains, _⟩
  have hevContains := (hcontains hmargin).2
  have hsemantic : final.Contains
      (((N : ℂ) * (2 * Real.pi : ℂ) * Complex.I)⁻¹ *
        circleIntegral
          (fun z ↦ semanticEmpiricalG p gcode data (spectralFold p.n 1) 0 z /
            semanticEmpiricalF p gcode data (spectralFold p.n 1) 0 z)
          0 (B.rho j)) := by
    dsimp [normalizedContourValue, ev] at hevContains
    rw [spectralNumeratorMap_value_canonical,
      spectralDenominatorMap_value_canonical, circleContourIntegral_eq_circleIntegral,
      hNmax] at hevContains
    exact hevContains
  have hmid := midpoint_error_le_half_width hsemantic.1
  have hratio := circleIntegral_ratio_difference_bound
    (rho := B.rho j) (d := d) (e := e) (C := C_G) (mu := mu) (nu := nu)
    (contourBank_rho_pos p pStar j).le hd he hCG hmu hnu hsmall
    (hratioIntegrable j hj).1 (hratioIntegrable j hj).2 hboundary
  have hnormN : ‖((N : ℂ) * (2 * Real.pi : ℂ) * Complex.I)⁻¹‖ =
      (N * (2 * Real.pi))⁻¹ := by
    simp [hN, Real.pi_pos.le]
  have hscaled :
      ‖((N : ℂ) * (2 * Real.pi : ℂ) * Complex.I)⁻¹ *
          circleIntegral
            (fun z ↦ semanticEmpiricalG p gcode data (spectralFold p.n 1) 0 z /
              semanticEmpiricalF p gcode data (spectralFold p.n 1) 0 z) 0 (B.rho j) -
        ((N : ℂ) * (2 * Real.pi : ℂ) * Complex.I)⁻¹ *
          circleIntegral (fun z ↦ G z / F z) 0 (B.rho j)‖ ≤
        B.rho j * (e / nu + C_G * d / (mu * nu)) / N := by
    rw [← mul_sub, norm_mul, hnormN]
    calc
      (N * (2 * Real.pi))⁻¹ *
          ‖circleIntegral
              (fun z ↦ semanticEmpiricalG p gcode data (spectralFold p.n 1) 0 z /
                semanticEmpiricalF p gcode data (spectralFold p.n 1) 0 z) 0 (B.rho j) -
            circleIntegral (fun z ↦ G z / F z) 0 (B.rho j)‖ ≤
          (N * (2 * Real.pi))⁻¹ *
            (2 * Real.pi * B.rho j * (e / nu + C_G * d / (mu * nu))) := by
              gcongr
      _ = B.rho j * (e / nu + C_G * d / (mu * nu)) / N := by
        field_simp [show (N : ℝ) ≠ 0 by exact_mod_cast (Nat.ne_of_gt hN), Real.pi_ne_zero]
        ring
  have hclip : |thetaHatSpec p pStar cStar gcode data - target| ≤
      |((ordinaryFiniteRationalResult p pStar cStar gcode data).raw : ℝ) - target| := by
    rw [thetaHatSpec_eq_clip_finite_rational]
    exact abs_sub_le_abs_sub (neg_le_of_abs_le htarget) (le_of_abs_le htarget)
  rw [hprogram] at hclip
  have hrealScaled :
      |(((N : ℂ) * (2 * Real.pi : ℂ) * Complex.I)⁻¹ *
          circleIntegral
            (fun z ↦ semanticEmpiricalG p gcode data (spectralFold p.n 1) 0 z /
              semanticEmpiricalF p gcode data (spectralFold p.n 1) 0 z)
            0 (B.rho j)).re - target| ≤
        B.rho j * (e / nu + C_G * d / (mu * nu)) / N := by
    rw [hidentify j N hj hdecoded]
    exact (abs_re_le_norm _).trans hscaled
  calc
    |thetaHatSpec p pStar cStar gcode data - target|
        ≤ |((rationalMidpoint final.re : ℚ) : ℝ) - target| := hclip
    _ ≤ |((rationalMidpoint final.re : ℚ) : ℝ) -
          ((((N : ℂ) * (2 * Real.pi : ℂ) * Complex.I)⁻¹ *
            circleIntegral
              (fun z ↦ semanticEmpiricalG p gcode data (spectralFold p.n 1) 0 z /
                semanticEmpiricalF p gcode data (spectralFold p.n 1) 0 z)
              0 (B.rho j)).re| +
          |((((N : ℂ) * (2 * Real.pi : ℂ) * Complex.I)⁻¹ *
            circleIntegral
              (fun z ↦ semanticEmpiricalG p gcode data (spectralFold p.n 1) 0 z /
                semanticEmpiricalF p gcode data (spectralFold p.n 1) 0 z)
              0 (B.rho j)).re - target| := abs_sub_le _ _ _
    _ ≤ (final.re.width : ℝ) / 2 +
          B.rho j * (e / nu + C_G * d / (mu * nu)) / N :=
      add_le_add hmid hrealScaled
    _ ≤ ordinaryContourPerturbationConstant p C_G mu nu * (d + e) +
          1 / (max p.n 1 : ℝ) := by
      have hrho := (contourBank_contract p pStar).2.2.2.2.2.2.2.2.2.2.2.2.2.2 j |>.2
      dsimp [ordinaryContourPerturbationConstant]
      norm_num at hwidth ⊢
      push_cast at hwidth
      have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
      have hratio' : B.rho j * (e / nu + C_G * d / (mu * nu)) / N ≤
          searchRadius p * max nu⁻¹ (C_G * (mu * nu)⁻¹) * (d + e) := by
        have hnuInv : 0 ≤ nu⁻¹ := inv_nonneg.mpr hnu.le
        have hmunuInv : 0 ≤ (mu * nu)⁻¹ := inv_nonneg.mpr (mul_nonneg hmu.le hnu.le)
        calc
          B.rho j * (e / nu + C_G * d / (mu * nu)) / N
              ≤ searchRadius p * (e / nu + C_G * d / (mu * nu)) := by
                have hsum : 0 ≤ e / nu + C_G * d / (mu * nu) := by positivity
                calc
                  _ ≤ B.rho j * (e / nu + C_G * d / (mu * nu)) := by
                    rw [div_le_iff₀ (by positivity : (0 : ℝ) < N)]
                    nlinarith
                  _ ≤ _ := mul_le_mul_of_nonneg_right hrho.le hsum
          _ ≤ _ := by
            have heBound : e / nu ≤ max nu⁻¹ (C_G * (mu * nu)⁻¹) * e := by
              rw [div_eq_mul_inv]
              exact mul_le_mul_of_nonneg_right (le_max_left _ _) he
            have hdBound : C_G * d / (mu * nu) ≤
                max nu⁻¹ (C_G * (mu * nu)⁻¹) * d := by
              rw [div_eq_mul_inv]
              nlinarith [mul_le_mul_of_nonneg_right (le_max_right nu⁻¹
                (C_G * (mu * nu)⁻¹)) hd]
            have hR : 0 ≤ searchRadius p := by linarith [hrho.1]
            nlinarith
      nlinarith
-/

/-! PRIOR PROOF (carry-over: auto; signature-unchanged `thetaHatSpec_good_event_exact_contour_perturbation`). Stage 3: replace the
   the placeholder above with this body, run diagnostics, and patch failures only.
   := by  rcases hgood with ⟨hd, he, hCG, hmu, hnu, hmuEq, hnuEq, hsmall,
    j, N, hj, hdecoded, hN, hevalMargin, hboundary⟩
  let input := canonicalRepresentedInput p pStar cStar gcode data
  let B := contourBank p pStar
  let final := evaluationEnclosure input B j N
  have hmargin : 0 < (pilotModulus input B 1 j).lo :=
    lt_of_lt_of_le (div_pos B.aStarRat_pos (by norm_num)) hevalMargin
  let ev := spectralEvaluationEvaluator input B j N
    ⟨(pilotModulus input B 1 j).lo, hmargin⟩
  have hprogram : (ordinaryFiniteRationalResult p pStar cStar gcode data).raw =
      rationalMidpoint final.re := by
    simp only [ordinaryFiniteRationalResult, ordinarySpectralProgram,
      instrumentedSpectralProgram, selectedContour, input, B]
    rw [hj, hdecoded, dif_pos hevalMargin]
  have hNmax : max N 1 = N := max_eq_left hN
  have hspec := (representedNodeSpecifications p) pStar cStar gcode data j
  have hevalSpec := hspec.2.2.2 N
  dsimp [EvaluationEnclosureSpecification, final, input, B] at hevalSpec
  rcases hevalSpec with ⟨hwidth, hcontains, _⟩
  have hevContains := (hcontains hmargin).2
  have hsemantic : final.Contains
      (((N : ℂ) * (2 * Real.pi : ℂ) * Complex.I)⁻¹ *
        circleIntegral
          (fun z ↦ semanticEmpiricalG p gcode data (spectralFold p.n 1) 0 z /
            semanticEmpiricalF p gcode data (spectralFold p.n 1) 0 z)
          0 (B.rho j)) := by
    dsimp [normalizedContourValue, ev] at hevContains
    rw [spectralNumeratorMap_value_canonical,
      spectralDenominatorMap_value_canonical, circleContourIntegral_eq_circleIntegral,
      hNmax] at hevContains
    exact hevContains
  have hmid := midpoint_error_le_half_width hsemantic.1
  have hratio := circleIntegral_ratio_difference_bound
    (rho := B.rho j) (d := d) (e := e) (C := C_G) (mu := mu) (nu := nu)
    (contourBank_rho_pos p pStar j).le hd he hCG hmu hnu hsmall
    (hratioIntegrable j hj).1 (hratioIntegrable j hj).2 hboundary
  have hnormN : ‖((N : ℂ) * (2 * Real.pi : ℂ) * Complex.I)⁻¹‖ =
      (N * (2 * Real.pi))⁻¹ := by
    simp [hN, Real.pi_pos.le]
  have hscaled :
      ‖((N : ℂ) * (2 * Real.pi : ℂ) * Complex.I)⁻¹ *
          circleIntegral
            (fun z ↦ semanticEmpiricalG p gcode data (spectralFold p.n 1) 0 z /
              semanticEmpiricalF p gcode data (spectralFold p.n 1) 0 z) 0 (B.rho j) -
        ((N : ℂ) * (2 * Real.pi : ℂ) * Complex.I)⁻¹ *
          circleIntegral (fun z ↦ G z / F z) 0 (B.rho j)‖ ≤
        B.rho j * (e / nu + C_G * d / (mu * nu)) / N := by
    rw [← mul_sub, norm_mul, hnormN]
    calc
      (N * (2 * Real.pi))⁻¹ *
          ‖circleIntegral
              (fun z ↦ semanticEmpiricalG p gcode data (spectralFold p.n 1) 0 z /
                semanticEmpiricalF p gcode data (spectralFold p.n 1) 0 z) 0 (B.rho j) -
            circleIntegral (fun z ↦ G z / F z) 0 (B.rho j)‖ ≤
          (N * (2 * Real.pi))⁻¹ *
            (2 * Real.pi * B.rho j * (e / nu + C_G * d / (mu * nu))) := by
              gcongr
      _ = B.rho j * (e / nu + C_G * d / (mu * nu)) / N := by
        field_simp [show (N : ℝ) ≠ 0 by exact_mod_cast (Nat.ne_of_gt hN), Real.pi_ne_zero]
        ring
  have hclip : |thetaHatSpec p pStar cStar gcode data - target| ≤
      |((ordinaryFiniteRationalResult p pStar cStar gcode data).raw : ℝ) - target| := by
    rw [thetaHatSpec_eq_clip_finite_rational]
    exact abs_sub_le_abs_sub (neg_le_of_abs_le htarget) (le_of_abs_le htarget)
  rw [hprogram] at hclip
  have hrealScaled :
      |(((N : ℂ) * (2 * Real.pi : ℂ) * Complex.I)⁻¹ *
          circleIntegral
            (fun z ↦ semanticEmpiricalG p gcode data (spectralFold p.n 1) 0 z /
              semanticEmpiricalF p gcode data (spectralFold p.n 1) 0 z)
            0 (B.rho j)).re - target| ≤
        B.rho j * (e / nu + C_G * d / (mu * nu)) / N := by
    rw [hidentify j N hj hdecoded]
    exact (abs_re_le_norm _).trans hscaled
  calc
    |thetaHatSpec p pStar cStar gcode data - target|
        ≤ |((rationalMidpoint final.re : ℚ) : ℝ) - target| := hclip
    _ ≤ |((rationalMidpoint final.re : ℚ) : ℝ) -
          ((((N : ℂ) * (2 * Real.pi : ℂ) * Complex.I)⁻¹ *
            circleIntegral
              (fun z ↦ semanticEmpiricalG p gcode data (spectralFold p.n 1) 0 z /
                semanticEmpiricalF p gcode data (spectralFold p.n 1) 0 z)
              0 (B.rho j)).re| +
          |((((N : ℂ) * (2 * Real.pi : ℂ) * Complex.I)⁻¹ *
            circleIntegral
              (fun z ↦ semanticEmpiricalG p gcode data (spectralFold p.n 1) 0 z /
                semanticEmpiricalF p gcode data (spectralFold p.n 1) 0 z)
              0 (B.rho j)).re - target| := abs_sub_le _ _ _
    _ ≤ (final.re.width : ℝ) / 2 +
          B.rho j * (e / nu + C_G * d / (mu * nu)) / N :=
      add_le_add hmid hrealScaled
    _ ≤ ordinaryContourPerturbationConstant p C_G mu nu * (d + e) +
          1 / (max p.n 1 : ℝ) := by
      have hrho := (contourBank_contract p pStar).2.2.2.2.2.2.2.2.2.2.2.2.2.2 j |>.2
      dsimp [ordinaryContourPerturbationConstant]
      norm_num at hwidth ⊢
      push_cast at hwidth
      have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
      have hratio' : B.rho j * (e / nu + C_G * d / (mu * nu)) / N ≤
          searchRadius p * max nu⁻¹ (C_G * (mu * nu)⁻¹) * (d + e) := by
        have hnuInv : 0 ≤ nu⁻¹ := inv_nonneg.mpr hnu.le
        have hmunuInv : 0 ≤ (mu * nu)⁻¹ := inv_nonneg.mpr (mul_nonneg hmu.le hnu.le)
        calc
          B.rho j * (e / nu + C_G * d / (mu * nu)) / N
              ≤ searchRadius p * (e / nu + C_G * d / (mu * nu)) := by
                have hsum : 0 ≤ e / nu + C_G * d / (mu * nu) := by positivity
                calc
                  _ ≤ B.rho j * (e / nu + C_G * d / (mu * nu)) := by
                    rw [div_le_iff₀ (by positivity : (0 : ℝ) < N)]
                    nlinarith
                  _ ≤ _ := mul_le_mul_of_nonneg_right hrho.le hsum
          _ ≤ _ := by
            have heBound : e / nu ≤ max nu⁻¹ (C_G * (mu * nu)⁻¹) * e := by
              rw [div_eq_mul_inv]
              exact mul_le_mul_of_nonneg_right (le_max_left _ _) he
            have hdBound : C_G * d / (mu * nu) ≤
                max nu⁻¹ (C_G * (mu * nu)⁻¹) * d := by
              rw [div_eq_mul_inv]
              nlinarith [mul_le_mul_of_nonneg_right (le_max_right nu⁻¹
                (C_G * (mu * nu)⁻¹)) hd]
            have hR : 0 ≤ searchRadius p := by linarith [hrho.1]
            nlinarith
      nlinarith

-/
end CausalSmith.Stat.SaPlmCumulantConverse
