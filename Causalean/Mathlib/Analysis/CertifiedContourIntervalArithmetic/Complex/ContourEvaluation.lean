import Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Complex.ContourProgram

/-!
# Certified finite contour evaluation

This module proves that scheduled rational contour quadrature encloses the normalized circle integral and attains its requested real-coordinate width.
-/

open scoped Interval
open MeasureTheory Set intervalIntegral

namespace Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Complex

open Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic

/-- The canceled unit-parameter integral equals the normalized exact circle
contour integral whenever the denominator is nonzero along the circle. -/
theorem normalizedContourIntegral_eq (program : ContourProgram) (schedule : Schedule)
    (hden : ∀ u ∈ Icc (0 : ℝ) 1,
      program.denominator.value
        ((program.radius : ℂ) * Complex.exp (((2 : ℝ) * Real.pi * u) * Complex.I)) ≠ 0) :
    program.normalizedContourIntegral =
      ∫ u in (0 : ℝ)..1, program.normalizedIntegrand schedule u := by
  rw [ContourProgram.normalizedContourIntegral, CircleMesh.circleContourIntegral]
  calc
    (∫ u in (0 : ℝ)..1,
        CircleMesh.circleIntegrand
          (fun z => program.numerator.value z / program.denominator.value z)
          0 program.radius u) /
        (((2 : ℝ) * Real.pi : ℂ) * Complex.I) =
      ∫ u in (0 : ℝ)..1,
        CircleMesh.circleIntegrand
          (fun z => program.numerator.value z / program.denominator.value z)
          0 program.radius u /
          (((2 : ℝ) * Real.pi : ℂ) * Complex.I) :=
        (intervalIntegral.integral_div _ _).symm
    _ = ∫ u in (0 : ℝ)..1, program.normalizedIntegrand schedule u := by
      apply intervalIntegral.integral_congr
      intro u hu
      simp only [CircleMesh.circleIntegrand, CircleMesh.circleMap,
        CircleMesh.circleTangent, ContourProgram.normalizedIntegrand, zero_add]
      have htwoPi : (((2 : ℝ) * Real.pi : ℂ) * Complex.I) ≠ 0 := by
        exact mul_ne_zero
          (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
          Complex.I_ne_zero
      have huIcc : u ∈ Icc (0 : ℝ) 1 := by
        simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hu
      have hdenu := hden u huIcc
      field_simp [htwoPi, hdenu]
      norm_num
      ring_nf

/-- Every certified finite endpoint rectangle contains the exact normalized integrand. -/
theorem integrandNodes_sound (program : ContourProgram) (schedule : Schedule)
    (certificate : DenominatorCertificate program schedule) {k : ℕ}
    (hk : k ≤ schedule.mesh) :
    (program.integrandNodes schedule certificate k).Contains
      (program.normalizedIntegrand schedule (CircleMesh.meshPoint schedule.mesh k)) := by
  have hnode : (program.nodeBox schedule k).Contains
      (exactCircleNode program.radius schedule k) := by
    exact circleNode_sound program.radius schedule hk
  have hnum := program.numerator.sound hnode schedule.fuel
  have hden := program.denominator.sound hnode schedule.fuel
  have hquot := ComplexRatInterval.div_sound (certificate.away k hk) hnum hden
  have hmul := ComplexRatInterval.mul_sound hquot hnode
  simpa [ContourProgram.integrandNodes, hk, ContourProgram.nodeBox,
    ContourProgram.normalizedIntegrand, exactCircleNode, CircleMesh.meshPoint] using hmul

/-- The scheduled node-width bound follows compositionally from circle input
precision, both map error moduli, their amplification fields, rational
magnitude bounds, guarded-division separation, and primitive width lemmas. -/
theorem integrandNodes_width_le_propagation (program : ContourProgram)
    (bounds : ContourValueBounds program) (separation : PosRat)
    (scheduled : CertifiedProgramSchedule program bounds separation)
    (certificate : DenominatorCertificate program scheduled.schedule)
    (hseparation : separation.1 ≤ certificate.separation) {k : ℕ}
    (hk : k ≤ scheduled.schedule.mesh) :
    (program.integrandNodes scheduled.schedule certificate k).width ≤
      program.nodePropagationBound bounds separation.1 scheduled.target.1 := by
  let schedule := scheduled.schedule
  let node := program.nodeBox schedule k
  let numerator := program.numerator.eval node schedule.fuel
  let denominator := program.denominator.eval node schedule.fuel
  let numeratorWidth := scheduled.target.1 +
    program.numerator.amplification * scheduled.target.1
  let denominatorWidth := scheduled.target.1 +
    program.denominator.amplification * scheduled.target.1
  let numeratorMax := bounds.numerator + numeratorWidth
  let denominatorMax := bounds.denominator + denominatorWidth
  let divisionMax := 2 * numeratorMax * denominatorMax
  let divisionWidth :=
    2 * (numeratorMax * denominatorWidth + denominatorMax * numeratorWidth)
  let normWidth := 4 * denominatorMax * denominatorWidth
  let quotientWidth := divisionMax * normWidth / separation.1 ^ 2 +
    divisionWidth / separation.1
  have hnodeWidth : node.width ≤ scheduled.target.1 := by
    exact circleNode_width_at_selected_precision program.radius program.radius_pos.le
      schedule scheduled.target scheduled.inputPrecision_eq scheduled.circleFuel_le hk
  have hnodeContains : node.Contains (exactCircleNode program.radius schedule k) := by
    exact circleNode_sound program.radius schedule hk
  have hnumContains : numerator.Contains
      (program.numerator.value (exactCircleNode program.radius schedule k)) := by
    exact program.numerator.sound hnodeContains schedule.fuel
  have hdenContains : denominator.Contains
      (program.denominator.value (exactCircleNode program.radius schedule k)) := by
    exact program.denominator.sound hnodeContains schedule.fuel
  have hnumAlgorithm : program.numerator.algorithmError schedule.fuel ≤
      scheduled.target.1 := by
    exact CertifiedComplexMap.algorithmError_le_of_modulus scheduled.numeratorFuel_le
  have hdenAlgorithm : program.denominator.algorithmError schedule.fuel ≤
      scheduled.target.1 := by
    exact CertifiedComplexMap.algorithmError_le_of_modulus scheduled.denominatorFuel_le
  have hnumWidth : numerator.width ≤ numeratorWidth := by
    calc
      numerator.width ≤ program.numerator.algorithmError schedule.fuel +
          program.numerator.amplification * node.width :=
        program.numerator.width_le node schedule.fuel
      _ ≤ scheduled.target.1 +
          program.numerator.amplification * scheduled.target.1 := by
        exact add_le_add hnumAlgorithm
          (mul_le_mul_of_nonneg_left hnodeWidth
            program.numerator.amplification_nonneg)
      _ = numeratorWidth := rfl
  have hdenWidth : denominator.width ≤ denominatorWidth := by
    calc
      denominator.width ≤ program.denominator.algorithmError schedule.fuel +
          program.denominator.amplification * node.width :=
        program.denominator.width_le node schedule.fuel
      _ ≤ scheduled.target.1 +
          program.denominator.amplification * scheduled.target.1 := by
        exact add_le_add hdenAlgorithm
          (mul_le_mul_of_nonneg_left hnodeWidth
            program.denominator.amplification_nonneg)
      _ = denominatorWidth := rfl
  have hmesh : CircleMesh.meshPoint schedule.mesh k ∈ Set.Icc (0 : ℝ) 1 :=
    CircleMesh.meshPoint_mem schedule.mesh_pos hk
  have hnumValueBound :
      max |(program.numerator.value
        (exactCircleNode program.radius schedule k)).re|
        |(program.numerator.value
        (exactCircleNode program.radius schedule k)).im| ≤ (bounds.numerator : ℝ) := by
    simpa [exactCircleNode, CircleMesh.meshPoint] using
      bounds.numerator_bound (CircleMesh.meshPoint schedule.mesh k) hmesh
  have hdenValueBound :
      max |(program.denominator.value
        (exactCircleNode program.radius schedule k)).re|
        |(program.denominator.value
        (exactCircleNode program.radius schedule k)).im| ≤ (bounds.denominator : ℝ) := by
    simpa [exactCircleNode, CircleMesh.meshPoint] using
      bounds.denominator_bound (CircleMesh.meshPoint schedule.mesh k) hmesh
  have hnumMax : numerator.maxAbs ≤ numeratorMax := by
    exact (ComplexRatInterval.maxAbs_le_of_contains_width hnumContains
      hnumValueBound hnumWidth)
  have hdenMax : denominator.maxAbs ≤ denominatorMax := by
    exact (ComplexRatInterval.maxAbs_le_of_contains_width hdenContains
      hdenValueBound hdenWidth)
  have htarget0 : 0 ≤ scheduled.target.1 := scheduled.target.2.le
  have hnWidth0 : 0 ≤ numeratorWidth := by
    dsimp [numeratorWidth]
    nlinarith [mul_nonneg program.numerator.amplification_nonneg htarget0]
  have hdWidth0 : 0 ≤ denominatorWidth := by
    dsimp [denominatorWidth]
    nlinarith [mul_nonneg program.denominator.amplification_nonneg htarget0]
  have hnMax0 : 0 ≤ numeratorMax := by
    dsimp [numeratorMax]
    linarith [bounds.numerator_nonneg]
  have hdMax0 : 0 ≤ denominatorMax := by
    dsimp [denominatorMax]
    linarith [bounds.denominator_nonneg]
  have hdivisionMax0 : 0 ≤ divisionMax := by
    dsimp [divisionMax]
    positivity
  have hdivisionWidth0 : 0 ≤ divisionWidth := by
    dsimp [divisionWidth]
    positivity
  have hnormWidth0 : 0 ≤ normWidth := by
    dsimp [normWidth]
    positivity
  have hnumDenMax : (numerator.mul denominator.conj).maxAbs ≤ divisionMax := by
    calc
      (numerator.mul denominator.conj).maxAbs ≤
          2 * numerator.maxAbs * denominator.conj.maxAbs :=
        ComplexRatInterval.mul_maxAbs numerator denominator.conj
      _ = 2 * numerator.maxAbs * denominator.maxAbs := by
        rw [ComplexRatInterval.maxAbs_conj]
      _ ≤ 2 * numeratorMax * denominatorMax := by
        nlinarith [mul_le_mul hnumMax hdenMax
          ((abs_nonneg denominator.re.lo).trans
            ((le_max_left _ _).trans (le_max_left _ _))) hnMax0]
      _ = divisionMax := rfl
  have hnumDenWidth : (numerator.mul denominator.conj).width ≤ divisionWidth := by
    calc
      (numerator.mul denominator.conj).width ≤
          2 * (numerator.maxAbs * denominator.conj.width +
            denominator.conj.maxAbs * numerator.width) :=
        ComplexRatInterval.mul_width numerator denominator.conj
      _ = 2 * (numerator.maxAbs * denominator.width +
            denominator.maxAbs * numerator.width) := by
        rw [ComplexRatInterval.width_conj, ComplexRatInterval.maxAbs_conj]
      _ ≤ 2 * (numeratorMax * denominatorWidth +
            denominatorMax * numeratorWidth) := by
        have hnumA0 : 0 ≤ numerator.maxAbs := (abs_nonneg numerator.re.lo).trans
          ((le_max_left _ _).trans (le_max_left _ _))
        have hdenA0 : 0 ≤ denominator.maxAbs := (abs_nonneg denominator.re.lo).trans
          ((le_max_left _ _).trans (le_max_left _ _))
        nlinarith [mul_le_mul hnumMax hdenWidth
            (show 0 ≤ denominator.width from
              (RatInterval.width_nonneg denominator.re).trans (le_max_left _ _)) hnMax0,
          mul_le_mul hdenMax hnumWidth
            (show 0 ≤ numerator.width from
              (RatInterval.width_nonneg numerator.re).trans (le_max_left _ _)) hdMax0]
      _ = divisionWidth := rfl
  have hnormWidth : denominator.normSq.width ≤ normWidth := by
    calc
      denominator.normSq.width ≤ 4 * denominator.maxAbs * denominator.width :=
        ComplexRatInterval.normSq_width denominator
      _ ≤ 4 * denominatorMax * denominatorWidth := by
        nlinarith [mul_le_mul hdenMax hdenWidth
          (show 0 ≤ denominator.width from
            (RatInterval.width_nonneg denominator.re).trans (le_max_left _ _)) hdMax0]
      _ = normWidth := rfl
  have hsep : separation.1 ≤ denominator.normSq.lo :=
    hseparation.trans (certificate.lower k hk)
  have hquotientWidth :
      (numerator.div denominator (certificate.away k hk)).width ≤ quotientWidth := by
    calc
      _ ≤ (numerator.mul denominator.conj).maxAbs * denominator.normSq.width /
            separation.1 ^ 2 +
          (numerator.mul denominator.conj).width / separation.1 :=
        ComplexRatInterval.div_width (certificate.away k hk) separation.2 hsep
      _ ≤ divisionMax * normWidth / separation.1 ^ 2 +
          divisionWidth / separation.1 := by
        have hproduct := mul_le_mul hnumDenMax hnormWidth
          (RatInterval.width_nonneg denominator.normSq) hdivisionMax0
        exact add_le_add
          (div_le_div_of_nonneg_right hproduct (sq_nonneg separation.1))
          (div_le_div_of_nonneg_right hnumDenWidth separation.2.le)
      _ = quotientWidth := rfl
  have hquotientMax :
      (numerator.div denominator (certificate.away k hk)).maxAbs ≤
        divisionMax / separation.1 := by
    exact (ComplexRatInterval.div_maxAbs (certificate.away k hk)
      separation.2 hsep).trans
        (div_le_div_of_nonneg_right hnumDenMax separation.2.le)
  have hexactNorm : ‖exactCircleNode program.radius schedule k‖ = program.radius := by
    have hradius0 : (0 : ℝ) ≤ program.radius := by
      exact_mod_cast program.radius_pos.le
    simp [exactCircleNode, Complex.norm_exp, abs_of_nonneg hradius0]
  have hnodeValueBound :
      max |(exactCircleNode program.radius schedule k).re|
        |(exactCircleNode program.radius schedule k).im| ≤ (program.radius : ℝ) := by
    exact max_le ((Complex.abs_re_le_norm _).trans_eq hexactNorm)
      ((Complex.abs_im_le_norm _).trans_eq hexactNorm)
  have hnodeMax : node.maxAbs ≤ program.radius + scheduled.target.1 := by
    exact ComplexRatInterval.maxAbs_le_of_contains_width hnodeContains
      hnodeValueBound hnodeWidth
  have hquotientWidth0 : 0 ≤ quotientWidth := by
    dsimp [quotientWidth]
    exact add_nonneg
      (div_nonneg (mul_nonneg hdivisionMax0 hnormWidth0) (sq_nonneg separation.1))
      (div_nonneg hdivisionWidth0 separation.2.le)
  rw [ContourProgram.integrandNodes, dif_pos hk]
  change ((numerator.div denominator (certificate.away k hk)).mul node).width ≤ _
  calc
    ((numerator.div denominator (certificate.away k hk)).mul node).width ≤
        2 * ((numerator.div denominator (certificate.away k hk)).maxAbs * node.width +
          node.maxAbs * (numerator.div denominator (certificate.away k hk)).width) :=
      ComplexRatInterval.mul_width _ _
    _ ≤ 2 * ((divisionMax / separation.1) * scheduled.target.1 +
          (program.radius + scheduled.target.1) * quotientWidth) := by
      have hquotientA0 :
          0 ≤ (numerator.div denominator (certificate.away k hk)).maxAbs :=
        (abs_nonneg (numerator.div denominator (certificate.away k hk)).re.lo).trans
          ((le_max_left _ _).trans (le_max_left _ _))
      have hnodeA0 : 0 ≤ node.maxAbs := (abs_nonneg node.re.lo).trans
        ((le_max_left _ _).trans (le_max_left _ _))
      nlinarith [mul_le_mul hquotientMax hnodeWidth
          (show 0 ≤ node.width from
            (RatInterval.width_nonneg node.re).trans (le_max_left _ _))
          (div_nonneg hdivisionMax0 separation.2.le),
        mul_le_mul hnodeMax hquotientWidth
          (show 0 ≤ (numerator.div denominator (certificate.away k hk)).width from
            (RatInterval.width_nonneg
              (numerator.div denominator (certificate.away k hk)).re).trans
                (le_max_left _ _))
          (by linarith [program.radius_pos])]
    _ = program.nodePropagationBound bounds separation.1 scheduled.target.1 := by
      rfl

/-- The executable contour result applies promoted deterministic quadrature
and then spends the schedule's final symmetric quadrature budget. -/
def ContourProgram.evaluate (program : ContourProgram) (schedule : Schedule)
    (certificate : DenominatorCertificate program schedule) : ComplexRatInterval :=
  (CircleMesh.integralEnclosure
    (program.integrandNodes schedule certificate)
    schedule.magnitude schedule.magnitude_nonneg schedule.mesh schedule.mesh_pos).expand
      (schedule.quadratureBudget / 2)
      (div_nonneg schedule.quadratureBudget_nonneg (by norm_num))

/-- Denominator separation at all certified nodes implies nonvanishing of the
exact denominator at all mesh endpoints. -/
theorem denominator_ne_zero_at_nodes (program : ContourProgram) (schedule : Schedule)
    (certificate : DenominatorCertificate program schedule) {k : ℕ}
    (hk : k ≤ schedule.mesh) :
    program.denominator.value (exactCircleNode program.radius schedule k) ≠ 0 := by
  have hnode : (program.nodeBox schedule k).Contains
      (exactCircleNode program.radius schedule k) := by
    exact circleNode_sound program.radius schedule hk
  have hden := program.denominator.sound hnode schedule.fuel
  have hnorm := ComplexRatInterval.normSq_sound hden
  have hnorm_ne : ‖program.denominator.value
      (exactCircleNode program.radius schedule k)‖ ^ 2 ≠ 0 :=
    RatInterval.ne_zero_of_contains (certificate.away k hk) hnorm
  intro hz
  apply hnorm_ne
  simp [hz]

/-- Under a Lipschitz bound and denominator nonvanishing on the full circle,
the returned rational rectangle contains the normalized exact contour integral. -/
theorem evaluate_contains (program : ContourProgram) (schedule : Schedule)
    (certificate : DenominatorCertificate program schedule)
    (hden : ∀ u ∈ Icc (0 : ℝ) 1,
      program.denominator.value
        ((program.radius : ℂ) * Complex.exp (((2 : ℝ) * Real.pi * u) * Complex.I)) ≠ 0)
    (hLip : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖program.normalizedIntegrand schedule s - program.normalizedIntegrand schedule t‖ ≤
        (schedule.magnitude : ℝ) * |s - t|) :
    (program.evaluate schedule certificate).Contains program.normalizedContourIntegral := by
  rw [normalizedContourIntegral_eq program schedule hden]
  apply ComplexRatInterval.expand_contains
  exact CircleMesh.integralEnclosure_sound schedule.magnitude_nonneg schedule.mesh_pos
    hLip (fun k hk => integrandNodes_sound program schedule certificate hk)

/-- Uniform scheduled node widths propagate through mesh and final widening,
so both result coordinates fit within the three split budgets. -/
theorem evaluate_width (program : ContourProgram)
    (bounds : ContourValueBounds program) (separation : PosRat)
    (scheduled : CertifiedProgramSchedule program bounds separation)
    (certificate : DenominatorCertificate program scheduled.schedule)
    (hseparation : separation.1 ≤ certificate.separation) :
    (program.evaluate scheduled.schedule certificate).width ≤
      scheduled.schedule.tolerance.1 := by
  let schedule := scheduled.schedule
  have hcoordinate : ∀ k ≤ schedule.mesh,
      (program.integrandNodes schedule certificate k).re.width ≤ schedule.nodeBudget ∧
        (program.integrandNodes schedule certificate k).im.width ≤ schedule.nodeBudget := by
    intro k hk
    have h := (integrandNodes_width_le_propagation program bounds separation scheduled
      certificate hseparation hk).trans scheduled.propagation_le
    exact ⟨(le_max_left _ _).trans h, (le_max_right _ _).trans h⟩
  have hbase := CircleMesh.integralEnclosure_width schedule.nodeBudget_nonneg
    schedule.magnitude_nonneg schedule.mesh_pos hcoordinate
  rw [ContourProgram.evaluate, ComplexRatInterval.width, ComplexRatInterval.expand,
    RatInterval.width_expand, RatInterval.width_expand]
  apply max_le
  · linarith [hbase.1, schedule.mesh_error_le, schedule.budget_sum_le]
  · linarith [hbase.2, schedule.mesh_error_le, schedule.budget_sum_le]

/-- **Certified finite-precision evaluation of a contour integral.** Fix [a contour-integral
program](hyp:program), [value bounds for it](hyp:bounds), [a target separation](hyp:separation),
[a certified mesh schedule built to meet that target](hyp:scheduled), and [a certificate that the
denominator stays bounded away from zero, whose guaranteed separation covers the target
one](hyp:certificate,hseparation); assume also that [the program's denominator never vanishes
anywhere on the parametrized circle](hyp:hden) and [the normalized integrand is Lipschitz in the
circle parameter with the schedule's constant](hyp:hLip). Then [the rational rectangle obtained by
evaluating the program both contains the true normalized contour integral and has real-part width
at most the schedule's requested tolerance](goal). -/
theorem certified_contour_evaluation (program : ContourProgram)
    (bounds : ContourValueBounds program) (separation : PosRat)
    (scheduled : CertifiedProgramSchedule program bounds separation)
    (certificate : DenominatorCertificate program scheduled.schedule)
    (hseparation : separation.1 ≤ certificate.separation)
    (hden : ∀ u ∈ Icc (0 : ℝ) 1,
      program.denominator.value
        ((program.radius : ℂ) * Complex.exp (((2 : ℝ) * Real.pi * u) * Complex.I)) ≠ 0)
    (hLip : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖program.normalizedIntegrand scheduled.schedule s -
        program.normalizedIntegrand scheduled.schedule t‖ ≤
        (scheduled.schedule.magnitude : ℝ) * |s - t|) :
    (program.evaluate scheduled.schedule certificate).Contains
        program.normalizedContourIntegral ∧
      (program.evaluate scheduled.schedule certificate).re.width ≤
        scheduled.schedule.tolerance.1 := by
  constructor
  · exact evaluate_contains program scheduled.schedule certificate hden hLip
  · exact (le_max_left _ _).trans
      (evaluate_width program bounds separation scheduled certificate hseparation)

/-- The canonical statistical tolerance is the positive rational reciprocal of `max n 1`. -/
def inverseMaxTolerance (n : ℕ) : PosRat :=
  ⟨1 / (max n 1 : ℚ), by positivity⟩

/-- Specializing the generic contour certificate to reciprocal-max tolerance
gives the width required by canonical finite-rational statistics. -/
theorem certified_contour_evaluation_inverseMax (n : ℕ) (program : ContourProgram)
    (bounds : ContourValueBounds program) (separation : PosRat)
    (scheduled : CertifiedProgramSchedule program bounds separation)
    (hschedule : scheduled.schedule.tolerance = inverseMaxTolerance n)
    (certificate : DenominatorCertificate program scheduled.schedule)
    (hseparation : separation.1 ≤ certificate.separation)
    (hden : ∀ u ∈ Icc (0 : ℝ) 1,
      program.denominator.value
        ((program.radius : ℂ) * Complex.exp (((2 : ℝ) * Real.pi * u) * Complex.I)) ≠ 0)
    (hLip : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖program.normalizedIntegrand scheduled.schedule s -
        program.normalizedIntegrand scheduled.schedule t‖ ≤
        (scheduled.schedule.magnitude : ℝ) * |s - t|) :
    (program.evaluate scheduled.schedule certificate).re.width ≤
      1 / (max n 1 : ℚ) := by
  have h := (certified_contour_evaluation program bounds separation scheduled certificate
    hseparation hden hLip).2
  rw [hschedule] at h
  exact h

/-- Containment in a rational real interval bounds its midpoint error by half
the interval width, turning the reciprocal-max width into a statistic error bound. -/
theorem midpoint_error_le_half_width {I : RatInterval} {x : ℝ}
    (hx : I.Contains x) :
    |(((I.lo + I.hi) / 2 : ℚ) : ℝ) - x| ≤ (I.width : ℝ) / 2 := by
  simp only [RatInterval.Contains] at hx
  simp only [RatInterval.width]
  rw [abs_le]
  push_cast
  constructor <;> linarith [hx.1, hx.2]

end Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Complex
