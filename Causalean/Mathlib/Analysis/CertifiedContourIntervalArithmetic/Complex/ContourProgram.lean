import Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Complex.Program

/-!
# Certified finite contour programs

This module packages executable interval extensions of numerator and
denominator maps, evaluates their normalized circle integrand at every mesh
endpoint, and feeds those rectangles to deterministic trapezoidal quadrature.
The final theorem combines denominator separation, node soundness, mesh error,
and the shared split budget into one containment-and-width certificate.
-/

open scoped Interval
open MeasureTheory Set intervalIntegral

namespace Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Complex

open Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic

/-- A finite rational contour program consists of certified numerator and
denominator maps and a positive rational circle radius. -/
structure ContourProgram where
  /-- Certified numerator interval extension. -/
  numerator : CertifiedComplexMap
  /-- Certified denominator interval extension. -/
  denominator : CertifiedComplexMap
  /-- Rational radius of the centered circle. -/
  radius : ℚ
  /-- The contour radius is strictly positive. -/
  radius_pos : 0 < radius

/-- The structural operation count of one contour node includes both certified
map programs, guarded division, and multiplication by the circle node. -/
def ContourProgram.operationCount (program : ContourProgram) : ℕ :=
  program.numerator.operationCount + program.denominator.operationCount + 2

/-- A concrete canonical rational program uses a rational constant numerator,
the unit denominator, and a positive rational circle radius. -/
def ContourProgram.constantUnit (numeratorRe numeratorIm radius : ℚ)
    (hradius : 0 < radius) : ContourProgram where
  numerator := CertifiedComplexMap.constant numeratorRe numeratorIm
  denominator := CertifiedComplexMap.constant 1 0
  radius := radius
  radius_pos := hradius

/-- The scheduled rational rectangle fed to both function interval extensions. -/
def ContourProgram.nodeBox (program : ContourProgram) (schedule : Schedule)
    (k : ℕ) : ComplexRatInterval :=
  circleNode program.radius schedule k

/-- Uniform semantic magnitude data bound the real and imaginary coordinates
of numerator and denominator values everywhere on the exact circle. -/
structure ContourValueBounds (program : ContourProgram) where
  /-- Uniform coordinate magnitude bound for the exact numerator. -/
  numerator : ℚ
  /-- Uniform coordinate magnitude bound for the exact denominator. -/
  denominator : ℚ
  /-- The numerator magnitude bound is nonnegative. -/
  numerator_nonneg : 0 ≤ numerator
  /-- The denominator magnitude bound is nonnegative. -/
  denominator_nonneg : 0 ≤ denominator
  /-- Numerator coordinates satisfy the bound at every circle parameter. -/
  numerator_bound : ∀ u ∈ Set.Icc (0 : ℝ) 1,
    max |(program.numerator.value
      ((program.radius : ℂ) * Complex.exp (((2 : ℝ) * Real.pi * u) * Complex.I))).re|
      |(program.numerator.value
      ((program.radius : ℂ) * Complex.exp (((2 : ℝ) * Real.pi * u) * Complex.I))).im| ≤
        (numerator : ℝ)
  /-- Denominator coordinates satisfy the bound at every circle parameter. -/
  denominator_bound : ∀ u ∈ Set.Icc (0 : ℝ) 1,
    max |(program.denominator.value
      ((program.radius : ℂ) * Complex.exp (((2 : ℝ) * Real.pi * u) * Complex.I))).re|
      |(program.denominator.value
      ((program.radius : ℂ) * Complex.exp (((2 : ℝ) * Real.pi * u) * Complex.I))).im| ≤
        (denominator : ℝ)

/-- A common leaf-error and circle-input target gives these numerator and
denominator rectangle width bounds by `CertifiedComplexMap.width_le`. -/
def ContourProgram.mapWidthBounds (program : ContourProgram) (target : ℚ) : ℚ × ℚ :=
  (target + program.numerator.amplification * target,
    target + program.denominator.amplification * target)

/-- The explicit arithmetic propagation bound for one guarded contour node
combines map errors, input refinement, magnitude amplification, separation,
division, and the final multiplication by the circle point. -/
def ContourProgram.nodePropagationBound (program : ContourProgram)
    (bounds : ContourValueBounds program) (separation target : ℚ) : ℚ :=
  let widths := program.mapWidthBounds target
  let numeratorMax := bounds.numerator + widths.1
  let denominatorMax := bounds.denominator + widths.2
  let divisionNumeratorMax := 2 * numeratorMax * denominatorMax
  let divisionNumeratorWidth :=
    2 * (numeratorMax * widths.2 + denominatorMax * widths.1)
  let denominatorNormWidth := 4 * denominatorMax * widths.2
  let quotientWidth :=
    divisionNumeratorMax * denominatorNormWidth / separation ^ 2 +
      divisionNumeratorWidth / separation
  let quotientMax := divisionNumeratorMax / separation
  2 * (quotientMax * target + (program.radius + target) * quotientWidth)

/-- A conservative positive scale controls every coefficient in the node
propagation polynomial on targets no larger than one. -/
def ContourProgram.nodeScale (program : ContourProgram)
    (bounds : ContourValueBounds program) (separation : PosRat) : ℚ :=
  |program.nodePropagationBound bounds separation.1 1| + 1

/-- The canonical common target spends the node budget after accounting for
all program operations, map amplification, magnitudes, and denominator separation. -/
def ContourProgram.canonicalNodeTarget (program : ContourProgram)
    (bounds : ContourValueBounds program) (separation tolerance : PosRat) : PosRat :=
  ⟨min 1 (tolerance.1 / (3 * program.nodeScale bounds separation)), by
    apply lt_min (by norm_num)
    apply div_pos tolerance.2
    dsimp [ContourProgram.nodeScale]
    linarith [abs_nonneg (program.nodePropagationBound bounds separation.1 1)]⟩

set_option maxHeartbeats 800000 in
-- Normalizing the explicit high-degree propagation polynomial exceeds the default limit.
private theorem ContourProgram.nodePropagationBound_le_scale_mul
    (program : ContourProgram) (bounds : ContourValueBounds program)
    (separation : PosRat) {target : ℚ} (htarget_nonneg : 0 ≤ target)
    (htarget_le_one : target ≤ 1) :
    program.nodePropagationBound bounds separation.1 target ≤
      program.nodeScale bounds separation * target := by
  let numeratorWidth := target + program.numerator.amplification * target
  let denominatorWidth := target + program.denominator.amplification * target
  let numeratorWidthOne := 1 + program.numerator.amplification
  let denominatorWidthOne := 1 + program.denominator.amplification
  let numeratorMax := bounds.numerator + numeratorWidth
  let denominatorMax := bounds.denominator + denominatorWidth
  let numeratorMaxOne := bounds.numerator + numeratorWidthOne
  let denominatorMaxOne := bounds.denominator + denominatorWidthOne
  let divisionMax := 2 * numeratorMax * denominatorMax
  let divisionMaxOne := 2 * numeratorMaxOne * denominatorMaxOne
  let divisionWidth :=
    2 * (numeratorMax * denominatorWidth + denominatorMax * numeratorWidth)
  let divisionWidthOne :=
    2 * (numeratorMaxOne * denominatorWidthOne +
      denominatorMaxOne * numeratorWidthOne)
  let normWidth := 4 * denominatorMax * denominatorWidth
  let normWidthOne := 4 * denominatorMaxOne * denominatorWidthOne
  let quotientWidth := divisionMax * normWidth / separation.1 ^ 2 +
    divisionWidth / separation.1
  let quotientWidthOne := divisionMaxOne * normWidthOne / separation.1 ^ 2 +
    divisionWidthOne / separation.1
  have hnWidthOne : 0 ≤ numeratorWidthOne := by
    dsimp [numeratorWidthOne]
    linarith [program.numerator.amplification_nonneg]
  have hdWidthOne : 0 ≤ denominatorWidthOne := by
    dsimp [denominatorWidthOne]
    linarith [program.denominator.amplification_nonneg]
  have hnWidth_scale : numeratorWidth = target * numeratorWidthOne := by
    dsimp [numeratorWidth, numeratorWidthOne]
    ring
  have hdWidth_scale : denominatorWidth = target * denominatorWidthOne := by
    dsimp [denominatorWidth, denominatorWidthOne]
    ring
  have hnWidth0 : 0 ≤ numeratorWidth := by rw [hnWidth_scale]; positivity
  have hdWidth0 : 0 ≤ denominatorWidth := by rw [hdWidth_scale]; positivity
  have hnWidth_le : numeratorWidth ≤ numeratorWidthOne := by
    rw [hnWidth_scale]
    nlinarith
  have hdWidth_le : denominatorWidth ≤ denominatorWidthOne := by
    rw [hdWidth_scale]
    nlinarith
  have hnMax0 : 0 ≤ numeratorMax := by
    dsimp [numeratorMax]
    linarith [bounds.numerator_nonneg]
  have hdMax0 : 0 ≤ denominatorMax := by
    dsimp [denominatorMax]
    linarith [bounds.denominator_nonneg]
  have hnMaxOne0 : 0 ≤ numeratorMaxOne := by
    dsimp [numeratorMaxOne]
    linarith [bounds.numerator_nonneg]
  have hdMaxOne0 : 0 ≤ denominatorMaxOne := by
    dsimp [denominatorMaxOne]
    linarith [bounds.denominator_nonneg]
  have hnMax_le : numeratorMax ≤ numeratorMaxOne := by
    dsimp [numeratorMax, numeratorMaxOne]
    linarith
  have hdMax_le : denominatorMax ≤ denominatorMaxOne := by
    dsimp [denominatorMax, denominatorMaxOne]
    linarith
  have hdivisionMax0 : 0 ≤ divisionMax := by
    dsimp [divisionMax]
    positivity
  have hdivisionMaxOne0 : 0 ≤ divisionMaxOne := by
    dsimp [divisionMaxOne]
    positivity
  have hdivisionMax_le : divisionMax ≤ divisionMaxOne := by
    dsimp [divisionMax, divisionMaxOne]
    nlinarith [mul_le_mul hnMax_le hdMax_le hdMax0 hnMaxOne0]
  have hnTerm : numeratorMax * denominatorWidth ≤
      target * (numeratorMaxOne * denominatorWidthOne) := by
    rw [hdWidth_scale]
    have h := mul_le_mul_of_nonneg_right hnMax_le hdWidthOne
    nlinarith
  have hdTerm : denominatorMax * numeratorWidth ≤
      target * (denominatorMaxOne * numeratorWidthOne) := by
    rw [hnWidth_scale]
    have h := mul_le_mul_of_nonneg_right hdMax_le hnWidthOne
    nlinarith
  have hdivisionWidth0 : 0 ≤ divisionWidth := by
    dsimp [divisionWidth]
    positivity
  have hdivisionWidthOne0 : 0 ≤ divisionWidthOne := by
    dsimp [divisionWidthOne]
    positivity
  have hdivisionWidth_le : divisionWidth ≤ target * divisionWidthOne := by
    dsimp [divisionWidth, divisionWidthOne]
    nlinarith
  have hnormWidth0 : 0 ≤ normWidth := by
    dsimp [normWidth]
    positivity
  have hnormWidthOne0 : 0 ≤ normWidthOne := by
    dsimp [normWidthOne]
    positivity
  have hnormWidth_le : normWidth ≤ target * normWidthOne := by
    dsimp [normWidth, normWidthOne]
    rw [hdWidth_scale]
    have h := mul_le_mul_of_nonneg_right hdMax_le hdWidthOne
    nlinarith
  have hdivisionNorm : divisionMax * normWidth ≤
      target * (divisionMaxOne * normWidthOne) := by
    calc
      divisionMax * normWidth ≤ divisionMax * (target * normWidthOne) :=
        mul_le_mul_of_nonneg_left hnormWidth_le hdivisionMax0
      _ = target * (divisionMax * normWidthOne) := by ring
      _ ≤ target * (divisionMaxOne * normWidthOne) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hdivisionMax_le hnormWidthOne0)
          htarget_nonneg
  have hquotientWidth0 : 0 ≤ quotientWidth := by
    dsimp [quotientWidth]
    exact add_nonneg
      (div_nonneg (mul_nonneg hdivisionMax0 hnormWidth0) (sq_nonneg separation.1))
      (div_nonneg hdivisionWidth0 separation.2.le)
  have hquotientWidthOne0 : 0 ≤ quotientWidthOne := by
    dsimp [quotientWidthOne]
    exact add_nonneg
      (div_nonneg (mul_nonneg hdivisionMaxOne0 hnormWidthOne0)
        (sq_nonneg separation.1))
      (div_nonneg hdivisionWidthOne0 separation.2.le)
  have hquotientWidth_le : quotientWidth ≤ target * quotientWidthOne := by
    have hfirst : divisionMax * normWidth / separation.1 ^ 2 ≤
        target * (divisionMaxOne * normWidthOne / separation.1 ^ 2) := by
      calc
        divisionMax * normWidth / separation.1 ^ 2 ≤
            (target * (divisionMaxOne * normWidthOne)) / separation.1 ^ 2 :=
          div_le_div_of_nonneg_right hdivisionNorm (sq_nonneg separation.1)
        _ = target * (divisionMaxOne * normWidthOne / separation.1 ^ 2) := by ring
    have hsecond : divisionWidth / separation.1 ≤
        target * (divisionWidthOne / separation.1) := by
      calc
        divisionWidth / separation.1 ≤ (target * divisionWidthOne) / separation.1 :=
          div_le_div_of_nonneg_right hdivisionWidth_le separation.2.le
        _ = target * (divisionWidthOne / separation.1) := by ring
    dsimp [quotientWidth, quotientWidthOne]
    linarith
  have hradius_target : program.radius + target ≤ program.radius + 1 := by linarith
  have hradius_target0 : 0 ≤ program.radius + target := by
    linarith [program.radius_pos]
  have hradius_one0 : 0 ≤ program.radius + 1 := by linarith [program.radius_pos]
  have hfinalQuotient : (program.radius + target) * quotientWidth ≤
      target * ((program.radius + 1) * quotientWidthOne) := by
    calc
      (program.radius + target) * quotientWidth ≤
          (program.radius + 1) * (target * quotientWidthOne) :=
        mul_le_mul hradius_target hquotientWidth_le hquotientWidth0 hradius_one0
      _ = target * ((program.radius + 1) * quotientWidthOne) := by ring
  have hpropagationOne0 :
      0 ≤ program.nodePropagationBound bounds separation.1 1 := by
    dsimp only [ContourProgram.nodePropagationBound, ContourProgram.mapWidthBounds]
    norm_num only [mul_one]
    change 0 ≤ 2 * (divisionMaxOne / separation.1 +
      (program.radius + 1) * quotientWidthOne)
    exact mul_nonneg (by norm_num) (add_nonneg
      (div_nonneg hdivisionMaxOne0 separation.2.le)
      (mul_nonneg hradius_one0 hquotientWidthOne0))
  have hpropagation : program.nodePropagationBound bounds separation.1 target ≤
      target * program.nodePropagationBound bounds separation.1 1 := by
    dsimp only [ContourProgram.nodePropagationBound, ContourProgram.mapWidthBounds]
    norm_num only [mul_one]
    change 2 * (divisionMax / separation.1 * target +
      (program.radius + target) * quotientWidth) ≤
        target * (2 * (divisionMaxOne / separation.1 +
          (program.radius + 1) * quotientWidthOne))
    have hfirst := div_le_div_of_nonneg_right hdivisionMax_le separation.2.le
    calc
      2 * (divisionMax / separation.1 * target +
          (program.radius + target) * quotientWidth) ≤
          2 * (target * (divisionMaxOne / separation.1) +
            target * ((program.radius + 1) * quotientWidthOne)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply add_le_add
        · simpa [mul_comm] using mul_le_mul_of_nonneg_right hfirst htarget_nonneg
        · exact hfinalQuotient
      _ = target * (2 * (divisionMaxOne / separation.1 +
          (program.radius + 1) * quotientWidthOne)) := by ring
  calc
    program.nodePropagationBound bounds separation.1 target ≤
        target * program.nodePropagationBound bounds separation.1 1 := hpropagation
    _ ≤ program.nodeScale bounds separation * target := by
      rw [ContourProgram.nodeScale, abs_of_nonneg hpropagationOne0]
      nlinarith

/-- The canonical constant-over-unit program has explicit global coordinate
magnitude bounds computed only from its rational numerator coordinates. -/
def ContourProgram.constantUnitBounds (numeratorRe numeratorIm radius : ℚ)
    (hradius : 0 < radius) :
    ContourValueBounds
      (ContourProgram.constantUnit numeratorRe numeratorIm radius hradius) := by
  refine {
    numerator := max |numeratorRe| |numeratorIm|
    denominator := 1
    numerator_nonneg := (abs_nonneg numeratorRe).trans (le_max_left _ _)
    denominator_nonneg := by norm_num
    numerator_bound := ?_
    denominator_bound := ?_ }
  · intro u hu
    simp only [ContourProgram.constantUnit, CertifiedComplexMap.constant]
    norm_num
  · intro u hu
    simp only [ContourProgram.constantUnit, CertifiedComplexMap.constant]
    norm_num

/-- A denominator certificate checks every endpoint actually evaluated and
stores a common positive rational lower bound on squared modulus. -/
structure DenominatorCertificate (program : ContourProgram) (schedule : Schedule) where
  /-- Common positive squared-modulus separation. -/
  separation : ℚ
  /-- The common separation is strictly positive. -/
  separation_pos : 0 < separation
  /-- Every endpoint denominator rectangle is executable and away from zero. -/
  away : ∀ k, k ≤ schedule.mesh →
    ((program.denominator.eval (program.nodeBox schedule k) schedule.fuel).normSq).AwayFromZero
  /-- The same rational separation lies below every squared-modulus lower endpoint. -/
  lower : ∀ k, k ≤ schedule.mesh → separation ≤
    (program.denominator.eval (program.nodeBox schedule k) schedule.fuel).normSq.lo

/-- A certified program schedule records primitive precision obligations, all
chosen from one shared schedule, from which node width is derived rather than
assumed. -/
structure CertifiedProgramSchedule (program : ContourProgram)
    (bounds : ContourValueBounds program) (separation : PosRat) where
  /-- The exact schedule consumed by execution, tracing, and specifications. -/
  schedule : Schedule
  /-- The schedule operation count is the structural count of the executable program. -/
  operationCount_eq : schedule.operationCount = program.operationCount
  /-- The common positive target for circle and map approximation errors. -/
  target : PosRat
  /-- The target is definitionally selected from tolerance and propagation scale. -/
  target_eq : target = program.canonicalNodeTarget bounds separation schedule.tolerance
  /-- Input precision is the explicit uniform circle precision for this target. -/
  inputPrecision_eq : schedule.inputPrecision = circleInputPrecision program.radius target
  /-- Scheduled fuel dominates the circle exponential fuel requirement. -/
  circleFuel_le : circleExpFuel program.radius schedule.mesh target ≤ schedule.fuel
  /-- Scheduled fuel dominates the numerator algorithmic-error modulus. -/
  numeratorFuel_le : program.numerator.errorModulus target ≤ schedule.fuel
  /-- Scheduled fuel dominates the denominator algorithmic-error modulus. -/
  denominatorFuel_le : program.denominator.errorModulus target ≤ schedule.fuel
  /-- The compositional arithmetic bound fits in the schedule's node budget. -/
  propagation_le : program.nodePropagationBound bounds separation.1 target.1 ≤
    schedule.nodeBudget

/-- The finite trace for one scheduled node has one event for each structural
primitive operation and every event retains the exact execution schedule. -/
def ContourProgram.nodeTrace (program : ContourProgram)
    {bounds : ContourValueBounds program} {separation : PosRat}
    (scheduled : CertifiedProgramSchedule program bounds separation) (k : ℕ) :
    List TraceEvent :=
  List.ofFn fun operation : Fin program.operationCount =>
    circleNodeEvent scheduled.schedule k operation

/-- The executable node trace length is definitionally the program's derived
operation count, and its retained schedule reports that same count. -/
theorem ContourProgram.nodeTrace_spec (program : ContourProgram)
    {bounds : ContourValueBounds program} {separation : PosRat}
    (scheduled : CertifiedProgramSchedule program bounds separation) (k : ℕ) :
    (program.nodeTrace scheduled k).length = program.operationCount ∧
      ∀ event ∈ program.nodeTrace scheduled k,
        event.schedule = scheduled.schedule ∧
          event.schedule.operationCount = program.operationCount := by
  constructor
  · simp [ContourProgram.nodeTrace]
  · intro event hevent
    simp only [ContourProgram.nodeTrace, List.mem_ofFn] at hevent
    obtain ⟨operation, rfl⟩ := hevent
    exact ⟨rfl, scheduled.operationCount_eq⟩

/-- The canonical certified schedule derives operation count, input precision,
fuel, mesh, and all three budgets from the program and rational bounds. -/
def ContourProgram.canonicalScheduled (program : ContourProgram)
    (bounds : ContourValueBounds program) (separation tolerance : PosRat)
    (magnitude : ℚ) (hmagnitude : 0 ≤ magnitude) :
    CertifiedProgramSchedule program bounds separation := by
  let base := Schedule.canonical tolerance program.operationCount magnitude hmagnitude
  let target := program.canonicalNodeTarget bounds separation tolerance
  let inputPrecision := circleInputPrecision program.radius target
  let fuel := max (circleExpFuel program.radius base.mesh target)
    (max (program.numerator.errorModulus target)
      (program.denominator.errorModulus target))
  let schedule : Schedule := { base with inputPrecision := inputPrecision, fuel := fuel }
  exact {
    schedule := schedule
    operationCount_eq := by rfl
    target := target
    target_eq := by rfl
    inputPrecision_eq := by rfl
    circleFuel_le := by
      dsimp [schedule, fuel]
      exact le_max_left _ _
    numeratorFuel_le := by
      dsimp [schedule, fuel]
      exact (le_max_left _ _).trans (le_max_right _ _)
    denominatorFuel_le := by
      dsimp [schedule, fuel]
      exact (le_max_right _ _).trans (le_max_right _ _)
    propagation_le := by
      have htarget_nonneg : 0 ≤ target.1 := target.2.le
      have htarget_le_one : target.1 ≤ 1 := by
        dsimp [target, ContourProgram.canonicalNodeTarget]
        exact min_le_left _ _
      have htarget_le : target.1 ≤
          tolerance.1 / (3 * program.nodeScale bounds separation) := by
        dsimp [target, ContourProgram.canonicalNodeTarget]
        exact min_le_right _ _
      have hscale : 0 < program.nodeScale bounds separation := by
        dsimp [ContourProgram.nodeScale]
        linarith [abs_nonneg
          (program.nodePropagationBound bounds separation.1 1)]
      calc
        program.nodePropagationBound bounds separation.1 target.1 ≤
            program.nodeScale bounds separation * target.1 :=
          program.nodePropagationBound_le_scale_mul bounds separation
            htarget_nonneg htarget_le_one
        _ ≤ program.nodeScale bounds separation *
            (tolerance.1 / (3 * program.nodeScale bounds separation)) :=
          mul_le_mul_of_nonneg_left htarget_le hscale.le
        _ = tolerance.1 / 3 := by field_simp
        _ = schedule.nodeBudget := by rfl }

/-- The concrete unit-denominator program has an executable separation
certificate with squared-modulus lower bound one at every endpoint. -/
def ContourProgram.constantUnitCertificate (numeratorRe numeratorIm radius : ℚ)
    (hradius : 0 < radius) (schedule : Schedule) :
    DenominatorCertificate
      (ContourProgram.constantUnit numeratorRe numeratorIm radius hradius) schedule where
  separation := 1
  separation_pos := by norm_num
  away := by
    intro k hk
    right
    norm_num [ContourProgram.constantUnit, CertifiedComplexMap.constant,
      ComplexRatInterval.normSq, RatInterval.sq, RatInterval.add,
      ComplexRatInterval.point, RatInterval.point]
  lower := by
    intro k hk
    norm_num [ContourProgram.constantUnit, CertifiedComplexMap.constant,
      ComplexRatInterval.normSq, RatInterval.sq, RatInterval.add,
      ComplexRatInterval.point, RatInterval.point]

/-- The node function with an explicit endpoint-bound argument avoids ever
constructing a division guard outside the scheduled finite endpoint range. -/
def ContourProgram.integrandNodeFin (program : ContourProgram) (schedule : Schedule)
    (certificate : DenominatorCertificate program schedule)
    (k : Fin (schedule.mesh + 1)) : ComplexRatInterval :=
  let node := program.nodeBox schedule k
  let numerator := program.numerator.eval node schedule.fuel
  let denominator := program.denominator.eval node schedule.fuel
  (numerator.div denominator (certificate.away k (Nat.le_of_lt_succ k.isLt))).mul node

/-- A total natural-indexed node family agrees with certified endpoints and
uses the terminal endpoint outside the range, which quadrature never queries. -/
def ContourProgram.integrandNodes (program : ContourProgram) (schedule : Schedule)
    (certificate : DenominatorCertificate program schedule) (k : ℕ) :
    ComplexRatInterval :=
  if hk : k ≤ schedule.mesh then
    let node := program.nodeBox schedule k
    let numerator := program.numerator.eval node schedule.fuel
    let denominator := program.denominator.eval node schedule.fuel
    (numerator.div denominator (certificate.away k hk)).mul node
  else
    program.integrandNodeFin schedule certificate ⟨schedule.mesh, Nat.lt_succ_self _⟩

/-- The exact normalized integrand after cancellation of the circle tangent's
`2 * π * i` factor is the quotient times the circle point. -/
noncomputable def ContourProgram.normalizedIntegrand (program : ContourProgram)
    (schedule : Schedule) (u : ℝ) : ℂ :=
  let z : ℂ := (program.radius : ℂ) *
    Complex.exp (((2 : ℝ) * Real.pi * u) * Complex.I)
  (program.numerator.value z / program.denominator.value z) * z

/-- The normalized exact contour integral is the usual circle contour integral
divided by `2 * π * i`; it is used only as the semantic target. -/
noncomputable def ContourProgram.normalizedContourIntegral
    (program : ContourProgram) : ℂ :=
  CircleMesh.circleContourIntegral
      (fun z => program.numerator.value z / program.denominator.value z)
      0 program.radius /
    (((2 : ℝ) * Real.pi : ℂ) * Complex.I)


end Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Complex
