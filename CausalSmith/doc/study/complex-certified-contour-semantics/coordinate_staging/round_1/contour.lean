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

/-- The generic finite contour theorem simultaneously certifies semantic
containment and the requested real-projection width. -/
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
