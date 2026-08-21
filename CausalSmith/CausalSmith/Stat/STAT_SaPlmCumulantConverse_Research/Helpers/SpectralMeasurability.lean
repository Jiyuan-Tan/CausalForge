import CausalSmith.Stat.STAT_SaPlmCumulantConverse_Research.Helpers.SpectralEstimator
import Causalean.Mathlib.Analysis.ArgumentPrincipleCircle.Basic
import Mathlib.MeasureTheory.Function.Floor

/-! # Measurability of the finite rational spectral program -/

noncomputable section

open MeasureTheory Set
open Causalean.Mathlib.Analysis.ArgumentPrincipleCircle
open Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Complex
open Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic
open Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.FiniteSearch

namespace CausalSmith.Stat.SaPlmCumulantConverse

variable {Xspace : Type*} [MeasurableSpace Xspace]

/-- A fixed-precision canonical dyadic interval is a Borel function of its real input. -/
lemma mcanon (precision : ℕ) :
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

/-- Canonical dyadic approximation is jointly measurable in the real input and precision. -/
lemma mcanon_joint :
    Measurable (fun xn : ℝ × ℕ ↦ canonicalDyadicInterval xn.1 xn.2) := by
  apply measurable_from_prod_countable_left
  intro precision
  simpa using mcanon precision

set_option maxHeartbeats 2400000 in
-- A cold Lake build spends substantial heartbeats normalizing the two product
-- measurable spaces in this otherwise direct composition.
/-- Canonical dyadic approximation remains measurable at a measurable data-dependent precision. -/
lemma mcanon_dyn {Ω : Type*} [MeasurableSpace Ω] (x : Ω → ℝ) (fuel : Ω → ℕ)
    (hx : Measurable x) (hf : Measurable fuel) :
    Measurable (fun ω ↦ canonicalDyadicInterval (x ω) (fuel ω)) := by
  exact mcanon_joint.comp (hx.prodMk hf)

/-- The treatment-name interval queried at measurable fuel is measurable in the sample. -/
lemma measurable_treatmentApprox (p : Parameters) (pStar : CertifiedBankInputs p)
    (cStar : CertifiedRangeInput p) (gcode : ℕ → Xspace → ℝ)
    (i : Fin p.n) (fuel : (Fin p.n → Obs Xspace) → ℕ) (hf : Measurable fuel) :
    Measurable (fun data ↦
      ((canonicalRepresentedInput p pStar cStar gcode data).observations i).tName.approx
        (fuel data)) := by
  change Measurable (fun data ↦ canonicalDyadicInterval (treatment (data i)) (fuel data))
  apply mcanon_dyn _ _ _ hf
  exact (measurable_pi_apply i).snd.fst

/-- The outcome-name interval queried at measurable fuel is measurable in the sample. -/
lemma measurable_outcomeApprox (p : Parameters) (pStar : CertifiedBankInputs p)
    (cStar : CertifiedRangeInput p) (gcode : ℕ → Xspace → ℝ)
    (i : Fin p.n) (fuel : (Fin p.n → Obs Xspace) → ℕ) (hf : Measurable fuel) :
    Measurable (fun data ↦
      ((canonicalRepresentedInput p pStar cStar gcode data).observations i).yName.approx
        (fuel data)) := by
  change Measurable (fun data ↦ canonicalDyadicInterval (outcome (data i)) (fuel data))
  apply mcanon_dyn _ _ _ hf
  exact (measurable_pi_apply i).snd.snd

/-- The clipped code-name interval queried at measurable fuel is measurable in the sample. -/
lemma measurable_codeApprox (p : Parameters) (pStar : CertifiedBankInputs p)
    (cStar : CertifiedRangeInput p) (gcode : ℕ → Xspace → ℝ)
    (hgcode : Measurable (gcode p.n)) (i : Fin p.n)
    (fuel : (Fin p.n → Obs Xspace) → ℕ) (hf : Measurable fuel) :
    Measurable (fun data ↦
      ((canonicalRepresentedInput p pStar cStar gcode data).observations i).gName.approx
        (fuel data)) := by
  change Measurable (fun data ↦ canonicalDyadicInterval
    (min (max (gcode p.n (covariate (data i))) (-p.Cg)) p.Cg) (fuel data))
  apply mcanon_dyn _ _ _ hf
  exact (((hgcode.comp ((measurable_pi_apply i).fst)).max measurable_const).min
    measurable_const)

end CausalSmith.Stat.SaPlmCumulantConverse

namespace CausalSmith.Stat.SaPlmCumulantConverse

variable {Xspace : Type*} [MeasurableSpace Xspace]

private theorem countable_ratInterval2 : Countable RatInterval :=
  Function.Injective.countable
    (f := fun interval : RatInterval => (interval.lo, interval.hi)) (by
      intro left right h
      cases left
      cases right
      simp_all)

private theorem countable_complexRatInterval2 : Countable ComplexRatInterval := by
  letI : Countable RatInterval := countable_ratInterval2
  exact Function.Injective.countable
    (f := fun rectangle : ComplexRatInterval => (rectangle.re, rectangle.im)) (by
      intro left right h
      cases left
      cases right
      simp_all)

attribute [local instance] countable_ratInterval2 countable_complexRatInterval2

/-- Evaluate a recursively tightened interval program from the finite prefix of
raw inputs that a fixed fuel actually consumes.  This is the countable carrier
used by the measurability proof after cross-fuel tightening. -/
private def tightenHistory {α : Type*} (raw : α → ℕ → ComplexRatInterval) :
    (fuel : ℕ) → (Fin (fuel + 1) → α) → ComplexRatInterval
  | 0, samples => raw (samples 0) 0
  | fuel + 1, samples =>
      (tightenHistory raw fuel (fun i => samples i.castSucc)).tighten
        (raw (samples (Fin.last (fuel + 1))) (fuel + 1))

private lemma tightenHistory_of_sequence {α : Type*}
    (raw : α → ℕ → ComplexRatInterval) (samples : ℕ → α) (fuel : ℕ) :
    tightenHistory raw fuel (fun i => samples i) =
      tightenAcrossFuel (fun m => raw (samples m) m) fuel := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      simp only [tightenHistory, tightenAcrossFuel]
      have hprefix :
          (fun i : Fin (fuel + 1) => samples (i.castSucc : Fin (fuel + 2))) =
            (fun i : Fin (fuel + 1) => samples i) := by
        rfl
      rw [hprefix]
      rw [ih]
      simp

private def denominatorRawEvalFromIntervals {p : Parameters}
    (I : Finset (Fin p.n)) (derivative : ℕ)
    (samples : Fin p.n → RatInterval × RatInterval) (z : ComplexRatInterval)
    (fuel : ℕ) : ComplexRatInterval :=
  let terms := I.toList.map fun i ↦
    let residual := (samples i).1.add (samples i).2.neg
    let argument := z.mul (realRect residual)
    let exponential := BoundedCertifiedComplex.centeredComplexExp argument fuel
    (realRect (residual.npow derivative)).mul exponential
  (intervalSum terms).smulRat ((max I.card 1 : ℚ)⁻¹)

private def denominatorEvalFromHistory {p : Parameters}
    (I : Finset (Fin p.n)) (derivative : ℕ) (z : ComplexRatInterval) (fuel : ℕ)
    (samples : Fin (fuel + 1) → Fin p.n → RatInterval × RatInterval) :
    ComplexRatInterval :=
  tightenHistory (fun sample m => denominatorRawEvalFromIntervals I derivative sample z m)
    fuel samples

private lemma denominatorEvalFromHistory_of_input {p : Parameters}
    (input : RepresentedSpectralInput p) (I : Finset (Fin p.n))
    (derivative : ℕ) (z : ComplexRatInterval) (fuel : ℕ) :
    denominatorEvalFromHistory I derivative z fuel (fun m i =>
        ((input.observations i).tName.approx m,
          (input.observations i).gName.approx m)) =
      spectralDenominatorEval input I derivative z fuel := by
  unfold denominatorEvalFromHistory
  calc
    _ = tightenAcrossFuel (fun m => denominatorRawEvalFromIntervals I derivative
        (fun i => ((input.observations i).tName.approx m,
          (input.observations i).gName.approx m)) z m) fuel :=
      by
        simpa only using tightenHistory_of_sequence
          (fun sample m => denominatorRawEvalFromIntervals I derivative sample z m)
          (fun m i => ((input.observations i).tName.approx m,
            (input.observations i).gName.approx m)) fuel
    _ = spectralDenominatorEval input I derivative z fuel := rfl

private def pilotUnitMargin : PosRat := ⟨1, by norm_num⟩

private def pilotModulusAtL (input : RepresentedSpectralInput p) (B : ContourBankData)
    (a : Fin 2) (j : Fin (B.JBase + 1)) (L scheduleMagnitude : ℚ) : RatInterval :=
  if hL : 0 ≤ L then
    if hMagnitude : 0 ≤ scheduleMagnitude then
      let map := spectralDenominatorMap input B (spectralFold p.n a) 0
      let operations := spectralNodeOperationCount .pilot (spectralFold p.n a).card
      let tolerance := estimatorNodePrecision (pilotNodeTolerance B)
        (spectralNodeScale B j scheduleMagnitude pilotUnitMargin 1 operations)
      let schedule := spectralSchedule tolerance
        operations L scheduleMagnitude hL hMagnitude
      CircleMesh.infEnclosure
        (fun k ↦ (map.eval (spectralRadiusNode B j schedule k) schedule.fuel).normInterval
          schedule.fuel) L hL schedule.mesh schedule.mesh_pos
    else RatInterval.point 0
  else RatInterval.point 0

private lemma pilotModulus_eq_atL (input : RepresentedSpectralInput p)
    (B : ContourBankData) (a : Fin 2) (j : Fin (B.JBase + 1)) :
    pilotModulus input B a j =
      pilotModulusAtL input B a j (pilotCircleLipschitzBound input (radiusUpper B j))
        (pilotScheduleMagnitude input B j) := by
  unfold pilotModulus pilotSchedule pilotModulusAtL pilotUnitMargin
  simp only [pilotCircleLipschitzBound_nonneg input (radiusUpper_nonneg B j),
    pilotScheduleMagnitude_nonneg input B j, ↓reduceDIte]

private lemma measurable_residualUpper_canonical
    (p : Parameters) (pStar : CertifiedBankInputs p) (cStar : CertifiedRangeInput p)
    (gcode : ℕ → Xspace → ℝ) (hgcode : Measurable (gcode p.n)) (i : Fin p.n) :
    Measurable (fun data : Fin p.n → Obs Xspace ↦
      residualUpper (canonicalRepresentedInput p pStar cStar gcode data) i) := by
  let fuel := fun data : Fin p.n → Obs Xspace ↦
    ((representedResidual (canonicalRepresentedInput p pStar cStar gcode data) i).modulus errorOne)
  have hfuel : Measurable fuel := by
    dsimp [fuel, representedResidual, CertifiedReal.sub, CertifiedReal.add,
      CertifiedReal.neg, canonicalRepresentedInput, canonicalObservationName]
    fun_prop
  have ht := measurable_treatmentApprox p pStar cStar gcode i fuel hfuel
  have hg := measurable_codeApprox p pStar cStar gcode hgcode i fuel hfuel
  have hpairs : Measurable (fun data ↦
      (((canonicalRepresentedInput p pStar cStar gcode data).observations i).tName.approx
          (fuel data),
        ((canonicalRepresentedInput p pStar cStar gcode data).observations i).gName.approx
          (fuel data))) := ht.prodMk hg
  let finish : RatInterval × RatInterval → ℚ := fun z ↦ (z.1.add z.2.neg).maxAbs
  have hfinish : Measurable finish := measurable_of_countable finish
  convert hfinish.comp hpairs using 1
  rfl

private lemma measurable_pilotCircleLipschitzBound_canonical
    (p : Parameters) (pStar : CertifiedBankInputs p) (cStar : CertifiedRangeInput p)
    (gcode : ℕ → Xspace → ℝ) (hgcode : Measurable (gcode p.n)) (rho : ℚ) :
    Measurable (fun data : Fin p.n → Obs Xspace ↦
      pilotCircleLipschitzBound (canonicalRepresentedInput p pStar cStar gcode data) rho) := by
  have hresiduals : Measurable (fun data : Fin p.n → Obs Xspace ↦ fun i ↦
      residualUpper (canonicalRepresentedInput p pStar cStar gcode data) i) := by
    exact measurable_pi_lambda _ fun i ↦
      measurable_residualUpper_canonical p pStar cStar gcode hgcode i
  let finish : (Fin p.n → ℚ) → ℚ := fun residuals ↦
    8 * rho * ∑ i, residuals i ^ 1 * rationalExpEnvelope rho (residuals i)
  exact (measurable_of_countable finish).comp hresiduals

private lemma measurable_empiricalFDerivativeBound_canonical
    (p : Parameters) (pStar : CertifiedBankInputs p) (cStar : CertifiedRangeInput p)
    (gcode : ℕ → Xspace → ℝ) (hgcode : Measurable (gcode p.n))
    (rho : ℚ) (derivative : ℕ) :
    Measurable (fun data : Fin p.n → Obs Xspace ↦
      empiricalFDerivativeBound (canonicalRepresentedInput p pStar cStar gcode data)
        rho derivative) := by
  have hresiduals : Measurable (fun data : Fin p.n → Obs Xspace ↦ fun i ↦
      residualUpper (canonicalRepresentedInput p pStar cStar gcode data) i) := by
    exact measurable_pi_lambda _ fun i ↦
      measurable_residualUpper_canonical p pStar cStar gcode hgcode i
  let finish : (Fin p.n → ℚ) → ℚ := fun residuals ↦
    ∑ i, residuals i ^ derivative * rationalExpEnvelope rho (residuals i)
  exact (measurable_of_countable finish).comp hresiduals

private lemma measurable_empiricalFWidthBound_canonical
    (p : Parameters) (pStar : CertifiedBankInputs p) (cStar : CertifiedRangeInput p)
    (gcode : ℕ → Xspace → ℝ) (hgcode : Measurable (gcode p.n))
    (rho : ℚ) (derivative : ℕ) :
    Measurable (fun data : Fin p.n → Obs Xspace ↦
      empiricalFWidthBound (canonicalRepresentedInput p pStar cStar gcode data)
        rho derivative) := by
  have hresiduals : Measurable (fun data : Fin p.n → Obs Xspace ↦ fun i ↦
      residualUpper (canonicalRepresentedInput p pStar cStar gcode data) i) := by
    exact measurable_pi_lambda _ fun i ↦
      measurable_residualUpper_canonical p pStar cStar gcode hgcode i
  let finish : (Fin p.n → ℚ) → ℚ := fun residuals ↦
    ∑ i, ((rho + 1) * (derivative + 1) *
      (2 * max 1 (residuals i)) ^ (derivative + 1) *
      rationalExpEnvelope rho (residuals i)) ^ 8
  exact (measurable_of_countable finish).comp hresiduals

private lemma measurable_pilotScheduleMagnitude_canonical
    (p : Parameters) (pStar : CertifiedBankInputs p) (cStar : CertifiedRangeInput p)
    (gcode : ℕ → Xspace → ℝ) (hgcode : Measurable (gcode p.n))
    (j : Fin ((contourBank p pStar).JBase + 1)) :
    Measurable (fun data : Fin p.n → Obs Xspace ↦
      pilotScheduleMagnitude (canonicalRepresentedInput p pStar cStar gcode data)
        (contourBank p pStar) j) := by
  have hQ := measurable_empiricalFWidthBound_canonical
    p pStar cStar gcode hgcode (spectralFullBoxRadius (contourBank p pStar)) 0
  let finish : ℚ → ℚ := fun Q ↦ (((128 * max 1 Q) ^ 2).num.natAbs : ℚ)
  exact (measurable_of_countable finish).comp hQ

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 4096 in
/-- Provided [the treatment-regression code used at the current sample size is a measurable
function of the covariates](hyp:hgcode), [the pilot enclosure of the smallest modulus the
empirical denominator transform attains along a given bank circle, computed on either fold from
the certified input built canonically from the data, is a measurable function of the
sample](goal). -/
lemma measurable_pilotModulus_canonical
    (p : Parameters) (pStar : CertifiedBankInputs p) (cStar : CertifiedRangeInput p)
    (gcode : ℕ → Xspace → ℝ) (hgcode : Measurable (gcode p.n))
    (a : Fin 2) (j : Fin ((contourBank p pStar).JBase + 1)) :
    Measurable (fun data : Fin p.n → Obs Xspace ↦
      pilotModulus (canonicalRepresentedInput p pStar cStar gcode data)
        (contourBank p pStar) a j) := by
  let B := contourBank p pStar
  let input := fun data : Fin p.n → Obs Xspace ↦
    canonicalRepresentedInput p pStar cStar gcode data
  let key := fun data ↦
    (pilotCircleLipschitzBound (input data) (radiusUpper B j),
      pilotScheduleMagnitude (input data) B j)
  have hkey : Measurable key := by
    exact (measurable_pilotCircleLipschitzBound_canonical
      p pStar cStar gcode hgcode _).prodMk
      (measurable_pilotScheduleMagnitude_canonical p pStar cStar gcode hgcode j)
  rw [show (fun data ↦ pilotModulus (input data) B a j) =
      (fun data ↦ pilotModulusAtL (input data) B a j (key data).1 (key data).2) by
    funext data
    exact pilotModulus_eq_atL (input data) B a j]
  let joint := fun state : (Fin p.n → Obs Xspace) × (ℚ × ℚ) ↦
    pilotModulusAtL (input state.1) B a j state.2.1 state.2.2
  apply (show Measurable joint from ?_).comp (measurable_id.prodMk hkey)
  apply measurable_from_prod_countable_left
  intro fixedKey
  let L := fixedKey.1
  let scheduleMagnitude := fixedKey.2
  dsimp [joint]
  unfold pilotModulusAtL
  split
  · split
    · let operations := spectralNodeOperationCount .pilot (spectralFold p.n a).card
      let tolerance := estimatorNodePrecision (pilotNodeTolerance B)
        (spectralNodeScale B j scheduleMagnitude pilotUnitMargin 1 operations)
      let schedule := spectralSchedule tolerance
        operations L scheduleMagnitude ‹0 ≤ L› ‹0 ≤ scheduleMagnitude›
      let intervals := fun data : Fin p.n → Obs Xspace ↦
        fun fuel : Fin (schedule.fuel + 1) ↦ fun i : Fin p.n ↦
          (((input data).observations i).tName.approx fuel,
            ((input data).observations i).gName.approx fuel)
      have hintervals : Measurable intervals := by
        apply measurable_pi_lambda
        intro fuel
        apply measurable_pi_lambda
        intro i
        exact (measurable_treatmentApprox p pStar cStar gcode i (fun _ ↦ (fuel : ℕ))
          measurable_const).prodMk
          (measurable_codeApprox p pStar cStar gcode hgcode i (fun _ ↦ (fuel : ℕ))
            measurable_const)
      let finish := fun samples :
          Fin (schedule.fuel + 1) → Fin p.n → RatInterval × RatInterval ↦
        CircleMesh.infEnclosure (fun k : ℕ ↦
          let z := spectralRadiusNode B j schedule k
          (denominatorEvalFromHistory (spectralFold p.n a) 0 z schedule.fuel samples).normInterval
            schedule.fuel) L ‹0 ≤ L› schedule.mesh schedule.mesh_pos
      have hfinish : Measurable finish := measurable_of_countable finish
      have hcomposed := hfinish.comp hintervals
      convert hcomposed using 1
      funext data
      dsimp only [Function.comp_apply, finish, intervals]
      congr 1
      funext k
      rw [denominatorEvalFromHistory_of_input]
      rfl
    · exact measurable_const
  · exact measurable_const

private def windingScheduleMagnitudeAt (input : RepresentedSpectralInput p)
    (B : ContourBankData) (j : Fin (B.JBase + 1)) (lower : ℚ) : ℚ :=
  let Q0 := empiricalFWidthBound input (spectralFullBoxRadius B) 0
  let Q1 := empiricalFWidthBound input (spectralFullBoxRadius B) 1
  let A0 := ((128 * max 1 Q0) ^ 2).num.natAbs
  let A1 := ((128 * max 1 Q1) ^ 2).num.natAbs
  ((max A0 A1 : ℕ) : ℚ)

private def windingFinish {p : Parameters} (B : ContourBankData) (j : Fin (B.JBase + 1))
    (schedule : Schedule) (L : ℚ) (hL : 0 ≤ L)
    (samples : Fin (schedule.fuel + 1) → Fin p.n → RatInterval × RatInterval) :
    ComplexRatInterval :=
  let node := fun k : ℕ ↦
    let z := spectralRadiusNode B j schedule k
    let num := denominatorEvalFromHistory (spectralFold p.n 0) 1 z schedule.fuel samples
    let den := denominatorEvalFromHistory (spectralFold p.n 0) 0 z schedule.fuel samples
    let quotient := if h : den.normSq.hi < 0 ∨ 0 < den.normSq.lo then num.div den h
      else ComplexRatInterval.zero
    quotient.mul (tangentNode (B.rhoName j) (bankRadiusPrecision schedule.tolerance
      (spectralNodeTarget schedule.tolerance).1) schedule.inputPrecision schedule k)
  let integral := CircleMesh.integralEnclosure node L hL schedule.mesh schedule.mesh_pos
  boundedContourNormalize integral 1 schedule.inputPrecision

private def windingEnclosureAt {p : Parameters} (input : RepresentedSpectralInput p) (B : ContourBankData)
    (j : Fin (B.JBase + 1)) (pilot : RatInterval) (L scheduleMagnitude : ℚ) :
    ComplexRatInterval :=
  if hp : 0 < pilot.lo then
    if hL : 0 ≤ L then
      if hMagnitude : 0 ≤ scheduleMagnitude then
        let lower : PosRat := ⟨pilot.lo, hp⟩
        let operations := spectralNodeOperationCount .winding (spectralFold p.n 0).card
        let tolerance := estimatorNodePrecision
          (guardedNodeTolerance windingNodeTolerance lower)
          (spectralNodeScale B j scheduleMagnitude lower 1 operations)
        let schedule := spectralSchedule tolerance
          operations L scheduleMagnitude hL hMagnitude
        let samples := fun fuel : Fin (schedule.fuel + 1) ↦ fun i : Fin p.n ↦
          ((input.observations i).tName.approx fuel,
            (input.observations i).gName.approx fuel)
        windingFinish B j schedule L hL samples
      else ComplexRatInterval.zero
    else ComplexRatInterval.zero
  else ComplexRatInterval.zero

private lemma windingEnclosure_eq_at {p : Parameters} (input : RepresentedSpectralInput p)
    (B : ContourBankData) (j : Fin (B.JBase + 1)) :
    windingEnclosure input B j =
      let pilot := pilotModulus input B 0 j
      windingEnclosureAt input B j pilot
        (windingLipschitzBound input (radiusUpper B j) pilot.lo)
        (windingScheduleMagnitudeAt input B j pilot.lo) := by
  unfold windingEnclosure
  dsimp only
  split
  · rename_i hp
    have hL : 0 ≤ windingLipschitzBound input (radiusUpper B j)
        (pilotModulus input B 0 j).lo :=
      windingLipschitzBound_nonneg input (radiusUpper_nonneg B j) hp
    have hM : 0 ≤ windingScheduleMagnitudeAt input B j
        (pilotModulus input B 0 j).lo := by
      unfold windingScheduleMagnitudeAt
      positivity
    simp only [windingEnclosureAt, hp, hL, hM, ↓reduceDIte]
    unfold spectralWindingEvaluator windingScheduleMagnitude
    unfold boundedContourEvaluate BoundedCircleEvaluator.node windingFinish
    unfold spectralRadiusNode
    simp only [spectralDenominatorMap, denominatorEvalFromHistory_of_input]
    rfl
  · simp [windingEnclosureAt, *]

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 4096 in
-- The countable dispatch now conditions on both quadrature and full-box fuel bounds.
/-- Provided [the treatment-regression code used at the current sample size is a measurable
function of the covariates](hyp:hgcode), [the certified rectangular enclosure of the winding
number of the empirical residual transform around a given bank circle, computed from the
certified input built canonically from the data, is a measurable function of the sample](goal).
-/
lemma measurable_windingEnclosure_canonical
    (p : Parameters) (pStar : CertifiedBankInputs p) (cStar : CertifiedRangeInput p)
    (gcode : ℕ → Xspace → ℝ) (hgcode : Measurable (gcode p.n))
    (j : Fin ((contourBank p pStar).JBase + 1)) :
    Measurable (fun data : Fin p.n → Obs Xspace ↦
      windingEnclosure (canonicalRepresentedInput p pStar cStar gcode data)
        (contourBank p pStar) j) := by
  let B := contourBank p pStar
  let input := fun data : Fin p.n → Obs Xspace ↦
    canonicalRepresentedInput p pStar cStar gcode data
  let pilot := fun data ↦ pilotModulus (input data) B 0 j
  have hpilot : Measurable pilot :=
    measurable_pilotModulus_canonical p pStar cStar gcode hgcode 0 j
  rw [show (fun data ↦ windingEnclosure (input data) B j) =
      (fun data ↦ windingEnclosureAt (input data) B j (pilot data)
        (windingLipschitzBound (input data) (radiusUpper B j) (pilot data).lo)
        (windingScheduleMagnitudeAt (input data) B j (pilot data).lo)) by
    funext data
    exact windingEnclosure_eq_at (input data) B j]
  let pilotJoint := fun state : (Fin p.n → Obs Xspace) × RatInterval ↦
    windingEnclosureAt (input state.1) B j state.2
      (windingLipschitzBound (input state.1) (radiusUpper B j) state.2.lo)
      (windingScheduleMagnitudeAt (input state.1) B j state.2.lo)
  apply (show Measurable pilotJoint from ?_).comp (measurable_id.prodMk hpilot)
  apply measurable_from_prod_countable_left
  intro fixedPilot
  let lipschitz := fun data ↦
    windingLipschitzBound (input data) (radiusUpper B j) fixedPilot.lo
  have hlipschitz : Measurable lipschitz := by
    have hresiduals : Measurable (fun data : Fin p.n → Obs Xspace ↦ fun i ↦
        residualUpper (input data) i) := by
      exact measurable_pi_lambda _ fun i ↦
        measurable_residualUpper_canonical p pStar cStar gcode hgcode i
    let finish : (Fin p.n → ℚ) → ℚ := fun residuals ↦
      64 * (radiusUpper B j *
          (∑ i, residuals i ^ 1 * rationalExpEnvelope (radiusUpper B j) (residuals i)) /
            fixedPilot.lo +
        radiusUpper B j ^ 2 *
          ((∑ i, residuals i ^ 2 * rationalExpEnvelope (radiusUpper B j) (residuals i)) /
              fixedPilot.lo +
            (∑ i, residuals i ^ 1 * rationalExpEnvelope (radiusUpper B j) (residuals i)) ^ 2 /
              fixedPilot.lo ^ 2))
    exact (measurable_of_countable finish).comp hresiduals
  let magnitude := fun data ↦
    windingScheduleMagnitudeAt (input data) B j fixedPilot.lo
  have hmagnitude : Measurable magnitude := by
    have hQ0 := measurable_empiricalFWidthBound_canonical
      p pStar cStar gcode hgcode (spectralFullBoxRadius B) 0
    have hQ1 := measurable_empiricalFWidthBound_canonical
      p pStar cStar gcode hgcode (spectralFullBoxRadius B) 1
    let finish : ℚ × ℚ → ℚ := fun q ↦
      ((max ((128 * max 1 q.1) ^ 2).num.natAbs
        ((128 * max 1 q.2) ^ 2).num.natAbs : ℕ) : ℚ)
    simpa [magnitude, windingScheduleMagnitudeAt, finish, Function.comp_def] using
      (measurable_of_countable finish).comp (hQ0.prodMk hQ1)
  let scheduleKey := fun data ↦ (lipschitz data, magnitude data)
  have hscheduleKey : Measurable scheduleKey := hlipschitz.prodMk hmagnitude
  let lipschitzJoint := fun state : (Fin p.n → Obs Xspace) × (ℚ × ℚ) ↦
    windingEnclosureAt (input state.1) B j fixedPilot state.2.1 state.2.2
  apply (show Measurable lipschitzJoint from ?_).comp (measurable_id.prodMk hscheduleKey)
  apply measurable_from_prod_countable_left
  intro fixedKey
  let fixedL := fixedKey.1
  let fixedMagnitude := fixedKey.2
  dsimp [lipschitzJoint]
  unfold windingEnclosureAt
  split
  · split
    · split
      · let tolerance := estimatorNodePrecision
          (guardedNodeTolerance windingNodeTolerance ⟨fixedPilot.lo, ‹0 < fixedPilot.lo›⟩)
            (spectralNodeScale B j fixedMagnitude
              ⟨fixedPilot.lo, ‹0 < fixedPilot.lo›⟩ 1
              (spectralNodeOperationCount .winding (spectralFold p.n 0).card))
        let schedule := spectralSchedule tolerance
          (spectralNodeOperationCount .winding (spectralFold p.n 0).card)
          fixedL fixedMagnitude ‹0 ≤ fixedL› ‹0 ≤ fixedMagnitude›
        let samples := fun data : Fin p.n → Obs Xspace ↦
          fun fuel : Fin (schedule.fuel + 1) ↦ fun i : Fin p.n ↦
            (((input data).observations i).tName.approx fuel,
              ((input data).observations i).gName.approx fuel)
        have hsamples : Measurable samples := by
          apply measurable_pi_lambda
          intro fuel
          apply measurable_pi_lambda
          intro i
          exact (measurable_treatmentApprox p pStar cStar gcode i (fun _ ↦ (fuel : ℕ))
            measurable_const).prodMk
            (measurable_codeApprox p pStar cStar gcode hgcode i (fun _ ↦ (fuel : ℕ))
              measurable_const)
        exact (measurable_of_countable
          (windingFinish B j schedule fixedL ‹0 ≤ fixedL›)).comp hsamples
      · exact measurable_const
    · exact measurable_const
  · exact measurable_const

private lemma measurable_outcomeUpper_canonical
    (p : Parameters) (pStar : CertifiedBankInputs p) (cStar : CertifiedRangeInput p)
    (gcode : ℕ → Xspace → ℝ) (i : Fin p.n) :
    Measurable (fun data : Fin p.n → Obs Xspace ↦
      outcomeUpper (canonicalRepresentedInput p pStar cStar gcode data) i) := by
  let fuel := fun data : Fin p.n → Obs Xspace ↦
    (((canonicalRepresentedInput p pStar cStar gcode data).observations i).yName.modulus
      errorOne)
  have hfuel : Measurable fuel := by
    dsimp [fuel, canonicalRepresentedInput, canonicalObservationName]
    fun_prop
  have hinterval := measurable_outcomeApprox p pStar cStar gcode i fuel hfuel
  exact (measurable_of_countable (fun interval : RatInterval ↦ interval.maxAbs)).comp hinterval

private lemma measurable_empiricalGDerivativeBound_canonical
    (p : Parameters) (pStar : CertifiedBankInputs p) (cStar : CertifiedRangeInput p)
    (gcode : ℕ → Xspace → ℝ) (hgcode : Measurable (gcode p.n))
    (rho : ℚ) (derivative : ℕ) :
    Measurable (fun data : Fin p.n → Obs Xspace ↦
      empiricalGDerivativeBound (canonicalRepresentedInput p pStar cStar gcode data)
        rho derivative) := by
  have hsummary : Measurable (fun data : Fin p.n → Obs Xspace ↦ fun i ↦
      (residualUpper (canonicalRepresentedInput p pStar cStar gcode data) i,
        outcomeUpper (canonicalRepresentedInput p pStar cStar gcode data) i)) := by
    apply measurable_pi_lambda
    intro i
    exact (measurable_residualUpper_canonical p pStar cStar gcode hgcode i).prodMk
      (measurable_outcomeUpper_canonical p pStar cStar gcode i)
  let finish : (Fin p.n → ℚ × ℚ) → ℚ := fun summary ↦
    ∑ i, (summary i).2 * (summary i).1 ^ derivative *
      rationalExpEnvelope rho (summary i).1
  exact (measurable_of_countable finish).comp hsummary

set_option maxHeartbeats 2400000 in
-- Expanding the canonical G width summary through the finite product is arithmetic-heavy.
private lemma measurable_empiricalGWidthBound_canonical
    (p : Parameters) (pStar : CertifiedBankInputs p) (cStar : CertifiedRangeInput p)
    (gcode : ℕ → Xspace → ℝ) (hgcode : Measurable (gcode p.n))
    (rho : ℚ) (derivative : ℕ) :
    Measurable (fun data : Fin p.n → Obs Xspace ↦
      empiricalGWidthBound (canonicalRepresentedInput p pStar cStar gcode data)
        rho derivative) := by
  let summary := fun data : Fin p.n → Obs Xspace ↦ fun i ↦
      (residualUpper (canonicalRepresentedInput p pStar cStar gcode data) i,
        outcomeUpper (canonicalRepresentedInput p pStar cStar gcode data) i)
  have hsummary : Measurable summary := by
    apply measurable_pi_lambda
    intro i
    exact (measurable_residualUpper_canonical p pStar cStar gcode hgcode i).prodMk
      (measurable_outcomeUpper_canonical p pStar cStar gcode i)
  let finish : (Fin p.n → ℚ × ℚ) → ℚ := fun summary ↦
    ∑ i, (max 1 (summary i).2 * (rho + 1) * (derivative + 1) *
      (2 * max 1 (summary i).1) ^ (derivative + 1) *
      rationalExpEnvelope rho (summary i).1) ^ 8
  have hcomposed := (measurable_of_countable finish).comp hsummary
  simpa only [Function.comp_def, finish, summary, empiricalGWidthBound] using hcomposed

private def numeratorRawEvalFromIntervals {p : Parameters} (I : Finset (Fin p.n))
    (derivative : ℕ) (samples : Fin p.n → (RatInterval × RatInterval) × RatInterval)
    (z : ComplexRatInterval) (fuel : ℕ) : ComplexRatInterval :=
  let terms := I.toList.map fun i ↦
    let residual := (samples i).1.1.add (samples i).1.2.neg
    let weight := (samples i).2
    let argument := z.mul (realRect residual)
    let exponential := BoundedCertifiedComplex.centeredComplexExp argument fuel
    (realRect (weight.mul (residual.npow derivative))).mul exponential
  (intervalSum terms).smulRat ((max I.card 1 : ℚ)⁻¹)

private def numeratorEvalFromHistory {p : Parameters} (I : Finset (Fin p.n))
    (derivative : ℕ) (z : ComplexRatInterval) (fuel : ℕ)
    (samples : Fin (fuel + 1) → Fin p.n → (RatInterval × RatInterval) × RatInterval) :
    ComplexRatInterval :=
  tightenHistory (fun sample m => numeratorRawEvalFromIntervals I derivative sample z m)
    fuel samples

private lemma numeratorEvalFromHistory_of_input {p : Parameters}
    (input : RepresentedSpectralInput p) (I : Finset (Fin p.n))
    (derivative : ℕ) (z : ComplexRatInterval) (fuel : ℕ) :
    numeratorEvalFromHistory I derivative z fuel (fun m i =>
        (((input.observations i).tName.approx m,
            (input.observations i).gName.approx m),
          (input.observations i).yName.approx m)) =
      spectralNumeratorEval input I derivative z fuel := by
  unfold numeratorEvalFromHistory
  calc
    _ = tightenAcrossFuel (fun m => numeratorRawEvalFromIntervals I derivative
        (fun i => (((input.observations i).tName.approx m,
            (input.observations i).gName.approx m),
          (input.observations i).yName.approx m)) z m) fuel :=
      by
        simpa only using tightenHistory_of_sequence
          (fun sample m => numeratorRawEvalFromIntervals I derivative sample z m)
          (fun m i => (((input.observations i).tName.approx m,
              (input.observations i).gName.approx m),
            (input.observations i).yName.approx m)) fuel
    _ = spectralNumeratorEval input I derivative z fuel := rfl

private def evaluationScheduleMagnitudeAt (input : RepresentedSpectralInput p)
    (B : ContourBankData) (j : Fin (B.JBase + 1)) (N : ℕ) (lower : ℚ) : ℚ :=
  let QF := empiricalFWidthBound input (spectralFullBoxRadius B) 0
  let QG := empiricalGWidthBound input (spectralFullBoxRadius B) 0
  let AF := ((128 * max 1 QF) ^ 2).num.natAbs
  let AG := ((256 * max 1 QG) ^ 2).num.natAbs
  ((max AF AG : ℕ) : ℚ)

private def evaluationFinish {p : Parameters} (B : ContourBankData)
    (j : Fin (B.JBase + 1)) (N : ℕ) (schedule : Schedule)
    (L : ℚ) (hL : 0 ≤ L)
    (samples : Fin (schedule.fuel + 1) →
      Fin p.n → (RatInterval × RatInterval) × RatInterval) : ComplexRatInterval :=
  let node := fun k : ℕ ↦
    let z := spectralRadiusNode B j schedule k
    let num := numeratorEvalFromHistory (spectralFold p.n 1) 0 z schedule.fuel samples
    let den := denominatorEvalFromHistory (spectralFold p.n 1) 0 z schedule.fuel
      (fun fuel i ↦ (samples fuel i).1)
    let quotient := if h : den.normSq.hi < 0 ∨ 0 < den.normSq.lo then num.div den h
      else ComplexRatInterval.zero
    quotient.mul (tangentNode (B.rhoName j) (bankRadiusPrecision schedule.tolerance
      (spectralNodeTarget schedule.tolerance).1) schedule.inputPrecision schedule k)
  let integral := CircleMesh.integralEnclosure node L hL schedule.mesh schedule.mesh_pos
  boundedContourNormalize integral (max N 1) schedule.inputPrecision

private def evaluationEnclosureAt {p : Parameters} (input : RepresentedSpectralInput p)
    (B : ContourBankData) (j : Fin (B.JBase + 1)) (N : ℕ) (pilot : RatInterval)
    (L scheduleMagnitude : ℚ) : ComplexRatInterval :=
  if hp : 0 < pilot.lo then
    if hL : 0 ≤ L then
      if hMagnitude : 0 ≤ scheduleMagnitude then
        let lower : PosRat := ⟨pilot.lo, hp⟩
        let operations := spectralNodeOperationCount .evaluation (spectralFold p.n 1).card
        let tolerance := estimatorNodePrecision
          (guardedNodeTolerance (evaluationNodeTolerance p) lower)
            (spectralNodeScale B j scheduleMagnitude lower (max N 1) operations)
        let schedule := spectralSchedule tolerance
          operations L scheduleMagnitude hL hMagnitude
        let samples := fun fuel : Fin (schedule.fuel + 1) ↦ fun i : Fin p.n ↦
          (((input.observations i).tName.approx fuel,
              (input.observations i).gName.approx fuel),
            (input.observations i).yName.approx fuel)
        evaluationFinish B j N schedule L hL samples
      else ComplexRatInterval.zero
    else ComplexRatInterval.zero
  else ComplexRatInterval.zero

private lemma evaluationEnclosure_eq_at {p : Parameters} (input : RepresentedSpectralInput p)
    (B : ContourBankData) (j : Fin (B.JBase + 1)) (N : ℕ) :
    evaluationEnclosure input B j N =
      let pilot := pilotModulus input B 1 j
      evaluationEnclosureAt input B j N pilot
        (momentLipschitzBound input (radiusUpper B j) pilot.lo N)
        (evaluationScheduleMagnitudeAt input B j N pilot.lo) := by
  unfold evaluationEnclosure
  dsimp only
  split
  · rename_i hp
    have hL : 0 ≤ momentLipschitzBound input (radiusUpper B j)
        (pilotModulus input B 1 j).lo N :=
      momentLipschitzBound_nonneg input N (radiusUpper_nonneg B j) hp
    have hM : 0 ≤ evaluationScheduleMagnitudeAt input B j N
        (pilotModulus input B 1 j).lo := by
      unfold evaluationScheduleMagnitudeAt
      positivity
    simp only [evaluationEnclosureAt, hp, hL, hM, ↓reduceDIte]
    unfold spectralEvaluationEvaluator evaluationScheduleMagnitude
    unfold boundedContourEvaluate BoundedCircleEvaluator.node evaluationFinish
    unfold spectralRadiusNode
    simp only [spectralNumeratorMap, spectralDenominatorMap,
      numeratorEvalFromHistory_of_input, denominatorEvalFromHistory_of_input]
    rfl
  · simp [evaluationEnclosureAt, *]

set_option maxHeartbeats 2400000 in
set_option maxRecDepth 4096 in
-- The countable dispatch now conditions on both quadrature and full-box fuel bounds.
/-- Provided [the treatment-regression code used at the current sample size is a measurable
function of the covariates](hyp:hgcode), [the certified rectangular enclosure of the contour
moment on a given bank circle at a given quadrature order, computed from the certified input
built canonically from the data, is a measurable function of the sample](goal). -/
lemma measurable_evaluationEnclosure_canonical
    (p : Parameters) (pStar : CertifiedBankInputs p) (cStar : CertifiedRangeInput p)
    (gcode : ℕ → Xspace → ℝ) (hgcode : Measurable (gcode p.n))
    (j : Fin ((contourBank p pStar).JBase + 1)) (N : ℕ) :
    Measurable (fun data : Fin p.n → Obs Xspace ↦
      evaluationEnclosure (canonicalRepresentedInput p pStar cStar gcode data)
        (contourBank p pStar) j N) := by
  let B := contourBank p pStar
  let input := fun data : Fin p.n → Obs Xspace ↦
    canonicalRepresentedInput p pStar cStar gcode data
  let pilot := fun data ↦ pilotModulus (input data) B 1 j
  have hpilot : Measurable pilot :=
    measurable_pilotModulus_canonical p pStar cStar gcode hgcode 1 j
  rw [show (fun data ↦ evaluationEnclosure (input data) B j N) =
      (fun data ↦ evaluationEnclosureAt (input data) B j N (pilot data)
        (momentLipschitzBound (input data) (radiusUpper B j) (pilot data).lo N)
        (evaluationScheduleMagnitudeAt (input data) B j N (pilot data).lo)) by
    funext data
    exact evaluationEnclosure_eq_at (input data) B j N]
  let pilotJoint := fun state : (Fin p.n → Obs Xspace) × RatInterval ↦
    evaluationEnclosureAt (input state.1) B j N state.2
      (momentLipschitzBound (input state.1) (radiusUpper B j) state.2.lo N)
      (evaluationScheduleMagnitudeAt (input state.1) B j N state.2.lo)
  apply (show Measurable pilotJoint from ?_).comp (measurable_id.prodMk hpilot)
  apply measurable_from_prod_countable_left
  intro fixedPilot
  let lipschitz := fun data ↦
    momentLipschitzBound (input data) (radiusUpper B j) fixedPilot.lo N
  have hlipschitz : Measurable lipschitz := by
    have hG0 := measurable_empiricalGDerivativeBound_canonical
      p pStar cStar gcode hgcode (radiusUpper B j) 0
    have hG1 := measurable_empiricalGDerivativeBound_canonical
      p pStar cStar gcode hgcode (radiusUpper B j) 1
    have hF1 := measurable_empiricalFDerivativeBound_canonical
      p pStar cStar gcode hgcode (radiusUpper B j) 1
    dsimp [lipschitz, input, B]
    unfold momentLipschitzBound
    fun_prop
  let magnitude := fun data ↦
    evaluationScheduleMagnitudeAt (input data) B j N fixedPilot.lo
  have hmagnitude : Measurable magnitude := by
    have hQG := measurable_empiricalGWidthBound_canonical
      p pStar cStar gcode hgcode (spectralFullBoxRadius B) 0
    have hQF := measurable_empiricalFWidthBound_canonical
      p pStar cStar gcode hgcode (spectralFullBoxRadius B) 0
    let finish : ℚ × ℚ → ℚ := fun q ↦
      ((max ((128 * max 1 q.1) ^ 2).num.natAbs
        ((256 * max 1 q.2) ^ 2).num.natAbs : ℕ) : ℚ)
    simpa [magnitude, evaluationScheduleMagnitudeAt, finish, Function.comp_def] using
      (measurable_of_countable finish).comp (hQF.prodMk hQG)
  let scheduleKey := fun data ↦ (lipschitz data, magnitude data)
  have hscheduleKey : Measurable scheduleKey := hlipschitz.prodMk hmagnitude
  let lipschitzJoint := fun state : (Fin p.n → Obs Xspace) × (ℚ × ℚ) ↦
    evaluationEnclosureAt (input state.1) B j N fixedPilot state.2.1 state.2.2
  apply (show Measurable lipschitzJoint from ?_).comp (measurable_id.prodMk hscheduleKey)
  apply measurable_from_prod_countable_left
  intro fixedKey
  let fixedL := fixedKey.1
  let fixedMagnitude := fixedKey.2
  dsimp [lipschitzJoint]
  unfold evaluationEnclosureAt
  split
  · split
    · split
      · let tolerance := estimatorNodePrecision
          (guardedNodeTolerance (evaluationNodeTolerance p)
            ⟨fixedPilot.lo, ‹0 < fixedPilot.lo›⟩)
            (spectralNodeScale B j fixedMagnitude
              ⟨fixedPilot.lo, ‹0 < fixedPilot.lo›⟩ (max N 1)
              (spectralNodeOperationCount .evaluation (spectralFold p.n 1).card))
        let schedule := spectralSchedule tolerance
          (spectralNodeOperationCount .evaluation (spectralFold p.n 1).card)
          fixedL fixedMagnitude ‹0 ≤ fixedL› ‹0 ≤ fixedMagnitude›
        let samples := fun data : Fin p.n → Obs Xspace ↦
          fun fuel : Fin (schedule.fuel + 1) ↦ fun i : Fin p.n ↦
            ((((input data).observations i).tName.approx fuel,
                ((input data).observations i).gName.approx fuel),
              ((input data).observations i).yName.approx fuel)
        have hsamples : Measurable samples := by
          apply measurable_pi_lambda
          intro fuel
          apply measurable_pi_lambda
          intro i
          exact ((measurable_treatmentApprox p pStar cStar gcode i (fun _ ↦ (fuel : ℕ))
            measurable_const).prodMk
            (measurable_codeApprox p pStar cStar gcode hgcode i (fun _ ↦ (fuel : ℕ))
              measurable_const)).prodMk
            (measurable_outcomeApprox p pStar cStar gcode i (fun _ ↦ (fuel : ℕ))
              measurable_const)
        exact (measurable_of_countable
          (evaluationFinish B j N schedule fixedL ‹0 ≤ fixedL›)).comp hsamples
      · exact measurable_const
    · exact measurable_const
  · exact measurable_const

/-- The raw rational projection of the option-A program, separated from its
certified output name and diagnostic trace. -/
def ordinarySpectralRaw (input : RepresentedSpectralInput p) : ℚ :=
  let B := contourBank p input.primitive
  let outcomes := fun j : Fin (B.JBase + 1) ↦
    let modulus := pilotModulus input B 0 j
    let winding := windingEnclosure input B j
    PilotOutcome.mk modulus winding (uniqueNonnegativeInteger winding)
  match selectedContourFrom B outcomes with
  | none => 0
  | some j =>
      match (outcomes j).decoded with
      | none => 0
      | some N =>
          let modulus := pilotModulus input B 1 j
          if B.aStarRat / 4 ≤ modulus.lo then
            rationalMidpoint (evaluationEnclosure input B j N).re
          else 0

/-- Erasing the certified name and trace from the option-A program preserves
its raw rational result. -/
lemma instrumentedSpectralProgram_raw_eq (input : RepresentedSpectralInput p) :
    (instrumentedSpectralProgram input).raw = ordinarySpectralRaw input := by
  unfold instrumentedSpectralProgram spectralProgramWith ordinarySpectralRaw
  dsimp only
  generalize hselection : selectedContourFrom _ _ = selection
  cases selection with
  | none => simp only [hselection]
  | some j =>
      simp only [hselection]
      generalize hdecoded : uniqueNonnegativeInteger _ = decoded
      cases decoded with
      | none => simp only [hdecoded]
      | some N =>
          simp only [hdecoded]
          split <;> rfl

/-- A measurable countable-valued control state may select among measurable branches. -/
lemma measurable_countable_dispatch {Ω κ β : Type*} [MeasurableSpace Ω]
    [MeasurableSpace κ] [Countable κ] [MeasurableSingletonClass κ]
    [MeasurableSpace β] (key : Ω → κ) (hkey : Measurable key)
    (branch : κ → Ω → β) (hbranch : ∀ k, Measurable (branch k)) :
    Measurable (fun ω ↦ branch (key ω) ω) := by
  let joint : Ω × κ → β := fun state ↦ branch state.2 state.1
  have hjoint : Measurable joint := by
    apply measurable_from_prod_countable_left
    exact hbranch
  exact hjoint.comp (measurable_id.prodMk hkey)

set_option maxHeartbeats 800000 in
/-- The rational output of the canonical option-A program is Borel measurable. -/
lemma ordinaryFiniteRationalResult_raw_measurable
    (p : Parameters) (pStar : CertifiedBankInputs p) (cStar : CertifiedRangeInput p)
    (gcode : ℕ → Xspace → ℝ) (hgcode : Measurable (gcode p.n)) :
    Measurable (fun data : Fin p.n → Obs Xspace ↦
      ((ordinaryFiniteRationalResult p pStar cStar gcode data).raw : ℝ)) := by
  apply (show Measurable (fun q : ℚ ↦ (q : ℝ)) from measurable_of_countable _).comp
  simp only [ordinaryFiniteRationalResult, ordinarySpectralProgram,
    instrumentedSpectralProgram_raw_eq]
  let B := contourBank p pStar
  let input := fun data : Fin p.n → Obs Xspace ↦
    canonicalRepresentedInput p pStar cStar gcode data
  let outcomes := fun data (j : Fin (B.JBase + 1)) ↦
    let modulus := pilotModulus (input data) B 0 j
    let winding := windingEnclosure (input data) B j
    PilotOutcome.mk modulus winding (uniqueNonnegativeInteger winding)
  let accept := fun j data ↦ pilotBestFrom B (outcomes data) j
  let selection := fun data ↦ selectedContourFrom B (outcomes data)
  letI : MeasurableSpace (Fin (B.JBase + 1)) := ⊤
  letI : MeasurableSpace (Option (Fin (B.JBase + 1))) := ⊤
  letI : MeasurableSpace (Option ℕ) := ⊤
  change Measurable (fun data ↦
    match selection data with
    | none => (0 : ℚ)
    | some j =>
        match (outcomes data j).decoded with
        | none => (0 : ℚ)
        | some N =>
            let modulus := pilotModulus (input data) B 1 j
            if B.aStarRat / 4 ≤ modulus.lo then
              rationalMidpoint (evaluationEnclosure (input data) B j N).re
            else (0 : ℚ))
  have hselection : Measurable selection := by
    let summary := fun data : Fin p.n → Obs Xspace ↦
      fun j : Fin (B.JBase + 1) ↦
        (pilotModulus (input data) B 0 j, windingEnclosure (input data) B j)
    have hsummary : Measurable summary := by
      apply measurable_pi_lambda
      intro j
      exact (measurable_pilotModulus_canonical p pStar cStar gcode hgcode 0 j).prodMk
        (measurable_windingEnclosure_canonical p pStar cStar gcode hgcode j)
    let choose := fun state : Fin (B.JBase + 1) → RatInterval × ComplexRatInterval ↦
      selectedContourFrom B (fun j ↦
        ⟨(state j).1, (state j).2, uniqueNonnegativeInteger (state j).2⟩)
    have hchoose : Measurable choose := measurable_of_countable choose
    convert hchoose.comp hsummary using 1
    rfl
  refine measurable_countable_dispatch selection hselection
    (fun selected data ↦
      match selected with
      | none => (0 : ℚ)
      | some j =>
          match (outcomes data j).decoded with
          | none => (0 : ℚ)
          | some N =>
              let modulus := pilotModulus (input data) B 1 j
              if B.aStarRat / 4 ≤ modulus.lo then
                rationalMidpoint (evaluationEnclosure (input data) B j N).re
              else (0 : ℚ)) ?_
  intro selected
  cases selected with
  | none => exact measurable_const
  | some j =>
      let decoded := fun data ↦ (outcomes data j).decoded
      have hdecoded : Measurable decoded := by
        have hwinding :=
          measurable_windingEnclosure_canonical p pStar cStar gcode hgcode j
        exact (measurable_of_countable uniqueNonnegativeInteger).comp hwinding
      refine measurable_countable_dispatch decoded hdecoded
        (fun decodedValue data ↦
          match decodedValue with
          | none => (0 : ℚ)
          | some N =>
              let modulus := pilotModulus (input data) B 1 j
              if B.aStarRat / 4 ≤ modulus.lo then
                rationalMidpoint (evaluationEnclosure (input data) B j N).re
              else (0 : ℚ)) ?_
      intro decodedValue
      cases decodedValue with
      | none => exact measurable_const
      | some N =>
          have hpilot : Measurable (fun data : Fin p.n → Obs Xspace ↦
              pilotModulus (input data) B 1 j) :=
            measurable_pilotModulus_canonical p pStar cStar gcode hgcode 1 j
          have hevaluation : Measurable (fun data : Fin p.n → Obs Xspace ↦
              evaluationEnclosure (input data) B j N) :=
            measurable_evaluationEnclosure_canonical p pStar cStar gcode hgcode j N
          let finish : RatInterval × ComplexRatInterval → ℚ := fun state ↦
            if B.aStarRat / 4 ≤ state.1.lo then rationalMidpoint state.2.re else 0
          exact (measurable_of_countable finish).comp (hpilot.prodMk hevaluation)

end CausalSmith.Stat.SaPlmCumulantConverse
