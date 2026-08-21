import CausalSmith.Stat.STAT_SaPlmCumulantConverse_Research.Helpers.ContourBank
import CausalSmith.Stat.STAT_SaPlmCumulantConverse_Research.Helpers.BoundedCertifiedComplex
import Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.FiniteSearch
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-! # One bounded-domain certified spectral evaluator
The ordinary and represented layers below are distinct wrappers around the
same finite bounded-domain adapter.  The adapter refines the certified-real
bank radius, multiplies it by a reused radius-one circle node, evaluates the
finite empirical transforms, forms the guarded quotient times the full circle
tangent, applies endpoint-complete quadrature, and normalizes only afterwards.
-/

noncomputable section

open MeasureTheory Set intervalIntegral
open Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic
open Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.FiniteSearch
open Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Complex

namespace CausalSmith.Stat.SaPlmCumulantConverse

variable {Xspace : Type*} [MeasurableSpace Xspace]

/-- A certified record for the experiment-wide range constant Ctheta: a strictly positive
real number supplied as a certified name (a nested family of rational enclosures with an
explicit accuracy modulus), together with the requirement that the number it names is
exactly the parameter block's range constant Ctheta. -/
structure CertifiedRangeInput (p : Parameters) where
  CthetaName : PositiveCertifiedReal
  Ctheta_value : CthetaName.name.value = p.Ctheta

/-- The sole experiment-wide primitive-record pair. -/
structure FixedExperimentRecords (p0 : Parameters) where
  bank : CertifiedBankInputs p0
  range : CertifiedRangeInput p0

/-- Two parameter blocks carry the same experiment-wide constants: the fixed order r, the
cumulant-separation constant delta, the target range constant Ctheta, the treatment- and
outcome-regression bounds Cg and Cq, and the two noise scales psieta and psixi all agree.
Sample size and the remaining parameters are unconstrained. -/
def SameFixedExperimentConstants (p q : Parameters) : Prop :=
  p.r = q.r ∧ p.delta = q.delta ∧ p.Ctheta = q.Ctheta ∧ p.Cg = q.Cg ∧
    p.Cq = q.Cq ∧ p.psieta = q.psieta ∧ p.psixi = q.psixi

/-- Reuse one certified range record for a second parameter block whose range constant
Ctheta is the same number. The certified name itself is reused verbatim; only the
propositional contract identifying its value with the range constant is transported. -/
def CertifiedRangeInput.transport {p q : Parameters}
    (cStar : CertifiedRangeInput p) (h : p.Ctheta = q.Ctheta) :
    CertifiedRangeInput q where
  CthetaName := cStar.CthetaName
  Ctheta_value := cStar.Ctheta_value.trans h

/-- Reuse one certified primitive-record bundle (cumulant order, separation constant,
noise scale, and the two search radii) for a second parameter block that carries the same
experiment-wide constants. -/
def fixedBankInput {p q : Parameters} (pStar : CertifiedBankInputs p)
    (h : SameFixedExperimentConstants p q) : CertifiedBankInputs q :=
  pStar.transport (by rw [p.k_eq, q.k_eq, h.1]) h.2.1 h.2.2.2.2.2.1

/-- Reuse one certified range record for a second parameter block that carries the same
experiment-wide constants. -/
def fixedRangeInput {p q : Parameters} (cStar : CertifiedRangeInput p)
    (h : SameFixedExperimentConstants p q) : CertifiedRangeInput q :=
  cStar.transport h.2.2.1

/-- Canonical floor-dyadic observation interval. -/
noncomputable def canonicalDyadicInterval (x : ℝ) (precision : ℕ) : RatInterval :=
  let scale : ℚ := (2 : ℚ) ^ (precision + 1)
  let lower : ℚ := (⌊(2 : ℝ) ^ (precision + 1) * x⌋ : ℤ) / scale
  ⟨lower, lower + 1 / scale, le_add_of_nonneg_right (by positivity)⟩

/-- Increasing the precision of the canonical dyadic enclosure of a real number by one
binary digit [shrinks the interval: the finer enclosure is contained in the coarser
one](goal). -/
lemma canonicalDyadic_nested (x : ℝ) (precision : ℕ) :
    (canonicalDyadicInterval x (precision + 1)).Subinterval
      (canonicalDyadicInterval x precision) := by
  have hf : ⌊(2 : ℝ) ^ (precision + 1) * x⌋ =
      ⌊(2 : ℝ) ^ (precision + 1 + 1) * x⌋ / 2 := by
    rw [show (2 : ℝ) ^ (precision + 1) * x =
        ((2 : ℝ) ^ (precision + 1 + 1) * x) / 2 by
          rw [pow_succ]
          ring]
    exact Int.floor_div_natCast _ 2
  let b : ℤ := ⌊(2 : ℝ) ^ (precision + 1 + 1) * x⌋
  have hbLower : 2 * (b / 2) ≤ b := by
    simpa [mul_comm] using Int.ediv_mul_le b (by norm_num : (2 : ℤ) ≠ 0)
  have hbRem : b % 2 < 2 := by
    simpa using Int.emod_lt b (by norm_num : (2 : ℤ) ≠ 0)
  have hbEq : b / 2 * 2 + b % 2 = b := Int.ediv_mul_add_emod b 2
  have hbUpper : b + 1 ≤ 2 * (b / 2 + 1) := by omega
  have hpow : (2 : ℚ) ^ (precision + 1 + 1) =
      2 * (2 : ℚ) ^ (precision + 1) := by
    rw [pow_succ]
    ring
  unfold canonicalDyadicInterval
  simp only [RatInterval.Subinterval]
  rw [hf]
  change ((b / 2 : ℤ) : ℚ) / (2 : ℚ) ^ (precision + 1) ≤
      (b : ℚ) / (2 : ℚ) ^ (precision + 1 + 1) ∧
    (b : ℚ) / (2 : ℚ) ^ (precision + 1 + 1) +
        1 / (2 : ℚ) ^ (precision + 1 + 1) ≤
      ((b / 2 : ℤ) : ℚ) / (2 : ℚ) ^ (precision + 1) +
        1 / (2 : ℚ) ^ (precision + 1)
  rw [hpow]
  constructor
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hq : (2 : ℚ) * ((b / 2 : ℤ) : ℚ) ≤ b := by exact_mod_cast hbLower
    nlinarith [show (0 : ℚ) < 2 ^ (precision + 1) by positivity]
  · rw [← add_div, ← add_div]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hq : (b : ℚ) + 1 ≤ 2 * (((b / 2 : ℤ) : ℚ) + 1) := by
      exact_mod_cast hbUpper
    nlinarith [show (0 : ℚ) < 2 ^ (precision + 1) by positivity]

/-- At every precision, [the canonical dyadic interval built from a real number actually
contains that number](goal). -/
lemma canonicalDyadic_contains (x : ℝ) (precision : ℕ) :
    (canonicalDyadicInterval x precision).Contains x := by
  unfold canonicalDyadicInterval
  simp only [RatInterval.Contains]
  constructor
  · norm_num
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ (precision + 1))]
    simpa [mul_comm] using Int.floor_le ((2 : ℝ) ^ (precision + 1) * x)
  · norm_num
    have hs : (0 : ℝ) < (2 : ℝ) ^ (precision + 1) := by positivity
    rw [inv_eq_one_div, ← add_div]
    rw [le_div_iff₀ hs]
    simpa [mul_comm] using
      (Int.lt_floor_add_one ((2 : ℝ) ^ (precision + 1) * x)).le

/-- For a positive rational accuracy target, [taking the canonical dyadic enclosure at
precision one more than the denominator of that target makes its width at most the
target](goal). This supplies the explicit accuracy modulus of the canonical name. -/
lemma canonicalDyadic_width (x : ℝ) (e : PosRat) :
    (canonicalDyadicInterval x (e.1.den + 1)).width ≤ e.1 := by
  unfold canonicalDyadicInterval RatInterval.width
  simp only [one_div, add_sub_cancel_left]
  have hpow : ∀ d : ℕ, d ≤ 2 ^ (d + 1 + 1) := by
    intro d
    induction d with
    | zero => simp
    | succ d ih =>
        have hp : 1 ≤ 2 ^ (d + 1 + 1) :=
          Nat.one_le_iff_ne_zero.mpr (Nat.two_pow_pos _).ne'
        calc
          d + 1 ≤ 2 ^ (d + 1 + 1) + 1 := Nat.add_le_add_right ih 1
          _ ≤ 2 * 2 ^ (d + 1 + 1) := by omega
          _ = 2 ^ (d + 1 + 1 + 1) := by rw [pow_succ]; ring
  have hdenQ : (e.1.den : ℚ) ≤ 2 ^ (e.1.den + 1 + 1) := by
    exact_mod_cast hpow e.1.den
  have hfirst : (2 ^ (e.1.den + 1 + 1) : ℚ)⁻¹ ≤ 1 / e.1.den := by
    rw [inv_eq_one_div]
    exact div_le_div_of_nonneg_left zero_le_one
      (by exact_mod_cast e.1.den_pos) hdenQ
  refine hfirst.trans ?_
  calc
    (1 : ℚ) / e.1.den ≤ (e.1.num : ℚ) / e.1.den := by
      apply div_le_div_of_nonneg_right
      · have hn : (0 : ℤ) < e.1.num := Rat.num_pos.mpr e.2
        exact_mod_cast hn
      · exact_mod_cast e.1.den_pos.le
    _ = e.1 := Rat.num_div_den e.1

/-- The canonical certified name of a real number: the number together with its family of
floor-dyadic rational enclosures, the proofs that these are nested and always contain the
number, and the explicit rule converting a requested accuracy into a precision level. -/
noncomputable def canonicalObservationName (x : ℝ) : CertifiedReal where
  value := x
  approx := canonicalDyadicInterval x
  nested := canonicalDyadic_nested x
  contains := canonicalDyadic_contains x
  modulus := fun e ↦ e.1.den + 1
  width_modulus := canonicalDyadic_width x

/-- One observation as seen by the certified evaluator: certified names for the treatment
value, the outcome value, and the clipped treatment-regression code value at that unit. -/
structure RepresentedObservation where
  tName : CertifiedReal
  yName : CertifiedReal
  gName : CertifiedReal

/-- The complete certified input of the spectral estimator: one certified observation
record for each of the n sample units, plus the experiment-wide certified primitive
records (cumulant order, separation, noise scale, search radii) and the certified range
constant. -/
structure RepresentedSpectralInput (p : Parameters) where
  observations : Fin p.n → RepresentedObservation
  primitive : CertifiedBankInputs p
  range : CertifiedRangeInput p

/-- The certified input built directly from a data set: each unit contributes the canonical
certified names of its treatment, its outcome, and its treatment-regression code value
clipped to the interval from minus Cg to Cg; the supplied primitive and range records are
carried over unchanged. -/
noncomputable def canonicalRepresentedInput (p : Parameters)
    (pStar : CertifiedBankInputs p) (cStar : CertifiedRangeInput p)
    (gcode : ℕ → Xspace → ℝ) (data : Fin p.n → Obs Xspace) :
    RepresentedSpectralInput p where
  observations := fun i ↦
    { tName := canonicalObservationName (treatment (data i))
      yName := canonicalObservationName (outcome (data i))
      gName := canonicalObservationName
        (min (max (gcode p.n (covariate (data i))) (-p.Cg)) p.Cg) }
  primitive := pStar
  range := cStar

/-- Take a treatment-regression code sequence and [a second one](hyp:hcode). If [they agree
at every covariate value after clipping to the range from minus Cg to Cg](hyp:hclip), then
[they produce the very same certified input record](goal). Only the clipped code matters to
the estimator. -/
lemma canonicalRepresentedInput_congr_current
    (p : Parameters) (pStar : CertifiedBankInputs p) (cStar : CertifiedRangeInput p)
    (gcode hcode : ℕ → Xspace → ℝ) (data : Fin p.n → Obs Xspace)
    (hclip : ∀ x,
      min (max (gcode p.n x) (-p.Cg)) p.Cg =
        min (max (hcode p.n x) (-p.Cg)) p.Cg) :
    canonicalRepresentedInput p pStar cStar gcode data =
      canonicalRepresentedInput p pStar cStar hcode data := by
  unfold canonicalRepresentedInput
  congr 1
  funext i
  congr 1
  exact congrArg canonicalObservationName (hclip (covariate (data i)))

/-- The certified name of unit i's treatment residual: the certified difference between
the treatment value and the clipped treatment-regression code value at that unit. -/
def representedResidual (input : RepresentedSpectralInput p) (i : Fin p.n) :
    CertifiedReal :=
  CertifiedReal.sub (input.observations i).tName (input.observations i).gName

/-- Selects one of the two deterministic sample-splitting folds: fold index zero gives the
units below the halfway point, fold index one gives the remaining units. -/
def spectralFold (n : ℕ) (a : Fin 2) : Finset (Fin n) :=
  if a = 0 then fold0 n else fold1 n

/-- The fixed disk box used by every empirical-transform map. -/
def spectralDiskBox (B : ContourBankData) : ComplexRatInterval := by
  let U : ℚ := B.UR + 2
  have hU : 0 ≤ U := by
    dsimp [U]
    positivity
  exact ⟨⟨-U, U, by linarith⟩, ⟨-U, U, by linarith⟩⟩

/-- A rational Euclidean-magnitude envelope for every point in
`spectralDiskBox`.  The factor two safely converts the coordinate maximum
used by `ComplexRatInterval.maxAbs` into a complex-norm bound. -/
def spectralFullBoxRadius (B : ContourBankData) : ℚ :=
  2 * (spectralDiskBox B).maxAbs

/-- [The rational magnitude envelope of the fixed evaluation disk is never
negative](goal). -/
lemma spectralFullBoxRadius_nonneg (B : ContourBankData) :
    0 ≤ spectralFullBoxRadius B := by
  unfold spectralFullBoxRadius
  exact mul_nonneg (by norm_num)
    ((abs_nonneg _).trans ((le_max_left _ _).trans (le_max_left _ _)))

/-- Adds up a finite list of complex rational rectangles left to right, starting from the
degenerate rectangle at the origin. -/
def intervalSum (xs : List ComplexRatInterval) : ComplexRatInterval :=
  xs.foldl ComplexRatInterval.add ComplexRatInterval.zero

set_option maxHeartbeats 800000 in
-- The real-axis reduction reuses the general complex-rectangle multiplication bound.
/-- Powers propagate input width with an explicit rational magnitude bound. -/
lemma ratInterval_npow_width_propagation (I : RatInterval) (n : ℕ)
    (A w : ℚ) (hA : 0 ≤ A) (hw : I.width ≤ w) (hmax : I.maxAbs ≤ A) :
    (I.npow n).width ≤ (n : ℚ) * (2 * max 1 A) ^ n * w := by
  have hw0 : 0 ≤ w := (RatInterval.width_nonneg I).trans hw
  have hM0 : 0 ≤ max 1 A := (by positivity)
  have hB0 : 0 ≤ 2 * max 1 A := mul_nonneg (by norm_num) hM0
  have hMleB : max 1 A ≤ 2 * max 1 A := by
    nlinarith [show (1 : ℚ) ≤ max 1 A from le_max_left _ _]
  have hnpowMax : ∀ k : ℕ, (I.npow k).maxAbs ≤ A ^ k := by
    intro k
    induction k with
    | zero => simp [RatInterval.npow, RatInterval.point, RatInterval.maxAbs]
    | succ k ih =>
        have hImax0 : 0 ≤ I.maxAbs := (abs_nonneg I.lo).trans (le_max_left _ _)
        rw [RatInterval.npow, pow_succ]
        exact (RatInterval.maxAbs_mul _ _).trans
          (mul_le_mul ih hmax hImax0 (pow_nonneg hA k))
  have hmulWidth (K L : RatInterval) :
      (K.mul L).width ≤
        2 * (K.maxAbs * L.width + L.maxAbs * K.width) := by
    let KR : ComplexRatInterval := ⟨K, RatInterval.point 0⟩
    let LR : ComplexRatInterval := ⟨L, RatInterval.point 0⟩
    have h := ComplexRatInterval.mul_width KR LR
    have hK0 : 0 ≤ K.maxAbs := (abs_nonneg K.lo).trans (le_max_left _ _)
    have hL0 : 0 ≤ L.maxAbs := (abs_nonneg L.lo).trans (le_max_left _ _)
    have hKw : 0 ≤ K.hi - K.lo := sub_nonneg.mpr K.lo_le_hi
    have hLw : 0 ≤ L.hi - L.lo := sub_nonneg.mpr L.lo_le_hi
    simpa [KR, LR, ComplexRatInterval.mul, ComplexRatInterval.width,
      ComplexRatInterval.maxAbs, RatInterval.sub, RatInterval.add,
      RatInterval.neg, RatInterval.mul, RatInterval.point, RatInterval.width,
      RatInterval.maxAbs, hK0, hL0, hKw, hLw] using h
  induction n with
  | zero => simp [RatInterval.npow, RatInterval.point, RatInterval.width]
  | succ n ih =>
      rw [RatInterval.npow]
      have hstep := hmulWidth (I.npow n) I
      have hpowAM : A ^ n ≤ (max 1 A) ^ n :=
        pow_le_pow_left₀ hA (le_max_right 1 A) n
      have hpowMB : (max 1 A) ^ n ≤ (2 * max 1 A) ^ n :=
        pow_le_pow_left₀ hM0 hMleB n
      have hpowAB : A ^ n ≤ (2 * max 1 A) ^ n := hpowAM.trans hpowMB
      have hAw : A ^ n * I.width ≤ (2 * max 1 A) ^ n * w := by
        exact mul_le_mul hpowAB hw (RatInterval.width_nonneg I) (pow_nonneg hB0 n)
      have hfirst : (I.npow n).maxAbs * I.width ≤
          (2 * max 1 A) ^ n * w :=
        (mul_le_mul (hnpowMax n) le_rfl (RatInterval.width_nonneg I)
          (pow_nonneg hA n)).trans hAw
      have hsecond : I.maxAbs * (I.npow n).width ≤
          max 1 A * ((n : ℚ) * (2 * max 1 A) ^ n * w) := by
        exact (mul_le_mul hmax ih (RatInterval.width_nonneg (I.npow n)) hA)
          |>.trans (mul_le_mul_of_nonneg_right (le_max_right 1 A)
            (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (pow_nonneg hB0 n)) hw0))
      calc
        ((I.npow n).mul I).width ≤
            2 * ((I.npow n).maxAbs * I.width + I.maxAbs * (I.npow n).width) := hstep
        _ ≤ 2 * ((2 * max 1 A) ^ n * w +
            max 1 A * ((n : ℚ) * (2 * max 1 A) ^ n * w)) :=
          mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) (by norm_num)
        _ ≤ ((n + 1 : ℕ) : ℚ) * (2 * max 1 A) ^ (n + 1) * w := by
          have hPw : 0 ≤ (2 * max 1 A) ^ n * w :=
            mul_nonneg (pow_nonneg hB0 n) hw0
          have htwo : (0 : ℚ) ≤ 2 := by norm_num
          have htwo_le : (2 : ℚ) ≤ 2 * max 1 A := by
            calc
              (2 : ℚ) = 2 * 1 := by ring
              _ ≤ 2 * max 1 A :=
                mul_le_mul_of_nonneg_left (le_max_left 1 A) htwo
          have hscale : 2 * ((2 * max 1 A) ^ n * w) ≤
              (2 * max 1 A) * ((2 * max 1 A) ^ n * w) := by
            exact mul_le_mul_of_nonneg_right htwo_le hPw
          rw [pow_succ]
          push_cast
          calc
            2 * ((2 * max 1 A) ^ n * w +
                max 1 A * ((n : ℚ) * (2 * max 1 A) ^ n * w)) =
              2 * ((2 * max 1 A) ^ n * w) +
                (n : ℚ) * (2 * max 1 A) * ((2 * max 1 A) ^ n * w) := by ring
            _ ≤ (2 * max 1 A) * ((2 * max 1 A) ^ n * w) +
                (n : ℚ) * (2 * max 1 A) * ((2 * max 1 A) ^ n * w) :=
              add_le_add hscale le_rfl
            _ = ((n : ℚ) + 1) * ((2 * max 1 A) ^ n * (2 * max 1 A)) * w := by
              ring

/-- Existing rectangle multiplication exposes both operand widths and
magnitudes; this alias records the propagation step used by the spectral
finite-sum proof. -/
lemma complexRectangle_mul_width_propagation (I J : ComplexRatInterval) :
    (I.mul J).width ≤
      2 * (I.maxAbs * J.width + J.maxAbs * I.width) :=
  ComplexRatInterval.mul_width I J

private lemma ratInterval_mul_width_propagation (I J : RatInterval) :
    (I.mul J).width ≤
      2 * (I.maxAbs * J.width + J.maxAbs * I.width) := by
  let IR : ComplexRatInterval := ⟨I, RatInterval.point 0⟩
  let JR : ComplexRatInterval := ⟨J, RatInterval.point 0⟩
  have h := ComplexRatInterval.mul_width IR JR
  have hI0 : 0 ≤ I.maxAbs := (abs_nonneg I.lo).trans (le_max_left _ _)
  have hJ0 : 0 ≤ J.maxAbs := (abs_nonneg J.lo).trans (le_max_left _ _)
  have hIw : 0 ≤ I.hi - I.lo := sub_nonneg.mpr I.lo_le_hi
  have hJw : 0 ≤ J.hi - J.lo := sub_nonneg.mpr J.lo_le_hi
  simpa [IR, JR, ComplexRatInterval.mul, ComplexRatInterval.width,
    ComplexRatInterval.maxAbs, RatInterval.sub, RatInterval.add,
    RatInterval.neg, RatInterval.mul, RatInterval.point, RatInterval.width,
    RatInterval.maxAbs, hI0, hJ0, hIw, hJw] using h

/-- A recursive rectangle sum contains the sum of pairwise enclosed values. -/
lemma intervalSum_contains_sum (xs : List ComplexRatInterval) (zs : List ℂ)
    (h : List.Forall₂ (fun I z ↦ I.Contains z) xs zs) :
    (intervalSum xs).Contains zs.sum := by
  have aux : ∀ {xs : List ComplexRatInterval} {zs : List ℂ},
      List.Forall₂ (fun I z ↦ I.Contains z) xs zs →
      ∀ {A : ComplexRatInterval} {a : ℂ}, A.Contains a →
        (xs.foldl ComplexRatInterval.add A).Contains (a + zs.sum) := by
    intro xs zs h
    induction h with
    | nil =>
        intro A a ha
        simpa using ha
    | cons hIz hrest ih =>
        intro A a ha
        simpa [add_assoc] using
          ih (ComplexRatInterval.add_sound ha hIz)
  have hzero : ComplexRatInterval.zero.Contains (0 : ℂ) := by
    simpa [ComplexRatInterval.zero, ComplexRatInterval.point] using
      ComplexRatInterval.point_sound 0 0
  simpa [intervalSum] using aux h hzero

/-- Recursive rectangle addition accumulates no more than the sum of the
individual coordinate widths. -/
lemma intervalSum_width_propagation (xs : List ComplexRatInterval) :
    (intervalSum xs).width ≤ (xs.map ComplexRatInterval.width).sum := by
  have hadd (I J : ComplexRatInterval) :
      (I.add J).width ≤ I.width + J.width := by
    rw [ComplexRatInterval.width_add]
    apply max_le
    · exact add_le_add (le_max_left _ _) (le_max_left _ _)
    · exact add_le_add (le_max_right _ _) (le_max_right _ _)
  have aux : ∀ (ys : List ComplexRatInterval) (A : ComplexRatInterval),
      (ys.foldl ComplexRatInterval.add A).width ≤
        A.width + (ys.map ComplexRatInterval.width).sum := by
    intro ys
    induction ys with
    | nil => intro A; simp
    | cons I ys ih =>
        intro A
        calc
          ((I :: ys).foldl ComplexRatInterval.add A).width =
              (ys.foldl ComplexRatInterval.add (A.add I)).width := rfl
          _ ≤ (A.add I).width + (ys.map ComplexRatInterval.width).sum := ih _
          _ ≤ A.width + I.width + (ys.map ComplexRatInterval.width).sum := by
            gcongr
            exact hadd A I
          _ = A.width + ((I :: ys).map ComplexRatInterval.width).sum := by simp [add_assoc]
  simpa [intervalSum, ComplexRatInterval.zero, ComplexRatInterval.width,
    RatInterval.point, RatInterval.width] using aux xs ComplexRatInterval.zero

/-- Rational post-scaling propagates width linearly in the scalar magnitude. -/
lemma complexRectangle_smulRat_width_propagation (q : ℚ)
    (I : ComplexRatInterval) :
    (I.smulRat q).width ≤ |q| * I.width := by
  have pointMulWidth_nonneg (r : ℚ) (hr : 0 ≤ r) (K : RatInterval) :
      ((RatInterval.point r).mul K).width = r * K.width := by
    have h := mul_le_mul_of_nonneg_left K.lo_le_hi hr
    simp [RatInterval.mul, RatInterval.point, RatInterval.width, h]
    ring
  have pointMulWidth_nonpos (r : ℚ) (hr : r ≤ 0) (K : RatInterval) :
      ((RatInterval.point r).mul K).width = (-r) * K.width := by
    have h := mul_le_mul_of_nonpos_left K.lo_le_hi hr
    simp [RatInterval.mul, RatInterval.point, RatInterval.width, h]
    ring
  rcases le_total 0 q with hq | hq
  · have hre := pointMulWidth_nonneg q hq I.re
    have him := pointMulWidth_nonneg q hq I.im
    change max ((RatInterval.point q).mul I.re).width
        ((RatInterval.point q).mul I.im).width ≤ |q| * max I.re.width I.im.width
    rw [hre, him, abs_of_nonneg hq, ← mul_max_of_nonneg I.re.width I.im.width hq]
  · have hre := pointMulWidth_nonpos q hq I.re
    have him := pointMulWidth_nonpos q hq I.im
    have hnq : 0 ≤ -q := neg_nonneg.mpr hq
    change max ((RatInterval.point q).mul I.re).width
        ((RatInterval.point q).mul I.im).width ≤ |q| * max I.re.width I.im.width
    rw [hre, him, abs_of_nonpos hq, ← mul_max_of_nonneg I.re.width I.im.width hnq]

/-- Explicit rational exponential envelope on the fixed disk. -/
def rationalExpEnvelope (rho zBound : ℚ) : ℚ :=
  3 ^ Int.toNat ⌈max 0 (rho * zBound)⌉

/-- A rational upper bound for the size of unit i's treatment residual: the largest
endpoint magnitude of the residual's certified enclosure, refined until its width is at
most one. -/
def residualUpper (input : RepresentedSpectralInput p) (i : Fin p.n) : ℚ :=
  ((representedResidual input i).approx
    ((representedResidual input i).modulus errorOne)).maxAbs

/-- A rational upper bound for the size of unit i's outcome: the largest endpoint magnitude
of the outcome's certified enclosure, refined until its width is at most one. -/
def outcomeUpper (input : RepresentedSpectralInput p) (i : Fin p.n) : ℚ :=
  ((input.observations i).yName.approx
    ((input.observations i).yName.modulus errorOne)).maxAbs

/-- [The rational residual magnitude bound of any unit is never negative](goal). -/
lemma residualUpper_nonneg (input : RepresentedSpectralInput p) (i : Fin p.n) :
    0 ≤ residualUpper input i :=
  (abs_nonneg _).trans (le_max_left _ _)

/-- [The rational outcome magnitude bound of any unit is never negative](goal). -/
lemma outcomeUpper_nonneg (input : RepresentedSpectralInput p) (i : Fin p.n) :
    0 ≤ outcomeUpper input i :=
  (abs_nonneg _).trans (le_max_left _ _)

/-- A rational magnitude envelope for the empirical residual transform and its derivatives
of a given order over the disk of radius rho: the sum across sample units of the unit's
residual magnitude bound raised to the derivative order, multiplied by a rational
exponential envelope for that residual on the disk. -/
def empiricalFDerivativeBound (input : RepresentedSpectralInput p)
    (rho : ℚ) (derivative : ℕ) : ℚ :=
  ∑ i, residualUpper input i ^ derivative * rationalExpEnvelope rho (residualUpper input i)

/-- The same magnitude envelope for the outcome-weighted empirical transform: each unit
contributes its outcome magnitude bound times its residual magnitude bound raised to the
derivative order, times the rational exponential envelope on the disk of radius rho. -/
def empiricalGDerivativeBound (input : RepresentedSpectralInput p)
    (rho : ℚ) (derivative : ℕ) : ℚ :=
  ∑ i, outcomeUpper input i * residualUpper input i ^ derivative *
    rationalExpEnvelope rho (residualUpper input i)

/-- A conservative propagation envelope for canonical F intervals.  The
`max 1` power is deliberately the same one exposed by the public interval
power-width theorem; the extra radius and derivative factors pay for all
finite-operation amplification without pretending that it is a semantic
derivative bound. -/
def empiricalFWidthBound (input : RepresentedSpectralInput p)
    (rho : ℚ) (derivative : ℕ) : ℚ :=
  ∑ i, ((rho + 1) * (derivative + 1) *
    (2 * max 1 (residualUpper input i)) ^ (derivative + 1) *
    rationalExpEnvelope rho (residualUpper input i)) ^ 8

/-- The analogous canonical G propagation envelope, including the outcome
magnitude needed by coefficient multiplication. -/
def empiricalGWidthBound (input : RepresentedSpectralInput p)
    (rho : ℚ) (derivative : ℕ) : ℚ :=
  ∑ i, (max 1 (outcomeUpper input i) * (rho + 1) * (derivative + 1) *
    (2 * max 1 (residualUpper input i)) ^ (derivative + 1) *
    rationalExpEnvelope rho (residualUpper input i)) ^ 8

/-- [The magnitude envelope for the empirical residual transform is never
negative](goal). -/
lemma empiricalFDerivativeBound_nonneg (input : RepresentedSpectralInput p)
    (rho : ℚ) (derivative : ℕ) :
    0 ≤ empiricalFDerivativeBound input rho derivative := by
  unfold empiricalFDerivativeBound rationalExpEnvelope
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (pow_nonneg (residualUpper_nonneg input i) _) (by positivity)

/-- [The magnitude envelope for the outcome-weighted empirical transform is never
negative](goal). -/
lemma empiricalGDerivativeBound_nonneg (input : RepresentedSpectralInput p)
    (rho : ℚ) (derivative : ℕ) :
    0 ≤ empiricalGDerivativeBound input rho derivative := by
  unfold empiricalGDerivativeBound rationalExpEnvelope
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg
    (mul_nonneg (outcomeUpper_nonneg input i)
      (pow_nonneg (residualUpper_nonneg input i) _)) (by positivity)

/-- For [a nonnegative disk radius](hyp:hrho), [the interval-propagation envelope of the
empirical residual transform is never negative](goal). -/
lemma empiricalFWidthBound_nonneg (input : RepresentedSpectralInput p)
    (rho : ℚ) (derivative : ℕ) (hrho : 0 ≤ rho) :
    0 ≤ empiricalFWidthBound input rho derivative := by
  unfold empiricalFWidthBound rationalExpEnvelope
  positivity

/-- For [a nonnegative disk radius](hyp:hrho), [the interval-propagation envelope of the
outcome-weighted empirical transform is never negative](goal). -/
lemma empiricalGWidthBound_nonneg (input : RepresentedSpectralInput p)
    (rho : ℚ) (derivative : ℕ) (hrho : 0 ≤ rho) :
    0 ≤ empiricalGWidthBound input rho derivative := by
  unfold empiricalGWidthBound rationalExpEnvelope
  positivity

/-- The full-box rational exponential envelope dominates a centered envelope
whose real upper endpoint has already been bounded by `rho * S`. -/
private lemma centeredExpEnvelope_le_rationalExpEnvelope
    (J : ComplexRatInterval) (rho S : ℚ) (hhi : J.re.hi ≤ rho * S) :
    BoundedCertifiedComplex.centeredExpEnvelope J ≤ rationalExpEnvelope rho S := by
  unfold BoundedCertifiedComplex.centeredExpEnvelope rationalExpEnvelope
  exact pow_le_pow_right₀ (by norm_num)
    (Int.toNat_le_toNat (Int.ceil_mono (max_le_max le_rfl hhi)))

/-! ## Canonical-name quantitative bounds

These bounds are specific to the floor-dyadic observation records used by the
ordinary statistic.  They are not fields of the generic represented input and
do not assert a width theorem for arbitrary names.
-/

/-- [The canonical certified enclosure of a real number, taken at a given refinement level,
has width at most two raised to the negative of one more than that level](goal). -/
lemma canonicalObservationName_approx_width (x : ℝ) (fuel : ℕ) :
    ((canonicalObservationName x).approx fuel).width ≤
      1 / (2 : ℚ) ^ (fuel + 1) := by
  unfold canonicalObservationName canonicalDyadicInterval RatInterval.width
  simp

/-- For canonically named data, [the certified enclosure of any unit's treatment residual
at a given refinement level has width at most twice two raised to the negative of one more
than that level](goal) — twice the single-name bound, because the residual is a
difference of two canonical names. -/
lemma canonicalRepresentedInput_residual_approx_width
    (p : Parameters) (pStar : CertifiedBankInputs p) (cStar : CertifiedRangeInput p)
    (gcode : ℕ → Xspace → ℝ) (data : Fin p.n → Obs Xspace)
    (i : Fin p.n) (fuel : ℕ) :
    ((representedResidual
      (canonicalRepresentedInput p pStar cStar gcode data) i).approx fuel).width ≤
      2 / (2 : ℚ) ^ (fuel + 1) := by
  have ht := canonicalObservationName_approx_width
    (treatment (data i)) fuel
  have hg := canonicalObservationName_approx_width
    (min (max (gcode p.n (covariate (data i))) (-p.Cg)) p.Cg) fuel
  rw [representedResidual, CertifiedReal.sub, CertifiedReal.add,
    RatInterval.width_add, CertifiedReal.neg, RatInterval.width_neg]
  change ((canonicalObservationName (treatment (data i))).approx fuel).width +
      ((canonicalObservationName
        (min (max (gcode p.n (covariate (data i))) (-p.Cg)) p.Cg)).approx fuel).width ≤
      2 / (2 : ℚ) ^ (fuel + 1)
  calc
    _ ≤ 1 / (2 : ℚ) ^ (fuel + 1) + 1 / (2 : ℚ) ^ (fuel + 1) :=
      add_le_add ht hg
    _ = 2 / (2 : ℚ) ^ (fuel + 1) := by ring

/-- For canonically named data, [the certified enclosure of any unit's outcome at a given
refinement level has width at most two raised to the negative of one more than that
level](goal). -/
lemma canonicalRepresentedInput_outcome_approx_width
    (p : Parameters) (pStar : CertifiedBankInputs p) (cStar : CertifiedRangeInput p)
    (gcode : ℕ → Xspace → ℝ) (data : Fin p.n → Obs Xspace)
    (i : Fin p.n) (fuel : ℕ) :
    (((canonicalRepresentedInput p pStar cStar gcode data).observations i).yName.approx
      fuel).width ≤ 1 / (2 : ℚ) ^ (fuel + 1) := by
  simpa [canonicalRepresentedInput] using
    canonicalObservationName_approx_width (outcome (data i)) fuel

/-- Once [the refinement level is at least the one at which the residual's enclosure has
width one](hyp:hfuel), [the largest endpoint magnitude of that enclosure is at most the
unit's rational residual magnitude bound](goal). Refining further can only shrink the
enclosure. -/
lemma canonicalResidual_maxAbs_at_fuel
    (p : Parameters) (pStar : CertifiedBankInputs p) (cStar : CertifiedRangeInput p)
    (gcode : ℕ → Xspace → ℝ) (data : Fin p.n → Obs Xspace)
    (i : Fin p.n) (fuel : ℕ)
    (hfuel : (representedResidual
      (canonicalRepresentedInput p pStar cStar gcode data) i).modulus errorOne ≤ fuel) :
    ((representedResidual
      (canonicalRepresentedInput p pStar cStar gcode data) i).approx fuel).maxAbs ≤
      residualUpper (canonicalRepresentedInput p pStar cStar gcode data) i := by
  unfold residualUpper
  exact ComplexRatInterval.rat_maxAbs_mono
    (CertifiedReal.approx_mono _ hfuel)

/-- Once [the refinement level is at least the one at which the outcome's enclosure has
width one](hyp:hfuel), [the largest endpoint magnitude of that enclosure is at most the
unit's rational outcome magnitude bound](goal). -/
lemma canonicalOutcome_maxAbs_at_fuel
    (p : Parameters) (pStar : CertifiedBankInputs p) (cStar : CertifiedRangeInput p)
    (gcode : ℕ → Xspace → ℝ) (data : Fin p.n → Obs Xspace)
    (i : Fin p.n) (fuel : ℕ)
    (hfuel : ((canonicalRepresentedInput p pStar cStar gcode data).observations i).yName.modulus
      errorOne ≤ fuel) :
    (((canonicalRepresentedInput p pStar cStar gcode data).observations i).yName.approx
      fuel).maxAbs ≤
      outcomeUpper (canonicalRepresentedInput p pStar cStar gcode data) i := by
  unfold outcomeUpper
  exact ComplexRatInterval.rat_maxAbs_mono
    (CertifiedReal.approx_mono _ hfuel)

/-- Recursive whole-rectangle tightening of a fuel-indexed raw evaluator. -/
def tightenAcrossFuel (raw : ℕ → ComplexRatInterval) : ℕ → ComplexRatInterval
  | 0 => raw 0
  | fuel + 1 => (tightenAcrossFuel raw fuel).tighten (raw (fuel + 1))

/-- Sound raw enclosures remain sound after recursive tightening; consecutive
fuel outputs are nested, and every tightened output lies inside the raw output
at the same fuel. -/
lemma tightenAcrossFuel_spec (raw : ℕ → ComplexRatInterval) (z : ℂ)
    (hraw : ∀ fuel, (raw fuel).Contains z) (fuel : ℕ) :
    (tightenAcrossFuel raw fuel).Contains z ∧
      (tightenAcrossFuel raw (fuel + 1)).Subinterval (tightenAcrossFuel raw fuel) ∧
      (tightenAcrossFuel raw fuel).Subinterval (raw fuel) := by
  induction fuel with
  | zero =>
      have h0 := hraw 0
      exact ⟨h0,
        (ComplexRatInterval.tighten_sound_left h0 (hraw 1)).2,
        ⟨RatInterval.subinterval_refl _, RatInterval.subinterval_refl _⟩⟩
  | succ fuel ih =>
      have hcurrent : (tightenAcrossFuel raw (fuel + 1)).Contains z := by
        rw [tightenAcrossFuel]
        exact (ComplexRatInterval.tighten_sound_left ih.1 (hraw (fuel + 1))).1
      have hnext := hraw (fuel + 2)
      exact ⟨hcurrent, by
        rw [show fuel + 1 + 1 = fuel + 2 by omega, tightenAcrossFuel]
        exact (ComplexRatInterval.tighten_sound_left hcurrent hnext).2,
        by
          rw [tightenAcrossFuel]
          exact ⟨
            Transcendental.tighten_subinterval_right ih.1.1 (hraw (fuel + 1)).1,
            Transcendental.tighten_subinterval_right ih.1.2 (hraw (fuel + 1)).2⟩⟩

/-- The raw finite-sum interval program for the empirical F derivative. -/
def spectralDenominatorRawEval (input : RepresentedSpectralInput p)
    (I : Finset (Fin p.n)) (derivative : ℕ)
    (z : ComplexRatInterval) (fuel : ℕ) : ComplexRatInterval :=
  let terms := I.toList.map fun i ↦
    let residual := (representedResidual input i).approx fuel
    let argument := z.mul (realRect residual)
    let exponential := BoundedCertifiedComplex.centeredComplexExp argument fuel
    (realRect (residual.npow derivative)).mul exponential
  (intervalSum terms).smulRat ((max I.card 1 : ℚ)⁻¹)

/-- The raw finite-sum interval program for the empirical G derivative. -/
def spectralNumeratorRawEval (input : RepresentedSpectralInput p)
    (I : Finset (Fin p.n)) (derivative : ℕ)
    (z : ComplexRatInterval) (fuel : ℕ) : ComplexRatInterval :=
  let terms := I.toList.map fun i ↦
    let residual := (representedResidual input i).approx fuel
    let weight := (input.observations i).yName.approx fuel
    let argument := z.mul (realRect residual)
    let exponential := BoundedCertifiedComplex.centeredComplexExp argument fuel
    (realRect (weight.mul (residual.npow derivative))).mul exponential
  (intervalSum terms).smulRat ((max I.card 1 : ℚ)⁻¹)

/-- Cross-fuel-nested empirical F evaluation obtained by tightening the whole
raw finite-sum rectangle at every successive fuel. -/
def spectralDenominatorEval (input : RepresentedSpectralInput p)
    (I : Finset (Fin p.n)) (derivative : ℕ)
    (z : ComplexRatInterval) : ℕ → ComplexRatInterval :=
  tightenAcrossFuel (spectralDenominatorRawEval input I derivative z)

/-- Cross-fuel-nested empirical G evaluation obtained by tightening the whole
raw finite-sum rectangle at every successive fuel. -/
def spectralNumeratorEval (input : RepresentedSpectralInput p)
    (I : Finset (Fin p.n)) (derivative : ℕ)
    (z : ComplexRatInterval) : ℕ → ComplexRatInterval :=
  tightenAcrossFuel (spectralNumeratorRawEval input I derivative z)

/-- The finite-sum certified empirical F map on the fixed disk. -/
def spectralDenominatorMap (input : RepresentedSpectralInput p)
    (B : ContourBankData) (I : Finset (Fin p.n)) (derivative : ℕ) :
    BoundedComplexMap (spectralDiskBox B) where
  value := fun z ↦ ((max I.card 1 : ℝ)⁻¹ : ℂ) * ∑ i ∈ I,
    (((representedResidual input i).value ^ derivative : ℝ) : ℂ) *
      Complex.exp (z * (representedResidual input i).value)
  eval := spectralDenominatorEval input I derivative
  operationCount := 12 * I.card + 8 + derivative
  magnitudeEnvelope := empiricalFDerivativeBound input
    (spectralFullBoxRadius B) derivative
  derivativeEnvelope := 128 * empiricalFWidthBound input
    (spectralFullBoxRadius B) derivative
  precision := fun e ↦ spectralEmpiricalMapFuel e (12 * I.card + 8 + derivative)
    ((128 * max 1 (empiricalFWidthBound input
      (spectralFullBoxRadius B) derivative)) ^ 2)

/-- The finite-sum certified empirical G map on the same fixed disk. -/
def spectralNumeratorMap (input : RepresentedSpectralInput p)
    (B : ContourBankData) (I : Finset (Fin p.n)) (derivative : ℕ) :
    BoundedComplexMap (spectralDiskBox B) where
  value := fun z ↦ ((max I.card 1 : ℝ)⁻¹ : ℂ) * ∑ i ∈ I,
    (((input.observations i).yName.value *
      (representedResidual input i).value ^ derivative : ℝ) : ℂ) *
      Complex.exp (z * (representedResidual input i).value)
  eval := spectralNumeratorEval input I derivative
  operationCount := 14 * I.card + 8 + derivative
  magnitudeEnvelope := empiricalGDerivativeBound input
    (spectralFullBoxRadius B) derivative
  derivativeEnvelope := 256 * empiricalGWidthBound input
    (spectralFullBoxRadius B) derivative
  precision := fun e ↦ spectralEmpiricalMapFuel e (14 * I.card + 8 + derivative)
    ((256 * max 1 (empiricalGWidthBound input
      (spectralFullBoxRadius B) derivative)) ^ 2)

/-- If [one complex rectangle is contained in another](hyp:h), then [its coordinate
diameter is no larger](goal). -/
lemma complexRectangle_width_mono {I J : ComplexRatInterval}
    (h : I.Subinterval J) : I.width ≤ J.width :=
  max_le_max (RatInterval.width_mono h.1) (RatInterval.width_mono h.2)

/-- A rectangle's coordinate diameter is at most twice its endpoint-magnitude
bound. -/
private lemma complexRectangle_width_le_two_maxAbs (I : ComplexRatInterval) :
    I.width ≤ 2 * I.maxAbs := by
  rw [ComplexRatInterval.width]
  apply max_le
  · rw [RatInterval.width]
    have hlo : -I.re.lo ≤ |I.re.lo| := neg_le_abs _
    have hhi : I.re.hi ≤ |I.re.hi| := le_abs_self _
    have hlo' : |I.re.lo| ≤ I.maxAbs :=
      (le_max_left _ _).trans (le_max_left _ _)
    have hhi' : |I.re.hi| ≤ I.maxAbs :=
      (le_max_right _ _).trans (le_max_left _ _)
    linarith
  · rw [RatInterval.width]
    have hlo : -I.im.lo ≤ |I.im.lo| := neg_le_abs _
    have hhi : I.im.hi ≤ |I.im.hi| := le_abs_self _
    have hlo' : |I.im.lo| ≤ I.maxAbs :=
      (le_max_left _ _).trans (le_max_right _ _)
    have hhi' : |I.im.hi| ≤ I.maxAbs :=
      (le_max_right _ _).trans (le_max_right _ _)
    linarith

private lemma ratInterval_npow_maxAbs_le (I : RatInterval) (n : ℕ) :
    (I.npow n).maxAbs ≤ I.maxAbs ^ n := by
  induction n with
  | zero => simp [RatInterval.npow, RatInterval.point, RatInterval.maxAbs]
  | succ n ih =>
      rw [RatInterval.npow, pow_succ]
      exact (RatInterval.maxAbs_mul _ _).trans
        (mul_le_mul ih le_rfl
          ((abs_nonneg I.lo).trans (le_max_left _ _))
          (pow_nonneg ((abs_nonneg I.lo).trans (le_max_left _ _)) n))

@[simp] private lemma realRect_maxAbs (R : RatInterval) :
    (realRect R).maxAbs = R.maxAbs := by
  simp [realRect, ComplexRatInterval.maxAbs, RatInterval.point,
    RatInterval.maxAbs, (abs_nonneg R.lo).trans (le_max_left _ _)]

/-- Coarse algebraic estimate used after all semantic quantities have been
absorbed into one per-observation propagation factor. -/
private lemma spectralDenominatorTerm_width_coarse
    (K : ComplexRatInterval) (R : RatInterval) (d : ℕ)
    (X : ComplexRatInterval) (b η : ℚ)
    (hb : 1 ≤ b) (hη : 0 ≤ η)
    (hRmax : R.maxAbs ^ d ≤ b)
    (hPwidth : (R.npow d).width ≤ 2 * b ^ 2 * η)
    (hXwidth : X.width ≤ 9 * b ^ 2 * η + 4 * b ^ 2 * K.width)
    (hXmax : X.maxAbs ≤ 14 * b ^ 3) :
    ((realRect (R.npow d)).mul X).width ≤
      128 * b ^ 8 * (K.width + η) := by
  have hb0 : 0 ≤ b := zero_le_one.trans hb
  have hkw0 : 0 ≤ K.width :=
    (RatInterval.width_nonneg K.re).trans (le_max_left _ _)
  have hPmax : (realRect (R.npow d)).maxAbs ≤ b := by
    simpa [realRect, ComplexRatInterval.maxAbs, RatInterval.point,
      RatInterval.maxAbs] using (ratInterval_npow_maxAbs_le R d).trans hRmax
  have hmul := complexRectangle_mul_width_propagation (realRect (R.npow d)) X
  rw [realRect_width] at hmul
  calc
    ((realRect (R.npow d)).mul X).width ≤
        2 * ((realRect (R.npow d)).maxAbs * X.width +
          X.maxAbs * (R.npow d).width) := hmul
    _ ≤ 2 * (b * (9 * b ^ 2 * η + 4 * b ^ 2 * K.width) +
          (14 * b ^ 3) * (2 * b ^ 2 * η)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply add_le_add
      · exact mul_le_mul hPmax hXwidth
          ((RatInterval.width_nonneg X.re).trans (le_max_left _ _)) hb0
      · exact mul_le_mul hXmax hPwidth
          (RatInterval.width_nonneg (R.npow d)) (by positivity)
    _ ≤ 128 * b ^ 8 * (K.width + η) := by
      have h38 : b ^ 3 ≤ b ^ 8 := pow_le_pow_right₀ hb (by norm_num)
      have h58 : b ^ 5 ≤ b ^ 8 := pow_le_pow_right₀ hb (by norm_num)
      have hkw38 := mul_le_mul_of_nonneg_right h38 hkw0
      have hη38 := mul_le_mul_of_nonneg_right h38 hη
      have hη58 := mul_le_mul_of_nonneg_right h58 hη
      calc
        2 * (b * (9 * b ^ 2 * η + 4 * b ^ 2 * K.width) +
            14 * b ^ 3 * (2 * b ^ 2 * η)) =
            8 * (b ^ 3 * K.width) + 18 * (b ^ 3 * η) +
              56 * (b ^ 5 * η) := by ring
        _ ≤ 8 * (b ^ 8 * K.width) + 18 * (b ^ 8 * η) +
              56 * (b ^ 8 * η) := by gcongr
        _ ≤ 128 * b ^ 8 * (K.width + η) := by
          nlinarith [mul_nonneg (pow_nonneg hb0 8) hkw0,
            mul_nonneg (pow_nonneg hb0 8) hη]

private lemma spectralExpWidth_arith (E b η w : ℚ)
    (hEb : E ≤ b) (hb : 1 ≤ b) (hη : 0 ≤ η) (hw : 0 ≤ w) :
    2 * E * (4 * b * η + 2 * b * w) + η ≤
      9 * b ^ 2 * η + 4 * b ^ 2 * w := by
  have hb0 : 0 ≤ b := zero_le_one.trans hb
  have hEbη := mul_le_mul_of_nonneg_right hEb (mul_nonneg hb0 hη)
  have hEbw := mul_le_mul_of_nonneg_right hEb (mul_nonneg hb0 hw)
  have h1b2 : (1 : ℚ) ≤ b ^ 2 := by nlinarith
  have hηb2 := mul_le_mul_of_nonneg_right h1b2 hη
  nlinarith

private lemma spectralNumeratorTerm_width_coarse
    (K : ComplexRatInterval) (C : RatInterval) (X : ComplexRatInterval)
    (b η : ℚ) (hb : 1 ≤ b) (hη : 0 ≤ η)
    (hCmax : C.maxAbs ≤ b ^ 2)
    (hCwidth : C.width ≤ 6 * b ^ 3 * η)
    (hXwidth : X.width ≤ 9 * b ^ 2 * η + 4 * b ^ 2 * K.width)
    (hXmax : X.maxAbs ≤ 14 * b ^ 3) :
    ((realRect C).mul X).width ≤ 256 * b ^ 8 * (K.width + η) := by
  have hb0 : 0 ≤ b := zero_le_one.trans hb
  have hw0 : 0 ≤ K.width :=
    (RatInterval.width_nonneg K.re).trans (le_max_left _ _)
  have h := complexRectangle_mul_width_propagation (realRect C) X
  rw [realRect_width, realRect_maxAbs] at h
  calc
    ((realRect C).mul X).width ≤
        2 * (C.maxAbs * X.width + X.maxAbs * C.width) := h
    _ ≤ 2 * (b ^ 2 * (9 * b ^ 2 * η + 4 * b ^ 2 * K.width) +
          14 * b ^ 3 * (6 * b ^ 3 * η)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply add_le_add
      · exact mul_le_mul hCmax hXwidth
          ((RatInterval.width_nonneg X.re).trans (le_max_left _ _))
          (pow_nonneg hb0 2)
      · exact mul_le_mul hXmax hCwidth (RatInterval.width_nonneg C) (by positivity)
    _ ≤ 256 * b ^ 8 * (K.width + η) := by
      have h48 : b ^ 4 ≤ b ^ 8 := pow_le_pow_right₀ hb (by norm_num)
      have h68 : b ^ 6 ≤ b ^ 8 := pow_le_pow_right₀ hb (by norm_num)
      have h48w := mul_le_mul_of_nonneg_right h48 hw0
      have h48η := mul_le_mul_of_nonneg_right h48 hη
      have h68η := mul_le_mul_of_nonneg_right h68 hη
      nlinarith [mul_nonneg (pow_nonneg hb0 8) hw0,
        mul_nonneg (pow_nonneg hb0 8) hη]

/-- A centered exponential rectangle is no larger in endpoint magnitude than
its semantic exponential envelope plus its own coordinate width. -/
private lemma centeredComplexExp_maxAbs_le (J : ComplexRatInterval) (fuel : ℕ) :
    (BoundedCertifiedComplex.centeredComplexExp J fuel).maxAbs ≤
      BoundedCertifiedComplex.centeredExpEnvelope J +
        (BoundedCertifiedComplex.centeredComplexExp J fuel).width := by
  let z : ℂ := (J.re.lo : ℝ) + (J.im.lo : ℝ) * Complex.I
  have hz : J.Contains z := by
    constructor
    · simpa [z] using (show J.re.Contains (J.re.lo : ℝ) by
        exact ⟨le_rfl, by exact_mod_cast J.re.lo_le_hi⟩)
    · simpa [z] using (show J.im.Contains (J.im.lo : ℝ) by
        exact ⟨le_rfl, by exact_mod_cast J.im.lo_le_hi⟩)
  have hcontains := BoundedCertifiedComplex.centeredComplexExp_sound J fuel hz
  have henv := BoundedCertifiedComplex.centeredExpEnvelope_sound J hz.1
  have hre : |(Complex.exp z).re| ≤
      (BoundedCertifiedComplex.centeredExpEnvelope J : ℝ) := by
    rw [Complex.exp_re, abs_mul, Real.abs_exp]
    calc
      Real.exp z.re * |Real.cos z.im| ≤ Real.exp z.re * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (Real.exp_pos _).le
      _ ≤ _ := by simpa using henv
  have him : |(Complex.exp z).im| ≤
      (BoundedCertifiedComplex.centeredExpEnvelope J : ℝ) := by
    rw [Complex.exp_im, abs_mul, Real.abs_exp]
    calc
      Real.exp z.re * |Real.sin z.im| ≤ Real.exp z.re * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (Real.exp_pos _).le
      _ ≤ _ := by simpa using henv
  exact ComplexRatInterval.maxAbs_le_of_contains_width hcontains
    (max_le hre him) le_rfl

set_option maxHeartbeats 400000 in
-- The cast and reciprocal normalization in the closed-fuel calculation is arithmetic-heavy.
/-- One dyadic cell at the closed empirical-map fuel fits inside the requested
tolerance divided by the explicit integer amplification used by that fuel. -/
private lemma spectralEmpiricalMapFuel_dyadic_le
    (e : PosRat) (operations : ℕ) (L : ℚ) :
    let H : ℕ := 64 * (operations + 1) * (L.num.natAbs + 2) ^ 2
    1 / (2 : ℚ) ^ (spectralEmpiricalMapFuel e operations L + 1) ≤ e.1 / H := by
  let H : ℕ := 64 * (operations + 1) * (L.num.natAbs + 2) ^ 2
  let F : ℕ := spectralEmpiricalMapFuel e operations L
  have hH : 0 < H := by
    dsimp [H]
    positivity
  have hF : F = H * (e.1.den + 1) := by
    simp [F, H, spectralEmpiricalMapFuel, mul_assoc, mul_comm, mul_left_comm]
  have hF0 : 0 < F := by rw [hF]; positivity
  have hHQ : (0 : ℚ) < H := by exact_mod_cast hH
  have hpowNat : F ≤ 2 ^ (F + 1) := by
    exact (Nat.le_of_lt (Nat.lt_pow_self (by norm_num : 1 < 2))).trans
      (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ F))
  have hpowQ : (F : ℚ) ≤ (2 : ℚ) ^ (F + 1) := by exact_mod_cast hpowNat
  have hinv : 1 / (2 : ℚ) ^ (F + 1) ≤ 1 / F := by
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hpowQ
  have hden : 1 / (e.1.den + 1 : ℚ) ≤ e.1 := by
    calc
      1 / (e.1.den + 1 : ℚ) ≤ 1 / (e.1.den : ℚ) := by
        exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
          (by exact_mod_cast Nat.le_succ e.1.den)
      _ ≤ e.1 := Transcendental.inv_den_le_of_pos e.1 e.2
  calc
    1 / (2 : ℚ) ^ (spectralEmpiricalMapFuel e operations L + 1) =
        1 / (2 : ℚ) ^ (F + 1) := rfl
    _ ≤ 1 / F := hinv
    _ = (1 / (e.1.den + 1 : ℚ)) / H := by
      rw [hF]
      push_cast
      field_simp
    _ ≤ e.1 / H := div_le_div_of_nonneg_right hden hHQ.le

set_option maxHeartbeats 400000 in
-- Rational normalization through the closed fuel is arithmetic-heavy.
/-- The reciprocal of the closed fuel obeys the same allocated error budget. -/
private lemma spectralEmpiricalMapFuel_inv_le
    (e : PosRat) (operations : ℕ) (L : ℚ) :
    let H : ℕ := 64 * (operations + 1) * (L.num.natAbs + 2) ^ 2
    1 / (spectralEmpiricalMapFuel e operations L : ℚ) ≤ e.1 / H := by
  let H : ℕ := 64 * (operations + 1) * (L.num.natAbs + 2) ^ 2
  let F : ℕ := spectralEmpiricalMapFuel e operations L
  have hH : 0 < H := by dsimp [H]; positivity
  have hF : F = H * (e.1.den + 1) := by
    simp [F, H, spectralEmpiricalMapFuel, mul_comm, mul_left_comm]
  have hHQ : (0 : ℚ) < H := by exact_mod_cast hH
  have hden : 1 / (e.1.den + 1 : ℚ) ≤ e.1 := by
    calc
      1 / (e.1.den + 1 : ℚ) ≤ 1 / (e.1.den : ℚ) := by
        exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
          (by exact_mod_cast Nat.le_succ e.1.den)
      _ ≤ e.1 := Transcendental.inv_den_le_of_pos e.1 e.2
  change 1 / (F : ℚ) ≤ e.1 / H
  rw [hF]
  push_cast
  rw [one_div, mul_inv, div_eq_mul_inv]
  simpa [mul_comm, mul_left_comm] using
    (mul_le_mul_of_nonneg_right hden (inv_nonneg.mpr hHQ.le))

/-- Canonical centered raw F evaluation is semantically sound on every
subrectangle of the full spectral box. -/
lemma spectralDenominatorRawEval_sound_of_canonical
    (input : RepresentedSpectralInput p) (B : ContourBankData)
    (I : Finset (Fin p.n)) (derivative : ℕ)
    (hcanonical : ∃ (pStar : CertifiedBankInputs p) (cStar : CertifiedRangeInput p)
      (gcode : ℕ → Xspace → ℝ) (data : Fin p.n → Obs Xspace),
      input = canonicalRepresentedInput p pStar cStar gcode data)
    {K : ComplexRatInterval} {z : ℂ} (hK : K.Subinterval (spectralDiskBox B))
    (hz : K.Contains z) (fuel : ℕ) :
    (spectralDenominatorRawEval input I derivative K fuel).Contains
      ((spectralDenominatorMap input B I derivative).value z) := by
  rcases hcanonical with ⟨pStar, cStar, gcode, data, rfl⟩
  let input := canonicalRepresentedInput p pStar cStar gcode data
  let termInterval : Fin p.n → ComplexRatInterval := fun i ↦
    let residual := (representedResidual input i).approx fuel
    let argument := K.mul (realRect residual)
    (realRect (residual.npow derivative)).mul
      (BoundedCertifiedComplex.centeredComplexExp argument fuel)
  let termValue : Fin p.n → ℂ := fun i ↦
    (((representedResidual input i).value ^ derivative : ℝ) : ℂ) *
      Complex.exp (z * (representedResidual input i).value)
  have hterm : ∀ i, (termInterval i).Contains (termValue i) := by
    intro i
    have hr := (representedResidual input i).contains fuel
    have hargument : (K.mul
        (realRect ((representedResidual input i).approx fuel))).Contains
          (z * (representedResidual input i).value) :=
      ComplexRatInterval.mul_sound hz (realRect_sound hr)
    have hexponential := BoundedCertifiedComplex.centeredComplexExp_sound
      (K.mul (realRect ((representedResidual input i).approx fuel))) fuel hargument
    have hpower := realRect_sound (RatInterval.npow_sound hr derivative)
    exact ComplexRatInterval.mul_sound hpower hexponential
  have hterms : List.Forall₂ (fun J v ↦ J.Contains v)
      (I.toList.map termInterval) (I.toList.map termValue) := by
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
    exact fun i _ ↦ hterm i
  have hsum := intervalSum_contains_sum _ _ hterms
  have hscaled := ComplexRatInterval.smulRat_sound ((max I.card 1 : ℚ)⁻¹) hsum
  have hscaleCast :
      (((max (I.card : ℚ) 1)⁻¹ : ℚ) : ℂ) =
        (((max (I.card : ℝ) 1)⁻¹ : ℝ) : ℂ) := by
    by_cases hcard : I.card = 0
    · simp [hcard]
    · have hc : 1 ≤ I.card := Nat.one_le_iff_ne_zero.mpr hcard
      rw [max_eq_left (by exact_mod_cast hc : (1 : ℚ) ≤ I.card),
        max_eq_left (by exact_mod_cast hc : (1 : ℝ) ≤ I.card)]
      norm_num
  have heval : spectralDenominatorRawEval input I derivative K fuel =
      (intervalSum (I.toList.map termInterval)).smulRat ((max I.card 1 : ℚ)⁻¹) := rfl
  have hvalue : (spectralDenominatorMap input B I derivative).value z =
      ((((max I.card 1 : ℚ)⁻¹ : ℚ) : ℂ) * (I.toList.map termValue).sum) := by
    rw [hscaleCast]
    simp [spectralDenominatorMap, termValue, Finset.sum_toList]
  rw [heval, hvalue]
  exact hscaled

/-- Canonical centered raw G evaluation is semantically sound on every
subrectangle of the full spectral box. -/
lemma spectralNumeratorRawEval_sound_of_canonical
    (input : RepresentedSpectralInput p) (B : ContourBankData)
    (I : Finset (Fin p.n)) (derivative : ℕ)
    (hcanonical : ∃ (pStar : CertifiedBankInputs p) (cStar : CertifiedRangeInput p)
      (gcode : ℕ → Xspace → ℝ) (data : Fin p.n → Obs Xspace),
      input = canonicalRepresentedInput p pStar cStar gcode data)
    {K : ComplexRatInterval} {z : ℂ} (hK : K.Subinterval (spectralDiskBox B))
    (hz : K.Contains z) (fuel : ℕ) :
    (spectralNumeratorRawEval input I derivative K fuel).Contains
      ((spectralNumeratorMap input B I derivative).value z) := by
  rcases hcanonical with ⟨pStar, cStar, gcode, data, rfl⟩
  let input := canonicalRepresentedInput p pStar cStar gcode data
  let termInterval : Fin p.n → ComplexRatInterval := fun i ↦
    let residual := (representedResidual input i).approx fuel
    let weight := (input.observations i).yName.approx fuel
    let argument := K.mul (realRect residual)
    (realRect (weight.mul (residual.npow derivative))).mul
      (BoundedCertifiedComplex.centeredComplexExp argument fuel)
  let termValue : Fin p.n → ℂ := fun i ↦
    (((input.observations i).yName.value *
      (representedResidual input i).value ^ derivative : ℝ) : ℂ) *
      Complex.exp (z * (representedResidual input i).value)
  have hterm : ∀ i, (termInterval i).Contains (termValue i) := by
    intro i
    have hr := (representedResidual input i).contains fuel
    have hy := (input.observations i).yName.contains fuel
    have hargument : (K.mul
        (realRect ((representedResidual input i).approx fuel))).Contains
          (z * (representedResidual input i).value) :=
      ComplexRatInterval.mul_sound hz (realRect_sound hr)
    have hexponential := BoundedCertifiedComplex.centeredComplexExp_sound
      (K.mul (realRect ((representedResidual input i).approx fuel))) fuel hargument
    have hcoefficient := realRect_sound
      (RatInterval.mul_sound hy (RatInterval.npow_sound hr derivative))
    exact ComplexRatInterval.mul_sound hcoefficient hexponential
  have hterms : List.Forall₂ (fun J v ↦ J.Contains v)
      (I.toList.map termInterval) (I.toList.map termValue) := by
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
    exact fun i _ ↦ hterm i
  have hsum := intervalSum_contains_sum _ _ hterms
  have hscaled := ComplexRatInterval.smulRat_sound ((max I.card 1 : ℚ)⁻¹) hsum
  have hscaleCast :
      (((max (I.card : ℚ) 1)⁻¹ : ℚ) : ℂ) =
        (((max (I.card : ℝ) 1)⁻¹ : ℝ) : ℂ) := by
    by_cases hcard : I.card = 0
    · simp [hcard]
    · have hc : 1 ≤ I.card := Nat.one_le_iff_ne_zero.mpr hcard
      rw [max_eq_left (by exact_mod_cast hc : (1 : ℚ) ≤ I.card),
        max_eq_left (by exact_mod_cast hc : (1 : ℝ) ≤ I.card)]
      norm_num
  have heval : spectralNumeratorRawEval input I derivative K fuel =
      (intervalSum (I.toList.map termInterval)).smulRat ((max I.card 1 : ℚ)⁻¹) := rfl
  have hvalue : (spectralNumeratorMap input B I derivative).value z =
      ((((max I.card 1 : ℚ)⁻¹ : ℚ) : ℂ) * (I.toList.map termValue).sum) := by
    rw [hscaleCast]
    simp [spectralNumeratorMap, termValue, Finset.sum_toList]
  rw [heval, hvalue]
  exact hscaled

set_option maxHeartbeats 4000000 in
-- The explicit finite-sum width and closed-fuel arithmetic require extra heartbeats.
/-- The scheduled raw F rectangle pays for the derivative envelope times the
certified input width in addition to the centered algorithmic remainder. -/
lemma spectralDenominatorRawEval_width_of_canonical
    (input : RepresentedSpectralInput p) (B : ContourBankData)
    (I : Finset (Fin p.n)) (derivative : ℕ)
    (hcanonical : ∃ (pStar : CertifiedBankInputs p) (cStar : CertifiedRangeInput p)
      (gcode : ℕ → Xspace → ℝ) (data : Fin p.n → Obs Xspace),
      input = canonicalRepresentedInput p pStar cStar gcode data)
    (K : ComplexRatInterval) (hK : K.Subinterval (spectralDiskBox B)) (e : PosRat) :
    (spectralDenominatorRawEval input I derivative K
      ((spectralDenominatorMap input B I derivative).precision e)).width ≤
      (spectralDenominatorMap input B I derivative).derivativeEnvelope * K.width + e.1 := by
  rcases hcanonical with ⟨pStar, cStar, gcode, data, rfl⟩
  let input := canonicalRepresentedInput p pStar cStar gcode data
  let ρ := spectralFullBoxRadius B
  let Q := empiricalFWidthBound input ρ derivative
  let L := (128 * max 1 Q) ^ 2
  let operations := 12 * I.card + 8 + derivative
  let F := spectralEmpiricalMapFuel e operations L
  let η : ℚ := 1 / F
  have hρ0 : 0 ≤ ρ := spectralFullBoxRadius_nonneg B
  have hQ0 : 0 ≤ Q := empiricalFWidthBound_nonneg input ρ derivative hρ0
  have hF0 : 0 < F := by
    dsimp [F, operations, L]
    unfold spectralEmpiricalMapFuel
    positivity
  have hη0 : 0 ≤ η := by dsimp [η]; positivity
  have hη1 : η ≤ 1 := by
    dsimp [η]
    rw [div_le_one (by exact_mod_cast hF0 : (0 : ℚ) < F)]
    exact_mod_cast hF0
  have hKbox : K.maxAbs ≤ (spectralDiskBox B).maxAbs :=
    max_le_max (ComplexRatInterval.rat_maxAbs_mono hK.1)
      (ComplexRatInterval.rat_maxAbs_mono hK.2)
  have hbox0 : 0 ≤ (spectralDiskBox B).maxAbs :=
    (abs_nonneg _).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hKmax : K.maxAbs ≤ ρ := hKbox.trans (by
    dsimp [ρ, spectralFullBoxRadius]
    nlinarith)
  have hKwidth : K.width ≤ ρ :=
    (complexRectangle_width_le_two_maxAbs K).trans (by
      dsimp [ρ, spectralFullBoxRadius]
      exact mul_le_mul_of_nonneg_left hKbox (by norm_num))
  let term : Fin p.n → ComplexRatInterval := fun i ↦
    let R := (representedResidual input i).approx F
    let J := K.mul (realRect R)
    (realRect (R.npow derivative)).mul
      (BoundedCertifiedComplex.centeredComplexExp J F)
  have hterm : ∀ i ∈ I, (term i).width ≤
      128 * (((ρ + 1) * (derivative + 1) *
        (2 * max 1 (residualUpper input i)) ^ (derivative + 1) *
        rationalExpEnvelope ρ (residualUpper input i)) ^ 8) *
        (K.width + η) := by
    intro i hi
    let S := residualUpper input i
    let A := 2 * max 1 S
    let E := rationalExpEnvelope ρ S
    let b := (ρ + 1) * (derivative + 1) * A ^ (derivative + 1) * E
    let R := (representedResidual input i).approx F
    let J := K.mul (realRect R)
    let X := BoundedCertifiedComplex.centeredComplexExp J F
    have hS0 : 0 ≤ S := residualUpper_nonneg input i
    have hA2 : 2 ≤ A := by dsimp [A]; nlinarith [le_max_left (1 : ℚ) S]
    have hE1 : 1 ≤ E := by
      dsimp [E, rationalExpEnvelope]
      exact one_le_pow₀ (by norm_num)
    have hb1 : 1 ≤ b := by
      dsimp [b]
      have hρ1 : (1 : ℚ) ≤ ρ + 1 := by linarith
      have hd1 : (1 : ℚ) ≤ derivative + 1 := by norm_num
      have hAp : 1 ≤ A ^ (derivative + 1) :=
        one_le_pow₀ (by linarith : (1 : ℚ) ≤ A)
      calc
        1 = 1 * 1 * 1 * 1 := by norm_num
        _ ≤ (ρ + 1) * (derivative + 1) * A ^ (derivative + 1) * E := by
          gcongr
    have hρb : ρ ≤ b := by
      have hd1 : (1 : ℚ) ≤ derivative + 1 := by norm_num
      have hAp : 1 ≤ A ^ (derivative + 1) := one_le_pow₀ (by linarith)
      have ht : 1 ≤ (derivative + 1 : ℚ) * A ^ (derivative + 1) * E := by
        calc 1 = 1 * 1 * 1 := by norm_num
          _ ≤ (derivative + 1 : ℚ) * A ^ (derivative + 1) * E := by gcongr
      calc ρ ≤ ρ + 1 := by linarith
        _ = (ρ + 1) * 1 := by ring
        _ ≤ b := by
          simpa [b, mul_assoc] using
            (mul_le_mul_of_nonneg_left ht (by linarith : (0 : ℚ) ≤ ρ + 1))
    have hF64 : 64 ≤ F := by
      dsimp [F]
      unfold spectralEmpiricalMapFuel
      have ho : 1 ≤ operations + 1 := by omega
      have he : 1 ≤ e.1.den + 1 := by omega
      have hl : 1 ≤ (L.num.natAbs + 2) ^ 2 :=
        Nat.one_le_pow 2 (L.num.natAbs + 2) (by omega)
      calc
        64 = 64 * 1 * 1 * 1 := by norm_num
        _ ≤ 64 * (operations + 1) * (e.1.den + 1) *
            (L.num.natAbs + 2) ^ 2 := by gcongr
    have hmod : (representedResidual input i).modulus errorOne ≤ F := by
      dsimp [input]
      simp [representedResidual, CertifiedReal.sub, CertifiedReal.add,
        CertifiedReal.neg, canonicalRepresentedInput, canonicalObservationName,
        errorOne]
      omega
    have hRmax : R.maxAbs ≤ S := canonicalResidual_maxAbs_at_fuel
      p pStar cStar gcode data i F hmod
    have hRmax0 : 0 ≤ R.maxAbs := (abs_nonneg _).trans (le_max_left _ _)
    have hdyadic : 1 / (2 : ℚ) ^ (F + 1) ≤ η := by
      dsimp [η]
      have hp : (F : ℚ) ≤ (2 : ℚ) ^ (F + 1) := by
        exact_mod_cast (Nat.le_of_lt (Nat.lt_pow_self (by norm_num : 1 < 2))).trans
          (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ F))
      exact div_le_div_of_nonneg_left (by norm_num)
        (by exact_mod_cast hF0) hp
    have hRw : R.width ≤ 2 * η :=
      (canonicalRepresentedInput_residual_approx_width
        p pStar cStar gcode data i F).trans
        (by simpa [div_eq_mul_inv] using
          (mul_le_mul_of_nonneg_left hdyadic (by norm_num : (0 : ℚ) ≤ 2)))
    have hSd : R.maxAbs ^ derivative ≤ b := by
      have hSA : R.maxAbs ≤ A := hRmax.trans
        ((le_max_right (1 : ℚ) S).trans (by nlinarith [hA2]))
      have hp : R.maxAbs ^ derivative ≤ A ^ (derivative + 1) :=
          (pow_le_pow_left₀ hRmax0 hSA derivative).trans
          (pow_le_pow_right₀ (by linarith : (1 : ℚ) ≤ A) (Nat.le_succ _))
      have hρ1 : (1 : ℚ) ≤ ρ + 1 := by linarith
      have hd1 : (1 : ℚ) ≤ derivative + 1 := by norm_num
      exact hp.trans (by
        calc
          A ^ (derivative + 1) = 1 * 1 * A ^ (derivative + 1) * 1 := by ring
          _ ≤ b := by dsimp [b]; gcongr)
    have hPw : (R.npow derivative).width ≤ 2 * b ^ 2 * η := by
      have hp := ratInterval_npow_width_propagation R derivative S (2 * η)
        hS0 hRw hRmax
      have hcoef : (derivative : ℚ) * A ^ derivative ≤ b := by
        have hd : (derivative : ℚ) ≤ derivative + 1 := by norm_num
        have hpow : A ^ derivative ≤ A ^ (derivative + 1) :=
          pow_le_pow_right₀ (by linarith : (1 : ℚ) ≤ A) (Nat.le_succ _)
        calc
          (derivative : ℚ) * A ^ derivative ≤
              (derivative + 1) * A ^ (derivative + 1) :=
            mul_le_mul hd hpow (pow_nonneg (by positivity) _) (by positivity)
          _ ≤ b := by
            have hρ1 : (1 : ℚ) ≤ ρ + 1 := by linarith
            calc
              (derivative + 1) * A ^ (derivative + 1) =
                  1 * (derivative + 1) * A ^ (derivative + 1) * 1 := by ring
              _ ≤ b := by dsimp [b]; gcongr
      calc
        (R.npow derivative).width ≤
            (derivative : ℚ) * A ^ derivative * (2 * η) := hp
        _ ≤ b * (2 * η) :=
          mul_le_mul_of_nonneg_right hcoef (mul_nonneg (by norm_num) hη0)
        _ ≤ 2 * b ^ 2 * η := by
          have hbb : b ≤ b ^ 2 := by nlinarith [hb1]
          nlinarith [mul_le_mul_of_nonneg_right hbb hη0]
    have hJw : J.width ≤ 4 * b * η + 2 * b * K.width := by
      dsimp [J]
      have hKb : K.maxAbs ≤ b := hKmax.trans (by
        exact hρb)
      have hRb : R.maxAbs ≤ b := hRmax.trans (by
        calc S ≤ A := by dsimp [A]; nlinarith [le_max_right (1 : ℚ) S]
          _ ≤ A ^ (derivative + 1) := by
            simpa using (pow_le_pow_right₀ (by linarith : (1 : ℚ) ≤ A)
              (show 1 ≤ derivative + 1 by omega))
          _ ≤ b := by
            have hρ1 : (1 : ℚ) ≤ ρ + 1 := by linarith
            have hd1 : (1 : ℚ) ≤ derivative + 1 := by norm_num
            calc A ^ (derivative + 1) = 1 * 1 * A ^ (derivative + 1) * 1 := by ring
              _ ≤ b := by dsimp [b]; gcongr)
      calc
        (K.mul (realRect R)).width ≤
            2 * (K.maxAbs * R.width + R.maxAbs * K.width) := by
          simpa using complexRectangle_mul_width_propagation K (realRect R)
        _ ≤ 2 * (b * (2 * η) + b * K.width) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply add_le_add
          · exact mul_le_mul hKb hRw (RatInterval.width_nonneg R)
              (by positivity)
          · exact mul_le_mul_of_nonneg_right hRb
              ((RatInterval.width_nonneg K.re).trans (le_max_left _ _))
        _ = _ := by ring
    have hJmax : J.maxAbs ≤ ρ * S := by
      dsimp [J]
      calc
        (K.mul (realRect R)).maxAbs ≤ 2 * K.maxAbs * R.maxAbs := by
          simpa using ComplexRatInterval.mul_maxAbs K (realRect R)
        _ ≤ 2 * (spectralDiskBox B).maxAbs * S := by
          exact mul_le_mul (mul_le_mul_of_nonneg_left hKbox (by norm_num)) hRmax
            hRmax0 (mul_nonneg (by norm_num) hbox0)
        _ = ρ * S := by simp [ρ, spectralFullBoxRadius]
    have hJhi : J.re.hi ≤ ρ * S := by
      exact (le_abs_self J.re.hi).trans
        ((le_max_right _ _).trans ((le_max_left _ _).trans hJmax))
    have hEnv : BoundedCertifiedComplex.centeredExpEnvelope J ≤ E :=
      centeredExpEnvelope_le_rationalExpEnvelope J ρ S hJhi
    let εF : PosRat := ⟨1 / (F : ℚ), by positivity⟩
    have hstage : Transcendental.complexExpPrecision
        (BoundedCertifiedComplex.centeredExpCenterName J) εF = F := by
      simp [Transcendental.complexExpPrecision, εF, hF0.ne']
    have hXw0 := BoundedCertifiedComplex.centeredComplexExp_width_at_precision J εF
    rw [hstage] at hXw0
    have hXw : X.width ≤ 9 * b ^ 2 * η + 4 * b ^ 2 * K.width := by
      dsimp [X, εF] at hXw0
      have hEb : E ≤ b := by
        have hρ1 : (1 : ℚ) ≤ ρ + 1 := by linarith
        have hd1 : (1 : ℚ) ≤ derivative + 1 := by norm_num
        have hAp : 1 ≤ A ^ (derivative + 1) :=
          one_le_pow₀ (by linarith : (1 : ℚ) ≤ A)
        calc E = 1 * 1 * 1 * E := by ring
          _ ≤ b := by dsimp [b]; gcongr
      calc
        _ ≤ 2 * E * (4 * b * η + 2 * b * K.width) + η := by
          exact hXw0.trans (add_le_add
            (mul_le_mul (mul_le_mul_of_nonneg_left hEnv (by norm_num)) hJw
              ((RatInterval.width_nonneg J.re).trans (le_max_left _ _))
              (mul_nonneg (by norm_num) (by linarith [hE1]))) le_rfl)
        _ ≤ _ := by
          exact spectralExpWidth_arith E b η K.width hEb hb1 hη0
            ((RatInterval.width_nonneg K.re).trans (le_max_left _ _))
    have hXmax : X.maxAbs ≤ 14 * b ^ 3 := by
      have hEb : E ≤ b := by
        have hρ1 : (1 : ℚ) ≤ ρ + 1 := by linarith
        have hd1 : (1 : ℚ) ≤ derivative + 1 := by norm_num
        have hAp : 1 ≤ A ^ (derivative + 1) :=
          one_le_pow₀ (by linarith : (1 : ℚ) ≤ A)
        calc E = 1 * 1 * 1 * E := by ring
          _ ≤ b := by dsimp [b]; gcongr
      calc
        X.maxAbs ≤ BoundedCertifiedComplex.centeredExpEnvelope J + X.width :=
          centeredComplexExp_maxAbs_le J F
        _ ≤ E + (9 * b ^ 2 * η + 4 * b ^ 2 * K.width) :=
          add_le_add hEnv hXw
        _ ≤ 14 * b ^ 3 := by
          have hKwb := hKwidth.trans hρb
          have hb2 : b ^ 2 ≤ b ^ 3 := pow_le_pow_right₀ hb1 (by norm_num)
          have hbη := mul_le_mul_of_nonneg_left hη1 (pow_nonneg (by positivity) 2)
          have hbK := mul_le_mul_of_nonneg_left hKwb (pow_nonneg (by positivity) 2)
          nlinarith
    simpa [term, R, J, X, b, A, E, S] using
      spectralDenominatorTerm_width_coarse K R derivative X b η
        hb1 hη0 hSd hPw hXw hXmax
  have hlist : ((I.toList.map term).map ComplexRatInterval.width).sum ≤
      128 * Q * (K.width + η) := by
    calc
      ((I.toList.map term).map ComplexRatInterval.width).sum =
          ∑ i ∈ I, (term i).width := by simp
      _ ≤ ∑ i ∈ I, 128 * (((ρ + 1) * (derivative + 1) *
          (2 * max 1 (residualUpper input i)) ^ (derivative + 1) *
          rationalExpEnvelope ρ (residualUpper input i)) ^ 8) *
          (K.width + η) := Finset.sum_le_sum fun i hi ↦ hterm i hi
      _ ≤ ∑ i, 128 * (((ρ + 1) * (derivative + 1) *
          (2 * max 1 (residualUpper input i)) ^ (derivative + 1) *
          rationalExpEnvelope ρ (residualUpper input i)) ^ 8) *
          (K.width + η) := by
        apply Finset.sum_le_univ_sum_of_nonneg
        intro i
        exact mul_nonneg
          (mul_nonneg (by norm_num)
            ((show Even 8 by exact ⟨4, by norm_num⟩).pow_nonneg _))
          (add_nonneg
            ((RatInterval.width_nonneg K.re).trans (le_max_left _ _)) hη0)
      _ = 128 * Q * (K.width + η) := by
        dsimp [Q, empiricalFWidthBound]
        rw [Finset.mul_sum, Finset.sum_mul]
  have hraw : (spectralDenominatorRawEval input I derivative K F).width ≤
      128 * Q * (K.width + η) := by
    have hs := intervalSum_width_propagation (I.toList.map term)
    have hscale := complexRectangle_smulRat_width_propagation
      ((max I.card 1 : ℚ)⁻¹) (intervalSum (I.toList.map term))
    have hinv : |((max I.card 1 : ℚ)⁻¹)| ≤ 1 := by
      rw [abs_of_nonneg (inv_nonneg.mpr (by positivity))]
      apply (inv_le_one₀ (by positivity)).2
      exact_mod_cast Nat.le_max_right I.card 1
    calc
      (spectralDenominatorRawEval input I derivative K F).width =
          ((intervalSum (I.toList.map term)).smulRat
            ((max I.card 1 : ℚ)⁻¹)).width := by rfl
      _ ≤ |((max I.card 1 : ℚ)⁻¹)| *
          (intervalSum (I.toList.map term)).width := hscale
      _ ≤ 1 * (intervalSum (I.toList.map term)).width :=
        mul_le_mul_of_nonneg_right hinv
          ((RatInterval.width_nonneg (intervalSum (I.toList.map term)).re).trans
            (le_max_left _ _))
      _ ≤ ((I.toList.map term).map ComplexRatInterval.width).sum := by simpa using hs
      _ ≤ 128 * Q * (K.width + η) := hlist
  let H : ℕ := 64 * (operations + 1) * (L.num.natAbs + 2) ^ 2
  have hηalloc : η ≤ e.1 / H := by
    have h := spectralEmpiricalMapFuel_inv_le e operations L
    dsimp only at h
    exact h
  have hL0 : 0 ≤ L := by dsimp [L]; positivity
  have hLnum : L ≤ (L.num.natAbs : ℚ) := by
    have hn : 0 ≤ L.num := Rat.num_nonneg.mpr hL0
    calc
      L = (L.num : ℚ) / (L.den : ℕ) := (Rat.num_div_den L).symm
      _ ≤ (L.num : ℚ) := div_le_self (by exact_mod_cast hn)
        (by exact_mod_cast Rat.den_pos L)
      _ = (L.num.natAbs : ℚ) := by
        have hnat : (L.num.natAbs : ℤ) = L.num := by
          rw [Int.natCast_natAbs, abs_of_nonneg hn]
        calc
          (L.num : ℚ) = ((L.num : ℤ) : ℚ) := rfl
          _ = (((L.num.natAbs : ℕ) : ℤ) : ℚ) := by rw [hnat]
          _ = (L.num.natAbs : ℚ) := by norm_num
  have hQL : 128 * Q ≤ L := by
    let t : ℚ := 128 * max 1 Q
    have ht1 : 1 ≤ t := by dsimp [t]; nlinarith [le_max_left (1 : ℚ) Q]
    have hQt : 128 * Q ≤ t := by
      dsimp [t]
      exact mul_le_mul_of_nonneg_left (le_max_right 1 Q) (by norm_num)
    exact hQt.trans (by dsimp [L, t]; nlinarith [ht1])
  have hnumH : (L.num.natAbs : ℚ) ≤ H := by
    have hop : (1 : ℚ) ≤ operations + 1 := by norm_num
    have hn : (0 : ℚ) ≤ L.num.natAbs := by positivity
    dsimp [H]
    push_cast
    nlinarith [sq_nonneg ((L.num.natAbs : ℚ) + 1)]
  have hQH : 128 * Q ≤ (H : ℚ) := hQL.trans (hLnum.trans hnumH)
  have herror : 128 * Q * η ≤ e.1 := by
    have hH0 : (0 : ℚ) < H := by dsimp [H]; positivity
    have hQ0' : 0 ≤ 128 * Q := mul_nonneg (by norm_num) hQ0
    calc
      128 * Q * η ≤ 128 * Q * (e.1 / H) :=
        mul_le_mul_of_nonneg_left hηalloc hQ0'
      _ ≤ (H : ℚ) * (e.1 / H) :=
        mul_le_mul_of_nonneg_right hQH (div_nonneg e.2.le hH0.le)
      _ = e.1 := by field_simp
  have hfinal := hraw.trans (by
      calc
        128 * Q * (K.width + η) = 128 * Q * K.width + 128 * Q * η := by ring
        _ ≤ 128 * Q * K.width + e.1 :=
          by simpa [add_comm] using
            (add_le_add_left herror (128 * Q * K.width)))
  have hFuel : (spectralDenominatorMap input B I derivative).precision e = F := rfl
  have hDerivative : (spectralDenominatorMap input B I derivative).derivativeEnvelope =
      128 * Q := rfl
  rw [hFuel, hDerivative]
  exact hfinal

set_option maxHeartbeats 4000000 in
-- The outcome-weighted finite-sum width and closed-fuel arithmetic require extra heartbeats.
/-- The scheduled raw G rectangle has the analogous full-box effective-width
bound, including the canonical outcome-name refinement. -/
lemma spectralNumeratorRawEval_width_of_canonical
    (input : RepresentedSpectralInput p) (B : ContourBankData)
    (I : Finset (Fin p.n)) (derivative : ℕ)
    (hcanonical : ∃ (pStar : CertifiedBankInputs p) (cStar : CertifiedRangeInput p)
      (gcode : ℕ → Xspace → ℝ) (data : Fin p.n → Obs Xspace),
      input = canonicalRepresentedInput p pStar cStar gcode data)
    (K : ComplexRatInterval) (hK : K.Subinterval (spectralDiskBox B)) (e : PosRat) :
    (spectralNumeratorRawEval input I derivative K
      ((spectralNumeratorMap input B I derivative).precision e)).width ≤
      (spectralNumeratorMap input B I derivative).derivativeEnvelope * K.width + e.1 := by
  rcases hcanonical with ⟨pStar, cStar, gcode, data, rfl⟩
  let input := canonicalRepresentedInput p pStar cStar gcode data
  let ρ := spectralFullBoxRadius B
  let Q := empiricalGWidthBound input ρ derivative
  let L := (256 * max 1 Q) ^ 2
  let operations := 14 * I.card + 8 + derivative
  let F := spectralEmpiricalMapFuel e operations L
  let η : ℚ := 1 / F
  have hρ0 : 0 ≤ ρ := spectralFullBoxRadius_nonneg B
  have hQ0 : 0 ≤ Q := empiricalGWidthBound_nonneg input ρ derivative hρ0
  have hF0 : 0 < F := by
    dsimp [F, operations, L]
    unfold spectralEmpiricalMapFuel
    positivity
  have hη0 : 0 ≤ η := by dsimp [η]; positivity
  have hη1 : η ≤ 1 := by
    dsimp [η]
    rw [div_le_one (by exact_mod_cast hF0 : (0 : ℚ) < F)]
    exact_mod_cast hF0
  have hKbox : K.maxAbs ≤ (spectralDiskBox B).maxAbs :=
    max_le_max (ComplexRatInterval.rat_maxAbs_mono hK.1)
      (ComplexRatInterval.rat_maxAbs_mono hK.2)
  have hbox0 : 0 ≤ (spectralDiskBox B).maxAbs :=
    (abs_nonneg _).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hKmax : K.maxAbs ≤ ρ := hKbox.trans (by
    dsimp [ρ, spectralFullBoxRadius]
    nlinarith)
  have hKwidth : K.width ≤ ρ :=
    (complexRectangle_width_le_two_maxAbs K).trans (by
      dsimp [ρ, spectralFullBoxRadius]
      exact mul_le_mul_of_nonneg_left hKbox (by norm_num))
  let term : Fin p.n → ComplexRatInterval := fun i ↦
    let R := (representedResidual input i).approx F
    let W := (input.observations i).yName.approx F
    let J := K.mul (realRect R)
    (realRect (W.mul (R.npow derivative))).mul
      (BoundedCertifiedComplex.centeredComplexExp J F)
  have hterm : ∀ i ∈ I, (term i).width ≤
      256 * ((max 1 (outcomeUpper input i) * (ρ + 1) * (derivative + 1) *
        (2 * max 1 (residualUpper input i)) ^ (derivative + 1) *
        rationalExpEnvelope ρ (residualUpper input i)) ^ 8) *
        (K.width + η) := by
    intro i hi
    let S := residualUpper input i
    let Y := outcomeUpper input i
    let A := 2 * max 1 S
    let E := rationalExpEnvelope ρ S
    let b := max 1 Y * (ρ + 1) * (derivative + 1) * A ^ (derivative + 1) * E
    let R := (representedResidual input i).approx F
    let W := (input.observations i).yName.approx F
    let J := K.mul (realRect R)
    let X := BoundedCertifiedComplex.centeredComplexExp J F
    have hS0 : 0 ≤ S := residualUpper_nonneg input i
    have hY0 : 0 ≤ Y := outcomeUpper_nonneg input i
    have hY1 : 1 ≤ max 1 Y := le_max_left _ _
    have hYρ1 : 1 ≤ max 1 Y * (ρ + 1) := by
      nlinarith [mul_le_mul hY1 (show (1 : ℚ) ≤ ρ + 1 by linarith)
        (by norm_num : (0 : ℚ) ≤ 1) (by positivity : (0 : ℚ) ≤ max 1 Y)]
    have hA2 : 2 ≤ A := by dsimp [A]; nlinarith [le_max_left (1 : ℚ) S]
    have hE1 : 1 ≤ E := by
      dsimp [E, rationalExpEnvelope]
      exact one_le_pow₀ (by norm_num)
    have hb1 : 1 ≤ b := by
      dsimp [b]
      have hρ1 : (1 : ℚ) ≤ ρ + 1 := by linarith
      have hd1 : (1 : ℚ) ≤ derivative + 1 := by norm_num
      have hAp : 1 ≤ A ^ (derivative + 1) :=
        one_le_pow₀ (by linarith : (1 : ℚ) ≤ A)
      calc
        1 = 1 * 1 * 1 * 1 * 1 := by norm_num
        _ ≤ max 1 Y * (ρ + 1) * (derivative + 1) * A ^ (derivative + 1) * E := by
          gcongr
    have hρb : ρ ≤ b := by
      have hd1 : (1 : ℚ) ≤ derivative + 1 := by norm_num
      have hAp : 1 ≤ A ^ (derivative + 1) := one_le_pow₀ (by linarith)
      have ht : 1 ≤ max 1 Y * (derivative + 1 : ℚ) * A ^ (derivative + 1) * E := by
        calc 1 = 1 * 1 * 1 * 1 := by norm_num
          _ ≤ max 1 Y * (derivative + 1 : ℚ) * A ^ (derivative + 1) * E := by gcongr
      calc ρ ≤ ρ + 1 := by linarith
        _ = (ρ + 1) * 1 := by ring
        _ ≤ b := by
          dsimp [b]
          nlinarith [mul_le_mul_of_nonneg_left ht
            (by linarith : (0 : ℚ) ≤ ρ + 1)]
    have hmod : (representedResidual input i).modulus errorOne ≤ F := by
      have hF64 : 64 ≤ F := by
        dsimp [F]
        unfold spectralEmpiricalMapFuel
        have ho : 1 ≤ operations + 1 := by omega
        have he : 1 ≤ e.1.den + 1 := by omega
        have hl : 1 ≤ (L.num.natAbs + 2) ^ 2 :=
          Nat.one_le_pow 2 (L.num.natAbs + 2) (by omega)
        calc
          64 = 64 * 1 * 1 * 1 := by norm_num
          _ ≤ 64 * (operations + 1) * (e.1.den + 1) *
              (L.num.natAbs + 2) ^ 2 := by gcongr
      dsimp [input]
      simp [representedResidual, CertifiedReal.sub, CertifiedReal.add,
        CertifiedReal.neg, canonicalRepresentedInput, canonicalObservationName,
        errorOne]
      omega
    have hmodY : (input.observations i).yName.modulus errorOne ≤ F := by
      have hF64 : 64 ≤ F := by
        dsimp [F]
        unfold spectralEmpiricalMapFuel
        have ho : 1 ≤ operations + 1 := by omega
        have he : 1 ≤ e.1.den + 1 := by omega
        have hl : 1 ≤ (L.num.natAbs + 2) ^ 2 :=
          Nat.one_le_pow 2 (L.num.natAbs + 2) (by omega)
        calc
          64 = 64 * 1 * 1 * 1 := by norm_num
          _ ≤ 64 * (operations + 1) * (e.1.den + 1) *
              (L.num.natAbs + 2) ^ 2 := by gcongr
      dsimp [input]
      simp [canonicalRepresentedInput, canonicalObservationName, errorOne]
      omega
    have hRmax : R.maxAbs ≤ S := canonicalResidual_maxAbs_at_fuel
      p pStar cStar gcode data i F hmod
    have hWmax : W.maxAbs ≤ Y := canonicalOutcome_maxAbs_at_fuel
      p pStar cStar gcode data i F hmodY
    have hRmax0 : 0 ≤ R.maxAbs := (abs_nonneg _).trans (le_max_left _ _)
    have hdyadic : 1 / (2 : ℚ) ^ (F + 1) ≤ η := by
      dsimp [η]
      have hp : (F : ℚ) ≤ (2 : ℚ) ^ (F + 1) := by
        exact_mod_cast (Nat.le_of_lt (Nat.lt_pow_self (by norm_num : 1 < 2))).trans
          (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ F))
      exact div_le_div_of_nonneg_left (by norm_num)
        (by exact_mod_cast hF0) hp
    have hRw : R.width ≤ 2 * η :=
      (canonicalRepresentedInput_residual_approx_width
        p pStar cStar gcode data i F).trans
        (by simpa [div_eq_mul_inv] using
          (mul_le_mul_of_nonneg_left hdyadic (by norm_num : (0 : ℚ) ≤ 2)))
    have hWw : W.width ≤ η :=
      (canonicalRepresentedInput_outcome_approx_width
        p pStar cStar gcode data i F).trans
        (by simpa [div_eq_mul_inv] using hdyadic)
    have hSd : R.maxAbs ^ derivative ≤ b := by
      have hSA : R.maxAbs ≤ A := hRmax.trans
        ((le_max_right (1 : ℚ) S).trans (by nlinarith [hA2]))
      have hp : R.maxAbs ^ derivative ≤ A ^ (derivative + 1) :=
          (pow_le_pow_left₀ hRmax0 hSA derivative).trans
          (pow_le_pow_right₀ (by linarith : (1 : ℚ) ≤ A) (Nat.le_succ _))
      have hρ1 : (1 : ℚ) ≤ ρ + 1 := by linarith
      have hd1 : (1 : ℚ) ≤ derivative + 1 := by norm_num
      exact hp.trans (by
        calc
          A ^ (derivative + 1) = 1 * 1 * A ^ (derivative + 1) * 1 := by ring
          _ ≤ b := by dsimp [b]; gcongr)
    have hPw : (R.npow derivative).width ≤ 2 * b ^ 2 * η := by
      have hp := ratInterval_npow_width_propagation R derivative S (2 * η)
        hS0 hRw hRmax
      have hcoef : (derivative : ℚ) * A ^ derivative ≤ b := by
        have hd : (derivative : ℚ) ≤ derivative + 1 := by norm_num
        have hpow : A ^ derivative ≤ A ^ (derivative + 1) :=
          pow_le_pow_right₀ (by linarith : (1 : ℚ) ≤ A) (Nat.le_succ _)
        calc
          (derivative : ℚ) * A ^ derivative ≤
              (derivative + 1) * A ^ (derivative + 1) :=
            mul_le_mul hd hpow (pow_nonneg (by positivity) _) (by positivity)
          _ ≤ b := by
            have hρ1 : (1 : ℚ) ≤ ρ + 1 := by linarith
            calc
              (derivative + 1) * A ^ (derivative + 1) =
                  1 * (derivative + 1) * A ^ (derivative + 1) * 1 := by ring
              _ ≤ b := by dsimp [b]; gcongr
      calc
        (R.npow derivative).width ≤
            (derivative : ℚ) * A ^ derivative * (2 * η) := hp
        _ ≤ b * (2 * η) :=
          mul_le_mul_of_nonneg_right hcoef (mul_nonneg (by norm_num) hη0)
        _ ≤ 2 * b ^ 2 * η := by
          have hbb : b ≤ b ^ 2 := by nlinarith [hb1]
          nlinarith [mul_le_mul_of_nonneg_right hbb hη0]
    have hJw : J.width ≤ 4 * b * η + 2 * b * K.width := by
      dsimp [J]
      have hKb : K.maxAbs ≤ b := hKmax.trans (by
        exact hρb)
      have hRb : R.maxAbs ≤ b := hRmax.trans (by
        calc S ≤ A := by dsimp [A]; nlinarith [le_max_right (1 : ℚ) S]
          _ ≤ A ^ (derivative + 1) := by
            simpa using (pow_le_pow_right₀ (by linarith : (1 : ℚ) ≤ A)
              (show 1 ≤ derivative + 1 by omega))
          _ ≤ b := by
            have hρ1 : (1 : ℚ) ≤ ρ + 1 := by linarith
            have hd1 : (1 : ℚ) ≤ derivative + 1 := by norm_num
            calc A ^ (derivative + 1) = 1 * 1 * A ^ (derivative + 1) * 1 := by ring
              _ ≤ b := by dsimp [b]; gcongr)
      calc
        (K.mul (realRect R)).width ≤
            2 * (K.maxAbs * R.width + R.maxAbs * K.width) := by
          simpa using complexRectangle_mul_width_propagation K (realRect R)
        _ ≤ 2 * (b * (2 * η) + b * K.width) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply add_le_add
          · exact mul_le_mul hKb hRw (RatInterval.width_nonneg R)
              (by positivity)
          · exact mul_le_mul_of_nonneg_right hRb
              ((RatInterval.width_nonneg K.re).trans (le_max_left _ _))
        _ = _ := by ring
    have hJmax : J.maxAbs ≤ ρ * S := by
      dsimp [J]
      calc
        (K.mul (realRect R)).maxAbs ≤ 2 * K.maxAbs * R.maxAbs := by
          simpa using ComplexRatInterval.mul_maxAbs K (realRect R)
        _ ≤ 2 * (spectralDiskBox B).maxAbs * S := by
          exact mul_le_mul (mul_le_mul_of_nonneg_left hKbox (by norm_num)) hRmax
            hRmax0 (mul_nonneg (by norm_num) hbox0)
        _ = ρ * S := by simp [ρ, spectralFullBoxRadius]
    have hJhi : J.re.hi ≤ ρ * S := by
      exact (le_abs_self J.re.hi).trans
        ((le_max_right _ _).trans ((le_max_left _ _).trans hJmax))
    have hEnv : BoundedCertifiedComplex.centeredExpEnvelope J ≤ E :=
      centeredExpEnvelope_le_rationalExpEnvelope J ρ S hJhi
    let εF : PosRat := ⟨1 / (F : ℚ), by positivity⟩
    have hstage : Transcendental.complexExpPrecision
        (BoundedCertifiedComplex.centeredExpCenterName J) εF = F := by
      simp [Transcendental.complexExpPrecision, εF, hF0.ne']
    have hXw0 := BoundedCertifiedComplex.centeredComplexExp_width_at_precision J εF
    rw [hstage] at hXw0
    have hXw : X.width ≤ 9 * b ^ 2 * η + 4 * b ^ 2 * K.width := by
      dsimp [X, εF] at hXw0
      have hEb : E ≤ b := by
        have hρ1 : (1 : ℚ) ≤ ρ + 1 := by linarith
        have hd1 : (1 : ℚ) ≤ derivative + 1 := by norm_num
        have hAp : 1 ≤ A ^ (derivative + 1) :=
          one_le_pow₀ (by linarith : (1 : ℚ) ≤ A)
        calc E = 1 * 1 * 1 * E := by ring
          _ ≤ b := by dsimp [b]; gcongr
      calc
        _ ≤ 2 * E * (4 * b * η + 2 * b * K.width) + η := by
          exact hXw0.trans (add_le_add
            (mul_le_mul (mul_le_mul_of_nonneg_left hEnv (by norm_num)) hJw
              ((RatInterval.width_nonneg J.re).trans (le_max_left _ _))
              (mul_nonneg (by norm_num) (by linarith [hE1]))) le_rfl)
        _ ≤ _ := by
          exact spectralExpWidth_arith E b η K.width hEb hb1 hη0
            ((RatInterval.width_nonneg K.re).trans (le_max_left _ _))
    have hXmax : X.maxAbs ≤ 14 * b ^ 3 := by
      have hEb : E ≤ b := by
        have hρ1 : (1 : ℚ) ≤ ρ + 1 := by linarith
        have hd1 : (1 : ℚ) ≤ derivative + 1 := by norm_num
        have hAp : 1 ≤ A ^ (derivative + 1) :=
          one_le_pow₀ (by linarith : (1 : ℚ) ≤ A)
        calc E = 1 * 1 * 1 * E := by ring
          _ ≤ b := by dsimp [b]; gcongr
      calc
        X.maxAbs ≤ BoundedCertifiedComplex.centeredExpEnvelope J + X.width :=
          centeredComplexExp_maxAbs_le J F
        _ ≤ E + (9 * b ^ 2 * η + 4 * b ^ 2 * K.width) :=
          add_le_add hEnv hXw
        _ ≤ 14 * b ^ 3 := by
          have hKwb := hKwidth.trans hρb
          have hb2 : b ^ 2 ≤ b ^ 3 := pow_le_pow_right₀ hb1 (by norm_num)
          have hbη := mul_le_mul_of_nonneg_left hη1 (pow_nonneg (by positivity) 2)
          have hbK := mul_le_mul_of_nonneg_left hKwb (pow_nonneg (by positivity) 2)
          nlinarith
    let C := W.mul (R.npow derivative)
    have hPmax : (R.npow derivative).maxAbs ≤ b :=
      (ratInterval_npow_maxAbs_le R derivative).trans hSd
    have hWb : W.maxAbs ≤ b := by
      have hρ1 : (1 : ℚ) ≤ ρ + 1 := by linarith
      have hrest : (1 : ℚ) ≤
          (derivative + 1) * A ^ (derivative + 1) * E := by
        have hd1 : (1 : ℚ) ≤ derivative + 1 := by norm_num
        have hAp : (1 : ℚ) ≤ A ^ (derivative + 1) :=
          one_le_pow₀ (by linarith : (1 : ℚ) ≤ A)
        calc
          1 = 1 * 1 * 1 := by ring
          _ ≤ (derivative + 1) * A ^ (derivative + 1) * E := by gcongr
      apply hWmax.trans
      calc
        Y ≤ max 1 Y := le_max_right _ _
        _ = max 1 Y * 1 := by ring
        _ ≤ max 1 Y * (ρ + 1) :=
          mul_le_mul_of_nonneg_left hρ1 (by positivity)
        _ = (max 1 Y * (ρ + 1)) * 1 := by ring
        _ ≤ (max 1 Y * (ρ + 1)) *
            ((derivative + 1) * A ^ (derivative + 1) * E) :=
          mul_le_mul_of_nonneg_left hrest (by positivity)
        _ = b := by dsimp [b]; ring
    have hCmax : C.maxAbs ≤ b ^ 2 := by
      dsimp [C]
      calc
        (W.mul (R.npow derivative)).maxAbs ≤
            W.maxAbs * (R.npow derivative).maxAbs := RatInterval.maxAbs_mul _ _
        _ ≤ b * b := mul_le_mul hWb hPmax
          ((abs_nonneg (R.npow derivative).lo).trans (le_max_left _ _))
          (zero_le_one.trans hb1)
        _ = b ^ 2 := by ring
    have hCwidth : C.width ≤ 6 * b ^ 3 * η := by
      have hmul := ratInterval_mul_width_propagation W (R.npow derivative)
      have hb0 : 0 ≤ b := zero_le_one.trans hb1
      have hb13 : b ≤ b ^ 3 := by
        calc b = b ^ 1 := by ring
          _ ≤ b ^ 3 := pow_le_pow_right₀ hb1 (by norm_num)
      have hb13η := mul_le_mul_of_nonneg_right hb13 hη0
      calc
        C.width ≤ 2 * (W.maxAbs * (R.npow derivative).width +
            (R.npow derivative).maxAbs * W.width) := by simpa [C] using hmul
        _ ≤ 2 * (b * (2 * b ^ 2 * η) + b * η) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply add_le_add
          · exact mul_le_mul hWb hPw (RatInterval.width_nonneg _)
              hb0
          · exact mul_le_mul hPmax hWw (RatInterval.width_nonneg W) hb0
        _ ≤ 6 * b ^ 3 * η := by nlinarith
    simpa [term, C, W, R, J, X, b, A, E, S, Y] using
      spectralNumeratorTerm_width_coarse K C X b η
        hb1 hη0 hCmax hCwidth hXw hXmax
  have hlist : ((I.toList.map term).map ComplexRatInterval.width).sum ≤
      256 * Q * (K.width + η) := by
    calc
      ((I.toList.map term).map ComplexRatInterval.width).sum =
          ∑ i ∈ I, (term i).width := by simp
      _ ≤ ∑ i ∈ I, 256 * ((max 1 (outcomeUpper input i) *
          (ρ + 1) * (derivative + 1) *
          (2 * max 1 (residualUpper input i)) ^ (derivative + 1) *
          rationalExpEnvelope ρ (residualUpper input i)) ^ 8) *
          (K.width + η) := Finset.sum_le_sum fun i hi ↦ hterm i hi
      _ ≤ ∑ i, 256 * ((max 1 (outcomeUpper input i) *
          (ρ + 1) * (derivative + 1) *
          (2 * max 1 (residualUpper input i)) ^ (derivative + 1) *
          rationalExpEnvelope ρ (residualUpper input i)) ^ 8) *
          (K.width + η) := by
        apply Finset.sum_le_univ_sum_of_nonneg
        intro i
        exact mul_nonneg
          (mul_nonneg (by norm_num)
            ((show Even 8 by exact ⟨4, by norm_num⟩).pow_nonneg _))
          (add_nonneg
            ((RatInterval.width_nonneg K.re).trans (le_max_left _ _)) hη0)
      _ = 256 * Q * (K.width + η) := by
        dsimp [Q, empiricalGWidthBound]
        rw [Finset.mul_sum, Finset.sum_mul]
  have hraw : (spectralNumeratorRawEval input I derivative K F).width ≤
      256 * Q * (K.width + η) := by
    have hs := intervalSum_width_propagation (I.toList.map term)
    have hscale := complexRectangle_smulRat_width_propagation
      ((max I.card 1 : ℚ)⁻¹) (intervalSum (I.toList.map term))
    have hinv : |((max I.card 1 : ℚ)⁻¹)| ≤ 1 := by
      rw [abs_of_nonneg (inv_nonneg.mpr (by positivity))]
      apply (inv_le_one₀ (by positivity)).2
      exact_mod_cast Nat.le_max_right I.card 1
    calc
      (spectralNumeratorRawEval input I derivative K F).width =
          ((intervalSum (I.toList.map term)).smulRat
            ((max I.card 1 : ℚ)⁻¹)).width := by rfl
      _ ≤ |((max I.card 1 : ℚ)⁻¹)| *
          (intervalSum (I.toList.map term)).width := hscale
      _ ≤ 1 * (intervalSum (I.toList.map term)).width :=
        mul_le_mul_of_nonneg_right hinv
          ((RatInterval.width_nonneg (intervalSum (I.toList.map term)).re).trans
            (le_max_left _ _))
      _ ≤ ((I.toList.map term).map ComplexRatInterval.width).sum := by simpa using hs
      _ ≤ 256 * Q * (K.width + η) := hlist
  let H : ℕ := 64 * (operations + 1) * (L.num.natAbs + 2) ^ 2
  have hηalloc : η ≤ e.1 / H := by
    have h := spectralEmpiricalMapFuel_inv_le e operations L
    dsimp only at h
    exact h
  have hL0 : 0 ≤ L := by dsimp [L]; positivity
  have hLnum : L ≤ (L.num.natAbs : ℚ) := by
    have hn : 0 ≤ L.num := Rat.num_nonneg.mpr hL0
    calc
      L = (L.num : ℚ) / (L.den : ℕ) := (Rat.num_div_den L).symm
      _ ≤ (L.num : ℚ) := div_le_self (by exact_mod_cast hn)
        (by exact_mod_cast Rat.den_pos L)
      _ = (L.num.natAbs : ℚ) := by
        have hnat : (L.num.natAbs : ℤ) = L.num := by
          rw [Int.natCast_natAbs, abs_of_nonneg hn]
        calc
          (L.num : ℚ) = ((L.num : ℤ) : ℚ) := rfl
          _ = (((L.num.natAbs : ℕ) : ℤ) : ℚ) := by rw [hnat]
          _ = (L.num.natAbs : ℚ) := by norm_num
  have hQL : 256 * Q ≤ L := by
    let t : ℚ := 256 * max 1 Q
    have ht1 : 1 ≤ t := by dsimp [t]; nlinarith [le_max_left (1 : ℚ) Q]
    have hQt : 256 * Q ≤ t := by
      dsimp [t]
      exact mul_le_mul_of_nonneg_left (le_max_right 1 Q) (by norm_num)
    exact hQt.trans (by dsimp [L, t]; nlinarith [ht1])
  have hnumH : (L.num.natAbs : ℚ) ≤ H := by
    have hop : (1 : ℚ) ≤ operations + 1 := by norm_num
    have hn : (0 : ℚ) ≤ L.num.natAbs := by positivity
    dsimp [H]
    push_cast
    nlinarith [sq_nonneg ((L.num.natAbs : ℚ) + 1)]
  have hQH : 256 * Q ≤ (H : ℚ) := hQL.trans (hLnum.trans hnumH)
  have herror : 256 * Q * η ≤ e.1 := by
    have hH0 : (0 : ℚ) < H := by dsimp [H]; positivity
    have hQ0' : 0 ≤ 256 * Q := mul_nonneg (by norm_num) hQ0
    calc
      256 * Q * η ≤ 256 * Q * (e.1 / H) :=
        mul_le_mul_of_nonneg_left hηalloc hQ0'
      _ ≤ (H : ℚ) * (e.1 / H) :=
        mul_le_mul_of_nonneg_right hQH (div_nonneg e.2.le hH0.le)
      _ = e.1 := by field_simp
  have hfinal := hraw.trans (by
      calc
        256 * Q * (K.width + η) = 256 * Q * K.width + 256 * Q * η := by ring
        _ ≤ 256 * Q * K.width + e.1 :=
          by simpa [add_comm] using
            (add_le_add_left herror (256 * Q * K.width)))
  have hFuel : (spectralNumeratorMap input B I derivative).precision e = F := rfl
  have hDerivative : (spectralNumeratorMap input B I derivative).derivativeEnvelope =
      256 * Q := rfl
  rw [hFuel, hDerivative]
  exact hfinal


/-- The three kinds of certified contour node the estimator evaluates: the pilot boundary
scan, the winding-number quadrature, and the final moment evaluation. -/
inductive SpectralNodeKind | pilot | winding | evaluation

/-- The number of certified interval operations charged to one contour node, as an affine
function of the fold's sample size: twelve per unit plus eighteen for a pilot node,
twenty-four per unit plus thirty-eight for a winding node, and twenty-eight per unit plus
forty-two for an evaluation node. -/
def spectralNodeOperationCount (kind : SpectralNodeKind) (sampleCard : ℕ) : ℕ :=
  match kind with
  | .pilot => 12 * sampleCard + 18
  | .winding => 24 * sampleCard + 38
  | .evaluation => 28 * sampleCard + 42

/-- The quadratic requested factor pays for applying the raw Newton norm
enclosure after certified-radius multiplication.  The factor sixty-four
leaves the corresponding quotient/tangent propagation margin. -/
def estimatorNodePrecision (requested : PosRat) (scale : ℚ) : PosRat :=
  ⟨requested.1 ^ 2 / (64 * (max 1 scale)), div_pos (sq_pos_of_pos requested.2)
    (mul_pos (by norm_num) (lt_of_lt_of_le zero_lt_one (le_max_left _ _)))⟩

/-- How accurately the certified contour radius must be refined before it is multiplied by
a unit-circle node: the requested accuracy divided by four times one plus the node's own
width, capped at one so the precision request never exceeds a unit. -/
def bankRadiusPrecision (requested : PosRat) (unitWidth : ℚ) : PosRat :=
  ⟨min 1 (requested.1 / (4 * (1 + max 0 unitWidth))), by
    apply lt_min
    · norm_num
    · exact div_pos requested.2
        (mul_pos (by norm_num) (by linarith [le_max_left (0 : ℚ) unitWidth]))⟩

/-- The node and mesh halves of the pilot's `aStar/64` error budget. -/
def pilotNodeTolerance (B : ContourBankData) : PosRat :=
  ⟨B.aStarRat / 128, div_pos B.aStarRat_pos (by norm_num)⟩

/-- The mesh half of the pilot error budget: one hundred twenty-eighth of the bank's
boundary-modulus certificate. -/
def pilotMeshTolerance (B : ContourBankData) : PosRat :=
  ⟨B.aStarRat / 128, div_pos B.aStarRat_pos (by norm_num)⟩

/-- The total pilot error budget: one sixty-fourth of the bank's boundary-modulus
certificate, split evenly between the node and mesh halves. -/
def pilotTolerance (B : ContourBankData) : PosRat :=
  ⟨B.aStarRat / 64, div_pos B.aStarRat_pos (by norm_num)⟩

/-- The total error budget of the final moment evaluation: the reciprocal of the sample
size (with one as a floor), so that the evaluation error vanishes as the sample grows. -/
def evaluationTolerance (p : Parameters) : PosRat :=
  ⟨1 / (max p.n 1 : ℚ), by positivity⟩

/-- The node half of the evaluation error budget: one over twice the sample size (with one
as a floor). -/
def evaluationNodeTolerance (p : Parameters) : PosRat :=
  ⟨1 / (2 * (max p.n 1 : ℚ)), by positivity⟩

/-- The mesh half of the evaluation error budget: one over twice the sample size (with one
as a floor). -/
def evaluationMeshTolerance (p : Parameters) : PosRat :=
  ⟨1 / (2 * (max p.n 1 : ℚ)), by positivity⟩

/-- The node half of the winding-number error budget, fixed at one sixteenth: together with
the mesh half this keeps the decoded winding enclosure inside a quarter-width window. -/
def windingNodeTolerance : PosRat := ⟨1 / 16, by norm_num⟩

/-- The mesh half of the winding-number error budget, fixed at one sixteenth. -/
def windingMeshTolerance : PosRat := ⟨1 / 16, by norm_num⟩

/-- A positive denominator certificate controls both guarded division and the
propagation of input-rectangle error through the quotient. -/
def guardedNodeTolerance (requested lower : PosRat) : PosRat :=
  ⟨min (lower.1 / 8)
      (requested.1 * lower.1 ^ 2 / (1 + lower.1) ^ 2), by
    apply lt_min
    · exact div_pos lower.2 (by norm_num)
    · exact div_pos (mul_pos requested.2 (sq_pos_of_pos lower.2))
        (sq_pos_of_pos (by linarith [lower.2]))⟩

/-- A rational upper bound for the j-th bank radius: the largest endpoint magnitude of that
radius's certified enclosure, refined until its width is at most one. -/
def radiusUpper (B : ContourBankData) (j : Fin (B.JBase + 1)) : ℚ :=
  ((B.rhoName j).approx ((B.rhoName j).modulus errorOne)).maxAbs

/-- The error-one radius enclosure needs one explicit unit of slack before it
is used as a rectangle-magnitude factor. -/
def radiusSlackUpper (B : ContourBankData) (j : Fin (B.JBase + 1)) : ℚ :=
  radiusUpper B j + 1

/-- A closed rational upper bound for the amplification introduced after
quadrature by division through the certified `N * 2πi` rectangle. -/
def spectralNormalizationAmplification (count : ℕ) : ℚ :=
  let divisor := boundedContourDivisor count 0
  1 + (max count 1 : ℚ) + divisor.maxAbs + |divisor.normSq.lo|⁻¹ +
    |divisor.normSq.lo|⁻¹ ^ 2

/-- Branch-wide scale for interval propagation.  It includes the certified
radius multiplication, full-box empirical-map magnitude/derivative envelope,
guarded quotient inverse-margin loss, tangent multiplication, finite
quadrature accumulation, and post-quadrature normalization. -/
def spectralNodeScale (B : ContourBankData) (j : Fin (B.JBase + 1))
    (amplification : ℚ) (lower : PosRat) (count operations : ℕ) : ℚ :=
  max 1 (256 * (operations + 1) * (1 + max 0 (radiusSlackUpper B j)) *
    (1 + max 0 amplification) ^ 2 *
    (1 + lower.1⁻¹ + lower.1⁻¹ ^ 2) *
    spectralNormalizationAmplification count)

/-- [The rational upper bound for a bank radius is never negative](goal). -/
lemma radiusUpper_nonneg (B : ContourBankData) (j : Fin (B.JBase + 1)) :
    0 ≤ radiusUpper B j :=
  (abs_nonneg _).trans (le_max_left _ _)

/-- A Lipschitz constant, along a circle of radius rho, for the modulus of the empirical
residual transform: eight times the radius times the first-derivative magnitude envelope
of that transform. It controls the mesh error of the pilot boundary scan. -/
def pilotCircleLipschitzBound (input : RepresentedSpectralInput p) (rho : ℚ) : ℚ :=
  8 * rho * empiricalFDerivativeBound input rho 1

/-- A Lipschitz constant along the circle of radius rho for the logarithmic-derivative
quotient integrated by the winding-number quadrature, given a positive lower bound m on
the denominator: it combines the first- and second-derivative magnitude envelopes of the
empirical residual transform, divided by m and by m squared respectively, with an overall
factor sixty-four. -/
def windingLipschitzBound (input : RepresentedSpectralInput p) (rho m : ℚ) : ℚ :=
  64 * (rho * empiricalFDerivativeBound input rho 1 / m + rho ^ 2 *
    (empiricalFDerivativeBound input rho 2 / m +
      empiricalFDerivativeBound input rho 1 ^ 2 / m ^ 2))

/-- A Lipschitz constant along the circle of radius rho for the outcome-weighted quotient
integrated by the moment evaluation, given a positive lower bound m on the denominator: it
combines the magnitude envelopes of the outcome-weighted transform and of the residual
transform, divided by m and by m squared, with an overall factor sixty-four. -/
def momentLipschitzBound (input : RepresentedSpectralInput p)
    (rho m : ℚ) (N : ℕ) : ℚ :=
  64 * (rho * empiricalGDerivativeBound input rho 0 / m + rho ^ 2 *
    (empiricalGDerivativeBound input rho 1 / m +
      empiricalGDerivativeBound input rho 0 * empiricalFDerivativeBound input rho 1 / m ^ 2))

/-- For [a nonnegative circle radius](hyp:hrho), [the pilot Lipschitz constant is never
negative](goal). -/
lemma pilotCircleLipschitzBound_nonneg (input : RepresentedSpectralInput p)
    {rho : ℚ} (hrho : 0 ≤ rho) : 0 ≤ pilotCircleLipschitzBound input rho := by
  unfold pilotCircleLipschitzBound
  have hF : 0 ≤ empiricalFDerivativeBound input rho 1 := by
    unfold empiricalFDerivativeBound rationalExpEnvelope
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (pow_nonneg (residualUpper_nonneg input i) _)
      (by positivity)
  positivity

/-- For [a nonnegative circle radius](hyp:hrho) and [a strictly positive denominator lower
bound](hyp:hm), [the winding-quadrature Lipschitz constant is never negative](goal). -/
lemma windingLipschitzBound_nonneg (input : RepresentedSpectralInput p)
    {rho m : ℚ} (hrho : 0 ≤ rho) (hm : 0 < m) :
    0 ≤ windingLipschitzBound input rho m := by
  unfold windingLipschitzBound
  have hF0 : 0 ≤ empiricalFDerivativeBound input rho 1 := by
    unfold empiricalFDerivativeBound rationalExpEnvelope
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (pow_nonneg (residualUpper_nonneg input i) _)
      (by positivity)
  have hF1 : 0 ≤ empiricalFDerivativeBound input rho 2 := by
    unfold empiricalFDerivativeBound rationalExpEnvelope
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (pow_nonneg (residualUpper_nonneg input i) _)
      (by positivity)
  positivity

/-- For [a nonnegative circle radius](hyp:hrho) and [a strictly positive denominator lower
bound](hyp:hm), [the moment-evaluation Lipschitz constant is never negative](goal). -/
lemma momentLipschitzBound_nonneg (input : RepresentedSpectralInput p)
    {rho m : ℚ} (N : ℕ) (hrho : 0 ≤ rho) (hm : 0 < m) :
    0 ≤ momentLipschitzBound input rho m N := by
  unfold momentLipschitzBound
  have hF : 0 ≤ empiricalFDerivativeBound input rho 1 := by
    unfold empiricalFDerivativeBound rationalExpEnvelope
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (pow_nonneg (residualUpper_nonneg input i) _)
      (by positivity)
  have hG0 : 0 ≤ empiricalGDerivativeBound input rho 0 := by
    unfold empiricalGDerivativeBound rationalExpEnvelope
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg
      (mul_nonneg (outcomeUpper_nonneg input i)
        (pow_nonneg (residualUpper_nonneg input i) _))
      (by positivity)
  have hG1 : 0 ≤ empiricalGDerivativeBound input rho 1 := by
    unfold empiricalGDerivativeBound rationalExpEnvelope
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg
      (mul_nonneg (outcomeUpper_nonneg input i)
        (pow_nonneg (residualUpper_nonneg input i) _))
      (by positivity)
  positivity

/-- Full-box interval amplification for the pilot empirical denominator map.
The contour Lipschitz bound is intentionally absent: it is stored separately
in `Schedule.magnitude` and controls only the mesh error. -/
def pilotScheduleMagnitude (input : RepresentedSpectralInput p)
    (B : ContourBankData) (j : Fin (B.JBase + 1)) : ℚ :=
  let Q := empiricalFWidthBound input (spectralFullBoxRadius B) 0
  (((128 * max 1 Q) ^ 2).num.natAbs : ℚ)

/-- [The pilot amplification factor is exactly the whole-number part of the square of one
hundred twenty-eight times the (floored-at-one) interval-propagation envelope of the
empirical residual transform at derivative order zero](goal); in particular it does not
depend on which bank circle is used. -/
lemma pilotScheduleMagnitude_eq (input : RepresentedSpectralInput p)
    (B : ContourBankData) (j : Fin (B.JBase + 1)) :
    pilotScheduleMagnitude input B j =
      ((((128 * max 1 (empiricalFWidthBound input
        (spectralFullBoxRadius B) 0)) ^ 2).num.natAbs : ℕ) : ℚ) := rfl

/-- [The pilot amplification factor is never negative](goal). -/
lemma pilotScheduleMagnitude_nonneg (input : RepresentedSpectralInput p)
    (B : ContourBankData) (j : Fin (B.JBase + 1)) :
    0 ≤ pilotScheduleMagnitude input B j := by
  dsimp [pilotScheduleMagnitude]
  positivity

/-- Full-box magnitude and derivative amplification for the two empirical
F maps used by guarded winding division. -/
def windingScheduleMagnitude (input : RepresentedSpectralInput p)
    (B : ContourBankData) (j : Fin (B.JBase + 1)) (lower : PosRat) : ℚ :=
  let Q0 := empiricalFWidthBound input (spectralFullBoxRadius B) 0
  let Q1 := empiricalFWidthBound input (spectralFullBoxRadius B) 1
  let A0 := ((128 * max 1 Q0) ^ 2).num.natAbs
  let A1 := ((128 * max 1 Q1) ^ 2).num.natAbs
  ((max A0 A1 : ℕ) : ℚ)

/-- [The winding-quadrature amplification factor is never negative](goal). -/
lemma windingScheduleMagnitude_nonneg (input : RepresentedSpectralInput p)
    (B : ContourBankData) (j : Fin (B.JBase + 1)) (lower : PosRat) :
    0 ≤ windingScheduleMagnitude input B j lower := by
  dsimp [windingScheduleMagnitude]
  positivity

/-- Full-box magnitude and derivative amplification for empirical G/F in the
evaluation quotient. -/
def evaluationScheduleMagnitude (input : RepresentedSpectralInput p)
    (B : ContourBankData) (j : Fin (B.JBase + 1)) (N : ℕ)
    (lower : PosRat) : ℚ :=
  let QF := empiricalFWidthBound input (spectralFullBoxRadius B) 0
  let QG := empiricalGWidthBound input (spectralFullBoxRadius B) 0
  let AF := ((128 * max 1 QF) ^ 2).num.natAbs
  let AG := ((256 * max 1 QG) ^ 2).num.natAbs
  ((max AF AG : ℕ) : ℚ)

/-- [The moment-evaluation amplification factor is never negative](goal). -/
lemma evaluationScheduleMagnitude_nonneg (input : RepresentedSpectralInput p)
    (B : ContourBankData) (j : Fin (B.JBase + 1)) (N : ℕ)
    (lower : PosRat) :
    0 ≤ evaluationScheduleMagnitude input B j N lower := by
  dsimp [evaluationScheduleMagnitude]
  positivity

/-- The complete accuracy schedule for the pilot boundary scan on fold a and bank circle j:
it fixes the mesh of the circle, the refinement level of every certified node, and the
input precision, from the pilot error budget rescaled by the branch-wide propagation scale
and by the circle Lipschitz constant. -/
def pilotSchedule (input : RepresentedSpectralInput p) (B : ContourBankData)
    (a : Fin 2) (j : Fin (B.JBase + 1)) : Schedule :=
  let L := pilotCircleLipschitzBound input (radiusUpper B j)
  let hL := pilotCircleLipschitzBound_nonneg input (radiusUpper_nonneg B j)
  let amplification := pilotScheduleMagnitude input B j
  let hAmplification := pilotScheduleMagnitude_nonneg input B j
  let operations := spectralNodeOperationCount .pilot (spectralFold p.n a).card
  let tolerance := estimatorNodePrecision (pilotNodeTolerance B)
    (spectralNodeScale B j amplification ⟨1, by norm_num⟩ 1 operations)
  spectralSchedule tolerance
    operations L amplification hL hAmplification

/-- Common certified-real-radius node used by pilot, winding, and evaluation. -/
def spectralRadiusNode (B : ContourBankData) (j : Fin (B.JBase + 1))
    (schedule : Schedule) (k : ℕ) : ComplexRatInterval :=
  certifiedRadiusNode (B.rhoName j)
    (bankRadiusPrecision schedule.tolerance (spectralNodeTarget schedule.tolerance).1)
    schedule k
/-- Pilot boundary infimum from the same bounded denominator map. -/
def pilotModulus (input : RepresentedSpectralInput p) (B : ContourBankData)
    (a : Fin 2) (j : Fin (B.JBase + 1)) : RatInterval :=
  let rho := radiusUpper B j
  let L := pilotCircleLipschitzBound input rho
  let hL := pilotCircleLipschitzBound_nonneg input (radiusUpper_nonneg B j)
  let map := spectralDenominatorMap input B (spectralFold p.n a) 0
  let schedule := pilotSchedule input B a j
  CircleMesh.infEnclosure
    (fun k ↦ (map.eval (spectralRadiusNode B j schedule k) schedule.fuel).normInterval
      schedule.fuel) L hL schedule.mesh schedule.mesh_pos

/-- The certified circle evaluator used to compute the winding number on bank circle j: its
numerator is the first derivative of the empirical residual transform on the lower fold,
its denominator the transform itself, and its accuracy schedule is derived from the winding
error budget guarded by the supplied positive lower bound on the denominator. -/
def spectralWindingEvaluator (input : RepresentedSpectralInput p)
    (B : ContourBankData) (j : Fin (B.JBase + 1)) (lower : PosRat) :
    BoundedCircleEvaluator (spectralDiskBox B) :=
  let rho := radiusUpper B j
  let L := windingLipschitzBound input rho lower.1
  let hL := windingLipschitzBound_nonneg input (radiusUpper_nonneg B j) lower.2
  let scheduleMagnitude := windingScheduleMagnitude input B j lower
  let hScheduleMagnitude := windingScheduleMagnitude_nonneg input B j lower
  let operations := spectralNodeOperationCount .winding (spectralFold p.n 0).card
  let tolerance := estimatorNodePrecision
    (guardedNodeTolerance windingNodeTolerance lower)
    (spectralNodeScale B j scheduleMagnitude lower 1 operations)
  let schedule := spectralSchedule tolerance
    operations L scheduleMagnitude hL hScheduleMagnitude
  { numerator := spectralDenominatorMap input B (spectralFold p.n 0) 1
    denominator := spectralDenominatorMap input B (spectralFold p.n 0) 0
    radius := B.rhoName j
    radiusPrecision := bankRadiusPrecision tolerance (spectralNodeTarget tolerance).1
    piPrecision := schedule.inputPrecision
    schedule := schedule
    mapFuel := schedule.fuel
    lipschitz := L
    lipschitz_nonneg := hL
    normalizationCount := 1 }

/-- A certified rectangular enclosure of the winding number of the empirical residual
transform around bank circle j: if the pilot scan certifies a strictly positive lower bound
on the transform's modulus along that circle, the argument-principle contour integral is
evaluated and normalized; otherwise the degenerate rectangle at the origin is returned. -/
def windingEnclosure (input : RepresentedSpectralInput p) (B : ContourBankData)
    (j : Fin (B.JBase + 1)) : ComplexRatInterval :=
  let pilot := pilotModulus input B 0 j
  if h : 0 < pilot.lo then
    let ev := spectralWindingEvaluator input B j ⟨pilot.lo, h⟩
    boundedContourNormalize (boundedContourEvaluate ev) 1 ev.piPrecision
  else ComplexRatInterval.zero

/-- Decodes a complex rectangle to a nonnegative whole number when it can only contain one:
the candidate is the ceiling of the real lower endpoint, and it is returned exactly when
that candidate lies inside the real range, the real upper endpoint is less than one above
it, and the imaginary range straddles zero. Otherwise nothing is returned. -/
def uniqueNonnegativeInteger (I : ComplexRatInterval) : Option ℕ :=
  let N := Int.toNat ⌈I.re.lo⌉
  if I.re.lo ≤ (N : ℚ) ∧ (N : ℚ) ≤ I.re.hi ∧ I.re.hi < N + 1 ∧
      I.im.lo ≤ 0 ∧ 0 ≤ I.im.hi then some N else none
  -- @realizes Nhat(unique decoded nonnegative winding number)

/-- Soundness, completeness at the paper's strict quarter-width threshold,
and uniqueness of the finite winding decoder. -/
def WindingDecoderContract (I : ComplexRatInterval) : Prop :=
  (∀ N : ℕ, uniqueNonnegativeInteger I = some N →
      I.Contains (((N : ℝ) : ℂ))) ∧
  (∀ N : ℕ, I.Contains (((N : ℝ) : ℂ)) → I.re.width < 1 / 4 →
      I.im.width < 1 / 4 → uniqueNonnegativeInteger I = some N) ∧
  (∀ N M : ℕ, uniqueNonnegativeInteger I = some N →
      I.Contains (((M : ℝ) : ℂ)) → I.re.width < 1 → N = M)

/-- [The finite winding decoder is sound, complete, and unique](goal): whatever it returns
is genuinely contained in the rectangle; any nonnegative whole number contained in a
rectangle narrower than a quarter in both coordinates is returned; and if it returns a
number while the rectangle is narrower than one in the real direction, no other nonnegative
whole number lies in the rectangle. -/
lemma uniqueNonnegativeInteger_contract (I : ComplexRatInterval) :
    WindingDecoderContract I := by
  constructor
  · intro N hN
    dsimp [uniqueNonnegativeInteger] at hN
    split at hN
    next h =>
      have hEq : Int.toNat ⌈I.re.lo⌉ = N := by simpa using hN
      rw [← hEq]
      unfold ComplexRatInterval.Contains RatInterval.Contains
      norm_num
      exact ⟨⟨h.1, h.2.1⟩, h.2.2.2.1, h.2.2.2.2⟩
    next h => simp at hN
  constructor
  · intro N hcontains hre him
    unfold ComplexRatInterval.Contains RatInterval.Contains at hcontains
    rcases hcontains with ⟨⟨hlo, hhi⟩, himlo, himhi⟩
    have hloQ : I.re.lo ≤ (N : ℚ) := by exact_mod_cast hlo
    have hhiQ : (N : ℚ) ≤ I.re.hi := by exact_mod_cast hhi
    have hceil_le : ⌈I.re.lo⌉ ≤ (N : ℤ) := (Int.ceil_le).2 hloQ
    have hpred_lt : (N : ℤ) - 1 < ⌈I.re.lo⌉ := by
      rw [Int.lt_ceil]
      norm_num
      unfold RatInterval.width at hre
      linarith
    have hceil : ⌈I.re.lo⌉ = (N : ℤ) := by omega
    unfold uniqueNonnegativeInteger
    simp only [hceil, Int.toNat_natCast]
    rw [if_pos]
    exact ⟨hloQ, hhiQ, by
      unfold RatInterval.width at hre
      linarith, by exact_mod_cast himlo, by exact_mod_cast himhi⟩
  · intro N M hN hM hwidth
    have hNcontains := (by
      dsimp [uniqueNonnegativeInteger] at hN
      split at hN
      next h =>
        have hEq : Int.toNat ⌈I.re.lo⌉ = N := by simpa using hN
        rw [← hEq]
        unfold ComplexRatInterval.Contains RatInterval.Contains
        norm_num
        exact ⟨⟨h.1, h.2.1⟩, h.2.2.2.1, h.2.2.2.2⟩
      next h => simp at hN : I.Contains (((N : ℝ) : ℂ)))
    unfold ComplexRatInterval.Contains RatInterval.Contains at hNcontains hM
    rcases hNcontains with ⟨⟨hNlo, hNhi⟩, -⟩
    rcases hM with ⟨⟨hMlo, hMhi⟩, -⟩
    unfold RatInterval.width at hwidth
    have hNhiQ : (N : ℚ) ≤ I.re.hi := by exact_mod_cast hNhi
    have hMloQ : I.re.lo ≤ (M : ℚ) := by exact_mod_cast hMlo
    have hMhiQ : (M : ℚ) ≤ I.re.hi := by exact_mod_cast hMhi
    have hNloQ : I.re.lo ≤ (N : ℚ) := by exact_mod_cast hNlo
    have hNM : N < M + 1 := by
      exact_mod_cast (show (N : ℚ) < M + 1 by linarith)
    have hMN : M < N + 1 := by
      exact_mod_cast (show (M : ℚ) < N + 1 by linarith)
    omega

/-- If [a rectangle contains a nonnegative whole number](hyp:hcontains) and is narrower
than a quarter [in the real direction](hyp:hre) and [in the imaginary direction](hyp:him),
then [the finite decoder returns exactly that number](goal). -/
lemma uniqueNonnegativeInteger_complete (I : ComplexRatInterval) (N : ℕ)
    (hcontains : I.Contains (((N : ℝ) : ℂ)))
    (hre : I.re.width < 1 / 4) (him : I.im.width < 1 / 4) :
    uniqueNonnegativeInteger I = some N :=
  (uniqueNonnegativeInteger_contract I).2.1 N hcontains hre him

/-- What the pilot pass records for one bank circle: the certified enclosure of the minimum
modulus of the empirical residual transform along the circle, the certified enclosure of
the winding number, and the decoded winding number when the enclosure pins one down. -/
structure PilotOutcome where
  modulus : RatInterval
  winding : ComplexRatInterval
  decoded : Option ℕ

/-- Runs the pilot pass on bank circle j: computes the certified boundary-modulus interval
from the lower fold, the certified winding enclosure, and the decoded winding number. -/
def pilotOutcome (input : RepresentedSpectralInput p) (B : ContourBankData)
    (j : Fin (B.JBase + 1)) : PilotOutcome :=
  let modulus := pilotModulus input B 0 j
  let winding := windingEnclosure input B j
  ⟨modulus, winding, uniqueNonnegativeInteger winding⟩

/-- A pilot outcome is admissible when its certified boundary modulus is at least half the
bank's modulus certificate and its winding number decoded to at least one, so the circle
provably encloses a zero and stays away from the boundary. -/
def PilotOutcome.admissible (B : ContourBankData) (outcome : PilotOutcome) : Bool :=
  decide (B.aStarRat / 2 ≤ outcome.modulus.lo ∧
    ∃ N, outcome.decoded = some N ∧ 1 ≤ N)

/-- Tests whether bank circle j is a best admissible circle: it is admissible and its
certified boundary modulus is at least as large as that of every other admissible
circle. -/
def pilotBestFrom (B : ContourBankData)
    (outcomes : Fin (B.JBase + 1) → PilotOutcome) (j : Fin (B.JBase + 1)) : Bool :=
  (outcomes j).admissible B && decide
    (∀ k, (outcomes k).admissible B = true →
      (outcomes k).modulus.lo ≤ (outcomes j).modulus.lo)

/-- Picks the contour from a family of pilot outcomes: the smallest-indexed circle among
those maximizing the certified boundary modulus over admissible circles, or nothing at all
if no circle is admissible. -/
def selectedContourFrom (B : ContourBankData)
    (outcomes : Fin (B.JBase + 1) → PilotOutcome) :
    Option (Fin (B.JBase + 1)) :=
  if ∃ j, pilotBestFrom B outcomes j = true then
    some (leastTrue (pilotBestFrom B outcomes)) else none

/-- The contour actually selected for a given certified input: run the pilot pass on every
bank circle, then take the least-indexed circle maximizing the certified boundary modulus
among admissible ones. -/
def selectedContour (input : RepresentedSpectralInput p) (B : ContourBankData) :
    Option (Fin (B.JBase + 1)) :=
  selectedContourFrom B (fun j ↦ pilotOutcome input B j)
  -- @realizes jhat(measurable finite maximizer with least-index tie break)

/-- The certified circle evaluator used for the final moment integral on bank circle j: its
numerator is the outcome-weighted empirical transform on the upper fold, its denominator
the residual transform on that fold, its normalization count the decoded winding number
(floored at one), and its accuracy schedule comes from the evaluation error budget guarded
by the supplied positive lower bound on the denominator. -/
def spectralEvaluationEvaluator (input : RepresentedSpectralInput p)
    (B : ContourBankData) (j : Fin (B.JBase + 1)) (N : ℕ) (lower : PosRat) :
    BoundedCircleEvaluator (spectralDiskBox B) :=
  let rho := radiusUpper B j
  let L := momentLipschitzBound input rho lower.1 N
  let hL := momentLipschitzBound_nonneg input N (radiusUpper_nonneg B j) lower.2
  let scheduleMagnitude := evaluationScheduleMagnitude input B j N lower
  let hScheduleMagnitude := evaluationScheduleMagnitude_nonneg input B j N lower
  let operations := spectralNodeOperationCount .evaluation (spectralFold p.n 1).card
  let tolerance := estimatorNodePrecision
    (guardedNodeTolerance (evaluationNodeTolerance p) lower)
    (spectralNodeScale B j scheduleMagnitude lower (max N 1) operations)
  let schedule := spectralSchedule tolerance
    operations L scheduleMagnitude hL hScheduleMagnitude
  { numerator := spectralNumeratorMap input B (spectralFold p.n 1) 0
    denominator := spectralDenominatorMap input B (spectralFold p.n 1) 0
    radius := B.rhoName j
    radiusPrecision := bankRadiusPrecision tolerance (spectralNodeTarget tolerance).1
    piPrecision := schedule.inputPrecision
    schedule := schedule
    mapFuel := schedule.fuel
    lipschitz := L
    lipschitz_nonneg := hL
    normalizationCount := max N 1 }

/-- A certified rectangular enclosure of the final contour moment on bank circle j: if the
upper fold's pilot scan certifies a strictly positive lower bound on the denominator's
modulus, the contour integral is evaluated and divided by the decoded winding count;
otherwise the degenerate rectangle at the origin is returned. -/
def evaluationEnclosure (input : RepresentedSpectralInput p) (B : ContourBankData)
    (j : Fin (B.JBase + 1)) (N : ℕ) : ComplexRatInterval :=
  let pilot := pilotModulus input B 1 j
  if h : 0 < pilot.lo then
    let ev := spectralEvaluationEvaluator input B j N ⟨pilot.lo, h⟩
    boundedContourNormalize (boundedContourEvaluate ev) (max N 1) ev.piPrecision
  else ComplexRatInterval.zero

/-- Build-aware pilot execution.  The finite extremum is performed by the
certified build over the actual denominator-node modulus intervals. -/
def builtPilotBoundary (build : complexCertifiedIntervalArithmetic)
    (input : RepresentedSpectralInput p) (B : ContourBankData)
    (a : Fin 2) (j : Fin (B.JBase + 1)) : RatInterval :=
  let rho := radiusUpper B j
  let L := pilotCircleLipschitzBound input rho
  let hL := pilotCircleLipschitzBound_nonneg input (radiusUpper_nonneg B j)
  let map := spectralDenominatorMap input B (spectralFold p.n a) 0
  let schedule := pilotSchedule input B a j
  build.operations.finiteInfimum
    (fun k ↦ (map.eval (spectralRadiusNode B j schedule k) schedule.fuel).normInterval
      schedule.fuel) L hL schedule.mesh schedule.mesh_pos

/-- Build-aware winding execution.  The build performs the trapezoidal
quadrature on the evaluator's certified nodes before normalization. -/
def builtWindingQuadrature (build : complexCertifiedIntervalArithmetic)
    (input : RepresentedSpectralInput p) (B : ContourBankData)
    (j : Fin (B.JBase + 1)) : ComplexRatInterval :=
  let pilot := builtPilotBoundary build input B 0 j
  if h : 0 < pilot.lo then
    let ev := spectralWindingEvaluator input B j ⟨pilot.lo, h⟩
    boundedContourNormalize
      (build.operations.quadrature ev.node ev.lipschitz ev.lipschitz_nonneg
        ev.schedule.mesh ev.schedule.mesh_pos)
      1 ev.piPrecision
  else ComplexRatInterval.zero

/-- Build-aware moment execution, using the build's pilot extremum and its
quadrature primitive on the evaluation nodes. -/
def builtEvaluationQuadrature (build : complexCertifiedIntervalArithmetic)
    (input : RepresentedSpectralInput p) (B : ContourBankData)
    (j : Fin (B.JBase + 1)) (N : ℕ) : ComplexRatInterval :=
  let pilot := builtPilotBoundary build input B 1 j
  if h : 0 < pilot.lo then
    let ev := spectralEvaluationEvaluator input B j N ⟨pilot.lo, h⟩
    boundedContourNormalize
      (build.operations.quadrature ev.node ev.lipschitz ev.lipschitz_nonneg
        ev.schedule.mesh ev.schedule.mesh_pos)
      (max N 1) ev.piPrecision
  else ComplexRatInterval.zero

/-- If [the compiled interval-arithmetic build computes finite extrema by the canonical
rule](hyp:hcanonical), then [running the pilot boundary scan through the build gives exactly
the reference boundary-modulus interval](goal). -/
lemma builtPilotBoundary_eq (build : complexCertifiedIntervalArithmetic)
    (hcanonical : build.operations.IsCanonical)
    (input : RepresentedSpectralInput p) (B : ContourBankData)
    (a : Fin 2) (j : Fin (B.JBase + 1)) :
    builtPilotBoundary build input B a j = pilotModulus input B a j := by
  simp only [builtPilotBoundary, pilotModulus,
    hcanonical.finiteInfimum_eq]

/-- If [the compiled interval-arithmetic build computes extrema and quadrature by the
canonical rules](hyp:hcanonical), then [running the winding computation through the build
gives exactly the reference winding enclosure](goal). -/
lemma builtWindingQuadrature_eq (build : complexCertifiedIntervalArithmetic)
    (hcanonical : build.operations.IsCanonical)
    (input : RepresentedSpectralInput p) (B : ContourBankData)
    (j : Fin (B.JBase + 1)) :
    builtWindingQuadrature build input B j = windingEnclosure input B j := by
  simp only [builtWindingQuadrature, windingEnclosure,
    builtPilotBoundary_eq build hcanonical, hcanonical.quadrature_eq,
    boundedContourEvaluate]

/-- If [the compiled interval-arithmetic build computes extrema and quadrature by the
canonical rules](hyp:hcanonical), then [running the moment evaluation through the build
gives exactly the reference evaluation enclosure](goal). -/
lemma builtEvaluationQuadrature_eq (build : complexCertifiedIntervalArithmetic)
    (hcanonical : build.operations.IsCanonical)
    (input : RepresentedSpectralInput p) (B : ContourBankData)
    (j : Fin (B.JBase + 1)) (N : ℕ) :
    builtEvaluationQuadrature build input B j N = evaluationEnclosure input B j N := by
  simp only [builtEvaluationQuadrature, evaluationEnclosure,
    builtPilotBoundary_eq build hcanonical, hcanonical.quadrature_eq,
    boundedContourEvaluate]

/-- A compiled implementation supplies only the three callable entry points
of the one bounded adapter, together with their correspondence to the local
finite programs.  Paper-specific map validity, margins, and schedule bounds
are derived locally and are deliberately not fields of this carrier. -/
structure CompiledBoundedSpectralAdapter where
  build : complexCertifiedIntervalArithmetic
  pilotBoundary : ∀ {p : Parameters}, RepresentedSpectralInput p →
    (B : ContourBankData) → Fin 2 → Fin (B.JBase + 1) → RatInterval
  windingQuadrature : ∀ {p : Parameters}, RepresentedSpectralInput p →
    (B : ContourBankData) → Fin (B.JBase + 1) → ComplexRatInterval
  evaluationQuadrature : ∀ {p : Parameters}, RepresentedSpectralInput p →
    (B : ContourBankData) → Fin (B.JBase + 1) → ℕ → ComplexRatInterval
  pilotBoundary_spec : ∀ {p : Parameters} (input : RepresentedSpectralInput p)
    (B : ContourBankData) (a : Fin 2) (j : Fin (B.JBase + 1)),
    pilotBoundary input B a j = builtPilotBoundary build input B a j
  windingQuadrature_spec : ∀ {p : Parameters} (input : RepresentedSpectralInput p)
    (B : ContourBankData) (j : Fin (B.JBase + 1)),
    windingQuadrature input B j = builtWindingQuadrature build input B j
  evaluationQuadrature_spec : ∀ {p : Parameters}
    (input : RepresentedSpectralInput p) (B : ContourBankData)
    (j : Fin (B.JBase + 1)) (N : ℕ),
    evaluationQuadrature input B j N = builtEvaluationQuadrature build input B j N

/-- The midpoint of a rational interval, the average of its two endpoints. -/
def rationalMidpoint (I : RatInterval) : ℚ := (I.lo + I.hi) / 2

/-- The bare computational content of a certified real number as returned by the program: a
family of rational enclosures indexed by a refinement level, together with a rule turning a
requested accuracy into a refinement level. No soundness property is bundled in; those are
stated separately. -/
structure ExecutableCertifiedRealName where
  approx : ℕ → RatInterval
  modulus : PosRat → ℕ

/-- An executable name represents a real number when every one of its rational enclosures,
at every refinement level, contains that number. -/
def ExecutableCertifiedRealName.Represents (name : ExecutableCertifiedRealName)
    (x : ℝ) : Prop := ∀ fuel, (name.approx fuel).Contains x

/-- An executable name certifies a real number when its enclosures shrink as the refinement
level increases, the enclosure returned at the level demanded by any accuracy request is at
least that accurate, and every enclosure contains the number. -/
def ExecutableCertifiedRealName.IsCertified (name : ExecutableCertifiedRealName)
    (x : ℝ) : Prop :=
  (∀ fuel, (name.approx (fuel + 1)).Subinterval (name.approx fuel)) ∧
  (∀ e, (name.approx (name.modulus e)).width ≤ e.1) ∧ name.Represents x

/-- The image of a rational interval under absolute value: the interval itself when it lies
in the nonnegative half-line, its reflection when it lies in the nonpositive half-line, and
otherwise the interval from zero to the larger of the two endpoint magnitudes. -/
def rationalAbsInterval (I : RatInterval) : RatInterval :=
  if _h : 0 ≤ I.lo then I
  else if h' : I.hi ≤ 0 then I.neg
  else ⟨0, max (-I.lo) I.hi,
    (le_of_lt (lt_of_not_ge h')).trans (le_max_right _ _)⟩

/-- The rational enclosure, at a given refinement level, of the raw output y clipped to the
symmetric range determined by the certified constant: it evaluates the identity that half
the difference between the absolute values of y plus the constant and y minus the constant
equals y truncated to that range. -/
def projectedOutputApprox (cStar : PositiveCertifiedReal) (y : ℚ)
    (fuel : ℕ) : RatInterval :=
  let yI := RatInterval.point y
  let cI := cStar.name.approx fuel
  (RatInterval.point (1 / 2)).mul
    ((rationalAbsInterval (yI.add cI)).sub (rationalAbsInterval (yI.sub cI)))

/-- The executable certified name of the estimator's reported value: the rational raw output
clipped to the symmetric range given by the certified range constant, with the accuracy
modulus inherited from that constant's own certified name. -/
def projectedOutputName (cStar : PositiveCertifiedReal) (y : ℚ) :
    ExecutableCertifiedRealName where
  approx := projectedOutputApprox cStar y
  modulus := cStar.name.modulus

/-- The three reasons the estimator can fall back to its default output: no bank circle was
admissible, the winding enclosure did not pin down a whole number, or the evaluation fold's
certified boundary modulus was too small. -/
inductive SpectralFallbackDecision
  | noAdmissibleCircle | windingNotDecoded | lowEvaluationModulus

/-- The five certified quantities the evaluator can request approximations of: a treatment
value, an outcome value, a clipped treatment-regression code value, a treatment residual,
and a bank radius. -/
inductive SpectralInputComponent
  | treatment | outcome | clippedTreatment | residual | radius

/-- The certified rectangle operations the evaluator performs: subtraction, exponentiation,
multiplication, addition, scalar rescaling, modulus and squared modulus, guarded division,
finite infimum, trapezoidal quadrature, and post-quadrature normalization. -/
inductive SpectralRectangleOperation
  | subtraction | exponential | multiplication | addition | scaling
  | modulus | modulusSquare | guardedQuotient | finiteInfimum | trapezoid | normalization

/-- One recorded step of the estimator's execution. Events cover which sample fold was used,
each accuracy request and each approximation read from a certified name, residual
subtractions, radius refinements, unit-circle nodes, complex exponentials with their Taylor
and square-root truncation levels, empirical transform node values, individual rectangle
operations, guarded divisions and tangent multiplications, the finite extremum and
quadrature calls, post-quadrature normalization, returned enclosures, endpoint acceptance
tests, fallback decisions, and the tie-break choice of contour. -/
inductive SpectralExecutionEvent
  | foldUsed (fold : Fin 2)
  | modulusCall (component : SpectralInputComponent) (index : ℕ)
      (requested : PosRat) (returnedFuel : ℕ)
  | approximationCall (component : SpectralInputComponent) (index fuel : ℕ)
  | residualSubtraction (index leftFuel rightFuel outputFuel : ℕ)
  | radiusRefinement (circle : ℕ) (precision : PosRat)
  | unitCircleNode (circle mesh node fuel : ℕ)
  | complexExponential (fold derivative circle node fuel : ℕ)
  | taylorCutoff (fold derivative circle node cutoff : ℕ)
  | squareRootCutoff (fold derivative circle node cutoff : ℕ)
  | empiricalFNode (fold derivative circle node fuel : ℕ)
  | empiricalGNode (fold derivative circle node fuel : ℕ)
  | rectangleOperation (operation : SpectralRectangleOperation)
      (fold derivative circle node ordinal : ℕ)
  | guardedDivision (circle node : ℕ) (accepted : Bool)
  | tangentMultiplication (circle node : ℕ)
  | finiteExtremum (circle mesh : ℕ)
  | quadrature (circle mesh : ℕ)
  | postNormalization (circle count : ℕ)
  | returnedEnclosure (circle : ℕ) (value : ComplexRatInterval)
  | endpointComparison (accepted : Bool)
  | fallback (decision : SpectralFallbackDecision)
  | tieBreak (circle : Option ℕ)

/-- A full execution trace: the list of recorded steps, in the order the estimator performs
them. -/
abbrev SpectralExecutionTrace := List SpectralExecutionEvent

/-- The half-error/max-fuel behavior of `CertifiedReal.sub` is visible in the
trace rather than summarized as one residual event. -/
def residualEnvelopeTrace (input : RepresentedSpectralInput p) (i : Fin p.n) :
    SpectralExecutionTrace :=
  let half : PosRat := ⟨errorOne.1 / 2, div_pos errorOne.2 (by norm_num)⟩
  let leftFuel := (input.observations i).tName.modulus half
  let rightFuel := (input.observations i).gName.modulus half
  let outputFuel := max leftFuel rightFuel
  [.modulusCall .treatment i half leftFuel,
    .modulusCall .clippedTreatment i half rightFuel,
    .approximationCall .treatment i outputFuel,
    .approximationCall .clippedTreatment i outputFuel,
    .residualSubtraction i leftFuel rightFuel outputFuel]

/-- The execution trace produced by evaluating the empirical residual transform at one
contour node: for each unit in the fold it records the residual-subtraction steps, the
approximation read of the residual, the complex exponential with its Taylor truncation
level, the multiplication by the residual power, and the resulting node value. -/
def empiricalFNodeTrace (input : RepresentedSpectralInput p) (I : Finset (Fin p.n))
    (z : ComplexRatInterval) (fold derivative circle node fuel : ℕ) :
    SpectralExecutionTrace :=
  I.toList.flatMap fun i ↦ residualEnvelopeTrace input i ++
    let residual := (representedResidual input i).approx fuel
    let argument := z.mul (realRect residual)
    [.approximationCall .residual i fuel,
      .complexExponential fold derivative circle node fuel,
      .taylorCutoff fold derivative circle node
        (BoundedCertifiedComplex.centeredExpStageFuel argument fuel),
      .rectangleOperation .multiplication fold derivative circle node i,
      .empiricalFNode fold derivative circle node fuel]

/-- The execution trace produced by evaluating the outcome-weighted empirical transform at
one contour node: as for the residual transform, with an extra approximation read of the
unit's outcome before the exponential and the multiplication. -/
def empiricalGNodeTrace (input : RepresentedSpectralInput p) (I : Finset (Fin p.n))
    (z : ComplexRatInterval) (fold derivative circle node fuel : ℕ) :
    SpectralExecutionTrace :=
  I.toList.flatMap fun i ↦ residualEnvelopeTrace input i ++
    let residual := (representedResidual input i).approx fuel
    let argument := z.mul (realRect residual)
    [.approximationCall .outcome i fuel,
      .approximationCall .residual i fuel,
      .complexExponential fold derivative circle node fuel,
      .taylorCutoff fold derivative circle node
        (BoundedCertifiedComplex.centeredExpStageFuel argument fuel),
      .rectangleOperation .multiplication fold derivative circle node i,
      .empiricalGNode fold derivative circle node fuel]

/-- Endpoint-complete node trace: `range (mesh+1)` is exactly `k ≤ mesh`.
Every repeated empirical rectangle operation is emitted at its execution site. -/
def evaluatorNodeTrace {box : ComplexRatInterval} (input : RepresentedSpectralInput p)
    (circle : ℕ) (fold : Fin 2) (numeratorIsG : Bool)
    (numeratorDerivative denominatorDerivative : ℕ)
    (ev : BoundedCircleEvaluator box) : SpectralExecutionTrace :=
  (List.range (ev.schedule.mesh + 1)).flatMap fun k ↦
    let z := certifiedRadiusNode ev.radius ev.radiusPrecision ev.schedule k
    [.radiusRefinement circle ev.radiusPrecision,
      .unitCircleNode circle ev.schedule.mesh k ev.schedule.fuel,
      .taylorCutoff fold 0 circle k ev.schedule.fuel] ++
      (if numeratorIsG then
        empiricalGNodeTrace input (spectralFold p.n fold) z fold numeratorDerivative
          circle k ev.mapFuel
      else
        empiricalFNodeTrace input (spectralFold p.n fold) z fold numeratorDerivative
          circle k ev.mapFuel) ++
      empiricalFNodeTrace input (spectralFold p.n fold) z fold denominatorDerivative
        circle k ev.mapFuel ++
      [.rectangleOperation .modulusSquare fold denominatorDerivative circle k 0,
        .guardedDivision circle k true,
        .rectangleOperation .guardedQuotient fold numeratorDerivative circle k 0,
        .tangentMultiplication circle k]

/-- The execution trace of the pilot boundary scan on one fold and one bank circle: the fold
selection, then for every mesh node the radius refinement, the unit-circle node, the
residual-transform evaluation and the modulus with its square-root truncation, and finally
the finite-infimum step over all nodes. -/
def pilotContourTrace (input : RepresentedSpectralInput p) (B : ContourBankData)
    (a : Fin 2) (j : Fin (B.JBase + 1)) : SpectralExecutionTrace :=
  let schedule := pilotSchedule input B a j
  let mapTrace := (List.range (schedule.mesh + 1)).flatMap fun k ↦
    let z := spectralRadiusNode B j schedule k
    [.radiusRefinement j (bankRadiusPrecision schedule.tolerance
      (spectralNodeTarget schedule.tolerance).1),
      .unitCircleNode j schedule.mesh k schedule.fuel,
      .taylorCutoff a 0 j k schedule.fuel] ++
      empiricalFNodeTrace input (spectralFold p.n a) z a 0 j k schedule.fuel ++
      [.rectangleOperation .modulus a 0 j k 0,
        .squareRootCutoff a 0 j k schedule.fuel]
  [.foldUsed a] ++ mapTrace ++
    [.finiteExtremum j schedule.mesh,
      .rectangleOperation .finiteInfimum a 0 j schedule.mesh 0]

/-- The execution trace of the winding-number computation on one bank circle: the pilot scan
on the lower fold, then — only if the certified boundary modulus is strictly positive — the
evaluator's node trace, the quadrature and normalization steps, and the returned enclosure;
if the modulus test fails the trace stops at the rejected endpoint comparison. -/
def windingTrace (input : RepresentedSpectralInput p) (B : ContourBankData)
    (j : Fin (B.JBase + 1)) : SpectralExecutionTrace :=
  let pilot := pilotModulus input B 0 j
  let repeatedPilot := pilotContourTrace input B 0 j
  if h : 0 < pilot.lo then
    let ev := spectralWindingEvaluator input B j ⟨pilot.lo, h⟩
    repeatedPilot ++ [.endpointComparison true, .foldUsed 0] ++
      evaluatorNodeTrace input j 0 false 1 0 ev ++
      [.quadrature j ev.schedule.mesh,
        .rectangleOperation .trapezoid 0 1 j ev.schedule.mesh 0,
        .postNormalization j 1,
        .rectangleOperation .normalization 0 1 j ev.schedule.mesh 0,
        .returnedEnclosure j (windingEnclosure input B j)]
  else repeatedPilot ++ [.endpointComparison false]

/-- The execution trace of the whole pilot pass: for every circle in the bank, in index
order, the lower-fold boundary scan followed by the winding computation on that circle. -/
def pilotBankTrace (input : RepresentedSpectralInput p) (B : ContourBankData) :
    SpectralExecutionTrace :=
  (Finset.univ.toList : List (Fin (B.JBase + 1))).flatMap fun j ↦
    pilotContourTrace input B 0 j ++ windingTrace input B j

/-- Everything one run of the estimator returns: the certified name of the reported value,
the raw rational value before clipping, the full execution trace, which bank circle was
selected, which winding number was decoded, and the final moment enclosure when one was
computed. -/
structure SpectralProgramResult where
  output : ExecutableCertifiedRealName
  raw : ℚ
  trace : SpectralExecutionTrace
  selected : Option ℕ
  decoded : Option ℕ
  evaluation : Option ComplexRatInterval

/-- The one instrumented option-A finite-rational adapter, parameterized only
by the three bounded-domain entry points used at runtime. -/
def spectralProgramWith
    (pilotBoundary : RepresentedSpectralInput p → (B : ContourBankData) →
      Fin 2 → Fin (B.JBase + 1) → RatInterval)
    (windingQuadrature : RepresentedSpectralInput p → (B : ContourBankData) →
      Fin (B.JBase + 1) → ComplexRatInterval)
    (evaluationQuadrature : RepresentedSpectralInput p → (B : ContourBankData) →
      Fin (B.JBase + 1) → ℕ → ComplexRatInterval)
    (input : RepresentedSpectralInput p) : SpectralProgramResult :=
  let B := contourBank p input.primitive
  let outcomes := fun j : Fin (B.JBase + 1) ↦
    let modulus := pilotBoundary input B 0 j
    let winding := windingQuadrature input B j
    PilotOutcome.mk modulus winding (uniqueNonnegativeInteger winding)
  let pilotTrace := pilotBankTrace input B
  match selectedContourFrom B outcomes with
  | none =>
      { output := projectedOutputName input.range.CthetaName 0, raw := 0
        trace := pilotTrace ++ [.tieBreak none, .fallback .noAdmissibleCircle]
        selected := none, decoded := none, evaluation := none }
  | some j =>
      match (outcomes j).decoded with
      | none =>
          { output := projectedOutputName input.range.CthetaName 0, raw := 0
            trace := pilotTrace ++ [.tieBreak (some j), .fallback .windingNotDecoded]
            selected := some j, decoded := none, evaluation := none }
      | some N =>
          let modulus := pilotBoundary input B 1 j
          if haccept : B.aStarRat / 4 ≤ modulus.lo then
            let final := evaluationQuadrature input B j N
            let y := rationalMidpoint final.re
            let hmodulus : 0 < modulus.lo := lt_of_lt_of_le
              (div_pos B.aStarRat_pos (by norm_num)) haccept
            let ev := spectralEvaluationEvaluator input B j N
              ⟨modulus.lo, hmodulus⟩
            { output := projectedOutputName input.range.CthetaName y, raw := y
              trace := pilotTrace ++ [.tieBreak (some j), .foldUsed 1] ++
                pilotContourTrace input B 1 j ++
                pilotContourTrace input B 1 j ++
                evaluatorNodeTrace input j 1 true 0 0 ev ++
                [.quadrature j ev.schedule.mesh,
                  .rectangleOperation .trapezoid 1 0 j ev.schedule.mesh 0,
                  .postNormalization j (max N 1),
                  .rectangleOperation .normalization 1 0 j ev.schedule.mesh 0,
                  .returnedEnclosure j final, .endpointComparison true]
              selected := some j, decoded := some N, evaluation := some final }
          else
            { output := projectedOutputName input.range.CthetaName 0, raw := 0
              trace := pilotTrace ++ [.tieBreak (some j)] ++
                pilotContourTrace input B 1 j ++ [.endpointComparison false,
                .fallback .lowEvaluationModulus]
              selected := some j, decoded := some N, evaluation := none }

/-- The one instrumented option-A finite-rational adapter used by the ordinary
wrapper. -/
def instrumentedSpectralProgram (input : RepresentedSpectralInput p) : SpectralProgramResult :=
  spectralProgramWith pilotModulus windingEnclosure evaluationEnclosure input

/-- Unconditional ordinary wrapper. -/
def ordinarySpectralProgram (input : RepresentedSpectralInput p) : SpectralProgramResult :=
  instrumentedSpectralProgram input

/-- The represented wrapper calls the supplied compiled entry points of the
same bounded adapter. -/
def representedSpectralProgram (compiled : CompiledBoundedSpectralAdapter)
    (input : RepresentedSpectralInput p) : SpectralProgramResult :=
  spectralProgramWith compiled.pilotBoundary compiled.windingQuadrature
    compiled.evaluationQuadrature input

/-- [Running the estimator through any compiled implementation of the bounded adapter gives
exactly the same result — value, trace, selected contour, decoded winding number and
enclosure — as the reference instrumented program](goal). -/
lemma representedSpectralProgram_eq_instrumented
    (compiled : CompiledBoundedSpectralAdapter) (input : RepresentedSpectralInput p) :
    representedSpectralProgram compiled input = instrumentedSpectralProgram input := by
  simp only [representedSpectralProgram, instrumentedSpectralProgram,
    spectralProgramWith, compiled.pilotBoundary_spec,
    compiled.windingQuadrature_spec, compiled.evaluationQuadrature_spec,
    builtPilotBoundary_eq compiled.build compiled.build.canonicalAlgorithms,
    builtWindingQuadrature_eq compiled.build compiled.build.canonicalAlgorithms,
    builtEvaluationQuadrature_eq compiled.build compiled.build.canonicalAlgorithms]

/-- Semantic empirical residual used only in soundness statements for the
finite rational adapter.  It is not an executable evaluator path. -/
def semanticEmpiricalResidual (p : Parameters) (gcode : ℕ → Xspace → ℝ)
    (data : Fin p.n → Obs Xspace) (i : Fin p.n) : ℝ :=
  treatment (data i) - min (max (gcode p.n (covariate (data i))) (-p.Cg)) p.Cg

/-- Exact value enclosed by `spectralDenominatorMap`; proof target only. -/
def semanticEmpiricalF (p : Parameters) (gcode : ℕ → Xspace → ℝ)
    (data : Fin p.n → Obs Xspace) (I : Finset (Fin p.n))
    (derivative : ℕ) (z : ℂ) : ℂ :=
  ((max I.card 1 : ℝ)⁻¹ : ℂ) * ∑ i ∈ I,
    ((semanticEmpiricalResidual p gcode data i ^ derivative : ℝ) : ℂ) *
      Complex.exp (z * semanticEmpiricalResidual p gcode data i)

/-- Exact value enclosed by `spectralNumeratorMap`; proof target only. -/
def semanticEmpiricalG (p : Parameters) (gcode : ℕ → Xspace → ℝ)
    (data : Fin p.n → Obs Xspace) (I : Finset (Fin p.n))
    (derivative : ℕ) (z : ℂ) : ℂ :=
  ((max I.card 1 : ℝ)⁻¹ : ℂ) * ∑ i ∈ I,
    (((outcome (data i) * semanticEmpiricalResidual p gcode data i ^ derivative : ℝ) : ℂ) *
      Complex.exp (z * semanticEmpiricalResidual p gcode data i))

/-- For canonically named data, [the real number named by the certified residual of a unit
is exactly that unit's treatment minus its clipped treatment-regression code value](goal).
-/
lemma canonicalRepresentedInput_residual_value
    (p : Parameters) (pStar : CertifiedBankInputs p) (cStar : CertifiedRangeInput p)
    (gcode : ℕ → Xspace → ℝ) (data : Fin p.n → Obs Xspace) (i : Fin p.n) :
    (representedResidual (canonicalRepresentedInput p pStar cStar gcode data) i).value =
      semanticEmpiricalResidual p gcode data i := by
  rfl

/-- For canonically named data, [the exact value enclosed by the certified residual-transform
map coincides with the semantic empirical transform](goal): the fold average of the residual
raised to the derivative order times the exponential of the argument against that
residual. -/
lemma spectralDenominatorMap_value_canonical
    (p : Parameters) (pStar : CertifiedBankInputs p) (cStar : CertifiedRangeInput p)
    (gcode : ℕ → Xspace → ℝ) (data : Fin p.n → Obs Xspace)
    (B : ContourBankData) (I : Finset (Fin p.n)) (derivative : ℕ) (z : ℂ) :
    (spectralDenominatorMap (canonicalRepresentedInput p pStar cStar gcode data)
      B I derivative).value z = semanticEmpiricalF p gcode data I derivative z := by
  simp only [spectralDenominatorMap, semanticEmpiricalF,
    canonicalRepresentedInput_residual_value]

/-- For canonically named data, [the exact value enclosed by the certified outcome-weighted
map coincides with the semantic outcome-weighted empirical transform](goal). -/
lemma spectralNumeratorMap_value_canonical
    (p : Parameters) (pStar : CertifiedBankInputs p) (cStar : CertifiedRangeInput p)
    (gcode : ℕ → Xspace → ℝ) (data : Fin p.n → Obs Xspace)
    (B : ContourBankData) (I : Finset (Fin p.n)) (derivative : ℕ) (z : ℂ) :
    (spectralNumeratorMap (canonicalRepresentedInput p pStar cStar gcode data)
      B I derivative).value z = semanticEmpiricalG p gcode data I derivative z := by
  unfold spectralNumeratorMap semanticEmpiricalG
  apply congrArg ((↑(max I.card 1 : ℝ) : ℂ)⁻¹ * ·)
  apply Finset.sum_congr rfl
  intro i hi
  rw [canonicalRepresentedInput_residual_value]
  rfl

/-- The estimator's full result on a data set: build the canonical certified input from the
data and the fixed primitive and range records, then run the ordinary finite-rational
program on it. -/
noncomputable def ordinaryFiniteRationalResult (p : Parameters)
    (pStar : CertifiedBankInputs p) (cStar : CertifiedRangeInput p)
    (gcode : ℕ → Xspace → ℝ) (data : Fin p.n → Obs Xspace) :
    SpectralProgramResult :=
  ordinarySpectralProgram (canonicalRepresentedInput p pStar cStar gcode data)

/-- The real-valued point estimate reported by the estimator: the raw rational output of the
program, truncated to the symmetric range determined by the certified range constant. -/
noncomputable def ordinaryThetaHatValue (p : Parameters)
    (pStar : CertifiedBankInputs p) (cStar : CertifiedRangeInput p)
    (gcode : ℕ → Xspace → ℝ) (data : Fin p.n → Obs Xspace) : ℝ :=
  let y : ℝ := (ordinaryFiniteRationalResult p pStar cStar gcode data).raw
  min (max y (-cStar.CthetaName.name.value)) cStar.CthetaName.name.value

/-- Take a treatment-regression code sequence and [a second one](hyp:hcode). If [they agree
at every covariate value after clipping to the range from minus Cg to Cg](hyp:hclip), then
[they yield the same point estimate on every data set](goal). -/
lemma ordinaryThetaHatValue_congr_current
    (p : Parameters) (pStar : CertifiedBankInputs p) (cStar : CertifiedRangeInput p)
    (gcode hcode : ℕ → Xspace → ℝ)
    (hclip : ∀ x,
      min (max (gcode p.n x) (-p.Cg)) p.Cg =
        min (max (hcode p.n x) (-p.Cg)) p.Cg) :
    ordinaryThetaHatValue p pStar cStar gcode =
      ordinaryThetaHatValue p pStar cStar hcode := by
  funext data
  unfold ordinaryThetaHatValue ordinaryFiniteRationalResult ordinarySpectralProgram
  rw [canonicalRepresentedInput_congr_current p pStar cStar gcode hcode data hclip]

/-- Supplied certified observation records for the represented transducer.
The type indices fix the experiment-wide primitive records; callers supply
only the observation records. -/
structure SuppliedRepresentedSpectralInput (p : Parameters)
    (_pStar : CertifiedBankInputs p) (_cStar : CertifiedRangeInput p) where
  observations : Fin p.n → RepresentedObservation

/-- Completes a caller-supplied family of certified observation records into a full
certified input by attaching the experiment-wide primitive and range records. -/
def SuppliedRepresentedSpectralInput.withFixedRecords
    (pStar : CertifiedBankInputs p) (cStar : CertifiedRangeInput p)
    (input : SuppliedRepresentedSpectralInput p pStar cStar) :
    RepresentedSpectralInput p where
  observations := input.observations
  primitive := pStar
  range := cStar

/-- The estimator packaged as one object: the domain condition it requires of the supplied
regression code, the program it runs on a data set, the real point estimate it reports, the
execution trace it emits, the version of the program driven by a compiled implementation,
and the correspondence property tying that version to the reference one. -/
structure AdaptiveContourEstimator (Xspace : Type*) [MeasurableSpace Xspace]
    (p : Parameters) (pStar : CertifiedBankInputs p) (cStar : CertifiedRangeInput p) where
  publicDomain : Prop
  ordinaryProgram : (Fin p.n → Obs Xspace) → SpectralProgramResult
  ordinaryValue : (Fin p.n → Obs Xspace) → ℝ
  fullTrace : (Fin p.n → Obs Xspace) → SpectralExecutionTrace
  representedProgram : CompiledBoundedSpectralAdapter →
    SuppliedRepresentedSpectralInput p pStar cStar → SpectralProgramResult
  representedOutputCorrespondence : CompiledBoundedSpectralAdapter → Prop

/-- Lets a packaged estimator be applied directly to a data set, returning its real point
estimate. -/
instance (p : Parameters) (pStar : CertifiedBankInputs p) (cStar : CertifiedRangeInput p) :
    CoeFun (AdaptiveContourEstimator Xspace p pStar cStar)
    (fun _ ↦ (Fin p.n → Obs Xspace) → ℝ) :=
  ⟨AdaptiveContourEstimator.ordinaryValue⟩

/-- The correctness contract demanded of a compiled implementation: on every data set it
returns the same result and the same execution trace as the reference program, and the
certified name it outputs genuinely certifies the estimator's real point estimate. -/
def representedExecutionContract (compiled : CompiledBoundedSpectralAdapter)
    (p : Parameters) (pStar : CertifiedBankInputs p) (cStar : CertifiedRangeInput p)
    (gcode : ℕ → Xspace → ℝ) : Prop :=
  ∀ data : Fin p.n → Obs Xspace,
    let input := canonicalRepresentedInput p pStar cStar gcode data
    let represented := representedSpectralProgram compiled input
    let ordinary := ordinaryFiniteRationalResult p pStar cStar gcode data
    represented = ordinary ∧ represented.trace = ordinary.trace ∧
      represented.output.IsCertified (ordinaryThetaHatValue p pStar cStar gcode data)

-- @node: def:adaptive-contour-estimator
/-- The estimator itself, assembled for a given parameter block, fixed certified records, and
supplied treatment-regression code sequence: it requires the code at the current sample size
to be measurable, runs the canonical finite-rational program, reports the clipped point
estimate, exposes the full execution trace, and demands of any compiled implementation the
represented-execution contract. -/
noncomputable def thetaHatSpec (p : Parameters) (pStar : CertifiedBankInputs p)
    (cStar : CertifiedRangeInput p) (gcode : ℕ → Xspace → ℝ) :
    AdaptiveContourEstimator Xspace p pStar cStar :=
  { publicDomain := Measurable (gcode p.n)
    ordinaryProgram := ordinaryFiniteRationalResult p pStar cStar gcode
    ordinaryValue := ordinaryThetaHatValue p pStar cStar gcode
    fullTrace := fun data ↦ (ordinaryFiniteRationalResult p pStar cStar gcode data).trace
    representedProgram := fun compiled input ↦
      representedSpectralProgram compiled
        (SuppliedRepresentedSpectralInput.withFixedRecords pStar cStar input)
    representedOutputCorrespondence := fun compiled ↦
      representedExecutionContract compiled p pStar cStar gcode }
  -- @realizes thetahatSpec(total Borel option-A statistic; fixed records)

/-- Take a treatment-regression code sequence and [a second one](hyp:hcode). If [they agree
at every covariate value after clipping to the range from minus Cg to Cg](hyp:hclip), then
[the two assembled estimators are the same function of the data](goal). -/
lemma thetaHatSpec_congr_current
    (p : Parameters) (pStar : CertifiedBankInputs p) (cStar : CertifiedRangeInput p)
    (gcode hcode : ℕ → Xspace → ℝ)
    (hclip : ∀ x,
      min (max (gcode p.n x) (-p.Cg)) p.Cg =
        min (max (hcode p.n x) (-p.Cg)) p.Cg) :
    (thetaHatSpec p pStar cStar gcode : (Fin p.n → Obs Xspace) → ℝ) =
      thetaHatSpec p pStar cStar hcode :=
  ordinaryThetaHatValue_congr_current p pStar cStar gcode hcode hclip

/-- A compiled implementation is a faithful execution of the estimator when it satisfies the
estimator's own represented-output correspondence requirement. -/
def RepresentedExecution (compiled : CompiledBoundedSpectralAdapter)
    (p : Parameters) (pStar : CertifiedBankInputs p) (cStar : CertifiedRangeInput p)
    (gcode : ℕ → Xspace → ℝ) : Prop :=
  (thetaHatSpec p pStar cStar gcode).representedOutputCorrespondence compiled

end CausalSmith.Stat.SaPlmCumulantConverse
