import Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Complex.IntervalExp

/-!
# Certified complex exponential semantics

This module composes the rational real exponential, sine, and cosine
extensions into complex exponential rectangles. For a certified complex input,
each name stage first requests a magnitude-sensitive input width, computes
Taylor fuel from the rational rectangle actually returned, and recursively
intersects the result with all preceding stages. This avoids both false
fixed-input convergence claims and false nesting claims between unrelated
midpoint extensions.
-/

namespace Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Complex

open Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic

namespace Transcendental

/-- Raw complex exponential evaluation composes certified real exponential,
cosine, and sine interval extensions coordinatewise. -/
def complexExpRaw (I : ComplexRatInterval) (fuel : ℕ) : ComplexRatInterval :=
  ⟨(expInterval I.re fuel).mul (cosInterval I.im fuel),
    (expInterval I.re fuel).mul (sinInterval I.im fuel)⟩

/-- Complex exponential outputs recursively intersect raw compositional bounds
for one fixed input rectangle. -/
def complexExp (I : ComplexRatInterval) : ℕ → ComplexRatInterval
  | 0 => complexExpRaw I 0
  | fuel + 1 => (complexExp I fuel).tighten (complexExpRaw I (fuel + 1))

private theorem complexExpRaw_sound {I : ComplexRatInterval} {z : ℂ}
    (hz : I.Contains z) (fuel : ℕ) :
    (complexExpRaw I fuel).Contains (Complex.exp z) := by
  have he := expInterval_sound hz.1 fuel
  have hc := cosInterval_sound hz.2 fuel
  have hs := sinInterval_sound hz.2 fuel
  exact ⟨by simpa [complexExpRaw, Complex.exp_re] using RatInterval.mul_sound he hc,
    by simpa [complexExpRaw, Complex.exp_im] using RatInterval.mul_sound he hs⟩

/-- Compositional complex exponential evaluation encloses the exact complex exponential. -/
theorem complexExp_sound {I : ComplexRatInterval} {z : ℂ}
    (hz : I.Contains z) (fuel : ℕ) :
    (complexExp I fuel).Contains (Complex.exp z) := by
  induction fuel with
  | zero => exact complexExpRaw_sound hz 0
  | succ fuel ih => exact (ComplexRatInterval.tighten_sound_left ih
      (complexExpRaw_sound hz (fuel + 1))).1

/-- Adjacent complex exponential outputs for one fixed input rectangle are
nested by coordinatewise finite intersection. -/
theorem complexExp_nested (I : ComplexRatInterval) (fuel : ℕ) :
    (complexExp I (fuel + 1)).Subinterval (complexExp I fuel) := by
  have hz : I.Contains ((intervalMid I.re : ℝ) +
      (intervalMid I.im : ℝ) * Complex.I) := by
    constructor
    · simpa using (show I.re.Contains (intervalMid I.re : ℝ) from by
        constructor <;> exact_mod_cast (by
          dsimp [intervalMid]
          linarith [I.re.lo_le_hi]))
    · simpa using (show I.im.Contains (intervalMid I.im : ℝ) from by
        constructor <;> exact_mod_cast (by
          dsimp [intervalMid]
          linarith [I.im.lo_le_hi]))
  exact (ComplexRatInterval.tighten_sound_left
    (complexExp_sound hz fuel) (complexExpRaw_sound hz (fuel + 1))).2

/-- Complex exponential width is bounded explicitly by the widths and endpoint
magnitudes of its certified exponential and trigonometric factors. -/
theorem complexExp_width (I : ComplexRatInterval) (fuel : ℕ) :
    (complexExp I fuel).width ≤
      2 * (max (expInterval I.re fuel).maxAbs 0 *
          max (cosInterval I.im fuel).width (sinInterval I.im fuel).width +
        max (cosInterval I.im fuel).maxAbs (sinInterval I.im fuel).maxAbs *
          max (expInterval I.re fuel).width 0) := by
  -- View `complexExpRaw` as multiplication of `⟨E, 0⟩` by `⟨cos, sin⟩`.
  -- First show the recursively tightened result is a subrectangle of the raw
  -- result at this fuel, then apply `ComplexRatInterval.mul_width` and simplify
  -- the point-zero coordinate widths and magnitudes.
  let E := expInterval I.re fuel
  let T : ComplexRatInterval := ⟨cosInterval I.im fuel, sinInterval I.im fuel⟩
  let A : ComplexRatInterval := ⟨E, RatInterval.point 0⟩
  have hsub : (complexExp I fuel).Subinterval (complexExpRaw I fuel) := by
    cases fuel with
    | zero =>
        exact ⟨RatInterval.subinterval_refl _, RatInterval.subinterval_refl _⟩
    | succ fuel =>
        rw [complexExp]
        have hmid : I.Contains ((intervalMid I.re : ℝ) +
            (intervalMid I.im : ℝ) * Complex.I) := by
          constructor
          · simpa using (show I.re.Contains (intervalMid I.re : ℝ) from by
              constructor <;> exact_mod_cast (by
                dsimp [intervalMid]
                linarith [I.re.lo_le_hi]))
          · simpa using (show I.im.Contains (intervalMid I.im : ℝ) from by
              constructor <;> exact_mod_cast (by
                dsimp [intervalMid]
                linarith [I.im.lo_le_hi]))
        have hprev := complexExp_sound hmid fuel
        have hraw := complexExpRaw_sound hmid (fuel + 1)
        exact ⟨
          Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Transcendental.tighten_subinterval_right
            hprev.1 hraw.1,
          Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Transcendental.tighten_subinterval_right
            hprev.2 hraw.2⟩
  have hwidth : (complexExp I fuel).width ≤ (complexExpRaw I fuel).width :=
    max_le_max (RatInterval.width_mono hsub.1) (RatInterval.width_mono hsub.2)
  have hraw_eq : complexExpRaw I fuel = A.mul T := by
    ext <;> simp [complexExpRaw, A, T, E, ComplexRatInterval.mul,
      RatInterval.point, RatInterval.mul, RatInterval.sub, RatInterval.add,
      RatInterval.neg]
  rw [hraw_eq] at hwidth
  refine hwidth.trans ((ComplexRatInterval.mul_width A T).trans_eq ?_)
  dsimp [A, T, E, ComplexRatInterval.maxAbs, ComplexRatInterval.width]
  simp only [RatInterval.point, RatInterval.maxAbs, RatInterval.width,
    abs_zero, max_self, sub_self]

/-- The initial real-part enclosure gives a positive rational amplification
scale for all later exponential stages. -/
def complexExpMagnitude (z : CertifiedComplex) : ℚ :=
  |(Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Transcendental.expScalar
      (z.approx 0).re.maxAbs 0).hi| + 2

/-- The canonical error target at name stage `n` is the reciprocal of `n + 1`. -/
def complexExpStageTolerance (n : ℕ) : PosRat :=
  ⟨1 / (n + 1 : ℚ), by positivity⟩

/-- The inner scalar-operation tolerance spends the stage budget after dividing
by the certified magnitude amplification scale. -/
def complexExpInnerTolerance (z : CertifiedComplex) (n : ℕ) : PosRat :=
  ⟨(complexExpStageTolerance n).1 / (16 * complexExpMagnitude z), by
    apply div_pos (complexExpStageTolerance n).2
    dsimp [complexExpMagnitude]
    positivity⟩

/-- The input-name tolerance also pays for exponential Lipschitz amplification,
so a large positive real part requests a proportionally narrower input box. -/
def complexExpInputTolerance (z : CertifiedComplex) (n : ℕ) : PosRat :=
  ⟨(complexExpInnerTolerance z n).1 / (4 * complexExpMagnitude z), by
    apply div_pos (complexExpInnerTolerance z n).2
    dsimp [complexExpMagnitude]
    positivity⟩

/-- A complex exponential stage refines its input using the magnitude-sensitive
tolerance selected for that stage. -/
def complexExpStageInput (z : CertifiedComplex) (n : ℕ) : ComplexRatInterval :=
  z.approx (z.modulus (complexExpInputTolerance z n))

/-- Taylor fuel for a stage is computed from the rational midpoint and
magnitude of the input rectangle actually returned, not from a denominator
ordering heuristic. -/
def complexExpStageFuel (z : CertifiedComplex) (n : ℕ) : ℕ :=
  let I := complexExpStageInput z n
  let α : PosRat :=
    ⟨(complexExpInnerTolerance z n).1 / 8,
      div_pos (complexExpInnerTolerance z n).2 (by norm_num)⟩
  let trigFuel :=
    32 * (α.1.den + 1) * ((intervalMid I.im).num.natAbs + 2) ^ 2
  max trigFuel
    (max
      (Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Transcendental.expPrecision
        (intervalMid I.re) α)
      (Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Transcendental.expPrecision
        I.re.maxAbs α))

/-- One executable complex exponential name stage uses its scheduled input
rectangle and the Taylor fuel computed from that same rectangle. -/
def complexExpStage (z : CertifiedComplex) (n : ℕ) : ComplexRatInterval :=
  complexExp (complexExpStageInput z n) (complexExpStageFuel z n)

/-- Certified complex-exponential name approximations recursively intersect
every scheduled stage output seen so far. -/
def complexExpNameApprox (z : CertifiedComplex) : ℕ → ComplexRatInterval
  | 0 => complexExpStage z 0
  | n + 1 => (complexExpNameApprox z n).tighten (complexExpStage z (n + 1))

private theorem complexExpStage_sound (z : CertifiedComplex) (n : ℕ) :
    (complexExpStage z n).Contains (Complex.exp z.value) := by
  exact complexExp_sound (z.contains _) _

/-- Recursive complex-exponential name approximations remain sound and
adjacent stages are nested by their defining finite intersection. -/
theorem complexExpNameApprox_spec (z : CertifiedComplex) (n : ℕ) :
    (complexExpNameApprox z n).Contains (Complex.exp z.value) ∧
      (complexExpNameApprox z (n + 1)).Subinterval (complexExpNameApprox z n) := by
  induction n with
  | zero =>
      have h0 := complexExpStage_sound z 0
      have h1 := complexExpStage_sound z 1
      exact ⟨h0, (ComplexRatInterval.tighten_sound_left h0 h1).2⟩
  | succ n ih =>
      have hnew := complexExpStage_sound z (n + 1)
      have hcur : (complexExpNameApprox z (n + 1)).Contains
          (Complex.exp z.value) := by
        rw [complexExpNameApprox]
        exact (ComplexRatInterval.tighten_sound_left ih.1 hnew).1
      have hnext := complexExpStage_sound z (n + 2)
      constructor
      · exact hcur
      · rw [show n + 1 + 1 = n + 2 by omega, complexExpNameApprox]
        exact (ComplexRatInterval.tighten_sound_left hcur hnext).2

private theorem complexExpNameApprox_subinterval_stage (z : CertifiedComplex) (n : ℕ) :
    (complexExpNameApprox z n).Subinterval (complexExpStage z n) := by
  cases n with
  | zero => exact ⟨RatInterval.subinterval_refl _, RatInterval.subinterval_refl _⟩
  | succ n =>
      rw [complexExpNameApprox]
      have hprev := (complexExpNameApprox_spec z n).1
      have hstage := complexExpStage_sound z (n + 1)
      exact ⟨
        Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Transcendental.tighten_subinterval_right
          hprev.1 hstage.1,
        Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Transcendental.tighten_subinterval_right
          hprev.2 hstage.2⟩

private theorem complexApprox_subinterval_of_le (z : CertifiedComplex) {m k : ℕ}
    (hmk : m ≤ k) : (z.approx k).Subinterval (z.approx m) := by
  induction k, hmk using Nat.le_induction with
  | base => exact ⟨RatInterval.subinterval_refl _, RatInterval.subinterval_refl _⟩
  | succ k hmk ih =>
      exact ⟨RatInterval.subinterval_trans (z.nested k).1 ih.1,
        RatInterval.subinterval_trans (z.nested k).2 ih.2⟩

private theorem expScalar_subinterval_of_le (q : ℚ) {m k : ℕ} (hmk : m ≤ k) :
    (Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Transcendental.expScalar
      q k).Subinterval
    (Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Transcendental.expScalar
      q m) := by
  induction k, hmk using Nat.le_induction with
  | base => exact RatInterval.subinterval_refl _
  | succ k hmk ih =>
      exact RatInterval.subinterval_trans
        (Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Transcendental.expScalar_nested
          q k) ih

private theorem ratMaxAbs_mono {I J : RatInterval} (hIJ : I.Subinterval J) :
    I.maxAbs ≤ J.maxAbs := by
  apply max_le
  · exact abs_le_max_abs_abs hIJ.1 (I.lo_le_hi.trans hIJ.2)
  · exact abs_le_max_abs_abs (hIJ.1.trans I.lo_le_hi) hIJ.2

private theorem ratMaxAbs_le_of_contains {I : RatInterval} {x : ℝ} {C w : ℚ}
    (hx : I.Contains x) (hC : |x| ≤ (C : ℝ)) (hw : I.width ≤ w)
    (hC0 : 0 ≤ C) (hw0 : 0 ≤ w) : I.maxAbs ≤ C + w := by
  have hw' : ((I.hi : ℝ) - I.lo) ≤ w := by
    exact_mod_cast hw
  have hC' : -(C : ℝ) ≤ x ∧ x ≤ (C : ℝ) := (abs_le.mp hC)
  have hloLower : -((C : ℝ) + w) ≤ I.lo := by
    nlinarith [hC'.1, hx.2, hw']
  have hloUpper : (I.lo : ℝ) ≤ C + w := by
    have hw0' : (0 : ℝ) ≤ w := by exact_mod_cast hw0
    linarith [hx.1, hC'.2]
  have hhiLower : -((C : ℝ) + w) ≤ I.hi := by
    have hw0' : (0 : ℝ) ≤ w := by exact_mod_cast hw0
    linarith [hx.2, hC'.1]
  have hhiUpper : (I.hi : ℝ) ≤ C + w := by
    nlinarith [hx.1, hC'.2, hw']
  have hloLower' : -(((C + w : ℚ) : ℝ)) ≤ I.lo := by
    norm_num at hloLower ⊢
    exact hloLower
  have hhiLower' : -(((C + w : ℚ) : ℝ)) ≤ I.hi := by
    norm_num at hhiLower ⊢
    exact hhiLower
  have hloUpper' : (I.lo : ℝ) ≤ ((C + w : ℚ) : ℝ) := by
    norm_num at hloUpper ⊢
    exact hloUpper
  have hhiUpper' : (I.hi : ℝ) ≤ ((C + w : ℚ) : ℝ) := by
    norm_num at hhiUpper ⊢
    exact hhiUpper
  have hlo : |(I.lo : ℝ)| ≤ (C + w : ℚ) := (abs_le.mpr ⟨hloLower', hloUpper'⟩)
  have hhi : |(I.hi : ℝ)| ≤ (C + w : ℚ) := (abs_le.mpr ⟨hhiLower', hhiUpper'⟩)
  exact_mod_cast (max_le hlo hhi)

set_option maxHeartbeats 2000000 in
/-- Every scheduled stage has width at most its reciprocal stage tolerance;
the proof combines input refinement, scalar Taylor convergence, magnitude
amplification, and explicit rectangle-product propagation. -/
theorem complexExpStage_width (z : CertifiedComplex) (n : ℕ) :
    (complexExpStage z n).width ≤ (complexExpStageTolerance n).1 := by
  -- Let η be the stage tolerance, B the initial exponential magnitude scale,
  -- τ = η/(16B), α = τ/8, and K the scheduled input. Nestedness of `z`
  -- gives `K ⊆ z.approx 0`, while `z.width_modulus` gives `width K ≤ τ/(4B)`.
  -- Use `power_div_factorial_le` for the sine/cosine errors and
  -- `expScalar_width` plus scalar nestedness for both exponential calls.
  -- Bound each factor's `maxAbs` from one contained exact value plus its width,
  -- feed those estimates to `complexExp_width`, and finish the deliberately
  -- loose constants by `nlinarith`/`field_simp` using η ≤ 1 and B ≥ 2.
  let η : ℚ := (complexExpStageTolerance n).1
  let B : ℚ := complexExpMagnitude z
  let τ : ℚ := (complexExpInnerTolerance z n).1
  let α : PosRat := ⟨τ / 8, by
    change 0 < (complexExpInnerTolerance z n).1 / 8
    exact div_pos (complexExpInnerTolerance z n).2 (by norm_num)⟩
  let K : ComplexRatInterval := complexExpStageInput z n
  let N : ℕ := complexExpStageFuel z n
  let d : ℕ := α.1.den + 1
  let A : ℕ := (intervalMid K.im).num.natAbs + 2
  let S0 :=
    Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Transcendental.expScalar
      (z.approx 0).re.maxAbs 0
  let E := expInterval K.re N
  let C := cosInterval K.im N
  let S := sinInterval K.im N
  have hηpos : 0 < η := by
    dsimp [η, complexExpStageTolerance]
    positivity
  have hηone : η ≤ 1 := by
    dsimp [η, complexExpStageTolerance]
    apply (div_le_iff₀ (by positivity : (0 : ℚ) < (n : ℚ) + 1)).2
    norm_num
  have hB : 2 ≤ B := by
    dsimp [B, complexExpMagnitude, S0]
    linarith [abs_nonneg
      ((Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Transcendental.expScalar
        (z.approx 0).re.maxAbs 0).hi)]
  have hBpos : 0 < B := lt_of_lt_of_le (by norm_num) hB
  have hτeq : τ = η / (16 * B) := by
    rfl
  have hαeq : α.1 = τ / 8 := by rfl
  have hτpos : 0 < τ := by rw [hτeq]; positivity
  have hτone : τ ≤ 1 := by
    rw [hτeq]
    apply (div_le_iff₀ (by positivity : (0 : ℚ) < 16 * B)).2
    nlinarith [hηone]
  have hαpos : 0 < α.1 := α.2
  have hαone : α.1 ≤ 1 := by rw [hαeq]; nlinarith [hτone]
  have hK0 : K.Subinterval (z.approx 0) := by
    dsimp [K, complexExpStageInput]
    exact complexApprox_subinterval_of_le z (Nat.zero_le _)
  have hKw : K.width ≤ τ / (4 * B) := by
    have hm := z.width_modulus (complexExpInputTolerance z n)
    simpa [K, complexExpStageInput, complexExpInputTolerance, τ] using hm
  have hKrew : K.re.width ≤ τ / (4 * B) := (le_max_left _ _).trans hKw
  have hKimw : K.im.width ≤ τ / (4 * B) := (le_max_right _ _).trans hKw
  have hNtrig : 32 * d * A ^ 2 ≤ N := by
    dsimp [N, complexExpStageFuel, d, A, α, K]
    exact le_max_left _ _
  have hNexpMid :
      Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Transcendental.expPrecision
        (intervalMid K.re) α ≤ N := by
    dsimp [N, complexExpStageFuel, K, α]
    exact (le_max_left _ _).trans (le_max_right _ _)
  have hNexpAbs :
      Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Transcendental.expPrecision
        K.re.maxAbs α ≤ N := by
    dsimp [N, complexExpStageFuel, K, α]
    exact (le_max_right _ _).trans (le_max_right _ _)
  have hAone : 1 ≤ A := by dsimp [A]; omega
  have hdone : 1 ≤ d := by dsimp [d]; omega
  have hmidA : |intervalMid K.im| ≤ (A : ℚ) := by
    have hdq : (0 : ℚ) < (intervalMid K.im).den := by
      exact_mod_cast (intervalMid K.im).den_pos
    have hnum : |intervalMid K.im| ≤
        ((intervalMid K.im).num.natAbs : ℚ) := by
      calc
        |intervalMid K.im| =
            |((intervalMid K.im).num : ℚ) / ((intervalMid K.im).den : ℚ)| := by
              rw [Rat.num_div_den]
        _ = ((intervalMid K.im).num.natAbs : ℚ) /
            (intervalMid K.im).den := by
              rw [abs_div, abs_of_pos hdq]
              norm_num
        _ ≤ ((intervalMid K.im).num.natAbs : ℕ) := by
          apply (div_le_iff₀ hdq).2
          have hd1 : (1 : ℚ) ≤ (intervalMid K.im).den := by
            exact_mod_cast (intervalMid K.im).den_pos
          nlinarith
    calc
      |intervalMid K.im| ≤ ((intervalMid K.im).num.natAbs : ℕ) := hnum
      _ ≤ A := by exact_mod_cast Nat.le_add_right (intervalMid K.im).num.natAbs 2
  have hsinErr : sinError (intervalMid K.im) N ≤ α.1 / 4 := by
    have hp := power_div_factorial_le (intervalMid K.im) A d N 3 hmidA hAone hdone
      (by omega) hNtrig
    have hinv : 1 / (d : ℚ) ≤ α.1 := by
      exact (div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (by dsimp [d]; exact_mod_cast Nat.le_succ α.1.den)).trans
          (Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Transcendental.inv_den_le_of_pos
            α.1 α.2)
    calc
      _ ≤ 1 / ((4 * d : ℕ) : ℚ) := by simpa [sinError] using hp
      _ = (1 / (d : ℚ)) / 4 := by push_cast; field_simp
      _ ≤ α.1 / 4 := div_le_div_of_nonneg_right hinv (by norm_num)
  have hcosErr : cosError (intervalMid K.im) N ≤ α.1 / 4 := by
    have hp := power_div_factorial_le (intervalMid K.im) A d N 2 hmidA hAone hdone
      (by omega) hNtrig
    have hinv : 1 / (d : ℚ) ≤ α.1 := by
      exact (div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (by dsimp [d]; exact_mod_cast Nat.le_succ α.1.den)).trans
          (Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Transcendental.inv_den_le_of_pos
            α.1 α.2)
    calc
      _ ≤ 1 / ((4 * d : ℕ) : ℚ) := by simpa [cosError] using hp
      _ = (1 / (d : ℚ)) / 4 := by push_cast; field_simp
      _ ≤ α.1 / 4 := div_le_div_of_nonneg_right hinv (by norm_num)
  have hCw : C.width ≤ τ := by
    have h := cosInterval_width K.im N
    dsimp [C]
    rw [hαeq] at hcosErr
    have hdiv : τ / (4 * B) ≤ τ / 8 := by
      apply div_le_div_of_nonneg_left hτpos.le (by norm_num)
      nlinarith
    nlinarith
  have hSw : S.width ≤ τ := by
    have h := sinInterval_width K.im N
    dsimp [S]
    rw [hαeq] at hsinErr
    have hdiv : τ / (4 * B) ≤ τ / 8 := by
      apply div_le_div_of_nonneg_left hτpos.le (by norm_num)
      nlinarith
    nlinarith
  have hscalarMid :
      (Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Transcendental.expScalar
        (intervalMid K.re) N).width ≤ α.1 := by
    exact (RatInterval.width_mono
      (expScalar_subinterval_of_le (intervalMid K.re) hNexpMid)).trans
        (Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Transcendental.expScalar_width
          (intervalMid K.re) α)
  have hscalarAbs :
      (Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Transcendental.expScalar
        K.re.maxAbs N).width ≤ α.1 := by
    exact (RatInterval.width_mono
      (expScalar_subinterval_of_le K.re.maxAbs hNexpAbs)).trans
        (Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Transcendental.expScalar_width
          K.re.maxAbs α)
  have hKabs : K.re.maxAbs ≤ (z.approx 0).re.maxAbs := ratMaxAbs_mono hK0.1
  have hmidK : K.re.Contains (intervalMid K.re : ℝ) := by
    constructor <;> exact_mod_cast (by
      dsimp [intervalMid]
      linarith [K.re.lo_le_hi])
  have hmidM : (intervalMid K.re : ℝ) ≤ (z.approx 0).re.maxAbs := by
    exact_mod_cast (le_trans (le_abs_self _) ((abs_le_max_abs_abs
      (by exact_mod_cast hmidK.1) (by exact_mod_cast hmidK.2)).trans hKabs))
  have hvalM : z.value.re ≤ ((z.approx 0).re.maxAbs : ℚ) := by
    have hz0 := (z.contains 0).1
    exact (le_abs_self _).trans (by exact_mod_cast abs_le_max_abs_abs hz0.1 hz0.2)
  have hS0 :=
    Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Transcendental.expScalar_sound
      (z.approx 0).re.maxAbs 0
  have hS0hi0 : 0 ≤ S0.hi := by
    dsimp [S0]
    exact_mod_cast (Real.exp_pos ((z.approx 0).re.maxAbs : ℝ)).le.trans hS0.2
  have hUpper :
      (Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Transcendental.expScalar
        K.re.maxAbs N).hi ≤ B := by
    change
      (Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Transcendental.expScalar
        K.re.maxAbs N).hi ≤ |S0.hi| + 2
    have hUs :=
      Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Transcendental.expScalar_sound
        K.re.maxAbs N
    have hexp : Real.exp (K.re.maxAbs : ℝ) ≤ Real.exp ((z.approx 0).re.maxAbs : ℝ) :=
      Real.exp_le_exp.mpr (by exact_mod_cast hKabs)
    have hUhi :
        ((Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Transcendental.expScalar
          K.re.maxAbs N).hi : ℝ) ≤ Real.exp (K.re.maxAbs : ℝ) + α.1 := by
      have hw :
          (((Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Transcendental.expScalar
            K.re.maxAbs N).hi : ℝ) -
          (Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Transcendental.expScalar
            K.re.maxAbs N).lo) ≤ α.1 := by
        exact_mod_cast hscalarAbs
      nlinarith [hUs.1]
    have hUS0 :
        ((Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Transcendental.expScalar
          K.re.maxAbs N).hi : ℝ) ≤ (S0.hi : ℝ) + α.1 := by
      nlinarith [hS0.2]
    have hUS0q :
        (Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Transcendental.expScalar
          K.re.maxAbs N).hi ≤ S0.hi + α.1 := by
      exact_mod_cast hUS0
    exact hUS0q.trans (by
      rw [abs_of_nonneg hS0hi0]
      nlinarith [hαone])
  have hEw : E.width ≤ τ := by
    have h := expInterval_width K.re N
    dsimp [E]
    rw [show intervalRadius K.re = K.re.width / 2 by rfl] at h
    rw [hαeq] at hscalarMid
    have hprod :
        (Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Transcendental.expScalar
          K.re.maxAbs N).hi * K.re.width ≤ τ / 4 := by
      have hu0 : 0 ≤
          (Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Transcendental.expScalar
            K.re.maxAbs N).hi := by
        exact_mod_cast (Real.exp_pos (K.re.maxAbs : ℝ)).le.trans
          (Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Transcendental.expScalar_sound
            K.re.maxAbs N).2
      have := mul_le_mul hUpper hKrew (RatInterval.width_nonneg K.re) hBpos.le
      calc
        _ ≤ B * (τ / (4 * B)) := this
        _ = τ / 4 := by field_simp
    nlinarith
  have hEcontains : E.Contains (Real.exp z.value.re) := by
    exact expInterval_sound (z.contains _).1 N
  have hEabs : E.maxAbs ≤ B := by
    have hexp : Real.exp z.value.re ≤ (S0.hi : ℝ) :=
      (Real.exp_le_exp.mpr hvalM).trans hS0.2
    have h := ratMaxAbs_le_of_contains hEcontains
      (by rw [Real.abs_exp]; exact hexp.trans (by exact_mod_cast le_abs_self S0.hi))
      hEw (abs_nonneg S0.hi) hτpos.le
    change E.maxAbs ≤ |S0.hi| + 2
    exact h.trans (by nlinarith [hτone])
  have hCcontains : C.Contains (Real.cos z.value.im) :=
    cosInterval_sound (z.contains _).2 N
  have hScontains : S.Contains (Real.sin z.value.im) :=
    sinInterval_sound (z.contains _).2 N
  have hCabs : C.maxAbs ≤ 2 := by
    exact (ratMaxAbs_le_of_contains (C := (1 : ℚ)) (w := τ)
      hCcontains (by simpa using Real.abs_cos_le_one z.value.im) hCw
      (by norm_num) hτpos.le).trans (by nlinarith [hτone])
  have hSabs : S.maxAbs ≤ 2 := by
    exact (ratMaxAbs_le_of_contains (C := (1 : ℚ)) (w := τ)
      hScontains (by simpa using Real.abs_sin_le_one z.value.im) hSw
      (by norm_num) hτpos.le).trans (by nlinarith [hτone])
  have hout := complexExp_width K N
  change (complexExp K N).width ≤ η
  have hEA0 : 0 ≤ E.maxAbs := (abs_nonneg E.lo).trans (le_max_left _ _)
  have hCA0 : 0 ≤ C.maxAbs := (abs_nonneg C.lo).trans (le_max_left _ _)
  have hSA0 : 0 ≤ S.maxAbs := (abs_nonneg S.lo).trans (le_max_left _ _)
  have hEw0 := RatInterval.width_nonneg E
  have hCw0 := RatInterval.width_nonneg C
  have hSw0 := RatInterval.width_nonneg S
  have hout' : (complexExp K N).width ≤
      2 * (E.maxAbs * max C.width S.width +
        max C.maxAbs S.maxAbs * E.width) := by
    simpa [E, C, S, max_eq_left hEA0, max_eq_left hEw0] using hout
  have hmaxW : max C.width S.width ≤ τ := max_le hCw hSw
  have hmaxA : max C.maxAbs S.maxAbs ≤ 2 := max_le hCabs hSabs
  have hmaxW0 : 0 ≤ max C.width S.width := hCw0.trans (le_max_left _ _)
  have hbound :
      2 * (E.maxAbs * max C.width S.width +
        max C.maxAbs S.maxAbs * E.width) ≤ 2 * (B * τ + 2 * τ) := by
    nlinarith [mul_le_mul hEabs hmaxW hmaxW0 hBpos.le,
      mul_le_mul hmaxA hEw hEw0 (by norm_num : (0 : ℚ) ≤ 2)]
  exact hout'.trans (hbound.trans (by
    have heq : τ * (16 * B) = η := by
      rw [hτeq]
      field_simp
    have hBτ : 2 * τ ≤ B * τ :=
      mul_le_mul_of_nonneg_right hB hτpos.le
    nlinarith [mul_nonneg hBpos.le hτpos.le]))

/-- The denominator of a requested rational tolerance selects a stage whose
canonical reciprocal target is no larger than that tolerance. -/
def complexExpPrecision (_z : CertifiedComplex) (ε : PosRat) : ℕ := ε.1.den

/-- For [a certified complex input](hyp:z) and [a requested positive rational tolerance
`ε`](hyp:ε), [evaluating the certified complex-exponential approximation at the precision
level selected for that tolerance yields an output enclosure whose width is no larger than
`ε`](goal). -/
theorem complexExp_width_at_precision (z : CertifiedComplex) (ε : PosRat) :
    (complexExpNameApprox z (complexExpPrecision z ε)).width ≤ ε.1 := by
  -- The recursive name approximation is a subrectangle of its current stage.
  -- Apply `complexExpStage_width`, unfold the denominator-selected precision,
  -- and finish with `inv_den_le_of_pos` (using denominator + 1 ≤ denominator
  -- only in the correct reciprocal direction).
  let N := complexExpPrecision z ε
  have hsub := complexExpNameApprox_subinterval_stage z N
  have hmono : (complexExpNameApprox z N).width ≤ (complexExpStage z N).width :=
    max_le_max (RatInterval.width_mono hsub.1) (RatInterval.width_mono hsub.2)
  have hstage := complexExpStage_width z N
  have hrecip : (complexExpStageTolerance N).1 ≤ 1 / (ε.1.den : ℚ) := by
    dsimp [complexExpStageTolerance, N, complexExpPrecision]
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (by exact_mod_cast Nat.le_succ ε.1.den)
  exact hmono.trans (hstage.trans (hrecip.trans
    (Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Transcendental.inv_den_le_of_pos
      ε.1 ε.2)))

/-- Complex exponential lifts a certified complex input to a certified complex
output without storing exact values in any returned rectangle. -/
noncomputable def complexExpName (z : CertifiedComplex) : CertifiedComplex where
  value := Complex.exp z.value
  approx := complexExpNameApprox z
  nested := fun n => (complexExpNameApprox_spec z n).2
  contains := by intro n; exact (complexExpNameApprox_spec z n).1
  modulus := complexExpPrecision z
  width_modulus := complexExp_width_at_precision z

end Transcendental

end Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Complex
