import Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Complex.Transcendental

/-!
# Certified sine and cosine names

This module turns refining rational real names into certified sine and cosine names with effective Taylor-error bounds.
-/

namespace Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Complex

open Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic

namespace Transcendental

/-- A sine output on a refining real name recursively intersects the current
input enclosure result with every preceding output. -/
def sinNameApprox (x : CertifiedReal) : ℕ → RatInterval
  | 0 => sinInterval (x.approx 0) 0
  | fuel + 1 => (sinNameApprox x fuel).tighten
      (sinInterval (x.approx (fuel + 1)) (fuel + 1))

/-- A cosine output on a refining real name recursively intersects the current
input enclosure result with every preceding output. -/
def cosNameApprox (x : CertifiedReal) : ℕ → RatInterval
  | 0 => cosInterval (x.approx 0) 0
  | fuel + 1 => (cosNameApprox x fuel).tighten
      (cosInterval (x.approx (fuel + 1)) (fuel + 1))

/-- Conservative trigonometric precision combines the input modulus, initial
argument magnitude, and target denominator. -/
def trigNamePrecision (x : CertifiedReal) (ε : PosRat) : ℕ :=
  let δ : PosRat := ⟨ε.1 / 2, div_pos ε.2 (by norm_num)⟩
  max (x.modulus δ)
    (32 * (ε.1.den + 1) * ((x.approx 0).maxAbs.num.natAbs + 2) ^ 2)

/-- Recursive sine-name approximations remain sound and adjacent-fuel nested. -/
theorem sinNameApprox_spec (x : CertifiedReal) (fuel : ℕ) :
    (sinNameApprox x fuel).Contains (Real.sin x.value) ∧
      (sinNameApprox x (fuel + 1)).Subinterval (sinNameApprox x fuel) := by
  induction fuel with
  | zero =>
      have h0 := sinInterval_sound (x.contains 0) 0
      have h1 := sinInterval_sound (x.contains 1) 1
      exact ⟨h0, RatInterval.tighten_subinterval_left h0 h1⟩
  | succ fuel ih =>
      have hnew := sinInterval_sound (x.contains (fuel + 1)) (fuel + 1)
      have hcur : (sinNameApprox x (fuel + 1)).Contains (Real.sin x.value) := by
        rw [sinNameApprox]
        exact RatInterval.tighten_sound ih.1 hnew
      have hnext := sinInterval_sound (x.contains (fuel + 2)) (fuel + 2)
      constructor
      · exact hcur
      · rw [show fuel + 1 + 1 = fuel + 2 by omega, sinNameApprox]
        exact RatInterval.tighten_subinterval_left hcur hnext

/-- Recursive cosine-name approximations remain sound and adjacent-fuel nested. -/
theorem cosNameApprox_spec (x : CertifiedReal) (fuel : ℕ) :
    (cosNameApprox x fuel).Contains (Real.cos x.value) ∧
      (cosNameApprox x (fuel + 1)).Subinterval (cosNameApprox x fuel) := by
  induction fuel with
  | zero =>
      have h0 := cosInterval_sound (x.contains 0) 0
      have h1 := cosInterval_sound (x.contains 1) 1
      exact ⟨h0, RatInterval.tighten_subinterval_left h0 h1⟩
  | succ fuel ih =>
      have hnew := cosInterval_sound (x.contains (fuel + 1)) (fuel + 1)
      have hcur : (cosNameApprox x (fuel + 1)).Contains (Real.cos x.value) := by
        rw [cosNameApprox]
        exact RatInterval.tighten_sound ih.1 hnew
      have hnext := cosInterval_sound (x.contains (fuel + 2)) (fuel + 2)
      constructor
      · exact hcur
      · rw [show fuel + 1 + 1 = fuel + 2 by omega, cosNameApprox]
        exact RatInterval.tighten_subinterval_left hcur hnext

private theorem factorial_power_bound (A d N r : ℕ) (hA : 1 ≤ A) (hd : 1 ≤ d)
    (hr : 1 ≤ r) (hN : 32 * d * A ^ 2 ≤ N) :
    4 * d * A ^ (2 * N + r) ≤ (2 * N + r).factorial := by
  have hbase0 : 4 * d * A ^ 2 ≤ 32 * d * A ^ 2 := by gcongr <;> omega
  have hbase : 4 * d * A ^ 2 ≤ N + 1 := hbase0.trans (hN.trans (Nat.le_succ N))
  have hpow : (4 * d * A ^ 2) ^ (N + r) ≤ (N + 1) ^ (N + r) :=
    Nat.pow_le_pow_left hbase (N + r)
  have hleft : 4 * d * A ^ (2 * N + r) ≤ (4 * d * A ^ 2) ^ (N + r) := by
    rw [show 4 * d * A ^ 2 = (4 * d) * A ^ 2 by ring, mul_pow, ← pow_mul]
    have h4d : 4 * d ≤ (4 * d) ^ (N + r) := by
      calc
        4 * d = (4 * d) ^ 1 := by simp
        _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
    have hApow : A ^ (2 * N + r) ≤ A ^ (2 * (N + r)) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    exact Nat.mul_le_mul h4d hApow
  calc
    _ ≤ (N + 1) ^ (N + r) := hleft.trans hpow
    _ ≤ N.factorial * (N + 1) ^ (N + r) :=
      Nat.le_mul_of_pos_left _ (Nat.factorial_pos N)
    _ ≤ _ := by
      have h := @Nat.factorial_mul_pow_le_factorial N (N + r)
      rw [show N + (N + r) = 2 * N + r by omega] at h
      exact h

/-- If the Taylor fuel dominates a rational magnitude and denominator scale,
the corresponding rational power-over-factorial remainder is explicitly small. -/
theorem power_div_factorial_le (q : ℚ) (A d N r : ℕ)
    (hq : |q| ≤ A) (hA : 1 ≤ A) (hd : 1 ≤ d) (hr : 1 ≤ r)
    (hN : 32 * d * A ^ 2 ≤ N) :
    |q| ^ (2 * N + r) / ((2 * N + r).factorial : ℚ) ≤ 1 / (4 * d : ℕ) := by
  have hp : |q| ^ (2 * N + r) ≤ (A : ℚ) ^ (2 * N + r) :=
    pow_le_pow_left₀ (abs_nonneg q) hq _
  have hf : (4 * d : ℚ) * (A : ℚ) ^ (2 * N + r) ≤
      ((2 * N + r).factorial : ℚ) := by
    exact_mod_cast factorial_power_bound A d N r hA hd hr hN
  apply (div_le_div_iff₀ (by positivity : (0 : ℚ) < (2 * N + r).factorial)
    (by positivity : (0 : ℚ) < (4 * d : ℕ))).2
  calc
    |q| ^ (2 * N + r) * (4 * d : ℕ) ≤
        (A : ℚ) ^ (2 * N + r) * (4 * d : ℕ) :=
      mul_le_mul_of_nonneg_right hp (by positivity)
    _ = (4 * d : ℚ) * (A : ℚ) ^ (2 * N + r) := by
      push_cast
      ring
    _ ≤ ((2 * N + r).factorial : ℚ) := hf
    _ = 1 * ((2 * N + r).factorial : ℚ) := by ring

private theorem sinNameApprox_subinterval_current (x : CertifiedReal) (fuel : ℕ) :
    (sinNameApprox x fuel).Subinterval (sinInterval (x.approx fuel) fuel) := by
  cases fuel with
  | zero => exact RatInterval.subinterval_refl _
  | succ fuel =>
      rw [sinNameApprox]
      exact Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Transcendental.tighten_subinterval_right
        (sinNameApprox_spec x fuel).1 (sinInterval_sound (x.contains (fuel + 1)) (fuel + 1))

private theorem cosNameApprox_subinterval_current (x : CertifiedReal) (fuel : ℕ) :
    (cosNameApprox x fuel).Subinterval (cosInterval (x.approx fuel) fuel) := by
  cases fuel with
  | zero => exact RatInterval.subinterval_refl _
  | succ fuel =>
      rw [cosNameApprox]
      exact Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Transcendental.tighten_subinterval_right
        (cosNameApprox_spec x fuel).1 (cosInterval_sound (x.contains (fuel + 1)) (fuel + 1))

/-- For [a certified real input](hyp:x) and [a requested positive rational tolerance
`ε`](hyp:ε), [evaluating the certified sine name-approximation at the precision level
selected for that tolerance yields an output enclosure whose width is no larger than
`ε`](goal). -/
theorem sinName_width_at_precision (x : CertifiedReal) (ε : PosRat) :
    (sinNameApprox x (trigNamePrecision x ε)).width ≤ ε.1 := by
  let δ : PosRat := ⟨ε.1 / 2, div_pos ε.2 (by norm_num)⟩
  let d : ℕ := ε.1.den + 1
  let A : ℕ := (x.approx 0).maxAbs.num.natAbs + 2
  let N : ℕ := trigNamePrecision x ε
  let K := x.approx N
  have hmod : x.modulus δ ≤ N := by exact le_max_left _ _
  have hN : 32 * d * A ^ 2 ≤ N := by exact le_max_right _ _
  have hKw : K.width ≤ δ.1 :=
    (RatInterval.width_mono (CertifiedReal.approx_mono x hmod)).trans (x.width_modulus δ)
  have hKK0 : K.Subinterval (x.approx 0) := CertifiedReal.approx_mono x (Nat.zero_le N)
  have hmidK : K.Contains (intervalMid K : ℝ) := by
    constructor <;> exact_mod_cast (by
      dsimp [intervalMid]
      linarith [K.lo_le_hi])
  have hmid0 := RatInterval.Contains.mono hKK0 hmidK
  have hM0 : 0 ≤ (x.approx 0).maxAbs :=
    (abs_nonneg (x.approx 0).lo).trans (le_max_left _ _)
  have hMle : (x.approx 0).maxAbs ≤ ((x.approx 0).maxAbs.num.natAbs : ℕ) := by
    have hn0 : 0 ≤ (x.approx 0).maxAbs.num := Rat.num_nonneg.mpr hM0
    calc
      (x.approx 0).maxAbs =
          ((x.approx 0).maxAbs.num : ℚ) / ((x.approx 0).maxAbs.den : ℕ) :=
        (Rat.num_div_den _).symm
      _ ≤ ((x.approx 0).maxAbs.num : ℚ) :=
        div_le_self (by exact_mod_cast hn0) (by exact_mod_cast Rat.den_pos _)
      _ = ((x.approx 0).maxAbs.num.natAbs : ℕ) := by
        have hi : ((x.approx 0).maxAbs.num.natAbs : ℤ) =
            (x.approx 0).maxAbs.num := Int.natAbs_of_nonneg hn0
        exact (congrArg (fun z : ℤ => (z : ℚ)) hi).symm
  have hmidA : |intervalMid K| ≤ (A : ℚ) := by
    exact (abs_le_max_abs_abs (by exact_mod_cast hmid0.1) (by exact_mod_cast hmid0.2)).trans
      (hMle.trans (by exact_mod_cast Nat.le_add_right (x.approx 0).maxAbs.num.natAbs 2))
  have herr : sinError (intervalMid K) N ≤ 1 / (4 * d : ℕ) := by
    simpa [sinError] using power_div_factorial_le (intervalMid K) A d N 3 hmidA
      (by dsimp [A]; omega) (by dsimp [d]; omega) (by omega) hN
  have hinv : 1 / (d : ℚ) ≤ ε.1 := by
    exact (div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (by dsimp [d]; exact_mod_cast Nat.le_succ ε.1.den)).trans
        (Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Transcendental.inv_den_le_of_pos
          ε.1 ε.2)
  have hcur := sinInterval_width K N
  have hout := RatInterval.width_mono (sinNameApprox_subinterval_current x N)
  have herr' : sinError (intervalMid K) N ≤ ε.1 / 4 := by
    calc
      _ ≤ (1 : ℚ) / ((4 * d : ℕ) : ℚ) := herr
      _ = (1 / (d : ℚ)) / 4 := by push_cast; field_simp
      _ ≤ _ := div_le_div_of_nonneg_right hinv (by norm_num)
  dsimp [δ] at hKw
  exact hout.trans (hcur.trans (by nlinarith [herr']))

/-- Refinement of the input name plus Taylor fuel makes cosine output width effective. -/
theorem cosName_width_at_precision (x : CertifiedReal) (ε : PosRat) :
    (cosNameApprox x (trigNamePrecision x ε)).width ≤ ε.1 := by
  let δ : PosRat := ⟨ε.1 / 2, div_pos ε.2 (by norm_num)⟩
  let d : ℕ := ε.1.den + 1
  let A : ℕ := (x.approx 0).maxAbs.num.natAbs + 2
  let N : ℕ := trigNamePrecision x ε
  let K := x.approx N
  have hmod : x.modulus δ ≤ N := by exact le_max_left _ _
  have hN : 32 * d * A ^ 2 ≤ N := by exact le_max_right _ _
  have hKw : K.width ≤ δ.1 :=
    (RatInterval.width_mono (CertifiedReal.approx_mono x hmod)).trans (x.width_modulus δ)
  have hKK0 : K.Subinterval (x.approx 0) := CertifiedReal.approx_mono x (Nat.zero_le N)
  have hmidK : K.Contains (intervalMid K : ℝ) := by
    constructor <;> exact_mod_cast (by
      dsimp [intervalMid]
      linarith [K.lo_le_hi])
  have hmid0 := RatInterval.Contains.mono hKK0 hmidK
  have hM0 : 0 ≤ (x.approx 0).maxAbs :=
    (abs_nonneg (x.approx 0).lo).trans (le_max_left _ _)
  have hMle : (x.approx 0).maxAbs ≤ ((x.approx 0).maxAbs.num.natAbs : ℕ) := by
    have hn0 : 0 ≤ (x.approx 0).maxAbs.num := Rat.num_nonneg.mpr hM0
    calc
      (x.approx 0).maxAbs =
          ((x.approx 0).maxAbs.num : ℚ) / ((x.approx 0).maxAbs.den : ℕ) :=
        (Rat.num_div_den _).symm
      _ ≤ ((x.approx 0).maxAbs.num : ℚ) :=
        div_le_self (by exact_mod_cast hn0) (by exact_mod_cast Rat.den_pos _)
      _ = ((x.approx 0).maxAbs.num.natAbs : ℕ) := by
        have hi : ((x.approx 0).maxAbs.num.natAbs : ℤ) =
            (x.approx 0).maxAbs.num := Int.natAbs_of_nonneg hn0
        exact (congrArg (fun z : ℤ => (z : ℚ)) hi).symm
  have hmidA : |intervalMid K| ≤ (A : ℚ) := by
    exact (abs_le_max_abs_abs (by exact_mod_cast hmid0.1) (by exact_mod_cast hmid0.2)).trans
      (hMle.trans (by exact_mod_cast Nat.le_add_right (x.approx 0).maxAbs.num.natAbs 2))
  have herr : cosError (intervalMid K) N ≤ 1 / (4 * d : ℕ) := by
    simpa [cosError] using power_div_factorial_le (intervalMid K) A d N 2 hmidA
      (by dsimp [A]; omega) (by dsimp [d]; omega) (by omega) hN
  have hinv : 1 / (d : ℚ) ≤ ε.1 := by
    exact (div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (by dsimp [d]; exact_mod_cast Nat.le_succ ε.1.den)).trans
        (Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Transcendental.inv_den_le_of_pos
          ε.1 ε.2)
  have hcur := cosInterval_width K N
  have hout := RatInterval.width_mono (cosNameApprox_subinterval_current x N)
  have herr' : cosError (intervalMid K) N ≤ ε.1 / 4 := by
    calc
      _ ≤ (1 : ℚ) / ((4 * d : ℕ) : ℚ) := herr
      _ = (1 / (d : ℚ)) / 4 := by push_cast; field_simp
      _ ≤ _ := div_le_div_of_nonneg_right hinv (by norm_num)
  dsimp [δ] at hKw
  exact hout.trans (hcur.trans (by nlinarith [herr']))

/-- Sine lifts a refining certified real input to a certified real output. -/
noncomputable def sinName (x : CertifiedReal) : CertifiedReal where
  value := Real.sin x.value
  approx := sinNameApprox x
  nested := fun fuel => (sinNameApprox_spec x fuel).2
  contains := by intro fuel; exact (sinNameApprox_spec x fuel).1
  modulus := trigNamePrecision x
  width_modulus := sinName_width_at_precision x

/-- Cosine lifts a refining certified real input to a certified real output. -/
noncomputable def cosName (x : CertifiedReal) : CertifiedReal where
  value := Real.cos x.value
  approx := cosNameApprox x
  nested := fun fuel => (cosNameApprox_spec x fuel).2
  contains := by intro fuel; exact (cosNameApprox_spec x fuel).1
  modulus := trigNamePrecision x
  width_modulus := cosName_width_at_precision x

end Transcendental

end Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Complex
