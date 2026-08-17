import Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Exponential
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Rat.BigOperators

/-!
# Certified rational logarithm enclosures

This module computes nested rational intervals for the logarithm of a positive
rational input.  The atanh series and an explicit geometric remainder bound
produce a certified real name with a computable precision for every positive
rational error target.
-/

namespace Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic
namespace Transcendental

/-- The atanh coordinate sends every positive rational logarithm argument into
the open interval from minus one to one. -/
def logCoordinate (q : ℚ) : ℚ := (q - 1) / (q + 1)

/-- The rational logarithm polynomial retains the first requested number of
terms of twice the atanh series. -/
def logPartial (q : ℚ) (n : ℕ) : ℚ :=
  2 * ∑ k ∈ Finset.range (n + 1),
    (logCoordinate q) ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℚ)

/-- The rational logarithm remainder bounds the tail of the atanh series geometrically. -/
def logRemainder (q : ℚ) (n : ℕ) : ℚ :=
  2 * |logCoordinate q| ^ (2 * n + 3) /
    (((2 * n + 3 : ℕ) : ℚ) * (1 - |logCoordinate q| ^ 2))

private theorem abs_logCoordinate_lt_one_aux (q : ℚ) (hq : 0 < q) :
    |logCoordinate q| < 1 := by
  have hden : 0 < q + 1 := by linarith
  rw [abs_lt]
  constructor
  · rw [logCoordinate, lt_div_iff₀ hden]
    linarith
  · rw [logCoordinate, div_lt_iff₀ hden]
    linarith

private theorem log_series_remainder_bound (z : ℝ) (hz : |z| < 1) (n : ℕ) :
    |(Real.log (1 + z) - Real.log (1 - z)) -
        2 * ∑ k ∈ Finset.range (n + 1), z ^ (2 * k + 1) / (2 * k + 1 : ℕ)| ≤
      2 * |z| ^ (2 * n + 3) /
        ((2 * n + 3 : ℕ) * (1 - |z| ^ 2)) := by
  let f : ℕ → ℝ := fun k =>
    2 * (1 / (2 * (k : ℝ) + 1)) * z ^ (2 * k + 1)
  let k₀ := n + 1
  have hs : HasSum f (Real.log (1 + z) - Real.log (1 - z)) := by
    simpa [f] using Real.hasSum_log_sub_log_of_abs_lt_one hz
  have htail : HasSum (fun i => f (i + k₀))
      ((Real.log (1 + z) - Real.log (1 - z)) -
        ∑ i ∈ Finset.range k₀, f i) :=
    (hasSum_nat_add_iff' k₀).2 hs
  let r : ℝ := |z| ^ 2
  let C : ℝ := 2 * |z| ^ (2 * n + 3) / (2 * n + 3 : ℕ)
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by
    dsimp [r]
    nlinarith [mul_self_lt_mul_self (abs_nonneg z) hz]
  have hgeom : HasSum (fun i : ℕ => C * r ^ i) (C * (1 - r)⁻¹) :=
    (hasSum_geometric_of_norm_lt_one (show ‖r‖ < 1 by simpa [abs_of_nonneg hr0])).mul_left C
  have hterm : ∀ i : ℕ, ‖f (i + k₀)‖ ≤ C * r ^ i := by
    intro i
    have hd₀ : (0 : ℝ) < 2 * n + 3 := by positivity
    have hn : 2 * n + 3 ≤ 2 * (i + k₀) + 1 := by
      dsimp [k₀]
      omega
    have hden : (2 * n + 3 : ℝ) ≤ 2 * (i + k₀ : ℕ) + 1 := by
      exact_mod_cast hn
    have hdiv : (1 : ℝ) / (2 * (i + k₀ : ℕ) + 1) ≤ 1 / (2 * n + 3) := by
      exact one_div_le_one_div_of_le hd₀ hden
    dsimp [f, C, r, k₀]
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (2 * (i + (n + 1) : ℕ) + 1)),
      abs_pow]
    rw [show 2 * (i + (n + 1)) + 1 = (2 * n + 3) + 2 * i by omega, pow_add,
      show |z| ^ (2 * i) = (|z| ^ 2) ^ i by rw [← pow_mul]]
    have hp : 0 ≤ |z| ^ (2 * n + 3) := by positivity
    have hri : 0 ≤ (|z| ^ 2) ^ i := by positivity
    calc
      2 * (1 / (2 * ↑(i + (n + 1)) + 1)) *
          (|z| ^ (2 * n + 3) * (|z| ^ 2) ^ i) ≤
        2 * (1 / (2 * ↑n + 3)) *
          (|z| ^ (2 * n + 3) * (|z| ^ 2) ^ i) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hdiv (by norm_num))
          (mul_nonneg hp hri)
      _ = 2 * |z| ^ (2 * n + 3) / ↑(2 * n + 3) * (|z| ^ 2) ^ i := by
        push_cast
        ring
  have hbound := tsum_of_norm_bounded hgeom hterm
  rw [htail.tsum_eq] at hbound
  have hsum : (∑ i ∈ Finset.range k₀, f i) =
      2 * ∑ i ∈ Finset.range (n + 1), z ^ (2 * i + 1) / (2 * i + 1 : ℕ) := by
    dsimp [k₀, f]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    push_cast
    ring
  rw [hsum] at hbound
  simpa [C, r, div_eq_mul_inv, mul_inv, mul_assoc, mul_comm, mul_left_comm] using hbound
/-- A positive rational logarithm argument is enclosed by its atanh polynomial
plus or minus its tail bound. -/
def logRaw (q : ℚ) (hq : 0 < q) (n : ℕ) : RatInterval :=
  ⟨logPartial q n - logRemainder q n,
    logPartial q n + logRemainder q n, by
      have hz := abs_logCoordinate_lt_one_aux q hq
      have hsquare : |logCoordinate q| ^ 2 < 1 := by
        nlinarith [mul_self_lt_mul_self (abs_nonneg (logCoordinate q)) hz]
      have hd : 0 < 1 - |logCoordinate q| ^ 2 := sub_pos.mpr hsquare
      have hr : 0 ≤ logRemainder q n := by
        simp only [logRemainder]
        positivity
      linarith⟩

/-- Successive positive-logarithm enclosures are intersected to make the sequence nested. -/
def logScalar (q : ℚ) (hq : 0 < q) : ℕ → RatInterval
  | 0 => logRaw q hq 0
  | n + 1 => RatInterval.tighten (logScalar q hq n) (logRaw q hq (n + 1))

/-- The explicit logarithm precision is a natural function of the input
numerator, denominator, and target width. -/
def logPrecision (q : ℚ) (ε : PosRat) : ℕ :=
  (ε.1.den + 1) * (q.num.natAbs + q.den + 1) * (q.num.natAbs + q.den + 1)

/-- A positive rational logarithm argument has atanh coordinate of absolute
value strictly below one. -/
theorem abs_logCoordinate_lt_one (q : ℚ) (hq : 0 < q) :
    |logCoordinate q| < 1 := by
  exact abs_logCoordinate_lt_one_aux q hq

private theorem logCoordinate_gap_lower (q : ℚ) (hq : 0 < q) :
    1 / ((q.num.natAbs : ℚ) + q.den + 1) ≤ 1 - |logCoordinate q| ^ 2 := by
  have hnum0 : 0 ≤ q.num := Rat.num_nonneg.mpr hq.le
  have hnumne : q.num ≠ 0 := by
    intro h
    have hq0 : q = 0 := by
      rw [← Rat.num_div_den q, h]
      simp
    linarith
  have ha : (1 : ℚ) ≤ q.num.natAbs := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hnumne))
  have hb : (1 : ℚ) ≤ q.den := by exact_mod_cast q.den_pos
  have hqrep : q = (q.num.natAbs : ℚ) / q.den := by
    calc
      q = (q.num : ℚ) / q.den := (Rat.num_div_den q).symm
      _ = (q.num.natAbs : ℚ) / q.den := by
        congr 1
        have hnum0' : (0 : ℚ) ≤ q.num := by exact_mod_cast hnum0
        norm_num [Int.natAbs_of_nonneg hnum0, abs_of_nonneg hnum0']
  have hcoord : logCoordinate q =
      ((q.num.natAbs : ℚ) - q.den) / (q.num.natAbs + q.den) := by
    calc
      logCoordinate q = (q - 1) / (q + 1) := rfl
      _ = ((q.num.natAbs : ℚ) / q.den - 1) /
          ((q.num.natAbs : ℚ) / q.den + 1) :=
        congrArg (fun x : ℚ => (x - 1) / (x + 1)) hqrep
      _ = _ := by field_simp
  rw [hcoord]
  have hab : (0 : ℚ) < q.num.natAbs + q.den := by linarith
  have hab1 : (0 : ℚ) < q.num.natAbs + q.den + 1 := by linarith
  rw [sq_abs, div_pow]
  rw [div_le_iff₀ hab1]
  field_simp
  nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb),
    sq_nonneg ((q.num.natAbs : ℚ) - q.den),
    sq_nonneg ((q.num.natAbs : ℚ) + q.den)]

/-- The raw rational logarithm interval encloses the real logarithm of its
positive rational input. -/
theorem logRaw_sound (q : ℚ) (hq : 0 < q) (n : ℕ) :
    (logRaw q hq n).Contains (Real.log (q : ℝ)) := by
  let z := logCoordinate q
  have hz : |(z : ℝ)| < 1 := by
    exact_mod_cast abs_logCoordinate_lt_one q hq
  have hb := log_series_remainder_bound (z : ℝ) hz n
  have hratio : (1 + (z : ℝ)) / (1 - (z : ℝ)) = (q : ℝ) := by
    have hd : (q : ℝ) + 1 ≠ 0 := by positivity
    dsimp [z, logCoordinate]
    push_cast
    field_simp [hd]
    ring
  have hplus : (1 + (z : ℝ)) ≠ 0 := by
    have := (abs_lt.mp hz).1
    linarith
  have hminus : (1 - (z : ℝ)) ≠ 0 := by
    have := (abs_lt.mp hz).2
    linarith
  have hlog : Real.log (q : ℝ) =
      Real.log (1 + (z : ℝ)) - Real.log (1 - (z : ℝ)) := by
    rw [← Real.log_div hplus hminus, hratio]
  have hp : ((logPartial q n : ℚ) : ℝ) =
      2 * ∑ k ∈ Finset.range (n + 1),
        (z : ℝ) ^ (2 * k + 1) / (2 * k + 1 : ℕ) := by
    simp [logPartial, z]
  have hr : ((logRemainder q n : ℚ) : ℝ) =
      2 * |(z : ℝ)| ^ (2 * n + 3) /
        ((2 * n + 3 : ℕ) * (1 - |(z : ℝ)| ^ 2)) := by
    simp [logRemainder, z]
  rw [← hlog, ← hp, ← hr] at hb
  rw [abs_le] at hb
  simp only [logRaw, RatInterval.Contains, Rat.cast_sub, Rat.cast_add]
  constructor <;> linarith [hb.1, hb.2]

/-- Every tightened scalar logarithm interval encloses the real logarithm. -/
theorem logScalar_sound (q : ℚ) (hq : 0 < q) (n : ℕ) :
    (logScalar q hq n).Contains (Real.log (q : ℝ)) := by
  induction n with
  | zero => exact logRaw_sound q hq 0
  | succ n ih =>
      exact RatInterval.tighten_sound ih (logRaw_sound q hq (n + 1))

/-- Scalar logarithm enclosures are nested as precision increases. -/
theorem logScalar_nested (q : ℚ) (hq : 0 < q) (n : ℕ) :
    (logScalar q hq (n + 1)).Subinterval (logScalar q hq n) := by
  exact RatInterval.tighten_subinterval_left
    (logScalar_sound q hq n) (logRaw_sound q hq (n + 1))

private theorem logScalar_subinterval_raw (q : ℚ) (hq : 0 < q) (n : ℕ) :
    (logScalar q hq n).Subinterval (logRaw q hq n) := by
  cases n with
  | zero => exact RatInterval.subinterval_refl _
  | succ n =>
      exact tighten_subinterval_right
        (logScalar_sound q hq n) (logRaw_sound q hq (n + 1))

/-- The explicit logarithm precision returns an enclosure no wider than the requested tolerance. -/
theorem logScalar_width (q : ℚ) (hq : 0 < q) (ε : PosRat) :
    (logScalar q hq (logPrecision q ε)).width ≤ ε.1 := by
  let D : ℚ := ε.1.den
  let S : ℚ := q.num.natAbs + q.den + 1
  let N : ℕ := logPrecision q ε
  let r : ℚ := |logCoordinate q|
  have hD : 1 ≤ D := by
    dsimp [D]
    exact_mod_cast ε.1.den_pos
  have hS : 2 ≤ S := by
    dsimp [S]
    have ha : (0 : ℚ) ≤ q.num.natAbs := by positivity
    have hb : (1 : ℚ) ≤ q.den := by exact_mod_cast q.den_pos
    linarith
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by simpa [r] using abs_logCoordinate_lt_one q hq
  have hrpow : r ^ (2 * N + 3) ≤ 1 := by
    exact pow_le_one₀ hr0 hr1.le
  have hgap : 1 / S ≤ 1 - r ^ 2 := by
    simpa [S, r] using logCoordinate_gap_lower q hq
  have hSpos : 0 < S := lt_of_lt_of_le (by norm_num) hS
  have hSgap : 1 ≤ S * (1 - r ^ 2) := by
    simpa [mul_comm] using (div_le_iff₀ hSpos).mp hgap
  have hN : (N : ℚ) = (D + 1) * S * S := by
    dsimp [N, D, S, logPrecision]
    push_cast
    ring
  have hden : 4 * D ≤ ((2 * N + 3 : ℕ) : ℚ) * (1 - r ^ 2) := by
    have hgap0 : 0 ≤ 1 - r ^ 2 := by nlinarith [sq_nonneg r]
    have hlarge := mul_le_mul_of_nonneg_left hSgap
      (show 0 ≤ 2 * (D + 1) * S by positivity)
    have hstep : 2 * (D + 1) * S ≤
        (2 * (D + 1) * S * S) * (1 - r ^ 2) := by
      nlinarith
    push_cast
    rw [hN]
    nlinarith [mul_nonneg (show (0 : ℚ) ≤ 3 by norm_num) hgap0]
  have hdenpos : 0 < ((2 * N + 3 : ℕ) : ℚ) * (1 - r ^ 2) := by
    have : 0 < 1 - r ^ 2 := by nlinarith [sq_nonneg r]
    positivity
  have hraw : (logRaw q hq N).width ≤ ε.1 := by
    have hnum : 4 * r ^ (2 * N + 3) ≤ 4 := by nlinarith
    have hfrac : 4 * r ^ (2 * N + 3) /
        (((2 * N + 3 : ℕ) : ℚ) * (1 - r ^ 2)) ≤ 1 / D := by
      apply (div_le_div_iff₀ hdenpos (show 0 < D by linarith)).2
      simpa only [one_mul] using
        (mul_le_mul_of_nonneg_right hnum (show 0 ≤ D by linarith)).trans hden
    calc
      (logRaw q hq N).width =
          4 * r ^ (2 * N + 3) /
            (((2 * N + 3 : ℕ) : ℚ) * (1 - r ^ 2)) := by
        simp [RatInterval.width, logRaw, logRemainder, r]
        ring
      _ ≤ 1 / D := hfrac
      _ ≤ ε.1 := by simpa [D] using inv_den_le_of_pos ε.1 ε.2
  exact (RatInterval.width_mono (logScalar_subinterval_raw q hq N)).trans hraw

/-- The logarithm of a positive rational is a certified real with fully rational endpoints. -/
noncomputable def logName (q : ℚ) (hq : 0 < q) : CertifiedReal where
  value := Real.log (q : ℝ)
  approx := logScalar q hq
  nested := logScalar_nested q hq
  contains := logScalar_sound q hq
  modulus := logPrecision q
  width_modulus := logScalar_width q hq
end Transcendental
end Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic
