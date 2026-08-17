import Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.CertifiedReal
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Rat.BigOperators

/-!
# Certified rational exponential enclosures

This module computes nested rational intervals for the exponential of a
rational input.  Range reduction, Taylor bounds, and an explicit precision
rule yield a certified real name whose returned interval meets every positive
rational error target.
-/

open scoped BigOperators

namespace Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic
namespace Transcendental

/-- The integer scaling factor reduces a rational exponential argument to
absolute value at most one. -/
def expScale (q : ℚ) : ℕ := max 1 q.num.natAbs

/-- The reduced exponential argument divides by its positive natural scaling factor. -/
def expReduced (q : ℚ) : ℚ := q / (expScale q : ℚ)

/-- The rational Taylor polynomial for the exponential retains all terms
through the requested degree. -/
def expPartial (q : ℚ) (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1), q ^ k / (k.factorial : ℚ)

/-- The rational remainder radius is the explicit exponential-series bound
after the retained Taylor terms. -/
def expRemainder (q : ℚ) (n : ℕ) : ℚ :=
  |q| ^ (n + 1) * ((n + 2 : ℕ) : ℚ) /
    (((n + 1).factorial : ℚ) * (n + 1 : ℕ))

/-- A reduced rational argument is enclosed by its Taylor polynomial plus or
minus the rational remainder radius. -/
def expReducedRaw (q : ℚ) (n : ℕ) : RatInterval :=
  ⟨expPartial q n - expRemainder q n,
    expPartial q n + expRemainder q n, by
      have hr : 0 ≤ expRemainder q n := by
        simp only [expRemainder]
        positivity
      linarith⟩

/-- The raw exponential enclosure raises the reduced-argument enclosure to the
exact scaling power. -/
def expRaw (q : ℚ) (n : ℕ) : RatInterval :=
  (expReducedRaw (expReduced q) n).npow (expScale q)

/-- Successive exponential enclosures are intersected to make the returned sequence nested. -/
def expScalar (q : ℚ) : ℕ → RatInterval
  | 0 => expRaw q 0
  | n + 1 => RatInterval.tighten (expScalar q n) (expRaw q (n + 1))

/-- The explicit exponential precision is a natural function of the rational
input and target width. -/
def expPrecision (q : ℚ) (ε : PosRat) : ℕ :=
  (ε.1.den + 1) * (expScale q + 1) * (expScale q + 1)

/-- Range reduction puts the exponential Taylor argument in the closed unit interval. -/
theorem abs_expReduced_le_one (q : ℚ) : |expReduced q| ≤ 1 := by
  have hsN : 0 < expScale q :=
    lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hs : (0 : ℚ) < expScale q := by exact_mod_cast hsN
  have hnum : |q| ≤ (q.num.natAbs : ℚ) := by
    have hd : (0 : ℚ) < q.den := by exact_mod_cast q.den_pos
    calc
      |q| = |(q.num : ℚ) / (q.den : ℚ)| := by rw [Rat.num_div_den]
      _ = (q.num.natAbs : ℚ) / q.den := by
        rw [abs_div, abs_of_pos hd]
        norm_num
      _ ≤ (q.num.natAbs : ℚ) := by
        apply (div_le_iff₀ hd).2
        have hd1 : (1 : ℚ) ≤ q.den := by exact_mod_cast q.den_pos
        nlinarith
  rw [expReduced, abs_div, abs_of_pos hs]
  apply (div_le_iff₀ hs).2
  have hscale : (q.num.natAbs : ℚ) ≤ expScale q := by
    exact_mod_cast (le_max_right 1 q.num.natAbs)
  simpa only [one_mul] using hnum.trans hscale

/-- The raw rational exponential interval encloses the real exponential of the rational input. -/
theorem expRaw_sound (q : ℚ) (n : ℕ) :
    (expRaw q n).Contains (Real.exp (q : ℝ)) := by
  let z := expReduced q
  have hzR : |(z : ℝ)| ≤ 1 := by
    exact_mod_cast abs_expReduced_le_one q
  have hb := Real.exp_bound hzR (n := n + 1) (Nat.succ_pos n)
  have hp : ((expPartial z n : ℚ) : ℝ) =
      ∑ k ∈ Finset.range (n + 1), (z : ℝ) ^ k / (k.factorial : ℝ) := by
    simp [expPartial]
  have hr : ((expRemainder z n : ℚ) : ℝ) =
      |(z : ℝ)| ^ (n + 1) * ((n + 2 : ℕ) : ℝ) /
        (((n + 1).factorial : ℝ) * (n + 1 : ℕ)) := by
    simp [expRemainder]
  rw [← hp] at hb
  have hb' : |Real.exp (z : ℝ) - (expPartial z n : ℝ)| ≤
      (expRemainder z n : ℝ) := by
    rw [hr]
    convert hb using 1 <;> norm_num [Nat.cast_succ] <;> ring
  have hred : (expReducedRaw z n).Contains (Real.exp (z : ℝ)) := by
    rw [abs_le] at hb'
    simp only [expReducedRaw, RatInterval.Contains, Rat.cast_sub, Rat.cast_add]
    constructor <;> linarith [hb'.1, hb'.2]
  have hpow := RatInterval.npow_sound hred (expScale q)
  have hs : (expScale q : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt
      (lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 q.num.natAbs)))
  have hq : (q : ℝ) = (expScale q : ℝ) * (z : ℝ) := by
    dsimp [z, expReduced]
    push_cast
    field_simp [hs]
  simpa [expRaw, ← Real.exp_nat_mul, hq] using hpow

/-- Every tightened scalar exponential interval encloses the real exponential. -/
theorem expScalar_sound (q : ℚ) (n : ℕ) :
    (expScalar q n).Contains (Real.exp (q : ℝ)) := by
  induction n with
  | zero => exact expRaw_sound q 0
  | succ n ih =>
      exact RatInterval.tighten_sound ih (expRaw_sound q (n + 1))

/-- Scalar exponential enclosures are nested as precision increases. -/
theorem expScalar_nested (q : ℚ) (n : ℕ) :
    (expScalar q (n + 1)).Subinterval (expScalar q n) := by
  exact RatInterval.tighten_subinterval_left
    (expScalar_sound q n) (expRaw_sound q (n + 1))

/-- Tightening two enclosures of the same real value is contained in either input enclosure. -/
theorem tighten_subinterval_right {I J : RatInterval} {x : ℝ}
    (hI : I.Contains x) (hJ : J.Contains x) :
    (RatInterval.tighten I J).Subinterval J := by
  have hlohi : max I.lo J.lo ≤ min I.hi J.hi := by
    apply max_le
    · apply le_min I.lo_le_hi
      exact_mod_cast hI.1.trans hJ.2
    · apply le_min
      · exact_mod_cast hJ.1.trans hI.2
      · exact J.lo_le_hi
  simp only [RatInterval.tighten, hlohi, dif_pos, RatInterval.Subinterval]
  exact ⟨le_max_right _ _, min_le_right _ _⟩

private theorem expScalar_subinterval_raw (q : ℚ) (n : ℕ) :
    (expScalar q n).Subinterval (expRaw q n) := by
  cases n with
  | zero => exact RatInterval.subinterval_refl _
  | succ n =>
      exact tighten_subinterval_right
        (expScalar_sound q n) (expRaw_sound q (n + 1))

private theorem interval_product_difference {I J : RatInterval}
    {x x' y y' : ℚ} (hx : I.lo ≤ x ∧ x ≤ I.hi)
    (hx' : I.lo ≤ x' ∧ x' ≤ I.hi) (hy : J.lo ≤ y ∧ y ≤ J.hi)
    (hy' : J.lo ≤ y' ∧ y' ≤ J.hi) :
    |x * y - x' * y'| ≤ I.maxAbs * J.width + J.maxAbs * I.width := by
  have hax : |x| ≤ I.maxAbs := abs_le_max_abs_abs hx.1 hx.2
  have hay' : |y'| ≤ J.maxAbs := abs_le_max_abs_abs hy'.1 hy'.2
  have hdx : |x - x'| ≤ I.width := by
    simpa [RatInterval.width] using
      (abs_sub_le_of_le_of_le hx.1 hx.2 hx'.1 hx'.2)
  have hdy : |y - y'| ≤ J.width := by
    simpa [RatInterval.width] using
      (abs_sub_le_of_le_of_le hy.1 hy.2 hy'.1 hy'.2)
  calc
    |x * y - x' * y'| = |x * (y - y') + (x - x') * y'| := by ring_nf
    _ ≤ |x| * |y - y'| + |x - x'| * |y'| := by
      simpa [abs_mul] using abs_add_le (x * (y - y')) ((x - x') * y')
    _ ≤ I.maxAbs * J.width + J.maxAbs * I.width := by
      have hI0 : 0 ≤ I.maxAbs := (abs_nonneg I.lo).trans (le_max_left _ _)
      have hJ0 : 0 ≤ J.maxAbs := (abs_nonneg J.lo).trans (le_max_left _ _)
      have hwI : 0 ≤ I.width := RatInterval.width_nonneg I
      have hwJ : 0 ≤ J.width := RatInterval.width_nonneg J
      nlinarith [mul_le_mul hax hdy (abs_nonneg (y - y')) hI0,
        mul_le_mul hdx hay' (abs_nonneg y') hwI]

private theorem interval_mul_width_le (I J : RatInterval) :
    (I.mul J).width ≤ I.maxAbs * J.width + J.maxAbs * I.width := by
  let R := I.maxAbs * J.width + J.maxAbs * I.width
  let a := I.lo * J.lo
  let b := I.lo * J.hi
  let c := I.hi * J.lo
  let d := I.hi * J.hi
  have hprod : ∀ u ∈ [a, b, c, d], ∀ v ∈ [a, b, c, d], |u - v| ≤ R := by
    intro u hu v hv
    simp at hu hv
    rcases hu with rfl | rfl | rfl | rfl <;>
      rcases hv with rfl | rfl | rfl | rfl <;>
      apply interval_product_difference <;>
      simp [a, b, c, d, I.lo_le_hi, J.lo_le_hi]
  have haa := hprod a (by simp) a (by simp)
  have hab := hprod a (by simp) b (by simp)
  have hac := hprod a (by simp) c (by simp)
  have had := hprod a (by simp) d (by simp)
  have hba := hprod b (by simp) a (by simp)
  have hbb := hprod b (by simp) b (by simp)
  have hbc := hprod b (by simp) c (by simp)
  have hbd := hprod b (by simp) d (by simp)
  have hca := hprod c (by simp) a (by simp)
  have hcb := hprod c (by simp) b (by simp)
  have hcc := hprod c (by simp) c (by simp)
  have hcd := hprod c (by simp) d (by simp)
  have hda := hprod d (by simp) a (by simp)
  have hdb := hprod d (by simp) b (by simp)
  have hdc := hprod d (by simp) c (by simp)
  have hdd := hprod d (by simp) d (by simp)
  rw [abs_le] at haa hab hac had hba hbb hbc hbd hca hcb hcc hcd hda hdb hdc hdd
  rcases haa with ⟨haa₁, haa₂⟩
  rcases hab with ⟨hab₁, hab₂⟩
  rcases hac with ⟨hac₁, hac₂⟩
  rcases had with ⟨had₁, had₂⟩
  rcases hba with ⟨hba₁, hba₂⟩
  rcases hbb with ⟨hbb₁, hbb₂⟩
  rcases hbc with ⟨hbc₁, hbc₂⟩
  rcases hbd with ⟨hbd₁, hbd₂⟩
  rcases hca with ⟨hca₁, hca₂⟩
  rcases hcb with ⟨hcb₁, hcb₂⟩
  rcases hcc with ⟨hcc₁, hcc₂⟩
  rcases hcd with ⟨hcd₁, hcd₂⟩
  rcases hda with ⟨hda₁, hda₂⟩
  rcases hdb with ⟨hdb₁, hdb₂⟩
  rcases hdc with ⟨hdc₁, hdc₂⟩
  rcases hdd with ⟨hdd₁, hdd₂⟩
  simp only [RatInterval.width, RatInterval.mul, a, b, c, d]
  rw [sub_le_iff_le_add]
  simp only [add_min]
  apply max_le <;> apply max_le <;> apply le_min <;> apply le_min <;>
    dsimp [a, b, c, d, R] at * <;>
    simp only [RatInterval.width] at * <;>
    linarith

private theorem interval_mul_maxAbs_le (I J : RatInterval) :
    (I.mul J).maxAbs ≤ I.maxAbs * J.maxAbs := by
  have hI0 : 0 ≤ I.maxAbs := (abs_nonneg I.lo).trans (le_max_left _ _)
  have hJ0 : 0 ≤ J.maxAbs := (abs_nonneg J.lo).trans (le_max_left _ _)
  have hp (x y : ℚ) (hx : |x| ≤ I.maxAbs) (hy : |y| ≤ J.maxAbs) :
      |x * y| ≤ I.maxAbs * J.maxAbs := by
    rw [abs_mul]
    exact mul_le_mul hx hy (abs_nonneg y) hI0
  have hIlo : |I.lo| ≤ I.maxAbs := le_max_left _ _
  have hIhi : |I.hi| ≤ I.maxAbs := le_max_right _ _
  have hJlo : |J.lo| ≤ J.maxAbs := le_max_left _ _
  have hJhi : |J.hi| ≤ J.maxAbs := le_max_right _ _
  simp only [RatInterval.maxAbs, RatInterval.mul]
  let B := I.maxAbs * J.maxAbs
  have ha : |I.lo * J.lo| ≤ B := hp _ _ hIlo hJlo
  have hb : |I.lo * J.hi| ≤ B := hp _ _ hIlo hJhi
  have hc : |I.hi * J.lo| ≤ B := hp _ _ hIhi hJlo
  have hd : |I.hi * J.hi| ≤ B := hp _ _ hIhi hJhi
  apply max_le
  · calc
      |min (min (I.lo * J.lo) (I.lo * J.hi))
          (min (I.hi * J.lo) (I.hi * J.hi))| ≤
          max |min (I.lo * J.lo) (I.lo * J.hi)|
            |min (I.hi * J.lo) (I.hi * J.hi)| := abs_min_le_max_abs_abs
      _ ≤ max (max |I.lo * J.lo| |I.lo * J.hi|)
          (max |I.hi * J.lo| |I.hi * J.hi|) :=
        max_le_max abs_min_le_max_abs_abs abs_min_le_max_abs_abs
      _ ≤ B := max_le (max_le ha hb) (max_le hc hd)
  · calc
      |max (max (I.lo * J.lo) (I.lo * J.hi))
          (max (I.hi * J.lo) (I.hi * J.hi))| ≤
          max |max (I.lo * J.lo) (I.lo * J.hi)|
            |max (I.hi * J.lo) (I.hi * J.hi)| := abs_max_le_max_abs_abs
      _ ≤ max (max |I.lo * J.lo| |I.lo * J.hi|)
          (max |I.hi * J.lo| |I.hi * J.hi|) :=
        max_le_max abs_max_le_max_abs_abs abs_max_le_max_abs_abs
      _ ≤ B := max_le (max_le ha hb) (max_le hc hd)

private theorem interval_npow_maxAbs_le (I : RatInterval) (n : ℕ) :
    (I.npow n).maxAbs ≤ I.maxAbs ^ n := by
  induction n with
  | zero => simp [RatInterval.npow, RatInterval.point, RatInterval.maxAbs]
  | succ n ih =>
      have hM : 0 ≤ I.maxAbs := (abs_nonneg I.lo).trans (le_max_left _ _)
      simpa [RatInterval.npow, pow_succ] using
        (interval_mul_maxAbs_le (I.npow n) I).trans
          (mul_le_mul ih le_rfl hM (pow_nonneg hM n))

private theorem interval_npow_width_le (I : RatInterval) (n : ℕ) :
    (I.npow n).width ≤ (n : ℚ) * I.maxAbs ^ (n - 1) * I.width := by
  induction n with
  | zero => simp [RatInterval.npow, RatInterval.point, RatInterval.width]
  | succ n ih =>
      cases n with
      | zero =>
          simpa [RatInterval.npow, RatInterval.point, RatInterval.width,
            RatInterval.maxAbs] using
            interval_mul_width_le (RatInterval.point 1) I
      | succ n =>
          have hM : 0 ≤ I.maxAbs := (abs_nonneg I.lo).trans (le_max_left _ _)
          have hw : 0 ≤ I.width := RatInterval.width_nonneg I
          calc
            (I.npow (n + 1 + 1)).width ≤
                (I.npow (n + 1)).maxAbs * I.width +
                  I.maxAbs * (I.npow (n + 1)).width :=
              interval_mul_width_le (I.npow (n + 1)) I
            _ ≤ I.maxAbs ^ (n + 1) * I.width +
                I.maxAbs * ((n + 1 : ℚ) * I.maxAbs ^ n * I.width) := by
              gcongr
              · exact interval_npow_maxAbs_le I (n + 1)
              · simpa using ih
            _ = ((n + 1 + 1 : ℕ) : ℚ) *
                I.maxAbs ^ (n + 1 + 1 - 1) * I.width := by
              simp only [Nat.add_sub_cancel]
              rw [pow_succ]
              push_cast
              ring

private theorem nat_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      have hpow : 1 ≤ 2 ^ n := one_le_pow₀ (by omega)
      omega

/-- The reciprocal of a positive rational's denominator is no larger than the rational itself. -/
theorem inv_den_le_of_pos (u : ℚ) (hu : 0 < u) :
    1 / (u.den : ℚ) ≤ u := by
  have hnum0 : 0 ≤ u.num := Rat.num_nonneg.mpr hu.le
  have hnumne : u.num ≠ 0 := by
    intro h
    have hu0 : u = 0 := by
      rw [← Rat.num_div_den u, h]
      simp
    linarith
  have hnum1 : (1 : ℚ) ≤ u.num := by
    exact_mod_cast (lt_of_le_of_ne hnum0 (Ne.symm hnumne))
  calc
    1 / (u.den : ℚ) ≤ (u.num : ℚ) / u.den :=
      div_le_div_of_nonneg_right hnum1 (by positivity)
    _ = u := Rat.num_div_den u

/-- The explicit exponential precision returns an enclosure no wider than the
requested tolerance. -/
theorem expScalar_width (q : ℚ) (ε : PosRat) :
    (expScalar q (expPrecision q ε)).width ≤ ε.1 := by
  let D : ℕ := ε.1.den
  let s : ℕ := expScale q
  let N : ℕ := expPrecision q ε
  let z : ℚ := expReduced q
  let R : ℚ := expRemainder z N
  let I : RatInterval := expReducedRaw z N
  have hD : 0 < D := by simpa [D] using ε.1.den_pos
  have hs : 0 < s := by
    dsimp [s, expScale]
    omega
  have hN : 1 ≤ N := by
    dsimp [N, expPrecision, D, s]
    exact Nat.mul_pos (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)) (Nat.succ_pos _)
  have hz : |z| ≤ 1 := by simpa [z] using abs_expReduced_le_one q
  have hz0 : 0 ≤ |z| := abs_nonneg z
  have hzpow (k : ℕ) : |z| ^ k ≤ 1 := pow_le_one₀ hz0 hz
  have hpartial : |expPartial z N| ≤ 3 := by
    calc
      |expPartial z N| ≤
          ∑ k ∈ Finset.range (N + 1), |z ^ k / (k.factorial : ℚ)| := by
        simpa [expPartial] using
          Finset.abs_sum_le_sum_abs (s := Finset.range (N + 1))
            (f := fun k => z ^ k / (k.factorial : ℚ))
      _ ≤ ∑ k ∈ Finset.range (N + 1), (1 / k.factorial : ℚ) := by
        gcongr with k hk
        rw [abs_div, abs_pow, abs_of_nonneg (by positivity : (0 : ℚ) ≤ k.factorial)]
        exact div_le_div_of_nonneg_right (hzpow k) (by positivity)
      _ = 1 + ∑ k ∈ Finset.range (N + 1) with 1 ≤ k,
          (1 / k.factorial : ℚ) := by
        rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.range (N + 1))
          (p := fun k => 1 ≤ k) (f := fun k => (1 / k.factorial : ℚ))]
        simp [add_comm]
      _ ≤ 3 := by
        linarith [Complex.sum_div_factorial_le (α := ℚ) 1 (N + 1) (by omega)]
  have hfac1 : (1 : ℕ) ≤ N.factorial := by
    exact Nat.factorial_pos N
  have hrem : R ≤ 1 := by
    have hnum : |z| ^ (N + 1) * ((N + 2 : ℕ) : ℚ) ≤
        ((N + 1).factorial : ℚ) * (N + 1 : ℕ) := by
      have hfac1Q : (1 : ℚ) ≤ N.factorial := by exact_mod_cast hfac1
      have hNQ : (1 : ℚ) ≤ N := by exact_mod_cast hN
      have hsq : ((N + 2 : ℕ) : ℚ) ≤ (N + 1 : ℚ) * (N + 1 : ℚ) := by
        push_cast
        nlinarith
      calc
        |z| ^ (N + 1) * ((N + 2 : ℕ) : ℚ) ≤ ((N + 2 : ℕ) : ℚ) := by
          nlinarith [hzpow (N + 1)]
        _ ≤ (N + 1 : ℚ) * (N + 1 : ℚ) := hsq
        _ ≤ ((N + 1).factorial : ℚ) * (N + 1 : ℕ) := by
          rw [Nat.factorial_succ]
          push_cast
          have haux : 0 ≤ ((N.factorial : ℚ) - 1) * (N + 1 : ℚ) ^ 2 :=
            mul_nonneg (sub_nonneg.mpr hfac1Q) (sq_nonneg _)
          nlinarith
    dsimp [R, expRemainder]
    exact (div_le_one (by positivity)).2 hnum
  have hR0 : 0 ≤ R := by
    dsimp [R, expRemainder]
    positivity
  have hIwidth : I.width = 2 * R := by
    simp [I, expReducedRaw, RatInterval.width, R]
    ring
  have hImax : I.maxAbs ≤ 4 := by
    dsimp [I, expReducedRaw, RatInterval.maxAbs]
    apply max_le
    · calc
        |expPartial z N - R| ≤ |expPartial z N| + |R| := abs_sub _ _
        _ = |expPartial z N| + R := by rw [abs_of_nonneg hR0]
        _ ≤ 4 := by linarith
    · calc
        |expPartial z N + R| ≤ |expPartial z N| + |R| := abs_add_le _ _
        _ = |expPartial z N| + R := by rw [abs_of_nonneg hR0]
        _ ≤ 4 := by linarith
  have hNlarge : D + 3 * s ≤ N := by
    have hsum : D + 1 + (s + 1) * (s + 1) ≤ N := by
      dsimp [N, expPrecision]
      change D + 1 + (s + 1) * (s + 1) ≤ (D + 1) * (s + 1) * (s + 1)
      rw [mul_assoc]
      apply add_le_mul
      · omega
      · nlinarith
    have hsquare : 3 * s ≤ 1 + (s + 1) * (s + 1) := by nlinarith
    omega
  have hpowbound : D * s * 4 ^ s ≤ 2 ^ N := by
    calc
      D * s * 4 ^ s ≤ 2 ^ D * 2 ^ s * 4 ^ s := by
        exact Nat.mul_le_mul (Nat.mul_le_mul (nat_le_two_pow D) (nat_le_two_pow s)) le_rfl
      _ = 2 ^ (D + 3 * s) := by
        rw [show 4 = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add, ← pow_add]
        congr 1
        omega
      _ ≤ 2 ^ N := Nat.pow_le_pow_right (by omega) hNlarge
  have hfactorial : D * s * 4 ^ s ≤ (N + 1).factorial := by
    exact hpowbound.trans (by
      simpa [Nat.add_comm] using
        (@Nat.factorial_mul_pow_le_factorial 1 N))
  have hfactorialQ : (D : ℚ) * s * 4 ^ s ≤ ((N + 1).factorial : ℚ) := by
    exact_mod_cast hfactorial
  have hRfac : R * ((N + 1).factorial : ℚ) ≤ 2 := by
    have heq : R * ((N + 1).factorial : ℚ) =
        |z| ^ (N + 1) * ((N + 2 : ℕ) : ℚ) / (N + 1 : ℕ) := by
      dsimp [R, expRemainder]
      field_simp
    rw [heq]
    norm_num [Nat.cast_add]
    apply (div_le_iff₀ (by positivity : (0 : ℚ) < N + 1)).2
    nlinarith [hzpow (N + 1)]
  have hscaled : (D : ℚ) * s * 4 ^ s * R ≤ 2 := by
    calc
      (D : ℚ) * s * 4 ^ s * R ≤ ((N + 1).factorial : ℚ) * R := by
        exact mul_le_mul_of_nonneg_right hfactorialQ hR0
      _ = R * ((N + 1).factorial : ℚ) := by ring
      _ ≤ 2 := hRfac
  have hraw : (expRaw q N).width ≤ 1 / (D : ℚ) := by
    have hp := interval_npow_width_le I s
    have hI0 : 0 ≤ I.maxAbs := (abs_nonneg I.lo).trans (le_max_left _ _)
    have hpow4 : I.maxAbs ^ (s - 1) ≤ (4 : ℚ) ^ (s - 1) :=
      pow_le_pow_left₀ hI0 hImax _
    have hbound : (s : ℚ) * I.maxAbs ^ (s - 1) * I.width ≤
        (s : ℚ) * 4 ^ (s - 1) * (2 * R) := by
      rw [hIwidth]
      gcongr
    have hDq : (0 : ℚ) < D := by exact_mod_cast hD
    have hsform : (4 : ℚ) ^ s = 4 * 4 ^ (s - 1) := by
      calc
        (4 : ℚ) ^ s = 4 ^ (s - 1 + 1) := by congr 1 <;> omega
        _ = 4 ^ (s - 1) * 4 := pow_succ _ _
        _ = 4 * 4 ^ (s - 1) := mul_comm _ _
    have hfinal : (s : ℚ) * 4 ^ (s - 1) * (2 * R) ≤ 1 / D := by
      apply (le_div_iff₀ hDq).2
      rw [hsform] at hscaled
      nlinarith
    simpa [expRaw, I, s] using hp.trans (hbound.trans hfinal)
  calc
    (expScalar q (expPrecision q ε)).width ≤ (expRaw q N).width := by
      apply RatInterval.width_mono
      simpa [N] using expScalar_subinterval_raw q N
    _ ≤ 1 / (D : ℚ) := hraw
    _ ≤ ε.1 := by
      simpa [D] using inv_den_le_of_pos ε.1 ε.2

/-- A rational exponential is a certified real with a fully rational endpoint algorithm. -/
noncomputable def expName (q : ℚ) : CertifiedReal where
  value := Real.exp (q : ℝ)
  approx := expScalar q
  nested := expScalar_nested q
  contains := expScalar_sound q
  modulus := expPrecision q
  width_modulus := expScalar_width q

end Transcendental
end Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic
