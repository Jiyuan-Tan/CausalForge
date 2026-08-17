import Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Mesh

/-!
# Certified trapezoidal contour quadrature

This module turns complex rational node rectangles on a uniform mesh into a
sound enclosure of an interval integral.  The deterministic trapezoidal rule
is widened by an explicit Lipschitz error, and the result specializes to a
circle contour through its standard parameterization.
-/

open scoped BigOperators Interval
open MeasureTheory Set intervalIntegral

namespace Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic
namespace CircleMesh

/-- The unscaled trapezoidal rectangle sum is computed by primitive recursion over mesh cells. -/
def trapezoidSum (nodes : ℕ → ComplexRatInterval) : ℕ → ComplexRatInterval
  | 0 => ComplexRatInterval.zero
  | n + 1 => ComplexRatInterval.add (trapezoidSum nodes n)
      (ComplexRatInterval.add (nodes n) (nodes (n + 1)))

/-- The rational complex trapezoidal enclosure applies the usual half-cell
average and mesh scaling to the recursive endpoint sum. -/
def trapezoidEnclosure (nodes : ℕ → ComplexRatInterval) (n : ℕ) : ComplexRatInterval :=
  ComplexRatInterval.smulRat (1 / (2 * n : ℚ)) (trapezoidSum nodes n)

/-- The certified contour enclosure widens the rational trapezoidal enclosure
by its Lipschitz discretization error. -/
def integralEnclosure (nodes : ℕ → ComplexRatInterval) (L : ℚ) (hL : 0 ≤ L)
    (n : ℕ) (hn : 0 < n) : ComplexRatInterval :=
  (trapezoidEnclosure nodes n).expand (L / (2 * n)) (by positivity)

private theorem meshPoint_self {n : ℕ} (hn : 0 < n) : meshPoint n n = 1 := by
  simp [meshPoint, ne_of_gt (by exact_mod_cast hn : (0 : ℝ) < n)]

private theorem meshPoint_mono {n k m : ℕ} (hn : 0 < n) (hkm : k ≤ m) :
    meshPoint n k ≤ meshPoint n m := by
  exact div_le_div_of_nonneg_right (by exact_mod_cast hkm)
    (by exact_mod_cast (Nat.zero_le n) : (0 : ℝ) ≤ n)

private theorem meshPoint_succ_sub {n k : ℕ} (hn : 0 < n) :
    meshPoint n (k + 1) - meshPoint n k = 1 / (n : ℝ) := by
  rw [meshPoint, meshPoint]
  field_simp
  norm_num

private theorem sum_cell_integrals {g : ℝ → ℂ} {n : ℕ} (hn : 0 < n)
    (hg : ContinuousOn g (Icc (0 : ℝ) 1)) :
    ∫ u in (0 : ℝ)..1, g u =
      ∑ k ∈ Finset.range n, ∫ u in meshPoint n k..meshPoint n (k + 1), g u := by
  have hcell : ∀ k ≤ n, IntervalIntegrable g volume 0 (meshPoint n k) := by
    intro k hk
    apply ContinuousOn.intervalIntegrable
    apply hg.mono
    have h0k : (0 : ℝ) ≤ meshPoint n k := (meshPoint_mem hn hk).1
    simp only [uIcc_of_le h0k]
    intro x hx
    exact ⟨hx.1, hx.2.trans (meshPoint_self hn ▸ meshPoint_mono hn hk)⟩
  have aux : ∀ m ≤ n, ∫ u in (0 : ℝ)..meshPoint n m, g u =
      ∑ k ∈ Finset.range m, ∫ u in meshPoint n k..meshPoint n (k + 1), g u := by
    intro m hm
    induction m with
    | zero => simp [meshPoint]
    | succ m ih =>
        rw [Finset.sum_range_succ, ← ih (Nat.le_of_succ_le hm)]
        exact (intervalIntegral.integral_add_adjacent_intervals
          (hcell m (Nat.le_of_succ_le hm))
          ((hg.mono (by
            rw [uIcc_of_le (meshPoint_mono hn m.le_succ)]
            intro x hx
            exact ⟨(meshPoint_mem hn (Nat.le_of_succ_le hm)).1.trans hx.1,
              hx.2.trans (meshPoint_mem hn hm).2⟩)).intervalIntegrable)).symm
  simpa [meshPoint_self hn] using aux n le_rfl

/-- A Lipschitz complex function on the unit parameter interval differs from
its deterministic trapezoidal rule by at most half a Lipschitz mesh unit. -/
theorem norm_integral_sub_trapezoid_le {g : ℝ → ℂ} {L : ℚ} (hL : 0 ≤ L)
    {n : ℕ} (hn : 0 < n)
    (hLip : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖g s - g t‖ ≤ (L : ℝ) * |s - t|) :
    ‖(∫ u in (0 : ℝ)..1, g u) -
      ((1 / (2 * n : ℝ)) * ∑ k ∈ Finset.range n,
        (g (meshPoint n k) + g (meshPoint n (k + 1))))‖ ≤ (L : ℝ) / (2 * n) := by
  have hL' : (0 : ℝ) ≤ L := by exact_mod_cast hL
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hcont : ContinuousOn g (Icc (0 : ℝ) 1) :=
    continuousOn_of_lipschitz_bound hL' hLip
  have hcell : ∀ k < n,
      ‖(∫ u in meshPoint n k..meshPoint n (k + 1), g u) -
        (1 / (2 * n : ℝ)) * (g (meshPoint n k) + g (meshPoint n (k + 1)))‖
        ≤ (L : ℝ) / (2 * n * n) := by
    intro k hk
    let a := meshPoint n k
    let b := meshPoint n (k + 1)
    have hka : k ≤ n := (Nat.le_of_lt hk)
    have hkb : k + 1 ≤ n := hk
    have hab : a ≤ b := meshPoint_mono hn k.le_succ
    have ha : a ∈ Icc (0 : ℝ) 1 := meshPoint_mem hn hka
    have hb : b ∈ Icc (0 : ℝ) 1 := meshPoint_mem hn hkb
    have hgi : IntervalIntegrable g volume a b :=
      (hcont.mono (by
        rw [uIcc_of_le hab]
        intro x hx
        exact ⟨ha.1.trans hx.1, hx.2.trans hb.2⟩)).intervalIntegrable
    have hp : ∀ u ∈ uIcc a b,
        ‖g u - ((1 / 2 : ℝ) : ℂ) * (g a + g b)‖ ≤ (L : ℝ) / (2 * n) := by
      intro u hu
      rw [uIcc_of_le hab] at hu
      have huI : u ∈ Icc (0 : ℝ) 1 := ⟨ha.1.trans hu.1, hu.2.trans hb.2⟩
      have hla := hLip u huI a ha
      have hlb := hLip u huI b hb
      have hdist : |u - a| + |u - b| = b - a := by
        rw [abs_of_nonneg (sub_nonneg.mpr hu.1), abs_of_nonpos (sub_nonpos.mpr hu.2)]
        ring
      have halg : g u - ((1 / 2 : ℝ) : ℂ) * (g a + g b) =
          ((1 / 2 : ℝ) : ℂ) * (g u - g a) +
            ((1 / 2 : ℝ) : ℂ) * (g u - g b) := by
        norm_num
        ring
      rw [halg]
      calc
        ‖((1 / 2 : ℝ) : ℂ) * (g u - g a) +
            ((1 / 2 : ℝ) : ℂ) * (g u - g b)‖
            ≤ ‖((1 / 2 : ℝ) : ℂ) * (g u - g a)‖ +
              ‖((1 / 2 : ℝ) : ℂ) * (g u - g b)‖ := norm_add_le _ _
        _ = (1 / 2 : ℝ) * ‖g u - g a‖ + (1 / 2 : ℝ) * ‖g u - g b‖ := by
          simp [norm_mul]
        _ ≤ (1 / 2 : ℝ) * ((L : ℝ) * |u - a|) +
            (1 / 2 : ℝ) * ((L : ℝ) * |u - b|) := by gcongr
        _ = (L : ℝ) / 2 * (b - a) := by rw [← hdist]; ring
        _ = (L : ℝ) / (2 * n) := by
          rw [show b - a = 1 / (n : ℝ) by exact meshPoint_succ_sub hn]
          ring
    have hbound :
        ‖∫ u in a..b, (g u - ((1 / 2 : ℝ) : ℂ) * (g a + g b))‖ ≤
          ((L : ℝ) / (2 * n)) * |b - a| :=
      intervalIntegral.norm_integral_le_of_norm_le_const (by
        intro u hu
        apply hp u
        rw [uIcc_of_le hab]
        rw [show Ι a b = Ioc a b from uIoc_of_le hab] at hu
        exact ⟨le_of_lt hu.1, hu.2⟩)
    have hrewrite :
        (∫ u in a..b, g u) - (1 / (2 * n : ℝ)) * (g a + g b) =
          ∫ u in a..b, (g u - ((1 / 2 : ℝ) : ℂ) * (g a + g b)) := by
      have hscale : (1 / (2 * n : ℝ)) * (g a + g b) =
          (1 / (n : ℝ)) • (((1 / 2 : ℝ) : ℂ) * (g a + g b)) := by
        rw [Complex.real_smul]
        push_cast
        field_simp
      rw [intervalIntegral.integral_sub hgi intervalIntegrable_const,
        intervalIntegral.integral_const]
      rw [show b - a = 1 / (n : ℝ) by exact meshPoint_succ_sub hn]
      rw [hscale]
      rfl
    rw [hrewrite]
    calc
      ‖∫ u in a..b, (g u - ((1 / 2 : ℝ) : ℂ) * (g a + g b))‖
          ≤ ((L : ℝ) / (2 * n)) * |b - a| := hbound
      _ = (L : ℝ) / (2 * n * n) := by
        rw [show b - a = 1 / (n : ℝ) by exact meshPoint_succ_sub hn,
          abs_of_nonneg (by positivity)]
        ring
  rw [sum_cell_integrals hn hcont, Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ k ∈ Finset.range n,
          ‖(∫ u in meshPoint n k..meshPoint n (k + 1), g u) -
            (1 / (2 * n : ℝ)) * (g (meshPoint n k) + g (meshPoint n (k + 1)))‖ := by
      convert norm_sum_le _ _ using 1 <;> norm_num [Nat.cast_mul]
    _ ≤ ∑ _k ∈ Finset.range n, (L : ℝ) / (2 * n * n) := by
      gcongr with k hk
      exact hcell k (Finset.mem_range.mp hk)
    _ = (L : ℝ) / (2 * n) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp

private theorem trapezoidSum_sound {g : ℝ → ℂ} {nodes : ℕ → ComplexRatInterval}
    {N : ℕ} (m : ℕ)
    (hnodes : ∀ k ≤ m, (nodes k).Contains (g (meshPoint N k))) :
    (trapezoidSum nodes m).Contains
      (∑ k ∈ Finset.range m, (g (meshPoint N k) + g (meshPoint N (k + 1)))) := by
  induction m with
  | zero =>
      constructor <;> simp [trapezoidSum, ComplexRatInterval.zero,
        ComplexRatInterval.Contains, RatInterval.Contains, RatInterval.point]
  | succ n ih =>
      rw [Finset.sum_range_succ]
      exact ComplexRatInterval.add_sound
        (ih (fun k hk => hnodes k (hk.trans n.le_succ)))
        (ComplexRatInterval.add_sound (hnodes n n.le_succ) (hnodes (n + 1) le_rfl))

private theorem expand_contains_of_norm_sub {I : ComplexRatInterval} {z w : ℂ}
    {e : ℚ} (he : 0 ≤ e) (hz : I.Contains z)
    (hzw : ‖w - z‖ ≤ (e : ℝ)) : (I.expand e he).Contains w := by
  have hre : |w.re - z.re| ≤ (e : ℝ) := by
    exact (Complex.abs_re_le_norm (w - z)).trans hzw
  have him : |w.im - z.im| ≤ (e : ℝ) := by
    exact (Complex.abs_im_le_norm (w - z)).trans hzw
  have he' : (0 : ℝ) ≤ e := by exact_mod_cast he
  constructor <;> constructor <;>
    simp only [ComplexRatInterval.expand, RatInterval.expand, RatInterval.Contains,
      Rat.cast_sub, Rat.cast_add] <;>
    linarith [hz.1.1, hz.1.2, hz.2.1, hz.2.2, neg_le_of_abs_le hre,
      le_of_abs_le hre, neg_le_of_abs_le him, le_of_abs_le him]

private theorem width_smulRat_of_nonneg (I : ComplexRatInterval) {q : ℚ} (hq : 0 ≤ q) :
    (ComplexRatInterval.smulRat q I).re.width = q * I.re.width ∧
      (ComplexRatInterval.smulRat q I).im.width = q * I.im.width := by
  have hre := mul_le_mul_of_nonneg_left I.re.lo_le_hi hq
  have him := mul_le_mul_of_nonneg_left I.im.lo_le_hi hq
  constructor
  · simp [ComplexRatInterval.smulRat, RatInterval.mul, RatInterval.point,
      RatInterval.width, min_eq_left hre, max_eq_right hre]
    ring
  · simp [ComplexRatInterval.smulRat, RatInterval.mul, RatInterval.point,
      RatInterval.width, min_eq_left him, max_eq_right him]
    ring

private theorem width_trapezoidSum {nodes : ℕ → ComplexRatInterval} {w : ℚ}
    (hw : 0 ≤ w) (hnodes : ∀ k ≤ n,
      (nodes k).re.width ≤ w ∧ (nodes k).im.width ≤ w) :
    (trapezoidSum nodes n).re.width ≤ 2 * n * w ∧
      (trapezoidSum nodes n).im.width ≤ 2 * n * w := by
  induction n with
  | zero => norm_num [trapezoidSum, ComplexRatInterval.zero, RatInterval.width,
      RatInterval.point]
  | succ n ih =>
      have ih' := ih (fun k hk => hnodes k (hk.trans n.le_succ))
      have hn0 := hnodes n n.le_succ
      have hn1 := hnodes (n + 1) le_rfl
      unfold RatInterval.width at ih' hn0 hn1
      simp only [trapezoidSum, ComplexRatInterval.add, RatInterval.add,
        RatInterval.width]
      constructor <;> dsimp <;> push_cast <;> ring_nf at * <;>
        linarith [ih'.1, ih'.2, hn0.1, hn0.2, hn1.1, hn1.2, hw]

/-- Rational complex node rectangles plus the Lipschitz mesh error enclose the interval integral. -/
theorem integralEnclosure_sound {g : ℝ → ℂ} {nodes : ℕ → ComplexRatInterval}
    {L : ℚ} (hL : 0 ≤ L) {n : ℕ} (hn : 0 < n)
    (hLip : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖g s - g t‖ ≤ (L : ℝ) * |s - t|)
    (hnodes : ∀ k ≤ n, (nodes k).Contains (g (meshPoint n k))) :
    (integralEnclosure nodes L hL n hn).Contains (∫ u in (0 : ℝ)..1, g u) := by
  let T : ℂ := (1 / (2 * n : ℝ)) * ∑ k ∈ Finset.range n,
    (g (meshPoint n k) + g (meshPoint n (k + 1)))
  have hsum := trapezoidSum_sound (N := n) n hnodes
  have hT : (trapezoidEnclosure nodes n).Contains T := by
    unfold trapezoidEnclosure T
    convert ComplexRatInterval.smulRat_sound (1 / (2 * n : ℚ)) hsum using 1 <;>
      norm_num [Nat.cast_mul]
  have herr : ‖(∫ u in (0 : ℝ)..1, g u) - T‖ ≤ (L : ℝ) / (2 * n) := by
    exact norm_integral_sub_trapezoid_le hL hn hLip
  unfold integralEnclosure
  apply expand_contains_of_norm_sub (he := by positivity) hT
  simpa [Rat.cast_div, Rat.cast_natCast] using herr

/-- Each coordinate width of the certified integral is bounded by the uniform
node width plus one mesh-scale Lipschitz allowance. -/
theorem integralEnclosure_width {nodes : ℕ → ComplexRatInterval} {w L : ℚ}
    (hw : 0 ≤ w) (hL : 0 ≤ L) {n : ℕ} (hn : 0 < n)
    (hnodes : ∀ k ≤ n, (nodes k).re.width ≤ w ∧ (nodes k).im.width ≤ w) :
    (integralEnclosure nodes L hL n hn).re.width ≤ w + L / n ∧
      (integralEnclosure nodes L hL n hn).im.width ≤ w + L / n := by
  have hs := width_trapezoidSum hw hnodes
  have hq : (0 : ℚ) ≤ 1 / (2 * n : ℚ) := by positivity
  have hscale := width_smulRat_of_nonneg (trapezoidSum nodes n) hq
  have htre : (trapezoidEnclosure nodes n).re.width ≤ w := by
    rw [trapezoidEnclosure, hscale.1]
    calc
      (1 / (2 * n : ℚ)) * (trapezoidSum nodes n).re.width
          ≤ (1 / (2 * n : ℚ)) * (2 * n * w) :=
        mul_le_mul_of_nonneg_left hs.1 hq
      _ = w := by field_simp
  have htim : (trapezoidEnclosure nodes n).im.width ≤ w := by
    rw [trapezoidEnclosure, hscale.2]
    calc
      (1 / (2 * n : ℚ)) * (trapezoidSum nodes n).im.width
          ≤ (1 / (2 * n : ℚ)) * (2 * n * w) :=
        mul_le_mul_of_nonneg_left hs.2 hq
      _ = w := by field_simp
  have herr : L / (2 * n : ℚ) + L / (2 * n : ℚ) = L / n := by
    field_simp
    ring
  unfold RatInterval.width at htre htim
  constructor <;>
    simp only [integralEnclosure, ComplexRatInterval.expand, RatInterval.expand,
      RatInterval.width] <;> linarith [herr]

/-- Applying the complex mesh theorem to the parameterized circle integrand
encloses the contour integral. -/
theorem circleContourIntegral_enclosed {f : ℂ → ℂ} {c : ℂ} {r : ℝ}
    {nodes : ℕ → ComplexRatInterval} {L : ℚ} (hL : 0 ≤ L)
    {n : ℕ} (hn : 0 < n)
    (hLip : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖circleIntegrand f c r s - circleIntegrand f c r t‖ ≤ (L : ℝ) * |s - t|)
    (hnodes : ∀ k ≤ n,
      (nodes k).Contains (circleIntegrand f c r (meshPoint n k))) :
    (integralEnclosure nodes L hL n hn).Contains (circleContourIntegral f c r) := by
  exact integralEnclosure_sound hL hn hLip hnodes

end CircleMesh
end Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic
