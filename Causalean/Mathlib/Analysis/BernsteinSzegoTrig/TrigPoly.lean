/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Mathlib

/-!
# Real trigonometric polynomials and their zero count

A *real trigonometric polynomial of degree ≤ `n`* is a function
`f(t) = ∑_{k=0}^{n} (a k · cos (k t) + b k · sin (k t))`.  This file defines the
predicate `IsTrigPolyLE n f`, records elementary closure properties, and proves
the zero-count lemmas that drive the Szegő comparison:

* `IsTrigPolyLE.card_zeros_le` — a nonzero real trigonometric polynomial of
  degree ≤ `n` has at most `2 n` zeros in any half-open period.
* `IsTrigPolyLE.card_simple_add_double_le` — the multiplicity-refined form used
  by the sharp Szegő proof: a further double zero is counted twice.

This is the crucial input to Szegő's inequality that is *absent from Mathlib*.
The proof substitutes `z = e^{i t}` so that `f(t) = z^{-n} · P(z)` for an
algebraic polynomial `P : ℂ[X]` of degree ≤ `2 n`; zeros of `f` in one period are
roots of `P` on the unit circle, and `Polynomial.card_roots_le_degree` bounds
their number by `2 n`.

## Standard reference
Borwein–Erdős, *Polynomials and Polynomial Inequalities* (1995), §5.1; Powell,
*Approximation Theory and Methods*, on trigonometric polynomials.
-/

open Real

namespace Causalean.Mathlib.Analysis.BernsteinSzegoTrig

/-- `IsTrigPolyLE n f` means `f` is a real trigonometric polynomial of degree at
most `n`, i.e. there are coefficient sequences `a b : ℕ → ℝ` with
`f t = ∑_{k=0}^{n} (a k · cos (k t) + b k · sin (k t))` for all `t`. -/
def IsTrigPolyLE (n : ℕ) (f : ℝ → ℝ) : Prop :=
  ∃ a b : ℕ → ℝ, ∀ t, f t
    = ∑ k ∈ Finset.range (n + 1),
        (a k * Real.cos ((k : ℝ) * t) + b k * Real.sin ((k : ℝ) * t))

/-- Constant functions are trigonometric polynomials of degree ≤ `n` (they use
only the `k = 0` term). -/
theorem isTrigPolyLE_const (n : ℕ) (c : ℝ) : IsTrigPolyLE n (fun _ => c) := by
  refine ⟨fun k => if k = 0 then c else 0, fun _ => 0, ?_⟩
  intro t
  simp

/-- A degree-≤`n` trig polynomial is also a degree-≤`m` trig polynomial when
`n ≤ m` (pad the higher coefficients with zeros). -/
theorem IsTrigPolyLE.mono {n m : ℕ} {f : ℝ → ℝ} (hf : IsTrigPolyLE n f)
    (hnm : n ≤ m) : IsTrigPolyLE m f := by
  rcases hf with ⟨a, b, hf⟩
  refine ⟨fun k => if k ≤ n then a k else 0, fun k => if k ≤ n then b k else 0, ?_⟩
  intro t
  rw [hf t]
  calc
    (∑ k ∈ Finset.range (n + 1),
        (a k * Real.cos ((k : ℝ) * t) + b k * Real.sin ((k : ℝ) * t)))
        = ∑ k ∈ Finset.range (n + 1),
            ((if k ≤ n then a k else 0) * Real.cos ((k : ℝ) * t)
              + (if k ≤ n then b k else 0) * Real.sin ((k : ℝ) * t)) := by
          apply Finset.sum_congr rfl
          intro k hk
          have hk_le : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
          simp [hk_le]
    _ = ∑ k ∈ Finset.range (m + 1),
            ((if k ≤ n then a k else 0) * Real.cos ((k : ℝ) * t)
              + (if k ≤ n then b k else 0) * Real.sin ((k : ℝ) * t)) := by
          apply Finset.sum_subset
          · rw [Finset.range_subset_range]
            exact Nat.succ_le_succ hnm
          · intro k _ hkn
            have hle : ¬ k ≤ n := by
              intro hk
              exact hkn (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
            simp [hle]

/-- The difference of two degree-≤`n` trig polynomials is a degree-≤`n` trig
polynomial (subtract the coefficient sequences termwise). -/
theorem IsTrigPolyLE.sub {n : ℕ} {f g : ℝ → ℝ} (hf : IsTrigPolyLE n f)
    (hg : IsTrigPolyLE n g) : IsTrigPolyLE n (fun t => f t - g t) := by
  rcases hf with ⟨af, bf, hf⟩
  rcases hg with ⟨ag, bg, hg⟩
  refine ⟨fun k => af k - ag k, fun k => bf k - bg k, ?_⟩
  intro t
  change f t - g t = _
  rw [hf t, hg t]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

private noncomputable def trigPolyComplexPoly (n : ℕ) (a b : ℕ → ℝ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range (n + 1),
    (Polynomial.C ((a k : ℂ) / 2 - (b k : ℂ) * Complex.I / 2)
        * Polynomial.X ^ (n + k)
      + Polynomial.C ((a k : ℂ) / 2 + (b k : ℂ) * Complex.I / 2)
        * Polynomial.X ^ (n - k))

private lemma exp_mul_I_pow (k : ℕ) (t : ℝ) :
    (Complex.exp ((t : ℂ) * Complex.I)) ^ k =
      Complex.exp ((((k : ℝ) * t : ℝ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_nat_mul]
  congr 1
  norm_num
  ring

private lemma exp_mul_I_pow_sub (n k : ℕ) (t : ℝ) (hk : k ≤ n) :
    (Complex.exp ((t : ℂ) * Complex.I)) ^ (n - k) =
      (Complex.exp ((t : ℂ) * Complex.I)) ^ n *
        ((Complex.exp ((t : ℂ) * Complex.I)) ^ k)⁻¹ := by
  let z := Complex.exp ((t : ℂ) * Complex.I)
  have hzpow_ne : z ^ k ≠ 0 := pow_ne_zero _ (Complex.exp_ne_zero _)
  calc
    z ^ (n - k) = z ^ (n - k) * 1 := by ring
    _ = z ^ (n - k) * (z ^ k * (z ^ k)⁻¹) := by
      rw [mul_inv_cancel₀ hzpow_ne]
    _ = z ^ n * (z ^ k)⁻¹ := by
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hk]

private lemma trigPolyComplexPoly_term_eval (n k : ℕ) (a b t : ℝ) (hk : k ≤ n) :
    Polynomial.eval (Complex.exp ((t : ℂ) * Complex.I))
      (Polynomial.C ((a : ℂ) / 2 - (b : ℂ) * Complex.I / 2) * Polynomial.X ^ (n + k)
        + Polynomial.C ((a : ℂ) / 2 + (b : ℂ) * Complex.I / 2)
          * Polynomial.X ^ (n - k))
      = (Complex.exp ((t : ℂ) * Complex.I)) ^ n *
          (((a * Real.cos ((k : ℝ) * t) + b * Real.sin ((k : ℝ) * t) : ℝ) : ℂ)) := by
  let z := Complex.exp ((t : ℂ) * Complex.I)
  have hz_comm : z = Complex.exp (Complex.I * (t : ℂ)) := by
    rw [show Complex.I * (t : ℂ) = (t : ℂ) * Complex.I by ring]
  have hpow_add : z ^ (n + k) = z ^ n * z ^ k := by rw [pow_add]
  have hpow_sub : z ^ (n - k) = z ^ n * (z ^ k)⁻¹ := exp_mul_I_pow_sub n k t hk
  have hzk : z ^ k = Complex.exp ((((k : ℝ) * t : ℝ) : ℂ) * Complex.I) :=
    exp_mul_I_pow k t
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X]
  rw [hpow_add, hpow_sub, hzk]
  rw [show (Complex.exp ((((k : ℝ) * t : ℝ) : ℂ) * Complex.I))⁻¹ =
      Complex.exp (-(((((k : ℝ) * t : ℝ) : ℂ) * Complex.I))) by
        exact (Complex.exp_neg _).symm]
  rw [show Complex.exp (-(((((k : ℝ) * t : ℝ) : ℂ) * Complex.I))) =
      Complex.exp (((-((k : ℝ) * t) : ℝ) : ℂ) * Complex.I) by
        congr 1
        simp [Complex.ofReal_neg]]
  rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I]
  simp only [Real.cos_neg, Real.sin_neg, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_neg]
  rw [hz_comm]
  rw [show Complex.exp ((t : ℂ) * Complex.I) = Complex.exp (Complex.I * (t : ℂ)) by
    rw [mul_comm]]
  ring_nf
  norm_num [Complex.I_sq]
  exact Mathlib.Tactic.Ring.mul_one _

private lemma trigPolyComplexPoly_eval (n : ℕ) (a b : ℕ → ℝ) (f : ℝ → ℝ)
    (hf : ∀ t, f t = ∑ k ∈ Finset.range (n + 1),
        (a k * Real.cos ((k : ℝ) * t) + b k * Real.sin ((k : ℝ) * t)))
    (t : ℝ) :
    Polynomial.eval (Complex.exp ((t : ℂ) * Complex.I)) (trigPolyComplexPoly n a b) =
      (Complex.exp ((t : ℂ) * Complex.I)) ^ n * ((f t : ℝ) : ℂ) := by
  unfold trigPolyComplexPoly
  simp only [Polynomial.eval_finset_sum, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  calc
    (∑ x ∈ Finset.range (n + 1),
      (((a x : ℂ) / 2 - (b x : ℂ) * Complex.I / 2) *
          Complex.exp ((t : ℂ) * Complex.I) ^ (n + x) +
        ((a x : ℂ) / 2 + (b x : ℂ) * Complex.I / 2) *
          Complex.exp ((t : ℂ) * Complex.I) ^ (n - x))) =
        ∑ x ∈ Finset.range (n + 1),
          Complex.exp ((t : ℂ) * Complex.I) ^ n *
            (((a x * Real.cos ((x : ℝ) * t) + b x * Real.sin ((x : ℝ) * t) : ℝ) : ℂ)) := by
          apply Finset.sum_congr rfl
          intro x hx
          have hx' : x ≤ n := by
            have : x < n + 1 := Finset.mem_range.mp hx
            omega
          simpa [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
            Polynomial.eval_pow, Polynomial.eval_X]
            using trigPolyComplexPoly_term_eval n x (a x) (b x) t hx'
    _ = Complex.exp ((t : ℂ) * Complex.I) ^ n *
        (∑ x ∈ Finset.range (n + 1),
          (((a x * Real.cos ((x : ℝ) * t) + b x * Real.sin ((x : ℝ) * t) : ℝ) : ℂ))) := by
          rw [Finset.mul_sum]
    _ = Complex.exp ((t : ℂ) * Complex.I) ^ n * ((f t : ℝ) : ℂ) := by
          rw [hf t]
          simp only [Complex.ofReal_sum]

private lemma trigPolyComplexPoly_natDegree_le (n : ℕ) (a b : ℕ → ℝ) :
    (trigPolyComplexPoly n a b).natDegree ≤ 2 * n := by
  unfold trigPolyComplexPoly
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  have hk' : k ≤ n := by
    have : k < n + 1 := Finset.mem_range.mp hk
    omega
  apply Polynomial.natDegree_add_le_of_degree_le
  · exact (Polynomial.natDegree_C_mul_X_pow_le
      ((a k : ℂ) / 2 - (b k : ℂ) * Complex.I / 2) (n + k)).trans (by omega)
  · exact (Polynomial.natDegree_C_mul_X_pow_le
      ((a k : ℂ) / 2 + (b k : ℂ) * Complex.I / 2) (n - k)).trans (by omega)

private lemma exp_mul_I_injOn_Ico {c s t : ℝ}
    (hs : s ∈ Set.Ico c (c + 2 * Real.pi)) (ht : t ∈ Set.Ico c (c + 2 * Real.pi))
    (h : Complex.exp ((s : ℂ) * Complex.I) = Complex.exp ((t : ℂ) * Complex.I)) :
    s = t := by
  rcases Complex.exp_eq_exp_iff_exists_int.mp h with ⟨m, hm⟩
  have him : s = t + (m : ℝ) * (2 * Real.pi) := by
    have := congrArg Complex.im hm
    simpa [Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_intCast] using this
  have hdiff : s - t = (m : ℝ) * (2 * Real.pi) := by linarith
  have hlt : -(2 * Real.pi) < s - t ∧ s - t < 2 * Real.pi := by
    constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
  have hpi : 0 < 2 * Real.pi := by positivity
  have hm0 : m = 0 := by
    by_contra hmne
    have hle_abs : 2 * Real.pi ≤ |(m : ℝ) * (2 * Real.pi)| := by
      rw [abs_mul, abs_of_pos hpi]
      have : (1 : ℝ) ≤ |(m : ℝ)| := by
        exact_mod_cast Int.one_le_abs hmne
      nlinarith
    have hbounds : |s - t| < 2 * Real.pi := by
      rw [abs_lt]
      exact hlt
    rw [hdiff] at hbounds
    linarith
  subst hm0
  simpa using him

/-- **Zero-count lemma for real trigonometric polynomials** (the load-bearing
input to Szegő's inequality; not in Mathlib).

If `f` is a real trigonometric polynomial of degree ≤ `n` that is not identically
zero, then `f` has at most `2 n` zeros in any half-open period `[c, c + 2π)`:
for every finite set `S ⊆ [c, c + 2π)` of zeros of `f`, `S.card ≤ 2 n`.

Proof route: put `z = e^{i t}`.  Writing `cos (k t) = (z^k + z^{-k})/2` and
`sin (k t) = (z^k − z^{-k})/(2 i)`, the identity `f t = z^{-n} · P(z)` holds for
an algebraic polynomial `P : ℂ[X]` with `P.natDegree ≤ 2 n`, and `P ≠ 0`
precisely because `f ≢ 0`.  Distinct points of `S` give distinct unit-circle
values `e^{i t}` (since `S` lies in one half-open period), each a root of `P`; hence
`S.card ≤ P.roots.card ≤ P.natDegree ≤ 2 n` via
`Polynomial.card_roots_le_degree`. -/
theorem IsTrigPolyLE.card_zeros_le {n : ℕ} {f : ℝ → ℝ} (hf : IsTrigPolyLE n f)
    (hne : ∃ t, f t ≠ 0) {c : ℝ} {S : Finset ℝ}
    (hS : ↑S ⊆ Set.Ico c (c + 2 * Real.pi)) (hzero : ∀ t ∈ S, f t = 0) :
    S.card ≤ 2 * n := by
  rcases hf with ⟨a, b, hf⟩
  let P := trigPolyComplexPoly n a b
  let e : ℝ → ℂ := fun t => Complex.exp ((t : ℂ) * Complex.I)
  have hPne : P ≠ 0 := by
    rcases hne with ⟨t₀, ht₀⟩
    intro hP
    have hprod : e t₀ ^ n * ((f t₀ : ℝ) : ℂ) = 0 := by
      simpa [P, e, hP] using (trigPolyComplexPoly_eval n a b f hf t₀).symm
    have hfzeroC : ((f t₀ : ℝ) : ℂ) = 0 := by
      exact (mul_eq_zero.mp hprod).resolve_left (pow_ne_zero _ (Complex.exp_ne_zero _))
    exact ht₀ (Complex.ofReal_eq_zero.mp hfzeroC)
  have hinj : Set.InjOn e (S : Set ℝ) := by
    intro s hs t ht hst
    exact exp_mul_I_injOn_Ico (hS hs) (hS ht) hst
  have hsubset : S.image e ⊆ P.roots.toFinset := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨t, htS, rfl⟩
    rw [Multiset.mem_toFinset]
    rw [Polynomial.mem_roots']
    refine ⟨hPne, ?_⟩
    rw [Polynomial.IsRoot.def]
    have heval := trigPolyComplexPoly_eval n a b f hf t
    have hft : ((f t : ℝ) : ℂ) = 0 := by
      rw [hzero t htS]
      norm_num
    simpa [P, e, hft] using heval
  calc
    S.card = (S.image e).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ P.roots.toFinset.card := Finset.card_le_card hsubset
    _ ≤ P.roots.card := Multiset.toFinset_card_le _
    _ ≤ P.natDegree := Polynomial.card_roots' P
    _ ≤ 2 * n := trigPolyComplexPoly_natDegree_le n a b

/-- **Multiplicity-refined zero-count lemma** for real trigonometric polynomials
(the sharp input to Szegő's inequality; not in Mathlib).

If `f` is a real trigonometric polynomial of degree ≤ `n` that is not identically
zero, `S ⊆ [c, c + 2π)` is a finite set of zeros of `f`, and
`t₀ ∈ [c, c + 2π)` is a further zero *of order ≥ 2* — i.e. `f t₀ = 0` **and**
`f' t₀ = 0` (`HasDerivAt f 0 t₀`) — with `t₀ ∉ S`, then

`S.card + 2 ≤ 2 n`.

This is strictly stronger than `card_zeros_le`: the double zero `t₀` is counted
*twice*, while each point of `S` is counted once.  It is the form actually needed
for Szegő's comparison argument, where the comparison difference `Q − S` has
`2n − 1` sign-change zeros plus a double zero at the base point, giving
`(2n − 1) + 2 = 2n + 1 > 2n`, a contradiction.

Proof route: with `z = e^{i t}` write `f t = z^{-n} · P(z)`, `P : ℂ[X]`,
`P.natDegree ≤ 2 n`, `P ≠ 0` (as in `card_zeros_le`).  Differentiating the
identity `P(e^{i t}) = e^{i n t} · f(t)` at `t₀` where `f t₀ = f' t₀ = 0` gives
`P'(e^{i t₀}) = 0`; since also `P(e^{i t₀}) = 0`, the point `e^{i t₀}` is a root of
`P` of multiplicity ≥ 2 (`Polynomial.derivative_rootMultiplicity_of_root`).  The
`S.card` points `e^{i t}` (`t ∈ S`) are distinct roots, all `≠ e^{i t₀}`; counting
them once and adding the double root gives root-multiset cardinality
`≥ S.card + 2`, and
`S.card + 2 ≤ P.roots.card ≤ P.natDegree ≤ 2 n`. -/
theorem IsTrigPolyLE.card_simple_add_double_le {n : ℕ} {f : ℝ → ℝ}
    (hf : IsTrigPolyLE n f) (hne : ∃ t, f t ≠ 0) {c : ℝ} {S : Finset ℝ}
    (hS : ↑S ⊆ Set.Ico c (c + 2 * Real.pi)) (hzero : ∀ t ∈ S, f t = 0)
    {t₀ : ℝ} (ht₀mem : t₀ ∈ Set.Ico c (c + 2 * Real.pi)) (ht₀S : t₀ ∉ S)
    (hf0 : f t₀ = 0) (hderiv : HasDerivAt f 0 t₀) :
    S.card + 2 ≤ 2 * n := by
  classical
  rcases hf with ⟨a, b, hf⟩
  let P := trigPolyComplexPoly n a b
  let e : ℝ → ℂ := fun t => Complex.exp ((t : ℂ) * Complex.I)
  have hPne : P ≠ 0 := by
    rcases hne with ⟨t, ht⟩
    intro hP
    have hprod : e t ^ n * ((f t : ℝ) : ℂ) = 0 := by
      simpa [P, e, hP] using (trigPolyComplexPoly_eval n a b f hf t).symm
    have hfzeroC : ((f t : ℝ) : ℂ) = 0 := by
      exact (mul_eq_zero.mp hprod).resolve_left (pow_ne_zero _ (Complex.exp_ne_zero _))
    exact ht (Complex.ofReal_eq_zero.mp hfzeroC)
  have hroot0 : P.IsRoot (e t₀) := by
    rw [Polynomial.IsRoot.def]
    have heval := trigPolyComplexPoly_eval n a b f hf t₀
    have hf0C : ((f t₀ : ℝ) : ℂ) = 0 := by
      rw [hf0]
      norm_num
    simpa [P, e, hf0C] using heval
  have hder0 : P.derivative.IsRoot (e t₀) := by
    have hcoerce : HasDerivAt (fun t : ℝ => ((t : ℝ) : ℂ)) (1 : ℂ) t₀ := by
      simpa using Complex.ofRealCLM.hasDerivAt (x := t₀)
    have hinner : HasDerivAt (fun t : ℝ => (t : ℂ) * Complex.I) Complex.I t₀ := by
      simpa using hcoerce.mul_const Complex.I
    have he : HasDerivAt e (e t₀ * Complex.I) t₀ := by
      simpa [e] using hinner.cexp
    have hpoly :
        HasDerivAt (fun t : ℝ => P.eval (e t))
          (P.derivative.eval (e t₀) * (e t₀ * Complex.I)) t₀ := by
      simpa using (P.hasDerivAt (e t₀)).comp t₀ he
    have hfC : HasDerivAt (fun t : ℝ => ((f t : ℝ) : ℂ)) (0 : ℂ) t₀ := by
      simpa using hderiv.ofReal_comp
    have hprod :
        HasDerivAt (fun t : ℝ => (e t) ^ n * ((f t : ℝ) : ℂ)) 0 t₀ := by
      have hraw := (he.pow n).mul hfC
      simpa [hf0] using hraw
    have hsame :
        HasDerivAt (fun t : ℝ => P.eval (e t)) 0 t₀ := by
      refine hprod.congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
      intro t
      simpa [P, e] using trigPolyComplexPoly_eval n a b f hf t
    have hmul :
        P.derivative.eval (e t₀) * (e t₀ * Complex.I) = 0 :=
      hpoly.unique hsame
    have hne : e t₀ * Complex.I ≠ 0 := by
      exact mul_ne_zero (Complex.exp_ne_zero _) Complex.I_ne_zero
    rw [Polynomial.IsRoot.def]
    exact (mul_eq_zero.mp hmul).resolve_right hne
  have hmult2 : 2 ≤ P.rootMultiplicity (e t₀) := by
    have hlt : 1 < P.rootMultiplicity (e t₀) :=
      (Polynomial.one_lt_rootMultiplicity_iff_isRoot hPne).2 ⟨hroot0, hder0⟩
    omega
  have hinj : Set.InjOn e ((S : Set ℝ) ∪ {t₀}) := by
    intro s hs t ht hst
    have hsI : s ∈ Set.Ico c (c + 2 * Real.pi) := by
      rcases hs with hsS | rfl
      · exact hS hsS
      · exact ht₀mem
    have htI : t ∈ Set.Ico c (c + 2 * Real.pi) := by
      rcases ht with htS | rfl
      · exact hS htS
      · exact ht₀mem
    exact exp_mul_I_injOn_Ico hsI htI hst
  let A : Finset ℂ := S.image e
  have hcardA : A.card = S.card := by
    have hinjS : Set.InjOn e (S : Set ℝ) := by
      intro s hs t ht hst
      exact hinj (Or.inl hs) (Or.inl ht) hst
    simpa [A] using Finset.card_image_of_injOn hinjS
  have he0_not_mem_A : e t₀ ∉ A := by
    intro hmem
    rcases Finset.mem_image.mp hmem with ⟨t, htS, ht⟩
    have ht_eq : t = t₀ := hinj (Or.inl htS) (Or.inr rfl) ht
    exact ht₀S (ht_eq ▸ htS)
  have hAroots : A ⊆ P.roots.toFinset := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨t, htS, rfl⟩
    rw [Multiset.mem_toFinset]
    rw [Polynomial.mem_roots']
    refine ⟨hPne, ?_⟩
    rw [Polynomial.IsRoot.def]
    have heval := trigPolyComplexPoly_eval n a b f hf t
    have hft : ((f t : ℝ) : ℂ) = 0 := by
      rw [hzero t htS]
      norm_num
    simpa [P, e, hft] using heval
  let T : Multiset ℂ := A.val + Multiset.replicate 2 (e t₀)
  have hTroots : T ≤ P.roots := by
    rw [Multiset.le_iff_count]
    intro z
    by_cases hz0 : z = e t₀
    · subst hz0
      have hAcount : A.val.count (e t₀) = 0 := by
        rw [Multiset.count_eq_zero]
        simpa using he0_not_mem_A
      have hrootcount : 2 ≤ P.roots.count (e t₀) := by
        simpa [Polynomial.count_roots] using hmult2
      change (A.val + Multiset.replicate 2 (e t₀)).count (e t₀) ≤ P.roots.count (e t₀)
      rw [Multiset.count_add, hAcount]
      simpa using hrootcount
    · by_cases hzA : z ∈ A
      · have hAcount : A.val.count z = 1 := by
          exact Multiset.count_eq_one_of_mem A.nodup hzA
        have hrepcount : (Multiset.replicate 2 (e t₀)).count z = 0 := by
          rw [Multiset.count_replicate]
          simp [show ¬ e t₀ = z by exact fun h => hz0 h.symm]
        have hrootmem : z ∈ P.roots := by
          exact Multiset.mem_toFinset.mp (hAroots hzA)
        have hrootcount : 1 ≤ P.roots.count z := by
          exact Multiset.count_pos.mpr hrootmem
        change (A.val + Multiset.replicate 2 (e t₀)).count z ≤ P.roots.count z
        rw [Multiset.count_add, hAcount, hrepcount]
        simpa using hrootcount
      · have hAcount : A.val.count z = 0 := by
          rw [Multiset.count_eq_zero]
          simpa using hzA
        have hrepcount : (Multiset.replicate 2 (e t₀)).count z = 0 := by
          rw [Multiset.count_replicate]
          simp [show ¬ e t₀ = z by exact fun h => hz0 h.symm]
        change (A.val + Multiset.replicate 2 (e t₀)).count z ≤ P.roots.count z
        rw [Multiset.count_add, hAcount, hrepcount]
        simp
  have hTcard : T.card = S.card + 2 := by
    simp [T, hcardA]
  calc
    S.card + 2 = T.card := hTcard.symm
    _ ≤ P.roots.card := Multiset.card_le_card hTroots
    _ ≤ P.natDegree := Polynomial.card_roots' P
    _ ≤ 2 * n := trigPolyComplexPoly_natDegree_le n a b

end Causalean.Mathlib.Analysis.BernsteinSzegoTrig
