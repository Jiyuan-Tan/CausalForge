/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Mathlib.Analysis.FiniteDimL1LinfDuality.WeakDuality

/-!
# Setup for strong duality: the algebraic Hahn–Banach route

The hard (`primal ≤ dual`) direction is proved with the *sublinear* Hahn–Banach
theorem `exists_extension_of_le_sublinear`, which works on a plain real vector
space (`Fin (k+1) → ℝ`) and needs **no** normed-space / `PiLp` / operator-norm
development.  This file collects the algebraic objects it consumes:

* `coeffPoly b` — the degree-`≤ β` polynomial `∑ i, b i * X^i` with coefficient
  vector `b : Fin (β+1) → ℝ`;
* `Ev p β : (Fin (β+1) → ℝ) →ₗ[ℝ] (Fin (k+1) → ℝ)` — node evaluation
  `b ↦ (∑ i, b i * (p j)^i)_j` (the transpose of the moment map);
* `contrastL β : (Fin (β+1) → ℝ) →ₗ[ℝ] ℝ` — the endpoint contrast
  `b ↦ ∑ i, b i * (1^i - 0^i)` of the coefficient vector;
* `ninf x` — the sup norm `maxⱼ |x j|` on `Fin (k+1) → ℝ`;
* `Ev_injective` — node evaluation is injective for distinct nodes and `β ≤ k`
  (Vandermonde), so the contrast is a *well-defined linear functional* on the
  node-value subspace `range (Ev p β)`;
* `contrastL_le_dual_mul_ninf` — the boundedness estimate
  `contrastL β b ≤ (sSup (dualValSet p β)) * ninf (Ev p β b)`, i.e. the contrast
  functional is dominated by `M · ‖·‖_∞` on the subspace, which is exactly the
  hypothesis of the sublinear Hahn–Banach theorem.

`StrongDuality.lean` assembles these into the extension `g`, reads off the ℓ¹
representing vector `w j = g (Pi.single j 1)`, and derives admissibility and the
norm bound.
-/

open Polynomial

namespace Causalean.Mathlib.Analysis.FiniteDimL1LinfDuality

variable {k β : ℕ} {p : Fin (k + 1) → ℝ}

/-- The degree-`≤ β` polynomial `∑ i, b i * X^i` associated to a coefficient
vector `b : Fin (β+1) → ℝ`.  Its node values are `Ev p β b` and its endpoint
contrast is `contrastL β b`. -/
noncomputable def coeffPoly (b : Fin (β + 1) → ℝ) : Polynomial ℝ :=
  ∑ i, Polynomial.C (b i) * Polynomial.X ^ (i : ℕ)

/-- `coeffPoly b` has degree at most `β` (each monomial `X^i` has `i ≤ β`). -/
theorem coeffPoly_natDegree_le (b : Fin (β + 1) → ℝ) :
    (coeffPoly b).natDegree ≤ β := by
  rw [coeffPoly]
  refine Polynomial.natDegree_sum_le_of_forall_le (s := Finset.univ)
    (f := fun i : Fin (β + 1) => Polynomial.C (b i) * Polynomial.X ^ (i : ℕ)) ?_
  intro i hi
  exact (Polynomial.natDegree_C_mul_X_pow_le (b i) (i : ℕ)).trans
    (Nat.le_of_lt_succ i.isLt)

/-- Evaluating `coeffPoly b` at `t` gives the polynomial value `∑ i, b i * t^i`. -/
theorem coeffPoly_eval (b : Fin (β + 1) → ℝ) (t : ℝ) :
    (coeffPoly b).eval t = ∑ i, b i * t ^ (i : ℕ) := by
  rw [coeffPoly, Polynomial.eval_finset_sum]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

/-- **Node evaluation** as a linear map: `Ev p β b` is the vector of values of
the degree-`≤ β` polynomial with coefficients `b`, sampled at the nodes,
`(Ev p β b) j = ∑ i, b i * (p j)^i`.  This is the transpose of the moment map. -/
def Ev (p : Fin (k + 1) → ℝ) (β : ℕ) :
    (Fin (β + 1) → ℝ) →ₗ[ℝ] (Fin (k + 1) → ℝ) where
  toFun b := fun j => ∑ i, b i * p j ^ (i : ℕ)
  map_add' := by
    intro b c
    ext j
    simp [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' := by
    intro c b
    ext j
    simp [Finset.mul_sum, mul_assoc]

/-- Unfolding lemma for `Ev` (definitional). -/
theorem Ev_apply (b : Fin (β + 1) → ℝ) (j : Fin (k + 1)) :
    Ev p β b j = ∑ i, b i * p j ^ (i : ℕ) := by
  rfl

/-- Node values of `coeffPoly b` coincide with `Ev p β b`. -/
theorem coeffPoly_eval_node (b : Fin (β + 1) → ℝ) (j : Fin (k + 1)) :
    (coeffPoly b).eval (p j) = Ev p β b j := by
  rw [coeffPoly_eval, Ev_apply]

/-- **Endpoint-contrast** functional on coefficient vectors:
`contrastL β b = ∑ i, b i * (if i = 0 then 0 else 1) = r.eval 1 - r.eval 0`
for `r = coeffPoly b`. -/
def contrastL (β : ℕ) : (Fin (β + 1) → ℝ) →ₗ[ℝ] ℝ where
  toFun b := ∑ i, b i * (if (i : ℕ) = 0 then (0 : ℝ) else 1)
  map_add' := by
    intro b c
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro i hi
    by_cases h : (i : ℕ) = 0 <;> simp [h]
  map_smul' := by
    intro c b
    simp [Finset.mul_sum]

/-- Unfolding lemma for `contrastL` (definitional). -/
theorem contrastL_apply (b : Fin (β + 1) → ℝ) :
    contrastL β b = ∑ i, b i * (if (i : ℕ) = 0 then (0 : ℝ) else 1) := by
  rfl

/-- The contrast functional computes the endpoint contrast of `coeffPoly b`. -/
theorem coeffPoly_contrast (b : Fin (β + 1) → ℝ) :
    (coeffPoly b).eval 1 - (coeffPoly b).eval 0 = contrastL β b := by
  rw [coeffPoly_eval, coeffPoly_eval, contrastL_apply]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro i hi
  by_cases h : (i : ℕ) = 0
  · simp [h]
  · simp [h]

/-- **Node evaluation is injective** for distinct nodes and `β ≤ k`.  A degree
`≤ β ≤ k` polynomial vanishing at the `k + 1` distinct nodes has more roots than
its degree, so it is zero; hence its coefficient vector is zero (Vandermonde).
This makes the contrast a well-defined functional on `range (Ev p β)`. -/
theorem Ev_injective (hp : Function.Injective p) (hβ : β ≤ k) :
    Function.Injective (Ev p β) := by
  classical
  let e : Fin (β + 1) → Fin (k + 1) := fun i =>
    ⟨i, Nat.lt_succ_of_le ((Nat.le_of_lt_succ i.isLt).trans hβ)⟩
  let q : Fin (β + 1) → ℝ := fun i => p (e i)
  have hq : Function.Injective q := by
    intro i j hij
    apply Fin.ext
    have heq : e i = e j := hp hij
    simpa [e] using congrArg Fin.val heq
  have hAunit : IsUnit (Matrix.vandermonde q) := by
    refine (Matrix.isUnit_iff_isUnit_det _).mpr ?_
    exact isUnit_iff_ne_zero.mpr ((Matrix.det_vandermonde_ne_zero_iff).mpr hq)
  have hmul_inj : Function.Injective (Matrix.vandermonde q).mulVec :=
    (Matrix.mulVec_injective_iff_isUnit).mpr hAunit
  intro b c hbc
  have hsubEv : Ev p β (b - c) = 0 := by
    rw [map_sub, hbc, sub_self]
  have hsub : b - c = 0 := by
    apply hmul_inj
    ext i
    have hev : Ev p β (b - c) (e i) = 0 := by
      simpa using congr_fun hsubEv (e i)
    calc
      (Matrix.vandermonde q).mulVec (b - c) i
          = ∑ j : Fin (β + 1), q i ^ (j : ℕ) * (b - c) j := by
              simp [Matrix.mulVec, dotProduct, Matrix.vandermonde_apply]
      _ = ∑ j : Fin (β + 1), (b - c) j * p (e i) ^ (j : ℕ) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              simp [q, mul_comm]
      _ = 0 := by
              simpa [Ev_apply] using hev
      _ = (Matrix.vandermonde q).mulVec 0 i := by
              simp [Matrix.mulVec, dotProduct]
  exact sub_eq_zero.mp hsub

/-- Node evaluation of the `ℓ`-th coordinate vector recovers the monomial column
`(p j)^ℓ`. -/
theorem Ev_single (ℓ : Fin (β + 1)) (j : Fin (k + 1)) :
    Ev p β (Pi.single ℓ 1) j = p j ^ (ℓ : ℕ) := by
  rw [Ev_apply]
  rw [Finset.sum_eq_single ℓ]
  · simp
  · intro i hi hne
    simp [Pi.single_eq_of_ne hne]
  · intro h
    exact (h (Finset.mem_univ ℓ)).elim

/-- The contrast of the `ℓ`-th coordinate vector is `1^ℓ - 0^ℓ`. -/
theorem contrastL_single (ℓ : Fin (β + 1)) :
    contrastL β (Pi.single ℓ (1 : ℝ)) = if (ℓ : ℕ) = 0 then (0 : ℝ) else 1 := by
  rw [contrastL_apply]
  rw [Finset.sum_eq_single ℓ]
  · simp
  · intro i hi hne
    simp [Pi.single_eq_of_ne hne]
  · intro h
    exact (h (Finset.mem_univ ℓ)).elim

/-- The **sup norm** `maxⱼ |x j|` on `Fin (k+1) → ℝ` (a `Finset.sup'` over the
nonempty index set).  Used as the majorant `M · ninf` in Hahn–Banach. -/
def ninf (x : Fin (k + 1) → ℝ) : ℝ :=
  Finset.univ.sup' ⟨0, Finset.mem_univ 0⟩ (fun j => |x j|)

/-- Each coordinate is bounded by the sup norm: `|x j| ≤ ninf x`. -/
theorem le_ninf (x : Fin (k + 1) → ℝ) (j : Fin (k + 1)) : |x j| ≤ ninf x := by
  exact Finset.le_sup' (s := Finset.univ) (f := fun j => |x j|) (Finset.mem_univ j)

/-- The sup norm is nonnegative. -/
theorem ninf_nonneg (x : Fin (k + 1) → ℝ) : 0 ≤ ninf x := by
  exact (abs_nonneg (x 0)).trans (le_ninf x 0)

/-- Positive homogeneity (with absolute value) of the sup norm. -/
theorem ninf_smul (c : ℝ) (x : Fin (k + 1) → ℝ) : ninf (c • x) = |c| * ninf x := by
  apply le_antisymm
  · rw [ninf, Finset.sup'_le_iff]
    intro j hj
    calc
      |c • x j| = |c| * |x j| := by
        simp [smul_eq_mul, abs_mul]
      _ ≤ |c| * ninf x :=
        mul_le_mul_of_nonneg_left (le_ninf x j) (abs_nonneg c)
  · obtain ⟨j, hj, hsup⟩ :=
      Finset.exists_mem_eq_sup' (s := Finset.univ) (H := ⟨0, Finset.mem_univ 0⟩)
        (f := fun j => |x j|)
    change |c| * (Finset.univ.sup' ⟨0, Finset.mem_univ 0⟩ fun j => |x j|) ≤
      ninf (c • x)
    rw [hsup]
    calc
      |c| * |x j| = |(c • x) j| := by
        simp [smul_eq_mul, abs_mul]
      _ ≤ ninf (c • x) := le_ninf (c • x) j

/-- Subadditivity (triangle inequality) of the sup norm. -/
theorem ninf_add_le (x y : Fin (k + 1) → ℝ) : ninf (x + y) ≤ ninf x + ninf y := by
  rw [ninf, Finset.sup'_le_iff]
  intro j hj
  calc
    |(x + y) j| = |x j + y j| := by rfl
    _ ≤ |x j| + |y j| := abs_add_le (x j) (y j)
    _ ≤ ninf x + ninf y := add_le_add (le_ninf x j) (le_ninf y j)

/-- The sup norm of a `±1` sign vector is `1`. -/
theorem ninf_sign (s : Fin (k + 1) → ℝ) (hs : ∀ j, |s j| = 1) : ninf s = 1 := by
  rw [ninf]
  exact Finset.sup'_eq_of_forall (s := Finset.univ) (H := ⟨0, Finset.mem_univ 0⟩)
    (f := fun j => |s j|) (fun j hj => hs j)

/-- **Dual value is nonnegative.**  `0 ∈ dualValSet p β` (the zero polynomial)
and the set is bounded above, so its supremum is `≥ 0`. -/
theorem dual_nonneg (hp : Function.Injective p) (hβ : β ≤ k) :
    0 ≤ sSup (dualValSet p β) := by
  have h0 : 0 ∈ dualValSet p β := by
    refine ⟨(0 : Polynomial ℝ), ?_, ?_, ?_⟩
    · simp
    · intro j
      simp
    · simp
  exact le_csSup (dualValSet_bddAbove hp hβ) h0

/-- **Boundedness estimate (the Hahn–Banach hypothesis).**  On the node-value
subspace the contrast functional is dominated by `M · ‖·‖_∞`, where
`M = sSup (dualValSet p β)`:
`contrastL β b ≤ (sSup (dualValSet p β)) * ninf (Ev p β b)`.

Proof idea: let `r = coeffPoly b`, `s = ninf (Ev p β b)`.  If `s = 0` then `r`
vanishes at all nodes, so `r = 0` and both sides are `0`.  If `s > 0`, scale
`r' = (1/s) • r`: then `|r'.eval (p j)| ≤ 1`, so `|r'.eval 1 - r'.eval 0| =
|contrastL β b| / s ∈ dualValSet p β`, hence `≤ M`, i.e. `|contrastL β b| ≤ M s`;
drop the absolute value on the left. -/
theorem contrastL_le_dual_mul_ninf (hp : Function.Injective p) (hβ : β ≤ k)
    (b : Fin (β + 1) → ℝ) :
    contrastL β b ≤ sSup (dualValSet p β) * ninf (Ev p β b) := by
  let M := sSup (dualValSet p β)
  let s := ninf (Ev p β b)
  by_cases hs0 : s = 0
  · have hEvzero : Ev p β b = 0 := by
      ext j
      have hle : |Ev p β b j| ≤ 0 := by
        simpa [s, hs0] using le_ninf (Ev p β b) j
      exact abs_eq_zero.mp (le_antisymm hle (abs_nonneg (Ev p β b j)))
    have hszero : ninf (Ev p β b) = 0 := by
      simpa [s] using hs0
    have hb : b = 0 := (Ev_injective hp hβ) (by simpa using hEvzero)
    simp only [hb, map_zero]
    exact mul_nonneg (dual_nonneg hp hβ) (ninf_nonneg 0)
  · have hspos : 0 < s := by
      exact lt_of_le_of_ne (by simpa [s] using ninf_nonneg (Ev p β b)) (Ne.symm hs0)
    let r' : Polynomial ℝ := s⁻¹ • coeffPoly b
    have hmem : |r'.eval 1 - r'.eval 0| ∈ dualValSet p β := by
      refine ⟨r', ?_, ?_, rfl⟩
      · exact (Polynomial.natDegree_smul_le s⁻¹ (coeffPoly b)).trans
          (coeffPoly_natDegree_le b)
      · intro j
        have hle : |Ev p β b j| ≤ s := by
          simpa [s] using le_ninf (Ev p β b) j
        calc
          |r'.eval (p j)| = |s⁻¹ * Ev p β b j| := by
            rw [show r'.eval (p j) = s⁻¹ * Ev p β b j by
              simp [r', Polynomial.eval_smul, coeffPoly_eval_node]]
          _ = s⁻¹ * |Ev p β b j| := by
            rw [abs_mul, abs_inv, abs_of_pos hspos]
          _ ≤ s⁻¹ * s := by
            exact mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr hspos.le)
          _ = 1 := by
            exact inv_mul_cancel₀ hspos.ne'
    have hdual : |r'.eval 1 - r'.eval 0| ≤ M := by
      exact le_csSup (dualValSet_bddAbove hp hβ) hmem
    have hscaled : r'.eval 1 - r'.eval 0 = s⁻¹ * contrastL β b := by
      calc
        r'.eval 1 - r'.eval 0 =
            s⁻¹ * (coeffPoly b).eval 1 - s⁻¹ * (coeffPoly b).eval 0 := by
          simp [r', Polynomial.eval_smul]
        _ = s⁻¹ * ((coeffPoly b).eval 1 - (coeffPoly b).eval 0) := by
          ring
        _ = s⁻¹ * contrastL β b := by
          rw [coeffPoly_contrast]
    have habs_le : |contrastL β b| ≤ M * s := by
      calc
        |contrastL β b| = s * |s⁻¹ * contrastL β b| := by
          rw [abs_mul, abs_inv, abs_of_pos hspos, ← mul_assoc, mul_inv_cancel₀ hspos.ne',
            one_mul]
        _ ≤ s * M := by
          exact mul_le_mul_of_nonneg_left (by simpa [hscaled] using hdual) hspos.le
        _ = M * s := by
          rw [mul_comm]
    exact (le_abs_self (contrastL β b)).trans (by simpa [M, s] using habs_le)

end Causalean.Mathlib.Analysis.FiniteDimL1LinfDuality
