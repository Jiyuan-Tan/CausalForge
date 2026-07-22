/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Hölder–Taylor remainder bound

Hölder–Taylor remainder bounds for approximating a smooth regression function near a target point
by its degree-`⌊β⌋` Taylor polynomial.

This file proves the standard nonparametric Hölder–Taylor remainder estimate
(Tsybakov, *Introduction to Nonparametric Estimation*, 2009, Chapter 1): if a
scalar function `f` is `⌊β⌋`-times continuously differentiable and its top
derivative is `(β − ⌊β⌋)`-Hölder with constant `M`, then `f` is approximated near
`t` by its degree-`⌊β⌋` Taylor polynomial with error `O(|a − t|^β)`:

`|f a − T_p(a; t)| ≤ (M / p!) · |a − t|^β`.

For noninteger `β`, `p = ⌊β⌋`. For positive integer `β`, `p = β − 1` and the
Hölder exponent is `1`, matching the usual Tsybakov-style convention.

This is the bias-controlling lemma behind interior local-polynomial / kernel
regression: a kernel of order at least `p` annihilates the Taylor polynomial, leaving
only this remainder, which is the source of the `O(h^β)` smoothing bias.
-/

namespace Causalean.Stat.Nonparametric

open scoped BigOperators

/-- The standard Hölder derivative order for smoothness `β`: the largest natural
number strictly below `β`. For positive noninteger `β` this is `⌊β⌋`; for a
positive integer `β = m` this is `m - 1`. -/
noncomputable def holderDerivOrder (β : ℝ) : ℕ := ⌈β⌉₊ - 1

lemma holderDerivOrder_lt {β : ℝ} (hβ : 0 < β) : (holderDerivOrder β : ℝ) < β := by
  have hceil_one : 1 ≤ ⌈β⌉₊ := Nat.one_le_ceil_iff.mpr hβ
  have hcast : ((⌈β⌉₊ - 1 : ℕ) : ℝ) = (⌈β⌉₊ : ℝ) - 1 := by
    rw [Nat.cast_sub hceil_one, Nat.cast_one]
  rw [holderDerivOrder, hcast]
  linarith [Nat.ceil_lt_add_one hβ.le]

/-- Degree-`p` Taylor polynomial of `f` at base point `t`, evaluated at `a`:
`∑_{k ≤ p} f⁽ᵏ⁾(t)/k! · (a − t)^k`. -/
noncomputable def taylorPoly (p : ℕ) (f : ℝ → ℝ) (t a : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (p + 1), iteratedDeriv k f t / (k.factorial : ℝ) * (a - t) ^ k

/-- The Taylor polynomial of `f` at base point `t`, evaluated at `t` itself, is `f t`
(every positive-degree term carries a `(t − t)^k = 0` factor). -/
theorem taylorPoly_eval_base (p : ℕ) (f : ℝ → ℝ) (t : ℝ) : taylorPoly p f t t = f t := by
  have h : taylorPoly p f t t
      = iteratedDeriv 0 f t / (Nat.factorial 0 : ℝ) * (t - t) ^ 0 := by
    unfold taylorPoly
    refine Finset.sum_eq_single 0 (fun k _ hk => ?_) (fun h => ?_)
    · rw [sub_self, zero_pow hk, mul_zero]
    · exact absurd (Finset.mem_range.mpr p.succ_pos) h
  simpa [iteratedDeriv_zero] using h

/-- On an interval with distinct endpoints, the Taylor polynomial computed from
derivatives restricted to the interval equals the usual Taylor polynomial
computed from ordinary derivatives. -/
lemma taylorWithinEval_eq_taylorPoly {f : ℝ → ℝ} {p n : ℕ} {x₀ x : ℝ}
    (hf : ContDiff ℝ p f) (hn : n ≤ p) (hx : x₀ < x) :
    taylorWithinEval f n (Set.Icc x₀ x) x₀ x = taylorPoly n f x₀ x := by
  rw [taylor_within_apply]
  unfold taylorPoly
  refine Finset.sum_congr rfl ?_
  intro k hk
  have hk_le_n : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hk_le_p : k ≤ p := hk_le_n.trans hn
  have hwithin :
      iteratedDerivWithin k f (Set.Icc x₀ x) x₀ = iteratedDeriv k f x₀ := by
    exact iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hx)
      ((hf.of_le (WithTop.coe_le_coe.mpr (ENat.coe_le_coe.mpr hk_le_p))).contDiffAt)
      (Set.left_mem_Icc.mpr hx.le)
  rw [hwithin]
  simp [smul_eq_mul, div_eq_mul_inv, mul_comm, mul_left_comm]

/-- Split the last term off the Taylor polynomial. -/
lemma taylorPoly_succ (n : ℕ) (f : ℝ → ℝ) (t a : ℝ) :
    taylorPoly (n + 1) f t a =
      taylorPoly n f t a
        + iteratedDeriv (n + 1) f t / ((n + 1).factorial : ℝ) * (a - t) ^ (n + 1) := by
  unfold taylorPoly
  rw [Finset.sum_range_succ]

/-- Reflecting across the base point preserves the Taylor polynomial value at the reflected
evaluation point. -/
lemma taylorPoly_reflect (p : ℕ) (f : ℝ → ℝ) (t a : ℝ) :
    taylorPoly p (fun x => f (2 * t - x)) t (2 * t - a) = taylorPoly p f t a := by
  unfold taylorPoly
  refine Finset.sum_congr rfl ?_
  intro k hk
  have hder :=
    congrFun (iteratedDeriv_comp_const_sub (n := k) (f := f) (s := 2 * t)) t
  rw [hder]
  simp only [smul_eq_mul]
  have hbase : 2 * t - t = t := by ring
  have harg : 2 * t - a - t = t - a := by ring
  have hpow : (-1 : ℝ) ^ k * (t - a) ^ k = (a - t) ^ k := by
    rw [← mul_pow]
    congr 1
    ring
  rw [hbase, harg, div_eq_mul_inv]
  calc
    ((-1 : ℝ) ^ k * iteratedDeriv k f t) * (↑k.factorial)⁻¹ * (t - a) ^ k
        = iteratedDeriv k f t * (↑k.factorial)⁻¹ * ((-1 : ℝ) ^ k * (t - a) ^ k) := by
          ring
    _ = iteratedDeriv k f t * (↑k.factorial)⁻¹ * (a - t) ^ k := by
          rw [hpow]

/-- Hölder-Taylor remainder when the evaluation point lies to the right of the base. -/
lemma holder_taylor_remainder_of_lt {f : ℝ → ℝ} {M β lo hi t a : ℝ} {p : ℕ}
    (hM : 0 ≤ M) (ht : t ∈ Set.Icc lo hi) (ha : a ∈ Set.Icc lo hi)
    (hf : ContDiff ℝ p f)
    (hb : ∀ x ∈ Set.Icc lo hi, ∀ y ∈ Set.Icc lo hi,
            |iteratedDeriv p f x - iteratedDeriv p f y|
              ≤ M * |x - y| ^ (β - (p : ℝ)))
    (hp_pos : 0 < p) (hp_le_beta : (p : ℝ) ≤ β) (hlt : t < a) :
    |f a - taylorPoly p f t a| ≤ M / (p.factorial : ℝ) * |a - t| ^ β := by
  have hexp_nonneg : 0 ≤ β - (p : ℝ) := sub_nonneg.mpr hp_le_beta
  have habs_pos : 0 < |a - t| := abs_pos.mpr (sub_ne_zero.mpr hlt.ne')
  set n : ℕ := p - 1 with hn
  have hn_succ : n + 1 = p := by
    simpa [hn] using Nat.succ_pred_eq_of_pos hp_pos
  have hcont : ContDiffOn ℝ (n + 1) f (Set.Icc t a) := by
    change ContDiffOn ℝ (((n + 1 : ℕ) : WithTop ℕ∞)) f (Set.Icc t a)
    rw [hn_succ]
    exact hf.contDiffOn
  rcases taylor_mean_remainder_lagrange_iteratedDeriv (f := f) (x := a) (x₀ := t)
      (n := n) hlt hcont with ⟨ξ, hξ, hrem⟩
  have hwithin_eq :
      taylorWithinEval f n (Set.Icc t a) t a = taylorPoly n f t a :=
    taylorWithinEval_eq_taylorPoly hf (by
      rw [← hn_succ]
      exact Nat.le_succ n) hlt
  have hrem_poly :
      f a - taylorPoly n f t a =
        iteratedDeriv p f ξ * (a - t) ^ p / (p.factorial : ℝ) := by
    rw [← hwithin_eq]
    simpa [hn_succ] using hrem
  have hpoly_succ :
      taylorPoly p f t a =
        taylorPoly n f t a
          + iteratedDeriv p f t / (p.factorial : ℝ) * (a - t) ^ p := by
    rw [← hn_succ]
    exact taylorPoly_succ n f t a
  have hdiff :
      f a - taylorPoly p f t a =
        (iteratedDeriv p f ξ - iteratedDeriv p f t) / (p.factorial : ℝ) * (a - t) ^ p := by
    rw [hpoly_succ]
    rw [sub_add_eq_sub_sub, hrem_poly]
    have hfac : (p.factorial : ℝ) ≠ 0 := by positivity
    field_simp [hfac]
  have hξ_window : ξ ∈ Set.Icc lo hi :=
    ⟨ht.1.trans hξ.1.le, hξ.2.le.trans ha.2⟩
  have hdist : |ξ - t| ≤ |a - t| := by
    rw [abs_of_nonneg (sub_nonneg.mpr hξ.1.le),
      abs_of_nonneg (sub_nonneg.mpr hlt.le)]
    exact sub_le_sub_right hξ.2.le t
  have hpow_le : |ξ - t| ^ (β - (p : ℝ)) ≤ |a - t| ^ (β - (p : ℝ)) :=
    Real.rpow_le_rpow (abs_nonneg _) hdist hexp_nonneg
  have htop :
      |iteratedDeriv p f ξ - iteratedDeriv p f t|
        ≤ M * |a - t| ^ (β - (p : ℝ)) :=
    (hb ξ hξ_window t ht).trans (mul_le_mul_of_nonneg_left hpow_le hM)
  rw [hdiff]
  calc
    |(iteratedDeriv p f ξ - iteratedDeriv p f t) / (p.factorial : ℝ) * (a - t) ^ p|
        = |iteratedDeriv p f ξ - iteratedDeriv p f t| / (p.factorial : ℝ) * |a - t| ^ p := by
          rw [abs_mul, abs_div, abs_pow, abs_of_nonneg (by positivity : 0 ≤ (p.factorial : ℝ))]
    _ ≤ (M * |a - t| ^ (β - (p : ℝ))) / (p.factorial : ℝ) * |a - t| ^ p := by
          gcongr
    _ = M / (p.factorial : ℝ) * |a - t| ^ β := by
          have hcombine :
              |a - t| ^ (β - (p : ℝ)) * |a - t| ^ p = |a - t| ^ β := by
            rw [← Real.rpow_natCast]
            rw [← Real.rpow_add habs_pos]
            ring_nf
          rw [← hcombine]
          ring

/-- **Hölder–Taylor remainder bound under the standard Hölder convention.**
Let `p = holderDerivOrder β`, the largest natural number strictly below `β`, and
let `[lo,hi]` be a window containing `t` and `a`. If `f` is
`p`-times continuously differentiable and its `p`-th derivative is
`(β − p)`-Hölder with constant `M` on the window, then the error of the degree-`p`
Taylor approximation of `f` at `t` is bounded by `(M / p!) · |a − t|^β`. For
positive integer `β = m`, this uses derivative order `m - 1` and Hölder exponent
`1`.

The window form of the Hölder hypothesis is essential: the Lagrange remainder is
evaluated at an interior point `ξ ∈ (t,a) ⊆ [lo,hi]`, so the increment bound must
hold for the pair `(ξ, t)`, not merely `(a, t)`.

The proof splits on `p = holderDerivOrder β`:
* `p = 0`: the bound is exactly the order-`β` Hölder condition on `f` itself,
  since `taylorPoly 0 f t a = f t`.
* `p ≥ 1`: Taylor with the Lagrange remainder
  (`taylor_mean_remainder_lagrange`, applied at order `p − 1` on `[t,a]` or `[a,t]`)
  gives `f a − T_{p−1}(a) = f⁽ᵖ⁾(ξ)/p! · (a − t)^p` for some `ξ` strictly between
  `t` and `a`; subtracting the degree-`p` term yields
  `f a − T_p(a) = (f⁽ᵖ⁾(ξ) − f⁽ᵖ⁾(t))/p! · (a − t)^p`, and the Hölder bound at the
  pair `(ξ,t)` with `|ξ − t| ≤ |a − t|` closes it. -/
theorem holder_taylor_remainder {f : ℝ → ℝ} {M β lo hi t a : ℝ}
    (hβ : 0 < β) (hM : 0 ≤ M)
    (ht : t ∈ Set.Icc lo hi) (ha : a ∈ Set.Icc lo hi)
    (hf : ContDiff ℝ ((holderDerivOrder β)) f)
    (hb : ∀ x ∈ Set.Icc lo hi, ∀ y ∈ Set.Icc lo hi,
            |iteratedDeriv (holderDerivOrder β) f x - iteratedDeriv (holderDerivOrder β) f y|
              ≤ M * |x - y| ^ (β - ((holderDerivOrder β) : ℝ))) :
    |f a - taylorPoly (holderDerivOrder β) f t a|
      ≤ M / ((holderDerivOrder β)).factorial * |a - t| ^ β := by
  have hRHS : 0 ≤ M / (((holderDerivOrder β)).factorial : ℝ) * |a - t| ^ β :=
    mul_nonneg (div_nonneg hM (by positivity)) (Real.rpow_nonneg (abs_nonneg _) _)
  rcases eq_or_ne a t with rfl | hne
  · -- a = t : both sides reduce, LHS = 0
    rw [taylorPoly_eval_base, sub_self, abs_zero]; exact hRHS
  rcases Nat.eq_zero_or_pos (holderDerivOrder β) with hp0 | hppos
  · -- p = 0 : the bound is exactly the order-β Hölder condition on f itself
    have htp : taylorPoly (holderDerivOrder β) f t a = f t := by
      rw [hp0]; simp [taylorPoly, iteratedDeriv_zero]
    rw [htp]
    have hbb := hb a ha t ht
    rw [hp0] at hbb
    simp only [iteratedDeriv_zero, Nat.cast_zero, sub_zero] at hbb
    rw [hp0]
    simp only [Nat.factorial_zero, Nat.cast_one, div_one]
    exact hbb
  · -- p ≥ 1 : Lagrange remainder at order p−1 + Hölder bound on f⁽ᵖ⁾.
    set p : ℕ := (holderDerivOrder β) with hp
    have hp_pos : 0 < p := by simpa [hp] using hppos
    have hp_le_beta : (p : ℝ) ≤ β := by
      simpa [hp] using (holderDerivOrder_lt hβ).le
    have hexp_nonneg : 0 ≤ β - (p : ℝ) := sub_nonneg.mpr hp_le_beta
    have habs_pos : 0 < |a - t| := abs_pos.mpr (sub_ne_zero.mpr hne)
    rcases lt_or_gt_of_ne hne.symm with hlt | hgt
    · -- t < a
      set n : ℕ := p - 1 with hn
      have hn_succ : n + 1 = p := by
        simpa [hn] using Nat.succ_pred_eq_of_pos hp_pos
      have hcont : ContDiffOn ℝ (n + 1) f (Set.Icc t a) := by
        change ContDiffOn ℝ (((n + 1 : ℕ) : WithTop ℕ∞)) f (Set.Icc t a)
        rw [hn_succ]
        exact hf.contDiffOn
      rcases taylor_mean_remainder_lagrange_iteratedDeriv (f := f) (x := a) (x₀ := t)
          (n := n) hlt hcont with ⟨ξ, hξ, hrem⟩
      have hwithin_eq :
          taylorWithinEval f n (Set.Icc t a) t a = taylorPoly n f t a :=
        taylorWithinEval_eq_taylorPoly hf (by
          rw [← hn_succ]
          exact Nat.le_succ n) hlt
      have hrem_poly :
          f a - taylorPoly n f t a =
            iteratedDeriv p f ξ * (a - t) ^ p / (p.factorial : ℝ) := by
        rw [← hwithin_eq]
        simpa [hn_succ] using hrem
      have hpoly_succ :
          taylorPoly p f t a =
            taylorPoly n f t a
              + iteratedDeriv p f t / (p.factorial : ℝ) * (a - t) ^ p := by
        rw [← hn_succ]
        exact taylorPoly_succ n f t a
      have hdiff :
          f a - taylorPoly p f t a =
            (iteratedDeriv p f ξ - iteratedDeriv p f t) / (p.factorial : ℝ) * (a - t) ^ p := by
        rw [hpoly_succ]
        rw [sub_add_eq_sub_sub, hrem_poly]
        have hfac : (p.factorial : ℝ) ≠ 0 := by positivity
        field_simp [hfac]
      have hξ_window : ξ ∈ Set.Icc lo hi :=
        ⟨ht.1.trans hξ.1.le, hξ.2.le.trans ha.2⟩
      have hdist : |ξ - t| ≤ |a - t| := by
        rw [abs_of_nonneg (sub_nonneg.mpr hξ.1.le),
          abs_of_nonneg (sub_nonneg.mpr hlt.le)]
        exact sub_le_sub_right hξ.2.le t
      have hpow_le : |ξ - t| ^ (β - (p : ℝ)) ≤ |a - t| ^ (β - (p : ℝ)) :=
        Real.rpow_le_rpow (abs_nonneg _) hdist hexp_nonneg
      have htop :
          |iteratedDeriv p f ξ - iteratedDeriv p f t|
            ≤ M * |a - t| ^ (β - (p : ℝ)) := by
        simpa [hp] using (hb ξ hξ_window t ht).trans (mul_le_mul_of_nonneg_left hpow_le hM)
      rw [hdiff]
      calc
        |(iteratedDeriv p f ξ - iteratedDeriv p f t) / (p.factorial : ℝ) * (a - t) ^ p|
            = |iteratedDeriv p f ξ - iteratedDeriv p f t| / (p.factorial : ℝ) * |a - t| ^ p := by
              rw [abs_mul, abs_div, abs_pow, abs_of_nonneg (by positivity : 0 ≤ (p.factorial : ℝ))]
        _ ≤ (M * |a - t| ^ (β - (p : ℝ))) / (p.factorial : ℝ) * |a - t| ^ p := by
              gcongr
        _ = M / (p.factorial : ℝ) * |a - t| ^ β := by
              have hcombine :
                  |a - t| ^ (β - (p : ℝ)) * |a - t| ^ p = |a - t| ^ β := by
                rw [← Real.rpow_natCast]
                rw [← Real.rpow_add habs_pos]
                ring_nf
              rw [← hcombine]
              ring
    · -- a < t
      set b : ℝ := 2 * t - a with hb_def
      have htb : t < b := by
        rw [hb_def]
        linarith
      have ht_ref : t ∈ Set.Icc t b := Set.left_mem_Icc.mpr htb.le
      have hb_ref : b ∈ Set.Icc t b := Set.right_mem_Icc.mpr htb.le
      have hf_ref : ContDiff ℝ p (fun x => f (2 * t - x)) := by
        fun_prop
      have hholder_ref :
          ∀ x ∈ Set.Icc t b, ∀ y ∈ Set.Icc t b,
            |iteratedDeriv p (fun x => f (2 * t - x)) x
                - iteratedDeriv p (fun x => f (2 * t - x)) y|
              ≤ M * |x - y| ^ (β - (p : ℝ)) := by
        intro x hx y hy
        have hx_window : 2 * t - x ∈ Set.Icc lo hi := by
          have hax : a ≤ 2 * t - x := by
            have hxb : x ≤ 2 * t - a := by simpa [hb_def] using hx.2
            linarith
          have hxt : 2 * t - x ≤ t := by linarith [hx.1]
          exact ⟨ha.1.trans hax, hxt.trans ht.2⟩
        have hy_window : 2 * t - y ∈ Set.Icc lo hi := by
          have hay : a ≤ 2 * t - y := by
            have hyb : y ≤ 2 * t - a := by simpa [hb_def] using hy.2
            linarith
          have hyt : 2 * t - y ≤ t := by linarith [hy.1]
          exact ⟨ha.1.trans hay, hyt.trans ht.2⟩
        have hxder :=
          congrFun (iteratedDeriv_comp_const_sub (n := p) (f := f) (s := 2 * t)) x
        have hyder :=
          congrFun (iteratedDeriv_comp_const_sub (n := p) (f := f) (s := 2 * t)) y
        rw [hxder, hyder]
        simp only [smul_eq_mul]
        have hsign : |(-1 : ℝ) ^ p| = 1 := by simp
        calc
          |(-1 : ℝ) ^ p * iteratedDeriv p f (2 * t - x)
              - (-1 : ℝ) ^ p * iteratedDeriv p f (2 * t - y)|
              = |iteratedDeriv p f (2 * t - x) - iteratedDeriv p f (2 * t - y)| := by
                rw [← mul_sub, abs_mul, hsign, one_mul]
          _ ≤ M * |(2 * t - x) - (2 * t - y)| ^ (β - (p : ℝ)) :=
                hb (2 * t - x) hx_window (2 * t - y) hy_window
          _ = M * |x - y| ^ (β - (p : ℝ)) := by
                congr 2
                rw [show (2 * t - x) - (2 * t - y) = y - x by ring, abs_sub_comm]
      have href := holder_taylor_remainder_of_lt (f := fun x => f (2 * t - x))
        (M := M) (β := β) (lo := t) (hi := b) (t := t) (a := b) (p := p)
        hM ht_ref hb_ref hf_ref hholder_ref hp_pos hp_le_beta htb
      have hgb : (fun x => f (2 * t - x)) b = f a := by
        have harg : 2 * t - (2 * t - a) = a := by ring
        simp [hb_def, harg]
      have hb_abs : |b - t| = |a - t| := by
        rw [hb_def]
        rw [show 2 * t - a - t = t - a by ring, abs_sub_comm]
      have href' :
          |f a - taylorPoly p f t a| ≤ M / (p.factorial : ℝ) * |b - t| ^ β := by
        simpa [hgb, hb_def, taylorPoly_reflect] using href
      simpa [hb_abs] using href'

end Causalean.Stat.Nonparametric
