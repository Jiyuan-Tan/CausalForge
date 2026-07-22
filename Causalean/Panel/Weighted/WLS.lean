/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Weighted least-squares characterization of `proj` / `residualize`

This file is the **headline** of the `Causalean.Panel.Weighted.Subspace` algebra: it
proves that the weighted orthogonal projection `c.proj H X` is the unique
solution (modulo behavior off the observed support) to the weighted
least-squares problem

    minimize  ⟨X - h, X - h⟩_ω  over  h ∈ H,

and that the residual-orthogonality condition is equivalent to
WLS-optimality (the WLS first-order condition).

These two theorems are the algebraic foundation of Frisch–Waugh–Lovell:
every downstream estimand paper (Sloczynski, Goodman-Bacon, Sun-Abraham,
DCDH, BJS, MTW, Angrist-Imbens, Wooldridge, …) ultimately expresses its
estimator as a weighted least-squares projection onto a nuisance subspace,
then reads off the implicit weights `ω_r` from `fwl_identity` in
`Causalean/Panel/Weighted/FWL.lean`.

## Main theorems

* `proj_eq_argmin` — `c.proj H X` minimizes the WLS objective over `H`.
* `residualize_orth_iff_argmin` — at any candidate `p ∈ H`, residual
  orthogonality to all of `H` is equivalent to WLS-optimality.
-/

import Causalean.Panel.Weighted.Subspace

/-! # Weighted least-squares optimality

This file proves that the semidefinite weighted projection from
`Causalean.Panel.Weighted.Subspace` has the expected least-squares
characterization. The lemma `ip_self_sub_le_of_orth` gives the forward
orthogonality-to-optimality implication, and `proj_eq_argmin` specializes it to
the chosen weighted projection `c.proj H X`.

The reverse perturbation argument is packaged in `residualize_orth_iff_argmin`:
for any candidate `p ∈ H`, residual orthogonality to every direction in `H` is
equivalent to weighted least-squares optimality. The helper lemmas
`ip_eq_zero_of_zero_on_observed` and `ip_sub_smul_expand` handle the
semidefinite zero-energy case and the quadratic expansion used in that proof. -/

open scoped BigOperators

namespace Causalean
namespace Panel.Weighted
namespace WeightedSupport

variable {R : Type*}
variable [Fintype R] [DecidableEq R]

/-! ### Forward direction: orthogonality ⇒ optimality

The expansion
`⟨X - h, X - h⟩_ω = ⟨X - p, X - p⟩_ω + ⟨p - h, p - h⟩_ω + 2 ⟨X - p, p - h⟩_ω`
combined with `⟨X - p, p - h⟩_ω = 0` (because `p - h ∈ H` and `X - p` is
orthogonal to all of `H`) reduces to
`⟨X - h, X - h⟩_ω = ⟨X - p, X - p⟩_ω + ⟨p - h, p - h⟩_ω ≥ ⟨X - p, X - p⟩_ω`. -/

/-- If `p ∈ H` and the residual `X - p` is `c.ip`-orthogonal to all of `H`,
then `p` minimizes the WLS objective over `H`. -/
lemma ip_self_sub_le_of_orth (c : WeightedSupport R) (H : Submodule ℝ (R → ℝ))
    (X p : R → ℝ) (hp : p ∈ H)
    (horth : ∀ h ∈ H, c.ip (X - p) h = 0)
    {h : R → ℝ} (hh : h ∈ H) :
    c.ip (X - p) (X - p) ≤ c.ip (X - h) (X - h) := by
  -- `X - h = (X - p) + (p - h)`.
  have hph : p - h ∈ H := H.sub_mem hp hh
  have hdecomp : X - h = (X - p) + (p - h) := by
    ext s; simp [sub_eq_add_neg]
  -- Expand the inner product via bilinearity.
  have hcross : c.ip (X - p) (p - h) = 0 := horth (p - h) hph
  have hexpand :
      c.ip (X - h) (X - h)
        = c.ip (X - p) (X - p)
          + c.ip (p - h) (p - h) := by
    -- `⟨(X-p)+(p-h), (X-p)+(p-h)⟩
    --   = ⟨X-p, X-p⟩ + ⟨X-p, p-h⟩ + ⟨p-h, X-p⟩ + ⟨p-h, p-h⟩`.
    rw [hdecomp, c.ip_add_left, c.ip_add_right, c.ip_add_right]
    have hsymm : c.ip (p - h) (X - p) = c.ip (X - p) (p - h) := c.ip_symm _ _
    rw [hsymm, hcross]; ring
  -- `⟨p - h, p - h⟩ ≥ 0`.
  have hpos : 0 ≤ c.ip (p - h) (p - h) := c.ip_self_nonneg (p - h)
  linarith

/-- **The weighted orthogonal projection minimizes the WLS objective over `H`.** -/
theorem proj_eq_argmin (c : WeightedSupport R) (H : Submodule ℝ (R → ℝ))
    (X h : R → ℝ) (hH : h ∈ H) :
    c.ip (X - c.proj H X) (X - c.proj H X) ≤ c.ip (X - h) (X - h) := by
  refine c.ip_self_sub_le_of_orth H X (c.proj H X) (c.proj_mem H X) ?_ hH
  intro g hg
  exact c.proj_orthogonal H X hg

/-! ### Reverse direction: optimality ⇒ orthogonality

The standard perturbation argument: for any `h ∈ H` and `t : ℝ`,
`p + t • h ∈ H`, so
`⟨X - p - t • h, X - p - t • h⟩_ω ≥ ⟨X - p, X - p⟩_ω`.
Expanding gives the quadratic-in-`t` inequality
`-2 t · ⟨X - p, h⟩_ω + t² · ⟨h, h⟩_ω ≥ 0`.

If `⟨h, h⟩_ω > 0`, plug `t = ⟨X-p, h⟩_ω / ⟨h, h⟩_ω` to get
`-⟨X-p, h⟩_ω² / ⟨h, h⟩_ω ≥ 0`, forcing `⟨X-p, h⟩_ω = 0`.

If `⟨h, h⟩_ω = 0`, then `h` vanishes on observed indices, so every summand
of `⟨X - p, h⟩_ω` is zero, hence `⟨X - p, h⟩_ω = 0`. -/

/-- If `h` vanishes on every observed index, then `c.ip A h = 0` for any `A`. -/
lemma ip_eq_zero_of_zero_on_observed (c : WeightedSupport R) (A h : R → ℝ)
    (hh : ∀ r ∈ c.observed, h r = 0) :
    c.ip A h = 0 := by
  unfold ip
  refine Finset.sum_eq_zero ?_
  intro r hr
  rw [hh r hr]; ring

/-- Quadratic-in-`t` expansion used in the perturbation argument:
`⟨X - p - t • h, X - p - t • h⟩_ω
  = ⟨X-p, X-p⟩_ω - 2 t · ⟨X-p, h⟩_ω + t² · ⟨h, h⟩_ω`. -/
lemma ip_sub_smul_expand (c : WeightedSupport R) (X p h : R → ℝ) (t : ℝ) :
    c.ip (X - p - t • h) (X - p - t • h)
      = c.ip (X - p) (X - p) - 2 * t * c.ip (X - p) h
        + t^2 * c.ip h h := by
  have hsub : X - p - t • h = (X - p) + (- (t • h)) := by
    ext s; simp [sub_eq_add_neg]
  rw [hsub]
  rw [c.ip_add_left, c.ip_add_right, c.ip_add_right]
  have hneg : -(t • h) = (-t) • h := by ext s; simp
  have h1 : c.ip (X - p) (-(t • h)) = - (t * c.ip (X - p) h) := by
    rw [hneg, c.ip_smul_right]; ring
  have h2 : c.ip (-(t • h)) (X - p) = - (t * c.ip (X - p) h) := by
    rw [c.ip_symm]; exact h1
  have h3 : c.ip (-(t • h)) (-(t • h)) = t^2 * c.ip h h := by
    rw [hneg, c.ip_smul_left, c.ip_smul_right]; ring
  rw [h1, h2, h3]; ring

/-- **First-order WLS optimality:** at any candidate `p ∈ H`, residual
orthogonality to every direction in `H` is equivalent to WLS-optimality. -/
theorem residualize_orth_iff_argmin
    (c : WeightedSupport R) (H : Submodule ℝ (R → ℝ))
    (X p : R → ℝ) (hp : p ∈ H) :
    (∀ h ∈ H, c.ip (X - p) h = 0) ↔
      (∀ h ∈ H, c.ip (X - p) (X - p) ≤ c.ip (X - h) (X - h)) := by
  constructor
  · -- Forward direction: standard expansion.
    intro horth h hh
    exact c.ip_self_sub_le_of_orth H X p hp horth hh
  · -- Reverse direction: perturbation argument.
    intro hmin h hh
    -- For any `t : ℝ`, `p + t • h ∈ H`.
    -- Note: `X - (p + t • h) = X - p - t • h`.
    have hkey : ∀ t : ℝ,
        c.ip (X - p) (X - p) ≤ c.ip (X - p - t • h) (X - p - t • h) := by
      intro t
      have hpth : p + t • h ∈ H := H.add_mem hp (H.smul_mem t hh)
      have := hmin (p + t • h) hpth
      have heq : X - (p + t • h) = X - p - t • h := by ext s; simp; ring
      rw [heq] at this
      exact this
    -- Combined with the quadratic expansion, this gives
    --   0 ≤ -2 t · ⟨X-p, h⟩_ω + t² · ⟨h, h⟩_ω   for all `t : ℝ`.
    have hquad : ∀ t : ℝ,
        0 ≤ - (2 * t * c.ip (X - p) h) + t^2 * c.ip h h := by
      intro t
      have := hkey t
      have hexp := c.ip_sub_smul_expand X p h t
      linarith
    -- Case split on whether `⟨h, h⟩_ω > 0`.
    by_cases hzero : c.ip h h = 0
    · -- `h` vanishes on observed, so `⟨X - p, h⟩_ω = 0` directly.
      have hvan : ∀ r ∈ c.observed, h r = 0 :=
        (c.ip_self_eq_zero_iff h).mp hzero
      exact c.ip_eq_zero_of_zero_on_observed (X - p) h hvan
    · -- `⟨h, h⟩_ω > 0`.  Plug `t = ⟨X-p, h⟩_ω / ⟨h, h⟩_ω`.
      have hpos : 0 < c.ip h h :=
        lt_of_le_of_ne (c.ip_self_nonneg h) (Ne.symm hzero)
      set a : ℝ := c.ip (X - p) h with ha
      set b : ℝ := c.ip h h with hb
      -- The minimum of `t ↦ -2 a t + b t²` over `t : ℝ` is `-a² / b` at
      -- `t = a / b`.
      have htest := hquad (a / b)
      -- `- (2 * (a/b) * a) + (a/b)² * b = -2 a² / b + a² / b = -a² / b`.
      have hsimp : - (2 * (a / b) * a) + (a / b)^2 * b = - a^2 / b := by
        field_simp
        ring
      rw [hsimp] at htest
      -- So `-a²/b ≥ 0`. Combined with `b > 0`, this forces `a² ≤ 0`,
      -- hence `a = 0`.
      have hineq : - a^2 / b ≥ 0 := htest
      have ha2 : a^2 ≤ 0 := by
        have : - a^2 ≥ 0 := by
          have := (div_nonneg_iff.mp hineq).resolve_right ?_
          · exact this.1
          · push_neg
            intro _
            exact hpos
        linarith
      have ha2nn : 0 ≤ a^2 := sq_nonneg a
      have ha2eq : a^2 = 0 := le_antisymm ha2 ha2nn
      have : a = 0 := by
        have := sq_eq_zero_iff.mp ha2eq
        exact this
      exact this

end WeightedSupport
end Panel.Weighted
end Causalean
