/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Analysis.Normed.Module.Basic

/-!
# Fréchet's functional equation (degree-one case)

Fréchet-style finite-difference arguments appear in classical proofs of independence
characterization theorems. This file proves the foundational degree-one case: a continuous
function with vanishing second forward difference is affine
(`affine_of_continuous_of_second_diff_zero`).

The argument is classical: a vanishing second difference makes `f` midpoint-affine;
subtracting `f 0` yields an additive function; a continuous additive map of real
vector spaces is `ℝ`-linear (`AddMonoidHom.toRealLinearMap`).
-/

namespace Causalean.Mathlib.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Fréchet functional equation, degree one.**  If `f : ℝ → E` is continuous and
its second forward difference vanishes (`f (x+s+s) + f x = f (x+s) + f (x+s)` for
all `x, s`), then `f` is affine: `f x = a + x • b` for some `a, b`. -/
theorem affine_of_continuous_of_second_diff_zero
    {f : ℝ → E} (hf : Continuous f)
    (h2 : ∀ x s : ℝ, f (x + s + s) + f x = f (x + s) + f (x + s)) :
    ∃ a b : E, ∀ x, f x = a + x • b := by
  -- Midpoint identity.
  have hmid : ∀ p q : ℝ, f p + f q = f ((p + q) / 2) + f ((p + q) / 2) := by
    intro p q
    have h := h2 p ((q - p) / 2)
    rw [show p + (q - p) / 2 + (q - p) / 2 = q from by ring,
        show p + (q - p) / 2 = (p + q) / 2 from by ring] at h
    rw [add_comm (f p) (f q)]; exact h
  -- Doubling identity.
  have hdouble : ∀ u : ℝ, f (u + u) + f 0 = f u + f u := by
    intro u; simpa using h2 0 u
  -- Additivity of `x ↦ f x - f 0`.
  have hadd : ∀ a b : ℝ, f (a + b) - f 0 = (f a - f 0) + (f b - f 0) := by
    intro a b
    have hm := hmid (a + a) (b + b)
    rw [show (a + a + (b + b)) / 2 = a + b from by ring] at hm
    have ha := hdouble a
    have hb := hdouble b
    -- `(f a + f a) + (f b + f b) = (f (a+b) + f (a+b)) + (f 0 + f 0)`
    have hsum : (f a + f a) + (f b + f b) = (f (a + b) + f (a + b)) + (f 0 + f 0) := by
      rw [← ha, ← hb,
          show (f (a + a) + f 0) + (f (b + b) + f 0)
              = (f (a + a) + f (b + b)) + (f 0 + f 0) from by abel,
          hm]
    -- Cancel the doubling via the `ℝ`-action.
    have hXY : f a + f b = f (a + b) + f 0 := by
      have h2s : (2 : ℝ) • (f a + f b) = (2 : ℝ) • (f (a + b) + f 0) := by
        rw [two_smul, two_smul,
            show (f a + f b) + (f a + f b) = (f a + f a) + (f b + f b) from by abel,
            show (f (a + b) + f 0) + (f (a + b) + f 0)
                = (f (a + b) + f (a + b)) + (f 0 + f 0) from by abel,
            hsum]
      exact smul_right_injective E two_ne_zero h2s
    have hfab : f (a + b) = (f a + f b) - f 0 := eq_sub_of_add_eq hXY.symm
    rw [hfab]; abel
  -- Continuous additive ⟹ `ℝ`-linear.
  have hgcont : Continuous (fun x => f x - f 0) := hf.sub continuous_const
  let φ : ℝ →+ E := AddMonoidHom.mk' (fun x => f x - f 0) hadd
  let L : ℝ →L[ℝ] E := φ.toRealLinearMap hgcont
  have hLx : ∀ x, L x = f x - f 0 := by
    intro x
    have : ⇑L = ⇑φ := φ.coe_toRealLinearMap hgcont
    rw [this]; rfl
  refine ⟨f 0, L 1, fun x => ?_⟩
  have hlin : f x - f 0 = x • L 1 := by
    rw [← hLx x, show L x = L (x • (1 : ℝ)) from by rw [smul_eq_mul, mul_one], map_smul]
  rw [← hlin]; abel

end Causalean.Mathlib.Analysis
