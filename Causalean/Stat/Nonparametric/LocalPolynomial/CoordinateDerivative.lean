/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

/-!
# Bivariate coordinate derivatives and operator-norm bounds

This file represents bivariate multi-index partial derivatives by evaluating
iterated Fréchet derivatives along repeated standard-coordinate directions,
and bounds those evaluations by the multilinear operator norm.
-/

open scoped BigOperators

namespace Causalean.Stat.Nonparametric.LocalPolynomial
/-- Total order of a bivariate coordinate multi-index. -/
def coordinateMultiOrder (alpha : Fin 2 → ℕ) : ℕ := alpha 0 + alpha 1

/-- The ordered list of standard coordinate directions associated with a
bivariate multi-index. -/
noncomputable def coordinateDirections (alpha : Fin 2 → ℕ)
    (k : Fin (coordinateMultiOrder alpha)) : EuclideanSpace ℝ (Fin 2) :=
  if (k : ℕ) < alpha 0 then EuclideanSpace.single 0 1
  else EuclideanSpace.single 1 1

/-- The scalar coordinate partial derivative indexed by `alpha`. -/
noncomputable def coordinatePartial (f : EuclideanSpace ℝ (Fin 2) → ℝ) (alpha : Fin 2 → ℕ)
    (x : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  iteratedFDeriv ℝ (coordinateMultiOrder alpha) f x (coordinateDirections alpha)
/-- Evaluating an iterated Fréchet derivative along the standard coordinate
directions cannot increase its operator norm. -/
-- @node: coordinatePartial_abs_le_iteratedFDeriv_norm
lemma coordinatePartial_abs_le_iteratedFDeriv_norm
    (f : EuclideanSpace ℝ (Fin 2) → ℝ) (alpha : Fin 2 → ℕ) (x : EuclideanSpace ℝ (Fin 2)) :
    |coordinatePartial f alpha x| ≤
      ‖iteratedFDeriv ℝ (coordinateMultiOrder alpha) f x‖ := by
  unfold coordinatePartial
  have h := (iteratedFDeriv ℝ (coordinateMultiOrder alpha) f x).le_opNorm
    (coordinateDirections alpha)
  have hprod : ∏ k : Fin (coordinateMultiOrder alpha),
      ‖coordinateDirections alpha k‖ ≤ 1 := by
    simpa using Finset.prod_le_one (fun _ _ ↦ norm_nonneg _)
      (fun k _ ↦ by
        unfold coordinateDirections
        split <;> simp [EuclideanSpace.norm_single])
  simpa only [Real.norm_eq_abs, mul_one] using
    h.trans (mul_le_mul_of_nonneg_left hprod (norm_nonneg _))

/-- Differences of scalar coordinate partials are bounded by the operator
norm of the corresponding Fréchet-derivative difference. -/
-- @node: coordinatePartial_sub_abs_le_iteratedFDeriv_sub_norm
lemma coordinatePartial_sub_abs_le_iteratedFDeriv_sub_norm
    (f : EuclideanSpace ℝ (Fin 2) → ℝ) (alpha : Fin 2 → ℕ) (x z : EuclideanSpace ℝ (Fin 2)) :
    |coordinatePartial f alpha x - coordinatePartial f alpha z| ≤
      ‖iteratedFDeriv ℝ (coordinateMultiOrder alpha) f x -
        iteratedFDeriv ℝ (coordinateMultiOrder alpha) f z‖ := by
  unfold coordinatePartial
  rw [← ContinuousMultilinearMap.sub_apply]
  have h := (iteratedFDeriv ℝ (coordinateMultiOrder alpha) f x -
    iteratedFDeriv ℝ (coordinateMultiOrder alpha) f z).le_opNorm
      (coordinateDirections alpha)
  have hprod : ∏ k : Fin (coordinateMultiOrder alpha),
      ‖coordinateDirections alpha k‖ ≤ 1 := by
    simpa using Finset.prod_le_one (fun _ _ ↦ norm_nonneg _)
      (fun k _ ↦ by
        unfold coordinateDirections
        split <;> simp [EuclideanSpace.norm_single])
  simpa only [Real.norm_eq_abs, mul_one] using
    h.trans (mul_le_mul_of_nonneg_left hprod (norm_nonneg _))

end Causalean.Stat.Nonparametric.LocalPolynomial
