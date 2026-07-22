/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Wooldridge vector (K-regressor) TWFE normal equation

The scalar `ScalarTWFEProblem` is the `K = Fin 1` specialization of the
K-vector TWFE problem, whose full-rank condition is the nonsingularity of the
residualized Gram matrix `Q_{\ddot X} ∈ R^{K×K}`. We build the matrix normal equation, prove
existence and uniqueness of the closed-form coefficient under matrix
invertibility, and show the scalar problem embeds as the singleton-`K` case.

The vector double-demeaned array is component-wise scalar double demeaning, so
all the uniform-panel orthogonality infrastructure is reused.
-/

import Causalean.Panel.EstimandCharacterization.FlexibleDIDMundlak.TWFE
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Matrix.Mul

/-! # Wooldridge Vector TWFE

This file defines the finite-dimensional vector-regressor version of
Wooldridge's two-way fixed effects normal equation on a balanced panel. It
constructs the componentwise residual `ddotVec`, residualized Gram matrix
`gram`, numerator `numer`, and `VectorTWFEProblem.betaTWFE`.  It proves
`vecNormalEq_iff_mulVec`, `VectorTWFEProblem.betaTWFE_normalEq`, and
`VectorTWFEProblem.betaTWFE_unique`, then relates the scalar problem to the
one-coordinate case with `ScalarTWFEProblem.toVector` and
`ScalarTWFEProblem.toVector_betaTWFE`. -/

namespace Causalean
namespace Panel.EstimandCharacterization
namespace FlexibleDIDMundlak

open Finset
open UniformTwoWayPanel

variable {Unit Time : Type*} [Fintype Unit] [Fintype Time]
variable {K : Type*} [Fintype K] [DecidableEq K]

/-- Component-wise double-demeaned vector regressor: the `k`-th coordinate is
the scalar double demean of the `k`-th component field. -/
noncomputable def ddotVec (X : Unit → Time → K → ℝ) (i : Unit) (t : Time) (k : K) : ℝ :=
  ddot (fun i t => X i t k) i t

/-- Residualized Gram matrix `Q_{\ddot X} = Σ_it ddot(X_it) ddot(X_it)ᵀ`. -/
noncomputable def gram (X : Unit → Time → K → ℝ) : Matrix K K ℝ :=
  fun j k => ∑ i, ∑ t, ddotVec X i t j * ddotVec X i t k

/-- Residualized numerator vector `Σ_it ddot(X_it) ddot(Y_it)`. -/
noncomputable def numer (X : Unit → Time → K → ℝ) (Y : Unit → Time → ℝ) : K → ℝ :=
  fun k => ∑ i, ∑ t, ddotVec X i t k * ddot Y i t

/-- Vector TWFE problem on a finite balanced panel. The full-rank condition is
the nonsingularity of the residualized Gram matrix, matching `Q_{\ddot X}`
invertible in the source. -/
structure VectorTWFEProblem (Unit Time : Type*) [Fintype Unit] [Fintype Time]
    (K : Type*) [Fintype K] [DecidableEq K] where
  panel : BalancedPanel Unit Time
  Y : Unit → Time → ℝ
  X : Unit → Time → K → ℝ
  gram_unit : IsUnit (gram X).det

namespace VectorTWFEProblem

/-- Closed-form vector TWFE coefficient `Q_{\ddot X}⁻¹ (Σ_it ddot X ddot Y)`. -/
noncomputable def betaTWFE (P : VectorTWFEProblem Unit Time K) : K → ℝ :=
  (gram P.X)⁻¹.mulVec (numer P.X P.Y)

/-- Vector TWFE normal equation after double demeaning: in every coordinate the
residualized regressor is orthogonal to the residual. -/
def vecTwfeNormalEq (P : VectorTWFEProblem Unit Time K) (β : K → ℝ) : Prop :=
  ∀ k, ∑ i, ∑ t,
    ddotVec P.X i t k * (ddot P.Y i t - ∑ j, ddotVec P.X i t j * β j) = 0

end VectorTWFEProblem

omit [DecidableEq K] in
/-- The coordinate-wise normal equation is equivalent to the matrix normal
equation `Q_{\ddot X} β = Σ_it ddot X ddot Y`. -/
theorem vecNormalEq_iff_mulVec (X : Unit → Time → K → ℝ) (Y : Unit → Time → ℝ)
    (β : K → ℝ) :
    (∀ k, ∑ i, ∑ t,
        ddotVec X i t k * (ddot Y i t - ∑ j, ddotVec X i t j * β j) = 0)
      ↔ (gram X).mulVec β = numer X Y := by
  have key : ∀ k, ∑ i, ∑ t,
      ddotVec X i t k * (ddot Y i t - ∑ j, ddotVec X i t j * β j)
        = numer X Y k - (gram X).mulVec β k := by
    intro k
    have hmv : (gram X).mulVec β k
        = ∑ j, (∑ i, ∑ t, ddotVec X i t k * ddotVec X i t j) * β j := by
      simp only [Matrix.mulVec, dotProduct, gram]
    rw [hmv]
    change ∑ i, ∑ t, ddotVec X i t k * (ddot Y i t - ∑ j, ddotVec X i t j * β j)
      = (∑ i, ∑ t, ddotVec X i t k * ddot Y i t)
        - ∑ j, (∑ i, ∑ t, ddotVec X i t k * ddotVec X i t j) * β j
    -- split off the regressor term and swap the `j` sum outward
    have hsplit : ∑ i, ∑ t, ddotVec X i t k * (ddot Y i t - ∑ j, ddotVec X i t j * β j)
        = (∑ i, ∑ t, ddotVec X i t k * ddot Y i t)
          - ∑ i, ∑ t, ∑ j, ddotVec X i t k * ddotVec X i t j * β j := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      rw [mul_sub, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
    rw [hsplit]
    congr 1
    -- reorder ∑ i ∑ t ∑ j → ∑ j ∑ i ∑ t and pull `β j` out of the i,t sums
    calc ∑ i, ∑ t, ∑ j, ddotVec X i t k * ddotVec X i t j * β j
        = ∑ i, ∑ j, ∑ t, ddotVec X i t k * ddotVec X i t j * β j := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.sum_comm]
      _ = ∑ j, ∑ i, ∑ t, ddotVec X i t k * ddotVec X i t j * β j := by
          rw [Finset.sum_comm]
      _ = ∑ j, (∑ i, ∑ t, ddotVec X i t k * ddotVec X i t j) * β j := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.sum_mul]
  constructor
  · intro h
    funext k
    have := key k
    rw [h k] at this
    -- 0 = numer k - mulVec k  ⇒ mulVec k = numer k
    linarith [this]
  · intro h k
    rw [key k, h]
    ring

namespace VectorTWFEProblem

/-- The closed-form coefficient solves the matrix normal equation: existence of a
TWFE solution under residualized-Gram nonsingularity. -/
theorem betaTWFE_normalEq (P : VectorTWFEProblem Unit Time K) :
    P.vecTwfeNormalEq P.betaTWFE := by
  rw [vecTwfeNormalEq, vecNormalEq_iff_mulVec]
  change (gram P.X).mulVec ((gram P.X)⁻¹.mulVec (numer P.X P.Y)) = numer P.X P.Y
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ P.gram_unit, Matrix.one_mulVec]

/-- Full-rank uniqueness: any solution of the matrix normal equation equals the
closed-form coefficient. -/
theorem betaTWFE_unique (P : VectorTWFEProblem Unit Time K) {β : K → ℝ}
    (hβ : P.vecTwfeNormalEq β) :
    β = P.betaTWFE := by
  have h : (gram P.X).mulVec β = numer P.X P.Y :=
    (vecNormalEq_iff_mulVec P.X P.Y β).mp hβ
  change β = (gram P.X)⁻¹.mulVec (numer P.X P.Y)
  rw [← h, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ P.gram_unit, Matrix.one_mulVec]

end VectorTWFEProblem

/-- The scalar TWFE problem embeds as the singleton-`K = Fin 1` vector problem:
the regressor is the same scalar in the single coordinate and the matrix
full-rank condition reduces to the scalar `ddotX_ss_pos`. -/
noncomputable def ScalarTWFEProblem.toVector (P : ScalarTWFEProblem Unit Time) :
    VectorTWFEProblem Unit Time (Fin 1) where
  panel := P.panel
  Y := P.Y
  X := fun i t _ => P.X i t
  gram_unit := by
    have hval : (gram (fun i t (_ : Fin 1) => P.X i t)).det
        = ∑ i, ∑ t, (ddot P.X i t) ^ 2 := by
      rw [Matrix.det_fin_one]
      simp only [gram, ddotVec]
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun t _ => ?_))
      rw [pow_two]
    rw [hval]
    exact (isUnit_iff_ne_zero).mpr (ne_of_gt P.ddotX_ss_pos)

/-- The singleton-coordinate vector TWFE coefficient recovers the scalar TWFE
coefficient, so the scalar theorem is the `K = Fin 1` case of the vector one. -/
theorem ScalarTWFEProblem.toVector_betaTWFE (P : ScalarTWFEProblem Unit Time) :
    P.toVector.betaTWFE 0 = P.betaTWFE := by
  have hsol : P.toVector.vecTwfeNormalEq (fun _ => P.betaTWFE) := by
    intro k
    have h := P.betaTWFE_normalEq
    rw [ScalarTWFEProblem.twfeNormalEq] at h
    simpa [VectorTWFEProblem.vecTwfeNormalEq, ScalarTWFEProblem.toVector, ddotVec,
      Fin.sum_univ_one] using h
  have heq := P.toVector.betaTWFE_unique hsol
  rw [← heq]

end FlexibleDIDMundlak
end Panel.EstimandCharacterization
end Causalean
