/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Stat.Concentration.ConditionalKernel
import Causalean.Stat.Concentration.SubGaussianNorm
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Concentration of projected bounded noise

This module gives a dimension-sensitive tail bound for the squared Euclidean
energy of independent, centered, unit-bounded noise after an orthogonal matrix
projection.  The ambient dimension is replaced by an a priori bound on the
matrix rank.
-/

namespace Causalean.Stat.Concentration

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace

noncomputable section

/-- A matrix admitting a Gram factorization through `r` vectors has rank at
most `r`. -/
theorem matrix_rank_le_of_gram_factor {R ι : Type*} [Nontrivial R] [CommRing R]
    [Fintype ι] {r : ℕ}
    (Pi : Matrix ι ι R) (vectors : Fin r → ι → R)
    (hfactor : ∀ i j, Pi i j = ∑ k, vectors k i * vectors k j) :
    Matrix.rank Pi ≤ r := by
  let B : Matrix ι (Fin r) R := fun i k ↦ vectors k i
  have hPi : Pi = B * B.transpose := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, B]
    exact hfactor i j
  rw [hPi]
  exact (Matrix.rank_mul_le_left B B.transpose).trans <| by
    simpa using Matrix.rank_le_card_width B

/-- The squared Euclidean energy of independent centered unit-bounded noise,
after applying a symmetric idempotent matrix of rank at most `r`, exceeds
`4 * t ^ 2` with probability at most `5 ^ r * exp (-t ^ 2 / 2)`.

The hypotheses say that the matrix is an orthogonal projection and that the
coordinates of the noise are measurable, mutually independent, centered, and
bounded by one almost surely. -/
theorem measure_projection_energy_gt_le
    {Ω : Type*} [MeasurableSpace Ω] {n r : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (eps : Fin n → Ω → ℝ) (Pi : Matrix (Fin n) (Fin n) ℝ)
    (hmeas : ∀ i, AEMeasurable (eps i) P)
    (hbound : ∀ i, ∀ᵐ ω ∂P, |eps i ω| ≤ 1)
    (hcenter : ∀ i, ∫ ω, eps i ω ∂P = 0)
    (hindep : ProbabilityTheory.iIndepFun eps P)
    (hsymm : Pi.transpose = Pi) (hidem : Pi * Pi = Pi)
    (hrank : Matrix.rank Pi ≤ r) {t : ℝ} (ht : 0 ≤ t) :
    P.real {ω | 4 * t ^ 2 <
        ∑ i, (∑ j, Pi i j * eps j ω) ^ 2} ≤
      (5 ^ r : ℝ) * Real.exp (-t ^ 2 / 2) := by
  classical
  let L : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    Matrix.toEuclideanLin Pi
  let V : Submodule ℝ (EuclideanSpace ℝ (Fin n)) := LinearMap.range L
  let Z : Ω → EuclideanSpace ℝ (Fin n) := fun ω ↦
    WithLp.toLp 2 (Pi.mulVec fun j ↦ eps j ω)
  have hZV : ∀ᵐ ω ∂P, Z ω ∈ V := by
    filter_upwards [] with ω
    exact ⟨WithLp.toLp 2 (fun j ↦ eps j ω), rfl⟩
  have hfix (v : EuclideanSpace ℝ (Fin n)) (hv : v ∈ V) :
      Pi.mulVec (WithLp.ofLp v) = WithLp.ofLp v := by
    rcases hv with ⟨u, rfl⟩
    change Pi.mulVec (Pi.mulVec (WithLp.ofLp u)) =
      Pi.mulVec (WithLp.ofLp u)
    rw [Matrix.mulVec_mulVec, hidem]
  have hinner (v : EuclideanSpace ℝ (Fin n)) (hv : v ∈ V) (ω : Ω) :
      inner ℝ v (Z ω) = ∑ j, v j * eps j ω := by
    change dotProduct (Pi.mulVec fun j ↦ eps j ω) (WithLp.ofLp v) =
      dotProduct (WithLp.ofLp v) (fun j ↦ eps j ω)
    rw [dotProduct_comm, Matrix.dotProduct_mulVec]
    have hvec : Matrix.vecMul (WithLp.ofLp v) Pi =
        Pi.mulVec (WithLp.ofLp v) := by
      rw [← Matrix.mulVec_transpose, hsymm]
    rw [hvec, hfix v hv]
  have hsubg (v : EuclideanSpace ℝ (Fin n)) (hv : v ∈ V)
      (hvnorm : ‖v‖ = 1) :
      ProbabilityTheory.HasSubgaussianMGF (fun ω ↦ inner ℝ v (Z ω)) 1 P := by
    have hsumsq : ∑ i, (v i) ^ 2 = 1 := by
      have hsq := EuclideanSpace.norm_sq_eq v
      rw [hvnorm] at hsq
      simpa only [one_pow, Real.norm_eq_abs, sq_abs] using hsq.symm
    have hlin := hasSubgaussianMGF_linearCombination_of_iIndep
      eps (fun i ↦ v i) hmeas hbound hcenter hindep
    have hlin_one :
        ProbabilityTheory.HasSubgaussianMGF
          (fun ω ↦ ∑ i, v i * eps i ω) 1 P := by
      have hnn : (⟨∑ i, (v i) ^ 2, by positivity⟩ : NNReal) = 1 :=
        NNReal.coe_injective hsumsq
      rwa [hnn] at hlin
    convert hlin_one using 1
    funext ω
    exact hinner v hv ω
  have hnet := Causalean.measure_norm_gt_le_five_pow_finrank
    P Z V hZV hsubg ht
  have hrank_eq : Module.finrank ℝ V = Matrix.rank Pi := by
    rw [Matrix.rank_eq_finrank_range_toLin Pi
      (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin n) ℝ).toBasis]
    rfl
  have hfinrank : Module.finrank ℝ V ≤ r := by
    rwa [hrank_eq]
  have hpowers : ((5 ^ Module.finrank ℝ V : ℕ) : ℝ) ≤ (5 ^ r : ℝ) := by
    exact_mod_cast Nat.pow_le_pow_right (by norm_num) hfinrank
  have hevent :
      {ω | 4 * t ^ 2 < ∑ i, (∑ j, Pi i j * eps j ω) ^ 2} =
        {ω | 2 * t < ‖Z ω‖} := by
    ext ω
    change 4 * t ^ 2 < ∑ i, (Z ω i) ^ 2 ↔ 2 * t < ‖Z ω‖
    have hsq : ∑ i, (Z ω i) ^ 2 = ‖Z ω‖ ^ 2 := by
      simpa only [Real.norm_eq_abs, sq_abs] using
        (EuclideanSpace.norm_sq_eq (Z ω)).symm
    rw [hsq]
    constructor <;> intro h
    · nlinarith [norm_nonneg (Z ω)]
    · nlinarith [norm_nonneg (Z ω)]
  rw [hevent]
  refine hnet.trans ?_
  exact mul_le_mul_of_nonneg_right hpowers (Real.exp_nonneg _)

end

end Causalean.Stat.Concentration
