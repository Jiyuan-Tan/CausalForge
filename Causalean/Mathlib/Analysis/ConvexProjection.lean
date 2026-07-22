/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.StarOrdered
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.Instances.Matrix

/-!
# Projection onto closed convex sets

This module provides metric projection onto a nonempty closed convex subset of a real Hilbert
space, together with its variational, contraction, continuity, and measurability properties.  It
also specializes the construction to a Loewner interval of real matrices, using Frobenius distance,
and supplies the associated matrix inequalities.
-/

namespace Causalean.Mathlib.Analysis

open scoped InnerProductSpace
open Set

section Hilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Metric projection assigns each point in a real Hilbert space its nearest point in a specified
nonempty closed convex set. -/
noncomputable def convexProj (K : Set E) (hne : K.Nonempty) (hc : IsClosed K)
    (hconv : Convex ℝ K) : E → E := fun x =>
  Classical.choose (exists_norm_eq_iInf_of_complete_convex hne hc.isComplete hconv x)

private lemma convexProj_spec (K : Set E) (hne : K.Nonempty) (hc : IsClosed K)
    (hconv : Convex ℝ K) (x : E) :
    convexProj K hne hc hconv x ∈ K ∧
      ‖x - convexProj K hne hc hconv x‖ = ⨅ y : K, ‖x - y‖ :=
  Classical.choose_spec (exists_norm_eq_iInf_of_complete_convex hne hc.isComplete hconv x)

/-- The metric projection of every point belongs to its nonempty closed convex target set. -/
theorem convexProj_mem (K : Set E) (hne : K.Nonempty) (hc : IsClosed K)
    (hconv : Convex ℝ K) (x : E) : convexProj K hne hc hconv x ∈ K :=
  (convexProj_spec K hne hc hconv x).1

/-- The residual from a point to its metric projection has nonpositive inner product with every
feasible direction based at the projection. -/
theorem convexProj_variational (K : Set E) (hne : K.Nonempty) (hc : IsClosed K)
    (hconv : Convex ℝ K) (x : E) (y : E) (hy : y ∈ K) :
    ⟪x - convexProj K hne hc hconv x, y - convexProj K hne hc hconv x⟫_ℝ ≤ 0 := by
  exact (norm_eq_iInf_iff_real_inner_le_zero hconv
    (convexProj_mem K hne hc hconv x)).1 (convexProj_spec K hne hc hconv x).2 y hy

/-- Projecting a point onto a nonempty closed convex set cannot increase its distance from any
point already in that set. -/
theorem convexProj_le_of_mem (K : Set E) (hne : K.Nonempty) (hc : IsClosed K)
    (hconv : Convex ℝ K) (x y : E) (hy : y ∈ K) :
    ‖convexProj K hne hc hconv x - y‖ ≤ ‖x - y‖ := by
  let p := convexProj K hne hc hconv x
  have hv := convexProj_variational K hne hc hconv x y hy
  have hi : 0 ≤ ⟪x - p, p - y⟫_ℝ := by
    rw [show p - y = -(y - p) by abel, inner_neg_right]
    simpa [p] using neg_nonneg.mpr hv
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
  rw [show x - y = (x - p) + (p - y) by abel, norm_add_sq_real]
  nlinarith [sq_nonneg ‖x - p‖]

/-- Every point in a nonempty closed convex target set is unchanged by metric projection onto that
set. -/
theorem convexProj_eq_self (K : Set E) (hne : K.Nonempty) (hc : IsClosed K)
    (hconv : Convex ℝ K) (x : E) (hx : x ∈ K) : convexProj K hne hc hconv x = x := by
  have h := convexProj_le_of_mem K hne hc hconv x x hx
  have : ‖convexProj K hne hc hconv x - x‖ = 0 := le_antisymm (by simpa using h) (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp this)

/-- Metric projection onto a nonempty closed convex set is nonexpansive: projected distances never
exceed the original distances. -/
theorem convexProj_lipschitz (K : Set E) (hne : K.Nonempty) (hc : IsClosed K)
    (hconv : Convex ℝ K) : LipschitzWith 1 (convexProj K hne hc hconv) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  let px := convexProj K hne hc hconv x
  let py := convexProj K hne hc hconv y
  have hx := convexProj_variational K hne hc hconv x py
    (convexProj_mem K hne hc hconv y)
  have hy := convexProj_variational K hne hc hconv y px
    (convexProj_mem K hne hc hconv x)
  have hi : ⟪px - py, px - py⟫_ℝ ≤ ⟪x - y, px - py⟫_ℝ := by
    simp only [inner_sub_left, inner_sub_right, real_inner_comm] at hx hy ⊢
    nlinarith
  have hs : ‖px - py‖ ^ 2 ≤ ‖x - y‖ * ‖px - py‖ := by
    rw [← real_inner_self_eq_norm_sq]
    exact hi.trans (real_inner_le_norm _ _)
  have hn : ‖px - py‖ ≤ ‖x - y‖ := by
    by_cases hz : ‖px - py‖ = 0
    · simp [hz]
    · have hp : 0 < ‖px - py‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
      nlinarith
  simpa [dist_eq_norm, px, py] using hn

/-- Metric projection onto a nonempty closed convex set varies continuously with the point being
projected. -/
theorem continuous_convexProj (K : Set E) (hne : K.Nonempty) (hc : IsClosed K)
    (hconv : Convex ℝ K) : Continuous (convexProj K hne hc hconv) :=
  (convexProj_lipschitz K hne hc hconv).continuous

/-- Metric projection onto a nonempty closed convex set is measurable under the Borel
sigma-algebra of the Hilbert space. -/
theorem measurable_convexProj [MeasurableSpace E] [BorelSpace E] (K : Set E)
    (hne : K.Nonempty) (hc : IsClosed K) (hconv : Convex ℝ K) :
    Measurable (convexProj K hne hc hconv) :=
  (continuous_convexProj K hne hc hconv).measurable

end Hilbert

section Matrices

variable {p : ℕ} {c C : ℝ}

/-- A Loewner interval contains the real matrices bounded between two scalar multiples of the
identity matrix in positive-semidefinite order. -/
def loewnerSet (p : ℕ) (c C : ℝ) : Set (Matrix (Fin p) (Fin p) ℝ) :=
  {G | (G - c • (1 : Matrix (Fin p) (Fin p) ℝ)).PosSemidef ∧
    (C • (1 : Matrix (Fin p) (Fin p) ℝ) - G).PosSemidef}

/-- The Frobenius distance between two real matrices is the square root of the sum of the squared
entrywise differences. -/
noncomputable def frobDist (A B : Matrix (Fin p) (Fin p) ℝ) : ℝ :=
  Real.sqrt (∑ k : Fin p, ∑ l : Fin p, (A k l - B k l) ^ 2)

/-- Finite real matrices are linearly equivalent to Euclidean vectors indexed by pairs of row and
column coordinates. -/
noncomputable def mtx (p : ℕ) :
    Matrix (Fin p) (Fin p) ℝ ≃ₗ[ℝ] EuclideanSpace ℝ (Fin p × Fin p) :=
  (LinearEquiv.curry ℝ ℝ (Fin p) (Fin p)).symm.trans
    (EuclideanSpace.equiv (Fin p × Fin p) ℝ).symm.toLinearEquiv

private noncomputable def mtxHomeo (p : ℕ) :
    Matrix (Fin p) (Fin p) ℝ ≃ₜ EuclideanSpace ℝ (Fin p × Fin p) :=
  Homeomorph.piCurry.symm.trans (EuclideanSpace.equiv (Fin p × Fin p) ℝ).symm.toHomeomorph

/-- The Frobenius distance between two finite real matrices equals the Euclidean norm of their
difference after vectorizing the entries. -/
theorem frobDist_eq_norm (A B : Matrix (Fin p) (Fin p) ℝ) :
    frobDist A B = ‖mtx p A - mtx p B‖ := by
  rw [EuclideanSpace.norm_eq]
  have hmtx (M : Matrix (Fin p) (Fin p) ℝ) (i : Fin p × Fin p) :
      mtx p M i = M i.1 i.2 := rfl
  simp [frobDist, Fintype.sum_prod_type, Real.norm_eq_abs, sq_abs, hmtx]

/-- Frobenius distance is nonnegative. -/
theorem frobDist_nonneg (A B : Matrix (Fin p) (Fin p) ℝ) : 0 ≤ frobDist A B :=
  Real.sqrt_nonneg _

/-- Frobenius distance is symmetric in its two matrix arguments. -/
theorem frobDist_comm (A B : Matrix (Fin p) (Fin p) ℝ) : frobDist A B = frobDist B A := by
  simp only [frobDist]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Frobenius distance satisfies the triangle inequality. -/
theorem frobDist_triangle (A B D : Matrix (Fin p) (Fin p) ℝ) :
    frobDist A D ≤ frobDist A B + frobDist B D := by
  rw [frobDist_eq_norm, frobDist_eq_norm, frobDist_eq_norm]
  exact norm_sub_le_norm_sub_add_norm_sub (mtx p A) (mtx p B) (mtx p D)

/-- A Loewner interval with ordered scalar endpoints is nonempty. -/
theorem loewnerSet_nonempty (p : ℕ) (c C : ℝ) (hcC : c ≤ C) :
    (loewnerSet p c C).Nonempty := by
  refine ⟨c • (1 : Matrix (Fin p) (Fin p) ℝ), ?_⟩
  constructor
  · simpa using (Matrix.PosSemidef.zero :
      (0 : Matrix (Fin p) (Fin p) ℝ).PosSemidef)
  · convert (Matrix.PosSemidef.one.smul (α := ℝ) (sub_nonneg.mpr hcC) :
        ((C - c) • (1 : Matrix (Fin p) (Fin p) ℝ)).PosSemidef) using 1
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring

/-- Every Loewner interval of finite real matrices is convex. -/
theorem loewnerSet_convex (p : ℕ) (c C : ℝ) : Convex ℝ (loewnerSet p c C) := by
  intro A hA B hB a b ha hb hab
  constructor
  · convert (hA.1.smul (α := ℝ) ha).add (hB.1.smul (α := ℝ) hb) using 1
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    rw [show b = 1 - a by linarith]
    ring
  · convert (hA.2.smul (α := ℝ) ha).add (hB.2.smul (α := ℝ) hb) using 1
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    rw [show b = 1 - a by linarith]
    ring

private theorem isClosed_posSemidef (p : ℕ) :
    IsClosed {A : Matrix (Fin p) (Fin p) ℝ | A.PosSemidef} := by
  rw [show {A : Matrix (Fin p) (Fin p) ℝ | A.PosSemidef} =
      {A | A.IsHermitian} ∩ {A | ∀ x, 0 ≤ dotProduct x (A.mulVec x)} by
    ext A; simp [Matrix.posSemidef_iff_dotProduct_mulVec]]
  apply IsClosed.inter
  · rw [show {A : Matrix (Fin p) (Fin p) ℝ | A.IsHermitian} =
        ⋂ i, ⋂ j, {A | A i j = A j i} by
      ext A
      simp only [Matrix.IsHermitian, Matrix.IsSelfAdjoint, Matrix.conjTranspose_apply,
        star_trivial, Set.mem_iInter, Set.mem_setOf_eq]
      constructor
      · intro h i j
        exact congr_fun (congr_fun h i) j |>.symm
      · intro h
        ext i j
        exact (h i j).symm]
    exact isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_eq (continuous_id.matrix_elem i j) (continuous_id.matrix_elem j i)
  · rw [show {A : Matrix (Fin p) (Fin p) ℝ | ∀ x, 0 ≤ dotProduct x (A.mulVec x)} =
        ⋂ x, {A | 0 ≤ dotProduct x (A.mulVec x)} by ext A; simp]
    exact isClosed_iInter fun x => isClosed_Ici.preimage
      (continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const))

/-- Every Loewner interval of finite real matrices is closed in the coordinatewise product
topology. -/
theorem loewnerSet_isClosed (p : ℕ) (c C : ℝ) : IsClosed (loewnerSet p c C) := by
  exact (isClosed_posSemidef p).preimage (by fun_prop) |>.inter
    ((isClosed_posSemidef p).preimage (by fun_prop))

/-- Every matrix in a Loewner interval with a strictly positive lower endpoint is positive
definite. -/
theorem loewnerSet_posDef (hc : 0 < c) (hcC : c ≤ C) {G : Matrix (Fin p) (Fin p) ℝ}
    (hG : G ∈ loewnerSet p c C) : G.PosDef := by
  have hbase : (c • (1 : Matrix (Fin p) (Fin p) ℝ)).PosDef :=
    Matrix.PosDef.one.smul (α := ℝ) hc
  convert hbase.add_posSemidef hG.1 using 1 <;> ext i j <;> simp [loewnerSet]

private theorem mtx_image_isClosed (p : ℕ) (c C : ℝ) :
    IsClosed (mtx p '' loewnerSet p c C) := by
  have he : (mtx p : Matrix (Fin p) (Fin p) ℝ → EuclideanSpace ℝ (Fin p × Fin p)) =
      mtxHomeo p := rfl
  rw [he]
  exact (mtxHomeo p).isClosed_image.mpr (loewnerSet_isClosed p c C)

private noncomputable def loewnerProjAux (p : ℕ) (c C : ℝ) (hcC : c ≤ C) :
    Matrix (Fin p) (Fin p) ℝ → Matrix (Fin p) (Fin p) ℝ := fun G =>
  (mtx p).symm (convexProj (mtx p '' loewnerSet p c C)
    ((loewnerSet_nonempty p c C hcC).image (mtx p))
    (mtx_image_isClosed p c C)
    ((loewnerSet_convex p c C).linear_image (mtx p).toLinearMap) (mtx p G))

/-- Loewner projection is the nearest-point projection in Frobenius geometry when the interval
endpoints are ordered, and is the identity map when they are reversed. -/
noncomputable def loewnerProj (p : ℕ) (c C : ℝ) :
    Matrix (Fin p) (Fin p) ℝ → Matrix (Fin p) (Fin p) ℝ :=
  if h : c ≤ C then loewnerProjAux p c C h else id

/-- When its endpoints are ordered, Loewner projection sends every finite real matrix into the
corresponding Loewner interval. -/
theorem loewnerProj_mem (hc : 0 < c) (hcC : c ≤ C) (G : Matrix (Fin p) (Fin p) ℝ) :
    loewnerProj p c C G ∈ loewnerSet p c C := by
  rw [loewnerProj, dif_pos hcC, loewnerProjAux]
  have hm := convexProj_mem (mtx p '' loewnerSet p c C)
    ((loewnerSet_nonempty p c C hcC).image (mtx p))
    (mtx_image_isClosed p c C)
    ((loewnerSet_convex p c C).linear_image (mtx p).toLinearMap) (mtx p G)
  rcases hm with ⟨S, hS, heq⟩
  simpa [← heq] using hS

/-- With ordered endpoints, Loewner projection cannot increase Frobenius distance from any matrix
already in the corresponding interval. -/
theorem loewnerProj_frobDist_le (hc : 0 < c) (hcC : c ≤ C)
    (G S : Matrix (Fin p) (Fin p) ℝ) (hS : S ∈ loewnerSet p c C) :
    frobDist (loewnerProj p c C G) S ≤ frobDist G S := by
  rw [frobDist_eq_norm, frobDist_eq_norm, loewnerProj, dif_pos hcC, loewnerProjAux]
  simp only [LinearEquiv.apply_symm_apply]
  exact convexProj_le_of_mem (mtx p '' loewnerSet p c C)
    ((loewnerSet_nonempty p c C hcC).image (mtx p))
    (mtx_image_isClosed p c C)
    ((loewnerSet_convex p c C).linear_image (mtx p).toLinearMap) (mtx p G) (mtx p S) ⟨S, hS, rfl⟩

/-- Loewner projection is measurable under the coordinatewise Borel sigma-algebra on finite real
matrix spaces. -/
theorem measurable_loewnerProj (p : ℕ) [MeasurableSpace (Matrix (Fin p) (Fin p) ℝ)]
    [BorelSpace (Matrix (Fin p) (Fin p) ℝ)] (c C : ℝ) :
    Measurable (loewnerProj p c C) := by
  by_cases h : c ≤ C
  · rw [loewnerProj, dif_pos h]
    unfold loewnerProjAux
    have he : (mtx p : Matrix (Fin p) (Fin p) ℝ → EuclideanSpace ℝ (Fin p × Fin p)) =
        mtxHomeo p := rfl
    have hes : ((mtx p).symm : EuclideanSpace ℝ (Fin p × Fin p) →
        Matrix (Fin p) (Fin p) ℝ) = (mtxHomeo p).symm := rfl
    rw [show (fun G => (mtx p).symm (convexProj (mtx p '' loewnerSet p c C)
        ((loewnerSet_nonempty p c C h).image (mtx p)) (mtx_image_isClosed p c C)
        ((loewnerSet_convex p c C).linear_image (mtx p).toLinearMap) (mtx p G))) =
      (mtxHomeo p).symm ∘ convexProj (mtx p '' loewnerSet p c C)
        ((loewnerSet_nonempty p c C h).image (mtx p)) (mtx_image_isClosed p c C)
        ((loewnerSet_convex p c C).linear_image (mtx p).toLinearMap) ∘ mtxHomeo p by
          funext G; simp [Function.comp_apply, he, hes]]
    exact (mtxHomeo p).symm.continuous.comp
      ((continuous_convexProj _ _ _ _).comp (mtxHomeo p).continuous) |>.measurable
  · rw [loewnerProj, dif_neg h]
    exact measurable_id

/-- Multiplying a vector by the difference of two finite real matrices has Euclidean norm at most
their Frobenius distance times the vector's Euclidean norm. -/
theorem mulVec_sub_norm_le (A B : Matrix (Fin p) (Fin p) ℝ) (v : Fin p → ℝ) :
    Real.sqrt (∑ k, ((A - B).mulVec v k) ^ 2) ≤
      frobDist A B * Real.sqrt (∑ k, (v k) ^ 2) := by
  rw [frobDist, ← Real.sqrt_mul
    (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg (A _ _ - B _ _))]
  apply Real.sqrt_le_sqrt
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro k _
  simpa [Matrix.mulVec, frobDist, Matrix.sub_apply] using
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun l : Fin p => A k l - B k l) v)

/-- The inverse of a matrix in a Loewner interval with a positive lower endpoint expands Euclidean
norm by at most the reciprocal of that endpoint. -/
theorem loewnerSet_inv_mulVec_norm_le (hc : 0 < c) (hcC : c ≤ C)
    {G : Matrix (Fin p) (Fin p) ℝ} (hG : G ∈ loewnerSet p c C) (v : Fin p → ℝ) :
    Real.sqrt (∑ k, (G⁻¹.mulVec v k) ^ 2) ≤ Real.sqrt (∑ k, (v k) ^ 2) / c := by
  let z := G⁻¹.mulVec v
  have hpd := loewnerSet_posDef hc hcC hG
  have hu : IsUnit G := hpd.isUnit
  have hudet : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).mp hu
  have hGz : G.mulVec z = v := by
    change G.mulVec (G⁻¹.mulVec v) = v
    calc
      _ = (G * G⁻¹).mulVec v := Matrix.mulVec_mulVec v G G⁻¹
      _ = v := by rw [Matrix.mul_nonsing_inv G hudet, Matrix.one_mulVec]
  have hquad := hG.1.dotProduct_mulVec_nonneg z
  have hlower : c * ∑ k, (z k) ^ 2 ≤ ∑ k, z k * v k := by
    rw [Matrix.sub_mulVec, hGz] at hquad
    have hq : (∑ k, z k * (c * z k)) ≤ ∑ k, z k * v k := by
      simpa [dotProduct, Matrix.smul_mulVec, Matrix.one_mulVec, mul_sub,
        Finset.sum_sub_distrib] using hquad
    calc
      c * ∑ k, (z k) ^ 2 = ∑ k, c * (z k) ^ 2 := Finset.mul_sum _ _ _
      _ = ∑ k, z k * (c * z k) := by
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ ≤ _ := hq
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ z v
  have hsquares : c * (Real.sqrt (∑ k, (z k) ^ 2)) ^ 2 ≤
      Real.sqrt (∑ k, (z k) ^ 2) * Real.sqrt (∑ k, (v k) ^ 2) := by
    rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg (z _))]
    exact hlower.trans hcs
  have hznonneg := Real.sqrt_nonneg (∑ k, (z k) ^ 2)
  have hbound : c * Real.sqrt (∑ k, (z k) ^ 2) ≤ Real.sqrt (∑ k, (v k) ^ 2) := by
    by_cases hz : Real.sqrt (∑ k, (z k) ^ 2) = 0
    · simp [hz]
    · have hzpos : 0 < Real.sqrt (∑ k, (z k) ^ 2) := lt_of_le_of_ne hznonneg (Ne.symm hz)
      nlinarith
  apply (le_div_iff₀ hc).2
  simpa [z, mul_comm] using hbound

end Matrices

end Causalean.Mathlib.Analysis

namespace Causalean.Mathlib.Analysis

/-! The finite matrix space uses its coordinatewise Borel measurable structure.  Keeping these
instances here makes measurability part of the public Loewner-projection interface. -/

/-- Finite real matrices carry the coordinatewise product sigma-algebra. -/
instance matrixMeasurableSpace (p : ℕ) :
    MeasurableSpace (Matrix (Fin p) (Fin p) ℝ) :=
  MeasurableSpace.pi

/-- The coordinatewise measurable structure on finite real matrices agrees with their Borel
sigma-algebra. -/
instance matrixBorelSpace (p : ℕ) :
    BorelSpace (Matrix (Fin p) (Fin p) ℝ) :=
  ⟨by
    change MeasurableSpace.pi = borel (Fin p → Fin p → ℝ)
    exact BorelSpace.measurable_eq⟩

/-- Every matrix already in a nonempty Loewner interval is unchanged by metric projection onto that
interval. -/
theorem loewnerProj_eq_self {p : ℕ} {c C : ℝ} (hc : 0 < c) (hcC : c ≤ C)
    (G : Matrix (Fin p) (Fin p) ℝ) (hG : G ∈ loewnerSet p c C) :
    loewnerProj p c C G = G := by
  rw [loewnerProj, dif_pos hcC, loewnerProjAux]
  rw [convexProj_eq_self (mtx p '' loewnerSet p c C)
    ((loewnerSet_nonempty p c C hcC).image (mtx p))
    (mtx_image_isClosed p c C)
    ((loewnerSet_convex p c C).linear_image (mtx p).toLinearMap)
    (mtx p G) ⟨G, hG, rfl⟩]
  exact (mtx p).symm_apply_apply G

end Causalean.Mathlib.Analysis
