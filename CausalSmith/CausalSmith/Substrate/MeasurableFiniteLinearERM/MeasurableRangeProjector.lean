/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

/-!
# Measurable projectors onto finite matrix ranges

This module constructs the orthogonal projector onto the column range of a
finite real matrix.  Ordered Gram--Schmidt is used with its canonical zero
output for dependent columns, so the construction remains Borel measurable
when the rank changes.
-/

namespace CausalSmith.Substrate.MeasurableFiniteLinearERM

open scoped BigOperators RealInnerProductSpace
open InnerProductSpace Matrix MeasureTheory Set Submodule

noncomputable section

variable {n d : ℕ}

private theorem real_inner_eq_mul (x y : ℝ) :
    @inner ℝ ℝ _ x y = x * y := by
  change RCLike.re (y * star x) = x * y
  simp [mul_comm]

/-- The columns of a matrix, regarded as Euclidean vectors. -/
def euclideanColumn (X : Matrix (Fin n) (Fin d) ℝ) (j : Fin d) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (X.col j)

/-- The ordered Gram--Schmidt residual of column `j`. -/
def orthogonalColumn (X : Matrix (Fin n) (Fin d) ℝ) (j : Fin d) :
    EuclideanSpace ℝ (Fin n) :=
  gramSchmidt ℝ (euclideanColumn X) j

/-- The normalized ordered Gram--Schmidt residual, with a zero dependent-column branch. -/
def normalizedColumn (X : Matrix (Fin n) (Fin d) ℝ) (j : Fin d) :
    EuclideanSpace ℝ (Fin n) :=
  gramSchmidtNormed ℝ (euclideanColumn X) j

/-- The matrix whose columns are the normalized Gram--Schmidt residuals of `X`. -/
def normalizedColumnMatrix (X : Matrix (Fin n) (Fin d) ℝ) :
    Matrix (Fin n) (Fin d) ℝ :=
  fun i j ↦ normalizedColumn X j i

/-- The orthogonal projector onto the column range of a finite real matrix.

Dependent Gram--Schmidt columns contribute zero, so this definition is valid
without an invertibility or constant-rank hypothesis. -/
def rangeProjector (X : Matrix (Fin n) (Fin d) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  normalizedColumnMatrix X * (normalizedColumnMatrix X).transpose

/-- Each projector coordinate is the sum of the outer products of the
normalized Gram--Schmidt columns. -/
theorem rangeProjector_apply (X : Matrix (Fin n) (Fin d) ℝ) (i k : Fin n) :
    rangeProjector X i k =
      ∑ j, normalizedColumn X j i * normalizedColumn X j k := by
  simp [rangeProjector, normalizedColumnMatrix, Matrix.mul_apply]

private theorem normalizedColumn_inner_of_ne
    (X : Matrix (Fin n) (Fin d) ℝ) {j k : Fin d} (hjk : j ≠ k) :
    @inner ℝ (EuclideanSpace ℝ (Fin n)) _ (normalizedColumn X j)
      (normalizedColumn X k) = 0 := by
  simp only [normalizedColumn, gramSchmidtNormed, real_inner_smul_left,
    real_inner_smul_right]
  rw [gramSchmidt_orthogonal ℝ (euclideanColumn X) hjk]
  simp

private theorem normalizedColumn_inner_self
    (X : Matrix (Fin n) (Fin d) ℝ) (j : Fin d) :
    @inner ℝ (EuclideanSpace ℝ (Fin n)) _ (normalizedColumn X j)
      (normalizedColumn X j) =
      if normalizedColumn X j = 0 then 0 else 1 := by
  by_cases hj : normalizedColumn X j = 0
  · simp [hj]
  · rw [if_neg hj, real_inner_self_eq_norm_sq]
    have hnorm : ‖normalizedColumn X j‖ = 1 := by
      simpa [normalizedColumn] using
        (gramSchmidtNormed_unit_length' (𝕜 := ℝ) hj)
    rw [hnorm]
    norm_num

private theorem normalizedColumn_orthonormal_or_zero
    (X : Matrix (Fin n) (Fin d) ℝ) (j k : Fin d) :
    @inner ℝ (EuclideanSpace ℝ (Fin n)) _ (normalizedColumn X j)
      (normalizedColumn X k) =
      if j = k then (if normalizedColumn X j = 0 then 0 else 1) else 0 := by
  by_cases hjk : j = k
  · subst k
    simpa using normalizedColumn_inner_self X j
  · simpa [hjk] using normalizedColumn_inner_of_ne X hjk

/-- The range projector is symmetric. -/
theorem rangeProjector_transpose (X : Matrix (Fin n) (Fin d) ℝ) :
    (rangeProjector X).transpose = rangeProjector X := by
  ext i k
  simp only [Matrix.transpose_apply, rangeProjector_apply]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem normalizedColumnMatrix_gram_apply
    (X : Matrix (Fin n) (Fin d) ℝ) (j k : Fin d) :
    ((normalizedColumnMatrix X).transpose * normalizedColumnMatrix X) j k =
      if j = k then (if normalizedColumn X j = 0 then 0 else 1) else 0 := by
  rw [Matrix.mul_apply]
  simpa [normalizedColumnMatrix, PiLp.inner_apply, real_inner_eq_mul] using
    normalizedColumn_orthonormal_or_zero X j k

private theorem normalizedColumnMatrix_gram_mul_transpose
    (X : Matrix (Fin n) (Fin d) ℝ) :
    ((normalizedColumnMatrix X).transpose * normalizedColumnMatrix X) *
        (normalizedColumnMatrix X).transpose =
      (normalizedColumnMatrix X).transpose := by
  ext j i
  rw [Matrix.mul_apply]
  simp_rw [normalizedColumnMatrix_gram_apply]
  simp only [Matrix.transpose_apply]
  by_cases hj : normalizedColumn X j = 0
  · simp [hj, normalizedColumnMatrix]
  · simp [hj, normalizedColumnMatrix]

/-- The range projector is idempotent. -/
theorem rangeProjector_mul_self (X : Matrix (Fin n) (Fin d) ℝ) :
    rangeProjector X * rangeProjector X = rangeProjector X := by
  simp only [rangeProjector]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (normalizedColumnMatrix X).transpose]
  rw [normalizedColumnMatrix_gram_mul_transpose]

/-- The projector rank is at most the number of columns of the original matrix. -/
theorem rangeProjector_rank_le (X : Matrix (Fin n) (Fin d) ℝ) :
    Matrix.rank (rangeProjector X) ≤ d := by
  rw [rangeProjector, Matrix.rank_self_mul_transpose]
  exact Matrix.rank_le_width _

private theorem rangeProjector_mulVec_apply
    (X : Matrix (Fin n) (Fin d) ℝ) (v : Fin n → ℝ) (i : Fin n) :
    (rangeProjector X *ᵥ v) i =
      ∑ j, @inner ℝ (EuclideanSpace ℝ (Fin n)) _ (normalizedColumn X j)
        (WithLp.toLp 2 v) *
        normalizedColumn X j i := by
  simp only [Matrix.mulVec, dotProduct, rangeProjector_apply, PiLp.inner_apply,
    real_inner_eq_mul]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Normalization with the zero convention preserves the span of the original columns. -/
theorem span_normalizedColumn (X : Matrix (Fin n) (Fin d) ℝ) :
    span ℝ (range (normalizedColumn X)) =
      span ℝ (range (euclideanColumn X)) := by
  rw [← span_gramSchmidt ℝ (euclideanColumn X)]
  apply le_antisymm
  · rw [span_le]
    rintro _ ⟨j, rfl⟩
    exact smul_mem _ _ (subset_span ⟨j, rfl⟩)
  · rw [span_le]
    rintro _ ⟨j, rfl⟩
    by_cases hj : gramSchmidt ℝ (euclideanColumn X) j = 0
    · simp [hj]
    · have hmem : normalizedColumn X j ∈ span ℝ (range (normalizedColumn X)) :=
        subset_span ⟨j, rfl⟩
      have hscale :
          (‖gramSchmidt ℝ (euclideanColumn X) j‖ : ℝ) • normalizedColumn X j =
            gramSchmidt ℝ (euclideanColumn X) j := by
        simp [normalizedColumn, gramSchmidtNormed, smul_smul, hj]
      rw [← hscale]
      exact smul_mem _ _ hmem

/-- The normalized Euclidean columns span the raw matrix column space. -/
theorem span_normalizedColumn_coe (X : Matrix (Fin n) (Fin d) ℝ) :
    span ℝ (range (fun j ↦ (normalizedColumn X j : Fin n → ℝ))) =
      span ℝ (range X.col) := by
  have h := congrArg
    (Submodule.map
      (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).toLinearMap)
    (span_normalizedColumn X)
  rw [Submodule.map_span, Submodule.map_span] at h
  change
    span ℝ
        ((WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).toLinearMap '' range (normalizedColumn X)) =
      span ℝ
        ((WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).toLinearMap '' range (euclideanColumn X))
    at h
  have hnormalized :
      ((WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).toLinearMap ''
          range (normalizedColumn X)) =
        range (fun j ↦ (normalizedColumn X j : Fin n → ℝ)) := by
    ext v
    constructor
    · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
      exact ⟨j, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨normalizedColumn X j, ⟨j, rfl⟩, rfl⟩
  have horiginal :
      ((WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).toLinearMap ''
          range (euclideanColumn X)) =
        range X.col := by
    ext v
    constructor
    · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
      exact ⟨j, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨euclideanColumn X j, ⟨j, rfl⟩, by simp [euclideanColumn]⟩
  rw [hnormalized, horiginal] at h
  exact h

private theorem rangeProjector_fixes_normalizedColumn
    (X : Matrix (Fin n) (Fin d) ℝ) (j : Fin d) :
    Matrix.toLin' (rangeProjector X) (normalizedColumn X j : Fin n → ℝ) =
      (normalizedColumn X j : Fin n → ℝ) := by
  ext i
  rw [Matrix.toLin'_apply, rangeProjector_mulVec_apply]
  simp only [WithLp.toLp_ofLp]
  simp_rw [normalizedColumn_orthonormal_or_zero]
  by_cases hj : normalizedColumn X j = 0
  · simp [hj]
  · simp [hj]

/-- A vector is fixed by the range projector exactly when it lies in the
column range of the original matrix. -/
theorem rangeProjector_fixed_iff
    (X : Matrix (Fin n) (Fin d) ℝ) (v : Fin n → ℝ) :
    Matrix.toLin' (rangeProjector X) v = v ↔
      v ∈ LinearMap.range (Matrix.toLin' X) := by
  rw [Matrix.range_toLin', ← span_normalizedColumn_coe]
  constructor
  · intro hv
    rw [← hv]
    have hformula :
        Matrix.toLin' (rangeProjector X) v =
          ∑ j, (@inner ℝ (EuclideanSpace ℝ (Fin n)) _
            (normalizedColumn X j) (WithLp.toLp 2 v)) •
            (normalizedColumn X j : Fin n → ℝ) := by
      ext i
      simp [rangeProjector_mulVec_apply]
    rw [hformula]
    exact Submodule.sum_mem _ fun j _ ↦
      smul_mem _ _ (subset_span ⟨j, rfl⟩)
  · intro hv
    refine LinearMap.eqOn_span
      (f := Matrix.toLin' (rangeProjector X))
      (g := LinearMap.id (R := ℝ) (M := Fin n → ℝ)) ?_ hv
    intro x hx
    rcases hx with ⟨j, rfl⟩
    simpa using rangeProjector_fixes_normalizedColumn X j

private theorem orthogonalColumn_measurable_coord
    {Ω : Type*} [MeasurableSpace Ω]
    (X : Ω → Matrix (Fin n) (Fin d) ℝ)
    (hX : ∀ i j, Measurable fun ω ↦ X ω i j)
    (j : Fin d) (i : Fin n) :
    Measurable fun ω ↦ orthogonalColumn (X ω) j i := by
  letI : MeasurableSpace (EuclideanSpace ℝ (Fin n)) :=
    borel (EuclideanSpace ℝ (Fin n))
  letI : BorelSpace (EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩
  revert i
  apply (Fin.Lt.isWellOrder d).wf.induction j
  intro j ih i
  have hnorm (k : Fin d) (hk : k < j) :
      Measurable fun ω ↦ ‖orthogonalColumn (X ω) k‖ := by
    have hraw :
        Measurable fun ω ↦
          (fun l ↦ orthogonalColumn (X ω) k l : Fin n → ℝ) :=
      measurable_pi_lambda _ fun l ↦ ih k hk l
    have heuc :
        Measurable fun ω ↦
          WithLp.toLp 2
            (fun l ↦ orthogonalColumn (X ω) k l : Fin n → ℝ) :=
      (PiLp.continuous_toLp 2 (fun _ : Fin n ↦ ℝ)).measurable.comp hraw
    simpa only [WithLp.toLp_ofLp] using heuc.norm
  have hinner (k : Fin d) (hk : k < j) :
      Measurable fun ω ↦
        @inner ℝ (EuclideanSpace ℝ (Fin n)) _
          (orthogonalColumn (X ω) k) (euclideanColumn (X ω) j) := by
    have hsum := Finset.univ.measurable_sum fun l _ ↦
      (ih k hk l).mul (hX l j)
    convert hsum using 1
    funext ω
    simp [PiLp.inner_apply, real_inner_eq_mul, euclideanColumn]
  have hsum :
      Measurable fun ω ↦
        ∑ k ∈ Finset.Iio j,
          (@inner ℝ (EuclideanSpace ℝ (Fin n)) _
              (orthogonalColumn (X ω) k) (euclideanColumn (X ω) j) /
            ‖orthogonalColumn (X ω) k‖ ^ 2) *
            orthogonalColumn (X ω) k i := by
    exact (Finset.Iio j).measurable_sum fun k hk ↦
      ((hinner k (Finset.mem_Iio.mp hk)).div
          ((hnorm k (Finset.mem_Iio.mp hk)).pow_const 2)).mul
        (ih k (Finset.mem_Iio.mp hk) i)
  have hmeas :
      Measurable fun ω ↦ X ω i j -
        ∑ k ∈ Finset.Iio j,
          (@inner ℝ (EuclideanSpace ℝ (Fin n)) _
              (orthogonalColumn (X ω) k) (euclideanColumn (X ω) j) /
            ‖orthogonalColumn (X ω) k‖ ^ 2) *
            orthogonalColumn (X ω) k i :=
    (hX i j).sub hsum
  convert hmeas using 1
  funext ω
  apply (eq_sub_iff_add_eq).2
  have heq := congrArg
    (fun z : EuclideanSpace ℝ (Fin n) ↦ z i)
    (gramSchmidt_def'' ℝ (euclideanColumn (X ω)) j)
  simpa [orthogonalColumn, euclideanColumn] using heq.symm

/-- Every coordinate of a normalized ordered Gram--Schmidt column is Borel
measurable in the input matrix coordinates, including at dependent columns. -/
theorem normalizedColumn_measurable_coord
    {Ω : Type*} [MeasurableSpace Ω]
    (X : Ω → Matrix (Fin n) (Fin d) ℝ)
    (hX : ∀ i j, Measurable fun ω ↦ X ω i j)
    (j : Fin d) (i : Fin n) :
    Measurable fun ω ↦ normalizedColumn (X ω) j i := by
  letI : MeasurableSpace (EuclideanSpace ℝ (Fin n)) :=
    borel (EuclideanSpace ℝ (Fin n))
  letI : BorelSpace (EuclideanSpace ℝ (Fin n)) := ⟨rfl⟩
  have hraw :
      Measurable fun ω ↦
        (fun l ↦ orthogonalColumn (X ω) j l : Fin n → ℝ) :=
    measurable_pi_lambda _ fun l ↦
      orthogonalColumn_measurable_coord X hX j l
  have heuc :
      Measurable fun ω ↦ orthogonalColumn (X ω) j := by
    have htoLp :
        Measurable fun ω ↦
          WithLp.toLp 2
            (fun l ↦ orthogonalColumn (X ω) j l : Fin n → ℝ) :=
      (PiLp.continuous_toLp 2 (fun _ : Fin n ↦ ℝ)).measurable.comp hraw
    simpa only [WithLp.toLp_ofLp] using htoLp
  simpa [normalizedColumn, orthogonalColumn, gramSchmidtNormed] using
    heuc.norm.inv.mul (orthogonalColumn_measurable_coord X hX j i)

/-- Every coordinate of the ordered Gram--Schmidt range projector is Borel
measurable, without a constant-rank assumption. -/
theorem rangeProjector_measurable_coord
    {Ω : Type*} [MeasurableSpace Ω]
    (X : Ω → Matrix (Fin n) (Fin d) ℝ)
    (hX : ∀ i j, Measurable fun ω ↦ X ω i j)
    (i k : Fin n) :
    Measurable fun ω ↦ rangeProjector (X ω) i k := by
  simp_rw [rangeProjector_apply]
  exact Finset.univ.measurable_sum fun j _ ↦
    (normalizedColumn_measurable_coord X hX j i).mul
      (normalizedColumn_measurable_coord X hX j k)

/-- The range projector facts needed by conditional projection concentration:
measurable coordinates, symmetry, idempotence, and the column-count rank
bound. -/
theorem rangeProjector_concentration_spec
    {Ω : Type*} [MeasurableSpace Ω]
    (X : Ω → Matrix (Fin n) (Fin d) ℝ)
    (hX : ∀ i j, Measurable fun ω ↦ X ω i j)
    (μ : Measure Ω) :
    (∀ i k, Measurable fun ω ↦ rangeProjector (X ω) i k) ∧
      (∀ᵐ ω ∂μ, (rangeProjector (X ω)).transpose = rangeProjector (X ω)) ∧
      (∀ᵐ ω ∂μ, rangeProjector (X ω) * rangeProjector (X ω) =
        rangeProjector (X ω)) ∧
      (∀ᵐ ω ∂μ, Matrix.rank (rangeProjector (X ω)) ≤ d) := by
  exact ⟨rangeProjector_measurable_coord X hX,
    Filter.Eventually.of_forall fun ω ↦ rangeProjector_transpose (X ω),
    Filter.Eventually.of_forall fun ω ↦ rangeProjector_mul_self (X ω),
    Filter.Eventually.of_forall fun ω ↦ rangeProjector_rank_le (X ω)⟩

end

end CausalSmith.Substrate.MeasurableFiniteLinearERM
