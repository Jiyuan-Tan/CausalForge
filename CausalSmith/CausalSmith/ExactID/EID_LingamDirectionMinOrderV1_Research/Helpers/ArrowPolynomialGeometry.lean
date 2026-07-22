/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Polynomial geometry of the two arrow maps
-/

import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.ExceptionalGeometryBasic
import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.FiniteCumBand
import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.ApolarRankBridge
import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.ZariskiLocus
import Mathlib.Algebra.MvPolynomial.Funext

namespace CausalSmith.ExactID.EID_LingamDirectionMinOrderV1

open scoped BigOperators

noncomputable section

/-- A cumulant-valued map whose scalar coordinates are polynomials in all
structural parameter coordinates. -/
def IsPolynomialCumMap {m : ℕ} (Φ : ParamSpace ℂ m → CumVec ℂ) : Prop :=
  ∃ coord : ℕ × ℕ → MvPolynomial (ParamCoord m) ℂ,
    ∀ θ r a, MvPolynomial.eval (paramEval θ) (coord (r, a)) = Φ θ r a

private def directPolynomial {m : ℕ} : MvPolynomial (ParamCoord m) ℂ :=
  MvPolynomial.X (Sum.inl ())

private def latentPolynomial {m : ℕ} (i : Fin m) : MvPolynomial (ParamCoord m) ℂ :=
  MvPolynomial.X (Sum.inr (Sum.inl i))

private def weightPolynomial {m : ℕ} (j : Fin (m + 2)) (r : ℕ) :
    MvPolynomial (ParamCoord m) ℂ :=
  MvPolynomial.X (Sum.inr (Sum.inr (j, r)))

private def forwardLoadingPolynomial (m : ℕ) (j : Fin (m + 2)) :
    MvPolynomial (ParamCoord m) ℂ × MvPolynomial (ParamCoord m) ℂ :=
  if h0 : j.val = 0 then (1, directPolynomial)
  else if hlast : j.val = m + 1 then (0, 1)
  else (1, latentPolynomial ⟨j.val - 1, by have := j.isLt; omega⟩)

private def reverseLoadingPolynomial (m : ℕ) (j : Fin (m + 2)) :
    MvPolynomial (ParamCoord m) ℂ × MvPolynomial (ParamCoord m) ℂ :=
  if h0 : j.val = 0 then (1, 0)
  else if hlast : j.val = m + 1 then (directPolynomial, 1)
  else (latentPolynomial ⟨j.val - 1, by have := j.isLt; omega⟩, 1)

private lemma eval_forwardLoadingPolynomial {m : ℕ} (θ : ParamSpace ℂ m)
    (j : Fin (m + 2)) :
    (MvPolynomial.eval (paramEval θ) (forwardLoadingPolynomial m j).1,
      MvPolynomial.eval (paramEval θ) (forwardLoadingPolynomial m j).2) =
      forwardLoading m θ.1 θ.2.1 j := by
  by_cases h0 : j.val = 0
  · simp [forwardLoadingPolynomial, forwardLoading, h0, directPolynomial, paramEval]
  · by_cases hlast : j.val = m + 1
    · simp [forwardLoadingPolynomial, forwardLoading, h0, hlast]
    · simp [forwardLoadingPolynomial, forwardLoading, h0, hlast,
        latentPolynomial, paramEval]

private lemma eval_reverseLoadingPolynomial {m : ℕ} (η : ParamSpace ℂ m)
    (j : Fin (m + 2)) :
    (MvPolynomial.eval (paramEval η) (reverseLoadingPolynomial m j).1,
      MvPolynomial.eval (paramEval η) (reverseLoadingPolynomial m j).2) =
      reverseLoading m η.1 η.2.1 j := by
  by_cases h0 : j.val = 0
  · simp [reverseLoadingPolynomial, reverseLoading, h0]
  · by_cases hlast : j.val = m + 1
    · simp [reverseLoadingPolynomial, reverseLoading, h0, hlast,
        directPolynomial, paramEval]
    · simp [reverseLoadingPolynomial, reverseLoading, h0, hlast,
        latentPolynomial, paramEval]

private def forwardCoordPolynomial (m L r a : ℕ) :
    MvPolynomial (ParamCoord m) ℂ :=
  if 2 ≤ r ∧ r ≤ L ∧ a ≤ r then
    ∑ j : Fin (m + 2), weightPolynomial j r *
      (forwardLoadingPolynomial m j).1 ^ (r - a) *
      (forwardLoadingPolynomial m j).2 ^ a
  else 0

private def reverseCoordPolynomial (m L r a : ℕ) :
    MvPolynomial (ParamCoord m) ℂ :=
  if 2 ≤ r ∧ r ≤ L ∧ a ≤ r then
    ∑ j : Fin (m + 2), weightPolynomial j r *
      (reverseLoadingPolynomial m j).1 ^ (r - a) *
      (reverseLoadingPolynomial m j).2 ^ a
  else 0

/-- Proves that the map called the forward Cumulant Map is Polynomial is polynomial. -/
lemma forwardCumulantMap_isPolynomial (m L : ℕ) :
    IsPolynomialCumMap (forwardCumulantMap m L) := by
  refine ⟨fun ra => forwardCoordPolynomial m L ra.1 ra.2, ?_⟩
  intro θ r a
  simp only [forwardCoordPolynomial, forwardCumulantMap]
  split
  · simp only [map_sum, map_mul, map_pow, weightPolynomial,
      MvPolynomial.eval_X, paramEval]
    apply Finset.sum_congr rfl
    intro j _
    rw [show MvPolynomial.eval (paramEval θ) (forwardLoadingPolynomial m j).1 =
        (forwardLoading m θ.1 θ.2.1 j).1 by
          simpa using congrArg Prod.fst (eval_forwardLoadingPolynomial θ j),
      show MvPolynomial.eval (paramEval θ) (forwardLoadingPolynomial m j).2 =
        (forwardLoading m θ.1 θ.2.1 j).2 by
          simpa using congrArg Prod.snd (eval_forwardLoadingPolynomial θ j)]
  · simp

/-- Proves that the map called the reverse Cumulant Map is Polynomial is polynomial. -/
lemma reverseCumulantMap_isPolynomial (m L : ℕ) :
    IsPolynomialCumMap (reverseCumulantMap m L) := by
  refine ⟨fun ra => reverseCoordPolynomial m L ra.1 ra.2, ?_⟩
  intro η r a
  simp only [reverseCoordPolynomial, reverseCumulantMap]
  split
  · simp only [map_sum, map_mul, map_pow, weightPolynomial,
      MvPolynomial.eval_X, paramEval]
    apply Finset.sum_congr rfl
    intro j _
    rw [show MvPolynomial.eval (paramEval η) (reverseLoadingPolynomial m j).1 =
        (reverseLoading m η.1 η.2.1 j).1 by
          simpa using congrArg Prod.fst (eval_reverseLoadingPolynomial η j),
      show MvPolynomial.eval (paramEval η) (reverseLoadingPolynomial m j).2 =
        (reverseLoading m η.1 η.2.1 j).2 by
          simpa using congrArg Prod.snd (eval_reverseLoadingPolynomial η j)]
  · simp

private def pullbackPolynomial {m : ℕ}
    (coord : ℕ × ℕ → MvPolynomial (ParamCoord m) ℂ)
    (P : MvPolynomial (ℕ × ℕ) ℂ) : MvPolynomial (ParamCoord m) ℂ :=
  MvPolynomial.eval₂Hom MvPolynomial.C coord P

private lemma eval_pullbackPolynomial {m : ℕ} {Φ : ParamSpace ℂ m → CumVec ℂ}
    {coord : ℕ × ℕ → MvPolynomial (ParamCoord m) ℂ}
    (hcoord : ∀ θ r a, MvPolynomial.eval (paramEval θ) (coord (r, a)) = Φ θ r a)
    (θ : ParamSpace ℂ m) (P : MvPolynomial (ℕ × ℕ) ℂ) :
    MvPolynomial.eval (paramEval θ) (pullbackPolynomial coord P) =
      MvPolynomial.eval (fun ra => Φ θ ra.1 ra.2) P := by
  change MvPolynomial.eval (paramEval θ)
      (MvPolynomial.eval₂ MvPolynomial.C coord P) = _
  rw [MvPolynomial.eval_eval₂]
  rw [show (MvPolynomial.eval (paramEval θ)).comp MvPolynomial.C = RingHom.id ℂ by
    ext c
    simp]
  change MvPolynomial.eval (fun s => MvPolynomial.eval (paramEval θ) (coord s)) P = _
  apply congrArg (fun f => MvPolynomial.eval f P)
  funext ra
  exact hcoord θ ra.1 ra.2

/-- The closure of the image of an affine polynomial map is irreducible. -/
lemma cumulantImageVariety_isIrreducible {m : ℕ} {Φ : ParamSpace ℂ m → CumVec ℂ}
    (hΦ : IsPolynomialCumMap Φ) :
    IsIrreducibleZariskiClosed (cumulantImageVariety Φ) := by
  obtain ⟨coord, hcoord⟩ := hΦ
  refine ⟨zariskiClosure_idem _, ?_, ?_⟩
  · exact ⟨Φ default, subset_zariskiClosure _ ⟨default, rfl⟩⟩
  · intro Z₁ Z₂ hZ₁ hZ₂ hunion
    by_contra hne
    push_neg at hne
    obtain ⟨hneq₁, hneq₂⟩ := hne
    have hrange₁ : ¬ Set.range Φ ⊆ Z₁ := by
      intro h
      apply hneq₁
      apply Set.Subset.antisymm
      · have hc := zariskiClosure_mono h
        rw [hZ₁] at hc
        exact hc
      · rw [hunion]
        exact Set.subset_union_left
    have hrange₂ : ¬ Set.range Φ ⊆ Z₂ := by
      intro h
      apply hneq₂
      apply Set.Subset.antisymm
      · have hc := zariskiClosure_mono h
        rw [hZ₂] at hc
        exact hc
      · rw [hunion]
        exact Set.subset_union_right
    obtain ⟨_, ⟨θ₁, rfl⟩, hθ₁⟩ := Set.not_subset.mp hrange₁
    obtain ⟨_, ⟨θ₂, rfl⟩, hθ₂⟩ := Set.not_subset.mp hrange₂
    have hp₁ : ∃ P : MvPolynomial (ℕ × ℕ) ℂ,
        (∀ t ∈ Z₁, MvPolynomial.eval (fun ra => t ra.1 ra.2) P = 0) ∧
        MvPolynomial.eval (fun ra => Φ θ₁ ra.1 ra.2) P ≠ 0 := by
      have hnot : Φ θ₁ ∉ zariskiClosure Z₁ := by
        rw [hZ₁]
        exact hθ₁
      simp only [zariskiClosure, Set.mem_setOf_eq] at hnot
      push_neg at hnot
      exact hnot
    have hp₂ : ∃ P : MvPolynomial (ℕ × ℕ) ℂ,
        (∀ t ∈ Z₂, MvPolynomial.eval (fun ra => t ra.1 ra.2) P = 0) ∧
        MvPolynomial.eval (fun ra => Φ θ₂ ra.1 ra.2) P ≠ 0 := by
      have hnot : Φ θ₂ ∉ zariskiClosure Z₂ := by
        rw [hZ₂]
        exact hθ₂
      simp only [zariskiClosure, Set.mem_setOf_eq] at hnot
      push_neg at hnot
      exact hnot
    obtain ⟨P₁, hP₁Z, hP₁ne⟩ := hp₁
    obtain ⟨P₂, hP₂Z, hP₂ne⟩ := hp₂
    have hprod : pullbackPolynomial coord P₁ * pullbackPolynomial coord P₂ = 0 := by
      apply MvPolynomial.funext
      intro x
      obtain ⟨θ, rfl⟩ := paramEval_surjective m x
      rw [map_zero, map_mul, eval_pullbackPolynomial hcoord,
        eval_pullbackPolynomial hcoord]
      have hx : Φ θ ∈ cumulantImageVariety Φ :=
        subset_zariskiClosure _ ⟨θ, rfl⟩
      rw [hunion] at hx
      rcases hx with hx | hx
      · rw [hP₁Z _ hx, zero_mul]
      · rw [hP₂Z _ hx, mul_zero]
    rcases mul_eq_zero.mp hprod with hzero | hzero
    · exact hP₁ne (by
        rw [← eval_pullbackPolynomial hcoord θ₁ P₁, hzero, map_zero])
    · exact hP₂ne (by
        rw [← eval_pullbackPolynomial hcoord θ₂ P₂, hzero, map_zero])

/-- Proves the stated mathematical property of forward Cumulant Image Variety is Irreducible. -/
lemma forwardCumulantImageVariety_isIrreducible (m L : ℕ) :
    IsIrreducibleZariskiClosed (cumulantImageVariety (forwardCumulantMap m L)) :=
  cumulantImageVariety_isIrreducible (forwardCumulantMap_isPolynomial m L)

/-- Proves the stated mathematical property of reverse Cumulant Image Variety is Irreducible. -/
lemma reverseCumulantImageVariety_isIrreducible (m L : ℕ) :
    IsIrreducibleZariskiClosed (cumulantImageVariety (reverseCumulantMap m L)) :=
  cumulantImageVariety_isIrreducible (reverseCumulantMap_isPolynomial m L)

/-! ### An observable common-axis contraction minor

For a degree-`m+2` differential operator divisible by `X 1`, use the monomial
basis `X 0 ^ (m+1-b) * X 1 ^ (b+1)`, `0 ≤ b < m+2`.  We retain the scalar
contraction at order `m+2` and every coefficient of the degree-`m` contraction
at order `2m+2`.  Up to nonzero row factors, the resulting observable matrix is

`t_(m+2,b+1)` in its first row and
`choose(m,a) * t_(2m+2,a+b+1)` in row `a+1`.

Every reverse loading list contains `(1,0)`.  The direction-evaluation factor
of this matrix therefore has a zero row, so its determinant vanishes on the
whole reverse arrow variety.  On the forward common-axis family the same zero
row is supplied by the loading `(1,ρ₀)=(1,0)`.
-/

private def retainedCumCoordOf {L r a : ℕ} (hr : 2 ≤ r) (hrL : r ≤ L)
    (ha : a ≤ r) : RetainedCumCoord L :=
  ⟨(⟨r, by omega⟩, ⟨a, by omega⟩), hr, ha⟩

/-- The explicit observable contraction matrix restricted to operators
divisible by the horizontal-axis annihilator `X 1`. -/
def horizontalContractionMinorMatrixPolynomial (m : ℕ) :
    Matrix (Fin (m + 2)) (Fin (m + 2))
      (MvPolynomial (RetainedCumCoord (2 * m + 2)) ℂ) :=
  fun i b => Fin.cases
    (MvPolynomial.X (retainedCumCoordOf (r := m + 2) (a := b.1 + 1)
      (by omega) (by omega) (by omega)))
    (fun a => MvPolynomial.C (m.choose a.1 : ℂ) *
      MvPolynomial.X (retainedCumCoordOf (r := 2 * m + 2)
        (a := a.1 + b.1 + 1) (by omega) (by omega) (by omega))) i

/-- The observable contraction-minor polynomial detecting the presence of the
horizontal direction in a length-`m+2` power decomposition. -/
def horizontalContractionMinorPolynomial (m : ℕ) :
    MvPolynomial (RetainedCumCoord (2 * m + 2)) ℂ :=
  (horizontalContractionMinorMatrixPolynomial m).det

private def horizontalContractionMinorMatrix (m : ℕ) (t : CumVec ℂ) :
    Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ :=
  fun i b => Fin.cases (t (m + 2) (b.1 + 1))
    (fun a => (m.choose a.1 : ℂ) * t (2 * m + 2) (a.1 + b.1 + 1)) i

lemma eval_horizontalContractionMinorPolynomial (m : ℕ) (t : CumVec ℂ) :
    MvPolynomial.eval (restrictCumBand (2 * m + 2) t)
        (horizontalContractionMinorPolynomial m) =
      (horizontalContractionMinorMatrix m t).det := by
  rw [horizontalContractionMinorPolynomial, RingHom.map_det]
  congr 1
  ext i b
  refine Fin.cases ?_ (fun a => ?_) i
  · simp [horizontalContractionMinorMatrixPolynomial,
      horizontalContractionMinorMatrix, restrictCumBand, retainedCumCoordOf]
  · simp [horizontalContractionMinorMatrixPolynomial,
      horizontalContractionMinorMatrix, restrictCumBand, retainedCumCoordOf]

private def selectedContractionWeightMatrix (m : ℕ)
    (weights : Fin (m + 2) → ℕ → ℂ) (dirs : Fin (m + 2) → ℂ × ℂ) :
    Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ :=
  fun i j => Fin.cases (weights j (m + 2))
    (fun a => (m.choose a.1 : ℂ) * weights j (2 * m + 2) *
      (dirs j).1 ^ (m - a.1) * (dirs j).2 ^ a.1) i

private def horizontalDirectionEvaluationMatrix (m : ℕ)
    (dirs : Fin (m + 2) → ℂ × ℂ) :
    Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ :=
  fun j b => (dirs j).1 ^ (m + 1 - b.1) * (dirs j).2 ^ (b.1 + 1)

private lemma horizontalContractionMinorMatrix_eq_mul_forward (m : ℕ)
    (theta : ParamSpace ℂ m) :
    horizontalContractionMinorMatrix m
        (forwardCumulantMap m (2 * m + 2) theta) =
      selectedContractionWeightMatrix m theta.2.2
          (forwardLoading m theta.1 theta.2.1) *
        horizontalDirectionEvaluationMatrix m
          (forwardLoading m theta.1 theta.2.1) := by
  ext i b
  refine Fin.cases ?_ (fun a => ?_) i
  · simp only [horizontalContractionMinorMatrix, Fin.cases_zero, Matrix.mul_apply,
      selectedContractionWeightMatrix, horizontalDirectionEvaluationMatrix,
      forwardCumulantMap, show 2 ≤ m + 2 ∧ m + 2 ≤ 2 * m + 2 ∧
        b.1 + 1 ≤ m + 2 by omega, if_true]
    apply Finset.sum_congr rfl
    intro j _
    have hsub : m + 2 - (b.1 + 1) = m + 1 - b.1 := by omega
    rw [hsub]
    ring
  · simp only [horizontalContractionMinorMatrix, Fin.cases_succ, Matrix.mul_apply,
      selectedContractionWeightMatrix, horizontalDirectionEvaluationMatrix,
      forwardCumulantMap]
    rw [if_pos (by omega)]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    have hpow : 2 * m + 2 - (a.1 + b.1 + 1) =
        (m - a.1) + (m + 1 - b.1) := by omega
    rw [hpow, pow_add, pow_add]
    ring

private lemma horizontalContractionMinorMatrix_eq_mul_reverse (m : ℕ)
    (eta : ParamSpace ℂ m) :
    horizontalContractionMinorMatrix m
        (reverseCumulantMap m (2 * m + 2) eta) =
      selectedContractionWeightMatrix m eta.2.2
          (reverseLoading m eta.1 eta.2.1) *
        horizontalDirectionEvaluationMatrix m
          (reverseLoading m eta.1 eta.2.1) := by
  ext i b
  refine Fin.cases ?_ (fun a => ?_) i
  · simp only [horizontalContractionMinorMatrix, Fin.cases_zero, Matrix.mul_apply,
      selectedContractionWeightMatrix, horizontalDirectionEvaluationMatrix,
      reverseCumulantMap, show 2 ≤ m + 2 ∧ m + 2 ≤ 2 * m + 2 ∧
        b.1 + 1 ≤ m + 2 by omega, if_true]
    apply Finset.sum_congr rfl
    intro j _
    have hsub : m + 2 - (b.1 + 1) = m + 1 - b.1 := by omega
    rw [hsub]
    ring
  · simp only [horizontalContractionMinorMatrix, Fin.cases_succ, Matrix.mul_apply,
      selectedContractionWeightMatrix, horizontalDirectionEvaluationMatrix,
      reverseCumulantMap]
    rw [if_pos (by omega)]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    have hpow : 2 * m + 2 - (a.1 + b.1 + 1) =
        (m - a.1) + (m + 1 - b.1) := by omega
    rw [hpow, pow_add, pow_add]
    ring

/-- Proves the stated mathematical property of horizontal Contraction Minor Polynomial reverse vanishes. -/
lemma horizontalContractionMinorPolynomial_reverse_vanishes (m : ℕ)
    (eta : ParamSpace ℂ m) :
    MvPolynomial.eval
        (restrictCumBand (2 * m + 2)
          (reverseCumulantMap m (2 * m + 2) eta))
        (horizontalContractionMinorPolynomial m) = 0 := by
  rw [eval_horizontalContractionMinorPolynomial,
    horizontalContractionMinorMatrix_eq_mul_reverse, Matrix.det_mul]
  have hzero : (horizontalDirectionEvaluationMatrix m
      (reverseLoading m eta.1 eta.2.1)).det = 0 := by
    apply Matrix.det_eq_zero_of_row_eq_zero (0 : Fin (m + 2))
    intro b
    simp [horizontalDirectionEvaluationMatrix, reverseLoading]
  rw [hzero, mul_zero]

/-- Proves the stated mathematical property of horizontal Contraction Minor Polynomial forward Common Axis vanishes. -/
lemma horizontalContractionMinorPolynomial_forwardCommonAxis_vanishes
    {m : ℕ} (hm : 1 ≤ m) {theta : ParamSpace ℂ m}
    (haxis : theta.2.1 ⟨0, hm⟩ = 0) :
    MvPolynomial.eval
        (restrictCumBand (2 * m + 2)
          (forwardCumulantMap m (2 * m + 2) theta))
        (horizontalContractionMinorPolynomial m) = 0 := by
  rw [eval_horizontalContractionMinorPolynomial,
    horizontalContractionMinorMatrix_eq_mul_forward, Matrix.det_mul]
  have hzero : (horizontalDirectionEvaluationMatrix m
      (forwardLoading m theta.1 theta.2.1)).det = 0 := by
    apply Matrix.det_eq_zero_of_row_eq_zero ⟨1, by omega⟩
    intro b
    have hm0 : m ≠ 0 := by omega
    simp [horizontalDirectionEvaluationMatrix, forwardLoading, haxis, hm0]
  rw [hzero, mul_zero]

/-- The observable horizontal-axis contraction minor vanishes on the entire
reverse arrow-image variety, not only on its parameterized range. -/
lemma horizontalContractionMinorPolynomial_reverseVariety_vanishes (m : ℕ)
    {t : CumVec ℂ}
    (ht : t ∈ cumulantImageVariety (reverseCumulantMap m (2 * m + 2))) :
    MvPolynomial.eval (restrictCumBand (2 * m + 2) t)
      (horizontalContractionMinorPolynomial m) = 0 := by
  have htband : t ∈ bandSupportedCumulants (2 * m + 2) := by
    apply zariskiClosure_subset_band
      (A := Set.range (reverseCumulantMap m (2 * m + 2)))
    · rintro _ ⟨eta, rfl⟩
      exact reverseCumulantMap_mem_bandSupportedCumulants m (2 * m + 2) eta
    · exact ht
  rw [← eval_extendCumPolynomial (2 * m + 2)
    (restrictCumBand (2 * m + 2) t) (horizontalContractionMinorPolynomial m)]
  rw [extend_restrictCumBand htband]
  apply ht (extendCumPolynomial (2 * m + 2)
    (horizontalContractionMinorPolynomial m))
  rintro _ ⟨eta, rfl⟩
  rw [← extend_restrictCumBand
    (reverseCumulantMap_mem_bandSupportedCumulants m (2 * m + 2) eta)]
  rw [eval_extendCumPolynomial]
  exact horizontalContractionMinorPolynomial_reverse_vanishes m eta

/-- The same observable minor vanishes on the Zariski closure of the explicit
forward common-axis image family. -/
lemma horizontalContractionMinorPolynomial_forwardCommonAxisClosure_vanishes
    {m : ℕ} (hm : 1 ≤ m) {t : CumVec ℂ}
    (ht : t ∈ zariskiClosure
      ((forwardCumulantMap m (2 * m + 2)) ''
        {theta : ParamSpace ℂ m |
          theta ∈ genericParameterLocus m (2 * m + 2) ∧
          theta.2.1 ⟨0, hm⟩ = 0})) :
    MvPolynomial.eval (restrictCumBand (2 * m + 2) t)
      (horizontalContractionMinorPolynomial m) = 0 := by
  have hsourceBand :
      (forwardCumulantMap m (2 * m + 2)) ''
          {theta : ParamSpace ℂ m |
            theta ∈ genericParameterLocus m (2 * m + 2) ∧
            theta.2.1 ⟨0, hm⟩ = 0} ⊆
        bandSupportedCumulants (2 * m + 2) := by
    rintro _ ⟨theta, _, rfl⟩
    exact forwardCumulantMap_mem_bandSupportedCumulants m (2 * m + 2) theta
  have htband : t ∈ bandSupportedCumulants (2 * m + 2) :=
    zariskiClosure_subset_band hsourceBand ht
  rw [← eval_extendCumPolynomial (2 * m + 2)
    (restrictCumBand (2 * m + 2) t) (horizontalContractionMinorPolynomial m)]
  rw [extend_restrictCumBand htband]
  apply ht (extendCumPolynomial (2 * m + 2)
    (horizontalContractionMinorPolynomial m))
  rintro _ ⟨theta, htheta, rfl⟩
  rw [← extend_restrictCumBand
    (forwardCumulantMap_mem_bandSupportedCumulants m (2 * m + 2) theta)]
  rw [eval_extendCumPolynomial]
  exact horizontalContractionMinorPolynomial_forwardCommonAxis_vanishes hm htheta.2

private lemma horizontalDirectionEvaluationMatrix_witness_det_ne_zero
    (m : ℕ) :
    (horizontalDirectionEvaluationMatrix m
      (forwardLoading m (forwardContractionMinorWitnessParameter m).1
        (forwardContractionMinorWitnessParameter m).2.1)).det ≠ 0 := by
  let R := horizontalDirectionEvaluationMatrix m
    (forwardLoading m (forwardContractionMinorWitnessParameter m).1
      (forwardContractionMinorWitnessParameter m).2.1)
  have hmul : Function.Injective R.mulVec := by
    intro e e' he
    let v : Fin (m + 2) → ℂ := e - e'
    have hvzero : R.mulVec v = 0 := by
      funext i
      simp only [v, Matrix.mulVec, dotProduct, Pi.sub_apply, Pi.zero_apply,
        mul_sub]
      rw [Finset.sum_sub_distrib]
      exact sub_eq_zero.mpr (congrFun he i)
    have hlast : v (Fin.last (m + 1)) = 0 := by
      have h : (∑ i, R (Fin.last (m + 1)) i * v i) = 0 := by
        simpa only [Matrix.mulVec, dotProduct, Pi.zero_apply] using
          congrFun hvzero (Fin.last (m + 1))
      rw [Fin.sum_univ_castSucc] at h
      have hRcast : ∀ x : Fin (m + 1),
          R (Fin.last (m + 1)) x.castSucc = 0 := by
        intro x
        change
          (forwardLoading m (forwardContractionMinorWitnessParameter m).1
              (forwardContractionMinorWitnessParameter m).2.1
              (Fin.last (m + 1))).1 ^ (m + 1 - x.1) *
            (forwardLoading m (forwardContractionMinorWitnessParameter m).1
              (forwardContractionMinorWitnessParameter m).2.1
              (Fin.last (m + 1))).2 ^ (x.1 + 1) = 0
        rw [forwardContractionMinorWitness_loading_last]
        simp [show m + 1 - x.1 ≠ 0 by omega]
      have hRlast : R (Fin.last (m + 1)) (Fin.last (m + 1)) = 1 := by
        dsimp [R, horizontalDirectionEvaluationMatrix]
        rw [forwardContractionMinorWitness_loading_last]
        simp
      simp_rw [hRcast] at h
      rw [hRlast] at h
      simpa using h
    have hfinite : (fun b : Fin (m + 1) => v b.castSucc) = 0 := by
      apply Matrix.eq_zero_of_mulVec_eq_zero
        (Matrix.det_vandermonde_ne_zero_iff.mpr
          (forwardContractionMinorWitness_slope_injective m))
      funext j
      have h := congrFun hvzero j.castSucc
      simp only [R, Matrix.mulVec, dotProduct] at h
      rw [Fin.sum_univ_castSucc] at h
      simp only [horizontalDirectionEvaluationMatrix,
        forwardContractionMinorWitness_loading_castSucc,
        forwardContractionMinorWitness_loading_last, Prod.fst, Prod.snd,
        one_pow, hlast, mul_zero, add_zero] at h
      have hz : (((j.1 + 1 : ℕ) : ℂ)) ≠ 0 := by
        exact_mod_cast (Nat.succ_ne_zero j.1)
      apply (mul_eq_zero.mp ?_).resolve_left hz
      calc
        ((j.1 + 1 : ℕ) : ℂ) *
            ((Matrix.vandermonde fun i : Fin (m + 1) =>
              ((i.1 + 1 : ℕ) : ℂ)).mulVec
                (fun b : Fin (m + 1) => v b.castSucc)) j =
            ∑ b : Fin (m + 1),
              ((j.1 + 1 : ℕ) : ℂ) ^ (b.1 + 1) * v b.castSucc := by
          simp only [Matrix.mulVec, dotProduct, Matrix.vandermonde_apply,
            Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro b _
          rw [pow_succ]
          ring
        _ = 0 := by simpa using h
    apply sub_eq_zero.mp
    funext b
    refine Fin.lastCases ?_ (fun i => ?_) b
    · exact hlast
    · exact congrFun hfinite i
  have hu : IsUnit R := Matrix.mulVec_injective_iff_isUnit.mp hmul
  have hdet : IsUnit R.det :=
    hu.map (Matrix.detMonoidHom (n := Fin (m + 2)) (R := ℂ))
  exact hdet.ne_zero

/-- Nonvanishing of the observable minor at the explicit forward
block-Vandermonde witness. -/
lemma horizontalContractionMinorPolynomial_forwardWitness_ne_zero
    (m : ℕ) (hm : 1 ≤ m) :
    MvPolynomial.eval
      (restrictCumBand (2 * m + 2)
        (forwardCumulantMap m (2 * m + 2)
          (forwardContractionMinorWitnessParameter m)))
      (horizontalContractionMinorPolynomial m) ≠ 0 := by
  rw [eval_horizontalContractionMinorPolynomial,
    horizontalContractionMinorMatrix_eq_mul_forward, Matrix.det_mul]
  apply mul_ne_zero
  · have heq : selectedContractionWeightMatrix m
        (forwardContractionMinorWitnessParameter m).2.2
        (forwardLoading m (forwardContractionMinorWitnessParameter m).1
          (forwardContractionMinorWitnessParameter m).2.1) =
        forwardSelectedContractionMatrix m
          (forwardContractionMinorWitnessParameter m) := by
        ext i j
        refine Fin.cases ?_ (fun a => ?_) i
        · rfl
        · dsimp [selectedContractionWeightMatrix,
            forwardSelectedContractionMatrix]
          ring
    rw [heq]
    exact forwardContractionMinorWitness_det_ne_zero m hm
  · exact horizontalDirectionEvaluationMatrix_witness_det_ne_zero m

/-- The observable contraction minor is a nonzero polynomial. -/
lemma horizontalContractionMinorPolynomial_ne_zero (m : ℕ) (hm : 1 ≤ m) :
    horizontalContractionMinorPolynomial m ≠ 0 := by
  intro hzero
  exact (horizontalContractionMinorPolynomial_forwardWitness_ne_zero m hm)
    (by rw [hzero, map_zero])

end

end CausalSmith.ExactID.EID_LingamDirectionMinOrderV1
