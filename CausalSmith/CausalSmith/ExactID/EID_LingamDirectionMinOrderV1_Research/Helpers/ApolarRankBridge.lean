/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# A polynomial rank witness for the genuine weighted contraction
-/

import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.ApolarKernelIdentity
import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.ZariskiLocus
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde

namespace CausalSmith.ExactID.EID_LingamDirectionMinOrderV1

open scoped BigOperators

noncomputable section

private def slopePolynomial (m : ℕ) (j : Fin (m + 2)) :
    MvPolynomial (ParamCoord m) ℂ :=
  if h0 : j.1 = 0 then MvPolynomial.X (Sum.inl ())
  else if ha : j.1 = m + 1 then 1
  else MvPolynomial.X (Sum.inr (Sum.inl ⟨j.1 - 1, by omega⟩))

private def firstPolynomial (m : ℕ) (j : Fin (m + 2)) :
    MvPolynomial (ParamCoord m) ℂ :=
  if j.1 = m + 1 then 0 else 1

private def weightPolynomial (m : ℕ) (j : Fin (m + 2)) (r : ℕ) :
    MvPolynomial (ParamCoord m) ℂ :=
  MvPolynomial.X (Sum.inr (Sum.inr (j, r)))

/-- The selected square coefficient matrix: its first row is the degree-zero
block and its remaining rows are the coefficients of the degree-`m` block. -/
private def contractionMinorPolynomial (m : ℕ) :
    Matrix (Fin (m + 2)) (Fin (m + 2)) (MvPolynomial (ParamCoord m) ℂ) :=
  fun i j => Fin.cases
    (weightPolynomial m j (m + 2))
    (fun r => weightPolynomial m j (2 * m + 2) *
      MvPolynomial.C (m.choose r.1 : ℂ) *
      firstPolynomial m j ^ (m - r.1) * slopePolynomial m j ^ r.1) i

private def contractionMinor (m : ℕ) (theta : ParamSpace ℂ m) :
    Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ :=
  (contractionMinorPolynomial m).map (MvPolynomial.eval (paramEval theta))

private lemma eval_firstPolynomial (m : ℕ) (theta : ParamSpace ℂ m)
    (j : Fin (m + 2)) :
    MvPolynomial.eval (paramEval theta) (firstPolynomial m j) =
      (forwardLoading m theta.1 theta.2.1 j).1 := by
  simp [firstPolynomial, forwardLoading]
  split_ifs <;> simp_all

private lemma eval_slopePolynomial (m : ℕ) (theta : ParamSpace ℂ m)
    (j : Fin (m + 2)) :
    MvPolynomial.eval (paramEval theta) (slopePolynomial m j) =
      (forwardLoading m theta.1 theta.2.1 j).2 := by
  simp [slopePolynomial, forwardLoading]
  split_ifs <;> simp [paramEval]

private lemma contractionMinor_apply (m : ℕ) (theta : ParamSpace ℂ m)
    (i j : Fin (m + 2)) :
    contractionMinor m theta i j = Fin.cases
      (theta.2.2 j (m + 2))
      (fun r => theta.2.2 j (2 * m + 2) * (m.choose r.1 : ℂ) *
        (forwardLoading m theta.1 theta.2.1 j).1 ^ (m - r.1) *
        (forwardLoading m theta.1 theta.2.1 j).2 ^ r.1) i := by
  refine Fin.cases ?_ (fun r => ?_) i
  · simp [contractionMinor, contractionMinorPolynomial, weightPolynomial, paramEval]
  · simp [contractionMinor, contractionMinorPolynomial, weightPolynomial, paramEval,
      eval_firstPolynomial, eval_slopePolynomial]

/-- Defines the mathematical object called the binary Dehom. -/
noncomputable def binaryDehom :
    MvPolynomial (Fin 2) ℂ →+* Polynomial ℂ :=
  MvPolynomial.eval₂Hom Polynomial.C (fun i => if i = 0 then 1 else Polynomial.X)

@[simp] private lemma binaryDehom_C (c : ℂ) :
    binaryDehom (MvPolynomial.C c) = Polynomial.C c := by
  simp [binaryDehom]

/-- Proves the stated mathematical property of coeff binary Dehom lin Form pow. -/
lemma coeff_binaryDehom_linForm_pow (u : ℂ × ℂ) (m r : ℕ) :
    (binaryDehom (linForm u ^ m)).coeff r =
      (m.choose r : ℂ) * u.1 ^ (m - r) * u.2 ^ r := by
  rw [map_pow]
  have hlin : binaryDehom (linForm u) =
      Polynomial.C u.1 + Polynomial.C u.2 * Polynomial.X := by
    simp [binaryDehom, linForm]
  rw [hlin]
  rw [add_comm]
  rw [Commute.add_pow (Commute.all _ _)]
  simp only [Polynomial.finset_sum_coeff]
  have hterm (x : ℕ) :
      (Polynomial.C u.2 * Polynomial.X) ^ x * Polynomial.C u.1 ^ (m - x) =
        Polynomial.C (u.1 ^ (m - x) * u.2 ^ x) * Polynomial.X ^ x := by
    rw [mul_pow, ← map_pow, ← map_pow, map_mul]
    ring
  simp only [hterm, ← Polynomial.C_eq_natCast, Polynomial.coeff_mul_C,
    Polynomial.coeff_C_mul_X_pow]
  by_cases hr : r < m + 1
  · rw [Finset.sum_eq_single r]
    · simp
      ring
    · intro b hb hbr
      simp [Ne.symm hbr]
    · intro hnot
      exact False.elim (hnot (Finset.mem_range.mpr hr))
  · have hmr : m < r := by omega
    have hchoose : m.choose r = 0 := Nat.choose_eq_zero_of_lt hmr
    rw [show (m.choose r : ℂ) = 0 by simp [hchoose]]
    simp only [zero_mul]
    apply Finset.sum_eq_zero
    intro b hb
    have hbr : r ≠ b := by
      have := Finset.mem_range.mp hb
      omega
    simp [hbr]

/-- Proves the stated mathematical property of coeff binary Dehom lin Form pow'. -/
lemma coeff_binaryDehom_linForm_pow' (u : ℂ × ℂ) (m r : ℕ) :
    (binaryDehom (linForm u) ^ m).coeff r =
      (m.choose r : ℂ) * u.1 ^ (m - r) * u.2 ^ r := by
  rw [← map_pow]
  exact coeff_binaryDehom_linForm_pow u m r

private lemma minor_mulVec_eq_zero_of_contraction_eq_zero (m : ℕ)
    (theta : ParamSpace ℂ m) (e : Fin (m + 2) → ℂ)
    (he : forwardWeightedContraction m theta e = 0) :
    (contractionMinor m theta).mulVec e = 0 := by
  funext i
  refine Fin.cases ?_ (fun r => ?_) i
  · have hzero := congrFun he (0 : Fin (m + 1))
    have h := congrArg (fun p => (binaryDehom p).coeff 0) hzero
    simp [forwardWeightedContraction, contractionMinor_apply, Matrix.mulVec,
      dotProduct, binaryDehom] at h ⊢
    simpa [mul_assoc] using h
  · have htop := congrFun he ⟨m, by omega⟩
    have h := congrArg (fun p => (binaryDehom p).coeff r.1) htop
    simp only [forwardWeightedContraction, map_sum, map_mul, map_pow,
      Polynomial.finset_sum_coeff, map_zero, Polynomial.coeff_zero, Pi.zero_apply,
      binaryDehom_C] at h
    have hindex : m + 2 + m = 2 * m + 2 := by omega
    rw [hindex] at h
    simp only [contractionMinor_apply, Fin.cases_succ, Matrix.mulVec, dotProduct]
    calc
      _ = ∑ x, e x *
          (theta.2.2 x (2 * m + 2) *
            (binaryDehom (linForm (forwardLoading m theta.1 theta.2.1 x)) ^ m).coeff r.1) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [coeff_binaryDehom_linForm_pow']
        ring
      _ = ∑ x, (Polynomial.C (theta.2.2 x (2 * m + 2)) *
          Polynomial.C (e x) *
          binaryDehom (linForm (forwardLoading m theta.1 theta.2.1 x)) ^ m).coeff r.1 := by
        apply Finset.sum_congr rfl
        intro x _
        rw [← map_mul, Polynomial.coeff_C_mul]
        ring
      _ = 0 := h

private lemma contraction_injective_of_minor_det_ne_zero (m : ℕ)
    (theta : ParamSpace ℂ m) (hdet : (contractionMinor m theta).det ≠ 0) :
    Function.Injective (forwardWeightedContraction m theta) := by
  intro e e' he
  apply sub_eq_zero.mp
  apply Matrix.eq_zero_of_mulVec_eq_zero hdet
  apply minor_mulVec_eq_zero_of_contraction_eq_zero
  funext k
  calc
    forwardWeightedContraction m theta (e - e') k =
        forwardWeightedContraction m theta e k -
          forwardWeightedContraction m theta e' k := by
      simp only [forwardWeightedContraction, Pi.sub_apply, map_sub]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = 0 := sub_eq_zero.mpr (congrFun he k)

private def witnessParameter (m : ℕ) : ParamSpace ℂ m :=
  ((1 : ℂ), (fun i => (i.1 + 2 : ℕ)), fun j r =>
    if r = m + 2 then if j.1 = m + 1 then 1 else 0
    else if r = 2 * m + 2 then if j.1 = m + 1 then 0 else 1
    else 0)

private lemma witness_loading_castSucc (m : ℕ) (j : Fin (m + 1)) :
    forwardLoading m (witnessParameter m).1 (witnessParameter m).2.1 j.castSucc =
      ((1 : ℂ), ((j.1 + 1 : ℕ) : ℂ)) := by
  rcases j with ⟨j, hj⟩
  simp only [forwardLoading, witnessParameter, Fin.castSucc_mk, Fin.val_mk]
  split_ifs with h0 ha
  · ext <;> simp_all
  · exact False.elim (by omega)
  · apply Prod.ext
    · simp
    · simp only [Prod.snd]
      norm_cast
      omega

private lemma witnessSlope_injective (m : ℕ) :
    Function.Injective (fun j : Fin (m + 1) => ((j.1 + 1 : ℕ) : ℂ)) := by
  intro i j h
  apply Fin.ext
  have hnat : i.1 + 1 = j.1 + 1 := by
    apply Nat.cast_injective (R := ℂ)
    simpa only [Nat.cast_add, Nat.cast_one] using h
  omega

private lemma witness_minor_zero_castSucc (m : ℕ) (j : Fin (m + 1)) :
    contractionMinor m (witnessParameter m) 0 j.castSucc = 0 := by
  simp [contractionMinor_apply, witnessParameter]
  omega

private lemma witness_minor_zero_last (m : ℕ) :
    contractionMinor m (witnessParameter m) 0 (Fin.last (m + 1)) = 1 := by
  simp [contractionMinor_apply, witnessParameter]

private lemma witness_minor_succ_castSucc (m : ℕ) (hm : 1 ≤ m)
    (r j : Fin (m + 1)) :
    contractionMinor m (witnessParameter m) r.succ j.castSucc =
      (m.choose r.1 : ℂ) * (((j.1 + 1 : ℕ) : ℂ) ^ r.1) := by
  rw [contractionMinor_apply]
  simp only [Fin.cases_succ, witnessParameter]
  have hload := witness_loading_castSucc m j
  change forwardLoading m 1 (fun i => ((i.1 + 2 : ℕ) : ℂ)) j.castSucc = _ at hload
  rw [hload]
  simp [show 2 * m ≠ m by omega, show j.1 ≠ m + 1 by omega]

private lemma witness_minor_succ_last (m : ℕ) (hm : 1 ≤ m)
    (r : Fin (m + 1)) :
    contractionMinor m (witnessParameter m) r.succ (Fin.last (m + 1)) = 0 := by
  simp [contractionMinor_apply, witnessParameter]
  omega

private lemma witness_minor_det_ne_zero (m : ℕ) (hm : 1 ≤ m) :
    (contractionMinor m (witnessParameter m)).det ≠ 0 := by
  have hinj : Function.Injective
      (contractionMinor m (witnessParameter m)).mulVec := by
    intro e e' he
    have haxis : e (Fin.last (m + 1)) = e' (Fin.last (m + 1)) := by
      have h := congrFun he (0 : Fin (m + 2))
      change (∑ j : Fin (m + 2),
          contractionMinor m (witnessParameter m) 0 j * e j) =
        ∑ j : Fin (m + 2),
          contractionMinor m (witnessParameter m) 0 j * e' j at h
      conv_lhs at h => rw [Fin.sum_univ_castSucc]
      conv_rhs at h => rw [Fin.sum_univ_castSucc]
      simpa only [witness_minor_zero_castSucc, witness_minor_zero_last, zero_mul,
        Finset.sum_const_zero, zero_add, one_mul] using h
    have hfinite : (fun j : Fin (m + 1) => e j.castSucc) =
        fun j => e' j.castSucc := by
      have hsum : ∀ r : Fin (m + 1),
          ∑ j : Fin (m + 1), (e j.castSucc - e' j.castSucc) *
              (((j.1 + 1 : ℕ) : ℂ) ^ r.1) = 0 := by
        intro r
        have h := congrFun he r.succ
        have hchoose : (m.choose r.1 : ℂ) ≠ 0 := by
          exact_mod_cast (Nat.choose_pos (Nat.lt_succ_iff.mp r.2)).ne'
        change (∑ j : Fin (m + 2),
            contractionMinor m (witnessParameter m) r.succ j * e j) =
          ∑ j : Fin (m + 2),
            contractionMinor m (witnessParameter m) r.succ j * e' j at h
        conv_lhs at h => rw [Fin.sum_univ_castSucc]
        conv_rhs at h => rw [Fin.sum_univ_castSucc]
        simp only [witness_minor_succ_castSucc m hm,
          witness_minor_succ_last m hm, zero_mul, add_zero] at h
        apply (mul_eq_zero.mp ?_).resolve_left hchoose
        calc
          (m.choose r.1 : ℂ) *
              (∑ j : Fin (m + 1), (e j.castSucc - e' j.castSucc) *
                (((j.1 + 1 : ℕ) : ℂ) ^ r.1)) =
              (∑ j : Fin (m + 1),
                (m.choose r.1 : ℂ) * (((j.1 + 1 : ℕ) : ℂ) ^ r.1) * e j.castSucc) -
              ∑ j : Fin (m + 1),
                (m.choose r.1 : ℂ) * (((j.1 + 1 : ℕ) : ℂ) ^ r.1) * e' j.castSucc := by
            rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro j _
            ring
          _ = 0 := sub_eq_zero.mpr h
      have hv : (fun j : Fin (m + 1) => e j.castSucc - e' j.castSucc) = 0 := by
        apply Matrix.eq_zero_of_vecMul_eq_zero
          (Matrix.det_vandermonde_ne_zero_iff.mpr (witnessSlope_injective m))
        funext r
        exact hsum r
      funext j
      exact sub_eq_zero.mp (congrFun hv j)
    funext j
    refine Fin.lastCases haxis (fun i => ?_) j
    exact congrFun hfinite i
  have hu : IsUnit (contractionMinor m (witnessParameter m)) :=
    Matrix.mulVec_injective_iff_isUnit.mp hinj
  have hdet : IsUnit (contractionMinor m (witnessParameter m)).det := by
    have h := hu.map (Matrix.detMonoidHom (n := Fin (m + 2)) (R := ℂ))
    simpa only [Matrix.coe_detMonoidHom] using h
  exact isUnit_iff_ne_zero.mp hdet

/-- The selected weighted-contraction coefficient matrix, exposed independently
of parameter polynomials so observable contraction minors can factor through
it. -/
def forwardSelectedContractionMatrix (m : ℕ) (theta : ParamSpace ℂ m) :
    Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ :=
  fun i j => Fin.cases (theta.2.2 j (m + 2))
    (fun r => theta.2.2 j (2 * m + 2) * (m.choose r.1 : ℂ) *
      (forwardLoading m theta.1 theta.2.1 j).1 ^ (m - r.1) *
      (forwardLoading m theta.1 theta.2.1 j).2 ^ r.1) i

/-- Explicit retained-band parameter at which the selected contraction matrix
is nonsingular. -/
def forwardContractionMinorWitnessParameter (m : ℕ) : ParamSpace ℂ m :=
  witnessParameter m

lemma forwardContractionMinorWitness_det_ne_zero (m : ℕ) (hm : 1 ≤ m) :
    (forwardSelectedContractionMatrix m
      (forwardContractionMinorWitnessParameter m)).det ≠ 0 := by
  have heq : forwardSelectedContractionMatrix m
      (forwardContractionMinorWitnessParameter m) =
      contractionMinor m (witnessParameter m) := by
    ext i j
    rw [contractionMinor_apply]
    rfl
  rw [heq]
  exact witness_minor_det_ne_zero m hm

/-- Proves the stated mathematical property of forward Contraction Minor Witness loading cast Succ. -/
lemma forwardContractionMinorWitness_loading_castSucc (m : ℕ)
    (j : Fin (m + 1)) :
    forwardLoading m (forwardContractionMinorWitnessParameter m).1
        (forwardContractionMinorWitnessParameter m).2.1 j.castSucc =
      ((1 : ℂ), ((j.1 + 1 : ℕ) : ℂ)) := by
  exact witness_loading_castSucc m j

/-- Proves that the map or coordinate assignment called the forward Contraction Minor Witness slope is injective. -/
lemma forwardContractionMinorWitness_slope_injective (m : ℕ) :
    Function.Injective (fun j : Fin (m + 1) => ((j.1 + 1 : ℕ) : ℂ)) :=
  witnessSlope_injective m

/-- Proves the stated mathematical property of forward Contraction Minor Witness loading last. -/
lemma forwardContractionMinorWitness_loading_last (m : ℕ) :
    forwardLoading m (forwardContractionMinorWitnessParameter m).1
        (forwardContractionMinorWitnessParameter m).2.1 (Fin.last (m + 1)) =
      (0, 1) := by
  simp [forwardContractionMinorWitnessParameter, witnessParameter, forwardLoading]

/-- Injectivity of the genuine contraction holds on the principal open set
cut out by the determinant of an explicit coefficient minor. The polynomial is nonzero at an
explicit witness whose weights vanish outside the pinned degree band. -/
theorem forward_contraction_injective_of_generic_and_minor (m : ℕ) (hm : 1 ≤ m) :
    ∃ P : MvPolynomial (ParamCoord m) ℂ, P ≠ 0 ∧
      (∃ θ₀ : ParamSpace ℂ m,
        (∀ (j : Fin (m + 2)) (r : ℕ), (r < 2 ∨ 2 * m + 2 < r) → θ₀.2.2 j r = 0) ∧
        MvPolynomial.eval (paramEval θ₀) P ≠ 0) ∧
      ∀ theta : ParamSpace ℂ m, MvPolynomial.eval (paramEval theta) P ≠ 0 →
        Function.Injective (forwardWeightedContraction m theta) := by
  refine ⟨(contractionMinorPolynomial m).det, ?_, ?_, ?_⟩
  · intro hzero
    apply witness_minor_det_ne_zero m hm
    change Matrix.det ((MvPolynomial.eval (paramEval (witnessParameter m))).mapMatrix
        (contractionMinorPolynomial m)) = 0
    rw [← RingHom.map_det, hzero, map_zero]
  · refine ⟨witnessParameter m, ?_, ?_⟩
    · intro j r hr
      simp only [witnessParameter]
      rcases hr with hr | hr
      · rw [if_neg (by omega), if_neg (by omega)]
      · rw [if_neg (by omega), if_neg (by omega)]
    · intro hzero
      apply witness_minor_det_ne_zero m hm
      change Matrix.det ((MvPolynomial.eval (paramEval (witnessParameter m))).mapMatrix
          (contractionMinorPolynomial m)) = 0
      rw [← RingHom.map_det]
      exact hzero
  · intro theta htheta
    apply contraction_injective_of_minor_det_ne_zero m theta
    change Matrix.det ((MvPolynomial.eval (paramEval theta)).mapMatrix
        (contractionMinorPolynomial m)) ≠ 0
    rw [← RingHom.map_det]
    exact htheta

end

end CausalSmith.ExactID.EID_LingamDirectionMinOrderV1
