/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Dimension of a Vandermonde synthesis kernel
-/

import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Analysis.Complex.Basic

/-!
# Vandermonde synthesis maps

This file computes the kernel dimension of a finite moment-synthesis map with
distinct complex nodes and one endpoint coordinate.
-/

namespace Causalean.Mathlib.LinearAlgebra

open scoped BigOperators

noncomputable section

/-- Moment synthesis from `n` complex nodes and one terminal coordinate. The
terminal coordinate contributes only to the highest requested moment. -/
def endpointOrderSynthesis {n : ℕ} (s : Fin n → ℂ) (r : ℕ) :
    (Fin (n + 1) → ℂ) →ₗ[ℂ] (Fin (r + 1) → ℂ) where
  toFun z a :=
    ∑ j : Fin n, z j.castSucc * s j ^ a.val +
      if a.val = r then z (Fin.last n) else 0
  map_add' x y := by
    funext a
    simp only [Pi.add_apply, Fin.isValue, add_mul, Finset.sum_add_distrib]
    split <;> ring
  map_smul' c x := by
    funext a
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split <;> simp [← Finset.mul_sum, mul_assoc] <;> ring

private lemma endpointOrderSynthesis_single {n r : ℕ} (s : Fin n → ℂ)
    (j : Fin n) :
    endpointOrderSynthesis s r (Pi.single j.castSucc 1) =
      fun a => s j ^ a.val := by
  funext a
  simp only [endpointOrderSynthesis, LinearMap.coe_mk, AddHom.coe_mk,
    Fin.castSucc_ne_last, Pi.single_eq_of_ne, ↓reduceIte]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    have hcast : b.castSucc ≠ j.castSucc := fun h => hb (Fin.castSucc_injective n h)
    simp [Pi.single_eq_of_ne hcast]
  · simp

private lemma endpointOrderSynthesis_surjective {n r : ℕ}
    (s : Fin n → ℂ) (hs : Function.Injective s) (hr : r < n) :
    Function.Surjective (endpointOrderSynthesis s r) := by
  let e : Fin (r + 1) → Fin n := fun j => ⟨j, by omega⟩
  have he : Function.Injective e := by
    intro x y h
    apply Fin.ext
    simpa [e] using congrArg Fin.val h
  let A : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ :=
    (Matrix.vandermonde (s ∘ e)).transpose
  have hdet : A.det ≠ 0 := by
    rw [Matrix.det_transpose]
    exact Matrix.det_vandermonde_ne_zero_iff.mpr (hs.comp he)
  have hAinj : Function.Injective A.mulVecLin := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply Matrix.eq_zero_of_mulVec_eq_zero hdet
    change A.mulVec x = A.mulVec y at hxy
    rw [Matrix.mulVec_sub, hxy, sub_self]
  let E : (Fin (r + 1) → ℂ) ≃ₗ[ℂ] (Fin (r + 1) → ℂ) :=
    LinearEquiv.ofInjectiveEndo A.mulVecLin hAinj
  intro y
  let w : Fin (r + 1) → ℂ := E.symm y
  let z : Fin (n + 1) → ℂ :=
    ∑ j : Fin (r + 1), w j •
      (Pi.single (e j).castSucc (1 : ℂ) : Fin (n + 1) → ℂ)
  refine ⟨z, ?_⟩
  rw [show z = ∑ j : Fin (r + 1), w j •
      (Pi.single (e j).castSucc (1 : ℂ) : Fin (n + 1) → ℂ) by rfl,
    map_sum]
  simp_rw [map_smul, endpointOrderSynthesis_single]
  have hEy : A.mulVec w = y := E.apply_symm_apply y
  funext a
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  calc
    ∑ j : Fin (r + 1), w j * s (e j) ^ a.val = A.mulVec w a := by
      simp [A, Matrix.mulVec, dotProduct, Matrix.vecMul,
        Matrix.vandermonde_apply, e, mul_comm]
    _ = y a := congrFun hEy a

private lemma endpointOrderSynthesis_injective {n r : ℕ}
    (s : Fin n → ℂ) (hs : Function.Injective s) (hr : n ≤ r) :
    Function.Injective (endpointOrderSynthesis s r) := by
  intro z z' hzz'
  apply sub_eq_zero.mp
  let v := z - z'
  have hv : endpointOrderSynthesis s r v = 0 := by
    rw [map_sub, hzz', sub_self]
  have hfinite : (fun j : Fin n => v j.castSucc) = 0 := by
    apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hs
    intro a
    have ha : a.val < r := lt_of_lt_of_le a.isLt hr
    have hcoord := congrFun hv ⟨a, by omega⟩
    simpa [endpointOrderSynthesis, ha.ne] using hcoord
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  ·
    have hcoord := congrFun hv (Fin.last r)
    have hzero : ∀ i : Fin n, v i.castSucc = 0 := fun i => congrFun hfinite i
    simpa [endpointOrderSynthesis, hzero] using hcoord
  ·
    exact congrFun hfinite i

/-- The order-`r` synthesis kernel has dimension `n-r` below the square
threshold and is zero at and above it. -/
theorem endpointOrderSynthesis_ker_finrank {n r : ℕ}
    (s : Fin n → ℂ) (hs : Function.Injective s) :
    Module.finrank ℂ (LinearMap.ker (endpointOrderSynthesis s r)) = n - r := by
  by_cases hr : r < n
  · have hsurj := endpointOrderSynthesis_surjective s hs hr
    have hrange : LinearMap.range (endpointOrderSynthesis s r) = ⊤ :=
      LinearMap.range_eq_top.mpr hsurj
    have hnull := LinearMap.finrank_range_add_finrank_ker
      (endpointOrderSynthesis s r)
    rw [hrange, finrank_top, Module.finrank_pi ℂ, Module.finrank_pi ℂ,
      Fintype.card_fin, Fintype.card_fin] at hnull
    omega
  · have hinj := endpointOrderSynthesis_injective (r := r) s hs (by omega)
    rw [LinearMap.ker_eq_bot.mpr hinj, finrank_bot]
    omega

end

end Causalean.Mathlib.LinearAlgebra
