/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Frisch–Waugh–Lovell on a finite-dim inner product space

A self-contained Mathlib-shim file: the algebraic content of the
Frisch–Waugh–Lovell theorem on a real inner-product space `V` with a
nuisance subspace `H` admitting an orthogonal projection.

This file is **causal-agnostic and panel-agnostic**: it depends only on
Mathlib (`Submodule.orthogonalProjection`, `Matrix.mulVec`,
`Matrix.nonsing_inv`). Chunk 5 of
`CausalSmith/doc/general_projection_carryover_note.tex` instantiates these
results with the panel inner-product space.

## Main definitions

* `Causalean.Mathlib.FWL.residualize H v` — `v - P_H v`, where `P_H` is the
  Mathlib orthogonal projection onto `H` (as a self-map of `V`).
* `Causalean.Mathlib.FWL.gramResid H X` — the `K × K` Gram matrix of the
  residualized regressors `X̃ k = residualize H (X k)`.
* `Causalean.Mathlib.FWL.fwlCoef H X Y` — the FWL coefficient
  `(gramResid H X)⁻¹ *ᵥ (fun j => ⟨X̃ j, Y⟩)`.

## Main results

* `residualize_inner_swap_right` — symmetric residualization in the
  inner product: `⟨residualize H v, w⟩ = ⟨residualize H v, residualize H w⟩`.
* `gramResid_mulVec_fwlCoef` — the residualized normal equations:
  `gramResid H X *ᵥ fwlCoef H X Y = fun j => ⟨residualize H (X j), Y⟩`,
  under invertibility of `gramResid H X`.
* `fwlCoef_residualized_minimizes` — `fwlCoef` minimizes the residualized
  least-squares objective.
* `fwlCoef_original_minimizes` and
  `original_minimizer_eq_fwlCoef_projection` — the standard FWL optimizer
  theorem and uniqueness characterization for the original least-squares
  problem over coefficients and nuisance terms in `H`.

Candidate for upstreaming to Mathlib.
-/

import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Matrix.Mul

/-! # Frisch-Waugh-Lovell Algebra

This file formalizes the finite-dimensional Frisch--Waugh--Lovell residualization
theorem on a real inner-product space with a nuisance subspace admitting an
orthogonal projection. It is a causal-agnostic linear-algebra layer: downstream
estimand-characterization modules instantiate this result, but the statements
here only mention inner products, finite regressor tuples, Gram matrices, and
least-squares objectives.

Main definitions:
* `residualize H v` is the orthogonal residual `v - P_H v`.
* `fittedValue X β` is the finite linear combination of regressors `X`.
* `gramResid H X` is the Gram matrix of the residualized regressors.
* `residInnerVec H X Y` is the right-hand side of the residualized normal
  equations.
* `fwlCoef H X Y` is the coefficient vector obtained by multiplying that
  right-hand side by the nonsingular inverse of `gramResid H X`.
* `residualizedObjective` and `originalObjective` are the least-squares
  objectives after residualization and before residualizing out the nuisance
  term.

Main results:
* `residualize_inner_swap_right` shows that the outcome can be residualized in
  inner products against a residualized regressor.
* `gramResid_mulVec_fwlCoef` gives the residualized normal equations.
* `fwlCoef_residualized_minimizes` proves that `fwlCoef` minimizes the
  residualized objective.
* `fwlCoef_original_minimizes` lifts that optimizer to the original objective
  with an explicit nuisance term in `H`.
* `fwlCoef_eq_of_original_minimizer` and
  `original_minimizer_eq_fwlCoef_projection` give the coefficient and full
  optimizer uniqueness characterizations. -/

namespace Causalean.Mathlib.FWL

open scoped InnerProductSpace
open scoped BigOperators
open Matrix

variable {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  (H : Submodule ℝ V) [H.HasOrthogonalProjection]

/-- Orthogonal residual operator `M_H v := v - P_H v` as a function
`V → V`. We use `Submodule.orthogonalProjectionFn` (which lands in `V`,
not in `↥H`) so that `residualize H v : V`. -/
noncomputable def residualize (v : V) : V := v - H.orthogonalProjectionFn v

/-- Residualization is the original vector minus its orthogonal projection onto
the nuisance subspace. -/
@[simp] lemma residualize_def (v : V) :
    residualize H v = v - H.orthogonalProjectionFn v := rfl

/-- The residual maker as a continuous linear map. This bundled form is
used only to transfer linearity facts back to `residualize`. -/
noncomputable def residualizeL : V →L[ℝ] V :=
  ContinuousLinearMap.id ℝ V - H.starProjection

/-- Applying the residual-maker linear map gives the residualized vector. -/
@[simp] lemma residualizeL_apply (v : V) :
    residualizeL H v = residualize H v := by
  simp [residualizeL, residualize]

/-- Residual is orthogonal to every element of `H`. This is the
defining property of the orthogonal residual. -/
lemma inner_residualize_of_mem
    (v : V) {w : V} (hw : w ∈ H) :
    inner ℝ (residualize H v) w = 0 := by
  simpa [residualize] using
    Submodule.orthogonalProjectionFn_inner_eq_zero (K := H) v w hw

/-- **Symmetric residualization in the right slot.**
Since `M_H` is self-adjoint and idempotent, `⟨X̃, Y⟩ = ⟨X̃, Ỹ⟩`. -/
lemma residualize_inner_swap_right (v w : V) :
    inner ℝ (residualize H v) w
      = inner ℝ (residualize H v) (residualize H w) := by
  -- `w = residualize H w + P_H w` and `P_H w ∈ H`, which is orthogonal
  -- to `residualize H v`.
  have hPw : H.orthogonalProjectionFn w ∈ H :=
    Submodule.orthogonalProjectionFn_mem (K := H) w
  have horth :
      inner ℝ (residualize H v) (H.orthogonalProjectionFn w) = 0 :=
    inner_residualize_of_mem H v hPw
  have hsplit :
      w = residualize H w + H.orthogonalProjectionFn w := by
    simp [residualize, sub_add_cancel]
  calc inner ℝ (residualize H v) w
      = inner ℝ (residualize H v)
          (residualize H w + H.orthogonalProjectionFn w) := by rw [← hsplit]
    _ = inner ℝ (residualize H v) (residualize H w)
          + inner ℝ (residualize H v) (H.orthogonalProjectionFn w) := by
              rw [inner_add_right]
    _ = inner ℝ (residualize H v) (residualize H w) := by
              rw [horth, add_zero]

variable {K : ℕ} (X : Fin K → V)

/-- Fitted value for a finite tuple of regressors. -/
noncomputable def fittedValue (β : Fin K → ℝ) : V :=
  ∑ j, β j • X j

/-- Fitted values are linear in the coefficient vector. -/
lemma fittedValue_sub (β γ : Fin K → ℝ) :
    fittedValue X (fun j => β j - γ j) =
      fittedValue X β - fittedValue X γ := by
  simp [fittedValue, sub_smul, Finset.sum_sub_distrib]

/-- Residualization commutes with forming a fitted value. -/
lemma residualize_fittedValue (β : Fin K → ℝ) :
    residualize H (fittedValue X β) =
      fittedValue (fun j => residualize H (X j)) β := by
  rw [← residualizeL_apply]
  change residualizeL H (fittedValue X β) =
    fittedValue (fun j => residualizeL H (X j)) β
  simp [fittedValue]

/-- Residualization of the raw regression residual is the residualized
outcome minus the fitted value of the residualized regressors. -/
lemma residualize_regressionResidual (Y : V) (β : Fin K → ℝ) :
    residualize H (Y - fittedValue X β) =
      residualize H Y - fittedValue (fun j => residualize H (X j)) β := by
  rw [← residualizeL_apply]
  change residualizeL H (Y - fittedValue X β) =
    residualizeL H Y - fittedValue (fun j => residualizeL H (X j)) β
  rw [map_sub]
  rw [show residualizeL H (fittedValue X β) =
      fittedValue (fun j => residualizeL H (X j)) β by
        simpa [residualizeL_apply] using residualize_fittedValue H X β]

/-- The residualized Gram matrix `Q_{XX}` with entries
`⟨residualize H (X j), residualize H (X k)⟩`. -/
noncomputable def gramResid : Matrix (Fin K) (Fin K) ℝ :=
  fun j k => inner ℝ (residualize H (X j)) (residualize H (X k))

/-- Each entry of the residualized Gram matrix is the inner product of two residualized
regressors. -/
@[simp] lemma gramResid_apply (j k : Fin K) :
    gramResid H X j k =
      inner ℝ (residualize H (X j)) (residualize H (X k)) := rfl

/-- The right-hand side of the residualized normal equations,
`r_j := ⟨residualize H (X j), Y⟩`. -/
noncomputable def residInnerVec (Y : V) : Fin K → ℝ :=
  fun j => inner ℝ (residualize H (X j)) Y

/-- Each entry of the residualized right-hand side is the inner product of a residualized
regressor with the outcome. -/
@[simp] lemma residInnerVec_apply (Y : V) (j : Fin K) :
    residInnerVec H X Y j = inner ℝ (residualize H (X j)) Y := rfl

/-- **The FWL coefficient.** Defined directly as
`Q_{XX}⁻¹ *ᵥ (fun j => ⟨X̃ j, Y⟩)`. -/
noncomputable def fwlCoef (Y : V) : Fin K → ℝ :=
  (gramResid H X)⁻¹.mulVec (residInnerVec H X Y)

/-- **Residualized normal equations (FWL coefficient form).**
If `Q_{XX} = gramResid H X` is invertible (equivalently, the residualized
regressors are linearly independent), the FWL coefficient
`fwlCoef H X Y = Q_{XX}⁻¹ *ᵥ (fun j => ⟨X̃ j, Y⟩)` satisfies the
residualized normal equations
`Q_{XX} *ᵥ fwlCoef H X Y = (fun j => ⟨X̃ j, Y⟩)`. -/
lemma gramResid_mulVec_fwlCoef
    (Y : V) (hQ : IsUnit (gramResid H X).det) :
    (gramResid H X).mulVec (fwlCoef H X Y) = residInnerVec H X Y := by
  -- Pure matrix algebra: `A *ᵥ (A⁻¹ *ᵥ b) = b` when `A.det` is a unit.
  unfold fwlCoef
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hQ,
      Matrix.one_mulVec]

/-- **Symmetric residualization for the FWL right-hand side.**
The residualized inner products `⟨X̃ j, Y⟩` agree with `⟨X̃ j, Ỹ⟩`,
so the FWL coefficient depends only on the residualized response. -/
lemma residInnerVec_eq_residualize_right (Y : V) :
    residInnerVec H X Y = residInnerVec H X (residualize H Y) := by
  funext j
  simpa [residInnerVec] using residualize_inner_swap_right H (X j) Y

/-- Residualized least-squares objective. -/
noncomputable def residualizedObjective (Y : V) (β : Fin K → ℝ) : ℝ :=
  inner ℝ
    (residualize H Y - fittedValue (fun j => residualize H (X j)) β)
    (residualize H Y - fittedValue (fun j => residualize H (X j)) β)

/-- Original least-squares objective with an explicit nuisance term `h ∈ H`. -/
noncomputable def originalObjective (Y : V) (β : Fin K → ℝ) (h : V) : ℝ :=
  inner ℝ (Y - fittedValue X β - h) (Y - fittedValue X β - h)

/-- The residual left by `fwlCoef` is orthogonal to every residualized
regressor. This is the normal-equation form used in the completing-square
argument. -/
lemma inner_residualizedRegressor_fwlResidual
    (Y : V) (hQ : IsUnit (gramResid H X).det) (j : Fin K) :
    inner ℝ (residualize H (X j))
      (residualize H Y -
        fittedValue (fun k => residualize H (X k)) (fwlCoef H X Y)) = 0 := by
  have hne := congrFun (gramResid_mulVec_fwlCoef H X Y hQ) j
  rw [← sub_eq_zero]
  rw [inner_sub_right]
  rw [fittedValue]
  simp_rw [inner_sum, inner_smul_right]
  rw [← residualize_inner_swap_right H (X j) Y]
  have hsum :
      (∑ x, fwlCoef H X Y x *
          inner ℝ (residualize H (X j)) (residualize H (X x))) =
        ∑ x, inner ℝ (residualize H (X j)) (residualize H (X x)) *
          fwlCoef H X Y x := by
    apply Finset.sum_congr rfl
    intro x _hx
    ring
  rw [hsum]
  simpa [Matrix.mulVec, dotProduct, gramResid, residInnerVec] using
    sub_eq_zero.mpr hne.symm

/-- Completing-square identity for the residualized objective around the
FWL coefficient. -/
theorem residualizedObjective_eq_fwlCoef_add_error
    (Y : V) (hQ : IsUnit (gramResid H X).det) (β : Fin K → ℝ) :
    residualizedObjective H X Y β =
      residualizedObjective H X Y (fwlCoef H X Y) +
        inner ℝ
          (fittedValue (fun j => residualize H (X j))
            (fun j => fwlCoef H X Y j - β j))
          (fittedValue (fun j => residualize H (X j))
            (fun j => fwlCoef H X Y j - β j)) := by
  let Xtilde : Fin K → V := fun j => residualize H (X j)
  let b : Fin K → ℝ := fwlCoef H X Y
  let e : V := residualize H Y - fittedValue Xtilde b
  let z : V := fittedValue Xtilde (fun j => b j - β j)
  have hz_eq : z = fittedValue Xtilde b - fittedValue Xtilde β := by
    dsimp [z, b]
    rw [fittedValue_sub]
  have hdecomp : residualize H Y - fittedValue Xtilde β = e + z := by
    dsimp [e]
    rw [hz_eq]
    abel
  have hcross' : inner ℝ z e = 0 := by
    dsimp [z, e, Xtilde, b]
    rw [fittedValue]
    simp_rw [sum_inner, inner_smul_left]
    apply Finset.sum_eq_zero
    intro j _hj
    have hjzero :
        inner ℝ (X j - H.starProjection (X j))
          (Y - H.starProjection Y -
            fittedValue (fun j => X j - H.starProjection (X j)) (fwlCoef H X Y)) = 0 := by
      simpa [residualize] using
        inner_residualizedRegressor_fwlResidual H X Y hQ j
    rw [hjzero]
    simp
  have hcross : inner ℝ e z = 0 := by
    rw [real_inner_comm, hcross']
  have hpyth :
      residualizedObjective H X Y β =
        residualizedObjective H X Y b + inner ℝ z z := by
    change inner ℝ (residualize H Y - fittedValue Xtilde β)
        (residualize H Y - fittedValue Xtilde β) =
      inner ℝ e e + inner ℝ z z
    rw [hdecomp]
    rw [inner_add_left, inner_add_right, inner_add_right, hcross, hcross']
    ring
  simpa [z, Xtilde, b] using hpyth

/-- The FWL coefficient minimizes the residualized least-squares objective. -/
theorem fwlCoef_residualized_minimizes
    (Y : V) (hQ : IsUnit (gramResid H X).det) (β : Fin K → ℝ) :
    residualizedObjective H X Y (fwlCoef H X Y) ≤
      residualizedObjective H X Y β := by
  rw [residualizedObjective_eq_fwlCoef_add_error H X Y hQ β]
  exact le_add_of_nonneg_right (by simp)

/-- Pythagorean split of the original objective into the residualized
objective plus the squared distance from `h` to the projection of the raw
regression residual onto `H`. -/
theorem originalObjective_eq_residualizedObjective_add_projectionError
    (Y : V) (β : Fin K → ℝ) {h : V} (hh : h ∈ H) :
    originalObjective X Y β h =
      residualizedObjective H X Y β +
        inner ℝ (H.orthogonalProjectionFn (Y - fittedValue X β) - h)
          (H.orthogonalProjectionFn (Y - fittedValue X β) - h) := by
  let v : V := Y - fittedValue X β
  let r : V := residualize H v
  let p : V := H.orthogonalProjectionFn v - h
  have hp_mem : p ∈ H := by
    exact Submodule.sub_mem H (Submodule.orthogonalProjectionFn_mem (K := H) v) hh
  have horth : inner ℝ r p = 0 := by
    exact inner_residualize_of_mem H v hp_mem
  have horth' : inner ℝ p r = 0 := by
    rw [real_inner_comm, horth]
  have hvh : v - h = r + p := by
    dsimp [r, p, v]
    simp
  have hres_vec :
      residualize H Y - fittedValue (fun j => residualize H (X j)) β = r := by
    dsimp [r, v]
    exact (residualize_regressionResidual H X Y β).symm
  have hres : residualizedObjective H X Y β = inner ℝ r r := by
    change inner ℝ
        (residualize H Y - fittedValue (fun j => residualize H (X j)) β)
        (residualize H Y - fittedValue (fun j => residualize H (X j)) β) =
      inner ℝ r r
    rw [hres_vec]
  dsimp [originalObjective]
  change inner ℝ (v - h) (v - h) =
    residualizedObjective H X Y β + inner ℝ p p
  rw [hvh, hres]
  rw [inner_add_left, inner_add_right, inner_add_right, horth, horth']
  ring

/-- For fixed `β`, the residualized objective is the minimum of the original
objective over the nuisance subspace `H`. -/
theorem residualizedObjective_le_originalObjective
    (Y : V) (β : Fin K → ℝ) {h : V} (hh : h ∈ H) :
    residualizedObjective H X Y β ≤ originalObjective X Y β h := by
  rw [originalObjective_eq_residualizedObjective_add_projectionError H X Y β hh]
  exact le_add_of_nonneg_right
    (by simp)

/-- At the nuisance projection, the original objective equals the
residualized objective. -/
theorem originalObjective_projection_eq_residualizedObjective
    (Y : V) (β : Fin K → ℝ) :
    originalObjective X Y β (H.orthogonalProjectionFn (Y - fittedValue X β)) =
      residualizedObjective H X Y β := by
  have hmem : H.orthogonalProjectionFn (Y - fittedValue X β) ∈ H :=
    Submodule.orthogonalProjectionFn_mem (K := H) (Y - fittedValue X β)
  rw [originalObjective_eq_residualizedObjective_add_projectionError H X Y β hmem]
  simp

/-- **Standard finite-dimensional FWL theorem.**
The residualized FWL coefficient, paired with the nuisance projection of its
raw residual, minimizes the original least-squares problem over coefficients
and nuisance terms in `H`. -/
theorem fwlCoef_original_minimizes
    (Y : V) (hQ : IsUnit (gramResid H X).det)
    (β : Fin K → ℝ) {h : V} (hh : h ∈ H) :
    originalObjective X Y (fwlCoef H X Y)
        (H.orthogonalProjectionFn (Y - fittedValue X (fwlCoef H X Y))) ≤
      originalObjective X Y β h := by
  calc
    originalObjective X Y (fwlCoef H X Y)
        (H.orthogonalProjectionFn (Y - fittedValue X (fwlCoef H X Y)))
        = residualizedObjective H X Y (fwlCoef H X Y) := by
          rw [originalObjective_projection_eq_residualizedObjective]
    _ ≤ residualizedObjective H X Y β :=
          fwlCoef_residualized_minimizes H X Y hQ β
    _ ≤ originalObjective X Y β h :=
          residualizedObjective_le_originalObjective H X Y β hh

/-- Any minimizer of the original least-squares problem has coefficient block
equal to the FWL coefficient. This is the uniqueness part of the standard FWL
statement for the `X`-block. -/
theorem fwlCoef_eq_of_original_minimizer
    (Y : V) (hQ : IsUnit (gramResid H X).det)
    (β : Fin K → ℝ) {h : V} (hh : h ∈ H)
    (hmin : ∀ (γ : Fin K → ℝ) {g : V}, g ∈ H →
      originalObjective X Y β h ≤ originalObjective X Y γ g) :
    β = fwlCoef H X Y := by
  let Xtilde : Fin K → V := fun j => residualize H (X j)
  let b : Fin K → ℝ := fwlCoef H X Y
  let z : V := fittedValue Xtilde (fun j => b j - β j)
  let hp : V := H.orthogonalProjectionFn (Y - fittedValue X b)
  have hp_mem : hp ∈ H := by
    dsimp [hp]
    exact Submodule.orthogonalProjectionFn_mem (K := H) (Y - fittedValue X b)
  have hle₁ : residualizedObjective H X Y β ≤ residualizedObjective H X Y b := by
    calc
      residualizedObjective H X Y β ≤ originalObjective X Y β h :=
        residualizedObjective_le_originalObjective H X Y β hh
      _ ≤ originalObjective X Y b hp := hmin b hp_mem
      _ = residualizedObjective H X Y b := by
        simpa [hp] using originalObjective_projection_eq_residualizedObjective H X Y b
  have hle₂ : residualizedObjective H X Y b ≤ residualizedObjective H X Y β :=
    fwlCoef_residualized_minimizes H X Y hQ β
  have hres_eq : residualizedObjective H X Y β = residualizedObjective H X Y b :=
    le_antisymm hle₁ hle₂
  have hpyth := residualizedObjective_eq_fwlCoef_add_error H X Y hQ β
  have hz_inner : inner ℝ z z = 0 := by
    rw [hres_eq] at hpyth
    have hpyth_z :
        residualizedObjective H X Y b =
          residualizedObjective H X Y b + inner ℝ z z := by
      simpa [z, Xtilde, b] using hpyth
    linarith
  have hz0 : z = 0 := inner_self_eq_zero.mp hz_inner
  let δ : Fin K → ℝ := fun j => b j - β j
  have hmul : (gramResid H X).mulVec δ = 0 := by
    funext j
    have hinner : inner ℝ (residualize H (X j)) z = 0 := by
      rw [hz0, inner_zero_right]
    dsimp [z, Xtilde, δ] at hinner ⊢
    rw [fittedValue] at hinner
    simp_rw [inner_sum, inner_smul_right] at hinner
    simpa [Matrix.mulVec, dotProduct, gramResid, mul_comm] using hinner
  have hδ0 : δ = 0 := Matrix.eq_zero_of_mulVec_eq_zero hQ.ne_zero hmul
  funext j
  have hj := congrFun hδ0 j
  dsimp [δ, b] at hj
  linarith

/-- Full uniqueness characterization of the original least-squares minimizer:
every minimizer equals the FWL coefficient paired with the nuisance projection
of its raw residual. -/
theorem original_minimizer_eq_fwlCoef_projection
    (Y : V) (hQ : IsUnit (gramResid H X).det)
    (β : Fin K → ℝ) {h : V} (hh : h ∈ H)
    (hmin : ∀ (γ : Fin K → ℝ) {g : V}, g ∈ H →
      originalObjective X Y β h ≤ originalObjective X Y γ g) :
    β = fwlCoef H X Y ∧
      h = H.orthogonalProjectionFn (Y - fittedValue X (fwlCoef H X Y)) := by
  have hβ : β = fwlCoef H X Y :=
    fwlCoef_eq_of_original_minimizer H X Y hQ β hh hmin
  have hp : h = H.orthogonalProjectionFn (Y - fittedValue X β) := by
    let p : V := H.orthogonalProjectionFn (Y - fittedValue X β)
    have hp_mem : p ∈ H := by
      dsimp [p]
      exact Submodule.orthogonalProjectionFn_mem (K := H) (Y - fittedValue X β)
    have hle : originalObjective X Y β h ≤ originalObjective X Y β p :=
      hmin β hp_mem
    have hsplit := originalObjective_eq_residualizedObjective_add_projectionError H X Y β hh
    have hproj : originalObjective X Y β p = residualizedObjective H X Y β := by
      simpa [p] using originalObjective_projection_eq_residualizedObjective H X Y β
    rw [hsplit, hproj] at hle
    have hnonneg :
        0 ≤ inner ℝ (H.orthogonalProjectionFn (Y - fittedValue X β) - h)
          (H.orthogonalProjectionFn (Y - fittedValue X β) - h) := by
      simp
    have hz :
        inner ℝ (H.orthogonalProjectionFn (Y - fittedValue X β) - h)
          (H.orthogonalProjectionFn (Y - fittedValue X β) - h) = 0 := by
      linarith
    have hzero : H.orthogonalProjectionFn (Y - fittedValue X β) - h = 0 :=
      inner_self_eq_zero.mp hz
    rw [sub_eq_zero] at hzero
    exact hzero.symm
  constructor
  · exact hβ
  · rw [hp, hβ]

end Causalean.Mathlib.FWL
