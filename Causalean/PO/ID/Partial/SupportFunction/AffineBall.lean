/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Sharp endpoints over an affine subspace intersected with a ball

The canonical Hilbert-space partial-identification program: a target functional
`⟪c, ·⟫` optimized over the *bridge fiber* — the solutions of a linear equation
`A h = b` (observed-data constraints) that also satisfy a norm bound `‖h‖ ≤ B`
(an L²-size restriction replacing the usual sup-norm box).  This is exactly the
proximal-L2-bridge identified set (`pid_proximal_l2_bridge`).

Writing `h = h₀ + v` with `h₀` the minimum-norm solution (`h₀ ⊥ ker A`) and
`v ∈ ker A` the free direction, the Pythagorean split `‖h‖² = ‖h₀‖² + ‖v‖²`
turns the program into maximizing `⟪c, v⟫` over `v ∈ ker A`, `‖v‖² ≤ B² − ‖h₀‖²`.
Only the `ker A`-component `P c = orthogonalProjection (ker A) c` of `c` matters,
and Cauchy–Schwarz gives the closed form

    supportFn (affineBall A b B) c = ⟪c, h₀⟫ + √(B² − ‖h₀‖²) · ‖P c‖,

a width `2√(B² − ‖h₀‖²)·‖P c‖`, with **point collapse** `width = 0 ⇔ P c = 0`,
i.e. `c ⊥ ker A` (equivalently `c` lies in the closed row space of `A`).

## Main results

* `opKer` / `affineBall` — the free-direction subspace `ker A` and the feasible fiber.
* `supportFn_affineBall_eq` — the closed-form support value.
* `width_affineBall_eq` — the closed-form width.
* `affineBall_point_identified_iff` — point identification `⇔ P c = 0`.
-/

import Causalean.PO.ID.Partial.SupportFunction.Interval
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! # Support bounds for an affine ball

This file solves the support-function problem for a linear functional over the
intersection of an affine solution set and a Hilbert-space ball. It defines the
free-direction kernel `opKer` and feasible set `affineBall`, proves the
closed-form endpoint `supportFn_affineBall_eq`, derives the width formula
`width_affineBall_eq`, and characterizes point identification by
`affineBall_point_identified_iff`.
-/

open scoped RealInnerProductSpace

namespace Causalean
namespace PartialID

variable {H F : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The **free-direction subspace** of a continuous operator: perturbations in `ker A` do not change
the linear constraint `A h = b`. -/
abbrev opKer (A : H →L[ℝ] F) : Submodule ℝ H := LinearMap.ker (A : H →ₗ[ℝ] F)

/-- The free-direction subspace of a continuous linear map admits an orthogonal projection because
the kernel is closed in a complete Hilbert space. -/
instance kerHasOrthogonalProjection (A : H →L[ℝ] F) :
    (opKer A).HasOrthogonalProjection := by
  haveI := (ContinuousLinearMap.isClosed_ker A).completeSpace_coe
  infer_instance

/-- The affine-ball fiber contains the solutions to a linear equation that also satisfy a norm
bound. -/
def affineBall (A : H →L[ℝ] F) (b : F) (B : ℝ) : Set H := {h | A h = b ∧ ‖h‖ ≤ B}

omit [CompleteSpace H] in
/-- Membership in the affine-ball fiber is exactly satisfying the equation and the norm bound. -/
@[simp] theorem mem_affineBall {A : H →L[ℝ] F} {b : F} {B : ℝ} {h : H} :
    h ∈ affineBall A b B ↔ A h = b ∧ ‖h‖ ≤ B := Iff.rfl

/-- **Closed-form support value** over the affine-ball fiber: with `h₀` the
minimum-norm solution (`h₀ ⊥ ker A`, fitting the ball), the best case of `⟪c,·⟫`
is `⟪c, h₀⟫ + √(B² − ‖h₀‖²)·‖P c‖`, `P` the projection onto `ker A`. -/
theorem supportFn_affineBall_eq (A : H →L[ℝ] F) {b : F} {B : ℝ} {c h₀ : H}
    (hsol : A h₀ = b) (hperp : h₀ ∈ (opKer A)ᗮ) (hfit : ‖h₀‖ ≤ B) :
    supportFn (affineBall A b B) c
      = ⟪c, h₀⟫ + Real.sqrt (B ^ 2 - ‖h₀‖ ^ 2)
          * ‖(Submodule.orthogonalProjection (opKer A) c : H)‖ := by
  set K : Submodule ℝ H := opKer A with hK
  set Pc : H := (Submodule.orthogonalProjection K c : H) with hPc
  set r : ℝ := Real.sqrt (B ^ 2 - ‖h₀‖ ^ 2) with hr
  -- basic nonnegativity facts
  have hB2 : (0 : ℝ) ≤ B ^ 2 - ‖h₀‖ ^ 2 := by
    have : ‖h₀‖ ^ 2 ≤ B ^ 2 := by
      have hn : (0 : ℝ) ≤ ‖h₀‖ := norm_nonneg _
      nlinarith [hn, hfit]
    linarith
  have hr_nonneg : (0 : ℝ) ≤ r := Real.sqrt_nonneg _
  have hr_sq : r ^ 2 = B ^ 2 - ‖h₀‖ ^ 2 := Real.sq_sqrt hB2
  -- (FIBER): A h = b ↔ h - h₀ ∈ K
  have hfiber : ∀ h : H, A h = b ↔ h - h₀ ∈ K := by
    intro h
    rw [hK, opKer, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, map_sub, hsol, sub_eq_zero]
  -- (PYTHAG): for v ∈ K, ⟪h₀, v⟫ = 0
  have hpythag_inner : ∀ v : H, v ∈ K → ⟪h₀, v⟫ = 0 := by
    intro v hv
    exact Submodule.inner_left_of_mem_orthogonal hv hperp
  have hpythag : ∀ v : H, v ∈ K → ‖h₀ + v‖ ^ 2 = ‖h₀‖ ^ 2 + ‖v‖ ^ 2 := by
    intro v hv
    rw [norm_add_sq_real, hpythag_inner v hv]; ring
  -- (PROJ): for v ∈ K, ⟪c, v⟫ = ⟪Pc, v⟫
  have hproj : ∀ v : H, v ∈ K → ⟪c, v⟫ = ⟪Pc, v⟫ := by
    intro v hv
    have h0 : ⟪c - Pc, v⟫ = 0 := by
      have hz := Submodule.starProjection_inner_eq_zero (K := K) c v hv
      rw [Submodule.starProjection_apply] at hz
      rw [hPc]; exact hz
    rw [inner_sub_left] at h0
    linarith [h0]
  -- h₀ is feasible
  have hh0_mem : h₀ ∈ affineBall A b B := ⟨hsol, hfit⟩
  -- KEY upper-bound computation: for any feasible h, ⟪c,h⟫ ≤ ⟪c,h₀⟫ + r * ‖Pc‖
  have hub : ∀ h ∈ affineBall A b B, ⟪c, h⟫ ≤ ⟪c, h₀⟫ + r * ‖Pc‖ := by
    intro h hh
    obtain ⟨hAh, hnorm⟩ := hh
    set v : H := h - h₀ with hv_def
    have hvK : v ∈ K := (hfiber h).mp hAh
    have hh_eq : h = h₀ + v := by rw [hv_def]; abel
    -- ‖v‖ ≤ r
    have hnorm_sq : ‖h‖ ^ 2 = ‖h₀‖ ^ 2 + ‖v‖ ^ 2 := by rw [hh_eq]; exact hpythag v hvK
    have hv_le : ‖v‖ ^ 2 ≤ B ^ 2 - ‖h₀‖ ^ 2 := by
      have hhB : ‖h‖ ^ 2 ≤ B ^ 2 := by
        have hn : (0 : ℝ) ≤ ‖h‖ := norm_nonneg _
        nlinarith [hn, hnorm]
      linarith [hnorm_sq]
    have hv_le_r : ‖v‖ ≤ r := by
      rw [hr]
      calc ‖v‖ = Real.sqrt (‖v‖ ^ 2) := by rw [Real.sqrt_sq (norm_nonneg _)]
        _ ≤ Real.sqrt (B ^ 2 - ‖h₀‖ ^ 2) := Real.sqrt_le_sqrt hv_le
    -- ⟪c,h⟫ = ⟪c,h₀⟫ + ⟪Pc,v⟫
    have hsplit : ⟪c, h⟫ = ⟪c, h₀⟫ + ⟪Pc, v⟫ := by
      rw [hh_eq, inner_add_right, hproj v hvK]
    rw [hsplit]
    have hcs : ⟪Pc, v⟫ ≤ ‖Pc‖ * ‖v‖ := real_inner_le_norm Pc v
    have hbound : ‖Pc‖ * ‖v‖ ≤ ‖Pc‖ * r := by
      apply mul_le_mul_of_nonneg_left hv_le_r (norm_nonneg _)
    have : ⟪Pc, v⟫ ≤ r * ‖Pc‖ := by rw [mul_comm r] at *; linarith [hcs, hbound]
    linarith
  -- BddAbove for le_supportFn
  have hbdd : BddAbove ((fun x => ⟪c, x⟫) '' (affineBall A b B)) := by
    refine ⟨⟪c, h₀⟫ + r * ‖Pc‖, ?_⟩
    rintro _ ⟨h, hh, rfl⟩
    exact hub h hh
  apply le_antisymm
  · -- upper bound
    refine supportFn_le ⟨h₀, hh0_mem⟩ ?_
    intro h hh
    exact hub h hh
  · -- lower bound / attainment
    by_cases hPc0 : Pc = 0
    · -- Pc = 0: RHS = ⟪c, h₀⟫, attained at h₀
      have hnorm0 : ‖Pc‖ = 0 := by rw [hPc0]; simp
      rw [hnorm0]
      simp only [mul_zero, add_zero]
      have := le_supportFn (C := affineBall A b B) (d := c) hh0_mem hbdd
      exact this
    · -- Pc ≠ 0: maximizer h* = h₀ + (r/‖Pc‖) • Pc
      have hPcK : Pc ∈ K := by rw [hPc]; exact Submodule.coe_mem _
      have hPc_ne : ‖Pc‖ ≠ 0 := by
        rwa [ne_eq, norm_eq_zero]
      set v : H := (r / ‖Pc‖) • Pc with hv_def
      have hvK : v ∈ K := by rw [hv_def]; exact K.smul_mem _ hPcK
      have hv_norm : ‖v‖ = r := by
        rw [hv_def, norm_smul, Real.norm_eq_abs, abs_div, abs_of_nonneg hr_nonneg,
          abs_of_nonneg (norm_nonneg _)]
        field_simp
      set hstar : H := h₀ + v with hstar_def
      have hAstar : A hstar = b := by
        rw [hfiber hstar, hstar_def, add_sub_cancel_left]
        exact hvK
      have hstar_norm : ‖hstar‖ ≤ B := by
        have hsq : ‖hstar‖ ^ 2 = B ^ 2 := by
          rw [hstar_def, hpythag v hvK, hv_norm, hr_sq]; ring
        have hBnn : (0 : ℝ) ≤ B := le_trans (norm_nonneg _) hfit
        nlinarith [norm_nonneg hstar, hsq, hBnn]
      have hstar_mem : hstar ∈ affineBall A b B := ⟨hAstar, hstar_norm⟩
      have hinner_v : ⟪Pc, v⟫ = r * ‖Pc‖ := by
        rw [hv_def, real_inner_smul_right, real_inner_self_eq_norm_sq, pow_two,
          div_mul_eq_mul_div, mul_div_assoc]
        rw [mul_div_assoc, div_self hPc_ne, mul_one]
      have hval : ⟪c, hstar⟫ = ⟪c, h₀⟫ + r * ‖Pc‖ := by
        rw [hstar_def, inner_add_right, hproj v hvK, hinner_v]
      have := le_supportFn (C := affineBall A b B) (d := c) hstar_mem hbdd
      rw [hval] at this
      exact this

/-- **Closed-form width** of the affine-ball identified set: twice the residual radius times the
target's free-direction norm. -/
theorem width_affineBall_eq (A : H →L[ℝ] F) {b : F} {B : ℝ} {c h₀ : H}
    (hsol : A h₀ = b) (hperp : h₀ ∈ (opKer A)ᗮ) (hfit : ‖h₀‖ ≤ B) :
    width (affineBall A b B) c
      = 2 * Real.sqrt (B ^ 2 - ‖h₀‖ ^ 2)
          * ‖(Submodule.orthogonalProjection (opKer A) c : H)‖ := by
  unfold width
  rw [supportFn_affineBall_eq A hsol hperp hfit,
      supportFn_affineBall_eq A hsol hperp hfit]
  -- projection of -c is -(projection of c), so its norm equals ‖P c‖
  have hneg : (Submodule.orthogonalProjection (opKer A) (-c) : H)
      = -(Submodule.orthogonalProjection (opKer A) c : H) := by
    rw [map_neg]; rfl
  rw [hneg, norm_neg, inner_neg_left]
  ring

/-- **Point identification.** With strict slack in the ball (`‖h₀‖ < B`), the
identified set collapses to a point iff `c`'s component along the free directions
vanishes: `P c = 0`, i.e. `c ⊥ ker A`. -/
theorem affineBall_point_identified_iff (A : H →L[ℝ] F) {b : F} {B : ℝ} {c h₀ : H}
    (hsol : A h₀ = b) (hperp : h₀ ∈ (opKer A)ᗮ) (hfit : ‖h₀‖ < B) :
    width (affineBall A b B) c = 0
      ↔ Submodule.orthogonalProjection (opKer A) c = 0 := by
  rw [width_affineBall_eq A hsol hperp (le_of_lt hfit)]
  -- r = √(B² − ‖h₀‖²) > 0 under strict slack
  have hpos : (0 : ℝ) < B ^ 2 - ‖h₀‖ ^ 2 := by
    have h1 : (0 : ℝ) ≤ ‖h₀‖ := norm_nonneg _
    nlinarith [h1, hfit]
  have hr_pos : (0 : ℝ) < Real.sqrt (B ^ 2 - ‖h₀‖ ^ 2) := Real.sqrt_pos.mpr hpos
  constructor
  · intro hw
    have hPc0 : ‖(Submodule.orthogonalProjection (opKer A) c : H)‖ = 0 := by
      rcases mul_eq_zero.mp hw with h | h
      · exact absurd h (by positivity)
      · exact h
    rw [norm_eq_zero] at hPc0
    exact (Submodule.coe_eq_zero).mp hPc0
  · intro hP
    rw [hP]
    simp

end PartialID
end Causalean
