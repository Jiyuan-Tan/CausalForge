/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Bilinear remainder bound for `GeneralMoment`

* `BilinearRemainder M C` — `|∫ m(η, ·, θ₀) dP_Z| ≤ C · ρ₁(η, η₀) · ρ₂(η, η₀)`
  for every `η ∈ M.H_ε`.
* `bilinear_remainder_of_smoothness` — a sufficient condition for
  `BilinearRemainder` from Neyman orthogonality plus a uniform second-order
  envelope on the linearization residual.

See `docs/superpowers/specs/2026-05-06-general-dml-framework-design.md` §4.4.
-/

import Causalean.Estimation.OrthogonalMoments.NeymanOrthogonal

/-! # Bilinear Remainder Bounds

This file formalizes the product-rate remainder condition for abstract
orthogonal moments. It also gives a smoothness bridge showing that Neyman
orthogonality plus a uniform second-order envelope implies such a bilinear
population bias bound. -/

namespace Causalean
namespace Estimation
namespace OrthogonalMoments

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
         {Z : Type*} [MeasurableSpace Z] {P_Z : MeasureTheory.Measure Z}
         {H : Type*} [AddCommGroup H] [Module ℝ H]

/-- Bilinear remainder predicate: the population moment at any
`η ∈ H_ε` is bounded by `C · ρ₁(η, η₀) · ρ₂(η, η₀)`. -/
def BilinearRemainder (M : GeneralMoment Ω μ Z P_Z H) (C : ℝ) : Prop :=
  ∀ η ∈ M.H_ε,
    |∫ z, M.m η z M.θ₀ ∂P_Z|
      ≤ C * ((M.ρ₁ η M.η₀ : ℝ)) * ((M.ρ₂ η M.η₀ : ℝ))

/-- **Smoothness bridge to a bilinear remainder bound.** For [a general moment `M` with
directional derivative `D` satisfying Neyman orthogonality](hyp:M,D,hNO), given [an envelope `g`
that is `P_Z`-integrable](hyp:g,hg_int), suppose the linearization residual obeys [a uniform
second-order envelope with constant `K`: for every perturbation η in the nuisance neighborhood,
`|m(η,·,θ₀) − m(η₀,·,θ₀) − dM(η,·)| ≤ K·ρ₁(η,η₀)·ρ₂(η,η₀)·g` almost everywhere](hyp:K,hSecond),
with [the directional derivative integrable at every such η](hyp:hdM_int), [the moment integrable
at the baseline η₀](hyp:hM0_int), [the moment integrable at every perturbed η](hyp:hMη_int), and
[the moment having population mean zero](hyp:hMZ). Then [some constant C makes the population
moment obey the bilinear remainder bound C·ρ₁(η,η₀)·ρ₂(η,η₀) uniformly over the nuisance
neighborhood](goal). -/
theorem bilinear_remainder_of_smoothness
    (M : GeneralMoment Ω μ Z P_Z H) (D : HasDirDeriv M)
    (hNO : NeymanOrthogonal M D)
    {K : ℝ} {g : Z → ℝ}
    (hg_int : Integrable g P_Z)
    (hSecond : ∀ η ∈ M.H_ε,
      ∀ᵐ z ∂P_Z,
        |M.m η z M.θ₀ - M.m M.η₀ z M.θ₀ - D.dM η z|
          ≤ K * ((M.ρ₁ η M.η₀ : ℝ)) * ((M.ρ₂ η M.η₀ : ℝ)) * g z)
    (hdM_int : ∀ η ∈ M.H_ε, Integrable (fun z => D.dM η z) P_Z)
    (hM0_int : Integrable (fun z => M.m M.η₀ z M.θ₀) P_Z)
    (hMη_int : ∀ η ∈ M.H_ε,
      Integrable (fun z => M.m η z M.θ₀) P_Z)
    (hMZ : MeanZero M) :
    ∃ C, BilinearRemainder M C := by
  refine ⟨|K| * ∫ z, |g z| ∂P_Z, ?_⟩
  intro η hη
  let r₁ : ℝ := M.ρ₁ η M.η₀
  let r₂ : ℝ := M.ρ₂ η M.η₀
  let rem : Z → ℝ := fun z =>
    M.m η z M.θ₀ - M.m M.η₀ z M.θ₀ - D.dM η z
  have hr₁_nonneg : 0 ≤ r₁ := by
    dsimp [r₁]
    exact NNReal.coe_nonneg _
  have hr₂_nonneg : 0 ≤ r₂ := by
    dsimp [r₂]
    exact NNReal.coe_nonneg _
  have hrem_int : Integrable rem P_Z := by
    dsimp [rem]
    exact ((hMη_int η hη).sub hM0_int).sub (hdM_int η hη)
  have hrem_abs_int : Integrable (fun z => |rem z|) P_Z := by
    simpa [Real.norm_eq_abs] using hrem_int.norm
  have hbound_int : Integrable (fun z => |K| * r₁ * r₂ * |g z|) P_Z := by
    simpa [Real.norm_eq_abs, mul_assoc] using
      (hg_int.norm.const_mul (|K| * r₁ * r₂))
  have hpoint :
      ∀ᵐ z ∂P_Z, |rem z| ≤ |K| * r₁ * r₂ * |g z| := by
    filter_upwards [hSecond η hη] with z hz
    dsimp [rem, r₁, r₂] at hz ⊢
    refine hz.trans ?_
    calc
      K * (M.ρ₁ η M.η₀ : ℝ) * (M.ρ₂ η M.η₀ : ℝ) * g z
          ≤ |K * (M.ρ₁ η M.η₀ : ℝ) * (M.ρ₂ η M.η₀ : ℝ) * g z| :=
            le_abs_self _
      _ = |K| * (M.ρ₁ η M.η₀ : ℝ) * (M.ρ₂ η M.η₀ : ℝ) * |g z| := by
            rw [abs_mul, abs_mul, abs_mul]
            simp [abs_of_nonneg (NNReal.coe_nonneg (M.ρ₁ η M.η₀)),
              abs_of_nonneg (NNReal.coe_nonneg (M.ρ₂ η M.η₀)), mul_assoc]
  have hrem_integral :
      ∫ z, rem z ∂P_Z = ∫ z, M.m η z M.θ₀ ∂P_Z := by
    have hdiff_int :
        Integrable (fun z => M.m η z M.θ₀ - M.m M.η₀ z M.θ₀) P_Z := by
      exact (hMη_int η hη).sub hM0_int
    dsimp [rem]
    change
      ∫ z,
          ((fun z : Z => M.m η z M.θ₀ - M.m M.η₀ z M.θ₀) z -
              (fun z : Z => D.dM η z) z) ∂P_Z =
        ∫ z, M.m η z M.θ₀ ∂P_Z
    rw [integral_sub hdiff_int (hdM_int η hη)]
    rw [integral_sub (hMη_int η hη) hM0_int]
    rw [hMZ, hNO η hη]
    ring
  calc
    |∫ z, M.m η z M.θ₀ ∂P_Z|
        = |∫ z, rem z ∂P_Z| := by rw [hrem_integral]
    _ ≤ ∫ z, |rem z| ∂P_Z :=
        MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ z, |K| * r₁ * r₂ * |g z| ∂P_Z :=
        integral_mono_ae hrem_abs_int hbound_int hpoint
    _ = |K| * r₁ * r₂ * (∫ z, |g z| ∂P_Z) := by
        rw [integral_const_mul]
    _ = (|K| * ∫ z, |g z| ∂P_Z) * r₁ * r₂ := by
        ring

end OrthogonalMoments
end Estimation
end Causalean
