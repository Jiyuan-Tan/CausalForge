/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Riesz representer pattern

A unifying abstraction for linear-in-γ causal functionals
(ATE, policy value, average derivative, weighted treatment effects).

When a target functional `θ(P)` depends on a regression function `γ_0`
only through a continuous linear functional `L(γ_0)`, by the Riesz
representation theorem there exists `α_0 : X → ℝ` such that
`L(γ) = E_{P_X}[α_0(X) · γ(X)]` for every `γ` in the regression class.

The orthogonal score is then

  `m(z; θ, γ, α) := L(γ) + α(X) · (Y − γ(X)) − θ`,

whose mean-zero remainder factorises as `-(α − α₀) · (γ − γ₀)` —
explaining why product rates suffice in DML.

Reference:
* `def:sp-riesz` in `doc/basic_concepts/Semi-parametric Inference/
  semi_parametric_inference.tex`.
* Chernozhukov–Newey–Singh (2022) Riesz/RieszNet learning.
-/

import Causalean.Estimation.OrthogonalMoments.MomentFunctional

/-! # Riesz Scores for Orthogonal Moments

This file provides the Riesz-representation pattern for linear-in-regression
causal functionals. It defines the representer, the corresponding orthogonal
score, and the mean-zero and bilinear-remainder identities used by automatic
debiasing and double machine learning. -/

namespace Causalean
namespace Estimation
namespace OrthogonalMoments

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
         {Z : Type*} [MeasurableSpace Z] {P_Z : MeasureTheory.Measure Z}
         {X : Type*} [MeasurableSpace X]

/-- A **Riesz representation** for a linear functional `L` on a regression
class `H_γ ⊆ (X → ℝ)` under `P_X : Measure X`:

  `α₀ : X → ℝ`  and  `∀ γ ∈ H_γ_class, L γ = ∫ x, α₀ x · γ x ∂P_X`.

Concrete causal targets such as ATE and policy value construct an instance of
this structure from their identification proof. -/
structure RieszRepresentation
    (H_γ : Type*) [AddCommGroup H_γ] [Module ℝ H_γ]
    (γ_target : H_γ → X → ℝ)
    (L : H_γ → ℝ)
    (P_X : Measure X) where
  α₀ : X → ℝ
  α₀_meas : Measurable α₀
  α₀_integrable : Integrable α₀ P_X
  representation : ∀ γ : H_γ, L γ = ∫ x, α₀ x * γ_target γ x ∂P_X

/-- **Generic Riesz orthogonal score.**  Given a Riesz representation,
the orthogonal moment for the target `θ(P) := L(γ_0)` is

  `m(z; θ, γ, α) := L(γ) + α(X) · (Y_obs z − γ(X)) − θ`,

where `X = proj_X z`.  Concrete instances (ATE, policy value) supply the
projections `proj_X` and outcome `Y_obs` and integrate this with the
`GeneralMoment` interface. -/
noncomputable def rieszScore
    {H_γ : Type*} [AddCommGroup H_γ] [Module ℝ H_γ]
    (γ_target : H_γ → X → ℝ)
    (L : H_γ → ℝ)
    (proj_X : Z → X) (Y_obs : Z → ℝ)
    (γ : H_γ) (α : X → ℝ) (θ : ℝ) (z : Z) : ℝ :=
  L γ + α (proj_X z) * (Y_obs z - γ_target γ (proj_X z)) - θ

/-- **Mean-zero of the Riesz score at the truth.**

With `θ₀ := L γ₀` and the population regression-orthogonality assumption
`∫ z, α₀(proj_X z) · (Y_obs z − γ_target γ₀ (proj_X z)) ∂P_Z = 0` (which
holds when `γ_target γ₀` is the conditional expectation of `Y_obs` given
`proj_X`, since residuals are orthogonal to all square-integrable
functions of `proj_X`), the population orthogonal score evaluated at the
truth `(γ₀, α₀, L γ₀)` integrates to zero:

    ∫ z, rieszScore γ_target L proj_X Y_obs γ₀ rep.α₀ (L γ₀) z ∂P_Z = 0. -/
theorem rieszScore_meanZero
    {H_γ : Type*} [AddCommGroup H_γ] [Module ℝ H_γ]
    {γ_target : H_γ → X → ℝ}
    {L : H_γ → ℝ}
    {P_X : Measure X}
    [IsProbabilityMeasure P_Z]
    (rep : RieszRepresentation H_γ γ_target L P_X)
    (γ₀ : H_γ) (proj_X : Z → X) (Y_obs : Z → ℝ)
    (h_orthog :
      ∫ z, rep.α₀ (proj_X z) * (Y_obs z - γ_target γ₀ (proj_X z)) ∂P_Z = 0) :
    ∫ z, rieszScore γ_target L proj_X Y_obs γ₀ rep.α₀ (L γ₀) z ∂P_Z = 0 := by
  unfold rieszScore
  have h1 :
      (fun z => L γ₀ + rep.α₀ (proj_X z) * (Y_obs z - γ_target γ₀ (proj_X z)) - L γ₀)
        = fun z => rep.α₀ (proj_X z) * (Y_obs z - γ_target γ₀ (proj_X z)) := by
    funext z
    ring
  rw [h1, h_orthog]

private lemma integral_comp_proj_eq
    {P_X : Measure X} {proj_X : Z → X}
    (h_pushforward : P_X = P_Z.map proj_X)
    (h_proj_meas : Measurable proj_X)
    {f : X → ℝ} (hf_int : Integrable f P_X) :
    ∫ z, f (proj_X z) ∂P_Z = ∫ x, f x ∂P_X := by
  rw [h_pushforward]
  have hf_map : AEStronglyMeasurable f (P_Z.map proj_X) := by
    simpa [← h_pushforward] using hf_int.aestronglyMeasurable
  rw [MeasureTheory.integral_map h_proj_meas.aemeasurable hf_map]

omit [MeasurableSpace X] in
private lemma rieszScore_integral_eq
    {H_γ : Type*} [AddCommGroup H_γ] [Module ℝ H_γ]
    {γ_target : H_γ → X → ℝ}
    {L : H_γ → ℝ}
    [IsProbabilityMeasure P_Z]
    (γ₀ γ : H_γ) (α : X → ℝ)
    (proj_X : Z → X) (Y_obs : Z → ℝ)
    (h_orthog_α :
      ∫ z, α (proj_X z) * (Y_obs z - γ_target γ₀ (proj_X z)) ∂P_Z = 0)
    (h_int_resid_α :
      Integrable
        (fun z => α (proj_X z) * (Y_obs z - γ_target γ₀ (proj_X z))) P_Z)
    (h_int_αγ :
      Integrable (fun z => α (proj_X z) * γ_target γ (proj_X z)) P_Z)
    (h_int_αγ₀ :
      Integrable (fun z => α (proj_X z) * γ_target γ₀ (proj_X z)) P_Z) :
    ∫ z, rieszScore γ_target L proj_X Y_obs γ α (L γ₀) z ∂P_Z
      = L γ - L γ₀
          - ∫ z, α (proj_X z) * γ_target γ (proj_X z) ∂P_Z
          + ∫ z, α (proj_X z) * γ_target γ₀ (proj_X z) ∂P_Z := by
  let const : Z → ℝ := fun _ => L γ - L γ₀
  let resid : Z → ℝ :=
    fun z => α (proj_X z) * (Y_obs z - γ_target γ₀ (proj_X z))
  let prod : Z → ℝ :=
    fun z => α (proj_X z) * γ_target γ (proj_X z)
  let negProd : Z → ℝ := fun z => -prod z
  let prod₀ : Z → ℝ :=
    fun z => α (proj_X z) * γ_target γ₀ (proj_X z)
  have hscore :
      (fun z => rieszScore γ_target L proj_X Y_obs γ α (L γ₀) z)
        = fun z => const z + resid z + negProd z + prod₀ z := by
    funext z
    simp [rieszScore, const, resid, prod, negProd, prod₀]
    ring
  have hconst : Integrable const P_Z := integrable_const _
  have hresid : Integrable resid P_Z := h_int_resid_α
  have hprod : Integrable prod P_Z := h_int_αγ
  have hnegProd : Integrable negProd P_Z := hprod.neg
  have hprod₀ : Integrable prod₀ P_Z := h_int_αγ₀
  have hconst_resid : Integrable (fun z => const z + resid z) P_Z :=
    hconst.add hresid
  have htriple : Integrable (fun z => const z + resid z + negProd z) P_Z :=
    hconst_resid.add hnegProd
  rw [hscore]
  change ∫ z, (const z + resid z + negProd z) + prod₀ z ∂P_Z
      = L γ - L γ₀
          - ∫ z, α (proj_X z) * γ_target γ (proj_X z) ∂P_Z
          + ∫ z, α (proj_X z) * γ_target γ₀ (proj_X z) ∂P_Z
  rw [integral_add htriple hprod₀]
  rw [integral_add hconst_resid hnegProd]
  rw [integral_add hconst hresid]
  have horthog : ∫ z, resid z ∂P_Z = 0 := h_orthog_α
  rw [horthog]
  rw [integral_neg prod]
  simp [const, prod, prod₀]
  ring_nf

/-- **Bilinear remainder identity for the Riesz score.**

For any perturbation `(γ, α)` with finite residual and product moments,
the population orthogonal moment at `θ₀ := L γ₀` factorises as a product
of the regression error and the representer error:

    ∫ z, rieszScore γ_target L proj_X Y_obs γ α (L γ₀) z ∂P_Z
        − ∫ z, rieszScore γ_target L proj_X Y_obs γ₀ rep.α₀ (L γ₀) z ∂P_Z
      = − ∫ x, (α x − rep.α₀ x) · (γ_target γ x − γ_target γ₀ x) ∂P_X.

(With `score` evaluated at `(γ, α)` perturbed and `(γ₀, α₀)` the truth;
the difference of population scores equals the negative inner product of
the two errors in `L²(P_X)`.)

Hypotheses bundle the standard ingredients:

* `h_pushforward` — `P_X = P_Z.map proj_X`, so `∫ f(X) dP_Z = ∫ f dP_X`.
* `h_proj_meas`   — `proj_X` is measurable.
* representation  — supplied via `rep.representation`.
* regression-orthogonality of the perturbation `α` against the truth
  residual: `∫ z, α(proj_X z)·(Y_obs z − γ_target γ₀ (proj_X z)) ∂P_Z = 0`
  (holds when `γ_target γ₀` is the L²-projection of `Y_obs` onto
  measurable functions of `proj_X`).
* finite moments for the perturbed residual and the product terms. The
  residual condition is needed mathematically for Bochner integral linearity;
  product integrability under `P_X` is recovered from the composition
  integrability under `P_Z` using the pushforward identity. -/
theorem rieszScore_bilinearRem
    {H_γ : Type*} [AddCommGroup H_γ] [Module ℝ H_γ]
    {γ_target : H_γ → X → ℝ}
    {L : H_γ → ℝ}
    {P_X : Measure X}
    [IsProbabilityMeasure P_Z]
    (rep : RieszRepresentation H_γ γ_target L P_X)
    (γ₀ γ : H_γ) (α : X → ℝ)
    (proj_X : Z → X) (Y_obs : Z → ℝ)
    (h_pushforward : P_X = P_Z.map proj_X)
    (h_proj_meas : Measurable proj_X)
    (h_orthog_α₀ :
      ∫ z, rep.α₀ (proj_X z) * (Y_obs z - γ_target γ₀ (proj_X z)) ∂P_Z = 0)
    (h_orthog_α :
      ∫ z, α (proj_X z) * (Y_obs z - γ_target γ₀ (proj_X z)) ∂P_Z = 0)
    (h_int_resid_α :
      Integrable
        (fun z => α (proj_X z) * (Y_obs z - γ_target γ₀ (proj_X z))) P_Z)
    (h_int_αγ :
      Integrable (fun z => α (proj_X z) * γ_target γ (proj_X z)) P_Z)
    (h_int_αγ₀ :
      Integrable (fun z => α (proj_X z) * γ_target γ₀ (proj_X z)) P_Z)
    (h_int_α₀γ :
      Integrable (fun x => rep.α₀ x * γ_target γ x) P_X)
    (h_int_α₀γ₀ :
      Integrable (fun x => rep.α₀ x * γ_target γ₀ x) P_X)
    (h_int_α : Integrable α P_X)
    (h_int_γ : Integrable (γ_target γ) P_X)
    (h_int_γ₀ : Integrable (γ_target γ₀) P_X) :
    (∫ z, rieszScore γ_target L proj_X Y_obs γ α (L γ₀) z ∂P_Z)
        - (∫ z, rieszScore γ_target L proj_X Y_obs γ₀ rep.α₀ (L γ₀) z ∂P_Z)
      = - ∫ x, (α x - rep.α₀ x) * (γ_target γ x - γ_target γ₀ x) ∂P_X := by
  have h_int_αγ_X :
      Integrable (fun x => α x * γ_target γ x) P_X := by
    rw [h_pushforward]
    have h_asm :
        AEStronglyMeasurable (fun x => α x * γ_target γ x) (P_Z.map proj_X) := by
      simpa [← h_pushforward] using
        h_int_α.aestronglyMeasurable.mul h_int_γ.aestronglyMeasurable
    exact (MeasureTheory.integrable_map_measure h_asm h_proj_meas.aemeasurable).2 h_int_αγ
  have h_int_αγ₀_X :
      Integrable (fun x => α x * γ_target γ₀ x) P_X := by
    rw [h_pushforward]
    have h_asm :
        AEStronglyMeasurable (fun x => α x * γ_target γ₀ x) (P_Z.map proj_X) := by
      simpa [← h_pushforward] using
        h_int_α.aestronglyMeasurable.mul h_int_γ₀.aestronglyMeasurable
    exact (MeasureTheory.integrable_map_measure h_asm h_proj_meas.aemeasurable).2 h_int_αγ₀
  have hscore :
      ∫ z, rieszScore γ_target L proj_X Y_obs γ α (L γ₀) z ∂P_Z
        = L γ - L γ₀
            - ∫ z, α (proj_X z) * γ_target γ (proj_X z) ∂P_Z
            + ∫ z, α (proj_X z) * γ_target γ₀ (proj_X z) ∂P_Z :=
    rieszScore_integral_eq γ₀ γ α proj_X Y_obs h_orthog_α h_int_resid_α
      h_int_αγ h_int_αγ₀
  have htruth :
      ∫ z, rieszScore γ_target L proj_X Y_obs γ₀ rep.α₀ (L γ₀) z ∂P_Z = 0 :=
    rieszScore_meanZero rep γ₀ proj_X Y_obs h_orthog_α₀
  have hmap_αγ :
      ∫ z, α (proj_X z) * γ_target γ (proj_X z) ∂P_Z
        = ∫ x, α x * γ_target γ x ∂P_X :=
    integral_comp_proj_eq h_pushforward h_proj_meas h_int_αγ_X
  have hmap_αγ₀ :
      ∫ z, α (proj_X z) * γ_target γ₀ (proj_X z) ∂P_Z
        = ∫ x, α x * γ_target γ₀ x ∂P_X :=
    integral_comp_proj_eq h_pushforward h_proj_meas h_int_αγ₀_X
  have hrhs :
      ∫ x, (α x - rep.α₀ x) * (γ_target γ x - γ_target γ₀ x) ∂P_X
        = (∫ x, α x * γ_target γ x ∂P_X
              - ∫ x, rep.α₀ x * γ_target γ x ∂P_X)
            - (∫ x, α x * γ_target γ₀ x ∂P_X
              - ∫ x, rep.α₀ x * γ_target γ₀ x ∂P_X) := by
    let aγ : X → ℝ := fun x => α x * γ_target γ x
    let rγ : X → ℝ := fun x => rep.α₀ x * γ_target γ x
    let aγ₀ : X → ℝ := fun x => α x * γ_target γ₀ x
    let rγ₀ : X → ℝ := fun x => rep.α₀ x * γ_target γ₀ x
    have hpoint :
        (fun x => (α x - rep.α₀ x) * (γ_target γ x - γ_target γ₀ x))
          = fun x => (aγ x - rγ x) - (aγ₀ x - rγ₀ x) := by
      funext x
      simp [aγ, rγ, aγ₀, rγ₀]
      ring
    rw [hpoint]
    change ∫ x, ((aγ - rγ) - (aγ₀ - rγ₀)) x ∂P_X
        = (∫ x, aγ x ∂P_X - ∫ x, rγ x ∂P_X)
          - (∫ x, aγ₀ x ∂P_X - ∫ x, rγ₀ x ∂P_X)
    have haγ : Integrable aγ P_X := h_int_αγ_X
    have hrγ : Integrable rγ P_X := h_int_α₀γ
    have haγ₀ : Integrable aγ₀ P_X := h_int_αγ₀_X
    have hrγ₀ : Integrable rγ₀ P_X := h_int_α₀γ₀
    calc
      ∫ x, aγ x - rγ x - (aγ₀ x - rγ₀ x) ∂P_X
          = ∫ x, aγ x - rγ x ∂P_X
              - ∫ x, aγ₀ x - rγ₀ x ∂P_X := by
        exact integral_sub (haγ.sub hrγ) (haγ₀.sub hrγ₀)
      _ = (∫ x, aγ x ∂P_X - ∫ x, rγ x ∂P_X)
            - (∫ x, aγ₀ x ∂P_X - ∫ x, rγ₀ x ∂P_X) := by
        rw [integral_sub haγ hrγ]
        rw [integral_sub haγ₀ hrγ₀]
  rw [hscore, htruth, hmap_αγ, hmap_αγ₀, rep.representation γ, rep.representation γ₀]
  rw [hrhs]
  ring

end OrthogonalMoments
end Estimation
end Causalean
