/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Deterministic sparse plug-in ERM guarantee

Headline finite-dimensional sparse plug-in theorem: under restricted strong
convexity at the truth, convex empirical risk, the support hypothesis
`|S₀| = s`, the first-order condition `∇L(θ₀, g₀) = 0`, and a penalty level
dominating twice the ℓ∞ deviation of the empirical gradient, every sparse
plug-in regularised ERM `θhat` satisfies

* `θhat - θ₀ ∈ RestrictedCone S₀`,
* `‖θhat - θ₀‖₂ ≤ 12 · lambda · √s / σn`.

See `doc/basic_concepts/po/estimation/orthogonal_statistical_learning.tex`,
`thm:est-osl-sparse-plugin-guarantee`.
-/

import Causalean.Estimation.OrthogonalLearning.Sparse.Setup
import Causalean.Estimation.OrthogonalLearning.Sparse.RSC
import Mathlib.Analysis.Convex.Function
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.OuterMeasure.Defs

/-! # Sparse Plug-In Guarantee

This file proves the deterministic sparse plug-in guarantee for penalized
empirical risk minimization under restricted strong convexity, support
sparsity, a first-order condition at the target, and a gradient-deviation
bound. It also states the high-probability interface that will turn a tail
bound for the gradient deviation into the same sparse estimation guarantee.

The deterministic theorem `sparse_plugin_guarantee` proves membership of
`θhat - θ₀` in `RestrictedCone S₀` and the displayed `12 * lambda * sqrt s / σn`
error bound. The predicate `LinftyDevTailBound` and theorem
`sparse_plugin_guarantee_highProb` lift this deterministic guarantee to a
high-probability event. -/

namespace Causalean
namespace Estimation
namespace OrthogonalLearning
namespace Sparse

open scoped BigOperators RealInnerProductSpace
open MeasureTheory

/-- Deterministic sparse plug-in ERM guarantee.

* `empRiskFn`     — empirical risk with the plug-in nuisance absorbed.
* `popGrad`       — population gradient at the truth, `∇L(θ₀, g₀)`.
* `gradEmp`       — empirical gradient as a function of the parameter.
* `θ₀`, `θhat`    — truth and estimator.
* `S₀`, `s`       — support of `θ₀` and its cardinality.
* `h_supp`        — `θ₀` is supported on `S₀`.
* `h_conv`        — `empRiskFn` is convex on the ambient space.
* `σn`, `h_RSC`   — `σn`-RSC of `empRiskFn` at `θ₀` over `S₀`.
* `h_subgrad`     — subgradient inequality at `θ₀`; this is the basic
                    inequality input that would follow from threading
                    `gradEmp θ₀ ∈ ∂empRiskFn(θ₀)` explicitly.
* `lambda`        — penalty level.
* `h_lambda_lb`   — `lambda ≥ 2 · ‖∇emp θ₀ - popGrad‖_∞` (using `linftyDev`
                   on the nonempty index set of `EuclideanSpace ℝ (Fin p)`).
* `h_FOC_pop`     — first-order condition at the truth, `popGrad = 0`.
* `h_pluginERM`   — `θhat` is a sparse plug-in regularised ERM.

Conclusion: `θhat - θ₀ ∈ RestrictedCone S₀` and the ℓ² bound. -/
theorem sparse_plugin_guarantee
    {p : ℕ}
    (empRiskFn : EuclideanSpace ℝ (Fin p) → ℝ)
    (popGrad : EuclideanSpace ℝ (Fin p))
    (gradEmp : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p))
    (θ₀ θhat : EuclideanSpace ℝ (Fin p))
    (S₀ : Finset (Fin p))
    (s : ℕ) (hs : S₀.card = s)
    (h_supp : ∀ i ∉ S₀, θ₀ i = 0)
    (_h_conv : ConvexOn ℝ Set.univ empRiskFn)
    (σn : ℝ) (hσn : 0 < σn)
    (h_RSC : RestrictedStrongConvexity empRiskFn gradEmp θ₀ S₀ σn)
    (h_subgrad : ∀ θ : EuclideanSpace ℝ (Fin p),
      empRiskFn θ - empRiskFn θ₀ ≥ inner ℝ (gradEmp θ₀) (θ - θ₀))
    (lambda : ℝ)
    (h_lambda_pos : 0 < lambda)
    (hp : (Finset.univ : Finset (Fin p)).Nonempty)
    (h_lambda_lb :
      lambda ≥ 2 * linftyDev hp (gradEmp θ₀ - popGrad))
    (h_FOC_pop : popGrad = 0)
    (h_pluginERM : SparsePluginERM empRiskFn θhat lambda) :
    θhat - θ₀ ∈ RestrictedCone S₀ ∧
      ‖θhat - θ₀‖ ≤ 12 * lambda * Real.sqrt s / σn := by
  classical
  let ν : EuclideanSpace ℝ (Fin p) := θhat - θ₀
  let δ : EuclideanSpace ℝ (Fin p) := gradEmp θ₀ - popGrad
  let C : Finset (Fin p) := (Finset.univ : Finset (Fin p)) \ S₀
  let A : ℝ := l1Norm ν S₀
  let B : ℝ := l1Norm ν C
  let L : ℝ := l1Full ν
  let D : ℝ := l1Full θ₀ - l1Full θhat
  let G : ℝ := inner ℝ δ ν
  let M : ℝ := linftyDev hp δ
  have hlambda_nonneg : 0 ≤ lambda := h_pluginERM.lambda_nonneg
  have hC : C = (Finset.univ : Finset (Fin p)) \ S₀ := rfl
  have hL_eq : L = A + B := by
    dsimp [L, A, B, C]
    exact l1Full_eq ν S₀
  have hA_nonneg : 0 ≤ A := by
    simp [A, l1Norm, Finset.sum_nonneg]
  have hB_nonneg : 0 ≤ B := by
    simp [B, l1Norm, Finset.sum_nonneg]
  have hL_nonneg : 0 ≤ L := by
    simp [L, l1Full, Finset.sum_nonneg]

  have hM_le : M ≤ lambda / 2 := by
    linarith [h_lambda_lb]
  have hHolder_M : |G| ≤ M * L := by
    have hcoord : ∀ i : Fin p, |δ i| ≤ M := by
      intro i
      exact Finset.le_sup' (fun j => |δ j|) (Finset.mem_univ i)
    have hinner_sum : inner ℝ δ ν = ∑ i : Fin p, δ i * ν i := by
      rw [PiLp.inner_apply]
      apply Finset.sum_congr rfl
      intro i _
      change ν i * δ i = δ i * ν i
      ring
    calc
      |G| = |inner ℝ δ ν| := by rfl
      _ = |∑ i : Fin p, δ i * ν i| := by rw [hinner_sum]
      _ ≤ ∑ i : Fin p, |δ i * ν i| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i : Fin p, |δ i| * |ν i| := by simp [abs_mul]
      _ ≤ ∑ i : Fin p, M * |ν i| := by
        exact Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_right (hcoord i) (abs_nonneg (ν i))
      _ = M * L := by
        simp [L, l1Full, Finset.mul_sum]
  have hHolder : |G| ≤ (lambda / 2) * L := by
    exact le_trans hHolder_M (mul_le_mul_of_nonneg_right hM_le hL_nonneg)
  have hnegG_le : -G ≤ (lambda / 2) * L := by
    exact le_trans (neg_le_abs G) hHolder

  have hemp_le_D : empRiskFn θhat - empRiskFn θ₀ ≤ lambda * D := by
    have hopt := h_pluginERM.minimiser θ₀
    dsimp [D]
    linarith
  have hsub_le_emp : G ≤ empRiskFn θhat - empRiskFn θ₀ := by
    simpa [G, δ, ν, h_FOC_pop] using (h_subgrad θhat)
  have hG_le_lambdaD : G ≤ lambda * D := le_trans hsub_le_emp hemp_le_D

  have htheta0_full : l1Full θ₀ = l1Norm θ₀ S₀ := by
    rw [l1Full_eq θ₀ S₀]
    have hzero : l1Norm θ₀ ((Finset.univ : Finset (Fin p)) \ S₀) = 0 := by
      unfold l1Norm
      exact Finset.sum_eq_zero fun i hi => by
        have hi_not : i ∉ S₀ := (Finset.mem_sdiff.mp hi).2
        simp [h_supp i hi_not]
    simp [hzero]
  have hcomp_hat : l1Norm θhat C = B := by
    unfold l1Norm
    apply Finset.sum_congr rfl
    intro i hi
    have hi_univ_sdiff : i ∈ (Finset.univ : Finset (Fin p)) \ S₀ := by
      simpa [C] using hi
    have hi_not : i ∉ S₀ := (Finset.mem_sdiff.mp hi_univ_sdiff).2
    simp [ν, h_supp i hi_not]
  have hreverse_sum : l1Norm θ₀ S₀ - A ≤ l1Norm θhat S₀ := by
    unfold l1Norm
    change (∑ i ∈ S₀, |θ₀ i|) - (∑ i ∈ S₀, |ν i|) ≤
      ∑ i ∈ S₀, |θhat i|
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum fun i hi => by
      have htri := abs_sub_le (θ₀ i) (θhat i) 0
      have hdiff : |θ₀ i - θhat i| = |ν i| := by
        have hcoord : θ₀ i - θhat i = -(ν i) := by
          simp [ν]
        rw [hcoord, abs_neg]
      have hmain : |θ₀ i| ≤ |ν i| + |θhat i| := by
        simpa [sub_zero, hdiff, add_comm] using htri
      linarith
  have hD_le : D ≤ A - B := by
    have hhat_full := l1Full_eq θhat S₀
    dsimp [D]
    rw [htheta0_full, hhat_full]
    rw [show l1Norm θhat ((Finset.univ : Finset (Fin p)) \ S₀) = B by
      simpa [C] using hcomp_hat]
    linarith

  have hG_le_AB : G ≤ lambda * (A - B) := by
    exact le_trans hG_le_lambdaD (mul_le_mul_of_nonneg_left hD_le hlambda_nonneg)
  have hcone_alg : B ≤ 3 * A := by
    have hpre : -lambda * (A - B) ≤ (lambda / 2) * L := by
      linarith
    rw [hL_eq] at hpre
    nlinarith [h_lambda_pos]
  have hcone : ν ∈ RestrictedCone S₀ := by
    simpa [ν, A, B, C, RestrictedCone] using hcone_alg

  have hRSC_le :
      (σn / 2) * ‖ν‖ ^ 2 ≤
        empRiskFn θhat - empRiskFn θ₀ - G := by
    have hR := h_RSC ν hcone
    simpa [ν, G, δ, h_FOC_pop, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      using hR
  have hemp_le_AB : empRiskFn θhat - empRiskFn θ₀ ≤ lambda * (A - B) := by
    exact le_trans hemp_le_D (mul_le_mul_of_nonneg_left hD_le hlambda_nonneg)
  have hquad_A : (σn / 2) * ‖ν‖ ^ 2 ≤ (3 * lambda / 2) * A := by
    have hfirst :
        empRiskFn θhat - empRiskFn θ₀ - G ≤
          lambda * (A - B) + (lambda / 2) * L := by
      linarith
    have hsecond :
        lambda * (A - B) + (lambda / 2) * L ≤ (3 * lambda / 2) * A := by
      rw [hL_eq]
      nlinarith
    exact le_trans hRSC_le (le_trans hfirst hsecond)
  have hA_le : A ≤ Real.sqrt s * ‖ν‖ := by
    have h := l1Norm_supp_le_card_sqrt_mul_l2norm ν S₀
    simpa [A, hs] using h
  have hquad :
      (σn / 2) * ‖ν‖ ^ 2 ≤
        (3 * lambda / 2) * (Real.sqrt s * ‖ν‖) := by
    exact le_trans hquad_A
      (mul_le_mul_of_nonneg_left hA_le (by nlinarith [hlambda_nonneg]))
  have hbound_tight : ‖ν‖ ≤ 3 * lambda * Real.sqrt s / σn := by
    by_cases hzero : ‖ν‖ = 0
    · rw [hzero]
      exact div_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) hlambda_nonneg) (Real.sqrt_nonneg s))
        (le_of_lt hσn)
    · have hnorm_pos : 0 < ‖ν‖ := lt_of_le_of_ne (norm_nonneg ν) (Ne.symm hzero)
      have hσmul : σn * ‖ν‖ ≤ 3 * lambda * Real.sqrt s := by
        nlinarith [hquad, hnorm_pos]
      rw [le_div_iff₀ hσn]
      simpa [mul_comm] using hσmul
  have hbound : ‖ν‖ ≤ 12 * lambda * Real.sqrt s / σn := by
    rw [le_div_iff₀ hσn] at hbound_tight ⊢
    nlinarith [hbound_tight, hlambda_nonneg, Real.sqrt_nonneg s]
  constructor
  · simpa [ν] using hcone
  · simpa [ν] using hbound

/-! ## High-probability sparse plug-in guarantee

The deterministic theorem `sparse_plugin_guarantee` consumes the
penalty-domination hypothesis
`lambda ≥ 2 · linftyDev hp (gradEmp θ₀ − popGrad)` as a deterministic
inequality.  In practice that hypothesis is met only on a high-probability
event under fold-B concentration of the empirical gradient.

`LinftyDevTailBound` is the high-probability event predicate.  A concrete
gradient-deviation concentration theorem (a sibling discharge to
`OrthogonalLearning.LocalEmpProcess.Rademacher`'s `LocalEmpProcessModulus`) is
left to a follow-up; here we expose the wrapper that lifts the deterministic
guarantee to the high-probability statement once such a tail bound is supplied.
-/

/-- High-probability ℓ∞ tail bound for an `Ω`-indexed deviation field
`dev : Ω → EuclideanSpace ℝ (Fin p)`: there is a measurable event `E ⊆ Ω`
of `μ`-mass at least `1 - δ` on which `linftyDev hp (dev ω) ≤ ρ`.

This is the gradient-deviation analogue of
`Causalean.Estimation.OrthogonalLearning.LocalEmpProcessModulus`. Concrete
McDiarmid, sub-Gaussian, or fold-B concentration assumptions can discharge this
tail bound; here it is a hypothesis. -/
def LinftyDevTailBound
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    {p : ℕ} (hp : (Finset.univ : Finset (Fin p)).Nonempty)
    (dev : Ω → EuclideanSpace ℝ (Fin p))
    (ρ δ : ℝ) : Prop :=
  ∃ E : Set Ω, MeasurableSet E ∧ μ E ≥ 1 - ENNReal.ofReal δ ∧
    ∀ ω ∈ E, linftyDev hp (dev ω) ≤ ρ

/-- **High-probability sparse plug-in ERM guarantee.**

Lift `sparse_plugin_guarantee` to a *probability-1−δ* statement once the
empirical gradient `gradEmp ω θ₀ − popGrad` satisfies an ℓ∞ tail bound `≤ ρ`
with `lambda ≥ 2 ρ` (the deterministic version's hypothesis is then
automatically met on the tail event).

The conclusion is: with `μ`-probability at least `1 − δ`,

* `θhat ω − θ₀ ∈ RestrictedCone S₀`,
* `‖θhat ω − θ₀‖ ≤ 12 · lambda · √s / σn`. -/
theorem sparse_plugin_guarantee_highProb
    {p : ℕ}
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (empRiskFn : Ω → EuclideanSpace ℝ (Fin p) → ℝ)
    (popGrad : EuclideanSpace ℝ (Fin p))
    (gradEmp : Ω → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p))
    (θ₀ : EuclideanSpace ℝ (Fin p))
    (θhat : Ω → EuclideanSpace ℝ (Fin p))
    (S₀ : Finset (Fin p))
    (s : ℕ) (hs : S₀.card = s)
    (h_supp : ∀ i ∉ S₀, θ₀ i = 0)
    (h_conv : ∀ ω, ConvexOn ℝ Set.univ (empRiskFn ω))
    (σn : ℝ) (hσn : 0 < σn)
    (h_RSC : ∀ ω, RestrictedStrongConvexity (empRiskFn ω) (gradEmp ω) θ₀ S₀ σn)
    (h_subgrad : ∀ ω, ∀ θ : EuclideanSpace ℝ (Fin p),
      empRiskFn ω θ - empRiskFn ω θ₀ ≥ inner ℝ (gradEmp ω θ₀) (θ - θ₀))
    (lambda : ℝ) (h_lambda_pos : 0 < lambda)
    (hp : (Finset.univ : Finset (Fin p)).Nonempty)
    (h_FOC_pop : popGrad = 0)
    (h_pluginERM : ∀ ω, SparsePluginERM (empRiskFn ω) (θhat ω) lambda)
    (ρ : ℝ) (δ : ℝ)
    (hLambdaTail :
      LinftyDevTailBound μ hp (fun ω => gradEmp ω θ₀ - popGrad) ρ δ)
    (h_lambda_dom : lambda ≥ 2 * ρ) :
    ∃ E : Set Ω, MeasurableSet E ∧ μ E ≥ 1 - ENNReal.ofReal δ ∧
      ∀ ω ∈ E,
        θhat ω - θ₀ ∈ RestrictedCone S₀ ∧
        ‖θhat ω - θ₀‖ ≤ 12 * lambda * Real.sqrt s / σn := by
  rcases hLambdaTail with ⟨E, hE_meas, hE_mass, hE_dev_bound⟩
  refine ⟨E, hE_meas, hE_mass, ?_⟩
  intro ω hω
  have h_lambda_lb :
      lambda ≥ 2 * linftyDev hp (gradEmp ω θ₀ - popGrad) := by
    nlinarith [h_lambda_dom, hE_dev_bound ω hω]
  exact sparse_plugin_guarantee (empRiskFn ω) popGrad (gradEmp ω) θ₀ (θhat ω)
    S₀ s hs h_supp (h_conv ω) σn hσn (h_RSC ω) (h_subgrad ω)
    lambda h_lambda_pos hp h_lambda_lb h_FOC_pop (h_pluginERM ω)

end Sparse
end OrthogonalLearning
end Estimation
end Causalean
