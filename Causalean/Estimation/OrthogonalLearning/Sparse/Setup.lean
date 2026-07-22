/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Finite-dimensional sparse plug-in ERM: setup

Finite-dimensional specialization of orthogonal statistical learning to a target space
`Θ ⊆ EuclideanSpace ℝ (Fin p)`.  This file provides:

* `l1Norm ν T` — coordinate ℓ¹ norm restricted to a `Finset T : Finset (Fin p)`.
* `l1Full ν` — full ℓ¹ norm `∑ i, |ν i|`.
* `RestrictedCone S₀` — the cone `{ν : ‖ν_{S₀ᶜ}‖₁ ≤ 3 ‖ν_{S₀}‖₁}`.
* `SparsePluginERM` — predicate on a candidate `θhat` saying it is the
  exact minimiser of the penalised empirical risk
  `empRiskFn θ + λ * ‖θ‖₁`.

We use `EuclideanSpace ℝ (Fin p)` because it carries the canonical
`InnerProductSpace ℝ` and `‖·‖_2` instances; coordinate access `ν i`
works directly because `EuclideanSpace ℝ (Fin p)` reduces to
`PiLp 2 (fun _ : Fin p => ℝ)`, which `↑` reduces to a function type.

See `doc/basic_concepts/po/estimation/orthogonal_statistical_learning.tex`,
`def:est-osl-sparse-plugin-erm`.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.MeanInequalities

/-! # Sparse Plug-In Setup

This file develops the finite-dimensional sparse target geometry used by the
orthogonal statistical-learning plug-in analysis, including restricted and full
coordinate one-norms, the restricted cone around a support set, and exact
penalized empirical risk minimizers. It specializes the abstract target space to
Euclidean coordinates suitable for sparsity arguments.

The geometry is exposed through `l1Norm`, `l1Full`, `linftyDev`, and
`RestrictedCone`, with `l1Full_eq` and `l1Norm_supp_le_card_sqrt_mul_l2norm`
supplying the norm identities and bounds used in the sparse guarantee. The
estimator predicate is `SparsePluginERM`. -/

namespace Causalean
namespace Estimation
namespace OrthogonalLearning
namespace Sparse

open scoped BigOperators

variable {p : ℕ}

/-- Coordinate ℓ¹ norm of `ν` restricted to a subset `T : Finset (Fin p)`:
`l1Norm ν T = ∑ i ∈ T, |ν i|`. -/
noncomputable def l1Norm
    (ν : EuclideanSpace ℝ (Fin p)) (T : Finset (Fin p)) : ℝ :=
  ∑ i ∈ T, |ν i|

/-- Full coordinate ℓ¹ norm of `ν`: `∑ i, |ν i|`. -/
noncomputable def l1Full (ν : EuclideanSpace ℝ (Fin p)) : ℝ :=
  ∑ i : Fin p, |ν i|

/-- Coordinate ℓ∞ deviation of `ν`: `max_i |ν i|`.

Defined as `Finset.univ.sup'` over the (nonempty when `0 < p`) index set.
For the headline theorem we always have `0 < p` implicit in the support
hypothesis `S₀.card = s` with the relevant `s`; we expose the version
parameterised over a nonemptiness witness `hp` to keep statements general. -/
noncomputable def linftyDev {p : ℕ} (hp : (Finset.univ : Finset (Fin p)).Nonempty)
    (ν : EuclideanSpace ℝ (Fin p)) : ℝ :=
  (Finset.univ : Finset (Fin p)).sup' hp (fun i => |ν i|)

/-- The restricted cone `C(S₀) := {ν : ‖ν_{S₀ᶜ}‖₁ ≤ 3 ‖ν_{S₀}‖₁}`.
The complement is taken in `Finset.univ`. -/
noncomputable def RestrictedCone (S₀ : Finset (Fin p)) :
    Set (EuclideanSpace ℝ (Fin p)) :=
  {ν | l1Norm ν ((Finset.univ : Finset (Fin p)) \ S₀) ≤ 3 * l1Norm ν S₀}

/-- Membership in `RestrictedCone` unfolded. -/
lemma mem_RestrictedCone_iff
    (S₀ : Finset (Fin p)) (ν : EuclideanSpace ℝ (Fin p)) :
    ν ∈ RestrictedCone S₀ ↔
      l1Norm ν ((Finset.univ : Finset (Fin p)) \ S₀) ≤ 3 * l1Norm ν S₀ := by
  rfl

/-- `l1Full` decomposes along any subset and its complement in `Finset.univ`. -/
lemma l1Full_eq (ν : EuclideanSpace ℝ (Fin p)) (S₀ : Finset (Fin p)) :
    l1Full ν =
      l1Norm ν S₀ + l1Norm ν ((Finset.univ : Finset (Fin p)) \ S₀) := by
  unfold l1Full l1Norm
  rw [← Finset.sum_sdiff (Finset.subset_univ S₀) (f := fun i => |ν i|)]
  ring

/-- Cauchy–Schwarz on the support: the ℓ¹ norm restricted to `S₀` is bounded
by `√|S₀|` times the full ℓ² norm. -/
lemma l1Norm_supp_le_card_sqrt_mul_l2norm
    (ν : EuclideanSpace ℝ (Fin p)) (S₀ : Finset (Fin p)) :
    l1Norm ν S₀ ≤ Real.sqrt (S₀.card) * ‖ν‖ := by
  unfold l1Norm
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt S₀ (fun i => |ν i|) (fun _ => (1 : ℝ))
  have hone : (∑ i ∈ S₀, (1 : ℝ) ^ 2) = (S₀.card : ℝ) := by
    simp
  have hleft :
      (∑ i ∈ S₀, |ν i|) ≤
        Real.sqrt (∑ i ∈ S₀, (ν i) ^ 2) * Real.sqrt (S₀.card) := by
    calc
      (∑ i ∈ S₀, |ν i|)
          = ∑ i ∈ S₀, |ν i| * (1 : ℝ) := by simp
      _ ≤ Real.sqrt (∑ i ∈ S₀, |ν i| ^ 2) *
          Real.sqrt (∑ i ∈ S₀, (1 : ℝ) ^ 2) := hcs
      _ = Real.sqrt (∑ i ∈ S₀, (ν i) ^ 2) * Real.sqrt (S₀.card) := by
        simp [sq_abs]
  have hsum_nonneg : 0 ≤ ∑ i ∈ S₀, (ν i) ^ 2 := by
    exact Finset.sum_nonneg fun i _ => sq_nonneg (ν i)
  have hsum_le_norm_sq : ∑ i ∈ S₀, (ν i) ^ 2 ≤ ‖ν‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq]
    rw [Real.sq_sqrt]
    · simpa [Real.norm_eq_abs, sq_abs] using
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S₀)
          (fun x _ _ => sq_nonneg (ν x))
    · exact Finset.sum_nonneg fun i _ => sq_nonneg ‖ν i‖
  have hsqrt_le_norm : Real.sqrt (∑ i ∈ S₀, (ν i) ^ 2) ≤ ‖ν‖ := by
    have hnorm_sq_nonneg : 0 ≤ ‖ν‖ ^ 2 := sq_nonneg ‖ν‖
    calc
      Real.sqrt (∑ i ∈ S₀, (ν i) ^ 2) ≤ Real.sqrt (‖ν‖ ^ 2) :=
        Real.sqrt_le_sqrt hsum_le_norm_sq
      _ = ‖ν‖ := Real.sqrt_sq_eq_abs ‖ν‖ |>.trans (abs_of_nonneg (norm_nonneg ν))
  calc
    (∑ i ∈ S₀, |ν i|) ≤
        Real.sqrt (∑ i ∈ S₀, (ν i) ^ 2) * Real.sqrt (S₀.card) := hleft
    _ ≤ ‖ν‖ * Real.sqrt (S₀.card) := by
      exact mul_le_mul_of_nonneg_right hsqrt_le_norm (Real.sqrt_nonneg _)
    _ = Real.sqrt (S₀.card) * ‖ν‖ := by ring

/-- Sparse plug-in regularised ERM (predicate form).

Given an empirical risk `empRiskFn : EuclideanSpace ℝ (Fin p) → ℝ`
(plug-in nuisance already absorbed) and a penalty level `lambda ≥ 0`,
`θhat` is a *sparse plug-in regularised ERM* iff it minimises
`θ ↦ empRiskFn θ + lambda * ‖θ‖₁` over the entire ambient space. -/
structure SparsePluginERM
    (empRiskFn : EuclideanSpace ℝ (Fin p) → ℝ)
    (θhat : EuclideanSpace ℝ (Fin p))
    (lambda : ℝ) : Prop where
  lambda_nonneg : 0 ≤ lambda
  /-- `θhat` minimises the penalised objective over the ambient space. -/
  minimiser :
    ∀ θ' : EuclideanSpace ℝ (Fin p),
      empRiskFn θhat + lambda * l1Full θhat
        ≤ empRiskFn θ' + lambda * l1Full θ'

end Sparse
end OrthogonalLearning
end Estimation
end Causalean
