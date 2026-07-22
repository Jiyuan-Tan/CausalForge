/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Discovery.LinearDisentanglement.Uniqueness

/-!
# Linear causal disentanglement: identifiability up to `S(𝒢)` and signed scaling

Flagship Theorem 2.

The headline result of Squires, Seigal, Bhate & Uhler, *Linear Causal Disentanglement
via Interventions* (ICML 2023), Theorem 2 (`thm:main_id_non_constructive`), in its
algebraic (matrix-level) form.

Under Assumption 1 (linear latent model, single-node interventions, linear
observations) and Assumption 2 (perfect interventions), with **one intervention per
latent node**, the latent graph and intervention targets are identifiable up to
`S(𝒢)`, the order-preserving relabelings, while the latent directions are identifiable
only up to nonzero signed diagonal scaling.  The signed diagonal is unavoidable because
the observable precision matrices are even in `H`.

The (⊆) inclusion is `disentanglement_uniqueness`; the (⊇) inclusion is
`sigma_solutions`.
-/

namespace Causalean.Discovery.LinearDisentanglement

open scoped Matrix

variable {d p K : ℕ}

/-- **Linear causal disentanglement identifiability (Theorem 2).**  With one
intervention per latent node (`hcov`) and non-degenerate interventions (`hNondeg`, the
paper's genericity/Assumption 1(b): each `Θ_k ≠ Θ_0`), two solutions producing the
same precision matrices in every context are related by a single order-preserving
relabeling `σ ∈ S(𝒢)` and nonzero signed diagonal scaling of latent directions; the
per-context structural relations carry a common row-sign diagonal `ν`. -/
theorem disentanglement_identifiability (S S' : Solution d p K)
    (hcov : Function.Bijective S.target) (hcov' : Function.Bijective S'.target)
    (hNondeg : ∀ k, S.Theta k ≠ S.Theta0)
    (hΘ0 : S.Theta0 = S'.Theta0) (hΘ : ∀ k, S.Theta k = S'.Theta k) :
    ∃ (σ : Equiv.Perm (Fin d)) (μ ν : Fin d → ℝ), S.InSG σ ∧
      (∀ i, μ i ≠ 0) ∧ (∀ i, ν i = 1 ∨ ν i = -1) ∧
      S'.H = Matrix.diagonal μ * permMat σ * S.H ∧
      S'.B0 * (Matrix.diagonal μ * permMat σ) =
        Matrix.diagonal ν * permMat σ * S.B0 ∧
      (∀ k, S'.Bint k * (Matrix.diagonal μ * permMat σ) =
        Matrix.diagonal ν * permMat σ * S.Bint k) ∧
      (∀ k, S'.target k = σ (S.target k)) :=
  disentanglement_uniqueness S S' hcov hcov' hNondeg hΘ0 hΘ

end Causalean.Discovery.LinearDisentanglement
