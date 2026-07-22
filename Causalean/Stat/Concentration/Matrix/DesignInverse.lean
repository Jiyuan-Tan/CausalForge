/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Stat.Concentration.Matrix.InversePerturbation
import Causalean.Stat.Concentration.Matrix.InverseUnionBound

/-!
# Matrix-inverse concentration for the random design moment matrix

Assembles deterministic inverse perturbation and iid union bounds into concentration for random
design moment-matrix inverses.

This module assembles the two halves of the interior local-polynomial leverage rate
`(M⁻¹)₀₀ = O(1/(Nh))` for the **random** design:

* `Perturbation.designInv00_perturb` — the deterministic transport: if the empirical moment
  matrix `M` is entrywise within `η` of an invertible population matrix `S` whose inverse has
  row sums bounded by `c`, with `c·(p+1)·η ≤ 1/2`, then `M` is invertible and
  `|(M⁻¹)₀₀ − (S⁻¹)₀₀| ≤ 2 c² (p+1) η`.
* `UnionBound.iid_sum_union_bound` — the probabilistic half: each entry `M_{jk}(ω) = ∑ᵢ g_{jk}(ωᵢ)`
  is an iid sum, so a union bound over the `(p+1)²` entries makes the entrywise-`η` good event
  have probability `≥ 1 − ∑ Var/η²`.

The capstone `designMatrix_inv_concentration` combines them: the analytic failure event
(`M` singular, or `(M⁻¹)₀₀` far from `(S⁻¹)₀₀`) has probability at most the union-bound tail.
Here the population matrix `S = 𝔼[M]` is supplied with its invertibility (`IsUnit S.det`, e.g. from
`designMatrix_posDef`) and an inverse-row-sum bound `c`; turning those into the explicit `Θ(Nh)`
density constants is the remaining kernel-change-of-variables step.
-/

namespace Causalean.Stat.Concentration

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

/-- **Matrix-inverse concentration of the random design moment matrix.** Let `g j k : Ω → ℝ` be
the per-entry design statistics, so the empirical moment matrix is
`M(ω) = fun j k => ∑ᵢ g j k (ωᵢ)` and its expectation is the population matrix
`S = fun j k => N·𝔼[g j k]`. If `S` is invertible with inverse row sums bounded by `c ≥ 0` and the
scale satisfies `c·(p+1)·η ≤ 1/2`, then the event on which `M` fails to be invertible *or* its
leverage `(M⁻¹)₀₀` is farther than `2 c² (p+1) η` from `(S⁻¹)₀₀` has probability at most the
union-bound tail `∑_{j,k} N·Var[g j k]/η²`. This is the high-probability statement that the
random design is non-degenerate with `O(1/(Nh))` leverage on the good event. -/
theorem designMatrix_inv_concentration {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : Fin (p + 1) → Fin (p + 1) → Ω → ℝ)
    (hg : ∀ j k, MemLp (g j k) 2 μ)
    (S : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ)
    (hSpop : ∀ j k, S j k = N * ∫ x, g j k x ∂μ)
    (hS : IsUnit S.det) {η c : ℝ} (hc : 0 ≤ c) (hη : 0 < η)
    (hSrow : ∀ i, (∑ j, |S⁻¹ i j|) ≤ c)
    (hsmall : c * ((p + 1 : ℕ) * η) ≤ 1 / 2) :
    (Measure.pi (fun _ : Fin N => μ))
        {ω : Fin N → Ω |
          ¬ (IsUnit (Matrix.of (fun j k => ∑ i, g j k (ω i))).det ∧
              |(Matrix.of (fun j k => ∑ i, g j k (ω i)))⁻¹ 0 0 - S⁻¹ 0 0|
                ≤ 2 * c ^ 2 * ((p + 1 : ℕ) * η))}
      ≤ ∑ a : Fin (p + 1) × Fin (p + 1),
          ENNReal.ofReal (N * Var[g a.1 a.2; μ] / η ^ 2) := by
  let Dev : Set (Fin N → Ω) :=
    {ω : Fin N → Ω | ∃ a : Fin (p + 1) × Fin (p + 1),
      η ≤ |(∑ i, g a.1 a.2 (ω i)) - N * ∫ x, g a.1 a.2 x ∂μ|}
  have hbad_le_dev :
      (Measure.pi (fun _ : Fin N => μ))
          {ω : Fin N → Ω |
            ¬ (IsUnit (Matrix.of (fun j k => ∑ i, g j k (ω i))).det ∧
                |(Matrix.of (fun j k => ∑ i, g j k (ω i)))⁻¹ 0 0 - S⁻¹ 0 0|
                  ≤ 2 * c ^ 2 * ((p + 1 : ℕ) * η))}
        ≤ (Measure.pi (fun _ : Fin N => μ)) Dev := by
    apply measure_mono
    intro ω hω
    by_contra hωDev
    have hωDev' : ∀ a : Fin (p + 1) × Fin (p + 1),
        |(∑ i, g a.1 a.2 (ω i)) - N * ∫ x, g a.1 a.2 x ∂μ| < η := by
      simpa [Dev, not_exists, not_le] using hωDev
    have hclose :
        ∀ j k,
          |(Matrix.of (fun j k => ∑ i, g j k (ω i))) j k - S j k| ≤ η := by
      intro j k
      rw [Matrix.of_apply, hSpop j k]
      exact le_of_lt (hωDev' (j, k))
    have hgood :=
      designInv00_perturb S (Matrix.of (fun j k => ∑ i, g j k (ω i)))
        hS hc hη.le hSrow hclose hsmall
    exact hω hgood
  refine le_trans hbad_le_dev ?_
  simpa [Dev] using iid_sum_union_bound μ
      (fun a : Fin (p + 1) × Fin (p + 1) => g a.1 a.2)
      (fun a => hg a.1 a.2) hη

end Causalean.Stat.Concentration
