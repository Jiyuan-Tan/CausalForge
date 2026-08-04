import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedVariables false

namespace CausalSmith.Stat.ReverseKLTwoCoverage

open scoped BigOperators

variable {d : ℕ} {𝒳 𝒜 : Type*}
  [Fintype 𝒳] [Fintype 𝒜] [DecidableEq 𝒳] [DecidableEq 𝒜]
  [MeasurableSpace 𝒳] [MeasurableSpace 𝒜]
  [MeasurableSingletonClass 𝒳] [MeasurableSingletonClass 𝒜]
  (E : CommonExperiment d 𝒳 𝒜)

noncomputable def loggingBlock (x : 𝒳) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => ∑ a, E.reference x a * (E.feature x a i * E.feature x a j)

noncomputable def candidateNormalizer (theta : Fin d → ℝ) (x : 𝒳) : ℝ :=
  ∑ a, E.reference x a * Real.exp (E.eta * ∑ i, E.feature x a i * theta i)

noncomputable def candidateWeight (theta : Fin d → ℝ) (x : 𝒳) (a : 𝒜) : ℝ :=
  Real.exp (E.eta * ∑ i, E.feature x a i * theta i) /
    candidateNormalizer E theta x

noncomputable def targetBlock (theta : Fin d → ℝ) (x : 𝒳) :
    Matrix (Fin d) (Fin d) ℝ :=
  fun i j => ∑ a, E.reference x a * candidateWeight E theta x a *
    (E.feature x a i * E.feature x a j)

/-- One branch of the finite fixed-experiment exponential/semidefinite
certificate, indexed by an arbitrary nonempty active context support. -/
def FixedExperimentFeasibilitySystem (C D : ℝ) : Prop :=
  ∃ (I : Finset 𝒳) (_hI : I.Nonempty) (x0 : I) (a0 : 𝒜)
    (theta : Fin d → ℝ) (rho : I → ℝ) (u : Fin d → ℝ),
    0 < E.reference x0.1 a0 ∧
    (∀ x a, (∑ i, E.feature x a i * theta i) ∈ Set.Icc (0 : ℝ) 1) ∧
    (∀ x : I, 0 < rho x) ∧ (∑ x : I, rho x = 1) ∧
    let B := ∑ x : I, rho x • loggingBlock E x.1
    let G := ∑ x : I, rho x • targetBlock E theta x.1
    Matrix.PosDef B ∧
    (∀ x : I, ∀ a, 0 < E.reference x.1 a →
      Real.exp (E.eta * ∑ i, E.feature x.1 a i * theta i) ≤
        C * candidateNormalizer E theta x.1) ∧
    Real.exp (E.eta * ∑ i, E.feature x0.1 a0 i * theta i) =
      C * candidateNormalizer E theta x0.1 ∧
    Matrix.PosSemidef (D • B - G) ∧
    (D • B - G).mulVec u = 0 ∧ ∑ i, (u i) ^ 2 = 1

/-- Branch labels are a nonempty active support and an active
reference-positive equality-attaining cell. -/
noncomputable def fixedExperimentBranchCount : ℕ :=
  (Finset.univ.filter fun b : Finset 𝒳 × (𝒳 × 𝒜) =>
    b.1.Nonempty ∧ b.2.1 ∈ b.1 ∧ 0 < E.reference b.2.1 b.2.2).card

end CausalSmith.Stat.ReverseKLTwoCoverage
