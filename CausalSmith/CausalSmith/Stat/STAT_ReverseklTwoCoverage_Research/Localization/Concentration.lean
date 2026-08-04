import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Localization.ConcentrationCore
import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Localization.BoundedLinearLocalization.Assembly

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedVariables false

namespace CausalSmith.Stat.ReverseKLTwoCoverage

open MeasureTheory
open ProbabilityTheory
open scoped BigOperators Topology

variable {d n : ℕ} {𝒳 𝒜 : Type*}
  [Fintype 𝒳] [Fintype 𝒜] [DecidableEq 𝒳] [DecidableEq 𝒜]
  [LinearOrder 𝒳] [LinearOrder 𝒜]
  [MeasurableSpace 𝒳] [MeasurableSpace 𝒜]
  [MeasurableSingletonClass 𝒳] [MeasurableSingletonClass 𝒜]

-- @node: lem:bounded-linear-localization
lemma bounded_linear_localization
    (E : CommonExperiment d 𝒳 𝒜) (P : BanditLaw E) (C D : ℝ)
    (hshell : ExactShell E P C D)
    (hZhao : ZhaoUniformSquareComparison (𝒳 := 𝒳) (𝒜 := 𝒜))
    (hn : 0 < n) :
    ∀ c0 : ℝ, 64 ≤ c0 →
      ∃ event : Set (LoggedSample n 𝒳 𝒜),
        MeasurableSet event ∧
        (productLaw E P n).real event ≥ 1 - failureProbability n hn / 2 ∧
        ∀ sample ∈ event,
          linearReward P ∈ confidencePolytope E c0 sample ∧
          ∀ f ∈ confidencePolytope E c0 sample,
            ∑ x, contextMass P x * ∑ a, E.reference x a *
                (f x a - linearReward P x a) ^ 2 ≤
              (4 * c0 + 291) *
                (d * Real.log (Real.exp 1 * n) + Real.log (2 * (n : ℝ) ^ 2)) / n := by
  exact
    BoundedLinearLocalizationExactWrapper.bounded_linear_localization_exact_wrapper
      E P C D hshell hZhao hn

-- @node: lem:measurable-maximum-theorem
/-- Cited measurable maximum theorem: Weigand, Roith, and Burger (2026),
Appendix F, Theorem F.3 (`WeigandRoithBurger2026MeasurableMaximum`). -/
def MeasurableMaximumTheorem : Prop :=
  ∀ {Ω K : Type*} [MeasurableSpace Ω] [TopologicalSpace K]
    [T2Space K] [TopologicalSpace.MetrizableSpace K] [SecondCountableTopology K]
    [MeasurableSpace K] [BorelSpace K],
    ∀ (Gamma : Ω → Set K) (u : Ω → K → ℝ),
      (∀ V, IsOpen V → MeasurableSet {ω | (Gamma ω ∩ V).Nonempty}) →
      (∀ ω, (Gamma ω).Nonempty ∧ IsCompact (Gamma ω)) →
      (∀ k, Measurable fun ω => u ω k) →
      (∀ ω, Continuous fun k => u ω k) →
      let value := fun ω => sSup (u ω '' Gamma ω)
      let argmax := fun ω => {k | k ∈ Gamma ω ∧ u ω k = value ω}
      Measurable value ∧
      (∀ ω, (argmax ω).Nonempty ∧ IsCompact (argmax ω)) ∧
      (∀ V, IsOpen V → MeasurableSet {ω | (argmax ω ∩ V).Nonempty}) ∧
      ∃ selector : Ω → K, Measurable selector ∧
        ∀ ω, selector ω ∈ argmax ω

end CausalSmith.Stat.ReverseKLTwoCoverage
