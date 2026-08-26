import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.LowerTransfer
import Causalean.Mathlib.InformationTheory.CommonStatisticBernoulli

/-!
# The observed Bernoulli contraction kernel

This file constructs the hypothesis-independent one-record channel used by the
radial converse and proves that it is a Markov kernel throughout the declared
radius range.
-/

namespace CausalSmith.Stat.DiscreteAteHeterogeneityFrontier

open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory

-- @node: bernoulliContractionSuccess
/-- The success probability of the paper's binary contraction channel. -/
noncomputable def bernoulliContractionSuccess (sigma : ℝ) (b : Bool) : ℝ :=
  1 / 2 + sigma / 2 * ((if b then 1 else 0) - 1 / 2)

-- @node: bernoulliContractionSuccess_mem_unitInterval
/-- If [the heterogeneity radius is nonnegative](hyp:hs0) and [the heterogeneity radius is at most
  two](hyp:hs2), [for a radius parameter between zero and two, both conditional success
  probabilities are valid Bernoulli parameters](goal). -/
lemma bernoulliContractionSuccess_mem_unitInterval {sigma : ℝ}
    (hs0 : 0 ≤ sigma) (hs2 : sigma ≤ 2) (b : Bool) :
    bernoulliContractionSuccess sigma b ∈ Icc (0 : ℝ) 1 := by
  cases b <;> simp [bernoulliContractionSuccess] <;> constructor <;> linarith

-- @node: bernoulliContractionObservedKernel
/-- The one-record radial channel preserves the padded cell and treatment,
draws the contracted Bernoulli response, and sends its atoms to `±M/2`. -/
noncomputable def bernoulliContractionObservedKernel {m d : ℕ}
    (pad : Fin m → Fin d) (M sigma : ℝ) :
    Kernel (CausalSmith.Stat.DiscreteAteMinimaxLoggap.Obs m) (Obs d) where
  toFun z := Measure.map
    (fun r : ℝ => (⟨pad z.1, z.2.1, M * (r - 1 / 2)⟩ : Obs d))
    (Causalean.Mathlib.Probability.bernoulliLaw
      (bernoulliContractionSuccess sigma z.2.2))
  measurable' := by
    exact measurable_of_finite
      (fun z : CausalSmith.Stat.DiscreteAteMinimaxLoggap.Obs m => Measure.map
        (fun r : ℝ => (⟨pad z.1, z.2.1, M * (r - 1 / 2)⟩ : Obs d))
        (Causalean.Mathlib.Probability.bernoulliLaw
          (bernoulliContractionSuccess sigma z.2.2)))

-- @node: bernoulliContractionObservedKernel_isMarkovKernel
/-- If [the heterogeneity radius is nonnegative](hyp:hs0) and [the heterogeneity radius is at most
  two](hyp:hs2), [the observed Bernoulli contraction is a Markov kernel for every declared radius
  `0 ≤ sigma ≤ 2`](goal). -/
lemma bernoulliContractionObservedKernel_isMarkovKernel {m d : ℕ}
    (pad : Fin m → Fin d) (M sigma : ℝ)
    (hs0 : 0 ≤ sigma) (hs2 : sigma ≤ 2) :
    IsMarkovKernel (bernoulliContractionObservedKernel pad M sigma) := by
  constructor
  intro z
  have hp := bernoulliContractionSuccess_mem_unitInterval hs0 hs2 z.2.2
  letI : IsProbabilityMeasure
      (Causalean.Mathlib.Probability.bernoulliLaw
        (bernoulliContractionSuccess sigma z.2.2)) :=
    Causalean.Mathlib.Probability.bernoulliLaw_isProbabilityMeasure hp.1 hp.2
  change IsProbabilityMeasure (Measure.map
    (fun r : ℝ => (⟨pad z.1, z.2.1, M * (r - 1 / 2)⟩ : Obs d))
    (Causalean.Mathlib.Probability.bernoulliLaw
      (bernoulliContractionSuccess sigma z.2.2)))
  have hmeas : Measurable
      (fun r : ℝ => (⟨pad z.1, z.2.1, M * (r - 1 / 2)⟩ : Obs d)) := by
    rw [measurable_comap_iff]
    change Measurable (fun r : ℝ => (pad z.1, z.2.1, M * (r - 1 / 2)))
    fun_prop
  exact Measure.isProbabilityMeasure_map hmeas.aemeasurable

end CausalSmith.Stat.DiscreteAteHeterogeneityFrontier
