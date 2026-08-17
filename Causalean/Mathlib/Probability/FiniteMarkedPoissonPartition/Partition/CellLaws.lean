import Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.Partition.Splitting

/-!
# Marginal laws for partition cells

This file derives each cell's Poisson count law and its exact conditional
marked sample law from the joint finite-partition splitting theorem.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

variable {X : Type*} [MeasurableSpace X]
variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

namespace FiniteMeasurablePartition

/-- **Cell counts are Poisson.** Under the marked Poisson sample law with base probability
measure `P`, mark distribution `R`, and [nonnegative intensity `lam`](hyp:lam), [the number of
marked observations landing in cell `j` of the finite measurable partition `p`, viewed as a random
variable, is Poisson distributed with mean equal to `lam` times the `P`-mass of cell `j`](goal). -/
lemma map_restrictCell_count_finiteMarkedPoissonSampleLaw
    [StandardBorelSpace X]
    (p : FiniteMeasurablePartition X ι)
    (P : Measure X) [IsProbabilityMeasure P]
    (R : Measure ℝ) [IsProbabilityMeasure R] (lam : ℝ≥0) (j : ι) :
    Measure.map (fun s => (p.restrictCell j s).count)
        (finiteMarkedPoissonSampleLaw P R lam) =
      poissonMeasure (lam * p.cellMass P j) := by
  /-
  Prefer deriving this from the joint splitting theorem by mapping the `j`th
  coordinate and then the measurable count map; `Measure.pi_map_eval` gives
  the marginal of the finite product.  A separate thinning calculation should
  only be used if it materially shortens the proof.
  -/
  classical
  let μ := finiteMarkedPoissonSampleLaw P R lam
  let ν : ι → Measure (FiniteSample (X × ℝ)) := fun k =>
    finiteMarkedPoissonSampleLaw (p.cellObservationLaw P k) R
      (lam * p.cellMass P k)
  have hjoint : Measure.map p.restrictPartition μ = Measure.pi ν := by
    exact map_restrictPartition_finiteMarkedPoissonSampleLaw p P R lam
  have hcell : Measure.map (p.restrictCell j) μ = ν j := by
    calc
      Measure.map (p.restrictCell j) μ =
          Measure.map (Function.eval j)
            (Measure.map p.restrictPartition μ) := by
        rw [Measure.map_map (measurable_pi_apply j)
          p.measurable_restrictPartition]
        rfl
      _ = Measure.map (Function.eval j) (Measure.pi ν) := by rw [hjoint]
      _ = ν j := by
        rw [Measure.pi_map_eval]
        simp [ν]
  change Measure.map (FiniteSample.count ∘ p.restrictCell j) μ =
    poissonMeasure (lam * p.cellMass P j)
  rw [← Measure.map_map measurable_finiteSample_count
    (p.measurable_restrictCell j), hcell]
  exact finiteMarkedPoissonSampleLaw_map_count
    (p.cellObservationLaw P j) R (lam * p.cellMass P j)

/-- On its count-`n` fibre, the `j`th cell experiment is the Poisson mass at
`n` times `n` independent draws from the normalised restriction and mark law. -/
lemma cellLaw_restrict_count_eq
    (p : FiniteMeasurablePartition X ι)
    (P : Measure X) [IsProbabilityMeasure P]
    (R : Measure ℝ) [IsProbabilityMeasure R]
    (lam : ℝ≥0) (j : ι) (n : ℕ) :
    (finiteMarkedPoissonSampleLaw (p.cellObservationLaw P j) R
        (lam * p.cellMass P j)).restrict
          (FiniteSample.count ⁻¹' ({n} : Set ℕ)) =
      (poissonMeasure (lam * p.cellMass P j)) ({n} : Set ℕ) •
        Measure.map (fixedSizeEmbed n)
          (Measure.pi (fun _ : Fin n => (p.cellObservationLaw P j).prod R)) := by
  exact finiteMarkedPoissonSampleLaw_restrict_count_eq
    (p.cellObservationLaw P j) R (lam * p.cellMass P j) n

end FiniteMeasurablePartition

end Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
