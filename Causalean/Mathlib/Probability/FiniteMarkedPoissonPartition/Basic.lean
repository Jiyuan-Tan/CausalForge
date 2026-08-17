import Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.IIDPoisson
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Finite Poisson samples

This file turns an independent Poisson count and infinite i.i.d. stream into a
genuine finite sequence.  It records the count law and the exact, unnormalised
fixed-count fibre law.  The latter is the convenient measure-theoretic form of
the statement that, conditional on the count, the observations are i.i.d.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

/-- The Poisson law with mean `r` gives the single count `n` exactly the Poisson
probability mass at `n`.

This bridge used to hold by definition, because the Poisson law was *defined* as
the measure attached to the Poisson mass function.  Mathlib now defines it
primitively, as a weighted sum of point masses, so the two descriptions have to
be reconciled explicitly.  Every result phrased against the mass function needs
this lemma to be transported to the Poisson law, so it is stated once here for
the whole `FiniteMarkedPoissonPartition` family rather than re-proved per file. -/
lemma poissonMeasure_singleton_eq_poissonPMF (r : ℝ≥0) (n : ℕ) :
    poissonMeasure r {n} = poissonPMF r n := by
  rw [poissonMeasure_singleton, ← poissonPMFReal_ofReal_eq_poissonPMF]
  rfl

variable {X : Type*} [MeasurableSpace X]

/-- A finite sequence is a length together with coordinates indexed by that
length. -/
abbrev FiniteSample (X : Type*) [MeasurableSpace X] := Σ n : ℕ, Fin n → X

/-- The number of observations in a finite sequence. -/
def FiniteSample.count (s : FiniteSample X) : ℕ := s.1

/-- The coordinates of a finite sequence at its dependent finite index type. -/
def FiniteSample.points (s : FiniteSample X) : Fin s.count → X := s.2

/-- Embed a fixed-length tuple into the space of all finite sequences. -/
def fixedSizeEmbed (n : ℕ) (x : Fin n → X) : FiniteSample X := ⟨n, x⟩

/-- Truncate a count-and-stream outcome to the prefix selected by its count. -/
def streamToFiniteSample (z : ℕ × (ℕ → X)) : FiniteSample X :=
  ⟨z.1, fun i => z.2 i⟩

/-- Embedding a fixed-size tuple into the finite-sequence space is measurable. -/
lemma measurable_fixedSizeEmbed (n : ℕ) : Measurable (fixedSizeEmbed (X := X) n) := by
  change Measurable (Sigma.mk n)
  apply Measurable.of_le_map
  exact iInf_le _ n

/-- Reading the count of a finite sequence is measurable. -/
lemma measurable_finiteSample_count : Measurable (FiniteSample.count : FiniteSample X → ℕ) := by
  apply measurable_to_countable'
  intro n
  change MeasurableSet ({s : FiniteSample X | s.1 = n})
  rw [MeasurableSpace.measurableSet_iInf]
  intro m
  change MeasurableSet ((Sigma.mk m) ⁻¹' {s : FiniteSample X | s.1 = n})
  by_cases hmn : m = n
  · subst m
    simp
  · convert MeasurableSet.empty using 1
    ext x
    simp [hmn]

/-- Truncating a count-and-stream outcome to its selected prefix is measurable. -/
lemma measurable_streamToFiniteSample :
    Measurable (streamToFiniteSample : (ℕ × (ℕ → X)) → FiniteSample X) := by
  intro s hs
  rw [MeasurableSpace.measurableSet_iInf] at hs
  rw [show streamToFiniteSample ⁻¹' s =
      ⋃ n : ℕ, {z : ℕ × (ℕ → X) | z.1 = n} ∩
        (fun z : ℕ × (ℕ → X) => fun i : Fin n => z.2 i) ⁻¹'
          (fixedSizeEmbed n ⁻¹' s) by
    ext z
    simp only [mem_preimage, mem_iUnion, mem_inter_iff, mem_setOf_eq]
    constructor
    · intro hz
      exact ⟨z.1, rfl, hz⟩
    · rintro ⟨n, hn, hz⟩
      subst n
      exact hz]
  apply MeasurableSet.iUnion
  intro n
  apply MeasurableSet.inter
  · exact measurable_fst (measurableSet_singleton n)
  · have hsn : MeasurableSet (fixedSizeEmbed n ⁻¹' s) := hs n
    exact hsn.preimage (by fun_prop)

/-- The finite Poisson sample law is obtained by drawing an independent scalar
Poisson count and i.i.d. stream and retaining exactly the selected prefix. -/
noncomputable def finitePoissonSampleLaw (P : Measure X) [IsProbabilityMeasure P]
    (lam : ℝ≥0) : Measure (FiniteSample X) :=
  Measure.map streamToFiniteSample (poissonIIDStreamLaw P lam)

/-- The finite Poisson sample law is a probability measure. -/
instance finitePoissonSampleLaw_isProbabilityMeasure (P : Measure X) [IsProbabilityMeasure P]
    (lam : ℝ≥0) : IsProbabilityMeasure (finitePoissonSampleLaw P lam) := by
  unfold finitePoissonSampleLaw
  exact Measure.isProbabilityMeasure_map measurable_streamToFiniteSample.aemeasurable

/-- The count of a finite Poisson sample has scalar Poisson law with the
requested mean. -/
lemma finitePoissonSampleLaw_map_count (P : Measure X) [IsProbabilityMeasure P]
    (lam : ℝ≥0) :
    Measure.map FiniteSample.count (finitePoissonSampleLaw P lam) = poissonMeasure lam := by
  unfold finitePoissonSampleLaw
  rw [Measure.map_map measurable_finiteSample_count measurable_streamToFiniteSample]
  change Measure.map Prod.fst (poissonIIDStreamLaw P lam) = poissonMeasure lam
  exact poissonIIDStreamLaw_map_count P lam

/-- On the fibre where the count equals `n`, the finite Poisson law is the
Poisson mass at `n` times the embedded `n`-fold product law. -/
lemma finitePoissonSampleLaw_restrict_count_eq (P : Measure X) [IsProbabilityMeasure P]
    (lam : ℝ≥0) (n : ℕ) :
    (finitePoissonSampleLaw P lam).restrict
        (FiniteSample.count ⁻¹' ({n} : Set ℕ)) =
      (poissonMeasure lam) ({n} : Set ℕ) •
        Measure.map (fixedSizeEmbed n) (Measure.pi (fun _ : Fin n => P)) := by
  unfold finitePoissonSampleLaw poissonIIDStreamLaw
  rw [Measure.restrict_map measurable_streamToFiniteSample
    (measurable_finiteSample_count (X := X) (measurableSet_singleton n))]
  have hpre : streamToFiniteSample ⁻¹'
      (FiniteSample.count ⁻¹' ({n} : Set ℕ)) =
      ({n} : Set ℕ) ×ˢ (Set.univ : Set (ℕ → X)) := by
    ext z
    simp [streamToFiniteSample, FiniteSample.count]
  rw [hpre, ← Measure.restrict_prod_eq_prod_univ, Measure.restrict_singleton,
    Measure.prod_smul_left, Measure.map_smul, Measure.dirac_prod,
    Measure.map_map measurable_streamToFiniteSample (by fun_prop)]
  change (poissonMeasure lam) {n} •
      Measure.map (fixedSizeEmbed n ∘ fun z : ℕ → X => fun i : Fin n => z i)
        (iidStreamLaw P) = _
  rw [← Measure.map_map (measurable_fixedSizeEmbed n) (by fun_prop),
    iidStreamLaw_map_finPrefix]

/-- A finite marked Poisson sample has i.i.d. observation-mark pairs, with
observation law `P`, independent mark law `R`, and Poisson mean `lam`. -/
noncomputable def finiteMarkedPoissonSampleLaw (P : Measure X) [IsProbabilityMeasure P]
    (R : Measure ℝ) [IsProbabilityMeasure R] (lam : ℝ≥0) :
    Measure (FiniteSample (X × ℝ)) :=
  finitePoissonSampleLaw (P.prod R) lam

/-- The finite marked Poisson sample law is a probability measure. -/
instance finiteMarkedPoissonSampleLaw_isProbabilityMeasure
    (P : Measure X) [IsProbabilityMeasure P]
    (R : Measure ℝ) [IsProbabilityMeasure R] (lam : ℝ≥0) :
    IsProbabilityMeasure (finiteMarkedPoissonSampleLaw P R lam) := by
  unfold finiteMarkedPoissonSampleLaw
  infer_instance

/-- The count of a finite marked Poisson sample has scalar Poisson law with
mean `lam`. -/
lemma finiteMarkedPoissonSampleLaw_map_count
    (P : Measure X) [IsProbabilityMeasure P]
    (R : Measure ℝ) [IsProbabilityMeasure R] (lam : ℝ≥0) :
    Measure.map FiniteSample.count (finiteMarkedPoissonSampleLaw P R lam) =
      poissonMeasure lam := by
  exact finitePoissonSampleLaw_map_count (P.prod R) lam

/-- Conditional on count `n` in the unnormalised-fibre sense, the marked
points are exactly `n` independent draws from `P.prod R`. -/
lemma finiteMarkedPoissonSampleLaw_restrict_count_eq
    (P : Measure X) [IsProbabilityMeasure P]
    (R : Measure ℝ) [IsProbabilityMeasure R] (lam : ℝ≥0) (n : ℕ) :
    (finiteMarkedPoissonSampleLaw P R lam).restrict
        (FiniteSample.count ⁻¹' ({n} : Set ℕ)) =
      (poissonMeasure lam) ({n} : Set ℕ) •
        Measure.map (fixedSizeEmbed n)
          (Measure.pi (fun _ : Fin n => P.prod R)) := by
  exact finitePoissonSampleLaw_restrict_count_eq (P.prod R) lam n

end Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
