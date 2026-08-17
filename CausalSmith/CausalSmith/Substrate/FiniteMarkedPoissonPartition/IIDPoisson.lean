import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.ProductMeasure

/-!
# I.i.d. streams paired with an independent Poisson count

This file provides the paper-neutral count-and-stream probability space used
as the elementary input to finite marked Poisson constructions. An infinite
i.i.d. stream has exact finite product marginals, and pairing it with an
independent scalar Poisson count preserves both the count and prefix laws.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace CausalSmith.Substrate.FiniteMarkedPoissonPartition

variable {X : Type*} [MeasurableSpace X]

/-- The law of an infinite i.i.d. stream with one-coordinate law `P`. -/
noncomputable def iidStreamLaw (P : Measure X) [IsProbabilityMeasure P] :
    Measure (ℕ → X) :=
  Measure.infinitePi (fun _ : ℕ => P)

/-- The infinite i.i.d. stream law is a probability measure. -/
instance iidStreamLaw_isProbabilityMeasure (P : Measure X) [IsProbabilityMeasure P] :
    IsProbabilityMeasure (iidStreamLaw P) := by
  unfold iidStreamLaw
  infer_instance

/-- Every finite prefix of an infinite i.i.d. stream has the corresponding
finite product law. -/
lemma iidStreamLaw_map_finPrefix (P : Measure X) [IsProbabilityMeasure P] (n : ℕ) :
    Measure.map (fun z : ℕ → X => fun i : Fin n => z i) (iidStreamLaw P) =
      Measure.pi (fun _ : Fin n => P) := by
  unfold iidStreamLaw
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply (by fun_prop) (.univ_pi hs)]
  rw [show (fun z : ℕ → X => fun i : Fin n => z i) ⁻¹' Set.univ.pi s =
      Set.pi (Finset.range n)
        (fun i : ℕ => if h : i < n then s ⟨i, h⟩ else Set.univ) by
    ext z
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_const]
    constructor
    · intro hz i hi
      have hin : i < n := by simpa using hi
      rw [dif_pos hin]
      simpa using hz ⟨i, hin⟩
    · intro hz i
      have hi := hz (i : ℕ)
        (show (i : ℕ) ∈ Finset.range n from Finset.mem_range.mpr i.2)
      rw [dif_pos i.2] at hi
      simpa using hi]
  rw [Measure.infinitePi_pi (μ := fun _ : ℕ => P)
    (s := Finset.range n)
    (t := fun i : ℕ => if h : i < n then s ⟨i, h⟩ else Set.univ)]
  · rw [Finset.prod_range]
    simp
  · intro i hi
    rw [dif_pos (Finset.mem_range.1 hi)]
    exact hs _

/-- An independent scalar Poisson count and infinite i.i.d. stream. -/
noncomputable def poissonIIDStreamLaw (P : Measure X) [IsProbabilityMeasure P]
    (lam : ℝ≥0) : Measure (ℕ × (ℕ → X)) :=
  (poissonMeasure lam).prod (iidStreamLaw P)

/-- The independent Poisson-count and i.i.d.-stream law is a probability
measure. -/
instance poissonIIDStreamLaw_isProbabilityMeasure (P : Measure X) [IsProbabilityMeasure P]
    (lam : ℝ≥0) : IsProbabilityMeasure (poissonIIDStreamLaw P lam) := by
  unfold poissonIIDStreamLaw
  infer_instance

/-- The count coordinate has the requested scalar Poisson law. -/
lemma poissonIIDStreamLaw_map_count (P : Measure X) [IsProbabilityMeasure P]
    (lam : ℝ≥0) :
    Measure.map Prod.fst (poissonIIDStreamLaw P lam) = poissonMeasure lam := by
  unfold poissonIIDStreamLaw iidStreamLaw
  rw [Measure.map_fst_prod, measure_univ, one_smul]

/-- Every finite stream prefix remains an exact product sample after pairing
the stream with an independent Poisson count. -/
lemma poissonIIDStreamLaw_map_finPrefix (P : Measure X) [IsProbabilityMeasure P]
    (lam : ℝ≥0) (n : ℕ) :
    Measure.map (fun z : ℕ × (ℕ → X) => fun i : Fin n => z.2 i)
        (poissonIIDStreamLaw P lam) = Measure.pi (fun _ : Fin n => P) := by
  rw [show (fun z : ℕ × (ℕ → X) => fun i : Fin n => z.2 i) =
      (fun z : ℕ → X => fun i : Fin n => z i) ∘ Prod.snd by rfl,
    ← Measure.map_map (by fun_prop) (by fun_prop)]
  unfold poissonIIDStreamLaw
  rw [Measure.map_snd_prod, measure_univ, one_smul, iidStreamLaw_map_finPrefix]

end CausalSmith.Substrate.FiniteMarkedPoissonPartition
