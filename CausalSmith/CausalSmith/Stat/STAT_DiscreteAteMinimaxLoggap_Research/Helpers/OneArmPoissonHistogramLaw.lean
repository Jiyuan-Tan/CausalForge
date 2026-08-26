import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.OneArmRaoBlackwell
import Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.Partition.CellLaws
import Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.Depoissonization

/-!
# Independent Poisson law of a finite-sample histogram

The histogram of a finite Poisson sample on a finite alphabet consists of
independent Poisson cell counts.
-/

namespace CausalSmith.Stat.DiscreteAteMinimaxLoggap

open MeasureTheory ProbabilityTheory
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open scoped NNReal

private lemma map_finitePoissonSampleLaw_finiteSampleMap
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (P : Measure X) [IsProbabilityMeasure P]
    (f : X → Y) (hf : Measurable f) (lam : ℝ≥0) :
    Measure.map (finiteSampleMap f) (finitePoissonSampleLaw P lam) =
      (letI : IsProbabilityMeasure (Measure.map f P) :=
        Measure.isProbabilityMeasure_map hf.aemeasurable
       finitePoissonSampleLaw (Measure.map f P) lam) := by
  letI : IsProbabilityMeasure (Measure.map f P) :=
    Measure.isProbabilityMeasure_map hf.aemeasurable
  let F := finiteSampleMap f
  have hF : Measurable F := measurable_finiteSampleMap f hf
  let μ := Measure.map F (finitePoissonSampleLaw P lam)
  let ν := finitePoissonSampleLaw (Measure.map f P) lam
  have hrest (n : ℕ) :
      μ.restrict (FiniteSample.count ⁻¹' ({n} : Set ℕ)) =
        ν.restrict (FiniteSample.count ⁻¹' ({n} : Set ℕ)) := by
    rw [show μ = Measure.map F (finitePoissonSampleLaw P lam) by rfl,
      Measure.restrict_map hF
        (measurable_finiteSample_count (MeasurableSet.singleton n))]
    have hpre : F ⁻¹' (FiniteSample.count ⁻¹' ({n} : Set ℕ)) =
        FiniteSample.count ⁻¹' ({n} : Set ℕ) := by ext s; rfl
    rw [hpre, finitePoissonSampleLaw_restrict_count_eq,
      show ν = finitePoissonSampleLaw (Measure.map f P) lam by rfl,
      finitePoissonSampleLaw_restrict_count_eq, Measure.map_smul,
      Measure.map_map hF (measurable_fixedSizeEmbed n)]
    have hfun : F ∘ fixedSizeEmbed n =
        fixedSizeEmbed n ∘ (fun x : Fin n → X => fun i => f (x i)) := by
      funext x
      exact finiteSampleMap_fixedSizeEmbed f n x
    rw [hfun]
    congr 1
    let G : (Fin n → X) → (Fin n → Y) := fun x i => f (x i)
    have hG : Measurable G :=
      measurable_pi_lambda _ fun i => hf.comp (measurable_pi_apply i)
    change Measure.map (fixedSizeEmbed n ∘ G)
      (Measure.pi fun _ : Fin n => P) = _
    calc
      Measure.map (fixedSizeEmbed n ∘ G) (Measure.pi fun _ : Fin n => P) =
          Measure.map (fixedSizeEmbed n)
            (Measure.map G (Measure.pi fun _ : Fin n => P)) :=
        (Measure.map_map (measurable_fixedSizeEmbed n) hG).symm
      _ = Measure.map (fixedSizeEmbed n)
          (Measure.pi fun _ : Fin n => Measure.map f P) := by
        rw [show G = (fun x i => f (x i)) by rfl,
          Measure.pi_map_pi (fun _ => hf.aemeasurable)]
  have hdecomp (η : Measure (FiniteSample Y)) :
      η = Measure.sum (fun n =>
        η.restrict (FiniteSample.count ⁻¹' ({n} : Set ℕ))) := by
    have hdis : Pairwise (Function.onFun Disjoint
        (fun n : ℕ => (FiniteSample.count : FiniteSample Y → ℕ) ⁻¹'
          ({n} : Set ℕ))) := by
      intro i j hij
      apply Set.disjoint_left.2
      intro s hi hj
      apply hij
      simpa using hi.symm.trans hj
    have hcover : ⋃ n : ℕ,
        (FiniteSample.count : FiniteSample Y → ℕ) ⁻¹' ({n} : Set ℕ) =
          Set.univ := by ext s; simp
    calc
      η = η.restrict Set.univ := by rw [Measure.restrict_univ]
      _ = η.restrict (⋃ n : ℕ,
          FiniteSample.count ⁻¹' ({n} : Set ℕ)) := by rw [hcover]
      _ = Measure.sum (fun n =>
          η.restrict (FiniteSample.count ⁻¹' ({n} : Set ℕ))) := by
        exact Measure.restrict_iUnion hdis
          (fun n => measurable_finiteSample_count (MeasurableSet.singleton n))
  change μ = ν
  rw [hdecomp μ, hdecomp ν]
  congr 1
  funext n
  exact hrest n

private noncomputable def singletonPartition
    (X : Type*) [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X] : FiniteMeasurablePartition X X where
  cell := id
  measurable_cell := measurable_id

private noncomputable def markedSingletonCounts
    {X : Type*} [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X]
    (s : FiniteSample (X × ℝ)) : X → ℕ :=
  fun x => ((singletonPartition X).restrictCell x s).count

private lemma map_markedSingletonCounts
    {X : Type*} [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X]
    (P : Measure X) [IsProbabilityMeasure P] (lam : ℝ≥0) :
    Measure.map markedSingletonCounts
        (finiteMarkedPoissonSampleLaw P (Measure.dirac 0) lam) =
      Measure.pi (fun x : X =>
        poissonMeasure (lam * (singletonPartition X).cellMass P x)) := by
  let p := singletonPartition X
  let R : Measure ℝ := Measure.dirac 0
  let countFamily : (X → FiniteSample (X × ℝ)) → (X → ℕ) :=
    fun q x => (q x).count
  have hcountFamily : Measurable countFamily :=
    measurable_pi_lambda _ fun x =>
      measurable_finiteSample_count.comp (measurable_pi_apply x)
  calc
    Measure.map markedSingletonCounts (finiteMarkedPoissonSampleLaw P R lam) =
        Measure.map countFamily
          (Measure.map p.restrictPartition
            (finiteMarkedPoissonSampleLaw P R lam)) := by
      rw [Measure.map_map hcountFamily p.measurable_restrictPartition]
      rfl
    _ = Measure.map countFamily
        (Measure.pi (fun x : X =>
          finiteMarkedPoissonSampleLaw (p.cellObservationLaw P x) R
            (lam * p.cellMass P x))) := by
      rw [p.map_restrictPartition_finiteMarkedPoissonSampleLaw]
    _ = Measure.pi (fun x : X => Measure.map FiniteSample.count
        (finiteMarkedPoissonSampleLaw (p.cellObservationLaw P x) R
          (lam * p.cellMass P x))) := by
      exact Measure.pi_map_pi
        (fun _ => measurable_finiteSample_count.aemeasurable)
    _ = Measure.pi (fun x : X =>
        poissonMeasure (lam * p.cellMass P x)) := by
      congr with x
      rw [finiteMarkedPoissonSampleLaw_map_count]

private lemma markedSingletonCounts_eq_histogram_erase
    {X : Type*} [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X] [DecidableEq X]
    (s : FiniteSample (X × ℝ)) :
    markedSingletonCounts s =
      finiteSampleHistogram (finiteSampleMap Prod.fst s).points := by
  classical
  rcases s with ⟨N, points⟩
  funext x
  unfold markedSingletonCounts finiteSampleHistogram
    FiniteMeasurablePartition.restrictCell
  simp only [FiniteSample.count, finiteSampleMap, FiniteSample.points]
  unfold FiniteMeasurablePartition.cellIndices
  let p : Fin N → Prop := fun i =>
    (singletonPartition X).cell
      (FiniteSample.points (⟨N, points⟩ : FiniteSample (X × ℝ)) i).1 = x
  let hp : DecidablePred p := fun _ => Classical.propDecidable _
  letI : DecidablePred p := hp
  change (Finset.univ.filter p).card =
    Fintype.card {i : Fin N // (points i).1 = x}
  calc
    (Finset.univ.filter p).card = Fintype.card {i : Fin N // p i} :=
      (Fintype.card_subtype p).symm
    _ = Fintype.card {i : Fin N // (points i).1 = x} :=
      Fintype.card_congr (Equiv.subtypeEquivRight fun i => by
        simp [p, singletonPartition, FiniteSample.points])

/-- The histogram of a finite Poisson sample on a finite alphabet is the
product of its independent singleton-cell Poisson count laws. -/
lemma map_finiteSampleHistogram_finitePoissonSampleLaw_eq_pi
    {X : Type*} [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X] [DecidableEq X]
    (P : Measure X) [IsProbabilityMeasure P] (lam : ℝ≥0) :
    Measure.map (fun s : FiniteSample X => finiteSampleHistogram s.points)
        (finitePoissonSampleLaw P lam) =
      Measure.pi (fun x : X =>
        poissonMeasure (lam * (singletonPartition X).cellMass P x)) := by
  have herase := map_finitePoissonSampleLaw_finiteSampleMap
    (P.prod (Measure.dirac (0 : ℝ))) Prod.fst measurable_fst lam
  have hprod : Measure.map Prod.fst (P.prod (Measure.dirac (0 : ℝ))) = P := by
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  have herase' :
      Measure.map (finiteSampleMap Prod.fst)
          (finitePoissonSampleLaw (P.prod (Measure.dirac (0 : ℝ))) lam) =
        finitePoissonSampleLaw P lam := by
    simpa only [hprod] using herase
  have hcompose :
      (fun s : FiniteSample X => finiteSampleHistogram s.points) ∘
          finiteSampleMap Prod.fst = markedSingletonCounts := by
    funext s
    exact (markedSingletonCounts_eq_histogram_erase s).symm
  have hhist : Measurable
      (fun s : FiniteSample X => finiteSampleHistogram s.points) :=
    measurable_of_countable _
  rw [← map_markedSingletonCounts P lam, ← herase',
    show finiteMarkedPoissonSampleLaw P (Measure.dirac (0 : ℝ)) lam =
      finitePoissonSampleLaw (P.prod (Measure.dirac (0 : ℝ))) lam by rfl,
    Measure.map_map hhist
      (measurable_finiteSampleMap Prod.fst measurable_fst)]
  exact congrArg
    (fun f : FiniteSample (X × ℝ) → (X → ℕ) =>
      Measure.map f
        (finitePoissonSampleLaw (P.prod (Measure.dirac (0 : ℝ))) lam))
    hcompose

/-- The independent Poisson histogram law, with each rate written directly
as the singleton mass of its alphabet atom. -/
lemma map_finiteSampleHistogram_finitePoissonSampleLaw_eq_pi_singleton
    {X : Type*} [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X] [DecidableEq X]
    (P : Measure X) [IsProbabilityMeasure P] (lam : ℝ≥0) :
    Measure.map (fun s : FiniteSample X => finiteSampleHistogram s.points)
        (finitePoissonSampleLaw P lam) =
      Measure.pi (fun x : X =>
        poissonMeasure (lam * (P {x}).toNNReal)) := by
  simpa [singletonPartition, FiniteMeasurablePartition.cellMass,
    FiniteMeasurablePartition.cellSet] using
    map_finiteSampleHistogram_finitePoissonSampleLaw_eq_pi P lam

end CausalSmith.Stat.DiscreteAteMinimaxLoggap
