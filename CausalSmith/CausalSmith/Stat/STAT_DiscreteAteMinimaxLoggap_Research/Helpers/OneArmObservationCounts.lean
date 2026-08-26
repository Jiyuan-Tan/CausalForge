import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.LowerBound
import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.OneArmConfiguration
import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.OneArmPoissonPredictive
import Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.Partition.CellLaws

/-!
# Poisson sufficient counts for the control-zero one-arm model

The observation alphabet is coarsened into the three possible control-zero
outcomes in each category.  Finite marked-Poisson splitting then makes all
category/triple counts independent Poisson variables.
-/

namespace CausalSmith.Stat.DiscreteAteMinimaxLoggap

open MeasureTheory ProbabilityTheory
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open scoped NNReal

/-- The three sufficient outcomes are treated-success, treated-failure, and
control.  The impossible control-success atom is grouped with control. -/
def oneArmObservationTripleLabel {d : ℕ} (z : Obs d) : Fin d × Fin 3 :=
  (z.1, if z.2.1 then if z.2.2 then 0 else 1 else 2)

def oneArmObservationTriplePartition (d : ℕ) :
    FiniteMeasurablePartition (Obs d) (Fin d × Fin 3) where
  cell := oneArmObservationTripleLabel
  measurable_cell := measurable_of_finite _

lemma oneArmObservationTriplePartition_cellMass_treatedSuccess
    {d : ℕ} (p pi mu : Fin d → ℝ)
    (hp : ∀ r, p r ∈ Set.Icc (0 : ℝ) 1)
    (hpi : ∀ r, pi r ∈ Set.Icc (0 : ℝ) 1)
    (hmu : ∀ r, mu r ∈ Set.Icc (0 : ℝ) 1)
    (hp_sum : ∑ r, p r = 1) (r : Fin d) :
    ((oneArmObservationTriplePartition d).cellMass
      (obsLaw (oneArmConfigurationLaw p pi mu hp hpi hmu hp_sum)) (r, 0) : ℝ) =
      p r * pi r * mu r := by
  have hset : (oneArmObservationTriplePartition d).cellSet (r, 0) =
      {(r, true, true)} := by
    ext z
    rcases z with ⟨k, a, y⟩
    fin_cases a <;> fin_cases y <;>
      simp [FiniteMeasurablePartition.cellSet, oneArmObservationTriplePartition,
        oneArmObservationTripleLabel]
  unfold FiniteMeasurablePartition.cellMass
  rw [hset]
  change ((obsLaw (oneArmConfigurationLaw p pi mu hp hpi hmu hp_sum))
    {(r, true, true)}).toReal = _
  rw [obsLaw,
    (oneArmConfigurationLaw p pi mu hp hpi hmu hp_sum).pmf.toMeasure_apply_singleton
      (r, true, true) (MeasurableSet.singleton _)]
  simp [oneArmConfigurationLaw, oneArmConfigurationAtom]
  exact mul_nonneg (mul_nonneg (hp r).1 (hpi r).1) (hmu r).1

lemma oneArmObservationTriplePartition_cellMass_treatedFailure
    {d : ℕ} (p pi mu : Fin d → ℝ)
    (hp : ∀ r, p r ∈ Set.Icc (0 : ℝ) 1)
    (hpi : ∀ r, pi r ∈ Set.Icc (0 : ℝ) 1)
    (hmu : ∀ r, mu r ∈ Set.Icc (0 : ℝ) 1)
    (hp_sum : ∑ r, p r = 1) (r : Fin d) :
    ((oneArmObservationTriplePartition d).cellMass
      (obsLaw (oneArmConfigurationLaw p pi mu hp hpi hmu hp_sum)) (r, 1) : ℝ) =
      p r * pi r * (1 - mu r) := by
  have hset : (oneArmObservationTriplePartition d).cellSet (r, 1) =
      {(r, true, false)} := by
    ext z
    rcases z with ⟨k, a, y⟩
    fin_cases a <;> fin_cases y <;>
      simp [FiniteMeasurablePartition.cellSet, oneArmObservationTriplePartition,
        oneArmObservationTripleLabel]
  unfold FiniteMeasurablePartition.cellMass
  rw [hset]
  change ((obsLaw (oneArmConfigurationLaw p pi mu hp hpi hmu hp_sum))
    {(r, true, false)}).toReal = _
  rw [obsLaw,
    (oneArmConfigurationLaw p pi mu hp hpi hmu hp_sum).pmf.toMeasure_apply_singleton
      (r, true, false) (MeasurableSet.singleton _)]
  simp [oneArmConfigurationLaw, oneArmConfigurationAtom]
  exact mul_nonneg (mul_nonneg (hp r).1 (hpi r).1)
    (sub_nonneg.mpr (hmu r).2)

lemma oneArmObservationTriplePartition_cellMass_control
    {d : ℕ} (p pi mu : Fin d → ℝ)
    (hp : ∀ r, p r ∈ Set.Icc (0 : ℝ) 1)
    (hpi : ∀ r, pi r ∈ Set.Icc (0 : ℝ) 1)
    (hmu : ∀ r, mu r ∈ Set.Icc (0 : ℝ) 1)
    (hp_sum : ∑ r, p r = 1) (r : Fin d) :
    ((oneArmObservationTriplePartition d).cellMass
      (obsLaw (oneArmConfigurationLaw p pi mu hp hpi hmu hp_sum)) (r, 2) : ℝ) =
      p r * (1 - pi r) := by
  have hset : (oneArmObservationTriplePartition d).cellSet (r, 2) =
      {(r, false, false), (r, false, true)} := by
    ext z
    rcases z with ⟨k, a, y⟩
    fin_cases a <;> fin_cases y <;>
      simp [FiniteMeasurablePartition.cellSet, oneArmObservationTriplePartition,
        oneArmObservationTripleLabel]
  unfold FiniteMeasurablePartition.cellMass
  rw [hset]
  change ((obsLaw (oneArmConfigurationLaw p pi mu hp hpi hmu hp_sum))
    {(r, false, false), (r, false, true)}).toReal = _
  rw [obsLaw, PMF.toMeasure_apply _ MeasurableSet.of_discrete]
  rw [ENNReal.tsum_toReal_eq, tsum_fintype]
  · rw [Fintype.sum_prod_type]
    rw [Finset.sum_eq_single r]
    · rw [Fintype.sum_prod_type]
      simp [oneArmConfigurationLaw, oneArmConfigurationAtom]
      exact mul_nonneg (hp r).1 (sub_nonneg.mpr (hpi r).2)
    · intro k _ hkr
      simp [Set.indicator, hkr]
    · simp
  · intro x
    by_cases hx : x ∈ ({(r, false, false), (r, false, true)} : Set (Obs d)) <;>
      simp [Set.indicator, hx, PMF.apply_ne_top]

/-- Counts of the three sufficient outcomes in every category. -/
noncomputable def markedOneArmTripleCounts {d : ℕ}
    (s : FiniteSample (Obs d × ℝ)) : Fin d × Fin 3 → ℕ :=
  fun j => ((oneArmObservationTriplePartition d).restrictCell j s).count

lemma measurable_markedOneArmTripleCounts {d : ℕ} :
    Measurable (markedOneArmTripleCounts :
      FiniteSample (Obs d × ℝ) → Fin d × Fin 3 → ℕ) := by
  unfold markedOneArmTripleCounts
  exact measurable_pi_lambda _ fun j =>
    measurable_finiteSample_count.comp
      ((oneArmObservationTriplePartition d).measurable_restrictCell j)

/-- Exact model-specific pushforward: all sufficient counts are jointly
independent Poisson variables with the corresponding coarsened atom masses. -/
lemma map_markedOneArmTripleCounts_finiteMarkedPoissonSampleLaw
    {d : ℕ} (P : Measure (Obs d)) [IsProbabilityMeasure P]
    (lam : ℝ≥0) :
    Measure.map markedOneArmTripleCounts
        (finiteMarkedPoissonSampleLaw P (Measure.dirac 0) lam) =
      Measure.pi (fun j : Fin d × Fin 3 =>
        poissonMeasure
          (lam * (oneArmObservationTriplePartition d).cellMass P j)) := by
  let p := oneArmObservationTriplePartition d
  let R : Measure ℝ := Measure.dirac 0
  let sampleLaw := finiteMarkedPoissonSampleLaw P R lam
  have hjoint :=
    FiniteMeasurablePartition.map_restrictPartition_finiteMarkedPoissonSampleLaw
      p P R lam
  let countFamily : (Fin d × Fin 3 → FiniteSample (Obs d × ℝ)) →
      (Fin d × Fin 3 → ℕ) := fun q j => (q j).count
  have hcountFamily : Measurable countFamily :=
    measurable_pi_lambda _ fun j =>
      measurable_finiteSample_count.comp (measurable_pi_apply j)
  calc
    Measure.map markedOneArmTripleCounts sampleLaw =
        Measure.map countFamily (Measure.map p.restrictPartition sampleLaw) := by
      rw [Measure.map_map hcountFamily p.measurable_restrictPartition]
      rfl
    _ = Measure.map countFamily
        (Measure.pi (fun j : Fin d × Fin 3 =>
          finiteMarkedPoissonSampleLaw (p.cellObservationLaw P j) R
            (lam * p.cellMass P j))) := by rw [hjoint]
    _ = Measure.pi (fun j : Fin d × Fin 3 =>
        Measure.map FiniteSample.count
          (finiteMarkedPoissonSampleLaw (p.cellObservationLaw P j) R
            (lam * p.cellMass P j))) := by
      exact Measure.pi_map_pi
        (fun _ => measurable_finiteSample_count.aemeasurable)
    _ = Measure.pi (fun j : Fin d × Fin 3 =>
        poissonMeasure (lam * p.cellMass P j)) := by
      congr with j
      rw [finiteMarkedPoissonSampleLaw_map_count]

/-- The explicit triple-Poisson PMF is the three-coordinate Poisson product
measure. -/
lemma triplePoissonPMF_toMeasure_eq_pi
    (lam11 lam10 lam0 : ℝ≥0) :
    (triplePoissonPMF lam11 lam10 lam0).toMeasure =
      Measure.pi (fun j : Fin 3 =>
        poissonMeasure (![lam11, lam10, lam0] j)) := by
  apply Measure.ext_of_singleton
  intro c
  rw [(triplePoissonPMF lam11 lam10 lam0).toMeasure_apply_singleton c
    (MeasurableSet.singleton c)]
  have hset : ({c} : Set (Fin 3 → ℕ)) =
      Set.univ.pi (fun j => {c j}) := by
    ext z
    simp [Set.mem_pi, funext_iff]
  rw [hset, Measure.pi_pi]
  simp_rw [poissonMeasure_singleton_eq_poissonPMF]
  rw [triplePoissonPMF_apply]
  simp [Fin.prod_univ_succ, mul_assoc]

def curryOneArmTripleCounts {d : ℕ}
    (c : Fin d × Fin 3 → ℕ) : Fin d → Fin 3 → ℕ :=
  fun k j => c (k, j)

/-- Currying the flat independent category/triple count vector gives the
product of the categorywise triple-Poisson laws. -/
lemma map_curryOneArmTripleCounts_pi_poisson
    {d : ℕ} (lam11 lam10 lam0 : Fin d → ℝ≥0) :
    Measure.map curryOneArmTripleCounts
        (Measure.pi (fun u : Fin d × Fin 3 =>
          poissonMeasure (![lam11 u.1, lam10 u.1, lam0 u.1] u.2))) =
      Measure.pi (fun k : Fin d =>
        (triplePoissonPMF (lam11 k) (lam10 k) (lam0 k)).toMeasure) := by
  apply Measure.ext_of_singleton
  intro c
  rw [Measure.map_apply (measurable_of_countable _)
    (MeasurableSet.singleton c)]
  have hpre : curryOneArmTripleCounts ⁻¹' {c} =
      {fun u : Fin d × Fin 3 => c u.1 u.2} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun h => by ext u; exact congrFun (congrFun h u.1) u.2,
      fun h => by ext k j; exact congrFun h (k, j)⟩
  rw [hpre]
  have hflat : ({fun u : Fin d × Fin 3 => c u.1 u.2} :
      Set (Fin d × Fin 3 → ℕ)) = Set.univ.pi
        (fun u => {c u.1 u.2}) := by
    ext z
    simp [Set.mem_pi, funext_iff]
  rw [hflat, Measure.pi_pi]
  simp_rw [poissonMeasure_singleton_eq_poissonPMF]
  have hcurried : ({c} : Set (Fin d → Fin 3 → ℕ)) =
      Set.univ.pi (fun k => {c k}) := by
    ext z
    simp [Set.mem_pi, funext_iff]
  rw [hcurried, Measure.pi_pi]
  have hsingle (k : Fin d) :
      (triplePoissonPMF (lam11 k) (lam10 k) (lam0 k)).toMeasure {c k} =
        triplePoissonPMF (lam11 k) (lam10 k) (lam0 k) (c k) :=
    (triplePoissonPMF (lam11 k) (lam10 k) (lam0 k)).toMeasure_apply_singleton
      (c k) (MeasurableSet.singleton (c k))
  simp_rw [hsingle, triplePoissonPMF_apply]
  rw [Fintype.prod_prod_type]
  simp [Fin.prod_univ_succ, mul_assoc]

end CausalSmith.Stat.DiscreteAteMinimaxLoggap
