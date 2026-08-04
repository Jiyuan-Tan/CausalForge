import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Lower.DimensionWitness.Shell
import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Localization.ConcentrationCore
import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Localization.BoundedLinearLocalization.LinearExactShell

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedVariables false

namespace CausalSmith.Stat.ReverseKLTwoCoverage

open MeasureTheory
open scoped BigOperators ENNReal Topology

def dwContextSample {d : ℕ}
    (sample : LoggedSample (d ^ 2) (Fin d) (Fin 2)) :
    Fin (d ^ 2) → Fin d :=
  fun i => (sample i).context

def dwCountBad (d : ℕ)
    (sample : LoggedSample (d ^ 2) (Fin d) (Fin 2)) : Prop :=
  ∃ j, 3 * d < cellCount (dwContextSample sample) j

def dwCountGood (d : ℕ)
    (sample : LoggedSample (d ^ 2) (Fin d) (Fin 2)) : Prop :=
  ¬dwCountBad d sample

def dwRewardGood (d : ℕ) (hd : 4 ≤ d)
    (sample : LoggedSample (d ^ 2) (Fin d) (Fin 2)) : Prop :=
  ∀ i, (sample i).reward =
    linearReward (dwLaw d hd) (sample i).context (sample i).action

def dwGoodEvent (d : ℕ) (hd : 4 ≤ d) :
    Set (LoggedSample (d ^ 2) (Fin d) (Fin 2)) :=
  {sample | dwCountGood d sample ∧ dwRewardGood d hd sample}

lemma dw_context_measurePreserving (d : ℕ) (hd : 4 ≤ d) :
    MeasurePreserving
      (fun z : BanditObservation (Fin d) (Fin 2) => z.context)
      (dwData d hd : Measure (BanditObservation (Fin d) (Fin 2)))
      (dwUniformFin d (by omega) : Measure (Fin d)) := by
  have hpair := dw_contextAction_measurePreserving d hd
  have hfst : MeasurePreserving Prod.fst
      (dwSource d hd : Measure (Fin d × Fin 2))
      (dwUniformFin d (by omega) : Measure (Fin d)) := by
    simpa [dwSource] using
      (measurePreserving_fst
        (μ := (dwUniformFin d (by omega) : Measure (Fin d)))
        (ν := (dwUniformFin 2 (by omega) : Measure (Fin 2))))
  simpa [Function.comp_def] using hfst.comp hpair

lemma dw_contextSample_measurePreserving (d : ℕ) (hd : 4 ≤ d) :
    MeasurePreserving
      dwContextSample
      (productLaw (dwExperiment d hd) (dwLaw d hd) (d ^ 2))
      (iidProduct (dwUniformFin d (by omega) : Measure (Fin d))
        inferInstance (d ^ 2)) := by
  unfold productLaw iidProduct
  simpa [dwContextSample] using
    (measurePreserving_pi
      (fun _ : Fin (d ^ 2) =>
        (dwData d hd : Measure (BanditObservation (Fin d) (Fin 2))))
      (fun _ : Fin (d ^ 2) =>
        (dwUniformFin d (by omega) : Measure (Fin d)))
      (fun _ => dw_context_measurePreserving d hd))

lemma dw_rewardGood_ae (d : ℕ) (hd : 4 ≤ d) :
    ∀ᵐ sample ∂productLaw (dwExperiment d hd) (dwLaw d hd) (d ^ 2),
      dwRewardGood d hd sample := by
  letI : IsProbabilityMeasure (dwLaw d hd).dataMeasure :=
    (dwLaw d hd).isProbability
  simp only [dwRewardGood]
  refine ae_all_iff.mpr (fun i => ?_)
  exact
    (measurePreserving_eval
      (fun _ : Fin (d ^ 2) => (dwLaw d hd).dataMeasure) i).quasiMeasurePreserving
      |>.ae (dw_deterministicReward d hd)

lemma dw_countBad_measurable (d : ℕ) (hd : 4 ≤ d) :
    MeasurableSet
      {sample : LoggedSample (d ^ 2) (Fin d) (Fin 2) |
        dwCountBad d sample} := by
  let badContexts : Set (Fin (d ^ 2) → Fin d) :=
    {sample | ∃ j, 3 * d < cellCount sample j}
  have hbad : MeasurableSet badContexts := Set.toFinite _ |>.measurableSet
  have hpre :
      {sample : LoggedSample (d ^ 2) (Fin d) (Fin 2) |
        dwCountBad d sample} = dwContextSample ⁻¹' badContexts := by
    rfl
  rw [hpre]
  exact hbad.preimage (dw_contextSample_measurePreserving d hd).measurable

lemma dw_rewardGood_measurable (d : ℕ) (hd : 4 ≤ d) :
    MeasurableSet
      {sample : LoggedSample (d ^ 2) (Fin d) (Fin 2) |
        dwRewardGood d hd sample} := by
  have hobs : Measurable
      (fun z : BanditObservation (Fin d) (Fin 2) =>
        (z.context, z.action, z.reward)) := by
    change Measurable[MeasurableSpace.comap
      (fun z : BanditObservation (Fin d) (Fin 2) =>
        (z.context, z.action, z.reward)) inferInstance] _
    exact comap_measurable _
  rw [show {sample : LoggedSample (d ^ 2) (Fin d) (Fin 2) |
      dwRewardGood d hd sample} =
      ⋂ i : Fin (d ^ 2),
        {sample | (sample i).reward =
          linearReward (dwLaw d hd) (sample i).context (sample i).action} by
    ext sample
    simp [dwRewardGood]]
  apply MeasurableSet.iInter
  intro i
  have heval : Measurable
      (fun sample : LoggedSample (d ^ 2) (Fin d) (Fin 2) => sample i) :=
    measurable_pi_apply i
  exact measurableSet_eq_fun
    (hobs.snd.snd.comp heval)
    ((measurable_of_finite
      (fun p : Fin d × Fin 2 => linearReward (dwLaw d hd) p.1 p.2)).comp
        ((Measurable.prodMk hobs.fst hobs.snd.fst).comp heval))

lemma dw_goodEvent_measurable (d : ℕ) (hd : 4 ≤ d) :
    MeasurableSet (dwGoodEvent d hd) := by
  exact (dw_countBad_measurable d hd).compl.inter
    (dw_rewardGood_measurable d hd)

lemma dw_countBad_probability (d : ℕ) (hd : 4 ≤ d) :
    (productLaw (dwExperiment d hd) (dwLaw d hd) (d ^ 2)).real
        {sample | dwCountBad d sample} ≤
      d * Real.exp (-(d : ℝ) * (3 * Real.log 3 - 2)) := by
  let μ : Measure (Fin d) := dwUniformFin d (by omega)
  have hunif : ∀ j, μ.real {j} = 1 / d :=
    dwUniformFin_singleton d (by omega)
  have htail :=
    (multinomial_max_count d (by omega) μ inferInstance hunif).1
  have hmp := dw_contextSample_measurePreserving d hd
  have hmeasure := congrArg
    (fun ν : Measure (Fin (d ^ 2) → Fin d) =>
      ν.real {sample | ∃ j, 3 * d < cellCount sample j}) hmp.map_eq
  change ((Measure.map dwContextSample
      (productLaw (dwExperiment d hd) (dwLaw d hd) (d ^ 2)))
      {sample | ∃ j, 3 * d < cellCount sample j}).toReal =
    (iidProduct μ inferInstance (d ^ 2)).real
      {sample | ∃ j, 3 * d < cellCount sample j} at hmeasure
  rw [Measure.map_apply hmp.measurable (Set.toFinite _ |>.measurableSet)] at hmeasure
  rw [← hmeasure] at htail
  simpa [dwCountBad, dwContextSample, μ, Set.preimage] using htail

lemma dw_goodEvent_probability (d : ℕ) (hd : 4 ≤ d) :
    (productLaw (dwExperiment d hd) (dwLaw d hd) (d ^ 2)).real
        (dwGoodEvent d hd) ≥
      1 - d * Real.exp (-(d : ℝ) * (3 * Real.log 3 - 2)) := by
  let ν := productLaw (dwExperiment d hd) (dwLaw d hd) (d ^ 2)
  letI : IsProbabilityMeasure (dwLaw d hd).dataMeasure :=
    (dwLaw d hd).isProbability
  letI : IsProbabilityMeasure ν := by
    dsimp only [ν, productLaw]
    infer_instance
  let countSet : Set (LoggedSample (d ^ 2) (Fin d) (Fin 2)) :=
    {sample | dwCountGood d sample}
  have hcountMeas : MeasurableSet countSet := by
    exact (dw_countBad_measurable d hd).compl
  have hgoodEq : ν (dwGoodEvent d hd) = ν countSet := by
    apply measure_congr
    filter_upwards [dw_rewardGood_ae d hd] with sample hs
    apply propext
    change (dwCountGood d sample ∧ dwRewardGood d hd sample) ↔
      dwCountGood d sample
    simp [hs]
  have hcount :
      ν.real countSet =
        1 - ν.real {sample | dwCountBad d sample} := by
    rw [show countSet =
        {sample : LoggedSample (d ^ 2) (Fin d) (Fin 2) |
          dwCountBad d sample}ᶜ by
      ext sample
      simp [countSet, dwCountGood]]
    rw [measureReal_compl (dw_countBad_measurable d hd), probReal_univ]
  rw [show ν.real (dwGoodEvent d hd) = ν.real countSet by
    exact congrArg ENNReal.toReal hgoodEq, hcount]
  linarith [dw_countBad_probability d hd]

end CausalSmith.Stat.ReverseKLTwoCoverage
