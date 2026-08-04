import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Basic
import Mathlib.Probability.Distributions.Uniform

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedVariables false

namespace CausalSmith.Stat.ReverseKLTwoCoverage

open MeasureTheory
open scoped BigOperators ENNReal Topology

noncomputable def dwEta : ℝ := 4 * Real.log 3
noncomputable def dwCoverageC : ℝ := 3 / 2
noncomputable def dwCoverageD : ℝ := 13 / 10

noncomputable def dwFeature (d : ℕ) (x : Fin d) (a : Fin 2) (i : Fin d) : ℝ :=
  if x = i then if a = 0 then 1 else 1 / 2 else 0

noncomputable def dwReward (a : Fin 2) : ℝ :=
  if a = 0 then 1 / 2 else 1 / 4

noncomputable def dwExperiment (d : ℕ) (hd : 4 ≤ d) :
    CommonExperiment d (Fin d) (Fin 2) where
  feature := dwFeature d
  reference := fun _ _ => 1 / 2
  eta := dwEta
  reference_isPolicy := by
    constructor
    · intro x a
      norm_num
    · intro x
      norm_num [Fin.sum_univ_two]
      rfl
  eta_pos := by
    unfold dwEta
    positivity
  dim_ge_four := hd

noncomputable def dwUniformFin (m : ℕ) (hm : 0 < m) :
    ProbabilityMeasure (Fin m) := by
  letI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
  exact ⟨(PMF.uniformOfFintype (Fin m)).toMeasure, inferInstance⟩

lemma dwUniformFin_singleton (m : ℕ) (hm : 0 < m) (x : Fin m) :
    (dwUniformFin m hm : Measure (Fin m)).real {x} = 1 / m := by
  letI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
  change (((PMF.uniformOfFintype (Fin m)).toMeasure) {x}).toReal = 1 / m
  rw [PMF.toMeasure_apply_singleton _ x (MeasurableSet.singleton x)]
  simp [PMF.uniformOfFintype_apply, ENNReal.toReal_inv]

noncomputable def dwSource (d : ℕ) (hd : 4 ≤ d) :
    ProbabilityMeasure (Fin d × Fin 2) :=
  ⟨(dwUniformFin d (by omega : 0 < d) : Measure (Fin d)).prod
      (dwUniformFin 2 (by omega) : Measure (Fin 2)), inferInstance⟩

noncomputable def dwObservation (d : ℕ) (p : Fin d × Fin 2) :
    BanditObservation (Fin d) (Fin 2) where
  context := p.1
  action := p.2
  reward := dwReward p.2

noncomputable def dwData (d : ℕ) (hd : 4 ≤ d) :
    ProbabilityMeasure (BanditObservation (Fin d) (Fin 2)) :=
  (dwSource d hd).map (measurable_of_finite (dwObservation d)).aemeasurable

noncomputable def dwLaw (d : ℕ) (hd : 4 ≤ d) :
    BanditLaw (dwExperiment d hd) where
  dataMeasure := dwData d hd
  isProbability := inferInstance
  reward_mem := by
    have htuple : Measurable
        (fun z : BanditObservation (Fin d) (Fin 2) =>
          (z.context, z.action, z.reward)) := by
      change Measurable[MeasurableSpace.comap
        (fun z : BanditObservation (Fin d) (Fin 2) =>
          (z.context, z.action, z.reward)) inferInstance] _
      exact comap_measurable _
    have hset : MeasurableSet
        {z : BanditObservation (Fin d) (Fin 2) |
          z.reward ∈ Set.Icc (0 : ℝ) 1} :=
      measurableSet_Icc.preimage htuple.snd.snd
    change ∀ᵐ z ∂(dwData d hd :
      Measure (BanditObservation (Fin d) (Fin 2))),
        z.reward ∈ Set.Icc (0 : ℝ) 1
    rw [show (dwData d hd : Measure (BanditObservation (Fin d) (Fin 2))) =
      Measure.map (dwObservation d) (dwSource d hd : Measure (Fin d × Fin 2)) by
        rfl]
    rw [ae_map_iff (measurable_of_finite _).aemeasurable hset]
    filter_upwards with p
    by_cases hp : p.2 = 0 <;>
      simp [dwObservation, dwReward, hp] <;> norm_num [inv_le_one₀]
  theta := fun _ => 1 / 2

lemma dw_linearReward (d : ℕ) (hd : 4 ≤ d) (x : Fin d) (a : Fin 2) :
    linearReward (dwLaw d hd) x a = dwReward a := by
  by_cases ha : a = 0
  · simp [linearReward, dwLaw, dwExperiment, dwFeature, dwReward, ha]
  · simp [linearReward, dwLaw, dwExperiment, dwFeature, dwReward, ha]
    norm_num

lemma dw_reward_eq_ae (d : ℕ) (hd : 4 ≤ d) :
    ∀ᵐ z ∂(dwLaw d hd).dataMeasure,
      z.reward = dwReward z.action := by
  change ∀ᵐ z ∂(dwData d hd :
    Measure (BanditObservation (Fin d) (Fin 2))),
      z.reward = dwReward z.action
  rw [show (dwData d hd : Measure (BanditObservation (Fin d) (Fin 2))) =
    Measure.map (dwObservation d) (dwSource d hd : Measure (Fin d × Fin 2)) by
      rfl]
  have htuple : Measurable
      (fun z : BanditObservation (Fin d) (Fin 2) =>
        (z.context, z.action, z.reward)) := by
    change Measurable[MeasurableSpace.comap
      (fun z : BanditObservation (Fin d) (Fin 2) =>
        (z.context, z.action, z.reward)) inferInstance] _
    exact comap_measurable _
  have hset : MeasurableSet
      {z : BanditObservation (Fin d) (Fin 2) |
        z.reward = dwReward z.action} := by
    exact measurableSet_eq_fun htuple.snd.snd
      ((measurable_of_finite dwReward).comp htuple.snd.fst)
  rw [ae_map_iff (measurable_of_finite _).aemeasurable hset]
  filter_upwards with p
  rfl

lemma dw_contextAction_measurePreserving (d : ℕ) (hd : 4 ≤ d) :
    MeasurePreserving
      (fun z : BanditObservation (Fin d) (Fin 2) => (z.context, z.action))
      (dwData d hd : Measure (BanditObservation (Fin d) (Fin 2)))
      (dwSource d hd : Measure (Fin d × Fin 2)) := by
  have htuple : Measurable
      (fun z : BanditObservation (Fin d) (Fin 2) =>
        (z.context, z.action, z.reward)) := by
    change Measurable[MeasurableSpace.comap
      (fun z : BanditObservation (Fin d) (Fin 2) =>
        (z.context, z.action, z.reward)) inferInstance] _
    exact comap_measurable _
  have hpair : Measurable
      (fun z : BanditObservation (Fin d) (Fin 2) => (z.context, z.action)) :=
    Measurable.prodMk htuple.fst htuple.snd.fst
  refine ⟨?_, ?_⟩
  · exact hpair
  · rw [show (dwData d hd : Measure (BanditObservation (Fin d) (Fin 2))) =
        Measure.map (dwObservation d) (dwSource d hd : Measure (Fin d × Fin 2)) by rfl,
      Measure.map_map]
    · simp [Function.comp_def, dwObservation]
    · exact hpair
    · exact measurable_of_finite _

lemma dw_contextMass (d : ℕ) (hd : 4 ≤ d) (x : Fin d) :
    contextMass (dwLaw d hd) x = 1 / d := by
  let pairMap :=
    fun z : BanditObservation (Fin d) (Fin 2) => (z.context, z.action)
  have hpair := dw_contextAction_measurePreserving d hd
  have hfst : MeasurePreserving
      (fun z : BanditObservation (Fin d) (Fin 2) => z.context)
      (dwData d hd : Measure (BanditObservation (Fin d) (Fin 2)))
      (dwUniformFin d (by omega) : Measure (Fin d)) := by
    have hprod : MeasurePreserving Prod.fst
        (dwSource d hd : Measure (Fin d × Fin 2))
        (dwUniformFin d (by omega) : Measure (Fin d)) := by
      simpa [dwSource] using
        (measurePreserving_fst
          (μ := (dwUniformFin d (by omega) : Measure (Fin d)))
          (ν := (dwUniformFin 2 (by omega) : Measure (Fin 2))))
    simpa [pairMap, Function.comp_def] using hprod.comp hpair
  unfold contextMass
  change ((dwData d hd : Measure (BanditObservation (Fin d) (Fin 2)))
      {z | z.context = x}).toReal = 1 / d
  have hx := congrArg (fun μ : Measure (Fin d) => μ.real {x}) hfst.map_eq
  change ((Measure.map
      (fun z : BanditObservation (Fin d) (Fin 2) => z.context)
      (dwData d hd : Measure (BanditObservation (Fin d) (Fin 2)))) {x}).toReal =
    ((dwUniformFin d (by omega) : Measure (Fin d)) {x}).toReal at hx
  rw [Measure.map_apply hfst.measurable (MeasurableSet.singleton x)] at hx
  simpa only [Set.preimage_setOf_eq, Set.mem_singleton_iff] using
    hx.trans (dwUniformFin_singleton d (by omega) x)

lemma dw_cellMass (d : ℕ) (hd : 4 ≤ d) (x : Fin d) (a : Fin 2) :
    cellMass (dwLaw d hd) x a = 1 / (2 * d) := by
  unfold cellMass
  change ((dwData d hd : Measure (BanditObservation (Fin d) (Fin 2)))
      {z | z.context = x ∧ z.action = a}).toReal = 1 / (2 * d)
  have hpair := dw_contextAction_measurePreserving d hd
  have hp := congrArg (fun μ : Measure (Fin d × Fin 2) => μ.real {(x, a)})
    hpair.map_eq
  change ((Measure.map
      (fun z : BanditObservation (Fin d) (Fin 2) => (z.context, z.action))
      (dwData d hd : Measure (BanditObservation (Fin d) (Fin 2))))
      {(x, a)}).toReal =
    ((dwSource d hd : Measure (Fin d × Fin 2)) {(x, a)}).toReal at hp
  rw [Measure.map_apply hpair.measurable
    (MeasurableSet.singleton (x, a))] at hp
  have hprod :
      (dwSource d hd : Measure (Fin d × Fin 2)).real {(x, a)} =
        (dwUniformFin d (by omega) : Measure (Fin d)).real {x} *
          (dwUniformFin 2 (by omega) : Measure (Fin 2)).real {a} := by
    change
      ((dwUniformFin d (by omega) : Measure (Fin d)).prod
        (dwUniformFin 2 (by omega) : Measure (Fin 2))).real {(x, a)} =
      (dwUniformFin d (by omega) : Measure (Fin d)).real {x} *
        (dwUniformFin 2 (by omega) : Measure (Fin 2)).real {a}
    rw [← Set.singleton_prod_singleton, measureReal_prod_prod]
  have hp' :
      (dwData d hd : Measure (BanditObservation (Fin d) (Fin 2))).real
          {z | z.context = x ∧ z.action = a} =
        (dwSource d hd : Measure (Fin d × Fin 2)).real {(x, a)} := by
    simpa only [Set.preimage, Set.mem_singleton_iff, Prod.mk.injEq] using hp
  calc
    (dwData d hd : Measure (BanditObservation (Fin d) (Fin 2))).real
        {z | z.context = x ∧ z.action = a} =
        (dwSource d hd : Measure (Fin d × Fin 2)).real {(x, a)} := hp'
    _ = (dwUniformFin d (by omega) : Measure (Fin d)).real {x} *
          (dwUniformFin 2 (by omega) : Measure (Fin 2)).real {a} := hprod
    _ = (1 / (d : ℝ)) * (1 / (2 : ℝ)) := by
      rw [dwUniformFin_singleton, dwUniformFin_singleton]
      norm_num
    _ = 1 / (2 * d) := by ring

end CausalSmith.Stat.ReverseKLTwoCoverage
