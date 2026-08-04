import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Feasibility.CertificateAlgebra
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSectionVars false

namespace CausalSmith.Stat.ReverseKLTwoCoverage

open MeasureTheory
open scoped BigOperators ENNReal

variable {d : ℕ} {𝒳 𝒜 : Type*}
  [Fintype 𝒳] [Fintype 𝒜] [DecidableEq 𝒳] [DecidableEq 𝒜]
  [MeasurableSpace 𝒳] [MeasurableSpace 𝒜]
  [MeasurableSingletonClass 𝒳] [MeasurableSingletonClass 𝒜]

noncomputable def ibBernoulliWeight
    (E : CommonExperiment d 𝒳 𝒜) (rho : 𝒳 → ℝ)
    (r : 𝒳 → 𝒜 → ℝ) (p : 𝒳 × (𝒜 × Bool)) : ℝ≥0∞ :=
  ENNReal.ofReal
    (rho p.1 * E.reference p.1 p.2.1 *
      if p.2.2 then r p.1 p.2.1 else 1 - r p.1 p.2.1)

lemma ibBernoulliWeight_sum
    (E : CommonExperiment d 𝒳 𝒜) (rho : 𝒳 → ℝ)
    (r : 𝒳 → 𝒜 → ℝ)
    (hrho : ∀ x, 0 ≤ rho x) (hrhosum : ∑ x, rho x = 1)
    (hr : ∀ x a, r x a ∈ Set.Icc (0 : ℝ) 1) :
    ∑ p : 𝒳 × (𝒜 × Bool), ibBernoulliWeight E rho r p = 1 := by
  simp only [ibBernoulliWeight, Fintype.sum_prod_type]
  calc
    (∑ x : 𝒳, ∑ a : 𝒜, ∑ b : Bool,
        ENNReal.ofReal
          (rho x * E.reference x a *
            if b then r x a else 1 - r x a)) =
        ∑ x : 𝒳, ENNReal.ofReal (rho x) := by
      apply Finset.sum_congr rfl
      intro x _
      calc
        (∑ a : 𝒜, ∑ b : Bool,
          ENNReal.ofReal
            (rho x * E.reference x a *
              if b then r x a else 1 - r x a)) =
          ∑ a : 𝒜, ENNReal.ofReal (rho x * E.reference x a) := by
            apply Finset.sum_congr rfl
            intro a _
            rw [show (∑ b : Bool,
                ENNReal.ofReal
                  (rho x * E.reference x a *
                    if b then r x a else 1 - r x a)) =
                ENNReal.ofReal
                  (rho x * E.reference x a * r x a) +
                ENNReal.ofReal
                  (rho x * E.reference x a * (1 - r x a)) by
              rw [Fintype.sum_bool]
              simp]
            rw [← ENNReal.ofReal_add]
            · congr 1
              ring
            · exact mul_nonneg
                (mul_nonneg (hrho x) (E.reference_isPolicy.1 x a))
                (hr x a).1
            · exact mul_nonneg
                (mul_nonneg (hrho x) (E.reference_isPolicy.1 x a))
                (sub_nonneg.mpr (hr x a).2)
      _ = ENNReal.ofReal (rho x) := by
            rw [← ENNReal.ofReal_sum_of_nonneg]
            · rw [← Finset.mul_sum, E.reference_isPolicy.2 x, mul_one]
            · intro a _
              exact mul_nonneg (hrho x) (E.reference_isPolicy.1 x a)
    _ = ENNReal.ofReal (∑ x, rho x) := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      intro x _
      exact hrho x
    _ = 1 := by
      rw [hrhosum]
      simp

noncomputable def ibBernoulliPMF
    (E : CommonExperiment d 𝒳 𝒜) (rho : 𝒳 → ℝ)
    (r : 𝒳 → 𝒜 → ℝ)
    (hrho : ∀ x, 0 ≤ rho x) (hrhosum : ∑ x, rho x = 1)
    (hr : ∀ x a, r x a ∈ Set.Icc (0 : ℝ) 1) :
    PMF (𝒳 × (𝒜 × Bool)) :=
  PMF.ofFintype (ibBernoulliWeight E rho r)
    (ibBernoulliWeight_sum E rho r hrho hrhosum hr)

noncomputable def ibObservation
    (p : 𝒳 × (𝒜 × Bool)) : BanditObservation 𝒳 𝒜 where
  context := p.1
  action := p.2.1
  reward := if p.2.2 then 1 else 0

lemma ibObservation_measurable :
    Measurable (ibObservation : 𝒳 × (𝒜 × Bool) → BanditObservation 𝒳 𝒜) :=
  measurable_of_finite _

lemma ibObservation_injective :
    Function.Injective
      (ibObservation : 𝒳 × (𝒜 × Bool) → BanditObservation 𝒳 𝒜) := by
  rintro ⟨x, a, b⟩ ⟨x', a', b'⟩ h
  have hx : x = x' := congrArg BanditObservation.context h
  have ha : a = a' := congrArg BanditObservation.action h
  have hb : b = b' := by
    have := congrArg BanditObservation.reward h
    cases b <;> cases b' <;> simp_all [ibObservation]
  simp [hx, ha, hb]

noncomputable def ibBernoulliLaw
    (E : CommonExperiment d 𝒳 𝒜) (rho : 𝒳 → ℝ)
    (theta : Fin d → ℝ)
    (hrho : ∀ x, 0 ≤ rho x) (hrhosum : ∑ x, rho x = 1)
    (hbound : ∀ x a,
      (∑ i, E.feature x a i * theta i) ∈ Set.Icc (0 : ℝ) 1) :
    BanditLaw E where
  dataMeasure :=
    Measure.map ibObservation
      (ibBernoulliPMF E rho
        (fun x a => ∑ i, E.feature x a i * theta i)
        hrho hrhosum hbound).toMeasure
  isProbability := by
    exact Measure.isProbabilityMeasure_map ibObservation_measurable.aemeasurable
  reward_mem := by
    have hreward : Measurable
        (fun z : BanditObservation 𝒳 𝒜 => z.reward) := by
      change Measurable[MeasurableSpace.comap
        (fun z : BanditObservation 𝒳 𝒜 =>
          (z.context, z.action, z.reward)) inferInstance] _
      exact (comap_measurable _).snd.snd
    have hset : MeasurableSet
        {z : BanditObservation 𝒳 𝒜 | z.reward ∈ Set.Icc (0 : ℝ) 1} :=
      measurableSet_Icc.preimage hreward
    rw [ae_map_iff ibObservation_measurable.aemeasurable hset]
    filter_upwards with p
    rcases p with ⟨x, a, b⟩
    cases b <;> simp [ibObservation]
  theta := theta

lemma ibBernoulliPMF_apply
    (E : CommonExperiment d 𝒳 𝒜) (rho : 𝒳 → ℝ)
    (r : 𝒳 → 𝒜 → ℝ)
    (hrho : ∀ x, 0 ≤ rho x) (hrhosum : ∑ x, rho x = 1)
    (hr : ∀ x a, r x a ∈ Set.Icc (0 : ℝ) 1)
    (x : 𝒳) (a : 𝒜) (b : Bool) :
    ibBernoulliPMF E rho r hrho hrhosum hr (x, a, b) =
      ENNReal.ofReal
        (rho x * E.reference x a *
          if b then r x a else 1 - r x a) := by
  exact PMF.ofFintype_apply _ _

lemma ibBernoulliSource_cell
    (E : CommonExperiment d 𝒳 𝒜) (rho : 𝒳 → ℝ)
    (r : 𝒳 → 𝒜 → ℝ)
    (hrho : ∀ x, 0 ≤ rho x) (hrhosum : ∑ x, rho x = 1)
    (hr : ∀ x a, r x a ∈ Set.Icc (0 : ℝ) 1)
    (x : 𝒳) (a : 𝒜) :
    (ibBernoulliPMF E rho r hrho hrhosum hr).toMeasure
        {p : 𝒳 × (𝒜 × Bool) | p.1 = x ∧ p.2.1 = a} =
      ENNReal.ofReal (rho x * E.reference x a) := by
  classical
  have hset :
      {p : 𝒳 × (𝒜 × Bool) | p.1 = x ∧ p.2.1 = a} =
        ⋃ b : Bool, {(x, (a, b))} := by
    ext p
    rcases p with ⟨y, c, b⟩
    cases b <;> simp [eq_comm]
  rw [hset, measure_iUnion]
  · simp_rw [PMF.toMeasure_apply_singleton _
      _ (MeasurableSet.singleton _), ibBernoulliPMF_apply]
    rw [tsum_fintype, Fintype.sum_bool, ← ENNReal.ofReal_add]
    · congr 1
      simp
      ring
    · exact mul_nonneg
        (mul_nonneg (hrho x) (E.reference_isPolicy.1 x a))
        (hr x a).1
    · exact mul_nonneg
        (mul_nonneg (hrho x) (E.reference_isPolicy.1 x a))
        (sub_nonneg.mpr (hr x a).2)
  · intro b c hbc
    exact Set.disjoint_singleton.2 fun h =>
      hbc (congrArg (fun p : 𝒳 × (𝒜 × Bool) => p.2.2) h)
  · intro b
    exact MeasurableSet.singleton _

lemma ibBernoulliLaw_contextMass
    (E : CommonExperiment d 𝒳 𝒜) (rho : 𝒳 → ℝ)
    (theta : Fin d → ℝ)
    (hrho : ∀ x, 0 ≤ rho x) (hrhosum : ∑ x, rho x = 1)
    (hbound : ∀ x a,
      (∑ i, E.feature x a i * theta i) ∈ Set.Icc (0 : ℝ) 1)
    (x : 𝒳) :
    contextMass (ibBernoulliLaw E rho theta hrho hrhosum hbound) x =
      rho x := by
  classical
  unfold contextMass ibBernoulliLaw
  have hcontext : Measurable
      (fun z : BanditObservation 𝒳 𝒜 => z.context) := by
    change Measurable[MeasurableSpace.comap
      (fun z : BanditObservation 𝒳 𝒜 =>
        (z.context, z.action, z.reward)) inferInstance] _
    exact (comap_measurable _).fst
  have hset : MeasurableSet
      {z : BanditObservation 𝒳 𝒜 | z.context = x} := by
    simpa only [Set.preimage, Set.mem_singleton_iff] using
      (measurableSet_singleton x).preimage hcontext
  rw [Measure.map_apply ibObservation_measurable hset]
  change ((ibBernoulliPMF E rho
      (fun x a => ∑ i, E.feature x a i * theta i)
      hrho hrhosum hbound).toMeasure
      {p : 𝒳 × (𝒜 × Bool) | p.1 = x}).toReal = rho x
  have hpre : MeasurableSet
      {p : 𝒳 × (𝒜 × Bool) | p.1 = x} :=
    (Set.toFinite _).measurableSet
  rw [PMF.toMeasure_apply _ hpre, tsum_fintype]
  simp only [Set.indicator, Set.mem_setOf_eq, Fintype.sum_prod_type]
  have hsum : (∑ y : 𝒳, ∑ a : 𝒜, ∑ b : Bool,
      if y = x then
        ibBernoulliPMF E rho
          (fun x a => ∑ i, E.feature x a i * theta i)
          hrho hrhosum hbound (y, (a, b))
      else 0) = ENNReal.ofReal (rho x) := by
    rw [Finset.sum_eq_single x]
    · simp only [if_pos, ibBernoulliPMF_apply]
      calc
        (∑ a : 𝒜, ∑ b : Bool,
            ENNReal.ofReal
              (rho x * E.reference x a *
                if b then
                  ∑ i, E.feature x a i * theta i
                else 1 - ∑ i, E.feature x a i * theta i)) =
            ∑ a : 𝒜, ENNReal.ofReal (rho x * E.reference x a) := by
              apply Finset.sum_congr rfl
              intro a _
              rw [Fintype.sum_bool, ← ENNReal.ofReal_add]
              · congr 1
                simp
                ring
              · exact mul_nonneg
                  (mul_nonneg (hrho x) (E.reference_isPolicy.1 x a))
                  (hbound x a).1
              · exact mul_nonneg
                  (mul_nonneg (hrho x) (E.reference_isPolicy.1 x a))
                  (sub_nonneg.mpr (hbound x a).2)
        _ = ENNReal.ofReal (rho x) := by
              rw [← ENNReal.ofReal_sum_of_nonneg]
              · rw [← Finset.mul_sum, E.reference_isPolicy.2 x, mul_one]
              · intro a _
                exact mul_nonneg (hrho x) (E.reference_isPolicy.1 x a)
    · intro y _ hy
      simp [hy]
    · simp
  have hsum' : (∑ x₁ : 𝒳, ∑ x₂ : 𝒜, ∑ y : Bool,
      if x₁ = x then
        ibBernoulliPMF E rho
          (fun x a => ∑ i, E.feature x a i * theta i)
          hrho hrhosum hbound (x₁, x₂, y)
      else 0) = ENNReal.ofReal (rho x) := by
    simpa using hsum
  convert (congrArg ENNReal.toReal hsum').trans
    (ENNReal.toReal_ofReal (hrho x)) using 1
  apply congrArg ENNReal.toReal
  apply Finset.sum_congr rfl
  intro y _
  by_cases hy : y = x <;> simp [hy]

lemma ibBernoulliLaw_cellMass
    (E : CommonExperiment d 𝒳 𝒜) (rho : 𝒳 → ℝ)
    (theta : Fin d → ℝ)
    (hrho : ∀ x, 0 ≤ rho x) (hrhosum : ∑ x, rho x = 1)
    (hbound : ∀ x a,
      (∑ i, E.feature x a i * theta i) ∈ Set.Icc (0 : ℝ) 1)
    (x : 𝒳) (a : 𝒜) :
    cellMass (ibBernoulliLaw E rho theta hrho hrhosum hbound) x a =
      contextMass (ibBernoulliLaw E rho theta hrho hrhosum hbound) x *
        E.reference x a := by
  classical
  unfold cellMass ibBernoulliLaw
  have hpair : Measurable
      (fun z : BanditObservation 𝒳 𝒜 => (z.context, z.action)) := by
    change Measurable[MeasurableSpace.comap
      (fun z : BanditObservation 𝒳 𝒜 =>
        (z.context, z.action, z.reward)) inferInstance] _
    exact Measurable.prodMk (comap_measurable _).fst
      (comap_measurable _).snd.fst
  have hset : MeasurableSet
      {z : BanditObservation 𝒳 𝒜 | z.context = x ∧ z.action = a} := by
    simpa only [Set.preimage, Set.mem_singleton_iff, Prod.mk.injEq] using
      (measurableSet_singleton (x, a)).preimage hpair
  rw [Measure.map_apply ibObservation_measurable hset]
  change ((ibBernoulliPMF E rho
      (fun x a => ∑ i, E.feature x a i * theta i)
      hrho hrhosum hbound).toMeasure
      {p : 𝒳 × (𝒜 × Bool) | p.1 = x ∧ p.2.1 = a}).toReal =
    contextMass (ibBernoulliLaw E rho theta hrho hrhosum hbound) x *
      E.reference x a
  rw [ibBernoulliSource_cell, ENNReal.toReal_ofReal
    (mul_nonneg (hrho x) (E.reference_isPolicy.1 x a)),
    ibBernoulliLaw_contextMass]

lemma ibBernoulliLaw_rewardMean
    (E : CommonExperiment d 𝒳 𝒜) (rho : 𝒳 → ℝ)
    (theta : Fin d → ℝ)
    (hrho : ∀ x, 0 ≤ rho x) (hrhosum : ∑ x, rho x = 1)
    (hbound : ∀ x a,
      (∑ i, E.feature x a i * theta i) ∈ Set.Icc (0 : ℝ) 1)
    (x : 𝒳) (a : 𝒜)
    (hcell : 0 <
      cellMass (ibBernoulliLaw E rho theta hrho hrhosum hbound) x a) :
    rewardMean (ibBernoulliLaw E rho theta hrho hrhosum hbound) x a =
      linearReward (ibBernoulliLaw E rho theta hrho hrhosum hbound) x a := by
  classical
  let P := ibBernoulliLaw E rho theta hrho hrhosum hbound
  let r : 𝒳 → 𝒜 → ℝ :=
    fun y b => ∑ i, E.feature y b i * theta i
  let s : Set (BanditObservation 𝒳 𝒜) :=
    {z | z.context = x ∧ z.action = a}
  have hpair : Measurable
      (fun z : BanditObservation 𝒳 𝒜 => (z.context, z.action)) := by
    change Measurable[MeasurableSpace.comap
      (fun z : BanditObservation 𝒳 𝒜 =>
        (z.context, z.action, z.reward)) inferInstance] _
    exact Measurable.prodMk (comap_measurable _).fst
      (comap_measurable _).snd.fst
  have hs : MeasurableSet s := by
    simpa only [s, Set.preimage, Set.mem_singleton_iff, Prod.mk.injEq] using
      (measurableSet_singleton (x, a)).preimage hpair
  have hreward : Measurable
      (fun z : BanditObservation 𝒳 𝒜 => z.reward) := by
    change Measurable[MeasurableSpace.comap
      (fun z : BanditObservation 𝒳 𝒜 =>
        (z.context, z.action, z.reward)) inferInstance] _
    exact (comap_measurable _).snd.snd
  have hg : Measurable
      (s.indicator fun z : BanditObservation 𝒳 𝒜 => z.reward) :=
    hreward.indicator hs
  have hnum :
      (∫ z in s, z.reward ∂P.dataMeasure) =
        rho x * E.reference x a * r x a := by
    dsimp [P, ibBernoulliLaw]
    rw [← integral_indicator hs]
    dsimp [r]
    change (∫ z, s.indicator
        (fun z : BanditObservation 𝒳 𝒜 => z.reward) z
      ∂Measure.map ibObservation
        (ibBernoulliPMF E rho
          (fun y b => ∑ i, E.feature y b i * theta i)
          hrho hrhosum hbound).toMeasure) =
      rho x * E.reference x a *
        (∑ i, E.feature x a i * theta i)
    rw [integral_map ibObservation_measurable.aemeasurable
      hg.aestronglyMeasurable, PMF.integral_eq_sum]
    simp only [Fintype.sum_prod_type, ibBernoulliPMF_apply, smul_eq_mul,
      s, ibObservation, Set.indicator]
    rw [Finset.sum_eq_single x]
    · rw [Finset.sum_eq_single a]
      · rw [Fintype.sum_bool]
        simp only [Bool.false_eq_true, if_false, Bool.true_eq, if_true]
        rw [ENNReal.toReal_ofReal]
        · simp
        · exact mul_nonneg
            (mul_nonneg (hrho x) (E.reference_isPolicy.1 x a))
            (hbound x a).1
      · intro b _ hba
        simp [hba]
      · simp
    · intro y _ hy
      simp [hy]
    · simp
  unfold rewardMean
  change (∫ z in s, z.reward ∂P.dataMeasure) /
      cellMass P x a = linearReward P x a
  rw [hnum]
  have hmass :
      cellMass P x a = rho x * E.reference x a := by
    dsimp [P]
    rw [ibBernoulliLaw_cellMass, ibBernoulliLaw_contextMass]
  have hmasspos : 0 < rho x * E.reference x a := by
    rwa [hmass] at hcell
  rw [hmass]
  change (rho x * E.reference x a * r x a) /
      (rho x * E.reference x a) = r x a
  exact mul_div_cancel_left₀ _ (ne_of_gt hmasspos)

lemma ibBernoulliLaw_linearRealizability
    (E : CommonExperiment d 𝒳 𝒜) (rho : 𝒳 → ℝ)
    (theta : Fin d → ℝ)
    (hrho : ∀ x, 0 ≤ rho x) (hrhosum : ∑ x, rho x = 1)
    (hbound : ∀ x a,
      (∑ i, E.feature x a i * theta i) ∈ Set.Icc (0 : ℝ) 1) :
    LinearRealizability E
      (ibBernoulliLaw E rho theta hrho hrhosum hbound) := by
  constructor
  · exact hbound
  · intro x a hcell
    exact ibBernoulliLaw_rewardMean E rho theta hrho hrhosum hbound x a hcell

lemma ibBernoulliLaw_referenceLogging
    (E : CommonExperiment d 𝒳 𝒜) (rho : 𝒳 → ℝ)
    (theta : Fin d → ℝ)
    (hrho : ∀ x, 0 ≤ rho x) (hrhosum : ∑ x, rho x = 1)
    (hbound : ∀ x a,
      (∑ i, E.feature x a i * theta i) ∈ Set.Icc (0 : ℝ) 1) :
    ReferenceLogging E
      (ibBernoulliLaw E rho theta hrho hrhosum hbound) := by
  intro x a
  exact ibBernoulliLaw_cellMass E rho theta hrho hrhosum hbound x a

end CausalSmith.Stat.ReverseKLTwoCoverage
