import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace CausalSmith.Stat.ReverseKLTwoCoverage

open MeasureTheory
open scoped BigOperators ENNReal

variable {d : ℕ} {𝒳 𝒜 : Type*}
  [Fintype 𝒳] [Fintype 𝒜] [DecidableEq 𝒳] [DecidableEq 𝒜]
  [MeasurableSpace 𝒳] [MeasurableSpace 𝒜]
  [MeasurableSingletonClass 𝒳] [MeasurableSingletonClass 𝒜]

noncomputable def certificateRho
    (I : Finset 𝒳) (rho : I → ℝ) (x : 𝒳) : ℝ :=
  if hx : x ∈ I then rho ⟨x, hx⟩ else 0

lemma certificateRho_nonneg
    (I : Finset 𝒳) (rho : I → ℝ) (hrho : ∀ x, 0 ≤ rho x) (x : 𝒳) :
    0 ≤ certificateRho I rho x := by
  simp only [certificateRho]
  split_ifs with hx
  · exact hrho ⟨x, hx⟩
  · exact le_rfl

lemma certificateRho_sum
    (I : Finset 𝒳) (rho : I → ℝ) (hsum : ∑ x, rho x = 1) :
    ∑ x, certificateRho I rho x = 1 := by
  classical
  rw [← hsum]
  calc
    (∑ x : 𝒳, certificateRho I rho x) =
        (∑ x ∈ I, certificateRho I rho x) := by
          symm
          apply Finset.sum_subset (Finset.subset_univ I)
          intro x _ hx
          simp [certificateRho, hx]
    _ = ∑ x : I, rho x := by
          rw [← Finset.sum_attach]
          simp [certificateRho]

noncomputable def certificateWeight
    (E : CommonExperiment d 𝒳 𝒜) (I : Finset 𝒳) (rho : I → ℝ)
    (p : 𝒳 × 𝒜) : ℝ≥0∞ :=
  ENNReal.ofReal (certificateRho I rho p.1 * E.reference p.1 p.2)

lemma certificateWeight_sum
    (E : CommonExperiment d 𝒳 𝒜) (I : Finset 𝒳) (rho : I → ℝ)
    (hrho : ∀ x, 0 ≤ rho x) (hsum : ∑ x, rho x = 1) :
    ∑ p : 𝒳 × 𝒜, certificateWeight E I rho p = 1 := by
  simp only [certificateWeight]
  rw [Fintype.sum_prod_type]
  calc
    (∑ x : 𝒳, ∑ a : 𝒜,
        ENNReal.ofReal (certificateRho I rho x * E.reference x a)) =
        ∑ x : 𝒳, ENNReal.ofReal (certificateRho I rho x) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [← ENNReal.ofReal_sum_of_nonneg]
          · rw [← Finset.mul_sum, E.reference_isPolicy.2 x, mul_one]
          · intro a _
            exact mul_nonneg (certificateRho_nonneg I rho hrho x)
              (E.reference_isPolicy.1 x a)
    _ = ENNReal.ofReal (∑ x : 𝒳, certificateRho I rho x) := by
          rw [ENNReal.ofReal_sum_of_nonneg]
          intro x _
          exact certificateRho_nonneg I rho hrho x
    _ = 1 := by rw [certificateRho_sum I rho hsum]; simp

noncomputable def certificateSourcePMF
    (E : CommonExperiment d 𝒳 𝒜) (I : Finset 𝒳) (rho : I → ℝ)
    (hrho : ∀ x, 0 ≤ rho x) (hsum : ∑ x, rho x = 1) :
    PMF (𝒳 × 𝒜) :=
  PMF.ofFintype (certificateWeight E I rho)
    (certificateWeight_sum E I rho hrho hsum)

lemma certificateSourcePMF_apply
    (E : CommonExperiment d 𝒳 𝒜) (I : Finset 𝒳) (rho : I → ℝ)
    (hrho : ∀ x, 0 ≤ rho x) (hsum : ∑ x, rho x = 1)
    (x : 𝒳) (a : 𝒜) :
    certificateSourcePMF E I rho hrho hsum (x, a) =
      ENNReal.ofReal (certificateRho I rho x * E.reference x a) := rfl

noncomputable def certificateObservation
    (E : CommonExperiment d 𝒳 𝒜) (theta : Fin d → ℝ)
    (p : 𝒳 × 𝒜) : BanditObservation 𝒳 𝒜 where
  context := p.1
  action := p.2
  reward := ∑ i, E.feature p.1 p.2 i * theta i

lemma certificateObservation_measurable
    (E : CommonExperiment d 𝒳 𝒜) (theta : Fin d → ℝ) :
    Measurable (certificateObservation E theta) := by
  exact measurable_of_finite _

noncomputable def certificateLaw
    (E : CommonExperiment d 𝒳 𝒜) (I : Finset 𝒳)
    (theta : Fin d → ℝ) (rho : I → ℝ)
    (hrho : ∀ x, 0 ≤ rho x) (hsum : ∑ x, rho x = 1)
    (hbound : ∀ x a,
      (∑ i, E.feature x a i * theta i) ∈ Set.Icc (0 : ℝ) 1) :
    BanditLaw E where
  dataMeasure :=
    Measure.map (certificateObservation E theta)
      (certificateSourcePMF E I rho hrho hsum).toMeasure
  isProbability := by
    exact Measure.isProbabilityMeasure_map
      (certificateObservation_measurable E theta).aemeasurable
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
    rw [ae_map_iff
      (certificateObservation_measurable E theta).aemeasurable hset]
    filter_upwards with p
    exact hbound p.1 p.2
  theta := theta

lemma certificateLaw_linearReward
    (E : CommonExperiment d 𝒳 𝒜) (I : Finset 𝒳)
    (theta : Fin d → ℝ) (rho : I → ℝ)
    (hrho : ∀ x, 0 ≤ rho x) (hsum : ∑ x, rho x = 1)
    (hbound : ∀ x a,
      (∑ i, E.feature x a i * theta i) ∈ Set.Icc (0 : ℝ) 1)
    (x : 𝒳) (a : 𝒜) :
    linearReward (certificateLaw E I theta rho hrho hsum hbound) x a =
      ∑ i, E.feature x a i * theta i := rfl

lemma certificateSource_context
    (E : CommonExperiment d 𝒳 𝒜) (I : Finset 𝒳) (rho : I → ℝ)
    (hrho : ∀ x, 0 ≤ rho x) (hsum : ∑ x, rho x = 1)
    (x : 𝒳) :
    (certificateSourcePMF E I rho hrho hsum).toMeasure
        {p : 𝒳 × 𝒜 | p.1 = x} =
      ENNReal.ofReal (certificateRho I rho x) := by
  have hdisj : Pairwise (Function.onFun Disjoint
      (fun a : 𝒜 => ({(x, a)} : Set (𝒳 × 𝒜)))) := by
    intro a b hab
    exact Set.disjoint_singleton.2 fun h => hab (congrArg Prod.snd h)
  rw [show {p : 𝒳 × 𝒜 | p.1 = x} =
      ⋃ a : 𝒜, {(x, a)} by
    ext p
    rcases p with ⟨y, b⟩
    simp [eq_comm]]
  rw [measure_iUnion hdisj (fun _ => MeasurableSet.singleton _)]
  simp_rw [PMF.toMeasure_apply_singleton _
    _ (MeasurableSet.singleton _), certificateSourcePMF_apply]
  rw [tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg]
  · rw [show (∑ a : 𝒜,
        certificateRho I rho x * E.reference x a) =
        certificateRho I rho x by
      rw [← Finset.mul_sum, E.reference_isPolicy.2 x, mul_one]]
  · intro a _
    exact mul_nonneg (certificateRho_nonneg I rho hrho x)
      (E.reference_isPolicy.1 x a)

lemma certificateLaw_contextMass
    (E : CommonExperiment d 𝒳 𝒜) (I : Finset 𝒳)
    (theta : Fin d → ℝ) (rho : I → ℝ)
    (hrho : ∀ x, 0 ≤ rho x) (hsum : ∑ x, rho x = 1)
    (hbound : ∀ x a,
      (∑ i, E.feature x a i * theta i) ∈ Set.Icc (0 : ℝ) 1)
    (x : 𝒳) :
    contextMass (certificateLaw E I theta rho hrho hsum hbound) x =
      certificateRho I rho x := by
  unfold contextMass certificateLaw
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
  rw [Measure.map_apply (certificateObservation_measurable E theta) hset]
  change ((certificateSourcePMF E I rho hrho hsum).toMeasure
      {p : 𝒳 × 𝒜 | p.1 = x}).toReal = certificateRho I rho x
  rw [certificateSource_context E I rho hrho hsum x]
  exact ENNReal.toReal_ofReal (certificateRho_nonneg I rho hrho x)

lemma certificateLaw_cellMass
    (E : CommonExperiment d 𝒳 𝒜) (I : Finset 𝒳)
    (theta : Fin d → ℝ) (rho : I → ℝ)
    (hrho : ∀ x, 0 ≤ rho x) (hsum : ∑ x, rho x = 1)
    (hbound : ∀ x a,
      (∑ i, E.feature x a i * theta i) ∈ Set.Icc (0 : ℝ) 1)
    (x : 𝒳) (a : 𝒜) :
    cellMass (certificateLaw E I theta rho hrho hsum hbound) x a =
      contextMass (certificateLaw E I theta rho hrho hsum hbound) x *
        E.reference x a := by
  unfold cellMass certificateLaw
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
  rw [Measure.map_apply (certificateObservation_measurable E theta) hset]
  have hpre :
      certificateObservation E theta ⁻¹'
          {z : BanditObservation 𝒳 𝒜 |
            z.context = x ∧ z.action = a} = {(x, a)} := by
    ext p
    rcases p with ⟨y, b⟩
    simp [certificateObservation, eq_comm]
  rw [hpre]
  change ((certificateSourcePMF E I rho hrho hsum).toMeasure
      {(x, a)}).toReal =
    contextMass (certificateLaw E I theta rho hrho hsum hbound) x *
      E.reference x a
  rw [PMF.toMeasure_apply_singleton _ _
      (MeasurableSet.singleton (x, a)),
    certificateSourcePMF_apply,
    ENNReal.toReal_ofReal
      (mul_nonneg (certificateRho_nonneg I rho hrho x)
        (E.reference_isPolicy.1 x a)),
    certificateLaw_contextMass E I theta rho hrho hsum hbound x]

lemma certificateLaw_rewardMean
    (E : CommonExperiment d 𝒳 𝒜) (I : Finset 𝒳)
    (theta : Fin d → ℝ) (rho : I → ℝ)
    (hrho : ∀ x, 0 ≤ rho x) (hsum : ∑ x, rho x = 1)
    (hbound : ∀ x a,
      (∑ i, E.feature x a i * theta i) ∈ Set.Icc (0 : ℝ) 1)
    (x : 𝒳) (a : 𝒜)
    (hcell : 0 <
      cellMass (certificateLaw E I theta rho hrho hsum hbound) x a) :
    rewardMean (certificateLaw E I theta rho hrho hsum hbound) x a =
      linearReward (certificateLaw E I theta rho hrho hsum hbound) x a := by
  let P := certificateLaw E I theta rho hrho hsum hbound
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
  have hrewards :
      ∀ᵐ z ∂P.dataMeasure,
        z.reward = linearReward P z.context z.action := by
    change ∀ᵐ z ∂Measure.map (certificateObservation E theta)
      (certificateSourcePMF E I rho hrho hsum).toMeasure,
        z.reward = linearReward P z.context z.action
    have hreward : Measurable
        (fun z : BanditObservation 𝒳 𝒜 => z.reward) := by
      change Measurable[MeasurableSpace.comap
        (fun z : BanditObservation 𝒳 𝒜 =>
          (z.context, z.action, z.reward)) inferInstance] _
      exact (comap_measurable _).snd.snd
    have heqset : MeasurableSet
        {z : BanditObservation 𝒳 𝒜 |
          z.reward = linearReward P z.context z.action} :=
      measurableSet_eq_fun hreward
        ((measurable_of_finite
          (fun p : 𝒳 × 𝒜 => linearReward P p.1 p.2)).comp hpair)
    rw [ae_map_iff
      (certificateObservation_measurable E theta).aemeasurable heqset]
    filter_upwards with p
    rfl
  have heq :
      (∫ z in s, z.reward ∂P.dataMeasure) =
        ∫ _z in s, linearReward P x a ∂P.dataMeasure := by
    apply integral_congr_ae
    apply (ae_restrict_iff' hs).2
    filter_upwards [hrewards] with z hz hzs
    rw [hz, hzs.1, hzs.2]
  unfold rewardMean
  change (∫ z in s, z.reward ∂P.dataMeasure) /
      cellMass P x a = linearReward P x a
  rw [heq, setIntegral_const, smul_eq_mul]
  change (P.dataMeasure.real s * linearReward P x a) /
      cellMass P x a = linearReward P x a
  have hreal : P.dataMeasure.real s = cellMass P x a := rfl
  rw [hreal]
  exact (mul_div_cancel_left₀ _ (ne_of_gt hcell)).trans rfl

end CausalSmith.Stat.ReverseKLTwoCoverage
