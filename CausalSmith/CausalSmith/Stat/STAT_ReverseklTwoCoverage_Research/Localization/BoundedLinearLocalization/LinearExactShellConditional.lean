import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Localization.BoundedLinearLocalization.LinearExactShell
import CausalSmith.Substrate.FiniteProductConditionalResidual

namespace CausalSmith.Stat.ReverseKLTwoCoverage.LinearExactShellTypeFit

open MeasureTheory
open CausalSmith.Substrate.FiniteProductConditionalResidual

variable {d n : ℕ} {𝒳 𝒜 : Type*}
  [Fintype 𝒳] [Fintype 𝒜] [DecidableEq 𝒳] [DecidableEq 𝒜]
  [LinearOrder 𝒳] [LinearOrder 𝒜]
  [MeasurableSpace 𝒳] [MeasurableSpace 𝒜]
  [MeasurableSingletonClass 𝒳] [MeasurableSingletonClass 𝒜]

private def observationEquiv :
    BanditObservation 𝒳 𝒜 ≃ 𝒳 × 𝒜 × ℝ where
  toFun z := (z.context, z.action, z.reward)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv z := by cases z; rfl
  right_inv p := by rcases p with ⟨x, a, y⟩; rfl

private lemma banditObservation_standardBorel :
    StandardBorelSpace (BanditObservation 𝒳 𝒜) := by
  let e := observationEquiv (𝒳 := 𝒳) (𝒜 := 𝒜)
  letI : StandardBorelSpace 𝒳 := by infer_instance
  letI : StandardBorelSpace 𝒜 := by infer_instance
  obtain ⟨t', hb', hp'⟩ :=
    (inferInstance : StandardBorelSpace (𝒳 × 𝒜 × ℝ)).polish
  let t : TopologicalSpace (BanditObservation 𝒳 𝒜) :=
    TopologicalSpace.induced e t'
  have hp : @PolishSpace (BanditObservation 𝒳 𝒜) t := by
    letI : TopologicalSpace (𝒳 × 𝒜 × ℝ) := t'
    letI : PolishSpace (𝒳 × 𝒜 × ℝ) := hp'
    exact e.polishSpace_induced
  have hb : @BorelSpace (BanditObservation 𝒳 𝒜) t
      instMeasurableSpaceBanditObservation := by
    constructor
    change MeasurableSpace.comap e inferInstance = @borel _ t
    rw [borel_comap]
    exact congrArg (MeasurableSpace.comap e) hb'.measurable_eq
  exact ⟨⟨t, hb, hp⟩⟩

noncomputable local instance instStandardBorelSpaceBanditObservation :
    StandardBorelSpace (BanditObservation 𝒳 𝒜) :=
  banditObservation_standardBorel

noncomputable local instance instIsProbabilityMeasureProductLaw
    (E : CommonExperiment d 𝒳 𝒜) (P : BanditLaw E) :
    IsProbabilityMeasure (productLaw E P n) := by
  unfold productLaw
  letI : IsProbabilityMeasure P.dataMeasure := P.isProbability
  infer_instance

private lemma oneObservationResidual_measurable
    (E : CommonExperiment d 𝒳 𝒜) (P : BanditLaw E) :
    Measurable fun z : BanditObservation 𝒳 𝒜 =>
      z.reward - linearReward P z.context z.action := by
  apply Measurable.sub
  · exact observationTuple_measurable.snd.snd
  · exact (measurable_of_finite
      (fun w : 𝒳 × 𝒜 => linearReward P w.1 w.2)).comp
        (Measurable.prodMk observationTuple_measurable.fst
          observationTuple_measurable.snd.fst)

private lemma oneObservationResidual_integrable
    (E : CommonExperiment d 𝒳 𝒜) (P : BanditLaw E) (C D : ℝ)
    (hshell : ExactShell E P C D) :
    Integrable (fun z : BanditObservation 𝒳 𝒜 =>
      z.reward - linearReward P z.context z.action) P.dataMeasure := by
  letI : IsProbabilityMeasure P.dataMeasure := P.isProbability
  apply Integrable.of_bound
    (oneObservationResidual_measurable E P).aestronglyMeasurable 1
  filter_upwards [P.reward_mem] with z hz
  have hp := hshell.linearRealizability.1 z.context z.action
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [hz.1, hz.2, hp.1, hp.2]

private lemma oneObservationResidual_fiber
    (E : CommonExperiment d 𝒳 𝒜) (P : BanditLaw E) (C D : ℝ)
    (hshell : ExactShell E P C D) (s : 𝒳 × 𝒜) :
    ∫ z in (fun z : BanditObservation 𝒳 𝒜 =>
        (z.context, z.action)) ⁻¹' {s},
      (z.reward - linearReward P z.context z.action) ∂P.dataMeasure = 0 := by
  let cell : Set (BanditObservation 𝒳 𝒜) :=
    {z | z.context = s.1 ∧ z.action = s.2}
  have hcell :
      (fun z : BanditObservation 𝒳 𝒜 =>
        (z.context, z.action)) ⁻¹' {s} = cell := by
    ext z
    constructor
    · intro h
      exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
    · rintro ⟨hx, ha⟩
      exact Prod.ext hx ha
  rw [hcell]
  letI : IsProbabilityMeasure P.dataMeasure := P.isProbability
  by_cases hpos : 0 < cellMass P s.1 s.2
  · have hmean := hshell.linearRealizability.2 s.1 s.2 hpos
    have hcell_meas : MeasurableSet cell := by
      rw [← hcell]
      exact (Measurable.prodMk observationTuple_measurable.fst
        observationTuple_measurable.snd.fst) (measurableSet_singleton s)
    have hreward_int :
        Integrable (fun z : BanditObservation 𝒳 𝒜 => z.reward)
          P.dataMeasure := by
      apply Integrable.of_bound
        observationTuple_measurable.snd.snd.aestronglyMeasurable 1
      filter_upwards [P.reward_mem] with z hz
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith [hz.1, hz.2]
    have hlinear_int :
        Integrable (fun z : BanditObservation 𝒳 𝒜 =>
          linearReward P z.context z.action) P.dataMeasure := by
      apply Integrable.of_bound
        ((measurable_of_finite
          (fun w : 𝒳 × 𝒜 => linearReward P w.1 w.2)).comp
            (Measurable.prodMk observationTuple_measurable.fst
              observationTuple_measurable.snd.fst)).aestronglyMeasurable 1
      filter_upwards [] with z
      have hz := hshell.linearRealizability.1 z.context z.action
      rw [Real.norm_eq_abs, abs_le]
      change -1 ≤ linearReward P z.context z.action ∧
        linearReward P z.context z.action ≤ 1
      constructor <;> linarith [hz.1, hz.2]
    rw [integral_sub hreward_int.integrableOn hlinear_int.integrableOn]
    have hreward :
        ∫ z in cell, z.reward ∂P.dataMeasure =
          cellMass P s.1 s.2 * linearReward P s.1 s.2 := by
      unfold rewardMean at hmean
      field_simp [ne_of_gt hpos] at hmean
      exact hmean
    rw [hreward]
    have hconst :
        ∫ z in cell, linearReward P z.context z.action ∂P.dataMeasure =
          cellMass P s.1 s.2 * linearReward P s.1 s.2 := by
      have heq :
          (fun z : BanditObservation 𝒳 𝒜 =>
              linearReward P z.context z.action) =ᵐ[P.dataMeasure.restrict cell]
            fun _ => linearReward P s.1 s.2 := by
        filter_upwards [ae_restrict_mem hcell_meas] with z hz
        exact congrArg₂ (linearReward P) hz.1 hz.2
      rw [integral_congr_ae heq, integral_const]
      change (P.dataMeasure.restrict cell).real Set.univ *
          linearReward P s.1 s.2 =
        cellMass P s.1 s.2 * linearReward P s.1 s.2
      change ((P.dataMeasure.restrict cell) Set.univ).toReal *
          linearReward P s.1 s.2 =
        cellMass P s.1 s.2 * linearReward P s.1 s.2
      rw [Measure.restrict_apply_univ]
      rfl
    rw [hconst, sub_self]
  · have hmass : cellMass P s.1 s.2 = 0 :=
      le_antisymm (not_lt.mp hpos) measureReal_nonneg
    have hmeasure : P.dataMeasure cell = 0 := by
      unfold cellMass at hmass
      exact (ENNReal.toReal_eq_zero_iff _).mp hmass |>.resolve_right
        (measure_ne_top _ _)
    rw [show P.dataMeasure.restrict cell = 0 from
      Measure.restrict_eq_zero.mpr hmeasure]
    simp

lemma productLaw_rewardNoise_conditional
    (E : CommonExperiment d 𝒳 𝒜) (P : BanditLaw E) (C D : ℝ)
    (hshell : ExactShell E P C D) :
    (∀ i : Fin n,
      ∀ᵐ sample ∂(productLaw E P n).trim designSigma_le,
        ∫ sample', rewardNoise E P i sample'
          ∂ProbabilityTheory.condExpKernel
            (mΩ := inferInstance) (productLaw E P n) designSigma sample = 0) ∧
      ProbabilityTheory.iCondIndepFun designSigma designSigma_le
        (rewardNoise E P) (μ := productLaw E P n) := by
  letI : IsProbabilityMeasure P.dataMeasure := P.isProbability
  have hdesign :
      Measurable (fun z : BanditObservation 𝒳 𝒜 =>
        (z.context, z.action)) :=
    Measurable.prodMk observationTuple_measurable.fst
      observationTuple_measurable.snd.fst
  have h := finiteProductConditionalResidual
    (ι := Fin n) (S := 𝒳 × 𝒜) (Z := BanditObservation 𝒳 𝒜)
    P.dataMeasure
    (fun z : BanditObservation 𝒳 𝒜 => (z.context, z.action))
    hdesign
    (fun z : BanditObservation 𝒳 𝒜 =>
      z.reward - linearReward P z.context z.action)
    (oneObservationResidual_measurable E P)
    (oneObservationResidual_integrable E P C D hshell)
    (oneObservationResidual_fiber E P C D hshell)
  simpa only [finiteIIDProduct, productLaw, finiteProductDesignSigma,
    designSigma, finiteProductDesign, loggedDesign, finiteProductResidual,
    rewardNoise] using h

end CausalSmith.Stat.ReverseKLTwoCoverage.LinearExactShellTypeFit
