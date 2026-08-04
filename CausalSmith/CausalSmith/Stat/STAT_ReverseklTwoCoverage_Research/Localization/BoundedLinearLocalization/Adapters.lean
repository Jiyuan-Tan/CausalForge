import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Localization.ConcentrationCore
import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Localization.BoundedLinearLocalization.LinearExactShellConditional
import CausalSmith.Substrate.UniformGibbsRadiusConcentration

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-!
# Adapters for bounded linear localization

This module supplies the measure transport and design-projector leaves.
-/

namespace CausalSmith.Stat.ReverseKLTwoCoverage.BoundedLinearLocalizationAdapters

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

open CausalSmith.Substrate.MeasurableFiniteLinearERM
open CausalSmith.Stat.ReverseKLTwoCoverage.LinearExactShellTypeFit

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

/-- Paper-local transport of the standard Borel structure.  This is used
through local `letI`s only; it is deliberately not a global instance. -/
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

lemma loggedSampleStandardBorel :
    @StandardBorelSpace (LoggedSample n 𝒳 𝒜) MeasurableSpace.pi := by
  letI : StandardBorelSpace (BanditObservation 𝒳 𝒜) :=
    banditObservation_standardBorel
  infer_instance

private lemma design_measurable :
    Measurable (fun z : BanditObservation 𝒳 𝒜 =>
      (z.context, z.action)) :=
  Measurable.prodMk observationTuple_measurable.fst
    observationTuple_measurable.snd.fst

lemma contextMass_nonneg_local
    (E : CommonExperiment d 𝒳 𝒜) (P : BanditLaw E) (x : 𝒳) :
    0 ≤ contextMass P x :=
  ENNReal.toReal_nonneg

lemma contextMass_sum_one
    (E : CommonExperiment d 𝒳 𝒜) (P : BanditLaw E) :
    ∑ x, contextMass P x = 1 := by
  letI : IsProbabilityMeasure P.dataMeasure := P.isProbability
  have h := sum_measureReal_preimage_singleton
    (μ := P.dataMeasure) (f := fun z : BanditObservation 𝒳 𝒜 => z.context)
    (Finset.univ : Finset 𝒳)
    (fun x _ => observationTuple_measurable.fst (measurableSet_singleton x))
  simpa [contextMass, measureReal_univ_eq_one] using h

lemma productLaw_isProbability
    (E : CommonExperiment d 𝒳 𝒜) (P : BanditLaw E) :
    IsProbabilityMeasure (productLaw E P n) := by
  unfold productLaw
  letI : IsProbabilityMeasure P.dataMeasure := P.isProbability
  infer_instance

lemma oneObservation_design_map
    (E : CommonExperiment d 𝒳 𝒜) (P : BanditLaw E) (C D : ℝ)
    (hshell : ExactShell E P C D) :
    Measure.map (fun z : BanditObservation 𝒳 𝒜 =>
        (z.context, z.action)) P.dataMeasure =
      finiteContextActionLaw (contextMass P) E.reference := by
  classical
  letI : IsProbabilityMeasure P.dataMeasure := P.isProbability
  rw [Measure.ext_iff_singleton]
  rintro ⟨x, a⟩
  rw [Measure.map_apply design_measurable (measurableSet_singleton (x, a))]
  have hpre :
      (fun z : BanditObservation 𝒳 𝒜 => (z.context, z.action)) ⁻¹' {(x, a)} =
        {z | z.context = x ∧ z.action = a} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq,
      Prod.mk.injEq]
  rw [hpre]
  have hfinite :
      P.dataMeasure {z | z.context = x ∧ z.action = a} ≠ ∞ :=
    measure_ne_top _ _
  rw [← ENNReal.ofReal_toReal hfinite]
  change ENNReal.ofReal (cellMass P x a) =
    finiteContextActionLaw (contextMass P) E.reference {(x, a)}
  rw [hshell.referenceLogging x a]
  simp [finiteContextActionLaw, Pi.single_apply, Prod.ext_iff]
  have hinner (x' : 𝒳) :
      (∑ a' : 𝒜, if x' = x ∧ a' = a then
          ENNReal.ofReal (contextMass P x' * E.reference x' a') else 0) =
        if x' = x then
          ENNReal.ofReal (contextMass P x * E.reference x a) else 0 := by
    by_cases hx : x' = x
    · subst x'
      simp
    · simp [hx]
  simp_rw [hinner]
  simp

lemma finiteContextActionLaw_isProbability
    (E : CommonExperiment d 𝒳 𝒜) (P : BanditLaw E) (C D : ℝ)
    (hshell : ExactShell E P C D) :
    IsProbabilityMeasure
      (finiteContextActionLaw (contextMass P) E.reference) := by
  letI : IsProbabilityMeasure P.dataMeasure := P.isProbability
  rw [← oneObservation_design_map E P C D hshell]
  exact Measure.isProbabilityMeasure_map design_measurable.aemeasurable

lemma loggedDesign_map_productLaw
    (E : CommonExperiment d 𝒳 𝒜) (P : BanditLaw E) (C D : ℝ)
    (hshell : ExactShell E P C D) :
    Measure.map
        (loggedDesign :
          LoggedSample n 𝒳 𝒜 → Fin n → 𝒳 × 𝒜)
        (productLaw E P n) =
      iidProduct
        (finiteContextActionLaw (contextMass P) E.reference)
        (finiteContextActionLaw_isProbability E P C D hshell) n := by
  classical
  unfold productLaw iidProduct
  letI : IsProbabilityMeasure P.dataMeasure := P.isProbability
  have hmap := Measure.pi_map_pi
    (μ := fun _ : Fin n => P.dataMeasure)
    (f := fun _ : Fin n => fun z : BanditObservation 𝒳 𝒜 =>
      (z.context, z.action))
    (fun _ => design_measurable.aemeasurable)
  calc
    Measure.map
        (loggedDesign :
          (Fin n → BanditObservation 𝒳 𝒜) → Fin n → 𝒳 × 𝒜)
        (Measure.pi fun _ : Fin n => P.dataMeasure) =
      Measure.pi (fun _ : Fin n =>
        Measure.map (fun z : BanditObservation 𝒳 𝒜 =>
          (z.context, z.action)) P.dataMeasure) := hmap
    _ = Measure.pi (fun _ : Fin n =>
        finiteContextActionLaw (contextMass P) E.reference) := by
      congr 1
      funext i
      exact oneObservation_design_map E P C D hshell

noncomputable def designMatrixOfLoggedDesign
    (E : CommonExperiment d 𝒳 𝒜)
    (w : Fin n → 𝒳 × 𝒜) : Matrix (Fin n) (Fin d) ℝ :=
  fun i j => E.feature (w i).1 (w i).2 j

lemma designMatrix_factor
    (E : CommonExperiment d 𝒳 𝒜) :
    designMatrix E =
      designMatrixOfLoggedDesign E ∘
        (loggedDesign : LoggedSample n 𝒳 𝒜 → Fin n → 𝒳 × 𝒜) := by
  rfl

lemma designMatrix_measurable_coord_designSigma
    (E : CommonExperiment d 𝒳 𝒜) (i : Fin n) (j : Fin d) :
    Measurable[designSigma]
      fun sample : LoggedSample n 𝒳 𝒜 => designMatrix E sample i j := by
  rw [designMatrix_factor E]
  exact (measurable_of_finite
    (fun w : Fin n → 𝒳 × 𝒜 => designMatrixOfLoggedDesign E w i j)).comp
      (comap_measurable loggedDesign)

lemma designProjector_measurable_coord_designSigma
    (E : CommonExperiment d 𝒳 𝒜) (i k : Fin n) :
    Measurable[designSigma]
      fun sample : LoggedSample n 𝒳 𝒜 =>
        rangeProjector (designMatrix E sample) i k :=
  @rangeProjector_measurable_coord n d
    (LoggedSample n 𝒳 𝒜) designSigma
    (designMatrix E) (designMatrix_measurable_coord_designSigma E) i k

lemma designProjector_rankAtMost
    (E : CommonExperiment d 𝒳 𝒜)
    (sample : LoggedSample n 𝒳 𝒜) :
    ProjectorRankAtMost
      (rangeProjector (designMatrix E sample)) d := by
  refine ⟨fun k i => normalizedColumn (designMatrix E sample) k i, ?_⟩
  exact rangeProjector_apply (designMatrix E sample)

end CausalSmith.Stat.ReverseKLTwoCoverage.BoundedLinearLocalizationAdapters
