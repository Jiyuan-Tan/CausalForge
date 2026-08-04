import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Lower.SameShellLower.Tilt

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace CausalSmith.Stat.ReverseKLTwoCoverage

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

def hardLaw {d : ℕ} (hd : 4 ≤ d)
    (eta C D gamma : ℝ)
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta)
    (v : Fin (hardCoordinateCount d) → Bool)
    (hgamma0 : 0 ≤ gamma)
    (hgammaBeta : gamma ≤ hardBeta D eta gamma)
    (hgammaOne : gamma ≤ 1 - hardBeta D eta gamma) :
    BanditLaw (hardExperiment d hd eta C D heta hD hDC hCexp) :=
  ibBernoulliLaw
    (hardExperiment d hd eta C D heta hD hDC hCexp)
    (hardRho (d := d) (C := C) (D := D) (eta := eta))
    (hardTheta hd D eta gamma v)
    (hardRho_nonneg hd heta hD hDC hCexp)
    (hardRho_sum hd heta hD hDC hCexp)
    (hard_linear_bounds hd v hgamma0 hgammaBeta hgammaOne)

lemma hardLaw_contextMass {d : ℕ} (hd : 4 ≤ d)
    {eta C D gamma : ℝ}
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta)
    (v : Fin (hardCoordinateCount d) → Bool)
    (hgamma0 : 0 ≤ gamma)
    (hgammaBeta : gamma ≤ hardBeta D eta gamma)
    (hgammaOne : gamma ≤ 1 - hardBeta D eta gamma)
    (x : Fin (hardContextCard d C D)) :
    contextMass
      (hardLaw hd eta C D gamma heta hD hDC hCexp v
        hgamma0 hgammaBeta hgammaOne) x =
      hardRho (d := d) (C := C) (D := D) (eta := eta) x := by
  exact ibBernoulliLaw_contextMass _ _ _ _ _ _ x

lemma hardLaw_referenceLogging {d : ℕ} (hd : 4 ≤ d)
    {eta C D gamma : ℝ}
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta)
    (v : Fin (hardCoordinateCount d) → Bool)
    (hgamma0 : 0 ≤ gamma)
    (hgammaBeta : gamma ≤ hardBeta D eta gamma)
    (hgammaOne : gamma ≤ 1 - hardBeta D eta gamma) :
    ReferenceLogging
      (hardExperiment d hd eta C D heta hD hDC hCexp)
      (hardLaw hd eta C D gamma heta hD hDC hCexp v
        hgamma0 hgammaBeta hgammaOne) := by
  exact ibBernoulliLaw_referenceLogging _ _ _ _ _ _

lemma ibBernoulliLaw_conditionalCell
    {d : ℕ} {𝒳 𝒜 : Type*}
    [Fintype 𝒳] [Fintype 𝒜] [DecidableEq 𝒳] [DecidableEq 𝒜]
    [MeasurableSpace 𝒳] [MeasurableSpace 𝒜]
    [MeasurableSingletonClass 𝒳] [MeasurableSingletonClass 𝒜]
    (E : CommonExperiment d 𝒳 𝒜) (rho : 𝒳 → ℝ)
    (theta : Fin d → ℝ)
    (hrho : ∀ x, 0 ≤ rho x) (hrhosum : ∑ x, rho x = 1)
    (hbound : ∀ x a,
      (∑ i, E.feature x a i * theta i) ∈ Set.Icc (0 : ℝ) 1)
    (x : 𝒳) (a : 𝒜) :
    ConditionalBernoulliCell E
      (ibBernoulliLaw E rho theta hrho hrhosum hbound) x a
      (linearReward
        (ibBernoulliLaw E rho theta hrho hrhosum hbound) x a) := by
  have hcontext : Measurable
      (fun z : BanditObservation 𝒳 𝒜 => z.context) :=
    (comap_measurable _).fst
  have haction : Measurable
      (fun z : BanditObservation 𝒳 𝒜 => z.action) :=
    (comap_measurable _).snd.fst
  have hreward : Measurable
      (fun z : BanditObservation 𝒳 𝒜 => z.reward) :=
    (comap_measurable _).snd.snd
  constructor
  · have hcx : MeasurableSet
        {z : BanditObservation 𝒳 𝒜 | z.context = x} :=
      (measurableSet_singleton x).preimage hcontext
    have haa : MeasurableSet
        {z : BanditObservation 𝒳 𝒜 | z.action = a} :=
      (measurableSet_singleton a).preimage haction
    have hr0 : MeasurableSet
        {z : BanditObservation 𝒳 𝒜 | z.reward = 0} :=
      (measurableSet_singleton (0 : ℝ)).preimage hreward
    have hr1 : MeasurableSet
        {z : BanditObservation 𝒳 𝒜 | z.reward = 1} :=
      (measurableSet_singleton (1 : ℝ)).preimage hreward
    have htarget : MeasurableSet
        {z : BanditObservation 𝒳 𝒜 |
          z.context = x → z.action = a →
            z.reward = 0 ∨ z.reward = 1} := by
      convert (hcx.inter haa).compl.union (hr0.union hr1) using 1
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_compl_iff,
        Set.mem_inter_iff, not_and_or]
      tauto
    dsimp [ibBernoulliLaw]
    rw [ae_map_iff ibObservation_measurable.aemeasurable htarget]
    filter_upwards with p
    rcases p with ⟨y, b, s⟩
    cases s <;> simp [ibObservation]
  · let P := ibBernoulliLaw E rho theta hrho hrhosum hbound
    let S : Set (BanditObservation 𝒳 𝒜) :=
      {z | z.context = x ∧ z.action = a ∧ z.reward = 1}
    have hS : MeasurableSet S := by
      simpa only [S, Set.preimage, Set.mem_singleton_iff, Prod.mk.injEq,
        and_assoc] using
        (measurableSet_singleton (x, (a, (1 : ℝ)))).preimage
          (comap_measurable
            (fun z : BanditObservation 𝒳 𝒜 =>
              (z.context, z.action, z.reward)))
    have hpre :
        ibObservation ⁻¹' S = {(x, (a, true))} := by
      ext p
      rcases p with ⟨y, b, s⟩
      cases s <;> simp [S, ibObservation]
    change
      ((Measure.map ibObservation
          (ibBernoulliPMF E rho
            (fun y b => ∑ i, E.feature y b i * theta i)
            hrho hrhosum hbound).toMeasure) S).toReal =
        cellMass P x a * linearReward P x a
    rw [Measure.map_apply ibObservation_measurable hS, hpre,
      PMF.toMeasure_apply_singleton _ _
        (MeasurableSet.singleton (x, (a, true))),
      ibBernoulliPMF_apply]
    rw [ENNReal.toReal_ofReal]
    · rw [ibBernoulliLaw_cellMass, ibBernoulliLaw_contextMass]
      rfl
    · exact mul_nonneg
        (mul_nonneg (hrho x) (E.reference_isPolicy.1 x a))
        (hbound x a).1

lemma hardLaw_conditionalCell {d : ℕ} (hd : 4 ≤ d)
    {eta C D gamma : ℝ}
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta)
    (v : Fin (hardCoordinateCount d) → Bool)
    (hgamma0 : 0 ≤ gamma)
    (hgammaBeta : gamma ≤ hardBeta D eta gamma)
    (hgammaOne : gamma ≤ 1 - hardBeta D eta gamma) :
    ∀ x a, ConditionalBernoulliCell
      (hardExperiment d hd eta C D heta hD hDC hCexp)
      (hardLaw hd eta C D gamma heta hD hDC hCexp v
        hgamma0 hgammaBeta hgammaOne) x a
      (linearReward
        (hardLaw hd eta C D gamma heta hD hDC hCexp v
          hgamma0 hgammaBeta hgammaOne) x a) := by
  exact ibBernoulliLaw_conditionalCell _ _ _ _ _ _

lemma hardLaw_family_injective {d : ℕ} (hd : 4 ≤ d)
    {eta C D gamma : ℝ}
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta)
    (hgamma : 0 < gamma)
    (hgammaBeta : gamma ≤ hardBeta D eta gamma)
    (hgammaOne : gamma ≤ 1 - hardBeta D eta gamma) :
    Function.Injective
      (fun v : Fin (hardCoordinateCount d) → Bool =>
        hardLaw hd eta C D gamma heta hD hDC hCexp v
          hgamma.le hgammaBeta hgammaOne) := by
  intro v w hvw
  funext j
  have htheta := congrArg BanditLaw.theta hvw
  have hcoord := congrFun htheta
    (hardBasisEquiv hd (Sum.inr (Sum.inr (Sum.inl j))))
  change hardTheta hd D eta gamma v
      (hardBasisEquiv hd (Sum.inr (Sum.inr (Sum.inl j)))) =
    hardTheta hd D eta gamma w
      (hardBasisEquiv hd (Sum.inr (Sum.inr (Sum.inl j)))) at hcoord
  cases hv : v j <;> cases hw : w j
  · rfl
  · simp [hardTheta, hv, hw] at hcoord
    nlinarith [Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)]
  · simp [hardTheta, hv, hw] at hcoord
    nlinarith [Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)]
  · rfl

end

end CausalSmith.Stat.ReverseKLTwoCoverage
