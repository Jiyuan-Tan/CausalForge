/-!
## Native-real finite-experiment van Trees assembly

This section packages the model-specific regularity fields for a finite dominated
experiment and turns sensitivity and information estimates into a real-valued
Bayes squared-risk lower bound.  Its canonical specialization discharges all
one-dimensional prior bookkeeping using the scaled quartic prior.
-/

open MeasureTheory Set

namespace Causalean.Stat.Limit.ObservationDependentVanTrees

/-- Finite-experiment van Trees regularity collects the model-specific normalization,
absolute-continuity, derivative, measurability, and integrability conditions for a
fixed prior and counting-measure observation model. -/
structure FiniteVanTreesModelRegularity
    (X : Type*) [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
    (ell u : ℝ) (w dw : ℝ → ℝ) (p dp g dg : ℝ → X → ℝ) (T : X → ℝ) : Prop where
  /-- Every likelihood mass is nonnegative. -/
  hpnonneg : ∀ θ x, 0 ≤ p θ x
  /-- Every likelihood mass function is normalized on the ambient interval. -/
  hpnorm : ∀ θ ∈ Icc ell u, ∫ x, p θ x ∂Measure.count = 1
  /-- Likelihood sections are integrable on the finite carrier. -/
  hpint : ∀ θ ∈ Icc ell u, Integrable (fun x => p θ x) Measure.count
  /-- Likelihood derivative sections are integrable on the finite carrier. -/
  hdpint : ∀ θ ∈ Icc ell u, Integrable (fun x => dp θ x) Measure.count
  /-- Differentiation of the normalized likelihood integral is valid in the interior. -/
  hdiffUnder : ∀ θ ∈ Ioo ell u,
    HasDerivAt (fun t => ∫ x, p t x ∂Measure.count)
      (∫ x, dp θ x ∂Measure.count) θ
  /-- Almost every likelihood section is absolutely continuous in the parameter. -/
  hpAC : ∀ᵐ x ∂Measure.count,
    AbsolutelyContinuousOnInterval (fun θ => p θ x) ell u
  /-- Almost every observation-dependent target section is absolutely continuous. -/
  hgAC : ∀ᵐ x ∂Measure.count,
    AbsolutelyContinuousOnInterval (fun θ => g θ x) ell u
  /-- The supplied likelihood derivative is valid almost everywhere jointly. -/
  hdp : ∀ᵐ z ∂((parameterMeasure ell u).prod Measure.count),
    HasDerivAt (fun t => p t z.2) (dp z.1 z.2) z.1
  /-- The supplied target derivative is valid almost everywhere jointly. -/
  hdg : ∀ᵐ z ∂((parameterMeasure ell u).prod Measure.count),
    HasDerivAt (fun t => g t z.2) (dg z.1 z.2) z.1
  /-- The derivative-balance field is strongly measurable. -/
  hbalanceSm : AEStronglyMeasurable (derivativeBalanceField w dw p dp g dg T)
    ((parameterMeasure ell u).prod Measure.count)
  /-- The derivative-balance field is integrable. -/
  hbalanceInt : Integrable (derivativeBalanceField w dw p dp g dg T)
    ((parameterMeasure ell u).prod Measure.count)
  /-- The error-score field is strongly measurable. -/
  herrorScoreSm : AEStronglyMeasurable (errorScoreField w dw p dp g T)
    ((parameterMeasure ell u).prod Measure.count)
  /-- The error-score field is integrable. -/
  herrorScoreInt : Integrable (errorScoreField w dw p dp g T)
    ((parameterMeasure ell u).prod Measure.count)
  /-- The sensitivity field is strongly measurable. -/
  hsensitivitySm : AEStronglyMeasurable (sensitivityField w p dg)
    ((parameterMeasure ell u).prod Measure.count)
  /-- The sensitivity field is integrable. -/
  hsensitivityInt : Integrable (sensitivityField w p dg)
    ((parameterMeasure ell u).prod Measure.count)
  /-- The weighted squared-error field is strongly measurable. -/
  herrorSqSm : AEStronglyMeasurable (errorSqField w p g T)
    ((parameterMeasure ell u).prod Measure.count)
  /-- The weighted squared-error field is integrable. -/
  herrorSqInt : Integrable (errorSqField w p g T)
    ((parameterMeasure ell u).prod Measure.count)
  /-- The joint squared-score field is strongly measurable. -/
  hscoreSqSm : AEStronglyMeasurable (scoreSqField w dw p dp)
    ((parameterMeasure ell u).prod Measure.count)
  /-- The joint squared-score field is integrable. -/
  hscoreSqInt : Integrable (scoreSqField w dw p dp)
    ((parameterMeasure ell u).prod Measure.count)
  /-- The lifted prior-score square is strongly measurable. -/
  hpriorJointSqSm : AEStronglyMeasurable
    (fun z : ℝ × X => w z.1 * p z.1 z.2 * (priorScore w dw z.1) ^ 2)
    ((parameterMeasure ell u).prod Measure.count)
  /-- The lifted prior-score square is integrable. -/
  hpriorJointSqInt : Integrable
    (fun z : ℝ × X => w z.1 * p z.1 z.2 * (priorScore w dw z.1) ^ 2)
    ((parameterMeasure ell u).prod Measure.count)
  /-- The lifted likelihood-score square is strongly measurable. -/
  hfisherSqSm : AEStronglyMeasurable
    (fun z : ℝ × X => w z.1 * p z.1 z.2 * (likelihoodScore p dp z.1 z.2) ^ 2)
    ((parameterMeasure ell u).prod Measure.count)
  /-- The lifted likelihood-score square is integrable. -/
  hfisherSqInt : Integrable
    (fun z : ℝ × X => w z.1 * p z.1 z.2 * (likelihoodScore p dp z.1 z.2) ^ 2)
    ((parameterMeasure ell u).prod Measure.count)
  /-- The prior-likelihood score cross field is strongly measurable. -/
  hcrossSm : AEStronglyMeasurable
    (fun z : ℝ × X => w z.1 * p z.1 z.2 *
      (priorScore w dw z.1 * likelihoodScore p dp z.1 z.2))
    ((parameterMeasure ell u).prod Measure.count)
  /-- The prior-likelihood score cross field is integrable. -/
  hcrossInt : Integrable
    (fun z : ℝ × X => w z.1 * p z.1 z.2 *
      (priorScore w dw z.1 * likelihoodScore p dp z.1 z.2))
    ((parameterMeasure ell u).prod Measure.count)

/-- A [nondegenerate parameter interval](hyp:hellu), [finite-model regularity]
(hyp:M), [continuous differentiability](hyp:hwC1), [compact support](hyp:hwsupport),
[a valid prior derivative](hyp:hwderiv), [nonnegativity](hyp:hwnonneg),
[normalization](hyp:hwnorm), [vanishing boundary errors](hyp:hboundary),
[measurability](hyp:hpriorSqSm) and [integrability](hyp:hpriorSqInt) of prior
information, a [nonnegative sensitivity bound](hyp:hs_nonneg) that [lies below average
sensitivity](hyp:hsensitivity), [upper bounds on average likelihood information]
(hyp:hlike) and [prior information](hyp:hprior), and [positive total information]
(hyp:hinfoPos) imply [a native-real Bayes squared-risk lower bound equal to squared
sensitivity divided by the sum of the two information bounds](goal). -/
theorem finite_vanTrees_lower_bound
    {X : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
    {ell u s I P : ℝ} {w dw : ℝ → ℝ} {p dp g dg : ℝ → X → ℝ} {T : X → ℝ}
    (hellu : ell < u) (M : FiniteVanTreesModelRegularity X ell u w dw p dp g dg T)
    (hwC1 : ContDiff ℝ 1 w) (hwsupport : Function.support w ⊆ Icc ell u)
    (hwderiv : ∀ θ, HasDerivAt w (dw θ) θ) (hwnonneg : ∀ θ, 0 ≤ w θ)
    (hwnorm : ∫ θ, w θ ∂parameterMeasure ell u = 1)
    (hboundary : ∀ᵐ x ∂Measure.count,
      w u * p u x * (T x - g u x) = 0 ∧
        w ell * p ell x * (T x - g ell x) = 0)
    (hpriorSqSm : AEStronglyMeasurable
      (fun θ => w θ * (priorScore w dw θ) ^ 2) (parameterMeasure ell u))
    (hpriorSqInt : Integrable
      (fun θ => w θ * (priorScore w dw θ) ^ 2) (parameterMeasure ell u))
    (hs_nonneg : 0 ≤ s)
    (hsensitivity : s ≤ ∫ z, sensitivityField w p dg z
      ∂((parameterMeasure ell u).prod Measure.count))
    (hlike : (∫ θ, w θ * fisherInformation Measure.count p dp θ
      ∂parameterMeasure ell u) ≤ I)
    (hprior : priorInformation ell u w dw ≤ P)
    (hinfoPos : 0 < priorInformation ell u w dw +
      ∫ θ, w θ * fisherInformation Measure.count p dp θ ∂parameterMeasure ell u) :
    s ^ 2 / (I + P) ≤
      ∫ z, errorSqField w p g T z
        ∂((parameterMeasure ell u).prod Measure.count) := by
  have hvanTrees := observation_dependent_van_trees Measure.count hellu
    w dw p dp g dg T hwC1 hwsupport hwderiv hwnonneg hwnorm
    M.hpnonneg M.hpnorm M.hpint M.hdpint M.hdiffUnder M.hpAC M.hgAC M.hdp M.hdg
    hboundary M.hbalanceSm M.hbalanceInt M.herrorScoreSm M.herrorScoreInt
    M.hsensitivitySm M.hsensitivityInt M.herrorSqSm M.herrorSqInt M.hscoreSqSm
    M.hscoreSqInt hpriorSqSm hpriorSqInt M.hpriorJointSqSm M.hpriorJointSqInt
    M.hfisherSqSm M.hfisherSqInt M.hcrossSm M.hcrossInt hinfoPos
  have hs_sq : s ^ 2 ≤
      (∫ z, sensitivityField w p dg z
        ∂((parameterMeasure ell u).prod Measure.count)) ^ 2 := by
    nlinarith
  have hdenom : priorInformation ell u w dw +
        ∫ θ, w θ * fisherInformation Measure.count p dp θ
          ∂parameterMeasure ell u ≤ I + P := by
    linarith
  exact (div_le_div₀ (sq_nonneg _) hs_sq hinfoPos hdenom).trans hvanTrees

/-- A [positive bandwidth](hyp:ha), [strict containment of the left](hyp:hleft) and
[right](hyp:hright) prior-support endpoints, [finite-model regularity](hyp:M), a
[nonnegative sensitivity bound](hyp:hs_nonneg) that [lies below average sensitivity]
(hyp:hsensitivity), a [pointwise likelihood-information bound](hyp:hpointwise), and
[positive total information](hyp:hinfoPos) imply [a native-real Bayes squared-risk
lower bound equal to squared sensitivity divided by likelihood information plus forty
over the squared bandwidth](goal). -/
theorem smoothPrior_finite_vanTrees_lower_bound
    {X : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
    {ell u c a s I : ℝ} {p dp g dg : ℝ → X → ℝ} {T : X → ℝ}
    (ha : 0 < a) (hleft : ell < c - a) (hright : c + a < u)
    (M : FiniteVanTreesModelRegularity X ell u (smoothPrior c a)
      (smoothPriorDeriv c a) p dp g dg T)
    (hs_nonneg : 0 ≤ s)
    (hsensitivity : s ≤ ∫ z, sensitivityField (smoothPrior c a) p dg z
      ∂((parameterMeasure ell u).prod Measure.count))
    (hpointwise : ∀ θ, 0 < smoothPrior c a θ →
      fisherInformation Measure.count p dp θ ≤ I)
    (hinfoPos : 0 < priorInformation ell u (smoothPrior c a) (smoothPriorDeriv c a) +
      ∫ θ, smoothPrior c a θ * fisherInformation Measure.count p dp θ
        ∂parameterMeasure ell u) :
    s ^ 2 / (I + 40 / a ^ 2) ≤
      ∫ z, errorSqField (smoothPrior c a) p g T z
        ∂((parameterMeasure ell u).prod Measure.count) := by
  have hellu : ell < u := by linarith
  have hendpoints := smoothPrior_ambient_endpoints ha hleft hright
  have hboundary : ∀ᵐ x ∂Measure.count,
      smoothPrior c a u * p u x * (T x - g u x) = 0 ∧
        smoothPrior c a ell * p ell x * (T x - g ell x) = 0 := by
    filter_upwards with x
    simp [hendpoints.1, hendpoints.2]
  have hweightedInt : Integrable
      (fun θ => smoothPrior c a θ * fisherInformation Measure.count p dp θ)
      (parameterMeasure ell u) := by
    have h := M.hfisherSqInt.integral_prod_left
    convert h using 1
    funext θ
    rw [fisherInformation, ← integral_const_mul]
    congr 1
    funext x
    ring
  have hlike :
      ∫ θ, smoothPrior c a θ * fisherInformation Measure.count p dp θ
        ∂parameterMeasure ell u ≤ I :=
    average_fisherInformation_le (smoothPrior_nonneg ha)
      (integral_smoothPrior_parameterMeasure ha hleft.le hright.le)
      (smoothPrior_integrable_parameterMeasure ha) hweightedInt hpointwise
  exact finite_vanTrees_lower_bound hellu M (smoothPrior_contDiff ha)
    (support_smoothPrior_subset_Icc ha hleft hright) (hasDerivAt_smoothPrior ha)
    (smoothPrior_nonneg ha)
    (integral_smoothPrior_parameterMeasure ha hleft.le hright.le) hboundary
    (smoothPrior_scoreSq_aestronglyMeasurable ha) (smoothPrior_scoreSq_integrable ha)
    hs_nonneg hsensitivity hlike
    (priorInformation_smoothPrior_le ha hleft.le hright.le) hinfoPos

end Causalean.Stat.Limit.ObservationDependentVanTrees
