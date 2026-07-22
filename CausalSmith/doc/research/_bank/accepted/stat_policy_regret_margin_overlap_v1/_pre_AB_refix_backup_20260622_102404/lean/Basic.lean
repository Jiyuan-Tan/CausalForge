/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Policy regret under margin and one-sided overlap decay

Stage-2 sorry-only scaffold for `stat_policy_regret_margin_overlap`.

## File plan / substrate survey

The Causalean PO/CATE substrate was audited for a policy-welfare law with
primitive covariate marginal, propensity, contrast, welfare, and regret. The
available PO/CATE worlds are SCM/counterfactual measure spaces, not the
observed-law abstraction used by this paper. This file therefore defines the
paper-local world `PolicyRegretLaw`; this is the planned bypass-justified path.

The minimax, chi-square, product-measure, ERM, offset-peeling, and rpow modules
are imported only in the files where their statement shapes are used.
-/

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CausalSmith.Mathlib.Analysis.RpowArith

set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false

namespace CausalSmith
namespace Stat
namespace PolicyRegretMarginOverlap

open MeasureTheory
open scoped BigOperators

-- @env: S1
abbrev Policy (𝒳 : Type*) := 𝒳 → Bool

-- @env: S1
structure Observation (𝒳 : Type*) where
  covariate : 𝒳
  treatment : Bool
  outcome : ℝ

instance instMeasurableSpaceObservation {𝒳 : Type*} [MeasurableSpace 𝒳] :
    MeasurableSpace (Observation 𝒳) :=
  MeasurableSpace.comap Observation.covariate inferInstance

-- @env: S1
structure PolicyRegretLaw (𝒳 : Type*) [MeasurableSpace 𝒳] where
  observedLaw : Measure (Observation 𝒳)
  observedIsProbability : IsProbabilityMeasure observedLaw
  covariateMeasure : Measure 𝒳
  isProbability : IsProbabilityMeasure covariateMeasure
  covariateMarginalSemantics : Prop
  binaryTreatmentSemantics : Prop
  boundedOutcomeSupport : Prop
  propensity : 𝒳 → ℝ
  mu0 : 𝒳 → ℝ
  mu1 : 𝒳 → ℝ
  propensitySemantics : Prop
  regressionSemantics : Prop

attribute [instance] PolicyRegretLaw.observedIsProbability
attribute [instance] PolicyRegretLaw.isProbability

-- @env: S2
noncomputable def iidProductLaw {Ω : Type*} [MeasurableSpace Ω] (n : ℕ)
    (P : Measure Ω) : Measure (Fin n → Ω) :=
  Measure.pi (fun _ : Fin n => P)

-- @env: S2
noncomputable def sampleLaw {𝒳 : Type*} [MeasurableSpace 𝒳] (n : ℕ) (P : PolicyRegretLaw 𝒳) :
    Measure (Fin n → Observation 𝒳) :=
  iidProductLaw n P.observedLaw

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

namespace PolicyRegretLaw

-- @node: def:welfare-regret
def contrast (P : PolicyRegretLaw 𝒳) (x : 𝒳) : ℝ :=
  P.mu1 x - P.mu0 x

-- @node: def:welfare-regret
noncomputable def lawOptimalPolicy (P : PolicyRegretLaw 𝒳) : Policy 𝒳 :=
  fun x => decide (0 ≤ P.contrast x)

-- @node: def:welfare-regret
noncomputable def lawWelfare (P : PolicyRegretLaw 𝒳) (pi : Policy 𝒳) : ℝ :=
  ∫ x, (if pi x then (1 : ℝ) else 0) * P.contrast x ∂P.covariateMeasure

-- @node: def:welfare-regret
noncomputable def lawRegret (P : PolicyRegretLaw 𝒳) (pi : Policy 𝒳) : ℝ :=
  P.lawWelfare P.lawOptimalPolicy - P.lawWelfare pi

end PolicyRegretLaw

-- @node: def:disagreement
def disagreementSet (P : PolicyRegretLaw 𝒳) (pi : Policy 𝒳) : Set 𝒳 :=
  {x | pi x ≠ P.lawOptimalPolicy x}

-- @node: def:disagreement
noncomputable def disagreementIndicator (P : PolicyRegretLaw 𝒳) (pi : Policy 𝒳) (x : 𝒳) : ℝ :=
  by
    classical
    exact if x ∈ disagreementSet P pi then 1 else 0

-- @node: ass:iid
def iidSample {Ω : Type*} [MeasurableSpace Ω] (n : ℕ) (P : Measure Ω)
    (sampleLaw : Measure (Fin n → Ω)) : Prop :=
  sampleLaw = iidProductLaw n P

-- @node: ass:consistency
def consistencySUTVA (A : Bool) (Y Y0 Y1 : ℝ) : Prop :=
  Y = (if A then Y1 else Y0)

-- @node: ass:unconfoundedness
def unconfoundedness (conditionalIndependenceGivenX : Prop) : Prop :=
  conditionalIndependenceGivenX

-- @node: ass:bounded-outcome
def boundedOutcome (P : PolicyRegretLaw 𝒳) : Prop :=
  P.boundedOutcomeSupport ∧
    ∀ x, -1 ≤ P.mu0 x ∧ P.mu0 x ≤ 1 ∧ -1 ≤ P.mu1 x ∧ P.mu1 x ≤ 1 ∧
      |P.contrast x| ≤ 2

-- @node: ass:positivity
def positivity (P : PolicyRegretLaw 𝒳) : Prop :=
  ∀ᵐ x ∂P.covariateMeasure, 0 < P.propensity x ∧ P.propensity x < 1

-- @node: ass:margin
def marginTail (P : PolicyRegretLaw 𝒳) (alpha C_m u_0 : ℝ) : Prop :=
  ∀ u, 0 < u → u ≤ u_0 →
    (P.covariateMeasure {x | 0 < |P.contrast x| ∧ |P.contrast x| ≤ u}).toReal ≤
      C_m * Real.rpow u alpha

-- @node: ass:zero-effect
def zeroEffectAgreement (P : PolicyRegretLaw 𝒳) (Pi : Set (Policy 𝒳)) : Prop :=
  (P.covariateMeasure {x | P.contrast x = 0}).toReal = 0 ∨
    ∀ pi ∈ Pi, ∀ᵐ x ∂P.covariateMeasure,
      P.contrast x = 0 → pi x = P.lawOptimalPolicy x

-- @node: ass:overlap-decay
def overlapDecay (P : PolicyRegretLaw 𝒳) (alpha gamma C_o c_o : ℝ) : Prop :=
  ∀ u v, 0 < u → 0 < v → v ≤ c_o * Real.rpow u gamma →
    (P.covariateMeasure
      {x | min (P.propensity x) (1 - P.propensity x) ≤ v ∧
        0 < |P.contrast x| ∧ |P.contrast x| ≤ u}).toReal ≤
      C_o * Real.rpow u alpha *
        (if gamma = 0 then 1 else Real.rpow v (1 / gamma))

-- @node: ass:policy-class
def pointwiseMeasurableVCClass (Pi : Set (Policy 𝒳)) (d_Pi : ℕ) : Prop :=
  ∃ Pi0 : ℕ → Policy 𝒳, (∀ j, Pi0 j ∈ Pi) ∧ (∀ j, Measurable (Pi0 j)) ∧
    (∀ pi ∈ Pi, Measurable pi) ∧ 0 < d_Pi ∧
    (∃ pi0 : Policy 𝒳, pi0 ∈ Pi) ∧
    ∀ pi ∈ Pi, ∃ approx : ℕ → ℕ,
      ∀ x : 𝒳, ∃ N : ℕ, ∀ n ≥ N, Pi0 (approx n) x = pi x

-- @node: ass:optimal-in-class
def optimalInClass (P : PolicyRegretLaw 𝒳) (Pi : Set (Policy 𝒳)) : Prop :=
  P.lawOptimalPolicy ∈ Pi

-- @node: ass:vc-localized-envelope
def centeredPolicyProcess (P : PolicyRegretLaw 𝒳) (Pi : Set (Policy 𝒳))
    (g : Policy 𝒳 → Observation 𝒳 → ℝ) (B r : ℝ) : Prop :=
  0 ≤ B ∧ 0 ≤ r ∧
    (∀ pi ∈ Pi, P.lawRegret pi ≤ r →
      (∀ O, |g pi O| ≤ B) ∧
        ∫ O, g pi O ∂P.observedLaw = 0 ∧
          ∫ O, (g pi O) ^ (2 : ℕ) ∂P.observedLaw ≤
            B ^ (2 : ℕ) * (P.covariateMeasure (disagreementSet P pi)).toReal)

-- @node: ass:vc-localized-offset-envelope
def centeredOffsetProcess (P : PolicyRegretLaw 𝒳) (Pi : Set (Policy 𝒳))
    (z : Policy 𝒳 → ℝ) (B offsetPositivePart : ℝ) : Prop :=
  0 ≤ B ∧ 0 ≤ offsetPositivePart ∧
    offsetPositivePart =
      sSup ((fun pi : Policy 𝒳 => max (2 * |z pi| - P.lawRegret pi / 4) 0) '' Pi)

-- @node: ass:vc-localized-envelope
def vcLocalizedEnvelope (P : PolicyRegretLaw 𝒳) (Pi : Set (Policy 𝒳))
    (alpha : ℝ) (d_Pi n : ℕ) : Prop :=
  pointwiseMeasurableVCClass Pi d_Pi ∧
  ∃ C p : ℝ, 0 < C ∧ 0 ≤ p ∧
    ∀ (sample : Fin n → Observation 𝒳) (g : Policy 𝒳 → Observation 𝒳 → ℝ)
      (localizedSupremum B r : ℝ),
      centeredPolicyProcess P Pi g B r →
        0 ≤ B → 0 ≤ r →
          localizedSupremum =
            sSup ((fun pi : Policy 𝒳 =>
              |(∑ i : Fin n, g pi (sample i)) / (n : ℝ) -
                ∫ O, g pi O ∂P.observedLaw|)
                '' {pi | pi ∈ Pi ∧ P.lawRegret pi ≤ r}) →
          localizedSupremum ≤
            C * B * Real.rpow (n : ℝ) (-1 / 2) *
              Real.rpow r (alpha / (2 + 2 * alpha)) *
                Real.rpow (Real.log ((n : ℝ) + 1)) p

-- @node: ass:margin-window
def marginWindow (u_0 : ℝ) : Prop :=
  0 < u_0 ∧ u_0 < 2

-- @node: ass:nuisance-rate
def crossfitNuisanceRate (P : PolicyRegretLaw 𝒳)
    (muhat0 muhat1 ehat : 𝒳 → ℝ) (n : ℕ) (r_mu_n r_e_n : ℝ) : Prop :=
  0 ≤ r_mu_n ∧ 0 ≤ r_e_n ∧
    ∫ x, (muhat0 x - P.mu0 x) ^ (2 : ℕ) ∂P.covariateMeasure ≤ r_mu_n ^ (2 : ℕ) ∧
    ∫ x, (muhat1 x - P.mu1 x) ^ (2 : ℕ) ∂P.covariateMeasure ≤ r_mu_n ^ (2 : ℕ) ∧
    ∫ x, (ehat x - P.propensity x) ^ (2 : ℕ) ∂P.covariateMeasure ≤ r_e_n ^ (2 : ℕ) ∧
    ∃ Cprod : ℝ, 0 < Cprod ∧
      r_mu_n * r_e_n ≤ Cprod * Real.rpow (n : ℝ) (-1 / 2)

-- @node: ass:strict-overlap-endpoint
def strictOverlapEndpoint (P : PolicyRegretLaw 𝒳) (gamma underline_p : ℝ) : Prop :=
  gamma = 0 → 0 < underline_p ∧ underline_p ≤ 1 / 2 ∧
    ∀ᵐ x ∂P.covariateMeasure,
      underline_p ≤ min (P.propensity x) (1 - P.propensity x)

-- @node: ass:bounded-crossfit-nuisances
def boundedCrossfitNuisances (muhat0 muhat1 : 𝒳 → ℝ) : Prop :=
  ∀ x, -1 ≤ muhat0 x ∧ muhat0 x ≤ 1 ∧ -1 ≤ muhat1 x ∧ muhat1 x ≤ 1

-- @node: ass:polynomial-nuisance-exponents
def polynomialNuisanceExponents (r_mu r_e : ℕ → ℝ) : Prop :=
  ∃ a c C_mu C_prod N : ℝ, 0 ≤ a ∧ (1 / 2 : ℝ) ≤ c ∧ 0 < C_mu ∧
    0 < C_prod ∧ ∀ n : ℕ, N ≤ n →
      r_mu n ≤ C_mu * Real.rpow (n : ℝ) (-a) ∧
        r_mu n * r_e n ≤ C_prod * Real.rpow (n : ℝ) (-c)

-- @node: ass:fixed-crossfit-fold-count
def fixedCrossfitFoldCount (K n : ℕ) : Prop :=
  0 < K ∧ K ≤ n ∧
    ∃ foldSize : Fin K → ℕ,
      (∀ k : Fin K, foldSize k = n / K ∨ foldSize k = n / K + 1) ∧
        (∑ k : Fin K, foldSize k) = n

-- @node: ass:vc-localized-offset-envelope
def vcLocalizedOffsetEnvelope (P : PolicyRegretLaw 𝒳) (Pi : Set (Policy 𝒳))
    (alpha : ℝ) (d_Pi n : ℕ) : Prop :=
  pointwiseMeasurableVCClass Pi d_Pi ∧
  ∃ C p : ℝ, 0 < C ∧ 0 ≤ p ∧
    ∀ (sample : Fin n → Observation 𝒳) (g : Policy 𝒳 → Observation 𝒳 → ℝ)
      (z : Policy 𝒳 → ℝ) (offsetPositivePart B : ℝ),
      centeredOffsetProcess P Pi z B offsetPositivePart →
        0 ≤ B →
          (∀ pi ∈ Pi, z pi =
            (∑ i : Fin n, g pi (sample i)) / (n : ℝ) -
              ∫ O, g pi O ∂P.observedLaw) →
          offsetPositivePart ≤
            C * Real.rpow (B ^ 2 / (n : ℝ)) ((1 + alpha) / (2 + alpha)) *
              Real.rpow (Real.log ((n : ℝ) + 1)) p

-- @node: def:exponents
noncomputable def betaWeak (alpha gamma : ℝ) : ℝ :=
  if gamma = 0 then 0 else alpha * gamma / (alpha + 1)

-- @node: def:exponents
noncomputable def dAlphaGamma (alpha gamma : ℝ) : ℝ :=
  2 + alpha + betaWeak alpha gamma

-- @node: def:exponents
noncomputable def rStar (alpha gamma : ℝ) : ℝ :=
  (1 + alpha) / dAlphaGamma alpha gamma

-- @node: def:feasible-rate
noncomputable def AAlpha (alpha : ℝ) : ℝ :=
  (1 + alpha) / (2 + alpha)

-- @node: def:feasible-rate
noncomputable def phiFeasible (alpha gamma a c s t : ℝ) : ℝ :=
  min (AAlpha alpha * (1 - 2 * s))
    (min (c - s)
      (min (a + s / (2 * gamma) + alpha * t / 2) (2 * a - t)))

-- @node: def:feasible-rate
def feasibleExponentSet (gamma : ℝ) : Set (ℝ × ℝ) :=
  {st : ℝ × ℝ | 0 ≤ st.1 ∧ st.1 ≤ 1 / 2 ∧ 0 ≤ st.2 ∧ st.2 ≤ st.1 / gamma}

-- @node: def:feasible-rate
noncomputable def gJoint (alpha gamma a c : ℝ) : ℝ :=
  sSup ((fun st : ℝ × ℝ => phiFeasible alpha gamma a c st.1 st.2) ''
    feasibleExponentSet gamma)

-- @node: def:feasible-rate
noncomputable def rFeas (alpha gamma a c : ℝ) : ℝ :=
  if gamma = 0 then min (AAlpha alpha) c else min (rStar alpha gamma) (gJoint alpha gamma a c)

-- @node: def:feasible-rate
noncomputable def feasibleClipSchedule (q0 s_feas : ℝ) (n : ℕ) : ℝ :=
  q0 * Real.rpow (n : ℝ) (-s_feas)

-- @node: def:feasible-rate
noncomputable def feasibleMarginSchedule (uBar t_feas : ℝ) (n : ℕ) : ℝ :=
  uBar * Real.rpow (n : ℝ) (-t_feas)

-- @node: def:feasible-rate
def feasibleSchedule (alpha gamma a c q0 uBar s_feas t_feas : ℝ) : Prop :=
  0 ≤ s_feas ∧ s_feas ≤ 1 / 2 ∧ 0 ≤ t_feas ∧
    (gamma = 0 ∨ t_feas ≤ s_feas / gamma) ∧
      (gamma = 0 ∨ phiFeasible alpha gamma a c s_feas t_feas = gJoint alpha gamma a c) ∧
        0 < q0 ∧ q0 ≤ 1 / 2 ∧ 0 < uBar ∧
          (gamma = 0 ∨
            ∃ N : ℕ, ∀ n ≥ N,
              feasibleClipSchedule q0 s_feas n ≤
                Real.rpow (feasibleMarginSchedule uBar t_feas n) gamma)

-- @node: def:feasible-rate
def feasibleScheduleWindow (gamma c_o underline_p q0 uBar s_feas t_feas : ℝ) : Prop :=
  (gamma = 0 ∧ q0 ≤ underline_p / 2 ∧ t_feas = 0) ∨
    (gamma ≠ 0 ∧ q0 ≤ c_o * Real.rpow uBar gamma ∧
      ∃ N : ℕ, ∀ n ≥ N,
        feasibleClipSchedule q0 s_feas n ≤
          c_o * Real.rpow (feasibleMarginSchedule uBar t_feas n) gamma)

-- @node: def:clipped-propensity
noncomputable def clippedPropensity (e : 𝒳 → ℝ) (q : ℝ) (x : 𝒳) : ℝ :=
  min (1 - q) (max q (e x))

-- @node: def:clipped-aipw-score
noncomputable def clippedAIPWScore (q : ℝ) (mu0 mu1 e : 𝒳 → ℝ) (O : Observation 𝒳) : ℝ :=
  let eq := clippedPropensity e q O.covariate
  mu1 O.covariate - mu0 O.covariate +
    (if O.treatment then 1 else 0) / eq * (O.outcome - mu1 O.covariate) -
      (if O.treatment then 0 else 1) / (1 - eq) * (O.outcome - mu0 O.covariate)

-- @node: def:feasible-erm
noncomputable def empiricalWelfare (n : ℕ) (sample : Fin n → Observation 𝒳)
    {K : ℕ} (foldOf : Fin n → Fin K) (q : ℝ)
    (mu0 mu1 e : Fin K → 𝒳 → ℝ) (pi : Policy 𝒳) : ℝ :=
  (∑ i : Fin n,
      (if pi (sample i).covariate then 1 else 0) *
        clippedAIPWScore q (mu0 (foldOf i)) (mu1 (foldOf i)) (e (foldOf i)) (sample i)) / n

-- @node: def:feasible-erm
structure FeasibleERMResult (n : ℕ) (Pi : Set (Policy 𝒳)) where
  rule : (Fin n → Observation 𝒳) → Policy 𝒳
  measurableRule : ∀ x : 𝒳, Measurable (fun sample => rule sample x)
  piValued : ∀ sample, rule sample ∈ Pi
  nearMax : Prop

-- @node: def:feasible-erm
noncomputable def feasibleERM (n : ℕ) (Pi0 : ℕ → Policy 𝒳)
    (Pi : Set (Policy 𝒳))
    {K : ℕ} (foldOf : Fin n → Fin K) (sample : Fin n → Observation 𝒳)
    (q : ℝ) (mu0 mu1 e : Fin K → 𝒳 → ℝ) : Policy 𝒳 := by
  classical
  let good : ℕ → Prop := fun j =>
    ∀ k : ℕ, empiricalWelfare n sample foldOf q mu0 mu1 e (Pi0 k) ≤
      empiricalWelfare n sample foldOf q mu0 mu1 e (Pi0 j) + (1 / n : ℝ)
  exact Pi0 (if h : ∃ j, good j then Nat.find h else 0)

-- @env: S2
structure PolicyEstimator (𝒳 : Type*) [MeasurableSpace 𝒳] (n : ℕ)
    (Pi : Set (Policy 𝒳)) where
  toFun : (Fin n → Observation 𝒳) → Policy 𝒳
  measurableRule : ∀ x : 𝒳, Measurable (fun sample => toFun sample x)
  piValued : ∀ sample, toFun sample ∈ Pi

instance instCoeFunPolicyEstimator (n : ℕ) (Pi : Set (Policy 𝒳)) :
    CoeFun (PolicyEstimator 𝒳 n Pi) (fun _ => (Fin n → Observation 𝒳) → Policy 𝒳) where
  coe est := est.toFun

-- @node: def:minimax-regret
noncomputable def estimatorRegretRisk (n : ℕ) [MeasurableSpace (Observation 𝒳)]
    (sampleLaw : PolicyRegretLaw 𝒳 → Measure (Fin n → Observation 𝒳))
    (Pi : Set (Policy 𝒳)) (P : PolicyRegretLaw 𝒳) (est : PolicyEstimator 𝒳 n Pi) : ℝ :=
  ∫ sample, P.lawRegret (est sample) ∂sampleLaw P

-- @node: def:minimax-regret
noncomputable def minimaxRegret (n : ℕ) [MeasurableSpace (Observation 𝒳)]
    (Pi : Set (Policy 𝒳)) (lawClass : Set (PolicyRegretLaw 𝒳))
    (sampleLaw : PolicyRegretLaw 𝒳 → Measure (Fin n → Observation 𝒳)) : ℝ :=
  sInf ((fun est : PolicyEstimator 𝒳 n Pi =>
    sSup ((fun P => estimatorRegretRisk n sampleLaw Pi P est) '' lawClass)) '' Set.univ)

-- @node: def:upper-risk
def feasibleUpperSideCondition (n K d_Pi : ℕ) (Pi : Set (Policy 𝒳))
    (alpha gamma C_m u_0 C_o c_o underline_p : ℝ)
    (a c q0 uBar s_feas t_feas : ℝ)
    (r_mu r_e : ℕ → ℝ)
    (mu0 mu1 e : Fin K → 𝒳 → ℝ)
    (P : PolicyRegretLaw 𝒳) : Prop :=
  boundedOutcome P ∧ positivity P ∧ marginTail P alpha C_m u_0 ∧
    zeroEffectAgreement P Pi ∧ overlapDecay P alpha gamma C_o c_o ∧
      strictOverlapEndpoint P gamma underline_p ∧ optimalInClass P Pi ∧
        (∀ k : Fin K, crossfitNuisanceRate P (mu0 k) (mu1 k) (e k) n (r_mu n) (r_e n)) ∧
          (∀ k : Fin K, boundedCrossfitNuisances (mu0 k) (mu1 k)) ∧
            polynomialNuisanceExponents r_mu r_e ∧
              pointwiseMeasurableVCClass Pi d_Pi ∧
                vcLocalizedEnvelope P Pi alpha d_Pi n ∧
                  vcLocalizedOffsetEnvelope P Pi alpha d_Pi n ∧
                    fixedCrossfitFoldCount K n ∧
                      feasibleSchedule alpha gamma a c q0 uBar s_feas t_feas ∧
                        feasibleScheduleWindow gamma c_o underline_p q0 uBar s_feas t_feas

-- @node: def:upper-risk
noncomputable def feasibleUpperRisk (n K d_Pi : ℕ) (Pi : Set (Policy 𝒳))
    (alpha gamma C_m u_0 C_o c_o underline_p a c : ℝ)
    (q0 uBar s_feas t_feas : ℝ)
    (r_mu r_e : ℕ → ℝ) [MeasurableSpace (Observation 𝒳)]
    (Pi0 : ℕ → Policy 𝒳) (foldOf : Fin n → Fin K)
    (mu0 mu1 e : Fin K → 𝒳 → ℝ)
    (lawClass : Set (PolicyRegretLaw 𝒳))
    (sampleLaw : PolicyRegretLaw 𝒳 → Measure (Fin n → Observation 𝒳)) : ℝ :=
  sSup ((fun P =>
    ∫ sample,
      P.lawRegret
        (feasibleERM n Pi0 Pi foldOf sample
          (feasibleClipSchedule q0 s_feas n) mu0 mu1 e) ∂sampleLaw P) ''
    {P | P ∈ lawClass ∧
      feasibleUpperSideCondition n K d_Pi Pi alpha gamma C_m u_0 C_o c_o underline_p
        a c q0 uBar s_feas t_feas r_mu r_e mu0 mu1 e P})

-- @node: oeq:feasible-tight
noncomputable def feasibleTightness_openQuestion (K d_Pi : ℕ) (Pi : Set (Policy 𝒳))
    (alpha gamma a c C_m u_0 C_o c_o underline_p : ℝ)
    (q0 uBar s_feas t_feas : ℝ) (r_mu r_e : ℕ → ℝ)
    [MeasurableSpace (Observation 𝒳)]
    (Pi0 : ℕ → Policy 𝒳) (foldOf : ∀ n : ℕ, Fin n → Fin K)
    (mu0 mu1 e : ∀ n : ℕ, Fin K → 𝒳 → ℝ)
    (lawClass : Set (PolicyRegretLaw 𝒳))
    (sampleLawFor : ∀ n : ℕ, PolicyRegretLaw 𝒳 → Measure (Fin n → Observation 𝒳)) :
    Prop :=
  gJoint alpha gamma a c < rStar alpha gamma ∧
    ∃ C p : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n ≥ N,
      feasibleUpperRisk n K d_Pi Pi alpha gamma C_m u_0 C_o c_o underline_p
        a c q0 uBar s_feas t_feas r_mu r_e Pi0 (foldOf n)
        (mu0 n) (mu1 n) (e n) lawClass (sampleLawFor n) ≤
        C * Real.rpow (n : ℝ) (-(rStar alpha gamma)) *
          Real.rpow (Real.log ((n : ℝ) + 1)) p

-- @node: def:law-class
structure PolicyRegretLawClass (P : PolicyRegretLaw 𝒳) (Pi : Set (Policy 𝒳))
    (alpha gamma C_m u_0 C_o c_o underline_p : ℝ) where
  bounded_outcome : boundedOutcome P
  positivity : positivity P
  margin : marginTail P alpha C_m u_0
  zero_effect : zeroEffectAgreement P Pi
  overlap_decay : overlapDecay P alpha gamma C_o c_o
  strict_overlap_endpoint : strictOverlapEndpoint P gamma underline_p

-- @node: def:two-point-witness
structure TwoPointWitness where
  h : ℝ
  q : ℝ
  blockMass : ℝ
  activeBlock : Set ℝ
  tau0 : ℝ
  Pplus : PolicyRegretLaw ℝ
  Pminus : PolicyRegretLaw ℝ
  intervalCovariateSemantics : Prop
  activeBlockMassSemantics : Prop
  activeBlockPropensitySemantics : Prop
  offBlockPropensitySemantics : Prop
  activeTreatedCellMassSemantics : Prop
  activeContrastSemantics : Prop
  offBlockContrastSemantics : Prop
  activeTreatedOutcomeLawSemantics : Prop
  activeTreatedOutcomeSemantics : Prop
  offBlockOutcomeSemantics : Prop
  boundedOutcomeLawSemantics : Prop
  informationRequirement : Prop

-- @node: def:two-point-witness
noncomputable def baseIntervalObservedLaw : PolicyRegretLaw ℝ :=
  { observedLaw := Measure.dirac { covariate := (0 : ℝ), treatment := true, outcome := 0 }
    observedIsProbability := by infer_instance
    covariateMeasure := Measure.dirac (0 : ℝ)
    isProbability := by infer_instance
    covariateMarginalSemantics := True
    binaryTreatmentSemantics := ∀ᵐ O ∂(Measure.dirac { covariate := (0 : ℝ), treatment := true, outcome := 0 } :
      Measure (Observation ℝ)), O.treatment = true ∨ O.treatment = false
    boundedOutcomeSupport := ∀ᵐ O ∂(Measure.dirac { covariate := (0 : ℝ), treatment := true, outcome := 0 } :
      Measure (Observation ℝ)), -1 ≤ O.outcome ∧ O.outcome ≤ 1
    propensity := fun _ => 1 / 2
    mu0 := fun _ => 0
    mu1 := fun _ => 0
    propensitySemantics := True
    regressionSemantics := True }

-- @node: def:two-point-witness
noncomputable def twoPointWitness (n : ℕ) (alpha gamma : ℝ) : TwoPointWitness :=
  let h := Real.rpow (n : ℝ) (-(1 / dAlphaGamma alpha gamma))
  let q := if betaWeak alpha gamma = 0 then 1 / 4 else Real.rpow h (betaWeak alpha gamma)
  let blockMass := Real.rpow h alpha
  let activeBlock : Set ℝ := {x | 0 ≤ x ∧ x ≤ blockMass}
  let tau0 := (3 / 2 : ℝ)
  let Pplus : PolicyRegretLaw ℝ :=
    { baseIntervalObservedLaw with
      propensity := fun x => if x ∈ activeBlock then q else 1 / 2
      mu0 := fun x => if x ∈ activeBlock then 0 else -tau0 / 2
      mu1 := fun x => if x ∈ activeBlock then h else tau0 / 2
      covariateMarginalSemantics := True
      propensitySemantics := ∀ x, (x ∈ activeBlock →
        (if x ∈ activeBlock then q else 1 / 2) = q) ∧ (x ∉ activeBlock →
          (if x ∈ activeBlock then q else 1 / 2) = 1 / 2)
      regressionSemantics := True }
  let Pminus : PolicyRegretLaw ℝ :=
    { baseIntervalObservedLaw with
      propensity := fun x => if x ∈ activeBlock then q else 1 / 2
      mu0 := fun x => if x ∈ activeBlock then 0 else -tau0 / 2
      mu1 := fun x => if x ∈ activeBlock then -h else tau0 / 2
      covariateMarginalSemantics := True
      propensitySemantics := ∀ x, (x ∈ activeBlock →
        (if x ∈ activeBlock then q else 1 / 2) = q) ∧ (x ∉ activeBlock →
          (if x ∈ activeBlock then q else 1 / 2) = 1 / 2)
      regressionSemantics := True }
  { h := h
    q := q
    blockMass := blockMass
    activeBlock := activeBlock
    tau0 := tau0
    Pplus := Pplus
    Pminus := Pminus
    intervalCovariateSemantics :=
      activeBlock = {x | 0 ≤ x ∧ x ≤ blockMass} ∧
        0 ≤ blockMass ∧ blockMass ≤ 1
    activeBlockMassSemantics := (Pplus.covariateMeasure activeBlock).toReal = blockMass
    activeBlockPropensitySemantics := ∀ x ∈ activeBlock, Pplus.propensity x = q ∧ Pminus.propensity x = q
    offBlockPropensitySemantics := ∀ x ∉ activeBlock, Pplus.propensity x = 1 / 2 ∧ Pminus.propensity x = 1 / 2
    activeTreatedCellMassSemantics :=
      (Pplus.observedLaw {O | O.covariate ∈ activeBlock ∧ O.treatment = true}).toReal =
        blockMass * q ∧
      (Pminus.observedLaw {O | O.covariate ∈ activeBlock ∧ O.treatment = true}).toReal =
        blockMass * q
    activeContrastSemantics := ∀ x ∈ activeBlock, Pplus.contrast x = h ∧ Pminus.contrast x = -h
    offBlockContrastSemantics := ∀ x ∉ activeBlock, Pplus.contrast x = tau0 ∧ Pminus.contrast x = tau0
    activeTreatedOutcomeLawSemantics :=
      ∀ x ∈ activeBlock,
        (Pplus.mu1 x = h ∧ Pminus.mu1 x = -h) ∧
          -1 ≤ h ∧ h ≤ 1
    activeTreatedOutcomeSemantics :=
      ∀ x ∈ activeBlock, Pplus.mu0 x = 0 ∧ Pminus.mu0 x = 0 ∧
        Pplus.mu1 x = h ∧ Pminus.mu1 x = -h
    offBlockOutcomeSemantics :=
      ∀ x ∉ activeBlock, Pplus.mu1 x = tau0 / 2 ∧ Pplus.mu0 x = -tau0 / 2 ∧
        Pminus.mu1 x = tau0 / 2 ∧ Pminus.mu0 x = -tau0 / 2
    boundedOutcomeLawSemantics :=
      Pplus.boundedOutcomeSupport ∧ Pminus.boundedOutcomeSupport ∧
        (∀ x ∈ activeBlock, Pplus.mu0 x = 0 ∧ Pminus.mu0 x = 0)
    informationRequirement := 8 * blockMass * q < Real.log 5 }

end PolicyRegretMarginOverlap
end Stat
end CausalSmith
