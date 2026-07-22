import CausalSmith.Stat.STAT_PolicyRegretMarginOverlap_Research.Basic
import CausalSmith.Mathlib.InformationTheory.ProductChiSquared
import Causalean.Stat.Minimax.ChiSquared

set_option linter.style.longLine false
set_option linter.style.whitespace false

namespace CausalSmith
namespace Stat
namespace PolicyRegretMarginOverlap

open MeasureTheory
open scoped BigOperators

variable {𝒳 Ω : Type*} [MeasurableSpace 𝒳] [MeasurableSpace Ω]

-- @node: lem:witness-membership
lemma witness_membership (alpha gamma C_m u_0 C_o c_o underline_p : ℝ)
    (Pi : Set (Policy ℝ)) (hwin : marginWindow u_0)
    (P : PolicyRegretLaw ℝ)
    (hclass : PolicyRegretLawClass P Pi alpha gamma C_m u_0 C_o c_o underline_p) :
    ∃ N : ℕ, ∀ n ≥ N,
      PolicyRegretLawClass (twoPointWitness n alpha gamma).Pplus Pi alpha gamma C_m u_0 C_o c_o underline_p ∧
      PolicyRegretLawClass (twoPointWitness n alpha gamma).Pminus Pi alpha gamma C_m u_0 C_o c_o underline_p ∧
        (twoPointWitness n alpha gamma).informationRequirement := by
  sorry

-- @node: lem:two-point-divergence
lemma twoPoint_chiSq_divergence (alpha gamma : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ n ≥ N,
      Causalean.Stat.chiSqDiv (twoPointWitness n alpha gamma).Pplus.observedLaw
          (twoPointWitness n alpha gamma).Pminus.observedLaw ≤
        C * (twoPointWitness n alpha gamma).blockMass *
          (twoPointWitness n alpha gamma).q *
            (twoPointWitness n alpha gamma).h ^ (2 : ℕ) ∧
      Causalean.Stat.chiSqDiv (sampleLaw n (twoPointWitness n alpha gamma).Pplus)
        (sampleLaw n (twoPointWitness n alpha gamma).Pminus) ≤ C := by
  sorry

-- @node: lem:regret-separation
lemma twoPoint_regret_separation (alpha gamma : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ pi : Policy ℝ,
      c * Real.rpow (n : ℝ) (-(rStar alpha gamma)) ≤
        max ((twoPointWitness n alpha gamma).Pplus.lawRegret pi)
          ((twoPointWitness n alpha gamma).Pminus.lawRegret pi) := by
  sorry

-- @node: lem:le-cam-two-point-chisq
lemma two_point_testing_error_floor (n : ℕ) (Pplus Pminus : Measure Ω)
    (C_chi : ℝ) :
    (Causalean.Stat.chiSqDiv (iidProductLaw n Pplus) (iidProductLaw n Pminus) ≤ C_chi →
      ∃ c : ℝ, 0 < c ∧ ∀ test : (Fin n → Ω) → Bool,
        c ≤ ((iidProductLaw n Pplus) {sample | test sample = false}).toReal +
              ((iidProductLaw n Pminus) {sample | test sample = true}).toReal) ∧
    (∀ c0 : ℝ, 0 ≤ c0 →
      Causalean.Stat.chiSqDiv Pplus Pminus ≤ c0 / n →
        ∃ c : ℝ, 0 < c ∧ ∀ test : (Fin n → Ω) → Bool,
          c ≤ ((iidProductLaw n Pplus) {sample | test sample = false}).toReal +
                ((iidProductLaw n Pminus) {sample | test sample = true}).toReal) := by
  sorry

-- @node: lem:clip-bias
lemma clip_bias_identity (P : PolicyRegretLaw 𝒳) (q : ℝ)
    (mu0bar mu1bar ebar : 𝒳 → ℝ) (hpos : positivity P) :
    ∀ x : 𝒳,
      let ebarq := clippedPropensity ebar q x
      let Delta1 := mu1bar x - P.mu1 x
      let Delta0 := mu0bar x - P.mu0 x
      (mu1bar x - mu0bar x +
          P.propensity x / ebarq * (P.mu1 x - mu1bar x) -
            (1 - P.propensity x) / (1 - ebarq) * (P.mu0 x - mu0bar x)) -
          P.contrast x =
        (ebarq - P.propensity x) * (Delta1 / ebarq + Delta0 / (1 - ebarq)) := by
  sorry

-- @node: lem:feasible-erm-basic-inequality
lemma feasibleERM_basic_inequality (n : ℕ) (Pi : Set (Policy 𝒳)) (Pi0 : ℕ → Policy 𝒳)
    {K : ℕ} (foldOf : Fin n → Fin K) (sample : Fin n → Observation 𝒳)
    (q : ℝ) (mu0 mu1 e : Fin K → 𝒳 → ℝ) (d_Pi : ℕ)
    (P : PolicyRegretLaw 𝒳)
    (hpolicy : pointwiseMeasurableVCClass Pi d_Pi)
    (hopt : optimalInClass P Pi) :
    (∀ piB ∈ Pi,
      - (1 / n : ℝ) ≤
        empiricalWelfare n sample foldOf q mu0 mu1 e
            (feasibleERM n Pi0 Pi foldOf sample q mu0 mu1 e) -
          empiricalWelfare n sample foldOf q mu0 mu1 e piB) ∧
      - (1 / n : ℝ) ≤
        empiricalWelfare n sample foldOf q mu0 mu1 e
            (feasibleERM n Pi0 Pi foldOf sample q mu0 mu1 e) -
          empiricalWelfare n sample foldOf q mu0 mu1 e P.lawOptimalPolicy := by
  sorry

-- @node: lem:localized-vc-self-bound
lemma localized_vc_self_bound (P : PolicyRegretLaw 𝒳) (Pi : Set (Policy 𝒳))
    (z : Policy 𝒳 → ℝ) (piTilde : Policy 𝒳)
    (alpha B rho delta risk offsetPositivePart : ℝ) (n : ℕ)
    (hrho : rho = Real.rpow (B ^ 2 / (n : ℝ)) (AAlpha alpha) *
      Real.rpow (Real.log ((n : ℝ) + 1)) 1)
    (hpi : piTilde ∈ Pi)
    (hrisk : risk = P.lawRegret piTilde)
    (hB : 1 ≤ B)
    (hn : 1 ≤ n)
    (hdelta_nonneg : 0 ≤ delta)
    (hdelta : delta ≤ 1 / (n : ℝ))
    (hoffsetObject : centeredOffsetProcess P Pi z B offsetPositivePart)
    (hoffset : offsetPositivePart ≤ rho) :
    risk ≤ 2 * |z piTilde| + delta → ∃ C : ℝ, 0 < C ∧ risk ≤ C * (rho + delta) := by
  sorry

-- @node: lem:localized-vc-process-bound
lemma localized_vc_process_bound (P : PolicyRegretLaw 𝒳) (Pi : Set (Policy 𝒳))
    (g : Policy 𝒳 → Observation 𝒳 → ℝ)
    (alpha : ℝ) (d_Pi m : ℕ) (B r localizedProcessBound : ℝ)
    (C_m u_0 : ℝ)
    (hvc : vcLocalizedEnvelope P Pi alpha d_Pi m)
    (hprocess : centeredPolicyProcess P Pi g B r)
    (hmargin : marginTail P alpha C_m u_0)
    (hzero : zeroEffectAgreement P Pi)
    (hbounded : boundedOutcome P)
    (hpolicy : pointwiseMeasurableVCClass Pi d_Pi)
    (hlocalized : localizedProcessBound =
      sSup ((fun pi : Policy 𝒳 => |∫ O, g pi O ∂P.observedLaw|)
        '' {pi | pi ∈ Pi ∧ P.lawRegret pi ≤ r})) :
    ∃ C p : ℝ, 0 < C ∧
      localizedProcessBound ≤
        C * B * Real.rpow (m : ℝ) (-1 / 2) *
          Real.rpow r (alpha / (2 + 2 * alpha)) *
            Real.rpow (Real.log ((m : ℝ) + 1)) p := by
  sorry

-- @node: lem:crossfit-localized-process-reduction
lemma crossfit_localized_process_reduction (P : PolicyRegretLaw 𝒳)
    (Pi : Set (Policy 𝒳)) (gcf : Policy 𝒳 → Observation 𝒳 → ℝ)
    (alpha B r pooledProcessBound : ℝ) (d_Pi K n : ℕ)
    (C_m u_0 : ℝ) (foldOf : Fin n → Fin K)
    (hvc : vcLocalizedEnvelope P Pi alpha d_Pi n)
    (hprocess : centeredPolicyProcess P Pi gcf B r)
    (hmargin : marginTail P alpha C_m u_0)
    (hzero : zeroEffectAgreement P Pi)
    (hbounded : boundedOutcome P)
    (hfold : fixedCrossfitFoldCount K n)
    (hpolicy : pointwiseMeasurableVCClass Pi d_Pi)
    (hiid : iidSample n P.observedLaw (sampleLaw n P))
    (hpooled : pooledProcessBound =
      sSup ((fun pi : Policy 𝒳 => |∫ O, gcf pi O ∂P.observedLaw|)
        '' {pi | pi ∈ Pi ∧ P.lawRegret pi ≤ r})) :
    ∃ C p : ℝ, 0 < C ∧
      pooledProcessBound ≤
        C * B * Real.rpow (n : ℝ) (-1 / 2) *
          Real.rpow r (alpha / (2 + 2 * alpha)) *
            Real.rpow (Real.log ((n : ℝ) + 1)) p := by
  sorry

-- @node: lem:crossfit-localized-offset-control
lemma crossfit_localized_offset_control (P : PolicyRegretLaw 𝒳)
    (Pi : Set (Policy 𝒳)) (zcf : Policy 𝒳 → ℝ)
    (alpha B offsetBound : ℝ) (d_Pi K n : ℕ)
    (C_m u_0 : ℝ) (foldOf : Fin n → Fin K)
    (hiid : iidSample n P.observedLaw (sampleLaw n P))
    (hfold : fixedCrossfitFoldCount K n)
    (hoffset : vcLocalizedOffsetEnvelope P Pi alpha d_Pi n)
    (hprocess : centeredOffsetProcess P Pi zcf B offsetBound)
    (hmargin : marginTail P alpha C_m u_0)
    (hzero : zeroEffectAgreement P Pi)
    (hbounded : boundedOutcome P)
    (hpolicy : pointwiseMeasurableVCClass Pi d_Pi)
    (hpooled : offsetBound =
      sSup ((fun pi : Policy 𝒳 => max (2 * |zcf pi| - P.lawRegret pi / 4) 0) '' Pi)) :
    ∃ C p : ℝ, 0 < C ∧
      offsetBound ≤
        C * Real.rpow (B ^ 2 / n) (AAlpha alpha) *
          Real.rpow (Real.log ((n : ℝ) + 1)) p := by
  sorry

-- @node: lem:clipped-region-localization
lemma clipped_region_localization (P : PolicyRegretLaw 𝒳) (Pi : Set (Policy 𝒳))
    (pi : Policy 𝒳) (alpha gamma C_o c_o q u r u_0 : ℝ)
    (hoverlap : overlapDecay P alpha gamma C_o c_o)
    (hzero : zeroEffectAgreement P Pi)
    (hbounded : boundedOutcome P)
    (hpi : pi ∈ Pi)
    (hr : r = P.lawRegret pi)
    (hu : 0 < u ∧ u ≤ u_0) :
    gamma > 0 → q ≤ c_o * Real.rpow u gamma →
      (P.covariateMeasure ({x | x ∈ disagreementSet P pi ∧
        min (P.propensity x) (1 - P.propensity x) ≤ q})).toReal ≤
          C_o * Real.rpow u alpha * Real.rpow q (1 / gamma) + r / u := by
  sorry

-- @node: lem:localized-clipped-drift-bound
lemma localized_clipped_drift_bound (n : ℕ) (P : PolicyRegretLaw 𝒳) (Pi : Set (Policy 𝒳))
    (pi : Policy 𝒳) (q u r r_mu_n r_e_n alpha gamma C_o c_o underline_p drift : ℝ)
    (bq : 𝒳 → ℝ)
    (mu0bar mu1bar ebar : 𝒳 → ℝ)
    (hnuis : crossfitNuisanceRate P mu0bar mu1bar ebar n r_mu_n r_e_n)
    (hstrict : strictOverlapEndpoint P gamma underline_p)
    (hoverlap : overlapDecay P alpha gamma C_o c_o)
    (hzero : zeroEffectAgreement P Pi)
    (hbounded : boundedOutcome P)
    (hpi : pi ∈ Pi)
    (hq : 0 < q ∧ q ≤ 1 / 2)
    (hr : r = P.lawRegret pi)
    (hbq : ∀ x : 𝒳,
      let ebarq := clippedPropensity ebar q x
      let Delta1 := mu1bar x - P.mu1 x
      let Delta0 := mu0bar x - P.mu0 x
      bq x =
        (ebarq - P.propensity x) * (Delta1 / ebarq + Delta0 / (1 - ebarq)))
    (hdrift : drift = ∫ x, ((if pi x then 1 else 0) -
        (if P.lawOptimalPolicy x then 1 else 0)) * bq x ∂P.covariateMeasure) :
    (gamma > 0 → q ≤ c_o * Real.rpow u gamma →
      ∃ C : ℝ, 0 < C ∧
        |drift| ≤
          C * (r_mu_n * r_e_n / q + r_mu_n * Real.rpow u (alpha / 2) *
            Real.rpow q (1 / (2 * gamma)) + r_mu_n * Real.sqrt (r / u))) ∧
    (gamma = 0 → q ≤ underline_p / 2 →
      ∃ C : ℝ, 0 < C ∧ |drift| ≤ C * (r_mu_n * r_e_n)) := by
  sorry

-- @node: lem:crude-clipped-score-envelope
lemma crude_clipped_score_envelope (P : PolicyRegretLaw 𝒳) (q : ℝ)
    (mu0bar mu1bar ebar : 𝒳 → ℝ)
    (hbounded : boundedOutcome P)
    (hnuisBound : boundedCrossfitNuisances mu0bar mu1bar)
    (hq : 0 < q ∧ q ≤ 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ O : Observation 𝒳,
      |clippedAIPWScore q mu0bar mu1bar ebar O| ≤ C / q ∧
        clippedAIPWScore q mu0bar mu1bar ebar O ^ (2 : ℕ) ≤ (C / q) ^ (2 : ℕ) ∧
          (∀ x : 𝒳,
            ∫ O, clippedAIPWScore q mu0bar mu1bar ebar O ^ (2 : ℕ) ∂P.observedLaw ≤
              (C / q) ^ (2 : ℕ)) ∧
          ∫ O, clippedAIPWScore q mu0bar mu1bar ebar O ^ (2 : ℕ) ∂P.observedLaw ≤
            (C / q) ^ (2 : ℕ) := by
  sorry

-- @node: lem:crude-localized-master-bound
lemma crude_localized_master_bound (n : ℕ) (P : PolicyRegretLaw 𝒳)
    (Pi : Set (Policy 𝒳)) (alpha gamma C_m u_0 C_o c_o underline_p q u r_mu_n r_e_n : ℝ)
    (risk : ℝ) (d_Pi K : ℕ)
    (Pi0 : ℕ → Policy 𝒳) (foldOf : Fin n → Fin K)
    (mu0 mu1 e : Fin K → 𝒳 → ℝ)
    (hclass : PolicyRegretLawClass P Pi alpha gamma C_m u_0 C_o c_o underline_p)
    (hopt : optimalInClass P Pi)
    (hnuis : ∀ k : Fin K, crossfitNuisanceRate P (mu0 k) (mu1 k) (e k) n r_mu_n r_e_n)
    (hpoly : polynomialNuisanceExponents (fun _ => r_mu_n) (fun _ => r_e_n))
    (hpolicy : pointwiseMeasurableVCClass Pi d_Pi)
    (hvc : vcLocalizedEnvelope P Pi alpha d_Pi n)
    (hoffset : vcLocalizedOffsetEnvelope P Pi alpha d_Pi n)
    (hfold : fixedCrossfitFoldCount K n)
    (hboundedNuis : ∀ k : Fin K, boundedCrossfitNuisances (mu0 k) (mu1 k))
    (hiid : iidSample n P.observedLaw (sampleLaw n P))
    (hrisk : risk =
      ∫ sample, P.lawRegret (feasibleERM n Pi0 Pi foldOf sample q mu0 mu1 e) ∂sampleLaw n P) :
    (gamma > 0 → q ≤ c_o * Real.rpow u gamma →
      ∃ C p : ℝ, 0 < C ∧
        risk ≤
        C * (Real.rpow (n : ℝ) (-(rStar alpha gamma)) +
          Real.rpow (n * q ^ 2) (-(AAlpha alpha)) +
            r_mu_n * r_e_n / q +
              r_mu_n * Real.rpow u (alpha / 2) * Real.rpow q (1 / (2 * gamma)) +
                r_mu_n ^ (2 : ℕ) / u) *
          Real.rpow (Real.log ((n : ℝ) + 1)) p) ∧
    (gamma = 0 → q ≤ underline_p / 2 →
      ∃ C p : ℝ, 0 < C ∧
        risk ≤
          C * (Real.rpow (n : ℝ) (-(AAlpha alpha)) + r_mu_n * r_e_n) *
            Real.rpow (Real.log ((n : ℝ) + 1)) p) := by
  sorry

-- @node: lem:clip-balance-exponent
lemma clip_balance_exponent (alpha gamma a c c_o underline_p q0 uBar s t : ℝ)
    (r_mu r_e : ℕ → ℝ)
    (hpoly : polynomialNuisanceExponents r_mu r_e)
    (hschedule : feasibleSchedule alpha gamma a c q0 uBar s t)
    (hwindowSchedule :
      (gamma = 0 ∧ q0 ≤ underline_p / 2 ∧ t = 0) ∨
        (gamma ≠ 0 ∧ q0 ≤ c_o * Real.rpow uBar gamma ∧
          ∃ N : ℕ, ∀ n ≥ N,
            feasibleClipSchedule q0 s n ≤
              c_o * Real.rpow (feasibleMarginSchedule uBar t n) gamma)) :
    (∃ N : ℕ, ∀ n ≥ N,
      gamma = 0 ∨
        feasibleClipSchedule q0 s n ≤
          c_o * Real.rpow (feasibleMarginSchedule uBar t n) gamma) ∧
    phiFeasible alpha gamma a c s t ≤ gJoint alpha gamma a c ∧
      rFeas alpha gamma a c = if gamma = 0 then min (AAlpha alpha) c
        else min (rStar alpha gamma) (gJoint alpha gamma a c) := by
  sorry

end PolicyRegretMarginOverlap
end Stat
end CausalSmith
