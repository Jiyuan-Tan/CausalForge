import CausalSmith.Stat.STAT_SaPlmCumulantConverse_Research.Basic
import CausalSmith.Stat.STAT_SaPlmCumulantConverse_Research.Helpers.AffineGaussianOutcomePath
import CausalSmith.Stat.STAT_SaPlmCumulantConverse_Research.Helpers.AffineGaussianSubGaussian
import CausalSmith.Stat.STAT_SaPlmCumulantConverse_Research.Helpers.AffineGaussianKL
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Causalean.Stat.Minimax.Pinsker
import Causalean.Stat.Minimax.MinimaxRisk

/-!
# Non-Gaussian hard submodel
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace CausalSmith.Stat.SaPlmCumulantConverse

variable {Xspace : Type*} [MeasurableSpace Xspace]

/-- Symmetric clipping used only to reduce arbitrary estimators to bounded
ones in the two-point lower bound. -/
-- @node: hardSubmodelClip
def hardSubmodelClip (R x : ℝ) : ℝ := min (max x (-R)) R

/-- For [a nonnegative clipping level](hyp:hR) and [a target whose absolute value does not
exceed it](hyp:ht), [clipping any real number symmetrically to that level never increases its
squared distance to the target](goal). Restricting attention to estimators bounded by the
clipping level therefore costs nothing in the two-point lower bound. -/
-- @node: hardSubmodelClip_sq_sub_le
lemma hardSubmodelClip_sq_sub_le (R x t : ℝ) (hR : 0 ≤ R) (ht : |t| ≤ R) :
    (hardSubmodelClip R x - t) ^ 2 ≤ (x - t) ^ 2 := by
  rw [abs_le] at ht
  unfold hardSubmodelClip
  by_cases hxlo : x < -R
  · rw [max_eq_right hxlo.le, min_eq_left (neg_le_self hR)]
    nlinarith
  · have hxlo' : -R ≤ x := le_of_not_gt hxlo
    by_cases hxhi : R < x
    · rw [max_eq_left hxlo', min_eq_right hxhi.le]
      nlinarith
    · rw [max_eq_left hxlo', min_eq_left (le_of_not_gt hxhi)]

/-- A pair of class members with finite KL budget gives an `ENNReal` lower
bound for the local class-indexed minimax risk. -/
-- @node: minimaxRiskOn_two_point_lower
lemma minimaxRiskOn_two_point_lower
    (p : Parameters) (n : ℕ) (laws : Set (Model (Xspace := Xspace) p))
    (m0 m1 : Model (Xspace := Xspace) p) (hm0 : m0 ∈ laws) (hm1 : m1 ∈ laws)
    (R cK : ℝ) (hR : 0 ≤ R) (ht0 : |m0.theta0| ≤ R) (ht1 : |m1.theta0| ≤ R)
    (hbody : ∀ T : (Fin n → Obs Xspace) → ℝ, Measurable T →
      Integrable (fun s ↦ (T s - m0.theta0) ^ 2) (iidLaw m0 n) →
      Integrable (fun s ↦ (T s - m1.theta0) ^ 2) (iidLaw m1 n) →
      cK * (m1.theta0 - m0.theta0) ^ 2 ≤
        max (∫ s, (T s - m0.theta0) ^ 2 ∂iidLaw m0 n)
          (∫ s, (T s - m1.theta0) ^ 2 ∂iidLaw m1 n)) :
    ENNReal.ofReal (cK * (m1.theta0 - m0.theta0) ^ 2) ≤ minimaxRiskOn p n laws := by
  rw [minimaxRiskOn]
  refine le_iInf fun est ↦ ?_
  let T : (Fin n → Obs Xspace) → ℝ := fun s ↦ hardSubmodelClip R (est.1 s)
  have hT : Measurable T := by
    exact (est.2.max measurable_const).min measurable_const
  have hTbd : ∀ s, T s ∈ Set.Icc (-R) R := by
    intro s
    dsimp [T, hardSubmodelClip]
    exact ⟨le_min (le_max_right _ _) (neg_le_self hR), min_le_right _ _⟩
  letI : IsProbabilityMeasure (iidLaw m0 n) := by
    unfold iidLaw
    infer_instance
  letI : IsProbabilityMeasure (iidLaw m1 n) := by
    unfold iidLaw
    infer_instance
  have hInt0 : Integrable (fun s ↦ (T s - m0.theta0) ^ 2) (iidLaw m0 n) :=
    Causalean.Stat.mse_integrable_of_estimator_bound _ T hT hR hTbd
  have hInt1 : Integrable (fun s ↦ (T s - m1.theta0) ^ 2) (iidLaw m1 n) :=
    Causalean.Stat.mse_integrable_of_estimator_bound _ T hT hR hTbd
  have hlc := hbody T hT hInt0 hInt1
  have hrisk0 : ENNReal.ofReal (∫ s, (T s - m0.theta0) ^ 2 ∂iidLaw m0 n) ≤
      mseRisk m0 n est.1 := by
    rw [ofReal_integral_eq_lintegral_ofReal hInt0
      (Filter.Eventually.of_forall fun _ ↦ sq_nonneg _)]
    apply lintegral_mono
    intro s
    exact ENNReal.ofReal_le_ofReal (hardSubmodelClip_sq_sub_le R _ _ hR ht0)
  have hrisk1 : ENNReal.ofReal (∫ s, (T s - m1.theta0) ^ 2 ∂iidLaw m1 n) ≤
      mseRisk m1 n est.1 := by
    rw [ofReal_integral_eq_lintegral_ofReal hInt1
      (Filter.Eventually.of_forall fun _ ↦ sq_nonneg _)]
    apply lintegral_mono
    intro s
    exact ENNReal.ofReal_le_ofReal (hardSubmodelClip_sq_sub_le R _ _ hR ht1)
  have hpair : ENNReal.ofReal (cK * (m1.theta0 - m0.theta0) ^ 2) ≤
      max (mseRisk m0 n est.1) (mseRisk m1 n est.1) := by
    calc
      ENNReal.ofReal (cK * (m1.theta0 - m0.theta0) ^ 2) ≤
          ENNReal.ofReal (max (∫ s, (T s - m0.theta0) ^ 2 ∂iidLaw m0 n)
            (∫ s, (T s - m1.theta0) ^ 2 ∂iidLaw m1 n)) :=
        ENNReal.ofReal_le_ofReal hlc
      _ = max (ENNReal.ofReal (∫ s, (T s - m0.theta0) ^ 2 ∂iidLaw m0 n))
          (ENNReal.ofReal (∫ s, (T s - m1.theta0) ^ 2 ∂iidLaw m1 n)) :=
        ENNReal.ofReal_max _ _
      _ ≤ max (mseRisk m0 n est.1) (mseRisk m1 n est.1) := max_le_max hrisk0 hrisk1
  refine hpair.trans (max_le ?_ ?_)
  · exact (le_iSup (fun _ : m0 ∈ laws ↦ mseRisk m0 n est.1) hm0).trans
      (le_iSup (fun m : Model (Xspace := Xspace) p ↦
        ⨆ (_ : m ∈ laws), mseRisk m n est.1) m0)
  · exact (le_iSup (fun _ : m1 ∈ laws ↦ mseRisk m1 n est.1) hm1).trans
      (le_iSup (fun m : Model (Xspace := Xspace) p ↦
        ⨆ (_ : m ∈ laws), mseRisk m n est.1) m1)

/-- Both the broad spectral class and the full published ACE class contain
ACE-preserving fixed-innovation paths with quadratic local KL divergence; the
second path yields the full-class `c / n` minimax converse. -/
-- @node: lem:non-gaussian-hard-submodel
lemma non_gaussian_hard_submodel
    (r : ℕ) (delta Ctheta Cg Cq psieta psixi : ℝ) (hpsixi : 0 < psixi) :
    ∃ c0 C0 tau cACE : ℝ,
      0 < c0 ∧ 0 < C0 ∧ 0 < tau ∧ tau ≤ psixi ∧ 0 < cACE ∧
      ∀ (p : Parameters), p.r = r → p.delta = delta → p.Ctheta = Ctheta →
        p.Cg = Cg → p.Cq = Cq → p.psieta = psieta → p.psixi = psixi →
      ∀ n : ℕ, 1 ≤ n →
      ((∃ base : Model (Xspace := Xspace) p, NonGaussianClass p n base) →
      ∃ (base : Model (Xspace := Xspace) p) (family : ℝ → Model (Xspace := Xspace) p),
        NonGaussianClass p n base ∧
        (∀ theta, |theta| ≤ c0 → NonGaussianClass p n (family theta)) ∧
        (∀ theta, |theta| ≤ c0 → (family theta).theta0 = theta) ∧
        (∀ theta, |theta| ≤ c0 →
          (family theta).P.map (fun o ↦ (covariate o, treatment o)) =
            base.P.map (fun o ↦ (covariate o, treatment o))) ∧
        (∀ theta, |theta| ≤ c0 →
          (family theta).g0 = base.g0 ∧ (family theta).q0 = base.q0 ∧
          (∀ x, barG p (family theta) n x = barG p base n x) ∧
          (∀ x, barQ p (family theta) n x = barQ p base n x)) ∧
        (∀ theta, |theta| ≤ c0 →
          (family theta).P.map (xi p (family theta)) =
              gaussianReal 0 ⟨tau ^ 2, sq_nonneg tau⟩ ∧
            IndepFun (xi p (family theta))
              (fun o ↦ (covariate o, treatment o)) (family theta).P) ∧
        (∀ theta, |theta| ≤ c0 →
          ∀ᵐ o ∂(family theta).P,
            outcome o = base.q0 (covariate o) + theta * eta p (family theta) o +
              xi p (family theta) o) ∧
        (∀ (theta0 theta1 h : ℝ),
          |theta0| ≤ c0 → |theta1| ≤ c0 →
          |theta1 - theta0| = h / Real.sqrt n →
          InformationTheory.klDiv (iidLaw (family theta0) n)
            (iidLaw (family theta1) n) ≤ ENNReal.ofReal (C0 * h ^ 2)) ) ∧
        (∀ aceBase : Model (Xspace := Xspace) p,
          JmsAceClass p n aceBase →
          ∃ aceFamily : ℝ → Model (Xspace := Xspace) p,
            (∀ theta, |theta| ≤ c0 → JmsAceClass p n (aceFamily theta)) ∧
            (∀ theta, |theta| ≤ c0 → (aceFamily theta).theta0 = theta) ∧
            (∀ theta, |theta| ≤ c0 →
              (aceFamily theta).P.map (fun o ↦ (covariate o, treatment o)) =
                aceBase.P.map (fun o ↦ (covariate o, treatment o))) ∧
            (∀ theta, |theta| ≤ c0 →
              (aceFamily theta).g0 = aceBase.g0 ∧
              (aceFamily theta).q0 = aceBase.q0 ∧
              (∀ x, barG p (aceFamily theta) n x = barG p aceBase n x) ∧
              (∀ x, barQ p (aceFamily theta) n x = barQ p aceBase n x) ∧
              eta p (aceFamily theta) = eta p aceBase ∧
              TreatmentCodeRadiusLrAt p (aceFamily theta) n ∧
              OutcomeCodeRadiusLrAt p (aceFamily theta) n) ∧
            (∀ theta, |theta| ≤ c0 →
              (aceFamily theta).P.map (xi p (aceFamily theta)) =
                gaussianReal 0 ⟨tau ^ 2, sq_nonneg tau⟩ ∧
              IndepFun (xi p (aceFamily theta))
                (fun o ↦ (covariate o, treatment o)) (aceFamily theta).P) ∧
            (∀ theta, |theta| ≤ c0 →
              ∀ᵐ o ∂(aceFamily theta).P,
                outcome o = aceBase.q0 (covariate o) +
                  theta * eta p (aceFamily theta) o + xi p (aceFamily theta) o) ∧
            ∀ (theta0 theta1 h : ℝ),
              |theta0| ≤ c0 → |theta1| ≤ c0 →
              |theta1 - theta0| = h / Real.sqrt n →
              InformationTheory.klDiv (iidLaw (aceFamily theta0) n)
                (iidLaw (aceFamily theta1) n) ≤ ENNReal.ofReal (C0 * h ^ 2)) ∧
        (∀ gbar qbar : Xspace → ℝ,
          (∃ aceBase : Model (Xspace := Xspace) p,
            JmsAceClass p n aceBase ∧ barG p aceBase n = gbar ∧
              barQ p aceBase n = qbar) →
            ENNReal.ofReal (cACE / n) ≤
              minimaxRiskOn p n {m : Model (Xspace := Xspace) p |
                JmsAceClass p n m ∧ barG p m n = gbar ∧ barQ p m n = qbar}) := by
  let c0 : ℝ := if 0 < Ctheta then min Ctheta 1 else 1
  let C0 : ℝ := max 1 (16 * psieta ^ 2 / psixi ^ 2)
  let tau : ℝ := psixi / 4
  let K : ℝ := C0 * c0 ^ 2
  obtain ⟨cK, hcK, hlecam⟩ := Causalean.Stat.Minimax.le_cam_two_point_mse K
  refine ⟨c0, C0, tau, cK * c0 ^ 2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [c0]
    split_ifs with h
    · exact lt_min h zero_lt_one
    · norm_num
  · dsimp [C0]
    exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  · dsimp [tau]
    linarith
  · dsimp [tau]
    linarith
  · apply mul_pos hcK
    apply sq_pos_of_pos
    dsimp [c0]
    split_ifs with h
    · exact lt_min h zero_lt_one
    · norm_num
  intro p hr hdelta hCtheta hCg hCq hpsieta hp
  subst r; subst delta; subst Ctheta; subst Cg; subst Cq; subst psieta; subst psixi
  intro n hn
  have hc0_le : c0 ≤ p.Ctheta := by
    simp only [c0, if_pos p.constants_pos.1]
    exact min_le_left _ _
  have hc0_pos : 0 < c0 := by
    simp only [c0, if_pos p.constants_pos.1]
    exact lt_min p.constants_pos.1 zero_lt_one
  have htau_pos : 0 < tau := by dsimp [tau]; linarith [p.constants_pos.2.2.2.2.1]
  have hC0_coeff : 16 * p.psieta ^ 2 / p.psixi ^ 2 ≤ C0 := by
    exact le_max_right _ _
  have hKLpath : ∀ (base : Model (Xspace := Xspace) p),
      EtaSubGaussian p base → ∀ theta0 theta1 h : ℝ,
      |theta0| ≤ c0 → |theta1| ≤ c0 →
      |theta1 - theta0| = h / Real.sqrt n →
      InformationTheory.klDiv
        (iidLaw (affineGaussianModel base theta0 tau) n)
        (iidLaw (affineGaussianModel base theta1 tau) n) ≤
        ENNReal.ofReal (C0 * h ^ 2) := by
    intro base heta theta0 theta1 h ht0 ht1 hsep
    refine (affineGaussianModel_iid_kl_le base n heta theta0 theta1 tau htau_pos).trans ?_
    apply ENNReal.ofReal_le_ofReal
    have hnreal : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
    have hsqrt : (Real.sqrt n) ^ 2 = (n : ℝ) := Real.sq_sqrt hnreal.le
    have hsep_sq : (theta1 - theta0) ^ 2 = h ^ 2 / (n : ℝ) := by
      rw [← sq_abs (theta1 - theta0), hsep, div_pow, hsqrt]
    dsimp [tau]
    rw [hsep_sq]
    have hpsi : 0 < p.psixi := p.constants_pos.2.2.2.2.1
    have hcoeff0 : 0 ≤ 16 * p.psieta ^ 2 / p.psixi ^ 2 := by positivity
    calc
      (n : ℝ) * ((h ^ 2 / (n : ℝ) * (2 * p.psieta ^ 2)) /
        (2 * (p.psixi / 4) ^ 2)) =
          (16 * p.psieta ^ 2 / p.psixi ^ 2) * h ^ 2 := by
            field_simp [ne_of_gt hnreal, ne_of_gt hpsi]
            ring
      _ ≤ C0 * h ^ 2 := mul_le_mul_of_nonneg_right hC0_coeff (sq_nonneg _)
  constructor
  · rintro ⟨base, hbase⟩
    refine ⟨base, fun theta ↦ affineGaussianModel base theta tau, hbase, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro theta htheta
      exact affineGaussianModel_nonGaussianClass_quarter base n hbase theta
        (htheta.trans hc0_le)
    · intro theta _
      rfl
    · intro theta _
      exact affineGaussianModel_map_xt base theta tau
    · intro theta _
      exact ⟨rfl, rfl, fun _ ↦ rfl, fun _ ↦ rfl⟩
    · intro theta _
      exact ⟨affineGaussianModel_map_xi base theta tau,
        affineGaussianModel_indep_xi_xt base theta tau⟩
    · intro theta _
      filter_upwards with o
      simp only [xi, affineGaussianModel_theta0, affineGaussianModel_q0]
      ring
    · exact hKLpath base hbase.etaSubGaussian
  constructor
  · intro aceBase hace
    refine ⟨fun theta ↦ affineGaussianModel aceBase theta tau, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro theta htheta
      exact affineGaussianModel_jmsAceClass_quarter aceBase n hace theta
        (htheta.trans hc0_le)
    · intro theta _; rfl
    · intro theta _; exact affineGaussianModel_map_xt aceBase theta tau
    · intro theta _
      exact ⟨rfl, rfl, fun _ ↦ rfl, fun _ ↦ rfl,
        affineGaussianModel_eta aceBase theta tau,
        (affineGaussianModel_jmsAceClass_quarter aceBase n hace theta
          (by linarith [abs_nonneg theta])).treatmentCodeRadiusLr,
        (affineGaussianModel_jmsAceClass_quarter aceBase n hace theta
          (by linarith [abs_nonneg theta])).outcomeCodeRadiusLr⟩
    · intro theta _
      exact ⟨affineGaussianModel_map_xi aceBase theta tau,
        affineGaussianModel_indep_xi_xt aceBase theta tau⟩
    · intro theta _
      filter_upwards with o
      simp only [xi, affineGaussianModel_theta0, affineGaussianModel_q0]
      ring
    · exact hKLpath aceBase hace.etaSubGaussian
  · intro gbar qbar hex
    rcases hex with ⟨aceBase, hace, hg, hq⟩
    let thetaMinus : ℝ := -c0 / (2 * Real.sqrt n)
    let thetaPlus : ℝ := c0 / (2 * Real.sqrt n)
    let m0 := affineGaussianModel aceBase thetaMinus tau
    let m1 := affineGaussianModel aceBase thetaPlus tau
    have hsqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
    have htminus : |thetaMinus| ≤ c0 := by
      dsimp [thetaMinus]
      rw [abs_div, abs_neg, abs_of_pos hc0_pos, abs_of_pos (mul_pos zero_lt_two hsqrt_pos)]
      have hsqrt_ge : 1 ≤ Real.sqrt n := Real.one_le_sqrt.mpr (by exact_mod_cast hn)
      apply (div_le_iff₀ (mul_pos zero_lt_two hsqrt_pos)).2
      nlinarith
    have htplus : |thetaPlus| ≤ c0 := by
      dsimp [thetaPlus]
      rw [abs_div, abs_of_pos hc0_pos, abs_of_pos (mul_pos zero_lt_two hsqrt_pos)]
      have hsqrt_ge : 1 ≤ Real.sqrt n := Real.one_le_sqrt.mpr (by exact_mod_cast hn)
      apply (div_le_iff₀ (mul_pos zero_lt_two hsqrt_pos)).2
      nlinarith
    have hm0 : m0 ∈ {m : Model (Xspace := Xspace) p |
        JmsAceClass p n m ∧ barG p m n = gbar ∧ barQ p m n = qbar} := by
      exact ⟨affineGaussianModel_jmsAceClass_quarter aceBase n hace thetaMinus
        (htminus.trans hc0_le), hg, hq⟩
    have hm1 : m1 ∈ {m : Model (Xspace := Xspace) p |
        JmsAceClass p n m ∧ barG p m n = gbar ∧ barQ p m n = qbar} := by
      exact ⟨affineGaussianModel_jmsAceClass_quarter aceBase n hace thetaPlus
        (htplus.trans hc0_le), hg, hq⟩
    have hsep : |thetaPlus - thetaMinus| = c0 / Real.sqrt n := by
      have heq : thetaPlus - thetaMinus = c0 / Real.sqrt n := by
        dsimp [thetaPlus, thetaMinus]
        field_simp [ne_of_gt hsqrt_pos]
        ring
      rw [heq, abs_of_pos (div_pos hc0_pos hsqrt_pos)]
    have hKL := hKLpath aceBase hace.etaSubGaussian thetaMinus thetaPlus c0 htminus htplus hsep
    letI : IsProbabilityMeasure (iidLaw m0 n) := by unfold iidLaw; infer_instance
    letI : IsProbabilityMeasure (iidLaw m1 n) := by unfold iidLaw; infer_instance
    have hbody : ∀ T : (Fin n → Obs Xspace) → ℝ, Measurable T →
        Integrable (fun s ↦ (T s - m0.theta0) ^ 2) (iidLaw m0 n) →
        Integrable (fun s ↦ (T s - m1.theta0) ^ 2) (iidLaw m1 n) →
        cK * (m1.theta0 - m0.theta0) ^ 2 ≤
          max (∫ s, (T s - m0.theta0) ^ 2 ∂iidLaw m0 n)
            (∫ s, (T s - m1.theta0) ^ 2 ∂iidLaw m1 n) := by
      exact hlecam (iidLaw m0 n) (iidLaw m1 n) m0.theta0 m1.theta0 hKL
    have hlow := minimaxRiskOn_two_point_lower p n _ m0 m1 hm0 hm1
      p.Ctheta cK p.constants_pos.1.le
      (by exact hm0.1.thetaRange)
      (by exact hm1.1.thetaRange) hbody
    have hnreal : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
    have hsqrt_sq : (Real.sqrt n) ^ 2 = (n : ℝ) := Real.sq_sqrt hnreal.le
    convert hlow using 1
    congr 1
    dsimp [m0, m1, thetaMinus, thetaPlus]
    field_simp [ne_of_gt hnreal, ne_of_gt hsqrt_pos]
    rw [hsqrt_sq]
    ring

end CausalSmith.Stat.SaPlmCumulantConverse
