import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Lower.SameShellLower.Risk
import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Lower.Informative.Minimax

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace CausalSmith.Stat.ReverseKLTwoCoverage

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

lemma hard_learnerRisk_uniform_upper
    {d n : ℕ} (hd : 4 ≤ d)
    (eta C D : ℝ)
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta)
    (P : BanditLaw
      (hardExperiment d hd eta C D heta hD hDC hCexp))
    (hP : ExactShell
      (hardExperiment d hd eta C D heta hD hDC hCexp) P C D)
    (L : Learner n
      (𝒳 := Fin (hardContextCard d C D)) (𝒜 := Fin 3))
    (hL : IsMeasurableLearner
      (hardExperiment d hd eta C D heta hD hDC hCexp) L) :
    learnerRisk
        (hardExperiment d hd eta C D heta hD hDC hCexp) P n L ≤
      eta⁻¹ *
        ∑ x : Fin (hardContextCard d C D), ∑ a : Fin 3,
          Real.log (Real.exp eta /
            (hardExperiment d hd eta C D heta hD hDC hCexp).reference x a) := by
  let E := hardExperiment d hd eta C D heta hD hDC hCexp
  let M := eta⁻¹ *
    ∑ x : Fin (hardContextCard d C D), ∑ a : Fin 3,
      Real.log (Real.exp eta / E.reference x a)
  have hpoint (sample : LoggedSample n
      (Fin (hardContextCard d C D)) (Fin 3)) :
      regularizedWelfare E P (gibbsPolicy E P) -
          regularizedWelfare E P
            (learnerPolicyOnSample E L sample) ≤ M := by
    obtain ⟨hp, hsupp⟩ := learnerPolicyOnSample_valid E L hL sample
    rw [gibbs_regret_identity E P C D hP
      (learnerPolicyOnSample E L sample) hp
      (fun x a hp0 => by
        by_contra href
        exact hp0 (hsupp x a href))]
    have hkl (x) :
        policyKL (learnerPolicyOnSample E L sample)
            (gibbsPolicy E P) x ≤
          ∑ a, Real.log (Real.exp eta / E.reference x a) := by
      exact policyKL_uniform_upper
        (learnerPolicyOnSample E L sample) (gibbsPolicy E P) E.reference
        hp (gibbsPolicy_isPolicy E P) E.reference_isPolicy
        (hardExperiment_reference_pos hd heta hD hDC hCexp)
        eta heta
        (gibbsPolicy_uniform_lower E P hP.linearRealizability.1) x
    have hrho1 (x) : contextMass P x ≤ 1 := by
      have hsum := certificate_contextMass_sum_one E P
      have hrho0 : ∀ y, 0 ≤ contextMass P y :=
        fun _ => ENNReal.toReal_nonneg
      have hsingle : contextMass P x ≤ ∑ y, contextMass P y :=
        Finset.single_le_sum (fun y _ => hrho0 y) (Finset.mem_univ x)
      rwa [hsum] at hsingle
    have hMrow0 (x) :
        0 ≤ ∑ a, Real.log (Real.exp eta / E.reference x a) := by
      apply Finset.sum_nonneg
      intro a _
      have href1 : E.reference x a ≤ 1 := le_trans
        (Finset.single_le_sum (fun b _ => E.reference_isPolicy.1 x b)
          (Finset.mem_univ a)) (le_of_eq (E.reference_isPolicy.2 x))
      apply Real.log_nonneg
      apply (le_div_iff₀
        (hardExperiment_reference_pos hd heta hD hDC hCexp x a)).2
      nlinarith [Real.one_le_exp heta.le]
    have hsum :
        ∑ x, contextMass P x *
            policyKL (learnerPolicyOnSample E L sample)
              (gibbsPolicy E P) x ≤
          ∑ x, ∑ a, Real.log (Real.exp eta / E.reference x a) := by
      apply Finset.sum_le_sum
      intro x _
      calc
        contextMass P x *
            policyKL (learnerPolicyOnSample E L sample)
              (gibbsPolicy E P) x ≤
          contextMass P x *
            (∑ a, Real.log (Real.exp eta / E.reference x a)) :=
          mul_le_mul_of_nonneg_left (hkl x) ENNReal.toReal_nonneg
        _ ≤ ∑ a, Real.log (Real.exp eta / E.reference x a) := by
          simpa only [one_mul] using
            mul_le_mul_of_nonneg_right (hrho1 x) (hMrow0 x)
    exact mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr heta.le)
  have hnonneg :
      ∀ sample, 0 ≤ regularizedWelfare E P (gibbsPolicy E P) -
          regularizedWelfare E P (learnerPolicyOnSample E L sample) := by
    intro sample
    obtain ⟨hp, hsupp⟩ := learnerPolicyOnSample_valid E L hL sample
    rw [gibbs_regret_identity E P C D hP
      (learnerPolicyOnSample E L sample) hp
      (fun x a hp0 => by
        by_contra href
        exact hp0 (hsupp x a href))]
    exact mul_nonneg (inv_nonneg.mpr heta.le)
      (Finset.sum_nonneg fun x _ =>
        mul_nonneg ENNReal.toReal_nonneg
          (policyKL_nonneg_of_isPolicy _ _ hp (gibbsPolicy_isPolicy E P)
            (fun _ _ hzero => False.elim
              ((div_pos
                (mul_pos
                  (hardExperiment_reference_pos hd heta hD hDC hCexp _ _)
                  (Real.exp_pos _))
                (gibbsNormalizer_pos E P _)).ne' hzero)) x))
  unfold learnerRisk
  letI : IsProbabilityMeasure (productLaw E P n) := by
    unfold productLaw
    letI : IsProbabilityMeasure P.dataMeasure := P.isProbability
    infer_instance
  have hconst : Integrable
      (fun _ : LoggedSample n
        (Fin (hardContextCard d C D)) (Fin 3) => M)
      (productLaw E P n) := integrable_const M
  have hi := integral_mono_of_nonneg
    (Filter.Eventually.of_forall hnonneg) hconst
    (Filter.Eventually.of_forall hpoint)
  rw [integral_const, probReal_univ, one_smul] at hi
  simpa [M] using hi

lemma hard_minimaxRisk_lower
    {n d : ℕ} (hd : 4 ≤ d)
    (eta C D gamma : ℝ)
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta)
    (hgamma : 0 < gamma)
    (hbeta : 0 < hardBeta D eta gamma)
    (hbeta1 : hardBeta D eta gamma < 1)
    (hgammaBeta : gamma ≤ hardBeta D eta gamma / 2)
    (hgammaOne : gamma ≤ (1 - hardBeta D eta gamma) / 2)
    (hden : 0 < Real.exp (eta * gamma) -
      2 * hardP D * D * Real.cosh (eta * gamma))
    (hpert : gamma ≤
      min (hardScale D eta)
        (min (1 / 4)
          (min (hardBeta D eta gamma)
            (1 - hardBeta D eta gamma))))
    (hbudget : (n : ℝ) * hardNeighborChiBound d eta C D gamma ≤
      Real.log (17 / 16)) :
    eta⁻¹ *
        ((hardCoordinateCount d : ℝ)⁻¹ / hardTotal d C D eta) *
        ((((1 / 4 : ℝ) - hardGibbsLow eta gamma) / 2) ^ 2 / 2) *
        (hardCoordinateCount d : ℝ) * 7 / 16 ≤
      minimaxRisk
        (hardExperiment d hd eta C D heta hD hDC hCexp) n
        (exactShellSet
          (hardExperiment d hd eta C D heta hD hDC hCexp) C D) := by
  classical
  let E := hardExperiment d hd eta C D heta hD hDC hCexp
  let L0 : Learner n
      (𝒳 := Fin (hardContextCard d C D)) (𝒜 := Fin 3) :=
    fun _ _ => E.reference
  have hL0 : IsMeasurableLearner E L0 := by
    constructor
    · intro x a
      rw [show (fun sample => learnerPolicyOnSample E L0 sample x a) =
          fun _sample => E.reference x a by
        funext sample
        by_cases hs : BoundedLoggedSample sample <;>
          simp [learnerPolicyOnSample, L0, hs]]
      exact measurable_const
    · intro sample hs
      exact ⟨E.reference_isPolicy, fun _ _ h => h⟩
  unfold minimaxRisk
  apply le_csInf
  · exact ⟨_, L0, hL0, rfl⟩
  · rintro r ⟨L, hL, rfl⟩
    obtain ⟨v, hv⟩ := hard_exists_learnerRisk_lower hd eta C D gamma
      heta hD hDC hCexp hgamma hbeta hbeta1 hgammaBeta hgammaOne
      hden hpert hbudget L hL
    let P := hardLaw hd eta C D gamma heta hD hDC hCexp v
      hgamma.le (hgammaBeta.trans (by linarith))
      (hgammaOne.trans (by linarith))
    have hP : P ∈ exactShellSet E C D :=
      hard_exactShell hd heta hD hDC hCexp hgamma.le hden
        (hgammaBeta.trans (by linarith))
        (hgammaOne.trans (by linarith)) v
    have hbdd : BddAbove
        {q : ℝ | ∃ P' : BanditLaw E, P' ∈ exactShellSet E C D ∧
          q = learnerRisk E P' n L} := by
      refine ⟨eta⁻¹ *
        ∑ x : Fin (hardContextCard d C D), ∑ a : Fin 3,
          Real.log (Real.exp eta / E.reference x a), ?_⟩
      rintro q ⟨P', hP', rfl⟩
      exact hard_learnerRisk_uniform_upper hd eta C D heta hD hDC
        hCexp P' hP' L hL
    exact hv.trans (le_csSup hbdd ⟨P, hP, rfl⟩)

end

end CausalSmith.Stat.ReverseKLTwoCoverage
