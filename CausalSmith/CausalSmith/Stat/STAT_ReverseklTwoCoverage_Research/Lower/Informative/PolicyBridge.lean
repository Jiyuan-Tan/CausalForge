import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Lower.Informative.ExactShell
import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Lower.ZeroRisk.Minimax
import Causalean.Stat.Minimax.Pinsker

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace CausalSmith.Stat.ReverseKLTwoCoverage

open MeasureTheory InformationTheory
open scoped BigOperators ENNReal

noncomputable section

lemma policyKL_eq_sum_klFun
    {𝒳 𝒜 : Type*} [Fintype 𝒜]
    (p q : Policy 𝒳 𝒜) (hp : IsPolicy p) (hq : IsPolicy q)
    (hqpos : ∀ x a, 0 < q x a) (x : 𝒳) :
    policyKL p q x = ∑ a, q x a * klFun (p x a / q x a) := by
  have hterm (a : 𝒜) :
      q x a * klFun (p x a / q x a) =
        (if p x a = 0 then 0
          else p x a * Real.log (p x a / q x a)) + q x a - p x a := by
    by_cases hpa : p x a = 0
    · simp [hpa, klFun]
    · have hqa : q x a ≠ 0 := ne_of_gt (hqpos x a)
      simp only [hpa, if_false, klFun]
      field_simp [hqa]
  unfold policyKL
  calc
    (∑ a, if p x a = 0 then 0
        else p x a * Real.log (p x a / q x a)) =
        ∑ a, ((if p x a = 0 then 0
          else p x a * Real.log (p x a / q x a)) + q x a - p x a) := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hp.2 x, hq.2 x]
      ring
    _ = ∑ a, q x a * klFun (p x a / q x a) := by
      apply Finset.sum_congr rfl
      intro a _
      exact (hterm a).symm

lemma policyKL_ge_half_sq_action
    {𝒳 𝒜 : Type*} [Fintype 𝒜]
    (p q : Policy 𝒳 𝒜) (hp : IsPolicy p) (hq : IsPolicy q)
    (hqpos : ∀ x a, 0 < q x a) (x : 𝒳) (a₀ : 𝒜) :
    (p x a₀ - q x a₀) ^ 2 / 2 ≤ policyKL p q x := by
  rw [policyKL_eq_sum_klFun p q hp hq hqpos x]
  have hp0 := hp.1 x a₀
  have hp1 : p x a₀ ≤ 1 := by
    exact le_trans (Finset.single_le_sum (fun a _ => hp.1 x a) (Finset.mem_univ a₀))
      (le_of_eq (hp.2 x))
  have hq0 := (hqpos x a₀).le
  have hq1 : q x a₀ ≤ 1 := by
    exact le_trans (Finset.single_le_sum (fun a _ => hq.1 x a) (Finset.mem_univ a₀))
      (le_of_eq (hq.2 x))
  have hnonneg (a : 𝒜) :
      0 ≤ q x a * klFun (p x a / q x a) :=
    mul_nonneg (hq.1 x a)
      (klFun_nonneg (div_nonneg (hp.1 x a) (hq.1 x a)))
  have hsingle :
      q x a₀ * klFun (p x a₀ / q x a₀) ≤
        ∑ a, q x a * klFun (p x a / q x a) :=
    Finset.single_le_sum (fun a _ => hnonneg a) (Finset.mem_univ a₀)
  have hpin := Causalean.Stat.klFun_lower_bound
    (div_nonneg hp0 hq0)
  have hden : 0 < p x a₀ / q x a₀ + 2 := by
    positivity
  have hlocal :
      (p x a₀ - q x a₀) ^ 2 / 2 ≤
        q x a₀ * klFun (p x a₀ / q x a₀) := by
    have hqne : q x a₀ ≠ 0 := ne_of_gt (hqpos x a₀)
    have heq :
        q x a₀ *
            ((3 / 2) * (p x a₀ / q x a₀ - 1) ^ 2 /
              (p x a₀ / q x a₀ + 2)) =
          (3 / 2) * (p x a₀ - q x a₀) ^ 2 /
            (p x a₀ + 2 * q x a₀) := by
      field_simp [hqne]
    have hden' : 0 < p x a₀ + 2 * q x a₀ := by positivity
    calc
      (p x a₀ - q x a₀) ^ 2 / 2
          ≤ q x a₀ *
              ((3 / 2) * (p x a₀ / q x a₀ - 1) ^ 2 /
                (p x a₀ / q x a₀ + 2)) := by
            rw [heq]
            apply (le_div_iff₀ hden').2
            nlinarith [sq_nonneg (p x a₀ - q x a₀)]
      _ ≤ q x a₀ * klFun (p x a₀ / q x a₀) :=
        mul_le_mul_of_nonneg_left hpin hq0
  exact hlocal.trans hsingle

def informativeCoordinate {d : ℕ} (hd : 4 ≤ d) (j : Fin (d - 1)) : Fin d :=
  ⟨j.val + 1, by omega⟩

lemma informativeCoordinate_ne_zero {d : ℕ} (hd : 4 ≤ d)
    (j : Fin (d - 1)) :
    informativeCoordinate hd j ≠ (⟨0, by omega⟩ : Fin d) := by
  intro h
  have := congrArg Fin.val h
  simp [informativeCoordinate] at this

lemma informativeBitIndex_coordinate {d : ℕ} (hd : 4 ≤ d)
    (j : Fin (d - 1)) :
    informativeBitIndex (by omega) (informativeCoordinate hd j)
        (informativeCoordinate_ne_zero hd j) = j := by
  apply Fin.ext
  simp [informativeBitIndex, informativeCoordinate]

lemma informativeTheta_coordinate {d : ℕ} (hd : 4 ≤ d)
    (eta D gamma : ℝ) (v : Fin (d - 1) → Bool) (j : Fin (d - 1)) :
    informativeTheta (by omega) eta D gamma v (informativeCoordinate hd j) =
      informativeBeta eta D + gamma * informativeSign (v j) := by
  rw [informativeTheta, dif_neg (informativeCoordinate_ne_zero hd j),
    informativeBitIndex_coordinate hd j]

def informativeLogistic (eta t : ℝ) : ℝ :=
  Real.exp (eta * t) / (1 + Real.exp (eta * t))

lemma informativeLogistic_gap
    {eta D gamma : ℝ} (heta : 0 < eta) (hD : 1 < D)
    (hDexp : D < Real.exp eta)
    (hgamma0 : 0 ≤ gamma) (hgamma : gamma ≤ informativeGammaCap eta D) :
    2 * eta * gamma / (1 + Real.exp eta) ^ 2 ≤
      informativeLogistic eta (informativeBeta eta D + gamma) -
        informativeLogistic eta (informativeBeta eta D - gamma) := by
  have hb0 := informativeBeta_pos heta hD
  have hb1 := informativeBeta_lt_one heta hD hDexp
  have hgB : gamma ≤ informativeBeta eta D / 2 :=
    le_trans hgamma (min_le_left _ _)
  have hg1 : gamma ≤ (1 - informativeBeta eta D) / 2 :=
    le_trans hgamma (le_trans (min_le_right _ _) (min_le_left _ _))
  have hm0 : 0 ≤ informativeBeta eta D - gamma := by nlinarith
  have hp1 : informativeBeta eta D + gamma ≤ 1 := by nlinarith
  have hm1 : informativeBeta eta D - gamma ≤ 1 := by nlinarith
  let em := Real.exp (eta * (informativeBeta eta D - gamma))
  let ep := Real.exp (eta * (informativeBeta eta D + gamma))
  have hem0 : 1 ≤ em := by
    rw [show (1 : ℝ) = Real.exp 0 by simp]
    exact Real.exp_le_exp.mpr (mul_nonneg heta.le hm0)
  have hep_eta : ep ≤ Real.exp eta :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hem_eta : em ≤ Real.exp eta :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hediff : 2 * eta * gamma ≤ ep - em := by
    have heq : ep = em * Real.exp (2 * eta * gamma) := by
      dsimp [ep, em]
      rw [← Real.exp_add]
      congr 1
      ring
    have hexp := Real.add_one_le_exp (2 * eta * gamma)
    rw [heq]
    nlinarith [mul_nonneg heta.le hgamma0]
  have hdenpos : 0 < (1 + ep) * (1 + em) := by
    dsimp [ep, em]
    positivity
  have hdenle :
      (1 + ep) * (1 + em) ≤ (1 + Real.exp eta) ^ 2 := by
    nlinarith [Real.exp_pos eta]
  have hbasepos : 0 < (1 + Real.exp eta) ^ 2 := by positivity
  have hfrac :
      2 * eta * gamma / (1 + Real.exp eta) ^ 2 ≤
        (ep - em) / ((1 + ep) * (1 + em)) := by
    apply (div_le_div_iff₀ hbasepos hdenpos).2
    have hnum0 : 0 ≤ 2 * eta * gamma :=
      mul_nonneg (mul_nonneg (by norm_num) heta.le) hgamma0
    calc
      2 * eta * gamma * ((1 + ep) * (1 + em))
          ≤ 2 * eta * gamma * (1 + Real.exp eta) ^ 2 :=
            mul_le_mul_of_nonneg_left hdenle hnum0
      _ ≤ (ep - em) * (1 + Real.exp eta) ^ 2 :=
            mul_le_mul_of_nonneg_right hediff hbasepos.le
  calc
    2 * eta * gamma / (1 + Real.exp eta) ^ 2
        ≤ (ep - em) / ((1 + ep) * (1 + em)) := hfrac
    _ = informativeLogistic eta (informativeBeta eta D + gamma) -
          informativeLogistic eta (informativeBeta eta D - gamma) := by
      dsimp [informativeLogistic, ep, em]
      field_simp
      ring

noncomputable def informativeLaw (d : ℕ) (hd : 4 ≤ d)
    (eta C D gamma : ℝ) (heta : 0 < eta) (hD : 1 < D)
    (hDC : D ≤ C) (hCexp : C < Real.exp eta)
    (v : Fin (d - 1) → Bool)
    (hgamma0 : 0 ≤ gamma) (hgamma : gamma ≤ informativeGammaCap eta D) :
    BanditLaw
      (informativeExperiment d hd eta C D heta
        (lt_of_lt_of_le hD hDC) hCexp) :=
  ibBernoulliLaw
    (informativeExperiment d hd eta C D heta
      (lt_of_lt_of_le hD hDC) hCexp)
    (informativeRho eta C D)
    (informativeTheta (by omega) eta D gamma v)
    (fun x => (informativeRho_pos hd heta hD hDC hCexp x).le)
    (informativeRho_sum hd heta hD hDC hCexp)
    (informative_linear_bounds (d := d) hd heta hD hDC hCexp
      v hgamma0 hgamma)

lemma informativeLaw_exactShell (d : ℕ) (hd : 4 ≤ d)
    (eta C D gamma : ℝ) (heta : 0 < eta) (hD : 1 < D)
    (hDC : D ≤ C) (hCexp : C < Real.exp eta)
    (v : Fin (d - 1) → Bool)
    (hgamma0 : 0 ≤ gamma) (hgamma : gamma ≤ informativeGammaCap eta D) :
    ExactShell
      (informativeExperiment d hd eta C D heta
        (lt_of_lt_of_le hD hDC) hCexp)
      (informativeLaw d hd eta C D gamma heta hD hDC hCexp
        v hgamma0 hgamma)
      C D := by
  exact informative_exactShell d hd heta hD hDC hCexp v hgamma0 hgamma

lemma indexQ_lt_one_of_one_lt {eta C : ℝ}
    (heta : 0 < eta) (hC : 1 < C) :
    indexQ eta C < 1 := by
  have he : 1 < Real.exp eta := (Real.one_lt_exp_iff).2 heta
  have hC0 : 0 < C := lt_trans zero_lt_one hC
  rw [indexQ, div_lt_one (sub_pos.mpr he)]
  have : Real.exp eta / C < Real.exp eta := by
    apply (div_lt_iff₀ hC0).2
    nlinarith [Real.exp_pos eta]
  linarith

lemma informativeExperiment_reference_pos (d : ℕ) (hd : 4 ≤ d)
    (eta C D : ℝ) (heta : 0 < eta) (hD : 1 < D)
    (hDC : D ≤ C) (hCexp : C < Real.exp eta) :
    ∀ x a, 0 <
      (informativeExperiment d hd eta C D heta
        (lt_of_lt_of_le hD hDC) hCexp).reference x a := by
  intro x a
  refine Fin.cases ?_ (fun j => ?_) x
  · norm_num [informativeExperiment, informativeReference]
  · by_cases hj : j = (⟨0, by omega⟩ : Fin d)
    · subst j
      fin_cases a
      · simp [informativeExperiment, informativeReference,
          diagonalIndexReference,
          indexQ_lt_one_of_one_lt heta (lt_of_lt_of_le hD hDC)]
      · simp [informativeExperiment, informativeReference,
          diagonalIndexReference,
          indexQ_pos heta
            (lt_trans zero_lt_one (lt_of_lt_of_le hD hDC)) hCexp]
    · fin_cases a <;>
        norm_num [informativeExperiment, informativeReference, hj]

lemma informativeLaw_gibbs_plus (d : ℕ) (hd : 4 ≤ d)
    (eta C D gamma : ℝ) (heta : 0 < eta) (hD : 1 < D)
    (hDC : D ≤ C) (hCexp : C < Real.exp eta)
    (v : Fin (d - 1) → Bool)
    (hgamma0 : 0 ≤ gamma) (hgamma : gamma ≤ informativeGammaCap eta D)
    (j : Fin (d - 1)) :
    gibbsPolicy
        (informativeExperiment d hd eta C D heta
          (lt_of_lt_of_le hD hDC) hCexp)
        (informativeLaw d hd eta C D gamma heta hD hDC hCexp
          v hgamma0 hgamma)
        (informativeCoordinate hd j).succ 1 =
      informativeLogistic eta
        (informativeBeta eta D + gamma * informativeSign (v j)) := by
  rw [gibbsPolicy_eq_candidate, candidateWeight]
  change
    (informativeExperiment d hd eta C D heta
        (lt_of_lt_of_le hD hDC) hCexp).reference
          (informativeCoordinate hd j).succ 1 *
      (Real.exp (eta *
          ∑ i, (informativeExperiment d hd eta C D heta
            (lt_of_lt_of_le hD hDC) hCexp).feature
              (informativeCoordinate hd j).succ 1 i *
            informativeTheta (by omega) eta D gamma v i) /
        candidateNormalizer
          (informativeExperiment d hd eta C D heta
            (lt_of_lt_of_le hD hDC) hCexp)
          (informativeTheta (by omega) eta D gamma v)
          (informativeCoordinate hd j).succ) =
      informativeLogistic eta
        (informativeBeta eta D + gamma * informativeSign (v j))
  rw [
    informative_normalizer_info (d := d) (hd := hd)
      (eta := eta) (C := C) (D := D) (gamma := gamma)
      (heta := heta) (hC1 := lt_of_lt_of_le hD hDC) (hCexp := hCexp)
      (v := v) (j := informativeCoordinate hd j)
      (informativeCoordinate_ne_zero hd j),
    informative_score_succ, informativeTheta_coordinate hd]
  simp only [informativeExperiment, informativeReference, Fin.cases_succ]
  rw [if_neg (informativeCoordinate_ne_zero hd j)]
  norm_num
  dsimp [informativeLogistic]
  field_simp

end

end CausalSmith.Stat.ReverseKLTwoCoverage
