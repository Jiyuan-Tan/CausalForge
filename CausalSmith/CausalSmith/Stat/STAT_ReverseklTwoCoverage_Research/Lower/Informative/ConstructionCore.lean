import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Lower.Informative.FeasibilityRealization
import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Feasibility.IndexRegionOffDiagonal

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace CausalSmith.Stat.ReverseKLTwoCoverage

open scoped BigOperators

noncomputable section

def informativeRatio (D : ℝ) : ℝ :=
  1 + (D - 1) / (4 * D)

def informativeOdds (D : ℝ) : ℝ :=
  informativeRatio D / (2 - informativeRatio D)

def informativeBeta (eta D : ℝ) : ℝ :=
  Real.log (informativeOdds D) / eta

lemma informativeRatio_gt_one {D : ℝ} (hD : 1 < D) :
    1 < informativeRatio D := by
  unfold informativeRatio
  have hD0 : 0 < D := lt_trans zero_lt_one hD
  have : 0 < (D - 1) / (4 * D) := div_pos (sub_pos.mpr hD) (by positivity)
  linarith

lemma informativeRatio_lt_D {D : ℝ} (hD : 1 < D) :
    informativeRatio D < D := by
  unfold informativeRatio
  have hD0 : 0 < D := lt_trans zero_lt_one hD
  have hden : 1 < 4 * D := by nlinarith
  have hfrac : (D - 1) / (4 * D) < D - 1 := by
    apply (div_lt_iff₀ (show 0 < 4 * D by positivity)).2
    nlinarith [mul_pos (sub_pos.mpr hD) (sub_pos.mpr hden)]
  linarith

lemma informativeRatio_lt_two {D : ℝ} (hD : 1 < D) :
    informativeRatio D < 2 := by
  have hD0 : 0 < D := lt_trans zero_lt_one hD
  have hfrac : (D - 1) / (4 * D) < 1 := by
    apply (div_lt_iff₀ (show 0 < 4 * D by positivity)).2
    nlinarith
  unfold informativeRatio
  linarith

lemma informativeOdds_gt_one {D : ℝ} (hD : 1 < D) :
    1 < informativeOdds D := by
  have hR1 := informativeRatio_gt_one hD
  have hR2 := informativeRatio_lt_two hD
  unfold informativeOdds
  apply (lt_div_iff₀ (sub_pos.mpr hR2)).2
  linarith

lemma informativeOdds_lt_D {D : ℝ} (hD : 1 < D) :
    informativeOdds D < D := by
  have hR2 := informativeRatio_lt_two hD
  unfold informativeOdds informativeRatio at *
  have hD0 : 0 < D := lt_trans zero_lt_one hD
  apply (div_lt_iff₀ (sub_pos.mpr hR2)).2
  field_simp [ne_of_gt hD0]
  nlinarith [mul_pos (sub_pos.mpr hD) (sub_pos.mpr (by linarith : 1 / 3 < D))]

lemma informativeBeta_pos {eta D : ℝ} (heta : 0 < eta) (hD : 1 < D) :
    0 < informativeBeta eta D := by
  unfold informativeBeta
  exact div_pos (Real.log_pos (informativeOdds_gt_one hD)) heta

lemma informativeBeta_lt_one {eta D : ℝ}
    (heta : 0 < eta) (hD : 1 < D) (hDexp : D < Real.exp eta) :
    informativeBeta eta D < 1 := by
  unfold informativeBeta
  apply (div_lt_iff₀ heta).2
  have hlog := Real.strictMonoOn_log
    (lt_trans zero_lt_one (informativeOdds_gt_one hD))
    (Real.exp_pos eta)
    (lt_trans (informativeOdds_lt_D hD) hDexp)
  simpa using hlog

def informativeGammaCap (eta D : ℝ) : ℝ :=
  min (informativeBeta eta D / 2)
    (min ((1 - informativeBeta eta D) / 2)
      ((Real.log D - Real.log (informativeOdds D)) / (2 * eta)))

lemma informativeGammaCap_pos {eta D : ℝ}
    (heta : 0 < eta) (hD : 1 < D) (hDexp : D < Real.exp eta) :
    0 < informativeGammaCap eta D := by
  have hb0 := informativeBeta_pos heta hD
  have hb1 := informativeBeta_lt_one heta hD hDexp
  have hlog : Real.log (informativeOdds D) < Real.log D :=
    Real.strictMonoOn_log
      (lt_trans zero_lt_one (informativeOdds_gt_one hD))
      (lt_trans zero_lt_one hD)
      (informativeOdds_lt_D hD)
  unfold informativeGammaCap
  exact lt_min (by positivity) (lt_min (by linarith) (div_pos (sub_pos.mpr hlog) (by positivity)))

def informativeAnchorRaw (eta C D : ℝ) : ℝ :=
  if C = D then 1 else indexQ eta C * (C - D) / (D - 1)

lemma informativeAnchorRaw_pos {eta C D : ℝ}
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hC : C < Real.exp eta) :
    0 < informativeAnchorRaw eta C D := by
  unfold informativeAnchorRaw
  split_ifs with h
  · norm_num
  · exact div_pos
      (mul_pos (indexQ_pos heta (by linarith) hC)
        (sub_pos.mpr (lt_of_le_of_ne hDC (Ne.symm h))))
      (sub_pos.mpr hD)

def informativeTotal (d : ℕ) (eta C D : ℝ) : ℝ :=
  d + informativeAnchorRaw eta C D

lemma informativeTotal_pos {d : ℕ} (hd : 4 ≤ d) {eta C D : ℝ}
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hC : C < Real.exp eta) :
    0 < informativeTotal d eta C D := by
  unfold informativeTotal
  exact add_pos (by exact_mod_cast (show 0 < d by omega))
    (informativeAnchorRaw_pos heta hD hDC hC)

def informativeRho {d : ℕ} (eta C D : ℝ) (x : Fin (d + 1)) : ℝ :=
  Fin.cases (informativeAnchorRaw eta C D) (fun _ => 1) x /
    informativeTotal d eta C D

lemma informativeRho_pos {d : ℕ} (hd : 4 ≤ d) {eta C D : ℝ}
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hC : C < Real.exp eta) (x : Fin (d + 1)) :
    0 < informativeRho eta C D x := by
  refine Fin.cases ?_ (fun _ => ?_) x
  · exact div_pos (informativeAnchorRaw_pos heta hD hDC hC)
      (informativeTotal_pos hd heta hD hDC hC)
  · exact div_pos zero_lt_one (informativeTotal_pos hd heta hD hDC hC)

lemma informativeRho_sum {d : ℕ} (hd : 4 ≤ d) {eta C D : ℝ}
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hC : C < Real.exp eta) :
    ∑ x : Fin (d + 1), informativeRho eta C D x = 1 := by
  rw [Fin.sum_univ_succ]
  simp only [informativeRho, Fin.cases_zero, Fin.cases_succ,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [show informativeAnchorRaw eta C D / informativeTotal d eta C D +
      (d : ℝ) * (1 / informativeTotal d eta C D) =
      informativeTotal d eta C D / informativeTotal d eta C D by
    unfold informativeTotal
    ring]
  exact div_self (ne_of_gt (informativeTotal_pos hd heta hD hDC hC))

def informativeFeature {d : ℕ} (j0 : Fin d) (C D : ℝ)
    (x : Fin (d + 1)) (a : Fin 2) (i : Fin d) : ℝ :=
  Fin.cases
    (if C = D then 0 else indexBasis j0 i)
    (fun j => diagonalIndexFeature j a i) x

def informativeReference {d : ℕ} (j0 : Fin d) (eta C : ℝ)
    (x : Fin (d + 1)) (a : Fin 2) : ℝ :=
  Fin.cases (1 / 2)
    (fun j => if j = j0
      then diagonalIndexReference eta C j a else 1 / 2) x

def informativeExperiment (d : ℕ) (hd : 4 ≤ d)
    (eta C D : ℝ) (heta : 0 < eta) (hC1 : 1 < C)
    (hCexp : C < Real.exp eta) :
    CommonExperiment d (Fin (d + 1)) (Fin 2) where
  feature := informativeFeature ⟨0, by omega⟩ C D
  reference := informativeReference ⟨0, by omega⟩ eta C
  eta := eta
  reference_isPolicy := by
    constructor
    · intro x a
      refine Fin.cases ?_ (fun j => ?_) x
      · norm_num [informativeReference]
      · by_cases hj : j = (⟨0, by omega⟩ : Fin d)
        · subst j
          fin_cases a
          · simp [informativeReference, diagonalIndexReference,
              indexQ_le_one heta hC1.le]
          · simp [informativeReference, diagonalIndexReference,
              (indexQ_pos heta (by linarith) hCexp).le]
        · norm_num [informativeReference, hj]
    · intro x
      refine Fin.cases ?_ (fun j => ?_) x
      · norm_num [Fin.sum_univ_two, informativeReference]
        rfl
      · by_cases hj : j = (⟨0, by omega⟩ : Fin d)
        · simp [Fin.sum_univ_two, informativeReference,
            diagonalIndexReference, hj]
        · norm_num [Fin.sum_univ_two, informativeReference, hj]
          rfl
  eta_pos := heta
  dim_ge_four := hd

end

end CausalSmith.Stat.ReverseKLTwoCoverage
