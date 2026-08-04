import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Lower.Informative.Minimax

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace CausalSmith.Stat.ReverseKLTwoCoverage

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

def informativeChiFactor (eta D : ℝ) : ℝ :=
  1 / informativeBeta eta D + 1 / (1 - informativeBeta eta D)

def informativeLowerConstant (eta D : ℝ) : ℝ :=
  1 / (1024 * D * (1 + Real.exp eta) ^ 4 * informativeChiFactor eta D)

def informativeAccuracyCap (eta C D : ℝ) : ℝ :=
  informativeGammaCap eta D ^ 2 * eta /
    (64 * (1 + Real.exp eta) ^ 4 *
      (2 + informativeAnchorRaw eta C D))

lemma informativeChiFactor_pos {eta D : ℝ}
    (heta : 0 < eta) (hD : 1 < D) (hDexp : D < Real.exp eta) :
    0 < informativeChiFactor eta D := by
  have hb0 := informativeBeta_pos heta hD
  have hb1 := informativeBeta_lt_one heta hD hDexp
  unfold informativeChiFactor
  exact add_pos (one_div_pos.mpr hb0)
    (one_div_pos.mpr (sub_pos.mpr hb1))

lemma informativeLowerConstant_pos {eta D : ℝ}
    (heta : 0 < eta) (hD : 1 < D) (hDexp : D < Real.exp eta) :
    0 < informativeLowerConstant eta D := by
  have hB := informativeChiFactor_pos heta hD hDexp
  unfold informativeLowerConstant
  positivity

lemma informativeAccuracyCap_pos {eta C D : ℝ}
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta) :
    0 < informativeAccuracyCap eta C D := by
  have hcap := informativeGammaCap_pos heta hD (lt_of_le_of_lt hDC hCexp)
  have hA := informativeAnchorRaw_pos heta hD hDC hCexp
  unfold informativeAccuracyCap
  positivity

lemma informativeTotal_le_dimension
    {d : ℕ} (hd : 4 ≤ d) {eta C D : ℝ}
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta) :
    informativeTotal d eta C D ≤
      (2 + informativeAnchorRaw eta C D) * ((d - 1 : ℕ) : ℝ) := by
  have hA := informativeAnchorRaw_pos heta hD hDC hCexp
  have hdR : (4 : ℝ) ≤ d := by exact_mod_cast hd
  have hdm1 : (((d - 1 : ℕ) : ℝ)) = (d : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ d)]
    norm_num
  rw [hdm1]
  unfold informativeTotal
  have hm : 0 ≤ informativeAnchorRaw eta C D * ((d : ℝ) - 2) :=
    mul_nonneg hA.le (by linarith)
  nlinarith

def informativeGammaFor
    (d : ℕ) (eta C D eps : ℝ) : ℝ :=
  Real.sqrt
    (32 * eps * informativeTotal d eta C D *
      (1 + Real.exp eta) ^ 4 /
      (eta * ((d - 1 : ℕ) : ℝ)))

lemma informativeGammaFor_nonneg
    (d : ℕ) (eta C D eps : ℝ) :
    0 ≤ informativeGammaFor d eta C D eps :=
  Real.sqrt_nonneg _

lemma informativeGammaFor_sq
    {d : ℕ} (hd : 4 ≤ d) {eta C D eps : ℝ}
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta) (heps : 0 < eps) :
    informativeGammaFor d eta C D eps ^ 2 =
      32 * eps * informativeTotal d eta C D *
        (1 + Real.exp eta) ^ 4 /
        (eta * ((d - 1 : ℕ) : ℝ)) := by
  unfold informativeGammaFor
  have hT := informativeTotal_pos hd heta hD hDC hCexp
  have hk : 0 < (((d - 1 : ℕ) : ℝ)) := by
    exact_mod_cast (show 0 < d - 1 by omega)
  exact Real.sq_sqrt (by positivity)

lemma informativeGammaFor_le_cap
    {d : ℕ} (hd : 4 ≤ d) {eta C D eps : ℝ}
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta) (heps : 0 < eps)
    (heps0 : eps ≤ informativeAccuracyCap eta C D) :
    informativeGammaFor d eta C D eps ≤ informativeGammaCap eta D := by
  have hcap := informativeGammaCap_pos heta hD (lt_of_le_of_lt hDC hCexp)
  have hA := informativeAnchorRaw_pos heta hD hDC hCexp
  have hT := informativeTotal_pos hd heta hD hDC hCexp
  have hk : 0 < (((d - 1 : ℕ) : ℝ)) := by
    exact_mod_cast (show 0 < d - 1 by omega)
  have hS : 0 < (1 + Real.exp eta) ^ 4 := by positivity
  have hdim := informativeTotal_le_dimension hd heta hD hDC hCexp
  have harg :
      32 * eps * informativeTotal d eta C D *
          (1 + Real.exp eta) ^ 4 /
          (eta * ((d - 1 : ℕ) : ℝ)) ≤
        informativeGammaCap eta D ^ 2 := by
    unfold informativeAccuracyCap at heps0
    have hden : 0 <
        64 * (1 + Real.exp eta) ^ 4 *
          (2 + informativeAnchorRaw eta C D) := by positivity
    have hepsmul := (le_div_iff₀ hden).1 heps0
    have hdim' :
        informativeTotal d eta C D /
            ((d - 1 : ℕ) : ℝ) ≤
          2 + informativeAnchorRaw eta C D := by
      exact (div_le_iff₀ hk).2 (by
        simpa [mul_comm] using hdim)
    have hmain :
        32 * eps * (informativeTotal d eta C D /
            ((d - 1 : ℕ) : ℝ)) *
            (1 + Real.exp eta) ^ 4 ≤
          informativeGammaCap eta D ^ 2 * eta := by
      calc
        32 * eps * (informativeTotal d eta C D /
              ((d - 1 : ℕ) : ℝ)) *
              (1 + Real.exp eta) ^ 4 ≤
            32 * eps * (2 + informativeAnchorRaw eta C D) *
              (1 + Real.exp eta) ^ 4 := by
          gcongr
        _ ≤ informativeGammaCap eta D ^ 2 * eta := by
          nlinarith
    rw [show
      32 * eps * informativeTotal d eta C D *
          (1 + Real.exp eta) ^ 4 /
          (eta * ((d - 1 : ℕ) : ℝ)) =
        (32 * eps * (informativeTotal d eta C D /
          ((d - 1 : ℕ) : ℝ)) * (1 + Real.exp eta) ^ 4) / eta by
            field_simp
            <;> ring]
    exact (div_le_iff₀ heta).2 hmain
  unfold informativeGammaFor
  have hsqrt := Real.sqrt_le_sqrt harg
  rw [Real.sqrt_sq_eq_abs, abs_of_pos hcap] at hsqrt
  exact hsqrt

lemma informative_budget_of_lt_ceil
    {n d : ℕ} (hd : 4 ≤ d) {eta C D eps : ℝ}
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta) (heps : 0 < eps)
    (hn :
      n < ⌈informativeLowerConstant eta D * (d : ℝ) * D * eta / eps⌉₊) :
    (n : ℝ) *
        (4 * informativeGammaFor d eta C D eps ^ 2 /
          informativeTotal d eta C D *
          (1 / informativeBeta eta D +
            1 / (1 - informativeBeta eta D))) ≤ 1 := by
  have hT := informativeTotal_pos hd heta hD hDC hCexp
  have hB := informativeChiFactor_pos heta hD
    (lt_of_le_of_lt hDC hCexp)
  have hk : 0 < (((d - 1 : ℕ) : ℝ)) := by
    exact_mod_cast (show 0 < d - 1 by omega)
  have hS : 0 < (1 + Real.exp eta) ^ 4 := by positivity
  have hnR :
      (n : ℝ) <
        informativeLowerConstant eta D * (d : ℝ) * D * eta / eps :=
    Nat.lt_ceil.mp hn
  let coef : ℝ :=
    128 * eps * (1 + Real.exp eta) ^ 4 *
      informativeChiFactor eta D /
      (eta * ((d - 1 : ℕ) : ℝ))
  have hcoef : 0 < coef := by
    unfold coef
    positivity
  have hstrict := mul_lt_mul_of_pos_right hnR hcoef
  have heq :
      (n : ℝ) *
          (4 * informativeGammaFor d eta C D eps ^ 2 /
            informativeTotal d eta C D *
            (1 / informativeBeta eta D +
              1 / (1 - informativeBeta eta D))) =
        (n : ℝ) * coef := by
    change (n : ℝ) *
        (4 * informativeGammaFor d eta C D eps ^ 2 /
          informativeTotal d eta C D * informativeChiFactor eta D) =
      (n : ℝ) * coef
    rw [informativeGammaFor_sq hd heta hD hDC hCexp heps]
    unfold coef
    field_simp [hT.ne']
    <;> ring
  rw [heq]
  apply (hstrict.trans_le ?_).le
  calc
    (informativeLowerConstant eta D * (d : ℝ) * D * eta / eps) *
          coef = (d : ℝ) / (8 * ((d - 1 : ℕ) : ℝ)) := by
        unfold informativeLowerConstant coef
        field_simp [heps.ne', heta.ne', hk.ne', hB.ne']
        <;> ring
    _ ≤ 1 := by
        apply (div_le_iff₀ (mul_pos (by norm_num) hk)).2
        have hdR : (4 : ℝ) ≤ d := by exact_mod_cast hd
        have hdm1 : (((d - 1 : ℕ) : ℝ)) = (d : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ d)]
          norm_num
        rw [hdm1]
        nlinarith

lemma informative_rawLower_eq_two_eps
    {d : ℕ} (hd : 4 ≤ d) {eta C D eps : ℝ}
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta) (heps : 0 < eps) :
    eta⁻¹ * (1 / informativeTotal d eta C D) *
          ((eta * informativeGammaFor d eta C D eps /
            (1 + Real.exp eta) ^ 2) ^ 2 / 2) *
          ((d - 1 : ℕ) : ℝ) / 8 =
      2 * eps := by
  have hT := informativeTotal_pos hd heta hD hDC hCexp
  have hk : 0 < (((d - 1 : ℕ) : ℝ)) := by
    exact_mod_cast (show 0 < d - 1 by omega)
  rw [show
    (eta * informativeGammaFor d eta C D eps /
        (1 + Real.exp eta) ^ 2) ^ 2 =
      eta ^ 2 * informativeGammaFor d eta C D eps ^ 2 /
        (1 + Real.exp eta) ^ 4 by
          field_simp [ne_of_gt (show 0 < 1 + Real.exp eta by positivity)]
          <;> ring]
  rw [informativeGammaFor_sq hd heta hD hDC hCexp heps]
  field_simp [heta.ne', hT.ne', hk.ne']
  <;> ring

end

end CausalSmith.Stat.ReverseKLTwoCoverage
