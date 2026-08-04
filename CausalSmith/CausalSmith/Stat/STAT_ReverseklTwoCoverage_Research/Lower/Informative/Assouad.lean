import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Lower.Informative.SourceChi
import Mathlib.Analysis.Complex.ExponentialBounds

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace CausalSmith.Stat.ReverseKLTwoCoverage

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

noncomputable def informativeSourceProduct
    (n d : ℕ) (hd : 4 ≤ d)
    (eta C D gamma : ℝ) (heta : 0 < eta) (hD : 1 < D)
    (hDC : D ≤ C) (hCexp : C < Real.exp eta)
    (v : Fin (d - 1) → Bool)
    (hgamma0 : 0 ≤ gamma) (hgamma : gamma ≤ informativeGammaCap eta D) :
    Measure (Fin n → (Fin (d + 1) × (Fin 2 × Bool))) :=
  Measure.pi (fun _ : Fin n =>
    informativeSourceMeasure d hd eta C D gamma heta hD hDC hCexp
      v hgamma0 hgamma)

instance informativeSourceProduct_isProbability
    (n d : ℕ) (hd : 4 ≤ d)
    (eta C D gamma : ℝ) (heta : 0 < eta) (hD : 1 < D)
    (hDC : D ≤ C) (hCexp : C < Real.exp eta)
    (v : Fin (d - 1) → Bool)
    (hgamma0 : 0 ≤ gamma) (hgamma : gamma ≤ informativeGammaCap eta D) :
    IsProbabilityMeasure
      (informativeSourceProduct n d hd eta C D gamma heta hD hDC hCexp
        v hgamma0 hgamma) := by
  unfold informativeSourceProduct
  infer_instance

lemma informativeSourceProduct_neighbor_tv
    {n d : ℕ} (hd : 4 ≤ d)
    (eta C D gamma : ℝ) (heta : 0 < eta) (hD : 1 < D)
    (hDC : D ≤ C) (hCexp : C < Real.exp eta)
    (v : Fin (d - 1) → Bool)
    (hgamma0 : 0 ≤ gamma) (hgamma : gamma ≤ informativeGammaCap eta D)
    (j : Fin (d - 1))
    (hbudget :
      (n : ℝ) *
        (4 * gamma ^ 2 / informativeTotal d eta C D *
          (1 / informativeBeta eta D +
            1 / (1 - informativeBeta eta D))) ≤ 1) :
    Causalean.Stat.tvDist
        (informativeSourceProduct n d hd eta C D gamma heta hD hDC hCexp
          v hgamma0 hgamma)
        (informativeSourceProduct n d hd eta C D gamma heta hD hDC hCexp
          (Causalean.Stat.flipBit j v) hgamma0 hgamma) ≤ 3 / 4 := by
  let μ := informativeSourceMeasure d hd eta C D gamma heta hD hDC hCexp
    v hgamma0 hgamma
  let ν := informativeSourceMeasure d hd eta C D gamma heta hD hDC hCexp
    (Causalean.Stat.flipBit j v) hgamma0 hgamma
  have hac : μ ≪ ν := informativeSource_neighbor_ac hd eta C D gamma
    heta hD hDC hCexp v hgamma0 hgamma j
  have hint :
      Integrable (fun x => ((μ.rnDeriv ν x).toReal - 1) ^ 2) ν :=
    Integrable.of_finite
  have hchi := informativeSource_neighbor_chiSq_bound hd eta C D gamma
    heta hD hDC hCexp v hgamma0 hgamma j
  change Causalean.Stat.chiSqDiv μ ν ≤
    4 * gamma ^ 2 / informativeTotal d eta C D *
      (1 / informativeBeta eta D +
        1 / (1 - informativeBeta eta D)) at hchi
  have hchi0 : 0 ≤ Causalean.Stat.chiSqDiv μ ν :=
    Causalean.Stat.chiSqDiv_nonneg
  have hx0 :
      0 ≤ 4 * gamma ^ 2 / informativeTotal d eta C D *
        (1 / informativeBeta eta D +
          1 / (1 - informativeBeta eta D)) := by
    have hT := informativeTotal_pos hd heta hD hDC hCexp
    have hb0 := informativeBeta_pos heta hD
    have hb1 := informativeBeta_lt_one heta hD (lt_of_le_of_lt hDC hCexp)
    exact mul_nonneg
      (div_nonneg (mul_nonneg (by norm_num) (sq_nonneg gamma)) hT.le)
      (add_nonneg (one_div_nonneg.mpr hb0.le)
        (one_div_nonneg.mpr (sub_nonneg.mpr hb1.le)))
  have hmul :
      (n : ℝ) * Causalean.Stat.chiSqDiv μ ν ≤ 1 := by
    exact (mul_le_mul_of_nonneg_left hchi (Nat.cast_nonneg n)).trans hbudget
  have hpow :
      (1 + Causalean.Stat.chiSqDiv μ ν) ^ n ≤
        Real.exp ((n : ℝ) * Causalean.Stat.chiSqDiv μ ν) := by
    calc
      (1 + Causalean.Stat.chiSqDiv μ ν) ^ n ≤
          (Real.exp (Causalean.Stat.chiSqDiv μ ν)) ^ n := by
        have he := Real.add_one_le_exp (Causalean.Stat.chiSqDiv μ ν)
        exact pow_le_pow_left₀ (by linarith) (by linarith) n
      _ = Real.exp ((n : ℝ) * Causalean.Stat.chiSqDiv μ ν) := by
        exact (Real.exp_nat_mul (Causalean.Stat.chiSqDiv μ ν) n).symm
  let μn := informativeSourceProduct n d hd eta C D gamma heta hD hDC
    hCexp v hgamma0 hgamma
  let νn := informativeSourceProduct n d hd eta C D gamma heta hD hDC
    hCexp (Causalean.Stat.flipBit j v) hgamma0 hgamma
  have hacn : μn ≪ νn := by
    dsimp [μn, νn, informativeSourceProduct, μ, ν] at *
    exact Causalean.Stat.pi_iid_absolutelyContinuous _ _ hac n
  have hintn :
      Integrable (fun x => ((μn.rnDeriv νn x).toReal - 1) ^ 2) νn := by
    exact Integrable.of_finite
  have hprod :
      1 + Causalean.Stat.chiSqDiv μn νn =
        (1 + Causalean.Stat.chiSqDiv μ ν) ^ n := by
    dsimp [μn, νn, informativeSourceProduct]
    exact Causalean.Stat.one_add_chiSqDiv_pi_iid_general μ ν hac hint n
  have hchin_lt : Causalean.Stat.chiSqDiv μn νn < 2 := by
    have he :
        Real.exp ((n : ℝ) * Causalean.Stat.chiSqDiv μ ν) ≤ Real.exp 1 :=
      Real.exp_le_exp.mpr hmul
    have hthree : Real.exp 1 < 3 := Real.exp_one_lt_three
    have : 1 + Causalean.Stat.chiSqDiv μn νn < 3 := by
      rw [hprod]
      exact hpow.trans_lt (he.trans_lt hthree)
    linarith
  have hchin0 : 0 ≤ Causalean.Stat.chiSqDiv μn νn :=
    Causalean.Stat.chiSqDiv_nonneg
  have hsqrt : Real.sqrt (Causalean.Stat.chiSqDiv μn νn) < 3 / 2 := by
    rw [Real.sqrt_lt hchin0 (by norm_num : (0 : ℝ) ≤ 3 / 2)]
    nlinarith
  have htv := Causalean.Stat.tvDist_le_half_sqrt_chiSqDiv
    μn νn hacn hintn
  change Causalean.Stat.tvDist μn νn ≤ 3 / 4
  nlinarith

end

end CausalSmith.Stat.ReverseKLTwoCoverage
