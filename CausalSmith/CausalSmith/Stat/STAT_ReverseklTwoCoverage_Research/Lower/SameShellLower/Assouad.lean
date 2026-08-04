import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Lower.SameShellLower.Source
import Mathlib.Analysis.Complex.ExponentialBounds

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace CausalSmith.Stat.ReverseKLTwoCoverage

open MeasureTheory
open scoped ENNReal

noncomputable section

noncomputable def hardSourceProduct
    {d : ℕ} (n : ℕ) (hd : 4 ≤ d)
    (eta C D gamma : ℝ)
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta)
    (v : Fin (hardCoordinateCount d) → Bool)
    (hgamma0 : 0 ≤ gamma)
    (hgammaBeta : gamma ≤ hardBeta D eta gamma / 2)
    (hgammaOne : gamma ≤ (1 - hardBeta D eta gamma) / 2) :
    Measure
      (Fin n → (Fin (hardContextCard d C D) × (Fin 3 × Bool))) :=
  Measure.pi (fun _ : Fin n =>
    hardSourceMeasure hd eta C D gamma heta hD hDC hCexp v
      hgamma0 (hgammaBeta.trans (by linarith))
      (hgammaOne.trans (by linarith)))

instance hardSourceProduct_isProbability
    {d : ℕ} (n : ℕ) (hd : 4 ≤ d)
    (eta C D gamma : ℝ)
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta)
    (v : Fin (hardCoordinateCount d) → Bool)
    (hgamma0 : 0 ≤ gamma)
    (hgammaBeta : gamma ≤ hardBeta D eta gamma / 2)
    (hgammaOne : gamma ≤ (1 - hardBeta D eta gamma) / 2) :
    IsProbabilityMeasure
      (hardSourceProduct n hd eta C D gamma heta hD hDC hCexp v
        hgamma0 hgammaBeta hgammaOne) := by
  unfold hardSourceProduct
  infer_instance

noncomputable def hardNeighborChiBound
    (d : ℕ) (eta C D gamma : ℝ) : ℝ :=
  16 *
    (((hardCoordinateCount d : ℝ)⁻¹ / hardTotal d C D eta) * hardP D) *
    gamma ^ 2 *
    (1 / hardBeta D eta gamma +
      1 / (1 - hardBeta D eta gamma))

lemma hardNeighborChiBound_nonneg
    {d : ℕ} (hd : 4 ≤ d)
    {eta C D gamma : ℝ}
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta)
    (hgamma0 : 0 ≤ gamma)
    (hbeta : 0 < hardBeta D eta gamma)
    (hbeta1 : hardBeta D eta gamma < 1)
    (hgammaBeta : gamma ≤ hardBeta D eta gamma / 2)
    (hgammaOne : gamma ≤ (1 - hardBeta D eta gamma) / 2) :
    0 ≤ hardNeighborChiBound d eta C D gamma := by
  unfold hardNeighborChiBound
  have hw : 0 ≤
      ((hardCoordinateCount d : ℝ)⁻¹ / hardTotal d C D eta) * hardP D :=
    (mul_pos
      (div_pos (inv_pos.mpr
        (Nat.cast_pos.mpr (hardCoordinateCount_pos hd)))
        (hardTotal_pos (d := d) heta hD hDC hCexp))
      (hardP_pos hD)).le
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) hw) (sq_nonneg gamma))
    (add_nonneg (one_div_nonneg.mpr hbeta.le)
      (one_div_nonneg.mpr (sub_pos.mpr hbeta1).le))

lemma hardSourceProduct_neighbor_tv
    {n d : ℕ} (hd : 4 ≤ d)
    (eta C D gamma : ℝ)
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta)
    (v : Fin (hardCoordinateCount d) → Bool)
    (hgamma0 : 0 ≤ gamma)
    (hbeta : 0 < hardBeta D eta gamma)
    (hbeta1 : hardBeta D eta gamma < 1)
    (hgammaBeta : gamma ≤ hardBeta D eta gamma / 2)
    (hgammaOne : gamma ≤ (1 - hardBeta D eta gamma) / 2)
    (j : Fin (hardCoordinateCount d))
    (hbudget : (n : ℝ) * hardNeighborChiBound d eta C D gamma ≤ 1) :
    Causalean.Stat.tvDist
      (hardSourceProduct n hd eta C D gamma heta hD hDC hCexp v
        hgamma0 hgammaBeta hgammaOne)
      (hardSourceProduct n hd eta C D gamma heta hD hDC hCexp
        (Causalean.Stat.flipBit j v)
        hgamma0 hgammaBeta hgammaOne) ≤ 3 / 4 := by
  let hgb : gamma ≤ hardBeta D eta gamma :=
    hgammaBeta.trans (by linarith)
  let hgo : gamma ≤ 1 - hardBeta D eta gamma :=
    hgammaOne.trans (by linarith)
  let μ := hardSourceMeasure hd eta C D gamma heta hD hDC hCexp
    v hgamma0 hgb hgo
  let ν := hardSourceMeasure hd eta C D gamma heta hD hDC hCexp
    (Causalean.Stat.flipBit j v) hgamma0 hgb hgo
  have hac : μ ≪ ν :=
    hardSource_neighbor_ac hd eta C D gamma heta hD hDC hCexp
      v hgamma0 hbeta hbeta1 hgammaBeta hgammaOne j
  have hint :
      Integrable (fun x => ((μ.rnDeriv ν x).toReal - 1) ^ 2) ν :=
    Integrable.of_finite
  have hchi : Causalean.Stat.chiSqDiv μ ν ≤
      hardNeighborChiBound d eta C D gamma := by
    exact hardSource_neighbor_chiSq_bound hd eta C D gamma heta hD hDC
      hCexp v hgamma0 hbeta hbeta1 hgammaBeta hgammaOne j
  have hchi0 : 0 ≤ Causalean.Stat.chiSqDiv μ ν :=
    Causalean.Stat.chiSqDiv_nonneg
  have hmul :
      (n : ℝ) * Causalean.Stat.chiSqDiv μ ν ≤ 1 :=
    (mul_le_mul_of_nonneg_left hchi (Nat.cast_nonneg n)).trans hbudget
  have hpow :
      (1 + Causalean.Stat.chiSqDiv μ ν) ^ n ≤
        Real.exp ((n : ℝ) * Causalean.Stat.chiSqDiv μ ν) := by
    calc
      (1 + Causalean.Stat.chiSqDiv μ ν) ^ n ≤
          (Real.exp (Causalean.Stat.chiSqDiv μ ν)) ^ n := by
        have he : 1 + Causalean.Stat.chiSqDiv μ ν ≤
            Real.exp (Causalean.Stat.chiSqDiv μ ν) := by
          simpa [add_comm] using
            Real.add_one_le_exp (Causalean.Stat.chiSqDiv μ ν)
        exact pow_le_pow_left₀ (by linarith) he n
      _ = Real.exp ((n : ℝ) * Causalean.Stat.chiSqDiv μ ν) := by
        exact (Real.exp_nat_mul (Causalean.Stat.chiSqDiv μ ν) n).symm
  let μn := hardSourceProduct n hd eta C D gamma heta hD hDC hCexp
    v hgamma0 hgammaBeta hgammaOne
  let νn := hardSourceProduct n hd eta C D gamma heta hD hDC hCexp
    (Causalean.Stat.flipBit j v) hgamma0 hgammaBeta hgammaOne
  have hacn : μn ≪ νn := by
    dsimp [μn, νn, hardSourceProduct, μ, ν] at *
    exact Causalean.Stat.pi_iid_absolutelyContinuous _ _ hac n
  have hintn :
      Integrable (fun x => ((μn.rnDeriv νn x).toReal - 1) ^ 2) νn :=
    Integrable.of_finite
  have hprod :
      1 + Causalean.Stat.chiSqDiv μn νn =
        (1 + Causalean.Stat.chiSqDiv μ ν) ^ n := by
    dsimp [μn, νn, hardSourceProduct]
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

lemma hardSourceProduct_neighbor_tv_eighth
    {n d : ℕ} (hd : 4 ≤ d)
    (eta C D gamma : ℝ)
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta)
    (v : Fin (hardCoordinateCount d) → Bool)
    (hgamma0 : 0 ≤ gamma)
    (hbeta : 0 < hardBeta D eta gamma)
    (hbeta1 : hardBeta D eta gamma < 1)
    (hgammaBeta : gamma ≤ hardBeta D eta gamma / 2)
    (hgammaOne : gamma ≤ (1 - hardBeta D eta gamma) / 2)
    (j : Fin (hardCoordinateCount d))
    (hbudget :
      (n : ℝ) * hardNeighborChiBound d eta C D gamma ≤
        Real.log (17 / 16)) :
    Causalean.Stat.tvDist
      (hardSourceProduct n hd eta C D gamma heta hD hDC hCexp v
        hgamma0 hgammaBeta hgammaOne)
      (hardSourceProduct n hd eta C D gamma heta hD hDC hCexp
        (Causalean.Stat.flipBit j v)
        hgamma0 hgammaBeta hgammaOne) ≤ 1 / 8 := by
  let hgb : gamma ≤ hardBeta D eta gamma :=
    hgammaBeta.trans (by linarith)
  let hgo : gamma ≤ 1 - hardBeta D eta gamma :=
    hgammaOne.trans (by linarith)
  let μ := hardSourceMeasure hd eta C D gamma heta hD hDC hCexp
    v hgamma0 hgb hgo
  let ν := hardSourceMeasure hd eta C D gamma heta hD hDC hCexp
    (Causalean.Stat.flipBit j v) hgamma0 hgb hgo
  have hac : μ ≪ ν :=
    hardSource_neighbor_ac hd eta C D gamma heta hD hDC hCexp
      v hgamma0 hbeta hbeta1 hgammaBeta hgammaOne j
  have hint :
      Integrable (fun x => ((μ.rnDeriv ν x).toReal - 1) ^ 2) ν :=
    Integrable.of_finite
  have hchi : Causalean.Stat.chiSqDiv μ ν ≤
      hardNeighborChiBound d eta C D gamma :=
    hardSource_neighbor_chiSq_bound hd eta C D gamma heta hD hDC
      hCexp v hgamma0 hbeta hbeta1 hgammaBeta hgammaOne j
  have hchi0 : 0 ≤ Causalean.Stat.chiSqDiv μ ν :=
    Causalean.Stat.chiSqDiv_nonneg
  have hmul :
      (n : ℝ) * Causalean.Stat.chiSqDiv μ ν ≤ Real.log (17 / 16) :=
    (mul_le_mul_of_nonneg_left hchi (Nat.cast_nonneg n)).trans hbudget
  have hpow :
      (1 + Causalean.Stat.chiSqDiv μ ν) ^ n ≤
        Real.exp ((n : ℝ) * Causalean.Stat.chiSqDiv μ ν) := by
    calc
      (1 + Causalean.Stat.chiSqDiv μ ν) ^ n ≤
          (Real.exp (Causalean.Stat.chiSqDiv μ ν)) ^ n := by
        have he : 1 + Causalean.Stat.chiSqDiv μ ν ≤
            Real.exp (Causalean.Stat.chiSqDiv μ ν) := by
          simpa [add_comm] using
            Real.add_one_le_exp (Causalean.Stat.chiSqDiv μ ν)
        exact pow_le_pow_left₀ (by linarith) he n
      _ = Real.exp ((n : ℝ) * Causalean.Stat.chiSqDiv μ ν) := by
        exact (Real.exp_nat_mul (Causalean.Stat.chiSqDiv μ ν) n).symm
  let μn := hardSourceProduct n hd eta C D gamma heta hD hDC hCexp
    v hgamma0 hgammaBeta hgammaOne
  let νn := hardSourceProduct n hd eta C D gamma heta hD hDC hCexp
    (Causalean.Stat.flipBit j v) hgamma0 hgammaBeta hgammaOne
  have hacn : μn ≪ νn := by
    dsimp [μn, νn, hardSourceProduct, μ, ν] at *
    exact Causalean.Stat.pi_iid_absolutelyContinuous _ _ hac n
  have hintn :
      Integrable (fun x => ((μn.rnDeriv νn x).toReal - 1) ^ 2) νn :=
    Integrable.of_finite
  have hprod :
      1 + Causalean.Stat.chiSqDiv μn νn =
        (1 + Causalean.Stat.chiSqDiv μ ν) ^ n := by
    dsimp [μn, νn, hardSourceProduct]
    exact Causalean.Stat.one_add_chiSqDiv_pi_iid_general μ ν hac hint n
  have hexp :
      Real.exp ((n : ℝ) * Causalean.Stat.chiSqDiv μ ν) ≤ 17 / 16 := by
    calc
      _ ≤ Real.exp (Real.log (17 / 16)) := Real.exp_le_exp.mpr hmul
      _ = 17 / 16 := by rw [Real.exp_log (by norm_num : (0 : ℝ) < 17 / 16)]
  have hchin : Causalean.Stat.chiSqDiv μn νn ≤ 1 / 16 := by
    rw [← add_le_add_iff_left (1 : ℝ), hprod]
    convert hpow.trans hexp using 1 <;> norm_num
  have hchin0 : 0 ≤ Causalean.Stat.chiSqDiv μn νn :=
    Causalean.Stat.chiSqDiv_nonneg
  have hsqrt :
      Real.sqrt (Causalean.Stat.chiSqDiv μn νn) ≤ 1 / 4 := by
    rw [Real.sqrt_le_iff]
    constructor
    · norm_num
    · nlinarith
  have htv := Causalean.Stat.tvDist_le_half_sqrt_chiSqDiv
    μn νn hacn hintn
  change Causalean.Stat.tvDist μn νn ≤ 1 / 8
  nlinarith

end

end CausalSmith.Stat.ReverseKLTwoCoverage
