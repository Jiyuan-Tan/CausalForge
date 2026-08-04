import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Lower.SameShellLower.Minimax
import Mathlib.Analysis.Complex.Exponential

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace CausalSmith.Stat.ReverseKLTwoCoverage

open scoped Topology

noncomputable section

def hardChiEnvelope (D eta : ℝ) : ℝ :=
  2 / hardBeta D eta 0 + 2 / (1 - hardBeta D eta 0)

def hardLowerConstant (D eta : ℝ) : ℝ :=
  Real.log (17 / 16) / (16384 * hardChiEnvelope D eta)

lemma hardTotal_le_three_halves
    {d : ℕ} {eta C D : ℝ}
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta) :
    hardTotal d C D eta ≤ 3 / 2 := by
  have hA := hardAnchorRaw_nonneg heta hD hDC hCexp
  have hden : 0 < 4 * (1 + hardAnchorRaw C D eta) := by positivity
  have hquarter :
      hardTau C D eta * (1 + hardAnchorRaw C D eta) = 1 / 4 := by
    unfold hardTau
    rw [inv_mul_eq_div]
    field_simp
  unfold hardTotal
  by_cases hCD : C > D
  · rw [if_pos hCD]
    by_cases heven : Even d
    · rw [if_pos heven]
      nlinarith [hquarter]
    · rw [if_neg heven]
      nlinarith [hquarter]
  · rw [if_neg hCD]
    have hCD_eq : C = D := le_antisymm (not_lt.mp hCD) hDC
    have hAz : hardAnchorRaw C D eta = 0 := by
      unfold hardAnchorRaw
      rw [hCD_eq]
      simp
    have htau : hardTau C D eta = 1 / 4 := by
      unfold hardTau
      rw [hAz]
      norm_num
    rw [htau]
    split_ifs <;> norm_num

lemma hardTotal_one_le
    {d : ℕ} {eta C D : ℝ}
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta) :
    1 ≤ hardTotal d C D eta := by
  have ht := (hardTau_pos heta hD hDC hCexp).le
  have hA := hardAnchorRaw_nonneg heta hD hDC hCexp
  unfold hardTotal
  split_ifs <;> nlinarith [mul_nonneg ht hA]

lemma hardChiEnvelope_pos
    {D eta : ℝ} (heta : 0 < eta) (hD : 1 < D)
    (hDexp : 2 * D - 1 < Real.exp eta) :
    0 < hardChiEnvelope D eta := by
  have hb0 := hardBeta_zero_pos heta hD
  have hb1 := hardBeta_zero_lt_one heta hDexp hD
  unfold hardChiEnvelope
  exact add_pos (div_pos (by norm_num) hb0)
    (div_pos (by norm_num) (sub_pos.mpr hb1))

lemma hardLowerConstant_pos
    {D eta : ℝ} (heta : 0 < eta) (hD : 1 < D)
    (hDexp : 2 * D - 1 < Real.exp eta) :
    0 < hardLowerConstant D eta := by
  have hlog : 0 < Real.log (17 / 16 : ℝ) := by
    apply Real.log_pos
    norm_num
  have hchi := hardChiEnvelope_pos heta hD hDexp
  unfold hardLowerConstant
  positivity

lemma exists_hardStrongScale
    {D eta : ℝ} (heta : 0 < eta) (hD : 1 < D)
    (hDexp : 2 * D - 1 < Real.exp eta) :
    ∃ g : ℝ, 0 < g ∧
      g ≤ min (hardScale D eta) (1 / 4) ∧
      128 * eta * g ≤ 1 ∧
      2 * eta * g ≤ Real.log (7 / 6) ∧
      ∀ s ∈ Set.Icc (0 : ℝ) g,
        0 < Real.exp (eta * s) -
            2 * hardP D * D * Real.cosh (eta * s) ∧
        s ≤ hardBeta D eta s / 2 ∧
        s ≤ (1 - hardBeta D eta s) / 2 ∧
        hardBeta D eta 0 / 2 ≤ hardBeta D eta s ∧
        hardBeta D eta s ≤ (1 + hardBeta D eta 0) / 2 := by
  have hb0 := hardBeta_zero_pos heta hD
  have hb1 := hardBeta_zero_lt_one heta hDexp hD
  have hden_cont : ContinuousAt
      (fun s : ℝ => Real.exp (eta * s) -
        2 * hardP D * D * Real.cosh (eta * s)) 0 := by
    fun_prop
  have hb_cont := continuousAt_hardBeta_zero heta hD
  have hden0 : 0 < Real.exp (eta * 0) -
      2 * hardP D * D * Real.cosh (eta * 0) := by
    rw [show 2 * hardP D * D = 1 / 2 from
      hardP_mul_D (lt_trans zero_lt_one hD)]
    norm_num
  have hlo0 : 0 < hardBeta D eta 0 / 2 - 0 := by linarith
  have hhi0 : 0 < (1 - hardBeta D eta 0) / 2 - 0 := by linarith
  have hbLo0 :
      0 < hardBeta D eta 0 - hardBeta D eta 0 / 2 := by linarith
  have hbHi0 :
      0 < (1 + hardBeta D eta 0) / 2 - hardBeta D eta 0 := by
    linarith
  have hev :
      ∀ᶠ s in 𝓝 (0 : ℝ),
        0 < Real.exp (eta * s) -
            2 * hardP D * D * Real.cosh (eta * s) ∧
        s < hardBeta D eta s / 2 ∧
        s < (1 - hardBeta D eta s) / 2 ∧
        hardBeta D eta 0 / 2 < hardBeta D eta s ∧
        hardBeta D eta s < (1 + hardBeta D eta 0) / 2 := by
    filter_upwards
      [hden_cont.eventually (isOpen_Ioi.mem_nhds hden0),
       (hb_cont.div_const 2 |>.sub continuousAt_id).eventually
          (isOpen_Ioi.mem_nhds hlo0),
       ((continuousAt_const.sub hb_cont).div_const 2 |>.sub
          continuousAt_id).eventually
          (isOpen_Ioi.mem_nhds hhi0),
       (hb_cont.sub continuousAt_const).eventually
          (isOpen_Ioi.mem_nhds hbLo0),
       (continuousAt_const.sub hb_cont).eventually
          (isOpen_Ioi.mem_nhds hbHi0)]
      with s hden hslo hshi hbLo hbHi
    exact ⟨hden, by simpa [sub_pos] using hslo,
      by simpa [sub_pos] using hshi,
      by simpa [sub_pos] using hbLo,
      by simpa [sub_pos] using hbHi⟩
  rcases Metric.eventually_nhds_iff.mp hev with ⟨r, hr, hev_r⟩
  have hscale := hardScale_pos heta hD hDexp
  have hlog : 0 < Real.log (7 / 6 : ℝ) := by
    apply Real.log_pos
    norm_num
  let g := min (r / 2)
    (min (min (hardScale D eta) (1 / 4))
      (min (1 / (128 * eta)) (Real.log (7 / 6) / (2 * eta))))
  have hg : 0 < g := by
    dsimp [g]
    positivity
  have hgr : g ≤ r / 2 := min_le_left _ _
  have hgM : g ≤ min (hardScale D eta) (1 / 4) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hg128 : 128 * eta * g ≤ 1 := by
    have hgle : g ≤ 1 / (128 * eta) := by
      dsimp [g]
      exact (min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _))
    have h128 : 0 < 128 * eta := mul_pos (by norm_num) heta
    simpa [mul_comm] using (le_div_iff₀ h128).mp hgle
  have hglog : 2 * eta * g ≤ Real.log (7 / 6) := by
    have hgle : g ≤ Real.log (7 / 6) / (2 * eta) := by
      dsimp [g]
      exact (min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_right _ _))
    have h2 : 0 < 2 * eta := mul_pos (by norm_num) heta
    simpa [mul_comm] using (le_div_iff₀ h2).mp hgle
  refine ⟨g, hg, hgM, hg128, hglog, ?_⟩
  intro s hs
  have hdist : dist s 0 < r := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hs.1]
    exact hs.2.trans_lt (lt_of_le_of_lt hgr (half_lt_self hr))
  exact (hev_r hdist).imp (fun h => h)
    (fun h => ⟨h.1.le, h.2.1.le, h.2.2.1.le, h.2.2.2.le⟩)

lemma exists_hardStrongEpsScale
    {C D eta : ℝ} (heta : 0 < eta) (hD : 1 < D)
    (hDexp : 2 * D - 1 < Real.exp eta) :
    ∃ eps1 g : ℝ, 0 < eps1 ∧ 0 < g ∧
      g ≤ min (hardScale D eta) (1 / 4) ∧
      eps1 ≤ hardAccuracyRange C D eta ∧
      ∀ eps, 0 < eps → eps ≤ eps1 →
        let gamma := hardPerturbation eps eta
        0 < gamma ∧ gamma ≤ g ∧
        128 * eta * eps ≤ 1 ∧
        2 * eta * gamma ≤ Real.log (7 / 6) ∧
        0 < Real.exp (eta * gamma) -
            2 * hardP D * D * Real.cosh (eta * gamma) ∧
        gamma ≤ hardBeta D eta gamma / 2 ∧
        gamma ≤ (1 - hardBeta D eta gamma) / 2 ∧
        hardBeta D eta 0 / 2 ≤ hardBeta D eta gamma ∧
        hardBeta D eta gamma ≤ (1 + hardBeta D eta 0) / 2 := by
  obtain ⟨g, hg, hgM, hg128, hglog, hgood⟩ :=
    exists_hardStrongScale heta hD hDexp
  let epsCosh :=
    (128 * eta)⁻¹ * Real.log (Real.cosh (eta * g))
  let eps1 := min epsCosh (1 / (128 * eta))
  have hlogg : 0 < Real.log (Real.cosh (eta * g)) := by
    exact Real.log_pos ((Real.one_lt_cosh).2 (mul_pos heta hg).ne')
  have hepsCosh : 0 < epsCosh := by
    dsimp [epsCosh]
    positivity
  have hepsOne : 0 < 1 / (128 * eta) := by positivity
  have heps1 : 0 < eps1 := by
    dsimp [eps1]
    exact lt_min hepsCosh hepsOne
  have hM : 0 < min (hardScale D eta) (1 / 4) :=
    lt_min (hardScale_pos heta hD hDexp) (by norm_num)
  have hcosh :
      Real.cosh (eta * g) ≤
        Real.cosh (eta * min (hardScale D eta) (1 / 4)) := by
    rw [Real.cosh_le_cosh]
    rw [abs_of_nonneg (mul_nonneg heta.le hg.le),
      abs_of_nonneg (mul_nonneg heta.le hM.le)]
    exact mul_le_mul_of_nonneg_left hgM heta.le
  have hlog :
      Real.log (Real.cosh (eta * g)) ≤
        Real.log (Real.cosh
          (eta * min (hardScale D eta) (1 / 4))) :=
    Real.strictMonoOn_log.monotoneOn
      (Real.cosh_pos _) (Real.cosh_pos _) hcosh
  have hcoef :
      (128 * eta)⁻¹ ≤ (64 * eta)⁻¹ := by
    exact (inv_le_inv₀
      (mul_pos (by norm_num) heta)
      (mul_pos (by norm_num) heta)).2 (by nlinarith)
  have hepsRange : eps1 ≤ hardAccuracyRange C D eta := by
    unfold hardAccuracyRange
    calc
      eps1 ≤ epsCosh := min_le_left _ _
      _ ≤ (64 * eta)⁻¹ *
          Real.log (Real.cosh (eta * g)) := by
        dsimp [epsCosh]
        exact mul_le_mul_of_nonneg_right hcoef hlogg.le
      _ ≤ (64 * eta)⁻¹ *
          Real.log
            (Real.cosh (eta * min (hardScale D eta) (1 / 4))) :=
        mul_le_mul_of_nonneg_left hlog
          (inv_nonneg.mpr (mul_pos (by norm_num) heta).le)
  refine ⟨eps1, g, heps1, hg, hgM, hepsRange, ?_⟩
  intro eps heps hepsle
  have hepsC : eps ≤ epsCosh :=
    hepsle.trans (min_le_left _ _)
  have hepsg :
      eps ≤ (64 * eta)⁻¹ * Real.log (Real.cosh (eta * g)) := by
    calc
      eps ≤ epsCosh := hepsC
      _ ≤ (64 * eta)⁻¹ * Real.log (Real.cosh (eta * g)) := by
        dsimp [epsCosh]
        exact mul_le_mul_of_nonneg_right hcoef hlogg.le
  have hgamma0 := hardPerturbation_pos heps heta
  have hgammag :=
    hardPerturbation_le_of_eps_le_logCosh heta heps.le hg.le hepsg
  have hepsOne' : eps ≤ 1 / (128 * eta) :=
    hepsle.trans (min_le_right _ _)
  have heps128 : 128 * eta * eps ≤ 1 := by
    have h128 : 0 < 128 * eta := mul_pos (by norm_num) heta
    simpa [mul_comm] using (le_div_iff₀ h128).mp hepsOne'
  have hs := hgood (hardPerturbation eps eta)
    ⟨hgamma0.le, hgammag⟩
  exact ⟨hgamma0, hgammag, heps128,
    (mul_le_mul_of_nonneg_left hgammag
      (mul_nonneg (by norm_num) heta.le)).trans hglog,
    hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2⟩

lemma hardPerturbation_sq_le
    {eps eta : ℝ} (heta : 0 < eta) (heps : 0 < eps)
    (hsmall : 128 * eta * eps ≤ 1) :
    hardPerturbation eps eta ^ 2 ≤ 256 * eps / eta := by
  let gamma := hardPerturbation eps eta
  have hgamma := hardPerturbation_pos heps heta
  have ht : 0 ≤ eta * gamma := mul_nonneg heta.le hgamma.le
  have hself : eta * gamma ≤ Real.sinh (eta * gamma) :=
    (Real.self_le_sinh_iff).2 ht
  have hsinh0 : 0 ≤ Real.sinh (eta * gamma) :=
    (Real.sinh_nonneg_iff).2 ht
  have hsq :
      (eta * gamma) ^ 2 ≤ Real.sinh (eta * gamma) ^ 2 :=
    (sq_le_sq₀ ht hsinh0).2 hself
  have hcosh := hardPerturbation_cosh heps.le heta
  have hsinh :
      Real.sinh (eta * gamma) ^ 2 =
        Real.exp (128 * eta * eps) - 1 := by
    rw [Real.sinh_sq, hcosh]
    rw [show Real.exp (64 * eta * eps) ^ 2 =
        Real.exp (128 * eta * eps) by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring]
  have hx0 : 0 ≤ 128 * eta * eps := by positivity
  have habs : |128 * eta * eps| ≤ 1 := by
    rw [abs_of_nonneg hx0]
    exact hsmall
  have hexpAbs := Real.abs_exp_sub_one_le habs
  have hexp0 : 0 ≤ Real.exp (128 * eta * eps) - 1 := by
    exact sub_nonneg.mpr (Real.one_le_exp hx0)
  have hexp :
      Real.exp (128 * eta * eps) - 1 ≤
        2 * (128 * eta * eps) := by
    simpa [abs_of_nonneg hexp0, abs_of_nonneg hx0] using hexpAbs
  rw [hsinh] at hsq
  have heta2 : 0 < eta ^ 2 := sq_pos_of_pos heta
  have hmain :
      eta ^ 2 * gamma ^ 2 ≤ eta ^ 2 * (256 * eps / eta) := by
    calc
      eta ^ 2 * gamma ^ 2 = (eta * gamma) ^ 2 := by ring
      _ ≤ Real.exp (128 * eta * eps) - 1 := hsq
      _ ≤ 2 * (128 * eta * eps) := hexp
      _ = eta ^ 2 * (256 * eps / eta) := by
        field_simp [heta.ne']
        <;> ring
  change gamma ^ 2 ≤ 256 * eps / eta
  nlinarith [hmain]

lemma hardBernoulliChi_le_envelope
    {D eta gamma : ℝ}
    (heta : 0 < eta) (hD : 1 < D)
    (hDexp : 2 * D - 1 < Real.exp eta)
    (hbLo : hardBeta D eta 0 / 2 ≤ hardBeta D eta gamma)
    (hbHi : hardBeta D eta gamma ≤
      (1 + hardBeta D eta 0) / 2) :
    1 / hardBeta D eta gamma +
        1 / (1 - hardBeta D eta gamma) ≤
      hardChiEnvelope D eta := by
  have hb0 := hardBeta_zero_pos heta hD
  have hb1 := hardBeta_zero_lt_one heta hDexp hD
  have hbg : 0 < hardBeta D eta gamma := lt_of_lt_of_le
    (half_pos hb0) hbLo
  have hbg1 : hardBeta D eta gamma < 1 := by
    have : (1 + hardBeta D eta 0) / 2 < 1 := by linarith
    exact hbHi.trans_lt this
  have hleft :
      1 / hardBeta D eta gamma ≤ 2 / hardBeta D eta 0 := by
    rw [div_le_div_iff₀ hbg hb0]
    nlinarith
  have hright :
      1 / (1 - hardBeta D eta gamma) ≤
        2 / (1 - hardBeta D eta 0) := by
    rw [div_le_div_iff₀ (sub_pos.mpr hbg1) (sub_pos.mpr hb1)]
    nlinarith
  unfold hardChiEnvelope
  linarith

lemma hard_dimension_le_four_coordinates
    {d : ℕ} (hd : 4 ≤ d) :
    (d : ℝ) ≤ 4 * (hardCoordinateCount d : ℝ) := by
  have hnat : d ≤ 4 * hardCoordinateCount d := by
    unfold hardCoordinateCount
    omega
  exact_mod_cast hnat

lemma hardNeighborChiBound_le
    {d : ℕ} (hd : 4 ≤ d)
    {eta C D gamma eps : ℝ}
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta)
    (heps : 0 < eps)
    (hgammaSq : gamma ^ 2 ≤ 256 * eps / eta)
    (hchi :
      1 / hardBeta D eta gamma +
          1 / (1 - hardBeta D eta gamma) ≤
        hardChiEnvelope D eta)
    (hbeta : 0 < hardBeta D eta gamma)
    (hbeta1 : hardBeta D eta gamma < 1) :
    hardNeighborChiBound d eta C D gamma ≤
      1024 * eps * hardChiEnvelope D eta /
        ((hardCoordinateCount d : ℝ) * D * eta) := by
  have hk : 0 < (hardCoordinateCount d : ℝ) :=
    Nat.cast_pos.mpr (hardCoordinateCount_pos hd)
  have hT := hardTotal_pos (d := d) heta hD hDC hCexp
  have hT1 := hardTotal_one_le (d := d) heta hD hDC hCexp
  have hD0 : 0 < D := lt_trans zero_lt_one hD
  have hP : hardP D = 1 / (4 * D) := by
    unfold hardP
    rw [inv_eq_one_div]
  have hchi0 : 0 ≤
      1 / hardBeta D eta gamma +
        1 / (1 - hardBeta D eta gamma) :=
    add_nonneg (one_div_nonneg.mpr hbeta.le)
      (one_div_nonneg.mpr (sub_pos.mpr hbeta1).le)
  have henv0 : 0 ≤ hardChiEnvelope D eta :=
    hchi0.trans hchi
  rw [hardNeighborChiBound, hP]
  calc
    16 *
        (((hardCoordinateCount d : ℝ)⁻¹ / hardTotal d C D eta) *
          (1 / (4 * D))) *
        gamma ^ 2 *
        (1 / hardBeta D eta gamma +
          1 / (1 - hardBeta D eta gamma)) =
      4 * gamma ^ 2 *
          (1 / hardBeta D eta gamma +
            1 / (1 - hardBeta D eta gamma)) /
        ((hardCoordinateCount d : ℝ) * hardTotal d C D eta * D) := by
      field_simp [hk.ne', hT.ne', hD0.ne']
      <;> ring
    _ ≤ 4 * (256 * eps / eta) * hardChiEnvelope D eta /
        ((hardCoordinateCount d : ℝ) * 1 * D) := by
      gcongr
    _ = 1024 * eps * hardChiEnvelope D eta /
        ((hardCoordinateCount d : ℝ) * D * eta) := by
      field_simp [heta.ne', hk.ne', hD0.ne']
      <;> ring

lemma hard_budget_of_lt_ceil
    {n d : ℕ} (hd : 4 ≤ d)
    {eta C D gamma eps : ℝ}
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta)
    (hDexp : 2 * D - 1 < Real.exp eta)
    (heps : 0 < eps)
    (hgammaSq : gamma ^ 2 ≤ 256 * eps / eta)
    (hbLo : hardBeta D eta 0 / 2 ≤ hardBeta D eta gamma)
    (hbHi : hardBeta D eta gamma ≤
      (1 + hardBeta D eta 0) / 2)
    (hn : n <
      ⌈hardLowerConstant D eta * (d : ℝ) * D * eta / eps⌉₊) :
    (n : ℝ) * hardNeighborChiBound d eta C D gamma ≤
      Real.log (17 / 16) := by
  have hb0 := hardBeta_zero_pos heta hD
  have hb1 := hardBeta_zero_lt_one heta hDexp hD
  have hbeta : 0 < hardBeta D eta gamma :=
    (half_pos hb0).trans_le hbLo
  have hbeta1 : hardBeta D eta gamma < 1 := by
    have : (1 + hardBeta D eta 0) / 2 < 1 := by linarith
    exact hbHi.trans_lt this
  have hchi := hardBernoulliChi_le_envelope
    heta hD hDexp hbLo hbHi
  have hbound := hardNeighborChiBound_le hd heta hD hDC hCexp
    heps hgammaSq hchi hbeta hbeta1
  have hk : 0 < (hardCoordinateCount d : ℝ) :=
    Nat.cast_pos.mpr (hardCoordinateCount_pos hd)
  have hD0 : 0 < D := lt_trans zero_lt_one hD
  have henv := hardChiEnvelope_pos heta hD hDexp
  have hlog : 0 < Real.log (17 / 16 : ℝ) := by
    exact Real.log_pos (by norm_num)
  have hnR :
      (n : ℝ) <
        hardLowerConstant D eta * (d : ℝ) * D * eta / eps :=
    Nat.lt_ceil.mp hn
  have hcoef : 0 <
      1024 * eps * hardChiEnvelope D eta /
        ((hardCoordinateCount d : ℝ) * D * eta) := by
    positivity
  apply le_of_lt
  calc
    (n : ℝ) * hardNeighborChiBound d eta C D gamma ≤
        (n : ℝ) *
          (1024 * eps * hardChiEnvelope D eta /
            ((hardCoordinateCount d : ℝ) * D * eta)) :=
      mul_le_mul_of_nonneg_left hbound (Nat.cast_nonneg n)
    _ < (hardLowerConstant D eta * (d : ℝ) * D * eta / eps) *
          (1024 * eps * hardChiEnvelope D eta /
            ((hardCoordinateCount d : ℝ) * D * eta)) :=
      mul_lt_mul_of_pos_right hnR hcoef
    _ = Real.log (17 / 16) * (d : ℝ) /
          (16 * (hardCoordinateCount d : ℝ)) := by
      unfold hardLowerConstant
      field_simp [heps.ne', heta.ne', hD0.ne', hk.ne', henv.ne']
      <;> ring
    _ ≤ Real.log (17 / 16) := by
      apply (div_le_iff₀ (mul_pos (by norm_num) hk)).2
      have hdim := hard_dimension_le_four_coordinates hd
      nlinarith

lemma hard_rawLower_gt_eps
    {d : ℕ} (hd : 4 ≤ d)
    {eta C D eps : ℝ}
    (heta : 0 < eta) (hD : 1 < D) (hDC : D ≤ C)
    (hCexp : C < Real.exp eta)
    (heps : 0 < eps)
    (hsmall :
      2 * eta * hardPerturbation eps eta ≤ Real.log (7 / 6)) :
    eps <
      eta⁻¹ *
        ((hardCoordinateCount d : ℝ)⁻¹ / hardTotal d C D eta) *
        ((((1 / 4 : ℝ) -
          hardGibbsLow eta (hardPerturbation eps eta)) / 2) ^ 2 / 2) *
        (hardCoordinateCount d : ℝ) * 7 / 16 := by
  let gamma := hardPerturbation eps eta
  let t := eta * gamma
  have hgamma := hardPerturbation_pos heps heta
  have ht : 0 < t := mul_pos heta hgamma
  have hk : 0 < (hardCoordinateCount d : ℝ) :=
    Nat.cast_pos.mpr (hardCoordinateCount_pos hd)
  have hT := hardTotal_pos (d := d) heta hD hDC hCexp
  have hTle := hardTotal_le_three_halves
    (d := d) heta hD hDC hCexp
  have hgap :
      (1 - Real.exp (-2 * t)) ^ 2 =
        4 * Real.exp (-2 * t) * (Real.cosh t ^ 2 - 1) := by
    rw [Real.cosh_eq, show -2 * t = -(t + t) by ring,
      Real.exp_neg, Real.exp_add, Real.exp_neg]
    field_simp [Real.exp_ne_zero]
    <;> ring
  have hcosh := hardPerturbation_cosh heps.le heta
  have hcoshSq :
      Real.cosh t ^ 2 - 1 =
        Real.exp (128 * eta * eps) - 1 := by
    change Real.cosh (eta * hardPerturbation eps eta) ^ 2 - 1 =
      Real.exp (128 * eta * eps) - 1
    rw [hcosh, pow_two, ← Real.exp_add]
    congr 2
    ring
  have hdelta :
      (((1 / 4 : ℝ) - (1 / 4) * Real.exp (-2 * t)) / 2) ^ 2 / 2 =
        Real.exp (-2 * t) * (Real.cosh t ^ 2 - 1) / 32 := by
    nlinarith [hgap]
  have hraw :
      eta⁻¹ *
          ((hardCoordinateCount d : ℝ)⁻¹ / hardTotal d C D eta) *
          ((((1 / 4 : ℝ) - hardGibbsLow eta gamma) / 2) ^ 2 / 2) *
          (hardCoordinateCount d : ℝ) * 7 / 16 =
        7 * Real.exp (-2 * t) *
            (Real.exp (128 * eta * eps) - 1) /
          (512 * eta * hardTotal d C D eta) := by
    unfold hardGibbsLow
    rw [show -2 * eta * gamma = -2 * t by
      dsimp [t]
      ring, hdelta, hcoshSq]
    field_simp [heta.ne', hT.ne', hk.ne']
    <;> ring
  rw [hraw]
  have hlogpos : (0 : ℝ) < (7 / 6 : ℝ) := by norm_num
  have hneg :
      (6 / 7 : ℝ) ≤ Real.exp (-2 * t) := by
    have hsmallt : 2 * t ≤ Real.log (7 / 6) := by
      simpa [t, gamma, mul_assoc] using hsmall
    have hmono := Real.exp_le_exp.mpr (neg_le_neg hsmallt)
    have hlogexp : Real.exp (-Real.log (7 / 6 : ℝ)) = 6 / 7 := by
      rw [Real.exp_neg, Real.exp_log hlogpos]
      norm_num
    simpa only [neg_mul] using hlogexp ▸ hmono
  have hx : 0 < 128 * eta * eps := by positivity
  have hexp :
      128 * eta * eps < Real.exp (128 * eta * eps) - 1 := by
    linarith [Real.add_one_lt_exp hx.ne']
  have hexp0 : 0 ≤ Real.exp (128 * eta * eps) - 1 :=
    (le_of_lt hexp).trans' hx.le
  have hden : 0 < 512 * eta * hardTotal d C D eta := by positivity
  apply (lt_div_iff₀ hden).2
  calc
    eps * (512 * eta * hardTotal d C D eta) ≤
        eps * (512 * eta * (3 / 2)) := by
      gcongr
    _ = 7 * (6 / 7 : ℝ) * (128 * eta * eps) := by ring
    _ < 7 * (6 / 7 : ℝ) *
        (Real.exp (128 * eta * eps) - 1) := by
      gcongr
    _ ≤ 7 * Real.exp (-2 * t) *
        (Real.exp (128 * eta * eps) - 1) := by
      gcongr

end

end CausalSmith.Stat.ReverseKLTwoCoverage
