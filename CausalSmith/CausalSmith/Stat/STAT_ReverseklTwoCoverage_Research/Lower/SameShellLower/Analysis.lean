import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Lower.HardFamilyCore
import Mathlib.Analysis.SpecialFunctions.Arcosh

set_option linter.unusedVariables false

namespace CausalSmith.Stat.ReverseKLTwoCoverage

open scoped Topology

noncomputable section

private def hardDenominator (D eta s : ℝ) : ℝ :=
  Real.exp (eta * s) - 2 * hardP D * D * Real.cosh (eta * s)

lemma hardP_mul_D {D : ℝ} (hD : 0 < D) :
    2 * hardP D * D = 1 / 2 := by
  unfold hardP
  field_simp
  ring

lemma hardDenominator_zero {D eta : ℝ} (hD : 0 < D) :
    hardDenominator D eta 0 = 1 / 2 := by
  simp [hardDenominator, hardP_mul_D hD]
  norm_num

lemma hardT_zero {D eta : ℝ} (hD : 0 < D) :
    hardT D eta 0 = 2 * D - 1 := by
  rw [hardT]
  simp [hardP_mul_D hD]
  unfold hardP
  field_simp
  ring

lemma hardBeta_zero {D eta : ℝ} (hD : 0 < D) :
    hardBeta D eta 0 = eta⁻¹ * Real.log (2 * D - 1) := by
  simp [hardBeta, hardT_zero hD]

lemma hardBeta_zero_pos {D eta : ℝ}
    (heta : 0 < eta) (hD : 1 < D) :
    0 < hardBeta D eta 0 := by
  rw [hardBeta_zero (lt_trans zero_lt_one hD)]
  exact mul_pos (inv_pos.mpr heta)
    (Real.log_pos (by linarith))

lemma hardBeta_zero_lt_one {D eta : ℝ}
    (heta : 0 < eta) (hDexp : 2 * D - 1 < Real.exp eta)
    (hD : 1 < D) :
    hardBeta D eta 0 < 1 := by
  rw [hardBeta_zero (lt_trans zero_lt_one hD)]
  have hlog : Real.log (2 * D - 1) < eta := by
    rw [← Real.log_exp eta]
    exact Real.strictMonoOn_log
      (by linarith : 0 < 2 * D - 1) (Real.exp_pos eta) hDexp
  rw [inv_mul_lt_one₀ heta]
  exact hlog

lemma continuousAt_hardBeta_zero {D eta : ℝ}
    (heta : 0 < eta) (hD : 1 < D) :
    ContinuousAt (hardBeta D eta) 0 := by
  have harg : ContinuousAt (fun s : ℝ => eta * s) 0 :=
    continuousAt_const.mul continuousAt_id
  have hexp : ContinuousAt (fun s : ℝ => Real.exp (eta * s)) 0 :=
    Real.continuous_exp.continuousAt.comp harg
  have hcosh : ContinuousAt (fun s : ℝ => Real.cosh (eta * s)) 0 :=
    Real.continuous_cosh.continuousAt.comp harg
  have hden : ContinuousAt
      (fun s : ℝ =>
        Real.exp (eta * s) -
          2 * hardP D * D * Real.cosh (eta * s)) 0 :=
    hexp.sub (continuousAt_const.mul hcosh)
  have hden_ne :
      Real.exp (eta * 0) -
          2 * hardP D * D * Real.cosh (eta * 0) ≠ 0 := by
    change hardDenominator D eta 0 ≠ 0
    rw [hardDenominator_zero (eta := eta) (lt_trans zero_lt_one hD)]
    norm_num
  have hTcont : ContinuousAt (hardT D eta) 0 := by
    unfold hardT
    exact continuousAt_const.div hden hden_ne
  have hTne : hardT D eta 0 ≠ 0 := by
    rw [hardT_zero (lt_trans zero_lt_one hD)]
    linarith
  unfold hardBeta
  exact continuousAt_const.mul (hTcont.log hTne)

lemma hardScale_pos {D eta : ℝ}
    (heta : 0 < eta) (hD : 1 < D)
    (hDexp : 2 * D - 1 < Real.exp eta) :
    0 < hardScale D eta := by
  have hD0 : 0 < D := lt_trans zero_lt_one hD
  have hden0 : 0 < hardDenominator D eta 0 := by
    rw [hardDenominator_zero hD0]
    norm_num
  have hb0 : 0 < hardBeta D eta 0 :=
    hardBeta_zero_pos heta hD
  have hb1 : hardBeta D eta 0 < 1 :=
    hardBeta_zero_lt_one heta hDexp hD
  have hden_cont : ContinuousAt (hardDenominator D eta) 0 := by
    unfold hardDenominator hardP
    fun_prop
  have hb_cont : ContinuousAt (hardBeta D eta) 0 :=
    continuousAt_hardBeta_zero heta hD
  have hhi0 : 0 < (1 : ℝ) - 0 - hardBeta D eta 0 := by
    linarith
  have hev :
      ∀ᶠ s in 𝓝 (0 : ℝ),
        0 < hardDenominator D eta s ∧
        s < hardBeta D eta s ∧
        hardBeta D eta s < 1 - s := by
    filter_upwards
      [hden_cont.eventually (isOpen_Ioi.mem_nhds hden0),
       (hb_cont.sub continuousAt_id).eventually
          (isOpen_Ioi.mem_nhds (by simpa using hb0)),
       ((continuousAt_const.sub continuousAt_id).sub hb_cont).eventually
          (isOpen_Ioi.mem_nhds hhi0)]
      with s hsden hslow hshigh
    exact ⟨hsden, by simpa using hslow, by simpa using hshigh⟩
  rcases Metric.eventually_nhds_iff.mp hev with ⟨r, hr, hev_r⟩
  let g : ℝ := r / 2
  have hg : 0 < g := by dsimp [g]; positivity
  have hgmem :
      g ∈ {g : ℝ | 0 < g ∧ ∀ s ∈ Set.Icc (0 : ℝ) g,
        0 < Real.exp (eta * s) -
            2 * hardP D * D * Real.cosh (eta * s) ∧
        s ≤ eta⁻¹ * Real.log (hardT D eta s) ∧
        eta⁻¹ * Real.log (hardT D eta s) ≤ 1 - s} := by
    refine ⟨hg, ?_⟩
    intro s hs
    have hdist : dist s 0 < r := by
      have hs0 : 0 ≤ s := hs.1
      have hsg : s ≤ r / 2 := hs.2
      rw [Real.dist_eq]
      simp only [sub_zero, abs_of_nonneg hs0]
      linarith
    have h := hev_r hdist
    have hden : 0 <
        Real.exp (eta * s) -
          2 * hardP D * D * Real.cosh (eta * s) := by
      simpa [hardDenominator] using h.1
    exact ⟨hden, h.2.1.le, h.2.2.le⟩
  have hbdd :
      BddAbove {g : ℝ | 0 < g ∧ ∀ s ∈ Set.Icc (0 : ℝ) g,
        0 < Real.exp (eta * s) -
            2 * hardP D * D * Real.cosh (eta * s) ∧
        s ≤ eta⁻¹ * Real.log (hardT D eta s) ∧
        eta⁻¹ * Real.log (hardT D eta s) ≤ 1 - s} := by
    refine ⟨1 / 2, ?_⟩
    rintro a ⟨ha, hall⟩
    have h := hall a ⟨ha.le, le_rfl⟩
    linarith [h.2.1, h.2.2]
  exact lt_of_lt_of_le hg (le_csSup hbdd hgmem)

lemma hardAccuracyRange_pos {C D eta : ℝ}
    (heta : 0 < eta) (hD : 1 < D)
    (hDexp : 2 * D - 1 < Real.exp eta) :
    0 < hardAccuracyRange C D eta := by
  have hs : 0 < hardScale D eta :=
    hardScale_pos heta hD hDexp
  have hm : 0 < min (hardScale D eta) (1 / 4) := by
    exact lt_min hs (by norm_num)
  have hcosh : 1 < Real.cosh (eta * min (hardScale D eta) (1 / 4)) := by
    rw [Real.one_lt_cosh]
    exact ne_of_gt (mul_pos heta hm)
  unfold hardAccuracyRange
  exact mul_pos (inv_pos.mpr (mul_pos (by norm_num) heta))
    (Real.log_pos hcosh)

lemma exists_hardAdmissible_scale {D eta : ℝ}
    (heta : 0 < eta) (hD : 1 < D)
    (hDexp : 2 * D - 1 < Real.exp eta) :
    ∃ g : ℝ, 0 < g ∧
      g ≤ min (hardScale D eta) (1 / 4) ∧
      ∀ s ∈ Set.Icc (0 : ℝ) g,
        0 < Real.exp (eta * s) -
            2 * hardP D * D * Real.cosh (eta * s) ∧
        s ≤ hardBeta D eta s ∧
        hardBeta D eta s ≤ 1 - s := by
  let S : Set ℝ :=
    {g : ℝ | 0 < g ∧ ∀ s ∈ Set.Icc (0 : ℝ) g,
      0 < Real.exp (eta * s) -
          2 * hardP D * D * Real.cosh (eta * s) ∧
      s ≤ hardBeta D eta s ∧
      hardBeta D eta s ≤ 1 - s}
  have hscale : 0 < hardScale D eta :=
    hardScale_pos heta hD hDexp
  have hSne : S.Nonempty := by
    by_contra h
    have hS : S = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    have hz : hardScale D eta = 0 := by
      unfold hardScale
      change sSup S = 0
      rw [hS]
      simp
    linarith
  rcases hSne with ⟨g0, hg0⟩
  let g := min g0 (1 / 4)
  have hg : 0 < g := lt_min hg0.1 (by norm_num)
  have hprop : ∀ s ∈ Set.Icc (0 : ℝ) g,
      0 < Real.exp (eta * s) -
          2 * hardP D * D * Real.cosh (eta * s) ∧
      s ≤ hardBeta D eta s ∧
      hardBeta D eta s ≤ 1 - s := by
    intro s hs
    exact hg0.2 s ⟨hs.1, hs.2.trans (min_le_left _ _)⟩
  have hgmem : g ∈ S := ⟨hg, hprop⟩
  have hbdd : BddAbove S := by
    refine ⟨1 / 2, ?_⟩
    rintro a ⟨ha, hall⟩
    have h := hall a ⟨ha.le, le_rfl⟩
    linarith [h.2.1, h.2.2]
  have hgscale : g ≤ hardScale D eta := by
    unfold hardScale
    exact le_csSup hbdd hgmem
  exact ⟨g, hg, le_min hgscale (min_le_right _ _), hprop⟩

lemma hardPerturbation_eq_arcosh (eps eta : ℝ) :
    hardPerturbation eps eta =
      eta⁻¹ * Real.arcosh (Real.exp (64 * eta * eps)) := by
  rfl

lemma hardPerturbation_pos {eps eta : ℝ}
    (heps : 0 < eps) (heta : 0 < eta) :
    0 < hardPerturbation eps eta := by
  rw [hardPerturbation_eq_arcosh]
  exact mul_pos (inv_pos.mpr heta)
    (Real.arcosh_pos (by
      rw [Real.one_lt_exp_iff]
      positivity))

lemma hardPerturbation_cosh {eps eta : ℝ}
    (heps : 0 ≤ eps) (heta : 0 < eta) :
    Real.cosh (eta * hardPerturbation eps eta) =
      Real.exp (64 * eta * eps) := by
  rw [hardPerturbation_eq_arcosh]
  have hexp : 1 ≤ Real.exp (64 * eta * eps) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by positivity)
  rw [show eta * (eta⁻¹ * Real.arcosh (Real.exp (64 * eta * eps))) =
      Real.arcosh (Real.exp (64 * eta * eps)) by
        field_simp]
  exact Real.cosh_arcosh hexp

lemma hardPerturbation_le_of_exp_le_cosh {eps eta g : ℝ}
    (heta : 0 < eta) (heps : 0 ≤ eps) (hg : 0 ≤ g)
    (h : Real.exp (64 * eta * eps) ≤ Real.cosh (eta * g)) :
    hardPerturbation eps eta ≤ g := by
  rw [hardPerturbation_eq_arcosh]
  have hexp0 : 0 < Real.exp (64 * eta * eps) := Real.exp_pos _
  have hcosh0 : 0 < Real.cosh (eta * g) := Real.cosh_pos _
  have harc :=
    (Real.arcosh_le_arcosh hexp0 hcosh0).2 h
  rw [Real.arcosh_cosh (mul_nonneg heta.le hg)] at harc
  rw [inv_mul_le_iff₀ heta]
  simpa [mul_comm] using harc

lemma hardPerturbation_le_of_eps_le_logCosh
    {eps eta g : ℝ} (heta : 0 < eta) (heps : 0 ≤ eps) (hg : 0 ≤ g)
    (heps_le :
      eps ≤ (64 * eta)⁻¹ * Real.log (Real.cosh (eta * g))) :
    hardPerturbation eps eta ≤ g := by
  have hmul :
      64 * eta * eps ≤ Real.log (Real.cosh (eta * g)) := by
    have h64 : 0 < 64 * eta := mul_pos (by norm_num) heta
    rw [← div_eq_inv_mul] at heps_le
    simpa [mul_comm] using (le_div_iff₀ h64).1 heps_le
  apply hardPerturbation_le_of_exp_le_cosh heta heps hg
  calc
    Real.exp (64 * eta * eps)
        ≤ Real.exp (Real.log (Real.cosh (eta * g))) :=
      Real.exp_le_exp.mpr hmul
    _ = Real.cosh (eta * g) := by
      rw [Real.exp_log (Real.cosh_pos _)]

lemma exists_hardEpsScale {C D eta : ℝ}
    (heta : 0 < eta) (hD : 1 < D)
    (hDexp : 2 * D - 1 < Real.exp eta) :
    ∃ eps1 g : ℝ,
      0 < eps1 ∧ 0 < g ∧
      g ≤ min (hardScale D eta) (1 / 4) ∧
      eps1 ≤ hardAccuracyRange C D eta ∧
      ∀ eps, 0 < eps → eps ≤ eps1 →
        let gamma := hardPerturbation eps eta
        0 < gamma ∧ gamma ≤ g ∧
          0 < Real.exp (eta * gamma) -
              2 * hardP D * D * Real.cosh (eta * gamma) ∧
          gamma ≤ hardBeta D eta gamma ∧
          hardBeta D eta gamma ≤ 1 - gamma := by
  obtain ⟨g, hg, hgM, hgood⟩ :=
    exists_hardAdmissible_scale heta hD hDexp
  let eps1 :=
    (128 * eta)⁻¹ * Real.log (Real.cosh (eta * g))
  have harg : 0 < eta * g := mul_pos heta hg
  have hlogg : 0 < Real.log (Real.cosh (eta * g)) := by
    exact Real.log_pos ((Real.one_lt_cosh).2 harg.ne')
  have heps1 : 0 < eps1 := by
    dsimp [eps1]
    exact mul_pos (inv_pos.mpr (mul_pos (by norm_num) heta)) hlogg
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
        Real.log (Real.cosh (eta * min (hardScale D eta) (1 / 4))) :=
    Real.strictMonoOn_log.monotoneOn
      (Real.cosh_pos _)
      (Real.cosh_pos _) hcosh
  have hcoef :
      (128 * eta)⁻¹ ≤ (64 * eta)⁻¹ := by
    exact (inv_le_inv₀
      (mul_pos (by norm_num) heta)
      (mul_pos (by norm_num) heta)).2 (by nlinarith)
  have hepsRange : eps1 ≤ hardAccuracyRange C D eta := by
    unfold hardAccuracyRange
    calc
      eps1 ≤ (64 * eta)⁻¹ * Real.log (Real.cosh (eta * g)) := by
        dsimp [eps1]
        exact mul_le_mul_of_nonneg_right hcoef hlogg.le
      _ ≤ (64 * eta)⁻¹ *
          Real.log
            (Real.cosh (eta * min (hardScale D eta) (1 / 4))) :=
        mul_le_mul_of_nonneg_left hlog
          (inv_nonneg.mpr (mul_pos (by norm_num) heta).le)
  refine ⟨eps1, g, heps1, hg, hgM, hepsRange, ?_⟩
  intro eps heps hepsle
  have hepsg :
      eps ≤ (64 * eta)⁻¹ * Real.log (Real.cosh (eta * g)) := by
    calc
      eps ≤ eps1 := hepsle
      _ ≤ (64 * eta)⁻¹ * Real.log (Real.cosh (eta * g)) := by
        dsimp [eps1]
        exact mul_le_mul_of_nonneg_right hcoef hlogg.le
  have hgamma0 := hardPerturbation_pos heps heta
  have hgammag :=
    hardPerturbation_le_of_eps_le_logCosh heta heps.le hg.le hepsg
  have h := hgood (hardPerturbation eps eta)
    ⟨hgamma0.le, hgammag⟩
  exact ⟨hgamma0, hgammag, h.1, h.2.1, h.2.2⟩

end

end CausalSmith.Stat.ReverseKLTwoCoverage
