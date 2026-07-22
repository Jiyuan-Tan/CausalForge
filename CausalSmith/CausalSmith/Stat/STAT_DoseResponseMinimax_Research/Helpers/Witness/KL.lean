/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Dose-response minimax lower bound: the genuine bump-driven KL budget

The information-theoretic crux. The two witnesses share the `(A,X)`-marginal and
differ ONLY in the outcome channel `twoPointMean B (μ_ζ(a,x))`, whose means differ by
`2 μ_{+1}(a,x) = 2 λ h^α ψ((a−t_0)/h)`. The shared-base KL chain rule collapses the
joint KL to the `(A,X)`-integral of the per-fibre two-point-channel KL, the
`bernoulli_mean_channel_kl` band bounds each fibre by `2(u−v)²/B²`, and the bump
support concentrates the integral on a window of width `2h`, yielding the genuine,
NONZERO, `Θ(h^{2α+1})` per-observation budget. The product-KL tensorization then gives
the `n`-fold bound `≤ n · (single)`.
-/

import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.Helpers.Witness.Channel
import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.Helpers.Witness.Regression
import Causalean.Mathlib.InformationTheory.KLBind
import Causalean.Mathlib.InformationTheory.ProductKLLeCam

namespace CausalSmith.Stat.DoseResponseMinimax

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {d : ℕ}

private lemma doseWitnessMu_abs_le_half {alpha t0 lambda h zeta B : ℝ}
    (hzeta : |zeta| ≤ 1) (halpha : 0 < alpha) (hh : 0 < h) (hhle : h ≤ 1)
    (hlam_nonneg : 0 ≤ lambda) (hlam_le : lambda ≤ B / 2)
    (a : ℝ) (x : Fin d → ℝ) :
    |doseWitnessMu (d := d) alpha t0 lambda h zeta a x| ≤ B / 2 := by
  have hhpow_nonneg : 0 ≤ h ^ alpha := Real.rpow_nonneg hh.le alpha
  have hhpow_le : h ^ alpha ≤ 1 := by
    simpa using Real.rpow_le_one hh.le hhle halpha.le
  have hbump := doseBump_abs_le_one ((a - t0) / h)
  calc
    |doseWitnessMu (d := d) alpha t0 lambda h zeta a x|
        = |zeta| * lambda * (h ^ alpha) * |doseBump ((a - t0) / h)| := by
          rw [doseWitnessMu, abs_mul, abs_mul, abs_mul, abs_of_nonneg hlam_nonneg,
            abs_of_nonneg hhpow_nonneg]
    _ ≤ 1 * lambda * 1 * 1 := by
          gcongr
    _ = lambda := by ring
    _ ≤ B / 2 := hlam_le

private lemma doseWitnessMu_abs_le_B {alpha t0 lambda h zeta B : ℝ}
    (hzeta : |zeta| ≤ 1) (halpha : 0 < alpha) (hh : 0 < h) (hhle : h ≤ 1)
    (hlam_nonneg : 0 ≤ lambda) (hlam_le : lambda ≤ B / 2) (hB : 0 < B)
    (a : ℝ) (x : Fin d → ℝ) :
    |doseWitnessMu (d := d) alpha t0 lambda h zeta a x| ≤ B := by
  exact (doseWitnessMu_abs_le_half (d := d) hzeta halpha hh hhle hlam_nonneg hlam_le a x).trans
    (by linarith [hB])

private lemma measurableEmbedding_doseObs_mk (a : ℝ) (x : Fin d → ℝ) :
    MeasurableEmbedding (fun y : ℝ => DoseObs.mk y a x) := by
  refine MeasurableEmbedding.of_measurable_inverse (measurable_doseObs_mk a x) ?_
    measurable_doseObs_Y ?_
  · have hRange :
        Set.range (fun y : ℝ => DoseObs.mk y a x) =
          {O : DoseObs d | O.A = a ∧ O.X = x} := by
        ext O
        constructor
        · rintro ⟨y, rfl⟩
          simp
        · intro hO
          rcases O with ⟨Y, A, X⟩
          rcases hO with ⟨hA, hX⟩
          exact ⟨Y, by cases hA; cases hX; rfl⟩
    rw [hRange]
    exact (measurableSet_eq_fun (measurable_doseObs_A (d := d)) measurable_const).inter
      (measurableSet_eq_fun (measurable_doseObs_X (d := d)) measurable_const)
  · intro y
    rfl

private lemma doseChannelAX_fibre_support {p0 : (Fin d → ℝ) → ℝ} {q0 : ℝ → ℝ}
    {B alpha t0 lambda h zeta : ℝ} (p : ℝ × (Fin d → ℝ)) :
    (doseChannelAX (d := d) p0 q0 B alpha t0 lambda h zeta p)
      {O : DoseObs d | (O.A, O.X) = p}ᶜ = 0 := by
  classical
  rw [doseChannelAX_apply]
  let f : ℝ → DoseObs d := fun y => DoseObs.mk y p.1 p.2
  have hset : MeasurableSet ({O : DoseObs d | (O.A, O.X) = p}ᶜ) := by
    exact (measurableSet_eq_fun
      ((measurable_doseObs_A (d := d)).prod (measurable_doseObs_X (d := d)))
      measurable_const).compl
  rw [Measure.map_apply (measurable_doseObs_mk p.1 p.2) hset]
  have hpre : f ⁻¹' {O : DoseObs d | (O.A, O.X) = p}ᶜ = ∅ := by
    ext y
    simp [f]
  rw [hpre]
  simp

private lemma twoPointMean_ac_of_half {B u v : ℝ} (hB : 0 < B)
    (hu : |u| ≤ B / 2) (hv : |v| ≤ B / 2) :
    twoPointMean B u ≪ twoPointMean B v := by
  classical
  refine Measure.AbsolutelyContinuous.mk ?_
  intro s hs
  have hBne : B ≠ 0 := ne_of_gt hB
  have huB : |u| ≤ B := hu.trans (by linarith [hB])
  have hv_bounds := abs_le.mp hv
  have hv_plus_pos : 0 < (1 + v / B) / 2 := by
    field_simp [hBne]
    nlinarith [hv_bounds.1, hB]
  have hv_minus_pos : 0 < (1 - v / B) / 2 := by
    field_simp [hBne]
    nlinarith [hv_bounds.2, hB]
  intro hs0
  unfold twoPointMean at hs0 ⊢
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply] at hs0 ⊢
  by_cases hBs : B ∈ s
  · by_cases hnBs : -B ∈ s
    · have hpos :
          0 < ENNReal.ofReal ((1 + v / B) / 2) * Measure.dirac B s
            + ENNReal.ofReal ((1 - v / B) / 2) * Measure.dirac (-B) s := by
          simp [hBs, hnBs, ENNReal.ofReal_pos.mpr hv_plus_pos,
            ENNReal.ofReal_pos.mpr hv_minus_pos]
      exact (hpos.ne' hs0).elim
    · have hpos :
          0 < ENNReal.ofReal ((1 + v / B) / 2) * Measure.dirac B s
            + ENNReal.ofReal ((1 - v / B) / 2) * Measure.dirac (-B) s := by
          simp [hBs, hnBs, ENNReal.ofReal_pos.mpr hv_plus_pos]
      exact (hpos.ne' hs0).elim
  · by_cases hnBs : -B ∈ s
    · have hpos :
          0 < ENNReal.ofReal ((1 + v / B) / 2) * Measure.dirac B s
            + ENNReal.ofReal ((1 - v / B) / 2) * Measure.dirac (-B) s := by
          simp [hBs, hnBs, ENNReal.ofReal_pos.mpr hv_minus_pos]
      exact (hpos.ne' hs0).elim
    · simp [hBs, hnBs]

private lemma M_sub_eta0_nonneg_of_q0_window {q0 : ℝ → ℝ} {M eta0 t0 eps0 h : ℝ}
    (hh : 0 < h) (hhe : h ≤ eps0)
    (hq0_nonneg : ∀ a, 0 ≤ q0 a)
    (hq0_bd : ∀ a ∈ doseWindow t0 eps0, q0 a ≤ M - eta0) :
    0 ≤ M - eta0 := by
  have heps_pos : 0 < eps0 := lt_of_lt_of_le hh hhe
  have ht0win : t0 ∈ doseWindow t0 eps0 := by
    rw [doseWindow, Set.mem_Icc]
    constructor <;> linarith
  exact (hq0_nonneg t0).trans (hq0_bd t0 ht0win)

private lemma doseBump_sq_pointwise_le_window {q0 : ℝ → ℝ} {M eta0 t0 eps0 h : ℝ}
    (hh : 0 < h) (hhe : h ≤ eps0)
    (hq0_nonneg : ∀ a, 0 ≤ q0 a)
    (hq0_bd : ∀ a ∈ doseWindow t0 eps0, q0 a ≤ M - eta0) (a : ℝ) :
    doseBump ((a - t0) / h) ^ 2 * q0 a ≤
      (M - eta0) * (Set.Ioo (t0 - h) (t0 + h)).indicator (fun _ : ℝ => (1 : ℝ)) a := by
  classical
  have hMeta_nonneg := M_sub_eta0_nonneg_of_q0_window (q0 := q0) (M := M)
    (eta0 := eta0) (t0 := t0) (eps0 := eps0) (h := h) hh hhe hq0_nonneg hq0_bd
  by_cases ha : a ∈ Set.Ioo (t0 - h) (t0 + h)
  · have hawin : a ∈ doseWindow t0 eps0 := by
      rw [doseWindow, Set.mem_Icc]
      constructor <;> linarith [ha.1, ha.2, hhe]
    have hbump_sq : doseBump ((a - t0) / h) ^ 2 ≤ 1 := by
      have hb := doseBump_abs_le_one ((a - t0) / h)
      exact (sq_le_one_iff_abs_le_one _).mpr hb
    have hmul : doseBump ((a - t0) / h) ^ 2 * q0 a ≤ 1 * (M - eta0) := by
      exact mul_le_mul hbump_sq (hq0_bd a hawin) (hq0_nonneg a) zero_le_one
    simpa [Set.indicator, ha] using hmul
  · have habs : h ≤ |a - t0| := by
      rw [Set.mem_Ioo] at ha
      rw [not_and_or] at ha
      rcases ha with hleft | hright
      · have hle : h ≤ -(a - t0) := by linarith
        exact hle.trans (neg_le_abs (a - t0))
      · have hle : t0 + h ≤ a := le_of_not_gt hright
        exact (by linarith : h ≤ a - t0).trans (le_abs_self (a - t0))
    have hz : 1 ≤ |(a - t0) / h| := by
      rw [abs_div]
      exact (one_le_div (abs_pos.mpr (ne_of_gt hh))).mpr
        (by simpa [abs_of_pos hh] using habs)
    have hb0 : doseBump ((a - t0) / h) = 0 := doseBump_eq_zero_of_one_le_abs hz
    simp [Set.indicator, ha, hb0]

private lemma doseBump_sq_lintegral_le {q0 : ℝ → ℝ} {M eta0 t0 eps0 h : ℝ}
    (hh : 0 < h) (hhe : h ≤ eps0)
    (hq0_nonneg : ∀ a, 0 ≤ q0 a)
    (hq0_bd : ∀ a ∈ doseWindow t0 eps0, q0 a ≤ M - eta0) :
    (∫⁻ a, ENNReal.ofReal (doseBump ((a - t0) / h) ^ 2) ∂(doseAMeasure q0))
      ≤ ENNReal.ofReal (2 * (M - eta0) * h) := by
  classical
  let W : Set ℝ := Set.Ioo (t0 - h) (t0 + h)
  have hMeta_nonneg := M_sub_eta0_nonneg_of_q0_window (q0 := q0) (M := M)
    (eta0 := eta0) (t0 := t0) (eps0 := eps0) (h := h) hh hhe hq0_nonneg hq0_bd
  have hbump_le_ind :
      (fun a : ℝ => ENNReal.ofReal (doseBump ((a - t0) / h) ^ 2))
        ≤ fun a => W.indicator (fun _ : ℝ => (1 : ℝ≥0∞)) a := by
    intro a
    by_cases ha : a ∈ W
    · have hbump_sq : doseBump ((a - t0) / h) ^ 2 ≤ 1 := by
        exact (sq_le_one_iff_abs_le_one _).mpr (doseBump_abs_le_one ((a - t0) / h))
      simpa [W, Set.indicator, ha] using ENNReal.ofReal_le_ofReal hbump_sq
    · have habs : h ≤ |a - t0| := by
        change ¬ a ∈ Set.Ioo (t0 - h) (t0 + h) at ha
        rw [Set.mem_Ioo] at ha
        rw [not_and_or] at ha
        rcases ha with hleft | hright
        · have hle : h ≤ -(a - t0) := by linarith
          exact hle.trans (neg_le_abs (a - t0))
        · have hle : t0 + h ≤ a := le_of_not_gt hright
          exact (by linarith : h ≤ a - t0).trans (le_abs_self (a - t0))
      have hz : 1 ≤ |(a - t0) / h| := by
        rw [abs_div]
        exact (one_le_div (abs_pos.mpr (ne_of_gt hh))).mpr
          (by simpa [abs_of_pos hh] using habs)
      have hb0 : doseBump ((a - t0) / h) = 0 := doseBump_eq_zero_of_one_le_abs hz
      simp [W, Set.indicator, ha, hb0]
  have hmass :
      (doseAMeasure q0) W ≤ ENNReal.ofReal (M - eta0) * volume W := by
    unfold doseAMeasure
    rw [withDensity_apply _ measurableSet_Ioo]
    calc
      ∫⁻ a in W, ENNReal.ofReal (q0 a) ∂volume.restrict (Set.Icc (0 : ℝ) 1)
          ≤ ∫⁻ a in W, ENNReal.ofReal (M - eta0) ∂volume.restrict (Set.Icc (0 : ℝ) 1) := by
            refine setLIntegral_mono measurable_const ?_
            intro a ha
            have hawin : a ∈ doseWindow t0 eps0 := by
              rw [doseWindow, Set.mem_Icc]
              constructor <;> linarith [ha.1, ha.2, hhe]
            exact ENNReal.ofReal_le_ofReal (hq0_bd a hawin)
      _ = ENNReal.ofReal (M - eta0) * (volume.restrict (Set.Icc (0 : ℝ) 1)) W := by
            rw [setLIntegral_const]
      _ ≤ ENNReal.ofReal (M - eta0) * volume W := by
            gcongr
            exact (Measure.restrict_le_self :
              (volume.restrict (Set.Icc (0 : ℝ) 1) : Measure ℝ) ≤ volume)
  calc
    ∫⁻ a, ENNReal.ofReal (doseBump ((a - t0) / h) ^ 2) ∂(doseAMeasure q0)
        ≤ ∫⁻ a, W.indicator (fun _ : ℝ => (1 : ℝ≥0∞)) a ∂(doseAMeasure q0) :=
          lintegral_mono hbump_le_ind
    _ = (doseAMeasure q0) W := lintegral_indicator_one measurableSet_Ioo
    _ ≤ ENNReal.ofReal (M - eta0) * volume W := hmass
    _ = ENNReal.ofReal (M - eta0) * ENNReal.ofReal (2 * h) := by
          rw [Real.volume_Ioo]
          have hlen : (t0 + h) - (t0 - h) = 2 * h := by ring
          rw [hlen]
    _ = ENNReal.ofReal (2 * (M - eta0) * h) := by
          rw [← ENNReal.ofReal_mul hMeta_nonneg]
          congr 1
          ring

/-- Bump-support concentration: the `doseAMeasure`-integral of `ψ((a−t_0)/h)²` is at
most `2(M−η_0)·h`, because `ψ` is supported in `(t_0−h, t_0+h) ⊆` window (for
`0 < h ≤ ε_0`) where the treatment density `q0` is bounded by `M−η_0`. -/
lemma doseBump_sq_integral_le {q0 : ℝ → ℝ} {M eta0 t0 eps0 h : ℝ}
    (hh : 0 < h) (hhe : h ≤ eps0)
    (hwin : doseWindow t0 eps0 ⊆ Set.Ioo (0 : ℝ) 1)
    (hq0_nonneg : ∀ a, 0 ≤ q0 a)
    (hq0_bd : ∀ a ∈ doseWindow t0 eps0, q0 a ≤ M - eta0) :
    (∫ a, doseBump ((a - t0) / h) ^ 2 ∂(doseAMeasure q0)) ≤ 2 * (M - eta0) * h := by
  classical
  have _hwin_used := hwin
  let f : ℝ → ℝ := fun a => doseBump ((a - t0) / h) ^ 2
  have hMeta_nonneg := M_sub_eta0_nonneg_of_q0_window (q0 := q0) (M := M)
    (eta0 := eta0) (t0 := t0) (eps0 := eps0) (h := h) hh hhe hq0_nonneg hq0_bd
  have hR_nonneg : 0 ≤ 2 * (M - eta0) * h := by nlinarith
  by_cases hfint : Integrable f (doseAMeasure q0)
  · have hf_nonneg : ∀ᵐ a ∂(doseAMeasure q0), 0 ≤ f a :=
      Filter.Eventually.of_forall fun a => sq_nonneg _
    have hlin := doseBump_sq_lintegral_le (q0 := q0) (M := M) (eta0 := eta0)
      (t0 := t0) (eps0 := eps0) (h := h) hh hhe hq0_nonneg hq0_bd
    have hof :
        ENNReal.ofReal (∫ a, f a ∂(doseAMeasure q0))
          ≤ ENNReal.ofReal (2 * (M - eta0) * h) := by
      rw [ofReal_integral_eq_lintegral_ofReal hfint hf_nonneg]
      exact hlin
    exact (ENNReal.ofReal_le_ofReal_iff hR_nonneg).mp hof
  · rw [show (∫ a, doseBump ((a - t0) / h) ^ 2 ∂(doseAMeasure q0)) =
        ∫ a, f a ∂(doseAMeasure q0) by rfl]
    rw [integral_undef hfint]
    exact hR_nonneg

-- @node: dose-witness-kl-single
/-- Single-observation KL budget: the joint KL between the two witness data laws is at
most `16 λ² (M−η_0) / B² · h^{2α+1}`. GENUINE and bump-driven (NONZERO): it is the
`(A,X)`-integral of the per-fibre two-point-channel KL, not a Dirac collapse. -/
lemma doseWitness_kl_single_le {p0 : (Fin d → ℝ) → ℝ} {q0 : ℝ → ℝ}
    {B M alpha lambda eta0 t0 eps0 h : ℝ}
    (hB : 0 < B) (halpha : 0 < alpha)
    (hh : 0 < h) (hhle : h ≤ 1) (hhe : h ≤ eps0)
    (hwin : doseWindow t0 eps0 ⊆ Set.Ioo (0 : ℝ) 1)
    (hpX : IsProbabilityMeasure (doseXMeasure p0))
    (hpA : IsProbabilityMeasure (doseAMeasure q0))
    (hp0_int : (∫ x in cube d, p0 x) = 1)
    (hlam_nonneg : 0 ≤ lambda) (hlam_le : lambda ≤ B / 2)
    (hq0_nonneg : ∀ a, 0 ≤ q0 a)
    (hq0_bd : ∀ a ∈ doseWindow t0 eps0, q0 a ≤ M - eta0) :
    InformationTheory.klDiv
      (doseDataMeasure (d := d) p0 q0 B alpha t0 lambda h (-1))
      (doseDataMeasure (d := d) p0 q0 B alpha t0 lambda h 1)
      ≤ ENNReal.ofReal (16 * lambda ^ 2 * (M - eta0) / B ^ 2 * h ^ (2 * alpha + 1)) := by
  classical
  have _hp0_int_used := hp0_int
  let m : Measure (ℝ × (Fin d → ℝ)) := doseAXMeasure (d := d) p0 q0
  let κ : Kernel (ℝ × (Fin d → ℝ)) (DoseObs d) :=
    doseChannelAX (d := d) p0 q0 B alpha t0 lambda h (-1)
  let η : Kernel (ℝ × (Fin d → ℝ)) (DoseObs d) :=
    doseChannelAX (d := d) p0 q0 B alpha t0 lambda h 1
  let proj : DoseObs d → ℝ × (Fin d → ℝ) := fun O => (O.A, O.X)
  let K : ℝ := 8 * lambda ^ 2 * h ^ (2 * alpha) / B ^ 2
  have hm_prob : IsProbabilityMeasure m := doseAXMeasure_isProbabilityMeasure (d := d) hpX hpA
  letI : IsProbabilityMeasure m := hm_prob
  have hmu_neg_B : ∀ a x,
      |doseWitnessMu (d := d) alpha t0 lambda h (-1 : ℝ) a x| ≤ B := by
    intro a x
    exact doseWitnessMu_abs_le_B (d := d) (by norm_num) halpha hh hhle
      hlam_nonneg hlam_le hB a x
  have hmu_pos_B : ∀ a x,
      |doseWitnessMu (d := d) alpha t0 lambda h (1 : ℝ) a x| ≤ B := by
    intro a x
    exact doseWitnessMu_abs_le_B (d := d) (by norm_num) halpha hh hhle
      hlam_nonneg hlam_le hB a x
  have hmu_neg_half : ∀ a x,
      |doseWitnessMu (d := d) alpha t0 lambda h (-1 : ℝ) a x| ≤ B / 2 := by
    intro a x
    exact doseWitnessMu_abs_le_half (d := d) (by norm_num) halpha hh hhle
      hlam_nonneg hlam_le a x
  have hmu_pos_half : ∀ a x,
      |doseWitnessMu (d := d) alpha t0 lambda h (1 : ℝ) a x| ≤ B / 2 := by
    intro a x
    exact doseWitnessMu_abs_le_half (d := d) (by norm_num) halpha hh hhle
      hlam_nonneg hlam_le a x
  letI : IsMarkovKernel κ := by
    dsimp [κ]
    exact instIsMarkovDoseChannelAX (d := d) (p0 := p0) (q0 := q0)
      (B := B) (alpha := alpha) (t0 := t0) (lambda := lambda)
      (h := h) (zeta := -1) hB hmu_neg_B
  letI : IsMarkovKernel η := by
    dsimp [η]
    exact instIsMarkovDoseChannelAX (d := d) (p0 := p0) (q0 := q0)
      (B := B) (alpha := alpha) (t0 := t0) (lambda := lambda)
      (h := h) (zeta := 1) hB hmu_pos_B
  have hproj : Measurable proj := measurable_doseObs_A.prod measurable_doseObs_X
  have hgraph : MeasurableSet {p : (ℝ × (Fin d → ℝ)) × DoseObs d | p.1 = proj p.2} := by
    exact measurableSet_eq_fun measurable_fst (hproj.comp measurable_snd)
  have hκ_fib : ∀ b, (κ b) {ω | proj ω = b}ᶜ = 0 := by
    intro b
    dsimp [κ, proj]
    simpa using doseChannelAX_fibre_support (d := d) (p0 := p0) (q0 := q0)
      (B := B) (alpha := alpha) (t0 := t0) (lambda := lambda)
      (h := h) (zeta := -1) b
  have hη_fib : ∀ b, (η b) {ω | proj ω = b}ᶜ = 0 := by
    intro b
    dsimp [η, proj]
    simpa using doseChannelAX_fibre_support (d := d) (p0 := p0) (q0 := q0)
      (B := B) (alpha := alpha) (t0 := t0) (lambda := lambda)
      (h := h) (zeta := 1) b
  have hκη : ∀ b, κ b ≪ η b := by
    intro b
    dsimp [κ, η]
    exact (twoPointMean_ac_of_half hB (hmu_neg_half b.1 b.2) (hmu_pos_half b.1 b.2)).map
      (measurable_doseObs_mk b.1 b.2)
  haveI : MeasurableSpace.CountablyGenerated (DoseObs d) := by
    change @MeasurableSpace.CountablyGenerated (DoseObs d)
      (MeasurableSpace.comap (fun O : DoseObs d => (O.Y, O.A, O.X)) inferInstance)
    exact MeasurableSpace.CountablyGenerated.comap
      (fun O : DoseObs d => (O.Y, O.A, O.X))
  haveI :
      MeasurableSpace.CountableOrCountablyGenerated (ℝ × (Fin d → ℝ)) (DoseObs d) :=
    ⟨Or.inr inferInstance⟩
  have hchain :
      InformationTheory.klDiv
        (doseDataMeasure (d := d) p0 q0 B alpha t0 lambda h (-1))
        (doseDataMeasure (d := d) p0 q0 B alpha t0 lambda h 1)
        = ∫⁻ b, InformationTheory.klDiv (κ b) (η b) ∂m := by
    rw [doseDataMeasure_eq_AXbind, doseDataMeasure_eq_AXbind]
    exact Causalean.Mathlib.InformationTheory.Measure.klDiv_bind_eq_of_base_recording
      (m := m) (κ := κ) (η := η) (proj := proj) hproj hgraph hκ_fib hη_fib hκη
  have hfiber_bound : ∀ b,
      InformationTheory.klDiv (κ b) (η b) ≤
        ENNReal.ofReal (K * doseBump ((b.1 - t0) / h) ^ 2) := by
    intro b
    let u : ℝ := doseWitnessMu (d := d) alpha t0 lambda h (-1) b.1 b.2
    let v : ℝ := doseWitnessMu (d := d) alpha t0 lambda h 1 b.1 b.2
    have hmap :
        InformationTheory.klDiv (κ b) (η b) =
          InformationTheory.klDiv (twoPointMean B u) (twoPointMean B v) := by
      dsimp [κ, η, u, v]
      haveI : IsProbabilityMeasure (twoPointMean B u) :=
        twoPointMean_isProbabilityMeasure hB (hmu_neg_B b.1 b.2)
      haveI : IsProbabilityMeasure (twoPointMean B v) :=
        twoPointMean_isProbabilityMeasure hB (hmu_pos_B b.1 b.2)
      exact Causalean.Mathlib.InformationTheory.Measure.klDiv_map_measurableEmbedding
        (measurableEmbedding_doseObs_mk (d := d) b.1 b.2)
    have hgap :
        2 * (u - v) ^ 2 / B ^ 2 = K * doseBump ((b.1 - t0) / h) ^ 2 := by
      dsimp [u, v, K]
      rw [doseWitnessMu, doseWitnessMu]
      have hp : (h ^ alpha) ^ 2 = h ^ (2 * alpha) := by
        calc
          (h ^ alpha) ^ 2 = h ^ (alpha * 2) := (Real.rpow_mul_natCast hh.le alpha 2).symm
          _ = h ^ (2 * alpha) := by ring_nf
      rw [show ((-1 : ℝ) * lambda * h ^ alpha * doseBump ((b.1 - t0) / h)) -
          (1 * lambda * h ^ alpha * doseBump ((b.1 - t0) / h)) =
          -2 * lambda * h ^ alpha * doseBump ((b.1 - t0) / h) by ring]
      rw [show (-2 * lambda * h ^ alpha * doseBump ((b.1 - t0) / h)) ^ 2 =
          4 * lambda ^ 2 * (h ^ alpha) ^ 2 * doseBump ((b.1 - t0) / h) ^ 2 by ring]
      rw [hp]
      ring
    calc
      InformationTheory.klDiv (κ b) (η b)
          = InformationTheory.klDiv (twoPointMean B u) (twoPointMean B v) := hmap
      _ ≤ ENNReal.ofReal (2 * (u - v) ^ 2 / B ^ 2) :=
          bernoulli_mean_channel_kl B u v hB (hmu_neg_half b.1 b.2) (hmu_pos_half b.1 b.2)
      _ = ENNReal.ofReal (K * doseBump ((b.1 - t0) / h) ^ 2) := by rw [hgap]
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    positivity
  have hbump_meas_A : Measurable fun a : ℝ => doseBump ((a - t0) / h) ^ 2 := by
    exact (measurable_doseBump.comp
      (by fun_prop : Measurable fun a : ℝ => (a - t0) / h)).pow_const 2
  have hbump_meas_m : AEStronglyMeasurable
      (fun b : ℝ × (Fin d → ℝ) => doseBump ((b.1 - t0) / h) ^ 2) m :=
    (hbump_meas_A.comp measurable_fst).aestronglyMeasurable
  have hKb_int : Integrable
      (fun b : ℝ × (Fin d → ℝ) => K * doseBump ((b.1 - t0) / h) ^ 2) m := by
    refine Integrable.of_bound
      (((hbump_meas_A.comp measurable_fst).const_mul K).aestronglyMeasurable) K ?_
    refine Filter.Eventually.of_forall fun b => ?_
    have hb : doseBump ((b.1 - t0) / h) ^ 2 ≤ 1 := by
      exact (sq_le_one_iff_abs_le_one _).mpr (doseBump_abs_le_one ((b.1 - t0) / h))
    have hb0 : 0 ≤ doseBump ((b.1 - t0) / h) ^ 2 := sq_nonneg _
    rw [Real.norm_of_nonneg (mul_nonneg hK_nonneg hb0)]
    nlinarith
  have hKb_nonneg : ∀ᵐ b ∂m, 0 ≤ K * doseBump ((b.1 - t0) / h) ^ 2 :=
    Filter.Eventually.of_forall fun b => mul_nonneg hK_nonneg (sq_nonneg _)
  have hlin_K :
      (∫⁻ b, ENNReal.ofReal (K * doseBump ((b.1 - t0) / h) ^ 2) ∂m)
        = ENNReal.ofReal (∫ b, K * doseBump ((b.1 - t0) / h) ^ 2 ∂m) := by
    rw [ofReal_integral_eq_lintegral_ofReal hKb_int hKb_nonneg]
  have hbump_int_m :
      ∫ b, doseBump ((b.1 - t0) / h) ^ 2 ∂m =
        ∫ a, doseBump ((a - t0) / h) ^ 2 ∂(doseAMeasure q0) := by
    have hmapint := integral_map (μ := m) (φ := fun b : ℝ × (Fin d → ℝ) => b.1)
      (f := fun a : ℝ => doseBump ((a - t0) / h) ^ 2)
      measurable_fst.aemeasurable hbump_meas_A.aestronglyMeasurable
    rw [doseAXMeasure_map_fst (d := d) (p0 := p0) (q0 := q0) hpX] at hmapint
    exact hmapint.symm
  have hreal_int :
      ∫ b, K * doseBump ((b.1 - t0) / h) ^ 2 ∂m ≤
        K * (2 * (M - eta0) * h) := by
    rw [integral_const_mul]
    rw [hbump_int_m]
    exact mul_le_mul_of_nonneg_left
      (doseBump_sq_integral_le (q0 := q0) (M := M) (eta0 := eta0)
        (t0 := t0) (eps0 := eps0) (h := h) hh hhe hwin hq0_nonneg hq0_bd)
      hK_nonneg
  calc
    InformationTheory.klDiv
        (doseDataMeasure (d := d) p0 q0 B alpha t0 lambda h (-1))
        (doseDataMeasure (d := d) p0 q0 B alpha t0 lambda h 1)
        = ∫⁻ b, InformationTheory.klDiv (κ b) (η b) ∂m := hchain
    _ ≤ ∫⁻ b, ENNReal.ofReal (K * doseBump ((b.1 - t0) / h) ^ 2) ∂m :=
        lintegral_mono hfiber_bound
    _ = ENNReal.ofReal (∫ b, K * doseBump ((b.1 - t0) / h) ^ 2 ∂m) := hlin_K
    _ ≤ ENNReal.ofReal (K * (2 * (M - eta0) * h)) :=
        ENNReal.ofReal_le_ofReal hreal_int
    _ = ENNReal.ofReal (16 * lambda ^ 2 * (M - eta0) / B ^ 2 * h ^ (2 * alpha + 1)) := by
      congr 1
      dsimp [K]
      have hp : h ^ (2 * alpha) * h = h ^ (2 * alpha + 1) := by
        calc
          h ^ (2 * alpha) * h = h ^ (2 * alpha) * h ^ (1 : ℝ) := by
            rw [Real.rpow_one]
          _ = h ^ (2 * alpha + 1) := by
            rw [← Real.rpow_add hh]
      rw [← hp]
      field_simp [ne_of_gt hB]
      ring

private lemma doseWitness_kl_ne_top_of_half {p0 : (Fin d → ℝ) → ℝ} {q0 : ℝ → ℝ}
    {B alpha lambda t0 h zeta₁ zeta₂ : ℝ}
    (hB : 0 < B)
    (hpX : IsProbabilityMeasure (doseXMeasure p0))
    (hpA : IsProbabilityMeasure (doseAMeasure q0))
    (hmu₁ : ∀ a x, |doseWitnessMu (d := d) alpha t0 lambda h zeta₁ a x| ≤ B / 2)
    (hmu₂ : ∀ a x, |doseWitnessMu (d := d) alpha t0 lambda h zeta₂ a x| ≤ B / 2) :
    InformationTheory.klDiv
      (doseDataMeasure (d := d) p0 q0 B alpha t0 lambda h zeta₁)
      (doseDataMeasure (d := d) p0 q0 B alpha t0 lambda h zeta₂) ≠ ∞ := by
  classical
  let m : Measure (ℝ × (Fin d → ℝ)) := doseAXMeasure (d := d) p0 q0
  let κ : Kernel (ℝ × (Fin d → ℝ)) (DoseObs d) :=
    doseChannelAX (d := d) p0 q0 B alpha t0 lambda h zeta₁
  let η : Kernel (ℝ × (Fin d → ℝ)) (DoseObs d) :=
    doseChannelAX (d := d) p0 q0 B alpha t0 lambda h zeta₂
  let proj : DoseObs d → ℝ × (Fin d → ℝ) := fun O => (O.A, O.X)
  have hm_prob : IsProbabilityMeasure m := doseAXMeasure_isProbabilityMeasure (d := d) hpX hpA
  letI : IsProbabilityMeasure m := hm_prob
  have hmu₁_B : ∀ a x,
      |doseWitnessMu (d := d) alpha t0 lambda h zeta₁ a x| ≤ B := by
    intro a x
    exact (hmu₁ a x).trans (by linarith [hB])
  have hmu₂_B : ∀ a x,
      |doseWitnessMu (d := d) alpha t0 lambda h zeta₂ a x| ≤ B := by
    intro a x
    exact (hmu₂ a x).trans (by linarith [hB])
  letI : IsMarkovKernel κ := by
    dsimp [κ]
    exact instIsMarkovDoseChannelAX (d := d) (p0 := p0) (q0 := q0)
      (B := B) (alpha := alpha) (t0 := t0) (lambda := lambda)
      (h := h) (zeta := zeta₁) hB hmu₁_B
  letI : IsMarkovKernel η := by
    dsimp [η]
    exact instIsMarkovDoseChannelAX (d := d) (p0 := p0) (q0 := q0)
      (B := B) (alpha := alpha) (t0 := t0) (lambda := lambda)
      (h := h) (zeta := zeta₂) hB hmu₂_B
  have hproj : Measurable proj := measurable_doseObs_A.prod measurable_doseObs_X
  have hgraph : MeasurableSet {p : (ℝ × (Fin d → ℝ)) × DoseObs d | p.1 = proj p.2} := by
    exact measurableSet_eq_fun measurable_fst (hproj.comp measurable_snd)
  have hκ_fib : ∀ b, (κ b) {ω | proj ω = b}ᶜ = 0 := by
    intro b
    dsimp [κ, proj]
    simpa using doseChannelAX_fibre_support (d := d) (p0 := p0) (q0 := q0)
      (B := B) (alpha := alpha) (t0 := t0) (lambda := lambda)
      (h := h) (zeta := zeta₁) b
  have hη_fib : ∀ b, (η b) {ω | proj ω = b}ᶜ = 0 := by
    intro b
    dsimp [η, proj]
    simpa using doseChannelAX_fibre_support (d := d) (p0 := p0) (q0 := q0)
      (B := B) (alpha := alpha) (t0 := t0) (lambda := lambda)
      (h := h) (zeta := zeta₂) b
  have hκη : ∀ b, κ b ≪ η b := by
    intro b
    dsimp [κ, η]
    exact (twoPointMean_ac_of_half hB (hmu₁ b.1 b.2) (hmu₂ b.1 b.2)).map
      (measurable_doseObs_mk b.1 b.2)
  haveI : MeasurableSpace.CountablyGenerated (DoseObs d) := by
    change @MeasurableSpace.CountablyGenerated (DoseObs d)
      (MeasurableSpace.comap (fun O : DoseObs d => (O.Y, O.A, O.X)) inferInstance)
    exact MeasurableSpace.CountablyGenerated.comap
      (fun O : DoseObs d => (O.Y, O.A, O.X))
  haveI :
      MeasurableSpace.CountableOrCountablyGenerated (ℝ × (Fin d → ℝ)) (DoseObs d) :=
    ⟨Or.inr inferInstance⟩
  have hchain :
      InformationTheory.klDiv
        (doseDataMeasure (d := d) p0 q0 B alpha t0 lambda h zeta₁)
        (doseDataMeasure (d := d) p0 q0 B alpha t0 lambda h zeta₂)
        = ∫⁻ b, InformationTheory.klDiv (κ b) (η b) ∂m := by
    rw [doseDataMeasure_eq_AXbind, doseDataMeasure_eq_AXbind]
    exact Causalean.Mathlib.InformationTheory.Measure.klDiv_bind_eq_of_base_recording
      (m := m) (κ := κ) (η := η) (proj := proj) hproj hgraph hκ_fib hη_fib hκη
  have hfiber_le_two : ∀ b, InformationTheory.klDiv (κ b) (η b) ≤ ENNReal.ofReal (2 : ℝ) := by
    intro b
    let u : ℝ := doseWitnessMu (d := d) alpha t0 lambda h zeta₁ b.1 b.2
    let v : ℝ := doseWitnessMu (d := d) alpha t0 lambda h zeta₂ b.1 b.2
    have hmap :
        InformationTheory.klDiv (κ b) (η b) =
          InformationTheory.klDiv (twoPointMean B u) (twoPointMean B v) := by
      dsimp [κ, η, u, v]
      haveI : IsProbabilityMeasure (twoPointMean B u) :=
        twoPointMean_isProbabilityMeasure hB (hmu₁_B b.1 b.2)
      haveI : IsProbabilityMeasure (twoPointMean B v) :=
        twoPointMean_isProbabilityMeasure hB (hmu₂_B b.1 b.2)
      exact Causalean.Mathlib.InformationTheory.Measure.klDiv_map_measurableEmbedding
        (measurableEmbedding_doseObs_mk (d := d) b.1 b.2)
    have hquad : 2 * (u - v) ^ 2 / B ^ 2 ≤ 2 := by
      have hdiff : |u - v| ≤ B := by
        have hu := abs_le.mp (hmu₁ b.1 b.2)
        have hv := abs_le.mp (hmu₂ b.1 b.2)
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      have hsq : (u - v) ^ 2 ≤ B ^ 2 := by
        rw [← sq_abs (u - v)]
        nlinarith [sq_nonneg (B - |u - v|), abs_nonneg (u - v), hdiff]
      field_simp [ne_of_gt hB]
      nlinarith
    calc
      InformationTheory.klDiv (κ b) (η b)
          = InformationTheory.klDiv (twoPointMean B u) (twoPointMean B v) := hmap
      _ ≤ ENNReal.ofReal (2 * (u - v) ^ 2 / B ^ 2) :=
          bernoulli_mean_channel_kl B u v hB (hmu₁ b.1 b.2) (hmu₂ b.1 b.2)
      _ ≤ ENNReal.ofReal (2 : ℝ) := ENNReal.ofReal_le_ofReal hquad
  have hlt :
      (∫⁻ b, InformationTheory.klDiv (κ b) (η b) ∂m) < ∞ := by
    calc
      ∫⁻ b, InformationTheory.klDiv (κ b) (η b) ∂m
          ≤ ∫⁻ _b, ENNReal.ofReal (2 : ℝ) ∂m := lintegral_mono hfiber_le_two
      _ = ENNReal.ofReal (2 : ℝ) * m Set.univ := by rw [lintegral_const]
      _ = ENNReal.ofReal (2 : ℝ) := by simp [m, hm_prob.measure_univ]
      _ < ∞ := ENNReal.ofReal_lt_top
  rw [hchain]
  exact ne_of_lt hlt

/-- The two single-observation witness laws are mutually absolutely continuous and have
integrable log-likelihood ratio (each fibre channel has positive mass on both atoms
`{B,−B}`, so the rn-derivative is bounded). These are the hypotheses of
`productKL_tensorization_iid`. -/
lemma doseWitness_single_ac_and_int {p0 : (Fin d → ℝ) → ℝ} {q0 : ℝ → ℝ}
    {B alpha lambda t0 h : ℝ}
    (hB : 0 < B)
    (hpX : IsProbabilityMeasure (doseXMeasure p0))
    (hpA : IsProbabilityMeasure (doseAMeasure q0))
    (hmu : ∀ a x, |doseWitnessMu (d := d) alpha t0 lambda h (1 : ℝ) a x| ≤ B / 2)
    (hmu' : ∀ a x, |doseWitnessMu (d := d) alpha t0 lambda h (-1 : ℝ) a x| ≤ B / 2) :
    (doseDataMeasure (d := d) p0 q0 B alpha t0 lambda h (-1)
        ≪ doseDataMeasure (d := d) p0 q0 B alpha t0 lambda h 1) ∧
      (doseDataMeasure (d := d) p0 q0 B alpha t0 lambda h 1
        ≪ doseDataMeasure (d := d) p0 q0 B alpha t0 lambda h (-1)) ∧
      Integrable
        (MeasureTheory.llr
          (doseDataMeasure (d := d) p0 q0 B alpha t0 lambda h (-1))
          (doseDataMeasure (d := d) p0 q0 B alpha t0 lambda h 1))
        (doseDataMeasure (d := d) p0 q0 B alpha t0 lambda h (-1)) := by
  have hKL_neg_pos : InformationTheory.klDiv
      (doseDataMeasure (d := d) p0 q0 B alpha t0 lambda h (-1))
      (doseDataMeasure (d := d) p0 q0 B alpha t0 lambda h 1) ≠ ∞ :=
    doseWitness_kl_ne_top_of_half (d := d) (p0 := p0) (q0 := q0)
      (B := B) (alpha := alpha) (lambda := lambda) (t0 := t0) (h := h)
      (zeta₁ := -1) (zeta₂ := 1) hB hpX hpA hmu' hmu
  have hKL_pos_neg : InformationTheory.klDiv
      (doseDataMeasure (d := d) p0 q0 B alpha t0 lambda h 1)
      (doseDataMeasure (d := d) p0 q0 B alpha t0 lambda h (-1)) ≠ ∞ :=
    doseWitness_kl_ne_top_of_half (d := d) (p0 := p0) (q0 := q0)
      (B := B) (alpha := alpha) (lambda := lambda) (t0 := t0) (h := h)
      (zeta₁ := 1) (zeta₂ := -1) hB hpX hpA hmu hmu'
  have hneg_pos := InformationTheory.klDiv_ne_top_iff.mp hKL_neg_pos
  have hpos_neg := InformationTheory.klDiv_ne_top_iff.mp hKL_pos_neg
  exact ⟨hneg_pos.1, hpos_neg.1, hneg_pos.2⟩

-- @node: dose-witness-kl-nfold
/-- `n`-fold KL budget via product tensorization: the KL between the `n`-fold product
witness laws is at most `n · (single-obs budget)`. -/
lemma doseWitness_kl_nfold_le {p0 : (Fin d → ℝ) → ℝ} {q0 : ℝ → ℝ}
    {B M alpha lambda eta0 t0 eps0 h : ℝ} (n : ℕ)
    (hB : 0 < B) (halpha : 0 < alpha)
    (hh : 0 < h) (hhle : h ≤ 1) (hhe : h ≤ eps0)
    (hwin : doseWindow t0 eps0 ⊆ Set.Ioo (0 : ℝ) 1)
    (hpX : IsProbabilityMeasure (doseXMeasure p0))
    (hpA : IsProbabilityMeasure (doseAMeasure q0))
    (hp0_int : (∫ x in cube d, p0 x) = 1)
    (hlam_nonneg : 0 ≤ lambda) (hlam_le : lambda ≤ B / 2)
    (hmu : ∀ a x, |doseWitnessMu (d := d) alpha t0 lambda h (1 : ℝ) a x| ≤ B / 2)
    (hmu' : ∀ a x, |doseWitnessMu (d := d) alpha t0 lambda h (-1 : ℝ) a x| ≤ B / 2)
    (hq0_nonneg : ∀ a, 0 ≤ q0 a)
    (hq0_bd : ∀ a ∈ doseWindow t0 eps0, q0 a ≤ M - eta0) :
    InformationTheory.klDiv
      (Measure.pi fun _ : Fin n =>
        doseDataMeasure (d := d) p0 q0 B alpha t0 lambda h (-1))
      (Measure.pi fun _ : Fin n =>
        doseDataMeasure (d := d) p0 q0 B alpha t0 lambda h 1)
      ≤ ENNReal.ofReal
          ((n : ℝ) * (16 * lambda ^ 2 * (M - eta0) / B ^ 2 * h ^ (2 * alpha + 1))) := by
  classical
  let μ : Measure (DoseObs d) :=
    doseDataMeasure (d := d) p0 q0 B alpha t0 lambda h (-1)
  let ν : Measure (DoseObs d) :=
    doseDataMeasure (d := d) p0 q0 B alpha t0 lambda h 1
  let C : ℝ := 16 * lambda ^ 2 * (M - eta0) / B ^ 2 * h ^ (2 * alpha + 1)
  have hmu_neg_B : ∀ a x,
      |doseWitnessMu (d := d) alpha t0 lambda h (-1 : ℝ) a x| ≤ B := by
    intro a x
    exact (hmu' a x).trans (by linarith [hB])
  have hmu_pos_B : ∀ a x,
      |doseWitnessMu (d := d) alpha t0 lambda h (1 : ℝ) a x| ≤ B := by
    intro a x
    exact (hmu a x).trans (by linarith [hB])
  haveI : IsProbabilityMeasure μ := by
    dsimp [μ]
    exact doseDataMeasure_isProbabilityMeasure (d := d) (p0 := p0) (q0 := q0)
      (B := B) (alpha := alpha) (t0 := t0) (lambda := lambda)
      (h := h) (zeta := -1) hB hpX hpA hmu_neg_B
  haveI : IsProbabilityMeasure ν := by
    dsimp [ν]
    exact doseDataMeasure_isProbabilityMeasure (d := d) (p0 := p0) (q0 := q0)
      (B := B) (alpha := alpha) (t0 := t0) (lambda := lambda)
      (h := h) (zeta := 1) hB hpX hpA hmu_pos_B
  have hac_int := doseWitness_single_ac_and_int (d := d) (p0 := p0) (q0 := q0)
    (B := B) (alpha := alpha) (lambda := lambda) (t0 := t0) (h := h)
    hB hpX hpA hmu hmu'
  have hac : μ ≪ ν := by
    simpa [μ, ν] using hac_int.1
  have hac' : ν ≪ μ := by
    simpa [μ, ν] using hac_int.2.1
  have hint : Integrable (MeasureTheory.llr μ ν) μ := by
    simpa [μ, ν] using hac_int.2.2
  have htensor :
      (InformationTheory.klDiv
        (Measure.pi fun _ : Fin n => μ)
        (Measure.pi fun _ : Fin n => ν)).toReal
        ≤ (n : ℝ) * (InformationTheory.klDiv μ ν).toReal :=
    (Causalean.Mathlib.InformationTheory.productKL_tensorization_iid
      n μ ν hac hac' hint).apply
  have hsingle :
      InformationTheory.klDiv μ ν ≤ ENNReal.ofReal C := by
    dsimp [μ, ν, C]
    exact doseWitness_kl_single_le (d := d) (p0 := p0) (q0 := q0)
      (B := B) (M := M) (alpha := alpha) (lambda := lambda)
      (eta0 := eta0) (t0 := t0) (eps0 := eps0) (h := h)
      hB halpha hh hhle hhe hwin hpX hpA hp0_int
      hlam_nonneg hlam_le hq0_nonneg hq0_bd
  have hMeta_nonneg := M_sub_eta0_nonneg_of_q0_window (q0 := q0) (M := M)
    (eta0 := eta0) (t0 := t0) (eps0 := eps0) (h := h) hh hhe hq0_nonneg hq0_bd
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  have hsingle_toReal : (InformationTheory.klDiv μ ν).toReal ≤ C := by
    have hmono := ENNReal.toReal_mono (by exact ENNReal.ofReal_ne_top) hsingle
    simpa [ENNReal.toReal_ofReal hC_nonneg] using hmono
  have hprod_toReal :
      (InformationTheory.klDiv
        (Measure.pi fun _ : Fin n => μ)
        (Measure.pi fun _ : Fin n => ν)).toReal ≤ (n : ℝ) * C := by
    calc
      (InformationTheory.klDiv
        (Measure.pi fun _ : Fin n => μ)
        (Measure.pi fun _ : Fin n => ν)).toReal
          ≤ (n : ℝ) * (InformationTheory.klDiv μ ν).toReal := htensor
      _ ≤ (n : ℝ) * C :=
          mul_le_mul_of_nonneg_left hsingle_toReal (Nat.cast_nonneg n)
  have hprod_ne_top :
      InformationTheory.klDiv
        (Measure.pi fun _ : Fin n => μ)
        (Measure.pi fun _ : Fin n => ν) ≠ ∞ := by
    exact InformationTheory.klDiv_ne_top
      (Causalean.Mathlib.InformationTheory.pi_iid_absolutelyContinuous μ ν hac n)
      (Causalean.Mathlib.InformationTheory.pi_iid_llr_integrable μ ν hac hint n)
  calc
    InformationTheory.klDiv
      (Measure.pi fun _ : Fin n =>
        doseDataMeasure (d := d) p0 q0 B alpha t0 lambda h (-1))
      (Measure.pi fun _ : Fin n =>
        doseDataMeasure (d := d) p0 q0 B alpha t0 lambda h 1)
        = InformationTheory.klDiv
            (Measure.pi fun _ : Fin n => μ)
            (Measure.pi fun _ : Fin n => ν) := by rfl
    _ = ENNReal.ofReal
          (InformationTheory.klDiv
            (Measure.pi fun _ : Fin n => μ)
            (Measure.pi fun _ : Fin n => ν)).toReal := by
          exact (ENNReal.ofReal_toReal hprod_ne_top).symm
    _ ≤ ENNReal.ofReal ((n : ℝ) * C) :=
          ENNReal.ofReal_le_ofReal hprod_toReal
    _ = ENNReal.ofReal
          ((n : ℝ) * (16 * lambda ^ 2 * (M - eta0) / B ^ 2 * h ^ (2 * alpha + 1))) := by
          rfl

end CausalSmith.Stat.DoseResponseMinimax
