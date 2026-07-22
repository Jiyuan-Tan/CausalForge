/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Sequential DR score L²(P_Z) — proof helpers

Pointwise Lipschitz constant `K_seqDR`, indicator/K bound lemmas,
`IsLittleOp` composition rules, `eLpNorm` projection lemmas, ratio
bounds, and `μ_val` MemLp — used by the headline theorem in `ScoreL2.lean`.
-/

import Causalean.Estimation.DTR.SeqDRMoment
import Causalean.Stat.Limit.Convergence
import Causalean.Stat.Orthogonality.ConditionalOp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Sequential DR score norm helpers

This module collects analytic helpers for proving L² consistency of the
two-stage sequential doubly robust DTR score. It defines the overlap envelope
`K_seqDR`, proves elementary indicator and inverse-overlap bounds, transports
L² norms from the stage histories to the observed data law, and supplies the
truncation lemma `residual_mul_error_isLittleOp_one` for residuals multiplied by
bounded nuisance errors.

The later lemmas provide the pointwise score algebra used by
`ScoreL2.lean`: `seqDR_stage0_ratio_bound`,
`seqDR_stage1_ratio_bound`, `seqDR_real_bound`, and the full almost-sure bound
`DTREstimationSystem.seqDR_score_diff_pointwise_bound`. The module also records
the square-integrability of the true stagewise regression representatives under
the corresponding history marginals.
-/

namespace Causalean
namespace Estimation
namespace DTR

open MeasureTheory ProbabilityTheory Filter Topology Causalean.PO Causalean.Stat

namespace DTREstimationSystem

variable {P : POSystem} {δ : Type} {γ : Fin 2 → Type}
  [MeasurableSpace δ] [MeasurableSingletonClass δ]
  [∀ k, MeasurableSpace (γ k)]
  [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]

/-- The sequential doubly robust Lipschitz constant combines the stagewise inverse-overlap bounds used in score continuity.

It is `1 + 2 / ε + 4 / ε² + 4 / ε³`, tracking the stage-0 inverse-overlap
weight, the stage-0 cross term, the stage-1 product inverse-overlap weight,
and the stage-1 cross terms. This exported envelope is used by the L² score
bound and its helper inequalities. -/
noncomputable def K_seqDR (ε : ℝ) : ℝ :=
  1 + 2 / ε + 4 / ε ^ 2 + 4 / ε ^ 3

omit [MeasurableSpace δ] [MeasurableSingletonClass δ] in
/-- The real-valued equality indicator is always nonnegative. -/
lemma indEq_nonneg (d d' : δ) : 0 ≤ indEq d d' := by
  unfold indEq
  split <;> norm_num

omit [MeasurableSpace δ] [MeasurableSingletonClass δ] in
/-- The real-valued equality indicator is always bounded above by one. -/
lemma indEq_le_one (d d' : δ) : indEq d d' ≤ 1 := by
  unfold indEq
  split <;> norm_num

/-- The sequential doubly robust Lipschitz constant dominates one under positive overlap. -/
lemma K_seqDR_one_le {ε : ℝ} (hε : 0 < ε) :
    1 ≤ K_seqDR ε := by
  unfold K_seqDR
  field_simp [hε.ne']
  nlinarith [sq_nonneg ε, pow_pos hε 3]

/-- The sequential doubly robust Lipschitz constant dominates the stage-zero regression coefficient bound. -/
lemma K_seqDR_mu0_le {ε : ℝ} (hε : 0 < ε) :
    1 + 1 / ε ≤ K_seqDR ε := by
  unfold K_seqDR
  field_simp [hε.ne']
  nlinarith [sq_nonneg ε, pow_pos hε 3]

/-- The sequential doubly robust Lipschitz constant dominates the stage-one regression coefficient bound. -/
lemma K_seqDR_mu1_le {ε : ℝ} (hε : 0 < ε) :
    1 / ε + 1 / ε ^ 2 ≤ K_seqDR ε := by
  unfold K_seqDR
  field_simp [hε.ne']
  nlinarith [sq_nonneg ε, pow_pos hε 3]

/-- The sequential doubly robust Lipschitz constant dominates the squared inverse-overlap bound. -/
lemma K_seqDR_inv_sq_le {ε : ℝ} (hε : 0 < ε) :
    1 / ε ^ 2 ≤ K_seqDR ε := by
  unfold K_seqDR
  field_simp [hε.ne']
  nlinarith [sq_nonneg ε, pow_pos hε 3]

/-- The sequential doubly robust Lipschitz constant dominates the cubed inverse-overlap bound. -/
lemma K_seqDR_inv_cubed_le {ε : ℝ} (hε : 0 < ε) :
    1 / ε ^ 3 ≤ K_seqDR ε := by
  unfold K_seqDR
  field_simp [hε.ne']
  nlinarith [sq_nonneg ε, pow_pos hε 3]

/-- Pulling a stage-zero function back along the full DTR data law preserves its L² norm. -/
lemma eLpNorm_comp_projS₀_eq
    (S : DTREstimationSystem P δ γ) {f : γ 0 → ℝ}
    (hf : AEStronglyMeasurable f S.P_H₀) :
    eLpNorm (fun z : γ 0 × δ × γ 1 × δ × ℝ => f (projS₀ z)) 2 S.P_Z =
      eLpNorm f 2 S.P_H₀ := by
  have hfmap : AEStronglyMeasurable f
      (S.P_Z.map (fun z : γ 0 × δ × γ 1 × δ × ℝ => projS₀ z)) := by
    simpa [P_Z_map_projS₀_eq_P_H₀ S] using hf
  rw [← P_Z_map_projS₀_eq_P_H₀ S]
  simpa [Function.comp_def] using
    (MeasureTheory.eLpNorm_map_measure
      (μ := S.P_Z) (f := fun z : γ 0 × δ × γ 1 × δ × ℝ => projS₀ z) (g := f)
      (p := 2) hfmap measurable_projS₀.aemeasurable).symm

/-- Pulling a stage-one history function back along the full DTR data law preserves its L² norm. -/
lemma eLpNorm_comp_histH₁_eq
    (S : DTREstimationSystem P δ γ) {f : γ 1 × δ × γ 0 → ℝ}
    (hf : AEStronglyMeasurable f S.P_H₁) :
    eLpNorm (fun z : γ 0 × δ × γ 1 × δ × ℝ => f (histH₁ z)) 2 S.P_Z =
      eLpNorm f 2 S.P_H₁ := by
  have hfmap : AEStronglyMeasurable f
      (S.P_Z.map (fun z : γ 0 × δ × γ 1 × δ × ℝ => histH₁ z)) := by
    simpa [P_Z_map_histH₁_eq_P_H₁ S] using hf
  rw [← P_Z_map_histH₁_eq_P_H₁ S]
  simpa [Function.comp_def] using
    (MeasureTheory.eLpNorm_map_measure
      (μ := S.P_Z) (f := fun z : γ 0 × δ × γ 1 × δ × ℝ => histH₁ z) (g := f)
      (p := 2) hfmap measurable_histH₁.aemeasurable).symm

set_option maxHeartbeats 800000 in
-- The truncation argument combines tail selection, L² monotonicity, and lpNorm coercions.
omit [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ] in
/-- Multiplying an L²-convergent error by a fixed square-integrable residual still gives a stochastic little-o L² norm.

The proof uses truncation of the residual and domination by the original error rate on the bounded part. -/
theorem residual_mul_error_isLittleOp_one
    {α : Type*} [MeasurableSpace α] {ν : Measure α} [IsProbabilityMeasure ν]
    {R : α → ℝ} (hR_meas : Measurable R) (hR_nonneg : ∀ z, 0 ≤ R z)
    (hR_memLp : MemLp R 2 ν)
    {deZ : ℕ → P.Ω → α → ℝ}
    (hdeZ_memLp : ∀ n ω, MemLp (deZ n ω) 2 ν)
    (hdeZ_meas : ∀ n ω, Measurable (deZ n ω))
    (hdeZ_bdd : ∀ n ω z, |deZ n ω z| ≤ 1)
    (hdeZ_rate :
      IsLittleOp
        (fun n ω => (eLpNorm (deZ n ω) 2 ν).toReal)
        (fun _ => (1 : ℝ)) P.μ) :
    IsLittleOp
      (fun n ω =>
        (eLpNorm (fun z => R z * |deZ n ω z|) 2 ν).toReal)
      (fun _ => (1 : ℝ)) P.μ := by
  classical
  intro δ hδ
  rw [ENNReal.tendsto_nhds_zero]
  intro κ hκ
  by_cases hκtop : κ = ⊤
  · filter_upwards with n
    simp [hκtop]
  let τ : ℝ := δ / 4
  have hτpos : 0 < τ := by
    dsimp [τ]
    linarith
  obtain ⟨M, hMpos, hMtail⟩ :=
    hR_memLp.eLpNorm_indicator_norm_ge_pos_le hR_meas.stronglyMeasurable hτpos
  let tail : α → ℝ := {z | M ≤ R z}.indicator R
  have htail_set : MeasurableSet {z : α | M ≤ R z} :=
    measurableSet_le measurable_const hR_meas
  have htail_memLp : MemLp tail 2 ν := hR_memLp.indicator htail_set
  have htail_norm_le : (eLpNorm tail 2 ν).toReal ≤ τ := by
    have hle : eLpNorm tail 2 ν ≤ ENNReal.ofReal τ := by
      have htail_eq :
          tail = ({z : α | M ≤ ‖R z‖₊}.indicator R) := by
        funext z
        by_cases hz : M ≤ R z
        · simp [tail, hz, Real.norm_eq_abs, abs_of_nonneg (hR_nonneg z)]
        · simp [tail, hz, Real.norm_eq_abs, abs_of_nonneg (hR_nonneg z)]
      simpa [htail_eq] using hMtail
    calc
      (eLpNorm tail 2 ν).toReal ≤ (ENNReal.ofReal τ).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
      _ = τ := ENNReal.toReal_ofReal hτpos.le
  have hcross_bound : ∀ n ω,
      (eLpNorm (fun z : α => R z * |deZ n ω z|) 2 ν).toReal
        ≤ M * (eLpNorm (deZ n ω) 2 ν).toReal + τ := by
    intro n ω
    let bulk : α → ℝ := fun z => M * |deZ n ω z|
    let upper : α → ℝ := fun z => bulk z + tail z
    have hbulk_memLp : MemLp bulk 2 ν := by
      have h_abs : MemLp (fun z => |deZ n ω z|) 2 ν := by
        simpa [Real.norm_eq_abs] using (hdeZ_memLp n ω).norm
      simpa [bulk, Pi.smul_apply, smul_eq_mul] using h_abs.const_smul M
    have hupper_memLp : MemLp upper 2 ν := by
      simpa [upper] using hbulk_memLp.add htail_memLp
    have hpoint : ∀ z, ‖R z * |deZ n ω z|‖ ≤ upper z := by
      intro z
      have hRz : 0 ≤ R z := hR_nonneg z
      have hdez_nonneg : 0 ≤ |deZ n ω z| := abs_nonneg _
      have hdez_le : |deZ n ω z| ≤ 1 := hdeZ_bdd n ω z
      by_cases hz : M ≤ R z
      · have htail_eq : tail z = R z := by simp [tail, hz]
        have hmain : ‖R z * |deZ n ω z|‖ ≤ R z := by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hRz, abs_of_nonneg hdez_nonneg]
          exact mul_le_of_le_one_right hRz hdez_le
        dsimp [upper, bulk]
        rw [htail_eq]
        have hbulk_nonneg : 0 ≤ M * |deZ n ω z| :=
          mul_nonneg hMpos.le hdez_nonneg
        exact hmain.trans (by nlinarith)
      · have htail_eq : tail z = 0 := by simp [tail, hz]
        have hR_le_M : R z ≤ M := le_of_not_ge hz
        have hmain : ‖R z * |deZ n ω z|‖ ≤ M * |deZ n ω z| := by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hRz, abs_of_nonneg hdez_nonneg]
          exact mul_le_mul_of_nonneg_right hR_le_M hdez_nonneg
        dsimp [upper, bulk]
        rw [htail_eq]
        simpa using hmain
    have hmono :
        lpNorm (fun z : α => R z * |deZ n ω z|) 2 ν ≤ lpNorm upper 2 ν :=
      lpNorm_mono_real hupper_memLp hpoint
    have htri :
        lpNorm upper 2 ν ≤ lpNorm bulk 2 ν + lpNorm tail 2 ν := by
      simpa [upper] using lpNorm_add_le (f := bulk) (g := tail)
        (μ := ν) hbulk_memLp (by norm_num : (1 : ENNReal) ≤ 2)
    have hbulk_norm :
        lpNorm bulk 2 ν = M * (eLpNorm (deZ n ω) 2 ν).toReal := by
      change lpNorm (M • (fun z : α => |deZ n ω z|)) 2 ν =
        M * (eLpNorm (deZ n ω) 2 ν).toReal
      rw [lpNorm_const_smul]
      rw [lpNorm_fun_abs (hdeZ_memLp n ω).aestronglyMeasurable]
      rw [← toReal_eLpNorm (hdeZ_memLp n ω).aestronglyMeasurable]
      have hcoef : (↑‖M‖₊ : ℝ) = M := by
        simp [Real.norm_eq_abs, abs_of_pos hMpos]
      rw [hcoef]
    have htail_lp : lpNorm tail 2 ν = (eLpNorm tail 2 ν).toReal := by
      rw [toReal_eLpNorm htail_memLp.aestronglyMeasurable]
    calc
      (eLpNorm (fun z : α => R z * |deZ n ω z|) 2 ν).toReal
          = lpNorm (fun z : α => R z * |deZ n ω z|) 2 ν := by
            have h_abs : Measurable (fun z : α => |deZ n ω z|) := by
              simpa [Function.comp_def] using
                (continuous_abs.measurable.comp (hdeZ_meas n ω))
            rw [toReal_eLpNorm (hR_meas.mul h_abs).aestronglyMeasurable]
      _ ≤ lpNorm upper 2 ν := hmono
      _ ≤ lpNorm bulk 2 ν + lpNorm tail 2 ν := htri
      _ = M * (eLpNorm (deZ n ω) 2 ν).toReal + (eLpNorm tail 2 ν).toReal := by
        rw [hbulk_norm, htail_lp]
      _ ≤ M * (eLpNorm (deZ n ω) 2 ν).toReal + τ :=
        add_le_add_right htail_norm_le (M * (eLpNorm (deZ n ω) 2 ν).toReal)
  have hsmall := (ENNReal.tendsto_nhds_zero.mp
    (hdeZ_rate (δ / (2 * M)) (by positivity))) κ hκ
  filter_upwards [hsmall] with n hn
  refine (measure_mono ?_).trans hn
  intro ω hω
  have hnorm_nonneg :
      0 ≤ (eLpNorm (fun z : α => R z * |deZ n ω z|) 2 ν).toReal :=
    ENNReal.toReal_nonneg
  have hlt_norm :
      δ < (eLpNorm (fun z : α => R z * |deZ n ω z|) 2 ν).toReal := by
    simpa [abs_of_nonneg hnorm_nonneg] using hω
  have hde_large : δ / (2 * M) < (eLpNorm (deZ n ω) 2 ν).toReal := by
    have hb := hcross_bound n ω
    by_contra hnot
    have hle : (eLpNorm (deZ n ω) 2 ν).toReal ≤ δ / (2 * M) :=
      le_of_not_gt hnot
    have hprod_le :
        M * (eLpNorm (deZ n ω) 2 ν).toReal ≤ δ / 2 := by
      calc
        M * (eLpNorm (deZ n ω) 2 ν).toReal
            ≤ M * (δ / (2 * M)) := mul_le_mul_of_nonneg_left hle hMpos.le
        _ = δ / 2 := by field_simp [hMpos.ne']
    have hcross_le :
        (eLpNorm (fun z : α => R z * |deZ n ω z|) 2 ν).toReal ≤ δ / 2 + τ := by
      exact hb.trans (add_le_add hprod_le le_rfl)
    dsimp [τ] at hcross_le
    nlinarith
  have hde_nonneg : 0 ≤ (eLpNorm (deZ n ω) 2 ν).toReal := ENNReal.toReal_nonneg
  simpa [abs_of_nonneg hde_nonneg] using hde_large

/-- The stage-zero weighted regression contrast is Lipschitz in the stage-zero nuisance errors under overlap. -/
lemma seqDR_stage0_ratio_bound
    {ε e ê μ0 μ0h μ1 μ1h : ℝ} (hε : 0 < ε) (he : ε ≤ e) (hê : ε ≤ ê) :
    |(μ1h - μ0h) / ê - (μ1 - μ0) / e| ≤
      (|μ1h - μ1| + |μ0h - μ0|) / ε +
        |μ1 - μ0| * |ê - e| / ε ^ 2 := by
  have he_pos : 0 < e := lt_of_lt_of_le hε he
  have hê_pos : 0 < ê := lt_of_lt_of_le hε hê
  have he_ne : e ≠ 0 := he_pos.ne'
  have hê_ne : ê ≠ 0 := hê_pos.ne'
  have hεsq_pos : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hprod_pos : 0 < ê * e := mul_pos hê_pos he_pos
  have hmul : ε ^ 2 ≤ ê * e := by
    nlinarith [mul_le_mul hê he hε.le hê_pos.le]
  have hid :
      (μ1h - μ0h) / ê - (μ1 - μ0) / e =
        ((μ1h - μ1) - (μ0h - μ0)) / ê -
          (μ1 - μ0) * (ê - e) / (ê * e) := by
    field_simp [hê_ne, he_ne]
    ring
  rw [hid]
  calc
    |((μ1h - μ1) - (μ0h - μ0)) / ê -
        (μ1 - μ0) * (ê - e) / (ê * e)|
        ≤ |((μ1h - μ1) - (μ0h - μ0)) / ê| +
            |(μ1 - μ0) * (ê - e) / (ê * e)| := abs_sub _ _
    _ = |(μ1h - μ1) - (μ0h - μ0)| / ê +
          |μ1 - μ0| * |ê - e| / (ê * e) := by
          rw [abs_div, abs_of_pos hê_pos, abs_div, abs_mul, abs_of_pos hprod_pos]
    _ ≤ (|μ1h - μ1| + |μ0h - μ0|) / ε +
          |μ1 - μ0| * |ê - e| / ε ^ 2 := by
          have hnum : |(μ1h - μ1) - (μ0h - μ0)| ≤
              |μ1h - μ1| + |μ0h - μ0| := abs_sub _ _
          have hterm1 :
              |(μ1h - μ1) - (μ0h - μ0)| / ê ≤
                (|μ1h - μ1| + |μ0h - μ0|) / ε := by
            rw [div_eq_mul_inv, div_eq_mul_inv]
            exact (mul_le_mul hnum ((inv_le_inv₀ hê_pos hε).2 hê)
              (inv_nonneg.mpr hê_pos.le) (by positivity))
          have hterm2 :
              |μ1 - μ0| * |ê - e| / (ê * e) ≤
                |μ1 - μ0| * |ê - e| / ε ^ 2 := by
            rw [div_eq_mul_inv, div_eq_mul_inv]
            exact mul_le_mul_of_nonneg_left ((inv_le_inv₀ hprod_pos hεsq_pos).2 hmul)
              (mul_nonneg (abs_nonneg _) (abs_nonneg _))
          exact add_le_add hterm1 hterm2

/-- The stage-one weighted residual contrast is Lipschitz in the stage-one regression error and both propensity errors under overlap. -/
lemma seqDR_stage1_ratio_bound
    {ε e0 ê0 e1 ê1 y μ1 μ1h : ℝ}
    (hε : 0 < ε) (he0 : ε ≤ e0) (hê0 : ε ≤ ê0)
    (he1 : ε ≤ e1) (hê1 : ε ≤ ê1) :
    |(y - μ1h) / (ê0 * ê1) - (y - μ1) / (e0 * e1)| ≤
      |μ1h - μ1| / ε ^ 2 +
        |y - μ1| * |ê0 - e0| / ε ^ 3 +
          |y - μ1| * |ê1 - e1| / ε ^ 3 := by
  have he0_pos : 0 < e0 := lt_of_lt_of_le hε he0
  have hê0_pos : 0 < ê0 := lt_of_lt_of_le hε hê0
  have he1_pos : 0 < e1 := lt_of_lt_of_le hε he1
  have hê1_pos : 0 < ê1 := lt_of_lt_of_le hε hê1
  have hprod_hat_pos : 0 < ê0 * ê1 := mul_pos hê0_pos hê1_pos
  have hprod_true_pos : 0 < e0 * e1 := mul_pos he0_pos he1_pos
  have hden0_pos : 0 < ê0 * e0 * ê1 := mul_pos (mul_pos hê0_pos he0_pos) hê1_pos
  have hden1_pos : 0 < e0 * ê1 * e1 := mul_pos (mul_pos he0_pos hê1_pos) he1_pos
  have hprod_hat_ne : ê0 * ê1 ≠ 0 := hprod_hat_pos.ne'
  have hprod_true_ne : e0 * e1 ≠ 0 := hprod_true_pos.ne'
  have hεsq_pos : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hεcub_pos : 0 < ε ^ 3 := pow_pos hε 3
  have hprod_hat_ge : ε ^ 2 ≤ ê0 * ê1 := by
    nlinarith [mul_le_mul hê0 hê1 hε.le hê0_pos.le]
  have hden0_ge : ε ^ 3 ≤ ê0 * e0 * ê1 := by
    nlinarith [mul_le_mul (mul_le_mul hê0 he0 hε.le hê0_pos.le) hê1 hε.le
      (mul_pos hê0_pos he0_pos).le]
  have hden1_ge : ε ^ 3 ≤ e0 * ê1 * e1 := by
    nlinarith [mul_le_mul (mul_le_mul he0 hê1 hε.le he0_pos.le) he1 hε.le
      (mul_pos he0_pos hê1_pos).le]
  have hid :
      (y - μ1h) / (ê0 * ê1) - (y - μ1) / (e0 * e1) =
        - (μ1h - μ1) / (ê0 * ê1)
          - (y - μ1) * (ê0 - e0) / (ê0 * e0 * ê1)
          - (y - μ1) * (ê1 - e1) / (e0 * ê1 * e1) := by
    field_simp [hprod_hat_ne, hprod_true_ne, hê0_pos.ne', he0_pos.ne',
      hê1_pos.ne', he1_pos.ne']
    ring
  rw [hid]
  calc
    |- (μ1h - μ1) / (ê0 * ê1)
        - (y - μ1) * (ê0 - e0) / (ê0 * e0 * ê1)
        - (y - μ1) * (ê1 - e1) / (e0 * ê1 * e1)|
        ≤ |-(μ1h - μ1) / (ê0 * ê1)
            - (y - μ1) * (ê0 - e0) / (ê0 * e0 * ê1)| +
          |(y - μ1) * (ê1 - e1) / (e0 * ê1 * e1)| := abs_sub _ _
    _ ≤ |-(μ1h - μ1) / (ê0 * ê1)| +
          |(y - μ1) * (ê0 - e0) / (ê0 * e0 * ê1)| +
            |(y - μ1) * (ê1 - e1) / (e0 * ê1 * e1)| := by
          nlinarith [abs_sub (-(μ1h - μ1) / (ê0 * ê1))
            ((y - μ1) * (ê0 - e0) / (ê0 * e0 * ê1))]
    _ = |μ1h - μ1| / (ê0 * ê1) +
          |y - μ1| * |ê0 - e0| / (ê0 * e0 * ê1) +
            |y - μ1| * |ê1 - e1| / (e0 * ê1 * e1) := by
          rw [abs_div, abs_neg, abs_of_pos hprod_hat_pos]
          rw [abs_div, abs_mul, abs_of_pos hden0_pos]
          rw [abs_div, abs_mul, abs_of_pos hden1_pos]
    _ ≤ |μ1h - μ1| / ε ^ 2 +
          |y - μ1| * |ê0 - e0| / ε ^ 3 +
            |y - μ1| * |ê1 - e1| / ε ^ 3 := by
          have h1 : |μ1h - μ1| / (ê0 * ê1) ≤ |μ1h - μ1| / ε ^ 2 := by
            rw [div_eq_mul_inv, div_eq_mul_inv]
            exact mul_le_mul_of_nonneg_left
              ((inv_le_inv₀ hprod_hat_pos hεsq_pos).2 hprod_hat_ge) (abs_nonneg _)
          have h2 : |y - μ1| * |ê0 - e0| / (ê0 * e0 * ê1) ≤
              |y - μ1| * |ê0 - e0| / ε ^ 3 := by
            rw [div_eq_mul_inv, div_eq_mul_inv]
            exact mul_le_mul_of_nonneg_left
              ((inv_le_inv₀ hden0_pos hεcub_pos).2 hden0_ge)
              (mul_nonneg (abs_nonneg _) (abs_nonneg _))
          have h3 : |y - μ1| * |ê1 - e1| / (e0 * ê1 * e1) ≤
              |y - μ1| * |ê1 - e1| / ε ^ 3 := by
            rw [div_eq_mul_inv, div_eq_mul_inv]
            exact mul_le_mul_of_nonneg_left
              ((inv_le_inv₀ hden1_pos hεcub_pos).2 hden1_ge)
              (mul_nonneg (abs_nonneg _) (abs_nonneg _))
          nlinarith

set_option maxHeartbeats 800000 in
-- The expanded sequential score has three weighted pieces; `ring`/`nlinarith`
-- need a larger budget to normalize the real-valued denominator algebra.
/-- The full two-stage sequential doubly robust score is pointwise Lipschitz in all nuisance components under overlap. -/
lemma seqDR_real_bound
    {ε e0 ê0 e1 ê1 μ0 μ0h μ1 μ1h y θ I0 I1 : ℝ}
    (hε : 0 < ε) (he0 : ε ≤ e0) (hê0 : ε ≤ ê0)
    (he1 : ε ≤ e1) (hê1 : ε ≤ ê1)
    (hI0 : |I0| ≤ 1) (hI1 : |I1| ≤ 1) :
    |(μ0h + (I0 / ê0) * (μ1h - μ0h)
        + (I0 * I1 / (ê0 * ê1)) * (y - μ1h) - θ)
      - (μ0 + (I0 / e0) * (μ1 - μ0)
        + (I0 * I1 / (e0 * e1)) * (y - μ1) - θ)|
      ≤ K_seqDR ε *
          (|μ0h - μ0| + |μ1h - μ1|
            + (|μ1 - μ0| + |y - μ1|) * |ê0 - e0|
            + |y - μ1| * |ê1 - e1|) := by
  have hK1 : 1 ≤ K_seqDR ε := K_seqDR_one_le hε
  have hKμ0 : 1 + 1 / ε ≤ K_seqDR ε := K_seqDR_mu0_le hε
  have hKμ1 : 1 / ε + 1 / ε ^ 2 ≤ K_seqDR ε := K_seqDR_mu1_le hε
  have hK2 : 1 / ε ^ 2 ≤ K_seqDR ε := K_seqDR_inv_sq_le hε
  have hK3 : 1 / ε ^ 3 ≤ K_seqDR ε := K_seqDR_inv_cubed_le hε
  have hKnonneg : 0 ≤ K_seqDR ε := le_trans zero_le_one hK1
  set d0 : ℝ := |μ0h - μ0|
  set d1 : ℝ := |μ1h - μ1|
  set r0 : ℝ := |μ1 - μ0|
  set r1 : ℝ := |y - μ1|
  set de0 : ℝ := |ê0 - e0|
  set de1 : ℝ := |ê1 - e1|
  have hd0 : 0 ≤ d0 := by simp [d0]
  have hd1 : 0 ≤ d1 := by simp [d1]
  have hr0 : 0 ≤ r0 := by simp [r0]
  have hr1 : 0 ≤ r1 := by simp [r1]
  have hde0 : 0 ≤ de0 := by simp [de0]
  have hde1 : 0 ≤ de1 := by simp [de1]
  have hstage0 :
      |I0 * ((μ1h - μ0h) / ê0 - (μ1 - μ0) / e0)| ≤
        (d1 + d0) / ε + r0 * de0 / ε ^ 2 := by
    rw [abs_mul]
    have hb := seqDR_stage0_ratio_bound (ε := ε) (e := e0) (ê := ê0)
      (μ0 := μ0) (μ0h := μ0h) (μ1 := μ1) (μ1h := μ1h) hε he0 hê0
    have hnonneg : 0 ≤ (d1 + d0) / ε + r0 * de0 / ε ^ 2 := by positivity
    calc
      |I0| * |(μ1h - μ0h) / ê0 - (μ1 - μ0) / e0|
          ≤ 1 * |(μ1h - μ0h) / ê0 - (μ1 - μ0) / e0| :=
            mul_le_mul_of_nonneg_right hI0 (abs_nonneg _)
      _ ≤ 1 * ((d1 + d0) / ε + r0 * de0 / ε ^ 2) := by
            simpa [d0, d1, r0, de0, add_comm] using hb
      _ = (d1 + d0) / ε + r0 * de0 / ε ^ 2 := one_mul _
  have hstage1 :
      |I0 * I1 * ((y - μ1h) / (ê0 * ê1) - (y - μ1) / (e0 * e1))| ≤
        d1 / ε ^ 2 + r1 * de0 / ε ^ 3 + r1 * de1 / ε ^ 3 := by
    rw [abs_mul, abs_mul]
    have hI01 : |I0| * |I1| ≤ 1 := by
      have hI1nonneg : 0 ≤ |I1| := abs_nonneg _
      calc
        |I0| * |I1| ≤ 1 * |I1| := mul_le_mul_of_nonneg_right hI0 hI1nonneg
        _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hI1 zero_le_one
        _ = 1 := by ring
    have hb := seqDR_stage1_ratio_bound (ε := ε) (e0 := e0) (ê0 := ê0)
      (e1 := e1) (ê1 := ê1) (y := y) (μ1 := μ1) (μ1h := μ1h)
      hε he0 hê0 he1 hê1
    calc
      |I0| * |I1| * |(y - μ1h) / (ê0 * ê1) - (y - μ1) / (e0 * e1)|
          ≤ 1 * |(y - μ1h) / (ê0 * ê1) - (y - μ1) / (e0 * e1)| :=
            mul_le_mul_of_nonneg_right hI01 (abs_nonneg _)
      _ ≤ 1 * (d1 / ε ^ 2 + r1 * de0 / ε ^ 3 + r1 * de1 / ε ^ 3) := by
            simpa [d1, r1, de0, de1] using hb
      _ = d1 / ε ^ 2 + r1 * de0 / ε ^ 3 + r1 * de1 / ε ^ 3 := one_mul _
  have hsplit :
      ((μ0h + (I0 / ê0) * (μ1h - μ0h)
          + (I0 * I1 / (ê0 * ê1)) * (y - μ1h) - θ)
        - (μ0 + (I0 / e0) * (μ1 - μ0)
          + (I0 * I1 / (e0 * e1)) * (y - μ1) - θ)) =
        (μ0h - μ0)
          + I0 * ((μ1h - μ0h) / ê0 - (μ1 - μ0) / e0)
          + I0 * I1 * ((y - μ1h) / (ê0 * ê1) - (y - μ1) / (e0 * e1)) := by
    ring
  rw [hsplit]
  have hpre :
      |(μ0h - μ0)
          + I0 * ((μ1h - μ0h) / ê0 - (μ1 - μ0) / e0)
          + I0 * I1 * ((y - μ1h) / (ê0 * ê1) - (y - μ1) / (e0 * e1))|
        ≤ d0 + ((d1 + d0) / ε + r0 * de0 / ε ^ 2) +
            (d1 / ε ^ 2 + r1 * de0 / ε ^ 3 + r1 * de1 / ε ^ 3) := by
    calc
      |(μ0h - μ0)
          + I0 * ((μ1h - μ0h) / ê0 - (μ1 - μ0) / e0)
          + I0 * I1 * ((y - μ1h) / (ê0 * ê1) - (y - μ1) / (e0 * e1))|
          ≤ |μ0h - μ0|
            + |I0 * ((μ1h - μ0h) / ê0 - (μ1 - μ0) / e0)|
            + |I0 * I1 * ((y - μ1h) / (ê0 * ê1) - (y - μ1) / (e0 * e1))| := by
            nlinarith [abs_add_le (μ0h - μ0)
              (I0 * ((μ1h - μ0h) / ê0 - (μ1 - μ0) / e0)),
              abs_add_le ((μ0h - μ0)
                + I0 * ((μ1h - μ0h) / ê0 - (μ1 - μ0) / e0))
                (I0 * I1 * ((y - μ1h) / (ê0 * ê1) - (y - μ1) / (e0 * e1)))]
      _ ≤ d0 + ((d1 + d0) / ε + r0 * de0 / ε ^ 2) +
            (d1 / ε ^ 2 + r1 * de0 / ε ^ 3 + r1 * de1 / ε ^ 3) := by
            simpa [d0] using add_le_add (add_le_add le_rfl hstage0) hstage1
  have htarget :
      d0 + ((d1 + d0) / ε + r0 * de0 / ε ^ 2) +
          (d1 / ε ^ 2 + r1 * de0 / ε ^ 3 + r1 * de1 / ε ^ 3)
        ≤ K_seqDR ε * (d0 + d1 + (r0 + r1) * de0 + r1 * de1) := by
    have hcoef0 : (1 + 1 / ε) * d0 ≤ K_seqDR ε * d0 :=
      mul_le_mul_of_nonneg_right hKμ0 hd0
    have hcoef1 : (1 / ε + 1 / ε ^ 2) * d1 ≤ K_seqDR ε * d1 :=
      mul_le_mul_of_nonneg_right hKμ1 hd1
    have hcross0 : r0 * de0 / ε ^ 2 ≤ K_seqDR ε * (r0 * de0) := by
      calc
        r0 * de0 / ε ^ 2 = (1 / ε ^ 2) * (r0 * de0) := by ring
        _ ≤ K_seqDR ε * (r0 * de0) :=
          mul_le_mul_of_nonneg_right hK2 (mul_nonneg hr0 hde0)
    have hcross1 : r1 * de0 / ε ^ 3 ≤ K_seqDR ε * (r1 * de0) := by
      calc
        r1 * de0 / ε ^ 3 = (1 / ε ^ 3) * (r1 * de0) := by ring
        _ ≤ K_seqDR ε * (r1 * de0) :=
          mul_le_mul_of_nonneg_right hK3 (mul_nonneg hr1 hde0)
    have hcross2 : r1 * de1 / ε ^ 3 ≤ K_seqDR ε * (r1 * de1) := by
      calc
        r1 * de1 / ε ^ 3 = (1 / ε ^ 3) * (r1 * de1) := by ring
        _ ≤ K_seqDR ε * (r1 * de1) :=
          mul_le_mul_of_nonneg_right hK3 (mul_nonneg hr1 hde1)
    calc
      d0 + ((d1 + d0) / ε + r0 * de0 / ε ^ 2) +
          (d1 / ε ^ 2 + r1 * de0 / ε ^ 3 + r1 * de1 / ε ^ 3)
          = (1 + 1 / ε) * d0 + (1 / ε + 1 / ε ^ 2) * d1
              + r0 * de0 / ε ^ 2 + r1 * de0 / ε ^ 3 + r1 * de1 / ε ^ 3 := by
            ring
      _ ≤ K_seqDR ε * d0 + K_seqDR ε * d1
            + K_seqDR ε * (r0 * de0) + K_seqDR ε * (r1 * de0)
            + K_seqDR ε * (r1 * de1) := by
            nlinarith
      _ = K_seqDR ε * (d0 + d1 + (r0 + r1) * de0 + r1 * de1) := by
            ring
  exact hpre.trans htarget

/-- The true stage-zero regression representative is square-integrable under the stage-zero history marginal. -/
lemma μ₀_val_memLp
    (S : DTREstimationSystem P δ γ)
    (hA : S.toPODTRSystem.Assumptions)
    (h_yd2 : ∀ dbar : Fin 2 → δ,
      Integrable (fun ω => (S.toPODTRSystem.Y_of dbar ω) ^ 2) P.μ) :
    MemLp S.μ₀_val 2 S.P_H₀ := by
  have hYd_L2 : MemLp (S.toPODTRSystem.Y_of S.dbar) 2 P.μ :=
    (memLp_two_iff_integrable_sq
      (S.toPODTRSystem.measurable_Y_of S.dbar).aestronglyMeasurable).2
        (h_yd2 S.dbar)
  have hcond_L2 :
      MemLp ((S.toPODTRSystem.historyBundle 0 (by decide)).condExpGiven
        (S.toPODTRSystem.Y_of S.dbar) P.μ) 2 P.μ := by
    simpa [POCFBundle.condExpGiven] using hYd_L2.condExp
  have hcomp_L2 :
      MemLp (fun ω => S.μ₀_val
        (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω)) 2 P.μ :=
    hcond_L2.ae_eq (S.μ₀_compat hA)
  rw [DTREstimationSystem.P_H₀]
  exact (memLp_map_measure_iff S.μ₀_meas.aestronglyMeasurable
    (S.toPODTRSystem.measurable_factualS ⟨0, by decide⟩).aemeasurable).2 hcomp_L2

/-- The true stage-one regression representative is square-integrable under the stage-one history marginal. -/
lemma μ₁_val_memLp
    (S : DTREstimationSystem P δ γ)
    {ε : ℝ}
    (h_overlap : S.StrictOverlap ε)
    (h_y2 : Integrable (fun ω => (S.toPODTRSystem.factualY ω) ^ 2) P.μ) :
    MemLp S.μ₁_val 2 S.P_H₁ := by
  let H1 : P.Ω → γ 1 × δ × γ 0 := fun ω =>
    (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
     S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
     S.toPODTRSystem.factualS ⟨0, by decide⟩ ω)
  have hH1_meas : Measurable H1 := by
    dsimp [H1]
    exact (S.toPODTRSystem.measurable_factualS ⟨1, by decide⟩).prod
      ((S.toPODTRSystem.measurable_factualD ⟨0, by decide⟩).prod
        (S.toPODTRSystem.measurable_factualS ⟨0, by decide⟩))
  have hcomp_L2 :
      MemLp (fun ω => S.μ₁_val (H1 ω)) 2 P.μ := by
    simpa [H1] using (S.stageOneReg_memLp h_overlap h_y2).ae_eq
      (S.μ₁_val_comp_eq_stageOneReg).symm
  rw [DTREstimationSystem.P_H₁]
  exact (memLp_map_measure_iff S.μ₁_meas.aestronglyMeasurable
    hH1_meas.aemeasurable).2 hcomp_L2

/-- The sequential doubly robust score difference is almost surely bounded by the Lipschitz constant times the stagewise nuisance errors.

The bound transfers strict overlap from the structural law to the full observed data law before applying the pointwise algebraic estimate. -/
theorem seqDR_score_diff_pointwise_bound
    (S : DTREstimationSystem P δ γ) {ε : ℝ}
    (h_overlap : S.StrictOverlap ε)
    (η : DTRNuisanceVec₂ δ γ) (hη : η ∈ DTREstimationSystem.H_ε ε) :
    ∀ᵐ z ∂S.P_Z,
      |S.seqDRMomentFunctional η z S.θ₀ - S.seqDRMomentFunctional S.η₀ z S.θ₀|
        ≤ K_seqDR ε *
            (|η.μ₀_fn (projS₀ z) - S.μ₀_val (projS₀ z)|
              + |η.μ₁_fn (histH₁ z) - S.μ₁_val (histH₁ z)|
              + (|S.μ₁_val (histH₁ z) - S.μ₀_val (projS₀ z)|
                  + |projY z - S.μ₁_val (histH₁ z)|)
                * |η.e₀_fn (projS₀ z) - S.e₀_val (projS₀ z)|
              + |projY z - S.μ₁_val (histH₁ z)|
                * |η.e₁_fn (histH₁ z) - S.e₁_val (histH₁ z)|) := by
  rcases h_overlap with ⟨hε_pos, _hε_half, hprop⟩
  have h_e_ω : ∀ᵐ ω ∂P.μ,
      (ε ≤ S.e₀_val (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) ∧
        S.e₀_val (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) ≤ 1 - ε)
      ∧ (ε ≤ S.e₁_val
          (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
           S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
           S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) ∧
        S.e₁_val
          (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
           S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
           S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) ≤ 1 - ε) := by
    filter_upwards [hprop, S.e₀_compat, S.e₁_compat] with ω hω hcomp0 hcomp1
    rw [hcomp0] at hω
    rw [hcomp1] at hω
    exact hω
  have h_e_z : ∀ᵐ z ∂S.P_Z,
      (ε ≤ S.e₀_val (projS₀ z) ∧ S.e₀_val (projS₀ z) ≤ 1 - ε)
      ∧ (ε ≤ S.e₁_val (histH₁ z) ∧ S.e₁_val (histH₁ z) ≤ 1 - ε) := by
    have hset : MeasurableSet
        {z : γ 0 × δ × γ 1 × δ × ℝ |
          (ε ≤ S.e₀_val (projS₀ z) ∧ S.e₀_val (projS₀ z) ≤ 1 - ε)
          ∧ (ε ≤ S.e₁_val (histH₁ z) ∧ S.e₁_val (histH₁ z) ≤ 1 - ε)} := by
      exact (measurableSet_Icc.preimage (S.e₀_meas.comp measurable_projS₀)).inter
        (measurableSet_Icc.preimage (S.e₁_meas.comp measurable_histH₁))
    unfold DTREstimationSystem.P_Z
    rw [MeasureTheory.ae_map_iff S.measurable_factualZ.aemeasurable hset]
    filter_upwards [h_e_ω] with ω hω
    simpa [DTREstimationSystem.factualZ, projS₀, histH₁, projS₁, projD₀]
      using hω
  filter_upwards [h_e_z] with z hz
  have hη0 : ε ≤ η.e₀_fn (projS₀ z) := (hη.1 (projS₀ z)).1
  have hη1 : ε ≤ η.e₁_fn (histH₁ z) := (hη.2 (histH₁ z)).1
  simpa [DTREstimationSystem.seqDRMomentFunctional, Causalean.Estimation.DTR.seqDRMoment,
    DTREstimationSystem.η₀, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    (seqDR_real_bound (ε := ε)
      (e0 := S.e₀_val (projS₀ z)) (ê0 := η.e₀_fn (projS₀ z))
      (e1 := S.e₁_val (histH₁ z)) (ê1 := η.e₁_fn (histH₁ z))
      (μ0 := S.μ₀_val (projS₀ z)) (μ0h := η.μ₀_fn (projS₀ z))
      (μ1 := S.μ₁_val (histH₁ z)) (μ1h := η.μ₁_fn (histH₁ z))
      (y := projY z) (θ := S.θ₀)
      (I0 := indEq (projD₀ z) (S.dbar 0)) (I1 := indEq (projD₁ z) (S.dbar 1))
      hε_pos hz.1.1 hη0 hz.2.1 hη1
      (by
        rw [abs_of_nonneg (indEq_nonneg (projD₀ z) (S.dbar 0))]
        exact indEq_le_one (projD₀ z) (S.dbar 0))
      (by
        rw [abs_of_nonneg (indEq_nonneg (projD₁ z) (S.dbar 1))]
        exact indEq_le_one (projD₁ z) (S.dbar 1)))


end DTREstimationSystem

end DTR
end Estimation
end Causalean
