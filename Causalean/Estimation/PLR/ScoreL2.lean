/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Partially linear score L²(P_Z) continuity

Discharges the `o_p(1)` score-difference hypothesis `h_score_diff_rate` that
`Estimation/PLR/DML.lean`'s `plr_dml_isAsymLinear` consumes from the abstract
Chernozhukov engine.  Writing `z = (x, d, y)`, `ℓ̂ = (η̂ n ω).lFn`,
`m̂ = (η̂ n ω).mFn`, `ℓ₀ = ℓ_val`, `m₀ = m_val`, `Δℓ = ℓ₀ − ℓ̂`, `Δm = m₀ − m̂`,
`v₀ = d − m₀`, and `A = y − ℓ₀ − θ₀·v₀`, the Robinson partialling-out score
difference factors as

    ψ(η̂, z, θ₀) − ψ(η₀, z, θ₀)
      = A·Δm + Δℓ·v₀ + Δℓ·Δm − θ₀·Δm·v₀ − θ₀·Δm²,

a pure `ring` identity.  Each of the five summands is a product of a uniformly
bounded factor (`A`, `v₀`, or one copy of `Δℓ`/`Δm`) and a single L²-rate factor
(`Δℓ` or `Δm`, functions of the covariate `x`).  Bounding `‖φ·f‖_{L²(P_Z)} ≤
‖φ‖_∞ · ‖f‖_{L²(P_Z)}`, transporting the rate factors to `P_X` through the
projection bridge `eLpNorm_comp_projX`, and assembling with the `IsLittleOp`
sum/scalar combinators yields the headline

    `‖ψ(η̂(n,ω), ·, θ₀) − ψ(η₀, ·, θ₀)‖_{L²(P_Z)} = o_p(1)`,

mirroring `Estimation/ATE/AIPWScoreL2.lean`'s
`aipw_score_diff_isLittleOp_one`.
-/

import Causalean.Estimation.PLR.Setup
import Causalean.Stat.Limit.Convergence
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-! # Partially linear score L²(P_Z) `o_p(1)` continuity

This file provides the standalone lemma `plr_score_diff_isLittleOp_one`, which
discharges the score-difference `o_p(1)` hypothesis of the partially linear DML
asymptotic-linearity theorem from boundedness of the truth residuals, uniform
boundedness of the nuisance errors, and the two individual L²(P_X) nuisance
rates. -/

namespace Causalean
namespace Estimation
namespace PLR

open MeasureTheory ProbabilityTheory Causalean.PO Causalean.Estimation.OrthogonalMoments
open Causalean.Stat

namespace PLRSystem

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ] [IsFiniteMeasure P.μ]

/-! ## Projection bridge `L²(P_Z)` ↔ `L²(P_X)` -/

/-- The L²-seminorm of a covariate function lifted to the observation triple
equals its L²-seminorm on the covariate marginal: for measurable `g : γ → ℝ`,
`‖fun z ↦ g(z.1)‖_{L²(P_Z)} = ‖g‖_{L²(P_X)}`.  Both sides equal the L²-seminorm
of the pullback `g ∘ X` against `μ`, since `(X, D, Y)` has covariate component
`X`. -/
private lemma eLpNorm_comp_projX
    (S : PLRSystem P γ) {g : γ → ℝ} (hg : Measurable g) :
    eLpNorm (fun z : γ × ℝ × ℝ => g z.1) 2 S.P_Z = eLpNorm g 2 S.P_X := by
  have hX_ae : AEMeasurable S.factualX P.μ := S.measurable_factualX.aemeasurable
  have hZ_ae : AEMeasurable S.factualZ P.μ := S.measurable_factualZ.aemeasurable
  -- RHS: pull `g` along `X`.
  rw [P_X, eLpNorm_map_measure hg.aestronglyMeasurable hX_ae]
  -- LHS: pull `(fun z ↦ g z.1)` along `Z`, then collapse `(Z ω).1 = X ω`.
  rw [P_Z, eLpNorm_map_measure (g := fun z : γ × ℝ × ℝ => g z.1)
    ((hg.comp measurable_fst).aestronglyMeasurable) hZ_ae]
  have hcomp : ((fun z : γ × ℝ × ℝ => g z.1) ∘ S.factualZ) = g ∘ S.factualX := by
    funext ω; rfl
  rw [hcomp]

/-! ## Bounded-times-L² product bound -/

/-- If `|φ| ≤ C` `P_Z`-a.e. with `C ≥ 0` and `f ∈ L²(P_Z)`, then
`‖φ·f‖_{L²(P_Z)} ≤ C·‖f‖_{L²(P_Z)}`.  The L∞·L² Hölder step specialised to a
uniformly bounded multiplier, proved by the a.e. monotonicity of the
L²-seminorm against `C·|f|` and the scalar pull-out. -/
private lemma lpNorm_bdd_mul_le
    {μ : Measure (γ × ℝ × ℝ)} {φ f : (γ × ℝ × ℝ) → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hφ_meas : AEStronglyMeasurable φ μ) (hf : MemLp f 2 μ)
    (hφ : ∀ᵐ z ∂μ, |φ z| ≤ C) :
    lpNorm (fun z => φ z * f z) 2 μ ≤ C * lpNorm f 2 μ := by
  have hprod_meas : AEStronglyMeasurable (fun z => φ z * f z) μ :=
    hφ_meas.mul hf.aestronglyMeasurable
  have hCabs_memLp : MemLp (fun z => C * |f z|) 2 μ := by
    have hg : MemLp (fun z => |f z|) 2 μ := by
      simpa [Real.norm_eq_abs] using hf.norm
    simpa [Pi.smul_apply, smul_eq_mul] using hg.const_smul C
  have hmono :
      eLpNorm (fun z => φ z * f z) 2 μ ≤ eLpNorm (fun z => C * |f z|) 2 μ := by
    refine eLpNorm_mono_ae_real ?_
    filter_upwards [hφ] with z hz
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right hz (abs_nonneg _)
  have hCabs_norm :
      lpNorm (fun z => C * |f z|) 2 μ = C * lpNorm f 2 μ := by
    have heq : (fun z => C * |f z|) = C • (fun z => |f z|) := by
      funext z; simp [smul_eq_mul]
    rw [heq, lpNorm_const_smul, lpNorm_fun_abs hf.aestronglyMeasurable]
    have hcoef : (↑‖C‖₊ : ℝ) = C := by
      simp [Real.norm_eq_abs, abs_of_nonneg hC]
    rw [hcoef]
  calc
    lpNorm (fun z => φ z * f z) 2 μ
        = (eLpNorm (fun z => φ z * f z) 2 μ).toReal := by
          rw [toReal_eLpNorm hprod_meas]
    _ ≤ (eLpNorm (fun z => C * |f z|) 2 μ).toReal :=
          ENNReal.toReal_mono hCabs_memLp.eLpNorm_ne_top hmono
    _ = lpNorm (fun z => C * |f z|) 2 μ := by
          rw [toReal_eLpNorm hCabs_memLp.aestronglyMeasurable]
    _ = C * lpNorm f 2 μ := hCabs_norm

/-- The Robinson partialling-out score difference expands into the five-term
doubly-robust form `A·Δm + Δℓ·v₀ + Δℓ·Δm − θ₀·Δm·v₀ − θ₀·Δm²`, a pure
algebraic identity in the observation coordinates. -/
private lemma score_diff_expand
    (S : PLRSystem P γ) (η : PLRNuisance γ) (z : γ × ℝ × ℝ) :
    plrMomentFunctional η z S.θ₀ - plrMomentFunctional S.η₀ z S.θ₀
      = (z.2.2 - S.lVal z.1 - S.θ₀ * (z.2.1 - S.mVal z.1)) *
          (S.mVal z.1 - η.mFn z.1)
        + (S.lVal z.1 - η.lFn z.1) * (z.2.1 - S.mVal z.1)
        + (S.lVal z.1 - η.lFn z.1) * (S.mVal z.1 - η.mFn z.1)
        - S.θ₀ * (S.mVal z.1 - η.mFn z.1) * (z.2.1 - S.mVal z.1)
        - S.θ₀ * (S.mVal z.1 - η.mFn z.1) ^ 2 := by
  simp only [plrMomentFunctional, plrResidual, η₀]
  ring

set_option maxHeartbeats 400000 in
-- The per-`(n, ω)` envelope assembly (five `MemLp`/`lpNorm` coercion steps plus
-- the projection-bridge rewrites) exceeds the default heartbeat budget.
open Filter in
/-- Per-`(n, ω)` quantitative bound feeding `plr_score_diff_isLittleOp_one`: the
real L²(P_Z)-seminorm of the partially linear score difference is dominated by a
constant multiple of the sum of the two regression-error L²(P_X) magnitudes,
via the five-term doubly-robust expansion and the bounded-times-L² product
estimate. -/
private theorem plr_score_diff_abs_le
    (S : PLRSystem P γ)
    (η_hat : ℕ → P.Ω → PLRNuisance γ) (n : ℕ) (ω : P.Ω)
    {Ca Cv Cm : ℝ} (hCa : 0 ≤ Ca) (hCv : 0 ≤ Cv) (hCm : 0 ≤ Cm)
    (Cconst : ℝ)
    (rateL rateM : ℕ → P.Ω → ℝ)
    (hrateL : rateL = fun n ω =>
      (eLpNorm (fun x => (η_hat n ω).lFn x - S.lVal x) 2 S.P_X).toReal)
    (hrateM : rateM = fun n ω =>
      (eLpNorm (fun x => (η_hat n ω).mFn x - S.mVal x) 2 S.P_X).toReal)
    (hrateL_nonneg : ∀ n ω, 0 ≤ rateL n ω)
    (hrateM_nonneg : ∀ n ω, 0 ≤ rateM n ω)
    (hCconst : Cconst = Ca + Cv + Cm + |S.θ₀| * Cv + |S.θ₀| * Cm)
    (hA_bdd : ∀ᵐ z ∂S.P_Z,
      |z.2.2 - S.lVal z.1 - S.θ₀ * (z.2.1 - S.mVal z.1)| ≤ Ca)
    (hv_bdd : ∀ᵐ z ∂S.P_Z, |z.2.1 - S.mVal z.1| ≤ Cv)
    (hΔm_bdd : ∀ n ω x, |S.mVal x - (η_hat n ω).mFn x| ≤ Cm)
    (hΔl_memLp : ∀ n ω, MemLp (fun x => (η_hat n ω).lFn x - S.lVal x) 2 S.P_X)
    (hΔm_memLp : ∀ n ω, MemLp (fun x => (η_hat n ω).mFn x - S.mVal x) 2 S.P_X) :
    |(eLpNorm (fun z => plrMomentFunctional (η_hat n ω) z S.θ₀
                      - plrMomentFunctional S.η₀ z S.θ₀) 2 S.P_Z).toReal|
      ≤ (Cconst + 1) * |rateL n ω + rateM n ω| := by
  -- Abbreviations: the score difference and the two regression errors lifted to
  -- the observation triple.
  set sc : (γ × ℝ × ℝ) → ℝ := fun z =>
    plrMomentFunctional (η_hat n ω) z S.θ₀ - plrMomentFunctional S.η₀ z S.θ₀ with hsc
  set dL : (γ × ℝ × ℝ) → ℝ := fun z => S.lVal z.1 - (η_hat n ω).lFn z.1 with hdL
  set dM : (γ × ℝ × ℝ) → ℝ := fun z => S.mVal z.1 - (η_hat n ω).mFn z.1 with hdM
  -- The two collecting coefficients.
  set cL : ℝ := Cv + Cm with hcL
  set cM : ℝ := Ca + |S.θ₀| * Cv + |S.θ₀| * Cm with hcM
  have hcL_nonneg : 0 ≤ cL := by rw [hcL]; linarith
  have hcM_nonneg : 0 ≤ cM := by
    rw [hcM]; positivity
  -- Measurability of the lifted errors.
  have hdL_meas : Measurable dL :=
    (S.lVal_meas.comp measurable_fst).sub
      ((η_hat n ω).lMeas.comp measurable_fst)
  have hdM_meas : Measurable dM :=
    (S.mVal_meas.comp measurable_fst).sub
      ((η_hat n ω).mMeas.comp measurable_fst)
  -- The lifted errors are in `L²(P_Z)` (pull back the `P_X` membership).
  -- One bridge each: `‖dL‖_{L²(P_Z)} = ‖Δℓ‖_{L²(P_X)}`, `‖dM‖_{L²(P_Z)} = ‖Δm‖_{L²(P_X)}`.
  have hdL_eLp : eLpNorm dL 2 S.P_Z
      = eLpNorm (fun x => (η_hat n ω).lFn x - S.lVal x) 2 S.P_X := by
    have h := eLpNorm_comp_projX S (g := fun x => S.lVal x - (η_hat n ω).lFn x)
      (S.lVal_meas.sub (η_hat n ω).lMeas)
    rw [show dL = (fun z : γ × ℝ × ℝ => (fun x => S.lVal x - (η_hat n ω).lFn x) z.1)
        from rfl, h, ← eLpNorm_neg (fun x => (η_hat n ω).lFn x - S.lVal x)]
    congr 1; funext x; simp only [Pi.neg_apply, neg_sub]
  have hdM_eLp : eLpNorm dM 2 S.P_Z
      = eLpNorm (fun x => (η_hat n ω).mFn x - S.mVal x) 2 S.P_X := by
    have h := eLpNorm_comp_projX S (g := fun x => S.mVal x - (η_hat n ω).mFn x)
      (S.mVal_meas.sub (η_hat n ω).mMeas)
    rw [show dM = (fun z : γ × ℝ × ℝ => (fun x => S.mVal x - (η_hat n ω).mFn x) z.1)
        from rfl, h, ← eLpNorm_neg (fun x => (η_hat n ω).mFn x - S.mVal x)]
    congr 1; funext x; simp only [Pi.neg_apply, neg_sub]
  have hdL_memLp : MemLp dL 2 S.P_Z :=
    ⟨hdL_meas.aestronglyMeasurable, by rw [hdL_eLp]; exact (hΔl_memLp n ω).2⟩
  have hdM_memLp : MemLp dM 2 S.P_Z :=
    ⟨hdM_meas.aestronglyMeasurable, by rw [hdM_eLp]; exact (hΔm_memLp n ω).2⟩
  -- The two rate identities: `‖dL‖_{L²(P_Z)} = rateL`, `‖dM‖_{L²(P_Z)} = rateM`.
  have hdL_rate : lpNorm dL 2 S.P_Z = rateL n ω := by
    rw [← toReal_eLpNorm hdL_meas.aestronglyMeasurable, hdL_eLp, hrateL]
  have hdM_rate : lpNorm dM 2 S.P_Z = rateM n ω := by
    rw [← toReal_eLpNorm hdM_meas.aestronglyMeasurable, hdM_eLp, hrateM]
  -- The dominating envelope `upper z = cL·|dL z| + cM·|dM z|`.
  set upper : (γ × ℝ × ℝ) → ℝ := fun z => cL * |dL z| + cM * |dM z| with hupper
  have hupper_memLp : MemLp upper 2 S.P_Z := by
    have hL : MemLp (fun z => cL * |dL z|) 2 S.P_Z := by
      have hg : MemLp (fun z => |dL z|) 2 S.P_Z := by
        simpa [Real.norm_eq_abs] using hdL_memLp.norm
      simpa [Pi.smul_apply, smul_eq_mul] using hg.const_smul cL
    have hM : MemLp (fun z => cM * |dM z|) 2 S.P_Z := by
      have hg : MemLp (fun z => |dM z|) 2 S.P_Z := by
        simpa [Real.norm_eq_abs] using hdM_memLp.norm
      simpa [Pi.smul_apply, smul_eq_mul] using hg.const_smul cM
    simpa [upper] using hL.add hM
  -- Pointwise (a.e.) domination of the score by the envelope.
  have hpoint : ∀ᵐ z ∂S.P_Z, ‖sc z‖ ≤ upper z := by
    filter_upwards [hA_bdd, hv_bdd] with z hAz hvz
    have hexp := S.score_diff_expand (η_hat n ω) z
    -- Name the five signed summands.
    set t1 : ℝ := (z.2.2 - S.lVal z.1 - S.θ₀ * (z.2.1 - S.mVal z.1)) * dM z with ht1
    set t2 : ℝ := dL z * (z.2.1 - S.mVal z.1) with ht2
    set t3 : ℝ := dL z * dM z with ht3
    set t4 : ℝ := S.θ₀ * dM z * (z.2.1 - S.mVal z.1) with ht4
    set t5 : ℝ := S.θ₀ * dM z ^ 2 with ht5
    -- Per-term bounds against the rate factors.
    have hb1 : |t1| ≤ Ca * |dM z| := by
      rw [ht1, abs_mul]; exact mul_le_mul_of_nonneg_right hAz (abs_nonneg _)
    have hb2 : |t2| ≤ Cv * |dL z| := by
      rw [ht2, abs_mul, mul_comm]; exact mul_le_mul_of_nonneg_right hvz (abs_nonneg _)
    have hb3 : |t3| ≤ Cm * |dL z| := by
      rw [ht3, abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (by simpa [dM] using hΔm_bdd n ω z.1)
        (abs_nonneg _)
    have hb4 : |t4| ≤ |S.θ₀| * Cv * |dM z| := by
      rw [ht4, abs_mul, abs_mul]
      calc |S.θ₀| * |dM z| * |z.2.1 - S.mVal z.1|
          ≤ |S.θ₀| * |dM z| * Cv := mul_le_mul_of_nonneg_left hvz (by positivity)
        _ = |S.θ₀| * Cv * |dM z| := by ring
    have hb5 : |t5| ≤ |S.θ₀| * Cm * |dM z| := by
      rw [ht5, abs_mul, pow_two, abs_mul]
      calc |S.θ₀| * (|dM z| * |dM z|)
          ≤ |S.θ₀| * (Cm * |dM z|) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right (by simpa [dM] using hΔm_bdd n ω z.1)
                (abs_nonneg _)) (abs_nonneg _)
        _ = |S.θ₀| * Cm * |dM z| := by ring
    -- Triangle inequality on the five-term sum, then collect.
    have htri : |t1 + t2 + t3 - t4 - t5| ≤ |t1| + |t2| + |t3| + |t4| + |t5| := by
      calc |t1 + t2 + t3 - t4 - t5|
          ≤ |t1 + t2 + t3 - t4| + |t5| := by
            simpa [sub_eq_add_neg, abs_neg] using abs_add_le (t1 + t2 + t3 - t4) (-t5)
        _ ≤ (|t1 + t2 + t3| + |t4|) + |t5| := by
            gcongr
            simpa [sub_eq_add_neg, abs_neg] using abs_add_le (t1 + t2 + t3) (-t4)
        _ ≤ ((|t1 + t2| + |t3|) + |t4|) + |t5| := by gcongr; exact abs_add_le _ _
        _ ≤ (((|t1| + |t2|) + |t3|) + |t4|) + |t5| := by gcongr; exact abs_add_le _ _
        _ = |t1| + |t2| + |t3| + |t4| + |t5| := by ring
    rw [Real.norm_eq_abs, show sc z = t1 + t2 + t3 - t4 - t5 from hexp]
    calc |t1 + t2 + t3 - t4 - t5|
        ≤ |t1| + |t2| + |t3| + |t4| + |t5| := htri
      _ ≤ Ca * |dM z| + Cv * |dL z| + Cm * |dL z|
            + |S.θ₀| * Cv * |dM z| + |S.θ₀| * Cm * |dM z| := by
            have := hb1; have := hb2; have := hb3; have := hb4; have := hb5
            gcongr
      _ = upper z := by rw [hupper, hcL, hcM]; ring
  -- Measurability of the score difference.
  have hsc_meas : Measurable sc := by
    rw [hsc]
    exact (measurable_plrMomentFunctional (η_hat n ω) S.θ₀).sub
      (measurable_plrMomentFunctional S.η₀ S.θ₀)
  -- Assemble: `‖sc‖₂ ≤ ‖upper‖₂ ≤ cL·rateL + cM·rateM ≤ (Cconst+1)·(rateL+rateM)`.
  have hsc_le_upper : lpNorm sc 2 S.P_Z ≤ lpNorm upper 2 S.P_Z := by
    rw [← toReal_eLpNorm hsc_meas.aestronglyMeasurable,
      ← toReal_eLpNorm hupper_memLp.aestronglyMeasurable]
    refine ENNReal.toReal_mono hupper_memLp.eLpNorm_ne_top ?_
    exact eLpNorm_mono_ae_real (by filter_upwards [hpoint] with z hz using hz)
  -- Triangle + scalar pull-out on the two-term envelope.
  have hupper_split :
      lpNorm upper 2 S.P_Z ≤ cL * lpNorm dL 2 S.P_Z + cM * lpNorm dM 2 S.P_Z := by
    have hL_memLp : MemLp (fun z => cL * |dL z|) 2 S.P_Z := by
      have hg : MemLp (fun z => |dL z|) 2 S.P_Z := by
        simpa [Real.norm_eq_abs] using hdL_memLp.norm
      simpa [Pi.smul_apply, smul_eq_mul] using hg.const_smul cL
    have htri :
        lpNorm upper 2 S.P_Z ≤
          lpNorm (fun z => cL * |dL z|) 2 S.P_Z +
            lpNorm (fun z => cM * |dM z|) 2 S.P_Z := by
      have hupper_eq :
          upper = (fun z => cL * |dL z|) + (fun z => cM * |dM z|) := by
        funext z; simp [upper, Pi.add_apply]
      rw [hupper_eq]
      exact lpNorm_add_le hL_memLp (by norm_num : (1 : ENNReal) ≤ 2)
    have hnormL :
        lpNorm (fun z => cL * |dL z|) 2 S.P_Z = cL * lpNorm dL 2 S.P_Z := by
      have heq : (fun z => cL * |dL z|) = cL • (fun z => |dL z|) := by
        funext z; simp [smul_eq_mul]
      rw [heq, lpNorm_const_smul, lpNorm_fun_abs hdL_memLp.aestronglyMeasurable]
      have : (↑‖cL‖₊ : ℝ) = cL := by simp [Real.norm_eq_abs, abs_of_nonneg hcL_nonneg]
      rw [this]
    have hnormM :
        lpNorm (fun z => cM * |dM z|) 2 S.P_Z = cM * lpNorm dM 2 S.P_Z := by
      have heq : (fun z => cM * |dM z|) = cM • (fun z => |dM z|) := by
        funext z; simp [smul_eq_mul]
      rw [heq, lpNorm_const_smul, lpNorm_fun_abs hdM_memLp.aestronglyMeasurable]
      have : (↑‖cM‖₊ : ℝ) = cM := by simp [Real.norm_eq_abs, abs_of_nonneg hcM_nonneg]
      rw [this]
    rw [hnormL, hnormM] at htri
    exact htri
  -- Final numeric chain.
  have hfinal :
      (eLpNorm sc 2 S.P_Z).toReal ≤ (Cconst + 1) * (rateL n ω + rateM n ω) := by
    have h1 : (eLpNorm sc 2 S.P_Z).toReal = lpNorm sc 2 S.P_Z :=
      toReal_eLpNorm hsc_meas.aestronglyMeasurable
    rw [h1]
    have hcL_le : cL ≤ Cconst + 1 := by rw [hcL, hCconst]; nlinarith [hcM_nonneg]
    have hcM_le : cM ≤ Cconst + 1 := by rw [hcM, hCconst]; nlinarith [hcL_nonneg, hcL]
    calc
      lpNorm sc 2 S.P_Z ≤ lpNorm upper 2 S.P_Z := hsc_le_upper
      _ ≤ cL * lpNorm dL 2 S.P_Z + cM * lpNorm dM 2 S.P_Z := hupper_split
      _ = cL * rateL n ω + cM * rateM n ω := by rw [hdL_rate, hdM_rate]
      _ ≤ (Cconst + 1) * rateL n ω + (Cconst + 1) * rateM n ω := by
            gcongr <;> [exact hrateL_nonneg n ω; exact hrateM_nonneg n ω]
      _ = (Cconst + 1) * (rateL n ω + rateM n ω) := by ring
  rw [abs_of_nonneg ENNReal.toReal_nonneg,
    abs_of_nonneg (add_nonneg (hrateL_nonneg n ω) (hrateM_nonneg n ω))]
  exact hfinal

open Filter in
/-- **Score-difference L²(P_Z) `o_p(1)` for the partially linear model.**

Under boundedness of the truth residual `A = Y − ℓ_val(X) − θ₀·(D − m_val(X))`
and the treatment residual `v₀ = D − m_val(X)`, a uniform sup-norm bound on the
treatment-regression error `Δm = m_val − m̂`, square-integrability of both
regression errors on the covariate marginal `P_X`, and the two individual
L²(P_X) `o_p(1)` rates for the regression errors, the L²(P_Z)-seminorm of the
Robinson partialling-out score difference between the estimated and the true
nuisance is itself `o_p(1)`.

This is exactly the `h_score_diff_rate` hypothesis consumed by
`plr_dml_isAsymLinear`: the five-term doubly-robust expansion bounds the score
difference pointwise by a constant multiple of the two regression-error
magnitudes, each of which vanishes in probability, so their L² product with the
uniformly bounded residual factors vanishes in probability too. -/
theorem plr_score_diff_isLittleOp_one
    (S : PLRSystem P γ)
    (η_hat : ℕ → P.Ω → PLRNuisance γ)
    {Ca Cv Cm : ℝ} (hCa : 0 ≤ Ca) (hCv : 0 ≤ Cv) (hCm : 0 ≤ Cm)
    (hA_bdd : ∀ᵐ z ∂S.P_Z,
      |z.2.2 - S.lVal z.1 - S.θ₀ * (z.2.1 - S.mVal z.1)| ≤ Ca)
    (hv_bdd : ∀ᵐ z ∂S.P_Z, |z.2.1 - S.mVal z.1| ≤ Cv)
    (hΔm_bdd : ∀ n ω x, |S.mVal x - (η_hat n ω).mFn x| ≤ Cm)
    (hΔl_memLp : ∀ n ω, MemLp (fun x => (η_hat n ω).lFn x - S.lVal x) 2 S.P_X)
    (hΔm_memLp : ∀ n ω, MemLp (fun x => (η_hat n ω).mFn x - S.mVal x) 2 S.P_X)
    (h_l_rate :
      IsLittleOp
        (fun n ω =>
          (eLpNorm (fun x => (η_hat n ω).lFn x - S.lVal x) 2 S.P_X).toReal)
        (fun _ => (1 : ℝ)) P.μ)
    (h_m_rate :
      IsLittleOp
        (fun n ω =>
          (eLpNorm (fun x => (η_hat n ω).mFn x - S.mVal x) 2 S.P_X).toReal)
        (fun _ => (1 : ℝ)) P.μ) :
    IsLittleOp
      (fun n ω => (eLpNorm (fun z => plrMomentFunctional (η_hat n ω) z S.θ₀
                                   - plrMomentFunctional S.η₀ z S.θ₀) 2 S.P_Z).toReal)
      (fun _ => (1 : ℝ)) P.μ := by
  classical
  -- The two L²(P_X) rate functions and their sum.
  set rateL : ℕ → P.Ω → ℝ := fun n ω =>
    (eLpNorm (fun x => (η_hat n ω).lFn x - S.lVal x) 2 S.P_X).toReal with hrateL
  set rateM : ℕ → P.Ω → ℝ := fun n ω =>
    (eLpNorm (fun x => (η_hat n ω).mFn x - S.mVal x) 2 S.P_X).toReal with hrateM
  have hrateL_nonneg : ∀ n ω, 0 ≤ rateL n ω := fun _ _ => ENNReal.toReal_nonneg
  have hrateM_nonneg : ∀ n ω, 0 ≤ rateM n ω := fun _ _ => ENNReal.toReal_nonneg
  -- Sum of the two rates is `o_p(1)`.
  have hsum_rate :
      IsLittleOp (fun n ω => rateL n ω + rateM n ω) (fun _ => (1 : ℝ)) P.μ :=
    IsLittleOp.add_one h_l_rate h_m_rate
  -- The combined constant.
  set Cconst : ℝ := Ca + Cv + Cm + |S.θ₀| * Cv + |S.θ₀| * Cm with hCconst
  have hCconst_pos : 0 < Cconst + 1 := by
    have : 0 ≤ Cconst := by
      have hθ : 0 ≤ |S.θ₀| := abs_nonneg _
      have : 0 ≤ |S.θ₀| * Cv := mul_nonneg hθ hCv
      have : 0 ≤ |S.θ₀| * Cm := mul_nonneg hθ hCm
      positivity
    linarith
  -- Reduce to a constant multiple of the rate sum, then apply the per-`(n, ω)`
  -- quantitative bound.
  refine IsLittleOp.of_abs_le_const_mul_one (C := Cconst + 1) hCconst_pos hsum_rate ?_
  intro n ω
  exact plr_score_diff_abs_le S η_hat n ω hCa hCv hCm Cconst rateL rateM
    hrateL hrateM hrateL_nonneg hrateM_nonneg hCconst
    hA_bdd hv_bdd hΔm_bdd hΔl_memLp hΔm_memLp

end PLRSystem

end PLR
end Estimation
end Causalean
