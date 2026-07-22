/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Score pull-out lemmas for sequential DR (DTR) proofs

Stagewise weighted-residual integral lemmas and indicator-to-propensity-score
integral lemmas, used by `MeanZero.lean` to collapse the IPW correction
terms in `ψ_seqDR`.  Mirrors `Estimation/ATE/ScorePullout.lean`, but
duplicated stage-by-stage (stage 0 and stage 1) since each stage is
conditioned on a different history bundle.

The DTR moment uses `indEq d (dbar k)` instead of the ATE Bool indicator,
so there is no `e_val_label` flip; we only need one regime per stage.

Stage 0 conditions on `historyBundle 0` (singleton `S 0`), stage 1
conditions on `historyBundle 1 = cons S₁ (cons D₀ (cons S₀ nil))` whose
`jointValue` factors through `(factualS 1, factualD 0, factualS 0)`.
-/

import Causalean.Estimation.DTR.MeanZero

/-!
# Score pull-out identities for two-stage DTR scores

This module proves the conditioning identities that collapse the weighted
residual and treatment-indicator terms in the sequential doubly robust DTR
score. The stage-0 results
`DTREstimationSystem.weighted_residual_integral_zero_stage0` and
`DTREstimationSystem.indicator_to_propScore_integral_stage0` condition on the
initial history `S₀`; the stage-1 results
`DTREstimationSystem.weighted_residual_integral_zero_stage1` and
`DTREstimationSystem.indicator_to_propScore_integral_stage1` condition on the
history `(S₁, D₀, S₀)`.

These lemmas move treatment indicators, history sigma-algebras, and regression
residuals into forms suitable for the DTR mean-zero and remainder proofs.
-/

namespace Causalean
namespace Estimation
namespace DTR

open MeasureTheory ProbabilityTheory Filter Topology Causalean.PO

namespace DTREstimationSystem

variable {P : POSystem} {δ : Type} {γ : Fin 2 → Type}
  [MeasurableSpace δ] [MeasurableSingletonClass δ]
  [∀ k, MeasurableSpace (γ k)]
  [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]

/-! ## Stage 0 helpers

Conditioning σ-algebra: `(historyBundle 0).sigma`.
Indicator: `(dVar ⟨0, _⟩).indicator (dbar ⟨0, _⟩)`.
Outcome residual: `μ₁_val(s₁,d₀,s₀) − μ₀_val(s₀)` (the **next-stage**
regression minus the current-stage regression — not `factualY`, which is
the residual at stage 1 only). -/

/-- Stage-0 weighted-residual integral.  Whenever `g : γ 0 → ℝ` is measurable
and the resulting product is integrable, the integral against `μ` of
`g(S₀) · 1{D₀ = dbar 0} · (μ₁_val(S₁,D₀,S₀) − μ₀_val(S₀))` is zero.  By
sequential exchangeability `D₀ ⟂ Y(dbar) | history₀` plus `μ₀_compat`
(applied via the tower σ(historyBundle 0) ⊆ σ(historyBundle 1)),
`μ[indD₀(dbar 0) · μ₁_val(history₁) | σ(historyBundle 0)] =
  e₀_val(S₀) · μ₀_val(S₀) =
  μ[indD₀(dbar 0) · μ₀_val(S₀) | σ(historyBundle 0)]`,
so the integrand has zero σ(historyBundle 0)-conditional mean. -/
theorem weighted_residual_integral_zero_stage0
    (S : DTREstimationSystem P δ γ)
    {ε : ℝ}
    (h_overlap : S.StrictOverlap ε)
    (hA : S.toPODTRSystem.Assumptions)
    (h_y2 : Integrable (fun ω => (S.toPODTRSystem.factualY ω) ^ 2) P.μ)
    (g : γ 0 → ℝ) (hg_meas : Measurable g)
    (h_int : Integrable
      (fun ω => g (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) *
        ((S.toPODTRSystem.dVar ⟨0, by decide⟩).indicator
            (S.dbar ⟨0, by decide⟩) ω *
          (S.μ₁_val
              (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
               S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
               S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) -
            S.μ₀_val (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω)))) P.μ) :
    ∫ ω, g (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) *
        ((S.toPODTRSystem.dVar ⟨0, by decide⟩).indicator
            (S.dbar ⟨0, by decide⟩) ω *
          (S.μ₁_val
              (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
               S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
               S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) -
            S.μ₀_val (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω))) ∂P.μ = 0 := by
  let B0 := S.toPODTRSystem.historyBundle 0 (by decide)
  let I0 : P.Ω → ℝ :=
    (S.toPODTRSystem.dVar ⟨0, by decide⟩).indicator
      (S.dbar ⟨0, by decide⟩)
  let M0 : P.Ω → ℝ :=
    fun ω => S.μ₀_val (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω)
  let M1 : P.Ω → ℝ :=
    fun ω => S.μ₁_val
      (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
       S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
       S.toPODTRSystem.factualS ⟨0, by decide⟩ ω)
  let R : P.Ω → ℝ := fun ω => I0 ω * (M1 ω - M0 ω)
  have hg_sm : StronglyMeasurable[B0.sigma]
      (fun ω => g (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω)) := by
    have hs0 : Measurable[B0.sigma]
        (S.toPODTRSystem.factualS ⟨0, by decide⟩) :=
      S.toPODTRSystem.measurable_factualS_sigma_history 0 (by decide)
        ⟨0, by decide⟩ (by decide)
    exact (hg_meas.comp hs0).stronglyMeasurable
  have hM0_int : Integrable M0 P.μ := by
    exact (B0.integrable_condExpGiven (S.toPODTRSystem.Y_of S.dbar)).congr
      (by simpa [B0, M0] using S.μ₀_compat hA)
  have hM1_int : Integrable M1 P.μ := by
    let B1 := S.toPODTRSystem.historyBundle 1 (by decide)
    have hM1_L2 : MemLp M1 2 P.μ := by
      simpa [M1] using (S.stageOneReg_memLp h_overlap h_y2).ae_eq
        (S.μ₁_val_comp_eq_stageOneReg).symm
    exact hM1_L2.integrable (by norm_num)
  have hM0_meas : Measurable M0 :=
    S.μ₀_meas.comp (S.toPODTRSystem.measurable_factualS ⟨0, by decide⟩)
  have hM1_meas : Measurable M1 := by
    have hs1 := S.toPODTRSystem.measurable_factualS ⟨1, by decide⟩
    have hd0 := S.toPODTRSystem.measurable_factualD ⟨0, by decide⟩
    have hs0 := S.toPODTRSystem.measurable_factualS ⟨0, by decide⟩
    exact S.μ₁_meas.comp (hs1.prod (hd0.prod hs0))
  have hI0M0_int : Integrable (fun ω => I0 ω * M0 ω) P.μ := by
    have h := (S.toPODTRSystem.dVar ⟨0, by decide⟩).integrable_mul_indicator
      (S.dbar ⟨0, by decide⟩) hM0_int hM0_meas
    exact h.congr (Filter.Eventually.of_forall (fun ω => by simp [I0, M0, mul_comm]))
  have hI0M1_int : Integrable (fun ω => I0 ω * M1 ω) P.μ := by
    have h := (S.toPODTRSystem.dVar ⟨0, by decide⟩).integrable_mul_indicator
      (S.dbar ⟨0, by decide⟩) hM1_int hM1_meas
    exact h.congr (Filter.Eventually.of_forall (fun ω => by simp [I0, M1, mul_comm]))
  have hR_int : Integrable R P.μ := by
    have hsub := hI0M1_int.sub hI0M0_int
    refine hsub.congr ?_
    exact Filter.Eventually.of_forall (fun ω => by
      simp [R]
      ring)
  have hcondexp_pull :=
    B0.condExpGiven_mul_of_stronglyMeasurable_left
      (f := fun ω => g (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω))
      (g := R) hg_sm
      (by
        exact h_int.congr (Filter.Eventually.of_forall (fun ω => by
          simp [R, I0, M0, M1])))
      hR_int
  have h_residual_ce_zero :
      B0.condExpGiven R P.μ =ᵐ[P.μ] (fun _ => (0 : ℝ)) := by
    simpa [B0, R, I0, M0, M1] using
      cond_exp_residual_zero_stage0 S h_overlap hA h_y2
  have hgresid_ce_zero :
      B0.condExpGiven
          (fun ω => g (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) * R ω) P.μ
        =ᵐ[P.μ] (fun _ => (0 : ℝ)) := by
    refine hcondexp_pull.trans ?_
    filter_upwards [h_residual_ce_zero] with ω hω
    rw [Pi.mul_apply, hω, mul_zero]
  calc
    ∫ ω, g (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) *
        ((S.toPODTRSystem.dVar ⟨0, by decide⟩).indicator
            (S.dbar ⟨0, by decide⟩) ω *
          (S.μ₁_val
              (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
               S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
               S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) -
            S.μ₀_val (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω))) ∂P.μ
        = ∫ ω, g (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) * R ω ∂P.μ := by
          rfl
    _ = ∫ ω, B0.condExpGiven
          (fun ω => g (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) * R ω) P.μ ω
          ∂P.μ := by
        exact (MeasureTheory.integral_condExp B0.sigma_le).symm
    _ = ∫ _, (0 : ℝ) ∂P.μ :=
        MeasureTheory.integral_congr_ae hgresid_ce_zero
    _ = 0 := MeasureTheory.integral_zero _ _

/-- Stage-0 indicator-to-propensity rewrite.  For any measurable
`f : γ 0 → ℝ`, the integral of `f(S₀) · 1{D₀ = dbar 0}` equals the integral
of `f(S₀) · e₀_val(S₀)` against `P.μ`, by pulling `f(S₀)` out of
`(historyBundle 0).sigma`-conditional expectation and replacing
`μ[1{D₀ = dbar 0} | σ(historyBundle 0)]` with `e₀_val ∘ factualS 0` via
`e₀_compat`. -/
theorem indicator_to_propScore_integral_stage0
    (S : DTREstimationSystem P δ γ)
    (f : γ 0 → ℝ) (hf_meas : Measurable f)
    (hf_ind_int : Integrable
      (fun ω => f (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) *
        (S.toPODTRSystem.dVar ⟨0, by decide⟩).indicator
            (S.dbar ⟨0, by decide⟩) ω) P.μ) :
    ∫ ω, f (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) *
        (S.toPODTRSystem.dVar ⟨0, by decide⟩).indicator
            (S.dbar ⟨0, by decide⟩) ω ∂P.μ
      = ∫ ω, f (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) *
          S.e₀_val (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) ∂P.μ := by
  let B := S.toPODTRSystem.historyBundle 0 (by decide)
  have hf_sm : StronglyMeasurable[B.sigma]
      (fun ω => f (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω)) := by
    have hs0 : Measurable[B.sigma]
        (S.toPODTRSystem.factualS ⟨0, by decide⟩) :=
      S.toPODTRSystem.measurable_factualS_sigma_history 0 (by decide)
        ⟨0, by decide⟩ (by decide)
    exact (hf_meas.comp hs0).stronglyMeasurable
  have hind_int : Integrable
      ((S.toPODTRSystem.dVar ⟨0, by decide⟩).indicator
        (S.dbar ⟨0, by decide⟩)) P.μ :=
    (S.toPODTRSystem.dVar ⟨0, by decide⟩).integrable_indicator
      (S.dbar ⟨0, by decide⟩)
  have hCE_pull :=
    B.condExpGiven_mul_of_stronglyMeasurable_left
      (μ := P.μ) hf_sm hf_ind_int hind_int
  have hCE_replace :
      B.condExpGiven
          (fun ω => f (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) *
            (S.toPODTRSystem.dVar ⟨0, by decide⟩).indicator
              (S.dbar ⟨0, by decide⟩) ω) P.μ
        =ᵐ[P.μ]
          (fun ω => f (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) *
            S.e₀_val (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω)) := by
    refine hCE_pull.trans ?_
    filter_upwards [S.e₀_compat] with ω hω
    rw [Pi.mul_apply, hω]
  calc
    ∫ ω, f (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) *
        (S.toPODTRSystem.dVar ⟨0, by decide⟩).indicator
            (S.dbar ⟨0, by decide⟩) ω ∂P.μ
      = ∫ ω, B.condExpGiven
          (fun ω => f (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) *
            (S.toPODTRSystem.dVar ⟨0, by decide⟩).indicator
              (S.dbar ⟨0, by decide⟩) ω) P.μ ω ∂P.μ :=
        (MeasureTheory.integral_condExp B.sigma_le).symm
    _ = ∫ ω, f (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) *
          S.e₀_val (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) ∂P.μ :=
        MeasureTheory.integral_congr_ae hCE_replace

/-! ## Stage 1 helpers

Conditioning σ-algebra: `(historyBundle 1).sigma`.
Indicator: `(dVar ⟨1, _⟩).indicator (dbar ⟨1, _⟩)`.
Outcome: `factualY` minus `μ₁_val ∘ (factualS 1, factualD 0, factualS 0)`.

Each integral is additionally weighted by stage-0 indicator
`1{D₀ = dbar 0}` so the resulting product picks out the trajectory
following the target regime in both stages. -/

/-- Stage-1 weighted-residual integral.  Whenever `g : γ 1 × δ × γ 0 → ℝ` is
measurable and the resulting product is integrable, the integral against
`μ` of
`g(S₁,D₀,S₀)(ω) · 1{D₀(ω) = dbar 0} · 1{D₁(ω) = dbar 1} ·
  (Y(ω) − μ₁_val(S₁(ω), D₀(ω), S₀(ω)))`
is zero.  The stage-0 indicator factor is `(historyBundle 1).sigma`-measurable
(it is in particular measurable in `D₀, S₀`), so it absorbs into the
`σ(historyBundle 1)`-pull-out, and the residual conditional expectation
vanishes. -/
theorem weighted_residual_integral_zero_stage1
    (S : DTREstimationSystem P δ γ)
    {ε : ℝ}
    (h_overlap : S.StrictOverlap ε)
    (hA : S.toPODTRSystem.Assumptions)
    (h_y2 : Integrable (fun ω => (S.toPODTRSystem.factualY ω) ^ 2) P.μ)
    (g : γ 1 × δ × γ 0 → ℝ) (hg_meas : Measurable g)
    (h_int : Integrable
      (fun ω => g (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
                   S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
                   S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) *
        ((S.toPODTRSystem.dVar ⟨0, by decide⟩).indicator
            (S.dbar ⟨0, by decide⟩) ω *
         ((S.toPODTRSystem.dVar ⟨1, by decide⟩).indicator
            (S.dbar ⟨1, by decide⟩) ω *
          (S.toPODTRSystem.factualY ω -
            S.μ₁_val
              (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
               S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
               S.toPODTRSystem.factualS ⟨0, by decide⟩ ω))))) P.μ) :
    ∫ ω, g (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
            S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
            S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) *
        ((S.toPODTRSystem.dVar ⟨0, by decide⟩).indicator
            (S.dbar ⟨0, by decide⟩) ω *
         ((S.toPODTRSystem.dVar ⟨1, by decide⟩).indicator
            (S.dbar ⟨1, by decide⟩) ω *
          (S.toPODTRSystem.factualY ω -
            S.μ₁_val
              (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
               S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
               S.toPODTRSystem.factualS ⟨0, by decide⟩ ω)))) ∂P.μ = 0 := by
  let B1 := S.toPODTRSystem.historyBundle 1 (by decide)
  let H1 : P.Ω → γ 1 × δ × γ 0 := fun ω =>
    (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
     S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
     S.toPODTRSystem.factualS ⟨0, by decide⟩ ω)
  let I0 : P.Ω → ℝ :=
    (S.toPODTRSystem.dVar ⟨0, by decide⟩).indicator
      (S.dbar ⟨0, by decide⟩)
  let I1 : P.Ω → ℝ :=
    (S.toPODTRSystem.dVar ⟨1, by decide⟩).indicator
      (S.dbar ⟨1, by decide⟩)
  let M1 : P.Ω → ℝ := fun ω => S.μ₁_val (H1 ω)
  let R : P.Ω → ℝ :=
    fun ω => I0 ω * (I1 ω * (S.toPODTRSystem.factualY ω - M1 ω))
  have hg_sm : StronglyMeasurable[B1.sigma] (fun ω => g (H1 ω)) := by
    have hs1 : Measurable[B1.sigma] (S.toPODTRSystem.factualS ⟨1, by decide⟩) :=
      S.toPODTRSystem.measurable_factualS_sigma_history 1 (by decide)
        ⟨1, by decide⟩ (by decide)
    have hd0 : Measurable[B1.sigma] (S.toPODTRSystem.factualD ⟨0, by decide⟩) :=
      S.toPODTRSystem.measurable_factualD_sigma_history 1 (by decide)
        ⟨0, by decide⟩ (by decide)
    have hs0 : Measurable[B1.sigma] (S.toPODTRSystem.factualS ⟨0, by decide⟩) :=
      S.toPODTRSystem.measurable_factualS_sigma_history 1 (by decide)
        ⟨0, by decide⟩ (by decide)
    exact (hg_meas.comp (hs1.prod (hd0.prod hs0))).stronglyMeasurable
  have hYf_int : Integrable S.toPODTRSystem.factualY P.μ := hA.integrable_factualY
  have hM1_int : Integrable M1 P.μ := by
    have hM1_L2 : MemLp M1 2 P.μ := by
      simpa [H1, M1] using (S.stageOneReg_memLp h_overlap h_y2).ae_eq
        (S.μ₁_val_comp_eq_stageOneReg).symm
    exact hM1_L2.integrable (by norm_num)
  have hM1_meas : Measurable M1 := by
    have hs1 := S.toPODTRSystem.measurable_factualS ⟨1, by decide⟩
    have hd0 := S.toPODTRSystem.measurable_factualD ⟨0, by decide⟩
    have hs0 := S.toPODTRSystem.measurable_factualS ⟨0, by decide⟩
    exact S.μ₁_meas.comp (hs1.prod (hd0.prod hs0))
  have hI1Yf_int : Integrable
      (fun ω => I1 ω * S.toPODTRSystem.factualY ω) P.μ := by
    have h := (S.toPODTRSystem.dVar ⟨1, by decide⟩).integrable_mul_indicator
      (S.dbar ⟨1, by decide⟩) hYf_int S.toPODTRSystem.measurable_factualY
    exact h.congr (Filter.Eventually.of_forall (fun ω => by simp [I1, mul_comm]))
  have hI1M1_int : Integrable (fun ω => I1 ω * M1 ω) P.μ := by
    have h := (S.toPODTRSystem.dVar ⟨1, by decide⟩).integrable_mul_indicator
      (S.dbar ⟨1, by decide⟩) hM1_int hM1_meas
    exact h.congr (Filter.Eventually.of_forall (fun ω => by simp [I1, M1, mul_comm]))
  have hI1_res_int : Integrable
      (fun ω => I1 ω * (S.toPODTRSystem.factualY ω - M1 ω)) P.μ := by
    have hsub := hI1Yf_int.sub hI1M1_int
    refine hsub.congr ?_
    exact Filter.Eventually.of_forall (fun ω => by
      rw [Pi.sub_apply]
      ring)
  have hI1_res_meas : Measurable
      (fun ω => I1 ω * (S.toPODTRSystem.factualY ω - M1 ω)) :=
    ((S.toPODTRSystem.dVar ⟨1, by decide⟩).measurable_indicator
      (S.dbar ⟨1, by decide⟩)).mul
      (S.toPODTRSystem.measurable_factualY.sub hM1_meas)
  have hR_int : Integrable R P.μ := by
    have h := (S.toPODTRSystem.dVar ⟨0, by decide⟩).integrable_mul_indicator
      (S.dbar ⟨0, by decide⟩) hI1_res_int hI1_res_meas
    exact h.congr (Filter.Eventually.of_forall (fun ω => by
      simp [R, I0, I1, M1, mul_comm]))
  have hcondexp_pull :=
    B1.condExpGiven_mul_of_stronglyMeasurable_left
      (f := fun ω => g (H1 ω)) (g := R) hg_sm
      (by
        exact h_int.congr (Filter.Eventually.of_forall (fun ω => by
          simp [R, H1, I0, I1, M1])))
      hR_int
  have h_residual_ce_zero :
      B1.condExpGiven R P.μ =ᵐ[P.μ] (fun _ => (0 : ℝ)) := by
    simpa [B1, R, H1, I0, I1, M1] using
      cond_exp_residual_zero_stage1 S h_overlap hA h_y2
  have hgresid_ce_zero :
      B1.condExpGiven (fun ω => g (H1 ω) * R ω) P.μ
        =ᵐ[P.μ] (fun _ => (0 : ℝ)) := by
    refine hcondexp_pull.trans ?_
    filter_upwards [h_residual_ce_zero] with ω hω
    rw [Pi.mul_apply, hω, mul_zero]
  calc
    ∫ ω, g (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
            S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
            S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) *
        ((S.toPODTRSystem.dVar ⟨0, by decide⟩).indicator
            (S.dbar ⟨0, by decide⟩) ω *
         ((S.toPODTRSystem.dVar ⟨1, by decide⟩).indicator
            (S.dbar ⟨1, by decide⟩) ω *
          (S.toPODTRSystem.factualY ω -
            S.μ₁_val
              (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
               S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
               S.toPODTRSystem.factualS ⟨0, by decide⟩ ω)))) ∂P.μ
        = ∫ ω, g (H1 ω) * R ω ∂P.μ := by
          rfl
    _ = ∫ ω, B1.condExpGiven (fun ω => g (H1 ω) * R ω) P.μ ω ∂P.μ := by
        exact (MeasureTheory.integral_condExp B1.sigma_le).symm
    _ = ∫ _, (0 : ℝ) ∂P.μ :=
        MeasureTheory.integral_congr_ae hgresid_ce_zero
    _ = 0 := MeasureTheory.integral_zero _ _

/-- Stage-1 indicator-to-propensity rewrite.  For any measurable
`f : γ 1 × δ × γ 0 → ℝ`, the integral of `f(S₁,D₀,S₀) · 1{D₁ = dbar 1}` (with
extra σ(historyBundle 1)-measurable weight) equals the integral of
`f(S₁,D₀,S₀) · e₁_val(S₁,D₀,S₀)`, by pulling the σ(historyBundle 1)-measurable
factor out and applying `e₁_compat`. -/
theorem indicator_to_propScore_integral_stage1
    (S : DTREstimationSystem P δ γ)
    (f : γ 1 × δ × γ 0 → ℝ) (hf_meas : Measurable f)
    (hf_ind_int : Integrable
      (fun ω => f (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
                   S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
                   S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) *
        (S.toPODTRSystem.dVar ⟨1, by decide⟩).indicator
            (S.dbar ⟨1, by decide⟩) ω) P.μ) :
    ∫ ω, f (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
            S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
            S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) *
        (S.toPODTRSystem.dVar ⟨1, by decide⟩).indicator
            (S.dbar ⟨1, by decide⟩) ω ∂P.μ
      = ∫ ω, f (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
                S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
                S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) *
          S.e₁_val
            (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
             S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
             S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) ∂P.μ := by
  let B := S.toPODTRSystem.historyBundle 1 (by decide)
  have hf_sm : StronglyMeasurable[B.sigma]
      (fun ω => f (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
                   S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
                   S.toPODTRSystem.factualS ⟨0, by decide⟩ ω)) := by
    have hs1 : Measurable[B.sigma]
        (S.toPODTRSystem.factualS ⟨1, by decide⟩) :=
      S.toPODTRSystem.measurable_factualS_sigma_history 1 (by decide)
        ⟨1, by decide⟩ (by decide)
    have hd0 : Measurable[B.sigma]
        (S.toPODTRSystem.factualD ⟨0, by decide⟩) :=
      S.toPODTRSystem.measurable_factualD_sigma_history 1 (by decide)
        ⟨0, by decide⟩ (by decide)
    have hs0 : Measurable[B.sigma]
        (S.toPODTRSystem.factualS ⟨0, by decide⟩) :=
      S.toPODTRSystem.measurable_factualS_sigma_history 1 (by decide)
        ⟨0, by decide⟩ (by decide)
    exact (hf_meas.comp (hs1.prod (hd0.prod hs0))).stronglyMeasurable
  have hind_int : Integrable
      ((S.toPODTRSystem.dVar ⟨1, by decide⟩).indicator
        (S.dbar ⟨1, by decide⟩)) P.μ :=
    (S.toPODTRSystem.dVar ⟨1, by decide⟩).integrable_indicator
      (S.dbar ⟨1, by decide⟩)
  have hCE_pull :=
    B.condExpGiven_mul_of_stronglyMeasurable_left
      (μ := P.μ) hf_sm hf_ind_int hind_int
  have hCE_replace :
      B.condExpGiven
          (fun ω => f (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
                       S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
                       S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) *
            (S.toPODTRSystem.dVar ⟨1, by decide⟩).indicator
              (S.dbar ⟨1, by decide⟩) ω) P.μ
        =ᵐ[P.μ]
          (fun ω => f (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
                       S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
                       S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) *
            S.e₁_val
              (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
               S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
               S.toPODTRSystem.factualS ⟨0, by decide⟩ ω)) := by
    refine hCE_pull.trans ?_
    filter_upwards [S.e₁_compat] with ω hω
    rw [Pi.mul_apply, hω]
  calc
    ∫ ω, f (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
            S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
            S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) *
        (S.toPODTRSystem.dVar ⟨1, by decide⟩).indicator
            (S.dbar ⟨1, by decide⟩) ω ∂P.μ
      = ∫ ω, B.condExpGiven
          (fun ω => f (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
                       S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
                       S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) *
            (S.toPODTRSystem.dVar ⟨1, by decide⟩).indicator
              (S.dbar ⟨1, by decide⟩) ω) P.μ ω ∂P.μ :=
        (MeasureTheory.integral_condExp B.sigma_le).symm
    _ = ∫ ω, f (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
                S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
                S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) *
          S.e₁_val
            (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
             S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
             S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) ∂P.μ :=
        MeasureTheory.integral_congr_ae hCE_replace

end DTREstimationSystem

end DTR
end Estimation
end Causalean
