/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Mean zero of the sequential DR (DTR) influence function

Headline theorem `seqDR_mean_zero`:

    ∫ z, ψ_seqDR z ∂(P_Z) = 0

Decomposition mirrors the ATE AIPW analysis but is staged: the
sequential DR moment expands as

* `μ₀_val(S₀)`                                                 — gives `θ₀`
* `(1{D₀=dbar 0} / e₀_val(S₀)) · (μ₁_val(S₁,D₀,S₀) − μ₀_val(S₀))` — stage-0 correction
* `(1{D₀=dbar 0} · 1{D₁=dbar 1} / (e₀_val(S₀) · e₁_val(S₁,D₀,S₀))) ·
    (Y − μ₁_val(S₁,D₀,S₀))`                                    — stage-1 correction
* `−θ₀`                                                        — constant

The two correction terms vanish via the stagewise weighted-residual integral
lemmas in `ScorePullout.lean`.
-/

import Causalean.Estimation.DTR.SeqDRMoment

/-!
Proves mean-zero properties for the sequential doubly robust score. The module
handles measurability, conditioning, and stagewise cancellation needed for the
DTR influence-function argument.
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

/-! ## Measurability of `ψ_seqDR` -/

/-- Measurability of the sequential DR influence function on the data tuple
`(s₀, d₀, s₁, d₁, y) : γ 0 × δ × γ 1 × δ × ℝ`.  Decomposes into
`Measurable.add`/`Measurable.mul`/`Measurable.div` chained against the
projections, the indicator functions `indEq`, and the value-space
nuisance functions stored in `S.η₀`. -/
lemma measurable_ψ_seqDR (S : DTREstimationSystem P δ γ) :
    Measurable S.ψ_seqDR := by
  simpa [DTREstimationSystem.ψ_seqDR] using
    S.measurable_seqDRMomentFunctional S.η₀ S.θ₀

/-! ## Helpers: stagewise propensity nondegeneracy -/

/-- Stage-0 propensity is a.e. nonzero under the DTR backdoor assumptions.
The conditional indicator `μ[1{D₀ = dbar 0} | σ(historyBundle 0)]` is
identified via `e₀_compat` with `e₀_val ∘ factualS 0`, and `e₀_val > 0`
pointwise on `γ 0`. -/
lemma propScore_ne_zero_stage0 (S : DTREstimationSystem P δ γ)
    (hA : S.toPODTRSystem.Assumptions) :
    ∀ᵐ ω ∂P.μ,
      (S.toPODTRSystem.historyBundle 0 (by decide)).condExpGiven
        ((S.toPODTRSystem.dVar ⟨0, by decide⟩).indicator
            (S.dbar ⟨0, by decide⟩)) P.μ ω ≠ 0 := by
  filter_upwards [hA.overlap S.dbar ⟨0, by decide⟩] with ω hω
  exact ne_of_gt hω

/-- Stage-1 propensity is a.e. nonzero under the DTR backdoor assumptions.
Analogous to `propScore_ne_zero_stage0` via `e₁_compat` and `e₁_pos`. -/
lemma propScore_ne_zero_stage1 (S : DTREstimationSystem P δ γ)
    (hA : S.toPODTRSystem.Assumptions) :
    ∀ᵐ ω ∂P.μ,
      (S.toPODTRSystem.historyBundle 1 (by decide)).condExpGiven
        ((S.toPODTRSystem.dVar ⟨1, by decide⟩).indicator
            (S.dbar ⟨1, by decide⟩)) P.μ ω ≠ 0 := by
  filter_upwards [hA.overlap S.dbar ⟨1, by decide⟩] with ω hω
  exact ne_of_gt hω

/-! ## Stagewise residual conditional-expectation zero lemmas

Stage-0 residual `1{D₀=dbar 0}·(μ₁_val(history₁) − μ₀_val(S₀))` has
σ(historyBundle 0)-conditional expectation zero a.s.; stage-1 analogue uses
`(factualY − μ₁_val(history₁))` under σ(historyBundle 1) (where consistency
bridges `factualY` to `Y_of dbar` under the joint regime indicator). -/

/-- Stage-0 residual conditional expectation is zero a.s.: under DTR
assumptions, `μ[1{D₀=dbar 0}·(μ₁_val(history₁) − μ₀_val(S₀)) | σ(historyBundle 0)] =ᵐ 0`.

Argument: by `stageOneReg_indD_eq` plus `μ₁_reg_compat`, the stage-1
observable regression agrees with the σ(historyBundle 1) CE of `Y_of dbar`
after multiplication by the partial regime indicator. Tower with
σ(history₀) ⊆ σ(history₁) gives
`E[μ₁_val(history₁)|hist₀] = E[Y_of dbar|hist₀] = μ₀_val(S₀)`
(using `μ₀_compat`). Sequential exchangeability `D₀ ⟂ Y(dbar) | history₀`
plus `e₀_compat` give `E[indD₀(dbar 0)·μ₁_val(history₁)|hist₀] =
e₀_val(S₀)·μ₀_val(S₀)`, and similarly for the `μ₀_val(S₀)` term;
the difference is zero. -/
lemma cond_exp_residual_zero_stage0
    (S : DTREstimationSystem P δ γ)
    {ε : ℝ}
    (h_overlap : S.StrictOverlap ε)
    (hA : S.toPODTRSystem.Assumptions)
    (h_y2 : Integrable (fun ω => (S.toPODTRSystem.factualY ω) ^ 2) P.μ) :
    (S.toPODTRSystem.historyBundle 0 (by decide)).condExpGiven
        (fun ω => (S.toPODTRSystem.dVar ⟨0, by decide⟩).indicator
            (S.dbar ⟨0, by decide⟩) ω *
          (S.μ₁_val
              (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
               S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
               S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) -
            S.μ₀_val (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω))) P.μ
      =ᵐ[P.μ] (fun _ => (0 : ℝ)) := by
  let B0 := S.toPODTRSystem.historyBundle 0 (by decide)
  let B1 := S.toPODTRSystem.historyBundle 1 (by decide)
  let I0 : P.Ω → ℝ :=
    (S.toPODTRSystem.dVar ⟨0, by decide⟩).indicator
      (S.dbar ⟨0, by decide⟩)
  let Y : P.Ω → ℝ := S.toPODTRSystem.Y_of S.dbar
  let M0 : P.Ω → ℝ :=
    fun ω => S.μ₀_val (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω)
  let M1 : P.Ω → ℝ :=
    fun ω => S.μ₁_val
      (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
       S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
       S.toPODTRSystem.factualS ⟨0, by decide⟩ ω)
  have hY_int : Integrable Y P.μ := by
    simpa [Y] using hA.integrable_Y S.dbar
  have hI0_int : Integrable I0 P.μ := by
    simpa [I0] using
      (S.toPODTRSystem.dVar ⟨0, by decide⟩).integrable_indicator
        (S.dbar ⟨0, by decide⟩)
  have hI0Y_int : Integrable (fun ω => I0 ω * Y ω) P.μ := by
    have h := (S.toPODTRSystem.dVar ⟨0, by decide⟩).integrable_mul_indicator
      (S.dbar ⟨0, by decide⟩) hY_int
      (by simpa [Y] using S.toPODTRSystem.measurable_Y_of S.dbar)
    exact h.congr (Filter.Eventually.of_forall (fun ω => by simp [I0, Y, mul_comm]))
  have hM0_int : Integrable M0 P.μ := by
    exact (B0.integrable_condExpGiven (S.toPODTRSystem.Y_of S.dbar)).congr
      (by simpa [B0, M0] using S.μ₀_compat hA)
  have hM1_int : Integrable M1 P.μ := by
    have hM1_L2 : MemLp M1 2 P.μ := by
      simpa [M1] using (S.stageOneReg_memLp h_overlap h_y2).ae_eq
        (S.μ₁_val_comp_eq_stageOneReg).symm
    exact hM1_L2.integrable (by norm_num)
  have hM0_meas : Measurable M0 := by
    exact S.μ₀_meas.comp (S.toPODTRSystem.measurable_factualS ⟨0, by decide⟩)
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
  have hres_eq :
      (fun ω => I0 ω * (M1 ω - M0 ω))
        = (fun ω => I0 ω * M1 ω - I0 ω * M0 ω) := by
    funext ω
    ring
  have hsub :
      B0.condExpGiven (fun ω => I0 ω * M1 ω - I0 ω * M0 ω) P.μ
        =ᵐ[P.μ]
          B0.condExpGiven (fun ω => I0 ω * M1 ω) P.μ
            - B0.condExpGiven (fun ω => I0 ω * M0 ω) P.μ := by
    simpa [POCFBundle.condExpGiven] using
      MeasureTheory.condExp_sub hI0M1_int hI0M0_int B0.sigma
  have hI0_sm_B1 :
      StronglyMeasurable[B1.sigma] I0 := by
    simpa [B1, I0] using
      S.toPODTRSystem.stronglyMeasurable_indicator_dVar_sigma_history
        1 (by decide) ⟨0, by decide⟩ (by decide) (S.dbar ⟨0, by decide⟩)
  have hrev_B1 :
      (fun ω => I0 ω * M1 ω)
        =ᵐ[P.μ] B1.condExpGiven (fun ω => I0 ω * Y ω) P.μ := by
    have hI0_eq_indD : I0 = S.toPODTRSystem.indD S.dbar 1 := by
      funext ω
      have hsplit := congr_fun
        (S.toPODTRSystem.indD_factor_split S.dbar 0 (by decide)) ω
      simp [I0, PODTRSystem.indD] at hsplit ⊢
    have hpull :=
      B1.condExpGiven_mul_of_stronglyMeasurable_left
        (f := I0) (g := Y) hI0_sm_B1 hI0Y_int hY_int
    filter_upwards [hpull,
      (by simpa [I0, B1, M1, Y] using S.indD_mul_μ₁_val_comp_eq hA)] with ω hp hμ1
    have hp' :
        B1.condExpGiven (fun ω => I0 ω * Y ω) P.μ ω =
          I0 ω * B1.condExpGiven Y P.μ ω := by
      simpa [Pi.mul_apply] using hp
    have hμ1_local : I0 ω * M1 ω = I0 ω * B1.condExpGiven Y P.μ ω := by
      simpa [I0, B1, M1, Y, hI0_eq_indD] using hμ1
    rw [hp']
    exact hμ1_local
  haveI : IsFiniteMeasure (P.μ.trim B1.sigma_le) := isFiniteMeasure_trim _
  have hB0_le_B1 : B0.sigma ≤ B1.sigma := by
    simpa [B0, B1] using
      S.toPODTRSystem.historyBundle_sigma_mono 0 1 (by decide) (by decide)
  have htower :
      B0.condExpGiven (B1.condExpGiven (fun ω => I0 ω * Y ω) P.μ) P.μ
        =ᵐ[P.μ] B0.condExpGiven (fun ω => I0 ω * Y ω) P.μ := by
    have h := B1.condExpGiven_tower_of_le
      (g := fun ω => I0 ω * Y ω) (μ := P.μ) (m := B0.sigma) hB0_le_B1
    simpa [POCFBundle.condExpGiven] using h
  have hCE_I0M1_to_Y :
      B0.condExpGiven (fun ω => I0 ω * M1 ω) P.μ
        =ᵐ[P.μ] B0.condExpGiven (fun ω => I0 ω * Y ω) P.μ := by
    exact (B0.condExpGiven_congr_ae hrev_B1).trans htower
  have hcfY_n : (S.toPODTRSystem.cfYBundle S.dbar).n = 1 := rfl
  let i0 : Fin (S.toPODTRSystem.cfYBundle S.dbar).n :=
    ⟨0, by rw [hcfY_n]; exact Nat.one_pos⟩
  let ψ : (∀ i : Fin (S.toPODTRSystem.cfYBundle S.dbar).n,
      (S.toPODTRSystem.cfYBundle S.dbar).type i) → ℝ :=
    fun f => (f i0 : ℝ)
  have hψ_meas : Measurable ψ := by
    change Measurable (fun f : (∀ i, (S.toPODTRSystem.cfYBundle S.dbar).type i) =>
      (f i0 : ℝ))
    exact measurable_pi_apply i0
  have hYof_eq_proj :
      S.toPODTRSystem.Y_of S.dbar =
        ψ ∘ (S.toPODTRSystem.cfYBundle S.dbar).jointValue := by
    funext ω
    rfl
  have hCI :
      ProbabilityTheory.CondIndepFun B0.sigma B0.sigma_le
        (S.toPODTRSystem.factualD ⟨0, by decide⟩) Y P.μ := by
    have hproj := (hA.exch S.dbar ⟨0, by decide⟩).project (ψ := ψ) hψ_meas
    change ProbabilityTheory.CondIndepFun B0.sigma B0.sigma_le
      (S.toPODTRSystem.factualD ⟨0, by decide⟩)
      (S.toPODTRSystem.Y_of S.dbar) P.μ
    rw [hYof_eq_proj]
    simpa [B0] using hproj
  let u : δ → ℝ := ({S.dbar ⟨0, by decide⟩} : Set δ).indicator (fun _ => (1 : ℝ))
  have hu_meas : Measurable u :=
    measurable_const.indicator (MeasurableSet.singleton _)
  have hu_eq : (fun ω => u (S.toPODTRSystem.factualD ⟨0, by decide⟩ ω)) = I0 := by
    funext ω
    by_cases h : S.toPODTRSystem.factualD ⟨0, by decide⟩ ω =
        S.dbar ⟨0, by decide⟩
    · have h1 : S.toPODTRSystem.factualD ⟨0, by decide⟩ ω ∈
          ({S.dbar ⟨0, by decide⟩} : Set δ) := h
      have h2 : ω ∈ (S.toPODTRSystem.dVar ⟨0, by decide⟩).event
          (S.dbar ⟨0, by decide⟩) := h
      rw [show u (S.toPODTRSystem.factualD ⟨0, by decide⟩ ω) = (1 : ℝ) from
            Set.indicator_of_mem h1 _,
          show I0 ω = (1 : ℝ) from by
            simpa [I0] using
              (S.toPODTRSystem.dVar ⟨0, by decide⟩).indicator_apply_eq_one h2]
    · have h1 : S.toPODTRSystem.factualD ⟨0, by decide⟩ ω ∉
          ({S.dbar ⟨0, by decide⟩} : Set δ) := h
      have h2 : ω ∉ (S.toPODTRSystem.dVar ⟨0, by decide⟩).event
          (S.dbar ⟨0, by decide⟩) := h
      rw [show u (S.toPODTRSystem.factualD ⟨0, by decide⟩ ω) = (0 : ℝ) from
            Set.indicator_of_notMem h1 _,
          show I0 ω = (0 : ℝ) from by
            simpa [I0] using
              (S.toPODTRSystem.dVar ⟨0, by decide⟩).indicator_apply_eq_zero h2]
  have hfact :
      P.μ[fun ω => u (S.toPODTRSystem.factualD ⟨0, by decide⟩ ω) * Y ω
          | B0.sigma]
        =ᵐ[P.μ]
          P.μ[fun ω => u (S.toPODTRSystem.factualD ⟨0, by decide⟩ ω)
            | B0.sigma] * P.μ[Y | B0.sigma] :=
    condExp_mul_of_condIndep (μ := P.μ)
      (m := B0.sigma) B0.sigma_le
      (f := S.toPODTRSystem.factualD ⟨0, by decide⟩) (g := Y)
      (S.toPODTRSystem.measurable_factualD ⟨0, by decide⟩)
      (by simpa [Y] using S.toPODTRSystem.measurable_Y_of S.dbar) hCI
      (u := u) (v := id) hu_meas measurable_id
      (by rw [hu_eq]; exact hI0_int) hY_int
      (by
        change Integrable
          (fun ω => u (S.toPODTRSystem.factualD ⟨0, by decide⟩ ω) * Y ω) P.μ
        have heq :
            (fun ω => u (S.toPODTRSystem.factualD ⟨0, by decide⟩ ω) * Y ω)
              = (fun ω => I0 ω * Y ω) := by
          funext ω
          rw [congr_fun hu_eq ω]
        rw [heq]
        exact hI0Y_int)
  have hExch :
      B0.condExpGiven (fun ω => I0 ω * Y ω) P.μ
        =ᵐ[P.μ]
          (fun ω => B0.condExpGiven I0 P.μ ω *
            B0.condExpGiven Y P.μ ω) := by
    unfold POCFBundle.condExpGiven
    have hprod_rw :
        (fun ω => u (S.toPODTRSystem.factualD ⟨0, by decide⟩ ω) * Y ω)
          = (fun ω => I0 ω * Y ω) := by
      funext ω
      rw [congr_fun hu_eq ω]
    rw [hprod_rw, hu_eq] at hfact
    filter_upwards [hfact] with ω hω
    simpa [Pi.mul_apply] using hω
  have hCE_I0M1 :
      B0.condExpGiven (fun ω => I0 ω * M1 ω) P.μ
        =ᵐ[P.μ] (fun ω => S.e₀_val (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) *
          S.μ₀_val (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω)) := by
    refine hCE_I0M1_to_Y.trans ?_
    filter_upwards [hExch, S.e₀_compat, S.μ₀_compat hA] with ω hE he hμ
    rw [hE, he, hμ]
  have hM0_sm_B0 : StronglyMeasurable[B0.sigma] M0 := by
    have hs0 : Measurable[B0.sigma] (S.toPODTRSystem.factualS ⟨0, by decide⟩) :=
      S.toPODTRSystem.measurable_factualS_sigma_history 0 (by decide)
        ⟨0, by decide⟩ (by decide)
    exact (S.μ₀_meas.comp hs0).stronglyMeasurable
  have hpull_M0 :=
    B0.condExpGiven_mul_of_stronglyMeasurable_right
      (f := I0) (g := M0) hM0_sm_B0 hI0M0_int hI0_int
  have hCE_I0M0 :
      B0.condExpGiven (fun ω => I0 ω * M0 ω) P.μ
        =ᵐ[P.μ] (fun ω => S.e₀_val (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) *
          S.μ₀_val (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω)) := by
    filter_upwards [hpull_M0, S.e₀_compat] with ω hp he
    have hp' :
        B0.condExpGiven (fun ω => I0 ω * M0 ω) P.μ ω =
          B0.condExpGiven I0 P.μ ω * M0 ω := by
      simpa [Pi.mul_apply] using hp
    rw [hp', he]
  rw [show (fun ω => (S.toPODTRSystem.dVar ⟨0, by decide⟩).indicator
            (S.dbar ⟨0, by decide⟩) ω *
          (S.μ₁_val
              (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
               S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
               S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) -
            S.μ₀_val (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω)))
        = (fun ω => I0 ω * (M1 ω - M0 ω)) by rfl]
  rw [hres_eq]
  refine hsub.trans ?_
  filter_upwards [hCE_I0M1, hCE_I0M0] with ω h1 h0
  rw [Pi.sub_apply, h1, h0]
  ring

/-- Stage-1 residual conditional expectation is zero a.s.: under DTR
assumptions, the σ(historyBundle 1)-conditional expectation of
`1{D₀ = dbar 0} · 1{D₁ = dbar 1} · (factualY − μ₁_val(S₁,D₀,S₀))` is zero a.s.

Both indicators are required: under the joint regime indicator,
`Assumptions.consistency` rewrites `factualY` to `Y_of dbar`, after which
`stageOneReg_indD_eq` plus `μ₁_reg_compat` gives the σ(historyBundle 1)-CE
of `Y_of dbar` in the required `indD₀`-weighted form. The stage-0 indicator is
σ(historyBundle 1)-measurable
(it is in particular measurable in `D₀, S₀`), so it pulls out cleanly. -/
lemma cond_exp_residual_zero_stage1
    (S : DTREstimationSystem P δ γ)
    {ε : ℝ}
    (h_overlap : S.StrictOverlap ε)
    (hA : S.toPODTRSystem.Assumptions)
    (h_y2 : Integrable (fun ω => (S.toPODTRSystem.factualY ω) ^ 2) P.μ) :
    (S.toPODTRSystem.historyBundle 1 (by decide)).condExpGiven
        (fun ω => (S.toPODTRSystem.dVar ⟨0, by decide⟩).indicator
            (S.dbar ⟨0, by decide⟩) ω *
          ((S.toPODTRSystem.dVar ⟨1, by decide⟩).indicator
            (S.dbar ⟨1, by decide⟩) ω *
          (S.toPODTRSystem.factualY ω -
            S.μ₁_val
              (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
               S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
               S.toPODTRSystem.factualS ⟨0, by decide⟩ ω)))) P.μ
      =ᵐ[P.μ] (fun _ => (0 : ℝ)) := by
  let B1 := S.toPODTRSystem.historyBundle 1 (by decide)
  let I0 : P.Ω → ℝ :=
    (S.toPODTRSystem.dVar ⟨0, by decide⟩).indicator
      (S.dbar ⟨0, by decide⟩)
  let I1 : P.Ω → ℝ :=
    (S.toPODTRSystem.dVar ⟨1, by decide⟩).indicator
      (S.dbar ⟨1, by decide⟩)
  let Y : P.Ω → ℝ := S.toPODTRSystem.Y_of S.dbar
  let Yf : P.Ω → ℝ := S.toPODTRSystem.factualY
  let M1 : P.Ω → ℝ :=
    fun ω => S.μ₁_val
      (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
       S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
       S.toPODTRSystem.factualS ⟨0, by decide⟩ ω)
  have hY_int : Integrable Y P.μ := by
    simpa [Y] using hA.integrable_Y S.dbar
  have hYf_int : Integrable Yf P.μ := by
    simpa [Yf] using hA.integrable_factualY
  have hI0_int : Integrable I0 P.μ := by
    simpa [I0] using
      (S.toPODTRSystem.dVar ⟨0, by decide⟩).integrable_indicator
        (S.dbar ⟨0, by decide⟩)
  have hI1_int : Integrable I1 P.μ := by
    simpa [I1] using
      (S.toPODTRSystem.dVar ⟨1, by decide⟩).integrable_indicator
        (S.dbar ⟨1, by decide⟩)
  have hM1_int : Integrable M1 P.μ := by
    have hM1_L2 : MemLp M1 2 P.μ := by
      simpa [M1] using (S.stageOneReg_memLp h_overlap h_y2).ae_eq
        (S.μ₁_val_comp_eq_stageOneReg).symm
    exact hM1_L2.integrable (by norm_num)
  have hM1_meas : Measurable M1 := by
    have hs1 := S.toPODTRSystem.measurable_factualS ⟨1, by decide⟩
    have hd0 := S.toPODTRSystem.measurable_factualD ⟨0, by decide⟩
    have hs0 := S.toPODTRSystem.measurable_factualS ⟨0, by decide⟩
    exact S.μ₁_meas.comp (hs1.prod (hd0.prod hs0))
  have hI1Y_int : Integrable (fun ω => I1 ω * Y ω) P.μ := by
    have h := (S.toPODTRSystem.dVar ⟨1, by decide⟩).integrable_mul_indicator
      (S.dbar ⟨1, by decide⟩) hY_int
      (by simpa [Y] using S.toPODTRSystem.measurable_Y_of S.dbar)
    exact h.congr (Filter.Eventually.of_forall (fun ω => by simp [I1, Y, mul_comm]))
  have hI1Yf_int : Integrable (fun ω => I1 ω * Yf ω) P.μ := by
    have h := (S.toPODTRSystem.dVar ⟨1, by decide⟩).integrable_mul_indicator
      (S.dbar ⟨1, by decide⟩) hYf_int
      (by simpa [Yf] using S.toPODTRSystem.measurable_factualY)
    exact h.congr (Filter.Eventually.of_forall (fun ω => by simp [I1, Yf, mul_comm]))
  have hI1M1_int : Integrable (fun ω => I1 ω * M1 ω) P.μ := by
    have h := (S.toPODTRSystem.dVar ⟨1, by decide⟩).integrable_mul_indicator
      (S.dbar ⟨1, by decide⟩) hM1_int hM1_meas
    exact h.congr (Filter.Eventually.of_forall (fun ω => by simp [I1, M1, mul_comm]))
  have hI0I1Y_int : Integrable (fun ω => I0 ω * (I1 ω * Y ω)) P.μ := by
    have hmeas : Measurable (fun ω => I1 ω * Y ω) :=
      ((S.toPODTRSystem.dVar ⟨1, by decide⟩).measurable_indicator
        (S.dbar ⟨1, by decide⟩)).mul
        (by simpa [Y] using S.toPODTRSystem.measurable_Y_of S.dbar)
    have h := (S.toPODTRSystem.dVar ⟨0, by decide⟩).integrable_mul_indicator
      (S.dbar ⟨0, by decide⟩) hI1Y_int hmeas
    exact h.congr (Filter.Eventually.of_forall (fun ω => by
      simp [I0, I1, Y, mul_comm, mul_left_comm]))
  have hI0I1Yf_int : Integrable (fun ω => I0 ω * (I1 ω * Yf ω)) P.μ := by
    have hmeas : Measurable (fun ω => I1 ω * Yf ω) :=
      ((S.toPODTRSystem.dVar ⟨1, by decide⟩).measurable_indicator
        (S.dbar ⟨1, by decide⟩)).mul
        (by simpa [Yf] using S.toPODTRSystem.measurable_factualY)
    have h := (S.toPODTRSystem.dVar ⟨0, by decide⟩).integrable_mul_indicator
      (S.dbar ⟨0, by decide⟩) hI1Yf_int hmeas
    exact h.congr (Filter.Eventually.of_forall (fun ω => by
      simp [I0, I1, Yf, mul_comm, mul_left_comm]))
  have hI0I1M1_int : Integrable (fun ω => I0 ω * (I1 ω * M1 ω)) P.μ := by
    have hmeas : Measurable (fun ω => I1 ω * M1 ω) :=
      ((S.toPODTRSystem.dVar ⟨1, by decide⟩).measurable_indicator
        (S.dbar ⟨1, by decide⟩)).mul hM1_meas
    have h := (S.toPODTRSystem.dVar ⟨0, by decide⟩).integrable_mul_indicator
      (S.dbar ⟨0, by decide⟩) hI1M1_int hmeas
    exact h.congr (Filter.Eventually.of_forall (fun ω => by
      simp [I0, I1, M1, mul_comm]))
  have hres_eq :
      (fun ω => I0 ω * (I1 ω * (Yf ω - M1 ω)))
        = (fun ω => I0 ω * (I1 ω * Yf ω) -
          I0 ω * (I1 ω * M1 ω)) := by
    funext ω
    ring
  have hsub :
      B1.condExpGiven
          (fun ω => I0 ω * (I1 ω * Yf ω) - I0 ω * (I1 ω * M1 ω)) P.μ
        =ᵐ[P.μ]
          B1.condExpGiven (fun ω => I0 ω * (I1 ω * Yf ω)) P.μ
            - B1.condExpGiven (fun ω => I0 ω * (I1 ω * M1 ω)) P.μ := by
    simpa [POCFBundle.condExpGiven] using
      MeasureTheory.condExp_sub hI0I1Yf_int hI0I1M1_int B1.sigma
  have hConsistency :
      (fun ω => Yf ω * S.toPODTRSystem.indD S.dbar 2 ω)
        = (fun ω => Y ω * S.toPODTRSystem.indD S.dbar 2 ω) := by
    have h := POVar.factual_mul_indicator_eq_cf_mul_indicator
      hA.consistency S.toPODTRSystem.yVar (S.toPODTRSystem.regime S.dbar)
      (S.toPODTRSystem.yVar_notMem_regime S.dbar)
      {ω | ∀ i : Fin 2, S.toPODTRSystem.factualD i ω = S.dbar i}
      (S.toPODTRSystem.factualAgrees_regime S.dbar)
    have hrewrite : S.toPODTRSystem.indD S.dbar 2 =
        ({ω | ∀ i : Fin 2, S.toPODTRSystem.factualD i ω = S.dbar i}).indicator
          (fun _ => (1 : ℝ)) := by
      have h0 := S.toPODTRSystem.indD_eq_indicator_event S.dbar 2 (le_refl 2)
      have h_set_eq :
          ({ω | ∀ i : Fin 2, i.val < 2 → S.toPODTRSystem.factualD i ω = S.dbar i})
            = {ω | ∀ i : Fin 2, S.toPODTRSystem.factualD i ω = S.dbar i} := by
        ext ω
        refine ⟨fun hω i => hω i i.isLt, fun hω i _ => hω i⟩
      rw [h0, h_set_eq]
    change
      (fun ω => S.toPODTRSystem.factualY ω * S.toPODTRSystem.indD S.dbar 2 ω)
        = (fun ω => S.toPODTRSystem.Y_of S.dbar ω *
          S.toPODTRSystem.indD S.dbar 2 ω)
    rw [hrewrite]
    exact h
  have hIndD2_factor :
      S.toPODTRSystem.indD S.dbar 2 = fun ω => I0 ω * I1 ω := by
    funext ω
    have hsplit1 := congr_fun
      (S.toPODTRSystem.indD_factor_split S.dbar 1 (by decide)) ω
    have hsplit0 := congr_fun
      (S.toPODTRSystem.indD_factor_split S.dbar 0 (by decide)) ω
    rw [hsplit1, hsplit0]
    have hzero : S.toPODTRSystem.indD S.dbar 0 ω = 1 := rfl
    rw [hzero]
    ring
  have hFact_to_cf :
      (fun ω => I0 ω * (I1 ω * Yf ω))
        =ᵐ[P.μ] (fun ω => I0 ω * (I1 ω * Y ω)) := by
    exact Filter.Eventually.of_forall (fun ω => by
      have hc := congr_fun hConsistency ω
      rw [hIndD2_factor] at hc
      change Yf ω * (I0 ω * I1 ω) = Y ω * (I0 ω * I1 ω) at hc
      nlinarith [hc])
  have hCE_fact_to_cf :
      B1.condExpGiven (fun ω => I0 ω * (I1 ω * Yf ω)) P.μ
        =ᵐ[P.μ]
          B1.condExpGiven (fun ω => I0 ω * (I1 ω * Y ω)) P.μ :=
    B1.condExpGiven_congr_ae hFact_to_cf
  have hI0_sm_B1 :
      StronglyMeasurable[B1.sigma] I0 := by
    simpa [B1, I0] using
      S.toPODTRSystem.stronglyMeasurable_indicator_dVar_sigma_history
        1 (by decide) ⟨0, by decide⟩ (by decide) (S.dbar ⟨0, by decide⟩)
  have hM1_sm_B1 : StronglyMeasurable[B1.sigma] M1 := by
    have hs1 : Measurable[B1.sigma] (S.toPODTRSystem.factualS ⟨1, by decide⟩) :=
      S.toPODTRSystem.measurable_factualS_sigma_history 1 (by decide)
        ⟨1, by decide⟩ (by decide)
    have hd0 : Measurable[B1.sigma] (S.toPODTRSystem.factualD ⟨0, by decide⟩) :=
      S.toPODTRSystem.measurable_factualD_sigma_history 1 (by decide)
        ⟨0, by decide⟩ (by decide)
    have hs0 : Measurable[B1.sigma] (S.toPODTRSystem.factualS ⟨0, by decide⟩) :=
      S.toPODTRSystem.measurable_factualS_sigma_history 1 (by decide)
        ⟨0, by decide⟩ (by decide)
    exact (S.μ₁_meas.comp (hs1.prod (hd0.prod hs0))).stronglyMeasurable
  have hI0M1_sm_B1 : StronglyMeasurable[B1.sigma] (fun ω => I0 ω * M1 ω) :=
    hI0_sm_B1.mul hM1_sm_B1
  have hcfY_n : (S.toPODTRSystem.cfYBundle S.dbar).n = 1 := rfl
  let i0 : Fin (S.toPODTRSystem.cfYBundle S.dbar).n :=
    ⟨0, by rw [hcfY_n]; exact Nat.one_pos⟩
  let ψ : (∀ i : Fin (S.toPODTRSystem.cfYBundle S.dbar).n,
      (S.toPODTRSystem.cfYBundle S.dbar).type i) → ℝ :=
    fun f => (f i0 : ℝ)
  have hψ_meas : Measurable ψ := by
    change Measurable (fun f : (∀ i, (S.toPODTRSystem.cfYBundle S.dbar).type i) =>
      (f i0 : ℝ))
    exact measurable_pi_apply i0
  have hYof_eq_proj :
      S.toPODTRSystem.Y_of S.dbar =
        ψ ∘ (S.toPODTRSystem.cfYBundle S.dbar).jointValue := by
    funext ω
    rfl
  have hCI :
      ProbabilityTheory.CondIndepFun B1.sigma B1.sigma_le
        (S.toPODTRSystem.factualD ⟨1, by decide⟩) Y P.μ := by
    have hproj := (hA.exch S.dbar ⟨1, by decide⟩).project (ψ := ψ) hψ_meas
    change ProbabilityTheory.CondIndepFun B1.sigma B1.sigma_le
      (S.toPODTRSystem.factualD ⟨1, by decide⟩)
      (S.toPODTRSystem.Y_of S.dbar) P.μ
    rw [hYof_eq_proj]
    simpa [B1] using hproj
  let u : δ → ℝ := ({S.dbar ⟨1, by decide⟩} : Set δ).indicator (fun _ => (1 : ℝ))
  have hu_meas : Measurable u :=
    measurable_const.indicator (MeasurableSet.singleton _)
  have hu_eq : (fun ω => u (S.toPODTRSystem.factualD ⟨1, by decide⟩ ω)) = I1 := by
    funext ω
    by_cases h : S.toPODTRSystem.factualD ⟨1, by decide⟩ ω =
        S.dbar ⟨1, by decide⟩
    · have h1 : S.toPODTRSystem.factualD ⟨1, by decide⟩ ω ∈
          ({S.dbar ⟨1, by decide⟩} : Set δ) := h
      have h2 : ω ∈ (S.toPODTRSystem.dVar ⟨1, by decide⟩).event
          (S.dbar ⟨1, by decide⟩) := h
      rw [show u (S.toPODTRSystem.factualD ⟨1, by decide⟩ ω) = (1 : ℝ) from
            Set.indicator_of_mem h1 _,
          show I1 ω = (1 : ℝ) from by
            simpa [I1] using
              (S.toPODTRSystem.dVar ⟨1, by decide⟩).indicator_apply_eq_one h2]
    · have h1 : S.toPODTRSystem.factualD ⟨1, by decide⟩ ω ∉
          ({S.dbar ⟨1, by decide⟩} : Set δ) := h
      have h2 : ω ∉ (S.toPODTRSystem.dVar ⟨1, by decide⟩).event
          (S.dbar ⟨1, by decide⟩) := h
      rw [show u (S.toPODTRSystem.factualD ⟨1, by decide⟩ ω) = (0 : ℝ) from
            Set.indicator_of_notMem h1 _,
          show I1 ω = (0 : ℝ) from by
            simpa [I1] using
              (S.toPODTRSystem.dVar ⟨1, by decide⟩).indicator_apply_eq_zero h2]
  have hfact :
      P.μ[fun ω => u (S.toPODTRSystem.factualD ⟨1, by decide⟩ ω) * Y ω
          | B1.sigma]
        =ᵐ[P.μ]
          P.μ[fun ω => u (S.toPODTRSystem.factualD ⟨1, by decide⟩ ω)
            | B1.sigma] * P.μ[Y | B1.sigma] :=
    condExp_mul_of_condIndep (μ := P.μ)
      (m := B1.sigma) B1.sigma_le
      (f := S.toPODTRSystem.factualD ⟨1, by decide⟩) (g := Y)
      (S.toPODTRSystem.measurable_factualD ⟨1, by decide⟩)
      (by simpa [Y] using S.toPODTRSystem.measurable_Y_of S.dbar) hCI
      (u := u) (v := id) hu_meas measurable_id
      (by rw [hu_eq]; exact hI1_int) hY_int
      (by
        have heq :
            (fun ω => u (S.toPODTRSystem.factualD ⟨1, by decide⟩ ω) * Y ω)
              = (fun ω => I1 ω * Y ω) := by
          funext ω
          rw [congr_fun hu_eq ω]
        change Integrable
          (fun ω => u (S.toPODTRSystem.factualD ⟨1, by decide⟩ ω) * Y ω) P.μ
        rw [heq]
        exact hI1Y_int)
  have hExch :
      B1.condExpGiven (fun ω => I1 ω * Y ω) P.μ
        =ᵐ[P.μ]
          (fun ω => B1.condExpGiven I1 P.μ ω *
            B1.condExpGiven Y P.μ ω) := by
    unfold POCFBundle.condExpGiven
    have hprod_rw :
        (fun ω => u (S.toPODTRSystem.factualD ⟨1, by decide⟩ ω) * Y ω)
          = (fun ω => I1 ω * Y ω) := by
      funext ω
      rw [congr_fun hu_eq ω]
    rw [hprod_rw, hu_eq] at hfact
    filter_upwards [hfact] with ω hω
    simpa [Pi.mul_apply] using hω
  have hpull_I0Y :=
    B1.condExpGiven_mul_of_stronglyMeasurable_left
      (f := I0) (g := fun ω => I1 ω * Y ω)
      hI0_sm_B1 hI0I1Y_int hI1Y_int
  have hCE_fact :
      B1.condExpGiven (fun ω => I0 ω * (I1 ω * Yf ω)) P.μ
        =ᵐ[P.μ] (fun ω => I0 ω *
          (S.e₁_val
            (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
             S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
             S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) * M1 ω)) := by
    refine hCE_fact_to_cf.trans ?_
    have hI0_eq_indD : I0 = S.toPODTRSystem.indD S.dbar 1 := by
      funext ω
      have hsplit := congr_fun
        (S.toPODTRSystem.indD_factor_split S.dbar 0 (by decide)) ω
      simp [I0, PODTRSystem.indD] at hsplit ⊢
    filter_upwards [hpull_I0Y, hExch, S.e₁_compat,
      (by simpa [I0, B1, M1, Y] using S.indD_mul_μ₁_val_comp_eq hA)] with
      ω hp hE he hμ
    have hp' :
        B1.condExpGiven (fun ω => I0 ω * (I1 ω * Y ω)) P.μ ω =
          I0 ω * B1.condExpGiven (fun ω => I1 ω * Y ω) P.μ ω := by
      simpa [Pi.mul_apply, mul_assoc] using hp
    have hμ_local : I0 ω * M1 ω = I0 ω * B1.condExpGiven Y P.μ ω := by
      simpa [I0, B1, M1, Y, hI0_eq_indD] using hμ
    rw [hp', hE, he]
    calc
      I0 ω * (S.e₁_val
          (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
           S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
           S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) *
          B1.condExpGiven Y P.μ ω)
          =
            S.e₁_val
              (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
               S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
               S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) *
              (I0 ω * B1.condExpGiven Y P.μ ω) := by ring
      _ =
            S.e₁_val
              (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
               S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
               S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) *
              (I0 ω * M1 ω) := by rw [← hμ_local]
      _ =
          I0 ω * (S.e₁_val
            (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
             S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
             S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) * M1 ω) := by ring
  have hpull_I0M1 :=
    B1.condExpGiven_mul_of_stronglyMeasurable_left
      (f := fun ω => I0 ω * M1 ω) (g := I1)
      hI0M1_sm_B1
      (by
        exact hI0I1M1_int.congr
          (Filter.Eventually.of_forall (fun ω => by
            change I0 ω * (I1 ω * M1 ω) = (I0 ω * M1 ω) * I1 ω
            ring)))
      hI1_int
  have hCE_M1 :
      B1.condExpGiven (fun ω => I0 ω * (I1 ω * M1 ω)) P.μ
        =ᵐ[P.μ] (fun ω => I0 ω *
          (S.e₁_val
            (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
             S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
             S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) * M1 ω)) := by
    filter_upwards [hpull_I0M1, S.e₁_compat] with ω hp he
    have hp' :
        B1.condExpGiven (fun ω => I0 ω * (I1 ω * M1 ω)) P.μ ω =
          (I0 ω * M1 ω) * B1.condExpGiven I1 P.μ ω := by
      have harg :
          ((fun ω => I0 ω * M1 ω) * I1)
            = (fun ω => I0 ω * (I1 ω * M1 ω)) := by
        funext ω
        change (I0 ω * M1 ω) * I1 ω = I0 ω * (I1 ω * M1 ω)
        ring
      rw [← harg]
      simpa [Pi.mul_apply] using hp
    rw [hp', he]
    ring
  rw [show (fun ω => (S.toPODTRSystem.dVar ⟨0, by decide⟩).indicator
            (S.dbar ⟨0, by decide⟩) ω *
          ((S.toPODTRSystem.dVar ⟨1, by decide⟩).indicator
            (S.dbar ⟨1, by decide⟩) ω *
          (S.toPODTRSystem.factualY ω -
            S.μ₁_val
              (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
               S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
               S.toPODTRSystem.factualS ⟨0, by decide⟩ ω))))
        = (fun ω => I0 ω * (I1 ω * (Yf ω - M1 ω))) by rfl]
  rw [hres_eq]
  refine hsub.trans ?_
  filter_upwards [hCE_fact, hCE_M1] with ω hfactω hMω
  rw [Pi.sub_apply, hfactω, hMω]
  ring

/-! ## Estimand lift through `factualZ`

Mirrors `theta_zero_factualX_integral` in the ATE template: writes `θ₀`
as an integral against `P.μ` of a function pulled back through
`factualS 0`. -/

/-- The DTR estimand `θ₀ = E[Y(dbar)]` lifts to an integral against `P.μ`:
under DTR backdoor assumptions, `θ₀ = ∫ ω, μ₀_val(factualS 0 ω) ∂P.μ`,
since `μ₀_val ∘ factualS 0` is the σ(historyBundle 0)-conditional
expectation of `Y_of dbar` and `P.μ` is a probability measure. -/
lemma theta_zero_factualS₀_integral
    (S : DTREstimationSystem P δ γ)
    (hA : S.toPODTRSystem.Assumptions) :
    S.θ₀ = ∫ ω, S.μ₀_val (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) ∂P.μ := by
  unfold DTREstimationSystem.θ₀ Causalean.PO.PODTRSystem.dtrEffect
  calc
    ∫ ω, S.toPODTRSystem.Y_of S.dbar ω ∂P.μ
        = ∫ ω, (S.toPODTRSystem.historyBundle 0 (by decide)).condExpGiven
            (S.toPODTRSystem.Y_of S.dbar) P.μ ω ∂P.μ := by
          exact (MeasureTheory.integral_condExp
            (S.toPODTRSystem.historyBundle 0 (by decide)).sigma_le).symm
    _ = ∫ ω, S.μ₀_val (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) ∂P.μ :=
          MeasureTheory.integral_congr_ae (S.μ₀_compat hA)

/-! ## Headline lemma -/

/-- `∫ ω, ψ_seqDR(factualZ ω) ∂P.μ = 0` — the unmapped form of the
mean-zero result, used to prove the headline `seqDR_mean_zero` after
pushforward through `factualZ`. -/
private lemma seqDR_factualZ_integral_zero (S : DTREstimationSystem P δ γ)
    {ε : ℝ}
    (h_overlap : S.StrictOverlap ε)
    (hA : S.toPODTRSystem.Assumptions)
    (h_y2 : Integrable (fun ω => (S.toPODTRSystem.factualY ω) ^ 2) P.μ) :
    (∫ ω, S.ψ_seqDR (S.factualZ ω) ∂P.μ) = 0 := by
  let B0 := S.toPODTRSystem.historyBundle 0 (by decide)
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
  let M0 : P.Ω → ℝ :=
    fun ω => S.μ₀_val (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω)
  let M1 : P.Ω → ℝ := fun ω => S.μ₁_val (H1 ω)
  let R0 : P.Ω → ℝ := fun ω => I0 ω * (M1 ω - M0 ω)
  let R1 : P.Ω → ℝ :=
    fun ω => I0 ω * (I1 ω * (S.toPODTRSystem.factualY ω - M1 ω))
  let W0 : P.Ω → ℝ := fun ω =>
    1 / S.e₀_val (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω)
  let W1 : P.Ω → ℝ := fun ω =>
    1 / (S.e₀_val (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) *
      S.e₁_val (H1 ω))
  have hY_int : Integrable (S.toPODTRSystem.Y_of S.dbar) P.μ := hA.integrable_Y S.dbar
  have hM0_int : Integrable M0 P.μ := by
    exact (B0.integrable_condExpGiven (S.toPODTRSystem.Y_of S.dbar)).congr
      (by simpa [B0, M0] using S.μ₀_compat hA)
  have hM1_int : Integrable M1 P.μ := by
    have hM1_L2 : MemLp M1 2 P.μ := by
      simpa [H1, M1] using (S.stageOneReg_memLp h_overlap h_y2).ae_eq
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
  have hR0_int : Integrable R0 P.μ := by
    have hsub := hI0M1_int.sub hI0M0_int
    refine hsub.congr ?_
    exact Filter.Eventually.of_forall (fun ω => by
      simp [R0]
      ring)
  have hI1Yf_int : Integrable
      (fun ω => I1 ω * S.toPODTRSystem.factualY ω) P.μ := by
    have h := (S.toPODTRSystem.dVar ⟨1, by decide⟩).integrable_mul_indicator
      (S.dbar ⟨1, by decide⟩) hA.integrable_factualY
      S.toPODTRSystem.measurable_factualY
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
  have hR1_int : Integrable R1 P.μ := by
    have h := (S.toPODTRSystem.dVar ⟨0, by decide⟩).integrable_mul_indicator
      (S.dbar ⟨0, by decide⟩) hI1_res_int hI1_res_meas
    exact h.congr (Filter.Eventually.of_forall (fun ω => by
      change (I1 ω * (S.toPODTRSystem.factualY ω - M1 ω)) * I0 ω =
        R1 ω
      simp [R1]
      ring))
  have hW0_sm : StronglyMeasurable[B0.sigma] W0 := by
    have hs0 : Measurable[B0.sigma] (S.toPODTRSystem.factualS ⟨0, by decide⟩) :=
      S.toPODTRSystem.measurable_factualS_sigma_history 0 (by decide)
        ⟨0, by decide⟩ (by decide)
    exact (measurable_const.div (S.e₀_meas.comp hs0)).stronglyMeasurable
  have hW1_sm : StronglyMeasurable[B1.sigma] W1 := by
    have hs1 : Measurable[B1.sigma] (S.toPODTRSystem.factualS ⟨1, by decide⟩) :=
      S.toPODTRSystem.measurable_factualS_sigma_history 1 (by decide)
        ⟨1, by decide⟩ (by decide)
    have hd0 : Measurable[B1.sigma] (S.toPODTRSystem.factualD ⟨0, by decide⟩) :=
      S.toPODTRSystem.measurable_factualD_sigma_history 1 (by decide)
        ⟨0, by decide⟩ (by decide)
    have hs0 : Measurable[B1.sigma] (S.toPODTRSystem.factualS ⟨0, by decide⟩) :=
      S.toPODTRSystem.measurable_factualS_sigma_history 1 (by decide)
        ⟨0, by decide⟩ (by decide)
    have he0 : Measurable[B1.sigma]
        (fun ω => S.e₀_val (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω)) :=
      S.e₀_meas.comp hs0
    have he1 : Measurable[B1.sigma] (fun ω => S.e₁_val (H1 ω)) :=
      S.e₁_meas.comp (hs1.prod (hd0.prod hs0))
    exact (measurable_const.div (he0.mul he1)).stronglyMeasurable
  have hW0_bound : ∀ᵐ ω ∂P.μ, ‖W0 ω‖ ≤ ε⁻¹ := by
    filter_upwards [h_overlap.2.2, S.e₀_compat] with ω hover hcomp
    have he : ε ≤ S.e₀_val (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) := by
      rw [← hcomp]
      exact hover.1.1
    have hpos : 0 < S.e₀_val (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) :=
      S.e₀_pos _
    have hle : (S.e₀_val (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω))⁻¹ ≤ ε⁻¹ :=
      (inv_le_inv₀ hpos h_overlap.1).2 he
    change ‖1 / S.e₀_val (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω)‖ ≤ ε⁻¹
    rw [norm_div, norm_one, Real.norm_eq_abs, abs_of_pos hpos]
    simpa [one_div] using hle
  have hW1_bound : ∀ᵐ ω ∂P.μ, ‖W1 ω‖ ≤ (ε * ε)⁻¹ := by
    filter_upwards [h_overlap.2.2, S.e₀_compat, S.e₁_compat] with ω hover he0c he1c
    have he0 : ε ≤ S.e₀_val (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) := by
      rw [← he0c]
      exact hover.1.1
    have he1 : ε ≤ S.e₁_val (H1 ω) := by
      rw [← he1c]
      simpa [H1] using hover.2.1
    have hpos0 : 0 < S.e₀_val (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) :=
      S.e₀_pos _
    have hpos1 : 0 < S.e₁_val (H1 ω) := S.e₁_pos _
    have hprod_le :
        ε * ε ≤ S.e₀_val (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) *
          S.e₁_val (H1 ω) :=
      mul_le_mul he0 he1 h_overlap.1.le hpos0.le
    have hle :
        (S.e₀_val (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) *
          S.e₁_val (H1 ω))⁻¹ ≤ (ε * ε)⁻¹ :=
      (inv_le_inv₀ (mul_pos hpos0 hpos1)
        (mul_pos h_overlap.1 h_overlap.1)).2 hprod_le
    change ‖1 / (S.e₀_val (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) *
      S.e₁_val (H1 ω))‖ ≤ (ε * ε)⁻¹
    rw [norm_div, norm_one, Real.norm_eq_abs, abs_of_pos (mul_pos hpos0 hpos1)]
    simpa [one_div] using hle
  have hW0R0_int : Integrable (fun ω => W0 ω * R0 ω) P.μ :=
    hR0_int.bdd_mul (hW0_sm.mono B0.sigma_le).aestronglyMeasurable hW0_bound
  have hW1R1_int : Integrable (fun ω => W1 ω * R1 ω) P.μ :=
    hR1_int.bdd_mul (hW1_sm.mono B1.sigma_le).aestronglyMeasurable hW1_bound
  have hstage0_zero : ∫ ω, W0 ω * R0 ω ∂P.μ = 0 := by
    have hpull := B0.condExpGiven_mul_of_stronglyMeasurable_left
      (f := W0) (g := R0) hW0_sm hW0R0_int hR0_int
    have hzero : B0.condExpGiven R0 P.μ =ᵐ[P.μ] (fun _ => (0 : ℝ)) := by
      simpa [B0, R0, I0, M0, M1, H1] using
        cond_exp_residual_zero_stage0 S h_overlap hA h_y2
    have hce : B0.condExpGiven (fun ω => W0 ω * R0 ω) P.μ
        =ᵐ[P.μ] (fun _ => (0 : ℝ)) := by
      refine hpull.trans ?_
      filter_upwards [hzero] with ω hω
      rw [Pi.mul_apply, hω, mul_zero]
    calc
      ∫ ω, W0 ω * R0 ω ∂P.μ
          = ∫ ω, B0.condExpGiven (fun ω => W0 ω * R0 ω) P.μ ω ∂P.μ := by
            exact (MeasureTheory.integral_condExp B0.sigma_le).symm
      _ = ∫ _, (0 : ℝ) ∂P.μ := MeasureTheory.integral_congr_ae hce
      _ = 0 := MeasureTheory.integral_zero _ _
  have hstage1_zero : ∫ ω, W1 ω * R1 ω ∂P.μ = 0 := by
    have hpull := B1.condExpGiven_mul_of_stronglyMeasurable_left
      (f := W1) (g := R1) hW1_sm hW1R1_int hR1_int
    have hzero : B1.condExpGiven R1 P.μ =ᵐ[P.μ] (fun _ => (0 : ℝ)) := by
      simpa [B1, R1, I0, I1, M1, H1] using
        cond_exp_residual_zero_stage1 S h_overlap hA h_y2
    have hce : B1.condExpGiven (fun ω => W1 ω * R1 ω) P.μ
        =ᵐ[P.μ] (fun _ => (0 : ℝ)) := by
      refine hpull.trans ?_
      filter_upwards [hzero] with ω hω
      rw [Pi.mul_apply, hω, mul_zero]
    calc
      ∫ ω, W1 ω * R1 ω ∂P.μ
          = ∫ ω, B1.condExpGiven (fun ω => W1 ω * R1 ω) P.μ ω ∂P.μ := by
            exact (MeasureTheory.integral_condExp B1.sigma_le).symm
      _ = ∫ _, (0 : ℝ) ∂P.μ := MeasureTheory.integral_congr_ae hce
      _ = 0 := MeasureTheory.integral_zero _ _
  have hθ : S.θ₀ = ∫ ω, M0 ω ∂P.μ := by
    simpa [M0] using theta_zero_factualS₀_integral S hA
  have hψ_eq :
      (fun ω => S.ψ_seqDR (S.factualZ ω))
        = fun ω => M0 ω + W0 ω * R0 ω + W1 ω * R1 ω - S.θ₀ := by
    funext ω
    by_cases hD0 : S.toPODTRSystem.factualD ⟨0, by decide⟩ ω =
        S.dbar ⟨0, by decide⟩
    · by_cases hD1 : S.toPODTRSystem.factualD ⟨1, by decide⟩ ω =
          S.dbar ⟨1, by decide⟩
      · have hI0 : I0 ω = 1 := by
          simpa [I0] using
            (S.toPODTRSystem.dVar ⟨0, by decide⟩).indicator_apply_eq_one hD0
        have hI1 : I1 ω = 1 := by
          simpa [I1] using
            (S.toPODTRSystem.dVar ⟨1, by decide⟩).indicator_apply_eq_one hD1
        have hI0raw :
            (S.toPODTRSystem.dVar ⟨0, by decide⟩).indicator
              (S.dbar ⟨0, by decide⟩) ω = 1 := by
          simpa [I0] using hI0
        have hI1raw :
            (S.toPODTRSystem.dVar ⟨1, by decide⟩).indicator
              (S.dbar ⟨1, by decide⟩) ω = 1 := by
          simpa [I1] using hI1
        have hD0n : S.toPODTRSystem.factualD 0 ω = S.dbar 0 := by simpa using hD0
        have hD1n : S.toPODTRSystem.factualD 1 ω = S.dbar 1 := by simpa using hD1
        have hI0rawn : (S.toPODTRSystem.dVar 0).indicator (S.dbar 0) ω = 1 := by
          simpa using hI0raw
        have hI1rawn : (S.toPODTRSystem.dVar 1).indicator (S.dbar 1) ω = 1 := by
          simpa using hI1raw
        simp [DTREstimationSystem.ψ_seqDR, DTREstimationSystem.seqDRMoment,
          Causalean.Estimation.DTR.seqDRMoment, DTREstimationSystem.factualZ,
          DTREstimationSystem.η₀, projS₀, projD₀, projS₁, projD₁, projY, histH₁,
          indEq, M0, M1, H1, R0, R1, W0, W1, I0, I1,
          hD0n, hD1n, hI0rawn, hI1rawn, one_div]
      · have hI0 : I0 ω = 1 := by
          simpa [I0] using
            (S.toPODTRSystem.dVar ⟨0, by decide⟩).indicator_apply_eq_one hD0
        have hI1 : I1 ω = 0 := by
          simpa [I1] using
            (S.toPODTRSystem.dVar ⟨1, by decide⟩).indicator_apply_eq_zero hD1
        have hI0raw :
            (S.toPODTRSystem.dVar ⟨0, by decide⟩).indicator
              (S.dbar ⟨0, by decide⟩) ω = 1 := by
          simpa [I0] using hI0
        have hI1raw :
            (S.toPODTRSystem.dVar ⟨1, by decide⟩).indicator
              (S.dbar ⟨1, by decide⟩) ω = 0 := by
          simpa [I1] using hI1
        have hD0n : S.toPODTRSystem.factualD 0 ω = S.dbar 0 := by simpa using hD0
        have hD1n : ¬S.toPODTRSystem.factualD 1 ω = S.dbar 1 := by simpa using hD1
        have hI0rawn : (S.toPODTRSystem.dVar 0).indicator (S.dbar 0) ω = 1 := by
          simpa using hI0raw
        have hI1rawn : (S.toPODTRSystem.dVar 1).indicator (S.dbar 1) ω = 0 := by
          simpa using hI1raw
        simp [DTREstimationSystem.ψ_seqDR, DTREstimationSystem.seqDRMoment,
          Causalean.Estimation.DTR.seqDRMoment, DTREstimationSystem.factualZ,
          DTREstimationSystem.η₀, projS₀, projD₀, projS₁, projD₁, projY, histH₁,
          indEq, M0, M1, H1, R0, R1, W0, W1, I0, I1,
          hD0n, hD1n, hI0rawn, hI1rawn, one_div]
    · have hI0 : I0 ω = 0 := by
        simpa [I0] using
          (S.toPODTRSystem.dVar ⟨0, by decide⟩).indicator_apply_eq_zero hD0
      have hI0raw :
          (S.toPODTRSystem.dVar ⟨0, by decide⟩).indicator
            (S.dbar ⟨0, by decide⟩) ω = 0 := by
        simpa [I0] using hI0
      have hD0n : ¬S.toPODTRSystem.factualD 0 ω = S.dbar 0 := by simpa using hD0
      have hI0rawn : (S.toPODTRSystem.dVar 0).indicator (S.dbar 0) ω = 0 := by
        simpa using hI0raw
      simp [DTREstimationSystem.ψ_seqDR, DTREstimationSystem.seqDRMoment,
        Causalean.Estimation.DTR.seqDRMoment, DTREstimationSystem.factualZ,
        DTREstimationSystem.η₀, projS₀, projD₀, projS₁, projD₁, projY, histH₁,
        indEq, hD0n, M0, M1, H1, R0, R1, W0, W1, I0, hI0rawn, one_div]
  have hconst_int : Integrable (fun _ : P.Ω => S.θ₀) P.μ := integrable_const _
  have hsum_int : Integrable
      (fun ω => M0 ω + W0 ω * R0 ω + W1 ω * R1 ω) P.μ :=
    (hM0_int.add hW0R0_int).add hW1R1_int
  calc
    ∫ ω, S.ψ_seqDR (S.factualZ ω) ∂P.μ
        = ∫ ω, M0 ω + W0 ω * R0 ω + W1 ω * R1 ω - S.θ₀ ∂P.μ := by
          exact MeasureTheory.integral_congr_ae
            (Filter.Eventually.of_forall (fun ω => congr_fun hψ_eq ω))
    _ = (∫ ω, M0 ω + W0 ω * R0 ω + W1 ω * R1 ω ∂P.μ)
          - ∫ _ : P.Ω, S.θ₀ ∂P.μ := by
        exact MeasureTheory.integral_sub hsum_int hconst_int
    _ = ((∫ ω, M0 ω + W0 ω * R0 ω ∂P.μ) + ∫ ω, W1 ω * R1 ω ∂P.μ)
          - ∫ _ : P.Ω, S.θ₀ ∂P.μ := by
        have hadd := MeasureTheory.integral_add (μ := P.μ)
          (f := fun ω => M0 ω + W0 ω * R0 ω)
          (g := fun ω => W1 ω * R1 ω)
          (hM0_int.add hW0R0_int) hW1R1_int
        exact congrArg (fun x => x - ∫ _ : P.Ω, S.θ₀ ∂P.μ) hadd
    _ = (((∫ ω, M0 ω ∂P.μ) + ∫ ω, W0 ω * R0 ω ∂P.μ)
          + ∫ ω, W1 ω * R1 ω ∂P.μ) - ∫ _ : P.Ω, S.θ₀ ∂P.μ := by
        have hadd := MeasureTheory.integral_add (μ := P.μ)
          (f := M0) (g := fun ω => W0 ω * R0 ω) hM0_int hW0R0_int
        exact congrArg (fun x => (x + ∫ ω, W1 ω * R1 ω ∂P.μ)
          - ∫ _ : P.Ω, S.θ₀ ∂P.μ) hadd
    _ = 0 := by
        rw [hstage0_zero, hstage1_zero, ← hθ]
        simp

/-- **Mean zero of `ψ_seqDR`** — under the DTR backdoor assumptions,
two-stage strict overlap, and a finite second moment for the observed factual
outcome, the sequential doubly robust influence function has expectation zero
under the observed data law.

Formally, the sequential DR score `ψ_seqDR` integrates to zero against the
pushforward law `P_Z` of `(S₀, D₀, S₁, D₁, Y)`.  No square-integrability
assumption is imposed on all counterfactual outcomes; the proof uses the DTR
assumptions for counterfactual integrability and the factual second moment for
the observable stagewise regressions. -/
theorem seqDR_mean_zero (S : DTREstimationSystem P δ γ) {ε : ℝ}
    (h_overlap : S.StrictOverlap ε)
    (hA : S.toPODTRSystem.Assumptions)
    (h_y2 : Integrable (fun ω => (S.toPODTRSystem.factualY ω) ^ 2) P.μ) :
    (∫ z, S.ψ_seqDR z ∂(S.P_Z)) = 0 := by
  rw [DTREstimationSystem.P_Z]
  rw [MeasureTheory.integral_map S.measurable_factualZ.aemeasurable
    (S.measurable_ψ_seqDR).aestronglyMeasurable]
  exact seqDR_factualZ_integral_zero S h_overlap hA h_y2

end DTREstimationSystem

end DTR
end Estimation
end Causalean
