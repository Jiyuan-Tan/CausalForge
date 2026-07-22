/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# DTR estimation system: structure, data law, value-space DTR estimand (n = 2)

The `DTREstimationSystem` extends `PODTRSystem P 2 δ γ` with the value-space
factorization of the σ(historyBundle k)-measurable representatives
(Doob–Dynkin lift) at each stage.  This file collects:

* the structure itself with the **observable** compatibility fields
  `μ₀_reg_compat` (→ `innerReg dbar (n-1)`), `μ₁_reg_compat` (→ the stage-1 regression
  `stageOneReg = E[Y|hist₁,D₁=dbar₁]`), `e₀_compat`, `e₁_compat`; plus the derived
  counterfactual lemma `μ₀_compat` and the `·indD` identity `stageOneReg_indD_eq`;
* the strict-overlap predicate at both stages;
* the marginals `P_H₀`, `P_H₁`, the factual data tuple `factualZ`,
  the joint law `P_Z`;
* the value-space estimand `θ₀` and its agreement with the PO-level
  `dtrEffect` at the chosen target regime `dbar`.

Mirrors the structure of `Estimation/ATE/Setup.lean` stage-by-stage.

Bundle ordering convention.  For `n = 2`,
`historyBundle 1 = cons S₁ (cons D₀ (cons S₀ nil))`, so its `jointValue`
indexes a dependent function over `Fin 3` with components
`(S₁ : γ 1, D₀ : δ, S₀ : γ 0)`.  Accordingly the value-space inner
regression / propensity take domain `γ 1 × δ × γ 0` (cons order:
outer → inner).
-/

import Causalean.PO.ID.Exact.DTR.Main
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Two-Stage DTR Estimation Setup

This file defines the data layer for two-stage dynamic treatment regime estimation:
the estimation-system structure, observable regression targets, stagewise overlap,
history marginals, the observed data law, and the value-space target estimand.
The target is the fixed-regime mean, and the observable compatibility fields are
the value-space representatives used by the sequential AIPW score.

This module is specialized to horizon two, with a discrete treatment space so that
target-regime equality indicators are measurable.
-/

namespace Causalean
namespace Estimation
namespace DTR

open MeasureTheory ProbabilityTheory Filter Topology Causalean.PO

/-! ## DTR estimation system (n = 2)

A `DTREstimationSystem` extends `PODTRSystem P 2 δ γ` with value-space
representatives of the stagewise outcome regressions and propensities at the
target regime `dbar`.  The σ-compat fields encode the Doob–Dynkin lift
through the factual history coordinates. -/

/-- This structure adds fixed-regime nuisance representatives to a two-stage potential-outcome DTR system.

It stores the target regime, value-space representatives for the stage-0 and stage-1 outcome
regressions and propensities, pointwise propensity bounds in the open unit interval, and
observable compatibility fields for the stagewise regressions and propensities.

Field summary (all at the fixed target `dbar`):

* `dbar`           — the target regime; stored at the system level.
* `μ₀_val s₀`      — value-space outer regression `μ₀(s₀)`.
* `e₀_val s₀`      — value-space stage-0 propensity `e₀(s₀) ∈ (0, 1)`.
* `μ₁_val (s₁,d₀,s₀)` — value-space inner regression `μ₁(s₁,d₀,s₀)`.
* `e₁_val (s₁,d₀,s₀)` — value-space stage-1 propensity `e₁(...) ∈ (0, 1)`.
* `μ₀_reg_compat`  — the observable nested regression `innerReg dbar 1`
                       `=ᵐ μ₀_val ∘ factualS 0`.
* `e₀_compat`      — `μ[1_{D₀=dbar 0} | σ(historyBundle 0)] =ᵐ e₀_val ∘ factualS 0`.
* `μ₁_reg_compat`  — the observable last-stage regression
                       `E[Y | history₁, D₁ = dbar₁]`
                       `=ᵐ μ₁_val ∘ (factualS 1, factualD 0, factualS 0)`.
* `e₁_compat`      — `μ[1_{D₁=dbar 1} | σ(historyBundle 1)]`
                       `=ᵐ e₁_val ∘ (factualS 1, factualD 0, factualS 0)`. -/
structure DTREstimationSystem (P : POSystem) (δ : Type) (γ : Fin 2 → Type)
    [MeasurableSpace δ] [MeasurableSingletonClass δ]
    [∀ k, MeasurableSpace (γ k)]
    [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
    extends PODTRSystem P 2 δ γ where
  /-- Target regime stored at the system level (mirrors the design rationale
  in the brief: regime is multi-stage, so we fix it). -/
  dbar : Fin 2 → δ
  /-- Value-space stage-0 outcome regression `μ₀ : γ 0 → ℝ`. -/
  μ₀_val : γ 0 → ℝ
  μ₀_meas : Measurable μ₀_val
  /-- Value-space stage-0 propensity `e₀ : γ 0 → ℝ`, in `(0, 1)`. -/
  e₀_val : γ 0 → ℝ
  e₀_meas : Measurable e₀_val
  e₀_pos : ∀ s, 0 < e₀_val s
  e₀_lt_one : ∀ s, e₀_val s < 1
  /-- Value-space stage-1 outcome regression `μ₁ : γ 1 × δ × γ 0 → ℝ`. -/
  μ₁_val : γ 1 × δ × γ 0 → ℝ
  μ₁_meas : Measurable μ₁_val
  /-- Value-space stage-1 propensity `e₁ : γ 1 × δ × γ 0 → ℝ`, in `(0, 1)`. -/
  e₁_val : γ 1 × δ × γ 0 → ℝ
  e₁_meas : Measurable e₁_val
  e₁_pos : ∀ h, 0 < e₁_val h
  e₁_lt_one : ∀ h, e₁_val h < 1
  /-- The stage-0 (outermost) regression `μ₀_val` represents the **observable**
  nested regression `innerReg dbar (n-1)` (the iterated g-computation regression on
  the factual data), with NO counterfactual: `μ₀_val (factualS 0 ·) =ᵐ innerReg dbar 1`.
  The counterfactual reading `μ[Y(dbar)|σ(historyBundle 0)] =ᵐ μ₀_val ∘ factualS 0` is
  NOT assumed here — it is the *derived* lemma `μ₀_compat` below, which requires
  `Assumptions` via the sequential back-door identity `cdtr_backdoor`. -/
  μ₀_reg_compat :
    (fun ω => μ₀_val (toPODTRSystem.factualS ⟨0, by decide⟩ ω))
      =ᵐ[P.μ] toPODTRSystem.innerReg dbar 1
  /-- Stage-0 propensity factors through `factualS 0`:
  `μ[1_{D₀ = dbar 0} | σ(historyBundle 0)] =ᵐ e₀_val (factualS 0 ·)`. -/
  e₀_compat :
    (toPODTRSystem.historyBundle 0 (by decide)).condExpGiven
        ((toPODTRSystem.dVar ⟨0, by decide⟩).indicator (dbar ⟨0, by decide⟩)) P.μ
      =ᵐ[P.μ] (fun ω => e₀_val (toPODTRSystem.factualS ⟨0, by decide⟩ ω))
  /-- The stage-1 regression `μ₁_val` represents the **observable** last-stage
  regression `f₂ = E[Y | hist₁, D₁=dbar₁]`, written as the ratio
  `condExpRatio_{hist₁}(Y·1_{D₁=dbar₁}, 1_{D₁=dbar₁})` (the paper's nested-regression
  base case), with NO counterfactual:
  `μ₁_val (factualS 1, factualD 0, factualS 0) =ᵐ f₂`. This is the ML/regression
  target. The counterfactual reading `μ[Y(dbar) | σ(hist₁)] =ᵐ μ₁_val ∘ …` holds only
  on the regime path `{D₀=dbar₀}` (the `·indD` form `stageOneReg_indD_eq`), NOT
  globally — which is exactly why `μ₁` is the regression `f₂`, not the full-regime
  intermediate counterfactual. -/
  μ₁_reg_compat :
    (fun ω => μ₁_val
        (toPODTRSystem.factualS ⟨1, by decide⟩ ω,
         toPODTRSystem.factualD ⟨0, by decide⟩ ω,
         toPODTRSystem.factualS ⟨0, by decide⟩ ω))
      =ᵐ[P.μ]
    (toPODTRSystem.historyBundle 1 (by decide)).condExpRatio
        (fun ω => toPODTRSystem.factualY ω *
          (toPODTRSystem.dVar ⟨1, by decide⟩).indicator (dbar ⟨1, by decide⟩) ω)
        ((toPODTRSystem.dVar ⟨1, by decide⟩).indicator (dbar ⟨1, by decide⟩)) P.μ
  /-- Stage-1 propensity factors through `(factualS 1, factualD 0, factualS 0)`:
  `μ[1_{D₁ = dbar 1} | σ(historyBundle 1)] =ᵐ e₁_val (factualS 1, factualD 0, factualS 0)`. -/
  e₁_compat :
    (toPODTRSystem.historyBundle 1 (by decide)).condExpGiven
        ((toPODTRSystem.dVar ⟨1, by decide⟩).indicator (dbar ⟨1, by decide⟩)) P.μ
      =ᵐ[P.μ] (fun ω => e₁_val
        (toPODTRSystem.factualS ⟨1, by decide⟩ ω,
         toPODTRSystem.factualD ⟨0, by decide⟩ ω,
         toPODTRSystem.factualS ⟨0, by decide⟩ ω))

namespace DTREstimationSystem

variable {P : POSystem} {δ : Type} {γ : Fin 2 → Type}
  [MeasurableSpace δ] [MeasurableSingletonClass δ]
  [∀ k, MeasurableSpace (γ k)]
  [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]

/-- The stage-0 value-space regression equals the counterfactual stage-0 regression under identification.

This is derived from the observable regression compatibility and the sequential backdoor identity,
rather than stored as a field of the estimation system. -/
lemma μ₀_compat (S : DTREstimationSystem P δ γ)
    (hA : S.toPODTRSystem.Assumptions) :
    (S.toPODTRSystem.historyBundle 0 (by decide)).condExpGiven
        (S.toPODTRSystem.Y_of S.dbar) P.μ
      =ᵐ[P.μ] (fun ω => S.μ₀_val (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω)) :=
  (S.toPODTRSystem.cdtr_backdoor hA S.dbar (by decide)).trans S.μ₀_reg_compat.symm

/-! ### Stage-1 observable regression `f₂` (target of `μ₁_val`) -/

/-- This is the observable stage-1 regression of the outcome within the target final treatment arm.

It is the nested-regression base case represented by the system's stage-1 value-space regression. -/
noncomputable def stageOneReg (S : DTREstimationSystem P δ γ) : P.Ω → ℝ :=
  (S.toPODTRSystem.historyBundle 1 (by decide)).condExpRatio
    (fun ω => S.toPODTRSystem.factualY ω *
      (S.toPODTRSystem.dVar ⟨1, by decide⟩).indicator (S.dbar ⟨1, by decide⟩) ω)
    ((S.toPODTRSystem.dVar ⟨1, by decide⟩).indicator (S.dbar ⟨1, by decide⟩)) P.μ

/-- The stage-1 value-space regression agrees almost everywhere with the observable stage-1 regression.

This is the system's stage-1 regression compatibility field restated using the `stageOneReg`
abbreviation. -/
lemma μ₁_val_comp_eq_stageOneReg (S : DTREstimationSystem P δ γ) :
    (fun ω => S.μ₁_val
        (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
         S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
         S.toPODTRSystem.factualS ⟨0, by decide⟩ ω))
      =ᵐ[P.μ] S.stageOneReg :=
  S.μ₁_reg_compat

/-- On the regime-consistent path, the observable stage-1 regression agrees with the counterfactual stage-1 regression.

This identification is the stage-1 foundation for the sequential AIPW mean-zero and score
arguments. -/
lemma stageOneReg_indD_eq (S : DTREstimationSystem P δ γ)
    (hA : S.toPODTRSystem.Assumptions) :
    (fun ω => S.stageOneReg ω * S.toPODTRSystem.indD S.dbar 1 ω)
      =ᵐ[P.μ]
    (fun ω => S.toPODTRSystem.indD S.dbar 1 ω *
      (S.toPODTRSystem.historyBundle 1 (by decide)).condExpGiven
        (S.toPODTRSystem.Y_of S.dbar) P.μ ω) := by
  let T := S.toPODTRSystem
  let kLast : Fin 2 := ⟨1, by decide⟩
  let I1 : P.Ω → ℝ := (T.dVar kLast).indicator (S.dbar kLast)
  let B := T.historyBundle 1 (by decide)
  have hFactor : T.indD S.dbar 2 = fun ω => T.indD S.dbar 1 ω * I1 ω := by
    simpa [T, I1, kLast] using T.indD_factor_split S.dbar 1 (by decide)
  have hYI_int : Integrable (fun ω => T.factualY ω * I1 ω) P.μ := by
    simpa [T, I1, kLast] using
      (T.dVar kLast).integrable_mul_indicator (S.dbar kLast)
        hA.integrable_factualY T.measurable_factualY
  have hYindD2_int :
      Integrable (fun ω => T.factualY ω * T.indD S.dbar 2 ω) P.μ := by
    refine hA.integrable_factualY.mono
      (T.measurable_factualY.mul (T.measurable_indD S.dbar 2)).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun ω => ?_)
    rcases T.indD_eq_zero_or_one S.dbar 2 ω with h0 | h1
    · simp [T, h0]
    · simp [T, h1]
  have hprodY_int :
      Integrable (T.indD S.dbar 1 * fun ω => T.factualY ω * I1 ω) P.μ := by
    have hfun :
        (T.indD S.dbar 1 * fun ω => T.factualY ω * I1 ω)
          = fun ω => T.factualY ω * T.indD S.dbar 2 ω := by
      funext ω
      change T.indD S.dbar 1 ω * (T.factualY ω * I1 ω)
        = T.factualY ω * T.indD S.dbar 2 ω
      rw [hFactor]
      ring
    rw [hfun]
    exact hYindD2_int
  have hI1_int : Integrable I1 P.μ := by
    simpa [T, I1, kLast] using (T.dVar kLast).integrable_indicator (S.dbar kLast)
  have hindD2_int : Integrable (T.indD S.dbar 2) P.μ :=
    T.indD_integrable S.dbar 2
  have hprodI_int :
      Integrable (T.indD S.dbar 1 * I1) P.μ := by
    have hfun : (T.indD S.dbar 1 * I1) = T.indD S.dbar 2 := by
      funext ω
      change T.indD S.dbar 1 ω * I1 ω = T.indD S.dbar 2 ω
      rw [hFactor]
    rw [hfun]
    exact hindD2_int
  have hindD1_sm : StronglyMeasurable[B.sigma] (T.indD S.dbar 1) := by
    simpa [T, B] using T.stronglyMeasurable_indD_sigma_history 1 (by decide) S.dbar 1
      (le_refl 1)
  have hNum_pull :
      B.condExpGiven (fun ω => T.factualY ω * T.indD S.dbar 2 ω) P.μ
        =ᵐ[P.μ]
      (fun ω => T.indD S.dbar 1 ω *
        B.condExpGiven (fun ω => T.factualY ω * I1 ω) P.μ ω) := by
    have hpull :=
      B.condExpGiven_mul_of_stronglyMeasurable_left
        (f := T.indD S.dbar 1) (g := fun ω => T.factualY ω * I1 ω)
        hindD1_sm hprodY_int hYI_int
    have harg :
        (fun ω => T.factualY ω * T.indD S.dbar 2 ω)
          = fun ω => T.indD S.dbar 1 ω * (T.factualY ω * I1 ω) := by
      funext ω
      rw [hFactor]
      ring
    rw [harg]
    filter_upwards [hpull] with ω hω
    simpa [Pi.mul_apply] using hω
  have hDen_pull :
      B.condExpGiven (T.indD S.dbar 2) P.μ
        =ᵐ[P.μ]
      (fun ω => T.indD S.dbar 1 ω * B.condExpGiven I1 P.μ ω) := by
    have hpull :=
      B.condExpGiven_mul_of_stronglyMeasurable_left
        (f := T.indD S.dbar 1) (g := I1) hindD1_sm hprodI_int hI1_int
    have harg : T.indD S.dbar 2 = T.indD S.dbar 1 * I1 := by
      funext ω
      rw [hFactor]
      rfl
    rw [harg]
    filter_upwards [hpull] with ω hω
    simpa [Pi.mul_apply] using hω
  have hbridge :
      (fun ω => S.stageOneReg ω * T.indD S.dbar 1 ω)
        =ᵐ[P.μ] (fun ω => T.innerReg S.dbar 0 ω * T.indD S.dbar 1 ω) := by
    have hover := hA.overlap S.dbar kLast
    filter_upwards [hNum_pull, hDen_pull, hover] with ω hN hD hov
    have hstage :
        S.stageOneReg ω =
          B.condExpGiven (fun ω => T.factualY ω * I1 ω) P.μ ω /
            B.condExpGiven I1 P.μ ω := by
      rfl
    have hinner :
        T.innerReg S.dbar 0 ω =
          B.condExpGiven (fun ω => T.factualY ω * T.indD S.dbar 2 ω) P.μ ω /
            B.condExpGiven (T.indD S.dbar 2) P.μ ω := by
      unfold PODTRSystem.innerReg
      simp only [Nat.ofNat_pos, ↓reduceDIte]
      rfl
    rw [hstage, hinner, hN, hD]
    rcases T.indD_eq_zero_or_one S.dbar 1 ω with h0 | h1
    · simp [h0]
    · have hne : B.condExpGiven I1 P.μ ω ≠ 0 := by
        intro hzero
        rw [hzero] at hov
        linarith
      rw [h1]
      field_simp [hne]
  have hbase := T.cdtr_base hA S.dbar (by decide : 0 < 2)
  exact hbridge.trans (by simpa [T, B] using hbase)

/-- Composed observable `μ₁_val`, multiplied by the partial regime indicator
`indD dbar 1`, agrees with the corresponding counterfactual conditional
expectation. This is the consumer-facing form of `stageOneReg_indD_eq`. -/
lemma μ₁_val_comp_mul_indD_eq (S : DTREstimationSystem P δ γ)
    (hA : S.toPODTRSystem.Assumptions) :
    (fun ω => S.μ₁_val
        (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
         S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
         S.toPODTRSystem.factualS ⟨0, by decide⟩ ω) *
        S.toPODTRSystem.indD S.dbar 1 ω)
      =ᵐ[P.μ]
    (fun ω => S.toPODTRSystem.indD S.dbar 1 ω *
      (S.toPODTRSystem.historyBundle 1 (by decide)).condExpGiven
        (S.toPODTRSystem.Y_of S.dbar) P.μ ω) := by
  filter_upwards [S.μ₁_val_comp_eq_stageOneReg, S.stageOneReg_indD_eq hA] with ω hμ hstage
  rw [hμ]
  exact hstage

/-- Same as `μ₁_val_comp_mul_indD_eq`, with the partial regime indicator written on
the left. -/
lemma indD_mul_μ₁_val_comp_eq (S : DTREstimationSystem P δ γ)
    (hA : S.toPODTRSystem.Assumptions) :
    (fun ω => S.toPODTRSystem.indD S.dbar 1 ω *
        S.μ₁_val
          (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
           S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
           S.toPODTRSystem.factualS ⟨0, by decide⟩ ω))
      =ᵐ[P.μ]
    (fun ω => S.toPODTRSystem.indD S.dbar 1 ω *
      (S.toPODTRSystem.historyBundle 1 (by decide)).condExpGiven
        (S.toPODTRSystem.Y_of S.dbar) P.μ ω) := by
  filter_upwards [S.μ₁_val_comp_mul_indD_eq hA] with ω hω
  simpa [mul_comm] using hω

/-! ### Strict overlap (both stages) -/

/-- This predicate requires both stagewise target-regime propensities to stay uniformly away from zero and one.

The overlap level is positive and at most one half, and the bounds hold almost surely. -/
def StrictOverlap (S : DTREstimationSystem P δ γ) (ε : ℝ) : Prop :=
  0 < ε ∧ ε ≤ 1 / 2 ∧
    (∀ᵐ ω ∂P.μ,
      (ε ≤ (S.toPODTRSystem.historyBundle 0 (by decide)).condExpGiven
          ((S.toPODTRSystem.dVar ⟨0, by decide⟩).indicator (S.dbar ⟨0, by decide⟩)) P.μ ω
        ∧ (S.toPODTRSystem.historyBundle 0 (by decide)).condExpGiven
          ((S.toPODTRSystem.dVar ⟨0, by decide⟩).indicator (S.dbar ⟨0, by decide⟩)) P.μ ω
            ≤ 1 - ε)
        ∧ (ε ≤ (S.toPODTRSystem.historyBundle 1 (by decide)).condExpGiven
            ((S.toPODTRSystem.dVar ⟨1, by decide⟩).indicator (S.dbar ⟨1, by decide⟩)) P.μ ω
          ∧ (S.toPODTRSystem.historyBundle 1 (by decide)).condExpGiven
              ((S.toPODTRSystem.dVar ⟨1, by decide⟩).indicator (S.dbar ⟨1, by decide⟩)) P.μ ω
                ≤ 1 - ε))

/-- The observable stage-1 regression is square-integrable under strict overlap and a factual second moment.

This supplies the L² input used by downstream DTR score and moment results. -/
lemma stageOneReg_memLp (S : DTREstimationSystem P δ γ) {ε : ℝ}
    (hov : S.StrictOverlap ε)
    (h_y2 : Integrable (fun ω => (S.toPODTRSystem.factualY ω) ^ 2) P.μ) :
    MemLp S.stageOneReg 2 P.μ := by
  let T := S.toPODTRSystem
  let kLast : Fin 2 := ⟨1, by decide⟩
  let I1 : P.Ω → ℝ := (T.dVar kLast).indicator (S.dbar kLast)
  let B := T.historyBundle 1 (by decide)
  have hε_pos : 0 < ε := hov.1
  have hY_L2 : MemLp T.factualY 2 P.μ :=
    (memLp_two_iff_integrable_sq T.measurable_factualY.aestronglyMeasurable).2 h_y2
  have hI1_meas : Measurable I1 := by
    simpa [T, I1, kLast] using (T.dVar kLast).measurable_indicator (S.dbar kLast)
  have hYI_L2 : MemLp (fun ω => T.factualY ω * I1 ω) 2 P.μ := by
    refine hY_L2.norm.mono'
      ((T.measurable_factualY.mul hI1_meas).aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall (fun ω => ?_)
    rcases (T.dVar kLast).indicator_eq_one_or_zero (S.dbar kLast) ω with h0 | h1
    · simp [I1, h0]
    · simp [I1, h1]
  have hNum_L2 : MemLp (B.condExpGiven (fun ω => T.factualY ω * I1 ω) P.μ) 2 P.μ := by
    simpa [POCFBundle.condExpGiven] using hYI_L2.condExp
  have hbound :
      ∀ᵐ ω ∂P.μ,
        ‖S.stageOneReg ω‖ ≤
          ε⁻¹ * ‖B.condExpGiven (fun ω => T.factualY ω * I1 ω) P.μ ω‖ := by
    filter_upwards [hov.2.2] with ω hover
    have hden_ge : ε ≤ B.condExpGiven I1 P.μ ω := by
      simpa [T, B, I1, kLast] using hover.2.1
    have hden_pos : 0 < B.condExpGiven I1 P.μ ω := lt_of_lt_of_le hε_pos hden_ge
    have hinv : (B.condExpGiven I1 P.μ ω)⁻¹ ≤ ε⁻¹ := by
      rw [inv_le_inv₀ hden_pos hε_pos]
      exact hden_ge
    unfold stageOneReg POCFBundle.condExpRatio
    simp only [T, B, I1, kLast]
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hden_pos]
    calc
      |B.condExpGiven (fun ω => T.factualY ω * I1 ω) P.μ ω| /
          B.condExpGiven I1 P.μ ω
          = (B.condExpGiven I1 P.μ ω)⁻¹ *
              |B.condExpGiven (fun ω => T.factualY ω * I1 ω) P.μ ω| := by ring
      _ ≤ ε⁻¹ * |B.condExpGiven (fun ω => T.factualY ω * I1 ω) P.μ ω| := by
        exact mul_le_mul_of_nonneg_right hinv (abs_nonneg _)
      _ = ε⁻¹ * ‖B.condExpGiven (fun ω => T.factualY ω * I1 ω) P.μ ω‖ := by
        rw [Real.norm_eq_abs]
  refine (hNum_L2.norm.const_mul ε⁻¹).mono'
    (B.stronglyMeasurable_condExpRatio
      (fun ω => T.factualY ω * I1 ω) I1).aestronglyMeasurable ?_
  simpa [DTREstimationSystem.stageOneReg, T, B, I1, kLast] using hbound

/-! ### Stage-history marginals and joint data law -/

/-- This is the marginal law of the stage-0 history. -/
noncomputable def P_H₀ (S : DTREstimationSystem P δ γ) : Measure (γ 0) :=
  P.μ.map (S.toPODTRSystem.factualS ⟨0, by decide⟩)

/-- This is the marginal law of the stage-1 history in the DTR history ordering. -/
noncomputable def P_H₁ (S : DTREstimationSystem P δ γ) :
    Measure (γ 1 × δ × γ 0) :=
  P.μ.map (fun ω =>
    (S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
     S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
     S.toPODTRSystem.factualS ⟨0, by decide⟩ ω))

/-- This map collects the full observed two-stage data tuple from the underlying outcome system. -/
noncomputable def factualZ (S : DTREstimationSystem P δ γ) :
    P.Ω → γ 0 × δ × γ 1 × δ × ℝ :=
  fun ω =>
    (S.toPODTRSystem.factualS ⟨0, by decide⟩ ω,
     S.toPODTRSystem.factualD ⟨0, by decide⟩ ω,
     S.toPODTRSystem.factualS ⟨1, by decide⟩ ω,
     S.toPODTRSystem.factualD ⟨1, by decide⟩ ω,
     S.toPODTRSystem.factualY ω)

/-- The full observed two-stage data tuple is measurable. -/
lemma measurable_factualZ (S : DTREstimationSystem P δ γ) :
    Measurable S.factualZ := by
  refine (S.toPODTRSystem.measurable_factualS ⟨0, by decide⟩).prodMk ?_
  refine (S.toPODTRSystem.measurable_factualD ⟨0, by decide⟩).prodMk ?_
  refine (S.toPODTRSystem.measurable_factualS ⟨1, by decide⟩).prodMk ?_
  exact (S.toPODTRSystem.measurable_factualD ⟨1, by decide⟩).prodMk
    S.toPODTRSystem.measurable_factualY

/-- This is the joint law of the full observed two-stage data tuple. -/
noncomputable def P_Z (S : DTREstimationSystem P δ γ) :
    Measure (γ 0 × δ × γ 1 × δ × ℝ) :=
  P.μ.map S.factualZ

/-! ### DTR estimand on the value space -/

/-- This is the fixed-regime mean outcome targeted by the two-stage DTR estimation system. -/
noncomputable def θ₀ (S : DTREstimationSystem P δ γ) : ℝ :=
  S.toPODTRSystem.dtrEffect S.dbar

/-- The value-space DTR estimand is definitionally the potential-outcome DTR effect at the chosen regime. -/
theorem θ₀_eq_dtrEffect (S : DTREstimationSystem P δ γ) :
    S.θ₀ = S.toPODTRSystem.dtrEffect S.dbar := rfl

end DTREstimationSystem

end DTR
end Estimation
end Causalean
