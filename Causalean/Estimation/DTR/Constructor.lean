/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Constructor for DTR estimation systems

This file constructs a two-stage DTR estimation system from a bare potential
outcome DTR system, a fixed regime, and two-stage pointwise overlap.  The
value-space nuisance functions are Doob--Dynkin lifts of the observable
history-measurable regressions and propensities, with propensities clamped into
the open unit interval off support.
-/

import Causalean.Estimation.DTR.Setup
import Mathlib.MeasureTheory.Function.FactorsThrough

/-!
Constructs value-space lifts for explicit two-stage dynamic-treatment-regime
histories. The module turns stagewise histories, actions, and outcome
regressions into the representatives consumed by sequential doubly robust
scores.
-/

namespace Causalean
namespace Estimation
namespace DTR

open MeasureTheory ProbabilityTheory Causalean.PO

variable {P : POSystem} {δ : Type} {γ : Fin 2 → Type}
  [MeasurableSpace δ] [MeasurableSingletonClass δ]
  [∀ k, MeasurableSpace (γ k)]
  [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]

/-! ## Value-space lifts for the explicit two-stage histories -/

omit [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ] in
/-- A real-valued stage-0 history-measurable function factors through the
explicit state coordinate `S₀`. -/
lemma exists_stage0_lift (S : PODTRSystem P 2 δ γ) (g : P.Ω → ℝ)
    (hg : Measurable[(S.historyBundle 0 (by decide)).sigma] g) :
    ∃ f : γ 0 → ℝ, Measurable f ∧
      g = fun ω => f (S.factualS ⟨0, by decide⟩ ω) := by
  let t : P.Ω → γ 0 := S.factualS ⟨0, by decide⟩
  let B := S.historyBundle 0 (by decide)
  let mT : MeasurableSpace P.Ω := MeasurableSpace.comap t inferInstance
  have ht : @Measurable P.Ω (γ 0) mT inferInstance t :=
    Measurable.of_comap_le (le_refl _)
  have hBmeas :
      @Measurable P.Ω (∀ i : Fin B.n, B.type i) mT inferInstance B.jointValue := by
    apply measurable_pi_lambda
    intro i
    dsimp [B, t, PODTRSystem.historyBundle, POCFBundle.jointValue, POCFBundle.cons,
      POCFBundle.nil, RegimedVar.ofFactual, RegimedVar.value, PODTRSystem.factualS]
    fin_cases i
    exact ht
  have hsub : B.sigma ≤ mT := hBmeas.comap_le
  have hmeas : @Measurable P.Ω ℝ mT inferInstance g := hg.mono hsub (le_refl _)
  obtain ⟨f, hf, hfg⟩ :=
    Measurable.exists_eq_measurable_comp (f := t) (g := g) hmeas
  exact ⟨f, hf, by funext ω; exact congrFun hfg ω⟩

omit [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ] in
/-- A real-valued stage-1 history-measurable function factors through the
explicit history tuple `(S₁, D₀, S₀)`. -/
lemma exists_stage1_lift (S : PODTRSystem P 2 δ γ) (g : P.Ω → ℝ)
    (hg : Measurable[(S.historyBundle 1 (by decide)).sigma] g) :
    ∃ f : γ 1 × δ × γ 0 → ℝ, Measurable f ∧
      g = fun ω => f
        (S.factualS ⟨1, by decide⟩ ω,
         S.factualD ⟨0, by decide⟩ ω,
         S.factualS ⟨0, by decide⟩ ω) := by
  let t : P.Ω → γ 1 × δ × γ 0 := fun ω =>
    (S.factualS ⟨1, by decide⟩ ω,
     S.factualD ⟨0, by decide⟩ ω,
     S.factualS ⟨0, by decide⟩ ω)
  let B := S.historyBundle 1 (by decide)
  let mT : MeasurableSpace P.Ω := MeasurableSpace.comap t inferInstance
  have ht : @Measurable P.Ω (γ 1 × δ × γ 0) mT inferInstance t :=
    Measurable.of_comap_le (le_refl _)
  have hS1 : @Measurable P.Ω (γ 1) mT inferInstance
      (S.factualS ⟨1, by decide⟩) := by
    change @Measurable P.Ω (γ 1) mT inferInstance (fun ω => (t ω).1)
    exact measurable_fst.comp ht
  have hD0 : @Measurable P.Ω δ mT inferInstance
      (S.factualD ⟨0, by decide⟩) := by
    change @Measurable P.Ω δ mT inferInstance (fun ω => (t ω).2.1)
    exact measurable_fst.comp (measurable_snd.comp ht)
  have hS0 : @Measurable P.Ω (γ 0) mT inferInstance
      (S.factualS ⟨0, by decide⟩) := by
    change @Measurable P.Ω (γ 0) mT inferInstance (fun ω => (t ω).2.2)
    exact measurable_snd.comp (measurable_snd.comp ht)
  have hBmeas :
      @Measurable P.Ω (∀ i : Fin B.n, B.type i) mT inferInstance B.jointValue := by
    apply measurable_pi_lambda
    intro i
    dsimp [B, t, PODTRSystem.historyBundle, POCFBundle.jointValue, POCFBundle.cons,
      POCFBundle.nil, RegimedVar.ofFactual, RegimedVar.value, PODTRSystem.factualS,
      PODTRSystem.factualD, PODTRSystem.dVar]
    fin_cases i
    · exact hS1
    · exact hD0
    · exact hS0
  have hsub : B.sigma ≤ mT := hBmeas.comap_le
  have hmeas : @Measurable P.Ω ℝ mT inferInstance g := hg.mono hsub (le_refl _)
  obtain ⟨f, hf, hfg⟩ :=
    Measurable.exists_eq_measurable_comp (f := t) (g := g) hmeas
  exact ⟨f, hf, by funext ω; exact congrFun hfg ω⟩

/-! ## Derivability constructor -/

open Classical in
/-- **The DTR estimation-system fields are free given two-stage overlap.**
From a bare `PODTRSystem P 2 δ γ`, a fixed target regime `dbar`, and a.e.
overlap at stages 0 and 1, construct a `DTREstimationSystem`.  The regression
fields are Doob--Dynkin lifts of the observable nested regressions, and the
propensity fields are the corresponding lifts clamped into `(0, 1)` off support. -/
noncomputable def _root_.Causalean.PO.PODTRSystem.toDTREstimationSystem
    (S : PODTRSystem P 2 δ γ) (dbar : Fin 2 → δ)
    (hov0 : ∀ᵐ ω ∂P.μ,
      0 < (S.historyBundle 0 (by decide)).condExpGiven
        ((S.dVar ⟨0, by decide⟩).indicator (dbar ⟨0, by decide⟩)) P.μ ω ∧
      (S.historyBundle 0 (by decide)).condExpGiven
        ((S.dVar ⟨0, by decide⟩).indicator (dbar ⟨0, by decide⟩)) P.μ ω < 1)
    (hov1 : ∀ᵐ ω ∂P.μ,
      0 < (S.historyBundle 1 (by decide)).condExpGiven
        ((S.dVar ⟨1, by decide⟩).indicator (dbar ⟨1, by decide⟩)) P.μ ω ∧
      (S.historyBundle 1 (by decide)).condExpGiven
        ((S.dVar ⟨1, by decide⟩).indicator (dbar ⟨1, by decide⟩)) P.μ ω < 1) :
    DTREstimationSystem P δ γ := by
  let e0prop : P.Ω → ℝ :=
    (S.historyBundle 0 (by decide)).condExpGiven
      ((S.dVar ⟨0, by decide⟩).indicator (dbar ⟨0, by decide⟩)) P.μ
  let e1prop : P.Ω → ℝ :=
    (S.historyBundle 1 (by decide)).condExpGiven
      ((S.dVar ⟨1, by decide⟩).indicator (dbar ⟨1, by decide⟩)) P.μ
  let f₂ : P.Ω → ℝ :=
    (S.historyBundle 1 (by decide)).condExpRatio
      (fun ω => S.factualY ω *
        (S.dVar ⟨1, by decide⟩).indicator (dbar ⟨1, by decide⟩) ω)
      ((S.dVar ⟨1, by decide⟩).indicator (dbar ⟨1, by decide⟩)) P.μ
  let innerReg : P.Ω → ℝ := S.innerReg dbar 1
  let B0 := S.historyBundle 0 (by decide)
  let B1 := S.historyBundle 1 (by decide)
  have hinner_meas : Measurable[B0.sigma] innerReg := by
    unfold innerReg
    unfold PODTRSystem.innerReg
    simp only [Nat.reduceAdd, Nat.reduceLT, ↓reduceDIte, Nat.reduceSub]
    let stage : Fin 2 := ⟨0, by decide⟩
    let ind_k : P.Ω → ℝ := (S.dVar stage).indicator (dbar stage)
    have hN : Measurable[B0.sigma]
        (B0.condExpGiven (fun ω' => S.innerReg dbar 0 ω' * ind_k ω') P.μ) :=
      (B0.stronglyMeasurable_condExpGiven_comap
        (fun ω' => S.innerReg dbar 0 ω' * ind_k ω')).measurable
    have hD : Measurable[B0.sigma] (B0.condExpGiven ind_k P.μ) :=
      (B0.stronglyMeasurable_condExpGiven_comap ind_k).measurable
    exact hN.div hD
  have he0_meas : Measurable[B0.sigma] e0prop :=
    (B0.stronglyMeasurable_condExpGiven_comap
      ((S.dVar ⟨0, by decide⟩).indicator (dbar ⟨0, by decide⟩))).measurable
  have hf₂_meas : Measurable[B1.sigma] f₂ := by
    let yInd : P.Ω → ℝ := fun ω => S.factualY ω *
      (S.dVar ⟨1, by decide⟩).indicator (dbar ⟨1, by decide⟩) ω
    let ind : P.Ω → ℝ :=
      (S.dVar ⟨1, by decide⟩).indicator (dbar ⟨1, by decide⟩)
    have hN : Measurable[B1.sigma] (B1.condExpGiven yInd P.μ) :=
      (B1.stronglyMeasurable_condExpGiven_comap yInd).measurable
    have hD : Measurable[B1.sigma] (B1.condExpGiven ind P.μ) :=
      (B1.stronglyMeasurable_condExpGiven_comap ind).measurable
    unfold f₂ POCFBundle.condExpRatio
    exact hN.div hD
  have he1_meas : Measurable[B1.sigma] e1prop :=
    (B1.stronglyMeasurable_condExpGiven_comap
      ((S.dVar ⟨1, by decide⟩).indicator (dbar ⟨1, by decide⟩))).measurable
  let μ0Lift := exists_stage0_lift S innerReg hinner_meas
  let e0Lift := exists_stage0_lift S e0prop he0_meas
  let μ1Lift := exists_stage1_lift S f₂ hf₂_meas
  let e1Lift := exists_stage1_lift S e1prop he1_meas
  exact
  { toPODTRSystem := S
    dbar := dbar
    μ₀_val := μ0Lift.choose
    μ₀_meas := μ0Lift.choose_spec.1
    e₀_val :=
      Set.piecewise {x : γ 0 | 0 < e0Lift.choose x ∧ e0Lift.choose x < 1}
        e0Lift.choose (fun _ => 1 / 2)
    e₀_meas := by
      refine Measurable.piecewise ?_ e0Lift.choose_spec.1 measurable_const
      exact (measurableSet_lt measurable_const e0Lift.choose_spec.1).inter
        (measurableSet_lt e0Lift.choose_spec.1 measurable_const)
    e₀_pos := by
      intro x
      by_cases hx : x ∈ {x : γ 0 | 0 < e0Lift.choose x ∧ e0Lift.choose x < 1}
      · rw [Set.piecewise_eq_of_mem _ _ _ hx]; exact hx.1
      · rw [Set.piecewise_eq_of_notMem _ _ _ hx]; norm_num
    e₀_lt_one := by
      intro x
      by_cases hx : x ∈ {x : γ 0 | 0 < e0Lift.choose x ∧ e0Lift.choose x < 1}
      · rw [Set.piecewise_eq_of_mem _ _ _ hx]; exact hx.2
      · rw [Set.piecewise_eq_of_notMem _ _ _ hx]; norm_num
    μ₁_val := μ1Lift.choose
    μ₁_meas := μ1Lift.choose_spec.1
    e₁_val :=
      Set.piecewise {x : γ 1 × δ × γ 0 | 0 < e1Lift.choose x ∧ e1Lift.choose x < 1}
        e1Lift.choose (fun _ => 1 / 2)
    e₁_meas := by
      refine Measurable.piecewise ?_ e1Lift.choose_spec.1 measurable_const
      exact (measurableSet_lt measurable_const e1Lift.choose_spec.1).inter
        (measurableSet_lt e1Lift.choose_spec.1 measurable_const)
    e₁_pos := by
      intro x
      by_cases hx : x ∈
          {x : γ 1 × δ × γ 0 | 0 < e1Lift.choose x ∧ e1Lift.choose x < 1}
      · rw [Set.piecewise_eq_of_mem _ _ _ hx]; exact hx.1
      · rw [Set.piecewise_eq_of_notMem _ _ _ hx]; norm_num
    e₁_lt_one := by
      intro x
      by_cases hx : x ∈
          {x : γ 1 × δ × γ 0 | 0 < e1Lift.choose x ∧ e1Lift.choose x < 1}
      · rw [Set.piecewise_eq_of_mem _ _ _ hx]; exact hx.2
      · rw [Set.piecewise_eq_of_notMem _ _ _ hx]; norm_num
    μ₀_reg_compat := Filter.EventuallyEq.of_eq μ0Lift.choose_spec.2.symm
    e₀_compat := by
      filter_upwards [hov0] with ω hω
      have heq : e0prop ω = e0Lift.choose (S.factualS (0 : Fin 2) ω) := by
        simpa using congrFun e0Lift.choose_spec.2 ω
      have hmem :
          S.factualS (0 : Fin 2) ω ∈
            {x : γ 0 | 0 < e0Lift.choose x ∧ e0Lift.choose x < 1} := by
        have hω' : 0 < e0prop ω ∧ e0prop ω < 1 := by
          simpa [e0prop] using hω
        change 0 < e0Lift.choose (S.factualS (0 : Fin 2) ω) ∧
          e0Lift.choose (S.factualS (0 : Fin 2) ω) < 1
        rw [← heq]
        exact hω'
      change e0prop ω =
        Set.piecewise {x : γ 0 | 0 < e0Lift.choose x ∧ e0Lift.choose x < 1}
          e0Lift.choose (fun _ => 1 / 2) (S.factualS (0 : Fin 2) ω)
      rw [heq]
      exact (Set.piecewise_eq_of_mem
        {x : γ 0 | 0 < e0Lift.choose x ∧ e0Lift.choose x < 1}
        e0Lift.choose (fun _ => 1 / 2) hmem).symm
    μ₁_reg_compat := Filter.EventuallyEq.of_eq μ1Lift.choose_spec.2.symm
    e₁_compat := by
      filter_upwards [hov1] with ω hω
      have heq : e1prop ω = e1Lift.choose
          (S.factualS (1 : Fin 2) ω,
           S.factualD (0 : Fin 2) ω,
           S.factualS (0 : Fin 2) ω) := by
        simpa using congrFun e1Lift.choose_spec.2 ω
      have hmem :
          (S.factualS (1 : Fin 2) ω,
           S.factualD (0 : Fin 2) ω,
           S.factualS (0 : Fin 2) ω) ∈
            {x : γ 1 × δ × γ 0 | 0 < e1Lift.choose x ∧ e1Lift.choose x < 1} := by
        have hω' : 0 < e1prop ω ∧ e1prop ω < 1 := by
          simpa [e1prop] using hω
        change 0 < e1Lift.choose
            (S.factualS (1 : Fin 2) ω,
             S.factualD (0 : Fin 2) ω,
             S.factualS (0 : Fin 2) ω) ∧
          e1Lift.choose
            (S.factualS (1 : Fin 2) ω,
             S.factualD (0 : Fin 2) ω,
             S.factualS (0 : Fin 2) ω) < 1
        rw [← heq]
        exact hω'
      change e1prop ω =
        Set.piecewise
          {x : γ 1 × δ × γ 0 | 0 < e1Lift.choose x ∧ e1Lift.choose x < 1}
          e1Lift.choose (fun _ => 1 / 2)
          (S.factualS (1 : Fin 2) ω,
           S.factualD (0 : Fin 2) ω,
           S.factualS (0 : Fin 2) ω)
      rw [heq]
      exact (Set.piecewise_eq_of_mem
        {x : γ 1 × δ × γ 0 | 0 < e1Lift.choose x ∧ e1Lift.choose x < 1}
        e1Lift.choose (fun _ => 1 / 2) hmem).symm }

end DTR
end Estimation
end Causalean
