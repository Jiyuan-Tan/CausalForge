/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Two-Period Dynamic LATE: pointwise consistency-on-event rewrites

Pointwise structural identities used by the bridge identifications in
`Bridges.lean` and the ratio identifications in `WhenToTreat.lean`.  Each
lemma is a direct consequence of PO consistency (def:po-consistency) applied
to one of the regimes `encZ2Regime z₂`, `encouragementRegime z`, restricted
to the corresponding factual event.

Two flavours appear:

* **Single-stage rewrites** on the events `{Z₂ = z₂}` and `{Z₁ = z₀}`: these
  match the existing `POVar.cf_eq_factual_on_event` pattern and identify a
  counterfactual under one of the dynamic regimes with a corresponding
  factual / smaller-regime variable on the event.
* **Composition rewrites** between `encZ2Regime (z 1)` and
  `encouragementRegime z` on the event `{Z₁ = z 0}`: these mirror the
  existing `YofDofZ_eq_YofD_on_DofZEq` pattern (in `WhenToTreat.lean`),
  combining `P.Consistency.composition` with the
  `encouragementRegime_disjoint_*` lemmas.

The proofs follow the existing single-period consistency proofs in
`PO/Assumptions/ConsistencyLemmas.lean` and the composition consistency proof of
`YofDofZ_eq_YofD_on_DofZEq`.
-/

import Causalean.PO.ID.Exact.DynamicLATE.Setup

/-! # Two-Period Dynamic LATE Consistency

This file proves pointwise consistency rewrites for the two-period dynamic LATE
system. The lemmas identify counterfactual outcomes and treatments with factual
or smaller-regime variables on the corresponding observed encouragement events. -/

namespace Causalean
namespace PO

open MeasureTheory ProbabilityTheory

namespace PODynLATESystem

variable {P : POSystem} {γ₀ γ₁ : Type}
variable [MeasurableSpace γ₀] [MeasurableSpace γ₁]
variable [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
variable {S : PODynLATESystem P γ₀ γ₁}

/-! ### Stage-2 single-event consistency (events `{Z₂ = z₂}`)

These mirror `POVar.cf_eq_factual_on_event` for the regime
`encZ2Regime z₂ = Regime.single S.Z2 (S.hZ2bool.symm z₂)`.  They identify
the factual outcome / treatment with the `encZ2Regime`-counterfactual on
the corresponding event. -/

/-- On `{Z₂ = z₂}`, `Y(D₁, D₂(Z₁, z₂)) = factualY` pointwise. -/
theorem YofZ2_eq_factualY_on_z2Event (As : S.Assumptions)
    (z₂ : Bool) {ω : P.Ω} (hω : S.factualZ2 ω = z₂) :
    S.YofZ2 z₂ ω = S.factualY ω := by
  -- Direct application of `POVar.cf_eq_factual_on_event` with `a := S.yVar`,
  -- `w := S.z2Var`, `y := z₂`.  Distinctness `S.Y ≠ S.Z2` from `S.Z2_ne_Y`.
  simpa [YofZ2, encZ2Regime, factualY, factualZ2, z2Var, yVar, POVar.cfUnder]
    using POVar.cf_eq_factual_on_event As.consistency S.yVar S.z2Var z₂
      S.Z2_ne_Y.symm hω

/-- On `{Z₂ = z₂}`, `D₂(Z₁, z₂) = factualD2` pointwise. -/
theorem D2ofZ2_eq_factualD2_on_z2Event (As : S.Assumptions)
    (z₂ : Bool) {ω : P.Ω} (hω : S.factualZ2 ω = z₂) :
    S.D2ofZ2 z₂ ω = S.factualD2 ω := by
  -- Same pattern as above with `a := S.d2Var`, distinctness `S.D2 ≠ S.Z2`.
  simpa [D2ofZ2, encZ2Regime, factualD2, factualZ2, z2Var, d2Var, POVar.cfUnder]
    using POVar.cf_eq_factual_on_event As.consistency S.d2Var S.z2Var z₂
      S.Z2_ne_D2.symm hω

/-! ### Stage-1 composition consistency between regimes

`encouragementRegime z` fixes `(Z₁, Z₂)` jointly; `encZ2Regime (z 1)` fixes
only `Z₂`.  On the event `{Z₁ = z 0}`, the two regimes agree on the
intermediate-agreement structure, so PO composition consistency
(`P.Consistency.composition`) identifies the corresponding outcomes /
treatments pointwise.  The proofs follow the pattern of
`YofDofZ_eq_YofD_on_DofZEq` (in `WhenToTreat.lean`). -/

/-- Shared helper: under `As.exclusion_Z1` and the event `{Z₁ = z 0}`, the
encouragement regime `S.encouragementRegime z` evaluates the same as the
single-`Z₂` regime `S.encZ2Regime (z 1)` at any node `v` distinct from both
`Z₁` and `Z₂`.  Used to derive `YofDofZ_eq_YofZ2_on_z1Event` (with `v := S.Y`)
and `D2ofZ_eq_D2ofZ2_on_z1Event` (with `v := S.D2`). -/
private lemma eval_encouragement_eq_eval_encZ2_on_z1Event
    (As : S.Assumptions) (z : Fin 2 → Bool) {ω : P.Ω}
    (hω : S.factualZ1 ω = z 0) (v : P.V) (hvZ1 : v ≠ S.Z1) (hvZ2 : v ≠ S.Z2) :
    P.eval (S.encouragementRegime z) ω v = P.eval (S.encZ2Regime (z 1)) ω v := by
  -- Step 1: apply `Consistency.composition` with
  --   r₁ := S.encZ2Regime (z 1)  (target {S.Z2}),
  --   r₂ := Regime.single S.Z1 (S.hZ1bool.symm (z 0))  (target {S.Z1}),
  --   Y := {v}  (disjoint from r₁.target ∪ r₂.target by hvZ1, hvZ2).
  -- The IntermediateAgrees premise reduces to
  --   `P.eval r₁ ω S.Z1 = S.hZ1bool.symm (z 0)`,
  -- which follows from `As.exclusion_Z1` plus the event hypothesis `hω`.
  set r₁ : Regime P.V P.X := S.encZ2Regime (z 1)
  set r₂ : Regime P.V P.X := Regime.single S.Z1 (S.hZ1bool.symm (z 0))
  have hr_disj : r₁.Disjoint r₂ := by
    simp [r₁, r₂, encZ2Regime, Regime.Disjoint, Regime.single, S.Z1_ne_Z2.symm]
  -- IntermediateAgrees r₁ r₂ ω.
  have hIA : P.IntermediateAgrees r₁ r₂ ω := by
    intro w hw
    -- r₂.target = {S.Z1}; so w = S.Z1.
    have hw_eq : w = S.Z1 := by
      have : w ∈ ({S.Z1} : Finset P.V) := hw
      simpa [Regime.single] using Finset.mem_singleton.mp this
    subst hw_eq
    -- P.eval r₁ ω S.Z1 = P.eval Regime.empty ω S.Z1   (by As.exclusion_Z1).
    -- Then factualZ1 ω = z 0 gives P.eval Regime.empty ω S.Z1 = S.hZ1bool.symm (z 0).
    have hexcl : P.eval r₁ ω S.Z1 = P.eval Regime.empty ω S.Z1 := As.exclusion_Z1 (z 1) ω
    have hfact : S.hZ1bool (P.eval Regime.empty ω S.Z1) = z 0 := hω
    have hfact' : P.eval Regime.empty ω S.Z1 = S.hZ1bool.symm (z 0) := by
      have := congrArg S.hZ1bool.symm hfact
      simpa using this
    -- r₂.assign S.Z1 _ = S.hZ1bool.symm (z 0).
    have hassign : r₂.assign S.Z1 (Finset.mem_singleton_self _) = S.hZ1bool.symm (z 0) := by
      simp [r₂, Regime.single]
    rw [hexcl, hfact', hassign]
  -- Disjointness of {v} from r₁.target ∪ r₂.target = {S.Z2, S.Z1}.
  have hYdisj : _root_.Disjoint ({v} : Finset P.V) (r₁.target ∪ r₂.target) := by
    simp [r₁, r₂, encZ2Regime, Regime.single, Finset.disjoint_singleton_left,
      Finset.mem_singleton, hvZ1, hvZ2]
  -- Apply composition: P.poVariable (r₁ ⊔ r₂) {v} ω = P.poVariable r₁ {v} ω.
  have hpv := As.consistency.composition r₁ r₂ hr_disj {v} hYdisj ω hIA
  -- Extract pointwise: P.eval (r₁ ⊔ r₂) ω v = P.eval r₁ ω v.
  have hev_sqcup_eq_r1 : P.eval (r₁.sqcup r₂ hr_disj) ω v = P.eval r₁ ω v := by
    have := congrFun hpv ⟨v, Finset.mem_singleton_self _⟩
    exact this
  -- The encouragementRegime z is `Regime.ofList`-built; show its eval at v
  -- agrees with eval of `r₁.sqcup r₂` at v via `Regime.ext`.
  have hReg_eq : S.encouragementRegime z = r₁.sqcup r₂ hr_disj := by
    refine Regime.ext ?_ ?_
    · -- targets equal as Finsets.
      simp [encouragementRegime, Regime.ofList, r₁, r₂, encZ2Regime, Regime.single,
        Finset.union_comm]
    · -- pointwise assignments equal.
      intro w h₁ h₂
      -- The encouragementRegime fixes Z₁ ↦ z 0, Z₂ ↦ z 1 via Regime.ofList.
      -- Need to case on w ∈ {S.Z1, S.Z2}.
      have hw_mem : w = S.Z1 ∨ w = S.Z2 := by
        have hw : w ∈ ({S.Z1, S.Z2} : Finset P.V) := by
          have : w ∈ (S.encouragementRegime z).target := h₁
          simpa [encouragementRegime, Regime.ofList] using this
        rcases Finset.mem_insert.mp hw with hw | hw
        · exact Or.inl hw
        · exact Or.inr (Finset.mem_singleton.mp hw)
      rcases hw_mem with rfl | rfl
      · -- w = S.Z1: encouragementRegime assigns hZ1bool.symm (z 0); r₁.sqcup r₂ assigns
        -- via r₂ since S.Z1 ∉ r₁.target = {S.Z2}.
        have hZ1_not_in_r1 : S.Z1 ∉ r₁.target := by
          simp [r₁, encZ2Regime, Regime.single, S.Z1_ne_Z2]
        have hZ1_in_r2 : S.Z1 ∈ r₂.target := by
          simp [r₂, Regime.single]
        rw [Regime.sqcup_assign_neg r₁ r₂ hr_disj S.Z1 h₂ hZ1_not_in_r1 hZ1_in_r2]
        -- LHS: encouragementRegime.assign S.Z1 _ = listLookup [⟨Z1,..⟩,⟨Z2,..⟩] S.Z1 _.
        change Regime.listLookup _ S.Z1 _ = _
        rw [Regime.listLookup_cons_self]
        -- RHS: r₂.assign S.Z1 _ = hZ1bool.symm (z 0).
        simp [r₂, Regime.single]
      · -- w = S.Z2: encouragementRegime assigns hZ2bool.symm (z 1); sqcup assigns via r₁.
        have hZ2_in_r1 : S.Z2 ∈ r₁.target := by
          simp [r₁, encZ2Regime, Regime.single]
        rw [Regime.sqcup_assign_pos r₁ r₂ hr_disj S.Z2 h₂ hZ2_in_r1]
        -- LHS: listLookup [⟨Z1,..⟩,⟨Z2,..⟩] S.Z2 _.
        change Regime.listLookup _ S.Z2 _ = _
        have hne : S.Z2 ≠ S.Z1 := S.Z1_ne_Z2.symm
        have hmem_rest : S.Z2 ∈
            ([⟨S.Z2, S.hZ2bool.symm (z 1)⟩] :
              List ((v : P.V) × P.X v)).map Sigma.fst := by simp
        rw [Regime.listLookup_cons_of_ne hne _ hmem_rest, Regime.listLookup_cons_self]
        -- RHS: r₁.assign S.Z2 _ = hZ2bool.symm (z 1).
        simp [r₁, encZ2Regime, Regime.single]
  rw [hReg_eq, hev_sqcup_eq_r1]

/-- On `{Z₁ = z 0}`, `Y` under `encouragementRegime z` agrees with `Y`
under `encZ2Regime (z 1)`. -/
theorem YofDofZ_eq_YofZ2_on_z1Event (As : S.Assumptions)
    (z : Fin 2 → Bool) {ω : P.Ω} (hω : S.factualZ1 ω = z 0) :
    S.YofDofZ z ω = S.YofZ2 (z 1) ω := by
  unfold YofDofZ YofZ2 POVar.cf yVar
  exact congrArg _
    (eval_encouragement_eq_eval_encZ2_on_z1Event As z hω S.Y S.Z1_ne_Y.symm S.Z2_ne_Y.symm)

/-- On `{Z₁ = z 0}`, `D₂` under `encouragementRegime z` agrees with `D₂`
under `encZ2Regime (z 1)`. -/
theorem D2ofZ_eq_D2ofZ2_on_z1Event (As : S.Assumptions)
    (z : Fin 2 → Bool) {ω : P.Ω} (hω : S.factualZ1 ω = z 0) :
    S.D2ofZ z ω = S.D2ofZ2 (z 1) ω := by
  unfold D2ofZ D2ofZ2 POVar.cf d2Var
  exact congrArg _
    (eval_encouragement_eq_eval_encZ2_on_z1Event As z hω S.D2 S.Z1_ne_D2.symm S.Z2_ne_D2.symm)

/-- On `{Z₁ = z 0}`, `D₁` under `encouragementRegime z` agrees with the
factual `D₁`.

Combines the primitive-process clause `As.exclusion_D1` (which reduces
`D₁` under `encouragementRegime z` to `D₁` under `Regime.single Z₁ (z 0)`)
with `POVar.cf_eq_factual_on_event` at `Z₁` (which collapses the
single-`Z₁` regime to factual on the event `{Z₁ = z 0}`). -/
theorem D1ofZ_eq_factualD1_on_z1Event (As : S.Assumptions)
    (z : Fin 2 → Bool) {ω : P.Ω} (hω : S.factualZ1 ω = z 0) :
    S.D1ofZ z ω = S.factualD1 ω := by
  -- Step 1: `S.d1Var.cf (encouragementRegime z) ω = S.d1Var.cf (Regime.single Z₁ ..) ω`
  --         via `As.exclusion_D1`.
  -- Step 2: `S.d1Var.cf (Regime.single Z₁ ..) ω = S.factualD1 ω` via
  --         `POVar.cf_eq_factual_on_event` with `a := S.d1Var`, `w := S.z1Var`,
  --         `y := z 0`, distinctness `S.D1 ≠ S.Z1` (from `S.Z1_ne_D1.symm`),
  --         and the event hypothesis `hω`.
  -- Note: `S.D1ofZ z ω = S.d1Var.cf (encouragementRegime z) ω` by definition,
  -- and `S.d1Var.cfUnder S.z1Var (z 0) = S.d1Var.cf (Regime.single Z₁ ..)`
  -- by `POVar.cfUnder` def.
  calc
    S.D1ofZ z ω
        = S.d1Var.cf (Regime.single S.Z1 (S.hZ1bool.symm (z 0))) ω := by
          simpa [D1ofZ] using As.exclusion_D1 z ω
    _ = S.factualD1 ω := by
          simpa [factualD1, factualZ1, z1Var, d1Var, POVar.cfUnder]
            using POVar.cf_eq_factual_on_event As.consistency S.d1Var S.z1Var
              (z 0) S.Z1_ne_D1.symm hω

end PODynLATESystem

end PO
end Causalean
