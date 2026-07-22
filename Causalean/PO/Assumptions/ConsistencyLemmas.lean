/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Pointwise Consistency Lemmas for `POVar`

Generalises the two pointwise consistency specialisations used in LATE.lean
(`DofZ_eq_factualD_on_zEvent`, `factualY_eq_YofD_factualD`) to arbitrary
`POVar` pairs.  The IV-specific versions in `PO/ID/Exact/LATE.lean`
can be recovered as instances of these.
-/

import Causalean.PO.Assumptions.Consistency
import Causalean.PO.Core.Regime
import Causalean.PO.Core.Variable

/-! # Pointwise consistency lemmas for potential-outcome variables

This file provides reusable pointwise consistency combinators for empty,
singleton, and disjoint-union regimes, together with generic event-level rewrites
for `POVar` counterfactual values. These lemmas factor the consistency arguments
used by LATE, frontdoor, dynamic regimes, and other multi-target PO
identification files.  Important results include `POSystem.factualAgrees_empty`,
`POSystem.factualAgrees_sqcup`, `POVar.factualAgrees_single`,
`POVar.cf_eq_factual_on_event`, and the integrated indicator rewrites
`POVar.factual_mul_indicator_eq_cfUnder_mul_indicator` and
`POVar.factual_mul_indicator_eq_cf_mul_indicator`.
-/

namespace Causalean
namespace PO

/-! ### `FactualAgrees` combinators

Reusable building blocks that reconstruct `P.FactualAgrees r ω` for compound
regimes built out of `Regime.empty`, `Regime.single`, and `Regime.sqcup`, from
per-variable factual equalities of the form `a.factual ω = x`.  Used by every
theorem file whose regime is a disjoint union of singletons (DTR, Frontdoor,
multi-target backdoor, …). -/

namespace POSystem

variable {P : POSystem}

/-- `FactualAgrees` holds vacuously for the empty regime. -/
theorem factualAgrees_empty (ω : P.Ω) : P.FactualAgrees Regime.empty ω := by
  intro v hv
  exact (Finset.notMem_empty v hv).elim

/-- Combinator: `FactualAgrees` for a disjoint union reduces to `FactualAgrees`
for each component. -/
theorem factualAgrees_sqcup
    {r₁ r₂ : Regime P.V P.X} (h : r₁.Disjoint r₂) {ω : P.Ω}
    (h₁ : P.FactualAgrees r₁ ω) (h₂ : P.FactualAgrees r₂ ω) :
    P.FactualAgrees (r₁.sqcup r₂ h) ω := by
  intro v hv
  -- `v ∈ r₁.target ∪ r₂.target`.
  have hv' : v ∈ r₁.target ∪ r₂.target := by
    simpa [Regime.sqcup] using hv
  by_cases hv₁ : v ∈ r₁.target
  · -- `r₁.sqcup r₂` agrees with `r₁` on `r₁.target`.
    have hassign : (r₁.sqcup r₂ h).assign v hv = r₁.assign v hv₁ := by
      simp [Regime.sqcup, hv₁]
    rw [hassign]
    exact h₁ v hv₁
  · -- Must be in `r₂.target`.
    have hv₂ : v ∈ r₂.target := by
      rcases Finset.mem_union.mp hv' with h₁ | h₂
      · exact (hv₁ h₁).elim
      · exact h₂
    have hassign : (r₁.sqcup r₂ h).assign v hv = r₂.assign v hv₂ := by
      simp [Regime.sqcup, hv₁]
    rw [hassign]
    exact h₂ v hv₂

end POSystem

namespace POVar

variable {P : POSystem} {α : Type*} [MeasurableSpace α]

/-- Combinator: from a factual equality `a.factual ω = x`, build
`FactualAgrees` for the singleton regime `{a.v ← a.equiv.symm x}`. -/
theorem factualAgrees_single (a : POVar P α) (x : α) {ω : P.Ω}
    (h : a.factual ω = x) :
    P.FactualAgrees (Regime.single a.v (a.equiv.symm x)) ω := by
  intro v hv
  -- `v ∈ {a.v}`, so `v = a.v`.
  have hv_eq : v = a.v := Finset.mem_singleton.mp hv
  subst hv_eq
  -- `h : a.equiv (P.eval ∅ ω a.v) = x`; apply `a.equiv.symm`.
  have hω : a.equiv (P.eval Regime.empty ω a.v) = x := h
  have := congrArg a.equiv.symm hω
  simpa [Regime.single] using this

end POVar

/-- Under consistency, changing a distinct variable to a value it already has
does not change the counterfactual value of the target variable on that event. -/
theorem POVar.cf_eq_factual_on_event
    {P : POSystem} {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (hC : P.Consistency)
    (a : POVar P α) (w : POVar P β) (y : β) (hvw : a.v ≠ w.v)
    {ω : P.Ω} (hω : ω ∈ w.event y) :
    a.cfUnder w y ω = a.factual ω := by
  -- The regime: `{w.v ← w.equiv.symm y}`.
  set r : Regime P.V P.X := Regime.single w.v (w.equiv.symm y) with hr
  -- Factual agreement: `P.eval ∅ ω v = r.assign v hv` for all `v ∈ r.target`.
  have hAgrees : P.FactualAgrees r ω := by
    intro v hv
    have hvw_eq : v = w.v := Finset.mem_singleton.mp hv
    subst hvw_eq
    -- `hω : ω ∈ w.event y`, i.e. `w.factual ω = y`, i.e.
    -- `w.equiv (P.eval ∅ ω w.v) = y`.
    have hωeq : w.equiv (P.eval Regime.empty ω w.v) = y := hω
    -- Apply `w.equiv.symm` and use `symm_apply_apply`.
    have := congrArg w.equiv.symm hωeq
    simpa [POVar.factual, POVar.cf, Regime.single] using this
  -- Disjointness: `{a.v}` is disjoint from `r.target = {w.v}`.
  have hdisj : _root_.Disjoint ({a.v} : Finset P.V) r.target := by
    simp [hr, Regime.single, hvw]
  -- Apply `hC.factual`.
  have hPoEq := hC.factual r {a.v} hdisj ω hAgrees
  have haEq : P.eval r ω a.v = P.eval Regime.empty ω a.v := by
    simpa [POSystem.poVariable] using
      congrFun hPoEq ⟨a.v, Finset.mem_singleton_self a.v⟩
  -- Push through `a.equiv`.
  change a.equiv (P.eval r ω a.v) = a.equiv (P.eval Regime.empty ω a.v)
  exact congrArg a.equiv haEq

/-- Under consistency, setting a distinct variable to its realized factual value
leaves the target variable at its factual value. -/
theorem POVar.factual_eq_cfUnder_self_selected
    {P : POSystem} {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (hC : P.Consistency)
    (a : POVar P α) (w : POVar P β) (hvw : a.v ≠ w.v) (ω : P.Ω) :
    a.factual ω = a.cfUnder w (w.factual ω) ω := by
  -- The regime: `{w.v ← w.equiv.symm (w.factual ω)}`.
  set r : Regime P.V P.X := Regime.single w.v (w.equiv.symm (w.factual ω))
    with hr
  -- Factual agreement is definitional: `w.equiv.symm (w.equiv x) = x`.
  have hAgrees : P.FactualAgrees r ω := by
    intro v hv
    have hvw_eq : v = w.v := Finset.mem_singleton.mp hv
    subst hvw_eq
    simp [hr, POVar.factual, POVar.cf, Regime.single]
  -- Disjointness.
  have hdisj : _root_.Disjoint ({a.v} : Finset P.V) r.target := by
    simp [hr, Regime.single, hvw]
  -- Apply `hC.factual`.
  have hPoEq := hC.factual r {a.v} hdisj ω hAgrees
  have haEq : P.eval r ω a.v = P.eval Regime.empty ω a.v := by
    simpa [POSystem.poVariable] using
      congrFun hPoEq ⟨a.v, Finset.mem_singleton_self a.v⟩
  change a.equiv (P.eval Regime.empty ω a.v) = a.equiv (P.eval r ω a.v)
  exact (congrArg a.equiv haEq).symm

/-- Integrated form of consistency: `Y · 1_{W=y} = Y(w=y) · 1_{W=y}` pointwise,
where `a` plays the role of `Y` and `w` the role of the treatment.  Used in
backdoor-style identification proofs where the factual outcome is replaced by
the counterfactual on the event `{W = y}`. -/
theorem POVar.factual_mul_indicator_eq_cfUnder_mul_indicator
    {P : POSystem} {β : Type*}
    [MeasurableSpace β]
    (hC : P.Consistency)
    (a : POVar P ℝ) (w : POVar P β) (y : β) (hvw : a.v ≠ w.v) :
    (fun ω => a.factual ω * (w.event y).indicator (fun _ => (1:ℝ)) ω)
    = fun ω => a.cfUnder w y ω * (w.event y).indicator (fun _ => (1:ℝ)) ω := by
  funext ω
  by_cases hω : ω ∈ w.event y
  · have hind : (w.event y).indicator (fun _ => (1:ℝ)) ω = 1 :=
      Set.indicator_of_mem hω _
    have hcf : a.cfUnder w y ω = a.factual ω :=
      POVar.cf_eq_factual_on_event hC a w y hvw hω
    simp [hind, hcf]
  · have hind : (w.event y).indicator (fun _ => (1:ℝ)) ω = 0 :=
      Set.indicator_of_notMem hω _
    simp [hind]

/-- Pointwise-function variant of
`POVar.factual_mul_indicator_eq_cfUnder_mul_indicator`, phrased directly in
terms of `POVar.indicator` (rather than `Set.indicator` on `w.event y`).

Used by backdoor/Manski/frontdoor/DTR consistency rewrites of the shape
`Y · 1_{W=y} =ᵐ Y(w=y) · 1_{W=y}`. -/
theorem POVar.factual_mul_indicator_eq_cfUnder_mul_indicator_fn
    {P : POSystem} {β : Type*}
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (hC : P.Consistency)
    (y : POVar P ℝ) (w : POVar P β) (x : β) (h_ne : y.v ≠ w.v) :
    (fun ω => y.factual ω * w.indicator x ω)
      = fun ω => y.cfUnder w x ω * w.indicator x ω := by
  rw [w.indicator_eq_event_indicator x]
  exact POVar.factual_mul_indicator_eq_cfUnder_mul_indicator hC y w x h_ne

/-- Multi-target consistency: if `r` is a regime whose target does not contain
`a.v`, and `ω` factually agrees with `r`, then the counterfactual value of `a`
under `r` equals its factual value at `ω`. -/
theorem POVar.cf_eq_factual_of_factualAgrees
    {P : POSystem} {α : Type*} [MeasurableSpace α]
    (hC : P.Consistency)
    (a : POVar P α) (r : Regime P.V P.X)
    (h_notmem : a.v ∉ r.target)
    (ω : P.Ω) (hAgrees : P.FactualAgrees r ω) :
    a.cf r ω = a.factual ω := by
  -- Disjointness: `{a.v}` is disjoint from `r.target`.
  have hdisj : _root_.Disjoint ({a.v} : Finset P.V) r.target := by
    simpa [Finset.disjoint_singleton_left] using h_notmem
  -- Apply `hC.factual`.
  have hPoEq := hC.factual r {a.v} hdisj ω hAgrees
  have haEq : P.eval r ω a.v = P.eval Regime.empty ω a.v := by
    simpa [POSystem.poVariable] using
      congrFun hPoEq ⟨a.v, Finset.mem_singleton_self a.v⟩
  -- Push through `a.equiv`.
  change a.equiv (P.eval r ω a.v) = a.equiv (P.eval Regime.empty ω a.v)
  exact congrArg a.equiv haEq

/-- Multi-target integrated consistency: `Y · 1_E = Y(r) · 1_E` pointwise,
whenever every `ω ∈ E` factually agrees with `r` and `a.v ∉ r.target`. -/
theorem POVar.factual_mul_indicator_eq_cf_mul_indicator
    {P : POSystem}
    (hC : P.Consistency)
    (a : POVar P ℝ) (r : Regime P.V P.X)
    (h_notmem : a.v ∉ r.target)
    (E : Set P.Ω) (hE : ∀ ω ∈ E, P.FactualAgrees r ω) :
    (fun ω => a.factual ω * E.indicator (fun _ => (1:ℝ)) ω)
    = (fun ω => a.cf r ω * E.indicator (fun _ => (1:ℝ)) ω) := by
  funext ω
  by_cases hω : ω ∈ E
  · have hind : E.indicator (fun _ => (1:ℝ)) ω = 1 :=
      Set.indicator_of_mem hω _
    have hcf : a.cf r ω = a.factual ω :=
      POVar.cf_eq_factual_of_factualAgrees hC a r h_notmem ω (hE ω hω)
    simp [hind, hcf]
  · have hind : E.indicator (fun _ => (1:ℝ)) ω = 0 :=
      Set.indicator_of_notMem hω _
    simp [hind]

end PO
end Causalean
