/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.PO.Assumptions.Consistency

/-! # Restricted Potential-Outcome Systems

This file builds the potential-outcome system induced by restricting attention
to a finite set of variables.  `POSystem.liftRegime` embeds regimes on the
restricted variable set back into the ambient system, `POSystem.restrict` builds
the sub-system itself, and the lift lemmas show that targets, assignments,
empty regimes, disjointness, and `Regime.sqcup` are preserved.  The theorem
`POSystem.restrict_consistency` proves that consistency of the original system
transfers to the restricted system. -/

namespace Causalean
namespace PO

open MeasureTheory

namespace POSystem

variable (P : POSystem) (R : Finset P.V)

/-- For a potential-outcome system, a finite set of variables, and an
intervention regime whose variables all lie in that finite set, this construction
returns the corresponding intervention regime on the original system by viewing
each restricted variable as a variable of the original system.

Lift a sub-regime on `R` to an ambient regime on `V`. -- def:po-restrict.

The assignment is defined by going through the membership proof: if `v` is in
the lifted target, then `v ∈ R` and the corresponding `↥R`-element lies in
the original sub-regime target.  No `Classical.choose` is needed because the
recovered subtype element `⟨v, hvR⟩` has `.val = v`, so the value type
matches definitionally. -/
def liftRegime
    (r' : Regime (↥R) (fun v : ↥R => P.X v.val)) : Regime P.V P.X where
  target := r'.target.map ⟨Subtype.val, Subtype.val_injective⟩
  assign v hv :=
    have hvR : v ∈ R := by
      rcases Finset.mem_map.mp hv with ⟨w, _, rfl⟩
      exact w.property
    have hwT : (⟨v, hvR⟩ : ↥R) ∈ r'.target := by
      rcases Finset.mem_map.mp hv with ⟨w, hw, hwv⟩
      have hwwR : (⟨v, hvR⟩ : ↥R) = w := Subtype.ext hwv.symm
      exact hwwR ▸ hw
    r'.assign ⟨v, hvR⟩ hwT

/-- The target of a lifted restricted regime is the image of the restricted
target in the original variable set. -/
@[simp] lemma liftRegime_target
    (r' : Regime (↥R) (fun v : ↥R => P.X v.val)) :
    (P.liftRegime R r').target =
      r'.target.map ⟨Subtype.val, Subtype.val_injective⟩ := rfl

/-- Reading the lifted assignment at a known sub-regime member returns the
original sub-assignment.  Membership proofs are propositional, so the
ambient `hv` is irrelevant. -/
lemma liftRegime_assign
    (r' : Regime (↥R) (fun v : ↥R => P.X v.val))
    (w : ↥R) (hw : w ∈ r'.target)
    (hv : (w.val : P.V) ∈ (P.liftRegime R r').target) :
    (P.liftRegime R r').assign w.val hv = r'.assign w hw := by
  change r'.assign ⟨w.val, w.property⟩ _ = r'.assign w hw
  congr 1

/-- Lifting the empty restricted regime gives the empty regime on the original system. -/
@[simp] lemma liftRegime_empty :
    P.liftRegime R (Regime.empty :
        Regime (↥R) (fun v : ↥R => P.X v.val)) =
      (Regime.empty : Regime P.V P.X) := by
  apply Regime.ext
  · simp [liftRegime_target, Regime.empty]
  · intro v hv _
    simp [liftRegime_target, Regime.empty] at hv

/-- For a potential-outcome system and a finite set of variables, the restricted
potential-outcome system has that finite set as its variable collection, keeps
the same sample space and probability measure, and evaluates restricted
intervention regimes by first lifting them back to intervention regimes of the
original system.

Restricted sub-PO system `P|_R` -- def:po-restrict. -/
noncomputable def restrict : POSystem where
  V := ↥R
  X := fun v => P.X v.val
  Ω := P.Ω
  μ := P.μ
  eval := fun r' ω v => P.eval (P.liftRegime R r') ω v.val
  measurable_eval := by
    intro r'
    refine measurable_pi_lambda _ ?_
    intro v
    exact (measurable_pi_apply v.val).comp (P.measurable_eval _)

/-- The variable type of the restricted potential-outcome system is the chosen
finite set of variables. -/
@[simp] lemma restrict_V : (P.restrict R).V = ↥R := rfl
/-- The value space in the restricted system is the original value space at the
underlying variable. -/
@[simp] lemma restrict_X (v : ↥R) : (P.restrict R).X v = P.X v.val := rfl
/-- The restricted potential-outcome system uses the same sample space as the original system. -/
@[simp] lemma restrict_Ω : (P.restrict R).Ω = P.Ω := rfl
/-- The restricted potential-outcome system uses the same probability measure
as the original system. -/
@[simp] lemma restrict_μ : (P.restrict R).μ = P.μ := rfl

/-- Evaluation in the restricted system is evaluation in the original system
after lifting the restricted regime. -/
@[simp] lemma restrict_eval
    (r' : Regime (↥R) (fun v : ↥R => P.X v.val))
    (ω : P.Ω) (v : ↥R) :
    (P.restrict R).eval r' ω v = P.eval (P.liftRegime R r') ω v.val := rfl

/-- A coordinate potential outcome in the restricted system agrees with the
original coordinate after lifting the regime. -/
@[simp] lemma restrict_component
    (r' : Regime (↥R) (fun v : ↥R => P.X v.val)) (v : ↥R) :
    (P.restrict R).component r' v = P.component (P.liftRegime R r') v.val :=
  rfl

/-! ### Disjointness and `sqcup` for the lift -/

/-- Disjoint restricted regimes remain disjoint after lifting them to the original system. -/
lemma liftRegime_disjoint
    {r₁' r₂' : Regime (↥R) (fun v : ↥R => P.X v.val)}
    (h : r₁'.Disjoint r₂') :
    (P.liftRegime R r₁').Disjoint (P.liftRegime R r₂') := by
  rw [Regime.Disjoint, liftRegime_target, liftRegime_target,
    Finset.disjoint_left]
  intro v hv₁ hv₂
  rcases Finset.mem_map.mp hv₁ with ⟨w₁, hw₁, rfl⟩
  rcases Finset.mem_map.mp hv₂ with ⟨w₂, hw₂, hw₂eq⟩
  have : w₁ = w₂ := Subtype.val_injective hw₂eq.symm
  subst this
  exact (Finset.disjoint_left.mp h hw₁) hw₂

/-- The lift commutes with `Regime.sqcup` (target equality). -/
lemma liftRegime_sqcup_target
    {r₁' r₂' : Regime (↥R) (fun v : ↥R => P.X v.val)}
    (h : r₁'.Disjoint r₂') :
    (P.liftRegime R (r₁'.sqcup r₂' h)).target =
      (P.liftRegime R r₁').target ∪ (P.liftRegime R r₂').target := by
  simp [liftRegime_target, Finset.map_union]

/-- The lift commutes with `Regime.sqcup` (full equality). -/
lemma liftRegime_sqcup
    {r₁' r₂' : Regime (↥R) (fun v : ↥R => P.X v.val)}
    (h : r₁'.Disjoint r₂') :
    P.liftRegime R (r₁'.sqcup r₂' h) =
      (P.liftRegime R r₁').sqcup (P.liftRegime R r₂')
        (P.liftRegime_disjoint R h) := by
  apply Regime.ext (P.liftRegime_sqcup_target R h)
  intro v hv hv2
  -- v lies in the lifted union, so v = w.val for some w in r₁' ∪ r₂'.
  rw [liftRegime_target] at hv
  rcases Finset.mem_map.mp hv with ⟨w, hwU, rfl⟩
  -- Normalize both membership proofs to talk about w.val instead of the
  -- raw embedding application.
  have hv1' : (w.val : P.V) ∈ (P.liftRegime R (r₁'.sqcup r₂' h)).target := by
    rw [liftRegime_target]; exact Finset.mem_map.mpr ⟨w, hwU, rfl⟩
  have hv2' : (w.val : P.V) ∈
      ((P.liftRegime R r₁').sqcup (P.liftRegime R r₂')
        (P.liftRegime_disjoint R h)).target := by
    rw [Regime.sqcup_target]
    rcases Finset.mem_union.mp hwU with hw | hw
    · exact Finset.mem_union_left _ (Finset.mem_map.mpr ⟨w, hw, rfl⟩)
    · exact Finset.mem_union_right _ (Finset.mem_map.mpr ⟨w, hw, rfl⟩)
  change (P.liftRegime R (r₁'.sqcup r₂' h)).assign w.val hv1' =
    ((P.liftRegime R r₁').sqcup (P.liftRegime R r₂')
      (P.liftRegime_disjoint R h)).assign w.val hv2'
  rw [P.liftRegime_assign R (r₁'.sqcup r₂' h) w hwU]
  -- Now goal: (r₁'.sqcup r₂' h).assign w hwU = (sqcup of lifts).assign w.val hv2'
  by_cases hw1 : w ∈ r₁'.target
  · have hv_in_lift1 : (w.val : P.V) ∈ (P.liftRegime R r₁').target :=
      Finset.mem_map.mpr ⟨w, hw1, rfl⟩
    rw [Regime.sqcup_assign_pos _ _ _ _ _ hw1,
        Regime.sqcup_assign_pos _ _ _ _ _ hv_in_lift1,
        P.liftRegime_assign R r₁' w hw1]
  · have hw2 : w ∈ r₂'.target := by
      rcases Finset.mem_union.mp hwU with hw | hw
      · exact (hw1 hw).elim
      · exact hw
    have hv_not_in_lift1 : (w.val : P.V) ∉ (P.liftRegime R r₁').target := by
      rw [liftRegime_target]
      intro hv1
      rcases Finset.mem_map.mp hv1 with ⟨w', hw', heq⟩
      have : w = w' := Subtype.val_injective heq.symm
      subst this
      exact hw1 hw'
    have hv_in_lift2 : (w.val : P.V) ∈ (P.liftRegime R r₂').target :=
      Finset.mem_map.mpr ⟨w, hw2, rfl⟩
    rw [Regime.sqcup_assign_neg _ _ _ _ _ hw1 hw2,
        Regime.sqcup_assign_neg _ _ _ _ _ hv_not_in_lift1 hv_in_lift2,
        P.liftRegime_assign R r₂' w hw2]

/-! ### Consistency propagates to the sub-system -/

/-- If `P` is consistent, so is `P|_R`. -- rem:po-restrict pragmatic use. -/
theorem restrict_consistency (hP : P.Consistency) :
    (P.restrict R).Consistency where
  factual := by
    intro r' Y hYr ω hag
    -- Build the ambient FactualAgrees witness.
    have hagP : P.FactualAgrees (P.liftRegime R r') ω := by
      intro v hv
      rcases Finset.mem_map.mp hv with ⟨w, hw, rfl⟩
      have hv' : (w.val : P.V) ∈ (P.liftRegime R r').target := hv
      change P.eval Regime.empty ω w.val =
        (P.liftRegime R r').assign w.val hv'
      rw [P.liftRegime_assign R r' w hw]
      have hwsub := hag w hw
      simp only [restrict_eval] at hwsub
      exact hwsub
    -- Lift Y.
    set Yamb : Finset P.V :=
      Y.map ⟨Subtype.val, Subtype.val_injective⟩ with hYamb_def
    have hYr_amb : _root_.Disjoint Yamb (P.liftRegime R r').target := by
      rw [hYamb_def, liftRegime_target, Finset.disjoint_left]
      intro v hvY hvr
      rcases Finset.mem_map.mp hvY with ⟨y, hy, rfl⟩
      rcases Finset.mem_map.mp hvr with ⟨w, hw, hwy⟩
      have : y = w := Subtype.val_injective hwy.symm
      subst this
      exact (Finset.disjoint_left.mp hYr hy) hw
    have hpv := hP.factual (P.liftRegime R r') Yamb hYr_amb ω hagP
    -- Pointwise equality on Y.
    funext y
    have hyamb : (y.val.val : P.V) ∈ Yamb := by
      rw [hYamb_def]; exact Finset.mem_map.mpr ⟨y.val, y.property, rfl⟩
    have heq := congrArg (fun f => f ⟨y.val.val, hyamb⟩) hpv
    -- Goal: (P.restrict R).poVariable r' Y ω y = (P.restrict R).poVariable Regime.empty Y ω y
    change P.eval (P.liftRegime R r') ω y.val.val =
      P.eval (P.liftRegime R Regime.empty) ω y.val.val
    rw [liftRegime_empty]
    exact heq
  composition := by
    intro r₁' r₂' hd Y hYr ω hag
    -- Build ambient IntermediateAgrees.
    have hagP : P.IntermediateAgrees (P.liftRegime R r₁') (P.liftRegime R r₂') ω := by
      intro v hv
      rcases Finset.mem_map.mp hv with ⟨w, hw, rfl⟩
      have hv' : (w.val : P.V) ∈ (P.liftRegime R r₂').target := hv
      change P.eval (P.liftRegime R r₁') ω w.val =
        (P.liftRegime R r₂').assign w.val hv'
      rw [P.liftRegime_assign R r₂' w hw]
      have hwsub := hag w hw
      simp only [restrict_eval] at hwsub
      exact hwsub
    -- Lift Y.
    set Yamb : Finset P.V :=
      Y.map ⟨Subtype.val, Subtype.val_injective⟩ with hYamb_def
    have hd_amb : (P.liftRegime R r₁').Disjoint (P.liftRegime R r₂') :=
      P.liftRegime_disjoint R hd
    have hYr_amb : _root_.Disjoint Yamb
        ((P.liftRegime R r₁').target ∪ (P.liftRegime R r₂').target) := by
      rw [hYamb_def, Finset.disjoint_left]
      intro v hvY hvU
      rcases Finset.mem_map.mp hvY with ⟨y, hy, rfl⟩
      rcases Finset.mem_union.mp hvU with hv | hv
      · rcases Finset.mem_map.mp hv with ⟨w, hw, hwy⟩
        have : y = w := Subtype.val_injective hwy.symm
        subst this
        exact (Finset.disjoint_left.mp hYr hy) (Finset.mem_union_left _ hw)
      · rcases Finset.mem_map.mp hv with ⟨w, hw, hwy⟩
        have : y = w := Subtype.val_injective hwy.symm
        subst this
        exact (Finset.disjoint_left.mp hYr hy) (Finset.mem_union_right _ hw)
    have hpv := hP.composition (P.liftRegime R r₁') (P.liftRegime R r₂')
      hd_amb Yamb hYr_amb ω hagP
    funext y
    have hyamb : (y.val.val : P.V) ∈ Yamb := by
      rw [hYamb_def]; exact Finset.mem_map.mpr ⟨y.val, y.property, rfl⟩
    have heq := congrArg (fun f => f ⟨y.val.val, hyamb⟩) hpv
    change P.eval (P.liftRegime R (r₁'.sqcup r₂' hd)) ω y.val.val =
      P.eval (P.liftRegime R r₁') ω y.val.val
    have hsq :
        P.liftRegime R (r₁'.sqcup r₂' hd) =
          (P.liftRegime R r₁').sqcup (P.liftRegime R r₂')
            (P.liftRegime_disjoint R hd) := by
      exact P.liftRegime_sqcup R hd
    rw [hsq]
    convert heq using 2

end POSystem

end PO
end Causalean
