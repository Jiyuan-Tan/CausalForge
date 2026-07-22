/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Grounding the BJS panel in a staggered-adoption two-way fixed-effect design

The abstract `BJSPanel` of `Imputation.lean` uses free index types for the
treated and untreated cells.  This file closes that scope gap (audit G5)
*constructively*: it exhibits `BJSPanel` as an instance built from genuine panel
primitives — units `I`, periods `Fin T`, and a staggered-adoption path
`g : I → WithTop (Fin T)` (with `⊤` the never-treated path, via
`Causalean.Panel.AdoptionPath`).

Treated cells are those whose treatment has switched on (`g i ≤ t`); untreated
cells are those still untreated (`t < g i`), which — faithfully to BJS — include
every never-treated cell *and* every pre-adoption cell of a treated unit.  The
regressor design is the canonical two-way fixed-effect block `I ⊕ Fin T`, so the
untreated-outcome model `E[Y_{it}(0)] = α_i + λ_t` holds by construction and the
BJS identification hypotheses discharge down to a concrete staggered panel.
-/

import Causalean.Panel.AdoptionPath
import Causalean.Panel.EstimandCharacterization.ImputationEventStudy.Imputation

/-! # BJS staggered-adoption grounding

Builds a `BJSPanel` from an adoption path and two-way fixed effects, and proves
the untreated-outcome model and fixed-effect hypotheses hold for it. Treated
cells are the cells whose treatment has switched on, untreated cells include
never-treated cells and pre-adoption cells, and the canonical two-way
fixed-effect design discharges the BJS hypotheses in a concrete panel.  The main
definitions are `TreatedCell`, `UntreatedCell`, `feRow`, and
`ofStaggeredTWFE`; the main theorem bridges are
`ofStaggeredTWFE_untreatedModel` and `ofStaggeredTWFE_treatmentFixed`. -/

namespace Causalean
namespace Panel.EstimandCharacterization
namespace ImputationEventStudy

open Causalean.Panel

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I] {T : ℕ}
  (g : I → WithTop (Fin T))

/-- Cells whose treatment has switched on by period `t` (`g i ≤ t`). -/
def TreatedCell : Type _ :=
  { c : I × Fin T // AdoptionPath.le (g c.1) c.2 }

/-- Cells still untreated at period `t` (`t < g i`).  Includes every cell of a
never-treated unit and every pre-adoption cell of a treated unit. -/
def UntreatedCell : Type _ :=
  { c : I × Fin T // AdoptionPath.lt (g c.1) c.2 }

/-- The treated-cell predicate is decidable for each unit-period cell. -/
instance : DecidablePred (fun c : I × Fin T => AdoptionPath.le (g c.1) c.2) := by
  intro c; unfold AdoptionPath.le; infer_instance

/-- The untreated-cell predicate is decidable for each unit-period cell. -/
instance : DecidablePred (fun c : I × Fin T => AdoptionPath.lt (g c.1) c.2) := by
  intro c; unfold AdoptionPath.lt; infer_instance

/-- The treated cells form a finite type whenever units and periods are finite. -/
instance : Fintype (TreatedCell g) := by unfold TreatedCell; infer_instance
/-- The untreated cells form a finite type whenever units and periods are finite. -/
instance : Fintype (UntreatedCell g) := by unfold UntreatedCell; infer_instance

omit [Fintype I] [DecidableEq I] in
/-- The cell partition is exclusive: no cell is both adopted-by-`t` and
untreated-at-`t`. -/
theorem treated_not_untreated {c : I × Fin T}
    (hT : AdoptionPath.le (g c.1) c.2) (hU : AdoptionPath.lt (g c.1) c.2) : False :=
  AdoptionPath.not_le_of_lt hU hT

omit [Fintype I] [DecidableEq I] in
/-- The cell partition is exhaustive: every cell is treated or untreated. -/
theorem treated_or_untreated (c : I × Fin T) :
    AdoptionPath.le (g c.1) c.2 ∨ AdoptionPath.lt (g c.1) c.2 := by
  unfold AdoptionPath.le AdoptionPath.lt
  rcases lt_trichotomy (g c.1) (c.2 : WithTop (Fin T)) with h | h | h
  · exact Or.inl (le_of_lt h)
  · exact Or.inl (le_of_eq h)
  · exact Or.inr h

/-- Two-way fixed-effect design row for cell `(i,t)`: the unit-`i` indicator on
the `I` block stacked with the time-`t` indicator on the `Fin T` block. -/
def feRow (c : I × Fin T) : (I ⊕ Fin T) → ℝ :=
  Sum.elim (fun i' => if i' = c.1 then (1 : ℝ) else 0)
    (fun t' => if t' = c.2 then (1 : ℝ) else 0)

/-- The two-way FE row evaluates the additive fixed-effect model:
`q_{(i,t)} · (α, λ) = α_i + λ_t`. -/
lemma dot_feRow (c : I × Fin T) (α : I → ℝ) (lam : Fin T → ℝ) :
    dot (feRow c) (Sum.elim α lam) = α c.1 + lam c.2 := by
  unfold dot feRow
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- **Grounding constructor.**  From an adoption path `g`, unit effects `α`, time
effects `λ`, target weights `a`, and treated-cell effects `τ`, build the
`BJSPanel` whose treated/untreated cells are the staggered-adoption partition of
`I × Fin T` and whose regressors are the two-way fixed effects.  The
untreated-outcome model `E[Y(0)] = α_i + λ_t`, no anticipation, and the
fixed-effect equation all hold definitionally. -/
def ofStaggeredTWFE (α : I → ℝ) (lam : Fin T → ℝ)
    (a tau : TreatedCell g → ℝ) :
    BJSPanel (TreatedCell g) (UntreatedCell g) (I ⊕ Fin T) where
  qT := fun c => feRow c.val
  qU := fun u => feRow u.val
  a := a
  EY_T := fun c => (α c.val.1 + lam c.val.2) + tau c
  EY_U := fun u => α u.val.1 + lam u.val.2
  EY0_T := fun c => α c.val.1 + lam c.val.2
  EY0_U := fun u => α u.val.1 + lam u.val.2
  beta0 := Sum.elim α lam
  tau := tau

/-- The grounded panel satisfies the BJS untreated-outcome model: both treated
and untreated cell means equal the two-way FE model `α_i + λ_t`, and untreated
cells have no anticipation. -/
theorem ofStaggeredTWFE_untreatedModel (α : I → ℝ) (lam : Fin T → ℝ)
    (a tau : TreatedCell g → ℝ) :
    (ofStaggeredTWFE g α lam a tau).UntreatedOutcomeModel := by
  refine ⟨fun c => ?_, fun u => ?_, fun _ => rfl⟩
  · change α c.val.1 + lam c.val.2 = dot (feRow c.val) (Sum.elim α lam)
    rw [dot_feRow]
  · change α u.val.1 + lam u.val.2 = dot (feRow u.val) (Sum.elim α lam)
    rw [dot_feRow]

/-- The grounded panel satisfies the BJS fixed-effect equation
`E[Y_T] = E[Y_T(0)] + τ`. -/
theorem ofStaggeredTWFE_treatmentFixed (α : I → ℝ) (lam : Fin T → ℝ)
    (a tau : TreatedCell g → ℝ) :
    (ofStaggeredTWFE g α lam a tau).TreatmentEffectFixed :=
  fun _ => rfl

end

end ImputationEventStudy
end Panel.EstimandCharacterization
end Causalean
