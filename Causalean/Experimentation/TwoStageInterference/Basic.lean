/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Experimentation.DesignBased.TwoStage

/-! # Hudgens–Halloran (2008): two-stage interference setup, estimands, estimators

This file formalizes the design layer for Hudgens & Halloran (2008), "Toward Causal Inference With
Interference."  The population is partitioned into groups; each unit's potential outcome may depend
on treatment assignments within its own group, but not on assignments in other groups.

Randomization is two-stage (Assumption 1): a first-stage design decides which groups receive
allocation strategy ψ versus φ; conditionally, each group is randomized by its assigned within-group
design.  The joint law combines the first-stage design with the per-group product design, so
cross-group independence is structural.

This file fixes the public vocabulary used by the rest of the subtree: assignment spaces
`WAssign` and `StratAssign`, the compound two-stage design `jointDesign`, average-potential-outcome
estimands `indMean`, `groupMean`, `popMean`, `indMarg`, and `popMarg`, causal contrasts
`CE_direct`, `CE_indirect`, `CE_total`, and `CE_overall`, and the estimators `groupEst`,
`popEst`, and `estDirect`.  The unbiasedness and variance theorems for these definitions live in
`Unbiased.lean`, `Effects.lean`, `BetweenGroup.lean`, and `Variance.lean`.
-/

open scoped BigOperators
open Finset

namespace Causalean
namespace Experimentation
namespace TwoStageInterference

open DesignBased

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {n : ι → ℕ}

/-- Within-group assignment space for group `i`: a `{treated/untreated}` flag per unit. -/
abbrev WAssign (n : ι → ℕ) (i : ι) := Fin (n i) → Bool

/-- Stage-1 strategy assignment space: each group is flagged ψ (`true`) or φ (`false`). -/
abbrev StratAssign (ι : Type*) := ι → Bool

/-- The joint two-stage design: stage-1 design `D₁` over strategy assignments, then,
conditionally, group `i` is randomized by `ψ i` if assigned ψ and by `φ i` otherwise. -/
noncomputable def jointDesign (D₁ : FiniteDesign (StratAssign ι))
    (ψ φ : ∀ i, FiniteDesign (WAssign n i)) :
    FiniteDesign (StratAssign ι × ∀ i, WAssign n i) :=
  compound D₁ (fun s i => if s i then ψ i else φ i)

/-! ### Estimands (population average potential outcomes) -/

/-- **Individual average potential outcome** `ȳ_ij(z;ρ)`: unit `(i,j)`'s expected outcome
under within-group design `ρ`, conditional on its own treatment being `z`. -/
noncomputable def indMean (ρ : ∀ i, FiniteDesign (WAssign n i))
    (Y : ∀ i, Fin (n i) → WAssign n i → ℝ) (i : ι) (j : Fin (n i)) (z : Bool) : ℝ :=
  (ρ i).E (fun w => if w j = z then Y i j w else 0) / (ρ i).Pr (fun w => w j = z)

/-- **Group average potential outcome** `ȳ_i(z;ρ) = (1/nᵢ)∑ⱼ ȳ_ij(z;ρ)`. -/
noncomputable def groupMean (ρ : ∀ i, FiniteDesign (WAssign n i))
    (Y : ∀ i, Fin (n i) → WAssign n i → ℝ) (i : ι) (z : Bool) : ℝ :=
  (∑ j, indMean ρ Y i j z) / (n i : ℝ)

/-- **Population average potential outcome** `ȳ(z;ρ) = (1/N)∑ᵢ ȳ_i(z;ρ)`. -/
noncomputable def popMean (ρ : ∀ i, FiniteDesign (WAssign n i))
    (Y : ∀ i, Fin (n i) → WAssign n i → ℝ) (z : Bool) : ℝ :=
  (∑ i, groupMean ρ Y i z) / (Fintype.card ι : ℝ)

/-- **Marginal individual average potential outcome** `ȳ_ij(ρ)`: expected outcome of `(i,j)`
under design `ρ`, averaging over its own treatment as well (the overall-effect target). -/
noncomputable def indMarg (ρ : ∀ i, FiniteDesign (WAssign n i))
    (Y : ∀ i, Fin (n i) → WAssign n i → ℝ) (i : ι) (j : Fin (n i)) : ℝ :=
  (ρ i).E (fun w => Y i j w)

/-- **Population marginal average potential outcome** `ȳ(ρ) = (1/N)∑ᵢ(1/nᵢ)∑ⱼ ȳ_ij(ρ)`. -/
noncomputable def popMarg (ρ : ∀ i, FiniteDesign (WAssign n i))
    (Y : ∀ i, Fin (n i) → WAssign n i → ℝ) : ℝ :=
  (∑ i, (∑ j, indMarg ρ Y i j) / (n i : ℝ)) / (Fintype.card ι : ℝ)

/-- **Hudgens-Halloran direct-effect contrast.** This is the population average outcome under
treatment minus the population average outcome under control, evaluated under the strategy ψ. -/
noncomputable def CE_direct (ψ : ∀ i, FiniteDesign (WAssign n i))
    (Y : ∀ i, Fin (n i) → WAssign n i → ℝ) : ℝ :=
  popMean ψ Y true - popMean ψ Y false

/-- **Indirect (spillover) causal effect** `C̄E^I(φ,ψ) = ȳ(0;φ) − ȳ(0;ψ)`. -/
noncomputable def CE_indirect (ψ φ : ∀ i, FiniteDesign (WAssign n i))
    (Y : ∀ i, Fin (n i) → WAssign n i → ℝ) : ℝ :=
  popMean φ Y false - popMean ψ Y false

/-- **Total causal effect** `C̄E^T(φ,ψ) = ȳ(0;φ) − ȳ(1;ψ)`.

Sign convention note: this is the control-minus-treatment orientation, negated
relative to the Hudgens-Halloran (2008) treatment-minus-control total effect. -/
noncomputable def CE_total (ψ φ : ∀ i, FiniteDesign (WAssign n i))
    (Y : ∀ i, Fin (n i) → WAssign n i → ℝ) : ℝ :=
  popMean φ Y false - popMean ψ Y true

/-- **Overall causal effect** `C̄E^O(φ,ψ) = ȳ(φ) − ȳ(ψ)`.

Sign convention note: this keeps the file's control-minus-treatment orientation,
negated relative to the Hudgens-Halloran (2008) overall-effect convention. -/
noncomputable def CE_overall (ψ φ : ∀ i, FiniteDesign (WAssign n i))
    (Y : ∀ i, Fin (n i) → WAssign n i → ℝ) : ℝ :=
  popMarg φ Y - popMarg ψ Y

/-! ### Estimators -/

/-- **Within-group estimator** `Ŷ_i(z;ρ)`: the empirical mean outcome among the `m`
units of group `i` whose own treatment equals `z`, as a function of the realized within-group
assignment `w`.  The denominator `m` is the (design-fixed) number of such units. -/
noncomputable def groupEst (Y : ∀ i, Fin (n i) → WAssign n i → ℝ)
    (i : ι) (z : Bool) (m : ℝ) (w : WAssign n i) : ℝ :=
  (∑ j, if w j = z then Y i j w else 0) / m

/-- **Population estimator** `Ŷ(z;ρ)` on the groups assigned strategy `pick`: the average of
the within-group estimators over the `denom` groups with `s i = pick`, as a function of the
realized joint assignment `(s, w)`.  `m i` is the design-fixed count of `z`-units in group `i`. -/
noncomputable def popEst (Y : ∀ i, Fin (n i) → WAssign n i → ℝ)
    (z : Bool) (pick : Bool) (m : ι → ℝ) (denom : ℝ)
    (sw : StratAssign ι × ∀ i, WAssign n i) : ℝ :=
  (∑ i, if sw.1 i = pick then groupEst Y i z (m i) (sw.2 i) else 0) / denom

/-- The Horvitz-Thompson estimator of the treatment-minus-control direct-effect contrast on the
ψ-groups: the estimated treatment mean minus the estimated control mean. -/
noncomputable def estDirect (Y : ∀ i, Fin (n i) → WAssign n i → ℝ)
    (m0 m1 : ι → ℝ) (denom : ℝ) (sw : StratAssign ι × ∀ i, WAssign n i) : ℝ :=
  popEst Y true true m1 denom sw - popEst Y false true m0 denom sw

end TwoStageInterference
end Experimentation
end Causalean
