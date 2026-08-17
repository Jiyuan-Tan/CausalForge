/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Sun-Abraham (2021): contamination representation

Public entry points for the conventional event-study contamination theorem.
Each takes a `CellGridResidualization` input, derives the
`ConventionalResidualization` orthogonality conditions and the identity
`D.mu = conventionalMuRatio` via the weighted cell-grid projection in
`CellGrid.lean`, then applies the finite-cell contamination algebra from
`Conventional.lean`.
-/

import Causalean.Panel.EstimandCharacterization.EventStudyContamination.CellGrid

/-! # Sun-Abraham Contamination Representation

This file provides the public contamination theorems for the conventional
Sun-Abraham event-study coefficient. It starts from the cell-grid weighted
projection, derives the needed residualization identities, and applies the
finite-cell algebra to obtain the displayed contamination formulas. -/

namespace Causalean
namespace Panel.EstimandCharacterization
namespace EventStudyContamination

namespace EventStudySystem

open Finset

variable {T : ℕ} {P : EventStudySystem T} {D : P.ConventionalDesign}

/-- **Contamination representation (genuine).** For the conventional event-study coefficient
`D.mu` of a design `D` on system `P`, if [observed outcomes equal the potential outcome under
the realized treatment path (consistency)](hyp:hConsistency), [the never-treated potential
outcome follows an additive parallel-trends restriction](hyp:hMeanParallelUntreated), [the
included, displayed, and admissible event times all lie within the declared finite
support](hyp:hSupport), and [the cell-grid weighted-projection residualization input is
supplied](hyp:hCell), then [`D.mu` equals the Sun-Abraham contamination-weighted sum of
cohort-relative-time CATTs over every admissible cell](goal). -/
theorem contamination_representation_of_cellGrid
    (hConsistency : P.Consistency) (hMeanParallelUntreated : P.MeanParallelUntreated)
    (hSupport : P.ConventionalFiniteSupport D)
    (hCell : P.CellGridResidualization D) :
    D.mu =
      ∑ ge ∈ P.admissibleCells D.eventSupport,
        P.omega D ge.1 ge.2 * P.CATT ge.1 ge.2 :=
  P.contamination_representation D hConsistency hMeanParallelUntreated
    (cellGrid_provides_residualization hCell.hCellMassPos hCell.hCellNonempty hCell.hRdotResidual).hResidualization
    hCell.hDenomPos (cellGrid_mu_eq_conventionalMuRatio hCell) hSupport

/-- **Contamination split (genuine).** For the conventional event-study coefficient `D.mu` of a
design `D` on system `P`, if [the consistency, mean-parallel-trends, and no-anticipation causal
restrictions hold](hyp:hCausal), [the included, displayed, and admissible event times all lie
within the declared finite support](hyp:hSupport), and [the cell-grid weighted-projection
residualization input is supplied](hyp:hCell), then [`D.mu` splits as the displayed-event-time
contamination term plus the contamination-weighted sum over every other admissible
cohort-relative-time cell](goal). -/
theorem contamination_representation_split_of_cellGrid
    (hCausal : P.EventStudyCausalRestrictions)
    (hSupport : P.ConventionalFiniteSupport D)
    (hCell : P.CellGridResidualization D) :
    D.mu =
      (∑ g ∈ P.cohortsAtEvent D.eventSupport D.displayedEvent,
        P.omega D g D.displayedEvent * P.CATT g D.displayedEvent) +
      (∑ ge ∈ (P.admissibleCells D.eventSupport).filter
          (fun ge => ge.2 ≠ D.displayedEvent),
        P.omega D ge.1 ge.2 * P.CATT ge.1 ge.2) :=
  P.contamination_representation_split D hCausal.hConsistency hCausal.hMeanParallelUntreated
    (cellGrid_provides_residualization hCell.hCellMassPos hCell.hCellNonempty hCell.hRdotResidual)
    hCell.hDenomPos (cellGrid_mu_eq_conventionalMuRatio hCell) hSupport

/-- **Apparent pretrends (genuine).** For the conventional event-study coefficient `D.mu` of a
design `D` on system `P`, if [the consistency, mean-parallel-trends, and no-anticipation causal
restrictions hold](hyp:hCausal), [the included, displayed, and admissible event times all lie
within the declared finite event-time support](hyp:hSupport), and [the cell-grid
weighted-projection residualization input is supplied](hyp:hCell), then [`D.mu` equals the
contamination-weighted sum of cohort-relative-time CATTs restricted to nonnegative relative
times — since no-anticipation forces every negative-relative-time CATT to vanish, this exhibits
`D.mu` as a weighted average of post-treatment effects](goal). -/
theorem apparent_pretrends_from_post_treatment_of_cellGrid
    (hCausal : P.EventStudyCausalRestrictions)
    (hSupport : P.ConventionalFiniteSupport D)
    (hCell : P.CellGridResidualization D) :
    D.mu =
      ∑ ge ∈ (P.admissibleCells D.eventSupport).filter (fun ge => 0 ≤ ge.2),
        P.omega D ge.1 ge.2 * P.CATT ge.1 ge.2 :=
  P.apparent_pretrends_from_post_treatment D hCausal
    (cellGrid_provides_residualization hCell.hCellMassPos hCell.hCellNonempty hCell.hRdotResidual).hResidualization
    hCell.hDenomPos (cellGrid_mu_eq_conventionalMuRatio hCell) hSupport

end EventStudySystem

end EventStudyContamination
end Panel.EstimandCharacterization
end Causalean
