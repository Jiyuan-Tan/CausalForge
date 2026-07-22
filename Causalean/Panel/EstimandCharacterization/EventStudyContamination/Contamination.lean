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

/-- **Contamination representation (genuine).** From the cell-grid weighted
projection input, the conventional event-study coefficient is the
contamination-weighted sum of cohort-relative-time CATTs. -/
theorem contamination_representation_of_cellGrid
    (hCausal : P.EventStudyCausalRestrictions)
    (hSupport : P.ConventionalFiniteSupport D)
    (hCell : P.CellGridResidualization D) :
    D.mu =
      ∑ ge ∈ P.admissibleCells D.eventSupport,
        P.omega D ge.1 ge.2 * P.CATT ge.1 ge.2 :=
  P.contamination_representation D hCausal (cellGrid_provides_residualization hCell)
    hCell.hDenomPos (cellGrid_mu_eq_conventionalMuRatio hCell) hSupport

/-- **Contamination split (genuine).** Displayed-event-time component plus
off-diagonal contamination, from the cell-grid projection input. -/
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
  P.contamination_representation_split D hCausal (cellGrid_provides_residualization hCell)
    hCell.hDenomPos (cellGrid_mu_eq_conventionalMuRatio hCell) hSupport

/-- **Apparent pretrends (genuine).** For a displayed lead, the coefficient is a
weighted sum of post-treatment CATTs, from the cell-grid projection input. -/
theorem apparent_pretrends_from_post_treatment_of_cellGrid
    (hCausal : P.EventStudyCausalRestrictions)
    (hSupport : P.ConventionalFiniteSupport D)
    (hCell : P.CellGridResidualization D)
    (hLead : D.displayedEvent < 0) :
    D.mu =
      ∑ ge ∈ (P.admissibleCells D.eventSupport).filter (fun ge => 0 ≤ ge.2),
        P.omega D ge.1 ge.2 * P.CATT ge.1 ge.2 :=
  P.apparent_pretrends_from_post_treatment D hCausal (cellGrid_provides_residualization hCell)
    hCell.hDenomPos (cellGrid_mu_eq_conventionalMuRatio hCell) hSupport hLead

end EventStudySystem

end EventStudyContamination
end Panel.EstimandCharacterization
end Causalean
