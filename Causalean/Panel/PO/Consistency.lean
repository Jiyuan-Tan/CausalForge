/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Panel consistency

Consistency is an assumption relating independently stored factual outcomes to
the corresponding potential outcomes at the realized exposure.  It is stated
only for observed cells `r ∈ R`, the support on which the panel records
outcomes and weights.
-/

import Causalean.Panel.PO.CellPO

/-! # Panel Consistency

This file states the panel consistency property for a `PanelPOSystem`. The
predicate `PanelPOSystem.observedY_eq_potentialOutcome` is the pointwise
observed-cell equality, while `PanelConsistency` requires it for every observed
cell and sample point. The lemma `panelConsistency_holds` exposes the equality
directly from the assumption. -/

namespace Causalean
namespace Panel

namespace PanelPOSystem

variable (P : PanelPOSystem)

/-- Pointwise consistency at a given observed cell is the equality between the
factual observed outcome and the potential outcome indexed by the realized exposure. -/
def observedY_eq_potentialOutcome (r : P.I × P.T) (hr : r ∈ P.cells.observed)
    (ω : P.Ω) : Prop :=
  P.observedY r hr ω = P.Y r hr (P.observedExposure r hr ω) ω

end PanelPOSystem

/-- Panel consistency says that on every observed unit-period cell, the factual
outcome equals the potential outcome evaluated at the realized exposure. -/
def PanelConsistency (P : PanelPOSystem) : Prop :=
  ∀ (r : P.I × P.T) (hr : r ∈ P.cells.observed) (ω : P.Ω),
    P.observedY_eq_potentialOutcome r hr ω

/-- If panel consistency is assumed, then the factual observed outcome equals the
potential outcome at the realized exposure for every observed cell and sample point. -/
lemma panelConsistency_holds (P : PanelPOSystem) (hP : PanelConsistency P) :
    ∀ (r : P.I × P.T) (hr : r ∈ P.cells.observed) (ω : P.Ω),
      P.observedY r hr ω = P.Y r hr (P.observedExposure r hr ω) ω :=
  hP

end Panel
end Causalean
