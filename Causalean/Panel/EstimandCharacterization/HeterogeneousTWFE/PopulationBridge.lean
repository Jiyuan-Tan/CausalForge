/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# DCDH cell consistency from a potential-outcome contrast

Supplies the population origin of the `DCDHPanel.consistency` field at the level
of cell-conditional means, connecting the finite treatment-effect field to an
actual potential-outcome contrast.

On a group-time cell event `A` where treatment is constant `D ≡ d ∈ {0,1}` and
potential-outcome consistency `Y = Y0 + D·(Y1 − Y0)` holds pointwise, the raw
cell event quotients satisfy the DCDH consistency identity
`Ȳ = Ȳ(0) + d·(Ȳ(1) − Ȳ(0))`, where the treatment-effect field is defined as the
difference between the `Y1` and `Y0` cell quotients.

This is *hypothesis-driven*: it takes the probability model `(μ, A, Y, Y0, Y1)`
and the pointwise consistency hypothesis (PO consistency restricted to the cell),
and discharges the consistency identity for the population cell means.  No paper
assumption is strengthened — `hcons` is exactly the paper's consistency axiom
`Y = Y(0) + D·(Y(1) − Y(0))`, while this constructor leaves any integrability
interpretation of those quotients to separate hypotheses or corollaries.
-/

import Causalean.Panel.EstimandCharacterization.HeterogeneousTWFE.FinitePanel
import Causalean.Panel.PO.PopulationCells

/-! # DCDH Population Bridge

This file connects the finite DCDH panel fields to a probability model with cell
events and potential outcomes.  The constructor `DCDHPanel.ofPopulation` builds a
finite panel whose cell weights are cell probabilities, whose `Y` and `Y0` fields
are population cell means, and whose `tau` field is the difference between the
`Y1` and `Y0` cell means.  Its `consistency` and `pi_sum_one` fields are derived
from the shared cell-partition mean-consistency and finite-partition mass
identities. -/

namespace Causalean
namespace Panel.EstimandCharacterization
namespace HeterogeneousTWFE

open MeasureTheory Causalean.PO

/-- Builds a finite DCDH panel from a population model.

The construction starts from a probability model with a finite partition into
group-time cells, factual and potential outcomes, and a binary cell-level
treatment.  The panel's outcomes are the population cell-conditional means:
`Y` is the factual cell mean, `Y0` is the untreated-potential cell mean, and
`tau` is the difference between the treated- and untreated-potential cell means.
The cell weights are the cell probabilities `pi g t = μ(cell g t)`.  The
`consistency` field is *derived* from pointwise potential-outcome consistency on
each cell via the shared `CellPartition.mean_consistency`, and `pi_sum_one` from
the shared `CellPartition.mass_sum_one` finite-partition additivity. The cell
statistics `pi`, `Y`, `Y0`, `tau` are the shared `CellPartition.mass` / `.mean`
over the cohort-period partition.

As in the base `DCDHPanel`, the residualized treatment `Dtilde` (and its
orthogonality / nonzero-variation properties) is supplied as a witness: deriving
the Frisch-Waugh-Lovell residual for *general* cell weights is a separate
construction (the uniform-weight case is `DCDHPanel.ofTwoWayPanel` in
`FWLBridge.lean`).  This constructor exhibits `tau` as the potential-outcome
contrast `Y(1) − Y(0)` inside an actual `DCDHPanel`. -/
noncomputable def DCDHPanel.ofPopulation
    {G T : Type*} [Fintype G] [Fintype T]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (cellEvent : G → T → Set Ω)
    (Yfac Y0pop Y1pop : Ω → ℝ) (d : G → T → ℝ) (Dtilde : G → T → ℝ)
    (hmeas : ∀ g t, MeasurableSet (cellEvent g t))
    (hdisj : Pairwise (Function.onFun Disjoint (fun p : G × T => cellEvent p.1 p.2)))
    (hcov : (⋃ p : G × T, cellEvent p.1 p.2) = Set.univ)
    (hpos : ∀ g t, 0 < (μ (cellEvent g t)).toReal)
    (hdbin : ∀ g t, d g t = 0 ∨ d g t = 1)
    (hcons : ∀ g t, ∀ ω ∈ cellEvent g t,
        Yfac ω = Y0pop ω + d g t * (Y1pop ω - Y0pop ω))
    (hDmem : IsGTFE (fun g t => d g t - Dtilde g t))
    (hDorth : ∀ h : G → T → ℝ, IsGTFE h →
        ∑ g, ∑ t, (μ (cellEvent g t)).toReal * Dtilde g t * h g t = 0)
    (hSD : 0 < ∑ g, ∑ t, (μ (cellEvent g t)).toReal * (Dtilde g t) ^ 2) :
    DCDHPanel G T :=
  let cells : Causalean.Panel.PO.CellPartition μ (G × T) :=
    { cell := fun p => cellEvent p.1 p.2
      cell_meas := fun p => hmeas p.1 p.2
      cell_disj := hdisj
      cell_cov := hcov
      cell_pos := fun p => hpos p.1 p.2 }
  { pi := fun g t => cells.mass (g, t)
    D := d
    Y := fun g t => cells.mean Yfac (g, t)
    Y0 := fun g t => cells.mean Y0pop (g, t)
    tau := fun g t => cells.mean Y1pop (g, t) - cells.mean Y0pop (g, t)
    Dtilde := Dtilde
    pi_pos := hpos
    pi_sum_one := by
      rw [← Fintype.sum_prod_type]; exact cells.mass_sum_one
    D_binary := hdbin
    consistency := fun g t =>
      cells.mean_consistency (g, t) Yfac Y0pop Y1pop (hdbin g t) (hcons g t)
    D_minus_resid_mem := hDmem
    Dtilde_orthogonal := hDorth
    SD_pos := hSD }

end HeterogeneousTWFE
end Panel.EstimandCharacterization
end Causalean
