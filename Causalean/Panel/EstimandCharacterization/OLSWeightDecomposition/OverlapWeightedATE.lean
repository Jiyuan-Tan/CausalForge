/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Słoczyński (2022): the finite-cell overlap-weighted ATE headline

This file states the finite-cell headline theorem: the saturated-OLS
residualized coefficient equals the overlap-weighted ATE built from real
potential outcomes. The supporting measure-theoretic machinery lives in the
`Support/` subfolder:

* `Support.Basic` — saturated class, cell statistics, and elementary bounds.
* `Support.Integrals` — reusable cell integral identities.
* `Support.Orthogonality` — per-cell orthogonality and observed-outcome L².
* `Support.Partition` — finite partition and residualization witnesses.
* `Support.PerCell` — denominator and numerator per-cell bridge identities.
-/

import Causalean.Panel.EstimandCharacterization.OLSWeightDecomposition.Support.PerCell
/-! # Słoczyński finite-cell overlap-weighted ATE (headline)

This file holds the finite-cell **headline theorem** of the module: starting
from a probability space with a binary treatment, potential outcomes, and a
finite covariate `G`, the saturated-OLS residualized coefficient is identified
with the overlap-weighted average treatment effect
`Σ ω_g · E[Y(1)−Y(0) ∣ G=g]`. This is where the abstract `FinitePartition`
algebra acquires its causal content; the `Support/` files provide the
per-cell measure-theoretic machinery. The continuous-covariate counterpart is
`GeneralCondExp.lean`. -/

namespace Causalean.Panel.EstimandCharacterization.OLSWeightDecomposition

open MeasureTheory Finset Causalean.Panel
open scoped BigOperators

/-- Finite-cell saturated-OLS bridge to the overlap-weighted average treatment
effect.

Given a probability space `(Ω, μ)` with a binary treatment `D`, an
observed outcome `Y` consistent with potential outcomes `Y0, Y1`, and a
finite covariate `G : Ω → 𝒢` satisfying the finite-cell bridge condition
`B_CMI` and nondegenerate overlap (`B_overlap`), the saturated-OLS
residualized coefficient equals the overlap-weighted ATE:

    residualizedCoefficient μ (saturatedClass μ G B_meas_G)
        (residWitnessY μ Y G B_meas_G ...)
        (residWitnessD μ D G B_meas_G B_meas_D B_binary)
      = overlapWeightedATE
            (partitionOf μ D Y0 Y1 G B_meas_G B_binary B_overlap).

`Y_memLp` is derived internally from `B_consis`, `B_binary`, `B_Y0_L2`, and
`B_Y1_L2` via `Y_memLp_of_consistency`. The denominator positivity
`0 < ∫ D̃² dμ` is derived from `B_overlap` via the per-cell denominator sum
`hDen_sum`, so no separate residual-variation hypothesis is needed.

Here `B_CMI` is the integrated-indicator finite-cell bridge condition implied
by the usual conditional-mean independence clause `E[Y(d) | D, G] = E[Y(d) | G]`
(this is a strictly weaker operational substitute on a finite-cell partition,
sufficient for the proof but not equivalent to full CMI).

This finite-cell statement is the finite-partition corollary formalized without
importing `Mathlib.MeasureTheory.Function.ConditionalExpectation.*`.

Proof sketch: per-cell denominator (`denom_per_cell`) and numerator
(`num_per_cell`) identities sum to the FWL ratio; replacing `Y` with
`wY.Vtilde` is harmless via `wD.orthogonal` against
`wY.VH = meanReg μ Y G`. The finite-partition algebra object on the right side has
`π_g = cellMass g`, `p_g = cellShare g`, `τ_g = cellTau g` by
construction in `partitionOf`, so the ratio equality is immediate. -/
theorem bridge_finite_residualized_eq_overlap
    {Ω 𝒢 : Type*} [MeasurableSpace Ω] [Fintype 𝒢]
    [DecidableEq 𝒢] [MeasurableSpace 𝒢] [MeasurableSingletonClass 𝒢]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (D Y Y0 Y1 : Ω → ℝ) (G : Ω → 𝒢)
    (B_meas_G : Measurable G)
    (B_meas_D : Measurable D)
    (B_binary : ∀ᵐ ω ∂μ, D ω = 0 ∨ D ω = 1)
    (B_Y0_L2 : MemLp Y0 2 μ)
    (B_Y1_L2 : MemLp Y1 2 μ)
    (B_consis : Y =ᵐ[μ] fun ω => D ω * Y1 ω + (1 - D ω) * Y0 ω)
    -- Finite-cell bridge condition implied by the usual CMI clause
    -- `E[Y(d) | D, G] = E[Y(d) | G]`; this integrated-indicator form is used
    -- directly in the cell algebra and is not stated as an equivalence to CMI.
    (B_CMI : ∀ (d : ℝ) (g : 𝒢), d = 0 ∨ d = 1 →
      ∫ ω, (if d = 1 then Y1 ω else Y0 ω)
              * Set.indicator {ω' | D ω' = d} (fun _ => (1 : ℝ)) ω
              * Set.indicator {ω' | G ω' = g} (fun _ => (1 : ℝ)) ω ∂μ
        = (∫ ω, (if d = 1 then Y1 ω else Y0 ω)
                  * Set.indicator {ω' | G ω' = g} (fun _ => (1 : ℝ)) ω ∂μ)
            * (if d = 1 then cellShare μ D G g else 1 - cellShare μ D G g))
    (B_overlap : 0 < ∑ g, cellMass μ G g
                        * (cellShare μ D G g * (1 - cellShare μ D G g))) :
    residualizedCoefficient μ (saturatedClass μ G B_meas_G)
        (residWitnessY μ Y G B_meas_G
          -- `Y_memLp` is derived from consistency, binary treatment, and the two
          -- potential-outcome square-integrability assumptions.
          (Y_memLp_of_consistency μ B_meas_D B_binary B_Y0_L2 B_Y1_L2 B_consis))
        (residWitnessD μ D G B_meas_G B_meas_D B_binary)
      = FinitePartition.overlapWeightedATE
          (partitionOf μ D Y0 Y1 G B_meas_G B_meas_D B_binary B_overlap) := by
  -- Bring derived Y_memLp into scope by name for readability.
  have Y_memLp : MemLp Y 2 μ :=
    Y_memLp_of_consistency μ B_meas_D B_binary B_Y0_L2 B_Y1_L2 B_consis
  let H := saturatedClass μ G B_meas_G
  let wY := residWitnessY μ Y G B_meas_G Y_memLp
  let wD := residWitnessD μ D G B_meas_G B_meas_D B_binary
  let P := partitionOf μ D Y0 Y1 G B_meas_G B_meas_D B_binary B_overlap
  have hMeanReg_mem : H.mem (meanReg μ Y G) :=
    meanReg_mem_saturatedClass μ Y G B_meas_G
  have hNum_tilde :
      ∫ ω, wD.Vtilde ω * wY.Vtilde ω ∂μ =
        ∫ ω, wD.Vtilde ω * Y ω ∂μ := by
    have hDY_int : Integrable (fun ω => wD.Vtilde ω * Y ω) μ :=
      wD.Vtilde_memLp.integrable_mul Y_memLp
    have hDM_int : Integrable (fun ω => wD.Vtilde ω * meanReg μ Y G ω) μ :=
      wD.Vtilde_memLp.integrable_mul (H.memLp hMeanReg_mem)
    calc
      ∫ ω, wD.Vtilde ω * wY.Vtilde ω ∂μ =
          ∫ ω, wD.Vtilde ω * Y ω
            - wD.Vtilde ω * meanReg μ Y G ω ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards [] with ω
        simp [wY, residWitnessY]
        ring
      _ = ∫ ω, wD.Vtilde ω * Y ω ∂μ
          - ∫ ω, wD.Vtilde ω * meanReg μ Y G ω ∂μ :=
        integral_sub hDY_int hDM_int
      _ = ∫ ω, wD.Vtilde ω * Y ω ∂μ := by
        rw [wD.orthogonal hMeanReg_mem]
        ring
  have hDen_sum :
      ∫ ω, wD.Vtilde ω * wD.Vtilde ω ∂μ =
        ∑ g, cellMass μ G g
          * (cellShare μ D G g * (1 - cellShare μ D G g)) := by
    have hF_int : Integrable (fun ω => wD.Vtilde ω * wD.Vtilde ω) μ :=
      wD.Vtilde_memLp.integrable_mul wD.Vtilde_memLp
    calc
      ∫ ω, wD.Vtilde ω * wD.Vtilde ω ∂μ =
          ∑ g, ∫ ω, (wD.Vtilde ω * wD.Vtilde ω)
            * Set.indicator {ω' | G ω' = g} (fun _ => (1 : ℝ)) ω ∂μ :=
        integral_eq_sum_cell μ (fun ω => wD.Vtilde ω * wD.Vtilde ω)
          G B_meas_G hF_int
      _ = ∑ g, cellMass μ G g
          * (cellShare μ D G g * (1 - cellShare μ D G g)) := by
        refine Finset.sum_congr rfl (fun g _ => ?_)
        simpa [wD, residWitnessD, mul_assoc] using
          denom_per_cell μ D G B_meas_G B_meas_D B_binary g
  have hNum_sum :
      ∫ ω, wD.Vtilde ω * Y ω ∂μ =
        ∑ g, cellMass μ G g
          * (cellShare μ D G g * (1 - cellShare μ D G g))
          * cellTau μ Y0 Y1 G g := by
    have hF_int : Integrable (fun ω => wD.Vtilde ω * Y ω) μ :=
      wD.Vtilde_memLp.integrable_mul Y_memLp
    calc
      ∫ ω, wD.Vtilde ω * Y ω ∂μ =
          ∑ g, ∫ ω, (wD.Vtilde ω * Y ω)
            * Set.indicator {ω' | G ω' = g} (fun _ => (1 : ℝ)) ω ∂μ :=
        integral_eq_sum_cell μ (fun ω => wD.Vtilde ω * Y ω)
          G B_meas_G hF_int
      _ = ∑ g, cellMass μ G g
          * (cellShare μ D G g * (1 - cellShare μ D G g))
          * cellTau μ Y0 Y1 G g := by
        refine Finset.sum_congr rfl (fun g _ => ?_)
        simpa [wD, residWitnessD, mul_assoc] using
          num_per_cell μ D Y Y0 Y1 G B_meas_G B_meas_D B_binary
            B_Y0_L2 B_Y1_L2 B_consis B_CMI g
  -- Derive residual-variation positivity from overlap via `hDen_sum`.
  -- `hDen_sum` rewrites `∫ wD.Vtilde^2 dμ` to the cell-sum form, which
  -- equals B_overlap. No separate B_Dtilde_pos hypothesis needed.
  have hOverlapDen_ne :
      (∑ g, cellMass μ G g
        * (cellShare μ D G g * (1 - cellShare μ D G g))) ≠ 0 :=
    B_overlap.ne'
  have hP :
      FinitePartition.overlapWeightedATE P =
        (∑ g, cellMass μ G g
          * (cellShare μ D G g * (1 - cellShare μ D G g))
          * cellTau μ Y0 Y1 G g)
        / (∑ g, cellMass μ G g
          * (cellShare μ D G g * (1 - cellShare μ D G g))) := by
    simp [P, partitionOf, FinitePartition.overlapWeightedATE,
      FinitePartition.overlapNumerator, FinitePartition.overlapDenominator,
      FinitePartition.cellOverlap, mul_assoc]
  have _ := hOverlapDen_ne
  calc
    residualizedCoefficient μ (saturatedClass μ G B_meas_G)
        (residWitnessY μ Y G B_meas_G Y_memLp)
        (residWitnessD μ D G B_meas_G B_meas_D B_binary)
        = (∫ ω, wD.Vtilde ω * wY.Vtilde ω ∂μ)
          / (∫ ω, wD.Vtilde ω * wD.Vtilde ω ∂μ) := by
      rfl
    _ = (∫ ω, wD.Vtilde ω * Y ω ∂μ)
          / (∫ ω, wD.Vtilde ω * wD.Vtilde ω ∂μ) := by
      rw [hNum_tilde]
    _ = (∑ g, cellMass μ G g
          * (cellShare μ D G g * (1 - cellShare μ D G g))
          * cellTau μ Y0 Y1 G g)
        / (∑ g, cellMass μ G g
          * (cellShare μ D G g * (1 - cellShare μ D G g))) := by
      rw [hNum_sum, hDen_sum]
    _ = FinitePartition.overlapWeightedATE
          (partitionOf μ D Y0 Y1 G B_meas_G B_meas_D B_binary B_overlap) := by
      rw [hP]

end Causalean.Panel.EstimandCharacterization.OLSWeightDecomposition
