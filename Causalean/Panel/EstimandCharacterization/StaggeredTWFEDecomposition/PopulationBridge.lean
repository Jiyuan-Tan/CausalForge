/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Goodman-Bacon (2021): TWFE decomposition under staggered timing — Layer B bridge

**Role in the folder.** *Population bridge.* Connects the finite `FinitePanel`
algebra to a real probability space — this is **statistical (population), not
causal**, meaning. The heavy cell algebra lives in the `Support/` subfolder;
this file states the public bridge theorems. See `StaggeredTWFEDecomposition.lean`
for the folder layer-map.

Layer B — measure-theoretic bridge from a probability space carrying the
balanced cohort-period law to the Layer A finite-cell `betaTWFE`. Mirrors
the Słoczyński Layer B file `Panel/EstimandCharacterization/OLSWeightDecomposition/OverlapWeightedATE.lean`
in its split structure:

* `Support.Basic` — saturated cohort + period class, cell statistics,
  in-class projections, basic positivity bounds.
* `Support.Integrals` — reusable cell integral identities (per-axis and
  per-cell mass identities, plus per-axis-to-whole-class orthogonality
  decoupler).
* `Support.Orthogonality` — per-axis orthogonality of the residuals
  against cohort and period indicators. Requires the balanced-cell
  hypothesis `IsBalancedPanelLaw`.
* `Support.Partition` — `panelOf` finite-cell panel and the residualization
  witnesses `residWitnessD_panel` / `residWitnessY_panel`.
* `Support.PerCell` — denominator and numerator per-cell bridge identities.

This file preserves the public import path and states the headline bridge
theorems.

NL artifact:
`doc/basic_concepts/po/estimand_characterization/goodman_bacon_twfe_timing.md`
("Layer B" section).
Source LaTeX:
`doc/basic_concepts/po/estimand_characterization/goodman_bacon_twfe_timing.tex`.
-/

import Causalean.Panel.EstimandCharacterization.StaggeredTWFEDecomposition.Support.PerCell

/-! # Goodman-Bacon Measure-Theoretic Bridge

This file states the public bridge from a probability-space panel model to the
finite Goodman-Bacon cohort-period algebra. It relates residualized-treatment
integrals to the finite-panel denominator and numerator, allowing the abstract
residualized coefficient to be read as the finite-cell TWFE coefficient under
the balanced cohort-period law. -/

namespace Causalean.Panel.EstimandCharacterization.StaggeredTWFEDecomposition

open MeasureTheory Finset Causalean.Panel
open scoped BigOperators

variable {Ω 𝒢 : Type*} [MeasurableSpace Ω] [Fintype 𝒢] [DecidableEq 𝒢]
  [MeasurableSpace 𝒢] [MeasurableSingletonClass 𝒢] {T : ℕ}

/-- The population FWL denominator equals the finite-cell Goodman-Bacon
denominator `VD`. -/
theorem bridge_Dtilde_sq_eq_VD
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (D Y : Ω → ℝ) (G : Ω → 𝒢) (T_rv : Ω → Fin T)
    (A : 𝒢 → WithTop (Fin T))
    (G_meas : Measurable G) (T_meas : Measurable T_rv)
    (D_meas : Measurable D)
    (D_binary : ∀ᵐ ω ∂μ, D ω = 0 ∨ D ω = 1)
    (B_balanced : IsBalancedPanelLaw μ G T_rv)
    (hT_pos : 0 < T)
    (hp_pos : ∀ g, 0 < cohortMass μ G g)
    (hp_sum : ∑ g, cohortMass μ G g = 1)
    (hLaw : ∀ g t,
      cellMass μ G T_rv g t = cohortMass μ G g / (T : ℝ))
    (hD_cell : ∀ g t, ∀ᵐ ω ∂μ.restrict {ω' | G ω' = g ∧ T_rv ω' = t},
      D ω = (∫ ω', D ω' * Set.indicator {ω' | G ω' = g ∧ T_rv ω' = t}
              (fun _ => (1 : ℝ)) ω' ∂μ) / cellMass μ G T_rv g t)
    (hDtilde_eq : ∀ g t,
      panelDtilde μ D G T_rv g t =
        Dtilde (panelOf μ Y G T_rv A hT_pos hp_pos hp_sum) g t) :
    (∫ ω, (residWitnessD_panel μ D G T_rv G_meas T_meas D_meas D_binary
              B_balanced).Vtilde ω
        * (residWitnessD_panel μ D G T_rv G_meas T_meas D_meas D_binary
              B_balanced).Vtilde ω ∂μ)
      = VD (panelOf μ Y G T_rv A hT_pos hp_pos hp_sum) := by
  let wD := residWitnessD_panel μ D G T_rv G_meas T_meas D_meas D_binary
    B_balanced
  let P := panelOf μ Y G T_rv A hT_pos hp_pos hp_sum
  have hDen_sum :
      ∫ ω, wD.Vtilde ω * wD.Vtilde ω ∂μ =
        ∑ g, ∑ t, cellMass μ G T_rv g t
          * (panelDtilde μ D G T_rv g t)^2 := by
    have hF_int : Integrable (fun ω => wD.Vtilde ω * wD.Vtilde ω) μ :=
      wD.Vtilde_memLp.integrable_mul wD.Vtilde_memLp
    calc
      ∫ ω, wD.Vtilde ω * wD.Vtilde ω ∂μ =
          ∑ g, ∑ t, ∫ ω, (wD.Vtilde ω * wD.Vtilde ω)
            * Set.indicator {ω' | G ω' = g ∧ T_rv ω' = t}
                (fun _ => (1 : ℝ)) ω ∂μ :=
        integral_eq_sum_panel_cell μ (fun ω => wD.Vtilde ω * wD.Vtilde ω)
          G T_rv G_meas T_meas hF_int
      _ = ∑ g, ∑ t, cellMass μ G T_rv g t
          * (panelDtilde μ D G T_rv g t)^2 := by
        refine Finset.sum_congr rfl (fun g _ => ?_)
        refine Finset.sum_congr rfl (fun t _ => ?_)
        simpa [wD, residWitnessD_panel, mul_assoc] using
          denom_per_cell_panel μ D G T_rv G_meas T_meas hD_cell g t
  calc
    ∫ ω, (residWitnessD_panel μ D G T_rv G_meas T_meas D_meas D_binary
              B_balanced).Vtilde ω
        * (residWitnessD_panel μ D G T_rv G_meas T_meas D_meas D_binary
              B_balanced).Vtilde ω ∂μ
        = ∫ ω, wD.Vtilde ω * wD.Vtilde ω ∂μ := by rfl
    _ = ∑ g, ∑ t, cellMass μ G T_rv g t
          * (panelDtilde μ D G T_rv g t)^2 := hDen_sum
    _ = VD P := by
      simp [P, panelOf, VD, hLaw, hDtilde_eq]

/-- The finite-cell denominator is positive if and only if the population FWL
denominator `∫ Vtilde² dμ` is positive.

Callers who already hold `hVD_pos : 0 < VD P` (from the Layer A side) can
derive `hDtilde_pos` automatically:
```
  (bridge_VD_pos_iff_Dtilde_sq_pos …).mpr hVD_pos
```
eliminating the need to supply `hDtilde_pos` as an independent hypothesis to
`bridge_finite_residualized_eq_twfe`. Previously callers had to supply both
`hVD_pos` and `hDtilde_pos` with no bridge between them. The equivalence is an
immediate rewrite via `bridge_Dtilde_sq_eq_VD`. -/
theorem bridge_VD_pos_iff_Dtilde_sq_pos
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (D Y : Ω → ℝ) (G : Ω → 𝒢) (T_rv : Ω → Fin T)
    (A : 𝒢 → WithTop (Fin T))
    (G_meas : Measurable G) (T_meas : Measurable T_rv)
    (D_meas : Measurable D)
    (D_binary : ∀ᵐ ω ∂μ, D ω = 0 ∨ D ω = 1)
    (B_balanced : IsBalancedPanelLaw μ G T_rv)
    (hT_pos : 0 < T)
    (hp_pos : ∀ g, 0 < cohortMass μ G g)
    (hp_sum : ∑ g, cohortMass μ G g = 1)
    (hLaw : ∀ g t,
      cellMass μ G T_rv g t = cohortMass μ G g / (T : ℝ))
    (hD_cell : ∀ g t, ∀ᵐ ω ∂μ.restrict {ω' | G ω' = g ∧ T_rv ω' = t},
      D ω = (∫ ω', D ω' * Set.indicator {ω' | G ω' = g ∧ T_rv ω' = t}
              (fun _ => (1 : ℝ)) ω' ∂μ) / cellMass μ G T_rv g t)
    (hDtilde_eq : ∀ g t,
      panelDtilde μ D G T_rv g t =
        Dtilde (panelOf μ Y G T_rv A hT_pos hp_pos hp_sum) g t) :
    0 < VD (panelOf μ Y G T_rv A hT_pos hp_pos hp_sum) ↔
      0 < ∫ ω, (residWitnessD_panel μ D G T_rv G_meas T_meas D_meas D_binary
                    B_balanced).Vtilde ω
              * (residWitnessD_panel μ D G T_rv G_meas T_meas D_meas D_binary
                    B_balanced).Vtilde ω ∂μ := by
  rw [bridge_Dtilde_sq_eq_VD μ D Y G T_rv A G_meas T_meas D_meas D_binary
        B_balanced hT_pos hp_pos hp_sum hLaw hD_cell hDtilde_eq]

/-- The population FWL coefficient on the panel class equals the finite-cell
Goodman-Bacon `betaTWFE`.

**Note on `hDtilde_eq`.**
The hypothesis
```
hDtilde_eq : ∀ g t, panelDtilde μ D G T_rv g t =
                      Dtilde (panelOf …) g t
```
encodes the assumption that `D` is *cell-measurable*, i.e. constant on each
cohort×period cell `{ω | G ω = g ∧ T_rv ω = t}`.  In the paper this is
definitional (D_{gt} = 1_{A_g ≤ t} depends only on (g, t)), and ideally one
would derive `hDtilde_eq` as a lemma from a cleaner premise
```
hD_cell_fun : ∀ᵐ ω ∂μ, D ω = if AdoptionDate.le (A (G ω)) (T_rv ω) then 1 else 0
```
via cell-mean computation under `hLaw`.  Deriving this step requires
measure-theoretic a.e.-equality machinery for cell restrictions that is not
yet present in Causalean (the gap requires showing that a cell conditional mean
of a cell-constant function returns that constant).  Until that machinery is
in place `hDtilde_eq` is carried as an explicit hypothesis; it is *not* an
opaque assumption about the conclusion but a precise statement of
cell-measurability of `D`, deferred to a future measure layer. -/
theorem bridge_finite_residualized_eq_twfe
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (D Y : Ω → ℝ) (G : Ω → 𝒢) (T_rv : Ω → Fin T)
    (A : 𝒢 → WithTop (Fin T))
    (G_meas : Measurable G) (T_meas : Measurable T_rv)
    (D_meas : Measurable D)
    (D_binary : ∀ᵐ ω ∂μ, D ω = 0 ∨ D ω = 1)
    (Y_memLp : MemLp Y 2 μ)
    (B_balanced : IsBalancedPanelLaw μ G T_rv)
    (hT_pos : 0 < T)
    (hp_pos : ∀ g, 0 < cohortMass μ G g)
    (hp_sum : ∑ g, cohortMass μ G g = 1)
    (hLaw : ∀ g t,
      cellMass μ G T_rv g t = cohortMass μ G g / (T : ℝ))
    (hD_cell : ∀ g t, ∀ᵐ ω ∂μ.restrict {ω' | G ω' = g ∧ T_rv ω' = t},
      D ω = (∫ ω', D ω' * Set.indicator {ω' | G ω' = g ∧ T_rv ω' = t}
              (fun _ => (1 : ℝ)) ω' ∂μ) / cellMass μ G T_rv g t)
    (hDtilde_eq : ∀ g t,
      panelDtilde μ D G T_rv g t =
        Dtilde (panelOf μ Y G T_rv A hT_pos hp_pos hp_sum) g t) :
    residualizedCoefficient μ (panelClass μ G T_rv G_meas T_meas)
        (residWitnessY_panel μ Y G T_rv G_meas T_meas Y_memLp B_balanced)
        (residWitnessD_panel μ D G T_rv G_meas T_meas D_meas D_binary
            B_balanced)
      = betaTWFE (panelOf μ Y G T_rv A hT_pos hp_pos hp_sum) := by
  let H := panelClass μ G T_rv G_meas T_meas
  let wY := residWitnessY_panel μ Y G T_rv G_meas T_meas Y_memLp B_balanced
  let wD := residWitnessD_panel μ D G T_rv G_meas T_meas D_meas D_binary
    B_balanced
  let P := panelOf μ Y G T_rv A hT_pos hp_pos hp_sum
  have hMeanReg_mem : H.mem (panelMeanReg μ Y G T_rv) :=
    panelMeanReg_mem_panelClass μ Y G T_rv G_meas T_meas
  have hNum_tilde :
      ∫ ω, wD.Vtilde ω * wY.Vtilde ω ∂μ =
        ∫ ω, wD.Vtilde ω * Y ω ∂μ := by
    have hDY_int : Integrable (fun ω => wD.Vtilde ω * Y ω) μ :=
      wD.Vtilde_memLp.integrable_mul Y_memLp
    have hDM_int : Integrable (fun ω => wD.Vtilde ω * panelMeanReg μ Y G T_rv ω) μ :=
      wD.Vtilde_memLp.integrable_mul (H.memLp hMeanReg_mem)
    calc
      ∫ ω, wD.Vtilde ω * wY.Vtilde ω ∂μ =
          ∫ ω, wD.Vtilde ω * Y ω
            - wD.Vtilde ω * panelMeanReg μ Y G T_rv ω ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards [] with ω
        simp [wY, residWitnessY_panel]
        ring
      _ = ∫ ω, wD.Vtilde ω * Y ω ∂μ
          - ∫ ω, wD.Vtilde ω * panelMeanReg μ Y G T_rv ω ∂μ :=
        integral_sub hDY_int hDM_int
      _ = ∫ ω, wD.Vtilde ω * Y ω ∂μ := by
        rw [wD.orthogonal hMeanReg_mem]
        ring
  have hDen_sum :
      ∫ ω, wD.Vtilde ω * wD.Vtilde ω ∂μ =
        ∑ g, ∑ t, cellMass μ G T_rv g t
          * (panelDtilde μ D G T_rv g t)^2 := by
    have hF_int : Integrable (fun ω => wD.Vtilde ω * wD.Vtilde ω) μ :=
      wD.Vtilde_memLp.integrable_mul wD.Vtilde_memLp
    calc
      ∫ ω, wD.Vtilde ω * wD.Vtilde ω ∂μ =
          ∑ g, ∑ t, ∫ ω, (wD.Vtilde ω * wD.Vtilde ω)
            * Set.indicator {ω' | G ω' = g ∧ T_rv ω' = t}
                (fun _ => (1 : ℝ)) ω ∂μ :=
        integral_eq_sum_panel_cell μ (fun ω => wD.Vtilde ω * wD.Vtilde ω)
          G T_rv G_meas T_meas hF_int
      _ = ∑ g, ∑ t, cellMass μ G T_rv g t
          * (panelDtilde μ D G T_rv g t)^2 := by
        refine Finset.sum_congr rfl (fun g _ => ?_)
        refine Finset.sum_congr rfl (fun t _ => ?_)
        simpa [wD, residWitnessD_panel, mul_assoc] using
          denom_per_cell_panel μ D G T_rv G_meas T_meas hD_cell g t
  have hNum_sum :
      ∫ ω, wD.Vtilde ω * Y ω ∂μ =
        ∑ g, ∑ t, cellMass μ G T_rv g t
          * panelDtilde μ D G T_rv g t
          * cellMean μ Y G T_rv g t := by
    have hF_int : Integrable (fun ω => wD.Vtilde ω * Y ω) μ :=
      wD.Vtilde_memLp.integrable_mul Y_memLp
    calc
      ∫ ω, wD.Vtilde ω * Y ω ∂μ =
          ∑ g, ∑ t, ∫ ω, (wD.Vtilde ω * Y ω)
            * Set.indicator {ω' | G ω' = g ∧ T_rv ω' = t}
                (fun _ => (1 : ℝ)) ω ∂μ :=
        integral_eq_sum_panel_cell μ (fun ω => wD.Vtilde ω * Y ω)
          G T_rv G_meas T_meas hF_int
      _ = ∑ g, ∑ t, cellMass μ G T_rv g t
          * panelDtilde μ D G T_rv g t
          * cellMean μ Y G T_rv g t := by
        refine Finset.sum_congr rfl (fun g _ => ?_)
        refine Finset.sum_congr rfl (fun t _ => ?_)
        simpa [wD, residWitnessD_panel, mul_assoc] using
          num_per_cell_panel μ D Y G T_rv G_meas T_meas hD_cell g t
  calc
    residualizedCoefficient μ (panelClass μ G T_rv G_meas T_meas)
        (residWitnessY_panel μ Y G T_rv G_meas T_meas Y_memLp B_balanced)
        (residWitnessD_panel μ D G T_rv G_meas T_meas D_meas D_binary
            B_balanced)
        = (∫ ω, wD.Vtilde ω * wY.Vtilde ω ∂μ)
          / (∫ ω, wD.Vtilde ω * wD.Vtilde ω ∂μ) := by
      rfl
    _ = (∫ ω, wD.Vtilde ω * Y ω ∂μ)
          / (∫ ω, wD.Vtilde ω * wD.Vtilde ω ∂μ) := by
      rw [hNum_tilde]
    _ = (∑ g, ∑ t, cellMass μ G T_rv g t
          * panelDtilde μ D G T_rv g t
          * cellMean μ Y G T_rv g t)
        / (∑ g, ∑ t, cellMass μ G T_rv g t
          * (panelDtilde μ D G T_rv g t)^2) := by
      rw [hNum_sum, hDen_sum]
    _ = betaTWFE P := by
      simp [P, panelOf, betaTWFE, VD, hLaw, hDtilde_eq, mul_assoc]

end Causalean.Panel.EstimandCharacterization.StaggeredTWFEDecomposition
