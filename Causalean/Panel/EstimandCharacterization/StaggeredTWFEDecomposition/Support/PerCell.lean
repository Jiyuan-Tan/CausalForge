/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Goodman-Bacon (2021) Layer B: per-cell denominator and numerator

Reduces `∫ Vtilde² · 𝟙{cell g t} dμ` and `∫ Vtilde · Y · 𝟙{cell g t} dμ`
to closed-form expressions in the cohort-period panel statistics
(`cellMass · Dtilde²` and `cellMass · Dtilde · cellMean`). These are the
two-axis analogues of Sloczynski's `denom_per_cell` / `num_per_cell`.
-/

import Causalean.Panel.EstimandCharacterization.StaggeredTWFEDecomposition.Support.Partition
/-! # Goodman-Bacon Per-Cell Bridge Identities

This file proves the cell-level integral identities that express the
residualized-treatment denominator and the residualized-outcome numerator in
terms of cohort-period panel statistics. These identities supply the local
algebra needed to connect the measure-theoretic bridge with the finite
Goodman-Bacon decomposition. -/

namespace Causalean.Panel.EstimandCharacterization.StaggeredTWFEDecomposition

open MeasureTheory Finset Causalean.Panel
open scoped BigOperators

variable {Ω 𝒢 : Type*} [MeasurableSpace Ω] [Fintype 𝒢] [DecidableEq 𝒢]
  [MeasurableSpace 𝒢] [MeasurableSingletonClass 𝒢] {T : ℕ}

/-- The "panel-residualized treatment hat" `Dtilde_{gt}` value of the
in-class residual on cell `(g, t)`: equals
`D_{gt} - barD_g - (E[D | T=t] - E[D])`, the LaTeX double-demeaning
formula.

We define this in terms of the existing `D` (the indicator
`AdoptionDate.le (A g) t`) and the cohort/period statistics, so that
`Dtilde P g t = D P g t - barD P g - (E[D | T=t] - E[D])` for the
`panelOf …` panel `P`. -/
noncomputable def panelDtilde
    (μ : Measure Ω) (D : Ω → ℝ) (G : Ω → 𝒢) (T_rv : Ω → Fin T)
    (g : 𝒢) (t : Fin T) : ℝ :=
  ((∫ ω, D ω * Set.indicator {ω' | G ω' = g ∧ T_rv ω' = t}
              (fun _ => (1 : ℝ)) ω ∂μ) / cellMass μ G T_rv g t)
    - panelPropensityHat μ D G T_rv g t

/-- **Per-cell denominator identity.** On the cell `{G = g ∧ T_rv = t}`,
`(D - panelPropensity)(ω) = panelDtilde μ D G T_rv g t`; squaring and
integrating over the cell gives

    ∫ (D - panelPropensity)² · 𝟙{cell g t} dμ
        = cellMass g t · panelDtilde g t².

The proof requires the cell-constancy hypothesis `hD_cell` saying that on
`{G = g ∧ T_rv = t}`, `D` agrees a.e. with the cell mean
`(∫ D · 𝟙{cell} dμ) / cellMass`. -/
theorem denom_per_cell_panel
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (D : Ω → ℝ) (G : Ω → 𝒢) (T_rv : Ω → Fin T)
    (G_meas : Measurable G) (T_meas : Measurable T_rv)
    (hD_cell : ∀ g t, ∀ᵐ ω ∂μ.restrict {ω' | G ω' = g ∧ T_rv ω' = t},
      D ω = (∫ ω', D ω' * Set.indicator {ω' | G ω' = g ∧ T_rv ω' = t}
              (fun _ => (1 : ℝ)) ω' ∂μ) / cellMass μ G T_rv g t)
    (g : 𝒢) (t : Fin T) :
    ∫ ω, (D ω - panelPropensity μ D G T_rv ω)
            * (D ω - panelPropensity μ D G T_rv ω)
            * Set.indicator {ω' | G ω' = g ∧ T_rv ω' = t}
                (fun _ => (1 : ℝ)) ω ∂μ
      = cellMass μ G T_rv g t * (panelDtilde μ D G T_rv g t)^2 := by
  let s : Set Ω := {ω | G ω = g ∧ T_rv ω = t}
  let I : Ω → ℝ := fun ω => Set.indicator s (fun _ => (1 : ℝ)) ω
  let q : ℝ := panelDtilde μ D G T_rv g t
  have hs : MeasurableSet s := by
    have hG : MeasurableSet {ω : Ω | G ω = g} :=
      G_meas (measurableSet_singleton g)
    have hT : MeasurableSet {ω : Ω | T_rv ω = t} :=
      T_meas (measurableSet_singleton t)
    simpa [s, Set.inter_def] using hG.inter hT
  change ∫ ω, (D ω - panelPropensity μ D G T_rv ω)
            * (D ω - panelPropensity μ D G T_rv ω) * I ω ∂μ
      = cellMass μ G T_rv g t * q^2
  have h_on :
      (fun ω => (D ω - panelPropensity μ D G T_rv ω)
            * (D ω - panelPropensity μ D G T_rv ω) * I ω)
        =ᵐ[μ.restrict s] (fun ω => q^2 * I ω) := by
    filter_upwards [hD_cell g t, MeasureTheory.ae_restrict_mem hs] with ω hDω hωs
    rcases hωs with ⟨hGω, hTω⟩
    have hpω :
        panelPropensity μ D G T_rv ω = panelPropensityHat μ D G T_rv g t :=
      panelPropensity_eq_hat_of_mem μ D G T_rv hGω hTω
    have hres : D ω - panelPropensity μ D G T_rv ω = q := by
      rw [hDω, hpω]
      simp [q, panelDtilde]
    simp [I, s, hGω, hTω, hres, pow_two]
  have h_off :
      (fun ω => (D ω - panelPropensity μ D G T_rv ω)
            * (D ω - panelPropensity μ D G T_rv ω) * I ω)
        =ᵐ[μ.restrict sᶜ] (fun ω => q^2 * I ω) := by
    rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' hs.compl]
    filter_upwards with ω hωs
    have hω_not_s : ω ∉ s := by simpa using hωs
    simp [I, Set.indicator, hω_not_s]
  have h_ae :
      (fun ω => (D ω - panelPropensity μ D G T_rv ω)
            * (D ω - panelPropensity μ D G T_rv ω) * I ω)
        =ᵐ[μ] (fun ω => q^2 * I ω) :=
    MeasureTheory.ae_of_ae_restrict_of_ae_restrict_compl s h_on h_off
  calc
    ∫ ω, (D ω - panelPropensity μ D G T_rv ω)
            * (D ω - panelPropensity μ D G T_rv ω) * I ω ∂μ
        = ∫ ω, q^2 * I ω ∂μ := integral_congr_ae h_ae
    _ = q^2 * ∫ ω, I ω ∂μ := integral_const_mul (q^2) I
    _ = q^2 * cellMass μ G T_rv g t := by
      rw [integral_panel_cell_indicator_one_eq_cellMass μ G T_rv G_meas T_meas g t]
    _ = cellMass μ G T_rv g t * q^2 := by ring

/-- **Per-cell numerator identity.** Under the same cell-constancy
hypothesis on `D`, plus the cell-mean defining identity for `Y`,

    ∫ (D - panelPropensity) · Y · 𝟙{cell g t} dμ
        = cellMass g t · panelDtilde g t · cellMean g t.

This is the two-axis analogue of Sloczynski's `num_per_cell`. -/
theorem num_per_cell_panel
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (D Y : Ω → ℝ) (G : Ω → 𝒢) (T_rv : Ω → Fin T)
    (G_meas : Measurable G) (T_meas : Measurable T_rv)
    (hD_cell : ∀ g t, ∀ᵐ ω ∂μ.restrict {ω' | G ω' = g ∧ T_rv ω' = t},
      D ω = (∫ ω', D ω' * Set.indicator {ω' | G ω' = g ∧ T_rv ω' = t}
              (fun _ => (1 : ℝ)) ω' ∂μ) / cellMass μ G T_rv g t)
    (g : 𝒢) (t : Fin T) :
    ∫ ω, (D ω - panelPropensity μ D G T_rv ω) * Y ω
            * Set.indicator {ω' | G ω' = g ∧ T_rv ω' = t}
                (fun _ => (1 : ℝ)) ω ∂μ
      = cellMass μ G T_rv g t * panelDtilde μ D G T_rv g t
          * cellMean μ Y G T_rv g t := by
  let s : Set Ω := {ω | G ω = g ∧ T_rv ω = t}
  let I : Ω → ℝ := fun ω => Set.indicator s (fun _ => (1 : ℝ)) ω
  let q : ℝ := panelDtilde μ D G T_rv g t
  let mY : ℝ := cellMean μ Y G T_rv g t
  have hs : MeasurableSet s := by
    have hG : MeasurableSet {ω : Ω | G ω = g} :=
      G_meas (measurableSet_singleton g)
    have hT : MeasurableSet {ω : Ω | T_rv ω = t} :=
      T_meas (measurableSet_singleton t)
    simpa [s, Set.inter_def] using hG.inter hT
  change ∫ ω, (D ω - panelPropensity μ D G T_rv ω) * Y ω * I ω ∂μ
      = cellMass μ G T_rv g t * q * mY
  have h_on :
      (fun ω => (D ω - panelPropensity μ D G T_rv ω) * Y ω * I ω)
        =ᵐ[μ.restrict s] (fun ω => q * (Y ω * I ω)) := by
    filter_upwards [hD_cell g t, MeasureTheory.ae_restrict_mem hs] with ω hDω hωs
    rcases hωs with ⟨hGω, hTω⟩
    have hpω :
        panelPropensity μ D G T_rv ω = panelPropensityHat μ D G T_rv g t :=
      panelPropensity_eq_hat_of_mem μ D G T_rv hGω hTω
    have hres : D ω - panelPropensity μ D G T_rv ω = q := by
      rw [hDω, hpω]
      simp [q, panelDtilde]
    simp [I, s, hGω, hTω, hres]
  have h_off :
      (fun ω => (D ω - panelPropensity μ D G T_rv ω) * Y ω * I ω)
        =ᵐ[μ.restrict sᶜ] (fun ω => q * (Y ω * I ω)) := by
    rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' hs.compl]
    filter_upwards with ω hωs
    have hω_not_s : ω ∉ s := by simpa using hωs
    simp [I, Set.indicator, hω_not_s]
  have h_ae :
      (fun ω => (D ω - panelPropensity μ D G T_rv ω) * Y ω * I ω)
        =ᵐ[μ] (fun ω => q * (Y ω * I ω)) :=
    MeasureTheory.ae_of_ae_restrict_of_ae_restrict_compl s h_on h_off
  have hmean :
      mY * cellMass μ G T_rv g t =
        ∫ ω, Y ω * I ω ∂μ := by
    simpa [mY, cellMean, I, s] using
      (panel_cell_integral_div_mul_cellMass μ Y G T_rv G_meas T_meas g t)
  calc
    ∫ ω, (D ω - panelPropensity μ D G T_rv ω) * Y ω * I ω ∂μ
        = ∫ ω, q * (Y ω * I ω) ∂μ := integral_congr_ae h_ae
    _ = q * ∫ ω, Y ω * I ω ∂μ := integral_const_mul q (fun ω => Y ω * I ω)
    _ = q * (mY * cellMass μ G T_rv g t) := by rw [hmean]
    _ = cellMass μ G T_rv g t * q * mY := by ring

end Causalean.Panel.EstimandCharacterization.StaggeredTWFEDecomposition
