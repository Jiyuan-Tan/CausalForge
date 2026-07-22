/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Słoczyński (2022): per-cell bridge identities

Per-cell denominator and numerator identities used by the headline
Słoczyński finite-cell bridge theorem.
-/

import Causalean.Panel.EstimandCharacterization.OLSWeightDecomposition.Support.Partition
/-! # Słoczyński per-cell bridge identities

This file proves the per-cell denominator and numerator identities used in
the Słoczyński finite-cell bridge. These identities reduce the
Frisch-Waugh-Lovell denominator and numerator to cell masses, treated shares,
and cell-specific treatment effects before summing over the finite partition.
The theorem `denom_per_cell` identifies the residualized-treatment second
moment on one cell, and `num_per_cell` identifies the residualized
treatment-outcome covariance on one cell under consistency and the finite-cell
conditional-mean-independence bridge condition. -/

namespace Causalean.Panel.EstimandCharacterization.OLSWeightDecomposition

open MeasureTheory Finset Causalean.Panel
open scoped BigOperators

section PerCellIdentities

/-- **Per-cell denominator identity.**
On the cell `{G = g}`, `(D − propensity)(ω) = D ω − cellShare μ D G g`;
squaring and using `D ∈ {0, 1}` plus the defining identity of
`cellShare` gives

    ∫ (D − propensity)² · 𝟙{G = g} dμ
        = cellMass g · cellShare g · (1 − cellShare g).

Used inside the bridge proof to identify the FWL denominator with the
saturated-overlap denominator. -/
theorem denom_per_cell {Ω 𝒢 : Type*} [MeasurableSpace Ω] [Fintype 𝒢]
    [DecidableEq 𝒢] [MeasurableSpace 𝒢] [MeasurableSingletonClass 𝒢]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (D : Ω → ℝ) (G : Ω → 𝒢)
    (G_meas : Measurable G) (D_meas : Measurable D)
    (D_binary : ∀ᵐ ω ∂μ, D ω = 0 ∨ D ω = 1) (g : 𝒢) :
      ∫ ω, (D ω - propensity μ D G ω) * (D ω - propensity μ D G ω)
              * Set.indicator {ω' | G ω' = g} (fun _ => (1 : ℝ)) ω ∂μ
        = cellMass μ G g * (cellShare μ D G g * (1 - cellShare μ D G g)) := by
    let s : Set Ω := {ω | G ω = g}
    let I : Ω → ℝ := fun ω => Set.indicator s (fun _ => (1 : ℝ)) ω
    let p : ℝ := cellShare μ D G g
    let A : ℝ := ∫ ω, D ω * I ω ∂μ
    let M : ℝ := cellMass μ G g
    have hD_mem : MemLp D 2 μ := by
      have hD_bounded : ∀ᵐ ω ∂μ, D ω ∈ Set.Icc (-1 : ℝ) 1 := by
        filter_upwards [D_binary] with ω hD
        rcases hD with hD0 | hD1
        · simp [hD0]
        · simp [hD1]
      exact memLp_of_bounded (f := D) hD_bounded
        (D_meas.aestronglyMeasurable) (2 : ENNReal)
    have hI_mem : MemLp I 2 μ := by
      simpa [I, s] using indicator_cell_memLp μ G G_meas g
    have hDInt : Integrable (fun ω => D ω * I ω) μ :=
      hD_mem.integrable_mul hI_mem
    have hconstIInt : Integrable (fun ω => (p * p) * I ω) μ :=
      (hI_mem.const_mul (p * p)).integrable (by norm_num : (1 : ENNReal) ≤ 2)
    have hlinInt : Integrable (fun ω => (1 - 2 * p) * (D ω * I ω)) μ :=
      hDInt.const_mul (1 - 2 * p)
    have h_ae :
        (fun ω => (D ω - propensity μ D G ω)
          * (D ω - propensity μ D G ω) * I ω) =ᵐ[μ]
          (fun ω => (1 - 2 * p) * (D ω * I ω) + (p * p) * I ω) := by
      filter_upwards [D_binary] with ω hD
      by_cases hω : ω ∈ s
      · have hp : propensity μ D G ω = p :=
          propensity_eq_cellShare_of_mem μ D G hω
        rcases hD with hD0 | hD1
        · simp [I, Set.indicator, hω, hp, p, hD0]
        · simp [I, Set.indicator, hω, hp, p, hD1]
          ring
      · simp [I, Set.indicator, hω]
    have hmain :
        ∫ ω, (D ω - propensity μ D G ω)
            * (D ω - propensity μ D G ω) * I ω ∂μ =
          (1 - 2 * p) * A + (p * p) * M := by
      calc
        ∫ ω, (D ω - propensity μ D G ω)
            * (D ω - propensity μ D G ω) * I ω ∂μ =
            ∫ ω, (1 - 2 * p) * (D ω * I ω) + (p * p) * I ω ∂μ :=
              integral_congr_ae h_ae
        _ = ∫ ω, (1 - 2 * p) * (D ω * I ω) ∂μ
              + ∫ ω, (p * p) * I ω ∂μ :=
          integral_add hlinInt hconstIInt
        _ = (1 - 2 * p) * A + (p * p) * M := by
          rw [integral_const_mul, integral_const_mul]
          have hIint : ∫ ω, I ω ∂μ = M := by
            simpa [I, s, M] using integral_cell_indicator_one_eq_cellMass μ G G_meas g
          simp [A, M, hIint]
    have hshare : p * M = A := by
      simpa [p, M, A, I, s, cellShare, cellMass] using
        (CellBridge.cellMean_mul_cellMass μ D G G_meas g)
    change ∫ ω, (D ω - propensity μ D G ω)
        * (D ω - propensity μ D G ω) * I ω ∂μ = M * (p * (1 - p))
    rw [hmain]
    rw [← hshare]
    ring

/-- **Per-cell numerator identity.**
Under consistency `Y =ᵐ D · Y1 + (1−D) · Y0` and the finite-cell
conditional-mean-independence bridge condition,

    ∫ (D − propensity) · Y · 𝟙{G = g} dμ
        = cellMass g · cellShare g · (1 − cellShare g) · cellTau g.

The bridge condition is the integrated finite-cell substitute for
`E[Y(d) | D, G] = E[Y(d) | G]` and is used here to factor each
indicator-integrated term in the expansion. -/
theorem num_per_cell {Ω 𝒢 : Type*} [MeasurableSpace Ω] [Fintype 𝒢]
    [DecidableEq 𝒢] [MeasurableSpace 𝒢] [MeasurableSingletonClass 𝒢]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (D Y Y0 Y1 : Ω → ℝ) (G : Ω → 𝒢)
    (G_meas : Measurable G) (D_meas : Measurable D)
    (D_binary : ∀ᵐ ω ∂μ, D ω = 0 ∨ D ω = 1)
    (Y0_memLp : MemLp Y0 2 μ) (Y1_memLp : MemLp Y1 2 μ)
    (consis : Y =ᵐ[μ] fun ω => D ω * Y1 ω + (1 - D ω) * Y0 ω)
    (CMI : ∀ (d : ℝ) (g : 𝒢), d = 0 ∨ d = 1 →
      ∫ ω, (if d = 1 then Y1 ω else Y0 ω)
              * Set.indicator {ω' | D ω' = d} (fun _ => (1 : ℝ)) ω
              * Set.indicator {ω' | G ω' = g} (fun _ => (1 : ℝ)) ω ∂μ
        = (∫ ω, (if d = 1 then Y1 ω else Y0 ω)
                  * Set.indicator {ω' | G ω' = g} (fun _ => (1 : ℝ)) ω ∂μ)
            * (if d = 1 then cellShare μ D G g else 1 - cellShare μ D G g))
    (g : 𝒢) :
    ∫ ω, (D ω - propensity μ D G ω) * Y ω
            * Set.indicator {ω' | G ω' = g} (fun _ => (1 : ℝ)) ω ∂μ
      = cellMass μ G g * (cellShare μ D G g * (1 - cellShare μ D G g))
          * cellTau μ Y0 Y1 G g := by
  let s : Set Ω := {ω | G ω = g}
  let I : Ω → ℝ := fun ω => Set.indicator s (fun _ => (1 : ℝ)) ω
  let J1 : Ω → ℝ := fun ω => Set.indicator {ω' | D ω' = (1 : ℝ)}
    (fun _ => (1 : ℝ)) ω
  let J0 : Ω → ℝ := fun ω => Set.indicator {ω' | D ω' = (0 : ℝ)}
    (fun _ => (1 : ℝ)) ω
  let p : ℝ := cellShare μ D G g
  let M : ℝ := cellMass μ G g
  let τ : ℝ := cellTau μ Y0 Y1 G g
  let B1 : ℝ := ∫ ω, Y1 ω * I ω ∂μ
  let B0 : ℝ := ∫ ω, Y0 ω * I ω ∂μ
  have hI_mem : MemLp I 2 μ := by
    simpa [I, s] using indicator_cell_memLp μ G G_meas g
  have hY1IInt : Integrable (fun ω => Y1 ω * I ω) μ :=
    Y1_memLp.integrable_mul hI_mem
  have hY0IInt : Integrable (fun ω => Y0 ω * I ω) μ :=
    Y0_memLp.integrable_mul hI_mem
  have hY1J1IInt :
      Integrable (fun ω => Y1 ω * J1 ω * I ω) μ := by
    simpa [J1, I, s] using
      integrable_mul_indicator_D_G μ Y1 D G D_meas G_meas Y1_memLp (1 : ℝ) g
  have hY0J0IInt :
      Integrable (fun ω => Y0 ω * J0 ω * I ω) μ := by
    simpa [J0, I, s] using
      integrable_mul_indicator_D_G μ Y0 D G D_meas G_meas Y0_memLp (0 : ℝ) g
  have hTerm1Int :
      Integrable (fun ω => (1 - p) * (Y1 ω * J1 ω * I ω)) μ :=
    hY1J1IInt.const_mul (1 - p)
  have hTerm0Int :
      Integrable (fun ω => p * (Y0 ω * J0 ω * I ω)) μ :=
    hY0J0IInt.const_mul p
  have h_ae :
      (fun ω => (D ω - propensity μ D G ω) * Y ω * I ω) =ᵐ[μ]
        (fun ω => (1 - p) * (Y1 ω * J1 ω * I ω)
          - p * (Y0 ω * J0 ω * I ω)) := by
    filter_upwards [D_binary, consis] with ω hD hY
    by_cases hω : ω ∈ s
    · have hp : propensity μ D G ω = p :=
        propensity_eq_cellShare_of_mem μ D G hω
      have hGω : G ω = g := hω
      rcases hD with hD0 | hD1
      · have hY0 : Y ω = Y0 ω := by
          simpa [hD0] using hY
        simp [I, J1, J0, s, Set.indicator, hGω, hp, p, hD0, hY0]
      · have hY1 : Y ω = Y1 ω := by
          simpa [hD1] using hY
        simp [I, J1, J0, s, Set.indicator, hGω, hp, p, hD1, hY1]
    · have hGne : G ω ≠ g := by
        simpa [s] using hω
      simp [I, s, Set.indicator, hGne]
  have hInt :
      ∫ ω, (D ω - propensity μ D G ω) * Y ω * I ω ∂μ =
        (1 - p) * (∫ ω, Y1 ω * J1 ω * I ω ∂μ)
          - p * (∫ ω, Y0 ω * J0 ω * I ω ∂μ) := by
    calc
      ∫ ω, (D ω - propensity μ D G ω) * Y ω * I ω ∂μ =
          ∫ ω, (1 - p) * (Y1 ω * J1 ω * I ω)
            - p * (Y0 ω * J0 ω * I ω) ∂μ :=
        integral_congr_ae h_ae
      _ = ∫ ω, (1 - p) * (Y1 ω * J1 ω * I ω) ∂μ
          - ∫ ω, p * (Y0 ω * J0 ω * I ω) ∂μ :=
        integral_sub hTerm1Int hTerm0Int
      _ = (1 - p) * (∫ ω, Y1 ω * J1 ω * I ω ∂μ)
          - p * (∫ ω, Y0 ω * J0 ω * I ω ∂μ) := by
        rw [integral_const_mul, integral_const_mul]
  have hA1 :
      ∫ ω, Y1 ω * J1 ω * I ω ∂μ = B1 * p := by
    simpa [J1, I, s, B1, p] using CMI (1 : ℝ) g (Or.inr rfl)
  have hA0 :
      ∫ ω, Y0 ω * J0 ω * I ω ∂μ = B0 * (1 - p) := by
    simpa [J0, I, s, B0, p] using CMI (0 : ℝ) g (Or.inl rfl)
  have hdiff :
      ∫ ω, (Y1 ω - Y0 ω) * I ω ∂μ = B1 - B0 := by
    calc
      ∫ ω, (Y1 ω - Y0 ω) * I ω ∂μ =
          ∫ ω, Y1 ω * I ω - Y0 ω * I ω ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards [] with ω
        ring
      _ = B1 - B0 := by
        simpa [B1, B0] using integral_sub hY1IInt hY0IInt
  have hTauM : τ * M = B1 - B0 := by
    calc
      τ * M = ∫ ω, (Y1 ω - Y0 ω) * I ω ∂μ := by
        simpa [τ, M, I, s, cellTau, cellMass] using
          (CellBridge.cellMean_mul_cellMass μ (fun ω => Y1 ω - Y0 ω) G G_meas g)
      _ = B1 - B0 := hdiff
  change ∫ ω, (D ω - propensity μ D G ω) * Y ω * I ω ∂μ =
    M * (p * (1 - p)) * τ
  calc
    ∫ ω, (D ω - propensity μ D G ω) * Y ω * I ω ∂μ =
        (1 - p) * (B1 * p) - p * (B0 * (1 - p)) := by
      rw [hInt, hA1, hA0]
    _ = p * (1 - p) * (B1 - B0) := by ring
    _ = M * (p * (1 - p)) * τ := by
      rw [← hTauM]
      ring

end PerCellIdentities

end Causalean.Panel.EstimandCharacterization.OLSWeightDecomposition
