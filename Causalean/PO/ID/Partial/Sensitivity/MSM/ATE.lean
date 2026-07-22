/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Marginal Sensitivity Model — the ATE interval

Combines the treated-arm sharp interval (`Sharp.lean`) and the control-arm sharp
interval (`ControlSharp.lean`) into a partial-identification interval for the average
treatment effect `τ = E[Y(1)] − E[Y(0)]`. Following Dorn–Guo, the sharp ATE bounds
are obtained by *opposing* the arm bounds:

    τ⁺(Λ) = ψ_T⁺(Λ) − ψ_C⁻(Λ),   τ⁻(Λ) = ψ_T⁻(Λ) − ψ_C⁺(Λ),

i.e. the ATE upper endpoint pairs the treated upper bound with the control *lower*
bound, and vice versa. The validity of the ATE interval (it contains the true `τ`)
follows from the two arm-wise validity statements by interval subtraction. The same
construction applied to the ZSB (uncalibrated) arm bounds gives the valid-but-wider
ZSB ATE interval.
-/

import Causalean.PO.ID.Partial.Sensitivity.MSM.Sharp
import Causalean.PO.ID.Partial.Sensitivity.MSM.ControlSharp

/-! # Marginal-sensitivity-model ATE interval

This file combines treated-arm and control-arm marginal-sensitivity intervals
into an interval for the average treatment effect. The ATE upper endpoint pairs
the treated upper bound with the control lower bound, and the lower endpoint
pairs the treated lower bound with the control upper bound.

The main declarations are `ate`, the calibrated endpoints `ateUpperCalib` and
`ateLowerCalib`, the uncalibrated endpoints `ateUpper` and `ateLower`, validity
theorems `ate_mem_Icc_calib` and `ate_mem_Icc`, and the nesting theorem
`ateCalib_subset`.
-/

namespace Causalean
namespace PO

open MeasureTheory ProbabilityTheory

namespace POBackdoorSystem

variable {P : POSystem} {γ : Type*} [MeasurableSpace γ]
variable (S : POBackdoorSystem P γ)

/-- The **average treatment effect** `τ = E[Y(1)] − E[Y(0)]`. -/
noncomputable def ate : ℝ := S.Y1mean - S.Y0mean

/-- The **sharp ATE upper bound** `τ⁺(Λ) = ψ_T⁺(Λ) − ψ_C⁻(Λ)`: the treated sharp upper
bound minus the control sharp *lower* bound. -/
noncomputable def ateUpperCalib (Λ : ℝ) : ℝ := S.msmUpperCalib Λ - S.msmLowerCalib0 Λ

/-- The **sharp ATE lower bound** `τ⁻(Λ) = ψ_T⁻(Λ) − ψ_C⁺(Λ)`: the treated sharp lower
bound minus the control sharp *upper* bound. -/
noncomputable def ateLowerCalib (Λ : ℝ) : ℝ := S.msmLowerCalib Λ - S.msmUpperCalib0 Λ

/-- The **ZSB ATE upper bound** `ψ_T⁺ − ψ_C⁻` formed from the uncalibrated arm bounds. -/
noncomputable def ateUpper (Λ : ℝ) : ℝ := S.msmUpper Λ - S.msmLower0 Λ

/-- The **ZSB ATE lower bound** `ψ_T⁻ − ψ_C⁺` formed from the uncalibrated arm bounds. -/
noncomputable def ateLower (Λ : ℝ) : ℝ := S.msmLower Λ - S.msmUpper0 Λ

/-- **Interval subtraction.** If `a ∈ [aₗ, aᵤ]` and `b ∈ [bₗ, bᵤ]`, then
`a − b ∈ [aₗ − bᵤ, aᵤ − bₗ]`. The arithmetic core of the ATE-interval theorems. -/
theorem sub_mem_Icc_of_mem_Icc {a aₗ aᵤ b bₗ bᵤ : ℝ}
    (ha : a ∈ Set.Icc aₗ aᵤ) (hb : b ∈ Set.Icc bₗ bᵤ) :
    a - b ∈ Set.Icc (aₗ - bᵤ) (aᵤ - bₗ) := by
  obtain ⟨ha₁, ha₂⟩ := ha
  obtain ⟨hb₁, hb₂⟩ := hb
  exact ⟨by linarith, by linarith⟩

/-- **The sharp ATE interval is valid:** the true `τ = E[Y(1)] − E[Y(0)]` lies in the
sharp interval `[ateLowerCalib Λ, ateUpperCalib Λ]`, given the two arm-wise sharp
validity statements (treated `Y1mean_mem_Icc_calib`, control `Y0mean_mem_Icc_calib`). -/
theorem ate_mem_Icc_calib (Λ : ℝ)
    (hT : S.Y1mean ∈ Set.Icc (S.msmLowerCalib Λ) (S.msmUpperCalib Λ))
    (hC : S.Y0mean ∈ Set.Icc (S.msmLowerCalib0 Λ) (S.msmUpperCalib0 Λ)) :
    S.ate ∈ Set.Icc (S.ateLowerCalib Λ) (S.ateUpperCalib Λ) := by
  unfold POBackdoorSystem.ate POBackdoorSystem.ateLowerCalib POBackdoorSystem.ateUpperCalib
  exact sub_mem_Icc_of_mem_Icc hT hC

/-- **The ZSB ATE interval is valid:** the true `τ` lies in `[ateLower Λ, ateUpper Λ]`,
from the two arm-wise ZSB validity statements (`Y1mean_mem_Icc`, `Y0mean_mem_Icc`). -/
theorem ate_mem_Icc (Λ : ℝ)
    (hT : S.Y1mean ∈ Set.Icc (S.msmLower Λ) (S.msmUpper Λ))
    (hC : S.Y0mean ∈ Set.Icc (S.msmLower0 Λ) (S.msmUpper0 Λ)) :
    S.ate ∈ Set.Icc (S.ateLower Λ) (S.ateUpper Λ) := by
  unfold POBackdoorSystem.ate POBackdoorSystem.ateLower POBackdoorSystem.ateUpper
  exact sub_mem_Icc_of_mem_Icc hT hC

/-- **The sharp ATE interval is contained in the ZSB ATE interval.** Each sharp arm
bound is tighter than its ZSB counterpart, so the opposed differences nest:
`ateLower Λ ≤ ateLowerCalib Λ` and `ateUpperCalib Λ ≤ ateUpper Λ`. -/
theorem ateCalib_subset (Λ : ℝ)
    (hUT : S.msmUpperCalib Λ ≤ S.msmUpper Λ)
    (hLT : S.msmLower Λ ≤ S.msmLowerCalib Λ)
    (hU0 : S.msmUpperCalib0 Λ ≤ S.msmUpper0 Λ)
    (hL0 : S.msmLower0 Λ ≤ S.msmLowerCalib0 Λ) :
    Set.Icc (S.ateLowerCalib Λ) (S.ateUpperCalib Λ)
      ⊆ Set.Icc (S.ateLower Λ) (S.ateUpper Λ) := by
  apply Set.Icc_subset_Icc
  · unfold POBackdoorSystem.ateLower POBackdoorSystem.ateLowerCalib
    linarith
  · unfold POBackdoorSystem.ateUpper POBackdoorSystem.ateUpperCalib
    linarith

end POBackdoorSystem

end PO
end Causalean
