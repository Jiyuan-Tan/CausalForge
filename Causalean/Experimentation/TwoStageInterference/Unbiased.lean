/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Hudgens–Halloran (2008): unbiasedness of the two-stage estimators

The expectation half of Hudgens & Halloran (2008), Theorems 1–3.  Under the two-stage
mixed-strategy design (Assumption 1) — expressed here through the *known design propensities*
(constant within-group treatment propensity `m i / n i` and constant stage-1 ψ-propensity
`C/N`) — the within-group, population, and effect estimators are exactly unbiased for the
corresponding average-potential-outcome estimands.

These are linearity-of-expectation arguments riding on the substrate engines: `E_sum`/
`E_const_mul` for the within-group average, and `E_compound_factor` (the stage-2 collapse) for
the population average over the randomly selected groups.
-/

import Causalean.Experimentation.TwoStageInterference.Basic

/-! # Two-stage estimator unbiasedness

Hudgens-Halloran within-group, population, and effect estimators are unbiased under
known propensities.

The theorem `E_groupEst` proves within-group unbiasedness from constant treatment propensities,
and `E_popEst` lifts it through the compound design to population means on the ψ-selected groups.
The file also records `CE_total_decomp`, the sign-convention identity relating the direct,
indirect, and total contrasts used in this subtree.
-/

open scoped BigOperators
open Finset

namespace Causalean
namespace Experimentation
namespace TwoStageInterference

open DesignBased

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {n : ι → ℕ}

/-- **Within-group unbiasedness.** Conditional on group `i` being assigned strategy `ρ`, the
empirical mean among `z`-treated units is unbiased for the group average potential outcome
`ȳ_i(z;ρ)`.  Uses the design's constant `z`-treatment propensity `m / nᵢ`. -/
theorem E_groupEst (ρ : ∀ i, FiniteDesign (WAssign n i))
    (Y : ∀ i, Fin (n i) → WAssign n i → ℝ) (i : ι) (z : Bool) (m : ℝ)
    (hm : m ≠ 0) (hn : (n i : ℝ) ≠ 0)
    (hprop : ∀ j : Fin (n i), (ρ i).Pr (fun w => w j = z) = m / (n i)) :
    (ρ i).E (groupEst Y i z m) = groupMean ρ Y i z := by
  unfold groupEst groupMean
  have hLHS : (ρ i).E (fun w => (∑ j, if w j = z then Y i j w else 0) / m)
      = (∑ j, (ρ i).E (fun w => if w j = z then Y i j w else 0)) / m := by
    rw [show (fun w => (∑ j, if w j = z then Y i j w else 0) / m)
          = (fun w => m⁻¹ * ∑ j, if w j = z then Y i j w else 0) from
        funext fun w => by rw [div_eq_inv_mul]]
    rw [FiniteDesign.E_const_mul, FiniteDesign.E_sum, ← div_eq_inv_mul]
  have key : ∀ j : Fin (n i), indMean ρ Y i j z
      = (n i / m) * (ρ i).E (fun w => if w j = z then Y i j w else 0) := by
    intro j
    rw [indMean, hprop j, div_div_eq_mul_div, mul_div_assoc, mul_comm]
  rw [hLHS, Finset.sum_congr rfl (fun j _ => key j), ← Finset.mul_sum]
  field_simp

/-- The summand of the population estimator equals the stage-1 indicator times the within-group
estimator, packaging it for the `E_compound_factor` stage-2 collapse. -/
private lemma popEst_summand (Y : ∀ i, Fin (n i) → WAssign n i → ℝ)
    (z : Bool) (m : ι → ℝ) (i : ι) (sw : StratAssign ι × ∀ i, WAssign n i) :
    (if sw.1 i = true then groupEst Y i z (m i) (sw.2 i) else 0)
      = FiniteDesign.ind (fun s : StratAssign ι => s i = true) sw.1
          * groupEst Y i z (m i) (sw.2 i) := by
  unfold FiniteDesign.ind
  by_cases h : sw.1 i = true <;> simp [h]

/-- **Population unbiasedness (Theorem 1).** The population estimator on the ψ-groups is
unbiased for the population average potential outcome `ȳ(z;ψ)`.  The within-group propensities
are `m i / n i` and the stage-1 ψ-propensity of every group is `C/N`. -/
theorem E_popEst (D₁ : FiniteDesign (StratAssign ι))
    (ψ φ : ∀ i, FiniteDesign (WAssign n i))
    (Y : ∀ i, Fin (n i) → WAssign n i → ℝ) (z : Bool) (m : ι → ℝ) (C : ℝ)
    (hC : C ≠ 0)
    (hm : ∀ i, m i ≠ 0) (hn : ∀ i, (n i : ℝ) ≠ 0)
    (hprop : ∀ i, ∀ j : Fin (n i), (ψ i).Pr (fun w => w j = z) = m i / (n i))
    (hstage1 : ∀ i, D₁.Pr (fun s => s i = true) = C / (Fintype.card ι : ℝ)) :
    (jointDesign D₁ ψ φ).E (popEst Y z true m C) = popMean ψ Y z := by
  unfold popEst popMean jointDesign
  have hEsum : (compound D₁ (fun s i => if s i then ψ i else φ i)).E
        (fun sw => (∑ i, if sw.1 i = true then groupEst Y i z (m i) (sw.2 i) else 0) / C)
      = (∑ i, groupMean ψ Y i z * (C / (Fintype.card ι : ℝ))) / C := by
    rw [show (fun sw : StratAssign ι × ∀ i, WAssign n i =>
            (∑ i, if sw.1 i = true then groupEst Y i z (m i) (sw.2 i) else 0) / C)
          = (fun sw => C⁻¹ * ∑ i, if sw.1 i = true then groupEst Y i z (m i) (sw.2 i) else 0)
          from funext fun sw => by rw [div_eq_inv_mul]]
    rw [FiniteDesign.E_const_mul, FiniteDesign.E_sum, ← div_eq_inv_mul]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    -- per-group: E[1(S_i=ψ)·Ŷ_i] = ȳ_i · (C/N)
    rw [(compound D₁ (fun s i => if s i then ψ i else φ i)).E_congr (popEst_summand Y z m i)]
    rw [FiniteDesign.E_compound_factor D₁ (fun s i => if s i then ψ i else φ i)
        (FiniteDesign.ind (fun s : StratAssign ι => s i = true)) i (groupEst Y i z (m i))]
    -- D₁.E (fun s => 1(s i) · (if s i then ψ i else φ i).E (groupEst...))
    rw [show (fun s : StratAssign ι =>
            FiniteDesign.ind (fun s => s i = true) s
              * (if s i then ψ i else φ i).E (groupEst Y i z (m i)))
          = (fun s => FiniteDesign.ind (fun s => s i = true) s * groupMean ψ Y i z)
          from ?_]
    · rw [FiniteDesign.E_mul_const, FiniteDesign.E_ind, hstage1 i]; ring
    · funext s
      unfold FiniteDesign.ind
      by_cases h : s i = true
      · simp only [h, if_true]
        rw [E_groupEst ψ Y i z (m i) (hm i) (hn i) (hprop i)]
      · simp [h]
  have hcN : (C / (Fintype.card ι : ℝ)) / C = 1 / (Fintype.card ι : ℝ) := by
    rw [div_div, mul_comm (Fintype.card ι : ℝ) C, ← div_div, div_self hC]
  rw [hEsum, ← Finset.sum_mul, mul_div_assoc, hcN, mul_one_div]

/-- **Mixed-orientation decomposition identity.** With direct effect measured as treatment minus
control under ψ, and indirect/total effects measured from φ-control to ψ, the total contrast equals
the indirect contrast minus the direct contrast. -/
theorem CE_total_decomp (ψ φ : ∀ i, FiniteDesign (WAssign n i))
    (Y : ∀ i, Fin (n i) → WAssign n i → ℝ) :
    CE_total ψ φ Y = CE_indirect ψ φ Y - CE_direct ψ Y := by
  unfold CE_total CE_direct CE_indirect
  ring

end TwoStageInterference
end Experimentation
end Causalean
