/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Hudgens–Halloran (2008): unbiasedness of the effect estimators

This file proves exact unbiasedness for the two-stage contrast estimators formalized in this
folder.  The direct contrast uses Hudgens-Halloran's treatment-minus-control sign convention, while
the indirect and total contrasts retain their control-strategy-minus-ψ orientation.  The key step is a
strategy-agnostic version of population unbiasedness: whichever allocation strategy a group of
groups is selected by (the ones flagged ψ, or the ones flagged
φ), the population estimator built on that selection is unbiased for the population average
potential outcome computed under that same strategy.  The three effect estimators are then
differences of two such selection-specific population estimators, so unbiasedness follows by
linearity of expectation.

Concretely this generalizes the population-unbiasedness theorem of `Unbiased.lean` from the
fixed ψ-selection to an arbitrary selection flag, and applies it twice — once for each
estimator in the contrast — discharging the design propensities required for each selection.
-/

import Causalean.Experimentation.TwoStageInterference.Unbiased

/-!
# Two-stage effect estimators and unbiasedness

This file proves unbiasedness for the Hudgens-Halloran direct, indirect, and total effect
estimators. The main reusable step is population unbiasedness for either stage-one selection flag,
which specializes to the ψ-selected and φ-selected groups used in the three causal-effect
contrasts.

The theorem `E_popEst_pick` generalizes `E_popEst` to either stage-one flag.  The definitions
`estIndirect` and `estTotal` are the Horvitz-Thompson effect estimators built from the selected
population estimators, and `E_estDirect`, `E_estIndirect`, and `E_estTotal` prove their exact
finite-sample unbiasedness for `CE_direct`, `CE_indirect`, and `CE_total`.
-/

open scoped BigOperators
open Finset

namespace Causalean
namespace Experimentation
namespace TwoStageInterference

open DesignBased

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {n : ι → ℕ}

/-- The `pick`-parameterized summand of the population estimator: on the groups selected by the
flag `pick`, the summand equals the stage-1 selection indicator times the within-group
estimator, packaging it for the `E_compound_factor` stage-2 collapse. -/
private lemma popEst_summand_pick (Y : ∀ i, Fin (n i) → WAssign n i → ℝ)
    (z : Bool) (m : ι → ℝ) (pick : Bool) (i : ι)
    (sw : StratAssign ι × ∀ i, WAssign n i) :
    (if sw.1 i = pick then groupEst Y i z (m i) (sw.2 i) else 0)
      = FiniteDesign.ind (fun s : StratAssign ι => s i = pick) sw.1
          * groupEst Y i z (m i) (sw.2 i) := by
  unfold FiniteDesign.ind
  by_cases h : sw.1 i = pick <;> simp [h]

/-- **Population unbiasedness, either selection (generalizing Theorem 1).** For an arbitrary
selection flag `pick`, the population estimator on the groups with `s i = pick` is unbiased for
the population average potential outcome `ȳ(z;ρ)` computed under the strategy `ρ` those groups
are actually randomized by.  The hypothesis `hcond` says exactly that: on the event
`s i = pick`, the compound's conditional design `(if s i then ψ i else φ i)` equals `ρ i`.  The
within-group propensities are `m i / n i` and the stage-1 selection propensity of every group
is `denom/N`.  Recovering `E_popEst` is the case `pick = true, ρ = ψ`. -/
theorem E_popEst_pick (D₁ : FiniteDesign (StratAssign ι))
    (ψ φ : ∀ i, FiniteDesign (WAssign n i))
    (Y : ∀ i, Fin (n i) → WAssign n i → ℝ) (z : Bool) (m : ι → ℝ)
    (pick : Bool) (denom : ℝ) (ρ : ∀ i, FiniteDesign (WAssign n i))
    (hdenom : denom ≠ 0) (hm : ∀ i, m i ≠ 0) (hn : ∀ i, (n i : ℝ) ≠ 0)
    (hcond : ∀ (s : StratAssign ι) (i : ι), s i = pick → (if s i then ψ i else φ i) = ρ i)
    (hprop : ∀ i, ∀ j : Fin (n i), (ρ i).Pr (fun w => w j = z) = m i / (n i))
    (hstage1 : ∀ i, D₁.Pr (fun s => s i = pick) = denom / (Fintype.card ι : ℝ)) :
    (jointDesign D₁ ψ φ).E (popEst Y z pick m denom) = popMean ρ Y z := by
  unfold popEst popMean jointDesign
  have hEsum : (compound D₁ (fun s i => if s i then ψ i else φ i)).E
        (fun sw => (∑ i, if sw.1 i = pick then groupEst Y i z (m i) (sw.2 i) else 0) / denom)
      = (∑ i, groupMean ρ Y i z * (denom / (Fintype.card ι : ℝ))) / denom := by
    rw [show (fun sw : StratAssign ι × ∀ i, WAssign n i =>
            (∑ i, if sw.1 i = pick then groupEst Y i z (m i) (sw.2 i) else 0) / denom)
          = (fun sw => denom⁻¹ * ∑ i, if sw.1 i = pick then groupEst Y i z (m i) (sw.2 i) else 0)
          from funext fun sw => by rw [div_eq_inv_mul]]
    rw [FiniteDesign.E_const_mul, FiniteDesign.E_sum, ← div_eq_inv_mul]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    -- per-group: E[1(S_i=pick)·Ŷ_i] = ȳ_i(z;ρ) · (denom/N)
    rw [(compound D₁ (fun s i => if s i then ψ i else φ i)).E_congr
        (popEst_summand_pick Y z m pick i)]
    rw [FiniteDesign.E_compound_factor D₁ (fun s i => if s i then ψ i else φ i)
        (FiniteDesign.ind (fun s : StratAssign ι => s i = pick)) i (groupEst Y i z (m i))]
    rw [show (fun s : StratAssign ι =>
            FiniteDesign.ind (fun s => s i = pick) s
              * (if s i then ψ i else φ i).E (groupEst Y i z (m i)))
          = (fun s => FiniteDesign.ind (fun s => s i = pick) s * groupMean ρ Y i z)
          from ?_]
    · rw [FiniteDesign.E_mul_const, FiniteDesign.E_ind, hstage1 i]; ring
    · funext s
      unfold FiniteDesign.ind
      by_cases h : s i = pick
      · rw [if_pos h, one_mul, hcond s i h,
          E_groupEst ρ Y i z (m i) (hm i) (hn i) (hprop i), one_mul]
      · rw [if_neg h, zero_mul, zero_mul]
  have hcN : (denom / (Fintype.card ι : ℝ)) / denom = 1 / (Fintype.card ι : ℝ) := by
    rw [div_div, mul_comm (Fintype.card ι : ℝ) denom, ← div_div, div_self hdenom]
  rw [hEsum, ← Finset.sum_mul, mul_div_assoc, hcN, mul_one_div]

/-! ### Effect estimators -/

/-- The HT-effect estimator of the **indirect (spillover)** effect:
`Ŷ(0;φ) − Ŷ(0;ψ)`, the control-treatment population estimators on the φ-groups minus on the
ψ-groups. -/
noncomputable def estIndirect (Y : ∀ i, Fin (n i) → WAssign n i → ℝ)
    (m0φ m0ψ : ι → ℝ) (dφ dψ : ℝ) (sw : StratAssign ι × ∀ i, WAssign n i) : ℝ :=
  popEst Y false false m0φ dφ sw - popEst Y false true m0ψ dψ sw

/-- The HT-effect estimator of the **total** effect:
`Ŷ(0;φ) − Ŷ(1;ψ)`, the control-treatment population estimator on the φ-groups minus the
treatment population estimator on the ψ-groups. -/
noncomputable def estTotal (Y : ∀ i, Fin (n i) → WAssign n i → ℝ)
    (m0φ m1ψ : ι → ℝ) (dφ dψ : ℝ) (sw : StratAssign ι × ∀ i, WAssign n i) : ℝ :=
  popEst Y false false m0φ dφ sw - popEst Y true true m1ψ dψ sw

/-! ### Unbiasedness of the effect estimators -/

/-- **Direct-contrast unbiasedness (Theorem 1 contrast).** The estimator on the ψ-groups is
unbiased for the Hudgens-Halloran direct-effect contrast: the population treatment mean under ψ
minus the population control mean under ψ. -/
theorem E_estDirect (D₁ : FiniteDesign (StratAssign ι))
    (ψ φ : ∀ i, FiniteDesign (WAssign n i))
    (Y : ∀ i, Fin (n i) → WAssign n i → ℝ) (m0 m1 : ι → ℝ) (C : ℝ)
    (hC : C ≠ 0) (hm0 : ∀ i, m0 i ≠ 0) (hm1 : ∀ i, m1 i ≠ 0) (hn : ∀ i, (n i : ℝ) ≠ 0)
    (hprop0 : ∀ i, ∀ j : Fin (n i), (ψ i).Pr (fun w => w j = false) = m0 i / (n i))
    (hprop1 : ∀ i, ∀ j : Fin (n i), (ψ i).Pr (fun w => w j = true) = m1 i / (n i))
    (hstage1ψ : ∀ i, D₁.Pr (fun s => s i = true) = C / (Fintype.card ι : ℝ)) :
    (jointDesign D₁ ψ φ).E (estDirect Y m0 m1 C) = CE_direct ψ Y := by
  unfold estDirect CE_direct
  rw [FiniteDesign.E_sub]
  rw [E_popEst_pick D₁ ψ φ Y true m1 true C ψ hC hm1 hn
      (fun s i hs => by simp [hs]) hprop1 hstage1ψ]
  rw [E_popEst_pick D₁ ψ φ Y false m0 true C ψ hC hm0 hn
      (fun s i hs => by simp [hs]) hprop0 hstage1ψ]

/-- **Indirect-effect unbiasedness (Theorem 2 contrast).** The indirect-effect estimator is
unbiased for `C̄E^I(φ,ψ) = ȳ(0;φ) − ȳ(0;ψ)`. -/
theorem E_estIndirect (D₁ : FiniteDesign (StratAssign ι))
    (ψ φ : ∀ i, FiniteDesign (WAssign n i))
    (Y : ∀ i, Fin (n i) → WAssign n i → ℝ) (m0φ m0ψ : ι → ℝ) (dφ dψ : ℝ)
    (hdφ : dφ ≠ 0) (hdψ : dψ ≠ 0)
    (hm0φ : ∀ i, m0φ i ≠ 0) (hm0ψ : ∀ i, m0ψ i ≠ 0) (hn : ∀ i, (n i : ℝ) ≠ 0)
    (hpropφ : ∀ i, ∀ j : Fin (n i), (φ i).Pr (fun w => w j = false) = m0φ i / (n i))
    (hpropψ : ∀ i, ∀ j : Fin (n i), (ψ i).Pr (fun w => w j = false) = m0ψ i / (n i))
    (hstage1φ : ∀ i, D₁.Pr (fun s => s i = false) = dφ / (Fintype.card ι : ℝ))
    (hstage1ψ : ∀ i, D₁.Pr (fun s => s i = true) = dψ / (Fintype.card ι : ℝ)) :
    (jointDesign D₁ ψ φ).E (estIndirect Y m0φ m0ψ dφ dψ) = CE_indirect ψ φ Y := by
  unfold estIndirect CE_indirect
  rw [FiniteDesign.E_sub]
  rw [E_popEst_pick D₁ ψ φ Y false m0φ false dφ φ hdφ hm0φ hn
      (fun s i hs => by simp [hs]) hpropφ hstage1φ]
  rw [E_popEst_pick D₁ ψ φ Y false m0ψ true dψ ψ hdψ hm0ψ hn
      (fun s i hs => by simp [hs]) hpropψ hstage1ψ]

/-- **Total-effect unbiasedness (Theorem 3 contrast).** The total-effect estimator is unbiased
for `C̄E^T(φ,ψ) = ȳ(0;φ) − ȳ(1;ψ)`. -/
theorem E_estTotal (D₁ : FiniteDesign (StratAssign ι))
    (ψ φ : ∀ i, FiniteDesign (WAssign n i))
    (Y : ∀ i, Fin (n i) → WAssign n i → ℝ) (m0φ m1ψ : ι → ℝ) (dφ dψ : ℝ)
    (hdφ : dφ ≠ 0) (hdψ : dψ ≠ 0)
    (hm0φ : ∀ i, m0φ i ≠ 0) (hm1ψ : ∀ i, m1ψ i ≠ 0) (hn : ∀ i, (n i : ℝ) ≠ 0)
    (hpropφ : ∀ i, ∀ j : Fin (n i), (φ i).Pr (fun w => w j = false) = m0φ i / (n i))
    (hpropψ : ∀ i, ∀ j : Fin (n i), (ψ i).Pr (fun w => w j = true) = m1ψ i / (n i))
    (hstage1φ : ∀ i, D₁.Pr (fun s => s i = false) = dφ / (Fintype.card ι : ℝ))
    (hstage1ψ : ∀ i, D₁.Pr (fun s => s i = true) = dψ / (Fintype.card ι : ℝ)) :
    (jointDesign D₁ ψ φ).E (estTotal Y m0φ m1ψ dφ dψ) = CE_total ψ φ Y := by
  unfold estTotal CE_total
  rw [FiniteDesign.E_sub]
  rw [E_popEst_pick D₁ ψ φ Y false m0φ false dφ φ hdφ hm0φ hn
      (fun s i hs => by simp [hs]) hpropφ hstage1φ]
  rw [E_popEst_pick D₁ ψ φ Y true m1ψ true dψ ψ hdψ hm1ψ hn
      (fun s i hs => by simp [hs]) hpropψ hstage1ψ]

end TwoStageInterference
end Experimentation
end Causalean
