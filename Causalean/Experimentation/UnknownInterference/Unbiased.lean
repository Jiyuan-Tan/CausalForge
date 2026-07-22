/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Sävje–Aronow–Hudgens (2021): Horvitz–Thompson is exactly unbiased for EATE under Bernoulli

Under a Bernoulli design the Horvitz–Thompson estimator is **exactly** unbiased for the expected
average treatment effect: `E[ĤT] = EATE`.  The key is that each unit's own treatment is independent
of the other treatments (`Z_i ⊥ Z_{-i}`), so

    E[Z_i Y_i / p_i] = E[Z_i y_i(1; Z_{-i})] / p_i = E[Z_i]·E[y_i(1; Z_{-i})] / p_i
                     = E[y_i(1; Z_{-i})],

using that `y_i(1; Z_{-i})` (the treated potential outcome) depends only on coordinates other than
`i` and `E[Z_i] = p_i`.  The control term gives `E[y_i(0; Z_{-i})]` symmetrically, so the `i`ᵗʰ HT
summand has expectation `E[τ_i(Z_{-i})]`, and averaging over `i` yields `EATE`.

The disjoint-block factorization `E_prod_block_mul` (block `{i}` vs. its complement) supplies the
independence; `bernoulliDesign_E_treat` / `_ctrl` supply the marginals `E[Z_i] = p_i`.
-/

import Causalean.Experimentation.UnknownInterference.Bernoulli
import Causalean.Experimentation.DesignBased.ProductBlock

/-! # Unbiasedness under unknown interference

Bernoulli Horvitz-Thompson estimators are exactly unbiased for the expected average treatment
effect even when outcomes may depend on other units' assignments.

The per-unit theorem `E_htSummand` shows that the `i`th Horvitz-Thompson summand has expectation
equal to the assignment-conditional treatment effect `tau y i`.  Its proof uses product-design
block independence between unit `i`'s own treatment and the remaining assignments that determine
`y_i(1; Z_{-i})` or `y_i(0; Z_{-i})`, plus the Bernoulli marginal identities from `Bernoulli`.
Summing these identities gives `htEst_unbiased`, the exact equality `E[htEst] = EATE`.
-/

open scoped BigOperators
open Finset

namespace Causalean
namespace Experimentation
namespace UnknownInterference

open DesignBased

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- **Per-unit unbiasedness.** Under the Bernoulli design with nonzero treatment and control
propensities, the `i`ᵗʰ HT summand has the same expectation as the assignment-conditional unit-level
effect: `E[htSummand i] = E[τ_i]`. -/
theorem E_htSummand (p : U → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (hp0' : ∀ i, p i ≠ 0) (hp1' : ∀ i, (1 : ℝ) - p i ≠ 0)
    (y : U → (U → Bool) → ℝ) (i : U) :
    (bernoulliDesign p hp0 hp1).E (htSummand p y i)
      = (bernoulliDesign p hp0 hp1).E (tau y i) := by
  classical
  letI : MeasurableSpace Bool := ⊤
  letI : MeasurableSingletonClass Bool := ⟨fun _ => trivial⟩
  set D := bernoulliDesign p hp0 hp1 with hD
  -- The treated potential outcome as a function of the full assignment.
  set hT : (U → Bool) → ℝ := fun z => y i (Function.update z i true) with hhT
  set hC : (U → Bool) → ℝ := fun z => y i (Function.update z i false) with hhC
  -- Treatment-term expectation equals `E[hT]`.
  have htreat : D.E (fun z => (if z i then (1 : ℝ) else 0) * y i z / p i) = D.E hT := by
    -- Pointwise rewrite `y i z` to `hT z` against the indicator.
    have hpt : ∀ z, (if z i then (1 : ℝ) else 0) * y i z / p i
        = (1 / p i) * ((if z i then (1 : ℝ) else 0) * hT z) := by
      intro z
      by_cases hz : z i
      · have : Function.update z i true = z := by
          funext x; by_cases hx : x = i
          · subst hx; rw [Function.update_self]; exact hz.symm
          · rw [Function.update_of_ne hx]
        simp only [hz, if_pos, hhT, this]
        field_simp
      · simp only [hz, hhT]
        simp
    rw [D.E_congr hpt, D.E_const_mul]
    -- Factor `E[(if z i then 1 else 0) * hT z]` via block independence.
    have hblock : D.E (fun z => (if z i then (1 : ℝ) else 0) * hT z)
        = D.E (fun z => if z i then (1 : ℝ) else 0) * D.E hT := by
      rw [hD]
      unfold bernoulliDesign
      refine FiniteDesign.E_prod_block_mul _ {i} (fun z => if z i then (1 : ℝ) else 0) hT ?_ ?_
      · intro w w' hww
        have hwi : w i = w' i := hww i (Finset.mem_singleton_self i)
        change (if w i then (1 : ℝ) else 0) = (if w' i then (1 : ℝ) else 0)
        rw [hwi]
      · intro w w' hww
        change y i (Function.update w i true) = y i (Function.update w' i true)
        congr 1
        funext x
        by_cases hx : x = i
        · subst hx; rw [Function.update_self, Function.update_self]
        · rw [Function.update_of_ne hx, Function.update_of_ne hx]
          exact hww x (by simp [Finset.mem_singleton, hx])
    rw [hblock]
    have hEtreat : D.E (fun z => if z i then (1 : ℝ) else 0) = p i := by
      rw [hD]; exact bernoulliDesign_E_treat p hp0 hp1 i
    rw [hEtreat]
    field_simp [hp0' i]
  -- Control-term expectation equals `E[hC]`.
  have hctrl : D.E (fun z => (if z i then (0 : ℝ) else 1) * y i z / (1 - p i)) = D.E hC := by
    have hpt : ∀ z, (if z i then (0 : ℝ) else 1) * y i z / (1 - p i)
        = (1 / (1 - p i)) * ((if z i then (0 : ℝ) else 1) * hC z) := by
      intro z
      by_cases hz : z i
      · simp only [hz, if_pos, hhC]
        simp
      · have : Function.update z i false = z := by
          funext x; by_cases hx : x = i
          · subst hx; rw [Function.update_self]; simpa using hz
          · rw [Function.update_of_ne hx]
        simp only [hz, hhC, this]
        field_simp
    rw [D.E_congr hpt, D.E_const_mul]
    have hblock : D.E (fun z => (if z i then (0 : ℝ) else 1) * hC z)
        = D.E (fun z => if z i then (0 : ℝ) else 1) * D.E hC := by
      rw [hD]
      unfold bernoulliDesign
      refine FiniteDesign.E_prod_block_mul _ {i} (fun z => if z i then (0 : ℝ) else 1) hC ?_ ?_
      · intro w w' hww
        have hwi : w i = w' i := hww i (Finset.mem_singleton_self i)
        change (if w i then (0 : ℝ) else 1) = (if w' i then (0 : ℝ) else 1)
        rw [hwi]
      · intro w w' hww
        change y i (Function.update w i false) = y i (Function.update w' i false)
        congr 1
        funext x
        by_cases hx : x = i
        · subst hx; rw [Function.update_self, Function.update_self]
        · rw [Function.update_of_ne hx, Function.update_of_ne hx]
          exact hww x (by simp [Finset.mem_singleton, hx])
    rw [hblock]
    have hEctrl : D.E (fun z => if z i then (0 : ℝ) else 1) = 1 - p i := by
      rw [hD]; exact bernoulliDesign_E_ctrl p hp0 hp1 i
    rw [hEctrl]
    field_simp [hp1' i]
  -- Assemble: `E[htSummand] = E[hT] - E[hC] = E[tau]`.
  have hsplit : D.E (htSummand p y i)
      = D.E (fun z => (if z i then (1 : ℝ) else 0) * y i z / p i)
        - D.E (fun z => (if z i then (0 : ℝ) else 1) * y i z / (1 - p i)) := by
    rw [← D.E_sub]; rfl
  rw [hsplit, htreat, hctrl, ← D.E_sub]
  rfl

/-- **Horvitz–Thompson unbiasedness for EATE (Sävje–Aronow–Hudgens 2021).** Under a Bernoulli
design with nonzero treatment and control propensities, the HT estimator is exactly unbiased for the
expected average treatment effect: `E[ĤT] = EATE`. -/
theorem htEst_unbiased (p : U → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (hp0' : ∀ i, p i ≠ 0) (hp1' : ∀ i, (1 : ℝ) - p i ≠ 0)
    (y : U → (U → Bool) → ℝ) :
    (bernoulliDesign p hp0 hp1).E (htEst p y) = EATE (bernoulliDesign p hp0 hp1) y := by
  set D := bernoulliDesign p hp0 hp1 with hD
  set n : ℝ := (Fintype.card U : ℝ) with hn
  -- `E[htEst] = (1/n) * ∑ i E[htSummand i]`.
  have h1 : D.E (htEst p y)
      = (1 / n) * ∑ i : U, D.E (htSummand p y i) := by
    have hcongr : ∀ z, htEst p y z = (1 / n) * ∑ i : U, htSummand p y i z := by
      intro z
      rw [htEst]
      rw [hn]
      ring
    rw [D.E_congr hcongr, D.E_const_mul, D.E_sum]
  -- `EATE = (1/n) * ∑ i E[tau i]`.
  have h2 : EATE D y = (1 / n) * ∑ i : U, D.E (tau y i) := by
    rw [EATE]
    have hcongr : ∀ z, ACATE y z = (1 / n) * ∑ i : U, tau y i z := by
      intro z
      rw [ACATE, hn]
      ring
    rw [D.E_congr hcongr, D.E_const_mul, D.E_sum]
  rw [h1, h2]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hD]
  exact E_htSummand p hp0 hp1 hp0' hp1' y i

end UnknownInterference
end Experimentation
end Causalean
