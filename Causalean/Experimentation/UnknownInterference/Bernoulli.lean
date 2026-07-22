/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Sävje–Aronow–Hudgens (2021): the Bernoulli randomization design

The Bernoulli design assigns each unit's treatment by an independent coin flip with unit-specific
probability `p i`.  It is exactly the product design `prodDesign` of the per-unit coin designs, so
cross-unit independence — and, more importantly, independence of two units' outcomes whenever they
are not interference dependent — is the structural disjoint-block independence of the product
design.  This file builds the coin design, the Bernoulli design, and the marginal facts
(`Z_i ⊥ Z_{-i}`, `E[Z_i] = p_i`) used for Horvitz–Thompson unbiasedness.
-/

import Causalean.Experimentation.DesignBased.Product
import Causalean.Experimentation.UnknownInterference.Basic

/-! # Bernoulli design under unknown interference

Independent Bernoulli assignment supplies the product-design independence used for
Sävje-Aronow-Hudgens unknown-interference results.

This file builds the single-unit `coinDesign`, the product Bernoulli randomization design
`bernoulliDesign`, and the one-coordinate marginal identities used throughout the
Horvitz-Thompson and Hájek arguments.  `coinDesign_E` expands the two-point expectation,
`bernoulliDesign_E_eval` reduces any function of one unit's assignment to the corresponding coin
expectation, and `bernoulliDesign_E_treat` / `bernoulliDesign_E_ctrl` give the marginal treatment
and control probabilities `p_i` and `1 - p_i`.
-/

open scoped BigOperators
open Finset

namespace Causalean
namespace Experimentation
namespace UnknownInterference

open DesignBased

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- The single-unit **coin design** on `Bool`: treatment (`true`) with probability `p`, control
(`false`) with probability `1 − p`. -/
def coinDesign (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : FiniteDesign Bool where
  p := fun b => cond b p (1 - p)
  p_nonneg := by
    intro b; cases b
    · exact sub_nonneg.mpr hp1
    · exact hp0
  p_sum := by rw [Fintype.sum_bool]; show p + (1 - p) = 1; ring

/-- The expectation of a function of a single coin: `E[g] = p·g(true) + (1−p)·g(false)`. -/
lemma coinDesign_E (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (g : Bool → ℝ) :
    (coinDesign p hp0 hp1).E g = p * g true + (1 - p) * g false := by
  simp only [FiniteDesign.E, coinDesign, Fintype.sum_bool, cond_true, cond_false]

/-- The **Bernoulli randomization design**: each unit `i` is independently assigned treatment with
probability `p i`.  Built as the product of the per-unit coin designs. -/
noncomputable def bernoulliDesign (p : U → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) :
    FiniteDesign (U → Bool) :=
  prodDesign (fun i => coinDesign (p i) (hp0 i) (hp1 i))

/-- A function of a single unit's treatment has the marginal coin expectation under the Bernoulli
design — the `Z_i ⊥ Z_{-i}` marginalization. -/
lemma bernoulliDesign_E_eval (p : U → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (i : U) (g : Bool → ℝ) :
    (bernoulliDesign p hp0 hp1).E (fun z => g (z i))
      = (coinDesign (p i) (hp0 i) (hp1 i)).E g :=
  FiniteDesign.E_prod_apply (fun i => coinDesign (p i) (hp0 i) (hp1 i)) i g

/-- The marginal treatment expectation is `E[Z_i] = p_i`. -/
lemma bernoulliDesign_E_treat (p : U → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (i : U) :
    (bernoulliDesign p hp0 hp1).E (fun z => if z i then (1 : ℝ) else 0) = p i := by
  rw [bernoulliDesign_E_eval p hp0 hp1 i (fun b => if b then (1 : ℝ) else 0), coinDesign_E]
  simp

/-- The marginal control expectation is `E[1 − Z_i] = 1 − p_i`. -/
lemma bernoulliDesign_E_ctrl (p : U → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (i : U) :
    (bernoulliDesign p hp0 hp1).E (fun z => if z i then (0 : ℝ) else 1) = 1 - p i := by
  rw [bernoulliDesign_E_eval p hp0 hp1 i (fun b => if b then (0 : ℝ) else 1), coinDesign_E]
  simp

end UnknownInterference
end Experimentation
end Causalean
