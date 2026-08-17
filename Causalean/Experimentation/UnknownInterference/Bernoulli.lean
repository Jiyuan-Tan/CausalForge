/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Sävje–Aronow–Hudgens (2021): the Bernoulli randomization design

The Bernoulli design assigns each unit's treatment by an independent coin flip with unit-specific
probability `p i`.  It is exactly the product design `prodDesign` of the per-unit coin designs, so
cross-unit independence — and, more importantly, independence of two units' outcomes whenever they
are not interference dependent — is the structural disjoint-block independence of the product
design.  This file reuses the canonical coin design, builds the Bernoulli design, and records the
marginal facts (`Z_i ⊥ Z_{-i}`, `E[Z_i] = p_i`) used for Horvitz–Thompson unbiasedness.
-/

import Causalean.Experimentation.DesignBased.Designs.Coin
import Causalean.Experimentation.DesignBased.Product
import Causalean.Experimentation.UnknownInterference.Basic

/-! # Bernoulli design under unknown interference

Independent Bernoulli assignment supplies the product-design independence used for
Sävje-Aronow-Hudgens unknown-interference results.

This file reuses the canonical single-unit `coinDesign`, builds the product Bernoulli randomization
design `bernoulliDesign`, and proves the one-coordinate marginal identities used throughout the
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

/-- The **Bernoulli randomization design**: each unit `i` is independently assigned treatment with
probability `p i`.  Built as the product of the per-unit coin designs. -/
noncomputable def bernoulliDesign (p : U → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) :
    FiniteDesign (U → Bool) :=
  prodDesign (fun i => coinDesign (p i) (hp0 i) (hp1 i))

/-- **Marginalizing the Bernoulli design to a single coordinate.** Under the Bernoulli design with
per-unit treatment probabilities `p` [taking values in `[0, 1]`](hyp:hp0,hp1), [the expected
value of any function `g` of a single unit `i`'s treatment status coincides with its expectation
under that unit's own coin design with success probability `p i`](goal) — the `Zᵢ ⊥ Z₋ᵢ`
marginalization. -/
lemma bernoulliDesign_E_eval (p : U → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (i : U) (g : Bool → ℝ) :
    (bernoulliDesign p hp0 hp1).E (fun z => g (z i))
      = (coinDesign (p i) (hp0 i) (hp1 i)).E g :=
  FiniteDesign.E_prod_apply (fun i => coinDesign (p i) (hp0 i) (hp1 i)) i g

/-- **Marginal treatment-indicator expectation under the Bernoulli design.** Under the Bernoulli
design with per-unit treatment probabilities `p` [taking values in `[0, 1]`](hyp:hp0,hp1),
[the expected value of the indicator that unit `i` is treated equals `p i`](goal). -/
lemma bernoulliDesign_E_treat (p : U → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (i : U) :
    (bernoulliDesign p hp0 hp1).E (fun z => if z i then (1 : ℝ) else 0) = p i := by
  rw [bernoulliDesign_E_eval p hp0 hp1 i (fun b => if b then (1 : ℝ) else 0), coinDesign_E]
  simp

/-- **Marginal control-indicator expectation under the Bernoulli design.** Under the Bernoulli
design with per-unit treatment probabilities `p` [taking values in `[0, 1]`](hyp:hp0,hp1),
[the expected value of the indicator that unit `i` is untreated equals `1 - p i`](goal). -/
lemma bernoulliDesign_E_ctrl (p : U → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (i : U) :
    (bernoulliDesign p hp0 hp1).E (fun z => if z i then (0 : ℝ) else 1) = 1 - p i := by
  rw [bernoulliDesign_E_eval p hp0 hp1 i (fun b => if b then (0 : ℝ) else 1), coinDesign_E]
  simp

end UnknownInterference
end Experimentation
end Causalean
