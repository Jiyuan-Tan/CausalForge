/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Bai (2022): the matched-pair difference-in-means estimator

For a fixed matched-pair randomization design, each unit is the position `b : Bool` of a pair
`p : P`, with treated/control potential outcomes `y1 p b` / `y0 p b`.  Under the matched-pair design
the coin `z p` selects the treated position in pair `p`; the **matched-pair difference-in-means
estimator** averages, over pairs, the observed treated outcome minus the observed control outcome:
`τ̂ = (1/N) ∑ₚ (y1 p (zₚ) − y0 p (¬zₚ))`, with `N = |P|` pairs.  This file records the estimator, the
sample average treatment effect over the `2N` units, and the theorem that the matched-pair estimator
is **unbiased** for the SATE — each pair contributes its own average effect in expectation.

This is the estimator-side template: a design-based estimator written as a per-pair sum, with
unbiasedness reduced to the single-coordinate (per-pair) marginal of the product design.
-/

import Causalean.Experimentation.MatchedPairDesign.MatchedPair

/-! # Matched-pair estimators

For a fixed matched-pair randomization design, each unit is the position `b : Bool` of a pair
`p : P`, with treated/control potential outcomes `y1 p b` and `y0 p b`.  Under the matched-pair
design the coin `z p` selects the treated position in pair `p`; `pairContribution` records that
pair's observed treated-minus-control contrast `y1 p (z p) - y0 p (!z p)`.

This file defines the sample average treatment effect `sate`, the matched-pair
difference-in-means estimator `matchedPairEstimator`, the per-pair expectation identity
`E_pairContribution`, and the unbiasedness theorem `E_matchedPairEstimator` for Bai's
matched-pair design.
-/

open scoped BigOperators
open Finset

namespace Causalean
namespace Experimentation
namespace MatchedPairDesign

open DesignBased

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- The **sample average treatment effect** over the `2|P|` units (both positions of every pair). -/
noncomputable def sate (y1 y0 : P → Bool → ℝ) : ℝ :=
  (∑ p, ∑ b, (y1 p b - y0 p b)) / (2 * (Fintype.card P : ℝ))

/-- The observed treated-minus-control contribution of pair `p` under assignment `z`: the treated
position is `z p` (outcome `y1 p (z p)`), the control position is `¬ z p` (outcome
`y0 p (¬ z p)`). -/
noncomputable def pairContribution (y1 y0 : P → Bool → ℝ) (p : P) (z : P → Bool) : ℝ :=
  y1 p (z p) - y0 p (!z p)

/-- The **matched-pair difference-in-means estimator**: the average over pairs of the per-pair
treated-minus-control contributions. -/
noncomputable def matchedPairEstimator (y1 y0 : P → Bool → ℝ) (z : P → Bool) : ℝ :=
  (∑ p, pairContribution y1 y0 p z) / (Fintype.card P : ℝ)

/-- The expected per-pair contribution is pair `p`'s average treatment effect
`½ ∑_b (y1 p b − y0 p b)` — the fair coin gives each position probability `½` of being treated. -/
lemma E_pairContribution (y1 y0 : P → Bool → ℝ) (p : P) :
    (matchedPairDesign (P := P)).E (pairContribution y1 y0 p)
      = (∑ b, (y1 p b - y0 p b)) / 2 := by
  change
    (prodDesign
      (fun k : P =>
        coinDesign ((fun _ : P => (1 : ℝ) / 2) k) (by norm_num) (by norm_num))).E
      (fun z => (fun c : Bool => y1 p c - y0 p (!c)) (z p))
      = (∑ b, (y1 p b - y0 p b)) / 2
  rw [FiniteDesign.E_prod_apply
    (fun k : P =>
      coinDesign ((fun _ : P => (1 : ℝ) / 2) k) (by norm_num) (by norm_num))
    p (fun c : Bool => y1 p c - y0 p (!c)), coinDesign_E]
  rw [Fintype.sum_bool]
  norm_num
  ring

/-- **Unbiasedness of the matched-pair estimator.** Under the matched-pair design the
difference-in-means estimator is unbiased for the sample average treatment effect. -/
theorem E_matchedPairEstimator (y1 y0 : P → Bool → ℝ) (hP : 0 < Fintype.card P) :
    (matchedPairDesign (P := P)).E (matchedPairEstimator y1 y0) = sate y1 y0 := by
  unfold matchedPairEstimator sate
  change (matchedPairDesign (P := P)).E
      (fun z => (∑ p, pairContribution y1 y0 p z) * ((Fintype.card P : ℝ)⁻¹)) =
    (∑ p, ∑ b, (y1 p b - y0 p b)) / (2 * (Fintype.card P : ℝ))
  rw [FiniteDesign.E_mul_const]
  rw [show (matchedPairDesign (P := P)).E (fun z => ∑ p, pairContribution y1 y0 p z) =
      ∑ p, (matchedPairDesign (P := P)).E (pairContribution y1 y0 p) by
    simpa using
      (FiniteDesign.E_sum (matchedPairDesign (P := P)) (Finset.univ)
        (fun p z => pairContribution y1 y0 p z))]
  simp_rw [E_pairContribution]
  have hN : (Fintype.card P : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hP
  field_simp [hN]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  ring

end MatchedPairDesign
end Experimentation
end Causalean
