/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Fixed-pair matched-pair estimator variance

For a fixed matched-pair randomization design, the difference-in-means estimator is a sum of
independent per-pair terms, so its randomization variance is the sum of the per-pair variances.  Each
per-pair variance is the variance of a fair two-point random variable and works out to `¼` times the
squared **within-pair imbalance** — the difference, across the two positions of the pair, of the unit
totals `y1 + y0`.  Hence

    Var(τ̂) = (1 / 4N²) ∑ₚ ((y1 p true + y0 p true) − (y1 p false + y0 p false))².

The theorem in this file only computes that fixed-pairing randomization variance.  It does not
compare alternative pairings and does not prove an optimal matching theorem.  The result is also the
variance-side template: a design-based estimator's variance computed through the product design's
cross-coordinate independence (`Var_prod_linear_comb`).
-/

import Causalean.Experimentation.MatchedPairDesign.Estimator

/-! # Matched-pair estimator variance

For a fixed set of pairs, the matched-pair estimator's randomization variance equals the sum of
squared within-pair imbalances, scaled by `1/(4N²)`.

The main definition is `pairImbalance`, the difference across the two units in a pair of the unit
totals `y1 + y0`.  The lemma `Var_pairContribution` computes the variance contribution of one
pair, and `Var_matchedPairEstimator` sums these independent pair contributions using
product-design independence.  The file does not compare alternative pairings or prove an optimal
matching theorem.
-/

open scoped BigOperators
open Finset

namespace Causalean
namespace Experimentation
namespace MatchedPairDesign

open DesignBased

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- The **within-pair imbalance** of pair `p`: the difference, between its two positions, of the
unit totals `y1 + y0`.  Good matching makes this small. -/
noncomputable def pairImbalance (y1 y0 : P → Bool → ℝ) (p : P) : ℝ :=
  (y1 p true + y0 p true) - (y1 p false + y0 p false)

/-- The variance of a single pair's contribution is `¼` times its squared within-pair imbalance —
the variance of the fair two-point random variable `y1 p (z p) − y0 p (¬ z p)`. -/
lemma Var_pairContribution (y1 y0 : P → Bool → ℝ) (p : P) :
    (matchedPairDesign (P := P)).Var (pairContribution y1 y0 p)
      = (pairImbalance y1 y0 p) ^ 2 / 4 := by
  change
    (prodDesign
      (fun k : P =>
        coinDesign ((fun _ : P => (1 : ℝ) / 2) k) (by norm_num) (by norm_num))).Var
      (fun z => (fun c : Bool => y1 p c - y0 p (!c)) (z p))
      = (pairImbalance y1 y0 p) ^ 2 / 4
  rw [FiniteDesign.Var_prod_apply
    (fun k : P =>
      coinDesign ((fun _ : P => (1 : ℝ) / 2) k) (by norm_num) (by norm_num))
    p (fun c : Bool => y1 p c - y0 p (!c))]
  rw [FiniteDesign.Var_eq]
  rw [coinDesign_E, coinDesign_E]
  unfold pairImbalance
  norm_num
  ring

/-- **Variance of the matched-pair estimator.** Under the matched-pair design the
difference-in-means estimator has randomization variance equal to `1/(4N²)` times the sum of squared
within-pair imbalances.  The formula exposes within-pair similarity in `y1 + y0` as the driver of
the estimator's randomization variance. -/
theorem Var_matchedPairEstimator (y1 y0 : P → Bool → ℝ) :
    (matchedPairDesign (P := P)).Var (matchedPairEstimator y1 y0)
      = (∑ p, (pairImbalance y1 y0 p) ^ 2) / (4 * (Fintype.card P : ℝ) ^ 2) := by
  let D : P → FiniteDesign Bool :=
    fun _ => coinDesign ((1 : ℝ) / 2) (by norm_num) (by norm_num)
  have hcongr : ∀ z : P → Bool,
      matchedPairEstimator y1 y0 z =
        ∑ p, ((Fintype.card P : ℝ)⁻¹) *
          (fun c : Bool => y1 p c - y0 p (!c)) (z p) := by
    intro z
    unfold matchedPairEstimator pairContribution
    rw [div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p hp
    ring
  rw [(matchedPairDesign (P := P)).Var_congr hcongr]
  change (prodDesign D).Var
      (fun z => ∑ p, ((Fintype.card P : ℝ)⁻¹) *
        (fun c : Bool => y1 p c - y0 p (!c)) (z p)) =
      (∑ p, (pairImbalance y1 y0 p) ^ 2) / (4 * (Fintype.card P : ℝ) ^ 2)
  rw [FiniteDesign.Var_prod_linear_comb D
      (fun _ : P => (Fintype.card P : ℝ)⁻¹)
      (fun p c => y1 p c - y0 p (!c))]
  have hVar : ∀ p : P,
      (D p).Var (fun c : Bool => y1 p c - y0 p (!c)) =
        (pairImbalance y1 y0 p) ^ 2 / 4 := by
    intro p
    rw [FiniteDesign.Var_eq, coinDesign_E, coinDesign_E]
    unfold pairImbalance
    norm_num
    ring
  simp_rw [hVar]
  rw [show (∑ x, (Fintype.card P : ℝ)⁻¹ ^ 2 *
      ((pairImbalance y1 y0 x) ^ 2 / 4)) =
      ∑ x, (pairImbalance y1 y0 x) ^ 2 *
        ((Fintype.card P : ℝ)⁻¹ ^ 2 / 4) by
    apply Finset.sum_congr rfl
    intro p hp
    ring]
  rw [← Finset.sum_mul]
  ring_nf

end MatchedPairDesign
end Experimentation
end Causalean
