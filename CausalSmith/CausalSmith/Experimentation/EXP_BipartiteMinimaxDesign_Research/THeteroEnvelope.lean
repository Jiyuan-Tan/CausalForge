/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Bipartite minimax design: the heterogeneous envelope kernel

`thm:hetero-envelope`. The exact per-pair covariance identity for the centered
Hájek linearization scores, and the resulting graph-only conservative envelope
bound `σ²_{G_n,p}(Y) ≤ V_env(G_n,p)` under bounded potential outcomes.
-/

import CausalSmith.Experimentation.EXP_BipartiteMinimaxDesign_Research.Envelope
import CausalSmith.Experimentation.EXP_BipartiteMinimaxDesign_Research.Helpers.Linearization

set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.style.show false

open scoped BigOperators
open Finset
open Causalean.Experimentation.DesignBased
open Causalean.Experimentation.UnknownInterference

namespace CausalSmith.Experimentation.BipartiteMinimaxDesign

variable {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I]

-- @node: abs_scaled_univ_sum_le_one
/-- If every outcome-side quantity lies between minus one and one, its average also lies between minus one and one. -/
lemma abs_scaled_univ_sum_le_one (f : O → ℝ) (hf : ∀ i, |f i| ≤ 1) :
    |(Fintype.card O : ℝ)⁻¹ * ∑ i, f i| ≤ 1 := by
  classical
  by_cases hcard : (Fintype.card O : ℝ) = 0
  · simp [hcard]
  · have hsum_abs : |∑ i : O, f i| ≤ ∑ i : O, |f i| := by
      exact Finset.abs_sum_le_sum_abs (s := Finset.univ) (f := f)
    have hsum_le : (∑ i : O, |f i|) ≤ ∑ i : O, (1 : ℝ) := by
      exact Finset.sum_le_sum (fun i _ => hf i)
    have hsum_card : (∑ i : O, (1 : ℝ)) = (Fintype.card O : ℝ) := by
      simp
    have hsum_bound : |∑ i : O, f i| ≤ (Fintype.card O : ℝ) := by
      calc
        |∑ i : O, f i| ≤ ∑ i : O, |f i| := hsum_abs
        _ ≤ ∑ i : O, (1 : ℝ) := hsum_le
        _ = (Fintype.card O : ℝ) := hsum_card
    have hscale_nonneg : 0 ≤ (Fintype.card O : ℝ)⁻¹ := by
      exact inv_nonneg.mpr (Nat.cast_nonneg (Fintype.card O))
    have hmain : (Fintype.card O : ℝ)⁻¹ * |∑ i : O, f i| ≤
        (Fintype.card O : ℝ)⁻¹ * (Fintype.card O : ℝ) := by
      exact mul_le_mul_of_nonneg_left hsum_bound hscale_nonneg
    rw [inv_mul_cancel₀ hcard] at hmain
    calc
      |(Fintype.card O : ℝ)⁻¹ * ∑ i : O, f i|
          = (Fintype.card O : ℝ)⁻¹ * |∑ i : O, f i| := by
            rw [abs_mul, abs_of_nonneg hscale_nonneg]
      _ ≤ 1 := hmain

-- @node: mu1_abs_le_one_of_bounded
/-- Under outcomes bounded by one in absolute value, the treated potential-outcome mean is bounded by one in absolute value. -/
lemma mu1_abs_le_one_of_bounded (E : BipartiteExperiment I O)
    (hbdd : BoundedOutcomes E) :
    |E.mu1| ≤ 1 := by
  simpa [BipartiteExperiment.mu1] using
    abs_scaled_univ_sum_le_one (O := O) (fun i => E.Y1 i) (fun i => (hbdd i).1)

-- @node: mu0_abs_le_one_of_bounded
/-- Under outcomes bounded by one in absolute value, the control potential-outcome mean is bounded by one in absolute value. -/
lemma mu0_abs_le_one_of_bounded (E : BipartiteExperiment I O)
    (hbdd : BoundedOutcomes E) :
    |E.mu0| ≤ 1 := by
  simpa [BipartiteExperiment.mu0] using
    abs_scaled_univ_sum_le_one (O := O) (fun i => E.Y0 i) (fun i => (hbdd i).2)

-- @node: centeredY1_abs_le_two
/-- Under bounded outcomes, each treated potential outcome differs from its treated mean by at most two. -/
lemma centeredY1_abs_le_two (E : BipartiteExperiment I O)
    (hbdd : BoundedOutcomes E) (i : O) :
    |E.Y1 i - E.mu1| ≤ 2 := by
  have hi := abs_le.mp (hbdd i).1
  have hmu := abs_le.mp (mu1_abs_le_one_of_bounded E hbdd)
  have hleft : -(2 : ℝ) ≤ E.Y1 i - E.mu1 := by
    calc
      -(2 : ℝ) = (-1) - (1 : ℝ) := by ring
      _ ≤ E.Y1 i - E.mu1 := sub_le_sub hi.1 hmu.2
  have hright : E.Y1 i - E.mu1 ≤ (2 : ℝ) := by
    calc
      E.Y1 i - E.mu1 ≤ (1 : ℝ) - (-1 : ℝ) := sub_le_sub hi.2 hmu.1
      _ = (2 : ℝ) := by ring
  exact abs_le.mpr ⟨hleft, hright⟩

-- @node: centeredY0_abs_le_two
/-- Under bounded outcomes, each control potential outcome differs from its control mean by at most two. -/
lemma centeredY0_abs_le_two (E : BipartiteExperiment I O)
    (hbdd : BoundedOutcomes E) (i : O) :
    |E.Y0 i - E.mu0| ≤ 2 := by
  have hi := abs_le.mp (hbdd i).2
  have hmu := abs_le.mp (mu0_abs_le_one_of_bounded E hbdd)
  have hleft : -(2 : ℝ) ≤ E.Y0 i - E.mu0 := by
    calc
      -(2 : ℝ) = (-1) - (1 : ℝ) := by ring
      _ ≤ E.Y0 i - E.mu0 := sub_le_sub hi.1 hmu.2
  have hright : E.Y0 i - E.mu0 ≤ (2 : ℝ) := by
    calc
      E.Y0 i - E.mu0 ≤ (1 : ℝ) - (-1 : ℝ) := sub_le_sub hi.2 hmu.1
      _ = (2 : ℝ) := by ring
  exact abs_le.mpr ⟨hleft, hright⟩

-- @node: r1_nonneg
/-- With strictly positive treatment probabilities no greater than one, every treated-overlap kernel is nonnegative. -/
lemma r1_nonneg (E : BipartiteExperiment I O) (p : I → ℝ)
    (hp1 : ∀ k, p k ≤ 1) (hpos : ∀ k, 0 < p k) (i j : O) :
    0 ≤ E.r1 p i j := by
  classical
  unfold BipartiteExperiment.r1
  by_cases hcard : 0 < (E.shared i j).card
  · rw [if_pos hcard]
    have hprod : (1 : ℝ) ≤ ∏ k ∈ E.shared i j, (p k)⁻¹ := by
      refine Finset.one_le_prod ?_
      intro k
      exact (one_le_inv₀ (hpos k)).mpr (hp1 k)
    exact sub_nonneg.mpr hprod
  · rw [if_neg hcard]

-- @node: r0_nonneg
/-- With control probabilities strictly positive and no greater than one, every control-overlap kernel is nonnegative. -/
lemma r0_nonneg (E : BipartiteExperiment I O) (p : I → ℝ)
    (hp0 : ∀ k, 0 ≤ p k) (hlt : ∀ k, p k < 1) (i j : O) :
    0 ≤ E.r0 p i j := by
  classical
  unfold BipartiteExperiment.r0
  by_cases hcard : 0 < (E.shared i j).card
  · rw [if_pos hcard]
    have hprod : (1 : ℝ) ≤ ∏ k ∈ E.shared i j, (1 - p k)⁻¹ := by
      refine Finset.one_le_prod ?_
      intro k
      have hpos1 : 0 < 1 - p k := sub_pos.mpr (hlt k)
      have hle1 : 1 - p k ≤ 1 := by
        simpa using sub_le_self (1 : ℝ) (hp0 k)
      exact (one_le_inv₀ hpos1).mpr hle1
    exact sub_nonneg.mpr hprod
  · rw [if_neg hcard]

-- @node: r10_nonneg
/-- Every mixed treatment-control overlap kernel is nonnegative. -/
lemma r10_nonneg (E : BipartiteExperiment I O) (i j : O) : 0 ≤ E.r10 i j := by
  unfold BipartiteExperiment.r10
  by_cases hcard : 0 < (E.shared i j).card
  · rw [if_pos hcard]
    exact zero_le_one
  · rw [if_neg hcard]

-- @node: mul_centered_pair_le_four_mul_of_nonneg
/-- A nonnegative weight times two quantities each bounded in absolute value by two is at most four times that weight. -/
lemma mul_centered_pair_le_four_mul_of_nonneg (r a b : ℝ)
    (hr : 0 ≤ r) (ha : |a| ≤ 2) (hb : |b| ≤ 2) :
    r * a * b ≤ 4 * r := by
  have hab : a * b ≤ 4 := by
    calc
      a * b ≤ |a * b| := le_abs_self (a * b)
      _ = |a| * |b| := by rw [abs_mul]
      _ ≤ 2 * 2 := by
        exact mul_le_mul ha hb (abs_nonneg b) (by positivity)
      _ = 4 := by ring
  have hmul : r * (a * b) ≤ r * 4 := mul_le_mul_of_nonneg_left hab hr
  calc
    r * a * b = r * (a * b) := by ring
    _ ≤ r * 4 := hmul
    _ = 4 * r := by ring

-- @node: pair_kernel_le_envelope_kernel
/-- Under interior assignment probabilities and bounded outcomes, each pairwise covariance contribution is no larger than four times its graph-only envelope kernel. -/
lemma pair_kernel_le_envelope_kernel
    (E : BipartiteExperiment I O) (p : I → ℝ) (hp0 : ∀ k, 0 ≤ p k)
    (hp1 : ∀ k, p k ≤ 1) (hpos : ∀ k, 0 < p k) (hlt : ∀ k, p k < 1)
    (hbdd : BoundedOutcomes E) (i j : O) :
    E.r1 p i j * (E.Y1 i - E.mu1) * (E.Y1 j - E.mu1)
      + E.r0 p i j * (E.Y0 i - E.mu0) * (E.Y0 j - E.mu0)
      + 2 * E.r10 i j * (E.Y1 i - E.mu1) * (E.Y0 j - E.mu0)
      ≤ 4 * (E.r1 p i j + E.r0 p i j + 2 * E.r10 i j) := by
  have h1 := mul_centered_pair_le_four_mul_of_nonneg
    (E.r1 p i j) (E.Y1 i - E.mu1) (E.Y1 j - E.mu1)
    (r1_nonneg E p hp1 hpos i j)
    (centeredY1_abs_le_two E hbdd i) (centeredY1_abs_le_two E hbdd j)
  have h0 := mul_centered_pair_le_four_mul_of_nonneg
    (E.r0 p i j) (E.Y0 i - E.mu0) (E.Y0 j - E.mu0)
    (r0_nonneg E p hp0 hlt i j)
    (centeredY0_abs_le_two E hbdd i) (centeredY0_abs_le_two E hbdd j)
  have h10 := mul_centered_pair_le_four_mul_of_nonneg
    (2 * E.r10 i j) (E.Y1 i - E.mu1) (E.Y0 j - E.mu0)
    (mul_nonneg (by positivity) (r10_nonneg E i j))
    (centeredY1_abs_le_two E hbdd i) (centeredY0_abs_le_two E hbdd j)
  calc
    E.r1 p i j * (E.Y1 i - E.mu1) * (E.Y1 j - E.mu1)
      + E.r0 p i j * (E.Y0 i - E.mu0) * (E.Y0 j - E.mu0)
      + 2 * E.r10 i j * (E.Y1 i - E.mu1) * (E.Y0 j - E.mu0)
        ≤ 4 * E.r1 p i j + 4 * E.r0 p i j + 4 * (2 * E.r10 i j) := by
          exact add_le_add (add_le_add h1 h0) h10
    _ = 4 * (E.r1 p i j + E.r0 p i j + 2 * E.r10 i j) := by ring

-- @node: thm:hetero-envelope
/-- **Heterogeneous envelope kernel.** Under the independent heterogeneous Bernoulli
design and bounded outcomes, the covariance of the linearization scores factors
through the overlap loads, and the variance scale is dominated by the observable
graph-only envelope. -/
theorem hetero_envelope
    (E : BipartiteExperiment I O)
    (D : FiniteDesign (I → Bool)) (p : I → ℝ) (hp0 : ∀ k, 0 ≤ p k) (hp1 : ∀ k, p k ≤ 1)
    (hpos : ∀ k, 0 < p k) (hlt : ∀ k, p k < 1)
    (hBern : IndepHeteroBernoulli D p hp0 hp1)
    (hbdd : BoundedOutcomes E) :
    (∀ i j, D.E (fun z => E.linScore p z i * E.linScore p z j)
        = E.r1 p i j * (E.Y1 i - E.mu1) * (E.Y1 j - E.mu1)
          + E.r0 p i j * (E.Y0 i - E.mu0) * (E.Y0 j - E.mu0)
          + E.r10 i j * ((E.Y1 i - E.mu1) * (E.Y0 j - E.mu0)
                          + (E.Y0 i - E.mu0) * (E.Y1 j - E.mu1)))
    ∧ E.varScale D p ≤ E.varEnvelope p := by
  refine ⟨fun i j => linScore_pair_moment E D p hp0 hp1 hpos hlt hBern i j, ?_⟩
  rw [varScale_homogeneous_formula E D p hp0 hp1 hpos hlt hBern]
  unfold BipartiteExperiment.varEnvelope
  have hsum : (∑ i : O, ∑ j : O,
      (E.r1 p i j * (E.Y1 i - E.mu1) * (E.Y1 j - E.mu1)
       + E.r0 p i j * (E.Y0 i - E.mu0) * (E.Y0 j - E.mu0)
       + 2 * E.r10 i j * (E.Y1 i - E.mu1) * (E.Y0 j - E.mu0)))
      ≤ ∑ i : O, ∑ j : O, 4 * (E.r1 p i j + E.r0 p i j + 2 * E.r10 i j) := by
    refine Finset.sum_le_sum ?_
    intro i _
    refine Finset.sum_le_sum ?_
    intro j _
    exact pair_kernel_le_envelope_kernel E p hp0 hp1 hpos hlt hbdd i j
  have hn : 0 ≤ (Fintype.card O : ℝ)⁻¹ := by
    exact inv_nonneg.mpr (Nat.cast_nonneg (Fintype.card O))
  have hscaled := mul_le_mul_of_nonneg_left hsum hn
  calc
    (Fintype.card O : ℝ)⁻¹ * ∑ i : O, ∑ j : O,
      (E.r1 p i j * (E.Y1 i - E.mu1) * (E.Y1 j - E.mu1)
       + E.r0 p i j * (E.Y0 i - E.mu0) * (E.Y0 j - E.mu0)
       + 2 * E.r10 i j * (E.Y1 i - E.mu1) * (E.Y0 j - E.mu0))
        ≤ (Fintype.card O : ℝ)⁻¹ * ∑ i : O, ∑ j : O,
            4 * (E.r1 p i j + E.r0 p i j + 2 * E.r10 i j) := hscaled
    _ = 4 * (Fintype.card O : ℝ)⁻¹ * ∑ i : O, ∑ j : O,
            (E.r1 p i j + E.r0 p i j + 2 * E.r10 i j) := by
          simp_rw [← Finset.mul_sum]
          ring

end CausalSmith.Experimentation.BipartiteMinimaxDesign
