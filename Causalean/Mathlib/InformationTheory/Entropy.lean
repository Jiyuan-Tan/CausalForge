/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Data.Fintype.BigOperators

/-!
# Finite-alphabet Shannon entropy and the maximum-entropy bound

This module builds the Shannon entropy of a (probability) mass function on a finite
alphabet `α` together with its maximum-entropy / Gibbs bound `H(p) ≤ log (card α)`,
which Mathlib does not provide for general `Fintype α` (it only has the binary case
`Real.binEntropy_le_log_two`).

The entropy is defined in *nats* as `entropy p = ∑ i, Real.negMulLog (p i)` for any
real-valued `p : α → ℝ`; the probability-mass hypotheses (`0 ≤ p i`, `∑ i, p i = 1`)
enter only the lemmas, never the definition.

Main results:
* `entropy_nonneg` — entropy of a sub-probability vector is nonnegative.
* `entropy_le_log_card` — the maximum-entropy (Gibbs) bound `H(p) ≤ log (card α)`,
  proved elementarily from `Real.log_le_sub_one_of_pos` (no Jensen/Gibbs black box).
* `entropy_const_eq_log_card` — the uniform pmf attains the bound, witnessing that the
  bound is sharp (and the statement non-vacuous).

This is the finite-entropy core meant to be reused by information-theoretic arguments
(Fano's inequality, max-entropy priors, mutual-information / capacity bounds). It is
stated generically over an arbitrary `Fintype α`.

Reference: Cover & Thomas, *Elements of Information Theory* (2e), §2.1 and Thm 2.6.4.
-/

namespace Causalean.Mathlib.InformationTheory

open scoped BigOperators

variable {α : Type*} [Fintype α]

/-- Shannon entropy (in nats) of a real-valued mass function `p : α → ℝ` on a finite
alphabet `α`, defined as `∑ i, Real.negMulLog (p i) = ∑ i, -(p i) * log (p i)`.

The definition makes no positivity or normalization assumption on `p`; the
probability-mass hypotheses enter the lemmas about `entropy`. -/
noncomputable def entropy (p : α → ℝ) : ℝ :=
  ∑ i, Real.negMulLog (p i)

/-- The finite-alphabet entropy definition unfolds to the sum of
`Real.negMulLog` over the alphabet. -/
@[simp] lemma entropy_def (p : α → ℝ) : entropy p = ∑ i, Real.negMulLog (p i) := rfl

/-- Entropy is nonnegative for any sub-probability vector: if `0 ≤ p i ≤ 1` for every
`i`, then `0 ≤ entropy p`. Each summand `Real.negMulLog (p i)` is nonnegative on `[0,1]`
(`Real.negMulLog_nonneg`), so the finite sum is nonnegative. -/
lemma entropy_nonneg {p : α → ℝ} (h0 : ∀ i, 0 ≤ p i) (h1 : ∀ i, p i ≤ 1) :
    0 ≤ entropy p := by
  rw [entropy_def]
  refine Finset.sum_nonneg ?_
  intro i _
  exact Real.negMulLog_nonneg (h0 i) (h1 i)

/-- Per-coordinate Gibbs lever. For a single coordinate of a pmf on an alphabet of
cardinality `n`, the entropy summand minus `p i · log n` is bounded by `1/n - p i`:
`Real.negMulLog (p i) - p i * Real.log n ≤ (n : ℝ)⁻¹ - p i`.

On the support (`p i > 0`) this is `p i · log (1 / (n · p i)) ≤ p i · (1/(n p i) - 1)`
via `Real.log_le_sub_one_of_pos`; off the support (`p i = 0`) both `negMulLog` and the
product vanish and the bound is `0 ≤ (n : ℝ)⁻¹`. Summing this over `α` yields the
maximum-entropy bound. -/
lemma negMulLog_sub_mul_log_le {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    Real.negMulLog x - x * Real.log n ≤ (n : ℝ)⁻¹ - x := by
  rcases eq_or_lt_of_le hx with rfl | hxpos
  · simp [Real.negMulLog]
  · have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hlog := Real.log_le_sub_one_of_pos
      (show (0 : ℝ) < ((n : ℝ) * x)⁻¹ by positivity)
    have hlogeq : Real.log (((n : ℝ) * x)⁻¹) = -(Real.log (n : ℝ) + Real.log x) := by
      rw [Real.log_inv]
      rw [Real.log_mul hnR.ne' hxpos.ne']
    have hid : Real.negMulLog x - x * Real.log n =
        x * Real.log (((n : ℝ) * x)⁻¹) := by
      rw [Real.negMulLog_def]
      rw [hlogeq]
      ring
    have hmul := mul_le_mul_of_nonneg_left hlog (le_of_lt hxpos)
    calc
      Real.negMulLog x - x * Real.log n = x * Real.log (((n : ℝ) * x)⁻¹) := hid
      _ ≤ x * (((n : ℝ) * x)⁻¹ - 1) := hmul
      _ = (n : ℝ)⁻¹ - x := by
        field_simp [hnR.ne', hxpos.ne']

/-- **Maximum-entropy (Gibbs) bound.** For a probability mass function `p` on a nonempty
finite alphabet `α` with `n = Fintype.card α`, the Shannon entropy is at most `log n`:
`entropy p ≤ Real.log (Fintype.card α)`.

This is Cover & Thomas Thm 2.6.4 (`H(p) ≤ log |𝒳|`). The proof is the elementary Gibbs
argument: sum the per-coordinate bound `negMulLog_sub_mul_log_le` over `α`. The right
side telescopes to `n · (1/n) - 1 = 0` (using `∑ p i = 1`), and the left side is
`entropy p - log n`, giving `entropy p - log n ≤ 0`. -/
theorem entropy_le_log_card [Nonempty α] {p : α → ℝ} (h0 : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) : entropy p ≤ Real.log (Fintype.card α) := by
  let n := Fintype.card α
  have hn : 0 < n := Fintype.card_pos
  have hterm :
      (∑ i, (Real.negMulLog (p i) - p i * Real.log (n : ℝ))) ≤
        ∑ i, ((n : ℝ)⁻¹ - p i) := by
    exact Finset.sum_le_sum (fun i _ => negMulLog_sub_mul_log_le hn (h0 i))
  have hleft :
      (∑ i, (Real.negMulLog (p i) - p i * Real.log (n : ℝ))) =
        entropy p - Real.log (n : ℝ) := by
    calc
      (∑ i, (Real.negMulLog (p i) - p i * Real.log (n : ℝ)))
          = (∑ i, Real.negMulLog (p i)) - (∑ i, p i * Real.log (n : ℝ)) := by
            rw [Finset.sum_sub_distrib]
      _ = entropy p - (∑ i, p i) * Real.log (n : ℝ) := by
            rw [entropy]
            rw [Finset.sum_mul]
      _ = entropy p - Real.log (n : ℝ) := by
            rw [hsum]
            ring
  have hright : (∑ i, ((n : ℝ)⁻¹ - p i)) = 0 := by
    calc
      (∑ i, ((n : ℝ)⁻¹ - p i)) = (∑ i : α, (n : ℝ)⁻¹) - ∑ i, p i := by
        rw [Finset.sum_sub_distrib]
      _ = (n : ℝ) * (n : ℝ)⁻¹ - 1 := by
        rw [Finset.sum_const, Finset.card_univ, hsum]
        simp [n]
      _ = 0 := by
        have hnR : (n : ℝ) ≠ 0 := by positivity
        field_simp [hnR]
        ring
  have : entropy p - Real.log (n : ℝ) ≤ 0 := by
    linarith
  have : entropy p ≤ Real.log (n : ℝ) := by
    linarith
  simpa [n] using this

/-- **Sharpness of the maximum-entropy bound.** The uniform pmf `p i = (card α)⁻¹` on a
nonempty finite alphabet attains the bound:
`entropy (fun _ => (Fintype.card α : ℝ)⁻¹) = Real.log (Fintype.card α)`.

Each of the `n = card α` summands equals `negMulLog (1/n) = (1/n) · log n`, so the sum is
`n · (1/n) · log n = log n`. This certifies that `entropy_le_log_card` is tight, hence
non-vacuous. -/
theorem entropy_const_eq_log_card [Nonempty α] :
    entropy (fun _ : α => (Fintype.card α : ℝ)⁻¹) = Real.log (Fintype.card α) := by
  let n := Fintype.card α
  have hn : 0 < n := Fintype.card_pos
  have hnR : (n : ℝ) ≠ 0 := by positivity
  have hneg : Real.negMulLog ((n : ℝ)⁻¹) = (n : ℝ)⁻¹ * Real.log (n : ℝ) := by
    simp [Real.negMulLog_def, Real.log_inv]
  have hmain : entropy (fun _ : α => (n : ℝ)⁻¹) = Real.log (n : ℝ) := by
    calc
      entropy (fun _ : α => (n : ℝ)⁻¹)
          = (n : ℝ) * Real.negMulLog ((n : ℝ)⁻¹) := by
            simp [entropy, Finset.sum_const, Finset.card_univ, n]
      _ = (n : ℝ) * ((n : ℝ)⁻¹ * Real.log (n : ℝ)) := by
            rw [hneg]
      _ = Real.log (n : ℝ) := by
            field_simp [hnR]
  simpa [n] using hmain

end Causalean.Mathlib.InformationTheory
