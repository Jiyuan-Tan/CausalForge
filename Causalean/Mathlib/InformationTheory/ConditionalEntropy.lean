/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Mathlib.InformationTheory.Entropy
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
# Conditional Shannon entropy and the Gibbs (cross-entropy) inequality

This module sets up the finite-alphabet objects feeding **Fano's inequality** and
proves the single information-theoretic inequality the Fano proof rests on.

For a joint mass function `p : α × β → ℝ` we define the `β`-marginal
`yMarginal p y = ∑ x, p (x, y)` and the conditional entropy via the chain rule
`condEntropy p = entropy p − entropy (yMarginal p)` (i.e. `H(X ∣ Y) = H(X,Y) − H(Y)`),
reusing the entropy core `Causalean.Mathlib.InformationTheory.entropy`.

The crux fact is the **Gibbs / cross-entropy inequality** `entropy_le_crossEntropy`:
for a pmf `p` and any sub-pmf `g` that dominates the support of `p`,
`entropy p ≤ −∑ i, p i · log (g i)`. Specialising `g` to a cleverly chosen reference
distribution turns this single inequality into Fano's bound (see `Fano.lean`); this
mirrors the entropy core's `entropy_le_log_card` (which is the case `g ≡ 1 / card`).

Main definitions:
* `yMarginal p` — the `β`-marginal of a joint mass function on `α × β`.
* `condEntropy p` — conditional entropy `H(X ∣ Y) = entropy p − entropy (yMarginal p)`.
* `errorProb p decode` — the error probability `∑_{x ≠ decode y} p (x, y)` of a
  deterministic decoder `decode : β → α`.

Main results:
* `negMulLog_add_mul_log_le` — the per-coordinate Gibbs lever.
* `entropy_le_crossEntropy` — the Gibbs / cross-entropy inequality.
* `yMarginal_sum`, `errorProb_nonneg`, `errorProb_le_one` — supporting pmf facts.

Reference: Cover & Thomas, *Elements of Information Theory* (2e), §2.10, Thm 2.10.1.
-/

namespace Causalean.Mathlib.InformationTheory

open scoped BigOperators
open Causalean.Mathlib.InformationTheory

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]

/-- The `β`-marginal of a joint mass function `p : α × β → ℝ`:
`yMarginal p y = ∑ x, p (x, y)`. This is the mass of the conditioning variable `Y`. -/
noncomputable def yMarginal (p : α × β → ℝ) (y : β) : ℝ := ∑ x, p (x, y)

/-- Conditional Shannon entropy `H(X ∣ Y)` of a joint mass function `p : α × β → ℝ`,
defined via the chain rule `H(X ∣ Y) = H(X,Y) − H(Y)`, i.e.
`entropy p − entropy (yMarginal p)`. -/
noncomputable def condEntropy (p : α × β → ℝ) : ℝ :=
  entropy p - entropy (yMarginal p)

omit [DecidableEq α] in
/-- Error probability of a deterministic decoder `decode : β → α` under the joint mass
function `p`: the total mass on cells where the decoder is wrong,
`∑_{x ≠ decode y} p (x, y)`. Encoded with an `if` so the correct cells contribute `0`. -/
noncomputable def errorProb (p : α × β → ℝ) (decode : β → α) : ℝ := by
  classical
  exact ∑ xy : α × β, (if xy.1 = decode xy.2 then 0 else p xy)

omit [Fintype β] [DecidableEq α] in
/-- The `β`-marginal is the finite sum of joint masses over the `α`
coordinate at the chosen value of `β`. -/
@[simp] lemma yMarginal_def (p : α × β → ℝ) (y : β) :
    yMarginal p y = ∑ x, p (x, y) := rfl

omit [DecidableEq α] in
/-- Conditional entropy unfolds to total joint entropy minus the entropy of the
conditioning marginal. -/
@[simp] lemma condEntropy_def (p : α × β → ℝ) :
    condEntropy p = entropy p - entropy (yMarginal p) := rfl

/-- The decoder error probability unfolds to the sum of the joint masses on
incorrect decoding cells. -/
@[simp] lemma errorProb_def (p : α × β → ℝ) (decode : β → α) :
    errorProb p decode = ∑ xy : α × β, (if xy.1 = decode xy.2 then 0 else p xy) := rfl

/-- **Per-coordinate Gibbs lever.** For `0 ≤ x` and `0 ≤ g`, with `g` positive whenever
`x` is nonzero (absolute continuity), the cross-entropy summand is controlled:
`Real.negMulLog x + x * Real.log g ≤ g - x`.

On the support (`x > 0`, hence `g > 0`) this is `x · log (g / x) ≤ x · (g/x − 1)` via
`Real.log_le_sub_one_of_pos`; off the support (`x = 0`) the left side vanishes and the
bound reads `0 ≤ g`. Summing this over a finite index set yields the Gibbs inequality. -/
lemma negMulLog_add_mul_log_le {x g : ℝ} (hx : 0 ≤ x) (hg : 0 ≤ g)
    (hac : x ≠ 0 → 0 < g) :
    Real.negMulLog x + x * Real.log g ≤ g - x := by
  rcases eq_or_lt_of_le hx with rfl | hxpos
  · simpa [Real.negMulLog] using hg
  · have hgpos : 0 < g := hac hxpos.ne'
    have hlog := Real.log_le_sub_one_of_pos
      (show (0 : ℝ) < g / x by positivity)
    have hid : Real.negMulLog x + x * Real.log g = x * Real.log (g / x) := by
      rw [Real.negMulLog_def]
      rw [Real.log_div hgpos.ne' hxpos.ne']
      ring
    have hmul := mul_le_mul_of_nonneg_left hlog (le_of_lt hxpos)
    calc
      Real.negMulLog x + x * Real.log g = x * Real.log (g / x) := hid
      _ ≤ x * (g / x - 1) := hmul
      _ = g - x := by
        field_simp [hxpos.ne']

/-- **Gibbs / cross-entropy inequality.** For [a nonnegative mass function `p`](hyp:hp0) and
[a nonnegative reference mass function `g`](hyp:hg0) on a finite type `γ`, if
[the total mass of `g` is at most the total mass of `p`](hyp:hgsum) (`∑ g ≤ ∑ p`) and `g`
[dominates the support of `p`](hyp:hac) (`p i ≠ 0 → 0 < g i`), then [the Shannon entropy of `p`
is bounded by the cross-entropy of `p` relative to `g`](goal):
`entropy p ≤ −∑ i, p i * Real.log (g i)`.

This is the elementary Gibbs argument: sum `negMulLog_add_mul_log_le` over `γ`. The right
telescopes to `∑ g − ∑ p ≤ 0`, leaving `entropy p + ∑ p log g ≤ 0`. It generalises
the entropy core's `entropy_le_log_card` (case `g ≡ (card γ)⁻¹`) and is the only
information-theoretic inequality Fano's proof needs. -/
theorem entropy_le_crossEntropy {γ : Type*} [Fintype γ] {p g : γ → ℝ}
    (hp0 : ∀ i, 0 ≤ p i)
    (hg0 : ∀ i, 0 ≤ g i) (hgsum : ∑ i, g i ≤ ∑ i, p i)
    (hac : ∀ i, p i ≠ 0 → 0 < g i) :
    entropy p ≤ - ∑ i, p i * Real.log (g i) := by
  have hterm :
      (∑ i, (Real.negMulLog (p i) + p i * Real.log (g i))) ≤
        ∑ i, (g i - p i) := by
    exact Finset.sum_le_sum (fun i _ => negMulLog_add_mul_log_le (hp0 i) (hg0 i) (hac i))
  have hleft :
      (∑ i, (Real.negMulLog (p i) + p i * Real.log (g i))) =
        entropy p + ∑ i, p i * Real.log (g i) := by
    calc
      (∑ i, (Real.negMulLog (p i) + p i * Real.log (g i)))
          = (∑ i, Real.negMulLog (p i)) + ∑ i, p i * Real.log (g i) := by
            rw [Finset.sum_add_distrib]
      _ = entropy p + ∑ i, p i * Real.log (g i) := by
            rw [entropy_def]
  have hright : (∑ i, (g i - p i)) ≤ 0 := by
    calc
      (∑ i, (g i - p i)) = (∑ i, g i) - ∑ i, p i := by
        rw [Finset.sum_sub_distrib]
      _ ≤ 0 := by
        exact sub_nonpos.mpr hgsum
  have : entropy p + ∑ i, p i * Real.log (g i) ≤ 0 := by
    linarith
  linarith

omit [DecidableEq α] in
/-- The `β`-marginal of a pmf is itself a pmf summing to one: if `∑ xy, p xy = 1`
then `∑ y, yMarginal p y = 1`. -/
lemma yMarginal_sum {p : α × β → ℝ} (hsum : ∑ xy : α × β, p xy = 1) :
    ∑ y, yMarginal p y = 1 := by
  simp only [yMarginal_def]
  rw [← Fintype.sum_prod_type_right]
  exact hsum

omit [Fintype β] [DecidableEq α] in
/-- The `β`-marginal of a nonnegative mass function is nonnegative. -/
lemma yMarginal_nonneg {p : α × β → ℝ} (hp0 : ∀ xy, 0 ≤ p xy) (y : β) :
    0 ≤ yMarginal p y := by
  rw [yMarginal_def]
  exact Finset.sum_nonneg (fun x _ => hp0 (x, y))

omit [Fintype β] [DecidableEq α] in
/-- A joint mass is dominated by its `β`-marginal: `p (x, y) ≤ yMarginal p y`
for nonnegative `p`. -/
lemma le_yMarginal {p : α × β → ℝ} (hp0 : ∀ xy, 0 ≤ p xy) (x : α) (y : β) :
    p (x, y) ≤ yMarginal p y := by
  rw [yMarginal_def]
  exact Finset.single_le_sum (fun x' _ => hp0 (x', y)) (Finset.mem_univ x)

/-- The error probability is nonnegative. -/
lemma errorProb_nonneg {p : α × β → ℝ} (hp0 : ∀ xy, 0 ≤ p xy) (decode : β → α) :
    0 ≤ errorProb p decode := by
  rw [errorProb_def]
  refine Finset.sum_nonneg ?_
  intro xy _
  split_ifs
  · exact le_refl 0
  · exact hp0 xy

/-- The error probability is at most one (it is a sub-sum of the total mass `= 1`). -/
lemma errorProb_le_one {p : α × β → ℝ} (hp0 : ∀ xy, 0 ≤ p xy)
    (hsum : ∑ xy : α × β, p xy = 1) (decode : β → α) :
    errorProb p decode ≤ 1 := by
  rw [errorProb_def, ← hsum]
  refine Finset.sum_le_sum ?_
  intro xy _
  split_ifs
  · exact hp0 xy
  · exact le_refl (p xy)

/-- The correct-decision mass equals `1 − errorProb`: splitting the total mass `= 1` into
the correct cells (`x = decode y`) and the error cells gives
`∑_{x = decode y} p (x, y) = 1 − errorProb p decode`. -/
lemma correctMass_eq {p : α × β → ℝ} (hsum : ∑ xy : α × β, p xy = 1) (decode : β → α) :
    (∑ xy : α × β, (if xy.1 = decode xy.2 then p xy else 0)) = 1 - errorProb p decode := by
  have hterm :
      (∑ xy : α × β, (if xy.1 = decode xy.2 then p xy else 0)) =
        ∑ xy : α × β, (p xy - (if xy.1 = decode xy.2 then 0 else p xy)) := by
    refine Finset.sum_congr rfl ?_
    intro xy _
    split_ifs <;> ring
  rw [hterm, Finset.sum_sub_distrib, hsum, errorProb_def]

end Causalean.Mathlib.InformationTheory
