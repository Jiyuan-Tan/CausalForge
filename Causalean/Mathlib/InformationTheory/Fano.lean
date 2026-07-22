/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Mathlib.InformationTheory.ConditionalEntropy

/-!
# Fano's inequality

This module proves the classical **Fano inequality** (Cover & Thomas, *Elements of
Information Theory* (2e), Thm 2.10.1): for a joint mass function `p : α × β → ℝ` over
finite alphabets, a deterministic decoder `decode : β → α`, and the error probability
`Pe = errorProb p decode`, the conditional entropy obeys

`condEntropy p ≤ Real.binEntropy Pe + Pe * Real.log (Fintype.card α − 1)`.

The proof applies the single Gibbs inequality `entropy_le_crossEntropy` from
`ConditionalEntropy.lean` to the **reference distribution** `fanoRef`, which on each
column `y` spreads mass
`1 − Pe` on the decoded symbol `decode y` and the remaining mass `Pe` uniformly over the
`card α − 1` incorrect symbols. Computing the resulting cross-entropy yields exactly
`entropy (yMarginal p) + binEntropy Pe + Pe · log (card α − 1)`, and subtracting
`entropy (yMarginal p)` gives Fano's bound. The `card α − 1` (rather than `card α`) is the
crux of the theorem and comes from the size of the error block.

Main results:
* `fano_inequality` — Fano's inequality in its sharp form.
* `fano_error_lower_bound` — the standard weakened corollary lower-bounding `Pe`.

Reference: Cover & Thomas, *Elements of Information Theory* (2e), §2.10, Thm 2.10.1.
-/

namespace Causalean.Mathlib.InformationTheory

open scoped BigOperators
open Causalean.Mathlib.InformationTheory

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]

/-- The **Fano reference distribution** on `α × β`. On each column `y` it places mass
`(1 − Pe)` on the decoded symbol `decode y` and spreads the error mass `Pe` uniformly over
the `card α − 1` other symbols, then weights the column by the marginal `yMarginal p y`:
`fanoRef p decode (x, y) = yMarginal p y · (if x = decode y then 1 − Pe else Pe / (card α − 1))`
where `Pe = errorProb p decode`. It is the worst-case posterior that makes Gibbs tight. -/
noncomputable def fanoRef (p : α × β → ℝ) (decode : β → α) (xy : α × β) : ℝ :=
  yMarginal p xy.2 *
    (if xy.1 = decode xy.2 then 1 - errorProb p decode
      else errorProb p decode / ((Fintype.card α : ℝ) - 1))

@[simp] lemma fanoRef_def (p : α × β → ℝ) (decode : β → α) (xy : α × β) :
    fanoRef p decode xy =
      yMarginal p xy.2 *
        (if xy.1 = decode xy.2 then 1 - errorProb p decode
          else errorProb p decode / ((Fintype.card α : ℝ) - 1)) := rfl

/-- The Fano reference distribution is nonnegative. -/
lemma fanoRef_nonneg {p : α × β → ℝ} (hp0 : ∀ xy, 0 ≤ p xy)
    (hsum : ∑ xy : α × β, p xy = 1) (hcard : 2 ≤ Fintype.card α) (decode : β → α)
    (xy : α × β) : 0 ≤ fanoRef p decode xy := by
  rw [fanoRef_def]
  refine mul_nonneg (yMarginal_nonneg hp0 xy.2) ?_
  split_ifs
  · exact sub_nonneg.mpr (errorProb_le_one hp0 hsum decode)
  · exact div_nonneg (errorProb_nonneg hp0 decode) (by
      have hMge1 : (1 : ℝ) ≤ (Fintype.card α : ℝ) := by
        exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) hcard)
      linarith)

/-- The Fano reference distribution is a probability mass function: `∑ xy, fanoRef = 1`.
On each column the inner weights sum to `(1 − Pe) + (card α − 1) · Pe/(card α − 1) = 1`,
so the total is `∑ y, yMarginal p y = 1`. -/
lemma fanoRef_sum_eq_one {p : α × β → ℝ} (hp0 : ∀ xy, 0 ≤ p xy)
    (hsum : ∑ xy : α × β, p xy = 1) (hcard : 2 ≤ Fintype.card α) (decode : β → α) :
    ∑ xy : α × β, fanoRef p decode xy = 1 := by
  classical
  have _ := hp0
  let Pe : ℝ := errorProb p decode
  let M : ℝ := Fintype.card α
  have hMne : M - 1 ≠ 0 := by
    have hMgt : 1 < M := by
      dsimp [M]
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hcard)
    linarith
  have hinner :
      ∀ y : β,
        (∑ x : α, (if x = decode y then 1 - Pe else Pe / (M - 1))) = 1 := by
    intro y
    calc
      (∑ x : α, (if x = decode y then 1 - Pe else Pe / (M - 1)))
          = ∑ x : α, ((if x = decode y then (1 - Pe) - Pe / (M - 1) else 0)
              + Pe / (M - 1)) := by
            refine Finset.sum_congr rfl ?_
            intro x hx
            by_cases h : x = decode y <;> simp [h]
      _ = (∑ x : α, (if x = decode y then (1 - Pe) - Pe / (M - 1) else 0))
          + ∑ x : α, Pe / (M - 1) := by
            simp [Finset.sum_add_distrib]
      _ = ((1 - Pe) - Pe / (M - 1)) + (Fintype.card α : ℝ) * (Pe / (M - 1)) := by
            have hsingle :
                (∑ x : α, (if x = decode y then (1 - Pe) - Pe / (M - 1) else 0))
                  = (1 - Pe) - Pe / (M - 1) := by
              rw [Finset.sum_ite_eq' Finset.univ (decode y)]
              simp
            rw [hsingle]
            simp
      _ = 1 := by
            dsimp [M] at hMne ⊢
            field_simp [hMne]
            ring
  rw [Fintype.sum_prod_type]
  calc
    (∑ x : α, ∑ y : β, fanoRef p decode (x, y))
        = ∑ y : β, ∑ x : α, fanoRef p decode (x, y) := by
          rw [Finset.sum_comm]
    _ = ∑ y : β, yMarginal p y * 1 := by
          refine Finset.sum_congr rfl ?_
          intro y hy
          simp_rw [fanoRef_def]
          rw [← Finset.mul_sum]
          simpa [Pe, M] using congrArg (fun z => yMarginal p y * z) (hinner y)
    _ = 1 := by
          simpa using yMarginal_sum (α := α) (β := β) hsum

/-- The Fano reference distribution dominates the support of `p`: `p xy ≠ 0 → 0 < fanoRef xy`.
A nonzero `p (x, y)` forces `yMarginal p y > 0`; on a correct cell the complementary mass
`1 − Pe ≥ p (x,y) > 0` and on an error cell `Pe ≥ p (x,y) > 0`, so the inner weight is
positive. This is the absolute-continuity hypothesis of the Gibbs inequality. -/
lemma fanoRef_ac {p : α × β → ℝ} (hp0 : ∀ xy, 0 ≤ p xy)
    (hsum : ∑ xy : α × β, p xy = 1) (hcard : 2 ≤ Fintype.card α) (decode : β → α)
    (xy : α × β) (hxy : p xy ≠ 0) : 0 < fanoRef p decode xy := by
  classical
  have hpxy_pos : 0 < p xy := lt_of_le_of_ne (hp0 xy) (Ne.symm hxy)
  have hy_pos : 0 < yMarginal p xy.2 :=
    lt_of_lt_of_le hpxy_pos (by
      simpa [xy.eta] using le_yMarginal hp0 xy.1 xy.2)
  have hMpos : 0 < (Fintype.card α : ℝ) - 1 := by
    have hMgt : (1 : ℝ) < Fintype.card α := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hcard)
    linarith
  rw [fanoRef_def]
  refine mul_pos hy_pos ?_
  split_ifs with hc
  · have hterm_nonneg :
        ∀ z : α × β, z ∈ Finset.univ →
          0 ≤ (if z.1 = decode z.2 then p z else 0) := by
      intro z hz
      split_ifs <;> simp [hp0]
    have hle :
        p xy ≤ ∑ z : α × β, (if z.1 = decode z.2 then p z else 0) := by
      simpa [hc] using
        (Finset.single_le_sum (f := fun z : α × β =>
          if z.1 = decode z.2 then p z else 0) hterm_nonneg
          (Finset.mem_univ xy))
    rw [correctMass_eq hsum decode] at hle
    exact lt_of_lt_of_le hpxy_pos hle
  · have hterm_nonneg :
        ∀ z : α × β, z ∈ Finset.univ →
          0 ≤ (if z.1 = decode z.2 then 0 else p z) := by
      intro z hz
      split_ifs <;> simp [hp0]
    have hle :
        p xy ≤ ∑ z : α × β, (if z.1 = decode z.2 then 0 else p z) := by
      simpa [hc] using
        (Finset.single_le_sum (f := fun z : α × β =>
          if z.1 = decode z.2 then 0 else p z) hterm_nonneg
          (Finset.mem_univ xy))
    rw [← errorProb_def p decode] at hle
    exact div_pos (lt_of_lt_of_le hpxy_pos hle) hMpos

/-- The cross-entropy of `p` against the Fano reference splits, via the chain rule for
`log` on the support of `p`, into the marginal entropy plus the binary-entropy/error terms:
`−∑ xy, p xy · log (fanoRef p decode xy)
  = entropy (yMarginal p) + Real.binEntropy Pe + Pe · Real.log (card α − 1)`,
where `Pe = errorProb p decode`. This is the key algebraic computation behind Fano. -/
lemma neg_crossEntropy_fanoRef {p : α × β → ℝ} (hp0 : ∀ xy, 0 ≤ p xy)
    (hsum : ∑ xy : α × β, p xy = 1) (hcard : 2 ≤ Fintype.card α) (decode : β → α) :
    (- ∑ xy : α × β, p xy * Real.log (fanoRef p decode xy))
      = entropy (yMarginal p) + Real.binEntropy (errorProb p decode)
          + errorProb p decode * Real.log ((Fintype.card α : ℝ) - 1) := by
  classical
  let Pe : ℝ := errorProb p decode
  let M : ℝ := Fintype.card α
  let inner : α × β → ℝ := fun xy =>
    if xy.1 = decode xy.2 then 1 - Pe else Pe / (M - 1)
  have hMpos : 0 < M - 1 := by
    have hMgt : (1 : ℝ) < M := by
      dsimp [M]
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hcard)
    linarith
  have hMne : M - 1 ≠ 0 := ne_of_gt hMpos
  have hsum_split :
      (∑ xy : α × β, p xy * Real.log (fanoRef p decode xy))
        = (∑ xy : α × β, p xy * Real.log (yMarginal p xy.2))
          + ∑ xy : α × β, p xy * Real.log (inner xy) := by
    calc
      (∑ xy : α × β, p xy * Real.log (fanoRef p decode xy))
          = ∑ xy : α × β,
              (p xy * Real.log (yMarginal p xy.2)
                + p xy * Real.log (inner xy)) := by
            refine Finset.sum_congr rfl ?_
            intro xy hxy_mem
            by_cases hpz : p xy = 0
            · simp [hpz]
            · have hpxy_pos : 0 < p xy := lt_of_le_of_ne (hp0 xy) (Ne.symm hpz)
              have hy_pos : 0 < yMarginal p xy.2 :=
                lt_of_lt_of_le hpxy_pos (by
                  simpa [xy.eta] using le_yMarginal hp0 xy.1 xy.2)
              have hfr_pos := fanoRef_ac hp0 hsum hcard decode xy hpz
              have hfr_eq : fanoRef p decode xy = yMarginal p xy.2 * inner xy := by
                simp [fanoRef_def, inner, Pe, M]
              have hinner_pos : 0 < inner xy := by
                rw [hfr_eq] at hfr_pos
                exact pos_of_mul_pos_right hfr_pos (le_of_lt hy_pos)
              calc
                p xy * Real.log (fanoRef p decode xy)
                    = p xy * (Real.log (yMarginal p xy.2) + Real.log (inner xy)) := by
                      rw [hfr_eq, Real.log_mul hy_pos.ne' hinner_pos.ne']
                _ = p xy * Real.log (yMarginal p xy.2)
                    + p xy * Real.log (inner xy) := by ring
      _ = (∑ xy : α × β, p xy * Real.log (yMarginal p xy.2))
          + ∑ xy : α × β, p xy * Real.log (inner xy) := by
            rw [Finset.sum_add_distrib]
  have hYlog :
      (∑ xy : α × β, p xy * Real.log (yMarginal p xy.2))
        = - entropy (yMarginal p) := by
    calc
      (∑ xy : α × β, p xy * Real.log (yMarginal p xy.2))
          = ∑ x : α, ∑ y : β, p (x, y) * Real.log (yMarginal p y) := by
            rw [Fintype.sum_prod_type]
      _ = ∑ y : β, ∑ x : α, p (x, y) * Real.log (yMarginal p y) := by
            rw [Finset.sum_comm]
      _ = ∑ y : β, yMarginal p y * Real.log (yMarginal p y) := by
            refine Finset.sum_congr rfl ?_
            intro y hy
            rw [← Finset.sum_mul]
            rfl
      _ = - entropy (yMarginal p) := by
            rw [Causalean.Mathlib.InformationTheory.entropy_def]
            simp [Real.negMulLog_def, Finset.sum_neg_distrib]
  have hInnerLog :
      (∑ xy : α × β, p xy * Real.log (inner xy))
        = (1 - Pe) * Real.log (1 - Pe) + Pe * Real.log (Pe / (M - 1)) := by
    calc
      (∑ xy : α × β, p xy * Real.log (inner xy))
          = ∑ xy : α × β,
              ((if xy.1 = decode xy.2 then p xy else 0) * Real.log (1 - Pe)
                + (if xy.1 = decode xy.2 then 0 else p xy) * Real.log (Pe / (M - 1))) := by
            refine Finset.sum_congr rfl ?_
            intro xy hxy_mem
            by_cases hc : xy.1 = decode xy.2 <;> simp [inner, hc]
      _ = (∑ xy : α × β, (if xy.1 = decode xy.2 then p xy else 0)) * Real.log (1 - Pe)
          + (∑ xy : α × β, (if xy.1 = decode xy.2 then 0 else p xy))
              * Real.log (Pe / (M - 1)) := by
            rw [Finset.sum_add_distrib]
            rw [← Finset.sum_mul, ← Finset.sum_mul]
      _ = (1 - Pe) * Real.log (1 - Pe) + Pe * Real.log (Pe / (M - 1)) := by
            rw [correctMass_eq hsum decode]
            rw [← errorProb_def p decode]
  have hlog_total :
      (∑ xy : α × β, p xy * Real.log (fanoRef p decode xy))
        = - entropy (yMarginal p)
          + ((1 - Pe) * Real.log (1 - Pe) + Pe * Real.log (Pe / (M - 1))) := by
    rw [hsum_split, hYlog, hInnerLog]
  have hlog_div :
      Pe * Real.log (Pe / (M - 1))
        = Pe * Real.log Pe - Pe * Real.log (M - 1) := by
    by_cases hPe : Pe = 0
    · simp [hPe]
    · rw [Real.log_div hPe hMne]
      ring
  calc
    (- ∑ xy : α × β, p xy * Real.log (fanoRef p decode xy))
        = - (- entropy (yMarginal p)
          + ((1 - Pe) * Real.log (1 - Pe) + Pe * Real.log (Pe / (M - 1)))) := by
            rw [hlog_total]
    _ = entropy (yMarginal p) + Real.binEntropy Pe + Pe * Real.log (M - 1) := by
          rw [hlog_div, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
          simp [Real.negMulLog_def]
          ring
    _ = entropy (yMarginal p) + Real.binEntropy (errorProb p decode)
          + errorProb p decode * Real.log ((Fintype.card α : ℝ) - 1) := by
          simp [Pe, M]

/-- **Fano's inequality** (Cover & Thomas, Thm 2.10.1). For a joint probability mass
function `p` on `α × β` with `2 ≤ Fintype.card α`, a decoder `decode : β → α`, and error
probability `Pe = errorProb p decode`, the conditional entropy is bounded:
`condEntropy p ≤ Real.binEntropy Pe + Pe * Real.log (Fintype.card α − 1)`.

The proof feeds the Fano reference distribution `fanoRef` to the Gibbs inequality
`entropy_le_crossEntropy`, giving `entropy p ≤ −∑ p log (fanoRef)`; the right side is
`entropy (yMarginal p) + binEntropy Pe + Pe · log (card α − 1)` by `neg_crossEntropy_fanoRef`,
and `condEntropy p = entropy p − entropy (yMarginal p)`. -/
theorem fano_inequality {p : α × β → ℝ} (hp0 : ∀ xy, 0 ≤ p xy)
    (hsum : ∑ xy : α × β, p xy = 1) (hcard : 2 ≤ Fintype.card α) (decode : β → α) :
    condEntropy p ≤ Real.binEntropy (errorProb p decode)
      + errorProb p decode * Real.log ((Fintype.card α : ℝ) - 1) := by
  have hcross :=
    entropy_le_crossEntropy (p := p) (g := fanoRef p decode) hp0 hsum
      (fun xy => fanoRef_nonneg hp0 hsum hcard decode xy)
      (le_of_eq (fanoRef_sum_eq_one hp0 hsum hcard decode))
      (fun xy h => fanoRef_ac hp0 hsum hcard decode xy h)
  rw [neg_crossEntropy_fanoRef hp0 hsum hcard decode] at hcross
  rw [condEntropy_def]
  linarith

/-- **Fano error lower bound** (the standard weakened corollary). Under the hypotheses of
`fano_inequality`, the error probability is bounded below by
`Pe ≥ (condEntropy p − Real.log 2) / Real.log (Fintype.card α)`.

It follows from `fano_inequality` using `Real.binEntropy_le_log_two`
(`binEntropy Pe ≤ log 2`) and the monotonicity `Real.log (card α − 1) ≤ Real.log (card α)`,
then dividing by the positive `Real.log (Fintype.card α)` (positive since `2 ≤ card α`). -/
theorem fano_error_lower_bound {p : α × β → ℝ} (hp0 : ∀ xy, 0 ≤ p xy)
    (hsum : ∑ xy : α × β, p xy = 1) (hcard : 2 ≤ Fintype.card α) (decode : β → α) :
    (condEntropy p - Real.log 2) / Real.log (Fintype.card α) ≤ errorProb p decode := by
  let Pe : ℝ := errorProb p decode
  let M : ℝ := Fintype.card α
  have hfano := fano_inequality hp0 hsum hcard decode
  have hPe_nonneg : 0 ≤ Pe := by
    simpa [Pe] using errorProb_nonneg hp0 decode
  have hMgt : (1 : ℝ) < M := by
    dsimp [M]
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hcard)
  have hMminus_pos : 0 < M - 1 := by linarith
  have hMminus_le : M - 1 ≤ M := by linarith
  have hlog_mono : Real.log (M - 1) ≤ Real.log M :=
    Real.log_le_log hMminus_pos hMminus_le
  have hmul_log : Pe * Real.log (M - 1) ≤ Pe * Real.log M :=
    mul_le_mul_of_nonneg_left hlog_mono hPe_nonneg
  have hbin : Real.binEntropy Pe ≤ Real.log 2 := Real.binEntropy_le_log_two
  have hfano' : condEntropy p ≤ Real.binEntropy Pe + Pe * Real.log (M - 1) := by
    simpa [Pe, M] using hfano
  have hmain : condEntropy p - Real.log 2 ≤ Pe * Real.log M := by
    linarith
  have hlogM_pos : 0 < Real.log M := Real.log_pos hMgt
  have hdiv : (condEntropy p - Real.log 2) / Real.log M ≤ Pe := by
    rw [div_le_iff₀ hlogM_pos]
    exact hmain
  simpa [Pe, M] using hdiv

end Causalean.Mathlib.InformationTheory
