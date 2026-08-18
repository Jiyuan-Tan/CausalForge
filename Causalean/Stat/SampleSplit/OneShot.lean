/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# One-shot sample split

`OneShotSplit` structure matching `def:est-one-shot-split` in
`doc/basic_concepts/po/estimation.tex`: a partition of the i.i.d. sample
into a nuisance fold `A(n) := {0, …, n₁(n)−1}` and an estimation fold
`B(n) := {n₁(n), …, n−1}` with both folds growing to infinity.

The headline lemma `folds_indep` (`prop:est-folds-indep`) states that the
two folds are independent under `μ`, expressed as `IndepFun` between the
fold-A and fold-B tuple-valued statistics — a direct corollary of
`iIndepFun.indepFun_finset` applied to the disjoint index sets.
-/

import Causalean.Stat.Sample
import Mathlib.Probability.Independence.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

/-! # One-Shot Sample Splits

This file defines a two-fold split of an i.i.d. sample into a nuisance-estimation
fold and a target-estimation fold, with both folds growing without bound. It
proves the finite-sample independence of the two fold-indexed sample tuples,
which is the basic splitting fact used in debiased estimation. -/

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Filter

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X}

/-- **One-shot sample split.** For an i.i.d. sample `S`, [a fold-size schedule
`n₁ : ℕ → ℕ` splitting the sample of size `n` into a nuisance fold
$A(n) = \{0,\dots,n_1(n)-1\}$ and an estimation fold $B(n) = \{n_1(n),\dots,n-1\}$](hyp:n₁),
where [the nuisance fold never exceeds the full sample, $n_1(n) \le n$](hyp:bound), [the
nuisance fold grows without bound](hyp:grow), and [the estimation fold also grows without
bound, $n - n_1(n) \to \infty$](hyp:cogrow). -/
structure OneShotSplit {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {μ : Measure Ω} {P : Measure X}
    (_S : IIDSample Ω X μ P) where
  n₁ : ℕ → ℕ
  bound  : ∀ n, n₁ n ≤ n
  grow   : Tendsto n₁ atTop atTop
  cogrow : Tendsto (fun n => n - n₁ n) atTop atTop

namespace OneShotSplit

variable {S : IIDSample Ω X μ P} (split : OneShotSplit S)

/-- Nuisance-fold index set at horizon `n`: `A(n) := {0, …, n₁(n)−1}`. -/
def foldA (n : ℕ) : Finset ℕ := Finset.range (split.n₁ n)

/-- Estimation-fold index set at horizon `n`: `B(n) := {n₁(n), …, n−1}`. -/
def foldB (n : ℕ) : Finset ℕ :=
  (Finset.range n).filter (fun i => split.n₁ n ≤ i)

/-- Cardinality of the estimation fold: `|B(n)| = n - n₁(n)`. -/
lemma foldB_card (n : ℕ) : (split.foldB n).card = n - split.n₁ n := by
  have hfoldB_eq : split.foldB n = Finset.Ico (split.n₁ n) n := by
    ext i
    simp [OneShotSplit.foldB, Finset.mem_Ico, and_comm]
  rw [hfoldB_eq]
  exact Nat.card_Ico (split.n₁ n) n

/-- The estimation-fold cardinality grows to infinity. -/
lemma foldB_card_tendsto :
    Tendsto (fun n => (split.foldB n).card) atTop atTop := by
  simpa [split.foldB_card] using split.cogrow

/-- Fold-A and fold-B index sets are disjoint. -/
lemma foldA_disjoint_foldB (n : ℕ) :
    Disjoint (split.foldA n) (split.foldB n) := by
  rw [foldA, foldB]
  refine Finset.disjoint_left.mpr ?_
  intro i hiA hiB
  simp only [Finset.mem_range, Finset.mem_filter] at hiA hiB
  have hnot : ¬ split.n₁ n ≤ i := Nat.not_le_of_gt hiA
  exact hnot hiB.2

/-- **Independence of folds.** For [a fixed sample size `n`](hyp:n), [the sample sub-tuple indexed
by the nuisance fold `A(n)` is independent, under `μ`, of the sub-tuple indexed by the estimation
fold `B(n)`](goal).

Direct corollary of `iIndepFun.indepFun_finset` applied to the disjoint index sets `A(n), B(n)`. -/
theorem folds_indep (n : ℕ) :
    IndepFun
      (fun ω (i : split.foldA n) => S.Z i ω)
      (fun ω (i : split.foldB n) => S.Z i ω)
      μ := by
  exact S.indep.indepFun_finset (split.foldA n) (split.foldB n)
    (split.foldA_disjoint_foldB n) S.meas

end OneShotSplit

end Causalean.Stat
