/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# K-fold sample split

Generalises `OneShotSplit` (in `OneShot.lean`) to K disjoint folds.  Used by
the cross-fitted DML estimator `dml_crossFit_asymptoticLinear` in
`Causalean/Estimation/OrthogonalMoments/DMLCrossFit.lean`.

Following Chernozhukov et al. (2018), at each sample size `n` the index
set `{0, …, n-1}` is partitioned into `K` folds `fold(n, k)` of roughly
equal size (`fold(n, k).card / n → 1/K`).  Fold k is the *evaluation* fold;
its complement `trainComplement(n, k) := {0,…,n-1} \ fold(n, k)` is used
to estimate the nuisance.

`folds_indep`: the evaluation fold `fold(n, k)` is independent of its
training complement under `μ`.
-/

import Causalean.Stat.Sample
import Causalean.Stat.SampleSplit.OneShot
import Mathlib.Probability.Independence.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Instances.Real.Lemmas

/-! # K-Fold Sample Splits

This file defines \(K\)-fold sample-splitting schedules for an i.i.d. sample,
including disjointness, coverage, fold growth, and limiting fold proportions.
It also proves that each evaluation fold is independent of its training
complement, supporting cross-fitted estimation procedures. -/

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X}

/-- A K-fold split of an i.i.d. sample `S` is a per-(n, k) finite-set
schedule `fold n k : Finset ℕ` satisfying:

* `partition` : different folds are disjoint at every `n`.
* `cover`     : the union over `k` of `fold n k` covers `Finset.range n`.
* `grow`      : each fold grows to infinity in `n`.
* `ratio`     : the fraction `fold(n,k).card / n` converges to `1/K`. -/
structure KFoldSplit {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {μ : Measure Ω} {P : Measure X}
    (_S : IIDSample Ω X μ P) (K : ℕ) where
  fold : ℕ → Fin K → Finset ℕ
  partition : ∀ n (k₁ k₂ : Fin K), k₁ ≠ k₂ → Disjoint (fold n k₁) (fold n k₂)
  cover     : ∀ n,
    (Finset.univ : Finset (Fin K)).biUnion (fold n) = Finset.range n
  grow      : ∀ k, Tendsto (fun n => (fold n k).card) atTop atTop
  ratio     : ∀ k,
    Tendsto (fun n => ((fold n k).card : ℝ) / n) atTop (𝓝 ((K : ℝ)⁻¹))

namespace KFoldSplit

variable {S : IIDSample Ω X μ P} {K : ℕ} (split : KFoldSplit S K)

/-- The training complement of fold `k` at sample size `n`:
`{0, …, n-1} \ fold(n, k)`. -/
def trainComplement (n : ℕ) (k : Fin K) : Finset ℕ :=
  (Finset.range n) \ split.fold n k

/-- The evaluation fold is disjoint from its training complement. -/
lemma fold_disjoint_trainComplement (n : ℕ) (k : Fin K) :
    Disjoint (split.fold n k) (split.trainComplement n k) := by
  rw [trainComplement]
  refine Finset.disjoint_left.mpr ?_
  intro i hi hi'
  exact (Finset.mem_sdiff.mp hi').2 hi

/-- **Independence of evaluation fold and training complement.**  The tuple
`(Z i)_{i ∈ fold(n, k)}` is independent of the tuple
`(Z i)_{i ∈ trainComplement(n, k)}` under `μ`. -/
theorem folds_indep (n : ℕ) (k : Fin K) :
    IndepFun
      (fun ω (i : split.fold n k) => S.Z i ω)
      (fun ω (i : split.trainComplement n k) => S.Z i ω)
      μ := by
  exact S.indep.indepFun_finset (split.fold n k) (split.trainComplement n k)
    (split.fold_disjoint_trainComplement n k) S.meas

end KFoldSplit

end Causalean.Stat
