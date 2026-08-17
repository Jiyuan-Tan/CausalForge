/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Cluster randomization

**Cluster randomization** assigns treatment at the level of clusters: each cluster `c` is treated by
an independent coin flip with probability `p c`, and every unit in a treated cluster is treated.  It
is the Bernoulli design over the cluster labels, read through the cluster-membership map `clus`.
This file records the design and its **inclusion probabilities**: a unit is treated with probability
`p (clus i)` (its cluster's rate); two units in the *same* cluster are jointly treated with that same
probability (their treatments coincide), while two units in *different* clusters are jointly treated
with the product of their cluster rates (clusters are independent).
-/

import Causalean.Experimentation.DesignBased.Designs.Bernoulli

/-! # Cluster randomization designs

Cluster randomization treats all units in a cluster according to one cluster-level coin flip.

This file packages cluster-level Bernoulli assignment and proves the resulting unit-level
inclusion probabilities for same-cluster and cross-cluster pairs.
-/

open scoped BigOperators

namespace Causalean
namespace Experimentation
namespace DesignBased

variable {U C : Type*} [Fintype C] [DecidableEq C]

/-- The **cluster-randomization design**: each cluster `c` is independently assigned treatment with
probability `p c` (a Bernoulli design over the cluster labels). A unit is treated iff its cluster
is. -/
noncomputable def clusterDesign (p : C → ℝ) (hp0 : ∀ c, 0 ≤ p c) (hp1 : ∀ c, p c ≤ 1) :
    FiniteDesign (C → Bool) :=
  bernoulliDesign p hp0 hp1

/-- The treatment indicator of unit `i` under cluster assignment `z`: `1` if `i`'s cluster is
treated, else `0`. -/
def unitTreatInd (clus : U → C) (i : U) (z : C → Bool) : ℝ := treatInd (clus i) z

/-- **First-order inclusion probability.** A unit `i` is treated with probability `p (clus i)`, the
treatment rate of its own cluster. -/
lemma clusterDesign_E_unitTreatInd (p : C → ℝ) (hp0 : ∀ c, 0 ≤ p c) (hp1 : ∀ c, p c ≤ 1)
    (clus : U → C) (i : U) :
    (clusterDesign p hp0 hp1).E (unitTreatInd clus i) = p (clus i) := by
  simp only [clusterDesign]
  have h := bernoulliDesign_E_treatInd p hp0 hp1 (clus i) (fun b => if b then (1 : ℝ) else 0)
  simp only [if_true, mul_one, Bool.false_eq_true, if_false, mul_zero, add_zero] at h
  exact h

/-- **Same-cluster joint treatment.** For a cluster-randomization design in which [each cluster's
treatment probability `p c` lies in `[0,1]`](hyp:hp0,hp1), if [two units `i` and `j` belong to the
same cluster](hyp:h), then [they are jointly treated with probability exactly their shared
cluster's rate `p (clus i)` — because being in the same cluster makes their treatment indicators
identical](goal). -/
lemma clusterDesign_E_unitTreatInd_pair_same (p : C → ℝ) (hp0 : ∀ c, 0 ≤ p c) (hp1 : ∀ c, p c ≤ 1)
    (clus : U → C) {i j : U} (h : clus i = clus j) :
    (clusterDesign p hp0 hp1).E (fun z => unitTreatInd clus i z * unitTreatInd clus j z)
      = p (clus i) := by
  simp only [clusterDesign, unitTreatInd]
  rw [← h]
  rw [show (fun z => treatInd (clus i) z * treatInd (clus i) z) =
      (fun z => treatInd (clus i) z) by
    funext z
    by_cases hz : z (clus i) <;> simp [treatInd, hz]]
  simpa [treatInd] using
    (bernoulliDesign_E_treatInd p hp0 hp1 (clus i) (fun b => if b then (1 : ℝ) else 0))

/-- **Different-cluster joint treatment.** Two units in distinct clusters are jointly treated with
the product of their cluster rates — distinct clusters are randomized independently. -/
lemma clusterDesign_E_unitTreatInd_pair_diff (p : C → ℝ) (hp0 : ∀ c, 0 ≤ p c) (hp1 : ∀ c, p c ≤ 1)
    (clus : U → C) {i j : U} (h : clus i ≠ clus j) :
    (clusterDesign p hp0 hp1).E (fun z => unitTreatInd clus i z * unitTreatInd clus j z)
      = p (clus i) * p (clus j) := by
  simp only [clusterDesign, unitTreatInd]
  exact bernoulliDesign_E_treatInd_pair p hp0 hp1 h

end DesignBased
end Experimentation
end Causalean
