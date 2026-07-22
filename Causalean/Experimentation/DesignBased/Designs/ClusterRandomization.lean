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

variable {U C : Type*} [Fintype U] [DecidableEq U] [Fintype C] [DecidableEq C]

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
  exact bernoulliDesign_E_treatInd p hp0 hp1 (clus i)

/-- **Same-cluster joint treatment.** Two units in the same cluster are jointly treated with their
shared cluster's probability — their treatments coincide. -/
lemma clusterDesign_E_unitTreatInd_pair_same (p : C → ℝ) (hp0 : ∀ c, 0 ≤ p c) (hp1 : ∀ c, p c ≤ 1)
    (clus : U → C) {i j : U} (h : clus i = clus j) :
    (clusterDesign p hp0 hp1).E (fun z => unitTreatInd clus i z * unitTreatInd clus j z)
      = p (clus i) := by
  simp only [clusterDesign, unitTreatInd]
  rw [← bernoulliDesign_E_treatInd p hp0 hp1 (clus i)]
  exact (bernoulliDesign p hp0 hp1).E_congr (fun z => by
    rw [← h]
    by_cases hz : z (clus i) <;> simp [treatInd, hz])

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
