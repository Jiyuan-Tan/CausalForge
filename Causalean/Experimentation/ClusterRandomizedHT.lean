/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Experimentation.DesignBased.Designs.ClusterRandomization
import Mathlib.Tactic.NormNum

/-!
# Middleton & Aronow (2015): cluster-randomized Horvitz-Thompson ATE

This file formalizes the cluster-randomized Horvitz-Thompson identity behind Middleton and
Aronow's average-treatment-effect result. Treatment is assigned independently by cluster, each
cluster has treated and control cluster-total potential outcomes, and inverse-probability weighting
recovers the finite-population average treatment effect after normalization by the total number of
units.

The file records the cluster Horvitz-Thompson treated/control totals, the unit-count denominator,
the normalized effect estimator, the normalized finite-population ATE estimand, and the
unbiasedness theorem (a direct consequence of the first-order cluster inclusion probability).
-/

open scoped BigOperators
open Finset

namespace Causalean
namespace Experimentation
namespace ClusterRandomizedHT

open DesignBased

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- The **Horvitz–Thompson treated total**: each treated cluster's total outcome `y1 c`, weighted by
the inverse assignment probability `1 / p c`. -/
noncomputable def htTreatedTotal (p y1 : C → ℝ) (z : C → Bool) : ℝ :=
  ∑ c, (treatInd c z / p c) * y1 c

/-- The **Horvitz–Thompson control total**: each control cluster's total outcome `y0 c`, weighted by
the inverse control probability `1 / (1 − p c)`. -/
noncomputable def htControlTotal (p y0 : C → ℝ) (z : C → Bool) : ℝ :=
  ∑ c, ((1 - treatInd c z) / (1 - p c)) * y0 c

/-- The total number of experimental units represented by the cluster counts `n c`. -/
noncomputable def totalUnits (n : C → ℕ) : ℝ := ∑ c, (n c : ℝ)

/-- The **Middleton-Aronow Horvitz-Thompson ATE estimator** divides the inverse-probability
weighted treated-minus-control cluster-total estimator by the total number of units. -/
noncomputable def htClusterEffect (p : C → ℝ) (n : C → ℕ) (y1 y0 : C → ℝ)
    (z : C → Bool) : ℝ :=
  (htTreatedTotal p y1 z - htControlTotal p y0 z) / totalUnits n

/-- The **finite-population average treatment effect** is the all-unit treated-minus-control
potential-outcome total, aggregated through cluster totals, divided by the total number of units. -/
noncomputable def totalEffect (n : C → ℕ) (y1 y0 : C → ℝ) : ℝ :=
  (∑ c, (y1 c - y0 c)) / totalUnits n

/-- The HT treated total is unbiased for the treated-arm population total `∑ y1 c`: each cluster is
treated with probability `p c`, which the inverse weight `1 / p c` exactly undoes. -/
theorem E_htTreatedTotal (p y1 : C → ℝ) (hp0 : ∀ c, 0 ≤ p c) (hp1 : ∀ c, p c ≤ 1)
    (hppos : ∀ c, 0 < p c) :
    (clusterDesign p hp0 hp1).E (htTreatedTotal p y1) = ∑ c, y1 c := by
  change (bernoulliDesign p hp0 hp1).E (fun z => ∑ c, treatInd c z / p c * y1 c)
    = ∑ c, y1 c
  rw [show (fun z => ∑ c, treatInd c z / p c * y1 c)
        = (fun z => ∑ c, y1 c / p c * treatInd c z) from
      funext (fun z => Finset.sum_congr rfl (fun c _ => by ring))]
  rw [FiniteDesign.E_sum]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [FiniteDesign.E_const_mul _ (y1 c / p c) (treatInd c), bernoulliDesign_E_treatInd]
  exact div_mul_cancel₀ (y1 c) (hppos c).ne'

/-- The HT control total is unbiased for the control-arm population total `∑ y0 c`: each cluster
is a control with probability `1 − p c`, undone by the weight `1 / (1 − p c)`. -/
theorem E_htControlTotal (p y0 : C → ℝ) (hp0 : ∀ c, 0 ≤ p c) (hp1 : ∀ c, p c ≤ 1)
    (hp1' : ∀ c, p c < 1) :
    (clusterDesign p hp0 hp1).E (htControlTotal p y0) = ∑ c, y0 c := by
  have hone : ∀ c, (bernoulliDesign p hp0 hp1).E (fun z => 1 - treatInd c z) = 1 - p c := by
    intro c
    rw [show (fun z => (1 : ℝ) - treatInd c z)
          = (fun z => (fun _ => (1 : ℝ)) z - treatInd c z) from rfl,
      FiniteDesign.E_sub, FiniteDesign.E_const, bernoulliDesign_E_treatInd]
  change (bernoulliDesign p hp0 hp1).E
      (fun z => ∑ c, (1 - treatInd c z) / (1 - p c) * y0 c)
    = ∑ c, y0 c
  rw [show (fun z => ∑ c, (1 - treatInd c z) / (1 - p c) * y0 c)
        = (fun z => ∑ c, y0 c / (1 - p c) * (1 - treatInd c z)) from
      funext (fun z => Finset.sum_congr rfl (fun c _ => by ring))]
  rw [FiniteDesign.E_sum]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [FiniteDesign.E_const_mul _ (y0 c / (1 - p c)) (fun z => 1 - treatInd c z), hone c]
  exact div_mul_cancel₀ (y0 c) (sub_ne_zero.mpr (hp1' c).ne')

/-- **Unbiasedness for the finite-population average treatment effect.** Under cluster
randomization with every cluster treatment probability strictly between zero and one and a positive
total unit count, the Middleton-Aronow Horvitz-Thompson effect estimator is unbiased for the
finite-population ATE. -/
theorem E_htClusterEffect (p : C → ℝ) (n : C → ℕ) (y1 y0 : C → ℝ) (hp0 : ∀ c, 0 ≤ p c)
    (hp1 : ∀ c, p c ≤ 1) (hppos : ∀ c, 0 < p c) (hp1' : ∀ c, p c < 1)
    (hNpos : 0 < totalUnits n) :
    (clusterDesign p hp0 hp1).E (htClusterEffect p n y1 y0) = totalEffect n y1 y0 := by
  unfold htClusterEffect totalEffect
  have hNne : totalUnits n ≠ 0 := ne_of_gt hNpos
  rw [show (fun z => (htTreatedTotal p y1 z - htControlTotal p y0 z) / totalUnits n)
        = (fun z => (htTreatedTotal p y1 z - htControlTotal p y0 z) * (totalUnits n)⁻¹) from
      funext (fun z => by rw [div_eq_mul_inv])]
  rw [FiniteDesign.E_mul_const, FiniteDesign.E_sub, E_htTreatedTotal p y1 hp0 hp1 hppos,
    E_htControlTotal p y0 hp0 hp1 hp1', ← Finset.sum_sub_distrib, div_eq_mul_inv]

end ClusterRandomizedHT
end Experimentation
end Causalean
