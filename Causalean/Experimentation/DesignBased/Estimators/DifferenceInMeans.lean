/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# The difference-in-means estimator under complete randomization

The canonical two-arm experiment: each unit `i` has potential outcomes `Y1 i` (treated) and `Y0 i`
(control), exactly `n₁` of the `N` units are treated by complete randomization, and the estimand is
the **sample average treatment effect** `τ = (1/N) ∑ (Y1 i − Y0 i)`.  The **difference-in-means**
estimator `τ̂ = (treated mean) − (control mean)` averages the observed outcomes within each arm.
This file records the estimator, the estimand, and the theorem that the difference in means is
**unbiased** for the SATE under complete randomization — a direct consequence of the first-order
inclusion probability `n₁ / N`.  The randomization variance (the Neyman variance) is left as a
target for the variance development.
-/

import Causalean.Experimentation.DesignBased.Designs.CompleteRandomization
import Causalean.Experimentation.DesignBased.Risk

/-! # Difference-in-means under complete randomization

The two-arm difference-in-means estimator is unbiased for the sample average treatment effect under
complete randomization.

This file defines the finite-population target `sateEstimand`, the realized arm averages
`treatedMean` and `controlMean`, and their contrast `diffInMeans`. The results
`E_treatedMean` and `E_controlMean` prove that each arm mean estimates its finite-population arm
mean, and `E_diffInMeans_eq_sate` packages the consequence: when `0 < n₁ < N`, the expected
difference in means equals `sateEstimand`. The companion theorem `unbiased_diffInMeans` states the
same fact using the generic `FiniteDesign.Unbiased` predicate.
-/

open scoped BigOperators
open Finset

namespace Causalean
namespace Experimentation
namespace DesignBased

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- The **sample average treatment effect** (SATE): the population mean of the unit-level treatment
effects `Y1 i − Y0 i`. -/
noncomputable def sateEstimand (Y1 Y0 : U → ℝ) : ℝ :=
  (∑ i, (Y1 i - Y0 i)) / (Fintype.card U : ℝ)

/-- The **treated-arm mean** of `Y1` under a treated set `S`: the average of `Y1` over the `n₁`
treated units. -/
noncomputable def treatedMean (n₁ : ℕ) (Y1 : U → ℝ) (S : {S : Finset U // S.card = n₁}) : ℝ :=
  (∑ i, (if i ∈ S.val then Y1 i else 0)) / (n₁ : ℝ)

/-- The **control-arm mean** of `Y0` under a treated set `S`: the average of `Y0` over the
`n₀ = N − n₁` control units. -/
noncomputable def controlMean (n₁ : ℕ) (Y0 : U → ℝ) (S : {S : Finset U // S.card = n₁}) : ℝ :=
  (∑ i, (if i ∈ S.val then 0 else Y0 i)) / ((Fintype.card U - n₁ : ℕ) : ℝ)

/-- The **difference-in-means** estimator: treated-arm mean of `Y1` minus control-arm mean of
`Y0`. -/
noncomputable def diffInMeans (n₁ : ℕ) (Y1 Y0 : U → ℝ) (S : {S : Finset U // S.card = n₁}) : ℝ :=
  treatedMean n₁ Y1 S - controlMean n₁ Y0 S

/-- The treated-arm mean is unbiased for the treated population mean `(1/N) ∑ Y1`. Each unit enters
the treated arm with probability `n₁ / N`, so its inverse-`n₁` weight averages to `1/N`. -/
theorem E_treatedMean (n₁ : ℕ) (hn : n₁ ≤ Fintype.card U) (hn1 : 0 < n₁) (Y1 : U → ℝ) :
    (completeRandomization n₁ hn).E (treatedMean n₁ Y1) = (∑ i, Y1 i) / (Fintype.card U : ℝ) := by
  let D := completeRandomization n₁ hn
  have hn1R : (n₁ : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn1)
  have hNpos : 0 < Fintype.card U := lt_of_lt_of_le hn1 hn
  have hNR : (Fintype.card U : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hNpos)
  have hterm (i : U) :
      D.E (fun S : {S : Finset U // S.card = n₁} => if i ∈ S.val then Y1 i else 0) =
        Y1 i * ((n₁ : ℝ) / (Fintype.card U : ℝ)) := by
    calc
      D.E (fun S : {S : Finset U // S.card = n₁} => if i ∈ S.val then Y1 i else 0)
          = D.E (fun S : {S : Finset U // S.card = n₁} =>
              Y1 i *
                FiniteDesign.ind
                  (fun T : {S : Finset U // S.card = n₁} => i ∈ T.val) S) := by
            exact D.E_congr (fun S => by
              unfold FiniteDesign.ind
              by_cases h : i ∈ S.val <;> simp [h])
      _ = Y1 i *
            D.E (FiniteDesign.ind
              (fun T : {S : Finset U // S.card = n₁} => i ∈ T.val)) := by
            rw [FiniteDesign.E_const_mul]
      _ = Y1 i * D.Pr (fun T : {S : Finset U // S.card = n₁} => i ∈ T.val) := by
            rw [FiniteDesign.E_ind]
      _ = Y1 i * ((n₁ : ℝ) / (Fintype.card U : ℝ)) := by
            rw [completeRandomization_incl]
  calc
    D.E (treatedMean n₁ Y1)
        = D.E (fun S : {S : Finset U // S.card = n₁} =>
            (∑ i, (if i ∈ S.val then Y1 i else 0)) * (1 / (n₁ : ℝ))) := by
          exact D.E_congr (fun S => by
            unfold treatedMean
            rw [div_eq_mul_inv, one_div])
    _ = D.E (fun S : {S : Finset U // S.card = n₁} =>
            ∑ i, (if i ∈ S.val then Y1 i else 0)) * (1 / (n₁ : ℝ)) := by
          rw [FiniteDesign.E_mul_const]
    _ = (∑ i, D.E (fun S : {S : Finset U // S.card = n₁} =>
            if i ∈ S.val then Y1 i else 0)) * (1 / (n₁ : ℝ)) := by
          rw [FiniteDesign.E_sum]
    _ = (∑ i, Y1 i * ((n₁ : ℝ) / (Fintype.card U : ℝ))) * (1 / (n₁ : ℝ)) := by
          congr 1
          exact Finset.sum_congr rfl (fun i _ => hterm i)
    _ = (∑ i, Y1 i) / (Fintype.card U : ℝ) := by
          rw [← Finset.sum_mul]
          field_simp [hn1R, hNR]

/-- The control-arm mean is unbiased for the control population mean `(1/N) ∑ Y0`. Each unit enters
the control arm with probability `n₀ / N`. -/
theorem E_controlMean (n₁ : ℕ) (hn : n₁ ≤ Fintype.card U) (hn0 : n₁ < Fintype.card U)
    (Y0 : U → ℝ) :
    (completeRandomization n₁ hn).E (controlMean n₁ Y0) = (∑ i, Y0 i) / (Fintype.card U : ℝ) := by
  let D := completeRandomization n₁ hn
  have hNpos : 0 < Fintype.card U := lt_of_le_of_lt (Nat.zero_le n₁) hn0
  have hNR : (Fintype.card U : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hNpos)
  have hdenNat : (Fintype.card U - n₁ : ℕ) ≠ 0 := Nat.sub_ne_zero_of_lt hn0
  have hdenR : ((Fintype.card U - n₁ : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hdenNat
  have hdiffR : (Fintype.card U : ℝ) - (n₁ : ℝ) ≠ 0 := by
    have hlt : (n₁ : ℝ) < (Fintype.card U : ℝ) := by exact_mod_cast hn0
    exact ne_of_gt (sub_pos.mpr hlt)
  have hterm (i : U) :
      D.E (fun S : {S : Finset U // S.card = n₁} => if i ∈ S.val then 0 else Y0 i) =
        Y0 i * (1 - (n₁ : ℝ) / (Fintype.card U : ℝ)) := by
    calc
      D.E (fun S : {S : Finset U // S.card = n₁} => if i ∈ S.val then 0 else Y0 i)
          = D.E (fun S : {S : Finset U // S.card = n₁} =>
              Y0 i *
                (1 -
                  FiniteDesign.ind
                    (fun T : {S : Finset U // S.card = n₁} => i ∈ T.val) S)) := by
            exact D.E_congr (fun S => by
              unfold FiniteDesign.ind
              by_cases h : i ∈ S.val <;> simp [h])
      _ = Y0 i *
            D.E (fun S : {S : Finset U // S.card = n₁} =>
              1 -
                FiniteDesign.ind
                  (fun T : {S : Finset U // S.card = n₁} => i ∈ T.val) S) := by
            rw [FiniteDesign.E_const_mul]
      _ = Y0 i *
            (D.E (fun _ : {S : Finset U // S.card = n₁} => 1) -
              D.E (FiniteDesign.ind
                (fun T : {S : Finset U // S.card = n₁} => i ∈ T.val))) := by
            rw [FiniteDesign.E_sub]
      _ = Y0 i * (1 - D.Pr (fun T : {S : Finset U // S.card = n₁} => i ∈ T.val)) := by
            rw [FiniteDesign.E_const, FiniteDesign.E_ind]
      _ = Y0 i * (1 - (n₁ : ℝ) / (Fintype.card U : ℝ)) := by
            rw [completeRandomization_incl]
  calc
    D.E (controlMean n₁ Y0)
        = D.E (fun S : {S : Finset U // S.card = n₁} =>
            (∑ i, (if i ∈ S.val then 0 else Y0 i)) *
              (1 / ((Fintype.card U - n₁ : ℕ) : ℝ))) := by
          exact D.E_congr (fun S => by
            unfold controlMean
            rw [div_eq_mul_inv, one_div])
    _ = D.E (fun S : {S : Finset U // S.card = n₁} =>
            ∑ i, (if i ∈ S.val then 0 else Y0 i)) *
            (1 / ((Fintype.card U - n₁ : ℕ) : ℝ)) := by
          rw [FiniteDesign.E_mul_const]
    _ = (∑ i, D.E (fun S : {S : Finset U // S.card = n₁} =>
            if i ∈ S.val then 0 else Y0 i)) *
            (1 / ((Fintype.card U - n₁ : ℕ) : ℝ)) := by
          rw [FiniteDesign.E_sum]
    _ = (∑ i, Y0 i * (1 - (n₁ : ℝ) / (Fintype.card U : ℝ))) *
            (1 / ((Fintype.card U - n₁ : ℕ) : ℝ)) := by
          congr 1
          exact Finset.sum_congr rfl (fun i _ => hterm i)
    _ = (∑ i, Y0 i) / (Fintype.card U : ℝ) := by
          rw [← Finset.sum_mul]
          rw [Nat.cast_sub hn]
          field_simp [hNR, hdenR, hdiffR]

/-- **Unbiasedness of difference in means.** Under complete randomization with `0 < n₁ < N`, the
difference-in-means estimator is unbiased for the sample average treatment effect. -/
theorem E_diffInMeans_eq_sate (n₁ : ℕ) (hn : n₁ ≤ Fintype.card U) (hn1 : 0 < n₁)
    (hn0 : n₁ < Fintype.card U) (Y1 Y0 : U → ℝ) :
    (completeRandomization n₁ hn).E (diffInMeans n₁ Y1 Y0) = sateEstimand Y1 Y0 := by
  unfold diffInMeans sateEstimand
  rw [FiniteDesign.E_sub, E_treatedMean n₁ hn hn1, E_controlMean n₁ hn hn0]
  rw [← sub_div]
  congr 1
  rw [← Finset.sum_sub_distrib]

/-- The difference in means is unbiased for the SATE, in the `Unbiased` predicate form. -/
theorem unbiased_diffInMeans (n₁ : ℕ) (hn : n₁ ≤ Fintype.card U) (hn1 : 0 < n₁)
    (hn0 : n₁ < Fintype.card U) (Y1 Y0 : U → ℝ) :
    (completeRandomization n₁ hn).Unbiased (diffInMeans n₁ Y1 Y0) (sateEstimand Y1 Y0) :=
  E_diffInMeans_eq_sate n₁ hn hn1 hn0 Y1 Y0

end DesignBased
end Experimentation
end Causalean
