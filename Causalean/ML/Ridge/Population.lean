/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.ML.Core
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Ridge regression — population target

This file defines the population ridge objective
`populationRidgeObjective`, the population squared prediction risk plus the L²
penalty `λ‖β‖²`, and the normal-equation predicate `IsPopulationRidge`.  The
main theorem, `populationRidge_minimizes`, proves that a coefficient vector
satisfying `E[(Y - ⟪β,φ⟫) φₖ] = λ βₖ` for every feature coordinate minimizes the
population ridge objective when `λ ≥ 0` and the required integrability
hypotheses hold.  This is a penalized coefficient target in the chosen finite
feature span, not a separate claim that the predictor equals the conditional
regression function.
-/

namespace Causalean.ML

open MeasureTheory BigOperators

variable {X' K : Type*} [MeasurableSpace X'] [Fintype K]

/-- The population ridge objective: population squared risk plus `λ‖β‖²`. -/
noncomputable def populationRidgeObjective
    (P : Measure (X' × ℝ)) (φ : FeatureMap X' K) (lam : ℝ) (β : K → ℝ) : ℝ :=
  populationRisk squaredLoss P (fun x => ∑ k, β k * φ.φ x k) + lam * ∑ k, β k ^ 2

/-- The regularized population normal equations:
`E[(Y − ⟪βstar,φ⟫) φₖ] = λ · βstarₖ` for every feature `k`. -/
def IsPopulationRidge (P : Measure (X' × ℝ)) (φ : FeatureMap X' K)
    (lam : ℝ) (βstar : K → ℝ) : Prop :=
  ∀ k, ∫ z, (z.2 - ∑ j, βstar j * φ.φ z.1 j) * φ.φ z.1 k ∂P = lam * βstar k

/-- With `λ ≥ 0`, a coefficient vector satisfying the regularized population
normal equations minimizes the population ridge objective. -/
theorem populationRidge_minimizes
    (P : Measure (X' × ℝ)) (φ : FeatureMap X' K) {lam : ℝ} (hlam : 0 ≤ lam)
    {βstar : K → ℝ} (hreg : IsPopulationRidge P φ lam βstar) (β : K → ℝ)
    (hint_star : HasFinitePopulationRisk squaredLoss P (fun x => ∑ k, βstar k * φ.φ x k))
    (hint_β : HasFinitePopulationRisk squaredLoss P (fun x => ∑ k, β k * φ.φ x k))
    (hcross : ∀ k, Integrable
      (fun z => (z.2 - ∑ j, βstar j * φ.φ z.1 j) * φ.φ z.1 k) P) :
    populationRidgeObjective P φ lam βstar ≤ populationRidgeObjective P φ lam β := by
  let m : X' → ℝ := fun x => ∑ k, βstar k * φ.φ x k
  let h : X' → ℝ := fun x => ∑ k, β k * φ.φ x k
  have hint_m' : Integrable (fun z : X' × ℝ => (z.2 - m z.1) ^ 2) P := by
    simpa [HasFinitePopulationRisk, squaredLoss, m] using hint_star
  have hint_h' : Integrable (fun z : X' × ℝ => (z.2 - h z.1) ^ 2) P := by
    simpa [HasFinitePopulationRisk, squaredLoss, h] using hint_β
  have hdiff :
      Integrable
        (fun z : X' × ℝ => (z.2 - h z.1) ^ 2 - (z.2 - m z.1) ^ 2) P :=
    hint_h'.sub hint_m'
  have hmh_expand : ∀ z : X' × ℝ,
      m z.1 - h z.1 = ∑ k, (βstar k - β k) * φ.φ z.1 k := by
    intro z
    calc
      m z.1 - h z.1
          = (∑ k, βstar k * φ.φ z.1 k) - ∑ k, β k * φ.φ z.1 k := rfl
      _ = ∑ k, (βstar k * φ.φ z.1 k - β k * φ.φ z.1 k) := by
        rw [Finset.sum_sub_distrib]
      _ = ∑ k, (βstar k - β k) * φ.φ z.1 k := by
        exact Finset.sum_congr rfl (fun k _ => by ring)
  have hcross_mh :
      Integrable (fun z : X' × ℝ => (z.2 - m z.1) * (m z.1 - h z.1)) P := by
    have hsum_int :
        Integrable
          (fun z : X' × ℝ =>
            ∑ k, (βstar k - β k) *
              ((z.2 - m z.1) * φ.φ z.1 k)) P := by
      exact integrable_finset_sum (s := Finset.univ)
        (fun k _ => (hcross k).const_mul (βstar k - β k))
    refine hsum_int.congr ?_
    filter_upwards with z
    rw [hmh_expand z]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro k _
    ring
  have hcross_val :
      ∫ z, (z.2 - m z.1) * (m z.1 - h z.1) ∂P =
        -lam * ∑ k, (β k - βstar k) * βstar k := by
    calc
      ∫ z, (z.2 - m z.1) * (m z.1 - h z.1) ∂P
          = ∫ z, ∑ k, (βstar k - β k) *
              ((z.2 - m z.1) * φ.φ z.1 k) ∂P := by
        apply integral_congr_ae
        filter_upwards with z
        rw [hmh_expand z]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro k _
        ring
      _ = ∑ k, ∫ z, (βstar k - β k) *
              ((z.2 - m z.1) * φ.φ z.1 k) ∂P := by
        rw [integral_finset_sum]
        intro k _
        exact (hcross k).const_mul (βstar k - β k)
      _ = ∑ k, (βstar k - β k) *
              ∫ z, (z.2 - m z.1) * φ.φ z.1 k ∂P := by
        refine Finset.sum_congr rfl ?_
        intro k _
        rw [integral_const_mul]
      _ = ∑ k, (βstar k - β k) * (lam * βstar k) := by
        refine Finset.sum_congr rfl ?_
        intro k _
        rw [hreg k]
      _ = -lam * ∑ k, (β k - βstar k) * βstar k := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun k _ => by ring)
  have hsq_int : Integrable (fun z : X' × ℝ => (m z.1 - h z.1) ^ 2) P := by
    have htmp :
        Integrable
          (fun z : X' × ℝ =>
            ((z.2 - h z.1) ^ 2 - (z.2 - m z.1) ^ 2) -
              2 * ((z.2 - m z.1) * (m z.1 - h z.1))) P :=
      hdiff.sub (hcross_mh.const_mul 2)
    convert htmp using 1
    funext z
    ring
  have hrisk_diff :
      populationRisk squaredLoss P h - populationRisk squaredLoss P m =
        2 * ∫ z, (z.2 - m z.1) * (m z.1 - h z.1) ∂P +
          ∫ z, (m z.1 - h z.1) ^ 2 ∂P := by
    change (∫ z, (z.2 - h z.1) ^ 2 ∂P) -
        (∫ z, (z.2 - m z.1) ^ 2 ∂P) =
        2 * ∫ z, (z.2 - m z.1) * (m z.1 - h z.1) ∂P +
          ∫ z, (m z.1 - h z.1) ^ 2 ∂P
    rw [← integral_sub hint_h' hint_m']
    calc
      ∫ z, ((z.2 - h z.1) ^ 2 - (z.2 - m z.1) ^ 2) ∂P
          = ∫ z, 2 * ((z.2 - m z.1) * (m z.1 - h z.1)) +
              (m z.1 - h z.1) ^ 2 ∂P := by
        apply integral_congr_ae
        filter_upwards with z
        ring
      _ = ∫ z, 2 * ((z.2 - m z.1) * (m z.1 - h z.1)) ∂P +
            ∫ z, (m z.1 - h z.1) ^ 2 ∂P := by
        rw [integral_add]
        · exact hcross_mh.const_mul 2
        · exact hsq_int
      _ = 2 * ∫ z, (z.2 - m z.1) * (m z.1 - h z.1) ∂P +
            ∫ z, (m z.1 - h z.1) ^ 2 ∂P := by
        rw [integral_const_mul]
  have hpenalty_diff :
      (∑ k, β k ^ 2) - ∑ k, βstar k ^ 2 =
        (∑ k, (β k - βstar k) ^ 2) +
          2 * ∑ k, (β k - βstar k) * βstar k := by
    calc
      (∑ k, β k ^ 2) - ∑ k, βstar k ^ 2
          = ∑ k, (β k ^ 2 - βstar k ^ 2) := by
        rw [Finset.sum_sub_distrib]
      _ = ∑ k, ((β k - βstar k) ^ 2 +
            2 * ((β k - βstar k) * βstar k)) := by
        exact Finset.sum_congr rfl (fun k _ => by ring)
      _ = (∑ k, (β k - βstar k) ^ 2) +
            ∑ k, 2 * ((β k - βstar k) * βstar k) := by
        rw [Finset.sum_add_distrib]
      _ = (∑ k, (β k - βstar k) ^ 2) +
          2 * ∑ k, (β k - βstar k) * βstar k := by
        rw [Finset.mul_sum]
  have hobj_diff :
      populationRidgeObjective P φ lam β - populationRidgeObjective P φ lam βstar =
        ∫ z, (m z.1 - h z.1) ^ 2 ∂P +
          lam * ∑ k, (β k - βstar k) ^ 2 := by
    calc
      populationRidgeObjective P φ lam β - populationRidgeObjective P φ lam βstar
          = (populationRisk squaredLoss P h - populationRisk squaredLoss P m) +
              lam * ((∑ k, β k ^ 2) - ∑ k, βstar k ^ 2) := by
        simp [populationRidgeObjective, m, h]
        ring
      _ = (2 * ∫ z, (z.2 - m z.1) * (m z.1 - h z.1) ∂P +
              ∫ z, (m z.1 - h z.1) ^ 2 ∂P) +
            lam * ((∑ k, (β k - βstar k) ^ 2) +
              2 * ∑ k, (β k - βstar k) * βstar k) := by
        rw [hrisk_diff, hpenalty_diff]
      _ = (2 * (-lam * ∑ k, (β k - βstar k) * βstar k) +
              ∫ z, (m z.1 - h z.1) ^ 2 ∂P) +
            lam * ((∑ k, (β k - βstar k) ^ 2) +
              2 * ∑ k, (β k - βstar k) * βstar k) := by
        rw [hcross_val]
      _ = ∫ z, (m z.1 - h z.1) ^ 2 ∂P +
          lam * ∑ k, (β k - βstar k) ^ 2 := by
        ring
  have hdiff_nonneg :
      0 ≤ populationRidgeObjective P φ lam β - populationRidgeObjective P φ lam βstar := by
    rw [hobj_diff]
    exact add_nonneg (integral_nonneg (fun z => sq_nonneg _))
      (mul_nonneg hlam (Finset.sum_nonneg (fun k _ => sq_nonneg _)))
  linarith

end Causalean.ML
