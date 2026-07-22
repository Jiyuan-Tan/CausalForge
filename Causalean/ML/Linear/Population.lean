/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.ML.Core
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Linear least squares — population target

The best linear predictor: the coefficient vector whose residual is uncorrelated
with every feature (the population normal equations) minimizes squared population
risk over the linear-in-features class. This file formalizes the condition as
`IsPopulationOLS` and proves `bestLinearPredictor_minimizes_populationRisk`;
global optimality under correct specification is supplied by the spine theorem
`square_loss_population_target_of_isL2Projection`.
-/

namespace Causalean.ML

open MeasureTheory BigOperators

variable {X' K : Type*} [MeasurableSpace X'] [Fintype K]

/-- Population normal equations: the residual of the linear predictor with
coefficients `βstar` is uncorrelated with every feature `φ·ₖ`. -/
def IsPopulationOLS (P : Measure (X' × ℝ)) (φ : FeatureMap X' K) (βstar : K → ℝ) : Prop :=
  ∀ k, ∫ z, (z.2 - ∑ j, βstar j * φ.φ z.1 j) * φ.φ z.1 k ∂P = 0

/-- A coefficient vector satisfying the population normal equations minimizes
squared population risk over all linear-in-features predictors. -/
theorem bestLinearPredictor_minimizes_populationRisk
    (P : Measure (X' × ℝ)) (φ : FeatureMap X' K) {βstar : K → ℝ}
    (hortho : IsPopulationOLS P φ βstar) (β : K → ℝ)
    (hint_star : HasFinitePopulationRisk squaredLoss P (fun x => ∑ k, βstar k * φ.φ x k))
    (hint_β : HasFinitePopulationRisk squaredLoss P (fun x => ∑ k, β k * φ.φ x k))
    (hcross : ∀ k, Integrable
      (fun z => (z.2 - ∑ j, βstar j * φ.φ z.1 j) * φ.φ z.1 k) P) :
    populationRisk squaredLoss P (fun x => ∑ k, βstar k * φ.φ x k)
      ≤ populationRisk squaredLoss P (fun x => ∑ k, β k * φ.φ x k) := by
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
  have horth : ∫ z, (z.2 - m z.1) * (m z.1 - h z.1) ∂P = 0 := by
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
      _ = 0 := by
        rw [Finset.sum_eq_zero]
        intro k _
        rw [hortho k]
        ring
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
  have hdiff_nonneg :
      0 ≤ ∫ z, ((z.2 - h z.1) ^ 2 - (z.2 - m z.1) ^ 2) ∂P := by
    calc
      0 ≤ ∫ z, (m z.1 - h z.1) ^ 2 ∂P := by
        exact integral_nonneg (fun z => sq_nonneg _)
      _ = 2 * ∫ z, (z.2 - m z.1) * (m z.1 - h z.1) ∂P +
            ∫ z, (m z.1 - h z.1) ^ 2 ∂P := by
        simp [horth]
      _ = ∫ z, 2 * ((z.2 - m z.1) * (m z.1 - h z.1)) +
            (m z.1 - h z.1) ^ 2 ∂P := by
        rw [integral_add]
        · rw [integral_const_mul]
        · exact hcross_mh.const_mul 2
        · exact hsq_int
      _ = ∫ z, ((z.2 - h z.1) ^ 2 - (z.2 - m z.1) ^ 2) ∂P := by
        apply integral_congr_ae
        filter_upwards with z
        ring
  have hle : ∫ z, (z.2 - m z.1) ^ 2 ∂P ≤ ∫ z, (z.2 - h z.1) ^ 2 ∂P := by
    have hnonneg_sub :
        0 ≤ ∫ z, (z.2 - h z.1) ^ 2 ∂P -
          ∫ z, (z.2 - m z.1) ^ 2 ∂P := by
      rw [← integral_sub hint_h' hint_m']
      exact hdiff_nonneg
    linarith
  simpa [populationRisk, squaredLoss, m, h] using hle

end Causalean.ML
