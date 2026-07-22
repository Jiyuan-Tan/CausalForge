/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Borusyak-Jaravel-Spiess efficiency: OLS imputation is BLUE under spherical errors

The efficiency half of `prop:po-estimand-bjs-linear-unbiased-imputation`.  The BJS
imputation estimator is the OLS estimator for the event-study design `designFull`
(a treated-cell indicator block stacked with the covariate block).  Applying the
finite Gauss-Markov theorem `variance_blue_spherical` to this design shows the OLS
estimator has minimum variance among all linear unbiased estimators of the target.
-/

import Causalean.Estimation.GaussMarkov.BLUE
import Causalean.Estimation.GaussMarkov.OLS
import Causalean.Panel.Weighted.IndicatorSpan
import Causalean.Panel.EstimandCharacterization.ImputationEventStudy.Imputation

/-! # Borusyak-Jaravel-Spiess Efficiency

This file connects the finite BJS imputation design to Gauss-Markov efficiency.
It builds the full event-study design matrix and proves that the OLS imputation
weights attain no larger variance than any linear unbiased estimator under
spherical cell-outcome errors. -/

namespace Causalean.Panel.EstimandCharacterization.ImputationEventStudy

open Matrix MeasureTheory ProbabilityTheory Causalean.GaussMarkov

variable {Treated Untreated Regressor : Type*}
  [Fintype Treated] [Fintype Untreated] [Fintype Regressor]
  [DecidableEq Treated] [DecidableEq Regressor]

namespace BJSPanel

/-- The event-study design matrix: rows are observed cells (`Treated ⊕ Untreated`),
columns are treated-cell fixed effects (`Treated`, the τ part) stacked with
covariates (`Regressor`, the β part).  Treated rows carry the cell-indicator in the
τ block and `qT` in the covariate block; untreated rows carry zeros in the τ block
and `qU` in the covariate block. -/
def designFull (P : BJSPanel Treated Untreated Regressor) :
    Matrix (Treated ⊕ Untreated) (Treated ⊕ Regressor) ℝ :=
  Matrix.of (Sum.elim
    (fun c => Sum.elim (fun d => if c = d then (1 : ℝ) else 0) (fun r => P.qT c r))
    (fun u => Sum.elim (fun _ => (0 : ℝ)) (fun r => P.qU u r)))

/-- Target functional in design coordinates: target weights `a` on the τ block,
zero on the covariate block. -/
def cFull (P : BJSPanel Treated Untreated Regressor) : Treated ⊕ Regressor → ℝ :=
  Sum.elim P.a (fun _ => 0)

/-- A linear estimator's weight vector over all observed cells. -/
def weightOf {P : BJSPanel Treated Untreated Regressor} (L : P.LinearEstimator) :
    Treated ⊕ Untreated → ℝ :=
  Sum.elim L.vT L.vU

omit [DecidableEq Regressor] in
/-- **Unbiasedness bridge.**  A linear estimator is unbiased for every `tau` iff its
weight vector satisfies the design constraint `w ᵥ* designFull = cFull`.  (Only the
forward direction is needed below, but it captures both `vT = a` and the nuisance
left-null constraint.) -/
lemma weightOf_vecMul_designFull {P : BJSPanel Treated Untreated Regressor}
    (L : P.LinearEstimator) (h : L.unbiasedForAllTau) :
    weightOf L ᵥ* designFull P = cFull P := by
  classical
  funext j
  have hsplit : (weightOf L ᵥ* designFull P) j
      = (∑ c : Treated, weightOf L (Sum.inl c) * designFull P (Sum.inl c) j)
        + ∑ u : Untreated, weightOf L (Sum.inr u) * designFull P (Sum.inr u) j := by
    simp only [Matrix.vecMul, dotProduct, Fintype.sum_sum_type]
  rw [hsplit]
  cases j with
  | inl d =>
    simp only [weightOf, designFull, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr,
      cFull, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      Finset.sum_const_zero, add_zero]
    exact L.vT_eq_a h d
  | inr r =>
    simp only [weightOf, designFull, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr, cFull]
    rw [show (∑ c : Treated, L.vT c * P.qT c r)
        = ∑ c : Treated, P.a c * P.qT c r from
      Finset.sum_congr rfl (fun c _ => by rw [L.vT_eq_a h c])]
    exact L.nuisance_coord h r

/-- **BJS efficiency: OLS imputation is BLUE under spherical errors.**
For the full-rank event-study design, the OLS estimator `olsWeight designFull cFull`
has variance no larger than that of any linear unbiased estimator `L` of the target,
when the cell outcomes form a spherical random family. -/
theorem bjs_ols_imputation_min_variance_spherical
    {P : BJSPanel Treated Untreated Regressor}
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (Y : Treated ⊕ Untreated → Ω → ℝ) (hY : ∀ i, MemLp (Y i) 2 μ)
    {σ : ℝ} (hsph : SphericalFamily Y μ σ)
    (hRank : IsUnit ((designFull P)ᵀ * designFull P).det)
    (L : P.LinearEstimator) (hL : L.unbiasedForAllTau) :
    Var[fun ω => ∑ i, olsWeight (designFull P) (cFull P) i * Y i ω; μ]
      ≤ Var[fun ω => ∑ i, weightOf L i * Y i ω; μ] := by
  exact variance_blue_spherical Y hY hsph
    (olsWeight_mem_colSpan (designFull P) (cFull P))
    (olsWeight_unbiased (cFull P) hRank)
    (weightOf_vecMul_designFull L hL)

/-! ### Fixed-effect block ↔ panel `IndicatorSpan`

The treated-cell fixed-effect block of `designFull` (the τ-columns) is exactly the
panel indicator-span substrate `Causalean.Panel.Weighted.IndicatorSpan`: each
τ-column is the cell indicator of the treated-cell classifier on observed cells.
This connects the event-study design to the panel FE/indicator-span layer; it is
additive — the BLUE result above stays on the finite Gauss-Markov substrate
(§13gm), the correct home for the variance argument. -/

open Causalean.Panel.Weighted in
/-- Classifier on observed cells sending each treated cell to its own label and
every untreated cell to `none`.  Its `Some`-indicators are the τ-columns of
`designFull`. -/
def treatedClassifier : (Treated ⊕ Untreated) → Option Treated :=
  Sum.elim (fun c => some c) (fun _ => none)

open Causalean.Panel.Weighted in
omit [DecidableEq Regressor] in
/-- Each treated-cell fixed-effect column of `designFull` is the panel cell
indicator of `treatedClassifier`. -/
lemma designFull_col_eq_cellIndicator (P : BJSPanel Treated Untreated Regressor)
    (d : Treated) :
    (fun i => designFull P i (Sum.inl d))
      = cellIndicator (treatedClassifier (Untreated := Untreated)) (some d) := by
  funext i
  cases i with
  | inl c =>
    simp [designFull, treatedClassifier, cellIndicator]
  | inr u =>
    simp [designFull, treatedClassifier, cellIndicator]

open Causalean.Panel.Weighted in
omit [DecidableEq Regressor] in
/-- The treated-cell fixed-effect block of `designFull` lies in the panel
`IndicatorSpan` of the treated-cell classifier: the BJS event-study FE design is
the panel indicator-span substrate. -/
lemma designFull_col_mem_indicatorSpan (P : BJSPanel Treated Untreated Regressor)
    (d : Treated) :
    (fun i => designFull P i (Sum.inl d))
      ∈ indicatorSpan (treatedClassifier (Untreated := Untreated)) := by
  rw [designFull_col_eq_cellIndicator]
  exact cellIndicator_mem_indicatorSpan _ _

end BJSPanel

end Causalean.Panel.EstimandCharacterization.ImputationEventStudy
