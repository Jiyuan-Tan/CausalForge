/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Borusyak-Jaravel-Spiess finite imputation event-study algebra

Finite-cell, paper-specific population characterization of the BJS imputation
functional.  Treated and untreated panel cells are modeled directly as finite
index types. Unit/time grounding, OLS construction of weights, and
Gauss-Markov efficiency are supplied by companion modules.
-/

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-! # Borusyak-Jaravel-Spiess Imputation

This file gives a finite-cell population formulation of the
Borusyak-Jaravel-Spiess imputation functional.  The core structure `BJSPanel`
stores treated and untreated cell rows, target weights, observed and untreated
cell means, the untreated-outcome nuisance vector, and treated-cell effects.
It defines the target `theta`, prediction-span witnesses `ImputationWeights`,
the observed imputation functional `psiImp`, and the identification theorem
`bjs_imputation_identification`.  It also defines the finite linear-estimator
API and the witness lemma `linear_unbiased_of_imputation_representation`; the
substrate-based construction of those witnesses lives in `PanelBridge.lean`. -/

namespace Causalean
namespace Panel.EstimandCharacterization
namespace ImputationEventStudy

open Finset

noncomputable section

variable {Treated Untreated Regressor : Type*}
  [Fintype Treated] [Fintype Untreated] [Fintype Regressor]

/-- Finite dot product for regressor rows and nuisance vectors. -/
def dot (x beta : Regressor → ℝ) : ℝ :=
  ∑ r : Regressor, x r * beta r

/-- Finite treated/untreated cell design for the BJS imputation decomposition.

The observed treated and untreated cell means, the untreated-potential-outcome
cell means, and the target weights are stored as primitive finite arrays. Target
weights are arbitrary real weights: signed and non-normalized weights are
allowed. -/
structure BJSPanel (Treated Untreated Regressor : Type*)
    [Fintype Treated] [Fintype Untreated] [Fintype Regressor] where
  /-- Regressor row for a treated cell. -/
  qT : Treated → Regressor → ℝ
  /-- Regressor row for an untreated cell. -/
  qU : Untreated → Regressor → ℝ
  /-- Arbitrary target weight on treated cells. -/
  a : Treated → ℝ
  /-- Observed-law mean for treated cells. -/
  EY_T : Treated → ℝ
  /-- Observed-law mean for untreated cells. -/
  EY_U : Untreated → ℝ
  /-- Untreated potential-outcome mean for treated cells. -/
  EY0_T : Treated → ℝ
  /-- Untreated potential-outcome mean for untreated cells. -/
  EY0_U : Untreated → ℝ
  /-- Nuisance vector in the untreated outcome model. -/
  beta0 : Regressor → ℝ
  /-- Treated-cell causal effects. -/
  tau : Treated → ℝ

namespace BJSPanel

variable (P : BJSPanel Treated Untreated Regressor)

/-- Target weighted sum over treated-cell effects.  No positivity or
normalization of `a` is imposed. -/
def theta : ℝ :=
  ∑ c : Treated, P.a c * P.tau c

/-- Target value for an arbitrary unrestricted treated-effect vector. -/
def targetForTau (tau' : Treated → ℝ) : ℝ :=
  ∑ c : Treated, P.a c * tau' c

/-- Deterministic untreated-outcome mean model and untreated-cell
no-anticipation / observation equation. -/
def UntreatedOutcomeModel : Prop :=
  (∀ c : Treated, P.EY0_T c = dot (P.qT c) P.beta0) ∧
    (∀ u : Untreated, P.EY0_U u = dot (P.qU u) P.beta0) ∧
      (∀ u : Untreated, P.EY_U u = P.EY0_U u)

/-- Treated-cell effects are fixed at the observed-law mean level:
treated observed means equal untreated means plus `tau`. -/
def TreatmentEffectFixed : Prop :=
  ∀ c : Treated, P.EY_T c = P.EY0_T c + P.tau c

/-- Witness-form prediction span / imputation weights.

The row identity is required only for target-relevant treated cells
(`a c ≠ 0`), matching the BJS identification condition without imposing
positivity, normalization, or a full-rank sufficient condition. -/
structure ImputationWeights where
  /-- Weight assigned to untreated cell `u` when imputing treated cell `c`. -/
  weight : Treated → Untreated → ℝ
  /-- Target-relevant treated rows are linear combinations of untreated rows. -/
  row_identity :
    ∀ c : Treated, P.a c ≠ 0 →
      ∀ r : Regressor, ∑ u : Untreated, weight c u * P.qU u r = P.qT c r

/-- Existence form of the target-relevant prediction-span condition. -/
def PredictionIdentified : Prop :=
  Nonempty P.ImputationWeights

/-- Observed-law population imputation functional for arbitrary imputation
weights.  The row identity is a theorem hypothesis, not part of this
functional's definition. -/
def psiImp (h : Treated → Untreated → ℝ) : ℝ :=
  ∑ c : Treated, P.a c *
    (P.EY_T c - ∑ u : Untreated, h c u * P.EY_U u)

/-- Population BJS imputation identification: under the untreated mean model,
target-relevant prediction weights, and fixed treated effects, the imputation
functional equals the target.

The hypothesis `hPredictionSpan : P.PredictionIdentified` is the natural
existence condition (Assumption 2 of BJS): some imputation weight matrix
satisfies the target-relevant row-span identity.  The concrete witness is
extracted internally via `Classical.choice`. -/
theorem bjs_imputation_identification
    (hUntreatedModel : P.UntreatedOutcomeModel)
    (hPredictionSpan : P.PredictionIdentified)
    (hTreatmentEffectFixed : P.TreatmentEffectFixed) :
    ∃ h : P.ImputationWeights, P.psiImp h.weight = P.theta := by
  classical
  let H : P.ImputationWeights := Classical.choice hPredictionSpan
  refine ⟨H, ?_⟩
  unfold psiImp theta
  refine Finset.sum_congr rfl ?_
  intro c hc
  by_cases hA : P.a c = 0
  · simp [hA]
  · have hEYU : ∀ u : Untreated, P.EY_U u = dot (P.qU u) P.beta0 := by
      intro u
      rw [hUntreatedModel.2.2 u, hUntreatedModel.2.1 u]
    have hImpute :
        (∑ u : Untreated, H.weight c u * P.EY_U u) =
          dot (P.qT c) P.beta0 := by
      unfold dot
      calc
        (∑ u : Untreated, H.weight c u * P.EY_U u)
            = ∑ u : Untreated,
                H.weight c u * ∑ r : Regressor,
                  P.qU u r * P.beta0 r := by
                apply Finset.sum_congr rfl
                intro u hu
                rw [hEYU u]
                rfl
        _ = ∑ u : Untreated, ∑ r : Regressor,
              (H.weight c u * P.qU u r) * P.beta0 r := by
                apply Finset.sum_congr rfl
                intro u hu
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro r hr
                rw [mul_assoc]
        _ = ∑ r : Regressor, ∑ u : Untreated,
              (H.weight c u * P.qU u r) * P.beta0 r := by
                rw [Finset.sum_comm]
        _ = ∑ r : Regressor,
              (∑ u : Untreated, H.weight c u * P.qU u r) *
                P.beta0 r := by
                apply Finset.sum_congr rfl
                intro r hr
                rw [Finset.sum_mul]
        _ = ∑ r : Regressor, P.qT c r * P.beta0 r := by
                apply Finset.sum_congr rfl
                intro r hr
                rw [H.row_identity c hA r]
    have hYT : P.EY_T c = dot (P.qT c) P.beta0 + P.tau c := by
      rw [hTreatmentEffectFixed c, hUntreatedModel.1 c]
    rw [hYT, hImpute]
    simp [add_sub_cancel_left]

/-- A linear functional of treated and untreated observed cell outcomes. -/
structure LinearEstimator (P : BJSPanel Treated Untreated Regressor) where
  /-- Coefficients on treated observed means. -/
  vT : Treated → ℝ
  /-- Coefficients on untreated observed means. -/
  vU : Untreated → ℝ

namespace LinearEstimator

variable {P}

/-- Value of a treated-plus-untreated linear estimator at arbitrary cell
outcome arrays. -/
def value (L : P.LinearEstimator) (YT : Treated → ℝ) (YU : Untreated → ℝ) : ℝ :=
  (∑ c : Treated, L.vT c * YT c) + ∑ u : Untreated, L.vU u * YU u

/-- Observed-law value of the linear estimator on the panel means. -/
def observedValue (L : P.LinearEstimator) : ℝ :=
  L.value P.EY_T P.EY_U

/-- Model-implied value for a nuisance vector and unrestricted treated-effect
vector. -/
def modelValue (L : P.LinearEstimator)
    (beta : Regressor → ℝ) (tau' : Treated → ℝ) : ℝ :=
  L.value
    (fun c : Treated => dot (P.qT c) beta + tau' c)
    (fun u : Untreated => dot (P.qU u) beta)

/-- Linear unbiasedness over unrestricted treated effects and nuisance vectors
in the finite-cell model. -/
def unbiasedForAllTau (L : P.LinearEstimator) : Prop :=
  ∀ (beta : Regressor → ℝ) (tau' : Treated → ℝ),
    L.modelValue beta tau' = P.targetForTau tau'

/-- Unrestricted treatment-effect heterogeneity forces the treated-cell weights to
equal the target weights (`vT = a`).  Proved by an indicator-`tau` test.  Hoisted
here so the efficiency layer can reuse it without re-running the argument. -/
lemma vT_eq_a (L : P.LinearEstimator) (h : L.unbiasedForAllTau) (c : Treated) :
    L.vT c = P.a c := by
  classical
  have hh := h (fun _ : Regressor => 0)
    (fun d : Treated => if d = c then (1 : ℝ) else 0)
  simpa [LinearEstimator.modelValue, LinearEstimator.value, targetForTau, dot] using hh

/-- Nuisance unbiasedness for every `beta` gives the BJS left-null-space coordinate
constraint `aᵀ Q_T + vUᵀ Q_U = 0` (row by row).  Hoisted for the efficiency layer. -/
lemma nuisance_coord (L : P.LinearEstimator) (h : L.unbiasedForAllTau) (r : Regressor) :
    (∑ c : Treated, P.a c * P.qT c r) + ∑ u : Untreated, L.vU u * P.qU u r = 0 := by
  classical
  have hh := h (fun r' : Regressor => if r' = r then (1 : ℝ) else 0)
    (fun _ : Treated => 0)
  simpa [LinearEstimator.modelValue, LinearEstimator.value, targetForTau, dot,
    L.vT_eq_a h] using hh

/-- Explicit imputation representation witness for the linear-unbiased
representation helper.

This is intentionally stronger than the primitive prediction-span hypothesis:
it assumes imputation weights that both satisfy the target-relevant row
identity and represent the untreated coefficients.  The source-strength theorem
`linear_unbiased_of_prediction_identified` constructs this witness from
row-span and left-null-space finite algebra. -/
structure HasImputationRepresentation (L : P.LinearEstimator) where
  /-- Valid target-relevant imputation weights. -/
  weights : P.ImputationWeights
  /-- Untreated coefficients equal the negative target-weighted imputation
  weights. -/
  untreated_weight_representation :
    ∀ u : Untreated, L.vU u = - ∑ c : Treated, P.a c * weights.weight c u

end LinearEstimator

/-- Witness-based BJS linear-unbiased representation lemma, exposed as an
estimator identity for arbitrary outcome arrays.

The source derives the imputation representation from raw row-span and
left-null-space infrastructure.  This lemma deliberately takes an explicit
`hImputationWitness` carrying both the row identity and untreated-weight
representation; it proves the algebraic representation once that finite
linear-algebra existence step has been supplied. -/
theorem linear_unbiased_of_imputation_representation
    (L : P.LinearEstimator)
    (hUnbiasedForAllTau : L.unbiasedForAllTau)
    (hImputationWitness : L.HasImputationRepresentation) :
    ∃ H : P.ImputationWeights,
      (∀ c : Treated, L.vT c = P.a c) ∧
        (∀ u : Untreated, L.vU u = - ∑ c : Treated, P.a c * H.weight c u) ∧
          (∀ (YT : Treated → ℝ) (YU : Untreated → ℝ),
            L.value YT YU =
              ∑ c : Treated, P.a c *
                (YT c - ∑ u : Untreated, H.weight c u * YU u)) ∧
            L.observedValue = P.psiImp H.weight := by
  classical
  let H : P.ImputationWeights := hImputationWitness.weights
  have hVT : ∀ c : Treated, L.vT c = P.a c := by
    intro c
    have h := hUnbiasedForAllTau (fun _ : Regressor => 0)
      (fun d : Treated => if d = c then (1 : ℝ) else 0)
    simpa [LinearEstimator.modelValue, LinearEstimator.value, targetForTau, dot] using h
  have hVU : ∀ u : Untreated, L.vU u = - ∑ c : Treated, P.a c * H.weight c u := by
    intro u
    exact hImputationWitness.untreated_weight_representation u
  have hValue : ∀ (YT : Treated → ℝ) (YU : Untreated → ℝ),
      L.value YT YU =
        ∑ c : Treated, P.a c *
          (YT c - ∑ u : Untreated, H.weight c u * YU u) := by
    intro YT YU
    unfold LinearEstimator.value
    rw [show (∑ c : Treated, L.vT c * YT c) =
        ∑ c : Treated, P.a c * YT c from by
      apply Finset.sum_congr rfl
      intro c hc
      rw [hVT c]]
    rw [show (∑ u : Untreated, L.vU u * YU u) =
        ∑ u : Untreated,
          (-(∑ c : Treated, P.a c * H.weight c u)) * YU u from by
      apply Finset.sum_congr rfl
      intro u hu
      rw [hVU u]]
    have hNeg :
        (∑ u : Untreated,
          (-(∑ c : Treated, P.a c * H.weight c u)) * YU u) =
            -∑ u : Untreated,
              (∑ c : Treated, P.a c * H.weight c u) * YU u := by
      calc
        (∑ u : Untreated,
          (-(∑ c : Treated, P.a c * H.weight c u)) * YU u)
            = ∑ u : Untreated,
                -((∑ c : Treated, P.a c * H.weight c u) * YU u) := by
                apply Finset.sum_congr rfl
                intro u hu
                rw [neg_mul]
        _ = -∑ u : Untreated,
              (∑ c : Treated, P.a c * H.weight c u) * YU u := by
                rw [Finset.sum_neg_distrib]
    have hReindex :
        (∑ u : Untreated,
          (∑ c : Treated, P.a c * H.weight c u) * YU u) =
            ∑ c : Treated, ∑ u : Untreated,
              (P.a c * H.weight c u) * YU u := by
      calc
        (∑ u : Untreated,
          (∑ c : Treated, P.a c * H.weight c u) * YU u)
            = ∑ u : Untreated, ∑ c : Treated,
                (P.a c * H.weight c u) * YU u := by
                apply Finset.sum_congr rfl
                intro u hu
                rw [Finset.sum_mul]
        _ = ∑ c : Treated, ∑ u : Untreated,
              (P.a c * H.weight c u) * YU u := by
                rw [Finset.sum_comm]
    calc
      (∑ c : Treated, P.a c * YT c) +
          ∑ u : Untreated,
            (-(∑ c : Treated, P.a c * H.weight c u)) * YU u
          = (∑ c : Treated, P.a c * YT c) -
              ∑ u : Untreated,
                (∑ c : Treated, P.a c * H.weight c u) * YU u := by
              rw [hNeg, sub_eq_add_neg]
      _ = (∑ c : Treated, P.a c * YT c) -
              ∑ c : Treated, ∑ u : Untreated,
                (P.a c * H.weight c u) * YU u := by
              rw [hReindex]
      _ = ∑ c : Treated,
              (P.a c * YT c -
                ∑ u : Untreated, (P.a c * H.weight c u) * YU u) := by
              rw [Finset.sum_sub_distrib]
      _ = ∑ c : Treated,
              P.a c *
                (YT c - ∑ u : Untreated, H.weight c u * YU u) := by
              apply Finset.sum_congr rfl
              intro c hc
              rw [mul_sub]
              congr
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro u hu
              rw [mul_assoc]
  refine ⟨H, hVT, hVU, hValue, ?_⟩
  unfold LinearEstimator.observedValue psiImp
  exact hValue P.EY_T P.EY_U

/-!
## Note on the Efficiency / BLUE / Gauss-Markov Result

The second half of `prop:po-estimand-bjs-linear-unbiased-imputation` in BJS
(2024) asserts that under spherical errors `Var(ε) = σ² I`, the OLS imputation
estimator is the **minimum-variance linear unbiased estimator** (BLUE /
Gauss-Markov) within the class characterized above.

This efficiency claim is formalized in the companion file
`Causalean/Panel/EstimandCharacterization/ImputationEventStudy/Efficiency.lean` as
`BJSPanel.bjs_ols_imputation_min_variance_spherical`.  It is built on the finite
Gauss-Markov layer under `Causalean/Estimation/GaussMarkov/`:

1. `GaussMarkov.quadVar Σ w = wᵀ Σ w` — the variance quadratic form, justified
   probabilistically by `GaussMarkov.variance_linearCombination`
   (`Var(∑ wᵢ Yᵢ) = wᵀ Σ w` with `Σ i j = cov(Yᵢ, Yⱼ)`).
2. `GaussMarkov.SphericalErrors Σ σ : Σ = σ² • I` (and the random-family form
   `GaussMarkov.SphericalFamily`).
3. `GaussMarkov.olsWeight X c = X (XᵀX)⁻¹ c` — the normal-equations inverse
   OLS weight, with `olsWeight_unbiased` and `olsWeight_mem_colSpan`.
4. `GaussMarkov.gauss_markov_spherical` / `gauss_markov_gls` — the finite
   Gauss-Markov ordering theorems (column-span weight ⟂ left-null-space, so
   Pythagoras gives minimum variance), and `variance_blue_spherical` /
   `variance_blue_gls` lift these to actual `ProbabilityTheory.variance`.

The BJS efficiency theorem instantiates `variance_blue_spherical` at the
event-study design `BJSPanel.designFull` (a treated-cell indicator block stacked
with the covariate block); the BJS imputation estimator is exactly the OLS
estimator for that design.  The hoisted facts `LinearEstimator.vT_eq_a` and
`LinearEstimator.nuisance_coord` supply the unbiasedness ↔ design-constraint
bridge.

The theorems in *this* file (`bjs_imputation_identification`,
`bjs_linear_unbiased_iff_imputation_form`,
`linear_unbiased_of_prediction_identified`) cover the
**identification + linear-unbiased characterization** half; `Efficiency.lean`
covers the **efficiency / BLUE** half.

## Note on `PredictionIdentified` sufficient conditions (G8)

`PredictionIdentified` is defined as `Nonempty P.ImputationWeights` — a
correct propositional existence wrapper, but opaque without a constructive
sufficient condition.  The natural sufficient condition from the paper is:

> For every treated cell `c` with `a c ≠ 0`, the row `qT c` lies in the
> column span of the untreated regressor matrix `(qU u r)_{u,r}`.

A corollary `PredictionIdentified_of_span_rows` could be stated as:

```
theorem PredictionIdentified_of_span_rows
    (hSpan : ∀ c : Treated, P.a c ≠ 0 →
      qT c ∈ Submodule.span ℝ (Set.range P.qU)) :
    P.PredictionIdentified
```

Proving this requires constructing explicit `weight : Treated → Untreated → ℝ`
from the `Submodule.span` membership certificates — specifically extracting
the finite linear-combination coefficients from
`Finsupp.mem_span_range_iff_exists_finsupp` or
`Basis.coord`-style decomposition of `qT c` in the `qU`-span.  This
construction is available in Mathlib but requires non-trivial plumbing between
`Finsupp`, `Fintype.linearCombination`, and the `ImputationWeights.weight`
function type.  It is deferred until the `FiniteLinearAlgebra` helper module
(see `doc/basic_concepts/…`) provides a cleaner interface.

In the meantime, callers can directly construct `ImputationWeights` when they
have an explicit coefficient matrix (the common case in finite examples), and
wrap it with `⟨⟨weight, row_identity⟩⟩ : P.PredictionIdentified`.
-/

end BJSPanel

end

end ImputationEventStudy
end Panel.EstimandCharacterization
end Causalean
