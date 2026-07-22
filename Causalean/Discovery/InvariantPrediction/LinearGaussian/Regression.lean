/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Discovery.InvariantPrediction.LinearGaussian.Model

/-!
# Invariant Causal Prediction — regression-invariance null and identified set

The observable layer of the linear-Gaussian ICP problem: the regression
predictor in each environment, the **regression-invariance null** `H_{0,S}`, and
the **identified set** `S(E)` (Peters–Bühlmann–Meinshausen 2016, `eq:betapred`,
`eq:H0Sregr`, `eq:ident`).

## Encoding choices (fidelity notes)

* **Residual.**  `residual γ env ω := Yᵉ(ω) − Σ_k γ k · Xₖᵉ(ω)` with the sum over
  all coordinates (`γ` is supported on `S`, so `k ∉ S` contributes nothing).
  This is `R^e(S)` of the paper (`R^e = Y^e − X^e β`).

* **Support on `S`.**  "`γ` supported on `S`" is `∀ k, γ k ≠ 0 → k ∈ S`
  (`SupportedOn`).  This is the paper's constraint `β_k = 0 if k ∉ S`.

* **Regression-invariance null `H_{0,S}`.** This file uses a pairwise-coordinate
  version of the regression null: there exist a coefficient vector `γ`
  supported on `S` and a fixed residual law `Fε` such that for **every**
  environment `e`, the residual `R^e = Y^e − Σ γ_k X_k^e` is (i) independent of
  each predictor coordinate in `S` and (ii) has law `Fε` (the *same* law across
  environments).  In this jointly Gaussian linear-Gaussian setting,
  coordinatewise independence of the residual from each `X_k`, `k ∈ S`, is
  equivalent to joint independence from the vector `X_S`, so this matches the
  Peters-Buhlmann-Meinshausen regression null despite the weaker-looking form.
  The paper also requires `γ = β^{pred,e}(S)` (the
  population-OLS coefficient); under independence of `R^e` from `X_S^e` that is
  automatic (the residual is orthogonal to `X_S`, i.e. the normal equations
  hold), so we fold it into the independence clause and do not carry `β^{pred}`
  as a separate object.  The **observational**
  environment `obs` is included as one of the environments (it is `e = 1`), so
  invariance is genuinely across the whole family.

* **Residual law as a measure on `ℝ`.**  `Fε : Measure ℝ`; "`R^e ∼ Fε`" is
  `Pᵉ.map (residual γ (env e)) = Fε`.  Equivalently `IdentDistrib` across
  environments; we phrase it via a single shared measure so the "same law" is one
  object.  The mean-shift proof only needs that the two laws differ, which a
  shared-measure formulation exposes directly (`hLawObs`, `hLawEnv`).

* **Identified set `S(E)` (`eq:ident`).**  `S(E) := ⋂ {S : H_{0,S} holds}`.
  We encode the intersection over the (finite) powerset of predictors that
  satisfy the null.
-/

namespace Causalean.Discovery.InvariantPrediction.LinearGaussian

open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {p : ℕ}

/-- `γ` is **supported on `S`**: every nonzero coordinate of `γ` lies in `S`
(the paper's `β_k = 0 if k ∉ S`). -/
def SupportedOn (γ : Fin (p + 1) → ℝ) (S : Finset (Fin (p + 1))) : Prop :=
  ∀ k, γ k ≠ 0 → k ∈ S

/-- The regression residual in the observational SEM:
`R = Y − Σ_k γ k · X_k` (with `γ` supported on `S`, so only `k ∈ S` matter). -/
def obsResidual (M : ObsSEM p) (γ : Fin (p + 1) → ℝ) (ω : M.Ω) : ℝ :=
  M.X ω (target p) - ∑ k, γ k * M.X ω k

/-- The regression residual in an interventional environment, on `M`'s space:
`R^e = Y^e − Σ_k γ k · X_k^e`. -/
def envResidual {M : ObsSEM p} (e : Env M) (γ : Fin (p + 1) → ℝ) (ω : M.Ω) : ℝ :=
  e.X ω (target p) - ∑ k, γ k * e.X ω k

namespace EnvFamily

variable (F : EnvFamily p)

/-- **Pairwise regression-invariance null.**

There exist a coefficient vector `γ` supported on `S` and a single residual law
`Fε : Measure ℝ` such that, in *every* environment of the family (observational
and interventional), the residual `R = Y − Σ γ_k X_k`

* is independent of every predictor coordinate in `S`, and
* has law `Fε` (the same distribution across environments).

In this jointly Gaussian linear-Gaussian setting, coordinatewise independence
of the residual from each `X_k`, `k ∈ S`, is equivalent to joint independence
from the vector `X_S`, so this matches the Peters-Buhlmann-Meinshausen
regression null despite the weaker-looking form. `S(E)` is the intersection of
all `S` for which it holds. -/
def InvarianceNull (S : Finset (Fin (p + 1))) : Prop :=
  ∃ (γ : Fin (p + 1) → ℝ) (Fε : Measure ℝ),
    SupportedOn γ S ∧
    -- observational block `e = 1`
    (∀ k ∈ S, IndepFun (obsResidual F.obs γ) (fun ω => F.obs.X ω k) F.obs.P) ∧
    F.obs.P.map (obsResidual F.obs γ) = Fε ∧
    -- every interventional block shares the same `γ` and the same residual law
    -- (each do-environment lives on `M.Ω = F.obs.Ω` with measure `F.obs.P`)
    (∀ i, ∀ k ∈ S, IndepFun (envResidual (F.env i) γ) (fun ω => (F.env i).X ω k)
      F.obs.P) ∧
    (∀ i, F.obs.P.map (envResidual (F.env i) γ) = Fε)

/-- Decidability of the invariance null, needed for the `filter` in
`invariantSets`.  The predicate is genuinely a `Prop` over measures, so this is
supplied classically. -/
noncomputable instance : DecidablePred (F.InvarianceNull) := fun _ => Classical.dec _

/-- The collection of predictor subsets `S ⊆ {1,…,p}` whose invariance null
holds — the index set of the `S(E)` intersection (`eq:ident`). -/
noncomputable def invariantSets : Finset (Finset (Fin (p + 1))) :=
  (predictors p).powerset.filter (fun S => F.InvarianceNull S)

/-- The **identified set** `S(E) := ⋂ {S : H_{0,S} holds}` (`eq:ident`).

Encoded as the intersection over all predictor subsets satisfying the invariance
null.  If no set satisfies the null the convention `⋂ ∅ = univ` is harmless,
because under the theorem's hypotheses `PA(Y)` itself always satisfies the null
(soundness), so the index set is nonempty. -/
noncomputable def identifiedSet : Finset (Fin (p + 1)) :=
  (F.invariantSets).inf id

/-- Membership in the identified set: `k ∈ S(E)` iff `k` lies in *every* `S`
whose invariance null holds. -/
theorem mem_identifiedSet {k : Fin (p + 1)} :
    k ∈ F.identifiedSet ↔ ∀ S ∈ F.invariantSets, k ∈ S := by
  classical
  simp only [identifiedSet, Finset.mem_inf, id_eq]

/-- Membership in `invariantSets`. -/
theorem mem_invariantSets {S : Finset (Fin (p + 1))} :
    S ∈ F.invariantSets ↔ S ⊆ predictors p ∧ F.InvarianceNull S := by
  classical
  simp [invariantSets, Finset.mem_filter, Finset.mem_powerset]

end EnvFamily

end Causalean.Discovery.InvariantPrediction.LinearGaussian
