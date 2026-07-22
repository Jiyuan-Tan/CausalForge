/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Conservative variance estimators

The randomization variance of a design-based estimator typically involves the unidentified
cross-products of potential outcomes, so it cannot be estimated unbiasedly; the standard remedy is a
**conservative** variance estimator `V̂`, whose expectation is at least the true variance.  This
file records that notion (`IsConservativeVarEst`), the basic way to certify it (an expectation that
equals the variance plus a nonnegative bias), and its purpose: a conservative variance estimator
yields a valid — indeed over-covering — Chebyshev tail bound, replacing the unknown true variance by
the estimable `E[V̂]`.
-/

import Causalean.Experimentation.DesignBased.Chebyshev
import Causalean.Experimentation.DesignBased.Risk

/-! # Conservative variance estimators

Conservative variance estimators have expectation at least the true finite-design variance.

`FiniteDesign.IsConservativeVarEst` states the comparison `Var X <= E[Vhat]`.  The lemmas
`FiniteDesign.isConservativeVarEst_of_E_eq_add` and
`FiniteDesign.isConservativeVarEst_of_unbiased` give common certification patterns, and
`FiniteDesign.chebyshev_conservative` turns conservativeness into a valid Chebyshev tail bound
with `E[Vhat]` in place of the unknown variance.
-/

open scoped BigOperators

namespace Causalean
namespace Experimentation
namespace DesignBased

namespace FiniteDesign

variable {Ω : Type*} [Fintype Ω] (D : FiniteDesign Ω)

/-- A variance estimator `Vhat` is **conservative** for `X` when its expectation is at least the
randomization variance of `X`. -/
def IsConservativeVarEst (Vhat X : Ω → ℝ) : Prop := D.Var X ≤ D.E Vhat

/-- A variance estimator whose expectation equals the variance plus a nonnegative bias is
conservative. -/
lemma isConservativeVarEst_of_E_eq_add {Vhat X : Ω → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (h : D.E Vhat = D.Var X + B) : D.IsConservativeVarEst Vhat X := by
  rw [IsConservativeVarEst, h]; exact le_add_of_nonneg_right hB

/-- An unbiased variance estimator (its expectation equals the variance) is conservative. -/
lemma isConservativeVarEst_of_unbiased {Vhat X : Ω → ℝ} (h : D.E Vhat = D.Var X) :
    D.IsConservativeVarEst Vhat X := by
  rw [IsConservativeVarEst, h]

/-- **Conservative Chebyshev bound.** If the design expectation of a proposed variance estimator is
at least the randomization variance of `X`, then the probability that `X` deviates from its mean by
at least `ε` is bounded by that expected estimator divided by `ε²`. -/
theorem chebyshev_conservative {Vhat X : Ω → ℝ} (hcons : D.IsConservativeVarEst Vhat X)
    {ε : ℝ} (hε : 0 < ε) :
    D.Pr (fun z => ε ≤ |X z - D.E X|) ≤ D.E Vhat / ε ^ 2 := by
  have hε2 : (0 : ℝ) < ε ^ 2 := pow_pos hε 2
  have hc : D.Var X ≤ D.E Vhat := hcons
  calc D.Pr (fun z => ε ≤ |X z - D.E X|)
      ≤ D.Var X / ε ^ 2 := D.chebyshev X hε
    _ ≤ D.E Vhat / ε ^ 2 := by gcongr

end FiniteDesign

end DesignBased
end Experimentation
end Causalean
