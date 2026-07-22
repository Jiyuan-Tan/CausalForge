/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Policy-regret rate: strict-gap tightness (OPEN residual)

Stage-2 scaffold. `oeq:feasible-tight` is the genuinely OPEN strict-gap
tightness question. Per the OEQ rule it is encoded as a named `Prop` `def`
(`FeasibleTightQuestion`) that STATES the residual — whether, in the strict-gap
branch `g_joint < r_⋆`, some genuinely feasible cross-fit estimator attains the
converse exponent `r_⋆` — WITHOUT proving it. No theorem is emitted for this
node and no downstream theorem depends on it; there is no proof and no `sorry`.
-/

import CausalSmith.Stat.STAT_PolicyRegretMarginOverlap_Research.Basic

namespace CausalSmith.Stat.PolicyRegretMarginOverlap

open MeasureTheory
open scoped BigOperators

-- @node: oeq:feasible-tight
/-- `oeq:feasible-tight` (OPEN research question — STATED, not proven).

In the strict-gap branch `g_joint < r_⋆`, the residual question is whether SOME
genuinely feasible cross-fitted-nuisance estimator — the `feasibleERM` built
from estimated nuisances `(μ̂₀, μ̂₁, ê)` that obey the bounded-truncation
(`BoundedCrossfitNuisances`), polynomial cross-fit-rate
(`PolynomialNuisanceExponents` at the same regime `(a, c, C_μ, C_prod)`), and
`L²(P)` nuisance-rate (`NuisanceRate`) conditions over the bundled
side-condition domain `dom` — attains the converse exponent `r_⋆`, i.e. whether
its conditional upper risk `upperRisk dom (feasibleERM …)` decays like
`n^{-r_⋆}` up to logarithmic factors, rather than the slower conditional
exponent `g_joint` of `oeq:feasible-upper`.

Per the OEQ rule this is a `Prop` `def` recording the open proposition: it
carries NO proof, no theorem is emitted for it, and no downstream theorem
depends on it. -/
def FeasibleTightQuestion {𝒳 : Type*} [MeasurableSpace 𝒳] {K : ℕ}
    (α γ Cm u0 Co co underlineP a c CMu CProd q0 : ℝ) (dPi : ℕ)
    (policySet : Set (Policy 𝒳)) (enum : ℕ → Policy 𝒳)
    (assign : (m : ℕ) → Fin m → Fin K) (rMu rE : ℕ → ℝ) : Prop :=
  gJoint α γ a c < rStar α γ →
    -- DETERMINATION: either SOME feasible cross-fitted-nuisance estimator attains
    -- the converse exponent `r_⋆`, …
    (∃ muHat0 muHat1 eHat : ℕ → Fin K → 𝒳 → ℝ,
        (∀ k : Fin K,
          BoundedCrossfitNuisances (fun m => muHat0 m k) (fun m => muHat1 m k)) ∧
        PolynomialNuisanceExponents rMu rE a c CMu CProd ∧
        ∃ C p : ℝ, 0 < C ∧ 0 ≤ p ∧ ∀ᶠ n : ℕ in Filter.atTop,
          upperRisk (n := n) α γ Cm u0 Co co underlineP a c CMu CProd q0 dPi
              policySet enum muHat0 muHat1 eHat assign rMu rE
            ≤ C * (n : ℝ) ^ (-(rStar α γ)) * (Real.log n) ^ p)
    ∨
    -- … or weak-arm nuisance learning imposes the slower conditional exponent
    -- `g_joint` on EVERY feasible cross-fitted-nuisance estimator.
    (∀ muHat0 muHat1 eHat : ℕ → Fin K → 𝒳 → ℝ,
        (∀ k : Fin K,
          BoundedCrossfitNuisances (fun m => muHat0 m k) (fun m => muHat1 m k)) →
        PolynomialNuisanceExponents rMu rE a c CMu CProd →
        ∃ c' : ℝ, 0 < c' ∧ ∀ᶠ n : ℕ in Filter.atTop,
          c' * (n : ℝ) ^ (-(gJoint α γ a c))
            ≤ upperRisk (n := n) α γ Cm u0 Co co underlineP a c CMu CProd q0 dPi
                policySet enum muHat0 muHat1 eHat assign rMu rE)

end CausalSmith.Stat.PolicyRegretMarginOverlap
