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

SCOPE (Lean encoding fidelity): the enumeration `enum : ℕ → Policy 𝒳` threaded
through `upperRisk` carries the note's dense-`Π₀` enumeration condition: the open
dichotomy is guarded by `DenseSkeleton enum policySet`, so the residual question is
recorded specifically for the pointwise-dense-skeleton feasible ERM of
`def:feasible-erm`, consistent with `def:upper-risk` and `oeq:feasible-upper`.

Per the OEQ rule this is a `Prop` `def` recording the open proposition: it
carries NO proof, no theorem is emitted for it, and no downstream theorem
depends on it. -/
def FeasibleTightQuestion {𝒳 : Type*} [MeasurableSpace 𝒳] {K : ℕ}
    (α γ Cm u0 Co co underlineP a c CMu CProd q0 : ℝ) (dPi : ℕ)
    (policySet : Set (Policy 𝒳)) (enum : ℕ → Policy 𝒳)
    (assign : (m : ℕ) → Fin m → Fin K) (rMu rE : ℕ → ℝ) : Prop :=
  -- The achievability predicate: SOME genuinely feasible cross-fitted-nuisance estimator
  -- attains the converse exponent `r_⋆` over a GENUINELY INHABITED feasible side-condition
  -- domain. SCAFFOLD REDIRECT: the `∃ P …` guard must witness the SAME bundled domain that
  -- `upperRisk` takes its `sSup` over (`def:upper-risk`), otherwise an EMPTY `upperRisk`
  -- domain (`sSup ∅ = 0`) would satisfy `Attains` vacuously. So the guard pins ALL the
  -- `upperRisk` side conditions: `IsIIDSample` (`ass:iid`), `NuisanceRate` (`ass:nuisance-rate`),
  -- `PolicyClassVC` (`ass:policy-class`), the two localized VC envelopes
  -- (`ass:vc-localized-envelope`, `ass:vc-localized-offset-envelope`), `FixedFoldCount`
  -- (`ass:fixed-crossfit-fold-count`), and `DenseSkeleton` (the dense-`Π₀` enumeration), in
  -- addition to the `BoundedCrossfitNuisances`/`PolynomialNuisanceExponents` conjuncts already
  -- carried in the outer existential — exactly the genuinely feasible domain of `def:upper-risk`.
  let Attains : Prop :=
    (∃ muHat0 muHat1 eHat : ℕ → Fin K → 𝒳 → ℝ,
        (∀ k : Fin K,
          BoundedCrossfitNuisances (fun m => muHat0 m k) (fun m => muHat1 m k)) ∧
        PolynomialNuisanceExponents rMu rE a c CMu CProd ∧
        (∃ P : ObservedLaw 𝒳,
          LawClass α γ Cm u0 Co co underlineP policySet P ∧
            OptimalInClass P policySet ∧
            IsIIDSample P ∧
            (∀ k : Fin K,
              NuisanceRate P (fun m => muHat0 m k) (fun m => muHat1 m k)
                (fun m => eHat m k) rMu rE) ∧
            PolicyClassVC policySet dPi ∧
            VCLocalizedEnvelope P policySet α ∧
            VCLocalizedOffsetEnvelope P policySet α ∧
            FixedFoldCount K assign ∧
            DenseSkeleton enum policySet) ∧
        ∃ C p : ℝ, 0 < C ∧ 0 ≤ p ∧ ∀ᶠ n : ℕ in Filter.atTop,
          upperRisk (n := n) α γ Cm u0 Co co underlineP a c CMu CProd q0 dPi
              policySet enum muHat0 muHat1 eHat assign rMu rE
            ≤ C * (n : ℝ) ^ (-(rStar α γ)) * (Real.log n) ^ p)
  -- The SUBSTANTIVE slower-exponent alternative: weak-arm nuisance learning genuinely
  -- IMPOSES the slower conditional exponent `g_joint` — over an inhabited feasible domain,
  -- EVERY feasible cross-fitted-nuisance estimator has worst-case risk `U_n` bounded BELOW
  -- by `c' n^{-g_joint}` (so NO feasible estimator attains `r_⋆`; the feasible rate is
  -- exactly `g_joint`, matching the proven `U_n ≤ C n^{-g_joint}` upper bound). This is the
  -- `∀`-over-estimators DETERMINATION the NL asks for — not the trivial `¬ Attains`
  -- (a classical tautology) nor a single failing-config existential.
  -- UNIFORM CONVERSE-FLOOR CONSTANT (scaffold redirect): the floor constant `c'` is
  -- quantified ABOVE the `∀`-over-estimators, so a SINGLE `c' > 0` (depending only on the
  -- regime/class, not on the particular feasible estimator) certifies the `g_joint` floor
  -- uniformly over the whole feasible-estimator class — the "feasible rate is exactly
  -- `g_joint`" determination, with the converse constant chosen BEFORE fixing the estimator
  -- (mirroring the uniform `c(C_χ)` of `lem:le-cam-two-point-chisq`), not after.
  let SlowerImposed : Prop :=
    (∃ P : ObservedLaw 𝒳,
        LawClass α γ Cm u0 Co co underlineP policySet P ∧ OptimalInClass P policySet) ∧
    (∃ c' : ℝ, 0 < c' ∧
      ∀ muHat0 muHat1 eHat : ℕ → Fin K → 𝒳 → ℝ,
        (∀ k : Fin K,
          BoundedCrossfitNuisances (fun m => muHat0 m k) (fun m => muHat1 m k)) →
        PolynomialNuisanceExponents rMu rE a c CMu CProd →
        ∀ᶠ n : ℕ in Filter.atTop,
          c' * (n : ℝ) ^ (-(gJoint α γ a c))
            ≤ upperRisk (n := n) α γ Cm u0 Co co underlineP a c CMu CProd q0 dPi
                policySet enum muHat0 muHat1 eHat assign rMu rE)
  -- The OPEN DICHOTOMY (STATED, not resolved): for the genuine pointwise-dense-skeleton
  -- ERM (`DenseSkeleton enum policySet`, the note's dense-`Π₀` enumeration condition on
  -- `enum`), in the strict-gap branch, EITHER some feasible estimator attains `r_⋆`
  -- (`Attains`) OR the slower exponent `g_joint` is genuinely imposed for every feasible
  -- estimator (`SlowerImposed`).
  DenseSkeleton enum policySet → gJoint α γ a c < rStar α γ → (Attains ∨ SlowerImposed)

end CausalSmith.Stat.PolicyRegretMarginOverlap
