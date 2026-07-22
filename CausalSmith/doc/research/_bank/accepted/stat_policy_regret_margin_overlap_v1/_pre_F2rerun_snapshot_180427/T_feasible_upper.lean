/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Policy-regret rate: conditional feasible achievability

Stage-2 scaffold. The CONDITIONAL achievability theorem `oeq:feasible-upper`,
stated over `def:upper-risk` with the estimator/fold/process side-conditions
bound as explicit `Prop` hypotheses. Every proof body is `sorry`.
-/

import CausalSmith.Stat.STAT_PolicyRegretMarginOverlap_Research.Basic
import CausalSmith.Stat.STAT_PolicyRegretMarginOverlap_Research.Helpers

namespace CausalSmith.Stat.PolicyRegretMarginOverlap

open MeasureTheory
open scoped BigOperators

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

-- @node: oeq:feasible-upper
/-- `oeq:feasible-upper` (CONDITIONAL achievability). The regime-indexed conditional
upper risk `U_n = upperRisk …` — whose estimator IS the cross-fit clipped-AIPW
`1/n`-ERM `feasibleERM` run with the SELECTED schedule clip `q_n = qSched α γ a c
q0 n`, supremized over the bundled `def:law-class`/optimal/finite-VC/foldwise
nuisance-rate side-condition domain at the fixed regime `(a,c,C_μ,C_prod)` —
achieves the UNIFORM EVENTUAL rate bound `U_n ≤ C n^{-r_feas}(log n)^p`
(`r_feas = (feasibleRate α γ a c q0 uBar).r`), using only the crude `q^{-2}`
score envelope and the deterministic clip-bias controls. CRUCIALLY the constants
`C, p` are chosen BEFORE `n` (quantified outside the `∀ᶠ n in atTop`), so this
encodes the paper's uniform eventual conditional rate bound over `n` — a single
pair `(C,p)` controlling `U_n` for ALL large `n` — not a per-`n` bound with
constants chosen after `n` (which would be vacuous). The schedule admissibility
`q_n ≤ c_o u_n^γ` selected by `def:feasible-rate` is carried as the explicit
hypothesis `hadm` (`feasibleAdmissible`, tying `q_0, ū`). Not an unconditional
minimax upper claim. -/
theorem feasible_upper {K : ℕ}
    (α γ Cm u0 Co co underlineP a c CMu CProd q0 uBar : ℝ) (dPi : ℕ)
    (assign : (m : ℕ) → Fin m → Fin K) (policySet : Set (Policy 𝒳))
    (enum : ℕ → Policy 𝒳) (muHat0 muHat1 eHat : ℕ → Fin K → 𝒳 → ℝ)
    (rMu rE : ℕ → ℝ)
    (hpoly : PolynomialNuisanceExponents rMu rE a c CMu CProd)
    (hvc : PolicyClassVC policySet dPi)
    (hK : FixedFoldCount K assign)
    (henum : ∀ j, enum j ∈ policySet)
    (hq0 : 0 < q0) (huBar : 0 < uBar)
    (hadm : feasibleAdmissible α γ a c co q0 uBar) :
    ∃ C p : ℝ, 0 < C ∧ 0 ≤ p ∧
      ∀ᶠ n : ℕ in Filter.atTop,
        upperRisk (n := n) α γ Cm u0 Co co underlineP a c CMu CProd q0 dPi
            policySet enum muHat0 muHat1 eHat assign rMu rE
          ≤ C * (n : ℝ) ^ (-(feasibleRate α γ a c q0 uBar).r) * (Real.log n) ^ p := by
  sorry

end CausalSmith.Stat.PolicyRegretMarginOverlap
