/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Dose-response minimax: headline frontier handle

Stage-2 scaffold. The headline frontier handle `def:beta-frontier-handle` is a
named `Prop` recording the delivered all-β lower floor with the regime-by-regime
`ρ_n` comparison. The former open residual was removed by the authoritative
manual salvage and is not recreated here.
-/

import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.Helpers.FrontierBracket

namespace CausalSmith.Stat.DoseResponseMinimax

-- @node: def:beta-frontier-handle
/-- Headline frontier handle. For EVERY `β > 0`, records the DELIVERED all-β oracle
lower floor `R_n ≥ c n^{-2α/(2α+1)}` on the corresponding original class, together with the
regime-by-regime `ρ_n` comparison for every `n ≥ 1`. The deficient comparison is
restricted to the note's regime `0 < s < d/4`. The final disjunction records, without
selecting or certifying an upper endpoint, the unresolved upper-frontier alternatives:
attainability of `ρ_n`, an intermediate exponent, or genuinely `β`-sensitive rates. -/
def betaFrontierHandle {d : ℕ} (alpha s M c0 eps0 t0 : ℝ) : Prop :=
  ∀ beta : ℝ, 0 < beta →
    (∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop,
        c * (n : ℝ) ^ (-(2 * alpha / (2 * alpha + 1)))
          ≤ minimaxRisk M n (HolderDoseClass d alpha beta s M c0 eps0 t0) t0)
      ∧ (∀ n : ℕ, 1 ≤ n → (d : ℝ) ≤ 4 * s →
          publishedHoifRate n alpha s d = (n : ℝ) ^ (-(2 * alpha / (2 * alpha + 1))))
      ∧ (∀ n : ℕ, 1 ≤ n → 0 < s ∧ 4 * s < (d : ℝ) →
          publishedHoifRate n alpha s d
              = (n : ℝ) ^ (-(2 / (1 + (d : ℝ) / (4 * s) + 1 / alpha))) ∧
            2 / (1 + (d : ℝ) / (4 * s) + 1 / alpha)
              < 2 * alpha / (2 * alpha + 1))
      ∧ ((∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in Filter.atTop,
            minimaxRisk M n (HolderDoseClass d alpha beta s M c0 eps0 t0) t0
              ≤ C * publishedHoifRate n alpha s d)
        ∨ (∃ kappa C : ℝ,
            2 / (1 + (d : ℝ) / (4 * s) + 1 / alpha) < kappa ∧
            kappa < 2 * alpha / (2 * alpha + 1) ∧ 0 < C ∧
            ∀ᶠ n : ℕ in Filter.atTop,
              minimaxRisk M n (HolderDoseClass d alpha beta s M c0 eps0 t0) t0
                ≤ C * (n : ℝ) ^ (-kappa))
        ∨ (∃ beta' kappa kappa' c C c' C' : ℝ,
            0 < beta' ∧ beta' ≠ beta ∧ kappa' ≠ kappa ∧
            0 < c ∧ 0 < C ∧ 0 < c' ∧ 0 < C' ∧
            (∀ᶠ n : ℕ in Filter.atTop,
              c * (n : ℝ) ^ (-kappa) ≤
                  minimaxRisk M n (HolderDoseClass d alpha beta s M c0 eps0 t0) t0 ∧
              minimaxRisk M n (HolderDoseClass d alpha beta s M c0 eps0 t0) t0
                ≤ C * (n : ℝ) ^ (-kappa)) ∧
            (∀ᶠ n : ℕ in Filter.atTop,
              c' * (n : ℝ) ^ (-kappa') ≤
                  minimaxRisk M n (HolderDoseClass d alpha beta' s M c0 eps0 t0) t0 ∧
              minimaxRisk M n (HolderDoseClass d alpha beta' s M c0 eps0 t0) t0
                ≤ C' * (n : ℝ) ^ (-kappa'))))

end CausalSmith.Stat.DoseResponseMinimax
