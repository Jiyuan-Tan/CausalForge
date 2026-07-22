/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import CausalSmith.Experimentation.EXP_SaturationSkewThreshold_Research.Basic
import Mathlib.Analysis.Convex.KreinMilman

namespace CausalSmith.Experimentation.SaturationSkew
open MeasureTheory
open scoped BigOperators

-- @node: lem:extreme-moment-slice-support
/-- SUBSTRATE-GATE (Winkler 1988 / Pinelis 2012), realized as a threaded `Prop`
assumption (NOT a discharged lemma): on a slice fixing the first two centered
moments, a minimizer of the continuous linear functional `∫ f dμ` can be taken at
an extreme point, supported on at most three atoms. Consumers (`prop:support-at-most-three`,
`prop:design-optimal-saturation`) take this as an inline hypothesis. Visible
substrate debt; excluded from the theorem manifest. -/
def ExtremeMomentSliceSupport : Prop :=
  ∀ (pbar s : ℝ) (f : ℝ → ℝ), Continuous f →
    {μ : Law | (μ : Measure ℝ) (centeredSupportDomain pbar)ᶜ = 0 ∧
        ∫ d, d ∂(μ : Measure ℝ) = 0 ∧ ∫ d, d ^ 2 ∂(μ : Measure ℝ) = s}.Nonempty →
    ∃ μ : Law,
      ((μ : Measure ℝ) (centeredSupportDomain pbar)ᶜ = 0 ∧
        ∫ d, d ∂(μ : Measure ℝ) = 0 ∧ ∫ d, d ^ 2 ∂(μ : Measure ℝ) = s) ∧
      (∀ η : Law, ((η : Measure ℝ) (centeredSupportDomain pbar)ᶜ = 0 ∧
          ∫ d, d ∂(η : Measure ℝ) = 0 ∧ ∫ d, d ^ 2 ∂(η : Measure ℝ) = s) →
        ∫ d, f d ∂(μ : Measure ℝ) ≤ ∫ d, f d ∂(η : Measure ℝ)) ∧
      cardSupportLe 3 μ

end CausalSmith.Experimentation.SaturationSkew
