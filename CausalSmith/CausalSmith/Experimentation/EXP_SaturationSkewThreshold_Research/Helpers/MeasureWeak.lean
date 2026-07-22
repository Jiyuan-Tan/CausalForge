/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import CausalSmith.Experimentation.EXP_SaturationSkewThreshold_Research.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

namespace CausalSmith.Experimentation.SaturationSkew
open MeasureTheory
open scoped BigOperators

-- @node: lem:compact-support-probability-laws-weakly-compact
/-- Prokhorov on an arbitrary compact interval: for any `a ≤ b`, the set of laws
supported on the compact interval `[a,b]` is weakly compact (the note states this for
an arbitrary compact interval `I`, not only `[0,1]`). The supported-on-`[0,1]` set
`{ν | SupportedOn01 ν}` is the special case `a = 0, b = 1`. -/
lemma probabilityMeasure_isCompact (a b : ℝ) :
    IsCompact {ν : Law | (ν : Measure ℝ) (Set.Icc a b)ᶜ = 0} := by sorry

-- @node: lem:bounded-continuous-integrals-weakly-continuous
/-- Portmanteau on a compact interval `I = [a,b]`: if `g` is bounded and continuous
on `I`, then `ν ↦ ∫ g dν` is weakly continuous on `P(I)`. The note states this for
an arbitrary compact interval `I`, NOT for all laws on `ℝ`; the realization restricts
the domain to the laws supported on `[a,b]` (`ν (Icc a b)ᶜ = 0`) and only requires `g`
bounded on that interval. -/
lemma weaklyContinuous_integral_bddCont (a b : ℝ) (g : ℝ → ℝ) (hg : Continuous g)
    (hb : ∃ C : ℝ, ∀ x ∈ Set.Icc a b, |g x| ≤ C) :
    ContinuousOn (fun ν : Law => ∫ x, g x ∂(ν : Measure ℝ))
      {ν : Law | (ν : Measure ℝ) (Set.Icc a b)ᶜ = 0} := by sorry

-- @node: lem:continuous-function-attains-minimum-on-compact-set
/-- A continuous real function attains its minimum on a nonempty compact set. -/
lemma continuous_attains_min_compact {α : Type*} [TopologicalSpace α] {K : Set α}
    (hK : IsCompact K) (hne : K.Nonempty) {h : α → ℝ} (hh : ContinuousOn h K) :
    ∃ x ∈ K, ∀ y ∈ K, h x ≤ h y := by sorry

-- @node: lem:compact-moment-program-attains
/-- The compact quartic moment program attains its minimum, globally and on slices. -/
lemma compact_moment_program_attains (V0 V1 V3 V4 pbar : ℝ) (hb : BudgetInterior pbar) :
    (∃ ν, IsMinimizer V0 V1 V3 V4 pbar ν) ∧
      (∀ s : ℝ, (secondMomentSlice pbar s).Nonempty →
        ∃ ν ∈ secondMomentSlice pbar s, ∀ η ∈ secondMomentSlice pbar s,
          (∫ u, (V1 * (u - pbar) ^ 2 + V3 * (u - pbar) ^ 3 + V4 * (u - pbar) ^ 4)
              ∂(ν : Measure ℝ))
            ≤ (∫ u, (V1 * (u - pbar) ^ 2 + V3 * (u - pbar) ^ 3 + V4 * (u - pbar) ^ 4)
              ∂(η : Measure ℝ))) := by sorry

-- @node: lem:compact-convex-moment-slice
/-- The fixed-second-moment slice is compact and a minimizer over it exists. -/
lemma compact_convex_moment_slice (pbar s : ℝ) :
    IsCompact {μ : Law | (μ : Measure ℝ) (centeredSupportDomain pbar)ᶜ = 0 ∧
        ∫ d, d ∂(μ : Measure ℝ) = 0 ∧ ∫ d, d ^ 2 ∂(μ : Measure ℝ) = s} ∧
      (∀ g : ℝ → ℝ, Continuous g → (∃ C : ℝ, ∀ x, |g x| ≤ C) →
        ({μ : Law | (μ : Measure ℝ) (centeredSupportDomain pbar)ᶜ = 0 ∧
          ∫ d, d ∂(μ : Measure ℝ) = 0 ∧ ∫ d, d ^ 2 ∂(μ : Measure ℝ) = s}).Nonempty →
        ∃ μ ∈ {μ : Law | (μ : Measure ℝ) (centeredSupportDomain pbar)ᶜ = 0 ∧
            ∫ d, d ∂(μ : Measure ℝ) = 0 ∧ ∫ d, d ^ 2 ∂(μ : Measure ℝ) = s},
          ∀ η ∈ {μ : Law | (μ : Measure ℝ) (centeredSupportDomain pbar)ᶜ = 0 ∧
            ∫ d, d ∂(μ : Measure ℝ) = 0 ∧ ∫ d, d ^ 2 ∂(μ : Measure ℝ) = s},
            ∫ d, g d ∂(μ : Measure ℝ) ≤ ∫ d, g d ∂(η : Measure ℝ)) := by sorry

-- @node: lem:boundary-admissible-law-singleton
/-- At a budget boundary the only admissible law is the boundary Dirac mass. -/
lemma boundary_admissible_law_singleton (pbar : ℝ) (hpb : pbar = 0 ∨ pbar = 1) :
    ∀ ν : Law, IsAdmissible pbar ν ↔ ν = diracLaw pbar := by sorry

end CausalSmith.Experimentation.SaturationSkew
