/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import CausalSmith.Experimentation.EXP_SaturationSkewThreshold_Research.Basic
import Mathlib.Analysis.MeanInequalities
import Mathlib.Topology.Order.Compact

namespace CausalSmith.Experimentation.SaturationSkew

open MeasureTheory
open scoped BigOperators

-- @node: lem:pearson-centered-moment-bound
/-- Pearson centered-moment bound: the normalized third moment lands in the
centered support domain and the fourth-vs-second moment gap dominates the
squared third moment. -/
lemma pearson_centered_moment_bound (pbar : ℝ) (μ : Law)
    (hsupp : (μ : Measure ℝ) (centeredSupportDomain pbar)ᶜ = 0)
    (hmean : ∫ d, d ∂(μ : Measure ℝ) = 0)
    (s : ℝ) (hs : s = ∫ d, d ^ 2 ∂(μ : Measure ℝ)) (hspos : 0 < s) :
    (∫ d, d ^ 3 ∂(μ : Measure ℝ)) / s ∈ centeredSupportDomain pbar ∧
      (∫ d, d ^ 4 ∂(μ : Measure ℝ)) - s ^ 2
        ≥ (∫ d, d ^ 3 ∂(μ : Measure ℝ)) ^ 2 / s := by sorry

-- @node: lem:second-moment-slices-nonempty
/-- Second-moment slices are nonempty across the admissible second-moment range. -/
lemma second_moment_slices_nonempty (pbar s : ℝ) (hb : BudgetInterior pbar)
    (hs0 : 0 ≤ s) (hs1 : s ≤ pbar * (1 - pbar)) :
    (secondMomentSlice pbar s).Nonempty := by sorry

-- @node: lem:two-point-centered-objective
/-- Two-point centered objective: the CONCRETE two-atom law of the note — `μ` places
mass `b/(a+b)` at `a` and `a/(a+b)` at `-b`, and `ν` is its pushforward under
`d ↦ pbar + d`, i.e. the law placing mass `b/(a+b)` at `pbar + a` and `a/(a+b)` at
`pbar - b` — realizes the prescribed centered moments and the closed-form variance
increment. The note names this specific pushforward law, so the realization PINS `ν`
to that two-atom measure (its defining identity `hν`) rather than existentializing it. -/
lemma two_point_centered_objective (pbar V0 V1 V3 V4 a b : ℝ)
    (ha : 0 < a) (ha1 : a ≤ 1 - pbar) (hb0 : 0 < b) (hb1 : b ≤ pbar)
    (ν : Law)
    (hν : (ν : Measure ℝ)
      = ENNReal.ofReal (b / (a + b)) • Measure.dirac (pbar + a)
        + ENNReal.ofReal (a / (a + b)) • Measure.dirac (pbar - b)) :
    IsAdmissible pbar ν ∧
      centeredMoment pbar 2 ν = a * b ∧
      centeredMoment pbar 3 ν = a * b * (a - b) ∧
      centeredMoment pbar 4 ν - (centeredMoment pbar 2 ν) ^ 2 = a * b * (a - b) ^ 2 ∧
      varianceFunctional V0 V1 V3 V4 pbar ν - V0
        = a * b * (V1 + V3 * (a - b) + V4 * (a - b) ^ 2) := by sorry

-- @node: lem:centered-second-moment-extrema
/-- Extrema of the centered second moment over admissible laws, with the Dirac and
two-endpoint saturation characterizations. -/
lemma centered_second_moment_extrema (pbar : ℝ) (ν : Law) (hν : IsAdmissible pbar ν) :
    0 ≤ centeredMoment pbar 2 ν ∧ centeredMoment pbar 2 ν ≤ pbar * (1 - pbar) ∧
      (centeredMoment pbar 2 ν = 0 → ν = diracLaw pbar) ∧
      (BudgetInterior pbar → centeredMoment pbar 2 ν = pbar * (1 - pbar) →
        (ν : Measure ℝ) (({0, 1} : Finset ℝ) : Set ℝ)ᶜ = 0) := by sorry

-- @node: lem:two-point-endpoint-reduction
/-- Two-point endpoint reduction: the least variance increment over admissible
≤2-atom laws is the min of the two endpoint-pinned profile infima and zero. -/
lemma two_point_endpoint_reduction (V0 V1 V3 V4 pbar : ℝ) (hb : BudgetInterior pbar) :
    IsLeast
      {v : ℝ | ∃ ν : Law, IsAdmissible pbar ν ∧ cardSupportLe 2 ν ∧
        v = varianceFunctional V0 V1 V3 V4 pbar ν - V0}
      (min 0 (min (⨅ t ∈ Set.Icc (-pbar) (1 - 2 * pbar),
                    pbar * (pbar + t) * (V1 + V3 * t + V4 * t ^ 2))
                  (⨅ t ∈ Set.Icc (1 - 2 * pbar) (1 - pbar),
                    (1 - pbar) * ((1 - pbar) - t) * (V1 + V3 * t + V4 * t ^ 2)))) := by sorry

-- @node: lem:fixed-second-moment-envelope
/-- Fixed-second-moment envelope: at a fixed interior second moment, the normalized
third moment lies in an explicit interval and the fourth moment is bounded below and
above. The note's EQUALITY cases are carried explicitly: the lower envelope
`m₄ ≥ s² + s t²` is ATTAINED (with equality) by the two-root centered law on the roots
of `x² - t x - s = 0` (a `≤ 2`-atom law with the same `(mean 0, m₂ = s, m₃)`), and the
upper envelope is ATTAINED by the endpoint-interior law on `{-pbar, r, 1 - pbar}` (a
`≤ 3`-atom law supported on that explicit three-point set with the same first three
moments), where `t = m₃/s` and `r = (m₃ - (q - p) s)/(s - p q)`. -/
lemma fixed_second_moment_envelope (V0 V1 V3 V4 pbar s : ℝ) (hb : BudgetInterior pbar)
    (hs0 : 0 < s) (hs1 : s < pbar * (1 - pbar)) (μ : Law)
    (hsupp : (μ : Measure ℝ) (centeredSupportDomain pbar)ᶜ = 0)
    (hmean : ∫ d, d ∂(μ : Measure ℝ) = 0)
    (hsm : ∫ d, d ^ 2 ∂(μ : Measure ℝ) = s) :
    (∫ d, d ^ 3 ∂(μ : Measure ℝ)) / s ∈ Set.Icc (s / pbar - pbar) ((1 - pbar) - s / (1 - pbar)) ∧
      ((∫ d, d ^ 3 ∂(μ : Measure ℝ)) - ((1 - pbar) - pbar) * s) / (s - pbar * (1 - pbar))
        ∈ Set.Icc (-s / (1 - pbar)) (s / pbar) ∧
      ∫ d, d ^ 4 ∂(μ : Measure ℝ)
        ≥ s ^ 2 + s * ((∫ d, d ^ 3 ∂(μ : Measure ℝ)) / s) ^ 2 ∧
      ∫ d, d ^ 4 ∂(μ : Measure ℝ)
        ≤ (1 - 3 * (pbar * (1 - pbar))) * s
            + (s - pbar * (1 - pbar))
                * ((((∫ d, d ^ 3 ∂(μ : Measure ℝ)) - ((1 - pbar) - pbar) * s)
                      / (s - pbar * (1 - pbar))) ^ 2
                  + ((1 - pbar) - pbar)
                      * (((∫ d, d ^ 3 ∂(μ : Measure ℝ)) - ((1 - pbar) - pbar) * s)
                          / (s - pbar * (1 - pbar)))) ∧
      -- Lower-envelope EQUALITY case: attained by the two-root law on `x² - t x - s = 0`.
      (∃ μ₂ : Law,
        (μ₂ : Measure ℝ) (centeredSupportDomain pbar)ᶜ = 0 ∧
        ∫ d, d ∂(μ₂ : Measure ℝ) = 0 ∧
        ∫ d, d ^ 2 ∂(μ₂ : Measure ℝ) = s ∧
        ∫ d, d ^ 3 ∂(μ₂ : Measure ℝ) = ∫ d, d ^ 3 ∂(μ : Measure ℝ) ∧
        cardSupportLe 2 μ₂ ∧
        ∫ d, d ^ 4 ∂(μ₂ : Measure ℝ)
          = s ^ 2 + s * ((∫ d, d ^ 3 ∂(μ : Measure ℝ)) / s) ^ 2) ∧
      -- Upper-envelope EQUALITY case: attained by the endpoint-interior law on
      -- `{-pbar, r, 1 - pbar}`.
      (∃ μ₃ : Law,
        (μ₃ : Measure ℝ) (centeredSupportDomain pbar)ᶜ = 0 ∧
        ∫ d, d ∂(μ₃ : Measure ℝ) = 0 ∧
        ∫ d, d ^ 2 ∂(μ₃ : Measure ℝ) = s ∧
        ∫ d, d ^ 3 ∂(μ₃ : Measure ℝ) = ∫ d, d ^ 3 ∂(μ : Measure ℝ) ∧
        (μ₃ : Measure ℝ)
            (({-pbar,
                ((∫ d, d ^ 3 ∂(μ : Measure ℝ)) - ((1 - pbar) - pbar) * s)
                  / (s - pbar * (1 - pbar)),
                1 - pbar} : Finset ℝ) : Set ℝ)ᶜ = 0 ∧
        ∫ d, d ^ 4 ∂(μ₃ : Measure ℝ)
          = (1 - 3 * (pbar * (1 - pbar))) * s
              + (s - pbar * (1 - pbar))
                  * ((((∫ d, d ^ 3 ∂(μ : Measure ℝ)) - ((1 - pbar) - pbar) * s)
                        / (s - pbar * (1 - pbar))) ^ 2
                    + ((1 - pbar) - pbar)
                        * (((∫ d, d ^ 3 ∂(μ : Measure ℝ)) - ((1 - pbar) - pbar) * s)
                            / (s - pbar * (1 - pbar))))) := by sorry

end CausalSmith.Experimentation.SaturationSkew
