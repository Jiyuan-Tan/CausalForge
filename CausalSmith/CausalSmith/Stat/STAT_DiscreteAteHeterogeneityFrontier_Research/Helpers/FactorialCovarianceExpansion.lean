/- Final partial-matching assembly for the marked-factorial covariance bound. -/

import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.FactorialCovarianceSummation

namespace CausalSmith.Stat.DiscreteAteHeterogeneityFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators

-- @node: centeredCrossMoment_allBlockOrderedMarkedFactorial
/-- If [the first factorial order is admissible](hyp:hj) and [the second factorial order is
  admissible](hyp:hr) and [the stated condition on the source size or matching order
  holds](hyp:hm), [the centered product of two paper-local all-block marked factorials is exactly
  the generic mixed-order partial-matching expansion](goal). -/
lemma centeredCrossMoment_allBlockOrderedMarkedFactorial
    {d m K : ℕ} {epsilon M sigma : ℝ}
    (P : ModelClass d epsilon M sigma) (k l : Fin d) (a b : Bool)
    (j r : ℕ) (hj : j + 2 ≤ K) (hr : r + 2 ≤ K)
    (hm : 4 * (K + 2) ^ 2 ≤ m) :
    Causalean.Stat.centeredCrossMoment
      (Measure.infinitePi fun _ : ℕ => P.law.observedLaw)
      (fun ω : ℕ → Obs d =>
        allBlockOrderedMarkedFactorial M (fun i : Fin m => ω i) k a j)
      (fun ω : ℕ → Obs d =>
        allBlockOrderedMarkedFactorial M (fun i : Fin m => ω i) l b r) =
      (Causalean.Stat.matchingNormalization m
          (Causalean.Stat.PartialMatching.empty (j + 2) (r + 2)) - 1) *
          Causalean.Stat.orderedProductMean P.law.observedLaw
            (markedFactorialCoordinate M k a j) *
          Causalean.Stat.orderedProductMean P.law.observedLaw
            (markedFactorialCoordinate M l b r) +
        ∑ h ∈ (Finset.range (min (j + 2) (r + 2) + 1)).filter
            (fun h => 0 < h),
          ∑ N ∈ Causalean.Stat.partialMatchingsOfSize (j + 2) (r + 2) h,
            Causalean.Stat.matchingNormalization m N *
              Causalean.Stat.mergedProductMoment P.law.observedLaw
                (markedFactorialCoordinate M k a j)
                (markedFactorialCoordinate M l b r) N := by
  let S0 := Causalean.Stat.iidSample_infinitePi P.law.observedLaw
  have hKm : K ≤ m := by
    calc
      K ≤ K + 2 := by omega
      _ ≤ (K + 2) ^ 2 := Nat.le_pow (by omega)
      _ ≤ 4 * (K + 2) ^ 2 := by omega
      _ ≤ m := hm
  have hjm : j + 2 ≤ m := hj.trans hKm
  have hrm : r + 2 ≤ m := hr.trans hKm
  have hkstat :
      (fun ω : ℕ → Obs d =>
        allBlockOrderedMarkedFactorial M (fun i : Fin m => ω i) k a j) =
        Causalean.Stat.normalizedOrderedProductStatistic S0
          (markedFactorialCoordinate M k a j) m := by
    funext ω
    exact allBlockOrderedMarkedFactorial_eq_normalizedOrderedProductStatistic
      (m := m) S0 M k a j ω
  have hlstat :
      (fun ω : ℕ → Obs d =>
        allBlockOrderedMarkedFactorial M (fun i : Fin m => ω i) l b r) =
        Causalean.Stat.normalizedOrderedProductStatistic S0
          (markedFactorialCoordinate M l b r) m := by
    funext ω
    exact allBlockOrderedMarkedFactorial_eq_normalizedOrderedProductStatistic
      (m := m) S0 M l b r ω
  rw [hkstat, hlstat]
  exact Causalean.Stat.centeredCrossMoment_normalizedOrderedProductStatistic
    S0 hjm hrm
    (markedFactorialCoordinate M k a j)
    (markedFactorialCoordinate M l b r)
    (measurable_orderedProductKernel_markedFactorialCoordinate M k a j)
    (measurable_orderedProductKernel_markedFactorialCoordinate M l b r)
    (integrable_orderedProductKernel_markedFactorialCoordinate P k a j)
    (integrable_orderedProductKernel_markedFactorialCoordinate P l b r)
    (fun N => measurable_mergedProductKernel_markedFactorialCoordinate
      M k l a b j r N)
    (fun N => integrable_mergedProductKernel_markedFactorialCoordinate
      P k l a b j r N)


end CausalSmith.Stat.DiscreteAteHeterogeneityFrontier
