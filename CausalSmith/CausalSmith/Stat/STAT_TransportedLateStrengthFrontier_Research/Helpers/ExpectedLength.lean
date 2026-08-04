/-
# Coverage-to-expected-length reduction

Paper-local specializations of the finite-volume honest-confidence-set
machinery in Causalean.
-/

import CausalSmith.Stat.STAT_TransportedLateStrengthFrontier_Research.Frontier
import Causalean.Stat.Minimax.HonestConfidenceSet

namespace CausalSmith.Stat.TransportedLateStrengthFrontier

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Tonelli section identity for a jointly measurable random set. -/
lemma expected_setLength_eq_integral_inclusion
    (Q : Measure Ω) [IsFiniteMeasure Q] (C : Ω → Set ℝ)
    (hgraph : MeasurableSet {p : Ω × ℝ | p.2 ∈ C p.1})
    (hsub : ∀ ω, C ω ⊆ parameterSpace) :
    (∫ ω, setLength (C ω) ∂Q) =
      ∫ u in parameterSpace, (Q {ω | u ∈ C ω}).toReal := by
  clear hsub
  simpa [setLength] using
    Causalean.Stat.expected_restrictedSetVolume_eq_integral_inclusion
      (Q := Q) C parameterSpace hgraph measurableSet_Icc
      (by simp [parameterSpace, Real.volume_Icc])

/-- Uniform coverage on an interval and a TV comparison with its center force
positive expected length at the center law. -/
lemma coverage_tv_expectedLength_lower
    (Q : ℝ → Measure Ω) (C : Ω → Set ℝ) (I : Set ℝ)
    (coverage tv : ℝ)
    (hQ : ∀ u, IsProbabilityMeasure (Q u))
    (hcover : ∀ u ∈ I, coverage ≤ (Q u {ω | u ∈ C ω}).toReal)
    (htv : ∀ u ∈ I, Causalean.Stat.tvDist (Q u) (Q 0) ≤ tv)
    (hgraph : MeasurableSet {p : Ω × ℝ | p.2 ∈ C p.1})
    (hsub : ∀ ω, C ω ⊆ parameterSpace)
    (hI : MeasurableSet I) (hI_sub : I ⊆ parameterSpace) :
    (volume I).toReal * (coverage - tv) ≤
      ∫ ω, setLength (C ω) ∂Q 0 := by
  clear hsub
  simpa [setLength] using
    Causalean.Stat.coverage_tv_expectedRestrictedVolume_lower
      Q C parameterSpace I 0 coverage tv hQ hcover htv hgraph
      measurableSet_Icc (by simp [parameterSpace, Real.volume_Icc]) hI hI_sub

end CausalSmith.Stat.TransportedLateStrengthFrontier
