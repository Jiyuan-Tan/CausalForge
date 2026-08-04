/-
# Regular-cell cross averages and collision scale

The raw collision kernel is nondegenerate.  Its variance is handled by the
Hoeffding projection plus the degenerate remainder; only the remainder enters
Causalean's `DegenKernel` variance API.
-/

import CausalSmith.Stat.STAT_TransportedLateStrengthFrontier_Research.Helpers.ScoreInversion
import Causalean.Stat.UStatistic.Basic
import Causalean.Stat.UStatistic.Variance
import Causalean.Stat.Sample.CollisionEstimator
import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.MultinomialMoments

namespace CausalSmith.Stat.TransportedLateStrengthFrontier

open MeasureTheory
open scoped BigOperators

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

/-- Symmetric, generally nondegenerate collision kernel. -/
noncomputable abbrev collisionKernel (q : 𝒳 → ℝ) (x y : 𝒳) : ℝ :=
  Causalean.Stat.collisionKernel q x y

/-- Ordered-pair collision estimate of Kish dispersion. -/
noncomputable abbrev collisionScale (q : 𝒳 → ℝ) {N : ℕ}
    (target : Fin N → 𝒳) : ℝ :=
  Causalean.Stat.collisionScale q target

/-- Source-cell inverse-frequency moment estimate. -/
noncomputable abbrev cellMoment (q : 𝒳 → ℝ) {n : ℕ}
    (sample : SourceSample 𝒳 n) (G : SourceObs 𝒳 → ℝ) (x : 𝒳) : ℝ :=
  Causalean.Stat.cellMoment q Prod.fst sample G x

/-- Cross-average using target empirical cell frequencies. -/
noncomputable abbrev crossAverage (q : 𝒳 → ℝ) {n N : ℕ}
    (source : SourceSample 𝒳 n) (target : TargetSample 𝒳 N)
    (G : SourceObs 𝒳 → ℝ) : ℝ :=
  Causalean.Stat.crossAverage q Prod.fst source target G

/-- Regular-cell inversion rule using cross-averaged outcome and receipt moments
and the collision estimate of the transport scale. -/
noncomputable def regularCellInversion (q e : 𝒳 → ℝ) {n N : ℕ} (L : ℝ)
    (source : SourceSample 𝒳 n) (target : TargetSample 𝒳 N) : Set ℝ :=
  if N < 2 then parameterSpace else
  {theta | theta ∈ parameterSpace ∧
    |crossAverage q source target
        (fun o => oracleInstrumentScore e o * o.2.2.2) -
      theta * crossAverage q source target
        (fun o => oracleInstrumentScore e o * boolReal o.2.2.1)| ≤
      L * Real.sqrt ((1 + collisionScale q target) / n)}

/-- Uniform-cell specialization with `q_x=1/k` and `e=1/2`. -/
noncomputable def finiteCellInversion (k n N : ℕ) (L : ℝ)
    (source : SourceSample 𝒳 n) (target : TargetSample 𝒳 N) :
    Set ℝ :=
  regularCellInversion (fun _ => (k : ℝ)⁻¹) (fun _ => (1 : ℝ) / 2)
    L source target

end CausalSmith.Stat.TransportedLateStrengthFrontier
