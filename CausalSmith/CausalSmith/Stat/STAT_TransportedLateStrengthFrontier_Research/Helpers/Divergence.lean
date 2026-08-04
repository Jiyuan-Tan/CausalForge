/-
# Divergence bounds for the continuum witness

Local bridge lemmas connect the explicit source law to Causalean's general-space
chi-square tensorization and ancillary-product cancellation.
-/

import CausalSmith.Stat.STAT_TransportedLateStrengthFrontier_Research.Helpers.Witness
import Causalean.Stat.Minimax.ChiSquared
import Causalean.Stat.Minimax.TotalVariation
import Causalean.Stat.Minimax.Scheffe

namespace CausalSmith.Stat.TransportedLateStrengthFrontier

open MeasureTheory

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

/-- Per-source-observation chi-square calibration for the continuum witness. -/
lemma witness_source_chiSq_bound
    (g : Geometry 𝒳) (k : ℕ → ℕ) (epsilon t0 : ℝ)
    (hepsilon : 0 < epsilon) (hg : AdmissibleGeometry g k epsilon)
    (n : ℕ) (h : ℝ) (hh : |h| ≤ 1 / 4)
    (hvalid : ∀ x, 0 ≤ geometryCompliance g t0 n x ∧
      geometryCompliance g t0 n x ≤ 1) :
    Causalean.Stat.chiSqDiv
        (sourceObsLaw (geometryWitnessFamily g t0 h) n)
        (sourceObsLaw (geometryWitnessFamily g t0 0) n) ≤
      8 * geometryMu g t0 n ^ 2 * h ^ 2 / geometryKish g n := by
  exact geometryWitnessFamily_source_chiSq_bound
    g k epsilon t0 hepsilon hg n h hh hvalid

end CausalSmith.Stat.TransportedLateStrengthFrontier
