import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Helpers.AngularPacking

/-!
# KL assembly for angular radial laws

This module packages the finite-KL bookkeeping needed to tensorize a
one-observation radial-outcome estimate.  In particular, absolute continuity
and log-likelihood integrability are consequences of a finite real KL bound;
they need not be proved separately by the angular construction.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace CausalSmith.Stat.BddUniformLogPenalty

/-- A finite real bound on one-observation radial KL supplies the absolute
continuity and log-likelihood integrability guards required by product
tensorization. -/
-- @node: compressedSampleLaw_klDiv_le_of_onePoint_finite_bound
lemma compressedSampleLaw_klDiv_le_of_onePoint_finite_bound
    (P P' : CtyLaw) (n : ℕ) (x : Score) {B : ℝ} (hB : 0 ≤ B)
    (hKL : InformationTheory.klDiv (onePointDistanceLaw P x)
      (onePointDistanceLaw P' x) ≤ ENNReal.ofReal B) :
    InformationTheory.klDiv (compressedSampleLaw P n x)
      (compressedSampleLaw P' n x) ≤ ENNReal.ofReal ((n : ℝ) * B) := by
  have hfinite : InformationTheory.klDiv (onePointDistanceLaw P x)
      (onePointDistanceLaw P' x) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hKL
  have hguards := InformationTheory.klDiv_ne_top_iff.mp hfinite
  exact compressedSampleLaw_klDiv_le_of_onePoint P P' n x hB
    hguards.1 hguards.2 hKL

end CausalSmith.Stat.BddUniformLogPenalty
