import CausalSmith.Stat.STAT_SaPlmCumulantConverse_Research.Helpers.EmpiricalTransformSeries
import CausalSmith.Stat.STAT_SaPlmCumulantConverse_Research.Helpers.JmsComparator
import Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.API
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Recorded local-to-Gaussian open problem

Nothing in this file asserts a solution of the open problem.
-/

noncomputable section

open MeasureTheory
open Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic

namespace CausalSmith.Stat.SaPlmCumulantConverse

variable {Xspace : Type*} [MeasurableSpace Xspace]

/-- A rational candidate circle is represented only by its positive radius. -/
abbrev RationalCircle := {rho : ℚ // 0 < rho}

/-- The finite deterministic rational-circle library at depth `m`. -/
def libraryOfCircles (m : ℕ) : Finset RationalCircle :=
  (Finset.range m).image fun j : ℕ ↦ ⟨((j : ℚ) + 1), by positivity⟩

/-- The point of a candidate circle at a given angle: the circle's rational radius times the
complex exponential of that angle, so that letting the angle run from zero to two pi traverses
the circle once counterclockwise. -/
def candidateCirclePoint (C : RationalCircle) (t : ℝ) : ℂ :=
  (C.1 : ℂ) * Complex.exp (t * Complex.I)

/-- The boundary modulus of a transform on a candidate circle: the smallest absolute value the
transform attains anywhere on the circle of that radius centred at the origin. It is the
quantity that must be certified strictly positive before the transform may be used as the
denominator of a contour integrand. -/
def candidateBoundaryModulus (C : RationalCircle) (Fhat : ℂ → ℂ) : ℝ :=
  sInf ((fun z ↦ ‖Fhat z‖) '' Metric.sphere (0 : ℂ) (C.1 : ℝ))

/-- The denominator in every candidate record is definitionally the actual
empirical transform on its stated inference fold. -/
def candidateEmpiricalF (p : Parameters) (m : Model (Xspace := Xspace) p)
    (data : Fin p.n → Obs Xspace) (a : Fin 2) : ℂ → ℂ :=
  empiricalF p m p.n data (inferenceFold p.n a)

/-- The numerator in every candidate record is definitionally the actual
outcome-weighted empirical transform on its stated inference fold. -/
def candidateEmpiricalG (p : Parameters) (m : Model (Xspace := Xspace) p)
    (data : Fin p.n → Obs Xspace) (a : Fin 2) : ℂ → ℂ :=
  empiricalG p m p.n data (inferenceFold p.n a)

/-- The two empirical contour integrands are formed only after a positive
boundary-modulus certificate has been supplied. -/
def candidateWindingIntegrand (C : RationalCircle) (Fhat : ℂ → ℂ)
    (_hden : 0 < candidateBoundaryModulus C Fhat) (t : ℝ) : ℂ :=
  candidateCirclePoint C t * deriv Fhat (candidateCirclePoint C t) /
    Fhat (candidateCirclePoint C t)

/-- The contour-moment integrand on a candidate circle: at each angle, the circle point times
the value of the numerator transform there, divided by the value of the denominator transform
there. It is formed only after the denominator's boundary modulus on that circle has been
certified strictly positive, so the ratio is well defined all along the contour. -/
def candidateMomentIntegrand (C : RationalCircle) (Fhat Ghat : ℂ → ℂ)
    (_hden : 0 < candidateBoundaryModulus C Fhat) (t : ℝ) : ℂ :=
  candidateCirclePoint C t * Ghat (candidateCirclePoint C t) /
    Fhat (candidateCirclePoint C t)

-- @env: S6
/-- Certified candidate data for one actual sample, inference fold, and
rational circle.  Its values are enclosures, and every soundness field is tied
definitionally to `empiricalF` and `empiricalG` on `inferenceFold`; arbitrary
transform arguments cannot be supplied.  It contains no selector, estimator,
risk, coverage, critical-scale, or lower-bound field. -/
structure CandidateRecord (p : Parameters) (m : Model (Xspace := Xspace) p)
    (data : Fin p.n → Obs Xspace) (depth : ℕ) (C : RationalCircle)
    (hC : C ∈ libraryOfCircles depth) (a : Fin 2) where
  denominatorPositive :
    0 < candidateBoundaryModulus C (candidateEmpiricalF p m data a)
  boundaryModulusEnclosure : RatInterval
  boundaryModulus_sound : boundaryModulusEnclosure.Contains
    (candidateBoundaryModulus C (candidateEmpiricalF p m data a))
  windingEnclosure : ComplexRatInterval
  winding_sound : windingEnclosure.Contains
    ((2 * Real.pi : ℂ)⁻¹ * ∫ t in (0 : ℝ)..2 * Real.pi,
      candidateWindingIntegrand C (candidateEmpiricalF p m data a)
        denominatorPositive t)
  contourMomentEnclosure : ComplexRatInterval
  contourMoment_sound : contourMomentEnclosure.Contains
    ((2 * Real.pi : ℂ)⁻¹ * ∫ t in (0 : ℝ)..2 * Real.pi,
      candidateMomentIntegrand C (candidateEmpiricalF p m data a)
        (candidateEmpiricalG p m data a) denominatorPositive t)
  angularVarianceEnclosure : RatInterval
  angularVariance_sound : angularVarianceEnclosure.Contains
    (let V := candidateMomentIntegrand C (candidateEmpiricalF p m data a)
        (candidateEmpiricalG p m data a) denominatorPositive
      let vbar := (2 * Real.pi : ℂ)⁻¹ * ∫ t in (0 : ℝ)..2 * Real.pi, V t
      (2 * Real.pi)⁻¹ * ∫ t in (0 : ℝ)..2 * Real.pi, ‖V t - vbar‖ ^ 2)
  -- @realizes Fhat(empirical denominator in the displayed contour integrands)
  -- @realizes Ghat(empirical numerator in the displayed contour integrand)

/-- The dependent candidate-data schema computed from the actual empirical
contour integrands on a prespecified fold and rational circle. -/
-- @node: def:local-gaussian-handle
def candidateRecord (p : Parameters) (m : Model (Xspace := Xspace) p)
    (data : Fin p.n → Obs Xspace) (depth : ℕ) (C : RationalCircle)
    (hC : C ∈ libraryOfCircles depth) (a : Fin 2) : Type :=
  CandidateRecord p m data depth C hC a

/--
The unresolved local-to-Gaussian frontier, recorded as complete descriptive
payload rather than an asserted proposition.  The paper leaves the sharp-rate
functional, uniform-inference criterion, selector, confidence procedure, and
matching lower-bound witness undefined.
-/
-- @node: oeq:local-to-gaussian-frontier
def LocalToGaussianFrontier : String :=
  "Open question: for triangular treatment-noise laws with absolute k-th cumulant at least delta_n decreasing to zero under the same supplied code sequences, ask whether there exists a data-driven selector among ordinary DML, finite-order ACE, and global-contour procedures that attains the sharp minimax mean-squared-error rate as a function of n, epsilon_1_n, epsilon_2_n, and delta_n; yields uniformly valid inference across these regimes; and admits a matching local minimax lower bound. Nonassertion: this is a research agenda, not a theorem; the paper defines no unique sharp-rate functional or uniform-inference/coverage criterion and asserts no existential selector, confidence procedure, or matching lower-bound witness. This String is descriptive payload only, contains no witness fields, and is absent from every delivered theorem dependency."

end CausalSmith.Stat.SaPlmCumulantConverse
