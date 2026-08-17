import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Causal.LawClass
import Causalean.Mathlib.MeasureTheory.AnalyticSetUniversalMeasurability

/-!
# Known-geometry point-indexed causal decision class and outer risk

Only fixed `(geometry, point)` sections are measurable.  No joint regularity in
the interface point is imposed, so the risk uses outer expectation.
-/

open MeasureTheory Set
open scoped ENNReal

namespace CausalSmith.Stat.BddUniformLogPenalty

/-- Ambient causal rules take the sample, the known geometry, and a query
point. -/
abbrev A1A2RuleFun (n : ℕ) := CausalSample n → GeometryData → Score → ℝ

/-- A law-independent family of Borel fixed sections. -/
structure A1A2PIRule (n : ℕ) where
  map : GeometryData → Score → SignedDistanceSample n → ℝ
  section_measurable : ∀ G x, Measurable (map G x)

-- @env: S7
variable (n p : ℕ) (ν L : ℝ)
  -- @realizes n(causal risk sample size)
  -- @realizes p(local-polynomial order)
  -- @realizes \nu(moment exponent offset)
  -- @realizes L(fixed uniform class envelope)

-- @node: def:cty-a1-a2-point-indexed-decision-class
/-- Known-geometry point-indexed rules with Borel fixed sections and no joint
regularity in the interface index. -/
def A1A2PointIndexedDecisionClass (n p : ℕ) (ν L : ℝ) : Set (A1A2RuleFun n) :=
  {rho | ∃ T : A1A2PIRule n, ∀ P, A1A2Class p ν L P →
    ∀ w x, x ∈ P.boundary →
      rho w (knownGeometry P) x =
        T.map (knownGeometry P) x (signedDistanceData n P w x)}
  -- @realizes \mathcal{T}^{12,\pm}_n(known-geometry point-indexed Borel class)

/-- Extended nonnegative interface-supremum loss. -/
noncomputable def a1a2BoundaryLoss {n : ℕ} (rho : A1A2RuleFun n)
    (P : A1A2Law) (w : CausalSample n) : ℝ≥0∞ :=
  ⨆ x : Score, ⨆ (_hx : x ∈ P.boundary),
    ENNReal.ofReal |rho w (knownGeometry P) x - P.tau x|
  -- @realizes \tau_P(target in interface-supremum loss)

-- @node: def:cty-a1-a2-outer-risk
/-- The known-geometry point-indexed minimax risk under outer expectation. -/
noncomputable def a1a2OuterRisk (n p : ℕ) (ν L : ℝ) : ℝ≥0∞ :=
  ⨅ rho : A1A2RuleFun n,
    ⨅ (_hrho : rho ∈ A1A2PointIndexedDecisionClass n p ν L),
      ⨆ P : A1A2Law, ⨆ (_hP : A1A2Class p ν L P),
        MeasureTheory.outerLIntegral (causalSampleLaw P n) (a1a2BoundaryLoss rho P)
  -- @realizes R_n^{12,\pm}(outer-expectation inf-sup causal risk)

/-- The local and upstream outer-integral spellings agree definitionally. -/
lemma MeasureTheory.outerLIntegral_eq_outerLIntegral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Ω → ℝ≥0∞) :
    MeasureTheory.outerLIntegral μ Z = MeasureTheory.outerLIntegral μ Z := rfl

end CausalSmith.Stat.BddUniformLogPenalty
