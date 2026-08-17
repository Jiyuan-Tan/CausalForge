import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Basic
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# CTY Assumptions 1--2: causal world and known geometry

This module introduces the selected-conditional-kernel causal law used by the
second half of the paper, together with its known assignment geometry and the
signed-distance observation.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal Topology

namespace CausalSmith.Stat.BddUniformLogPenalty

/-- A potential-outcome observation `(Y(0), Y(1), X)`. -/
abbrev CausalObservation := ℝ × ℝ × Score
  -- @realizes Y(t)(potential outcomes in ℝ) @realizes X(covariate in Euclidean ℝ²)

/-- An ordered sample of potential-outcome observations. -/
abbrev CausalSample (n : ℕ) := Fin n → CausalObservation

/-- Arm `t` of a potential-outcome observation. -/
def armCoord (t : Bool) (w : CausalObservation) : ℝ :=
  if t then w.2.1 else w.1
  -- @realizes Y(t)(arm-t potential-outcome coordinate)

/-- The score coordinate. -/
def causalScore (w : CausalObservation) : Score := w.2.2
  -- @realizes X(score coordinate)

-- @env: S5
variable (p : ℕ) -- @realizes p(local-polynomial order in ℕ₀)
variable (ν L : ℝ) -- @realizes \nu(moment offset; theorem regime ν≥2)
  -- @realizes L(causal class envelope; theorem regime L≥4)

/-- A decorated causal law carrying one selected arm-indexed regular
conditional-kernel witness.  Forgetting the decoration recovers the bare
data-generating law.  Membership in the law class below constrains the carried
selected representative pointwise. -/
structure A1A2Law where
  law : Measure CausalObservation -- @realizes P(law of (Y(0),Y(1),X))
  support : Set Score -- @realizes \mathcal{X}_P(score-support carrier)
  A0 : Set Score -- @realizes \mathcal{A}_{t,P}(arm-zero assignment region)
  A1 : Set Score -- @realizes \mathcal{A}_{t,P}(arm-one assignment region)
  boundary : Set Score -- @realizes \mathcal{B}_P(interface carrier)
  A0_measurable : MeasurableSet A0
    -- @realizes \mathcal{A}_{t,P}(arm-zero region is Borel)
  A1_measurable : MeasurableSet A1
    -- @realizes \mathcal{A}_{t,P}(arm-one region is Borel)
  assignment_partition : A0 ∪ A1 = support ∧ Disjoint A0 A1
    -- @realizes \mathcal{A}_{t,P}(Borel partition of the support)
  boundary_eq : boundary = frontier A0 ∩ frontier A1
    -- @realizes \mathcal{B}_P(common frontier of the assignment regions)
  boundary_subset_interior : boundary ⊆ interior support
    -- @realizes \mathcal{B}_P(interface lies in the interior support)
  density : Score → ℝ -- @realizes f_P(score-density carrier)
  muPO : Bool → Score → ℝ -- @realizes \mu_{t,P}(conditional-mean carrier)
  sigmaSqPO : Bool → Score → ℝ -- @realizes \sigma^2_{t,P}(conditional-variance carrier)
  condKer : Bool → Kernel Score ℝ -- @realizes Y(t)(selected conditional law given X)
  law_isProbability : IsProbabilityMeasure law -- @realizes P(probability law)
  condKer_markov : ∀ t, IsMarkovKernel (condKer t)
  marginal_eq : Measure.map causalScore law =
    volume.withDensity (fun x => ENNReal.ofReal (support.indicator density x))
    -- @realizes f_P(Lebesgue density of X) @realizes \mathcal{X}_P(density support)
  support_eq_marginal_support : support = (Measure.map causalScore law).support
    -- @realizes \mathcal{X}_P(exact marginal topological support)
  condKer_disint : ∀ t,
    (Measure.map causalScore law).compProd (condKer t) =
      Measure.map (fun w => (causalScore w, armCoord t w)) law
    -- @realizes Y(t)(selected kernel disintegrates joint arm-score law)
  mu_condMean : ∀ t, ∀ᵐ x ∂Measure.map causalScore law,
    muPO t x = ∫ y, y ∂condKer t x
    -- @realizes \mu_{t,P}(conditional mean under selected kernel)
  sigmaSq_condVar : ∀ t, ∀ᵐ x ∂Measure.map causalScore law,
    sigmaSqPO t x = variance id (condKer t x)
    -- @realizes \sigma^2_{t,P}(conditional variance under selected kernel)

/-- The `n`-fold i.i.d. law of potential-outcome observations. -/
noncomputable def causalSampleLaw (P : A1A2Law) (n : ℕ) : Measure (CausalSample n) := by
  letI : IsProbabilityMeasure P.law := P.law_isProbability
  exact Measure.pi (fun _ : Fin n => P.law)

/-- Treatment is the indicator of the known arm-one region. -/
noncomputable def treatment (P : A1A2Law) (w : CausalObservation) : ℝ :=
  P.A1.indicator (fun _ => (1 : ℝ)) (causalScore w)
  -- @realizes T(1{X∈A₁,P})

/-- The observed outcome obeying consistency. -/
noncomputable def observedOutcome (P : A1A2Law) (w : CausalObservation) : ℝ :=
  treatment P w * armCoord true w + (1 - treatment P w) * armCoord false w
  -- @realizes Y(consistency Y=T Y(1)+(1-T)Y(0))

/-- The boundary treatment-effect curve. -/
def A1A2Law.tau (P : A1A2Law) (x : Score) : ℝ :=
  P.muPO true x - P.muPO false x
  -- @realizes \tau_P(μ₁,P-μ₀,P)

/-- The selected conditional absolute moment at exponent `2 + ν`. -/
noncomputable def A1A2Law.condAbsMoment (P : A1A2Law)
    (ν : ℝ) (t : Bool) (x : Score) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal (|y| ^ (2 + ν)) ∂P.condKer t x
  -- @realizes Y(t)(pointwise conditional |Y(t)|^(2+ν) moment)

-- @node: def:cty-uniform-kernel
/-- The fixed uniform smoothing kernel `1{|u| ≤ 1}`. -/
noncomputable def uniformKernel (u : ℝ) : ℝ :=
  Set.Icc (-1 : ℝ) 1 |>.indicator (fun _ => (1 : ℝ)) u
  -- @realizes K_\square(1{|u|≤1})

/-- The tuple of geometry known to every causal decision rule. -/
structure GeometryData where
  support : Set Score
  A0 : Set Score
  A1 : Set Score
  boundary : Set Score
  A0_measurable : MeasurableSet A0
  A1_measurable : MeasurableSet A1
  assignment_partition : A0 ∪ A1 = support ∧ Disjoint A0 A1
  boundary_eq : boundary = frontier A0 ∩ frontier A1
  boundary_subset_interior : boundary ⊆ interior support
  metric : Score → Score → ℝ
  kernel : ℝ → ℝ

-- @node: def:cty-known-geometry
/-- The support, assignment regions, interface, Euclidean metric, and fixed
uniform kernel supplied to the estimator. -/
noncomputable def knownGeometry (P : A1A2Law) : GeometryData where
  support := P.support -- @realizes G_P(support component) @realizes \mathcal{X}_P(known support)
  A0 := P.A0 -- @realizes G_P(A₀ component) @realizes \mathcal{A}_{t,P}(known arm zero)
  A1 := P.A1 -- @realizes G_P(A₁ component) @realizes \mathcal{A}_{t,P}(known arm one)
  boundary := P.boundary
    -- @realizes G_P(interface component) @realizes \mathcal{B}_P(known interface)
  A0_measurable := P.A0_measurable
  A1_measurable := P.A1_measurable
  assignment_partition := P.assignment_partition
  boundary_eq := P.boundary_eq
  boundary_subset_interior := P.boundary_subset_interior
  metric := fun x z => dist x z -- @realizes G_P(metric component) @realizes d_P(Euclidean distance)
  kernel := uniformKernel
    -- @realizes G_P(kernel component) @realizes K_\square(fixed uniform kernel)

/-- Signed Euclidean distance computed from a known geometry. -/
noncomputable def signedDistance (G : GeometryData) (x z : Score) : ℝ :=
  (G.A1.indicator (fun _ => (1 : ℝ)) z -
      G.A0.indicator (fun _ => (1 : ℝ)) z) * G.metric z x
  -- @realizes D^{\pm}_{P,x}((1{A₁}-1{A₀})d_P(X,x))

/-- The observed signed-distance sample. -/
abbrev SignedDistanceSample (n : ℕ) := Fin n → ℝ × ℝ

-- @env: S6
variable (n : ℕ) -- @realizes n(causal sample size in ℕ)
variable (h : ℝ) -- @realizes h(positive bandwidth in theorem regimes)

-- @node: def:cty-known-geometry-signed-distance-data
/-- Observed-outcome and signed-distance pairs for an admissible causal law.
The first coordinate is the law-indexed observed outcome, so consistency and
the assignment partition cannot be bypassed by supplying arbitrary geometry. -/
noncomputable def signedDistanceData (n : ℕ) (P : A1A2Law)
    (w : CausalSample n) (x : Score) : SignedDistanceSample n :=
  fun i => (observedOutcome P (w i),
    signedDistance (knownGeometry P) x (causalScore (w i)))
  -- @realizes U^{\pm}_{n,P}(x)(((Y_i,D^{±}_{P,x,i})) for i≤n)

/-- Geometry-only implementation used by a law-independent rule.  Its input
type carries the Borel-partition and common-interior-frontier invariants. -/
noncomputable def geometrySignedDistanceData (n : ℕ) (G : GeometryData)
    (w : CausalSample n) (x : Score) : SignedDistanceSample n :=
  fun i =>
    (G.A1.indicator (fun _ => armCoord true (w i)) (causalScore (w i)) +
      (1 - G.A1.indicator (fun _ => (1 : ℝ)) (causalScore (w i))) *
        armCoord false (w i),
      signedDistance G x (causalScore (w i)))

/-- The degree-`p` monomial basis `(1,u,…,u^p)`. -/
def polyBasis (p : ℕ) (u : ℝ) : Fin (p + 1) → ℝ :=
  fun k => u ^ (k : ℕ)
  -- @realizes r_p((1,u,…,u^p))

/-- Winsorization at level `B`. -/
noncomputable def winsorize (B y : ℝ) : ℝ :=
  if y < 0 then -min |y| B else if y = 0 then 0 else min |y| B
  -- @realizes \psi_B(sign(y) min(|y|,B))

end CausalSmith.Stat.BddUniformLogPenalty
