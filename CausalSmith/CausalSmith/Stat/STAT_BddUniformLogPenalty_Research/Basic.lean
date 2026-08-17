import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Helpers.OuterExpectation
import Causalean.Stat.Nonparametric.Approximation.HolderInterpolation
import Causalean.Mathlib.CondDistrib
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

/-!
# Bounded uniform logarithmic penalty: common definitions

This module formalizes the random-design regression laws, distance-compressed
decision classes, completed and outer risks, and the logarithmic frontier rate.
The bivariate covariate is represented by `EuclideanSpace ℝ (Fin 2)`, so every
metric and Hölder condition below uses the paper's Euclidean geometry.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal NNReal Topology

namespace CausalSmith.Stat.BddUniformLogPenalty

/-- Bivariate random-design covariates with their Euclidean `ℓ2` metric. -/
abbrev Score := EuclideanSpace ℝ (Fin 2) -- @realizes X(carrier Euclidean ℝ²)

/-- One observed outcome-covariate pair. -/
abbrev Observation := ℝ × Score -- @realizes Y(carrier ℝ) @realizes X(observed covariate)

/-- An ordered i.i.d. sample of size `n`. -/
abbrev Sample (n : ℕ) := Fin n → Observation

/-- The unsigned-distance compressed sample at one query point. -/
abbrev DistanceSample (n : ℕ) := Fin n → ℝ × ℝ

-- @env: S1
variable (n : ℕ) -- @realizes n(sample size in ℕ)
variable (q : ℕ) -- @realizes q(Hölder order in ℕ)
variable (L : ℝ) -- @realizes L(envelope parameter; theorem regime L≥4)

/-- A CTY random-design regression law. Its density and conditional-moment
fields are pinned to the joint law, rather than supplied as free auxiliaries. -/
structure CtyLaw where
  law : Measure Observation -- @realizes P(law of (Y,X))
  support : Set Score -- @realizes \mathcal{X}_P(compact score support carrier)
  density : Score → ℝ -- @realizes f_P(score-density carrier)
  mu : Score → ℝ -- @realizes \mu_P(regression carrier)
  sigmaSq : Score → ℝ -- @realizes \sigma_P^2(conditional-variance carrier)
  law_isProbability : IsProbabilityMeasure law -- @realizes P(probability law)
  sq_integrable : MemLp Prod.fst 2 law -- @realizes Y(square-integrable outcome)
  marginal_eq : Measure.map Prod.snd law =
    volume.withDensity (fun x => ENNReal.ofReal (support.indicator density x))
    -- @realizes f_P(Lebesgue density of X) @realizes \mathcal{X}_P(density support)
  support_eq_marginal_support : support = (Measure.map Prod.snd law).support
    -- @realizes \mathcal{X}_P(exact topological support of the X-marginal)
  support_closed : IsClosed support -- @realizes \mathcal{X}_P(closed support)
  density_pos : ∀ x ∈ support, 0 < density x -- @realizes f_P(positive on support)
  mu_condMean :
    (let _ : IsProbabilityMeasure law := law_isProbability
     ∀ᵐ x ∂Measure.map Prod.snd law,
       mu x = ∫ y, y ∂(condDistrib Prod.fst Prod.snd law x))
    -- @realizes \mu_P(conditional mean of Y given X)
  sigmaSq_condVar :
    (let _ : IsProbabilityMeasure law := law_isProbability
     ∀ᵐ x ∂Measure.map Prod.snd law,
       sigmaSq x = variance id (condDistrib Prod.fst Prod.snd law x))
    -- @realizes \sigma_P^2(conditional variance of Y given X)

/-- The product law of `n` independent observations from `P`. -/
noncomputable def sampleLaw (P : CtyLaw) (n : ℕ) : Measure (Sample n) := by
  letI : IsProbabilityMeasure P.law := P.law_isProbability
  exact Measure.pi (fun _ : Fin n => P.law)

/-- Rectifiability of the support boundary, expressed by a Lipschitz
parameterization of the boundary by the unit interval. -/
def RectifiableBoundary (S : Set Score) : Prop :=
  ∃ K : ℝ≥0, ∃ γ : ℝ → Score,
    LipschitzOnWith K γ (Icc 0 1) ∧ γ '' Icc 0 1 = frontier S

/-- The coordinate cube `[-r,r]²`, regarded as a subset of Euclidean space. -/
def scoreCube (r : ℝ) : Set Score :=
  {x | ∀ i, |x i| ≤ r}

/-- The standard Hölder ball formed using the Euclidean norm on the bivariate
score carrier. -/
def EuclideanHolderBallStd (f : Score → ℝ) (order M : ℝ)
    (S : Set Score) : Prop :=
  ContDiffOn ℝ (⌈order⌉₊ - 1) f S ∧
    (∀ j : ℕ, j ≤ ⌈order⌉₊ - 1 → ∀ x ∈ S, ‖iteratedFDeriv ℝ j f x‖ ≤ M) ∧
    (∀ x ∈ S, ∀ y ∈ S,
      ‖iteratedFDeriv ℝ (⌈order⌉₊ - 1) f x -
          iteratedFDeriv ℝ (⌈order⌉₊ - 1) f y‖
        ≤ M * ‖x - y‖ ^ (order - ((⌈order⌉₊ - 1 : ℕ) : ℝ)))

-- @node: def:cty-nonparametric-class
/-- The CTY nonparametric law class: i.i.d. probability sampling, a compact
rectifiable score support with a continuous density bounded between `L⁻¹` and
`L`, a `q`-Hölder regression, and a continuous conditional variance with the
same envelope. The fidelity fields of `CtyLaw` identify all three functions
with functionals of the joint law. -/
def CtyNonparametricClass (q : ℕ) (L : ℝ) (P : CtyLaw) : Prop :=
  1 ≤ q ∧ -- @realizes q(regime q≥1)
  4 ≤ L ∧ -- @realizes L(regime L≥4)
  ContinuousOn P.density P.support ∧
  IsCompact P.support ∧ -- @realizes \mathcal{X}_P(compact)
  P.support ⊆ scoreCube L ∧
    -- @realizes \mathcal{X}_P(subset of [-L,L]²)
  (∀ x ∈ P.support, L⁻¹ ≤ P.density x ∧ P.density x ≤ L) ∧
    -- @realizes f_P(range [L⁻¹,L])
  RectifiableBoundary P.support ∧ -- @realizes \mathcal{X}_P(rectifiable boundary)
  EuclideanHolderBallStd P.mu (q : ℝ) L P.support ∧
    -- @realizes \mu_P(q-Hölder ball of radius L)
  ContinuousOn P.sigmaSq P.support ∧
  ∀ x ∈ P.support, L⁻¹ ≤ P.sigmaSq x ∧ P.sigmaSq x ≤ L
    -- @realizes \sigma_P^2(range [L⁻¹,L])

/-- The named class as a set of law objects. -/
def admissibleLaws (q : ℕ) (L : ℝ) : Set CtyLaw :=
  {P | CtyNonparametricClass q L P} -- @realizes \mathcal{P}_{\mathrm{NP}}(set of admissible P)

/-- The labelled support is the topological support of the covariate marginal. -/
lemma support_eq_measureSupport {q : ℕ} {L : ℝ} (P : CtyLaw)
    (_hP : CtyNonparametricClass q L P) :
    (Measure.map Prod.snd P.law).support = P.support := by
  exact P.support_eq_marginal_support.symm

/-- Every relatively open neighborhood of a support point has positive
covariate-marginal mass. -/
lemma class_pos_on_relopen {q : ℕ} {L : ℝ} (P : CtyLaw)
    (_hP : CtyNonparametricClass q L P) (U : Set Score)
    (hU : IsOpen U) (x : Score) (hx : x ∈ U ∩ P.support) :
    0 < Measure.map Prod.snd P.law (U ∩ P.support) := by
  let mu := Measure.map Prod.snd P.law
  have hxs : x ∈ mu.support := by
    simpa [mu, P.support_eq_marginal_support] using hx.2
  have hUpos : 0 < mu U :=
    (Measure.mem_support_iff_forall x).mp hxs U (hU.mem_nhds hx.1)
  rw [show mu (U ∩ P.support) = mu U by
    apply measure_congr
    filter_upwards [mu.support_mem_ae] with y hy
    apply propext
    constructor
    · exact fun h => h.1
    · intro hyU
      refine ⟨hyU, ?_⟩
      simpa [mu, P.support_eq_marginal_support] using hy]
  exact hUpos

/-- Two continuous versions that agree almost everywhere under an admissible
covariate marginal agree at every point of the support, including its boundary. -/
lemma continuous_version_unique_on_support {q : ℕ} {L : ℝ} (P : CtyLaw)
    (hP : CtyNonparametricClass q L P) (f g : Score → ℝ)
    (hf : ContinuousOn f P.support) (hg : ContinuousOn g P.support)
    (hfg : f =ᵐ[Measure.map Prod.snd P.law] g) :
    ∀ x ∈ P.support, f x = g x := by
  let mu := Measure.map Prod.snd P.law
  let E : Set Score := {x | x ∈ P.support ∧ f x = g x}
  have hnull : mu {x | f x ≠ g x} = 0 := by
    exact hfg
  have hclosure : P.support ⊆ closure E := by
    intro x hx
    rw [mem_closure_iff]
    intro U hU hxU
    have hpos : 0 < mu (U ∩ P.support) := by
      exact class_pos_on_relopen P hP U hU x ⟨hxU, hx⟩
    by_contra hUE
    rw [not_nonempty_iff_eq_empty] at hUE
    have hsub : U ∩ P.support ⊆ {y | f y ≠ g y} := by
      intro y hy hEq
      have : y ∈ U ∩ E := ⟨hy.1, hy.2, hEq⟩
      simpa [hUE] using this
    exact (ne_of_gt hpos) (measure_mono_null hsub hnull)
  exact Set.EqOn.of_subset_closure
    (s := E) (t := P.support) (fun _ hx => hx.2) hf hg
    (fun _ hx => hx.1) hclosure

/-- The unsigned-distance sample seen at query point `x`. -/
-- @node: def:cty-distance-data
noncomputable def distanceData (n : ℕ) (w : Sample n) (x : Score) : DistanceSample n :=
  fun i => ((w i).1, dist (w i).2 x)
  -- @realizes V_{n,P}(x)((Y_i, ‖X_i-x‖₂) for i≤n)

/-- For each fixed point, unsigned-distance compression is measurable in the
sample. -/
lemma measurable_distanceData (n : ℕ) (x : Score) :
    Measurable (fun w : Sample n => distanceData n w x) := by
  unfold distanceData
  fun_prop

/-- Ambient type of boundary-indexed regression rules. -/
abbrev RuleFun (n : ℕ) := Sample n → Score → ℝ
  -- @realizes \widehat{\mu}_n(sample-and-point rule)
  -- @realizes \widehat{\mu}^{\mathrm{PI}}_n(sample-and-point rule)

/-- Generator for a CTY rule: one common measurable map at every point. -/
structure CtyRule (n : ℕ) where
  map : DistanceSample n → ℝ
  measurable : Measurable map

/-- Generator for a point-indexed rule. Only fixed-point sections are required
to be measurable; no joint regularity in the query point is imposed. -/
structure PIRule (n : ℕ) where
  map : Score → DistanceSample n → ℝ
  section_measurable : ∀ x, Measurable (map x)

-- @env: S2
variable {n q : ℕ} {L : ℝ}

-- @node: def:cty-distance-decision-class
/-- Rules generated, uniformly over admissible laws, by one law-independent
measurable map of the unsigned-distance data. -/
def CtyDistanceDecisionClass (n q : ℕ) (L : ℝ) : Set (RuleFun n) :=
  {rho | ∃ T : CtyRule n, ∀ P, CtyNonparametricClass q L P →
    ∀ w x, x ∈ frontier P.support → rho w x = T.map (distanceData n w x)}
  -- @realizes \mathcal{T}^{\mathrm{NP}}_n(common-map decision class)
  -- @realizes \widehat{\mu}_n(T_n applied to V_{n,P}(x))

-- @env: S4
variable {n q : ℕ} {L : ℝ}

-- @node: def:point-indexed-distance-decision-class
/-- Rules generated by a law-independent point-indexed family with measurable
fixed-point sections and no joint measurability or continuity in the point. -/
def PointIndexedDecisionClass (n q : ℕ) (L : ℝ) : Set (RuleFun n) :=
  {rho | ∃ T : PIRule n, ∀ P, CtyNonparametricClass q L P →
    ∀ w x, x ∈ frontier P.support → rho w x = T.map x (distanceData n w x)}
  -- @realizes \mathcal{T}^{\mathrm{PI}}_n(sectionwise-Borel decision class)
  -- @realizes \widehat{\mu}^{\mathrm{PI}}_n(T_{n,x} applied to V_{n,P}(x))

/-- The extended nonnegative uniform boundary loss of a rule under a law. -/
noncomputable def boundaryLoss {n : ℕ} (rho : RuleFun n) (P : CtyLaw)
    (w : Sample n) : ℝ≥0∞ :=
  ⨆ x : Score, ⨆ (_hx : x ∈ frontier P.support),
    ENNReal.ofReal |rho w x - P.mu x|

-- @env: S3
variable (n q : ℕ) (L : ℝ)

-- @node: def:cty-distance-risk
/-- The common-map minimax risk, using the ordinary nonnegative expectation on
the completed sample space. -/
noncomputable def ctyDistanceRisk (n q : ℕ) (L : ℝ) : ℝ≥0∞ :=
  ⨅ rho : RuleFun n, ⨅ (_hrho : rho ∈ CtyDistanceDecisionClass n q L),
    ⨆ P : CtyLaw, ⨆ (_hP : CtyNonparametricClass q L P),
      ∫⁻ w, boundaryLoss rho P w ∂(sampleLaw P n).completion
  -- @realizes R_n^{\mathrm{NP}}(completed-expectation inf-sup risk)

-- @node: def:point-indexed-distance-risk
/-- The point-indexed minimax risk, using outer expectation because only the
fixed-point rule sections are assumed measurable. -/
noncomputable def pointIndexedDistanceRisk (n q : ℕ) (L : ℝ) : ℝ≥0∞ :=
  ⨅ rho : RuleFun n, ⨅ (_hrho : rho ∈ PointIndexedDecisionClass n q L),
    ⨆ P : CtyLaw, ⨆ (_hP : CtyNonparametricClass q L P),
      MeasureTheory.outerLIntegral (sampleLaw P n) (boundaryLoss rho P)
  -- @realizes R_n^{\mathrm{PI}}(outer-expectation inf-sup risk)

-- @node: def:frontier-rates
/-- The first-order distance rate `a_n = (log n / n)^(1/4)`. -/
noncomputable def frontierRate (n : ℕ) : ℝ :=
  Real.rpow (Real.log (n : ℝ) / (n : ℝ)) ((1 : ℝ) / 4)
  -- @realizes a_n((log n / n)^(1/4))

/-- The frontier rate is positive once `n ≥ 2`. -/
lemma frontierRate_pos {n : ℕ} (hn : 2 ≤ n) : 0 < frontierRate n := by
  unfold frontierRate
  apply Real.rpow_pos_of_pos
  have hn' : (1 : ℝ) < n := by
    exact_mod_cast (show 1 < n by omega)
  exact div_pos (Real.log_pos hn') (by positivity)

/-- The logarithmic distance frontier rate tends to zero. -/
lemma frontierRate_tendsto_zero :
    Tendsto frontierRate atTop (nhds 0) := by
  have h : Tendsto
      (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ)) atTop (nhds 0) := by
    exact Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
      tendsto_natCast_atTop_atTop
  convert (Real.continuousAt_rpow_const (0 : ℝ) ((1 : ℝ) / 4)
    (Or.inr (by norm_num))).tendsto.comp h using 1 <;> first | rfl | norm_num

/-- A risk normalized by the distance frontier rate. -/
noncomputable def normalizedRisk (risk : ℕ → ℝ≥0∞) (n : ℕ) : ℝ≥0∞ :=
  risk n / ENNReal.ofReal (frontierRate n)

/-- The multiplier form appearing on the left side of the paper's displayed
normalization. -/
noncomputable def scaledRisk (risk : ℕ → ℝ≥0∞) (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal
      (Real.rpow ((n : ℝ) / Real.log (n : ℝ)) ((1 : ℝ) / 4)) * risk n

-- @node: scaledRisk_eventually_eq_normalizedRisk
/-- The multiplier and quotient normalizations agree once the sample size is at
least two. -/
lemma scaledRisk_eventually_eq_normalizedRisk (risk : ℕ → ℝ≥0∞) :
    (fun n => scaledRisk risk n) =ᶠ[atTop]
      (fun n => normalizedRisk risk n) := by
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
  unfold scaledRisk normalizedRisk frontierRate
  have hn0 : (0 : ℝ) < n := by positivity
  have hlog : 0 < Real.log (n : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < n by omega)
  rw [ENNReal.div_eq_inv_mul]
  congr 1
  have hinv :
      (ENNReal.ofReal ((Real.log (n : ℝ) / (n : ℝ)).rpow ((1 : ℝ) / 4)))⁻¹ =
        ENNReal.ofReal (((Real.log (n : ℝ) / (n : ℝ)).rpow ((1 : ℝ) / 4))⁻¹) :=
    (ENNReal.ofReal_inv_of_pos
      (Real.rpow_pos_of_pos (div_pos hlog hn0) _)).symm
  rw [hinv]
  congr 1
  calc
    ((n : ℝ) / Real.log (n : ℝ)).rpow ((1 : ℝ) / 4) =
        ((Real.log (n : ℝ) / (n : ℝ))⁻¹).rpow ((1 : ℝ) / 4) := by
          congr 1
          field_simp
    _ = ((Real.log (n : ℝ) / (n : ℝ)).rpow ((1 : ℝ) / 4))⁻¹ :=
      Real.inv_rpow (le_of_lt (div_pos hlog hn0)) _

end CausalSmith.Stat.BddUniformLogPenalty
