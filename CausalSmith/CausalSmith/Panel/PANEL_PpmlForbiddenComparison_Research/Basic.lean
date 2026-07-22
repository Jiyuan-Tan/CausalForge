import Causalean.Panel.AdoptionPath
import Causalean.Panel.PO.TreatmentPath
import Causalean.Stat.MEstimation.FinitePoisson
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Topology.Order.OrderClosed

/-!
# PPML forbidden comparisons: finite collapsed worlds

This file defines the deterministic triangular-array and collapsed cohort-time
objects used by the paper. Calendar time is zero-indexed in Lean, so Lean
period `0` represents paper period 1. Adoption dates use the shared
`WithTop (Fin T)` convention, with `⊤` denoting never treated.
-/

open scoped BigOperators Topology
open Filter
open Causalean.Stat

namespace CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research

/-- A cohort is an adoption date within the panel, with an additional never-treated cohort. -/
abbrev Cohort (T : ℕ) := WithTop (Fin T)
/-- A cell is a cohort-period pair in the panel. -/
abbrev Cell (T : ℕ) := Cohort T × Fin T
/-- Cohort-time cells restricted to the finite support `C`. -/
abbrev SupportedCell (T : ℕ) (C : Finset (Cohort T)) := ↑C × Fin T

/-- Strictly positive real numbers, used for primitive masses. -/
abbrev PosReal := {x : ℝ // 0 < x}

/-- Limiting shares, whose carrier records the open-unit-interval restriction. -/
abbrev OpenUnit := {x : ℝ // x ∈ Set.Ioo (0 : ℝ) 1}

abbrev CohortDummy (T : ℕ) (C : Finset (Cohort T)) :=
  {g : ↑C // (g.1 : Cohort T) ≠ ⊤}

abbrev TimeDummy (T : ℕ) := {t : Fin T // t.val ≠ 0}

/-- Intercept, non-never-treated cohort effects, and non-base-period time effects. -/
abbrev CollapsedNuisanceIndex (T : ℕ) (C : Finset (Cohort T)) :=
  Unit ⊕ (CohortDummy T C ⊕ TimeDummy T)

/-- The treatment coordinate is stored last, as the second factor. -/
abbrev CollapsedParameter (T : ℕ) (C : Finset (Cohort T)) :=
  (CollapsedNuisanceIndex T C → ℝ) × ℝ

abbrev UnitDummy (N : ℕ) := {i : Fin N // i.val ≠ 0}
  -- @realizes j(non-base unit-dummy index {2,...,N})

/-- Calendar indices use all Lean indices `0,...,T-1`, representing paper periods `1,...,T`. -/
abbrev PeriodIndex (T : ℕ) := Fin T
  -- @realizes t(calendar index Fin T; zero represents paper period one)
  -- @realizes s(effect-perturbation time index Fin T)
  -- @realizes u(calendar-period index {1,...,T})

/-- Unit indices use all Lean indices `0,...,N-1`, representing paper units `1,...,N`. -/
abbrev UnitIndex (N : ℕ) := Fin N
  -- @realizes i(unit index {1,...,N})

abbrev UnitNuisanceIndex (N T : ℕ) :=
  Unit ⊕ (UnitDummy N ⊕ TimeDummy T)

abbrev UnitParameter (N T : ℕ) := (UnitNuisanceIndex N T → ℝ) × ℝ

/-! ## Collapsed cohort-time world -/

-- @env: S1
-- @realizes T(natural-number carrier; range pinned by ValidPanelHorizon)
-- @realizes C(finite support carrier; range pinned by ValidCohortSupport)
-- @realizes g(index in C through membership premises)
-- @realizes k(effect-perturbation cohort index in C)
-- @realizes t(calendar index Fin T; zero represents period one)
-- @realizes s(effect-perturbation time index Fin T)
variable (T : ℕ) (C : Finset (Cohort T))

/-- The paper only considers horizons in `{4,5,...}`. -/
def ValidPanelHorizon : Prop := 4 ≤ T
  -- @realizes T(standing restriction 4 ≤ T)

/-- Supported finite cohorts are paper dates `2,...,T`, and never-treated is supported. -/
def ValidCohortSupport : Prop :=
  (⊤ : Cohort T) ∈ C ∧
  ∀ g : Fin T, (g : Cohort T) ∈ C → g.val ≠ 0
  -- @realizes C(contains infinity and excludes the finite index 0)

/-- Whether adoption cohort `g` is treated in calendar period `t`. -/
noncomputable def treatmentIndicator (g : Cohort T) (t : Fin T) : ℝ :=
  Causalean.Panel.AdoptionPath.absorbingTreatment g t
  -- @realizes D_gt(1{g≤t}, with top never treated)

/-- The finite-array cohort count induced by deterministic cohort labels. -/
def cohortCount {N : ℕ} (G : Fin N → Cohort T) (g : Cohort T) : ℕ :=
  (Finset.univ.filter fun i => G i = g).card
  -- @realizes n_gN(cardinality of the units labelled g)

/-- The cohort index set induced by deterministic labels. -/
def cohortIndexSet {N : ℕ} (G : Fin N → Cohort T) (g : Cohort T) : Finset (Fin N) :=
  Finset.univ.filter fun i => G i = g
  -- @realizes I_gN({i : G_i = g})

/-- The finite-array cohort share `n_gN / N`. -/
noncomputable def cohortShare {N : ℕ} (G : Fin N → Cohort T) (g : Cohort T) : ℝ :=
  (cohortCount T G g : ℝ) / N
  -- @realizes pi_gN(n_gN / N)

/-- A positive supported count and positive panel size put the finite share in `(0,1]`. -/
lemma cohortShare_mem_Ioc {N : ℕ} (G : Fin N → Cohort T) (g : Cohort T)
    (hN : 0 < N) (hCount : 0 < cohortCount T G g) :
    cohortShare T G g ∈ Set.Ioc (0 : ℝ) 1 := by
  rw [Set.mem_Ioc]
  constructor
  · exact div_pos (Nat.cast_pos.mpr hCount) (Nat.cast_pos.mpr hN)
  · rw [cohortShare, div_le_one (Nat.cast_pos.mpr hN)]
    exact_mod_cast (show cohortCount T G g ≤ N by
      simpa [cohortCount] using
        Finset.card_filter_le (Finset.univ : Finset (Fin N)) (fun i => G i = g))
  -- @realizes pi_gN(positive-count and N>0 domain gives range (0,1])

/-- The limiting cohort-time mass `pi_g / T`. -/
noncomputable def limitingCellMass (pi : Cohort T → OpenUnit) (g : Cohort T) : ℝ :=
  (pi g : ℝ) / T
  -- @realizes q_gt(pi_g / T)

/-- The finite-array cohort-time mass `n_gN / (N*T)`. -/
noncomputable def finiteCellMass {N : ℕ} (G : Fin N → Cohort T) (g : Cohort T) : ℝ :=
  (cohortCount T G g : ℝ) / (N * T)
  -- @realizes q_gtN(n_gN / (N*T))

/-- The within-cohort average of the positive unit baseline masses. -/
noncomputable def withinCohortBaseline {N : ℕ} (G : Fin N → Cohort T)
    (b : Fin N → PosReal) (g : Cohort T) : ℝ :=
  (cohortCount T G g : ℝ)⁻¹ * ∑ i ∈ cohortIndexSet T G g, (b i : ℝ)
  -- @realizes bar_b_gN(n_gN⁻¹ times the within-cohort baseline sum)

/-- On its declared positive-count domain, the within-cohort baseline is strictly positive. -/
lemma withinCohortBaseline_pos {N : ℕ} (G : Fin N → Cohort T)
    (b : Fin N → PosReal) (g : Cohort T) (hCount : 0 < cohortCount T G g) :
    0 < withinCohortBaseline T G b g := by
  unfold withinCohortBaseline
  apply mul_pos (inv_pos.mpr (Nat.cast_pos.mpr hCount))
  apply Finset.sum_pos'
  · intro i _
    exact (b i).property.le
  · rw [cohortCount] at hCount
    obtain ⟨i, hi⟩ := Finset.card_pos.mp hCount
    exact ⟨i, by simpa [cohortIndexSet] using hi, (b i).property⟩
  -- @realizes bar_b_gN(positive-count domain gives range (0,infinity))

/-- The finite-array untreated cohort mean. -/
noncomputable def finiteUntreatedMean {N : ℕ} (G : Fin N → Cohort T)
    (b : Fin N → PosReal) (gamma : Fin T → ℝ) (g : Cohort T) (t : Fin T) : ℝ :=
  withinCohortBaseline T G b g * Real.exp (gamma t)
  -- @realizes B_gtN(bar_b_gN * exp gamma_t0)

/-- A supported positive-count cohort has a strictly positive finite untreated mean. -/
lemma finiteUntreatedMean_pos {N : ℕ} (G : Fin N → Cohort T)
    (b : Fin N → PosReal) (gamma : Fin T → ℝ) (g : Cohort T) (t : Fin T)
    (hCount : 0 < cohortCount T G g) :
    0 < finiteUntreatedMean T G b gamma g t := by
  exact mul_pos (withinCohortBaseline_pos T G b g hCount) (Real.exp_pos _)
  -- @realizes B_gtN(positive-count domain gives range (0,infinity))

/-- The limiting untreated cohort mean. -/
noncomputable def untreatedMean (barB : Cohort T → PosReal) (gamma : Fin T → ℝ)
    (g : Cohort T) (t : Fin T) : ℝ :=
  (barB g : ℝ) * Real.exp (gamma t)
  -- @realizes B_gt(bar_b_g * exp gamma_t0)

/-- The finite-array observed cohort mean. -/
noncomputable def finiteObservedCohortMean {N : ℕ} (G : Fin N → Cohort T)
    (b : Fin N → PosReal) (gamma : Fin T → ℝ) (delta : Cell T → ℝ)
    (g : Cohort T) (t : Fin T) : ℝ :=
  finiteUntreatedMean T G b gamma g t *
    Real.exp (treatmentIndicator T g t * delta (g, t))
  -- @realizes m_gtN(delta)(B_gtN * exp(D_gt*delta_gt))

/-- A supported positive-count cohort has a strictly positive finite observed mean. -/
lemma finiteObservedCohortMean_pos {N : ℕ} (G : Fin N → Cohort T)
    (b : Fin N → PosReal) (gamma : Fin T → ℝ) (delta : Cell T → ℝ)
    (g : Cohort T) (t : Fin T) (hCount : 0 < cohortCount T G g) :
    0 < finiteObservedCohortMean T G b gamma delta g t := by
  exact mul_pos (finiteUntreatedMean_pos T G b gamma g t hCount) (Real.exp_pos _)
  -- @realizes m_gtN(delta)(positive-count domain gives range (0,infinity))

/-- The limiting observed cohort mean. -/
noncomputable def observedCohortMean (barB : Cohort T → PosReal) (gamma : Fin T → ℝ)
    (delta : Cell T → ℝ) (g : Cohort T) (t : Fin T) : ℝ :=
  untreatedMean T barB gamma g t * Real.exp (treatmentIndicator T g t * delta (g, t))
  -- @realizes m_gt(delta)(B_gt * exp(D_gt*delta_gt))

/-- The fixed-effect nuisance part of the collapsed regressor. -/
noncomputable def collapsedNuisanceRegressor (g : Cohort T) (t : Fin T) :
    CollapsedNuisanceIndex T C → ℝ
  | Sum.inl _ => 1
  | Sum.inr (Sum.inl c) => if g = c.1.1 then 1 else 0
  | Sum.inr (Sum.inr u) => if t = u.1 then 1 else 0
  -- @realizes X_gt(r_gt with the last treatment coordinate removed)

/-- The collapsed regressor, with treatment as its final coordinate. -/
noncomputable def collapsedRegressor (g : Cohort T) (t : Fin T) :
    CollapsedParameter T C :=
  (collapsedNuisanceRegressor T C g t, treatmentIndicator T g t)
  -- @realizes r_gt(intercept, cohort FE, time FE, then D_gt)

/-- Dot product for collapsed parameters. -/
def collapsedIndex (r theta : CollapsedParameter T C) : ℝ :=
  (∑ j, r.1 j * theta.1 j) + r.2 * theta.2

/-- The limiting collapsed Poisson pseudo-criterion. -/
noncomputable def limitingCriterion (pi : Cohort T → OpenUnit)
    (barB : Cohort T → PosReal) (gamma : Fin T → ℝ) (delta : Cell T → ℝ)
    (theta : CollapsedParameter T C) : ℝ :=
  ∑ g ∈ C, ∑ t : Fin T,
    limitingCellMass T pi g *
      (observedCohortMean T barB gamma delta g t *
          collapsedIndex T C (collapsedRegressor T C g t) theta -
        Real.exp (collapsedIndex T C (collapsedRegressor T C g t) theta))
  -- @realizes L(theta;delta)(finite q_gt-weighted Poisson criterion)
  -- @realizes theta(collapsed coefficient argument; second coordinate is beta)

/-- The finite-array collapsed Poisson pseudo-criterion. -/
noncomputable def finiteCollapsedCriterion {N : ℕ} (G : Fin N → Cohort T)
    (b : Fin N → PosReal) (gamma : Fin T → ℝ) (delta : Cell T → ℝ)
    (theta : CollapsedParameter T C) : ℝ :=
  ∑ g ∈ C, ∑ t : Fin T,
    finiteCellMass T G g *
      (finiteObservedCohortMean T G b gamma delta g t *
          collapsedIndex T C (collapsedRegressor T C g t) theta -
        Real.exp (collapsedIndex T C (collapsedRegressor T C g t) theta))
  -- @realizes L_Nc(theta;delta)(finite collapsed Poisson criterion)

-- @node: def:collapsed-population-projection
/-- The selected maximizer `theta_star(delta)` of the limiting collapsed criterion. -/
noncomputable def collapsedPopulationProjection (pi : Cohort T → OpenUnit)
    (barB : Cohort T → PosReal) (gamma : Fin T → ℝ) (delta : Cell T → ℝ) :
    CollapsedParameter T C :=
  maximizerOrZero (limitingCriterion T C pi barB gamma delta)
  -- @realizes theta_star(delta)(argmax of L(theta;delta))

/-- The treatment coordinate of the limiting pseudo-true parameter. -/
noncomputable def betaStar (pi : Cohort T → OpenUnit) (barB : Cohort T → PosReal)
    (gamma : Fin T → ℝ) (delta : Cell T → ℝ) : ℝ :=
  (collapsedPopulationProjection T C pi barB gamma delta).2
  -- @realizes beta_star(delta)(last coordinate of theta_star(delta))

/-- The fitted limiting cohort-time mean. -/
noncomputable def fittedMean (pi : Cohort T → OpenUnit) (barB : Cohort T → PosReal)
    (gamma : Fin T → ℝ) (delta : Cell T → ℝ) (g : Cohort T) (t : Fin T) : ℝ :=
  Real.exp (collapsedIndex T C (collapsedRegressor T C g t)
    (collapsedPopulationProjection T C pi barB gamma delta))
  -- @realizes mu_star_gt(delta)(exp(r_gt' theta_star(delta)))

/-! ## Finite unit-and-time fixed-effect world -/

abbrev SamplingLaw (Omega : Type*) := (Omega → ℝ) → ℝ
  -- @realizes Omega_N(finite-array outcome sample space)
  -- @realizes Pcal(array family of abstract sampling laws)

/-- The expectation operator carried by the abstract sampling law. -/
def expectationUnder {Omega : Type*} (P : SamplingLaw Omega) : (Omega → ℝ) → ℝ := P
  -- @realizes E_Pcal_N(expectation functional of Pcal_N)

-- @env: S2
-- @realizes N(array size; theorem signatures restrict N relative to C)
-- @realizes G_i(Cohort-valued label carrier; range pinned by hGSupport premises)
-- @realizes Pcal_N(abstract sampling law represented by its expectation functional)
variable (N : ℕ)

/-- The unit treatment indicator induced by its cohort label. -/
noncomputable def unitTreatment (G : Fin N → Cohort T) (i : Fin N) (t : Fin T) : ℝ :=
  treatmentIndicator T (G i) t
  -- @realizes D_it(D_{G_i,t})

/-- Unit-and-time fixed-effect nuisance regressor. -/
noncomputable def unitNuisanceRegressor (i : Fin N) (t : Fin T) :
    UnitNuisanceIndex N T → ℝ
  | Sum.inl _ => 1
  | Sum.inr (Sum.inl j) => if i = j.1 then 1 else 0
  | Sum.inr (Sum.inr u) => if t = u.1 then 1 else 0

/-- The unit-and-time regressor with treatment last. -/
noncomputable def unitRegressor (G : Fin N → Cohort T) (i : Fin N) (t : Fin T) :
    UnitParameter N T :=
  (unitNuisanceRegressor T N i t, unitTreatment T N G i t)
  -- @realizes v_itN(intercept, unit FE, time FE, then D_it)

/-- Dot product for finite-array unit parameters. -/
def unitIndex (v theta : UnitParameter N T) : ℝ :=
  (∑ j, v.1 j * theta.1 j) + v.2 * theta.2
  -- @realizes theta_N(unit-and-time-FE coefficient argument; beta last)

/-- The deterministic unit-time mean implied by the exponential model. -/
noncomputable def unitObservedMean (G : Fin N → Cohort T) (b : Fin N → PosReal)
    (gamma : Fin T → ℝ) (delta : Cell T → ℝ) (i : Fin N) (t : Fin T) : ℝ :=
  (b i : ℝ) * Real.exp (gamma t + unitTreatment T N G i t * delta (G i, t))
  -- @realizes b_iN(positive unit baseline carrier)
  -- @realizes gamma_t0(real time effect; normalization is in UnitUntreatedExponentialMean)
  -- @realizes delta_gt(real cohort-time log proportional effect)
  -- @realizes m_itN(delta)(b_iN * exp(gamma_t0 + D_it*delta_Gi,t))

/-- The unit-and-time-FE population Poisson criterion. -/
noncomputable def unitCriterion (G : Fin N → Cohort T) (b : Fin N → PosReal)
    (gamma : Fin T → ℝ) (delta : Cell T → ℝ) (theta : UnitParameter N T) : ℝ :=
  ((N * T : ℕ) : ℝ)⁻¹ * ∑ i : Fin N, ∑ t : Fin T,
    (unitObservedMean T N G b gamma delta i t *
        unitIndex T N (unitRegressor T N G i t) theta -
      Real.exp (unitIndex T N (unitRegressor T N G i t) theta))
  -- @realizes L_N(theta_N;delta)((NT)⁻¹ finite unit-time Poisson criterion)

-- @node: def:unit-fe-population-projection
/-- The last coordinate of the selected unit-FE population maximizer. -/
noncomputable def betaNStar (G : Fin N → Cohort T) (b : Fin N → PosReal)
    (gamma : Fin T → ℝ) (delta : Cell T → ℝ) : ℝ :=
  (maximizerOrZero (unitCriterion T N G b gamma delta)).2
  -- @realizes beta_Nstar(delta)(last coordinate of argmax L_N)

/-- `Option ℝ` realizes finite unit effects together with `none = -∞`. -/
noncomputable def extendedExp : Option ℝ → ℝ
  | none => 0
  | some x => Real.exp x
  -- @realizes exp(-infty)(extended exponential convention)

abbrev ExtendedCandidate (N T : ℕ) := (Fin N → Option ℝ) × ((Fin T → ℝ) × ℝ)

/-- Extended unit-FE sample objective with finite time and treatment coordinates. -/
noncomputable def sampleCriterion (G : Fin N → Cohort T) (Y : Fin N → Fin T → ℝ)
    (p : ExtendedCandidate N T) : ℝ :=
  ∑ i : Fin N, ∑ t : Fin T,
    let etaFinite := p.2.1 t + p.2.2 * unitTreatment T N G i t
    match p.1 i with
    | none => 0
    | some unitEffect =>
        Y i t * (unitEffect + etaFinite) - Real.exp unitEffect * Real.exp etaFinite

/-- A `-∞` unit effect is admissible only for a unit whose whole outcome path is zero. -/
def ExtendedCandidateAdmissible (Y : Fin N → Fin T → ℝ) (p : ExtendedCandidate N T) : Prop :=
  (∀ t : Fin T, t.val = 0 → p.2.1 t = 0) ∧
  ∀ i : Fin N, p.1 i = none → ∀ t : Fin T, Y i t = 0

/-- Normalized maximizers of the extended sample objective. -/
def IsExtendedSampleMaximizer (G : Fin N → Cohort T) (Y : Fin N → Fin T → ℝ)
    (p : ExtendedCandidate N T) : Prop :=
  ExtendedCandidateAdmissible T N Y p ∧
  ∀ q : ExtendedCandidate N T,
    ExtendedCandidateAdmissible T N Y q →
      sampleCriterion T N G Y q ≤ sampleCriterion T N G Y p

/-- Squared norm of the finite time-effect and treatment coordinates. -/
def finiteCoordinateNormSq (p : ExtendedCandidate N T) : ℝ :=
  (∑ t, (p.2.1 t) ^ 2) + p.2.2 ^ 2

-- @node: def:sample-unit-fe-ppml
/-- The total extended-MLE coefficient, with the stipulated minimum-norm selection and zero fallback. -/
noncomputable def hatBetaN (G : Fin N → Cohort T) (Y : Fin N → Fin T → ℝ) : ℝ :=
  by
    classical
    exact if h : ∃ p : ExtendedCandidate N T,
        IsExtendedSampleMaximizer T N G Y p ∧
        ∀ q, IsExtendedSampleMaximizer T N G Y q →
          finiteCoordinateNormSq T N p ≤ finiteCoordinateNormSq T N q
      then (Classical.choose h).2.2 else 0
  -- @realizes Y_it(observed nonnegative outcome supplied to the sample objective)
  -- @realizes hat_beta_N(beta of minimum-finite-coordinate-norm extended maximizer; zero fallback)

/-! ## Named assumption atoms -/

-- @node: ass:cohort-share-limit
def CohortShareLimit (G : ∀ N, Fin N → Cohort T) (pi : Cohort T → OpenUnit) : Prop :=
  (∀ N, C.card ≤ N →
    0 < N ∧ -- @realizes pi_gN(positive denominator N)
    ∀ g ∈ C,
      0 < cohortCount T (G N) g) ∧ -- @realizes n_gN(supported count in {1,...,N})
                                      -- @realizes pi_gN(strictly positive supported share)
  ∀ g ∈ C, Tendsto (fun N => cohortShare T (G N) g) atTop (nhds (pi g : ℝ))
  -- @realizes pi_g(positive open-unit-interval limit of pi_gN)

-- @node: ass:unit-untreated-exponential-mean
/-- Untreated potential-outcome means factor into a positive unit baseline and a common
calendar-time exponential component; the treatment-zero outcome equals that untreated outcome. -/
def UnitUntreatedExponentialMean (Omega : ℕ → Type*)
    (P : ∀ N, SamplingLaw (Omega N))
    (Y : ∀ N, Fin N → Fin T → Fin 2 → Omega N → ℝ)
    (b : ∀ N, Fin N → PosReal) (gamma : Fin T → ℝ) : Prop :=
  (∀ N i t, expectationUnder (P N) (Y N i t 0) = (b N i : ℝ) * Real.exp (gamma t)) ∧
  ∀ t : Fin T, t.val = 0 → gamma t = 0
  -- @realizes Y_it(d)(potential-outcome random variable; d : Fin 2)

-- @node: ass:within-cohort-baseline-limit
/-- Within each supported cohort, the average unit baseline converges to a strictly positive
cohort-specific limiting baseline. -/
def WithinCohortBaselineLimit (G : ∀ N, Fin N → Cohort T)
    (b : ∀ N, Fin N → PosReal) (barB : Cohort T → PosReal) : Prop :=
  ∀ g ∈ C, Tendsto (fun N => withinCohortBaseline T (G N) (b N) g) atTop (nhds (barB g : ℝ))
  -- @realizes bar_b_g(positive limit of bar_b_gN)

-- @node: ass:proportional-effects
/-- In every treated unit-period, the mean treated outcome equals the mean untreated outcome
multiplied by that cell's exponential treatment effect. -/
def ProportionalEffects (Omega : ℕ → Type*) (P : ∀ N, SamplingLaw (Omega N))
    (Y : ∀ N, Fin N → Fin T → Fin 2 → Omega N → ℝ)
    (G : ∀ N, Fin N → Cohort T) (delta : Cell T → ℝ) : Prop :=
  ∀ N i t, unitTreatment T N (G N) i t = 1 →
    expectationUnder (P N) (Y N i t 1) =
      expectationUnder (P N) (Y N i t 0) * Real.exp (delta (G N i, t))

-- @node: ass:collapsed-design-rank
/-- The collapsed fixed-effects and treatment design has full rank under the limiting cell masses. -/
def CollapsedDesignRank (pi : Cohort T → OpenUnit) : Prop :=
  ∀ a : CollapsedParameter T C, a ≠ 0 →
    0 < ∑ g ∈ C, ∑ t : Fin T,
      limitingCellMass T pi g * (collapsedIndex T C (collapsedRegressor T C g t) a) ^ 2

-- @node: ass:multicohort-frontier-scope
/-- The support contains adoption cohorts 1, 2, and 3, as well as the never-treated cohort. -/
def MulticohortFrontierScope : Prop :=
  (∃ g : Fin T, g.val = 1 ∧ (g : Cohort T) ∈ C) ∧
  (∃ g : Fin T, g.val = 2 ∧ (g : Cohort T) ∈ C) ∧
  (∃ g : Fin T, g.val = 3 ∧ (g : Cohort T) ∈ C) ∧
  (⊤ : Cohort T) ∈ C

-- @node: ass:strict-positive-effects
/-- Every treated cohort-period has a strictly positive log treatment effect. -/
def StrictPositiveEffects (delta : Cell T → ℝ) : Prop :=
  ∀ g ∈ C, ∀ t : Fin T, treatmentIndicator T g t = 1 → 0 < delta (g, t)

end CausalSmith.Panel.PANEL_PpmlForbiddenComparison_Research
