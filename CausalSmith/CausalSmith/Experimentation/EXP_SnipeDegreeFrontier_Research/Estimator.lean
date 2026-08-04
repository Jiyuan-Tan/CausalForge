import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Basic
import Causalean.Experimentation.DesignBased.Risk
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Graph-aware SNIPE estimators and minimax risks

The estimator receives the known graph together with assignment and observed
outcomes.  The risk then composes one global estimator with each model's own
graph before applying `FiniteDesign.mse`.
-/

open scoped BigOperators
open Finset

namespace CausalSmith.Experimentation.SnipeDegreeFrontier

open Causalean.Experimentation.DesignBased

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A Boolean graph's in-neighborhood. -/
def nbhdB (G : V → V → Bool) (i : V) : Finset V :=
  Finset.univ.filter (fun j => G j i)

/-- Turn a model's decidable relation into estimator data. -/
def edgeFn (M : ModelClass V d β B) : V → V → Bool :=
  fun j i => @decide (M.edge j i) (M.decEdge j i)

/-- The same graph encoding for the bounded-outcome class. -/
def edgeFnBdd (M : BddOutcomeModelClass V d β B) : V → V → Bool :=
  fun j i => @decide (M.edge j i) (M.decEdge j i)

/-- A graph-aware estimator of the finite-population contrast. -/
-- @env: S3
abbrev Estimator (V : Type*) :=
  (V → V → Bool) → (V → Bool) → (V → ℝ) → ℝ
-- @realizes \widehat\tau_n(generic graph-aware estimator)

/-- Measurability in the outcome vector, with graph and assignment fixed. -/
def OutcomeMeasurable (est : Estimator V) : Prop :=
  ∀ G z, Measurable (fun y : V → ℝ => est G z y)

/-- The centered SNIPE score read from the estimator's graph argument. -/
-- @node: def:snipe-score
noncomputable def snipeScore
    (G : V → V → Bool) (β : ℕ) (p : ℝ) (i : V) (z : V → Bool) : ℝ :=
  ∑ r ∈ Finset.Icc 1 (effBeta β (nbhdB G i).card),
    (bernoulliContrast p r / (p * (1 - p)) ^ r) *
      ∑ S ∈ ((nbhdB G i).powerset.filter (fun S => S.card = r)),
        ∏ j ∈ S, ((if z j then (1 : ℝ) else 0) - p)
-- @realizes g_{i,\beta,p}(centered Bernoulli contrast score)

/-- Clip a scalar to `[-radius,radius]`. -/
def clipTo (radius x : ℝ) : ℝ :=
  max (-radius) (min radius x)

/-- SNIPE, as one graph-aware estimator valid for every model in the supremum. -/
noncomputable def snipeEstimator (β : ℕ) (p : ℝ) : Estimator V :=
  fun G z y =>
    (Fintype.card V : ℝ)⁻¹ *
      ∑ i : V, y i * snipeScore G β p i z
-- @realizes \widehat\tau_n^{\mathrm{SNIPE}}(n⁻¹ sum Yobs_i g_i)

/-- SNIPE projected onto the coefficient-class target interval `[-B,B]`. -/
noncomputable def snipeClipped (B : ℝ) (β : ℕ) (p : ℝ) : Estimator V :=
  fun G z y => clipTo B (snipeEstimator β p G z y)
-- @realizes \widehat\tau_n^{\mathrm{up}}(projection onto [-B,B])

/-- The paper's two jointly defined SNIPE estimators: the raw estimator and
its Euclidean projection onto `[-B,B]`. -/
-- @node: def:snipe-estimator
noncomputable def snipeEstimatorBundle
    (B : ℝ) (β : ℕ) (p : ℝ) : Estimator V × Estimator V :=
  (snipeEstimator β p, snipeClipped B β p)

/-- Design MSE of one graph-aware estimator at a coefficient-mass model. -/
noncomputable def riskAt
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (M : ModelClass V d β B) (est : Estimator V) : ℝ :=
  (bernoulliDesign (fun _ : V => p) (fun _ => hp0) (fun _ => hp1)).mse
    (fun z => est (edgeFn M) z (obsOutcome M.edge M.coef z))
    (tte M.edge M.coef)

/-- Worst-case MSE over the coefficient-mass model class. -/
noncomputable def worstRisk
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (d β : ℕ) (B : ℝ) (est : Estimator V) : ℝ :=
  sSup (Set.range fun M : ModelClass V d β B => riskAt p hp0 hp1 M est)

/-- A measurable estimator is admissible for the real-valued minimax
infimum only when its modelwise risk range is bounded above.  This excludes
the conditionally-complete `sSup` junk value for unbounded competitors. -/
def AdmissibleEstimator
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (d β : ℕ) (B : ℝ) (est : Estimator V) : Prop :=
  OutcomeMeasurable est ∧
    BddAbove (Set.range fun M : ModelClass V d β B =>
      riskAt p hp0 hp1 M est)

/-- Infimum, over measurable graph-aware estimators, of worst-case MSE. -/
-- @node: def:minimax-risk
noncomputable def minimaxRisk
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (d β : ℕ) (B : ℝ) : ℝ :=
  sInf {r : ℝ | ∃ est : Estimator V,
    AdmissibleEstimator p hp0 hp1 d β B est ∧
      r = worstRisk p hp0 hp1 d β B est}
-- @realizes R_n^\star(d,\beta,p,B)(infimum of coefficient-class worst risk)

/-- Design MSE at a uniformly bounded-outcome model. -/
noncomputable def riskAtBdd
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (M : BddOutcomeModelClass V d β B) (est : Estimator V) : ℝ :=
  (bernoulliDesign (fun _ : V => p) (fun _ => hp0) (fun _ => hp1)).mse
    (fun z => est (edgeFnBdd M) z (obsOutcome M.edge M.coef z))
    (tte M.edge M.coef)

/-- Worst-case MSE over uniformly bounded potential outcomes. -/
noncomputable def worstRiskBdd
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (d β : ℕ) (B : ℝ) (est : Estimator V) : ℝ :=
  sSup (Set.range fun M : BddOutcomeModelClass V d β B =>
    riskAtBdd p hp0 hp1 M est)

/-- Bounded-outcome analogue of `AdmissibleEstimator`. -/
def AdmissibleEstimatorBdd
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (d β : ℕ) (B : ℝ) (est : Estimator V) : Prop :=
  OutcomeMeasurable est ∧
    BddAbove (Set.range fun M : BddOutcomeModelClass V d β B =>
      riskAtBdd p hp0 hp1 M est)

/-- The coefficient-mass minimax risk in the two-class notation. -/
noncomputable def minimaxRiskL1
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (d β : ℕ) (B : ℝ) : ℝ :=
  @minimaxRisk V _ _ p hp0 hp1 d β B
-- @realizes R_{n,\ell_1}^{\star}(d,\beta,p,B)(definitionally R_n^\star)

/-- The minimax risk over the uniformly bounded-outcome class. -/
noncomputable def minimaxRiskBddOutcome
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (d β : ℕ) (B : ℝ) : ℝ :=
  sInf {r : ℝ | ∃ est : Estimator V,
    AdmissibleEstimatorBdd p hp0 hp1 d β B est ∧
      r = worstRiskBdd p hp0 hp1 d β B est}
-- @realizes R_{n,\infty}^{\star}(d,\beta,p,B)(bounded-outcome minimax MSE)

/-- The two minimax risks introduced simultaneously in the paper. -/
-- @node: def:two-class-minimax-risks
noncomputable def twoClassMinimaxRisks
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (d β : ℕ) (B : ℝ) : ℝ × ℝ :=
  (minimaxRiskL1 (V := V) p hp0 hp1 d β B,
    minimaxRiskBddOutcome (V := V) p hp0 hp1 d β B)

/-- SNIPE projected onto the bounded-outcome target interval `[-2B,2B]`. -/
-- @node: def:bounded-outcome-clipped-snipe
noncomputable def snipeClippedBdd (B : ℝ) (β : ℕ) (p : ℝ) : Estimator V :=
  fun G z y => clipTo (2 * B) (snipeEstimator β p G z y)
-- @realizes \widehat\tau_{n,\infty}^{\mathrm{up}}(projection onto [-2B,2B])

end CausalSmith.Experimentation.SnipeDegreeFrontier
