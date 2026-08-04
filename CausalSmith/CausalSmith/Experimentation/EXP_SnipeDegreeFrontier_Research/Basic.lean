import Causalean.Experimentation.DesignBased.Designs.Bernoulli
import Causalean.Experimentation.DesignBased.PotentialOutcome
import Mathlib.Order.Interval.Finset.Nat

/-!
# SNIPE degree-frontier model

This file defines the finite-population graph, raw polynomial potential outcomes,
and the two model classes used throughout the paper.  The Causalean Bernoulli
product design supplies the assignment law; a bare directed relation is used for
the interference graph because self-loops are part of the model.

Substrate survey: `Causalean.Experimentation.DesignBased.Designs.Bernoulli` is
reused for the assignment law.  The exposure-mapping potential-outcome layer and
`Causalean.Graph.DAG` are bypassed because the former hides the raw polynomial
coefficients and the latter forbids the required self-loops.
-/

open scoped BigOperators
open Finset

namespace CausalSmith.Experimentation.SnipeDegreeFrontier

open Causalean.Experimentation.DesignBased

-- @env: S1
variable {V : Type*} [Fintype V] [DecidableEq V]
-- @realizes V_n(finite population carrier)
-- @realizes n(Fintype.card V)
-- @realizes i(unit index in V)
-- @realizes j(assignment-coordinate index in V)
-- @realizes l(overlapping-neighborhood index in V)

/-- The in-neighborhood `{j | G j i}` of an outcome unit. -/
noncomputable def nbhd (G : V → V → Prop) (i : V) : Finset V :=
  by
    classical
    exact Finset.univ.filter (fun j => G j i)
-- @realizes G_n(directed relation on V_n)
-- @realizes N_i({j | G_n j i})

/-- The out-neighborhood `{i | G j i}` of an assignment coordinate. -/
noncomputable def outNbhd (G : V → V → Prop) (j : V) : Finset V :=
  by
    classical
    exact Finset.univ.filter (fun i => G j i)

/-- The Bernoulli contrast `(1-p)^r - (-p)^r`. -/
def bernoulliContrast (p : ℝ) (r : ℕ) : ℝ :=
  (1 - p) ^ r - (-p) ^ r
-- @realizes \Delta_r(p)((1-p)^r - (-p)^r)

/-- The effective interaction order `min β d`. -/
def effBeta (β d : ℕ) : ℕ := min β d
-- @realizes \beta(interaction order in ℕ)
-- @realizes \bar\beta_d(min β d)

/-- The standing degree-index restriction `d ≤ n = |V|`. -/
def DegreeIndex (V : Type*) [Fintype V] (d : ℕ) : Prop :=
  d ≤ Fintype.card V
-- @realizes d(degree bound in {0,...,Fintype.card V})

/-- A nonconstant interaction order in `{1,...,min β d}`. -/
def OrderIndex (β d r : ℕ) : Prop :=
  1 ≤ r ∧ r ≤ effBeta β d
-- @realizes r(interaction-order index restricted to 1 ≤ r ≤ min β d)

/-- A finite subset of the in-neighborhood of `i`. -/
def NeighborhoodSubset
    (G : V → V → Prop) (i : V) (S : Finset V) : Prop :=
  S ⊆ nbhd G i
-- @realizes S(finite subset S ⊆ N_i)

/-- The largest exposed order, with value zero when the exposed set is empty. -/
-- @node: def:exposed-order
noncomputable def kStar (d β : ℕ) (p : ℝ) : ℕ :=
  let exposed : Finset ℕ :=
    (Finset.Icc 1 (effBeta β d)).filter (fun r => bernoulliContrast p r ≠ 0)
  if h : exposed.Nonempty then exposed.max' h else 0
-- @realizes k_\star(maximum nonvanishing Bernoulli contrast order)

/-- A finite design is the common-probability product Bernoulli design, with
the paper's strict overlap condition `0 < p < 1`. -/
-- @node: ass:bernoulli-design
def IsProductBernoulli (D : FiniteDesign (V → Bool)) (p : ℝ) : Prop :=
  0 < p ∧ p < 1 ∧
    ∃ (hp0 : ∀ _ : V, (0 : ℝ) ≤ p) (hp1 : ∀ _ : V, p ≤ 1),
      D = bernoulliDesign (fun _ => p) hp0 hp1
-- @realizes p(common Bernoulli probability in (0,1))
-- @realizes P_Z(product Bernoulli assignment law)
-- @realizes \mathbb E_Z(FiniteDesign.E under P_Z)

/-- Both directed degrees are at most `d`; loops are neither removed nor
treated specially, and hence are counted in both finsets. -/
-- @node: ass:bounded-degree
def BoundedDegree (G : V → V → Prop) (d : ℕ) : Prop :=
  (∀ i, (nbhd G i).card ≤ d) ∧
    ∀ j, (outNbhd G j).card ≤ d

/-- Raw polynomial coefficients above order `β` vanish. -/
-- @node: ass:low-order
def LowOrder (c : V → Finset V → ℝ) (β : ℕ) : Prop :=
  ∀ i S, β < S.card → c i S = 0
-- @realizes c(coefficient schedule)
-- @realizes c_{i,S}(real raw-monomial coefficient)

/-- The raw coefficient mass in every outcome neighborhood is at most `B`. -/
-- @node: ass:bounded-coefficient-mass
noncomputable def BoundedCoeffMass
    (G : V → V → Prop) (c : V → Finset V → ℝ) (B : ℝ) : Prop :=
  ∀ i, ∑ S ∈ (nbhd G i).powerset, |c i S| ≤ B
-- @realizes B(nonnegative coefficient envelope when theorem assumptions impose 0 ≤ B)

/-- A raw-monomial potential outcome on the in-neighborhood of `i`. -/
-- @env: S2
noncomputable def potentialOutcome
    (G : V → V → Prop) (c : V → Finset V → ℝ)
    (i : V) (z : V → Bool) : ℝ := -- @realizes z(generic assignment z : V → Bool)
  ∑ S ∈ (nbhd G i).powerset,
    c i S * ∏ j ∈ S, if z j then (1 : ℝ) else 0
-- @realizes Y_i(z)(sum of raw monomials over N_i)

/-- The observed-outcome vector obtained by evaluating the fixed schedule at
the realized assignment. -/
noncomputable def obsOutcome
    (G : V → V → Prop) (c : V → Finset V → ℝ)
    (Z : V → Bool) : V → ℝ := -- @realizes Z(realized assignment Z : V → Bool)
  fun i => potentialOutcome G c i Z
-- @realizes Y_i^{\mathrm{obs}}(Y_i evaluated at Z)

/-- The finite-population all-treated versus all-control contrast. -/
noncomputable def tte
    (G : V → V → Prop) (c : V → Finset V → ℝ) : ℝ :=
  (Fintype.card V : ℝ)⁻¹ *
    ∑ i : V,
      (potentialOutcome G c i (fun _ => true) -
        potentialOutcome G c i (fun _ => false))
-- @realizes \tau_n(n⁻¹ sum of all-one versus all-zero contrasts)

/-- A directed graph with both degrees bounded by `d`. -/
-- @node: def:graph-class
structure GraphClass (V : Type*) [Fintype V] [DecidableEq V] (d : ℕ) where
  edge : V → V → Prop -- @realizes \mathcal G_{n,d}(graph carrier)
  decEdge : DecidableRel edge
  degree_le : BoundedDegree edge d -- @realizes G_n(bounded in/out degree, loops retained)

/-- A neighborhood-supported, low-order coefficient schedule with bounded
raw coefficient mass. -/
-- @node: def:coefficient-class
structure CoeffClass
    (G : V → V → Prop) (β : ℕ) (B : ℝ) where
  coef : V → Finset V → ℝ -- @realizes \mathcal C_{n,d,\beta}(B)(schedule carrier)
  supported : ∀ i S, ¬ S ⊆ nbhd G i → coef i S = 0
  low_order : LowOrder coef β
  mass_le : BoundedCoeffMass G coef B

/-- The graph-and-schedule class used by the coefficient-mass minimax risk. -/
-- @node: def:model-class
structure ModelClass
    (V : Type*) [Fintype V] [DecidableEq V] (d β : ℕ) (B : ℝ) where
  edge : V → V → Prop -- @realizes \mathcal M_{n,d,\beta}(B)(graph component)
  decEdge : DecidableRel edge
  coef : V → Finset V → ℝ -- @realizes \mathcal M_{n,d,\beta}(B)(schedule component)
  supported : ∀ i S, ¬ S ⊆ nbhd edge i → coef i S = 0
  degree_le : BoundedDegree edge d
  low_order : LowOrder coef β
  mass_le : BoundedCoeffMass edge coef B

namespace ModelClass

/-- Assemble the flat model class from its graph and schedule components. -/
def ofComponents (g : GraphClass V d) (c : CoeffClass g.edge β B) :
    ModelClass V d β B :=
  { edge := g.edge
    decEdge := g.decEdge
    coef := c.coef
    supported := c.supported
    degree_le := g.degree_le
    low_order := c.low_order
    mass_le := c.mass_le }

/-- Project a model to its bounded-degree graph. -/
def toGraphClass (M : ModelClass V d β B) : GraphClass V d :=
  { edge := M.edge, decEdge := M.decEdge, degree_le := M.degree_le }

/-- Project a model to its coefficient schedule. -/
def toCoeffClass (M : ModelClass V d β B) : CoeffClass M.edge β B :=
  { coef := M.coef
    supported := M.supported
    low_order := M.low_order
    mass_le := M.mass_le }

end ModelClass

/-- A low-order schedule whose induced potential outcomes are uniformly
bounded by `B`. -/
-- @node: def:bounded-outcome-coefficient-class
structure BddOutcomeCoeffClass
    (G : V → V → Prop) (β : ℕ) (B : ℝ) where
  coef : V → Finset V → ℝ -- @realizes \mathcal C_{n,d,\beta}^{\infty}(B)(schedule carrier)
  supported : ∀ i S, ¬ S ⊆ nbhd G i → coef i S = 0
  low_order : LowOrder coef β
  outcome_bound : ∀ i z, |potentialOutcome G coef i z| ≤ B

/-- The graph-and-schedule class with uniformly bounded potential outcomes. -/
-- @node: def:bounded-outcome-model-class
structure BddOutcomeModelClass
    (V : Type*) [Fintype V] [DecidableEq V] (d β : ℕ) (B : ℝ) where
  edge : V → V → Prop -- @realizes \mathcal M_{n,d,\beta}^{\infty}(B)(graph component)
  decEdge : DecidableRel edge
  coef : V → Finset V → ℝ -- @realizes \mathcal M_{n,d,\beta}^{\infty}(B)(schedule component)
  supported : ∀ i S, ¬ S ⊆ nbhd edge i → coef i S = 0
  degree_le : BoundedDegree edge d
  low_order : LowOrder coef β
  outcome_bound : ∀ i z, |potentialOutcome edge coef i z| ≤ B

namespace BddOutcomeModelClass

/-- Assemble the flat bounded-outcome model from component classes. -/
def ofComponents (g : GraphClass V d) (c : BddOutcomeCoeffClass g.edge β B) :
    BddOutcomeModelClass V d β B :=
  { edge := g.edge
    decEdge := g.decEdge
    coef := c.coef
    supported := c.supported
    degree_le := g.degree_le
    low_order := c.low_order
    outcome_bound := c.outcome_bound }

/-- Project a bounded-outcome model to its graph component. -/
def toGraphClass (M : BddOutcomeModelClass V d β B) : GraphClass V d :=
  { edge := M.edge, decEdge := M.decEdge, degree_le := M.degree_le }

/-- Project a bounded-outcome model to its schedule component. -/
def toBddOutcomeCoeffClass (M : BddOutcomeModelClass V d β B) :
    BddOutcomeCoeffClass M.edge β B :=
  { coef := M.coef
    supported := M.supported
    low_order := M.low_order
    outcome_bound := M.outcome_bound }

end BddOutcomeModelClass

end CausalSmith.Experimentation.SnipeDegreeFrontier
