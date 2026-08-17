/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Identifiability of Causal Effects

This file defines causal queries and identifiability, stated against the
SCM-primitive model (`Causalean.SCM`) and the derived observational kernel
`Causalean.SCM.obsKernel`.

## Main definitions

* `CausalQuery` — a functional of a causal model (Definition 9 from tex)
* `Identifiable` — a causal query is identifiable if same observational
  distribution implies same query value (Definition 10 from tex)
* `NonIdentifiable` — negation of identifiability
* `IdentifiableUnder` — identifiability given additional functional and
  structural assumptions

## Design notes

`IdentifiableUnder` takes two assumption predicates separately, matching the
separation in Basic Concepts.tex:
- `Af : SCM N Ω → Prop` — functional assumptions (edge type constraints)
- `As : SCM N Ω → Prop` — structural assumptions (distributional constraints:
  IV, DID, RDD, proxy, etc.)

Two SCMs are declared observationally equivalent when they share the same DAG
and their `obsKernel`s are equal as `ProbabilityTheory.Kernel`s.  Because the
kernel types depend on `M.fixed` / `M.observed` (through `FixedValues` and
`ObservedValues`), equality is expressed via `HEq` to tolerate the dependent
types; when the two models share the same DAG the value spaces coincide but
Lean will not always see this definitionally.

## References

* Basic Concepts.tex, Definitions 9-10 (Causal Effect, Identifiability)
-/

import Causalean.SCM.Model.SCM
import Causalean.SCM.Model.Kernel

/-! # Identifiability

This file defines the query-level interface used by SCM identification theorems.
`CausalQuery` is a functional of an SCM, `obsEquiv` compares observational
kernels with heterogeneous equality, `Identifiable` and `NonIdentifiable` express
whether a query is a functional of the observational law on a fixed SWIG graph,
and `IdentifiableUnder` adds functional and structural assumption predicates.
The helper theorems expose witness-based non-identifiability and monotonicity
under stronger assumptions. -/

namespace Causalean.SCM.ID

variable {N : Type*} [DecidableEq N] [Fintype N]

-- ============================================================
-- Causal Queries
-- ============================================================

/-- A causal query is a functional of a causal model, producing a value in
    some type α.

    From the tex: "A causal query is a functional Φ of the counterfactual
    distribution, e.g., Φ(C) = P(Y(x)) or Φ(C) = E[Y(x)] - E[Y(x')]."

    Examples:
    - ATE: Φ(C) = E[Y(1)] - E[Y(0)]
    - LATE: Φ(C) = E[Y(1) - Y(0) | complier]
    - Interventional distribution: Φ(C) = P(Y(x)) as a Measure

    The type parameter Ω assigns measurable value spaces to nodes; α is the
    result type. -/
abbrev CausalQuery (N : Type*) [DecidableEq N] [Fintype N]
    (Ω : N → Type*) [∀ n, MeasurableSpace (Ω n)] (α : Type*) :=
  Causalean.SCM N Ω → α

-- ============================================================
-- Observational equivalence
-- ============================================================

/-- Two SCMs are **observationally equivalent** if their derived observational
    kernels agree.  Because `obsKernel` has dependent domain/codomain
    (`FixedValues M` and `ObservedValues M`), we use `HEq` to accommodate two
    models whose `fixed`/`observed` sets may only be propositionally equal. -/
def obsEquiv {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]
    (M₁ M₂ : Causalean.SCM N Ω) : Prop :=
  HEq (Causalean.SCM.obsKernel M₁) (Causalean.SCM.obsKernel M₂)

-- ============================================================
-- Identifiability
-- ============================================================

/-- A causal query Φ is **identifiable** from the observational distribution
    if any two causal models sharing the same **SWIG graph** and observational
    kernel must agree on Φ.

    From the tex (`def:scm-identifiability`):
    "Let ℱ be a class of gSCMs **sharing a SWIG graph 𝒢** … A causal query Φ is
    identifiable if, for all 𝓜₁, 𝓜₂ ∈ ℱ, P_obs = P_obs ⟹ Φ(𝓜₁) = Φ(𝓜₂)."

    The model class is pinned by the full SWIG graph `G` (which fixes the
    observed / latent / fixed node partition and the edges), not merely the
    underlying DAG: the observed/latent/fixed split is part of the causal
    diagram and is not recoverable from `dag` alone.  Equivalently, Φ is
    identifiable if it is a functional of P_obs alone. -/
def Identifiable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)] {α : Type*}
    (G : SWIGGraph N) (Φ : CausalQuery N Ω α) : Prop :=
  ∀ M₁ M₂ : Causalean.SCM N Ω,
    M₁.toSWIGGraph = G → M₂.toSWIGGraph = G →
    obsEquiv M₁ M₂ →
    Φ M₁ = Φ M₂

/-- A causal query is **non-identifiable** if there exist two models with the
    same SWIG graph and observational kernel but different query values.

    A witness for non-identifiability consists of two models C₁, C₂ such that
    P_obs^{C₁} = P_obs^{C₂} but Φ(C₁) ≠ Φ(C₂). -/
def NonIdentifiable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)] {α : Type*}
    (G : SWIGGraph N) (Φ : CausalQuery N Ω α) : Prop :=
  ¬Identifiable G Φ

/-- Non-identifiability can be witnessed by a pair of models. -/
theorem nonIdentifiable_iff {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]
    {α : Type*} (G : SWIGGraph N) (Φ : CausalQuery N Ω α) :
    NonIdentifiable G Φ ↔
    ∃ M₁ M₂ : Causalean.SCM N Ω,
      M₁.toSWIGGraph = G ∧ M₂.toSWIGGraph = G ∧
      obsEquiv M₁ M₂ ∧
      Φ M₁ ≠ Φ M₂ := by
  simp only [NonIdentifiable, Identifiable, not_forall]
  constructor
  · intro ⟨M₁, M₂, h1, h2, h3, h4⟩
    exact ⟨M₁, M₂, h1, h2, h3, h4⟩
  · intro ⟨M₁, M₂, h1, h2, h3, h4⟩
    exact ⟨M₁, M₂, h1, h2, h3, h4⟩

-- ============================================================
-- Identifiability with additional assumptions
-- ============================================================

/-- Identifiability given both functional and structural assumptions.

    `Af` encodes *functional assumptions* on edge types (nonparametric,
    monotonic, linear).
    `As` encodes *structural assumptions* (IV, DID, RDD, proxy variable
    conditions).
    Both are plain `Prop`-valued predicates over causal models; the
    distinction is conceptual.  Concrete structural assumptions are supplied by
    the identification theorem or downstream module that needs them. -/
def IdentifiableUnder {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)] {α : Type*}
    (G : SWIGGraph N)
    (Af : Causalean.SCM N Ω → Prop) -- functional assumptions
    (As : Causalean.SCM N Ω → Prop) -- structural assumptions
    (Φ : CausalQuery N Ω α) : Prop :=
  ∀ M₁ M₂ : Causalean.SCM N Ω,
    M₁.toSWIGGraph = G → M₂.toSWIGGraph = G →
    Af M₁ → Af M₂ → As M₁ → As M₂ →
    obsEquiv M₁ M₂ →
    Φ M₁ = Φ M₂

/-- Identifiability without additional assumptions is the special case where
    both Af and As are trivially satisfied. -/
theorem identifiable_eq_identifiableUnder_true {Ω : N → Type*}
    [∀ n, MeasurableSpace (Ω n)]
    {α : Type*} (G : SWIGGraph N) (Φ : CausalQuery N Ω α) :
    Identifiable G Φ ↔ IdentifiableUnder G (fun _ => True) (fun _ => True) Φ := by
  simp [Identifiable, IdentifiableUnder]

/-- **Monotonicity of identifiability under assumptions.** Fix functional-assumption predicates
    `Af₁`, `Af₂` and structural-assumption predicates `As₁`, `As₂` on causal models sharing a graph
    `G`, together with a causal query `Φ`. If [every model satisfying `Af₂` also satisfies
    `Af₁`](hyp:hf), [every model satisfying `As₂` also satisfies `As₁`](hyp:hs), and [`Φ` is
    identifiable under the assumption pair `(Af₁, As₁)`](hyp:h_id), then [`Φ` is identifiable under
    `(Af₂, As₂)`](goal): passing to the more restrictive assumption predicates `Af₂`, `As₂` cannot
    destroy identifiability. -/
theorem identifiableUnder_mono {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]
    {α : Type*}
    (G : SWIGGraph N)
    (Af₁ Af₂ : Causalean.SCM N Ω → Prop)
    (As₁ As₂ : Causalean.SCM N Ω → Prop)
    (Φ : CausalQuery N Ω α)
    (hf : ∀ M, Af₂ M → Af₁ M)
    (hs : ∀ M, As₂ M → As₁ M)
    (h_id : IdentifiableUnder G Af₁ As₁ Φ) :
    IdentifiableUnder G Af₂ As₂ Φ :=
  fun M₁ M₂ hG₁ hG₂ hAf₁ hAf₂ hAs₁ hAs₂ hObs =>
    h_id M₁ M₂ hG₁ hG₂ (hf M₁ hAf₁) (hf M₂ hAf₂) (hs M₁ hAs₁) (hs M₂ hAs₂) hObs

end Causalean.SCM.ID
