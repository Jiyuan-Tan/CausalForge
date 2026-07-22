/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Graph.MarkovEquiv.Defs
import Causalean.SCM.Do.GlobalMarkov

/-! # Markov equivalence — the distributional I-map layer

The graph-level `MarkovEquiv` (same d-separations) is connected here to *distributions*.
A distribution `μ` is a **global I-map** of a DAG `G` when every d-separation of `G` is a
conditional independence of `μ`; it is **faithful** to `G` when, conversely, every such
conditional independence reflects an actual d-separation. The global Markov property
(`full_globalMarkov`) says every structural causal model is a global I-map of its own DAG —
this is the bridge from graphs to distributions, restated here as `isGlobalIMap_dag_self`.

The theorem in this file proves the easy direction:

* `distMarkovEquiv_of_markovEquiv`: graph-level Markov equivalence implies
  distributional Markov equivalence (the two DAGs are I-maps of exactly the same
  distributions). This is immediate from the definitions: the I-map condition is the same
  predicate when the d-separations agree.

The d-separation triples handled here are pairwise disjoint, matching the global Markov
property; this is the standard setting for the I-map and faithfulness notions. The file
states the I-map direction needed by the public Markov-equivalence API and leaves
faithfulness-existence results outside this layer.
-/

namespace Causalean

open scoped MeasureTheory

namespace SCM

universe uN uΩ

variable {N : Type uN} [DecidableEq N] [Fintype N]
variable {Ω : N → Type uΩ} [∀ n, MeasurableSpace (Ω n)]

/-- A measure `μ` on the random values of `M` is a **global I-map** of a DAG `G` (on the
same node set) when every d-separation in `G` is a conditional independence under `μ`:
for pairwise-disjoint `X, Y, Z`, if `G` d-separates `X` and `Y` given `Z` then `X ⟂ Y | Z`
under `μ`. -/
def IsGlobalIMap (G : DAG (SWIGNode N)) (M : Causalean.SCM N Ω)
    [StandardBorelSpace M.RandomValues]
    (μ : MeasureTheory.Measure M.RandomValues) [MeasureTheory.IsFiniteMeasure μ] : Prop :=
  ∀ (X Y Z : Finset (SWIGNode N)) (hX : X ⊆ M.randomVars) (hY : Y ⊆ M.randomVars)
    (hZ : Z ⊆ M.randomVars),
    Disjoint X Y → Disjoint X Z → Disjoint Y Z → G.dSep X Y Z →
    FullCondIndep M X Y Z hX hY hZ μ

/-- A measure `μ` is **faithful** to a DAG `G` when every conditional independence of `μ`
reflects a genuine d-separation of `G` (the converse of being an I-map): for
pairwise-disjoint `X, Y, Z`, `X ⟂ Y | Z` under `μ` forces `G` to d-separate `X` and `Y`
given `Z`. A measure that is both an I-map of and faithful to `G` has conditional
independences exactly matching `G`'s d-separations. -/
def IsFaithful (G : DAG (SWIGNode N)) (M : Causalean.SCM N Ω)
    [StandardBorelSpace M.RandomValues]
    (μ : MeasureTheory.Measure M.RandomValues) [MeasureTheory.IsFiniteMeasure μ] : Prop :=
  ∀ (X Y Z : Finset (SWIGNode N)) (hX : X ⊆ M.randomVars) (hY : Y ⊆ M.randomVars)
    (hZ : Z ⊆ M.randomVars),
    Disjoint X Y → Disjoint X Z → Disjoint Y Z →
    FullCondIndep M X Y Z hX hY hZ μ → G.dSep X Y Z

/-- Two DAGs are **distributionally Markov equivalent** (over value spaces `Ω`) when they
are global I-maps of exactly the same distributions over every structural causal model on
the same node set. The value-space family `Ω` is an explicit parameter since it is not
determined by the graphs. -/
def DistMarkovEquiv (Ω : N → Type uΩ) [∀ n, MeasurableSpace (Ω n)]
    (G₁ G₂ : DAG (SWIGNode N)) : Prop :=
  ∀ (M : Causalean.SCM N Ω) [StandardBorelSpace M.RandomValues]
    (μ : MeasureTheory.Measure M.RandomValues) [MeasureTheory.IsFiniteMeasure μ],
    IsGlobalIMap G₁ M μ ↔ IsGlobalIMap G₂ M μ

/-- **The bridge, restated.** Every structural causal model is a global I-map of its own
DAG: this is exactly the global Markov property `full_globalMarkov`. -/
theorem isGlobalIMap_dag_self (M : Causalean.SCM N Ω)
    [StandardBorelSpace M.RandomValues]
    [∀ n, StandardBorelSpace (swigΩ Ω n)] [∀ n, Nonempty (swigΩ Ω n)]
    [∀ s : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.jointKernel s)]
    (s : M.FixedValues) :
    IsGlobalIMap M.dag M (M.jointKernel s) := by
  intro X Y Z hX hY hZ hXY hXZ hYZ hdsep
  exact full_globalMarkov M X Y Z hX hY hZ hXY hXZ hYZ hdsep s

/-- **Easy half.** Graph-level Markov equivalence implies distributional Markov equivalence:
when two DAGs declare the same d-separations they are I-maps of the same distributions. -/
theorem distMarkovEquiv_of_markovEquiv {G₁ G₂ : DAG (SWIGNode N)}
    (h : MarkovEquiv G₁ G₂) : DistMarkovEquiv Ω G₁ G₂ := by
  intro M _ μ _
  constructor
  · intro himap X Y Z hX hY hZ hXY hXZ hYZ hdsep
    exact himap X Y Z hX hY hZ hXY hXZ hYZ ((h X Y Z hXY hXZ hYZ).mpr hdsep)
  · intro himap X Y Z hX hY hZ hXY hXZ hYZ hdsep
    exact himap X Y Z hX hY hZ hXY hXZ hYZ ((h X Y Z hXY hXZ hYZ).mp hdsep)

end SCM

end Causalean
