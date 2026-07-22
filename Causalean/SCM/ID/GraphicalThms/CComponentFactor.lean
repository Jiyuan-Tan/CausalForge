/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# C-Component Chain-Rule Factorization (Tian, 2002)

Formalizes `thm:scm-c-factor` (Basic Concepts.tex:662–672) against the
SCM-primitive observational kernel.  This file keeps Tian's c-component
factor definitions and records the continuous-safe per-node chain-rule form
currently used as the foundational factorization:

    P(v) = ∏_{i} P(V_i | V_0, ..., V_{i-1})

where the observed nodes are ordered topologically and Tian's
`Pa⁺(V_i)` is the full observed history before `V_i`.

The component-specific factors remain available as conditional kernels:

    Q_j (C_j | ·) = ∏_{V ∈ C_j} P(V | Pa⁺_G(V)).

Here `Pa⁺_G(V)` denotes the *observed predecessors* of `V` in a fixed
topological order — Tian's "history up to V" convention.

## Main definitions

* `SWIGGraph.qFactorParents C` — `(⋃ v ∈ C, Pa⁺_G(v)) \ C`: the
  conditioning set used by the current kernel-level proxy for `Q[C]`.
* `SCM.qFactor M C s` — the current conditional-kernel representation,
  `P(C | qFactorParents C)` at fixed slice `s`.  The Tian c-factor product
  interpretation requires a separate bridge; it is not definitional from this
  declaration alone.

## Main statement

* `c_component_factorization` — `obsKernel M s = M.qFactorProduct s`,
  the per-node chain-rule product over observed variables.  Grouping this
  product into c-components is the next theorem layer.

## References

* Basic Concepts.tex, Theorem `thm:scm-c-factor` (lines 662–672).
* Tian, J. (2002), "Studies in causal reasoning and learning."
-/

import Causalean.SCM.Factored.ObsChainKernel
import Causalean.SCM.Model.Induced
import Causalean.Graph.CComponents
import Causalean.SCM.ID.GraphicalThms.InducedSubgraph

/-!
# C-Component Factorization

This file develops Tian's c-component factor setup for structural causal models
and connects it to the per-node observational chain-rule product.

The public API names the conditioning set for a component factor,
`SWIGGraph.qFactorParents C = (⋃ v ∈ C, Pa⁺_G(v)) \ C`, proves that these
conditioning coordinates are observed, and defines `SCM.qFactor M C s` as the
conditional-kernel proxy for `Q[C]` at a fixed slice.  The theorem
`c_component_factorization` records the continuous-safe foundation: the
observational kernel is the chain-rule product of one-node conditional kernels
along the topological order of observed nodes.

Grouping that chain-rule product into Tian c-component factors is theorem
content supplied by downstream density and q-factor identity files; it is not a
definitional property of `qFactor`.
-/

namespace Causalean

variable {N : Type*} [DecidableEq N] [Fintype N]

namespace SWIGGraph

variable (G : SWIGGraph N)

/-- The conditioning set of the c-component factor `Q[C]`:

    `Pa⁺_G(C) \ C  :=  (⋃_{v ∈ C} Pa⁺_G(v)) \ C`.

    Members are the observed predecessors of any node in `C` that are
    not themselves in `C`. -/
noncomputable def qFactorParents (C : Finset (SWIGNode N)) : Finset (SWIGNode N) :=
  (C.biUnion G.observedPredecessors) \ C

/-- `qFactorParents C` consists of observed nodes outside `C`. -/
lemma qFactorParents_subset_observed (C : Finset (SWIGNode N)) :
    G.qFactorParents C ⊆ G.observed := by
  intro w hw
  rcases Finset.mem_sdiff.mp hw with ⟨hw_union, _⟩
  rcases Finset.mem_biUnion.mp hw_union with ⟨v, _, hw_pred⟩
  exact G.observedPredecessors_subset_observed v hw_pred

end SWIGGraph

namespace SCM

variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

open scoped MeasureTheory ProbabilityTheory

/-- **Conditional-kernel proxy for a Tian c-component factor.**

    For a node set `C` and a fixed slice `s`, this is the conditional law of
    `C` given `Pa⁺(C) \ C` under `M.obsKernel s`.

    The standard Tian c-factor `Q[C]` is the product over the prefix factors
    belonging to `C`, and Eq. 13 identifies that product with a do-complement
    law for a full c-component.  Those identifications are theorem content, not
    consequences of this definition by unfolding. -/
noncomputable def qFactor
    (M : Causalean.SCM N Ω) (C : Finset (SWIGNode N))
    (hC : C ⊆ M.observed)
    [StandardBorelSpace (ValuesOn C (swigΩ Ω))]
    [Nonempty (ValuesOn C (swigΩ Ω))]
    (s : M.FixedValues)
    [∀ s' : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.obsKernel s')]
    [MeasurableSpace.CountableOrCountablyGenerated
      M.FixedValues
      (ValuesOn (M.toSWIGGraph.qFactorParents C) (swigΩ Ω))] :
    ProbabilityTheory.Kernel
      (ValuesOn (M.toSWIGGraph.qFactorParents C) (swigΩ Ω))
      (ValuesOn C (swigΩ Ω)) :=
  (M.obsCondKernel C (M.toSWIGGraph.qFactorParents C) hC
    (M.toSWIGGraph.qFactorParents_subset_observed C)).comap
      (fun c => (s, c))
      (Measurable.prodMk measurable_const measurable_id)

/-- **Theorem (Tian 2002, per-node chain-rule factorization).**

    The observational kernel of a gSCM is the full chain-rule product of
    one-node conditional kernels along the topological order of observed nodes.
    Tian's `Pa⁺(V)` is interpreted as the full observed history before `V`,
    so this statement is the ordinary iterated-disintegration factorization and
    does not use graphical Markov or do-calculus reasoning.

    The subsequent c-component grouping theorem should collect these per-node
    factors according to the c-components of `M.toSWIGGraph`. -/
theorem c_component_factorization
    (M : Causalean.SCM N Ω) (s : M.FixedValues)
    [∀ s' : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.obsKernel s')]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      StandardBorelSpace
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      Nonempty
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ k : ℕ,
      MeasurableSpace.CountableOrCountablyGenerated
        (M.FixedValues) (ValuesOn (M.prefixNodes k) (swigΩ Ω))] :
    M.obsKernel s = M.qFactorProduct s :=
  M.obsKernel_eq_qFactorProduct s

end SCM

end Causalean
