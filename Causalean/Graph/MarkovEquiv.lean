/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Graph.MarkovEquiv.Defs
import Causalean.Graph.MarkovEquiv.Readoff
import Causalean.Graph.MarkovEquiv.Transfer
import Causalean.Graph.MarkovEquiv.Distributional
import Causalean.Graph.MarkovEquiv.Moralization

/-!
# Markov equivalence of DAGs (Verma–Pearl) — umbrella

Entry point for the formalization of the **Verma–Pearl characterization of Markov
equivalence** (Verma & Pearl, *Equivalence and synthesis of causal models*, 1990): two
directed acyclic graphs declare the same conditional-independence constraints exactly when
they have the same skeleton and the same v-structures. Import this file for the whole
development; the headline result is stated here so it is not buried among the supporting
files.

## Main results

* `MarkovEquiv` (`Defs.lean`) — two DAGs declare the same d-separations.
* `markovEquiv_iff_sameSkeleton_sameImmoralities` (this file) — **the flagship.** Two DAGs
  are Markov equivalent iff they have the same skeleton (`SameSkeleton`, undirected
  adjacency) and the same v-structures (`SameImmoralities`, colliders with non-adjacent
  parents). The constraint-based characterization underlying PC/FCI/GES and the CPDAG.
* `distMarkovEquiv_of_markovEquiv` (`Distributional.lean`) — graph-level Markov equivalence
  implies *distributional* Markov equivalence (same distributions have the two DAGs as
  I-maps), via the global Markov bridge `isGlobalIMap_dag_self`.
* `DAG.dSep_iff_moralSep` (`Moralization.lean`) — the Lauritzen moralization
  criterion: d-separation in a DAG is equivalent to graph separation in the
  moral graph of the ancestral closure.

## Supporting machinery

`Readoff.lean` (easy direction — skeleton and v-structures are read off the d-separation
relation), `Transfer.lean` (hard direction — same skeleton + v-structures transfer every
d-separation), `Distributional.lean` (the I-map / faithfulness layer connecting the
graph notion to distributions), and `Moralization.lean` (the ancestral moral graph
criterion for d-separation). The development reuses the existing d-separation engine
(`Causalean.Graph.DSep`) and the global Markov property (`Causalean.SCM.Do.GlobalMarkov`).
-/

namespace Causalean

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- **Verma–Pearl (1990).** Two DAGs on the same vertex set are Markov equivalent — they
declare exactly the same d-separations, hence impose the same conditional-independence
constraints — if and only if they have the same skeleton and the same v-structures
(immoralities).

The easy direction reads the skeleton and v-structures from d-separation. The hard
direction is supplied by the covered-edge reversal route: same-skeleton/same-immorality
DAGs are connected by covered edge reversals, each preserving every d-separation. -/
theorem markovEquiv_iff_sameSkeleton_sameImmoralities (G₁ G₂ : DAG V) :
    MarkovEquiv G₁ G₂ ↔ SameSkeleton G₁ G₂ ∧ SameImmoralities G₁ G₂ :=
  ⟨sameSkeleton_sameImmoralities_of_markovEquiv,
    fun ⟨hskel, himm⟩ => markovEquiv_of_sameSkeleton_sameImmoralities hskel himm⟩

end Causalean
