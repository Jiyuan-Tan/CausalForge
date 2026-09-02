/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Tactic.Attr
import Causalean.PO.Core.System

/-! # Cross-World Counterfactual Distributions

This file constructs finite joint distributions of potential outcomes evaluated
under possibly different intervention regimes.  It supplies the cross-world
evaluation map, its pushforward law, and the basic marginal reading of that law. -/

namespace Causalean
namespace PO

open MeasureTheory

namespace POSystem

variable (P : POSystem)

/-- For a potential-outcome system, a finite list of queries, and a unit in the
sample space, this function returns the tuple whose $i$th component is the
potential outcome, for the finite variable set in the $i$th query, under the
intervention regime in the $i$th query.

Cross-world evaluation: a tuple of `Y_i(r_i)(ω)` for a finite list of queries.
def:po-counterfactual. -/
def crossWorldEval
    (qs : List (Regime P.V P.X × Finset P.V)) :
    P.Ω → (i : Fin qs.length) → ValuesOn (qs[i].2) P.X :=
  fun ω i => P.poVariable (qs[i].1) (qs[i].2) ω

/-- Reading off the `i`-th coordinate of the cross-world evaluation of a unit
returns the joint potential outcome of the `i`-th query's variable set under the
`i`-th query's regime, at that same unit.

This is the simp-shaped form of the definition of cross-world evaluation:
rewriting with it replaces the tuple-valued map by the single-query potential
outcome, after which the potential-outcome API applies. -/
@[causal_defs_simps]
lemma crossWorldEval_apply (qs : List (Regime P.V P.X × Finset P.V))
    (ω : P.Ω) (i : Fin qs.length) :
    P.crossWorldEval qs ω i = P.poVariable (qs[i].1) (qs[i].2) ω :=
  rfl

/-- The cross-world evaluation map for a finite list of counterfactual queries is measurable. -/
@[fun_prop]
lemma measurable_crossWorldEval
    (qs : List (Regime P.V P.X × Finset P.V)) :
    Measurable (P.crossWorldEval qs) := by
  refine measurable_pi_lambda _ ?_
  intro i
  exact P.measurable_poVariable _ _

/-- For a potential-outcome system and a finite list of counterfactual queries,
the counterfactual distribution is the probability measure obtained by pushing
the system's probability measure on the sample space through the cross-world
evaluation map for those queries.

Counterfactual distribution -- def:po-counterfactual. -/
noncomputable def counterfactualDist
    (qs : List (Regime P.V P.X × Finset P.V)) :
    Measure ((i : Fin qs.length) → ValuesOn (qs[i].2) P.X) :=
  P.μ.map (P.crossWorldEval qs)

/-- The joint counterfactual law of a finite list of queries is the pushforward
of the system's probability measure along the cross-world evaluation map for
those queries.

This is the simp-shaped form of the definition of the counterfactual
distribution: rewriting with it replaces the project constant by an explicit
pushforward measure, after which the pushforward API applies. -/
@[causal_defs_simps]
lemma counterfactualDist_eq (qs : List (Regime P.V P.X × Finset P.V)) :
    P.counterfactualDist qs = P.μ.map (P.crossWorldEval qs) :=
  rfl

/-- The finite cross-world counterfactual distribution is a probability measure. -/
instance (qs : List (Regime P.V P.X × Finset P.V)) :
    IsProbabilityMeasure (P.counterfactualDist qs) := by
  simp only [causal_defs_simps]
  exact MeasureTheory.Measure.isProbabilityMeasure_map
    (P.measurable_crossWorldEval qs).aemeasurable

/-- For [a finite list of counterfactual queries `qs`](hyp:qs) and [an index `i`
into that list](hyp:i), [the `i`-th coordinate marginal of the joint counterfactual
distribution over all queries equals the potential-outcome law for query `i`
alone](goal).

Matches rem:po-reading. -/
theorem counterfactualDist_marginal
    (qs : List (Regime P.V P.X × Finset P.V)) (i : Fin qs.length) :
    (P.counterfactualDist qs).map (fun f => f i) =
      P.poOperator (qs[i].1) (qs[i].2) := by
  simp only [causal_defs_simps]
  rw [MeasureTheory.Measure.map_map
        (measurable_pi_apply i) (P.measurable_crossWorldEval qs)]
  rfl

end POSystem

end PO
end Causalean
