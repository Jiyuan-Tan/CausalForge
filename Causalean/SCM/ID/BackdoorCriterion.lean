/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Backdoor-style graph clauses and Rule-3 leg (shared plumbing)

The graph predicate here records the two ancestry and d-separation clauses that
the backdoor identification proof consumes, together with the
regime-independent do-calculus Rule-3 leg.  The identification *theorems*
themselves live in `Causalean/SCM/ID/Backdoor.lean`
(`backdoor_completeness_ae`, `backdoor_identifiable_ae`); this file holds only
the graph predicate and the shared Rule-3 marginal-invariance leg.

* `SWIGGraph.backdoorCriterion` — the standard adjustment-set predicate
  (definition).
* `backdoor_rule3_Z_marginal` — under criterion (i), the `Z`-marginal of the
  intervened observational kernel equals that of the base kernel (Rule 3 leg).

## Main definitions

* `SWIGGraph.backdoorCriterion G X hX_obs hX_fix Y Z` — the standard
  adjustment predicate: `Z` is observed, excludes the outcome and treatment
  random nodes, contains no descendant of a treatment random node, and
  d-separates `Y` from `X.image .random` in the splitMono graph
  `G.splitMono X hX_obs hX_fix`, which encodes the lower-bar mutilation
  `G_{X̲}` (outgoing edges of `random D` for `D ∈ X` rerouted to
  `fixed D`, making them graph roots with respect to the random copies).

## Design note

The lower-bar mutilation `G_{X̲}` deletes outgoing edges of `X.image .random`.
In the SWIG split (`SWIGGraph.splitMono`), exactly those outgoing edges are
rerouted to `fixed D` nodes, which are roots, so d-separation in the splitMono
graph gives the criterion needed by the SCM do-calculus rules without a
separate mutilated-graph construction.

## References

* Basic Concepts.tex, Theorem `thm:scm-backdoor` (lines 636–645).
* Pearl, J. (2009), *Causality*, Theorem 3.3.2.
-/

import Causalean.SCM.Do.DoCalculus
import Causalean.SCM.Model.InterventionAncestry
import Causalean.Graph.SWIGSplitMono
import Causalean.Graph.DSep.BackdoorBridges
import Causalean.SCM.ID.Adjustment
import Causalean.SCM.ID.Identifiable

/-!
# Backdoor criterion and Rule 3 marginal leg

This file defines the SWIG backdoor criterion used by SCM backdoor
identification and proves the Rule 3 marginal-invariance step for the adjustment
set.  The full backdoor completeness and identifiability theorems live in
`Causalean/SCM/ID/Backdoor.lean`; this module supplies their reusable graphical
criterion and the `Z`-marginal equality needed in the do-calculus assembly.
-/

namespace Causalean

variable {N : Type*} [DecidableEq N] [Fintype N]

namespace SWIGGraph

variable (G : SWIGGraph N)

/-- **Backdoor criterion** of `Z` relative to `(X, Y)` in the SWIG graph `G`.

    * **(0) Adjustment-set guards.** `Z` is observed, disjoint from `Y`, and
      disjoint from the treatment random nodes `X.image .random`.

    * **(i) Non-descendant condition.**  No node in `Z` is a descendant of any
      treatment random node `random D` (with `D ∈ X`) in `G`. Written as:
      `G.dag.isAncestor (random D) z` is false for all `D ∈ X`, `z ∈ Z`.

    * **(ii) splitMono d-separation.**  `Z ∪ X.image .fixed` d-separates
      `Y` from `X.image .random` in the splitMono graph
      `G.splitMono X hX_obs hX_fix`.  This encodes the lower-bar mutilation
      criterion `G_{X̲}`: splitting reroutes outgoing edges of `random D`
      (for `D ∈ X`) to root nodes `fixed D`.  The additional
      `X.image SWIGNode.fixed` conditioning is vacuous in the splitMono graph
      (fixed_X are roots with no incoming edges; no undirected path from
      `random_X` to `Y` traverses them — any such fork would force a DAG
      cycle) but is carried to match `do_rule2_kernel`'s contract directly.

    The preconditions `hX_obs` and `hX_fix` are needed to form `splitMono`. -/
def backdoorCriterion
    (X : Finset N)
    (hX_obs : ∀ D ∈ X, SWIGNode.random D ∈ G.observed)
    (hX_fix : ∀ D ∈ X, SWIGNode.fixed D ∉ G.fixed)
    (Y Z : Finset (SWIGNode N)) : Prop :=
  -- (0) Standard adjustment-set guards.
  Z ⊆ G.observed ∧
  Disjoint Z Y ∧
  Disjoint Z (X.image SWIGNode.random) ∧
  -- (i) Non-descendant condition: no z ∈ Z is a descendant of any random D with D ∈ X
  (∀ z ∈ Z, ∀ D ∈ X, ¬ G.dag.isAncestor (SWIGNode.random D) z) ∧
  -- (ii) d-separation in the splitMono graph (encodes G_{X̲})
  (G.splitMono X hX_obs hX_fix).dag.dSep Y (X.image SWIGNode.random)
    (Z ∪ X.image SWIGNode.fixed)

end SWIGGraph

namespace SCM

variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

open scoped MeasureTheory ProbabilityTheory

/-- **Backdoor Rule-3 leg.** Fix a causal model `M` and a treatment set `X` [whose random copy
    is observed and whose fixed copy is not already held fixed in `M`](hyp:hX_obs,hX_fixed),
    and a set `Z` [that is observed in `M`](hyp:hZ) such that [no node of `Z` is a descendant
    of any treatment random node](hyp:h_crit_i) — the non-descendant clause of the backdoor
    criterion. Then, at any post-intervention configuration `s_post`, [the `Z`-marginal of the
    post-intervention observational law at `s_post` equals the `Z`-marginal of the original
    observational law at the pre-intervention configuration underlying `s_post`](goal).

    Proof: direct application of `SCM.do_rule3` with `Y_param := ∅`,
    `W_param := Z`.  Criterion (i) composes with
    `SCM.fixSet_isAncestor_fixed_forward` (Phase 1A) to supply Rule 3's
    `hNoDesc` hypothesis on the post-intervention graph. -/
theorem backdoor_rule3_Z_marginal
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hX_obs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hX_fixed : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (Z : Finset (SWIGNode N)) (hZ : Z ⊆ M.observed)
    (h_crit_i : ∀ z ∈ Z, ∀ D ∈ X,
      ¬ M.toSWIGGraph.dag.isAncestor (SWIGNode.random D) z)
    (s_post : (M.fixSet X hX_obs hX_fixed).FixedValues) :
    ((M.fixSet X hX_obs hX_fixed).obsKernel s_post).map
        (valuesProjection
          ((SCM.fixSet_observed M X hX_obs hX_fixed).symm ▸ hZ))
      =
    (M.obsKernel (M.fixSetProj X hX_obs hX_fixed s_post)).map
        (valuesProjection hZ) := by
  -- Compose criterion (i) with A2-forward to get Rule 3's `hNoDesc`.
  have hNoDesc : ∀ v ∈ (∅ : Finset (SWIGNode N)) ∪ Z, ∀ d ∈ X,
      ¬ (M.fixSet X hX_obs hX_fixed).dag.isAncestor (SWIGNode.fixed d) v := by
    intro v hv d hd hanc
    -- A2-forward lifts `.fixed d`-ancestry in `fixSet X` to `.random d`-ancestry in `M`.
    have hanc_base :
        M.toSWIGGraph.dag.isAncestor (SWIGNode.random d) v :=
      SCM.fixSet_isAncestor_fixed_forward M X hX_obs hX_fixed hd hanc
    -- Unpack `v ∈ ∅ ∪ Z = Z` and contradict criterion (i).
    rw [Finset.empty_union] at hv
    exact h_crit_i v hv d hd hanc_base
  -- Apply `do_rule3` with `Y_param := ∅`, `W_param := Z`.  Rule 3's
  -- conclusion projects along `Finset.union_subset (∅.empty_subset _) hZ`
  -- (indexed by `∅ ∪ Z`); the goal projects along `hZ` (indexed by `Z`).
  have _h := SCM.do_rule3 M X hX_obs hX_fixed
      (∅ : Finset (SWIGNode N)) Z (Finset.empty_subset _) hZ hNoDesc s_post
  -- Bridge `ValuesOn (∅ ∪ Z) ↦ ValuesOn Z` via `valuesEquivOfEq`.
  -- Post-composing both sides of `_h` with `valuesEquivOfEq hU` and applying
  -- `Measure.map_map` produces `valuesProjection` into `Z` on both sides
  -- (the composition reduces definitionally).
  have hU : (∅ : Finset (SWIGNode N)) ∪ Z = Z := Finset.empty_union _
  have hmap := congrArg
    (fun μ : MeasureTheory.Measure (ValuesOn (∅ ∪ Z) (swigΩ Ω)) =>
      μ.map (valuesEquivOfEq (Ω := swigΩ Ω) hU)) _h
  rw [MeasureTheory.Measure.map_map
        (valuesEquivOfEq (Ω := swigΩ Ω) hU).measurable
        (measurable_valuesProjection _),
      MeasureTheory.Measure.map_map
        (valuesEquivOfEq (Ω := swigΩ Ω) hU).measurable
        (measurable_valuesProjection _)] at hmap
  exact hmap

end SCM

end Causalean
