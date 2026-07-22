/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Example: Real-Valued Backdoor Adjustment Skeleton

End-to-end typeclass and graph validation of the kernel-native backdoor pipeline
on an SCM whose observed value spaces are all `ℝ`. The concrete structural
functions below are deterministic constants, so the induced observed law is
degenerate; the example does not prove overlap or positivity and supplies those
analytic conditions as hypotheses in the identification theorem.

## The SCM

Three observed nodes indexed by `Fin 3`:

* `0 ↦ Z` — the confounder (continuous, ℝ-valued)
* `1 ↦ X` — the treatment (continuous, ℝ-valued)
* `2 ↦ Y` — the outcome  (continuous, ℝ-valued)

Edges: `Z → X`, `Z → Y`, `X → Y` — i.e. `Z` is a backdoor-admissible confounder.

The structural functions are deterministic (latent set is empty) and constant
`0`; the file uses this degenerate model to exercise the real-valued
measurability and graphical bookkeeping with minimal analytic overhead.

## What this validates

* The SCM construction (`continuousBackdoorSCM`) type-checks on `ℝ`-valued
  spaces.  The kernel-native backdoor pipeline does *not* require value-type
  countability or finiteness.
* `SWIGGraph.backdoorCriterion` discharges via `native_decide` on the
  underlying DAG (`cb_backdoor_criterion`), witnessing that the continuous SCM
  admits the backdoor adjustment set `{Z}`.
* `cb_backdoor_identified` applies the general a.e. backdoor pipeline on this
  concrete continuous-treatment graph once the overlap and positivity
  hypotheses are supplied.

## References

* `Causalean/SCM/Examples/BackDoor.lean` — discrete-treatment analogue.
* `Causalean/SCM/ID/Backdoor.lean` — `backdoor_completeness_ae` /
  `backdoor_identifiable_ae` (the general continuous backdoor results).
-/

import Causalean.Graph.DAG
import Causalean.Graph.SWIG
import Causalean.Graph.SWIGSplitMono
import Causalean.SCM.Model.SCM
import Causalean.SCM.Model.Kernel
import Causalean.SCM.ID.BackdoorCriterion
import Causalean.SCM.ID.Toolkit.Derivation

/-! # Real-Valued Backdoor Example

This file gives a real-valued backdoor example in which the confounder,
treatment, and outcome all take values in `ℝ`. The declarations `CBNode`,
`CBΩ`, `cbDAG`, `cbSWIGGraph`, and `continuousBackdoorSCM` build a degenerate
constant structural model whose purpose is to exercise the real-valued graph and
kernel interfaces. The theorem `cb_backdoor_criterion` verifies the graphical
backdoor criterion by computation, and `cb_backdoor_identified` applies the
kernel-based backdoor pipeline once the required overlap and positivity
conditions are supplied as hypotheses.
-/

set_option linter.style.nativeDecide false

namespace Causalean.SCM.Examples.ContinuousBackdoor

open Causalean
open scoped MeasureTheory ProbabilityTheory

-- ============================================================
-- § 1. Vertex set and value spaces
-- ============================================================

/-- The continuous-backdoor example has three nodes: confounder, treatment, and outcome. -/
abbrev CBNode : Type := Fin 3

/-- Every node in the continuous-backdoor example takes real values. -/
abbrev CBΩ : CBNode → Type := fun _ => ℝ

/-- This node index denotes the confounder in the continuous-backdoor example. -/
@[reducible] def Zidx : CBNode := 0
/-- This node index denotes the treatment in the continuous-backdoor example. -/
@[reducible] def Xidx : CBNode := 1
/-- This node index denotes the outcome in the continuous-backdoor example. -/
@[reducible] def Yidx : CBNode := 2

-- ============================================================
-- § 2. Underlying DAG on `CBNode`
-- ============================================================

/-- The edge indicator records confounder-to-treatment, confounder-to-outcome, and treatment-to-outcome arrows.

It is Boolean-valued so the graphical criterion can be discharged by computation. -/
def cbEdgeBool : CBNode → CBNode → Bool := fun a b =>
  (a.val == 0 && b.val == 1) || (a.val == 0 && b.val == 2) ||
  (a.val == 1 && b.val == 2)

/-- The edge relation says exactly that the confounder points to treatment and outcome, and treatment points to outcome. -/
def cbEdge : CBNode → CBNode → Prop := fun a b => cbEdgeBool a b = true

/-- Whether a proposed continuous-backdoor edge is present is decidable by evaluating the edge indicator. -/
instance : DecidableRel cbEdge := by
  intro a b; unfold cbEdge; infer_instance

/-- The continuous-backdoor graph orders confounder before treatment before outcome. -/
def cbTopo : CBNode → ℕ := fun n => n.val

/-- Every edge in the continuous-backdoor graph points from an earlier to a later node in the chosen topological order. -/
theorem cbTopo_lt : ∀ u v, cbEdge u v → cbTopo u < cbTopo v := by
  intro u v h
  fin_cases u <;> fin_cases v <;> simp_all [cbEdge, cbEdgeBool, cbTopo]

/-- This directed acyclic graph formalizes the three-node continuous backdoor example. -/
def cbDAG : DAG CBNode where
  edge := cbEdge
  decEdge := inferInstance
  acyclic := DAG.acyclic_of_topoOrder cbTopo_lt

-- ============================================================
-- § 3. The SWIGGraph (computable, used for `native_decide` proofs)
-- ============================================================

/-- This computable SWIG graph represents the continuous-backdoor example before any intervention.

It is defined separately from the full structural model so the graphical
backdoor criterion can be checked by computation. -/
def cbSWIGGraph : SWIGGraph CBNode where
  dag := initialSWIG cbDAG
  fixed := ∅
  observed := {SWIGNode.random Zidx, SWIGNode.random Xidx, SWIGNode.random Yidx}
  unobserved := ∅
  fixed_is_fixed := by intro s hs; simp at hs
  observed_is_random := by
    intro v hv; simp at hv
    rcases hv with rfl | rfl | rfl <;> exact ⟨_, rfl⟩
  unobserved_is_random := by intro u hu; simp at hu
  obs_unobs_disjoint := by
    rw [Finset.disjoint_right]; intro x hx; simp at hx
  dag_edges_classified := by native_decide
  fixed_image_in_observed := by intro s hs; simp at hs
  fixed_are_roots := by intro s hs; simp at hs
  unobs_are_roots := by intro u hu; simp at hu
  fixed_outside_fixed_isolated := by
    intro n _
    refine ⟨?_, ?_⟩
    · revert n; decide
    · revert n; decide
  all_children_in_observed := by native_decide

-- ============================================================
-- § 4. The SCM
-- ============================================================

/-- This real-valued backdoor structural model has observed nodes for a
confounder, treatment, and outcome, with no latent variables.

The structural functions are all constant `0`, so the induced observed law is
degenerate. The model is used as a minimal real-valued witness for the graph and
measurability interfaces, not as a non-degenerate continuous-treatment data
generating process. -/
noncomputable def continuousBackdoorSCM : Causalean.SCM CBNode CBΩ where
  toSWIGGraph := cbSWIGGraph
  edgeTypes := EdgeTypeAssignment.allNonparametric cbSWIGGraph.dag
  iota_valueSpace := by
    intro s
    exact (Finset.notMem_empty s.val s.property).elim
  structFun := fun v => by
    -- Structural functions: constant 0 for every observed node.  `swigΩ CBΩ v.val`
    -- reduces to `ℝ` for any `.random _` or `.fixed _` (since `CBΩ _ = ℝ`).
    rcases v with ⟨n, _⟩
    cases n <;> exact fun _ => (0 : ℝ)
  structFun_measurable := by
    intro v
    rcases v with ⟨n, _⟩
    cases n <;> exact measurable_const
  latentDist := fun u => (Finset.notMem_empty u.val u.property).elim
  isProbability_latent := by
    intro u
    exact (Finset.notMem_empty u.val u.property).elim

-- ============================================================
-- § 4. Trivial sanity checks
-- ============================================================

/-- The model is in the *standard* regime (no interventions). -/
example : continuousBackdoorSCM.isStandard := rfl

/-- `Z` is a parent of `X` in the base DAG. -/
example : Zidx ∈ cbDAG.parents Xidx := by native_decide

/-- `Z` is a parent of `Y` in the base DAG. -/
example : Zidx ∈ cbDAG.parents Yidx := by native_decide

/-- `X` is a parent of `Y` in the base DAG. -/
example : Xidx ∈ cbDAG.parents Yidx := by native_decide

-- ============================================================
-- § 5. Backdoor criterion for `do(X)` with adjustment set `{Z}`
-- ============================================================

/-- The treatment's observed random node belongs to the computable continuous-backdoor SWIG graph.

The witness is stated against the computable graph rather than the full structural
model, whose observed set is definitionally the same. -/
theorem cb_Xrand_obs :
    ∀ D ∈ ({Xidx} : Finset CBNode), SWIGNode.random D ∈ cbSWIGGraph.observed := by
  intro D hD
  rw [Finset.mem_singleton] at hD
  subst hD
  change SWIGNode.random Xidx ∈ ({SWIGNode.random Zidx, SWIGNode.random Xidx,
    SWIGNode.random Yidx} : Finset (SWIGNode CBNode))
  simp

/-- The treatment's fixed node is not already fixed in the computable continuous-backdoor SWIG graph. -/
theorem cb_Xfixed :
    ∀ D ∈ ({Xidx} : Finset CBNode), SWIGNode.fixed D ∉ cbSWIGGraph.fixed := by
  intro D _ hmem
  simp [cbSWIGGraph] at hmem

/-- The confounder satisfies the graphical backdoor criterion for the continuous treatment-outcome effect.

The statement is on the computable SWIG graph; the full structural model has the
same graph by definition. -/
theorem cb_backdoor_criterion :
    cbSWIGGraph.backdoorCriterion
      ({Xidx} : Finset CBNode) cb_Xrand_obs cb_Xfixed
      {SWIGNode.random Yidx} {SWIGNode.random Zidx} := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- Guard: `{random Z}` is observed.
    intro z hz
    rw [Finset.mem_singleton] at hz
    subst hz
    change SWIGNode.random Zidx ∈ ({SWIGNode.random Zidx, SWIGNode.random Xidx,
      SWIGNode.random Yidx} : Finset (SWIGNode CBNode))
    simp
  · -- Guard: `{random Z}` is disjoint from `{random Y}`.
    native_decide
  · -- Guard: `{random Z}` is disjoint from `{random X}`.
    native_decide
  · -- Condition (i): no element of `{random Z}` is a descendant of `random X`.
    intro z hz D hD
    rw [Finset.mem_singleton] at hz hD
    subst hz; subst hD
    -- Goal: ¬ (initialSWIG cbDAG).isAncestor (.random X) (.random Z).
    -- The only edges from `random X` go to `random Y`; `Z` is not reachable.
    native_decide
  · -- Condition (ii): `{random Z} ∪ {fixed X}` d-separates `{random Y}` from
    -- `{random X}` in the splitMono graph.  Discharged via `splitMonoDAG`
    -- (computable) + `native_decide`, mirroring `SCM/Examples/BackDoor.lean`.
    exact (by native_decide :
      (cbSWIGGraph.splitMonoDAG ({Xidx} : Finset CBNode) (by native_decide)).dSep
        {SWIGNode.random Yidx}
        (Finset.image SWIGNode.random ({Xidx} : Finset CBNode))
        ({SWIGNode.random Zidx} ∪ Finset.image SWIGNode.fixed ({Xidx} : Finset CBNode)))

-- ============================================================
-- § 5. Identification via the toolkit (sanity check)
-- ============================================================

/-- `{random Y}` is an observed node set. -/
theorem cb_Yobs : ({SWIGNode.random Yidx} : Finset (SWIGNode CBNode)) ⊆
    continuousBackdoorSCM.observed := by
  intro v hv; rw [Finset.mem_singleton] at hv; subst hv
  change SWIGNode.random Yidx ∈ ({SWIGNode.random Zidx, SWIGNode.random Xidx,
    SWIGNode.random Yidx} : Finset (SWIGNode CBNode)); simp

/-- `{random Z}` (the adjustment set) is an observed node set. -/
theorem cb_Zobs : ({SWIGNode.random Zidx} : Finset (SWIGNode CBNode)) ⊆
    continuousBackdoorSCM.observed := by
  intro v hv; rw [Finset.mem_singleton] at hv; subst hv
  change SWIGNode.random Zidx ∈ ({SWIGNode.random Zidx, SWIGNode.random Xidx,
    SWIGNode.random Yidx} : Finset (SWIGNode CBNode)); simp

/-- The treatment random-image is observed. -/
theorem cb_Xr_obs : (({Xidx} : Finset CBNode).image SWIGNode.random) ⊆
    continuousBackdoorSCM.observed := by
  rw [Finset.image_singleton]
  intro v hv; rw [Finset.mem_singleton] at hv; subst hv
  change SWIGNode.random Xidx ∈ ({SWIGNode.random Zidx, SWIGNode.random Xidx,
    SWIGNode.random Yidx} : Finset (SWIGNode CBNode)); simp

/-- Treatment random-image together with the adjustment set is observed. -/
theorem cb_XrZ_obs : (({Xidx} : Finset CBNode).image SWIGNode.random ∪
    {SWIGNode.random Zidx}) ⊆ continuousBackdoorSCM.observed :=
  Finset.union_subset cb_Xr_obs cb_Zobs

/-- The outcome is disjoint from the treatment random-image. -/
theorem cb_disj_YXr : Disjoint ({SWIGNode.random Yidx} : Finset (SWIGNode CBNode))
    (({Xidx} : Finset CBNode).image SWIGNode.random) := by
  rw [Finset.image_singleton]; decide

/-- The treatment random-image is disjoint from the adjustment set. -/
theorem cb_disj_XrZ : Disjoint (({Xidx} : Finset CBNode).image SWIGNode.random)
    ({SWIGNode.random Zidx} : Finset (SWIGNode CBNode)) := by
  rw [Finset.image_singleton]; decide

/-- Sanity check: identification on the concrete graph via the toolkit.

    On this real-valued, degenerate backdoor SCM, if the analytic overlap
    (`Rule2JointOverlap`) and product-level positivity conditions are assumed,
    the a.e. Rule-2 identity follows from a single application of
    `SCM.backdoor_rule2_ae` to the graphical criterion
    `cb_backdoor_criterion`. The theorem checks that the toolkit handles the
    graph, non-descendance, kernel disintegration, and typeclass bookkeeping for
    this concrete example; it does not prove the overlap or positivity
    hypotheses from the constant structural equations. -/
theorem cb_backdoor_identified
    (s0 : continuousBackdoorSCM.FixedValues)
    (hOverlap : ∀ s : (continuousBackdoorSCM.fixSet ({Xidx} : Finset CBNode)
        cb_Xrand_obs cb_Xfixed).FixedValues,
      Causalean.SCM.ID.Rule2JointOverlap continuousBackdoorSCM ({Xidx} : Finset CBNode)
        cb_Xrand_obs cb_Xfixed {SWIGNode.random Zidx} cb_XrZ_obs s)
    (hPositivity_ae :
      (((continuousBackdoorSCM.obsKernel s0).map (valuesProjection cb_Xr_obs) ⊗ₘ
          ProbabilityTheory.Kernel.const _
            ((continuousBackdoorSCM.obsKernel s0).map (valuesProjection cb_Zobs))).map
          (fun p => valuesUnionMk p.1 p.2))
        ≪ ((continuousBackdoorSCM.obsKernel s0).map (valuesProjection cb_XrZ_obs))) :
    ∀ᵐ p ∂((continuousBackdoorSCM.obsKernel s0).map (valuesProjection cb_Xr_obs) ⊗ₘ
            ProbabilityTheory.Kernel.const _
              ((continuousBackdoorSCM.obsKernel s0).map (valuesProjection cb_Zobs))),
      (continuousBackdoorSCM.fixSet ({Xidx} : Finset CBNode) cb_Xrand_obs cb_Xfixed).obsCondKernel
          {SWIGNode.random Yidx} {SWIGNode.random Zidx}
          ((SCM.fixSet_observed continuousBackdoorSCM ({Xidx} : Finset CBNode)
            cb_Xrand_obs cb_Xfixed).symm ▸ cb_Yobs)
          ((SCM.fixSet_observed continuousBackdoorSCM ({Xidx} : Finset CBNode)
            cb_Xrand_obs cb_Xfixed).symm ▸ cb_Zobs)
          (continuousBackdoorSCM.fixSetExtend ({Xidx} : Finset CBNode)
            cb_Xrand_obs cb_Xfixed s0 p.1, p.2)
      = continuousBackdoorSCM.obsCondKernel {SWIGNode.random Yidx}
          (({Xidx} : Finset CBNode).image SWIGNode.random ∪ {SWIGNode.random Zidx})
          cb_Yobs cb_XrZ_obs (s0, valuesUnionMk p.1 p.2) :=
  SCM.backdoor_rule2_ae continuousBackdoorSCM ({Xidx} : Finset CBNode)
    cb_Xrand_obs cb_Xfixed {SWIGNode.random Yidx} {SWIGNode.random Zidx}
    cb_Yobs cb_Zobs cb_Xr_obs cb_XrZ_obs cb_disj_YXr cb_disj_XrZ
    cb_backdoor_criterion s0 hOverlap hPositivity_ae

end Causalean.SCM.Examples.ContinuousBackdoor
