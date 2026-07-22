/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.SCM.Model.SCM

/-! # Structural Monotonicity Assumptions

This file defines monotonicity as a restriction on a structural equation itself.
The predicate fixes an observed child and one of its parents, then requires the
child's structural function to be nondecreasing in that parent coordinate while
all other parent coordinates are held fixed.

The file also contains a two-node Boolean SCM used as a sanity check: one model
satisfies the structural restriction and one model violates it. These witnesses
show that the predicate is a genuine constraint on `structFun`, not a vacuous
edge label.
-/

namespace Causalean.SCM.Assumptions

open Causalean

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

/-- The SWIG value spaces inherit the base-variable order.

The random and fixed copies of a node use the same value space, so an order on
each base-variable space also orders each SWIG coordinate. -/
instance instPreorderSwigΩ [∀ n, Preorder (Ω n)] :
    ∀ s : SWIGNode N, Preorder (swigΩ Ω s)
  | .random _ => inferInstance
  | .fixed _ => inferInstance

/-- Raising one parent coordinate cannot decrease the child equation.

`MonotoneMechanism child parent M` says that `child` is an observed node of the
model, `parent` is a parent of that child in the model's DAG, and the structural
equation for `child` is nondecreasing in the `parent` input when all other
parent inputs are held fixed. This is a restriction on the structural function,
not on the graph's edge-type labels. -/
def MonotoneMechanism [∀ n, Preorder (Ω n)]
    (child parent : SWIGNode N) (M : Causalean.SCM N Ω) : Prop :=
  ∃ hchild : child ∈ M.observed,
    ∃ hparent : parent ∈ M.dag.parents child,
      ∀ x y : ∀ w : {w // w ∈ M.dag.parents child}, swigΩ Ω w.val,
        x ⟨parent, hparent⟩ ≤ y ⟨parent, hparent⟩ →
        (∀ w, w.val ≠ parent → x w = y w) →
        M.structFun ⟨child, hchild⟩ x ≤ M.structFun ⟨child, hchild⟩ y

/-! ## Concrete Boolean witnesses -/

/-- Two variables for the Boolean monotonicity sanity check. -/
inductive BoolChainNode
  | d
  | y
  deriving DecidableEq, Repr, Fintype

namespace BoolChainNode

/-- The Boolean witness has one directed edge, from treatment `d` to outcome `y`. -/
def edge : BoolChainNode → BoolChainNode → Prop
  | d, y => True
  | _, _ => False

instance edgeDecidable : DecidableRel edge := by
  intro a b
  cases a <;> cases b <;> simp [edge] <;> infer_instance

/-- The topological order places the parent before the child. -/
def topo : BoolChainNode → ℕ
  | d => 0
  | y => 1

private theorem topo_injective : Function.Injective topo := by
  intro a b h
  cases a <;> cases b <;> simp [topo] at h ⊢

private theorem topo_lt : ∀ a b, edge a b → topo a < topo b := by
  intro a b h
  cases a <;> cases b <;> simp [edge, topo] at h ⊢

/-- The two-node DAG used by the Boolean monotonicity witnesses. -/
def dag : DAG BoolChainNode where
  edge := edge
  decEdge := edgeDecidable
  acyclic := DAG.acyclic_of_topoOrder topo_lt

end BoolChainNode

open BoolChainNode

/-- The standard SWIG graph for the two-node Boolean witness. -/
def boolChainSWIG : SWIGGraph BoolChainNode where
  dag := initialSWIG BoolChainNode.dag
  fixed := ∅
  observed := {SWIGNode.random d, SWIGNode.random y}
  unobserved := ∅
  fixed_is_fixed := by intro s hs; simp at hs
  observed_is_random := by
    intro v hv
    simp at hv
    rcases hv with rfl | rfl <;> exact ⟨_, rfl⟩
  unobserved_is_random := by intro u hu; simp at hu
  obs_unobs_disjoint := by
    rw [Finset.disjoint_right]
    intro x hx
    simp at hx
  dag_edges_classified := by decide
  fixed_image_in_observed := by intro s hs; simp at hs
  fixed_are_roots := by intro s hs; simp at hs
  unobs_are_roots := by intro u hu; simp at hu
  fixed_outside_fixed_isolated := by
    intro n _
    cases n <;> exact ⟨by decide, by decide⟩
  all_children_in_observed := by decide

/-- Every variable in the Boolean witness has Boolean values. -/
def boolChainΩ : BoolChainNode → Type := fun _ => Bool

instance boolChainMeasurableSpace : ∀ n, MeasurableSpace (boolChainΩ n)
  | d => ⊤
  | y => ⊤

instance boolChainPreorder : ∀ n, Preorder (boolChainΩ n)
  | d => inferInstanceAs (Preorder Bool)
  | y => inferInstanceAs (Preorder Bool)

/-- The designated parent coordinate for the Boolean witness outcome. -/
def boolChainDParent :
    {w // w ∈ boolChainSWIG.dag.parents (SWIGNode.random y)} :=
  ⟨SWIGNode.random d, by decide⟩

/-- The Boolean copying structural equation for the witness SCM.

The treatment node is fixed at `false`; the outcome node copies the treatment
parent coordinate. -/
def copyStructFun (v : {v // v ∈ boolChainSWIG.observed}) :
    (∀ w : {w // w ∈ boolChainSWIG.dag.parents v.val}, swigΩ boolChainΩ w.val) →
      swigΩ boolChainΩ v.val := by
  rcases v with ⟨n, hn⟩
  cases n with
  | random n =>
      cases n with
      | d => exact fun _ => false
      | y => exact fun parents => parents boolChainDParent
  | fixed n =>
      cases n <;> simp [boolChainSWIG] at hn

/-- The Boolean reversing structural equation for the witness SCM.

The treatment node is fixed at `false`; the outcome node reverses the treatment
parent coordinate. -/
def flipStructFun (v : {v // v ∈ boolChainSWIG.observed}) :
    (∀ w : {w // w ∈ boolChainSWIG.dag.parents v.val}, swigΩ boolChainΩ w.val) →
      swigΩ boolChainΩ v.val := by
  rcases v with ⟨n, hn⟩
  cases n with
  | random n =>
      cases n with
      | d => exact fun _ => false
      | y => exact fun parents => !parents boolChainDParent
  | fixed n =>
      cases n <;> simp [boolChainSWIG] at hn

private theorem copyStructFun_measurable (v : {v // v ∈ boolChainSWIG.observed}) :
    Measurable (copyStructFun v) := by
  rcases v with ⟨n, hn⟩
  cases n with
  | random n =>
      cases n with
      | d => exact measurable_const
      | y => exact measurable_pi_apply boolChainDParent
  | fixed n =>
      cases n <;> simp [boolChainSWIG] at hn

private theorem flipStructFun_measurable (v : {v // v ∈ boolChainSWIG.observed}) :
    Measurable (flipStructFun v) := by
  rcases v with ⟨n, hn⟩
  cases n with
  | random n =>
      cases n with
      | d => exact measurable_const
      | y =>
          exact (measurable_of_finite (fun b : Bool => !b)).comp
            (measurable_pi_apply boolChainDParent)
  | fixed n =>
      cases n <;> simp [boolChainSWIG] at hn

/-- A Boolean SCM whose outcome equation copies the parent value.

This concrete model witnesses that the structural monotonicity predicate is
satisfiable. -/
noncomputable def monotoneBoolSCM : Causalean.SCM BoolChainNode boolChainΩ where
  toSWIGGraph := boolChainSWIG
  edgeTypes := EdgeTypeAssignment.allNonparametric boolChainSWIG.dag
  iota_valueSpace := by
    intro s
    exact (Finset.notMem_empty s.val s.property).elim
  structFun := copyStructFun
  structFun_measurable := copyStructFun_measurable
  latentDist := fun u => (Finset.notMem_empty u.val u.property).elim
  isProbability_latent := by
    intro u
    exact (Finset.notMem_empty u.val u.property).elim

/-- A Boolean SCM whose outcome equation reverses the parent value.

This concrete model witnesses that the structural monotonicity predicate is a
nontrivial restriction: an otherwise well-formed SCM can violate it. -/
noncomputable def antitoneBoolSCM : Causalean.SCM BoolChainNode boolChainΩ where
  toSWIGGraph := boolChainSWIG
  edgeTypes := EdgeTypeAssignment.allNonparametric boolChainSWIG.dag
  iota_valueSpace := by
    intro s
    exact (Finset.notMem_empty s.val s.property).elim
  structFun := flipStructFun
  structFun_measurable := flipStructFun_measurable
  latentDist := fun u => (Finset.notMem_empty u.val u.property).elim
  isProbability_latent := by
    intro u
    exact (Finset.notMem_empty u.val u.property).elim

/-- The Boolean parent assignment that sets the designated parent to `b`.

All non-designated parent coordinates, if any, are fixed at `false`. In the
two-node witness graph there are no such coordinates. -/
def boolParentAssignment (b : Bool) :
    ∀ w : {w // w ∈ boolChainSWIG.dag.parents (SWIGNode.random y)},
      swigΩ boolChainΩ w.val := by
  intro w
  rcases w with ⟨n, _⟩
  cases n with
  | random n =>
      cases n with
      | d => exact b
      | y => exact false
  | fixed n =>
      cases n <;> exact false

/-- Evaluating the Boolean parent assignment at the designated parent returns
the assigned value. -/
@[simp] theorem boolParentAssignment_boolChainDParent (b : Bool) :
    boolParentAssignment b boolChainDParent = b := by
  cases b <;> rfl

/-- The copying Boolean SCM satisfies monotonicity of the outcome mechanism in
the parent coordinate.

The witness is substantive: the proof applies the actual structural equation
for the outcome node. -/
theorem monotoneBoolSCM_satisfies :
    MonotoneMechanism (Ω := boolChainΩ)
      (SWIGNode.random y) (SWIGNode.random d) monotoneBoolSCM := by
  refine ⟨by simp [monotoneBoolSCM, boolChainSWIG], boolChainDParent.property, ?_⟩
  intro x y hxy _
  simpa [monotoneBoolSCM, copyStructFun] using hxy

/-- The reversing Boolean SCM violates monotonicity of the outcome mechanism in
the parent coordinate.

The low parent value maps to `true` and the high parent value maps to `false`,
so the required nondecreasing inequality fails. -/
theorem antitoneBoolSCM_violates :
    ¬ MonotoneMechanism (Ω := boolChainΩ)
      (SWIGNode.random y) (SWIGNode.random d) antitoneBoolSCM := by
  intro hmono
  rcases hmono with ⟨hchild, hparent, hmono⟩
  have hle :
      boolParentAssignment false ⟨SWIGNode.random d, hparent⟩ ≤
        boolParentAssignment true ⟨SWIGNode.random d, hparent⟩ := by
    change false ≤ true
    decide
  have hsame :
      ∀ w, w.val ≠ SWIGNode.random d →
        boolParentAssignment false w = boolParentAssignment true w := by
    intro w hw
    rcases w with ⟨n, hn⟩
    cases n with
    | random n =>
        cases n with
        | d => simp at hw
        | y => simp [boolParentAssignment]
    | fixed n =>
        cases n <;> simp [boolParentAssignment]
  have hbad := hmono (boolParentAssignment false) (boolParentAssignment true) hle hsame
  change Bool.not (boolParentAssignment false boolChainDParent) ≤
      Bool.not (boolParentAssignment true boolChainDParent) at hbad
  simp only [boolParentAssignment_boolChainDParent] at hbad
  cases hbad rfl

end Causalean.SCM.Assumptions
