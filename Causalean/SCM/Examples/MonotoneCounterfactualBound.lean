/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.SCM.ID.Assumptions.Monotonicity
import Causalean.SCM.PartialID.CanonicalModel
import Mathlib.Data.Real.Basic

/-! # Monotone Counterfactual Bound Example

This file gives a worked example of structural monotonicity in a two-node
Boolean SCM. The target is the unit-level response contrast of the outcome
equation when the parent coordinate is changed from `false` to `true`.

Without any structural restriction that contrast has logical range `[-1, 1]`.
Under the monotone-mechanism assumption it must lie in `[0, 1]`. The companion
counterexample below uses the reversing Boolean SCM as the reference model to
show that graph and observational compatibility alone do not generally imply a
`[0, 1]` response-contrast bound.
-/

namespace Causalean.SCM.Examples.MonotoneCounterfactualBound

open Causalean
open Causalean.SCM.Assumptions
open Causalean.SCM.Assumptions.BoolChainNode
open Causalean.SCM.PartialID

/-- A Boolean value is scored as one for `true` and zero for `false`.

This turns the Boolean structural response into the usual real-valued response
indicator used in a binary-outcome causal contrast. -/
def boolScore (b : Bool) : ℝ :=
  if b then 1 else 0

/-- A parent assignment inside an arbitrary Boolean-chain SCM.

The designated treatment parent is set to `b`; every other parent coordinate is
held at `false`. In compatible models with the Boolean-chain graph, the only
parent of the outcome is the designated treatment parent. -/
def boolParentAssignmentIn (M : Causalean.SCM BoolChainNode boolChainΩ) (b : Bool) :
    ∀ w : {w // w ∈ M.dag.parents (SWIGNode.random y)}, swigΩ boolChainΩ w.val := by
  intro w
  rcases w with ⟨n, _⟩
  cases n with
  | random n =>
      cases n with
      | d => exact b
      | y => exact false
  | fixed n =>
      cases n <;> exact false

/-- The designated parent coordinate receives the assigned Boolean value. -/
@[simp] theorem boolParentAssignmentIn_parent
    (M : Causalean.SCM BoolChainNode boolChainΩ)
    (hparent : SWIGNode.random d ∈ M.dag.parents (SWIGNode.random y)) (b : Bool) :
    boolParentAssignmentIn M b ⟨SWIGNode.random d, hparent⟩ = b := by
  cases b <;> rfl

@[simp] private theorem boolParentAssignmentIn_monotoneBoolSCM (b : Bool) :
    boolParentAssignmentIn monotoneBoolSCM b boolChainDParent = b := by
  cases b <;> rfl

@[simp] private theorem boolParentAssignmentIn_antitoneBoolSCM (b : Bool) :
    boolParentAssignmentIn antitoneBoolSCM b boolChainDParent = b := by
  cases b <;> rfl

/-- The real-valued response contrast of the Boolean outcome equation.

This is the difference between the outcome structural response at parent value
`true` and the response at parent value `false`, scored as a binary outcome. If
the requested child or parent is absent, the total functional returns zero; the
example theorem applies on a compatible class where both nodes are present. -/
noncomputable def monotoneResponseContrast :
    Causalean.SCM BoolChainNode boolChainΩ → ℝ :=
  fun M =>
    if hchild : SWIGNode.random y ∈ M.observed then
      if SWIGNode.random d ∈ M.dag.parents (SWIGNode.random y) then
        boolScore (M.structFun ⟨SWIGNode.random y, hchild⟩
          (boolParentAssignmentIn M true)) -
          boolScore (M.structFun ⟨SWIGNode.random y, hchild⟩
            (boolParentAssignmentIn M false))
      else 0
    else 0

private theorem boolScore_sub_mem_Icc {lo hi : Bool} (h : lo ≤ hi) :
    boolScore hi - boolScore lo ∈ Set.Icc (0 : ℝ) 1 := by
  cases lo <;> cases hi
  · simp [boolScore]
  · simp [boolScore]
  · exfalso
    cases h rfl
  · simp [boolScore]

private theorem responseContrast_eq_of_present
    (M : Causalean.SCM BoolChainNode boolChainΩ)
    (hchild : SWIGNode.random y ∈ M.observed)
    (hparent : SWIGNode.random d ∈ M.dag.parents (SWIGNode.random y)) :
    monotoneResponseContrast M =
      boolScore (M.structFun ⟨SWIGNode.random y, hchild⟩
        (boolParentAssignmentIn M true)) -
        boolScore (M.structFun ⟨SWIGNode.random y, hchild⟩
          (boolParentAssignmentIn M false)) := by
  simp [monotoneResponseContrast, hchild, hparent]

/-- Structural monotonicity gives a valid `[0, 1]` partial-identification bound.

Every SCM that is compatible with the Boolean-chain graph, observationally
equivalent to the reference model, and monotone in the outcome's treatment
parent has a nonnegative binary response contrast, and the contrast cannot
exceed one. The companion theorem
`monotoneCounterfactualBound_fails_without_monotonicity` gives a separate
unconstrained Boolean-chain compatible class, using the reversing SCM as the
reference model, where a `[0, 1]` response-contrast bound is false. -/
theorem monotoneCounterfactualBound :
    compatibleInterval boolChainSWIG
        (MonotoneMechanism (Ω := boolChainΩ) (SWIGNode.random y) (SWIGNode.random d))
        monotoneBoolSCM monotoneResponseContrast ⊆ Set.Icc (0 : ℝ) 1 := by
  intro z hz
  rcases hz with ⟨⟨M, hM⟩, hz⟩
  rcases hM.2.1 with ⟨hchild, hparent, hmono⟩
  have hparent_le :
      boolParentAssignmentIn M false ⟨SWIGNode.random d, hparent⟩ ≤
        boolParentAssignmentIn M true ⟨SWIGNode.random d, hparent⟩ := by
    change false ≤ true
    decide
  have hsame :
      ∀ w, w.val ≠ SWIGNode.random d →
        boolParentAssignmentIn M false w = boolParentAssignmentIn M true w := by
    intro w hw
    rcases w with ⟨n, hn⟩
    cases n with
    | random n =>
        cases n with
        | d => simp at hw
        | y => simp [boolParentAssignmentIn]
    | fixed n =>
        cases n <;> simp [boolParentAssignmentIn]
  have hresp :
      M.structFun ⟨SWIGNode.random y, hchild⟩ (boolParentAssignmentIn M false) ≤
        M.structFun ⟨SWIGNode.random y, hchild⟩ (boolParentAssignmentIn M true) :=
    hmono (boolParentAssignmentIn M false) (boolParentAssignmentIn M true)
      hparent_le hsame
  rw [← hz]
  change monotoneResponseContrast M ∈ Set.Icc (0 : ℝ) 1
  rw [responseContrast_eq_of_present M hchild hparent]
  exact boolScore_sub_mem_Icc hresp

/-- The monotone-compatible class is nonempty for the monotone-bound example.

The copying Boolean SCM has the declared graph, satisfies the monotone
structural assumption, and is observationally equivalent to itself. -/
theorem monotoneCounterfactualBound_assumption_satisfiable :
    CompatibleSCM boolChainSWIG
        (MonotoneMechanism (Ω := boolChainΩ) (SWIGNode.random y) (SWIGNode.random d))
        monotoneBoolSCM monotoneBoolSCM := by
  exact compatibleSCM_self _ _ _ rfl monotoneBoolSCM_satisfies

/-- The copying Boolean SCM has response contrast one. -/
theorem monotoneResponseContrast_monotoneBoolSCM :
    monotoneResponseContrast monotoneBoolSCM = 1 := by
  have hchild : SWIGNode.random y ∈ monotoneBoolSCM.observed := by
    simp [monotoneBoolSCM, boolChainSWIG]
  have hparent : SWIGNode.random d ∈ monotoneBoolSCM.dag.parents (SWIGNode.random y) :=
    boolChainDParent.property
  rw [responseContrast_eq_of_present monotoneBoolSCM hchild hparent]
  change boolScore (boolParentAssignmentIn monotoneBoolSCM true boolChainDParent) -
      boolScore (boolParentAssignmentIn monotoneBoolSCM false boolChainDParent) = 1
  simp [boolScore]

/-- The reversing Boolean SCM has response contrast minus one. -/
theorem monotoneResponseContrast_antitoneBoolSCM :
    monotoneResponseContrast antitoneBoolSCM = -1 := by
  have hchild : SWIGNode.random y ∈ antitoneBoolSCM.observed := by
    simp [antitoneBoolSCM, boolChainSWIG]
  have hparent : SWIGNode.random d ∈ antitoneBoolSCM.dag.parents (SWIGNode.random y) :=
    boolChainDParent.property
  rw [responseContrast_eq_of_present antitoneBoolSCM hchild hparent]
  change boolScore (Bool.not (boolParentAssignmentIn antitoneBoolSCM true boolChainDParent)) -
      boolScore (Bool.not (boolParentAssignmentIn antitoneBoolSCM false boolChainDParent)) = -1
  simp [boolScore]

/-- The `[0, 1]` bound fails without the monotonicity assumption.

Using the reversing Boolean SCM as the reference model, the unconstrained
compatible class contains that same model and its response contrast is `-1`,
outside `[0, 1]`. Thus the monotone-bound example is not a consequence of graph or
observational compatibility alone. -/
theorem monotoneCounterfactualBound_fails_without_monotonicity :
    ¬ compatibleInterval boolChainSWIG (fun _ : Causalean.SCM BoolChainNode boolChainΩ => True)
        antitoneBoolSCM monotoneResponseContrast ⊆ Set.Icc (0 : ℝ) 1 := by
  intro hsub
  have hmem : (-1 : ℝ) ∈
      compatibleInterval boolChainSWIG
        (fun _ : Causalean.SCM BoolChainNode boolChainΩ => True)
        antitoneBoolSCM monotoneResponseContrast := by
    refine ⟨⟨antitoneBoolSCM, ?_⟩, ?_⟩
    · exact compatibleSCM_self _ _ _ rfl trivial
    · exact monotoneResponseContrast_antitoneBoolSCM
  have hbad := hsub hmem
  norm_num at hbad

end Causalean.SCM.Examples.MonotoneCounterfactualBound
