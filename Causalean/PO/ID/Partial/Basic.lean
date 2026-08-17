/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-! # Partial Identification Basics

This file provides abstract infrastructure for scalar partial-identification
intervals. It defines the identified interval as the set of objective values
attainable over a feasible parameter set and proves general criteria for
placing that set inside, or identifying it exactly with, a closed real
interval.

The results are independent of the potential-outcome framework and are reused
by concrete bound constructions such as Balke-Pearl intervals. -/

namespace Causalean
namespace PartialID

/-- Sharp identified interval: the set of all objective values attainable by
a feasible parameter. -/
noncomputable def IdentifiedInterval {α : Type*} (obj : α → ℝ) (feasible : α → Prop) : Set ℝ :=
  Set.range (fun x : {x // feasible x} => obj x)

/-- A feasible parameter's objective value belongs to the identified interval. -/
lemma mem_identifiedInterval {α : Type*} {obj : α → ℝ} {feasible : α → Prop}
    {x : α} (hx : feasible x) : obj x ∈ IdentifiedInterval obj feasible :=
  ⟨⟨x, hx⟩, rfl⟩

/-- **Sandwich → membership.**  The literal content of a two-sided bound
`L ≤ θ ≤ U`: the target functional `θ` lies in the reported interval `[L, U]`.
Names the step that turns the inequality pair every concrete bound produces into
the `Set.Icc` vocabulary. -/
theorem mem_Icc_of_sandwich {θ L U : ℝ} (hlo : L ≤ θ) (hhi : θ ≤ U) :
    θ ∈ Set.Icc L U :=
  ⟨hlo, hhi⟩

/-- **Worst/best case over a nuisance.**  If a set `s ⊆ ℝ` is bounded, every one
of its members lies between `sInf s` and `sSup s`.  Applied with `s = range obj`
this is the engine form of "the truth is bracketed by the extreme feasible
values". -/
theorem mem_Icc_csInf_csSup {s : Set ℝ} {y : ℝ}
    (hb : BddBelow s) (ha : BddAbove s) (hy : y ∈ s) :
    y ∈ Set.Icc (sInf s) (sSup s) :=
  ⟨csInf_le hb hy, le_csSup ha hy⟩

variable {α : Type*} {obj : α → ℝ} {feasible : α → Prop}

/-- **Outer bound.**  If the objective is uniformly bounded below by `L` and
above by `U` over the feasible set, the sharp identified interval is contained
in `[L, U]`. -/
theorem identifiedInterval_subset_Icc {L U : ℝ}
    (hL : ∀ x, feasible x → L ≤ obj x) (hU : ∀ x, feasible x → obj x ≤ U) :
    IdentifiedInterval obj feasible ⊆ Set.Icc L U := by
  rintro _ ⟨x, rfl⟩
  exact ⟨hL x.1 x.2, hU x.1 x.2⟩

/-- **Sharp interval (order-connected form).** For an abstract objective function over a
feasible parameter set, suppose [the objective is bounded below by `L` on every feasible
parameter](hyp:hL), [bounded above by `U` on every feasible parameter](hyp:hU), [the value
`L` itself is attained by some feasible parameter](hyp:hLmem), [the value `U` itself is
attained by some feasible parameter](hyp:hUmem), and [the set of attainable objective
values is order-connected — it contains every real number between any two of its
members](hyp:hconn). Then [the identified interval — the set of all objective values
attainable over the feasible parameter set — equals the closed interval `[L, U]`
exactly](goal). Order-connectedness is the abstract substitute for "no gaps", supplied
concretely by `identifiedInterval_param_Icc` through continuity + connectedness of a
parameterization. -/
theorem identifiedInterval_eq_Icc {L U : ℝ}
    (hL : ∀ x, feasible x → L ≤ obj x) (hU : ∀ x, feasible x → obj x ≤ U)
    (hLmem : L ∈ IdentifiedInterval obj feasible)
    (hUmem : U ∈ IdentifiedInterval obj feasible)
    (hconn : (IdentifiedInterval obj feasible).OrdConnected) :
    IdentifiedInterval obj feasible = Set.Icc L U :=
  Set.Subset.antisymm (identifiedInterval_subset_Icc hL hU) (hconn.out hLmem hUmem)

/-- **Mixing-pattern constructor.** Suppose [the feasible parameter set is exactly the
image of the unit interval `[0, 1]` under a path `γ`](hyp:hfeas), [the objective composed
with `γ` is continuous on `[0, 1]`](hyp:hcont), [the objective value at the path's start
equals `L`](hyp:hL), [the objective value at the path's end equals `U`](hyp:hU), and [the
objective stays between `L` and `U` at every point along the path](hyp:hbound). Then [the
sharp identified interval is exactly `[L, U]`](goal). This is the canonical
partial-identification "mixing" shape: an unidentified nuisance ranging over a connected
parameter set sweeps the objective continuously across the whole interval between its
extreme values. -/
theorem identifiedInterval_param_Icc {γ : ℝ → α} {L U : ℝ}
    (hfeas : ∀ x, feasible x ↔ ∃ t ∈ Set.Icc (0 : ℝ) 1, γ t = x)
    (hcont : ContinuousOn (fun t => obj (γ t)) (Set.Icc 0 1))
    (hL : obj (γ 0) = L) (hU : obj (γ 1) = U)
    (hbound : ∀ t ∈ Set.Icc (0 : ℝ) 1, L ≤ obj (γ t) ∧ obj (γ t) ≤ U) :
    IdentifiedInterval obj feasible = Set.Icc L U := by
  have himg : IdentifiedInterval obj feasible = (fun t => obj (γ t)) '' Set.Icc 0 1 := by
    ext y
    simp only [IdentifiedInterval, Set.mem_range, Set.mem_image, Subtype.exists]
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨t, ht, rfl⟩ := (hfeas x).1 hx
      exact ⟨t, ht, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨γ t, (hfeas (γ t)).2 ⟨t, ht, rfl⟩, rfl⟩
  rw [himg]
  have hord : ((fun t => obj (γ t)) '' Set.Icc 0 1).OrdConnected :=
    ((isPreconnected_Icc).image _ hcont).ordConnected
  apply Set.Subset.antisymm
  · rintro _ ⟨t, ht, rfl⟩
    exact ⟨(hbound t ht).1, (hbound t ht).2⟩
  · exact hord.out ⟨0, by norm_num, hL⟩ ⟨1, by norm_num, hU⟩

end PartialID
end Causalean
