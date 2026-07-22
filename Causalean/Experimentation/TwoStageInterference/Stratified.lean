/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Hudgens–Halloran (2008): Assumption 2 (stratified interference)

Within Hudgens & Halloran's partial-interference setup, **stratified interference**
(their Assumption 2) restricts how a unit's outcome can depend on the rest of its group.
A unit `(i,j)`'s outcome is allowed to depend on the within-group assignment `w` only
through two summaries: the unit's *own* treatment `w j`, and the *number of other units in
the group that are treated* — not which particular units are treated.  Formally, if two
assignments `w` and `w'` give unit `j` the same own treatment and the same count of treated
others, then unit `(i,j)`'s outcome is the same under `w` and under `w'`.

This file records the stratified exposure summary (own treatment together with the count of
treated others), the stratified-interference predicate, and the resulting factorization: a
population `Y` satisfying stratified interference factors through the exposure, i.e. there is
`g i j : Bool × ℕ → ℝ` with `Y i j w = g i j (stratExpo i j w)`.  This is the instance of
Aronow–Samii's "properly specified exposure mapping" appropriate to grouped interference.
-/

import Causalean.Experimentation.TwoStageInterference.Basic
import Causalean.Experimentation.DesignBased.PotentialOutcome

/-! # Stratified interference

Stratified interference factors outcomes through own treatment and the count of treated peers.

The grouped exposure summary is `stratExpo`, built from a unit's own treatment and
`numTreatedOthers`.  `StratifiedInterference` states Hudgens-Halloran Assumption 2 as invariance
under equality of that exposure summary, `StratifiedInterference.elim` exposes the two raw
conditions, and `exists_strat_factor` proves that any stratified-interference outcome function
factors through the exposure map.
-/

open scoped BigOperators
open Finset

namespace Causalean
namespace Experimentation
namespace TwoStageInterference

open DesignBased

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {n : ι → ℕ}

/-- The number of units `k ≠ j` in group `i` that are treated under within-group assignment
`w` (the count of *other* treated units relevant to unit `j`). -/
def numTreatedOthers (i : ι) (j : Fin (n i)) (w : WAssign n i) : ℕ :=
  (Finset.univ.filter (fun k => k ≠ j ∧ w k = true)).card

/-- The **stratified-interference exposure** of unit `(i,j)` under within-group assignment
`w`: the pair of its own treatment `w j` and the number of other treated units in its group.
This is the exposure summary through which outcomes are allowed to depend on the assignment. -/
def stratExpo (i : ι) (j : Fin (n i)) (w : WAssign n i) : Bool × ℕ :=
  (w j, numTreatedOthers i j w)

/-- **Assumption 2 (stratified interference).**  A population of potential outcomes `Y`
satisfies stratified interference when each unit's outcome depends on the within-group
assignment only through its stratified exposure: whenever two assignments give a unit the
same own treatment and the same count of treated others, the unit's outcome agrees. -/
def StratifiedInterference (Y : ∀ i, Fin (n i) → WAssign n i → ℝ) : Prop :=
  ∀ i (j : Fin (n i)) (w w' : WAssign n i),
    stratExpo i j w = stratExpo i j w' → Y i j w = Y i j w'

/-- Restatement of stratified interference in terms of the two raw summaries: equal own
treatment and equal count of treated others force equal outcomes. -/
lemma StratifiedInterference.elim {Y : ∀ i, Fin (n i) → WAssign n i → ℝ}
    (h : StratifiedInterference Y) (i : ι) (j : Fin (n i)) (w w' : WAssign n i)
    (hown : w j = w' j) (hcount : numTreatedOthers i j w = numTreatedOthers i j w') :
    Y i j w = Y i j w' :=
  h i j w w' (by rw [stratExpo, stratExpo, hown, hcount])

/-- The exposure summary of unit `(i,j)` is always realized — namely by `w` itself; so every
stratified exposure value reachable from some assignment has a witnessing assignment. -/
lemma stratExpo_exists (i : ι) (j : Fin (n i)) (w : WAssign n i) :
    ∃ w', stratExpo i j w' = stratExpo i j w :=
  ⟨w, rfl⟩

/-- **Factorization through the exposure.**  Under stratified interference there is a family
`g i j : Bool × ℕ → ℝ` of exposure-indexed potential outcomes such that every outcome factors
as `Y i j w = g i j (stratExpo i j w)`.  This realizes the Aronow–Samii "properly specified
exposure mapping" form for grouped interference with exposure map `stratExpo`. -/
theorem exists_strat_factor {Y : ∀ i, Fin (n i) → WAssign n i → ℝ}
    (h : StratifiedInterference Y) :
    ∃ g : ∀ i, Fin (n i) → (Bool × ℕ) → ℝ,
      ∀ i (j : Fin (n i)) (w : WAssign n i), Y i j w = g i j (stratExpo i j w) := by
  classical
  refine ⟨fun i j e =>
      if he : ∃ w, stratExpo i j w = e then Y i j (Classical.choose he) else 0, ?_⟩
  intro i j w
  have he : ∃ w', stratExpo i j w' = stratExpo i j w := stratExpo_exists i j w
  simp only [dif_pos he]
  exact (h i j w (Classical.choose he) (Classical.choose_spec he).symm)

end TwoStageInterference
end Experimentation
end Causalean
