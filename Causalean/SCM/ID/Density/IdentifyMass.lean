/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.SCM.ID.Density.PiUnion
import Causalean.SCM.ID.GraphicalThms.DoGFormulaRec

/-! # Mass-level IDENTIFY functionals

This file contains the finite, mass-level coordinate operations used by the
recursive ID recovery.  The graph helpers `SWIGGraph.topoLinearOrder`,
`SWIGGraph.nodesAt`, `SWIGGraph.nodeIndex`, and `SWIGGraph.prefixIn` enumerate
selected SWIG nodes in topological order.  The mass operations
`SCM.marginalizeOn` and `SCM.extractDistrict` implement the coordinate
marginalization and district-ratio extraction steps.  The recursion
`SCM.identifyMassRec` then combines induced ancestral restriction, hedge
detection, and district extraction, with simp equations for its base, hedge, and
recursive branches.
-/

set_option linter.unusedFintypeInType false

namespace Causalean

open scoped BigOperators ENNReal

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

namespace SWIGGraph

/-- This order compares graph nodes by their topological position in the SWIG graph. -/
noncomputable def topoLinearOrder (G : SWIGGraph N) : LinearOrder (SWIGNode N) :=
  LinearOrder.lift' G.dag.topoOrder G.dag.topoOrder_injective

/-- This selector returns the node at a given position in a finite node set
sorted by graph topological order. -/
noncomputable def nodesAt (G : SWIGGraph N) (D : Finset (SWIGNode N))
    (i : Fin D.card) : {v // v ∈ D} := by
  classical
  letI := G.topoLinearOrder
  exact D.orderIsoOfFin rfl i

/-- This selector returns a node's position inside a finite node set sorted by
graph topological order. -/
noncomputable def nodeIndex (G : SWIGGraph N) (D : Finset (SWIGNode N))
    (v : {v // v ∈ D}) : Fin D.card := by
  classical
  letI := G.topoLinearOrder
  exact (D.orderIsoOfFin rfl).symm v

/-- This finite set contains the first selected nodes in graph topological order. -/
noncomputable def prefixIn (G : SWIGGraph N) (D : Finset (SWIGNode N)) (n : ℕ) :
    Finset (SWIGNode N) :=
  D.filter (fun v => if h : v ∈ D then (G.nodeIndex D ⟨v, h⟩).val < n else False)

/-- Every node in a topological prefix of a selected node set belongs to the selected node set. -/
lemma prefixIn_subset (G : SWIGGraph N) (D : Finset (SWIGNode N)) (n : ℕ) :
    G.prefixIn D n ⊆ D := by
  intro v hv
  exact (Finset.mem_filter.mp hv).1

end SWIGGraph

namespace SCM.ID

/-- The induced ancestral set lies inside the ambient observed node set. -/
theorem inducedAncestral_subset_left
    (G : SWIGGraph N) (T C : Finset (SWIGNode N)) :
    inducedAncestral G T C ⊆ T := by
  intro v hv
  unfold inducedAncestral at hv
  have hvObs : v ∈ (G.induce T).observed := (Finset.mem_inter.mp hv).2
  exact (Finset.mem_inter.mp (by simpa [SWIGGraph.induce] using hvObs)).1

/-- If `C` is observed and contained in `T`, then it is contained in its induced
ancestral set inside `T`. -/
theorem subset_inducedAncestral
    (G : SWIGGraph N) {T C : Finset (SWIGNode N)}
    (hCT : C ⊆ T) (hCobs : C ⊆ G.observed) :
    C ⊆ inducedAncestral G T C := by
  intro v hv
  unfold inducedAncestral
  refine Finset.mem_inter.mpr ⟨?_, ?_⟩
  · exact (G.induce T).dag.subset_ancestralSet C hv
  · simp [SWIGGraph.induce, hCT hv, hCobs hv]

/-- The containing c-component is always a set of observed nodes. -/
theorem containingCComponent_subset_observed
    (G : SWIGGraph N) (S : Finset (SWIGNode N)) :
    containingCComponent G S ⊆ G.observed := by
  classical
  by_cases hS : S.Nonempty
  · simpa [containingCComponent, hS] using G.cComponentOf_subset_observed hS.choose
  · simp [containingCComponent, hS]

/-- A containing c-component in an induced graph lies inside the inducing set. -/
theorem containingCComponent_induce_subset
    (G : SWIGGraph N) (A C : Finset (SWIGNode N)) :
    containingCComponent (G.induce A) C ⊆ A := by
  intro v hv
  have hvObs := containingCComponent_subset_observed (G.induce A) C hv
  exact (Finset.mem_inter.mp (by simpa [SWIGGraph.induce] using hvObs)).1

end SCM.ID

namespace SCM

/-- Marginalize a full-observed mass function by summing over the coordinates
in `W` and overriding those coordinates in the evaluation point. -/
noncomputable def marginalizeOn [∀ n, Fintype (Ω n)]
    (M : Causalean.SCM N Ω) (W : Finset (SWIGNode N)) (hW : W ⊆ M.observed)
    (q : ValuesOn M.observed (swigΩ Ω) → ENNReal) :
    ValuesOn M.observed (swigΩ Ω) → ENNReal :=
  fun x => ∑ y : ValuesOn W (swigΩ Ω), q (overrideOn hW x y)

/-- Extract the district factor for `C'` from a mass function on `A` by
multiplying adjacent prefix marginal ratios along the topological order of
`G'`. -/
noncomputable def extractDistrict [∀ n, Fintype (Ω n)]
    (M : Causalean.SCM N Ω) (G' : SWIGGraph N)
    (A C' : Finset (SWIGNode N)) (hA : A ⊆ M.observed)
    (q : ValuesOn M.observed (swigΩ Ω) → ENNReal) :
    ValuesOn M.observed (swigΩ Ω) → ENNReal :=
  fun x =>
    ∏ i ∈ Finset.univ.filter (fun i : Fin A.card => (G'.nodesAt A i).val ∈ C'),
      M.marginalizeOn (A \ G'.prefixIn A (i.val + 1))
          (fun _ hv => hA ((Finset.mem_sdiff.mp hv).1)) q x /
        M.marginalizeOn (A \ G'.prefixIn A i.val)
          (fun _ hv => hA ((Finset.mem_sdiff.mp hv).1)) q x

/-- The mass-level IDENTIFY recursion.  Starting with a mass function for `T`,
it recursively projects to the induced ancestral set of `C`, extracts the
containing district there, and stops when the induced ancestral set is exactly
`C`.  The hedge branch `A = T` returns the current mass function; successful
reachability proofs never use that branch. -/
noncomputable def identifyMassRec [∀ n, Fintype (Ω n)]
    (M : Causalean.SCM N Ω) (G : SWIGGraph N) :
    (T C : Finset (SWIGNode N)) → (hT : T ⊆ M.observed) →
      (q : ValuesOn M.observed (swigΩ Ω) → ENNReal) →
        ValuesOn M.observed (swigΩ Ω) → ENNReal
  | T, C, hT, q =>
    let A := ID.inducedAncestral G T C
    let hA : A ⊆ M.observed := fun _ hv =>
      hT (ID.inducedAncestral_subset_left G T C hv)
    if _hAC : A = C then
      M.marginalizeOn (T \ C)
        (fun _ hv => hT ((Finset.mem_sdiff.mp hv).1)) q
    else if _hAT : A = T then
      q
    else
      let C₁ := ID.containingCComponent (G.induce A) C
      let hC₁ : C₁ ⊆ M.observed := fun _ hv =>
        hT (ID.inducedAncestral_subset_left G T C
          (ID.containingCComponent_induce_subset G A C hv))
      M.identifyMassRec G C₁ C hC₁
        (M.extractDistrict (G.induce A) A C₁ hA
          (M.marginalizeOn (T \ A)
            (fun _ hv => hT ((Finset.mem_sdiff.mp hv).1)) q))
termination_by T _ _ _ => T.card
decreasing_by
  classical
  have hAsubT : A ⊆ T := ID.inducedAncestral_subset_left G T C
  have hAssubT : A ⊂ T := Finset.ssubset_iff_subset_ne.mpr ⟨hAsubT, _hAT⟩
  have hC₁subA : C₁ ⊆ A := ID.containingCComponent_induce_subset G A C
  exact Nat.lt_of_le_of_lt (Finset.card_le_card hC₁subA)
    (Finset.card_lt_card hAssubT)

/-- Base equation for `identifyMassRec`: if the induced ancestral set is already
the target, the result is the corresponding marginal. -/
@[simp] theorem identifyMassRec_base [∀ n, Fintype (Ω n)]
    (M : Causalean.SCM N Ω) (G : SWIGGraph N)
    (T C : Finset (SWIGNode N)) (hT : T ⊆ M.observed)
    (q : ValuesOn M.observed (swigΩ Ω) → ENNReal)
    (hAC : ID.inducedAncestral G T C = C) :
    M.identifyMassRec G T C hT q =
      M.marginalizeOn (T \ C)
        (fun _ hv => hT ((Finset.mem_sdiff.mp hv).1)) q := by
  rw [identifyMassRec]
  simp [hAC]

/-- Hedge equation for `identifyMassRec`: if the induced ancestral set is all of
`T` after the base branch has failed, the recursion returns the current mass. -/
@[simp] theorem identifyMassRec_hedge [∀ n, Fintype (Ω n)]
    (M : Causalean.SCM N Ω) (G : SWIGGraph N)
    (T C : Finset (SWIGNode N)) (hT : T ⊆ M.observed)
    (q : ValuesOn M.observed (swigΩ Ω) → ENNReal)
    (hAC : ID.inducedAncestral G T C ≠ C)
    (hAT : ID.inducedAncestral G T C = T) :
    M.identifyMassRec G T C hT q = q := by
  have hTC : T ≠ C := by
    intro h
    exact hAC (hAT.trans h)
  rw [identifyMassRec]
  simp [hAT, hTC]

/-- Step equation for `identifyMassRec`: outside the base and hedge branches,
the recursion descends to the containing c-component of `C` in the induced
ancestral graph after extracting that district. -/
@[simp] theorem identifyMassRec_step [∀ n, Fintype (Ω n)]
    (M : Causalean.SCM N Ω) (G : SWIGGraph N)
    (T C : Finset (SWIGNode N)) (hT : T ⊆ M.observed)
    (q : ValuesOn M.observed (swigΩ Ω) → ENNReal)
    (hAC : ID.inducedAncestral G T C ≠ C)
    (hAT : ID.inducedAncestral G T C ≠ T) :
    M.identifyMassRec G T C hT q =
      let A := ID.inducedAncestral G T C
      let hA : A ⊆ M.observed := fun _ hv =>
        hT (ID.inducedAncestral_subset_left G T C hv)
      let C₁ := ID.containingCComponent (G.induce A) C
      let hC₁ : C₁ ⊆ M.observed := fun _ hv =>
        hT (ID.inducedAncestral_subset_left G T C
          (ID.containingCComponent_induce_subset G A C hv))
      M.identifyMassRec G C₁ C hC₁
        (M.extractDistrict (G.induce A) A C₁ hA
          (M.marginalizeOn (T \ A)
            (fun _ hv => hT ((Finset.mem_sdiff.mp hv).1)) q)) := by
  rw [identifyMassRec]
  simp [hAC, hAT]

end SCM
end Causalean
