/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.SCM.ID.GraphicalThms.DoGFormula

/-! # The recursive IDENTIFY certificate (full Tian–Shpitser ID success)

The no-fixing certificate `cFactorReachable` (in `DoGFormula`) only handles the
case where a required district is already a full c-component of the original
graph.  The full ID algorithm recovers a target c-factor `Q[C]` from the c-factor
`Q[T]` of its containing district `T` by Tian's IDENTIFY subroutine
(Shpitser–Pearl, Fig. 3): repeatedly restrict to the ancestral set of `C` and
descend into the c-component of `C` in that restriction.

This file encodes IDENTIFY as an **inductive reachability predicate**
`CFactorReachableRec G T C` — a derivation exists iff `identify(C, T, ·)` returns
successfully (no hedge).  Using an inductive predicate (rather than a
`termination_by` recursion) makes the downstream soundness proof a clean
induction on the derivation, and makes well-foundedness structural.

* `inducedAncestral G T C` — the observed ancestors of `C` within the subgraph of
  `G` induced on `T` (Tian's `An(C)_{G_T}`, the observed part).
* `CFactorReachableRec G T C` — the IDENTIFY success predicate.
* `cFactorReachable_base_toRec` / `idSucceeds_toRec` — the no-fixing certificate is
  the base case, so `idSucceedsRec` generalizes `idSucceeds` (and the recursive
  soundness `id_sound_rec` will subsume the no-fixing `id_sound`).
-/

namespace Causalean.SCM.ID

variable {N : Type*} [DecidableEq N] [Fintype N]

/-- **Observed ancestors of `C` within the subgraph induced on `T`.**  Tian's
`An(C)_{G_T}`: restrict `G` to the node set `T`, take the ancestors of `C` in that
restricted graph, and keep the observed nodes.  This is the set the IDENTIFY
subroutine compares against `C` (project) and `T` (hedge / fail). -/
def inducedAncestral
    (G : SWIGGraph N) (T C : Finset (SWIGNode N)) : Finset (SWIGNode N) :=
  (G.induce T).dag.ancestralSet C ∩ (G.induce T).observed

/-- The induced ancestral set is closed under observed parents inside the
ambient district `T`. -/
theorem inducedAncestral_parent_closed
    (G : SWIGGraph N) {T C : Finset (SWIGNode N)} (hT : T ⊆ G.observed) :
    ∀ v ∈ T, ∀ w ∈ inducedAncestral G T C, G.dag.edge v w →
      v ∈ inducedAncestral G T C := by
  classical
  intro v hvT w hw hEdge
  unfold inducedAncestral at hw ⊢
  rcases Finset.mem_inter.mp hw with ⟨hwAnc, hwIndObs⟩
  have hvIndObs : v ∈ (G.induce T).observed := by
    simp [SWIGGraph.induce, hvT, hT hvT]
  have hwIndObs' : w ∈ T ∩ G.observed := by
    simpa [SWIGGraph.induce] using hwIndObs
  have hEdgeInd : (G.induce T).dag.edge v w := by
    rw [SWIGGraph.induce]
    rw [SWIGGraph.inducedDag_edge_iff]
    refine ⟨hEdge, ?_, ?_⟩
    · simp [hvT, hT hvT]
    · simp [(Finset.mem_inter.mp hwIndObs').1, (Finset.mem_inter.mp hwIndObs').2]
  have hvAnc : v ∈ (G.induce T).dag.ancestralSet C := by
    rcases Finset.mem_union.mp hwAnc with hwC | hwA
    · exact (G.induce T).dag.mem_ancestralSet_of_isAncestor hwC
        (DAG.isAncestor.edge hEdgeInd)
    · apply Finset.mem_union_right
      simp only [DAG.ancestorsSet, Finset.mem_filter, Finset.mem_univ, true_and]
        at hwA ⊢
      obtain ⟨c, hcC, hwc⟩ := hwA
      exact ⟨c, hcC,
        (G.induce T).dag.isAncestor_trans (DAG.isAncestor.edge hEdgeInd) hwc⟩
  exact Finset.mem_inter.mpr ⟨hvAnc, hvIndObs⟩

/-- **Recursive IDENTIFY reachability (full Tian–Shpitser success certificate).**
`CFactorReachableRec G T C` holds when `identify(C, T, Q[T])` succeeds, i.e. the
c-factor `Q[C]` is recoverable from `Q[T]`.

* `base`: `An(C)_{G_T} = C`, so `Q[C]` is the marginal `∑_{T∖C} Q[T]` — no further
  fixing needed.  (This subsumes the no-fixing case, where `T = C`.)
* `step`: `An(C)_{G_T}` is a proper intermediate set `A` (neither `C` nor `T`; the
  `A = T` case is the hedge, which is *absent* here — no constructor), and IDENTIFY
  recurses on the c-component of `C` inside `G_A`, a strictly smaller district. -/
inductive CFactorReachableRec (G : SWIGGraph N) :
    Finset (SWIGNode N) → Finset (SWIGNode N) → Prop where
  | base {T C : Finset (SWIGNode N)}
      (hne : C.Nonempty) (hCT : C ⊆ T)
      (hproject : inducedAncestral G T C = C) :
      CFactorReachableRec G T C
  | step {T C : Finset (SWIGNode N)}
      (hne : C.Nonempty) (hCT : C ⊆ T)
      (hnotC : inducedAncestral G T C ≠ C)
      (hnotT : inducedAncestral G T C ≠ T)
      (hrec : CFactorReachableRec G
        (containingCComponent (G.induce (inducedAncestral G T C)) C) C) :
      CFactorReachableRec G T C

/-- **Full recursive success certificate for the ID algorithm.**  As `idSucceeds`,
but each c-component `S` of the post-intervention ancestral graph need only be
*recursively reachable* from its containing district (`CFactorReachableRec`), not
already a full c-component.  This is the honest Tian–Shpitser ID success
condition (for the soundness direction). -/
noncomputable def idSucceedsRec
    (X : Finset N) (Y : Finset (SWIGNode N)) (G : SWIGGraph N) : Prop :=
  ∃ hX : interventionValid X G,
    let GX := G.splitMono X hX.1 hX.2
    let Ystar := GX.dag.ancestralSet Y
    Y ⊆ G.observed ∧
      (∀ d ∈ X, SWIGNode.random d ∉ Y) ∧
        ∀ S ∈ (GX.induce Ystar).cComponentSet,
          CFactorReachableRec G (containingCComponent G S) S

/-- When `S` is a full c-component of `G`, its containing district is `S` itself. -/
theorem containingCComponent_of_mem_cComponentSet
    (G : SWIGGraph N) (S : Finset (SWIGNode N))
    (hS : S ∈ G.cComponentSet) :
    containingCComponent G S = S := by
  simp only [SWIGGraph.cComponentSet] at hS
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hS
  have hne : (G.cComponentOf v).Nonempty := ⟨v, G.mem_cComponentOf_self hv⟩
  simp only [containingCComponent, dif_pos hne]
  have hreach : G.bidirectedReachable v hne.choose :=
    (G.mem_cComponentOf_iff_reachable hv).mp hne.choose_spec
  exact (G.cComponentOf_eq_of_reachable hreach).symm

/-- The observed ancestors of a full c-component `S` within `G_S` are `S` itself. -/
theorem inducedAncestral_self_of_mem_cComponentSet
    (G : SWIGGraph N) (S : Finset (SWIGNode N))
    (hS : S ∈ G.cComponentSet) :
    inducedAncestral G S S = S := by
  have hSobs : S ⊆ G.observed := G.cComponentSet_subset_observed S hS
  have hobs : (G.induce S).observed = S := by
    change S ∩ G.observed = S
    exact Finset.inter_eq_left.mpr hSobs
  rw [inducedAncestral, hobs]
  apply Finset.Subset.antisymm
  · exact Finset.inter_subset_right
  · intro x hx
    exact Finset.mem_inter.mpr ⟨(G.induce S).dag.subset_ancestralSet S hx, hx⟩

/-- **The no-fixing certificate is the base case of the recursive one.**  A district
that is already a full c-component of `G` is recursively reachable from its
containing district (which is itself). -/
theorem cFactorReachable_base_toRec
    (G : SWIGGraph N) (S : Finset (SWIGNode N))
    (h : cFactorReachable G (containingCComponent G S) S) :
    CFactorReachableRec G (containingCComponent G S) S := by
  obtain ⟨hne, _hsub, hmem⟩ := h
  rw [containingCComponent_of_mem_cComponentSet G S hmem]
  exact CFactorReachableRec.base hne (Finset.Subset.refl _)
    (inducedAncestral_self_of_mem_cComponentSet G S hmem)

/-- **`idSucceedsRec` generalizes `idSucceeds`.**  Every no-fixing certificate is a
recursive certificate, so soundness proved for `idSucceedsRec` subsumes the
no-fixing headline. -/
theorem idSucceeds_toRec
    (X : Finset N) (Y : Finset (SWIGNode N)) (G : SWIGGraph N)
    (h : idSucceeds X Y G) : idSucceedsRec X Y G := by
  obtain ⟨hX, hYobs, hdisj, hreach⟩ := h
  refine ⟨hX, hYobs, hdisj, ?_⟩
  intro S hS
  exact cFactorReachable_base_toRec G S (hreach S hS)

end Causalean.SCM.ID
