/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.SCM.Model.InterventionSet
import Causalean.SCM.Model.Kernel
import Causalean.Graph.SWIGSplitMono
import Causalean.Graph.Induce
import Causalean.Graph.CComponents
import Causalean.Graph.DSep.Ancestral
import Causalean.SCM.ID.Density.LatentBlocks

/-! # Geometric foundation of the do-law g-formula (Tian, fixing route)

This file builds the graph-side objects over which the truncated g-formula for the
do-law `Y`-marginal is assembled.  Intervening on a treatment set `X` mutilates the
SWIG graph to `G_X = (M.fixSet X).toSWIGGraph` (the monolithic split `splitMono X`).
Tian's identification of `P(Y ∣ do(X))` only involves the part of the do-law lying
on the **ancestors of the query** in the mutilated graph, and factorizes that part
over the **c-components of the induced ancestral subgraph**.

* `fixAncestralSet`  — the ancestors of `Y` (together with `Y`) in the mutilated
  graph `G_X`; the support of the relevant do-law marginal.
* `fixTruncCComponentSet` — the c-components of `G_X` induced on that ancestral set;
  the index set of the truncated product.

These are exactly the objects the success certificate `idSucceeds` ranges over
(`∀ S ∈ (G_X.induce Ystar).cComponentSet, cFactorReachable G (containingCComponent G S) S`),
named here for use in the measure-theoretic g-formula.  The factorization itself —
the do-law `Y`-marginal equals the product over `fixTruncCComponentSet` of the
recovered full-district c-factors (each a functional of `obsDensity` via
`district_id`, with the truncation realized by the fixing operation `M.fixSet Wn`) —
is developed by the downstream Tian density and ID soundness layers.
-/

namespace Causalean.SCM.ID

open scoped MeasureTheory ProbabilityTheory

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

/-- The graph-level precondition that the SWIG split by `X` is valid. -/
def interventionValid (X : Finset N) (G : SWIGGraph N) : Prop :=
  (∀ D ∈ X, SWIGNode.random D ∈ G.observed) ∧
    (∀ D ∈ X, SWIGNode.fixed D ∉ G.fixed)

/-- The c-component of `G` containing the finite set `S`, seeded by an arbitrary
member of `S`; empty `S` has no containing component and returns `∅`. -/
noncomputable def containingCComponent
    (G : SWIGGraph N) (S : Finset (SWIGNode N)) :
    Finset (SWIGNode N) :=
  if hS : S.Nonempty then G.cComponentOf hS.choose else ∅

/-- Structural c-factor reachability, no-fixing approximation.

This captures the certified case where the target district `S` is already an
entire c-component of the original graph and lies in the component `T` that
contains it. The full ID algorithm permits more cases by a valid fixing
sequence reducing `T` to `S`; that general structural sequence predicate is the
recursive certificate `CFactorReachableRec` in `DoGFormulaRec`. -/
noncomputable def cFactorReachable
    (G : SWIGGraph N) (T S : Finset (SWIGNode N)) : Prop :=
  S.Nonempty ∧ S ⊆ T ∧ S ∈ G.cComponentSet

/-- Structural success certificate for the **no-additional-fixing (full-district)
fragment** of the Tian–Shpitser ID algorithm.

Split the graph on treatment variables `X`, form `Ystar = An_{G_X}(Y) ∪ Y`,
induce the SWIG on `Ystar`, and require every c-component of that ancestral
induced graph to be reachable from its containing c-component in the original
graph. The outcome set `Y` is required to be observed (a well-posed
interventional query targets observed nodes), and `X`, `Y` are disjoint.

Reachability here is the no-fixing approximation `cFactorReachable`: it certifies
only the cases where each required district is *already* a full c-component of the
original graph, so no recursive fixing sequence is needed. The full ID algorithm
succeeds in strictly more cases; that recursive predicate is `CFactorReachableRec`
(and its soundness `id_sound_rec`). -/
noncomputable def idSucceeds
    (X : Finset N) (Y : Finset (SWIGNode N)) (G : SWIGGraph N) : Prop :=
  ∃ hX : interventionValid X G,
    let GX := G.splitMono X hX.1 hX.2
    let Ystar := GX.dag.ancestralSet Y
    Y ⊆ G.observed ∧
      (∀ d ∈ X, SWIGNode.random d ∉ Y) ∧
        ∀ S ∈ (GX.induce Ystar).cComponentSet,
          cFactorReachable G (containingCComponent G S) S

/-- **The post-intervention ancestral set of the query.**  In the graph obtained by
intervening on the treatment set `X`, this is the set consisting of the query nodes
`Y` together with all of their ancestors.  It is the support of the part of the
do-law that Tian's algorithm identifies: nodes outside it do not influence
`P(Y ∣ do(X))`. -/
noncomputable def fixAncestralSet
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (Y : Finset (SWIGNode N)) : Finset (SWIGNode N) :=
  (M.fixSet X hObs hFix).toSWIGGraph.dag.ancestralSet Y

/-- **The truncated c-component index set.**  The c-components of the mutilated
graph `G_X` after inducing on the post-intervention ancestral set of the query.
This is the index set of the truncated product in the do-law g-formula: the do-law
`Y`-marginal factorizes into one c-factor per element of this set. -/
noncomputable def fixTruncCComponentSet
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (Y : Finset (SWIGNode N)) : Finset (Finset (SWIGNode N)) :=
  ((M.fixSet X hObs hFix).toSWIGGraph.induce
    (fixAncestralSet M X hObs hFix Y)).cComponentSet

/-- The post-intervention ancestral set contains the query. -/
theorem subset_fixAncestralSet
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (Y : Finset (SWIGNode N)) :
    Y ⊆ fixAncestralSet M X hObs hFix Y :=
  (M.fixSet X hObs hFix).toSWIGGraph.dag.subset_ancestralSet Y

/-- The **observed part of the post-intervention ancestral support** of the query.
The post-intervention ancestral set `An_{G_X}(Y)` is a SWIG-node set and may
include fixed intervention nodes, but the observational law is carried only on
observed coordinates, so the measure-theoretic support is its intersection with
the observed nodes. -/
noncomputable def fixObservedAncestralSet
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (Y : Finset (SWIGNode N)) : Finset (SWIGNode N) :=
  fixAncestralSet M X hObs hFix Y ∩ (M.fixSet X hObs hFix).observed

/-- Extend an assignment on the post-intervention observed ancestral support to
the original observed coordinates, pinning intervened random coordinates to the
fixed values of the do-slice. -/
noncomputable def pinnedExtend
    [∀ n, Nonempty (Ω n)]
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (Y : Finset (SWIGNode N))
    (sDo : (M.fixSet X hObs hFix).FixedValues) :
    ValuesOn (fixObservedAncestralSet M X hObs hFix Y) (swigΩ Ω) →
      ValuesOn M.observed (swigΩ Ω) :=
  fun xD v =>
    match v.val with
    | SWIGNode.random d =>
        if hd : d ∈ X then
          sDo ⟨SWIGNode.fixed d,
            Finset.mem_union_right _
              (Finset.mem_image.mpr ⟨d, hd, rfl⟩)⟩
        else if hvD : SWIGNode.random d ∈ fixObservedAncestralSet M X hObs hFix Y then
          xD ⟨SWIGNode.random d, hvD⟩
        else
          Classical.arbitrary _
    | SWIGNode.fixed d =>
        if hvD : SWIGNode.fixed d ∈ fixObservedAncestralSet M X hObs hFix Y then
          xD ⟨SWIGNode.fixed d, hvD⟩
        else
          Classical.arbitrary _

private lemma splitMono_edge_from_unobserved_iff
    (G : SWIGGraph N) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ G.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ G.fixed)
    {u v : SWIGNode N} (hu : u ∈ G.unobserved) :
    (G.splitMono X hObs hFix).dag.edge u v ↔ G.dag.edge u v := by
  obtain ⟨d, rfl⟩ := G.unobserved_is_random u hu
  have hdX : d ∉ X := by
    intro hd
    exact (Finset.disjoint_left.mp G.obs_unobs_disjoint (hObs d hd)) hu
  simp [SWIGGraph.splitMono, SWIGGraph.splitMonoDAG,
    SWIGGraph.splitMonoEdgeRel, hdX]

private lemma splitMono_directlyConfounded_iff
    (G : SWIGGraph N) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ G.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ G.fixed)
    (v₁ v₂ : SWIGNode N) :
    (G.splitMono X hObs hFix).directlyConfounded v₁ v₂ ↔
      G.directlyConfounded v₁ v₂ := by
  constructor
  · rintro ⟨hv₁, hv₂, hne, u, hu, hu₁, hu₂⟩
    exact ⟨hv₁, hv₂, hne, u, hu,
      (splitMono_edge_from_unobserved_iff G X hObs hFix hu).mp hu₁,
      (splitMono_edge_from_unobserved_iff G X hObs hFix hu).mp hu₂⟩
  · rintro ⟨hv₁, hv₂, hne, u, hu, hu₁, hu₂⟩
    exact ⟨hv₁, hv₂, hne, u, hu,
      (splitMono_edge_from_unobserved_iff G X hObs hFix hu).mpr hu₁,
      (splitMono_edge_from_unobserved_iff G X hObs hFix hu).mpr hu₂⟩

private lemma splitMono_bidirectedReachable_iff
    (G : SWIGGraph N) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ G.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ G.fixed)
    (v w : SWIGNode N) :
    (G.splitMono X hObs hFix).bidirectedReachable v w ↔
      G.bidirectedReachable v w := by
  constructor
  · intro h
    induction h with
    | refl hv => exact SWIGGraph.bidirectedReachable.refl hv
    | step hreach hconf ih =>
        exact SWIGGraph.bidirectedReachable.step ih
          ((splitMono_directlyConfounded_iff G X hObs hFix _ _).mp hconf)
  · intro h
    induction h with
    | refl hv => exact SWIGGraph.bidirectedReachable.refl hv
    | step hreach hconf ih =>
        exact SWIGGraph.bidirectedReachable.step ih
          ((splitMono_directlyConfounded_iff G X hObs hFix _ _).mpr hconf)

private lemma splitMono_cComponentOf_eq
    (G : SWIGGraph N) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ G.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ G.fixed)
    (v : SWIGNode N) :
    (G.splitMono X hObs hFix).cComponentOf v = G.cComponentOf v := by
  by_cases hv : v ∈ G.observed
  · apply Finset.Subset.antisymm
    · intro w hw
      rw [G.mem_cComponentOf_iff_reachable hv]
      exact (splitMono_bidirectedReachable_iff G X hObs hFix v w).mp
        (((G.splitMono X hObs hFix).mem_cComponentOf_iff_reachable hv).mp hw)
    · intro w hw
      rw [(G.splitMono X hObs hFix).mem_cComponentOf_iff_reachable hv]
      exact (splitMono_bidirectedReachable_iff G X hObs hFix v w).mpr
        ((G.mem_cComponentOf_iff_reachable hv).mp hw)
  · simp [SWIGGraph.cComponentOf, SWIGGraph.bidirectedBFS, hv]

private lemma splitMono_cComponentSet_eq
    (G : SWIGGraph N) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ G.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ G.fixed) :
    (G.splitMono X hObs hFix).cComponentSet = G.cComponentSet := by
  ext C
  simp [SWIGGraph.cComponentSet, splitMono_cComponentOf_eq G X hObs hFix]

private lemma DAG.mem_ancestralSet_of_edge_to_mem
    {V : Type*} [DecidableEq V] [Fintype V] (G : DAG V)
    {u v : V} {S : Finset V} (huv : G.edge u v)
    (hv : v ∈ G.ancestralSet S) :
    u ∈ G.ancestralSet S := by
  rcases Finset.mem_union.mp hv with hvS | hvA
  · exact G.mem_ancestralSet_of_isAncestor hvS (DAG.isAncestor.edge huv)
  · apply Finset.mem_union_right
    simp only [DAG.ancestorsSet, Finset.mem_filter, Finset.mem_univ, true_and] at hvA ⊢
    obtain ⟨w, hwS, hvw⟩ := hvA
    exact ⟨w, hwS, G.isAncestor_trans (DAG.isAncestor.edge huv) hvw⟩

private lemma splitMono_no_edge_from_intervened_random
    (G : SWIGGraph N) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ G.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ G.fixed)
    {d : N} (hd : d ∈ X) (v : SWIGNode N) :
    ¬ (G.splitMono X hObs hFix).dag.edge (SWIGNode.random d) v := by
  simp [SWIGGraph.splitMono, SWIGGraph.splitMonoDAG,
    SWIGGraph.splitMonoEdgeRel, hd]

private lemma splitMono_not_isAncestor_from_intervened_random
    (G : SWIGGraph N) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ G.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ G.fixed)
    {d : N} (hd : d ∈ X) (v : SWIGNode N) :
    ¬ (G.splitMono X hObs hFix).dag.isAncestor (SWIGNode.random d) v := by
  intro h
  induction h with
  | edge he => exact splitMono_no_edge_from_intervened_random G X hObs hFix hd _ he
  | trans _ _ ih => exact ih

private lemma random_intervened_mem_fixAncestralSet_iff_mem_Y_aux
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (Y : Finset (SWIGNode N)) {d : N} (hd : d ∈ X) :
    SWIGNode.random d ∈ fixAncestralSet M X hObs hFix Y ↔
      SWIGNode.random d ∈ Y := by
  constructor
  · intro h
    unfold fixAncestralSet at h
    rcases Finset.mem_union.mp h with hY | hAnc
    · exact hY
    · simp only [DAG.ancestorsSet, Finset.mem_filter, Finset.mem_univ, true_and] at hAnc
      obtain ⟨v, hvY, hanc⟩ := hAnc
      have hno := splitMono_not_isAncestor_from_intervened_random
        (M.toSWIGGraph) X hObs hFix hd v
      have hno' :
          ¬ (M.fixSet X hObs hFix).toSWIGGraph.dag.isAncestor
            (SWIGNode.random d) v := by
        simpa [SCM.fixSet, SCM.fixMono] using hno
      exact False.elim (hno' hanc)
  · intro hY
    exact (M.fixSet X hObs hFix).toSWIGGraph.dag.subset_ancestralSet Y hY

/-- The pinned extension projects back to the ancestral assignment when natural
intervened coordinates are excluded from the query. -/
lemma pinnedExtend_projection_eq
    [∀ n, Nonempty (Ω n)]
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (Y : Finset (SWIGNode N))
    (sDo : (M.fixSet X hObs hFix).FixedValues)
    (hYX : ∀ D ∈ X, SWIGNode.random D ∉ Y) :
    ∀ xD, valuesProjection
        (show fixObservedAncestralSet M X hObs hFix Y ⊆ M.observed from
          Finset.inter_subset_right)
        (pinnedExtend M X hObs hFix Y sDo xD) = xD := by
  intro xD
  funext v
  rcases v with ⟨v, hv⟩
  cases v with
  | random d =>
      have hvD : SWIGNode.random d ∈ fixObservedAncestralSet M X hObs hFix Y := hv
      have hnotX : d ∉ X := by
        intro hd
        have hAnc : SWIGNode.random d ∈ fixAncestralSet M X hObs hFix Y :=
          (Finset.mem_inter.mp hvD).1
        have hYd : SWIGNode.random d ∈ Y :=
          (random_intervened_mem_fixAncestralSet_iff_mem_Y_aux
            M X hObs hFix Y hd).mp hAnc
        exact hYX d hd hYd
      simp [valuesProjection, pinnedExtend, hnotX, hvD]
  | fixed d =>
      have hvD : SWIGNode.fixed d ∈ fixObservedAncestralSet M X hObs hFix Y := hv
      simp [valuesProjection, pinnedExtend, hvD]

/-- The pinned extension reads intervened random coordinates from the matching
fixed coordinate of the do-slice. -/
lemma pinnedExtend_pin_eq
    [∀ n, Nonempty (Ω n)]
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (Y : Finset (SWIGNode N))
    (sDo : (M.fixSet X hObs hFix).FixedValues) :
    ∀ xD (D : N) (hD : D ∈ X),
      pinnedExtend M X hObs hFix Y sDo xD
          ⟨SWIGNode.random D, hObs D hD⟩ =
        sDo ⟨SWIGNode.fixed D,
          Finset.mem_union_right _
            (Finset.mem_image.mpr ⟨D, hD, rfl⟩)⟩ := by
  intro xD D hD
  simp [pinnedExtend, hD]

/-- Intervening does not change the full c-component partition. -/
lemma fixSet_cComponentSet_eq
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed) :
    (M.fixSet X hObs hFix).toSWIGGraph.cComponentSet =
      M.toSWIGGraph.cComponentSet := by
  simpa [SCM.fixSet, SCM.fixMono] using
    (splitMono_cComponentSet_eq (M.toSWIGGraph) X hObs hFix)

/-- Membership in the full c-component partition transports across `fixSet`. -/
lemma fixSet_cComponentSet_mem
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (S : Finset (SWIGNode N)) :
    S ∈ (M.fixSet X hObs hFix).toSWIGGraph.cComponentSet ↔
      S ∈ M.toSWIGGraph.cComponentSet := by
  rw [fixSet_cComponentSet_eq M X hObs hFix]

/-- The observed post-intervention ancestral support is closed under observed
parents in the do-model. -/
lemma fixObservedAncestralSet_obsParent_closed
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (Y : Finset (SWIGNode N)) :
    (M.fixSet X hObs hFix).ObsParentClosed
      (fixObservedAncestralSet M X hObs hFix Y) := by
  refine ⟨Finset.inter_subset_right, ?_⟩
  intro v hv w hw hEdge
  have hvAnc : v ∈ fixAncestralSet M X hObs hFix Y :=
    (Finset.mem_inter.mp hv).1
  have hwAnc : w ∈ fixAncestralSet M X hObs hFix Y := by
    unfold fixAncestralSet at hvAnc ⊢
    exact DAG.mem_ancestralSet_of_edge_to_mem
      (M.fixSet X hObs hFix).toSWIGGraph.dag hEdge hvAnc
  exact Finset.mem_inter.mpr ⟨hwAnc, hw⟩

/-- For an intervened variable, its random copy is a post-intervention ancestor
of the query exactly when it is explicitly queried. -/
lemma random_intervened_mem_fixAncestralSet_iff_mem_Y
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (Y : Finset (SWIGNode N)) {d : N} (hd : d ∈ X) :
    SWIGNode.random d ∈ fixAncestralSet M X hObs hFix Y ↔
      SWIGNode.random d ∈ Y := by
  exact random_intervened_mem_fixAncestralSet_iff_mem_Y_aux M X hObs hFix Y hd

/-- The **post-intervention marginal on the observed ancestors of the query**: the
do-observational law pushed forward to the observed part of `Ystar = An_{G_X}(Y)`.
This is the object the truncated g-formula identifies first; the requested
`Y`-marginal is a further projection of it along `Y ⊆ Ystar`. -/
noncomputable def doObsKernelAncestralMarginal
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (Y : Finset (SWIGNode N)) :
    ProbabilityTheory.Kernel (M.fixSet X hObs hFix).FixedValues
      (ValuesOn (fixObservedAncestralSet M X hObs hFix Y) (swigΩ Ω)) :=
  (M.fixSet X hObs hFix).obsKernel.map (valuesProjection Finset.inter_subset_right)

/-- The post-intervention ancestral marginal is a Markov kernel: it is the
coordinate pushforward of the (Markov) do-observational kernel, so each slice is a
probability measure. -/
instance instIsMarkovKernel_doObsKernelAncestralMarginal
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (Y : Finset (SWIGNode N)) :
    ProbabilityTheory.IsMarkovKernel (doObsKernelAncestralMarginal M X hObs hFix Y) := by
  unfold doObsKernelAncestralMarginal
  exact ProbabilityTheory.Kernel.IsMarkovKernel.map _
    (measurable_valuesProjection Finset.inter_subset_right)

/-- The query is contained in the observed ancestral support: it lies in the
post-intervention ancestral set (`subset_fixAncestralSet`) and in the observed
nodes. -/
theorem subset_fixObservedAncestralSet
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (Y : Finset (SWIGNode N)) (hY : Y ⊆ M.observed) :
    Y ⊆ fixObservedAncestralSet M X hObs hFix Y :=
  Finset.subset_inter (subset_fixAncestralSet M X hObs hFix Y)
    ((SCM.fixSet_observed M X hObs hFix).symm ▸ hY)

end Causalean.SCM.ID
