/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.SCM.ID.GraphicalThms.DoGFormula
import Causalean.SCM.Do.ObsMarkov
import Causalean.SCM.ID.Density.CComponentDensity
import Causalean.SCM.ID.Density.DoLawMarginal
import Causalean.SCM.ID.Density.MechCFactor
import Causalean.Graph.DSep.InduceTransport

/-!
# Tian district densities and the c-component recovery core

This file provides the density-level Tian district objects used by the ID
do-law assembly: the topological prefix helpers on a SWIG node set
(`nodesAt`, `nodeIndex`, `prefixIn`), `tianPrefixStepDensity`,
`tianDistrictDensity` (the `S`-district prefix-conditional product of a measure
on `D`), and `tianDensityProduct`, around Tian and Pearl (2002) Eqs. 37 and
70-72.

The keystone is `tian_full_cComponent_density_recovery_core_direct`: for a
district `S` of the post-intervention ancestral graph that is also a full
c-component of `M`, the `S`-district factor of the do-law ancestral marginal
equals a.e. the full observational c-component factor `Q_M[S]`.  The proof
chains the do-model district-density identity, do(X)-invariance of mechanism
c-factors, and the observational c-component/mechanism equivalence.
-/

namespace Causalean

open scoped MeasureTheory ProbabilityTheory ENNReal BigOperators

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

namespace SWIGGraph

/-- Topological prefixes of an observed-parent-closed set remain
observed-parent-closed. -/
lemma prefixIn_obsParentClosed
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (Y : Finset (SWIGNode N)) (k : ℕ) :
    (M.fixSet X hObs hFix).ObsParentClosed
      (((M.fixSet X hObs hFix).toSWIGGraph.induce
          (SCM.ID.fixAncestralSet M X hObs hFix Y)).prefixIn
        (SCM.ID.fixObservedAncestralSet M X hObs hFix Y) k) := by
  classical
  let M' := M.fixSet X hObs hFix
  let A := SCM.ID.fixAncestralSet M X hObs hFix Y
  let D := SCM.ID.fixObservedAncestralSet M X hObs hFix Y
  let H := M'.toSWIGGraph.induce A
  have hDclosed : M'.ObsParentClosed D := by
    simpa [M', D] using
      (SCM.ID.fixObservedAncestralSet_obsParent_closed M X hObs hFix Y)
  refine ⟨?_, ?_⟩
  · intro v hv
    exact hDclosed.1 (H.prefixIn_subset D k hv)
  · intro v hv w hwObs hEdge
    have hvD : v ∈ D := H.prefixIn_subset D k hv
    have hwD : w ∈ D := hDclosed.2 v hvD w hwObs hEdge
    rcases Finset.mem_filter.mp hv with ⟨hvD₀, hvIdxLt₀⟩
    have hvIdxLt : (H.nodeIndex D ⟨v, hvD⟩).val < k := by
      have hsub :
          (⟨v, hvD⟩ : {v // v ∈ D}) = ⟨v, hvD₀⟩ := Subtype.ext rfl
      simpa [SWIGGraph.prefixIn, hsub, hvD₀] using hvIdxLt₀
    have hEdgeH : H.dag.edge w v := by
      have hwA : w ∈ A := (Finset.mem_inter.mp hwD).1
      have hvA : v ∈ A := (Finset.mem_inter.mp hvD).1
      have hvObs : v ∈ M'.observed := hDclosed.1 hvD
      dsimp [H, M', A, SWIGGraph.induce, SWIGGraph.inducedDag,
        SWIGGraph.inducedEdge]
      refine ⟨hEdge, ?_, ?_⟩
      · exact Finset.mem_union_left _
          (Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hwA, hwObs⟩))
      · exact Finset.mem_union_left _
          (Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hvA, hvObs⟩))
    have hTopo : H.dag.topoOrder w < H.dag.topoOrder v :=
      H.dag.topoOrder_lt w v hEdgeH
    letI := H.topoLinearOrder
    have hSubtypeLt : (⟨w, hwD⟩ : {v // v ∈ D}) < ⟨v, hvD⟩ := by
      change H.dag.topoOrder w < H.dag.topoOrder v
      exact hTopo
    have hIndexLt :
        (H.nodeIndex D ⟨w, hwD⟩).val < (H.nodeIndex D ⟨v, hvD⟩).val := by
      have hIndexLtFin : H.nodeIndex D ⟨w, hwD⟩ < H.nodeIndex D ⟨v, hvD⟩ := by
        simpa [SWIGGraph.nodeIndex] using
          ((D.orderIsoOfFin rfl).symm.strictMono hSubtypeLt)
      simpa [SWIGGraph.nodeIndex] using
        hIndexLtFin
    change w ∈ D.filter
      (fun v => if h : v ∈ D then (H.nodeIndex D ⟨v, h⟩).val < k else False)
    exact Finset.mem_filter.mpr
      ⟨hwD, by simpa [hwD] using lt_trans hIndexLt hvIdxLt⟩

end SWIGGraph

namespace SCM.ID

/-- This predicate says that two coordinate blocks are conditionally independent
given a third block under a finite-coordinate measure.

It is the measure-level analogue of observational conditional independence, but
it is not tied to a particular structural causal model or induced model. -/
def KernelObsCondIndepOn
    (D X Y Z : Finset (SWIGNode N))
    (hX : X ⊆ D) (hY : Y ⊆ D) (hZ : Z ⊆ D)
    (μ : MeasureTheory.Measure (ValuesOn D (swigΩ Ω)))
    [StandardBorelSpace (ValuesOn D (swigΩ Ω))]
    [MeasureTheory.IsFiniteMeasure μ] : Prop :=
  ProbabilityTheory.CondIndepFun
    (MeasurableSpace.comap (valuesProjection hZ) inferInstance)
    (comap_valuesProjection_le hZ)
    (valuesProjection hX)
    (valuesProjection hY)
    μ

/-- This predicate says that every graphical separation in a graph gives the
corresponding coordinate conditional independence under a finite-coordinate
measure.

It is the graph-to-measure interface needed for Tian's Lemma 1 and deliberately
does not mention an induced structural causal model. -/
def KernelGlobalMarkovOn
    (H : SWIGGraph N) (D : Finset (SWIGNode N))
    (_hD : H.observed = D)
    (μ : MeasureTheory.Measure (ValuesOn D (swigΩ Ω)))
    [StandardBorelSpace (ValuesOn D (swigΩ Ω))]
    [MeasureTheory.IsFiniteMeasure μ] : Prop :=
  ∀ X Y Z : Finset (SWIGNode N),
    ∀ (hX : X ⊆ D) (hY : Y ⊆ D) (hZ : Z ⊆ D),
      Disjoint X Y → Disjoint X Z → Disjoint Y Z →
        H.dag.dSep X Y Z →
          KernelObsCondIndepOn D X Y Z hX hY hZ μ

/-- This density is Tian's one-node conditional factor along the topological
prefix of a finite node set.

The conditioning set is the prefix inside the chosen finite node set, not graph
parents and not the full observed prefix of an ambient model. -/
noncomputable def tianPrefixStepDensity
    (G : SWIGGraph N) (D : Finset (SWIGNode N))
    (μ : MeasureTheory.Measure (ValuesOn D (swigΩ Ω)))
    (ref : Causalean.SCM.ReferenceMeasures Ω)
    (i : Fin D.card)
    [MeasureTheory.IsFiniteMeasure μ]
    [StandardBorelSpace
      (ValuesOn ({(G.nodesAt D i).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [Nonempty
      (ValuesOn ({(G.nodesAt D i).val} : Finset (SWIGNode N)) (swigΩ Ω))] :
    ValuesOn D (swigΩ Ω) → ENNReal :=
  fun x =>
    ((ProbabilityTheory.condDistrib
        (valuesProjection
          (show ({(G.nodesAt D i).val} : Finset (SWIGNode N)) ⊆ D from by
            intro v hv
            rw [Finset.mem_singleton] at hv
            exact hv ▸ (G.nodesAt D i).property))
        (valuesProjection (G.prefixIn_subset D i.val))
        μ)
        (valuesProjection (G.prefixIn_subset D i.val) x)).rnDeriv
      (Causalean.SCM.jointRef ref ({(G.nodesAt D i).val} : Finset (SWIGNode N)))
      (valuesProjection
        (show ({(G.nodesAt D i).val} : Finset (SWIGNode N)) ⊆ D from by
          intro v hv
          rw [Finset.mem_singleton] at hv
          exact hv ▸ (G.nodesAt D i).property) x)

/-- Tian's district density multiplies the prefix conditional factors whose
nodes lie in one district.

This is the induce-free district factor for a measure on the selected finite
node set. -/
noncomputable def tianDistrictDensity
    (G : SWIGGraph N) (D : Finset (SWIGNode N))
    (μ : MeasureTheory.Measure (ValuesOn D (swigΩ Ω)))
    (ref : Causalean.SCM.ReferenceMeasures Ω)
    (S : Finset (SWIGNode N))
    [MeasureTheory.IsFiniteMeasure μ]
    [∀ (k : ℕ) (hk : k < D.card),
      StandardBorelSpace
        (ValuesOn ({(G.nodesAt D ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < D.card),
      Nonempty
        (ValuesOn ({(G.nodesAt D ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))] :
    ValuesOn D (swigΩ Ω) → ENNReal :=
  fun x =>
    ∏ i ∈ Finset.univ.filter
        (fun i : Fin D.card => (G.nodesAt D i).val ∈ S),
      tianPrefixStepDensity G D μ ref i x

/-- Tian's full prefix-chain density multiplies all one-node prefix conditional
factors for a finite node set. -/
noncomputable def tianDensityProduct
    (G : SWIGGraph N) (D : Finset (SWIGNode N))
    (μ : MeasureTheory.Measure (ValuesOn D (swigΩ Ω)))
    (ref : Causalean.SCM.ReferenceMeasures Ω)
    [MeasureTheory.IsFiniteMeasure μ]
    [∀ (k : ℕ) (hk : k < D.card),
      StandardBorelSpace
        (ValuesOn ({(G.nodesAt D ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < D.card),
      Nonempty
        (ValuesOn ({(G.nodesAt D ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))] :
    ValuesOn D (swigΩ Ω) → ENNReal :=
  fun x => ∏ i : Fin D.card, tianPrefixStepDensity G D μ ref i x

/-- For an observed node and a c-component listed in `cComponentSet`, membership
in that component is the same as saying that the node's computed c-component is
that listed component.  This converts Tian's district factor, which filters by
membership in a district, into the fiber form needed for finite-product
regrouping. -/
lemma mem_cComponent_iff_cComponentOf_eq
    (G : SWIGGraph N) {v : SWIGNode N} {S : Finset (SWIGNode N)}
    (hv : v ∈ G.observed) (hS : S ∈ G.cComponentSet) :
    v ∈ S ↔ G.cComponentOf v = S := by
  constructor
  · intro hvS
    rw [SWIGGraph.cComponentSet, Finset.mem_image] at hS
    obtain ⟨w, hw, rfl⟩ := hS
    have hwv : G.bidirectedReachable w v :=
      (G.mem_cComponentOf_iff_reachable hw).mp hvS
    exact (G.cComponentOf_eq_of_reachable hwv).symm
  · intro hcomp
    exact hcomp ▸ G.mem_cComponentOf_self hv

/-- Tian's full prefix-chain density regroups exactly as the product of the
Tian district factors over the graph c-components.  This is pure finite-product
algebra: each prefix index maps to the c-component of its node, and the district
factor is precisely the product over the corresponding fiber. -/
theorem prod_tianDistrictDensity_eq_tianDensityProduct
    (H : SWIGGraph N) (D : Finset (SWIGNode N))
    (hD : H.observed = D)
    (μ : MeasureTheory.Measure (ValuesOn D (swigΩ Ω)))
    (ref : Causalean.SCM.ReferenceMeasures Ω)
    [MeasureTheory.IsFiniteMeasure μ]
    [∀ (k : ℕ) (hk : k < D.card),
      StandardBorelSpace
        (ValuesOn ({(H.nodesAt D ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < D.card),
      Nonempty
        (ValuesOn ({(H.nodesAt D ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))] :
    (fun x => ∏ S ∈ H.cComponentSet, tianDistrictDensity H D μ ref S x)
      = fun x => tianDensityProduct H D μ ref x := by
  classical
  funext x
  have hmaps : ∀ i ∈ (Finset.univ : Finset (Fin D.card)),
      H.cComponentOf (H.nodesAt D i).val ∈ H.cComponentSet := by
    intro i _
    exact Finset.mem_image.mpr ⟨(H.nodesAt D i).val, hD.symm ▸ (H.nodesAt D i).property, rfl⟩
  unfold tianDensityProduct tianDistrictDensity
  rw [← Finset.prod_fiberwise_of_maps_to hmaps
    (fun i => tianPrefixStepDensity H D μ ref i x)]
  refine Finset.prod_congr rfl ?_
  intro S hS
  refine Finset.prod_congr ?_ (fun i _ => rfl)
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact mem_cComponent_iff_cComponentOf_eq H
    (hD.symm ▸ (H.nodesAt D i).property) hS

private lemma mem_prefixIn_iff_qfactor (H : SWIGGraph N) (D : Finset (SWIGNode N))
    (n : ℕ) (v : SWIGNode N) :
    v ∈ H.prefixIn D n ↔
      ∃ h : v ∈ D, (H.nodeIndex D ⟨v, h⟩).val < n := by
  unfold SWIGGraph.prefixIn
  constructor
  · intro hv
    rcases Finset.mem_filter.mp hv with ⟨hD, hltif⟩
    exact ⟨hD, by simpa [hD] using hltif⟩
  · rintro ⟨hD, hlt⟩
    exact Finset.mem_filter.mpr ⟨hD, by simpa [hD] using hlt⟩

private lemma prefixIn_zero_qfactor (H : SWIGGraph N) (D : Finset (SWIGNode N)) :
    H.prefixIn D 0 = ∅ := by
  ext v
  constructor
  · intro hv
    rcases (mem_prefixIn_iff_qfactor H D 0 v).mp hv with ⟨_, hlt⟩
    omega
  · simp

private lemma nodesAt_mem_prefixIn_iff_qfactor (H : SWIGGraph N)
    (D : Finset (SWIGNode N)) (n : ℕ) (i : Fin D.card) :
    (H.nodesAt D i).val ∈ H.prefixIn D n ↔ i.val < n := by
  rw [mem_prefixIn_iff_qfactor]
  constructor
  · rintro ⟨hD, hlt⟩
    have hidx : H.nodeIndex D ⟨(H.nodesAt D i).val, hD⟩ = i := by
      have hsub :
          (⟨(H.nodesAt D i).val, hD⟩ : {v // v ∈ D}) = H.nodesAt D i :=
        Subtype.ext rfl
      rw [hsub]
      simp [SWIGGraph.nodeIndex, SWIGGraph.nodesAt]
    rwa [hidx] at hlt
  · intro hlt
    exact ⟨(H.nodesAt D i).property,
      by
        have hidx : H.nodeIndex D (H.nodesAt D i) = i := by
          simp [SWIGGraph.nodeIndex, SWIGGraph.nodesAt]
        simpa [hidx] using hlt⟩

private lemma prefixIn_card_qfactor (H : SWIGGraph N) (D : Finset (SWIGNode N)) :
    H.prefixIn D D.card = D := by
  ext v
  constructor
  · exact fun hv => H.prefixIn_subset D D.card hv
  · intro hv
    exact (mem_prefixIn_iff_qfactor H D D.card v).mpr
      ⟨hv, (H.nodeIndex D ⟨v, hv⟩).isLt⟩

private lemma prefixIn_mono_qfactor (H : SWIGGraph N) (D : Finset (SWIGNode N))
    {m k : ℕ} (h : m ≤ k) :
    H.prefixIn D m ⊆ H.prefixIn D k := by
  intro v hv
  rcases (mem_prefixIn_iff_qfactor H D m v).mp hv with ⟨hD, hlt⟩
  exact (mem_prefixIn_iff_qfactor H D k v).mpr ⟨hD, lt_of_lt_of_le hlt h⟩

private lemma prefixIn_succ_qfactor (H : SWIGGraph N) (D : Finset (SWIGNode N))
    {n : ℕ} (hn : n < D.card) :
    H.prefixIn D (n + 1) =
      H.prefixIn D n ∪ {(H.nodesAt D ⟨n, hn⟩).val} := by
  ext v
  constructor
  · intro hv
    rcases (mem_prefixIn_iff_qfactor H D (n + 1) v).mp hv with ⟨hD, hlt⟩
    by_cases hlt_n : (H.nodeIndex D ⟨v, hD⟩).val < n
    · exact Finset.mem_union_left _ ((mem_prefixIn_iff_qfactor H D n v).mpr ⟨hD, hlt_n⟩)
    · have hidx_val : (H.nodeIndex D ⟨v, hD⟩).val = n := by omega
      have hidx : H.nodeIndex D ⟨v, hD⟩ = ⟨n, hn⟩ := Fin.ext hidx_val
      have hv_eq : v = (H.nodesAt D ⟨n, hn⟩).val := by
        have hround : H.nodesAt D (H.nodeIndex D ⟨v, hD⟩) = ⟨v, hD⟩ := by
          simp [SWIGGraph.nodeIndex, SWIGGraph.nodesAt]
        rw [hidx] at hround
        exact congrArg Subtype.val hround.symm
      exact Finset.mem_union_right _ (by simp [hv_eq])
  · intro hv
    rcases Finset.mem_union.mp hv with hvpre | hvlast
    · rcases (mem_prefixIn_iff_qfactor H D n v).mp hvpre with ⟨hD, hlt⟩
      exact (mem_prefixIn_iff_qfactor H D (n + 1) v).mpr ⟨hD, by omega⟩
    · have hv_eq : v = (H.nodesAt D ⟨n, hn⟩).val := by simpa using hvlast
      subst hv_eq
      exact (mem_prefixIn_iff_qfactor H D (n + 1) (H.nodesAt D ⟨n, hn⟩).val).mpr
        ⟨(H.nodesAt D ⟨n, hn⟩).property, by
          have hidx : H.nodeIndex D (H.nodesAt D ⟨n, hn⟩) = ⟨n, hn⟩ := by
            simp [SWIGGraph.nodeIndex, SWIGGraph.nodesAt]
          simp [hidx]⟩

private lemma fixSet_fixed_random_edgeless_qfactor
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (hStd : M.isStandard) :
    ∀ n : N, SWIGNode.fixed n ∈ (M.fixSet X hObs hFix).fixed →
      ∀ v : SWIGNode N, ¬ (M.fixSet X hObs hFix).dag.edge (SWIGNode.random n) v := by
  classical
  intro n hn v
  have hnX : n ∈ X := by
    rw [SCM.fixSet_fixed] at hn
    rcases Finset.mem_union.mp hn with hnM | hnX
    · exfalso
      rw [SCM.isStandard] at hStd
      rw [hStd] at hnM
      simp at hnM
    · rcases Finset.mem_image.mp hnX with ⟨D, hD, hDfix⟩
      cases hDfix
      exact hD
  intro hEdge
  have hEdgeRel :
      SWIGGraph.splitMonoEdgeRel M.toSWIGGraph.dag.edge X
        (SWIGNode.random n) v := by
    simpa [SCM.fixSet, SCM.fixMono, SWIGGraph.splitMono, SWIGGraph.splitMonoDAG]
      using hEdge
  simp [SWIGGraph.splitMonoEdgeRel, hnX] at hEdgeRel

private lemma qLocalMass_ne_top_qfactor
    (M : Causalean.SCM N Ω) (s : M.FixedValues)
    (T : Finset (SWIGNode N)) (hT : T ⊆ M.observed)
    (x : ValuesOn M.observed (swigΩ Ω)) :
    M.qLocalMass s T hT x ≠ ∞ := by
  exact ne_of_lt (MeasureTheory.measure_lt_top M.latentProduct _)

private lemma prefixIn_parent_closed_induce_observed
    (M : Causalean.SCM N Ω) (A : Finset (SWIGNode N)) (hA : A ⊆ M.observed)
    (k : ℕ) :
    ∀ v ∈ A, ∀ w ∈ (M.toSWIGGraph.induce A).prefixIn A k,
      M.dag.edge v w → v ∈ (M.toSWIGGraph.induce A).prefixIn A k := by
  classical
  intro v hvA w hwPre hEdge
  let H := M.toSWIGGraph.induce A
  have hwA : w ∈ A := H.prefixIn_subset A k hwPre
  have hEdgeH : H.dag.edge v w := by
    dsimp [H, SWIGGraph.induce]
    rw [SWIGGraph.inducedDag_edge_iff]
    refine ⟨hEdge, ?_, ?_⟩
    · simp [hvA, hA hvA]
    · simp [hwA, hA hwA]
  have hTopo : H.dag.topoOrder v < H.dag.topoOrder w :=
    H.dag.topoOrder_lt v w hEdgeH
  rcases (mem_prefixIn_iff_qfactor H A k w).mp hwPre with ⟨hwA', hwIdxLt⟩
  letI := H.topoLinearOrder
  have hSubtypeLt : (⟨v, hvA⟩ : {v // v ∈ A}) < ⟨w, hwA'⟩ := by
    change H.dag.topoOrder v < H.dag.topoOrder w
    exact hTopo
  have hIndexLt :
      (H.nodeIndex A ⟨v, hvA⟩).val < (H.nodeIndex A ⟨w, hwA'⟩).val := by
    have hIndexLtFin : H.nodeIndex A ⟨v, hvA⟩ < H.nodeIndex A ⟨w, hwA'⟩ := by
      simpa [SWIGGraph.nodeIndex] using
        ((A.orderIsoOfFin rfl).symm.strictMono hSubtypeLt)
    simpa [SWIGGraph.nodeIndex] using hIndexLtFin
  exact (mem_prefixIn_iff_qfactor H A k v).mpr
    ⟨hvA, lt_trans hIndexLt hwIdxLt⟩

private lemma qLocalMass_prefixIn_eq_prod_induce_components
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (s : M.FixedValues)
    (A : Finset (SWIGNode N)) (hA : A ⊆ M.observed)
    (k : ℕ) (x : ValuesOn M.observed (swigΩ Ω)) :
    let H := M.toSWIGGraph.induce A
    M.qLocalMass s (H.prefixIn A k)
        (fun _ hv => hA (H.prefixIn_subset A k hv)) x =
      ∏ C ∈ H.cComponentSet,
        M.qLocalMass s (C ∩ H.prefixIn A k)
          (fun _ hv => hA (H.prefixIn_subset A k
            (Finset.mem_of_mem_inter_right hv))) x := by
  classical
  let H := M.toSWIGGraph.induce A
  have hHobs : H.observed = A := by
    simp [H, SWIGGraph.induce, Finset.inter_eq_left.mpr hA]
  have h𝒞obs : ∀ U ∈ H.cComponentSet, U ⊆ M.observed := by
    intro U hU v hv
    exact hA (hHobs ▸ H.cComponentSet_subset_observed U hU hv)
  have hcover : H.prefixIn A k ⊆ H.cComponentSet.sup id := by
    intro v hv
    have hvObs : v ∈ H.observed := by
      rw [hHobs]
      exact H.prefixIn_subset A k hv
    rw [Finset.mem_sup]
    exact ⟨H.cComponentOf v,
      (by
        rw [SWIGGraph.cComponentSet, Finset.mem_image]
        exact ⟨v, hvObs, rfl⟩),
      H.mem_cComponentOf_self hvObs⟩
  have hblock :
      (↑H.cComponentSet : Set (Finset (SWIGNode N))).Pairwise
        (fun U U' => Disjoint (M.latentBlock U) (M.latentBlock U')) := by
    intro U hU V hV hne
    exact latentBlock_pairwise_disjoint_induce_components M A hU hV hne
  have hnode :
      (↑H.cComponentSet : Set (Finset (SWIGNode N))).Pairwise
        (fun U U' => Disjoint U U') := by
    intro U hU V hV hne
    exact H.cComponentSet_pairwise_disjoint hU hV hne
  have hfac :=
    M.qLocalMass_prod_inter_of_latentBlock_disjoint s
      (H.prefixIn A k) (fun _ hv => hA (H.prefixIn_subset A k hv))
      H.cComponentSet h𝒞obs hcover hblock hnode x
  calc
    M.qLocalMass s (H.prefixIn A k)
        (fun _ hv => hA (H.prefixIn_subset A k hv)) x =
      ∏ C ∈ H.cComponentSet,
        if hC : C ∈ H.cComponentSet then
          M.qLocalMass s (C ∩ H.prefixIn A k)
            (fun _ hv => h𝒞obs C hC (Finset.mem_of_mem_inter_left hv)) x
        else 1 := by
          simpa [H] using hfac
    _ =
      ∏ C ∈ H.cComponentSet,
        M.qLocalMass s (C ∩ H.prefixIn A k)
          (fun _ hv => hA (H.prefixIn_subset A k
            (Finset.mem_of_mem_inter_right hv))) x := by
          refine Finset.prod_congr rfl ?_
          intro C hC
          simp [hC]

private lemma ENNReal.div_mul_common_qfactor
    {a b r : ENNReal} (hr0 : r ≠ 0) (hrtop : r ≠ ∞) :
    (a * r) / (b * r) = a / b := by
  rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
  rw [ENNReal.mul_inv]
  · rw [show b⁻¹ * r⁻¹ * (a * r) = (r⁻¹ * r) * (b⁻¹ * a) by ac_rfl]
    rw [ENNReal.inv_mul_cancel hr0 hrtop]
    simp [mul_comm]
  · exact Or.inr hrtop
  · exact Or.inr hr0

private lemma Finset.prod_ne_top_of_ne_top_qfactor {ι : Type*}
    (s : Finset ι) (f : ι → ENNReal) (hf : ∀ i ∈ s, f i ≠ ∞) :
    (∏ i ∈ s, f i) ≠ ∞ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      exact ENNReal.mul_ne_top (hf a (Finset.mem_insert_self a s))
        (ih (by intro i hi; exact hf i (Finset.mem_insert_of_mem hi)))

private lemma ENNReal.prod_div_prod_qfactor {ι : Type*}
    (t : Finset ι) (f g : ι → ENNReal)
    (hg0 : ∀ i ∈ t, g i ≠ 0) (hgtop : ∀ i ∈ t, g i ≠ ∞) :
    (∏ i ∈ t, f i / g i) = (∏ i ∈ t, f i) / (∏ i ∈ t, g i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
      have ih' :
          (∏ i ∈ t, f i / g i) = (∏ i ∈ t, f i) / (∏ i ∈ t, g i) :=
        ih (by intro i hi; exact hg0 i (Finset.mem_insert_of_mem hi))
          (by intro i hi; exact hgtop i (Finset.mem_insert_of_mem hi))
      have hprod0 : (∏ i ∈ t, g i) ≠ 0 := by
        exact Finset.prod_ne_zero_iff.mpr (by
          intro i hi
          exact hg0 i (Finset.mem_insert_of_mem hi))
      have hprodtop : (∏ i ∈ t, g i) ≠ ∞ := by
        exact Finset.prod_ne_top_of_ne_top_qfactor _ g (by
          intro i hi
          exact hgtop i (Finset.mem_insert_of_mem hi))
      rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.prod_insert ha, ih']
      rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
      rw [ENNReal.mul_inv]
      · ac_rfl
      · exact Or.inr hprodtop
      · exact Or.inr hprod0

private lemma ENNReal.prod_div_prod₂_qfactor {ι : Type*}
    (t : Finset ι) (f g h : ι → ENNReal)
    (hh0 : ∀ i ∈ t, h i ≠ 0) (hhtop : ∀ i ∈ t, h i ≠ ∞) :
    (∏ i ∈ t, (f i / g i) / h i) =
      (∏ i ∈ t, f i / g i) / (∏ i ∈ t, h i) := by
  exact ENNReal.prod_div_prod_qfactor t (fun i => f i / g i) h hh0 hhtop

private lemma mechCFactor_eq_qLocalMass_div_jointRef_qfactor
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (ref : ReferenceMeasures Ω) (s : M.FixedValues)
    (S : Finset (SWIGNode N)) (hS : S ⊆ M.observed)
    (href : Causalean.SCM.ReferenceFaithful ref)
    (hfe : ∀ n : N, SWIGNode.fixed n ∈ M.fixed →
      ∀ v : SWIGNode N, ¬ M.dag.edge (SWIGNode.random n) v)
    (x : ValuesOn M.observed (swigΩ Ω)) :
    M.mechCFactor ref S hS s x =
      M.qLocalMass s S hS x /
        jointRef ref S ({valuesProjection hS x} :
          Set (ValuesOn S (swigΩ Ω))) := by
  have hnum :
      QmechMeasure M S hS (M.mechDoValues S s x) {valuesProjection hS x}
        = M.qLocalMass s S hS x :=
    QmechMeasure_singleton_eq_qLocalMass M S hS hfe s x
  have hden0 :
      jointRef ref S ({valuesProjection hS x} :
        Set (ValuesOn S (swigΩ Ω))) ≠ 0 :=
    jointRef_singleton_ne_zero ref href S (valuesProjection hS x)
  have hdenTop :
      jointRef ref S ({valuesProjection hS x} :
        Set (ValuesOn S (swigΩ Ω))) ≠ ∞ := by
    exact ne_of_lt (MeasureTheory.measure_lt_top (jointRef ref S)
      ({valuesProjection hS x} : Set (ValuesOn S (swigΩ Ω))))
  unfold mechCFactor
  rw [rnDeriv_singleton_eq_div _ _
      (absolutelyContinuous_jointRef_of_faithful ref href S
        (QmechMeasure M S hS (M.mechDoValues S s x)))
      (valuesProjection hS x) hden0 hdenTop]
  rw [hnum]

private lemma cComponent_inter_prefixIn_succ_eq_of_ne
    (M : Causalean.SCM N Ω) (H : SWIGGraph N) (D : Finset (SWIGNode N))
    {S C : Finset (SWIGNode N)}
    (hScomp : S ∈ M.toSWIGGraph.cComponentSet)
    (hCcomp : C ∈ M.toSWIGGraph.cComponentSet)
    {i : Fin D.card}
    (hDobs : D ⊆ M.observed)
    (hiS : (H.nodesAt D i).val ∈ S)
    (hCS : C ≠ S) :
    C ∩ H.prefixIn D (i.val + 1) = C ∩ H.prefixIn D i.val := by
  classical
  ext v
  constructor
  · intro hv
    rcases Finset.mem_inter.mp hv with ⟨hvC, hvpre⟩
    rw [prefixIn_succ_qfactor H D i.isLt] at hvpre
    rcases Finset.mem_union.mp hvpre with hvold | hvnew
    · exact Finset.mem_inter.mpr ⟨hvC, hvold⟩
    · have hvnode : v = (H.nodesAt D i).val := by simpa using hvnew
      subst hvnode
      have hnodeObs : (H.nodesAt D i).val ∈ M.observed :=
        hDobs (H.nodesAt D i).property
      have hSC : S = C := by
        exact (mem_cComponent_iff_cComponentOf_eq M.toSWIGGraph
          hnodeObs hCcomp).mp hvC ▸
          ((mem_cComponent_iff_cComponentOf_eq M.toSWIGGraph
            hnodeObs hScomp).mp hiS).symm
      exact False.elim (hCS hSC.symm)
  · intro hv
    rcases Finset.mem_inter.mp hv with ⟨hvC, hvpre⟩
    exact Finset.mem_inter.mpr
      ⟨hvC, prefixIn_mono_qfactor H D (Nat.le_succ i.val) hvpre⟩

private lemma family_inter_prefixIn_succ_eq_of_ne
    (H : SWIGGraph N) (D : Finset (SWIGNode N))
    {S C : Finset (SWIGNode N)} {i : Fin D.card}
    (hiS : (H.nodesAt D i).val ∈ S)
    (hdisj : Disjoint C S) :
    C ∩ H.prefixIn D (i.val + 1) = C ∩ H.prefixIn D i.val := by
  classical
  ext v
  constructor
  · intro hv
    rcases Finset.mem_inter.mp hv with ⟨hvC, hvpre⟩
    rw [prefixIn_succ_qfactor H D i.isLt] at hvpre
    rcases Finset.mem_union.mp hvpre with hvold | hvnew
    · exact Finset.mem_inter.mpr ⟨hvC, hvold⟩
    · have hvnode : v = (H.nodesAt D i).val := by simpa using hvnew
      subst hvnode
      exact False.elim (Finset.disjoint_left.mp hdisj hvC hiS)
  · intro hv
    rcases Finset.mem_inter.mp hv with ⟨hvC, hvpre⟩
    exact Finset.mem_inter.mpr
      ⟨hvC, prefixIn_mono_qfactor H D (Nat.le_succ i.val) hvpre⟩

private lemma cComponent_inter_prefixIn_succ_eq_of_node_not_mem
    (H : SWIGGraph N) (D : Finset (SWIGNode N))
    {S : Finset (SWIGNode N)} {i : Fin D.card}
    (hiS : (H.nodesAt D i).val ∉ S) :
    S ∩ H.prefixIn D (i.val + 1) = S ∩ H.prefixIn D i.val := by
  classical
  ext v
  constructor
  · intro hv
    rcases Finset.mem_inter.mp hv with ⟨hvS, hvpre⟩
    rw [prefixIn_succ_qfactor H D i.isLt] at hvpre
    rcases Finset.mem_union.mp hvpre with hvold | hvnew
    · exact Finset.mem_inter.mpr ⟨hvS, hvold⟩
    · have hvnode : v = (H.nodesAt D i).val := by simpa using hvnew
      subst hvnode
      exact False.elim (hiS hvS)
  · intro hv
    rcases Finset.mem_inter.mp hv with ⟨hvS, hvpre⟩
    exact Finset.mem_inter.mpr
      ⟨hvS, prefixIn_mono_qfactor H D (Nat.le_succ i.val) hvpre⟩

/-- In a product over an abstract pairwise-disjoint family, the prefix-ratio
step at a node of `S` cancels every factor except the `S` factor. -/
lemma prefixIn_qProduct_ratio_eq_component_ratio_of_family
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (H : SWIGGraph N) (D : Finset (SWIGNode N))
    (s : M.FixedValues)
    (𝒞 : Finset (Finset (SWIGNode N))) (S : Finset (SWIGNode N))
    (hS𝒞 : S ∈ 𝒞)
    (hdisj : (↑𝒞 : Set (Finset (SWIGNode N))).Pairwise (fun U U' => Disjoint U U'))
    (i : Fin D.card) (hDobs : D ⊆ M.observed)
    (hiS : (H.nodesAt D i).val ∈ S)
    (hpos : DiscreteID.PositiveMass (M.obsKernel s))
    (x : ValuesOn M.observed (swigΩ Ω)) :
    (∏ C ∈ 𝒞,
        M.qLocalMass s (C ∩ H.prefixIn D (i.val + 1))
          (fun _ hv => hDobs (H.prefixIn_subset D (i.val + 1)
            (Finset.mem_of_mem_inter_right hv))) x) /
      (∏ C ∈ 𝒞,
        M.qLocalMass s (C ∩ H.prefixIn D i.val)
          (fun _ hv => hDobs (H.prefixIn_subset D i.val
            (Finset.mem_of_mem_inter_right hv))) x)
      =
    M.qLocalMass s (S ∩ H.prefixIn D (i.val + 1))
        (fun _ hv => hDobs (H.prefixIn_subset D (i.val + 1)
          (Finset.mem_of_mem_inter_right hv))) x /
      M.qLocalMass s (S ∩ H.prefixIn D i.val)
        (fun _ hv => hDobs (H.prefixIn_subset D i.val
          (Finset.mem_of_mem_inter_right hv))) x := by
  classical
  let f₁ : Finset (SWIGNode N) → ENNReal := fun C =>
    M.qLocalMass s (C ∩ H.prefixIn D (i.val + 1))
      (fun _ hv => hDobs (H.prefixIn_subset D (i.val + 1)
        (Finset.mem_of_mem_inter_right hv))) x
  let f₀ : Finset (SWIGNode N) → ENNReal := fun C =>
    M.qLocalMass s (C ∩ H.prefixIn D i.val)
      (fun _ hv => hDobs (H.prefixIn_subset D i.val
        (Finset.mem_of_mem_inter_right hv))) x
  have hrest :
      ∏ C ∈ 𝒞 \ {S}, f₁ C =
        ∏ C ∈ 𝒞 \ {S}, f₀ C := by
    refine Finset.prod_congr rfl ?_
    intro C hC
    have hC𝒞 : C ∈ 𝒞 := (Finset.mem_sdiff.mp hC).1
    have hCne : C ≠ S := by
      intro h
      exact (Finset.mem_sdiff.mp hC).2 (by simp [h])
    simp [f₁, f₀,
      family_inter_prefixIn_succ_eq_of_ne H D hiS (hdisj hC𝒞 hS𝒞 hCne)]
  have hsplit₁ : (∏ C ∈ 𝒞, f₁ C) =
      f₁ S * ∏ C ∈ 𝒞 \ {S}, f₁ C := by
    exact Finset.prod_eq_mul_prod_diff_singleton S f₁
      (by intro h; exact False.elim (h hS𝒞))
  have hsplit₀ : (∏ C ∈ 𝒞, f₀ C) =
      f₀ S * ∏ C ∈ 𝒞 \ {S}, f₀ C := by
    exact Finset.prod_eq_mul_prod_diff_singleton S f₀
      (by intro h; exact False.elim (h hS𝒞))
  have hr0 : (∏ C ∈ 𝒞 \ {S}, f₀ C) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr (by
      intro C _hC
      exact M.qLocalMass_pos_of_positiveObs s hpos (C ∩ H.prefixIn D i.val)
        (fun _ hv => hDobs (H.prefixIn_subset D i.val
          (Finset.mem_of_mem_inter_right hv))) x)
  have hrtop : (∏ C ∈ 𝒞 \ {S}, f₀ C) ≠ ∞ := by
    exact Finset.prod_ne_top_of_ne_top_qfactor _ f₀ (by
      intro C _hC
      exact qLocalMass_ne_top_qfactor M s (C ∩ H.prefixIn D i.val)
        (fun _ hv => hDobs (H.prefixIn_subset D i.val
          (Finset.mem_of_mem_inter_right hv))) x)
  change (∏ C ∈ 𝒞, f₁ C) / (∏ C ∈ 𝒞, f₀ C) = f₁ S / f₀ S
  rw [hsplit₁, hsplit₀, hrest]
  exact ENNReal.div_mul_common_qfactor hr0 hrtop

private lemma prefixIn_qProduct_ratio_eq_component_ratio_of_ne_zero
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (H : SWIGGraph N) (D : Finset (SWIGNode N))
    (s : M.FixedValues)
    (S : Finset (SWIGNode N)) (hScomp : S ∈ M.toSWIGGraph.cComponentSet)
    (i : Fin D.card) (hDobs : D ⊆ M.observed)
    (hiS : (H.nodesAt D i).val ∈ S)
    (x : ValuesOn M.observed (swigΩ Ω))
    (hrest0 :
      (∏ C ∈ M.toSWIGGraph.cComponentSet \ {S},
        M.qLocalMass s (C ∩ H.prefixIn D i.val)
          (fun _ hv => hDobs (H.prefixIn_subset D i.val
            (Finset.mem_of_mem_inter_right hv))) x) ≠ 0) :
    (∏ C ∈ M.toSWIGGraph.cComponentSet,
        M.qLocalMass s (C ∩ H.prefixIn D (i.val + 1))
          (fun _ hv => hDobs (H.prefixIn_subset D (i.val + 1)
            (Finset.mem_of_mem_inter_right hv))) x) /
      (∏ C ∈ M.toSWIGGraph.cComponentSet,
        M.qLocalMass s (C ∩ H.prefixIn D i.val)
          (fun _ hv => hDobs (H.prefixIn_subset D i.val
            (Finset.mem_of_mem_inter_right hv))) x)
      =
    M.qLocalMass s (S ∩ H.prefixIn D (i.val + 1))
        (fun _ hv => hDobs (H.prefixIn_subset D (i.val + 1)
          (Finset.mem_of_mem_inter_right hv))) x /
      M.qLocalMass s (S ∩ H.prefixIn D i.val)
        (fun _ hv => hDobs (H.prefixIn_subset D i.val
          (Finset.mem_of_mem_inter_right hv))) x := by
  classical
  let f₁ : Finset (SWIGNode N) → ENNReal := fun C =>
    M.qLocalMass s (C ∩ H.prefixIn D (i.val + 1))
      (fun _ hv => hDobs (H.prefixIn_subset D (i.val + 1)
        (Finset.mem_of_mem_inter_right hv))) x
  let f₀ : Finset (SWIGNode N) → ENNReal := fun C =>
    M.qLocalMass s (C ∩ H.prefixIn D i.val)
      (fun _ hv => hDobs (H.prefixIn_subset D i.val
        (Finset.mem_of_mem_inter_right hv))) x
  have hrest :
      ∏ C ∈ M.toSWIGGraph.cComponentSet \ {S}, f₁ C =
        ∏ C ∈ M.toSWIGGraph.cComponentSet \ {S}, f₀ C := by
    refine Finset.prod_congr rfl ?_
    intro C hC
    have hCcomp : C ∈ M.toSWIGGraph.cComponentSet := (Finset.mem_sdiff.mp hC).1
    have hCne : C ≠ S := by
      intro h
      exact (Finset.mem_sdiff.mp hC).2 (by simp [h])
    simp [f₁, f₀,
      cComponent_inter_prefixIn_succ_eq_of_ne M H D hScomp hCcomp hDobs hiS hCne]
  have hsplit₁ : (∏ C ∈ M.toSWIGGraph.cComponentSet, f₁ C) =
      f₁ S * ∏ C ∈ M.toSWIGGraph.cComponentSet \ {S}, f₁ C := by
    exact Finset.prod_eq_mul_prod_diff_singleton S f₁
      (by intro h; exact False.elim (h hScomp))
  have hsplit₀ : (∏ C ∈ M.toSWIGGraph.cComponentSet, f₀ C) =
      f₀ S * ∏ C ∈ M.toSWIGGraph.cComponentSet \ {S}, f₀ C := by
    exact Finset.prod_eq_mul_prod_diff_singleton S f₀
      (by intro h; exact False.elim (h hScomp))
  have hrtop : (∏ C ∈ M.toSWIGGraph.cComponentSet \ {S}, f₀ C) ≠ ∞ := by
    exact Finset.prod_ne_top_of_ne_top_qfactor _ f₀ (by
      intro C _hC
      exact qLocalMass_ne_top_qfactor M s (C ∩ H.prefixIn D i.val)
        (fun _ hv => hDobs (H.prefixIn_subset D i.val
          (Finset.mem_of_mem_inter_right hv))) x)
  change (∏ C ∈ M.toSWIGGraph.cComponentSet, f₁ C) /
      (∏ C ∈ M.toSWIGGraph.cComponentSet, f₀ C) = f₁ S / f₀ S
  rw [hsplit₁, hsplit₀, hrest]
  exact ENNReal.div_mul_common_qfactor hrest0 hrtop

/-- Nonzero-denominator variant of
`prefixIn_qProduct_ratio_eq_component_ratio_of_family`. -/
lemma prefixIn_qProduct_ratio_eq_component_ratio_of_family_of_ne_zero
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (H : SWIGGraph N) (D : Finset (SWIGNode N))
    (s : M.FixedValues)
    (𝒞 : Finset (Finset (SWIGNode N))) (S : Finset (SWIGNode N))
    (hS𝒞 : S ∈ 𝒞)
    (hdisj : (↑𝒞 : Set (Finset (SWIGNode N))).Pairwise (fun U U' => Disjoint U U'))
    (i : Fin D.card) (hDobs : D ⊆ M.observed)
    (hiS : (H.nodesAt D i).val ∈ S)
    (x : ValuesOn M.observed (swigΩ Ω))
    (hrest0 :
      (∏ C ∈ 𝒞 \ {S},
        M.qLocalMass s (C ∩ H.prefixIn D i.val)
          (fun _ hv => hDobs (H.prefixIn_subset D i.val
            (Finset.mem_of_mem_inter_right hv))) x) ≠ 0) :
    (∏ C ∈ 𝒞,
        M.qLocalMass s (C ∩ H.prefixIn D (i.val + 1))
          (fun _ hv => hDobs (H.prefixIn_subset D (i.val + 1)
            (Finset.mem_of_mem_inter_right hv))) x) /
      (∏ C ∈ 𝒞,
        M.qLocalMass s (C ∩ H.prefixIn D i.val)
          (fun _ hv => hDobs (H.prefixIn_subset D i.val
            (Finset.mem_of_mem_inter_right hv))) x)
      =
    M.qLocalMass s (S ∩ H.prefixIn D (i.val + 1))
        (fun _ hv => hDobs (H.prefixIn_subset D (i.val + 1)
          (Finset.mem_of_mem_inter_right hv))) x /
      M.qLocalMass s (S ∩ H.prefixIn D i.val)
        (fun _ hv => hDobs (H.prefixIn_subset D i.val
          (Finset.mem_of_mem_inter_right hv))) x := by
  classical
  let f₁ : Finset (SWIGNode N) → ENNReal := fun C =>
    M.qLocalMass s (C ∩ H.prefixIn D (i.val + 1))
      (fun _ hv => hDobs (H.prefixIn_subset D (i.val + 1)
        (Finset.mem_of_mem_inter_right hv))) x
  let f₀ : Finset (SWIGNode N) → ENNReal := fun C =>
    M.qLocalMass s (C ∩ H.prefixIn D i.val)
      (fun _ hv => hDobs (H.prefixIn_subset D i.val
        (Finset.mem_of_mem_inter_right hv))) x
  have hrest :
      ∏ C ∈ 𝒞 \ {S}, f₁ C =
        ∏ C ∈ 𝒞 \ {S}, f₀ C := by
    refine Finset.prod_congr rfl ?_
    intro C hC
    have hC𝒞 : C ∈ 𝒞 := (Finset.mem_sdiff.mp hC).1
    have hCne : C ≠ S := by
      intro h
      exact (Finset.mem_sdiff.mp hC).2 (by simp [h])
    simp [f₁, f₀,
      family_inter_prefixIn_succ_eq_of_ne H D hiS (hdisj hC𝒞 hS𝒞 hCne)]
  have hsplit₁ : (∏ C ∈ 𝒞, f₁ C) =
      f₁ S * ∏ C ∈ 𝒞 \ {S}, f₁ C := by
    exact Finset.prod_eq_mul_prod_diff_singleton S f₁
      (by intro h; exact False.elim (h hS𝒞))
  have hsplit₀ : (∏ C ∈ 𝒞, f₀ C) =
      f₀ S * ∏ C ∈ 𝒞 \ {S}, f₀ C := by
    exact Finset.prod_eq_mul_prod_diff_singleton S f₀
      (by intro h; exact False.elim (h hS𝒞))
  have hrtop : (∏ C ∈ 𝒞 \ {S}, f₀ C) ≠ ∞ := by
    exact Finset.prod_ne_top_of_ne_top_qfactor _ f₀ (by
      intro C _hC
      exact qLocalMass_ne_top_qfactor M s (C ∩ H.prefixIn D i.val)
        (fun _ hv => hDobs (H.prefixIn_subset D i.val
          (Finset.mem_of_mem_inter_right hv))) x)
  change (∏ C ∈ 𝒞, f₁ C) / (∏ C ∈ 𝒞, f₀ C) = f₁ S / f₀ S
  rw [hsplit₁, hsplit₀, hrest]
  exact ENNReal.div_mul_common_qfactor hrest0 hrtop

private lemma component_qLocalMass_ratio_product_prefixIn
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (H : SWIGGraph N) (D : Finset (SWIGNode N))
    (s : M.FixedValues)
    (S : Finset (SWIGNode N)) (hS : S ⊆ M.observed) (hSD : S ⊆ D)
    (hpos : DiscreteID.PositiveMass (M.obsKernel s))
    (x : ValuesOn M.observed (swigΩ Ω)) :
    (∏ i ∈ Finset.univ.filter (fun i : Fin D.card => (H.nodesAt D i).val ∈ S),
      M.qLocalMass s (S ∩ H.prefixIn D (i.val + 1))
        (fun _ hv => hS (Finset.mem_of_mem_inter_left hv)) x /
      M.qLocalMass s (S ∩ H.prefixIn D i.val)
        (fun _ hv => hS (Finset.mem_of_mem_inter_left hv)) x)
      = M.qLocalMass s S hS x := by
  classical
  let hPrefObs : ∀ k, S ∩ H.prefixIn D k ⊆ M.observed := fun k _ hv =>
    hS (Finset.mem_of_mem_inter_left hv)
  let a : ℕ → ENNReal := fun k =>
    M.qLocalMass s (S ∩ H.prefixIn D k) (hPrefObs k) x
  let T : Finset ℕ := (Finset.range D.card).filter fun k =>
    if hk : k < D.card then (H.nodesAt D ⟨k, hk⟩).val ∈ S else False
  have hreindex :
      (∏ i ∈ Finset.univ.filter (fun i : Fin D.card => (H.nodesAt D i).val ∈ S),
        a (i.val + 1) / a i.val)
        = ∏ k ∈ T, a (k + 1) / a k := by
    refine Finset.prod_bij (fun i _hi => i.val) ?_ ?_ ?_ ?_
    · intro i hi
      simp [T, i.isLt, Finset.mem_filter.mp hi]
    · intro i _hi j _hj hij
      exact Fin.ext hij
    · intro k hk
      simp [T] at hk
      have hklt : k < D.card := hk.1
      refine ⟨⟨k, hklt⟩, ?_, rfl⟩
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by simpa [hklt] using hk.2⟩
    · intro i _hi
      rfl
  have hTsubset : T ⊆ Finset.range D.card := by
    intro k hk
    exact (Finset.mem_filter.mp hk).1
  have hne : ∀ k ≤ D.card, a k ≠ 0 := by
    intro k hk
    exact M.qLocalMass_pos_of_positiveObs s hpos (S ∩ H.prefixIn D k) (hPrefObs k) x
  have hfin : ∀ k ≤ D.card, a k ≠ ∞ := by
    intro k hk
    exact qLocalMass_ne_top_qfactor M s (S ∩ H.prefixIn D k) (hPrefObs k) x
  have hconst : ∀ k < D.card, k ∉ T → a (k + 1) = a k := by
    intro k hk hnot
    have hnode_not :
        (H.nodesAt D ⟨k, hk⟩).val ∉ S := by
      intro hnode
      exact hnot (by simp [T, hk, hnode])
    dsimp [a]
    have hset :
        S ∩ H.prefixIn D (k + 1) = S ∩ H.prefixIn D k :=
      cComponent_inter_prefixIn_succ_eq_of_node_not_mem H D hnode_not
    unfold qLocalMass
    congr 1
    ext ℓ
    constructor
    · intro hℓ v hv
      have hv' : v ∈ S ∩ H.prefixIn D (k + 1) := by
        simpa [hset] using hv
      simpa using hℓ v hv'
    · intro hℓ v hv
      have hv' : v ∈ S ∩ H.prefixIn D k := by
        simpa [hset] using hv
      simpa using hℓ v hv'
  have htelescope :
      ∏ k ∈ T, a (k + 1) / a k = a D.card / a 0 :=
    prod_filter_div_telescope a D.card T hTsubset hne hfin hconst
  have htop : S ∩ H.prefixIn D D.card = S := by
    rw [prefixIn_card_qfactor H D]
    exact Finset.inter_eq_left.mpr hSD
  have hzero : S ∩ H.prefixIn D 0 = ∅ := by
    rw [prefixIn_zero_qfactor H D, Finset.inter_empty]
  calc
    (∏ i ∈ Finset.univ.filter (fun i : Fin D.card => (H.nodesAt D i).val ∈ S),
      M.qLocalMass s (S ∩ H.prefixIn D (i.val + 1))
        (fun _ hv => hS (Finset.mem_of_mem_inter_left hv)) x /
      M.qLocalMass s (S ∩ H.prefixIn D i.val)
        (fun _ hv => hS (Finset.mem_of_mem_inter_left hv)) x)
        = ∏ i ∈ Finset.univ.filter (fun i : Fin D.card => (H.nodesAt D i).val ∈ S),
          a (i.val + 1) / a i.val := by rfl
    _ = ∏ k ∈ T, a (k + 1) / a k := hreindex
    _ = a D.card / a 0 := htelescope
    _ = M.qLocalMass s S hS x / 1 := by
          simp [a, htop, hzero]
    _ = M.qLocalMass s S hS x := by
          simp

private lemma component_qLocalMass_ratio_product_prefixIn_of_ne_zero
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (H : SWIGGraph N) (D : Finset (SWIGNode N))
    (s : M.FixedValues)
    (S : Finset (SWIGNode N)) (hS : S ⊆ M.observed) (hSD : S ⊆ D)
    (x : ValuesOn M.observed (swigΩ Ω))
    (hne : ∀ k ≤ D.card,
      M.qLocalMass s (S ∩ H.prefixIn D k)
        (fun _ hv => hS (Finset.mem_of_mem_inter_left hv)) x ≠ 0) :
    (∏ i ∈ Finset.univ.filter (fun i : Fin D.card => (H.nodesAt D i).val ∈ S),
      M.qLocalMass s (S ∩ H.prefixIn D (i.val + 1))
        (fun _ hv => hS (Finset.mem_of_mem_inter_left hv)) x /
      M.qLocalMass s (S ∩ H.prefixIn D i.val)
        (fun _ hv => hS (Finset.mem_of_mem_inter_left hv)) x)
      = M.qLocalMass s S hS x := by
  classical
  let hPrefObs : ∀ k, S ∩ H.prefixIn D k ⊆ M.observed := fun k _ hv =>
    hS (Finset.mem_of_mem_inter_left hv)
  let a : ℕ → ENNReal := fun k =>
    M.qLocalMass s (S ∩ H.prefixIn D k) (hPrefObs k) x
  let T : Finset ℕ := (Finset.range D.card).filter fun k =>
    if hk : k < D.card then (H.nodesAt D ⟨k, hk⟩).val ∈ S else False
  have hreindex :
      (∏ i ∈ Finset.univ.filter (fun i : Fin D.card => (H.nodesAt D i).val ∈ S),
        a (i.val + 1) / a i.val)
        = ∏ k ∈ T, a (k + 1) / a k := by
    refine Finset.prod_bij (fun i _hi => i.val) ?_ ?_ ?_ ?_
    · intro i hi
      simp [T, i.isLt, Finset.mem_filter.mp hi]
    · intro i _hi j _hj hij
      exact Fin.ext hij
    · intro k hk
      simp [T] at hk
      have hklt : k < D.card := hk.1
      refine ⟨⟨k, hklt⟩, ?_, rfl⟩
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by simpa [hklt] using hk.2⟩
    · intro i _hi
      rfl
  have hTsubset : T ⊆ Finset.range D.card := by
    intro k hk
    exact (Finset.mem_filter.mp hk).1
  have hne' : ∀ k ≤ D.card, a k ≠ 0 := by
    intro k hk
    exact hne k hk
  have hfin : ∀ k ≤ D.card, a k ≠ ∞ := by
    intro k hk
    exact qLocalMass_ne_top_qfactor M s (S ∩ H.prefixIn D k) (hPrefObs k) x
  have hconst : ∀ k < D.card, k ∉ T → a (k + 1) = a k := by
    intro k hk hnot
    have hnode_not :
        (H.nodesAt D ⟨k, hk⟩).val ∉ S := by
      intro hnode
      exact hnot (by simp [T, hk, hnode])
    dsimp [a]
    have hset :
        S ∩ H.prefixIn D (k + 1) = S ∩ H.prefixIn D k :=
      cComponent_inter_prefixIn_succ_eq_of_node_not_mem H D hnode_not
    unfold qLocalMass
    congr 1
    ext ℓ
    constructor
    · intro hℓ v hv
      have hv' : v ∈ S ∩ H.prefixIn D (k + 1) := by
        simpa [hset] using hv
      simpa using hℓ v hv'
    · intro hℓ v hv
      have hv' : v ∈ S ∩ H.prefixIn D k := by
        simpa [hset] using hv
      simpa using hℓ v hv'
  have htelescope :
      ∏ k ∈ T, a (k + 1) / a k = a D.card / a 0 :=
    prod_filter_div_telescope a D.card T hTsubset hne' hfin hconst
  have htop : S ∩ H.prefixIn D D.card = S := by
    rw [prefixIn_card_qfactor H D]
    exact Finset.inter_eq_left.mpr hSD
  have hzero : S ∩ H.prefixIn D 0 = ∅ := by
    rw [prefixIn_zero_qfactor H D, Finset.inter_empty]
  calc
    (∏ i ∈ Finset.univ.filter (fun i : Fin D.card => (H.nodesAt D i).val ∈ S),
      M.qLocalMass s (S ∩ H.prefixIn D (i.val + 1))
        (fun _ hv => hS (Finset.mem_of_mem_inter_left hv)) x /
      M.qLocalMass s (S ∩ H.prefixIn D i.val)
        (fun _ hv => hS (Finset.mem_of_mem_inter_left hv)) x)
        = ∏ i ∈ Finset.univ.filter (fun i : Fin D.card => (H.nodesAt D i).val ∈ S),
          a (i.val + 1) / a i.val := by rfl
    _ = ∏ k ∈ T, a (k + 1) / a k := hreindex
    _ = a D.card / a 0 := htelescope
    _ = M.qLocalMass s S hS x / 1 := by
          simp [a, htop, hzero]
    _ = M.qLocalMass s S hS x := by
          simp

/-- Extracting an induced district from the local mass on an ancestral set
recovers that district's local q-mass. -/
lemma extractDistrict_qLocalMass
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (s : M.FixedValues)
    (A C' : Finset (SWIGNode N)) (hA : A ⊆ M.observed)
    (hC' : C' ∈ (M.toSWIGGraph.induce A).cComponentSet)
    (hpos : DiscreteID.PositiveMass (M.obsKernel s))
    (x : ValuesOn M.observed (swigΩ Ω)) :
    M.extractDistrict (M.toSWIGGraph.induce A) A C' hA
        (M.qLocalMass s A hA) x =
      M.qLocalMass s C'
        (fun _ hv =>
          hA (by
            have hHobs :
                (M.toSWIGGraph.induce A).observed = A := by
              simp [SWIGGraph.induce, Finset.inter_eq_left.mpr hA]
            exact hHobs ▸
              (M.toSWIGGraph.induce A).cComponentSet_subset_observed C' hC' hv)) x := by
  classical
  let H := M.toSWIGGraph.induce A
  have hHobs : H.observed = A := by
    simp [H, SWIGGraph.induce, Finset.inter_eq_left.mpr hA]
  have hCobs : C' ⊆ M.observed := by
    intro v hv
    exact hA (hHobs ▸ H.cComponentSet_subset_observed C' hC' hv)
  have hCA : C' ⊆ A := by
    intro v hv
    exact hHobs ▸ H.cComponentSet_subset_observed C' hC' hv
  have hdisj :
      (↑H.cComponentSet : Set (Finset (SWIGNode N))).Pairwise
        (fun U U' => Disjoint U U') := by
    intro U hU V hV hne
    exact H.cComponentSet_pairwise_disjoint hU hV hne
  have hmarg : ∀ k,
      M.marginalizeOn (A \ H.prefixIn A k)
          (fun _ hv => hA ((Finset.mem_sdiff.mp hv).1))
          (M.qLocalMass s A hA) x =
        M.qLocalMass s (H.prefixIn A k)
          (fun _ hv => hA (H.prefixIn_subset A k hv)) x := by
    intro k
    simpa [H] using
      M.qLocalMass_marginalize_ancestralClosed s A (H.prefixIn A k) hA
        (H.prefixIn_subset A k)
        (prefixIn_parent_closed_induce_observed M A hA k) x
  have hprod : ∀ k,
      M.qLocalMass s (H.prefixIn A k)
          (fun _ hv => hA (H.prefixIn_subset A k hv)) x =
        ∏ C ∈ H.cComponentSet,
          M.qLocalMass s (C ∩ H.prefixIn A k)
            (fun _ hv => hA (H.prefixIn_subset A k
              (Finset.mem_of_mem_inter_right hv))) x := by
    intro k
    simpa [H] using qLocalMass_prefixIn_eq_prod_induce_components M s A hA k x
  unfold SCM.extractDistrict
  calc
    (∏ i ∈ Finset.univ.filter
        (fun i : Fin A.card => (H.nodesAt A i).val ∈ C'),
      M.marginalizeOn (A \ H.prefixIn A (i.val + 1))
          (fun _ hv => hA ((Finset.mem_sdiff.mp hv).1))
          (M.qLocalMass s A hA) x /
        M.marginalizeOn (A \ H.prefixIn A i.val)
          (fun _ hv => hA ((Finset.mem_sdiff.mp hv).1))
          (M.qLocalMass s A hA) x)
        =
      ∏ i ∈ Finset.univ.filter
          (fun i : Fin A.card => (H.nodesAt A i).val ∈ C'),
        (∏ C ∈ H.cComponentSet,
          M.qLocalMass s (C ∩ H.prefixIn A (i.val + 1))
            (fun _ hv => hA (H.prefixIn_subset A (i.val + 1)
              (Finset.mem_of_mem_inter_right hv))) x) /
          (∏ C ∈ H.cComponentSet,
            M.qLocalMass s (C ∩ H.prefixIn A i.val)
              (fun _ hv => hA (H.prefixIn_subset A i.val
                (Finset.mem_of_mem_inter_right hv))) x) := by
          refine Finset.prod_congr rfl ?_
          intro i _hi
          rw [hmarg (i.val + 1), hmarg i.val, hprod (i.val + 1), hprod i.val]
    _ =
      ∏ i ∈ Finset.univ.filter
          (fun i : Fin A.card => (H.nodesAt A i).val ∈ C'),
        M.qLocalMass s (C' ∩ H.prefixIn A (i.val + 1))
          (fun _ hv => hA (H.prefixIn_subset A (i.val + 1)
            (Finset.mem_of_mem_inter_right hv))) x /
          M.qLocalMass s (C' ∩ H.prefixIn A i.val)
            (fun _ hv => hA (H.prefixIn_subset A i.val
              (Finset.mem_of_mem_inter_right hv))) x := by
          refine Finset.prod_congr rfl ?_
          intro i hi
          have hiC : (H.nodesAt A i).val ∈ C' := (Finset.mem_filter.mp hi).2
          exact prefixIn_qProduct_ratio_eq_component_ratio_of_family
            M H A s H.cComponentSet C' hC' hdisj i hA hiC hpos x
    _ =
      M.qLocalMass s C' hCobs x := by
          simpa using
            component_qLocalMass_ratio_product_prefixIn
              M H A s C' hCobs hCA hpos x
    _ =
      M.qLocalMass s C'
        (fun _ hv =>
          hA (by
            have hHobs' :
                (M.toSWIGGraph.induce A).observed = A := by
              simp [SWIGGraph.induce, Finset.inter_eq_left.mpr hA]
            exact hHobs' ▸
              (M.toSWIGGraph.induce A).cComponentSet_subset_observed C' hC' hv)) x := by
          rfl

/-- The target set of a recursive c-factor reachability certificate is contained
in the source set. -/
theorem CFactorReachableRec.target_subset
    {G : SWIGGraph N} {T C : Finset (SWIGNode N)}
    (h : CFactorReachableRec G T C) : C ⊆ T := by
  cases h with
  | base _ hCT _ => exact hCT
  | step _ hCT _ _ _ => exact hCT

private lemma qLocalMass_obsProof_irrel
    (M : Causalean.SCM N Ω) (s : M.FixedValues)
    (T : Finset (SWIGNode N)) (hT hT' : T ⊆ M.observed)
    (x : ValuesOn M.observed (swigΩ Ω)) :
    M.qLocalMass s T hT x = M.qLocalMass s T hT' x := by
  unfold SCM.qLocalMass
  congr 1

/-- The obs-side IDENTIFY recursion recovers the local q-mass of the target
district from the local q-mass of any recursively reachable source district. -/
theorem identifyMassRec_qLocalMass
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (s : M.FixedValues)
    (hpos : DiscreteID.PositiveMass (M.obsKernel s))
    (T C : Finset (SWIGNode N)) (hT : T ⊆ M.observed)
    (hReach : CFactorReachableRec M.toSWIGGraph T C)
    (x : ValuesOn M.observed (swigΩ Ω)) :
    M.identifyMassRec M.toSWIGGraph T C hT (M.qLocalMass s T hT) x =
      M.qLocalMass s C (fun _ hv => hT (hReach.target_subset hv)) x := by
  classical
  induction hReach generalizing x with
  | base hne hCT hproject =>
      rename_i T₀ C₀
      rw [SCM.identifyMassRec_base M M.toSWIGGraph T₀ C₀ hT
        (M.qLocalMass s T₀ hT) hproject]
      have hclosed :
          ∀ v ∈ T₀, ∀ w ∈ C₀, M.dag.edge v w → v ∈ C₀ := by
        have hclosedA :=
          inducedAncestral_parent_closed M.toSWIGGraph
            (T := T₀) (C := C₀) (by simpa using hT)
        intro v hvT w hwC hEdge
        have hwA : w ∈ inducedAncestral M.toSWIGGraph T₀ C₀ := by
          simpa [hproject] using hwC
        have hvA := hclosedA v hvT w hwA hEdge
        simpa [hproject] using hvA
      exact M.qLocalMass_marginalize_ancestralClosed s T₀ C₀ hT hCT hclosed x
  | step hne hCT hnotC hnotT hrec ih =>
      rename_i T₀ C₀
      let A := inducedAncestral M.toSWIGGraph T₀ C₀
      let C₁ := containingCComponent (M.toSWIGGraph.induce A) C₀
      let hA : A ⊆ M.observed := fun _ hv =>
        hT (inducedAncestral_subset_left M.toSWIGGraph T₀ C₀ hv)
      let hC₁obs : C₁ ⊆ M.observed := fun _ hv =>
        hT (inducedAncestral_subset_left M.toSWIGGraph T₀ C₀
          (containingCComponent_induce_subset M.toSWIGGraph A C₀ hv))
      have hCobs : C₀ ⊆ M.toSWIGGraph.observed := by
        intro v hv
        simpa using hT (hCT hv)
      have hCA : C₀ ⊆ A :=
        subset_inducedAncestral M.toSWIGGraph hCT hCobs
      have hC₁mem : C₁ ∈ (M.toSWIGGraph.induce A).cComponentSet := by
        simp only [C₁, containingCComponent, dif_pos hne, SWIGGraph.cComponentSet]
        have hchooseA : hne.choose ∈ A := hCA hne.choose_spec
        have hchooseObs : hne.choose ∈ M.toSWIGGraph.observed :=
          hCobs hne.choose_spec
        have hchooseInd :
            hne.choose ∈ (M.toSWIGGraph.induce A).observed := by
          simp [SWIGGraph.induce, hchooseA, hchooseObs]
        exact Finset.mem_image.mpr ⟨hne.choose, hchooseInd, rfl⟩
      have hmarg :
          M.marginalizeOn (T₀ \ A)
              (fun _ hv => hT ((Finset.mem_sdiff.mp hv).1))
              (M.qLocalMass s T₀ hT) =
            M.qLocalMass s A hA := by
        funext y
        have hclosedA :
            ∀ v ∈ T₀, ∀ w ∈ A, M.dag.edge v w → v ∈ A := by
          simpa [A] using
            inducedAncestral_parent_closed M.toSWIGGraph
              (T := T₀) (C := C₀) (by simpa using hT)
        exact M.qLocalMass_marginalize_ancestralClosed s T₀ A hT
          (inducedAncestral_subset_left M.toSWIGGraph T₀ C₀) hclosedA y
      have hextract :
          M.extractDistrict (M.toSWIGGraph.induce A) A C₁ hA
              (M.qLocalMass s A hA) =
            M.qLocalMass s C₁ hC₁obs := by
        funext y
        calc
          M.extractDistrict (M.toSWIGGraph.induce A) A C₁ hA
              (M.qLocalMass s A hA) y
              = M.qLocalMass s C₁
                  (fun _ hv =>
                    hA (by
                      have hHobs :
                          (M.toSWIGGraph.induce A).observed = A := by
                        simp [SWIGGraph.induce, Finset.inter_eq_left.mpr hA]
                      exact hHobs ▸
                        (M.toSWIGGraph.induce A).cComponentSet_subset_observed
                          C₁ hC₁mem hv)) y := by
                exact extractDistrict_qLocalMass M s A C₁ hA hC₁mem hpos y
          _ = M.qLocalMass s C₁ hC₁obs y := by
                exact qLocalMass_obsProof_irrel M s C₁ _ _ y
      rw [SCM.identifyMassRec_step M M.toSWIGGraph T₀ C₀ hT
        (M.qLocalMass s T₀ hT) hnotC hnotT]
      change
        M.identifyMassRec M.toSWIGGraph C₁ C₀ hC₁obs
          (M.extractDistrict (M.toSWIGGraph.induce A) A C₁ hA
            (M.marginalizeOn (T₀ \ A)
              (fun _ hv => hT ((Finset.mem_sdiff.mp hv).1))
              (M.qLocalMass s T₀ hT))) x = _
      rw [hmarg, hextract]
      calc
        M.identifyMassRec M.toSWIGGraph C₁ C₀ hC₁obs
            (M.qLocalMass s C₁ hC₁obs) x
            = M.qLocalMass s C₀
                (fun _ hv => hC₁obs (hrec.target_subset hv)) x := by
              exact ih hC₁obs x
        _ = M.qLocalMass s C₀
              (fun _ hv =>
                hT ((CFactorReachableRec.step hne hCT hnotC hnotT hrec).target_subset hv)) x := by
              exact qLocalMass_obsProof_irrel M s C₀ _ _ x

private lemma component_ref_atom_product_eq_jointRef_prefixIn
    [∀ n, MeasurableSingletonClass (Ω n)]
    (H : SWIGGraph N) (D : Finset (SWIGNode N)) (ref : ReferenceMeasures Ω)
    (S : Finset (SWIGNode N)) (hSD : S ⊆ D)
    (xD : ValuesOn D (swigΩ Ω)) :
    (∏ i ∈ Finset.univ.filter (fun i : Fin D.card => (H.nodesAt D i).val ∈ S),
      ref.μ (H.nodesAt D i).val
        ({xD (H.nodesAt D i)} : Set (swigΩ Ω (H.nodesAt D i).val)))
      =
    jointRef ref S ({valuesProjection hSD xD} :
      Set (ValuesOn S (swigΩ Ω))) := by
  classical
  have hprod :
      (∏ i ∈ Finset.univ.filter (fun i : Fin D.card => (H.nodesAt D i).val ∈ S),
        ref.μ (H.nodesAt D i).val
          ({xD (H.nodesAt D i)} : Set (swigΩ Ω (H.nodesAt D i).val)))
        =
      ∏ v : {v // v ∈ S},
        ref.μ v.val ({(valuesProjection hSD xD) v} :
          Set (swigΩ Ω v.val)) := by
    refine Finset.prod_bij
      (fun i hi => ⟨(H.nodesAt D i).val, (Finset.mem_filter.mp hi).2⟩)
      ?_ ?_ ?_ ?_
    · intro i hi
      exact Finset.mem_univ _
    · intro i _hi j _hj hij
      have hval : (H.nodesAt D i).val = (H.nodesAt D j).val :=
        congrArg (fun v : {v // v ∈ S} => v.val) hij
      have hsub : H.nodesAt D i = H.nodesAt D j :=
        Subtype.ext hval
      calc
        i = H.nodeIndex D (H.nodesAt D i) := by
              simp [SWIGGraph.nodeIndex, SWIGGraph.nodesAt]
        _ = H.nodeIndex D (H.nodesAt D j) := by rw [hsub]
        _ = j := by
              simp [SWIGGraph.nodeIndex, SWIGGraph.nodesAt]
    · intro v _hv
      let i : Fin D.card := H.nodeIndex D ⟨v.val, hSD v.property⟩
      have hnode : (H.nodesAt D i).val = v.val := by
        have hround : H.nodesAt D (H.nodeIndex D ⟨v.val, hSD v.property⟩) =
            ⟨v.val, hSD v.property⟩ := by
          simp [SWIGGraph.nodeIndex, SWIGGraph.nodesAt]
        exact congrArg Subtype.val hround
      refine ⟨i, ?_, ?_⟩
      · rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, by simp [hnode, v.property]⟩
      · exact Subtype.ext hnode
    · intro i hi
      simp [valuesProjection]
  rw [jointRef_singleton_eq_prod]
  exact hprod

private lemma prefix_pair_singleton_mass_eq_succ_prefix_mass
    [∀ n, MeasurableSingletonClass (Ω n)]
    (H : SWIGGraph N) (D : Finset (SWIGNode N))
    (μ : MeasureTheory.Measure (ValuesOn D (swigΩ Ω)))
    (i : Fin D.card) (x : ValuesOn D (swigΩ Ω)) :
    (μ.map
        (fun ω : ValuesOn D (swigΩ Ω) =>
          (valuesProjection (H.prefixIn_subset D i.val) ω,
            valuesProjection
              (show ({(H.nodesAt D i).val} : Finset (SWIGNode N)) ⊆ D from by
                intro v hv
                rw [Finset.mem_singleton] at hv
                exact hv ▸ (H.nodesAt D i).property) ω)))
        ({(valuesProjection (H.prefixIn_subset D i.val) x,
            valuesProjection
              (show ({(H.nodesAt D i).val} : Finset (SWIGNode N)) ⊆ D from by
                intro v hv
                rw [Finset.mem_singleton] at hv
                exact hv ▸ (H.nodesAt D i).property) x)} :
          Set (ValuesOn (H.prefixIn D i.val) (swigΩ Ω) ×
            ValuesOn ({(H.nodesAt D i).val} : Finset (SWIGNode N)) (swigΩ Ω))) =
      (μ.map (valuesProjection (H.prefixIn_subset D (i.val + 1))))
        ({valuesProjection (H.prefixIn_subset D (i.val + 1)) x} :
          Set (ValuesOn (H.prefixIn D (i.val + 1)) (swigΩ Ω))) := by
  classical
  let hNodeD : ({(H.nodesAt D i).val} : Finset (SWIGNode N)) ⊆ D := by
    intro v hv
    rw [Finset.mem_singleton] at hv
    exact hv ▸ (H.nodesAt D i).property
  let pairMap : ValuesOn D (swigΩ Ω) →
      ValuesOn (H.prefixIn D i.val) (swigΩ Ω) ×
        ValuesOn ({(H.nodesAt D i).val} : Finset (SWIGNode N)) (swigΩ Ω) :=
    fun ω => (valuesProjection (H.prefixIn_subset D i.val) ω,
      valuesProjection hNodeD ω)
  let succMap : ValuesOn D (swigΩ Ω) →
      ValuesOn (H.prefixIn D (i.val + 1)) (swigΩ Ω) :=
    valuesProjection (H.prefixIn_subset D (i.val + 1))
  have hsets :
      pairMap ⁻¹'
          ({(valuesProjection (H.prefixIn_subset D i.val) x,
              valuesProjection hNodeD x)} :
            Set (ValuesOn (H.prefixIn D i.val) (swigΩ Ω) ×
              ValuesOn ({(H.nodesAt D i).val} : Finset (SWIGNode N)) (swigΩ Ω))) =
        succMap ⁻¹'
          ({valuesProjection (H.prefixIn_subset D (i.val + 1)) x} :
            Set (ValuesOn (H.prefixIn D (i.val + 1)) (swigΩ Ω))) := by
    ext ω
    constructor
    · intro hω
      have hpre :
          valuesProjection (H.prefixIn_subset D i.val) ω =
            valuesProjection (H.prefixIn_subset D i.val) x :=
        congrArg Prod.fst hω
      have hnode :
          valuesProjection hNodeD ω = valuesProjection hNodeD x :=
        congrArg Prod.snd hω
      ext v
      by_cases hvpre : v.val ∈ H.prefixIn D i.val
      · have h := congrFun hpre ⟨v.val, hvpre⟩
        simpa [succMap, valuesProjection] using h
      · have hvnode : v.val = (H.nodesAt D i).val := by
          have hvsucc : v.val ∈ H.prefixIn D (i.val + 1) := v.property
          have hvsucc' : v.val ∈
              H.prefixIn D i.val ∪ {(H.nodesAt D i).val} := by
            simpa [prefixIn_succ_qfactor H D i.isLt] using hvsucc
          rcases Finset.mem_union.mp hvsucc' with hvold | hvnew
          · exact False.elim (hvpre hvold)
          · simpa using hvnew
        have h := congrFun hnode
          ⟨v.val, by simpa [hvnode] using Finset.mem_singleton_self (H.nodesAt D i).val⟩
        simpa [succMap, valuesProjection, hvnode] using h
    · intro hω
      have hsucc :
          valuesProjection (H.prefixIn_subset D (i.val + 1)) ω =
            valuesProjection (H.prefixIn_subset D (i.val + 1)) x := hω
      apply Prod.ext
      · ext v
        have hvsucc : v.val ∈ H.prefixIn D (i.val + 1) :=
          prefixIn_mono_qfactor H D (Nat.le_succ i.val) v.property
        have h := congrFun hsucc ⟨v.val, hvsucc⟩
        simpa [pairMap, valuesProjection] using h
      · ext v
        have hvnode : v.val = (H.nodesAt D i).val := by
          exact Finset.mem_singleton.mp v.property
        have hvsucc : v.val ∈ H.prefixIn D (i.val + 1) := by
          rw [hvnode, nodesAt_mem_prefixIn_iff_qfactor H D (i.val + 1) i]
          exact Nat.lt_succ_self i.val
        have h := congrFun hsucc ⟨v.val, hvsucc⟩
        simpa [pairMap, valuesProjection] using h
  rw [MeasureTheory.Measure.map_apply
      ((measurable_valuesProjection (H.prefixIn_subset D i.val)).prod
        (measurable_valuesProjection hNodeD))
      (MeasurableSet.singleton _),
    MeasureTheory.Measure.map_apply
      (measurable_valuesProjection (H.prefixIn_subset D (i.val + 1)))
      (MeasurableSet.singleton _),
    hsets]

private lemma tianPrefixStepDensity_eq_prefix_mass_ratio
    [∀ n, Fintype (Ω n)]
    [∀ n, MeasurableSingletonClass (Ω n)]
    (H : SWIGGraph N) (D : Finset (SWIGNode N))
    (μ : MeasureTheory.Measure (ValuesOn D (swigΩ Ω)))
    (ref : ReferenceMeasures Ω) (href : ReferenceFaithful ref)
    [MeasureTheory.IsFiniteMeasure μ]
    [∀ (k : ℕ) (hk : k < D.card),
      StandardBorelSpace
        (ValuesOn ({(H.nodesAt D ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < D.card),
      Nonempty
        (ValuesOn ({(H.nodesAt D ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    (i : Fin D.card) (x : ValuesOn D (swigΩ Ω))
    (hprefix0 :
      (μ.map (valuesProjection (H.prefixIn_subset D i.val)))
        ({valuesProjection (H.prefixIn_subset D i.val) x} :
          Set (ValuesOn (H.prefixIn D i.val) (swigΩ Ω))) ≠ 0) :
    tianPrefixStepDensity H D μ ref i x =
      ((μ.map (valuesProjection (H.prefixIn_subset D (i.val + 1))))
          ({valuesProjection (H.prefixIn_subset D (i.val + 1)) x} :
            Set (ValuesOn (H.prefixIn D (i.val + 1)) (swigΩ Ω))) /
        (μ.map (valuesProjection (H.prefixIn_subset D i.val)))
          ({valuesProjection (H.prefixIn_subset D i.val) x} :
            Set (ValuesOn (H.prefixIn D i.val) (swigΩ Ω)))) /
      jointRef ref ({(H.nodesAt D i).val} : Finset (SWIGNode N))
        ({valuesProjection
          (show ({(H.nodesAt D i).val} : Finset (SWIGNode N)) ⊆ D from by
            intro v hv
            rw [Finset.mem_singleton] at hv
            exact hv ▸ (H.nodesAt D i).property) x} :
          Set (ValuesOn ({(H.nodesAt D i).val} : Finset (SWIGNode N)) (swigΩ Ω))) := by
  classical
  let hNodeD : ({(H.nodesAt D i).val} : Finset (SWIGNode N)) ⊆ D := by
    intro v hv
    rw [Finset.mem_singleton] at hv
    exact hv ▸ (H.nodesAt D i).property
  let nodeMap : ValuesOn D (swigΩ Ω) →
      ValuesOn ({(H.nodesAt D i).val} : Finset (SWIGNode N)) (swigΩ Ω) :=
    valuesProjection hNodeD
  let prefixMap : ValuesOn D (swigΩ Ω) →
      ValuesOn (H.prefixIn D i.val) (swigΩ Ω) :=
    valuesProjection (H.prefixIn_subset D i.val)
  have hden0 :
      jointRef ref ({(H.nodesAt D i).val} : Finset (SWIGNode N))
        ({nodeMap x} :
          Set (ValuesOn ({(H.nodesAt D i).val} : Finset (SWIGNode N)) (swigΩ Ω))) ≠ 0 :=
    jointRef_singleton_ne_zero ref href _ (nodeMap x)
  have hdentop :
      jointRef ref ({(H.nodesAt D i).val} : Finset (SWIGNode N))
        ({nodeMap x} :
          Set (ValuesOn ({(H.nodesAt D i).val} : Finset (SWIGNode N)) (swigΩ Ω))) ≠ ∞ := by
    exact ne_of_lt (MeasureTheory.measure_lt_top
      (jointRef ref ({(H.nodesAt D i).val} : Finset (SWIGNode N))) _)
  have hcond :
      (ProbabilityTheory.condDistrib nodeMap prefixMap μ (prefixMap x))
        ({nodeMap x} :
          Set (ValuesOn ({(H.nodesAt D i).val} : Finset (SWIGNode N)) (swigΩ Ω))) =
        (μ.map (valuesProjection (H.prefixIn_subset D (i.val + 1))))
          ({valuesProjection (H.prefixIn_subset D (i.val + 1)) x} :
            Set (ValuesOn (H.prefixIn D (i.val + 1)) (swigΩ Ω))) /
          (μ.map prefixMap)
            ({prefixMap x} : Set (ValuesOn (H.prefixIn D i.val) (swigΩ Ω))) := by
    rw [condDistrib_singleton_mass_of_ne_zero (μ := μ)
        (Y := nodeMap) (Z := prefixMap)
        (measurable_valuesProjection hNodeD) (prefixMap x) (nodeMap x) hprefix0]
    rw [prefix_pair_singleton_mass_eq_succ_prefix_mass H D μ i x]
  unfold tianPrefixStepDensity
  rw [rnDeriv_singleton_eq_div _ _
      (absolutelyContinuous_jointRef_of_faithful ref href
        ({(H.nodesAt D i).val} : Finset (SWIGNode N))
        (ProbabilityTheory.condDistrib nodeMap prefixMap μ (prefixMap x)))
      (nodeMap x) hden0 hdentop]
  simpa [nodeMap, prefixMap, hNodeD] using congrArg
    (fun a => a / jointRef ref ({(H.nodesAt D i).val} : Finset (SWIGNode N))
        ({nodeMap x} :
          Set (ValuesOn ({(H.nodesAt D i).val} : Finset (SWIGNode N)) (swigΩ Ω))))
    hcond

private lemma doModel_mechCFactor_eq_qLocalMass_div_jointRef
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (hStd : M.isStandard)
    (ref : Causalean.SCM.ReferenceMeasures Ω)
    (href : Causalean.SCM.ReferenceFaithful ref)
    (sDo : (M.fixSet X hObs hFix).FixedValues)
    (S : Finset (SWIGNode N))
    (hSobs : S ⊆ (M.fixSet X hObs hFix).observed)
    (x : ValuesOn (M.fixSet X hObs hFix).observed (swigΩ Ω)) :
    (M.fixSet X hObs hFix).mechCFactor ref S hSobs sDo x =
      (M.fixSet X hObs hFix).qLocalMass sDo S hSobs x /
        jointRef ref S ({valuesProjection hSobs x} :
          Set (ValuesOn S (swigΩ Ω))) := by
  exact mechCFactor_eq_qLocalMass_div_jointRef_qfactor
    (M.fixSet X hObs hFix) ref sDo S hSobs href
    (fixSet_fixed_random_edgeless_qfactor M X hObs hFix hStd) x

private lemma valuesProjection_extend_eq_of_subset
    (M : Causalean.SCM N Ω)
    {D S : Finset (SWIGNode N)}
    (hDobs : D ⊆ M.observed) (hSD : S ⊆ D) (hSobs : S ⊆ M.observed)
    (extend : ValuesOn D (swigΩ Ω) → ValuesOn M.observed (swigΩ Ω))
    (hExtend : ∀ xD, valuesProjection hDobs (extend xD) = xD)
    (xD : ValuesOn D (swigΩ Ω)) :
    valuesProjection hSobs (extend xD) = valuesProjection hSD xD := by
  ext v
  have h := congrFun (hExtend xD) ⟨v.val, hSD v.property⟩
  simpa [valuesProjection] using h

private lemma obsKernel_marginal_singleton_eq_qLocalMass
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (s : M.FixedValues)
    (P : Finset (SWIGNode N)) (hP : M.ObsParentClosed P)
    (x : ValuesOn M.observed (swigΩ Ω)) :
    ((M.obsKernel s).map (valuesProjection hP.1))
        ({valuesProjection hP.1 x} : Set (ValuesOn P (swigΩ Ω))) =
      M.qLocalMass s P hP.1 x := by
  classical
  rw [obsKernel_marginal_singleton_eq_latentProduct_agree M s hP.1 x]
  have hset :
      {ℓ | ∀ v : {v // v ∈ P},
        M.evalMap s ℓ
            ⟨v.val, Finset.mem_union_left M.unobserved (hP.1 v.property)⟩ =
          x ⟨v.val, hP.1 v.property⟩}
        =
      {ℓ | ∀ v (hv : v ∈ P), M.localConsistent s x v (hP.1 hv) ℓ} := by
    ext ℓ
    constructor
    · intro hEval
      exact (M.evalMap_agree_iff_localConsistent s P hP x ℓ).mp
        (fun v hv => hEval ⟨v, hv⟩)
    · intro hLocal v
      exact (M.evalMap_agree_iff_localConsistent s P hP x ℓ).mpr
        hLocal v.val v.property
  unfold qLocalMass
  rw [hset]

private lemma doObsKernelAncestralMarginal_map_prefix_eq_doObsKernel_map_prefix
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (Y : Finset (SWIGNode N))
    (sDo : (M.fixSet X hObs hFix).FixedValues)
    {P : Finset (SWIGNode N)}
    (hPD : P ⊆ fixObservedAncestralSet M X hObs hFix Y) :
    ((doObsKernelAncestralMarginal M X hObs hFix Y sDo).map
        (valuesProjection hPD)) =
      (((M.fixSet X hObs hFix).obsKernel sDo).map
        (valuesProjection
          (show P ⊆ (M.fixSet X hObs hFix).observed from
            fun _ hv => Finset.inter_subset_right (hPD hv)))) := by
  classical
  let D := fixObservedAncestralSet M X hObs hFix Y
  let hDobs : D ⊆ (M.fixSet X hObs hFix).observed := Finset.inter_subset_right
  let hPobs : P ⊆ (M.fixSet X hObs hFix).observed := fun _ hv => hDobs (hPD hv)
  have hcomp :
      valuesProjection (Ω := swigΩ Ω) hPobs =
        valuesProjection hPD ∘ valuesProjection hDobs :=
    valuesProjection_comp (Ω' := swigΩ Ω) hPD hDobs hPobs
  unfold doObsKernelAncestralMarginal
  rw [ProbabilityTheory.Kernel.map_apply _ (measurable_valuesProjection hDobs)]
  rw [MeasureTheory.Measure.map_map (measurable_valuesProjection hPD)
    (measurable_valuesProjection hDobs)]
  rw [← hcomp]

private lemma doObsKernelAncestralMarginal_prefix_singleton_eq_prod_qLocalMass
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (Y : Finset (SWIGNode N))
    (sDo : (M.fixSet X hObs hFix).FixedValues)
    (extend :
      ValuesOn (fixObservedAncestralSet M X hObs hFix Y) (swigΩ Ω) →
        ValuesOn M.observed (swigΩ Ω))
    (hExtend : ∀ xD, valuesProjection
        (show fixObservedAncestralSet M X hObs hFix Y ⊆ M.observed from
          Finset.inter_subset_right) (extend xD) = xD)
    (k : ℕ)
    (xD : ValuesOn (fixObservedAncestralSet M X hObs hFix Y) (swigΩ Ω)) :
    let MX := M.fixSet X hObs hFix
    let D := fixObservedAncestralSet M X hObs hFix Y
    let H := MX.toSWIGGraph.induce (fixAncestralSet M X hObs hFix Y)
    ((doObsKernelAncestralMarginal M X hObs hFix Y sDo).map
        (valuesProjection (H.prefixIn_subset D k)))
      ({valuesProjection (H.prefixIn_subset D k) xD} :
        Set (ValuesOn (H.prefixIn D k) (swigΩ Ω))) =
      ∏ C ∈ MX.toSWIGGraph.cComponentSet,
        MX.qLocalMass sDo (C ∩ H.prefixIn D k)
          (fun _ hv => (SWIGGraph.prefixIn_obsParentClosed M X hObs hFix Y k).1
            (Finset.mem_of_mem_inter_right hv)) (extend xD) := by
  classical
  let MX := M.fixSet X hObs hFix
  let D := fixObservedAncestralSet M X hObs hFix Y
  let H := MX.toSWIGGraph.induce (fixAncestralSet M X hObs hFix Y)
  let P := H.prefixIn D k
  let hPD : P ⊆ D := H.prefixIn_subset D k
  let hPclosed : MX.ObsParentClosed P := by
    simpa [MX, D, H, P] using SWIGGraph.prefixIn_obsParentClosed M X hObs hFix Y k
  let hPobsMX : P ⊆ MX.observed := hPclosed.1
  let hPobsM : P ⊆ M.observed := fun _ hv => Finset.inter_subset_right (hPD hv)
  have hpointM :
      valuesProjection hPobsM (extend xD) = valuesProjection hPD xD :=
    valuesProjection_extend_eq_of_subset M
      (show D ⊆ M.observed from Finset.inter_subset_right)
      hPD hPobsM extend hExtend xD
  have hpointMX :
      valuesProjection hPobsMX (extend xD) = valuesProjection hPD xD := by
    simpa [MX, SCM.fixSet_observed, hPobsMX, hPobsM] using hpointM
  have hmap :=
    doObsKernelAncestralMarginal_map_prefix_eq_doObsKernel_map_prefix
      M X hObs hFix Y sDo hPD
  have hengine :=
    MX.obsKernel_marginal_singleton_eq_prod_qLocalMass sDo P hPclosed (extend xD)
  calc
    ((doObsKernelAncestralMarginal M X hObs hFix Y sDo).map
        (valuesProjection hPD))
      ({valuesProjection hPD xD} : Set (ValuesOn P (swigΩ Ω)))
        =
      ((MX.obsKernel sDo).map (valuesProjection hPobsMX))
        ({valuesProjection hPD xD} : Set (ValuesOn P (swigΩ Ω))) := by
          simpa [MX, D, H, P, hPobsMX] using congrArg
            (fun μ : MeasureTheory.Measure (ValuesOn P (swigΩ Ω)) =>
              μ ({valuesProjection hPD xD} : Set (ValuesOn P (swigΩ Ω)))) hmap
    _ =
      ((MX.obsKernel sDo).map (valuesProjection hPobsMX))
        ({valuesProjection hPobsMX (extend xD)} : Set (ValuesOn P (swigΩ Ω))) := by
          rw [hpointMX]
    _ = ∏ C ∈ MX.toSWIGGraph.cComponentSet,
        MX.qLocalMass sDo (C ∩ P)
          (fun _ hv => hPclosed.1 (Finset.mem_of_mem_inter_right hv)) (extend xD) := by
          exact hengine

private lemma doObsKernelAncestralMarginal_prefix_singleton_eq_prod_H_qLocalMass
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (Y : Finset (SWIGNode N))
    (sDo : (M.fixSet X hObs hFix).FixedValues)
    (extend :
      ValuesOn (fixObservedAncestralSet M X hObs hFix Y) (swigΩ Ω) →
        ValuesOn M.observed (swigΩ Ω))
    (hExtend : ∀ xD, valuesProjection
        (show fixObservedAncestralSet M X hObs hFix Y ⊆ M.observed from
          Finset.inter_subset_right) (extend xD) = xD)
    (k : ℕ)
    (xD : ValuesOn (fixObservedAncestralSet M X hObs hFix Y) (swigΩ Ω)) :
    let MX := M.fixSet X hObs hFix
    let D := fixObservedAncestralSet M X hObs hFix Y
    let H := MX.toSWIGGraph.induce (fixAncestralSet M X hObs hFix Y)
    ((doObsKernelAncestralMarginal M X hObs hFix Y sDo).map
        (valuesProjection (H.prefixIn_subset D k)))
      ({valuesProjection (H.prefixIn_subset D k) xD} :
        Set (ValuesOn (H.prefixIn D k) (swigΩ Ω))) =
      ∏ C ∈ H.cComponentSet,
        MX.qLocalMass sDo (C ∩ H.prefixIn D k)
          (fun _ hv => (SWIGGraph.prefixIn_obsParentClosed M X hObs hFix Y k).1
            (Finset.mem_of_mem_inter_right hv)) (extend xD) := by
  classical
  let MX := M.fixSet X hObs hFix
  let A := fixAncestralSet M X hObs hFix Y
  let D := fixObservedAncestralSet M X hObs hFix Y
  let H := MX.toSWIGGraph.induce A
  let P := H.prefixIn D k
  let hPD : P ⊆ D := H.prefixIn_subset D k
  let hPclosed : MX.ObsParentClosed P := by
    simpa [MX, D, H, P] using SWIGGraph.prefixIn_obsParentClosed M X hObs hFix Y k
  let hPobsMX : P ⊆ MX.observed := hPclosed.1
  let hPobsM : P ⊆ M.observed := fun _ hv => Finset.inter_subset_right (hPD hv)
  have hpointM :
      valuesProjection hPobsM (extend xD) = valuesProjection hPD xD :=
    valuesProjection_extend_eq_of_subset M
      (show D ⊆ M.observed from Finset.inter_subset_right)
      hPD hPobsM extend hExtend xD
  have hpointMX :
      valuesProjection hPobsMX (extend xD) = valuesProjection hPD xD := by
    simpa [MX, SCM.fixSet_observed, hPobsMX, hPobsM] using hpointM
  have hmap :=
    doObsKernelAncestralMarginal_map_prefix_eq_doObsKernel_map_prefix
      M X hObs hFix Y sDo hPD
  have hHobs : H.observed = D := by
    simp [H, D, A, MX, SWIGGraph.induce, fixObservedAncestralSet, SCM.fixSet_observed]
  have h𝒞obs : ∀ U ∈ H.cComponentSet, U ⊆ MX.observed := by
    intro U hU v hv
    have hvHobs : v ∈ H.observed := H.cComponentSet_subset_observed U hU hv
    have hvD : v ∈ D := by simpa [hHobs] using hvHobs
    exact Finset.mem_inter.mp hvD |>.2
  have hcover : P ⊆ H.cComponentSet.sup id := by
    intro v hv
    have hvObs : v ∈ H.observed := by
      rw [hHobs]
      exact H.prefixIn_subset D k hv
    rw [Finset.mem_sup]
    exact ⟨H.cComponentOf v,
      (by
        rw [SWIGGraph.cComponentSet, Finset.mem_image]
        exact ⟨v, hvObs, rfl⟩),
      H.mem_cComponentOf_self hvObs⟩
  have hblock :
      (↑H.cComponentSet : Set (Finset (SWIGNode N))).Pairwise
        (fun U U' => Disjoint (MX.latentBlock U) (MX.latentBlock U')) := by
    intro U hU V hV hne
    exact latentBlock_pairwise_disjoint_induce_components MX A hU hV hne
  have hnode :
      (↑H.cComponentSet : Set (Finset (SWIGNode N))).Pairwise
        (fun U U' => Disjoint U U') := by
    intro U hU V hV hne
    exact H.cComponentSet_pairwise_disjoint hU hV hne
  have hfac :=
    MX.qLocalMass_prod_inter_of_latentBlock_disjoint sDo
      P hPobsMX H.cComponentSet h𝒞obs hcover hblock hnode (extend xD)
  have hq :
      ((MX.obsKernel sDo).map (valuesProjection hPobsMX))
        ({valuesProjection hPobsMX (extend xD)} : Set (ValuesOn P (swigΩ Ω))) =
        MX.qLocalMass sDo P hPobsMX (extend xD) :=
    obsKernel_marginal_singleton_eq_qLocalMass MX sDo P hPclosed (extend xD)
  calc
    ((doObsKernelAncestralMarginal M X hObs hFix Y sDo).map
        (valuesProjection hPD))
      ({valuesProjection hPD xD} : Set (ValuesOn P (swigΩ Ω)))
        =
      ((MX.obsKernel sDo).map (valuesProjection hPobsMX))
        ({valuesProjection hPD xD} : Set (ValuesOn P (swigΩ Ω))) := by
          simpa [MX, D, H, P, hPobsMX] using congrArg
            (fun μ : MeasureTheory.Measure (ValuesOn P (swigΩ Ω)) =>
              μ ({valuesProjection hPD xD} : Set (ValuesOn P (swigΩ Ω)))) hmap
    _ =
      ((MX.obsKernel sDo).map (valuesProjection hPobsMX))
        ({valuesProjection hPobsMX (extend xD)} : Set (ValuesOn P (swigΩ Ω))) := by
          rw [hpointMX]
    _ = MX.qLocalMass sDo P hPobsMX (extend xD) := hq
    _ = ∏ C ∈ H.cComponentSet,
        MX.qLocalMass sDo (C ∩ P)
          (fun _ hv => hPclosed.1 (Finset.mem_of_mem_inter_right hv)) (extend xD) := by
          calc
            MX.qLocalMass sDo P hPobsMX (extend xD) =
              ∏ U ∈ H.cComponentSet,
                if hU : U ∈ H.cComponentSet then
                  MX.qLocalMass sDo (U ∩ P)
                    (fun _ hv => h𝒞obs U hU (Finset.mem_of_mem_inter_left hv))
                    (extend xD)
                else 1 := by
                  simpa [P] using hfac
            _ = ∏ C ∈ H.cComponentSet,
                MX.qLocalMass sDo (C ∩ P)
                  (fun _ hv => hPclosed.1 (Finset.mem_of_mem_inter_right hv))
                  (extend xD) := by
                  refine Finset.prod_congr rfl ?_
                  intro C hC
                  simp [hC]

/-- **(B) Tian Lemma 1 for the do-model ancestral marginal.**  The district
density extracted from the do-law ancestral marginal equals the corresponding
mechanism c-factor in the do-model. -/
theorem tianDistrictDensity_eq_mechCFactor_doModel
    [∀ n, Nonempty (Ω n)]
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (Y : Finset (SWIGNode N))
    (ref : Causalean.SCM.ReferenceMeasures Ω)
    (href : Causalean.SCM.ReferenceFaithful ref)
    (sDo : (M.fixSet X hObs hFix).FixedValues)
    (hpos : ∀ s' : M.FixedValues, DiscreteID.PositiveMass (M.obsKernel s'))
    (hYX : ∀ d ∈ X, SWIGNode.random d ∉ Y)
    (hStd : M.isStandard)
    (S : Finset (SWIGNode N))
    (hS : S ∈ fixTruncCComponentSet M X hObs hFix Y)
    (hSfull : S ∈ M.toSWIGGraph.cComponentSet)
    [MeasureTheory.IsFiniteMeasure
      (doObsKernelAncestralMarginal M X hObs hFix Y sDo)]
    [∀ (k : ℕ) (hk : k < (fixObservedAncestralSet M X hObs hFix Y).card),
      StandardBorelSpace
        (ValuesOn
          ({(((M.fixSet X hObs hFix).toSWIGGraph.induce
              (fixAncestralSet M X hObs hFix Y)).nodesAt
                (fixObservedAncestralSet M X hObs hFix Y) ⟨k, hk⟩).val} :
            Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < (fixObservedAncestralSet M X hObs hFix Y).card),
      Nonempty
        (ValuesOn
          ({(((M.fixSet X hObs hFix).toSWIGGraph.induce
              (fixAncestralSet M X hObs hFix Y)).nodesAt
                (fixObservedAncestralSet M X hObs hFix Y) ⟨k, hk⟩).val} :
            Finset (SWIGNode N)) (swigΩ Ω))]
    (extend :
      ValuesOn (fixObservedAncestralSet M X hObs hFix Y) (swigΩ Ω) →
        ValuesOn M.observed (swigΩ Ω))
    (hExtend : ∀ xD, valuesProjection
        (show fixObservedAncestralSet M X hObs hFix Y ⊆ M.observed from
          Finset.inter_subset_right) (extend xD) = xD)
    (xD : ValuesOn (fixObservedAncestralSet M X hObs hFix Y) (swigΩ Ω)) :
    tianDistrictDensity
        ((M.fixSet X hObs hFix).toSWIGGraph.induce
          (fixAncestralSet M X hObs hFix Y))
        (fixObservedAncestralSet M X hObs hFix Y)
        (doObsKernelAncestralMarginal M X hObs hFix Y sDo) ref S xD
      = (M.fixSet X hObs hFix).mechCFactor ref S
          (by
            have hSobs : S ⊆ M.observed :=
              M.toSWIGGraph.cComponentSet_subset_observed S hSfull
            simpa [SCM.fixSet_observed] using hSobs)
          sDo (extend xD) := by
  classical
  let MX := M.fixSet X hObs hFix
  let D := fixObservedAncestralSet M X hObs hFix Y
  let H := MX.toSWIGGraph.induce (fixAncestralSet M X hObs hFix Y)
  let μ : MeasureTheory.Measure (ValuesOn D (swigΩ Ω)) :=
    doObsKernelAncestralMarginal M X hObs hFix Y sDo
  have hDobs : D ⊆ MX.observed := Finset.inter_subset_right
  have hSdoComp : S ∈ MX.toSWIGGraph.cComponentSet := by
    exact (fixSet_cComponentSet_mem M X hObs hFix S).mpr hSfull
  have hSobsMX : S ⊆ MX.observed :=
    MX.toSWIGGraph.cComponentSet_subset_observed S hSdoComp
  have hSobsM : S ⊆ M.observed :=
    M.toSWIGGraph.cComponentSet_subset_observed S hSfull
  have hSD : S ⊆ D := by
    have hSHobs : S ⊆ H.observed := by
      exact H.cComponentSet_subset_observed S (by
        simpa [H, MX, fixTruncCComponentSet] using hS)
    simpa [H, D, MX, fixObservedAncestralSet] using hSHobs
  have hμpos : DiscreteID.PositiveMass μ := by
    simpa [μ] using
      doObsKernelAncestralMarginal_positiveMass M X hObs hFix Y hpos hYX sDo
  have hprefixMass_ne0 : ∀ k,
      (μ.map (valuesProjection (H.prefixIn_subset D k)))
        ({valuesProjection (H.prefixIn_subset D k) xD} :
          Set (ValuesOn (H.prefixIn D k) (swigΩ Ω))) ≠ 0 := by
    intro k
    have hmapPos :=
      DiscreteID.PositiveMass.map_valuesProjection (Ω' := swigΩ Ω)
        hμpos (H.prefixIn_subset D k)
    simpa [DiscreteID.singletonMass_apply] using
      hmapPos (valuesProjection (H.prefixIn_subset D k) xD)
  have hprefixProd_eq : ∀ k,
      (μ.map (valuesProjection (H.prefixIn_subset D k)))
        ({valuesProjection (H.prefixIn_subset D k) xD} :
          Set (ValuesOn (H.prefixIn D k) (swigΩ Ω))) =
        ∏ C ∈ MX.toSWIGGraph.cComponentSet,
          MX.qLocalMass sDo (C ∩ H.prefixIn D k)
            (fun _ hv => hDobs (H.prefixIn_subset D k
              (Finset.mem_of_mem_inter_right hv))) (extend xD) := by
    intro k
    simpa [MX, D, H, μ, hDobs] using
      doObsKernelAncestralMarginal_prefix_singleton_eq_prod_qLocalMass
        M X hObs hFix Y sDo extend hExtend k xD
  have hprefixProd_ne0 : ∀ k,
      (∏ C ∈ MX.toSWIGGraph.cComponentSet,
          MX.qLocalMass sDo (C ∩ H.prefixIn D k)
            (fun _ hv => hDobs (H.prefixIn_subset D k
              (Finset.mem_of_mem_inter_right hv))) (extend xD)) ≠ 0 := by
    intro k hzero
    exact hprefixMass_ne0 k (by rw [hprefixProd_eq k, hzero])
  have hfactor_ne0 : ∀ k C, C ∈ MX.toSWIGGraph.cComponentSet →
      MX.qLocalMass sDo (C ∩ H.prefixIn D k)
        (fun _ hv => hDobs (H.prefixIn_subset D k
          (Finset.mem_of_mem_inter_right hv))) (extend xD) ≠ 0 := by
    intro k C hC
    exact (Finset.prod_ne_zero_iff.mp (hprefixProd_ne0 k)) C hC
  have hS_q_ne0 : ∀ k ≤ D.card,
      MX.qLocalMass sDo (S ∩ H.prefixIn D k)
        (fun _ hv => hSobsMX (Finset.mem_of_mem_inter_left hv)) (extend xD) ≠ 0 := by
    intro k _hk
    simpa [hDobs, hSobsMX] using hfactor_ne0 k S hSdoComp
  have hpointS :
      valuesProjection hSobsMX (extend xD) = valuesProjection hSD xD := by
    have h :=
      valuesProjection_extend_eq_of_subset M
        (show D ⊆ M.observed from Finset.inter_subset_right)
        hSD hSobsM extend hExtend xD
    simpa [MX, SCM.fixSet_observed, hSobsMX, hSobsM] using h
  have hstep : ∀ i ∈ Finset.univ.filter
      (fun i : Fin D.card => (H.nodesAt D i).val ∈ S),
      tianPrefixStepDensity H D μ ref i xD =
        (MX.qLocalMass sDo (S ∩ H.prefixIn D (i.val + 1))
            (fun _ hv => hSobsMX (Finset.mem_of_mem_inter_left hv)) (extend xD) /
          MX.qLocalMass sDo (S ∩ H.prefixIn D i.val)
            (fun _ hv => hSobsMX (Finset.mem_of_mem_inter_left hv)) (extend xD)) /
        jointRef ref ({(H.nodesAt D i).val} : Finset (SWIGNode N))
          ({valuesProjection
            (show ({(H.nodesAt D i).val} : Finset (SWIGNode N)) ⊆ D from by
              intro v hv
              rw [Finset.mem_singleton] at hv
              exact hv ▸ (H.nodesAt D i).property) xD} :
            Set (ValuesOn ({(H.nodesAt D i).val} : Finset (SWIGNode N)) (swigΩ Ω))) := by
    intro i hi
    have hiS : (H.nodesAt D i).val ∈ S := (Finset.mem_filter.mp hi).2
    have hmass :=
      tianPrefixStepDensity_eq_prefix_mass_ratio H D μ ref href i xD
        (hprefixMass_ne0 i.val)
    have hrest0 :
        (∏ C ∈ MX.toSWIGGraph.cComponentSet \ {S},
          MX.qLocalMass sDo (C ∩ H.prefixIn D i.val)
            (fun _ hv => hDobs (H.prefixIn_subset D i.val
              (Finset.mem_of_mem_inter_right hv))) (extend xD)) ≠ 0 := by
      exact Finset.prod_ne_zero_iff.mpr (by
        intro C hC
        exact hfactor_ne0 i.val C (Finset.mem_sdiff.mp hC).1)
    have hcancel :=
      prefixIn_qProduct_ratio_eq_component_ratio_of_ne_zero
        MX H D sDo S hSdoComp i hDobs hiS (extend xD) hrest0
    calc
      tianPrefixStepDensity H D μ ref i xD
          =
        (((∏ C ∈ MX.toSWIGGraph.cComponentSet,
          MX.qLocalMass sDo (C ∩ H.prefixIn D (i.val + 1))
            (fun _ hv => hDobs (H.prefixIn_subset D (i.val + 1)
              (Finset.mem_of_mem_inter_right hv))) (extend xD)) /
          (∏ C ∈ MX.toSWIGGraph.cComponentSet,
          MX.qLocalMass sDo (C ∩ H.prefixIn D i.val)
            (fun _ hv => hDobs (H.prefixIn_subset D i.val
              (Finset.mem_of_mem_inter_right hv))) (extend xD))) /
        jointRef ref ({(H.nodesAt D i).val} : Finset (SWIGNode N))
          ({valuesProjection
            (show ({(H.nodesAt D i).val} : Finset (SWIGNode N)) ⊆ D from by
              intro v hv
              rw [Finset.mem_singleton] at hv
              exact hv ▸ (H.nodesAt D i).property) xD} :
            Set (ValuesOn ({(H.nodesAt D i).val} : Finset (SWIGNode N)) (swigΩ Ω)))) := by
            rw [hmass, hprefixProd_eq (i.val + 1), hprefixProd_eq i.val]
      _ =
        (MX.qLocalMass sDo (S ∩ H.prefixIn D (i.val + 1))
            (fun _ hv => hSobsMX (Finset.mem_of_mem_inter_left hv)) (extend xD) /
          MX.qLocalMass sDo (S ∩ H.prefixIn D i.val)
            (fun _ hv => hSobsMX (Finset.mem_of_mem_inter_left hv)) (extend xD)) /
        jointRef ref ({(H.nodesAt D i).val} : Finset (SWIGNode N))
          ({valuesProjection
            (show ({(H.nodesAt D i).val} : Finset (SWIGNode N)) ⊆ D from by
              intro v hv
              rw [Finset.mem_singleton] at hv
              exact hv ▸ (H.nodesAt D i).property) xD} :
            Set (ValuesOn ({(H.nodesAt D i).val} : Finset (SWIGNode N)) (swigΩ Ω))) := by
            rw [hcancel]
  let idxS := Finset.univ.filter (fun i : Fin D.card => (H.nodesAt D i).val ∈ S)
  let qratio : Fin D.card → ENNReal := fun i =>
    MX.qLocalMass sDo (S ∩ H.prefixIn D (i.val + 1))
      (fun _ hv => hSobsMX (Finset.mem_of_mem_inter_left hv)) (extend xD) /
    MX.qLocalMass sDo (S ∩ H.prefixIn D i.val)
      (fun _ hv => hSobsMX (Finset.mem_of_mem_inter_left hv)) (extend xD)
  let den : Fin D.card → ENNReal := fun i =>
    jointRef ref ({(H.nodesAt D i).val} : Finset (SWIGNode N))
      ({valuesProjection
        (show ({(H.nodesAt D i).val} : Finset (SWIGNode N)) ⊆ D from by
          intro v hv
          rw [Finset.mem_singleton] at hv
          exact hv ▸ (H.nodesAt D i).property) xD} :
        Set (ValuesOn ({(H.nodesAt D i).val} : Finset (SWIGNode N)) (swigΩ Ω)))
  have hden0 : ∀ i ∈ idxS, den i ≠ 0 := by
    intro i _hi
    exact jointRef_singleton_ne_zero ref href _ _
  have hdentop : ∀ i ∈ idxS, den i ≠ ∞ := by
    intro i _hi
    exact ne_of_lt (MeasureTheory.measure_lt_top
      (jointRef ref ({(H.nodesAt D i).val} : Finset (SWIGNode N))) _)
  have hqprod :
      (∏ i ∈ idxS, qratio i) =
        MX.qLocalMass sDo S hSobsMX (extend xD) := by
    simpa [idxS, qratio] using
      component_qLocalMass_ratio_product_prefixIn_of_ne_zero
        MX H D sDo S hSobsMX hSD (extend xD) hS_q_ne0
  have hdenprod :
      (∏ i ∈ idxS, den i) =
        jointRef ref S ({valuesProjection hSD xD} :
          Set (ValuesOn S (swigΩ Ω))) := by
    have hden_atom :
        (∏ i ∈ idxS, den i) =
          ∏ i ∈ idxS,
            ref.μ (H.nodesAt D i).val
              ({xD (H.nodesAt D i)} : Set (swigΩ Ω (H.nodesAt D i).val)) := by
      refine Finset.prod_congr rfl ?_
      intro i hi
      dsimp [den]
      rw [jointRef_singleton_eq_prod]
      simp [valuesProjection]
    rw [hden_atom]
    simpa [idxS] using component_ref_atom_product_eq_jointRef_prefixIn H D ref S hSD xD
  have htian :
      tianDistrictDensity H D μ ref S xD =
        MX.qLocalMass sDo S hSobsMX (extend xD) /
          jointRef ref S ({valuesProjection hSD xD} :
            Set (ValuesOn S (swigΩ Ω))) := by
    unfold tianDistrictDensity
    calc
      (∏ i ∈ Finset.univ.filter (fun i : Fin D.card => (H.nodesAt D i).val ∈ S),
        tianPrefixStepDensity H D μ ref i xD)
          = ∏ i ∈ idxS, qratio i / den i := by
            refine Finset.prod_congr ?_ ?_
            · simp [idxS]
            · intro i hi
              simpa [idxS, qratio, den] using hstep i (by simpa [idxS] using hi)
      _ = (∏ i ∈ idxS, qratio i) / (∏ i ∈ idxS, den i) := by
            exact ENNReal.prod_div_prod_qfactor idxS qratio den hden0 hdentop
      _ = MX.qLocalMass sDo S hSobsMX (extend xD) /
          jointRef ref S ({valuesProjection hSD xD} :
            Set (ValuesOn S (swigΩ Ω))) := by
            rw [hqprod, hdenprod]
  have hmech :
      MX.mechCFactor ref S hSobsMX sDo (extend xD) =
        MX.qLocalMass sDo S hSobsMX (extend xD) /
          jointRef ref S ({valuesProjection hSobsMX (extend xD)} :
            Set (ValuesOn S (swigΩ Ω))) := by
    simpa [MX] using
      doModel_mechCFactor_eq_qLocalMass_div_jointRef
        M X hObs hFix hStd ref href sDo S hSobsMX (extend xD)
  rw [show
      tianDistrictDensity
          ((M.fixSet X hObs hFix).toSWIGGraph.induce
            (fixAncestralSet M X hObs hFix Y))
          (fixObservedAncestralSet M X hObs hFix Y)
          (doObsKernelAncestralMarginal M X hObs hFix Y sDo) ref S xD =
        tianDistrictDensity H D μ ref S xD by rfl]
  rw [htian, hmech, hpointS]

/-- The Tian district density for any district of the post-intervention
ancestral graph collapses to the matching do-model local q-mass divided by the
district reference atom.  Unlike
`tianDistrictDensity_eq_mechCFactor_doModel`, this statement does not require
the district to be a full c-component of the original graph. -/
theorem tianDistrictDensity_eq_qLocalMass_div_jointRef_district
    [∀ n, Nonempty (Ω n)]
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (Y : Finset (SWIGNode N))
    (ref : Causalean.SCM.ReferenceMeasures Ω)
    (href : Causalean.SCM.ReferenceFaithful ref)
    (sDo : (M.fixSet X hObs hFix).FixedValues)
    (hpos : ∀ s' : M.FixedValues, DiscreteID.PositiveMass (M.obsKernel s'))
    (hYX : ∀ d ∈ X, SWIGNode.random d ∉ Y)
    (S : Finset (SWIGNode N))
    (hS : S ∈ fixTruncCComponentSet M X hObs hFix Y)
    [MeasureTheory.IsFiniteMeasure
      (doObsKernelAncestralMarginal M X hObs hFix Y sDo)]
    [∀ (k : ℕ) (hk : k < (fixObservedAncestralSet M X hObs hFix Y).card),
      StandardBorelSpace
        (ValuesOn
          ({(((M.fixSet X hObs hFix).toSWIGGraph.induce
              (fixAncestralSet M X hObs hFix Y)).nodesAt
                (fixObservedAncestralSet M X hObs hFix Y) ⟨k, hk⟩).val} :
            Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < (fixObservedAncestralSet M X hObs hFix Y).card),
      Nonempty
        (ValuesOn
          ({(((M.fixSet X hObs hFix).toSWIGGraph.induce
              (fixAncestralSet M X hObs hFix Y)).nodesAt
                (fixObservedAncestralSet M X hObs hFix Y) ⟨k, hk⟩).val} :
            Finset (SWIGNode N)) (swigΩ Ω))]
    (extend :
      ValuesOn (fixObservedAncestralSet M X hObs hFix Y) (swigΩ Ω) →
        ValuesOn M.observed (swigΩ Ω))
    (hExtend : ∀ xD, valuesProjection
        (show fixObservedAncestralSet M X hObs hFix Y ⊆ M.observed from
          Finset.inter_subset_right) (extend xD) = xD)
    (xD : ValuesOn (fixObservedAncestralSet M X hObs hFix Y) (swigΩ Ω)) :
    let MX := M.fixSet X hObs hFix
    let D := fixObservedAncestralSet M X hObs hFix Y
    let H := MX.toSWIGGraph.induce (fixAncestralSet M X hObs hFix Y)
    tianDistrictDensity H D
        (doObsKernelAncestralMarginal M X hObs hFix Y sDo) ref S xD
      =
      MX.qLocalMass sDo S
          (show S ⊆ MX.observed from by
            intro v hv
            have hSHobs : S ⊆ H.observed :=
              H.cComponentSet_subset_observed S
                (by simpa [H, MX, fixTruncCComponentSet] using hS)
            have hvD : v ∈ D := by
              dsimp [H, D, SWIGGraph.induce, fixObservedAncestralSet] at hSHobs ⊢
              simpa using hSHobs hv
            exact (Finset.mem_inter.mp hvD).2)
          (extend xD) /
        jointRef ref S
          ({valuesProjection
            (show S ⊆ D from by
              intro v hv
              have hSHobs : S ⊆ H.observed :=
                H.cComponentSet_subset_observed S
                  (by simpa [H, MX, fixTruncCComponentSet] using hS)
              dsimp [H, D, SWIGGraph.induce, fixObservedAncestralSet] at hSHobs ⊢
              simpa using hSHobs hv) xD} :
            Set (ValuesOn S (swigΩ Ω))) := by
  classical
  let MX := M.fixSet X hObs hFix
  let D := fixObservedAncestralSet M X hObs hFix Y
  let H := MX.toSWIGGraph.induce (fixAncestralSet M X hObs hFix Y)
  let μ : MeasureTheory.Measure (ValuesOn D (swigΩ Ω)) :=
    doObsKernelAncestralMarginal M X hObs hFix Y sDo
  have hDobs : D ⊆ MX.observed := Finset.inter_subset_right
  have hScomp : S ∈ H.cComponentSet := by
    simpa [H, MX, fixTruncCComponentSet] using hS
  have hSobsMX : S ⊆ MX.observed := by
    intro v hv
    have hSHobs : S ⊆ H.observed := H.cComponentSet_subset_observed S hScomp
    have hvD : v ∈ D := by
      dsimp [H, D, SWIGGraph.induce, fixObservedAncestralSet] at hSHobs ⊢
      simpa using hSHobs hv
    exact (Finset.mem_inter.mp hvD).2
  have hSD : S ⊆ D := by
    intro v hv
    have hSHobs : S ⊆ H.observed := H.cComponentSet_subset_observed S hScomp
    dsimp [H, D, SWIGGraph.induce, fixObservedAncestralSet] at hSHobs ⊢
    simpa using hSHobs hv
  have hdisj :
      (↑H.cComponentSet : Set (Finset (SWIGNode N))).Pairwise
        (fun U U' => Disjoint U U') := by
    intro U hU V hV hne
    exact H.cComponentSet_pairwise_disjoint hU hV hne
  have hμpos : DiscreteID.PositiveMass μ := by
    simpa [μ] using
      doObsKernelAncestralMarginal_positiveMass M X hObs hFix Y hpos hYX sDo
  have hprefixMass_ne0 : ∀ k,
      (μ.map (valuesProjection (H.prefixIn_subset D k)))
        ({valuesProjection (H.prefixIn_subset D k) xD} :
          Set (ValuesOn (H.prefixIn D k) (swigΩ Ω))) ≠ 0 := by
    intro k
    have hmapPos :=
      DiscreteID.PositiveMass.map_valuesProjection (Ω' := swigΩ Ω)
        hμpos (H.prefixIn_subset D k)
    simpa [DiscreteID.singletonMass_apply] using
      hmapPos (valuesProjection (H.prefixIn_subset D k) xD)
  have hprefixProd_eq : ∀ k,
      (μ.map (valuesProjection (H.prefixIn_subset D k)))
        ({valuesProjection (H.prefixIn_subset D k) xD} :
          Set (ValuesOn (H.prefixIn D k) (swigΩ Ω))) =
        ∏ C ∈ H.cComponentSet,
          MX.qLocalMass sDo (C ∩ H.prefixIn D k)
            (fun _ hv => hDobs (H.prefixIn_subset D k
              (Finset.mem_of_mem_inter_right hv))) (extend xD) := by
    intro k
    simpa [MX, D, H, μ, hDobs] using
      doObsKernelAncestralMarginal_prefix_singleton_eq_prod_H_qLocalMass
        M X hObs hFix Y sDo extend hExtend k xD
  have hprefixProd_ne0 : ∀ k,
      (∏ C ∈ H.cComponentSet,
          MX.qLocalMass sDo (C ∩ H.prefixIn D k)
            (fun _ hv => hDobs (H.prefixIn_subset D k
              (Finset.mem_of_mem_inter_right hv))) (extend xD)) ≠ 0 := by
    intro k hzero
    exact hprefixMass_ne0 k (by rw [hprefixProd_eq k, hzero])
  have hfactor_ne0 : ∀ k C, C ∈ H.cComponentSet →
      MX.qLocalMass sDo (C ∩ H.prefixIn D k)
        (fun _ hv => hDobs (H.prefixIn_subset D k
          (Finset.mem_of_mem_inter_right hv))) (extend xD) ≠ 0 := by
    intro k C hC
    exact (Finset.prod_ne_zero_iff.mp (hprefixProd_ne0 k)) C hC
  have hS_q_ne0 : ∀ k ≤ D.card,
      MX.qLocalMass sDo (S ∩ H.prefixIn D k)
        (fun _ hv => hSobsMX (Finset.mem_of_mem_inter_left hv)) (extend xD) ≠ 0 := by
    intro k _hk
    simpa [hDobs, hSobsMX] using hfactor_ne0 k S hScomp
  have hstep : ∀ i ∈ Finset.univ.filter
      (fun i : Fin D.card => (H.nodesAt D i).val ∈ S),
      tianPrefixStepDensity H D μ ref i xD =
        (MX.qLocalMass sDo (S ∩ H.prefixIn D (i.val + 1))
            (fun _ hv => hSobsMX (Finset.mem_of_mem_inter_left hv)) (extend xD) /
          MX.qLocalMass sDo (S ∩ H.prefixIn D i.val)
            (fun _ hv => hSobsMX (Finset.mem_of_mem_inter_left hv)) (extend xD)) /
        jointRef ref ({(H.nodesAt D i).val} : Finset (SWIGNode N))
          ({valuesProjection
            (show ({(H.nodesAt D i).val} : Finset (SWIGNode N)) ⊆ D from by
              intro v hv
              rw [Finset.mem_singleton] at hv
              exact hv ▸ (H.nodesAt D i).property) xD} :
            Set (ValuesOn ({(H.nodesAt D i).val} : Finset (SWIGNode N)) (swigΩ Ω))) := by
    intro i hi
    have hiS : (H.nodesAt D i).val ∈ S := (Finset.mem_filter.mp hi).2
    have hmass :=
      tianPrefixStepDensity_eq_prefix_mass_ratio H D μ ref href i xD
        (hprefixMass_ne0 i.val)
    have hrest0 :
        (∏ C ∈ H.cComponentSet \ {S},
          MX.qLocalMass sDo (C ∩ H.prefixIn D i.val)
            (fun _ hv => hDobs (H.prefixIn_subset D i.val
              (Finset.mem_of_mem_inter_right hv))) (extend xD)) ≠ 0 := by
      exact Finset.prod_ne_zero_iff.mpr (by
        intro C hC
        exact hfactor_ne0 i.val C (Finset.mem_sdiff.mp hC).1)
    have hcancel :=
      prefixIn_qProduct_ratio_eq_component_ratio_of_family_of_ne_zero
        MX H D sDo H.cComponentSet S hScomp hdisj i hDobs hiS (extend xD) hrest0
    calc
      tianPrefixStepDensity H D μ ref i xD
          =
        (((∏ C ∈ H.cComponentSet,
          MX.qLocalMass sDo (C ∩ H.prefixIn D (i.val + 1))
            (fun _ hv => hDobs (H.prefixIn_subset D (i.val + 1)
              (Finset.mem_of_mem_inter_right hv))) (extend xD)) /
          (∏ C ∈ H.cComponentSet,
          MX.qLocalMass sDo (C ∩ H.prefixIn D i.val)
            (fun _ hv => hDobs (H.prefixIn_subset D i.val
              (Finset.mem_of_mem_inter_right hv))) (extend xD))) /
        jointRef ref ({(H.nodesAt D i).val} : Finset (SWIGNode N))
          ({valuesProjection
            (show ({(H.nodesAt D i).val} : Finset (SWIGNode N)) ⊆ D from by
              intro v hv
              rw [Finset.mem_singleton] at hv
              exact hv ▸ (H.nodesAt D i).property) xD} :
            Set (ValuesOn ({(H.nodesAt D i).val} : Finset (SWIGNode N)) (swigΩ Ω)))) := by
            rw [hmass, hprefixProd_eq (i.val + 1), hprefixProd_eq i.val]
      _ =
        (MX.qLocalMass sDo (S ∩ H.prefixIn D (i.val + 1))
            (fun _ hv => hSobsMX (Finset.mem_of_mem_inter_left hv)) (extend xD) /
          MX.qLocalMass sDo (S ∩ H.prefixIn D i.val)
            (fun _ hv => hSobsMX (Finset.mem_of_mem_inter_left hv)) (extend xD)) /
        jointRef ref ({(H.nodesAt D i).val} : Finset (SWIGNode N))
          ({valuesProjection
            (show ({(H.nodesAt D i).val} : Finset (SWIGNode N)) ⊆ D from by
              intro v hv
              rw [Finset.mem_singleton] at hv
              exact hv ▸ (H.nodesAt D i).property) xD} :
            Set (ValuesOn ({(H.nodesAt D i).val} : Finset (SWIGNode N)) (swigΩ Ω))) := by
            rw [hcancel]
  let idxS := Finset.univ.filter (fun i : Fin D.card => (H.nodesAt D i).val ∈ S)
  let qratio : Fin D.card → ENNReal := fun i =>
    MX.qLocalMass sDo (S ∩ H.prefixIn D (i.val + 1))
      (fun _ hv => hSobsMX (Finset.mem_of_mem_inter_left hv)) (extend xD) /
    MX.qLocalMass sDo (S ∩ H.prefixIn D i.val)
      (fun _ hv => hSobsMX (Finset.mem_of_mem_inter_left hv)) (extend xD)
  let den : Fin D.card → ENNReal := fun i =>
    jointRef ref ({(H.nodesAt D i).val} : Finset (SWIGNode N))
      ({valuesProjection
        (show ({(H.nodesAt D i).val} : Finset (SWIGNode N)) ⊆ D from by
          intro v hv
          rw [Finset.mem_singleton] at hv
          exact hv ▸ (H.nodesAt D i).property) xD} :
        Set (ValuesOn ({(H.nodesAt D i).val} : Finset (SWIGNode N)) (swigΩ Ω)))
  have hden0 : ∀ i ∈ idxS, den i ≠ 0 := by
    intro i _hi
    exact jointRef_singleton_ne_zero ref href _ _
  have hdentop : ∀ i ∈ idxS, den i ≠ ∞ := by
    intro i _hi
    exact ne_of_lt (MeasureTheory.measure_lt_top
      (jointRef ref ({(H.nodesAt D i).val} : Finset (SWIGNode N))) _)
  have hqprod :
      (∏ i ∈ idxS, qratio i) =
        MX.qLocalMass sDo S hSobsMX (extend xD) := by
    simpa [idxS, qratio] using
      component_qLocalMass_ratio_product_prefixIn_of_ne_zero
        MX H D sDo S hSobsMX hSD (extend xD) hS_q_ne0
  have hdenprod :
      (∏ i ∈ idxS, den i) =
        jointRef ref S ({valuesProjection hSD xD} :
          Set (ValuesOn S (swigΩ Ω))) := by
    have hden_atom :
        (∏ i ∈ idxS, den i) =
          ∏ i ∈ idxS,
            ref.μ (H.nodesAt D i).val
              ({xD (H.nodesAt D i)} : Set (swigΩ Ω (H.nodesAt D i).val)) := by
      refine Finset.prod_congr rfl ?_
      intro i hi
      dsimp [den]
      rw [jointRef_singleton_eq_prod]
      simp [valuesProjection]
    rw [hden_atom]
    simpa [idxS] using component_ref_atom_product_eq_jointRef_prefixIn H D ref S hSD xD
  have htian :
      tianDistrictDensity H D μ ref S xD =
        MX.qLocalMass sDo S hSobsMX (extend xD) /
          jointRef ref S ({valuesProjection hSD xD} :
            Set (ValuesOn S (swigΩ Ω))) := by
    unfold tianDistrictDensity
    calc
      (∏ i ∈ Finset.univ.filter (fun i : Fin D.card => (H.nodesAt D i).val ∈ S),
        tianPrefixStepDensity H D μ ref i xD)
          = ∏ i ∈ idxS, qratio i / den i := by
            refine Finset.prod_congr ?_ ?_
            · simp [idxS]
            · intro i hi
              simpa [idxS, qratio, den] using hstep i (by simpa [idxS] using hi)
      _ = (∏ i ∈ idxS, qratio i) / (∏ i ∈ idxS, den i) := by
            exact ENNReal.prod_div_prod_qfactor idxS qratio den hden0 hdentop
      _ = MX.qLocalMass sDo S hSobsMX (extend xD) /
          jointRef ref S ({valuesProjection hSD xD} :
            Set (ValuesOn S (swigΩ Ω))) := by
            rw [hqprod, hdenprod]
  simpa [MX, D, H, μ] using htian

/-- **District recovery (Tian Lemma 4 projection consistency).**

For a district `S` of the post-intervention ancestral graph `H = G_X[D]`
(`D := fixObservedAncestralSet`) that is also a full c-component of `M`, the
`S`-district factor extracted from the do-law ancestral marginal
`ν_M = (M.fixSet X).obsKernel.map π_D` equals, almost everywhere, the full
observational c-component factor `Q_M[S]` pulled back along any extension
`extend` that is the identity on the ancestral observed coordinates `D`.

Both sides are the same c-factor `Q[S]`: the left reads it from the do(X)-law
ancestral marginal, while the right reads it from the observational law.  They
agree because Tian's c-factor invariance leaves a full c-component avoiding the
intervention set unchanged under `do(X)`.  This theorem packages the final
projection-consistency step used by the density-level ID assembly. -/
lemma tian_full_cComponent_density_recovery_core_direct
    [∀ n, Nonempty (Ω n)]
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hStd : M.isStandard)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (Y : Finset (SWIGNode N))
    (ref : Causalean.SCM.ReferenceMeasures Ω)
    (href : Causalean.SCM.ReferenceFaithful ref)
    (sDo : (M.fixSet X hObs hFix).FixedValues)
    (S : Finset (SWIGNode N))
    (hS : S ∈ fixTruncCComponentSet M X hObs hFix Y)
    (hSfull : S ∈ M.toSWIGGraph.cComponentSet)
    [MeasureTheory.IsFiniteMeasure
      (doObsKernelAncestralMarginal M X hObs hFix Y sDo)]
    [∀ s' : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.obsKernel s')]
    [∀ (k : ℕ) (hk : k < (fixObservedAncestralSet M X hObs hFix Y).card),
      StandardBorelSpace
        (ValuesOn
          ({(((M.fixSet X hObs hFix).toSWIGGraph.induce
              (fixAncestralSet M X hObs hFix Y)).nodesAt
                (fixObservedAncestralSet M X hObs hFix Y) ⟨k, hk⟩).val} :
            Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < (fixObservedAncestralSet M X hObs hFix Y).card),
      Nonempty
        (ValuesOn
          ({(((M.fixSet X hObs hFix).toSWIGGraph.induce
              (fixAncestralSet M X hObs hFix Y)).nodesAt
                (fixObservedAncestralSet M X hObs hFix Y) ⟨k, hk⟩).val} :
            Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      StandardBorelSpace
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      Nonempty
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ k : ℕ,
      MeasurableSpace.CountableOrCountablyGenerated
        M.FixedValues (ValuesOn (M.prefixNodes k) (swigΩ Ω))]
    (hpos : ∀ s' : M.FixedValues, DiscreteID.PositiveMass (M.obsKernel s'))
    (hYX : ∀ D ∈ X, SWIGNode.random D ∉ Y)
    (extend :
      ValuesOn (fixObservedAncestralSet M X hObs hFix Y) (swigΩ Ω) →
        ValuesOn M.observed (swigΩ Ω))
    (hExtend : ∀ xD, valuesProjection
        (show fixObservedAncestralSet M X hObs hFix Y ⊆ M.observed from
          Finset.inter_subset_right) (extend xD) = xD)
    (hExtendX : ∀ xD (D : N) (hD : D ∈ X),
      extend xD ⟨SWIGNode.random D, hObs D hD⟩ =
        sDo ⟨SWIGNode.fixed D,
          Finset.mem_union_right _
            (Finset.mem_image.mpr ⟨D, hD, rfl⟩)⟩) :
    let D := fixObservedAncestralSet M X hObs hFix Y
    let H := (M.fixSet X hObs hFix).toSWIGGraph.induce
      (fixAncestralSet M X hObs hFix Y)
    tianDistrictDensity H D
        (doObsKernelAncestralMarginal M X hObs hFix Y sDo) ref S
      =ᵐ[Causalean.SCM.jointRef ref D]
        fun xD =>
          M.cComponentDensityFactor ref
            (M.fixSetProj X hObs hFix sDo) S (extend xD) := by
  classical
  let D := fixObservedAncestralSet M X hObs hFix Y
  let H := (M.fixSet X hObs hFix).toSWIGGraph.induce
    (fixAncestralSet M X hObs hFix Y)
  have hSobs : S ⊆ M.observed :=
    M.toSWIGGraph.cComponentSet_subset_observed S hSfull
  have hSD : S ⊆ D := by
    have hSHobs : S ⊆ H.observed := by
      exact H.cComponentSet_subset_observed S (by
        simpa [H, fixTruncCComponentSet] using hS)
    simpa [H, D, fixObservedAncestralSet] using hSHobs
  have hSX : ∀ n ∈ X, SWIGNode.random n ∉ S := by
    intro n hn hnS
    have hnD : SWIGNode.random n ∈ D := hSD hnS
    have hnA : SWIGNode.random n ∈ fixAncestralSet M X hObs hFix Y := by
      simpa [D, fixObservedAncestralSet] using (Finset.mem_inter.mp hnD).1
    exact hYX n hn
      ((random_intervened_mem_fixAncestralSet_iff_mem_Y M X hObs hFix Y hn).mp hnA)
  filter_upwards with xD
  have hB :
      tianDistrictDensity H D
          (doObsKernelAncestralMarginal M X hObs hFix Y sDo) ref S xD
        = (M.fixSet X hObs hFix).mechCFactor ref S
            (by simpa [SCM.fixSet_observed] using hSobs)
            sDo (extend xD) := by
    simpa [H, D] using
      tianDistrictDensity_eq_mechCFactor_doModel
        M X hObs hFix Y ref href sDo hpos hYX hStd S hS hSfull
        extend hExtend xD
  have hC :
      (M.fixSet X hObs hFix).mechCFactor ref S
          (by simpa [SCM.fixSet_observed] using hSobs)
          sDo (extend xD)
        = M.mechCFactor ref S hSobs
            (M.fixSetProj X hObs hFix sDo) (extend xD) := by
    simpa using
      Causalean.SCM.ID.mechCFactor_fixSet_invariant
        M ref X href hStd hObs hFix S hSobs hSX sDo (extend xD)
        (fun D hD => hExtendX xD D hD)
  have hA :
      M.mechCFactor ref S hSobs
          (M.fixSetProj X hObs hFix sDo) (extend xD)
        = M.cComponentDensityFactor ref
            (M.fixSetProj X hObs hFix sDo) S (extend xD) := by
    exact
      (Causalean.SCM.ID.cComponentDensityFactor_eq_mechCFactor
        M ref (M.fixSetProj X hObs hFix sDo) hStd S hSobs hSfull
        href (hpos (M.fixSetProj X hObs hFix sDo)) (extend xD)).symm
  exact hB.trans (hC.trans hA)

end SCM.ID
end Causalean
