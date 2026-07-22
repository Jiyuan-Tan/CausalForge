/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.SCM.ID.GraphicalThms.DoGFormula
import Causalean.SCM.ID.Density.CComponentDensity
import Causalean.SCM.ID.Density.QMass
import Causalean.SCM.ID.Density.DoLawMarginal
import Causalean.SCM.ID.Density.FiniteReference

/-!
# Mechanism c-factor `Q[S]` and its do(X)-invariance (Tian Lemma 4)

The recovery `tianDistrictDensity ν_M S =ᵐ cComponentDensityFactor M S` used by
the density route for ID soundness is, at bottom, the do(X)-invariance of the
c-factor `Q[S]` for a full c-component `S`.  This file isolates the
mechanism-level object carrying that content.

`mechCFactor M' S` is Tian's `Q[S] = P_{v∖s}(s)` (Eq. 36): intervene on every
observed node outside `S` *that is not already fixed in `M'`* (its do-complement)
and read off the `S`-marginal density.  The "not already fixed" clause makes the
definition apply to the **non-standard** do-model `M.fixSet X` (whose `fixed` set
is the fixed copies of `X`), which is what the invariance step compares against.

Decomposition of the recovery:

* `cComponentDensityFactor M S = mechCFactor M S` — Tian Lemma 1
  (Eq. 37 = Eq. 36): the observational full-prefix product is the
  do-complement marginal.
* `mechCFactor (M.fixSet X) S = mechCFactor M S` for c-components avoiding `X`:
  the c-factor is invariant under interventions outside the component.
* `tianDistrictDensity ν_M S = mechCFactor (M.fixSet X) S`: the district density
  in the do-law ancestral marginal is the corresponding mechanism c-factor.

Together these results identify the recovered district density with the
observational c-component density used by the ID soundness argument.
-/

set_option linter.unusedFintypeInType false

namespace Causalean

open scoped MeasureTheory ProbabilityTheory ENNReal BigOperators

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

namespace SCM

/-- Base-node names whose random copy lies in `M.observed \ S` and whose fixed
copy is **not already fixed** in `M` — the variables intervened on in Tian's
do-complement object `Q[S] = P_{v∖s}(s)`.  The "not already fixed" clause lets
this apply to non-standard models such as `M.fixSet X`. -/
noncomputable def mechComplementNames
    (M : Causalean.SCM N Ω) (S : Finset (SWIGNode N)) : Finset N :=
  Finset.univ.filter fun n =>
    SWIGNode.random n ∈ M.observed \ S ∧ SWIGNode.fixed n ∉ M.fixed

/-- Every mechanism-complement variable has its random copy among the observed nodes. -/
lemma mechComplementNames_random_mem_observed
    (M : Causalean.SCM N Ω) (S : Finset (SWIGNode N)) :
    ∀ n ∈ M.mechComplementNames S, SWIGNode.random n ∈ M.observed := by
  intro n hn
  exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hn).2.1).1

/-- Every mechanism-complement variable has a fixed copy that is not already fixed. -/
lemma mechComplementNames_fixed_not_mem
    (M : Causalean.SCM N Ω) (S : Finset (SWIGNode N)) :
    ∀ n ∈ M.mechComplementNames S, SWIGNode.fixed n ∉ M.fixed := by
  intro n hn
  exact (Finset.mem_filter.mp hn).2.2

/-- The random copies of the mechanism-complement variables form a subset of the observed nodes. -/
lemma mechComplementNames_image_random_subset_observed
    (M : Causalean.SCM N Ω) (S : Finset (SWIGNode N)) :
    (M.mechComplementNames S).image SWIGNode.random ⊆ M.observed := by
  intro v hv
  rcases Finset.mem_image.mp hv with ⟨n, hn, rfl⟩
  exact M.mechComplementNames_random_mem_observed S n hn

private lemma mechComplementNames_mem_of_random_observed_not_mem
    (M : Causalean.SCM N Ω) (S : Finset (SWIGNode N)) {n : N}
    (hobs : SWIGNode.random n ∈ M.observed)
    (hnotS : SWIGNode.random n ∉ S)
    (hfix : SWIGNode.fixed n ∉ M.fixed) :
    n ∈ M.mechComplementNames S := by
  rw [mechComplementNames, Finset.mem_filter]
  exact ⟨Finset.mem_univ n, Finset.mem_sdiff.mpr ⟨hobs, hnotS⟩, hfix⟩

private lemma mechComplement_fixSet_obsParentClosed
    (M : Causalean.SCM N Ω) (S : Finset (SWIGNode N)) (hS : S ⊆ M.observed)
    (hfe : ∀ n : N, SWIGNode.fixed n ∈ M.fixed →
      ∀ v : SWIGNode N, ¬ M.dag.edge (SWIGNode.random n) v) :
    (M.fixSet (M.mechComplementNames S)
      (M.mechComplementNames_random_mem_observed S)
      (M.mechComplementNames_fixed_not_mem S)).ObsParentClosed S := by
  classical
  refine ⟨by simpa [fixSet_observed] using hS, ?_⟩
  intro v hvS w hwObs hEdge
  by_contra hwNotS
  have hwObsM : w ∈ M.observed := by
    simpa [fixSet_observed] using hwObs
  rcases M.observed_is_random w hwObsM with ⟨n, rfl⟩
  by_cases hfix : SWIGNode.fixed n ∈ M.fixed
  · have hnW : n ∉ M.mechComplementNames S := by
      intro hn
      exact (M.mechComplementNames_fixed_not_mem S n hn) hfix
    have hEdgeRel :
        SWIGGraph.splitMonoEdgeRel M.toSWIGGraph.dag.edge
          (M.mechComplementNames S) (SWIGNode.random n) v := by
      simpa [fixSet, fixMono, SWIGGraph.splitMono, SWIGGraph.splitMonoDAG] using hEdge
    have hEdgeM : M.dag.edge (SWIGNode.random n) v := by
      simpa [SWIGGraph.splitMonoEdgeRel, hnW] using hEdgeRel
    exact hfe n hfix v hEdgeM
  · have hnW : n ∈ M.mechComplementNames S :=
      mechComplementNames_mem_of_random_observed_not_mem M S hwObsM hwNotS hfix
    have hEdgeRel :
        SWIGGraph.splitMonoEdgeRel M.toSWIGGraph.dag.edge
          (M.mechComplementNames S) (SWIGNode.random n) v := by
      simpa [fixSet, fixMono, SWIGGraph.splitMono, SWIGGraph.splitMonoDAG] using hEdge
    simp [SWIGGraph.splitMonoEdgeRel, hnW] at hEdgeRel

/-- Fixed-value slice for the do-complement SCM, read from a full observed
assignment: keep `M`'s existing fixed slice `s` and extend it on the
do-complement coordinates by projecting `x` to the random copies in `V∖S`. -/
noncomputable def mechDoValues
    (M : Causalean.SCM N Ω) (S : Finset (SWIGNode N))
    (s : M.FixedValues) (x : ValuesOn M.observed (swigΩ Ω)) :
    (M.fixSet (M.mechComplementNames S)
      (M.mechComplementNames_random_mem_observed S)
      (M.mechComplementNames_fixed_not_mem S)).FixedValues :=
  M.fixSetExtend (M.mechComplementNames S)
    (M.mechComplementNames_random_mem_observed S)
    (M.mechComplementNames_fixed_not_mem S) s
    (valuesProjection (M.mechComplementNames_image_random_subset_observed S) x)

/-- Tian's `Q[S]` measure (Eq. 36 / Eq. 55): the do(observed∖S) marginal on `S`.
Intervene on every not-already-fixed observed node outside `S`, then project the
intervened observational law to the coordinates in `S`. -/
noncomputable def QmechMeasure
    (M : Causalean.SCM N Ω) (S : Finset (SWIGNode N)) (hS : S ⊆ M.observed)
    (sWn :
      (M.fixSet (M.mechComplementNames S)
        (M.mechComplementNames_random_mem_observed S)
        (M.mechComplementNames_fixed_not_mem S)).FixedValues) :
    MeasureTheory.Measure (ValuesOn S (swigΩ Ω)) :=
  ((M.fixSet (M.mechComplementNames S)
      (M.mechComplementNames_random_mem_observed S)
      (M.mechComplementNames_fixed_not_mem S)).obsKernel sWn).map
    (valuesProjection
      (show S ⊆ (M.fixSet (M.mechComplementNames S)
          (M.mechComplementNames_random_mem_observed S)
          (M.mechComplementNames_fixed_not_mem S)).observed by
        simpa [fixSet_observed] using hS))

/-- The **mechanism c-factor density** `Q[S]` as a function of a full observed
assignment `x`: read the do-values for `V∖S` from `x` (keeping `M`'s fixed slice
`s`), form the do-complement marginal on `S`, and take its `rnDeriv` against the
product reference on `S`, evaluated at the `S`-projection of `x`. -/
noncomputable def mechCFactor
    (M : Causalean.SCM N Ω) (ref : ReferenceMeasures Ω) (S : Finset (SWIGNode N))
    (hS : S ⊆ M.observed) (s : M.FixedValues) :
    ValuesOn M.observed (swigΩ Ω) → ENNReal :=
  fun x =>
    (QmechMeasure M S hS (M.mechDoValues S s x)).rnDeriv
      (Causalean.SCM.jointRef ref S) (valuesProjection hS x)

/-- The do-complement `Q[S]` atom equals the local q-mass on `S`. -/
theorem QmechMeasure_singleton_eq_qLocalMass
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (S : Finset (SWIGNode N)) (hS : S ⊆ M.observed)
    (hfe : ∀ n : N, SWIGNode.fixed n ∈ M.fixed →
      ∀ v : SWIGNode N, ¬ M.dag.edge (SWIGNode.random n) v)
    (s : M.FixedValues) (x : ValuesOn M.observed (swigΩ Ω)) :
    QmechMeasure M S hS (M.mechDoValues S s x) {valuesProjection hS x}
      = M.qLocalMass s S hS x := by
  classical
  let W := M.mechComplementNames S
  let hWobs := M.mechComplementNames_random_mem_observed S
  let hWfix := M.mechComplementNames_fixed_not_mem S
  let M' := M.fixSet W hWobs hWfix
  let s' : M'.FixedValues := M.mechDoValues S s x
  have hclosed : M'.ObsParentClosed S := by
    simpa [M', W, hWobs, hWfix] using
      mechComplement_fixSet_obsParentClosed M S hS hfe
  let hS' : S ⊆ M'.observed := hclosed.1
  have hbridge := obsKernel_marginal_singleton_eq_latentProduct_agree M' s' hS' x
  have heval_local :
      {ℓ | ∀ v : {v // v ∈ S},
        M'.evalMap s' ℓ
            ⟨v.val, Finset.mem_union_left M'.unobserved (hS' v.property)⟩ =
          x ⟨v.val, hS' v.property⟩}
        = {ℓ | ∀ v (hv : v ∈ S), M'.localConsistent s' x v (hS' hv) ℓ} := by
    ext ℓ
    constructor
    · intro hEval
      exact (M'.evalMap_agree_iff_localConsistent s' S hclosed x ℓ).mp
        (fun v hv => hEval ⟨v, hv⟩)
    · intro hLocal v
      exact (M'.evalMap_agree_iff_localConsistent s' S hclosed x ℓ).mpr
        hLocal v.val v.property
  have hobsAgree : ∀ w (hw : w ∈ M.observed),
      x ⟨w, by simpa [M', W, hWobs, hWfix, fixSet_observed] using hw⟩ = x ⟨w, hw⟩ := by
    intro w hw
    rfl
  have hpin : ∀ D (hD : D ∈ W),
      x ⟨SWIGNode.random D, hWobs D hD⟩ =
        s' ⟨SWIGNode.fixed D,
          Finset.mem_union_right _ (Finset.mem_image.mpr ⟨D, hD, rfl⟩)⟩ := by
    intro D hD
    have hnew := M.fixSetExtend_apply_new_fixed W hWobs hWfix s
      (valuesProjection (M.mechComplementNames_image_random_subset_observed S) x) hD
    simpa [s', W, mechDoValues, valuesProjection] using hnew.symm
  have hproj : M.fixSetProj W hWobs hWfix s' = s := by
    simpa [s', W, hWobs, hWfix, mechDoValues] using
      (M.fixSetProj_fixSetExtend W hWobs hWfix s
        (valuesProjection (M.mechComplementNames_image_random_subset_observed S) x))
  have hset_do :
      {ℓ | ∀ v (hv : v ∈ S), M'.localConsistent s' x v (hS' hv) ℓ}
        = {ℓ | ∀ v (hv : v ∈ S), M.localConsistent s x v (hS hv) ℓ} := by
    ext ℓ
    constructor
    · intro hLocal v hv
      have hnot : v ∉ W.image SWIGNode.random := by
        intro hvW
        rcases Finset.mem_image.mp hvW with ⟨D, hD, rfl⟩
        exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hD).2.1).2 hv
      exact (localConsistent_fixSet_iff M W hWobs hWfix s' s x x v (hS' hv) (hS hv)
        hnot hobsAgree hpin hproj ℓ).mp (hLocal v hv)
    · intro hLocal v hv
      have hnot : v ∉ W.image SWIGNode.random := by
        intro hvW
        rcases Finset.mem_image.mp hvW with ⟨D, hD, rfl⟩
        exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hD).2.1).2 hv
      exact (localConsistent_fixSet_iff M W hWobs hWfix s' s x x v (hS' hv) (hS hv)
        hnot hobsAgree hpin hproj ℓ).mpr (hLocal v hv)
  calc
    QmechMeasure M S hS (M.mechDoValues S s x) {valuesProjection hS x}
        = ((M'.obsKernel s').map (valuesProjection hS')) {valuesProjection hS' x} := by
            rfl
    _ = M'.latentProduct
          {ℓ | ∀ v : {v // v ∈ S},
            M'.evalMap s' ℓ
                ⟨v.val, Finset.mem_union_left M'.unobserved (hS' v.property)⟩ =
              x ⟨v.val, hS' v.property⟩} := hbridge
    _ = M'.latentProduct
          {ℓ | ∀ v (hv : v ∈ S), M'.localConsistent s' x v (hS' hv) ℓ} := by
            rw [heval_local]
    _ = M.latentProduct
          {ℓ | ∀ v (hv : v ∈ S), M.localConsistent s x v (hS hv) ℓ} := by
            rw [hset_do]
            rfl
    _ = M.qLocalMass s S hS x := by
            rfl

lemma standard_fixed_random_edgeless
    (M : Causalean.SCM N Ω) (hStd : M.isStandard) :
    ∀ n : N, SWIGNode.fixed n ∈ M.fixed →
      ∀ v : SWIGNode N, ¬ M.dag.edge (SWIGNode.random n) v := by
  intro n hn
  rw [SCM.isStandard] at hStd
  rw [hStd] at hn
  simp at hn

private lemma fixSet_fixed_random_edgeless
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

end SCM

namespace SCM.ID

private lemma prefixNodes_obsParentClosed
    (M : Causalean.SCM N Ω) (k : ℕ) :
    M.ObsParentClosed (M.prefixNodes k) := by
  classical
  refine ⟨M.prefixNodes_subset_observed k, ?_⟩
  intro v hv w hwObs hEdge
  rcases (M.mem_prefixNodes_iff k v).mp hv with ⟨hvObs, hvlt⟩
  let i : Fin M.observed.card := M.observedIndex ⟨v, hvObs⟩
  have hi_eq : (M.observedAt i).val = v := by
    exact M.observedAt_observedIndex ⟨v, hvObs⟩
  have hwPred :
      w ∈ M.toSWIGGraph.observedPredecessors (M.observedAt i).val := by
    rw [hi_eq]
    exact Finset.mem_filter.mpr
      ⟨hwObs, M.dag.topoOrder_lt w v hEdge⟩
  have hwPrefixI : w ∈ M.prefixNodes i.val := by
    simpa using
      ((M.observedPredecessors_observedAt i.isLt).symm ▸ hwPred)
  exact M.prefixNodes_mono (show i.val ≤ k from Nat.le_of_lt hvlt) hwPrefixI

private lemma mem_cComponent_iff_cComponentOf_eq
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

private lemma obsKernel_prefix_singleton_eq_prod_qLocalMass
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (s : M.FixedValues) (k : ℕ)
    (x : ValuesOn M.observed (swigΩ Ω)) :
    ((M.obsKernel s).map (valuesProjection (M.prefixNodes_subset_observed k)))
        ({valuesProjection (M.prefixNodes_subset_observed k) x} :
          Set (ValuesOn (M.prefixNodes k) (swigΩ Ω)))
      =
    ∏ C ∈ M.toSWIGGraph.cComponentSet,
      M.qLocalMass s (C ∩ M.prefixNodes k)
        (fun _ hv =>
          M.prefixNodes_subset_observed k (Finset.mem_of_mem_inter_right hv)) x := by
  simpa using
    (M.obsKernel_marginal_singleton_eq_prod_qLocalMass s
      (M.prefixNodes k) (prefixNodes_obsParentClosed M k) x)

private lemma qLocalMass_ne_top
    (M : Causalean.SCM N Ω) (s : M.FixedValues)
    (T : Finset (SWIGNode N)) (hT : T ⊆ M.observed)
    (x : ValuesOn M.observed (swigΩ Ω)) :
    M.qLocalMass s T hT x ≠ ∞ := by
  exact ne_of_lt (MeasureTheory.measure_lt_top M.latentProduct _)

private lemma ENNReal.div_mul_common
    {a b r : ENNReal} (hr0 : r ≠ 0) (hrtop : r ≠ ∞) :
    (a * r) / (b * r) = a / b := by
  rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
  rw [ENNReal.mul_inv]
  · rw [show b⁻¹ * r⁻¹ * (a * r) = (r⁻¹ * r) * (b⁻¹ * a) by ac_rfl]
    rw [ENNReal.inv_mul_cancel hr0 hrtop]
    simp [mul_comm]
  · exact Or.inr hrtop
  · exact Or.inr hr0

private lemma Finset.prod_ne_top_of_ne_top {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ENNReal) (hf : ∀ i ∈ s, f i ≠ ∞) :
    (∏ i ∈ s, f i) ≠ ∞ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      exact ENNReal.mul_ne_top (hf a (Finset.mem_insert_self a s))
        (ih (by intro i hi; exact hf i (Finset.mem_insert_of_mem hi)))

private lemma cComponent_inter_prefix_succ_eq_of_ne
    (M : Causalean.SCM N Ω) {S C : Finset (SWIGNode N)}
    (hScomp : S ∈ M.toSWIGGraph.cComponentSet)
    (hCcomp : C ∈ M.toSWIGGraph.cComponentSet)
    {i : Fin M.observed.card}
    (hiS : M.toSWIGGraph.cComponentOf (M.observedAt i).val = S)
    (hCS : C ≠ S) :
    C ∩ M.prefixNodes (i.val + 1) = C ∩ M.prefixNodes i.val := by
  classical
  ext v
  constructor
  · intro hv
    rcases Finset.mem_inter.mp hv with ⟨hvC, hvpre⟩
    rw [M.prefixNodes_succ i.isLt] at hvpre
    rcases Finset.mem_union.mp hvpre with hvold | hvnew
    · exact Finset.mem_inter.mpr ⟨hvC, hvold⟩
    · have hvnode : v = (M.observedAt i).val := by simpa using hvnew
      subst hvnode
      have hnodeS : (M.observedAt i).val ∈ S := by
        exact (mem_cComponent_iff_cComponentOf_eq M.toSWIGGraph
          (M.observedAt i).property hScomp).mpr hiS
      have hnodeC : (M.observedAt i).val ∈ C := hvC
      have hSC : S = C := by
        exact (mem_cComponent_iff_cComponentOf_eq M.toSWIGGraph
          (M.observedAt i).property hCcomp).mp hnodeC ▸ hiS.symm
      exact False.elim (hCS hSC.symm)
  · intro hv
    rcases Finset.mem_inter.mp hv with ⟨hvC, hvpre⟩
    exact Finset.mem_inter.mpr
      ⟨hvC, M.prefixNodes_mono (Nat.le_succ i.val) hvpre⟩

private lemma cComponent_inter_prefix_succ_eq_of_node_ne
    (M : Causalean.SCM N Ω) {S : Finset (SWIGNode N)}
    (hScomp : S ∈ M.toSWIGGraph.cComponentSet)
    {i : Fin M.observed.card}
    (hiS : M.toSWIGGraph.cComponentOf (M.observedAt i).val ≠ S) :
    S ∩ M.prefixNodes (i.val + 1) = S ∩ M.prefixNodes i.val := by
  classical
  ext v
  constructor
  · intro hv
    rcases Finset.mem_inter.mp hv with ⟨hvS, hvpre⟩
    rw [M.prefixNodes_succ i.isLt] at hvpre
    rcases Finset.mem_union.mp hvpre with hvold | hvnew
    · exact Finset.mem_inter.mpr ⟨hvS, hvold⟩
    · have hvnode : v = (M.observedAt i).val := by simpa using hvnew
      subst hvnode
      exact False.elim (hiS
        ((mem_cComponent_iff_cComponentOf_eq M.toSWIGGraph
          (M.observedAt i).property hScomp).mp hvS))
  · intro hv
    rcases Finset.mem_inter.mp hv with ⟨hvS, hvpre⟩
    exact Finset.mem_inter.mpr
      ⟨hvS, M.prefixNodes_mono (Nat.le_succ i.val) hvpre⟩

private lemma prefix_qProduct_ratio_eq_component_ratio
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (s : M.FixedValues)
    (S : Finset (SWIGNode N)) (hScomp : S ∈ M.toSWIGGraph.cComponentSet)
    (i : Fin M.observed.card)
    (hiS : M.toSWIGGraph.cComponentOf (M.observedAt i).val = S)
    (hpos : DiscreteID.PositiveMass (M.obsKernel s))
    (x : ValuesOn M.observed (swigΩ Ω)) :
    (∏ C ∈ M.toSWIGGraph.cComponentSet,
        M.qLocalMass s (C ∩ M.prefixNodes (i.val + 1))
          (fun _ hv =>
            M.prefixNodes_subset_observed (i.val + 1)
              (Finset.mem_of_mem_inter_right hv)) x) /
      (∏ C ∈ M.toSWIGGraph.cComponentSet,
        M.qLocalMass s (C ∩ M.prefixNodes i.val)
          (fun _ hv =>
            M.prefixNodes_subset_observed i.val
              (Finset.mem_of_mem_inter_right hv)) x)
      =
    M.qLocalMass s (S ∩ M.prefixNodes (i.val + 1))
        (fun _ hv =>
          M.prefixNodes_subset_observed (i.val + 1)
            (Finset.mem_of_mem_inter_right hv)) x /
      M.qLocalMass s (S ∩ M.prefixNodes i.val)
        (fun _ hv =>
          M.prefixNodes_subset_observed i.val
            (Finset.mem_of_mem_inter_right hv)) x := by
  classical
  let f₁ : Finset (SWIGNode N) → ENNReal := fun C =>
    M.qLocalMass s (C ∩ M.prefixNodes (i.val + 1))
      (fun _ hv => M.prefixNodes_subset_observed (i.val + 1)
        (Finset.mem_of_mem_inter_right hv)) x
  let f₀ : Finset (SWIGNode N) → ENNReal := fun C =>
    M.qLocalMass s (C ∩ M.prefixNodes i.val)
      (fun _ hv => M.prefixNodes_subset_observed i.val
        (Finset.mem_of_mem_inter_right hv)) x
  have hrest :
      ∏ C ∈ M.toSWIGGraph.cComponentSet \ {S}, f₁ C =
        ∏ C ∈ M.toSWIGGraph.cComponentSet \ {S}, f₀ C := by
    refine Finset.prod_congr rfl ?_
    intro C hC
    have hCcomp : C ∈ M.toSWIGGraph.cComponentSet := (Finset.mem_sdiff.mp hC).1
    have hCne : C ≠ S := by
      intro h
      exact (Finset.mem_sdiff.mp hC).2 (by simp [h])
    simp [f₁, f₀, cComponent_inter_prefix_succ_eq_of_ne M hScomp hCcomp hiS hCne]
  have hsplit₁ : (∏ C ∈ M.toSWIGGraph.cComponentSet, f₁ C) =
      f₁ S * ∏ C ∈ M.toSWIGGraph.cComponentSet \ {S}, f₁ C := by
    exact Finset.prod_eq_mul_prod_diff_singleton S f₁
      (by intro h; exact False.elim (h hScomp))
  have hsplit₀ : (∏ C ∈ M.toSWIGGraph.cComponentSet, f₀ C) =
      f₀ S * ∏ C ∈ M.toSWIGGraph.cComponentSet \ {S}, f₀ C := by
    exact Finset.prod_eq_mul_prod_diff_singleton S f₀
      (by intro h; exact False.elim (h hScomp))
  have hr0 : (∏ C ∈ M.toSWIGGraph.cComponentSet \ {S}, f₀ C) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr (by
      intro C _hC
      exact M.qLocalMass_pos_of_positiveObs s hpos (C ∩ M.prefixNodes i.val)
        (fun _ hv =>
          M.prefixNodes_subset_observed i.val (Finset.mem_of_mem_inter_right hv)) x)
  have hrtop : (∏ C ∈ M.toSWIGGraph.cComponentSet \ {S}, f₀ C) ≠ ∞ := by
    exact Finset.prod_ne_top_of_ne_top _ f₀ (by
      intro C _hC
      exact qLocalMass_ne_top M s (C ∩ M.prefixNodes i.val)
        (fun _ hv =>
          M.prefixNodes_subset_observed i.val (Finset.mem_of_mem_inter_right hv)) x)
  change (∏ C ∈ M.toSWIGGraph.cComponentSet, f₁ C) /
      (∏ C ∈ M.toSWIGGraph.cComponentSet, f₀ C) = f₁ S / f₀ S
  rw [hsplit₁, hsplit₀, hrest]
  exact ENNReal.div_mul_common hr0 hrtop

private lemma obsStepCondKernel_singleton_eq_obsCondKernel_singleton
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (s : M.FixedValues)
    (i : Fin M.observed.card)
    [∀ s' : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.obsKernel s')]
    [StandardBorelSpace
      (ValuesOn ({(M.observedAt i).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [Nonempty
      (ValuesOn ({(M.observedAt i).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [MeasurableSpace.CountableOrCountablyGenerated
      M.FixedValues (ValuesOn (M.prefixNodes i.val) (swigΩ Ω))]
    (x : ValuesOn M.observed (swigΩ Ω)) :
    (M.obsStepCondKernel i.isLt)
        (s, valuesProjection (M.prefixNodes_subset_observed i.val) x)
        ({x (M.observedAt i)} : Set (swigΩ Ω (M.observedAt i).val))
      =
    M.obsCondKernel ({(M.observedAt i).val} : Finset (SWIGNode N))
        (M.prefixNodes i.val)
        (by
          intro v hv
          have hv_eq : v = (M.observedAt i).val := by simpa using hv
          simp [hv_eq, (M.observedAt i).property])
        (M.prefixNodes_subset_observed i.val)
        (s, valuesProjection (M.prefixNodes_subset_observed i.val) x)
        ({valuesProjection
          (by
            intro v hv
            have hv_eq : v = (M.observedAt i).val := by simpa using hv
            simp [hv_eq, (M.observedAt i).property])
          x} :
          Set (ValuesOn ({(M.observedAt i).val} : Finset (SWIGNode N)) (swigΩ Ω))) := by
  unfold obsStepCondKernel
  rw [ProbabilityTheory.Kernel.map_apply _ (measurable_singletonValue (Ω := Ω))]
  rw [MeasureTheory.Measure.map_apply
    (measurable_singletonValue (Ω := Ω)) (MeasurableSet.singleton _)]
  congr 1
  ext y
  constructor
  · intro hy
    ext a
    obtain ⟨a, ha⟩ := a
    have ha' : a = (M.observedAt i).val := by simpa using ha
    subst a
    simpa [singletonValue, valuesProjection] using hy
  · intro hy
    have h := congrFun hy ⟨(M.observedAt i).val, by simp⟩
    simpa [singletonValue, valuesProjection] using h

private lemma obsStepCondKernel_singleton_eq_prefix_ratio
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (s : M.FixedValues)
    (i : Fin M.observed.card)
    (hpos : DiscreteID.PositiveMass (M.obsKernel s))
    [∀ s' : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.obsKernel s')]
    [StandardBorelSpace
      (ValuesOn ({(M.observedAt i).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [Nonempty
      (ValuesOn ({(M.observedAt i).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [MeasurableSpace.CountableOrCountablyGenerated
      M.FixedValues (ValuesOn (M.prefixNodes i.val) (swigΩ Ω))]
    (x : ValuesOn M.observed (swigΩ Ω)) :
    (M.obsStepCondKernel i.isLt)
        (s, valuesProjection (M.prefixNodes_subset_observed i.val) x)
        ({x (M.observedAt i)} : Set (swigΩ Ω (M.observedAt i).val))
      =
    ((M.obsKernel s).map
        (valuesProjection (M.prefixNodes_subset_observed (i.val + 1))))
        ({valuesProjection (M.prefixNodes_subset_observed (i.val + 1)) x} :
          Set (ValuesOn (M.prefixNodes (i.val + 1)) (swigΩ Ω))) /
    ((M.obsKernel s).map
        (valuesProjection (M.prefixNodes_subset_observed i.val)))
        ({valuesProjection (M.prefixNodes_subset_observed i.val) x} :
          Set (ValuesOn (M.prefixNodes i.val) (swigΩ Ω))) := by
  rw [obsStepCondKernel_singleton_eq_obsCondKernel_singleton]
  let hY : ({(M.observedAt i).val} : Finset (SWIGNode N)) ⊆ M.observed := by
    intro v hv
    have hv_eq : v = (M.observedAt i).val := by simpa using hv
    simp [hv_eq, (M.observedAt i).property]
  let hCC : M.prefixNodes i.val ⊆ M.observed := M.prefixNodes_subset_observed i.val
  have hc0 : ((M.obsKernel s).map (valuesProjection hCC))
        ({valuesProjection hCC x} :
          Set (ValuesOn (M.prefixNodes i.val) (swigΩ Ω))) ≠ 0 := by
    rw [obsKernel_prefix_singleton_eq_prod_qLocalMass]
    exact Finset.prod_ne_zero_iff.mpr (by
      intro C _hC
      exact M.qLocalMass_pos_of_positiveObs s hpos (C ∩ M.prefixNodes i.val)
        (fun _ hv =>
          M.prefixNodes_subset_observed i.val (Finset.mem_of_mem_inter_right hv)) x)
  have hctop : ((M.obsKernel s).map (valuesProjection hCC))
        ({valuesProjection hCC x} :
          Set (ValuesOn (M.prefixNodes i.val) (swigΩ Ω))) ≠ ∞ := by
    exact ne_of_lt
      (MeasureTheory.measure_lt_top ((M.obsKernel s).map (valuesProjection hCC)) _)
  rw [obsCondKernel_singleton_mass_of_ne_zero M
    ({(M.observedAt i).val} : Finset (SWIGNode N)) (M.prefixNodes i.val)
    hY hCC s (valuesProjection hCC x) (valuesProjection hY x) hc0 hctop]
  congr 1
  let e : ValuesOn (M.prefixNodes (i.val + 1)) (swigΩ Ω) ≃ᵐ
      ValuesOn (M.prefixNodes i.val) (swigΩ Ω) ×
        ValuesOn ({(M.observedAt i).val} : Finset (SWIGNode N)) (swigΩ Ω) :=
    (valuesEquivOfEq (Ω := swigΩ Ω) (M.prefixNodes_succ i.isLt)).trans
      (valuesUnionEquiv (Ω := Ω) (M.prefixNodes_disjoint_singleton_next i.isLt))
  have hfun :
      (fun ω : M.ObservedValues => (valuesProjection hCC ω, valuesProjection hY ω)) =
        e ∘ valuesProjection (M.prefixNodes_subset_observed (i.val + 1)) := by
    simpa [e, hY, hCC] using (M.prefixSucc_projection_pair i.isLt).symm
  rw [hfun]
  rw [← MeasureTheory.Measure.map_map e.measurable
    (measurable_valuesProjection (M.prefixNodes_subset_observed (i.val + 1)))]
  rw [MeasureTheory.Measure.map_apply e.measurable (MeasurableSet.singleton _)]
  congr 1
  ext z
  have hxpair :
      e (valuesProjection (M.prefixNodes_subset_observed (i.val + 1)) x) =
        (valuesProjection hCC x, valuesProjection hY x) := by
    have h := congrFun (M.prefixSucc_projection_pair i.isLt) x
    simpa [e, hY, hCC, Function.comp_def] using h
  constructor
  · intro hz
    exact e.injective (by simpa [hxpair] using hz)
  · intro hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    change e (valuesProjection (M.prefixNodes_subset_observed (i.val + 1)) x) =
      (valuesProjection hCC x, valuesProjection hY x)
    exact hxpair

private lemma obsStepCondDensity_eq_component_ratio_div_ref
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (ref : ReferenceMeasures Ω) (s : M.FixedValues)
    (S : Finset (SWIGNode N)) (hScomp : S ∈ M.toSWIGGraph.cComponentSet)
    (i : Fin M.observed.card)
    (hiS : M.toSWIGGraph.cComponentOf (M.observedAt i).val = S)
    (href : Causalean.SCM.ReferenceFaithful ref)
    (hpos : DiscreteID.PositiveMass (M.obsKernel s))
    [∀ s' : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.obsKernel s')]
    [StandardBorelSpace
      (ValuesOn ({(M.observedAt i).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [Nonempty
      (ValuesOn ({(M.observedAt i).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [MeasurableSpace.CountableOrCountablyGenerated
      M.FixedValues (ValuesOn (M.prefixNodes i.val) (swigΩ Ω))]
    (x : ValuesOn M.observed (swigΩ Ω)) :
    M.obsStepCondDensity ref s i x =
      (M.qLocalMass s (S ∩ M.prefixNodes (i.val + 1))
          (fun _ hv =>
            M.prefixNodes_subset_observed (i.val + 1)
              (Finset.mem_of_mem_inter_right hv)) x /
        M.qLocalMass s (S ∩ M.prefixNodes i.val)
          (fun _ hv =>
            M.prefixNodes_subset_observed i.val
              (Finset.mem_of_mem_inter_right hv)) x) /
      ref.μ (M.observedAt i).val
        ({x (M.observedAt i)} : Set (swigΩ Ω (M.observedAt i).val)) := by
  have hac : (M.obsStepCondKernel i.isLt)
        (s, valuesProjection (M.prefixNodes_subset_observed i.val) x) ≪
      ref.μ (M.observedAt i).val := by
    exact absolutelyContinuous_of_singleton_ne_zero _ _ (href (M.observedAt i).val)
  have href0 : ref.μ (M.observedAt i).val
        ({x (M.observedAt i)} : Set (swigΩ Ω (M.observedAt i).val)) ≠ 0 :=
    href (M.observedAt i).val (x (M.observedAt i))
  have hreftop : ref.μ (M.observedAt i).val
        ({x (M.observedAt i)} : Set (swigΩ Ω (M.observedAt i).val)) ≠ ∞ := by
    exact ne_of_lt (MeasureTheory.measure_lt_top (ref.μ (M.observedAt i).val) _)
  rw [obsStepCondDensity_eq_mass_ratio M ref s i x hac href0 hreftop]
  rw [obsStepCondKernel_singleton_eq_prefix_ratio M s i hpos x]
  rw [obsKernel_prefix_singleton_eq_prod_qLocalMass]
  rw [obsKernel_prefix_singleton_eq_prod_qLocalMass]
  rw [prefix_qProduct_ratio_eq_component_ratio M s S hScomp i hiS hpos x]

private lemma ENNReal.prod_div_prod {ι : Type*} [DecidableEq ι]
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
        exact Finset.prod_ne_top_of_ne_top _ g (by
          intro i hi
          exact hgtop i (Finset.mem_insert_of_mem hi))
      rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.prod_insert ha, ih']
      rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
      rw [ENNReal.mul_inv]
      · ac_rfl
      · exact Or.inr hprodtop
      · exact Or.inr hprod0

private lemma ENNReal.prod_div_prod₂ {ι : Type*} [DecidableEq ι]
    (t : Finset ι) (f g h : ι → ENNReal)
    (hh0 : ∀ i ∈ t, h i ≠ 0) (hhtop : ∀ i ∈ t, h i ≠ ∞) :
    (∏ i ∈ t, (f i / g i) / h i) =
      (∏ i ∈ t, f i / g i) / (∏ i ∈ t, h i) := by
  exact ENNReal.prod_div_prod t (fun i => f i / g i) h hh0 hhtop

lemma mechCFactor_eq_qLocalMass_div_jointRef
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

private lemma component_qLocalMass_ratio_product
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (s : M.FixedValues)
    (S : Finset (SWIGNode N)) (hS : S ⊆ M.observed)
    (hScomp : S ∈ M.toSWIGGraph.cComponentSet)
    (hpos : DiscreteID.PositiveMass (M.obsKernel s))
    (x : ValuesOn M.observed (swigΩ Ω)) :
    (∏ i ∈ Finset.univ.filter
        (fun i : Fin M.observed.card =>
          M.toSWIGGraph.cComponentOf (M.observedAt i).val = S),
      M.qLocalMass s (S ∩ M.prefixNodes (i.val + 1))
        (fun _ hv =>
          M.prefixNodes_subset_observed (i.val + 1)
            (Finset.mem_of_mem_inter_right hv)) x /
      M.qLocalMass s (S ∩ M.prefixNodes i.val)
        (fun _ hv =>
          M.prefixNodes_subset_observed i.val
            (Finset.mem_of_mem_inter_right hv)) x)
      = M.qLocalMass s S hS x := by
  classical
  let a : ℕ → ENNReal := fun k =>
    M.qLocalMass s (S ∩ M.prefixNodes k)
      (fun _ hv =>
        M.prefixNodes_subset_observed k (Finset.mem_of_mem_inter_right hv)) x
  let T : Finset ℕ := (Finset.range M.observed.card).filter fun k =>
    if hk : k < M.observed.card then
      M.toSWIGGraph.cComponentOf (M.observedAt ⟨k, hk⟩).val = S
    else False
  have hreindex :
      (∏ i ∈ Finset.univ.filter
          (fun i : Fin M.observed.card =>
            M.toSWIGGraph.cComponentOf (M.observedAt i).val = S),
        a (i.val + 1) / a i.val)
        = ∏ k ∈ T, a (k + 1) / a k := by
    refine Finset.prod_bij (fun i _hi => i.val) ?_ ?_ ?_ ?_
    · intro i hi
      simp [T, i.isLt, Finset.mem_filter.mp hi]
    · intro i _hi j _hj hij
      exact Fin.ext hij
    · intro k hk
      simp [T] at hk
      have hklt : k < M.observed.card := hk.1
      refine ⟨⟨k, hklt⟩, ?_, rfl⟩
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by simpa [hklt] using hk.2⟩
    · intro i _hi
      rfl
  have hTsubset : T ⊆ Finset.range M.observed.card := by
    intro k hk
    exact (Finset.mem_filter.mp hk).1
  have hne : ∀ k ≤ M.observed.card, a k ≠ 0 := by
    intro k hk
    exact M.qLocalMass_pos_of_positiveObs s hpos (S ∩ M.prefixNodes k)
      (fun _ hv =>
        M.prefixNodes_subset_observed k (Finset.mem_of_mem_inter_right hv)) x
  have hfin : ∀ k ≤ M.observed.card, a k ≠ ∞ := by
    intro k hk
    exact qLocalMass_ne_top M s (S ∩ M.prefixNodes k)
      (fun _ hv =>
        M.prefixNodes_subset_observed k (Finset.mem_of_mem_inter_right hv)) x
  have hconst : ∀ k < M.observed.card, k ∉ T → a (k + 1) = a k := by
    intro k hk hnot
    have hnode_ne :
        M.toSWIGGraph.cComponentOf (M.observedAt ⟨k, hk⟩).val ≠ S := by
      intro hnode
      exact hnot (by
        simp [T, hk, hnode])
    dsimp [a]
    have hset :
        S ∩ M.prefixNodes (k + 1) = S ∩ M.prefixNodes k :=
      cComponent_inter_prefix_succ_eq_of_node_ne M hScomp hnode_ne
    unfold qLocalMass
    congr 1
    ext ℓ
    constructor
    · intro hℓ v hv
      have hv' : v ∈ S ∩ M.prefixNodes (k + 1) := by
        simpa [hset] using hv
      simpa using hℓ v hv'
    · intro hℓ v hv
      have hv' : v ∈ S ∩ M.prefixNodes k := by
        simpa [hset] using hv
      simpa using hℓ v hv'
  have htelescope :
      ∏ k ∈ T, a (k + 1) / a k = a M.observed.card / a 0 :=
    prod_filter_div_telescope a M.observed.card T hTsubset hne hfin hconst
  have htop : S ∩ M.prefixNodes M.observed.card = S := by
    rw [M.prefixNodes_card]
    exact Finset.inter_eq_left.mpr hS
  have hzero : S ∩ M.prefixNodes 0 = ∅ := by
    rw [M.prefixNodes_zero, Finset.inter_empty]
  calc
    (∏ i ∈ Finset.univ.filter
        (fun i : Fin M.observed.card =>
          M.toSWIGGraph.cComponentOf (M.observedAt i).val = S),
      M.qLocalMass s (S ∩ M.prefixNodes (i.val + 1))
        (fun _ hv =>
          M.prefixNodes_subset_observed (i.val + 1)
            (Finset.mem_of_mem_inter_right hv)) x /
      M.qLocalMass s (S ∩ M.prefixNodes i.val)
        (fun _ hv =>
          M.prefixNodes_subset_observed i.val
            (Finset.mem_of_mem_inter_right hv)) x)
        = ∏ i ∈ Finset.univ.filter
          (fun i : Fin M.observed.card =>
            M.toSWIGGraph.cComponentOf (M.observedAt i).val = S),
          a (i.val + 1) / a i.val := by rfl
    _ = ∏ k ∈ T, a (k + 1) / a k := hreindex
    _ = a M.observed.card / a 0 := htelescope
    _ = M.qLocalMass s S hS x / 1 := by
          simp [a, htop, hzero]
    _ = M.qLocalMass s S hS x := by
          simp

private lemma component_ref_atom_product_eq_jointRef
    [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (ref : ReferenceMeasures Ω)
    (S : Finset (SWIGNode N)) (hS : S ⊆ M.observed)
    (hScomp : S ∈ M.toSWIGGraph.cComponentSet)
    (x : ValuesOn M.observed (swigΩ Ω)) :
    (∏ i ∈ Finset.univ.filter
        (fun i : Fin M.observed.card =>
          M.toSWIGGraph.cComponentOf (M.observedAt i).val = S),
      ref.μ (M.observedAt i).val
        ({x (M.observedAt i)} : Set (swigΩ Ω (M.observedAt i).val)))
      =
    jointRef ref S ({valuesProjection hS x} :
      Set (ValuesOn S (swigΩ Ω))) := by
  classical
  have hprod :
      (∏ i ∈ Finset.univ.filter
          (fun i : Fin M.observed.card =>
            M.toSWIGGraph.cComponentOf (M.observedAt i).val = S),
        ref.μ (M.observedAt i).val
          ({x (M.observedAt i)} : Set (swigΩ Ω (M.observedAt i).val)))
        =
      ∏ v : {v // v ∈ S},
        ref.μ v.val ({(valuesProjection hS x) v} :
          Set (swigΩ Ω v.val)) := by
    refine Finset.prod_bij
      (fun i hi =>
        ⟨(M.observedAt i).val,
          (mem_cComponent_iff_cComponentOf_eq M.toSWIGGraph
            (M.observedAt i).property hScomp).mpr
            (Finset.mem_filter.mp hi).2⟩)
      ?_ ?_ ?_ ?_
    · intro i hi
      exact Finset.mem_univ _
    · intro i _hi j _hj hij
      have hval : (M.observedAt i).val = (M.observedAt j).val :=
        congrArg (fun v : {v // v ∈ S} => v.val) hij
      have hsub : M.observedAt i = M.observedAt j :=
        Subtype.ext hval
      calc
        i = M.observedIndex (M.observedAt i) := (M.observedIndex_observedAt i).symm
        _ = M.observedIndex (M.observedAt j) := by rw [hsub]
        _ = j := M.observedIndex_observedAt j
    · intro v _hv
      let i : Fin M.observed.card := M.observedIndex ⟨v.val, hS v.property⟩
      have hnode : (M.observedAt i).val = v.val :=
        M.observedAt_observedIndex ⟨v.val, hS v.property⟩
      refine ⟨i, ?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        have hvcomp :
            M.toSWIGGraph.cComponentOf v.val = S :=
          (mem_cComponent_iff_cComponentOf_eq M.toSWIGGraph
            (hS v.property) hScomp).mp v.property
        simpa [hnode] using hvcomp
      · exact Subtype.ext hnode
    · intro i hi
      simp [valuesProjection]
  rw [jointRef_singleton_eq_prod]
  exact hprod

/-- **(A) Tian Lemma 1 (Eq. 37 = Eq. 36).**  The observational full-prefix
c-component density equals the do-complement marginal density `Q[S]`.

The prefix-conditional product `cComponentDensityFactor` telescopes to the
do(observed∖S) marginal.  The equality is a statement about the whole
telescoped product, not about matching each one-node conditional factor
separately. -/
lemma cComponentDensityFactor_eq_mechCFactor
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (ref : ReferenceMeasures Ω) (s : M.FixedValues)
    (hStd : M.isStandard)
    (S : Finset (SWIGNode N)) (hS : S ⊆ M.observed)
    (hScomp : S ∈ M.toSWIGGraph.cComponentSet)
    (href : Causalean.SCM.ReferenceFaithful ref)
    (hpos : DiscreteID.PositiveMass (M.obsKernel s))
    [∀ s' : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.obsKernel s')]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      StandardBorelSpace
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      Nonempty
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ k : ℕ,
      MeasurableSpace.CountableOrCountablyGenerated
        M.FixedValues (ValuesOn (M.prefixNodes k) (swigΩ Ω))]
    (x : ValuesOn M.observed (swigΩ Ω)) :
    M.cComponentDensityFactor ref s S x = M.mechCFactor ref S hS s x := by
  classical
  let I : Finset (Fin M.observed.card) :=
    Finset.univ.filter
      (fun i : Fin M.observed.card =>
        M.toSWIGGraph.cComponentOf (M.observedAt i).val = S)
  let num : Fin M.observed.card → ENNReal := fun i =>
    M.qLocalMass s (S ∩ M.prefixNodes (i.val + 1))
      (fun _ hv =>
        M.prefixNodes_subset_observed (i.val + 1)
          (Finset.mem_of_mem_inter_right hv)) x
  let den : Fin M.observed.card → ENNReal := fun i =>
    M.qLocalMass s (S ∩ M.prefixNodes i.val)
      (fun _ hv =>
        M.prefixNodes_subset_observed i.val
          (Finset.mem_of_mem_inter_right hv)) x
  let atom : Fin M.observed.card → ENNReal := fun i =>
    ref.μ (M.observedAt i).val
      ({x (M.observedAt i)} : Set (swigΩ Ω (M.observedAt i).val))
  have hsteps :
      M.cComponentDensityFactor ref s S x =
        ∏ i ∈ I, (num i / den i) / atom i := by
    unfold cComponentDensityFactor
    refine Finset.prod_congr rfl ?_
    intro i hi
    have hiS : M.toSWIGGraph.cComponentOf (M.observedAt i).val = S :=
      (Finset.mem_filter.mp hi).2
    exact obsStepCondDensity_eq_component_ratio_div_ref
      M ref s S hScomp i hiS href hpos x
  have hatom0 : ∀ i ∈ I, atom i ≠ 0 := by
    intro i _hi
    exact href (M.observedAt i).val (x (M.observedAt i))
  have hatomtop : ∀ i ∈ I, atom i ≠ ∞ := by
    intro i _hi
    exact ne_of_lt
      (MeasureTheory.measure_lt_top (ref.μ (M.observedAt i).val)
        ({x (M.observedAt i)} : Set (swigΩ Ω (M.observedAt i).val)))
  have hsplit :
      (∏ i ∈ I, (num i / den i) / atom i) =
        (∏ i ∈ I, num i / den i) / (∏ i ∈ I, atom i) :=
    ENNReal.prod_div_prod₂ I num den atom hatom0 hatomtop
  have hnum :
      (∏ i ∈ I, num i / den i) = M.qLocalMass s S hS x := by
    simpa [I, num, den] using
      component_qLocalMass_ratio_product M s S hS hScomp hpos x
  have hrefprod :
      (∏ i ∈ I, atom i) =
        jointRef ref S ({valuesProjection hS x} :
          Set (ValuesOn S (swigΩ Ω))) := by
    simpa [I, atom] using
      component_ref_atom_product_eq_jointRef M ref S hS hScomp x
  have hanchor :
      M.mechCFactor ref S hS s x =
        M.qLocalMass s S hS x /
          jointRef ref S ({valuesProjection hS x} :
            Set (ValuesOn S (swigΩ Ω))) :=
    mechCFactor_eq_qLocalMass_div_jointRef M ref s S hS href
      (standard_fixed_random_edgeless M hStd) x
  calc
    M.cComponentDensityFactor ref s S x
        = ∏ i ∈ I, (num i / den i) / atom i := hsteps
    _ = (∏ i ∈ I, num i / den i) / (∏ i ∈ I, atom i) := hsplit
    _ = M.qLocalMass s S hS x /
        jointRef ref S ({valuesProjection hS x} :
          Set (ValuesOn S (swigΩ Ω))) := by rw [hnum, hrefprod]
    _ = M.mechCFactor ref S hS s x := hanchor.symm

/-- Local q-mass is invariant under a `fixSet` intervention when no coordinate
in `S` is one of the intervened random nodes and the full assignment pins each
intervened random node to the corresponding fixed value. -/
lemma qLocalMass_fixSet_invariant
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (sDo : (M.fixSet X hObs hFix).FixedValues)
    (S : Finset (SWIGNode N)) (hS : S ⊆ M.observed)
    (hSX : ∀ n ∈ X, SWIGNode.random n ∉ S)
    (x : ValuesOn M.observed (swigΩ Ω))
    (hpin : ∀ D (hD : D ∈ X),
      x ⟨SWIGNode.random D, hObs D hD⟩ =
        sDo ⟨SWIGNode.fixed D,
          Finset.mem_union_right _ (Finset.mem_image.mpr ⟨D, hD, rfl⟩)⟩) :
    (M.fixSet X hObs hFix).qLocalMass sDo S
        (by simpa [fixSet_observed] using hS) x =
      M.qLocalMass (M.fixSetProj X hObs hFix sDo) S hS x := by
  classical
  let MX := M.fixSet X hObs hFix
  let hSXobs : S ⊆ MX.observed := by
    simpa [MX, fixSet_observed] using hS
  have hobsAgree : ∀ w (hw : w ∈ M.observed),
      x ⟨w, by simpa [MX, fixSet_observed] using hw⟩ = x ⟨w, hw⟩ := by
    intro w hw
    rfl
  have hproj : M.fixSetProj X hObs hFix sDo =
      M.fixSetProj X hObs hFix sDo := rfl
  unfold qLocalMass
  congr 1
  ext ℓ
  constructor
  · intro hLocal v hv
    have hnot : v ∉ X.image SWIGNode.random := by
      intro hvX
      rcases Finset.mem_image.mp hvX with ⟨D, hD, rfl⟩
      exact hSX D hD hv
    exact (localConsistent_fixSet_iff M X hObs hFix sDo
      (M.fixSetProj X hObs hFix sDo) x x v (hSXobs hv) (hS hv)
      hnot hobsAgree hpin hproj ℓ).mp (hLocal v hv)
  · intro hLocal v hv
    have hnot : v ∉ X.image SWIGNode.random := by
      intro hvX
      rcases Finset.mem_image.mp hvX with ⟨D, hD, rfl⟩
      exact hSX D hD hv
    exact (localConsistent_fixSet_iff M X hObs hFix sDo
      (M.fixSetProj X hObs hFix sDo) x x v (hSXobs hv) (hS hv)
      hnot hobsAgree hpin hproj ℓ).mpr (hLocal v hv)

/-- **Do(X)-invariance of the c-factor `Q[S]`** (Tian Lemma 4), for a
c-component `S` whose random copies avoid the intervention set `X`.

The `S`-c-factor of the do-model `M.fixSet X` equals the `S`-c-factor of the
original model at the projected fixed-value slice.  The proof reduces both
mechanism c-factors to the same local q-mass and the same reference atom: the
intervention changes coordinates outside `S`, while the supplied pinning
hypothesis makes the full observed assignment agree with the intervention
values on the treated random copies. -/
lemma mechCFactor_fixSet_invariant
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (ref : ReferenceMeasures Ω) (X : Finset N)
    (href : Causalean.SCM.ReferenceFaithful ref)
    (hStd : M.isStandard)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (S : Finset (SWIGNode N)) (hS : S ⊆ M.observed)
    (hSX : ∀ n ∈ X, SWIGNode.random n ∉ S)
    (sDo : (M.fixSet X hObs hFix).FixedValues)
    (x : ValuesOn M.observed (swigΩ Ω))
    (hpin : ∀ D (hD : D ∈ X),
      x ⟨SWIGNode.random D, hObs D hD⟩ =
        sDo ⟨SWIGNode.fixed D,
          Finset.mem_union_right _ (Finset.mem_image.mpr ⟨D, hD, rfl⟩)⟩) :
    (M.fixSet X hObs hFix).mechCFactor ref S
        (by simpa [fixSet_observed] using hS) sDo x
      = M.mechCFactor ref S hS (M.fixSetProj X hObs hFix sDo) x := by
  classical
  let MX := M.fixSet X hObs hFix
  let hSXobs : S ⊆ MX.observed := by
    simpa [MX, fixSet_observed] using hS
  have hfeX :
      ∀ n : N, SWIGNode.fixed n ∈ MX.fixed →
        ∀ v : SWIGNode N, ¬ MX.dag.edge (SWIGNode.random n) v := by
    simpa [MX] using fixSet_fixed_random_edgeless M X hObs hFix hStd
  have hfeM :
      ∀ n : N, SWIGNode.fixed n ∈ M.fixed →
        ∀ v : SWIGNode N, ¬ M.dag.edge (SWIGNode.random n) v :=
    standard_fixed_random_edgeless M hStd
  have hq :
      MX.qLocalMass sDo S hSXobs x =
        M.qLocalMass (M.fixSetProj X hObs hFix sDo) S hS x :=
    qLocalMass_fixSet_invariant M X hObs hFix sDo S hS hSX x hpin
  have hnumX :
      QmechMeasure MX S hSXobs (MX.mechDoValues S sDo x)
          {valuesProjection hSXobs x}
        = MX.qLocalMass sDo S hSXobs x :=
    QmechMeasure_singleton_eq_qLocalMass MX S hSXobs hfeX sDo x
  have hnumM :
      QmechMeasure M S hS
          (M.mechDoValues S (M.fixSetProj X hObs hFix sDo) x)
          {valuesProjection hS x}
        = M.qLocalMass (M.fixSetProj X hObs hFix sDo) S hS x :=
    QmechMeasure_singleton_eq_qLocalMass M S hS hfeM
      (M.fixSetProj X hObs hFix sDo) x
  have hprojPoint : valuesProjection hSXobs x = valuesProjection hS x := by
    ext v
    rfl
  have hden0X :
      jointRef ref S ({valuesProjection hSXobs x} :
        Set (ValuesOn S (swigΩ Ω))) ≠ 0 :=
    jointRef_singleton_ne_zero ref href S (valuesProjection hSXobs x)
  have hdenTopX :
      jointRef ref S ({valuesProjection hSXobs x} :
        Set (ValuesOn S (swigΩ Ω))) ≠ ∞ := by
    exact ne_of_lt (MeasureTheory.measure_lt_top (jointRef ref S)
      ({valuesProjection hSXobs x} : Set (ValuesOn S (swigΩ Ω))))
  have hden0M :
      jointRef ref S ({valuesProjection hS x} :
        Set (ValuesOn S (swigΩ Ω))) ≠ 0 :=
    jointRef_singleton_ne_zero ref href S (valuesProjection hS x)
  have hdenTopM :
      jointRef ref S ({valuesProjection hS x} :
        Set (ValuesOn S (swigΩ Ω))) ≠ ∞ := by
    exact ne_of_lt (MeasureTheory.measure_lt_top (jointRef ref S)
      ({valuesProjection hS x} : Set (ValuesOn S (swigΩ Ω))))
  unfold mechCFactor
  rw [rnDeriv_singleton_eq_div _ _
      (absolutelyContinuous_jointRef_of_faithful ref href S
        (QmechMeasure MX S hSXobs (MX.mechDoValues S sDo x)))
      (valuesProjection hSXobs x) hden0X hdenTopX]
  rw [rnDeriv_singleton_eq_div _ _
      (absolutelyContinuous_jointRef_of_faithful ref href S
        (QmechMeasure M S hS
          (M.mechDoValues S (M.fixSetProj X hObs hFix sDo) x)))
      (valuesProjection hS x) hden0M hdenTopM]
  rw [hnumX, hnumM, hq, hprojPoint]

end SCM.ID
end Causalean
