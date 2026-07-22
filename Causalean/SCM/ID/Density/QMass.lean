/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.SCM.ID.Density.LatentBlocks
import Causalean.SCM.ID.Density.IdentifyMass
import Causalean.SCM.ID.Density.MassBridge
import Causalean.SCM.ID.DiscreteID.Positive
import Causalean.SCM.ID.GraphicalThms.DoGFormula
import Mathlib.Probability.Independence.InfinitePi

/-! # Local q-masses for ID density factorization

This file develops the finite mass identities behind the density route to ID.
The central definition is `qLocalMass`, the latent-product mass of satisfying
local consistency on a chosen observed node set.  The file proves elimination
and marginalization lemmas for local q-masses, factors local consistency events
over disjoint latent blocks, and derives the c-component factorization
`obsKernel_marginal_singleton_eq_prod_qLocalMass` for observed marginal atoms.

It also supplies the positivity bridge
`doObsKernelAncestralMarginal_positiveMass` for do-model ancestral marginals and
the pure ENNReal telescope `prod_filter_div_telescope`, both used by the Tian
district-density recovery in `QFactor`.
-/

set_option linter.unusedFintypeInType false

namespace Causalean.SCM

open scoped MeasureTheory ProbabilityTheory ENNReal BigOperators
open MeasureTheory ProbabilityTheory

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

/-- The latent-product mass of satisfying local consistency on an observed
subset. -/
noncomputable def qLocalMass
    (M : Causalean.SCM N Ω) (s : M.FixedValues)
    (T : Finset (SWIGNode N)) (hT : T ⊆ M.observed)
    (x : ValuesOn M.observed (swigΩ Ω)) : ENNReal :=
  M.latentProduct {ℓ | ∀ v (hv : v ∈ T),
    M.localConsistent s x v (hT hv) ℓ}

/-- The empty local q-mass is one. -/
@[simp] lemma qLocalMass_empty
    (M : Causalean.SCM N Ω) (s : M.FixedValues)
    (x : ValuesOn M.observed (swigΩ Ω)) :
    M.qLocalMass s ∅ (by simp) x = 1 := by
  simp [qLocalMass]

/-- Local q-mass is antitone in the constrained observed set. -/
lemma qLocalMass_anti
    (M : Causalean.SCM N Ω) (s : M.FixedValues)
    {T T' : Finset (SWIGNode N)} (hTT' : T ⊆ T')
    (hT : T ⊆ M.observed) (hT' : T' ⊆ M.observed)
    (x : ValuesOn M.observed (swigΩ Ω)) :
    M.qLocalMass s T' hT' x ≤ M.qLocalMass s T hT x := by
  apply MeasureTheory.measure_mono
  intro ℓ hℓ v hv
  exact hℓ v (hTT' hv)

private def singletonValuePt
    (v : SWIGNode N) (ω : swigΩ Ω v) :
    ValuesOn ({v} : Finset (SWIGNode N)) (swigΩ Ω) :=
  fun i => cast (congrArg (swigΩ Ω) (Finset.mem_singleton.mp i.property).symm) ω

@[simp] private lemma singletonValuePt_self
    (v : SWIGNode N) (ω : swigΩ Ω v) :
    singletonValuePt v ω ⟨v, by simp⟩ = ω := by
  simp [singletonValuePt]

@[simp] private lemma overrideOn_singleton_self
    {M : Causalean.SCM N Ω} {v : SWIGNode N} (hv : v ∈ M.observed)
    (x : ValuesOn M.observed (swigΩ Ω)) (ω : swigΩ Ω v) :
    overrideOn (Finset.singleton_subset_iff.mpr hv) x (singletonValuePt v ω)
      ⟨v, hv⟩ = ω := by
  simp

@[simp] private lemma overrideOn_singleton_ne
    {M : Causalean.SCM N Ω} {v w : SWIGNode N}
    (hv : v ∈ M.observed) (hw : w ∈ M.observed) (hvw : w ≠ v)
    (x : ValuesOn M.observed (swigΩ Ω)) (ω : swigΩ Ω v) :
    overrideOn (Finset.singleton_subset_iff.mpr hv) x (singletonValuePt v ω)
      ⟨w, hw⟩ = x ⟨w, hw⟩ := by
  simp [hvw]

private noncomputable def singletonValuePtEquiv
    (v : SWIGNode N) :
    swigΩ Ω v ≃ ValuesOn ({v} : Finset (SWIGNode N)) (swigΩ Ω) where
  toFun := singletonValuePt v
  invFun := fun y => y ⟨v, by simp⟩
  left_inv := by
    intro ω
    simp
  right_inv := by
    intro y
    funext i
    rcases i with ⟨w, hw⟩
    have hwv : w = v := Finset.mem_singleton.mp hw
    subst w
    simp [singletonValuePt]

@[simp] private lemma singletonValuePtEquiv_symm_apply
    (v : SWIGNode N)
    (y : ValuesOn ({v} : Finset (SWIGNode N)) (swigΩ Ω)) :
    singletonValuePt v ((singletonValuePtEquiv (Ω := Ω) v).symm y) = y := by
  exact (singletonValuePtEquiv (Ω := Ω) v).right_inv y

private lemma overrideOn_union_singletonValuePt
    {I U : Finset (SWIGNode N)} {v : SWIGNode N}
    (hUnion : ({v} : Finset (SWIGNode N)) ∪ U ⊆ I)
    (hU : U ⊆ I) (hvI : v ∈ I)
    (x : ValuesOn I (swigΩ Ω)) (y : ValuesOn U (swigΩ Ω))
    (ω : swigΩ Ω v) :
    overrideOn hUnion x (valuesUnionMk (singletonValuePt v ω) y) =
      overrideOn (Finset.singleton_subset_iff.mpr hvI)
        (overrideOn hU x y) (singletonValuePt v ω) := by
  classical
  funext i
  by_cases hiv : i.val = v
  · have hiSing : i.val ∈ ({v} : Finset (SWIGNode N)) := by simp [hiv]
    have hiUnion : i.val ∈ ({v} : Finset (SWIGNode N)) ∪ U :=
      Finset.mem_union_left U hiSing
    rw [overrideOn_mem _ _ _ i hiUnion]
    rw [valuesUnionMk_apply_left _ _ hiUnion hiSing]
    rw [overrideOn_mem _ _ _ i hiSing]
  · have hiNotSing : i.val ∉ ({v} : Finset (SWIGNode N)) := by simpa using hiv
    by_cases hiU : i.val ∈ U
    · have hiUnion : i.val ∈ ({v} : Finset (SWIGNode N)) ∪ U :=
        Finset.mem_union_right _ hiU
      rw [overrideOn_mem _ _ _ i hiUnion]
      rw [valuesUnionMk_apply_right _ _ hiUnion hiNotSing hiU]
      rw [overrideOn_notMem _ _ _ i hiNotSing]
      rw [overrideOn_mem hU x y i hiU]
    · have hiUnionNot : i.val ∉ ({v} : Finset (SWIGNode N)) ∪ U := by
        intro hmem
        rcases Finset.mem_union.mp hmem with hs | hUmem
        · exact hiNotSing hs
        · exact hiU hUmem
      rw [overrideOn_notMem _ _ _ i hiUnionNot]
      rw [overrideOn_notMem _ _ _ i hiNotSing]
      rw [overrideOn_notMem hU x y i hiU]

private lemma marginalizeOn_congr_finset
    [∀ n, Fintype (Ω n)]
    (M : Causalean.SCM N Ω) {A B : Finset (SWIGNode N)}
    (hAB : A = B) (hA : A ⊆ M.observed) (hB : B ⊆ M.observed)
    (q : ValuesOn M.observed (swigΩ Ω) → ENNReal)
    (x : ValuesOn M.observed (swigΩ Ω)) :
    M.marginalizeOn A hA q x = M.marginalizeOn B hB q x := by
  classical
  subst B
  unfold marginalizeOn
  refine Finset.sum_congr rfl ?_
  intro y _hy
  congr

private lemma marginalizeOn_empty
    [∀ n, Fintype (Ω n)]
    (M : Causalean.SCM N Ω)
    (q : ValuesOn M.observed (swigΩ Ω) → ENNReal)
    (x : ValuesOn M.observed (swigΩ Ω)) :
    M.marginalizeOn ∅ (by simp) q x = q x := by
  classical
  unfold marginalizeOn
  let y0 : ValuesOn (∅ : Finset (SWIGNode N)) (swigΩ Ω) :=
    fun i => False.elim (Finset.notMem_empty i.val i.property)
  rw [Finset.sum_eq_single y0]
  · congr
    funext i
    simp
  · intro y _hy hy
    exact (hy (Subsingleton.elim y y0)).elim
  · intro hy
    exact (hy (Finset.mem_univ y0)).elim

private lemma marginalizeOn_insert
    [∀ n, Fintype (Ω n)]
    (M : Causalean.SCM N Ω) {U : Finset (SWIGNode N)} {v : SWIGNode N}
    (hvU : v ∉ U) (hins : insert v U ⊆ M.observed)
    (hU : U ⊆ M.observed)
    (q : ValuesOn M.observed (swigΩ Ω) → ENNReal)
    (x : ValuesOn M.observed (swigΩ Ω)) :
    M.marginalizeOn (insert v U) hins q x =
      M.marginalizeOn U hU
        (fun x' => ∑ ω : swigΩ Ω v,
          q (overrideOn
            (Finset.singleton_subset_iff.mpr
              (hins (Finset.mem_insert_self v U)))
            x' (singletonValuePt v ω))) x := by
  classical
  have hvObs : v ∈ M.observed := hins (Finset.mem_insert_self v U)
  have hInsert : insert v U = ({v} : Finset (SWIGNode N)) ∪ U := by
    ext w
    simp [Finset.mem_insert]
  have hDisj : Disjoint ({v} : Finset (SWIGNode N)) U := by
    rw [Finset.disjoint_left]
    intro w hwv hwU
    exact hvU (by simpa [Finset.mem_singleton.mp hwv] using hwU)
  have hUnion : ({v} : Finset (SWIGNode N)) ∪ U ⊆ M.observed := by
    intro w hw
    rcases Finset.mem_union.mp hw with hwv | hwU
    · simpa [Finset.mem_singleton.mp hwv] using hvObs
    · exact hU hwU
  unfold marginalizeOn
  calc
    (∑ y : ValuesOn (insert v U) (swigΩ Ω),
        q (overrideOn hins x y))
        = ∑ y : ValuesOn (({v} : Finset (SWIGNode N)) ∪ U) (swigΩ Ω),
            q (overrideOn hUnion x y) := by
          refine Fintype.sum_equiv
            (valuesEquivOfEq (Ω := swigΩ Ω) hInsert).toEquiv _ _ ?_
          intro y
          congr
    _ = ∑ p : ValuesOn ({v} : Finset (SWIGNode N)) (swigΩ Ω) ×
              ValuesOn U (swigΩ Ω),
            q (overrideOn hUnion x ((valuesUnionEquiv (Ω := Ω) hDisj).symm p)) := by
          refine Fintype.sum_equiv (valuesUnionEquiv (Ω := Ω) hDisj).toEquiv _ _ ?_
          intro y
          congr
          exact ((valuesUnionEquiv (Ω := Ω) hDisj).left_inv y).symm
    _ = ∑ p : ValuesOn ({v} : Finset (SWIGNode N)) (swigΩ Ω) ×
              ValuesOn U (swigΩ Ω),
            q (overrideOn hUnion x (valuesUnionMk p.1 p.2)) := by
          rfl
    _ = ∑ yv : ValuesOn ({v} : Finset (SWIGNode N)) (swigΩ Ω),
          ∑ yU : ValuesOn U (swigΩ Ω),
            q (overrideOn hUnion x (valuesUnionMk yv yU)) := by
          rw [Fintype.sum_prod_type]
    _ = ∑ yU : ValuesOn U (swigΩ Ω),
          ∑ yv : ValuesOn ({v} : Finset (SWIGNode N)) (swigΩ Ω),
            q (overrideOn hUnion x (valuesUnionMk yv yU)) := by
          simpa using (Finset.sum_comm
            (s := (Finset.univ :
              Finset (ValuesOn ({v} : Finset (SWIGNode N)) (swigΩ Ω))))
            (t := (Finset.univ : Finset (ValuesOn U (swigΩ Ω))))
            (f := fun yv yU => q (overrideOn hUnion x (valuesUnionMk yv yU))))
    _ = ∑ yU : ValuesOn U (swigΩ Ω),
          ∑ ω : swigΩ Ω v,
            q (overrideOn (Finset.singleton_subset_iff.mpr hvObs)
              (overrideOn hU x yU) (singletonValuePt v ω)) := by
          refine Finset.sum_congr rfl ?_
          intro yU _hyU
          refine (Fintype.sum_equiv (singletonValuePtEquiv (Ω := Ω) v)
            (fun ω : swigΩ Ω v =>
              q (overrideOn (Finset.singleton_subset_iff.mpr hvObs)
                (overrideOn hU x yU) (singletonValuePt v ω)))
            (fun yv : ValuesOn ({v} : Finset (SWIGNode N)) (swigΩ Ω) =>
              q (overrideOn hUnion x (valuesUnionMk yv yU))) ?_).symm
          intro ω
          exact (congrArg q
            (overrideOn_union_singletonValuePt hUnion hU hvObs x yU ω)).symm

private lemma localConsistent_override_singleton_of_ne
    (M : Causalean.SCM N Ω) (s : M.FixedValues)
    {T : Finset (SWIGNode N)} (hT : T ⊆ M.observed)
    {v w : SWIGNode N} (hvT : v ∈ T) (hwT : w ∈ T) (hwv : w ≠ v)
    (hNoEdge : ¬ M.dag.edge v w)
    (x : ValuesOn M.observed (swigΩ Ω)) (ω : swigΩ Ω v)
    (ℓ : M.LatentValues) :
    M.localConsistent s
        (overrideOn (Finset.singleton_subset_iff.mpr (hT hvT)) x
          (singletonValuePt v ω))
        w (hT hwT) ℓ ↔
      M.localConsistent s x w (hT hwT) ℓ := by
  classical
  rw [localConsistent_iff_structFun_dispatch,
    localConsistent_iff_structFun_dispatch]
  have htarget :
      overrideOn (Finset.singleton_subset_iff.mpr (hT hvT)) x
          (singletonValuePt v ω) ⟨w, hT hwT⟩ =
        x ⟨w, hT hwT⟩ := by
    exact overrideOn_singleton_ne (hT hvT) (hT hwT) hwv x ω
  have hparents :
      (fun p : {p // p ∈ M.dag.parents w} =>
          if huo : p.val ∈ M.unobserved then ℓ ⟨p.val, huo⟩
          else if hfix : p.val ∈ M.fixed then s ⟨p.val, hfix⟩
          else
            have hedge : M.dag.edge p.val w :=
              M.dag.mem_parents.mp p.property
            have hobs : p.val ∈ M.observed := by
              rcases Finset.mem_union.mp (M.dag_edges_classified _ _ hedge).1 with h1 | h2
              · rcases Finset.mem_union.mp h1 with hfx | hob
                · exact absurd hfx hfix
                · exact hob
              · exact absurd h2 huo
            (show swigΩ Ω p.val from
              overrideOn (Finset.singleton_subset_iff.mpr (hT hvT)) x
                (singletonValuePt v ω) ⟨p.val, hobs⟩))
        =
      (fun p : {p // p ∈ M.dag.parents w} =>
          if huo : p.val ∈ M.unobserved then ℓ ⟨p.val, huo⟩
          else if hfix : p.val ∈ M.fixed then s ⟨p.val, hfix⟩
          else
            have hedge : M.dag.edge p.val w :=
              M.dag.mem_parents.mp p.property
            have hobs : p.val ∈ M.observed := by
              rcases Finset.mem_union.mp (M.dag_edges_classified _ _ hedge).1 with h1 | h2
              · rcases Finset.mem_union.mp h1 with hfx | hob
                · exact absurd hfx hfix
                · exact hob
              · exact absurd h2 huo
            (show swigΩ Ω p.val from x ⟨p.val, hobs⟩)) := by
    funext p
    by_cases huo : p.val ∈ M.unobserved
    · simp [huo]
    · by_cases hfix : p.val ∈ M.fixed
      · simp [huo, hfix]
      · have hpv : p.val ≠ v := by
          intro hpv
          exact hNoEdge (hpv ▸ M.dag.mem_parents.mp p.property)
        simp [huo, hfix, overrideOn_singleton_ne (hT hvT) _ hpv x ω]
  rw [hparents, htarget]

private noncomputable def localStructValue
    (M : Causalean.SCM N Ω) (s : M.FixedValues)
    (x : ValuesOn M.observed (swigΩ Ω)) (v : SWIGNode N)
    (hv : v ∈ M.observed) (ℓ : M.LatentValues) : swigΩ Ω v :=
  M.structFun ⟨v, hv⟩
    (fun p : {p // p ∈ M.dag.parents v} =>
      if huo : p.val ∈ M.unobserved then ℓ ⟨p.val, huo⟩
      else if hfix : p.val ∈ M.fixed then s ⟨p.val, hfix⟩
      else
        have hedge : M.dag.edge p.val v :=
          M.dag.mem_parents.mp p.property
        have hobs : p.val ∈ M.observed := by
          rcases Finset.mem_union.mp (M.dag_edges_classified _ _ hedge).1 with h1 | h2
          · rcases Finset.mem_union.mp h1 with hfx | hob
            · exact absurd hfx hfix
            · exact hob
          · exact absurd h2 huo
        (show swigΩ Ω p.val from x ⟨p.val, hobs⟩))

private lemma localConsistent_override_singleton_self_iff
    (M : Causalean.SCM N Ω) (s : M.FixedValues)
    {T : Finset (SWIGNode N)} (hT : T ⊆ M.observed)
    {v : SWIGNode N} (hvT : v ∈ T)
    (x : ValuesOn M.observed (swigΩ Ω)) (ω : swigΩ Ω v)
    (ℓ : M.LatentValues) :
    M.localConsistent s
        (overrideOn (Finset.singleton_subset_iff.mpr (hT hvT)) x
          (singletonValuePt v ω))
        v (hT hvT) ℓ ↔
      localStructValue M s x v (hT hvT) ℓ = ω := by
  classical
  rw [localConsistent_iff_structFun_dispatch]
  unfold localStructValue
  have htarget :
      overrideOn (Finset.singleton_subset_iff.mpr (hT hvT)) x
          (singletonValuePt v ω) ⟨v, hT hvT⟩ = ω := by
    exact overrideOn_singleton_self (hT hvT) x ω
  have hparents :
      (fun p : {p // p ∈ M.dag.parents v} =>
          if huo : p.val ∈ M.unobserved then ℓ ⟨p.val, huo⟩
          else if hfix : p.val ∈ M.fixed then s ⟨p.val, hfix⟩
          else
            have hedge : M.dag.edge p.val v :=
              M.dag.mem_parents.mp p.property
            have hobs : p.val ∈ M.observed := by
              rcases Finset.mem_union.mp (M.dag_edges_classified _ _ hedge).1 with h1 | h2
              · rcases Finset.mem_union.mp h1 with hfx | hob
                · exact absurd hfx hfix
                · exact hob
              · exact absurd h2 huo
            (show swigΩ Ω p.val from
              overrideOn (Finset.singleton_subset_iff.mpr (hT hvT)) x
                (singletonValuePt v ω) ⟨p.val, hobs⟩))
        =
      (fun p : {p // p ∈ M.dag.parents v} =>
          if huo : p.val ∈ M.unobserved then ℓ ⟨p.val, huo⟩
          else if hfix : p.val ∈ M.fixed then s ⟨p.val, hfix⟩
          else
            have hedge : M.dag.edge p.val v :=
              M.dag.mem_parents.mp p.property
            have hobs : p.val ∈ M.observed := by
              rcases Finset.mem_union.mp (M.dag_edges_classified _ _ hedge).1 with h1 | h2
              · rcases Finset.mem_union.mp h1 with hfx | hob
                · exact absurd hfx hfix
                · exact hob
              · exact absurd h2 huo
            (show swigΩ Ω p.val from x ⟨p.val, hobs⟩)) := by
    funext p
    by_cases huo : p.val ∈ M.unobserved
    · simp [huo]
    · by_cases hfix : p.val ∈ M.fixed
      · simp [huo, hfix]
      · have hpv : p.val ≠ v := by
          intro hpv
          exact M.dag.irrefl v (by
            simpa [hpv] using M.dag.mem_parents.mp p.property)
        simp [huo, hfix, overrideOn_singleton_ne (hT hvT) _ hpv x ω]
  rw [hparents, htarget]

private lemma qLocalEvent_override_singleton_eq_inter
    (M : Causalean.SCM N Ω) (s : M.FixedValues)
    {T : Finset (SWIGNode N)} (hT : T ⊆ M.observed)
    {v : SWIGNode N} (hvT : v ∈ T)
    (hNoChild : ∀ w ∈ T, ¬ M.dag.edge v w)
    (x : ValuesOn M.observed (swigΩ Ω)) (ω : swigΩ Ω v) :
    {ℓ : M.LatentValues | ∀ w (hw : w ∈ T),
      M.localConsistent s
        (overrideOn (Finset.singleton_subset_iff.mpr (hT hvT)) x
          (singletonValuePt v ω))
        w (hT hw) ℓ} =
      {ℓ : M.LatentValues | ∀ w (hw : w ∈ T.erase v),
        M.localConsistent s x w (hT (Finset.mem_of_mem_erase hw)) ℓ} ∩
      {ℓ : M.LatentValues | localStructValue M s x v (hT hvT) ℓ = ω} := by
  classical
  ext ℓ
  constructor
  · intro hℓ
    constructor
    · intro w hw
      have hwT : w ∈ T := Finset.mem_of_mem_erase hw
      have hwv : w ≠ v := (Finset.mem_erase.mp hw).1
      exact (localConsistent_override_singleton_of_ne M s hT hvT hwT hwv
        (hNoChild w hwT) x ω ℓ).mp (hℓ w hwT)
    · exact (localConsistent_override_singleton_self_iff M s hT hvT x ω ℓ).mp
        (hℓ v hvT)
  · rintro ⟨hrest, hv⟩ w hwT
    by_cases hwv : w = v
    · subst w
      exact (localConsistent_override_singleton_self_iff M s hT hvT x ω ℓ).mpr hv
    · have hwerase : w ∈ T.erase v := Finset.mem_erase.mpr ⟨hwv, hwT⟩
      exact (localConsistent_override_singleton_of_ne M s hT hvT hwT hwv
        (hNoChild w hwT) x ω ℓ).mpr (hrest w hwerase)

/-- Summing a local q-mass over one childless observed coordinate removes that
coordinate from the constrained set. -/
lemma qLocalMass_sum_point_eliminate
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (s : M.FixedValues)
    (T : Finset (SWIGNode N)) (hT : T ⊆ M.observed)
    {v : SWIGNode N} (hvT : v ∈ T)
    (hNoChild : ∀ w ∈ T, ¬ M.dag.edge v w)
    (x : ValuesOn M.observed (swigΩ Ω)) :
    (∑ ω : swigΩ Ω v,
      M.qLocalMass s T hT
        (overrideOn (Finset.singleton_subset_iff.mpr (hT hvT)) x
          (singletonValuePt v ω))) =
      M.qLocalMass s (T.erase v)
        (fun _ hv => hT (Finset.mem_of_mem_erase hv)) x := by
  classical
  let Erest : Set M.LatentValues :=
    {ℓ | ∀ w (hw : w ∈ T.erase v),
      M.localConsistent s x w (hT (Finset.mem_of_mem_erase hw)) ℓ}
  let Fset : swigΩ Ω v → Set M.LatentValues :=
    fun ω => {ℓ | localStructValue M s x v (hT hvT) ℓ = ω}
  have hevent :
      ∀ ω : swigΩ Ω v,
        {ℓ : M.LatentValues | ∀ w (hw : w ∈ T),
          M.localConsistent s
            (overrideOn (Finset.singleton_subset_iff.mpr (hT hvT)) x
              (singletonValuePt v ω))
            w (hT hw) ℓ} = Erest ∩ Fset ω := by
    intro ω
    simpa [Erest, Fset] using
      qLocalEvent_override_singleton_eq_inter M s hT hvT hNoChild x ω
  have hdisj :
      Set.PairwiseDisjoint (↑(Finset.univ : Finset (swigΩ Ω v)))
        (fun ω => Erest ∩ Fset ω) := by
    intro ω₁ _ ω₂ _ hne
    change Disjoint (Erest ∩ Fset ω₁) (Erest ∩ Fset ω₂)
    rw [Set.disjoint_left]
    intro ℓ hℓ₁ hℓ₂
    exact hne (hℓ₁.2.symm.trans hℓ₂.2)
  have hmeas :
      ∀ ω ∈ (Finset.univ : Finset (swigΩ Ω v)),
        MeasurableSet (Erest ∩ Fset ω) := by
    intro ω _hω
    exact Set.Finite.measurableSet (Set.toFinite _)
  have hunion :
      (⋃ ω ∈ (Finset.univ : Finset (swigΩ Ω v)), Erest ∩ Fset ω) = Erest := by
    ext ℓ
    simp [Fset]
  simp only [qLocalMass]
  calc
    (∑ ω : swigΩ Ω v,
        M.latentProduct {ℓ : M.LatentValues | ∀ w (hw : w ∈ T),
          M.localConsistent s
            (overrideOn (Finset.singleton_subset_iff.mpr (hT hvT)) x
              (singletonValuePt v ω))
            w (hT hw) ℓ})
        =
      ∑ ω : swigΩ Ω v, M.latentProduct (Erest ∩ Fset ω) := by
        refine Finset.sum_congr rfl ?_
        intro ω _hω
        rw [hevent ω]
    _ = M.latentProduct (⋃ ω ∈ (Finset.univ : Finset (swigΩ Ω v)),
          Erest ∩ Fset ω) := by
        symm
        simpa using
          (MeasureTheory.measure_biUnion_finset
            (μ := M.latentProduct)
            (s := (Finset.univ : Finset (swigΩ Ω v)))
            (f := fun ω => Erest ∩ Fset ω) hdisj hmeas)
    _ = M.latentProduct Erest := by
        rw [hunion]

private lemma exists_sdiff_topoMax_noChild
    (M : Causalean.SCM N Ω)
    {T W : Finset (SWIGNode N)}
    (hne : (T \ W).Nonempty)
    (hclosed : ∀ v ∈ T, ∀ w ∈ W, M.dag.edge v w → v ∈ W) :
    ∃ v ∈ T \ W, ∀ w ∈ T, ¬ M.dag.edge v w := by
  classical
  obtain ⟨v, hvS, hvMax⟩ :=
    Finset.exists_max_image (T \ W) M.dag.topoOrder hne
  refine ⟨v, hvS, ?_⟩
  intro w hwT hvw
  have hvT : v ∈ T := (Finset.mem_sdiff.mp hvS).1
  have hvNotW : v ∉ W := (Finset.mem_sdiff.mp hvS).2
  by_cases hwW : w ∈ W
  · exact hvNotW (hclosed v hvT w hwW hvw)
  · have hwS : w ∈ T \ W := Finset.mem_sdiff.mpr ⟨hwT, hwW⟩
    have hle : M.dag.topoOrder w ≤ M.dag.topoOrder v := hvMax w hwS
    exact (not_lt_of_ge hle) (M.dag.topoOrder_lt v w hvw)

omit [Fintype N] in
private lemma erase_sdiff_eq_sdiff_erase
    {T W : Finset (SWIGNode N)} {v : SWIGNode N} :
    (T.erase v) \ W = (T \ W).erase v := by
  ext w
  simp [Finset.mem_sdiff, Finset.mem_erase, and_assoc]

/-- Marginalizing a local q-mass over `T \ W` gives the q-mass on `W` when `W`
is parent-closed inside `T`. -/
lemma qLocalMass_marginalize_ancestralClosed
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (s : M.FixedValues)
    (T W : Finset (SWIGNode N)) (hT : T ⊆ M.observed) (hWT : W ⊆ T)
    (hclosed : ∀ v ∈ T, ∀ w ∈ W, M.dag.edge v w → v ∈ W)
    (x : ValuesOn M.observed (swigΩ Ω)) :
    M.marginalizeOn (T \ W)
        (fun _ hv => hT ((Finset.mem_sdiff.mp hv).1))
        (M.qLocalMass s T hT) x =
      M.qLocalMass s W (fun _ hv => hT (hWT hv)) x := by
  classical
  let P : Nat → Prop := fun n =>
    ∀ (T : Finset (SWIGNode N)) (hT : T ⊆ M.observed) (hWT : W ⊆ T),
      (∀ v ∈ T, ∀ w ∈ W, M.dag.edge v w → v ∈ W) →
      ∀ x : ValuesOn M.observed (swigΩ Ω),
      (T \ W).card = n →
        M.marginalizeOn (T \ W)
            (fun _ hv => hT ((Finset.mem_sdiff.mp hv).1))
            (M.qLocalMass s T hT) x =
          M.qLocalMass s W (fun _ hv => hT (hWT hv)) x
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro T hT hWT hclosed x hcard
      by_cases hempty : T \ W = ∅
      · have hTW : T ⊆ W := by
          intro v hvT
          by_contra hvW
          have hvS : v ∈ T \ W := Finset.mem_sdiff.mpr ⟨hvT, hvW⟩
          simp [hempty] at hvS
        have hEq : T = W := Finset.Subset.antisymm hTW hWT
        subst T
        simpa [Finset.sdiff_self] using
          (marginalizeOn_empty M (M.qLocalMass s W hT) x)
      · have hne : (T \ W).Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
        obtain ⟨v, hvS, hNoChild⟩ :=
          exists_sdiff_topoMax_noChild M hne hclosed
        let U : Finset (SWIGNode N) := (T \ W).erase v
        have hvT : v ∈ T := (Finset.mem_sdiff.mp hvS).1
        have hvNotW : v ∉ W := (Finset.mem_sdiff.mp hvS).2
        have hvNotU : v ∉ U := by
          dsimp [U]
          simp
        have hS_eq : T \ W = insert v U := by
          dsimp [U]
          exact (Finset.insert_erase hvS).symm
        have hUobs : U ⊆ M.observed := by
          intro u hu
          exact hT ((Finset.mem_sdiff.mp (Finset.mem_of_mem_erase hu)).1)
        have hInsobs : insert v U ⊆ M.observed := by
          intro u hu
          have huS : u ∈ T \ W := by
            simpa [hS_eq] using hu
          exact hT ((Finset.mem_sdiff.mp huS).1)
        let hTerase : T.erase v ⊆ M.observed :=
          fun _ hv => hT (Finset.mem_of_mem_erase hv)
        have hfun :
            (fun x' : ValuesOn M.observed (swigΩ Ω) =>
              ∑ ω : swigΩ Ω v,
                M.qLocalMass s T hT
                  (overrideOn
                    (Finset.singleton_subset_iff.mpr
                      (hInsobs (Finset.mem_insert_self v U)))
                    x' (singletonValuePt v ω))) =
            (fun x' : ValuesOn M.observed (swigΩ Ω) =>
              M.qLocalMass s (T.erase v) hTerase x') := by
          funext x'
          simpa using
            (qLocalMass_sum_point_eliminate M s T hT hvT hNoChild x')
        have hEraseSdiff : (T.erase v) \ W = U := by
          dsimp [U]
          exact erase_sdiff_eq_sdiff_erase
        have hcard_lt : ((T.erase v) \ W).card < n := by
          rw [hEraseSdiff]
          dsimp [U]
          rw [← hcard]
          exact Finset.card_erase_lt_of_mem hvS
        have hWTerase : W ⊆ T.erase v := by
          intro w hw
          refine Finset.mem_erase.mpr ⟨?_, hWT hw⟩
          intro hwv
          exact hvNotW (by simpa [hwv] using hw)
        have hclosedErase :
            ∀ a ∈ T.erase v, ∀ w ∈ W, M.dag.edge a w → a ∈ W := by
          intro a ha w hw haw
          exact hclosed a (Finset.mem_of_mem_erase ha) w hw haw
        calc
          M.marginalizeOn (T \ W)
              (fun _ hv => hT ((Finset.mem_sdiff.mp hv).1))
              (M.qLocalMass s T hT) x
              =
            M.marginalizeOn (insert v U) hInsobs (M.qLocalMass s T hT) x := by
              exact marginalizeOn_congr_finset M hS_eq
                (fun _ hv => hT ((Finset.mem_sdiff.mp hv).1))
                hInsobs (M.qLocalMass s T hT) x
          _ =
            M.marginalizeOn U hUobs
              (fun x' => ∑ ω : swigΩ Ω v,
                M.qLocalMass s T hT
                  (overrideOn
                    (Finset.singleton_subset_iff.mpr
                      (hInsobs (Finset.mem_insert_self v U)))
                    x' (singletonValuePt v ω))) x := by
              exact marginalizeOn_insert M hvNotU hInsobs hUobs
                (M.qLocalMass s T hT) x
          _ =
            M.marginalizeOn U hUobs
              (M.qLocalMass s (T.erase v) hTerase) x := by
              rw [hfun]
          _ =
            M.marginalizeOn ((T.erase v) \ W)
              (fun _ hv => hTerase ((Finset.mem_sdiff.mp hv).1))
              (M.qLocalMass s (T.erase v) hTerase) x := by
              exact marginalizeOn_congr_finset M hEraseSdiff.symm
                hUobs
                (fun _ hv => hTerase ((Finset.mem_sdiff.mp hv).1))
                (M.qLocalMass s (T.erase v) hTerase) x
          _ = M.qLocalMass s W (fun _ hv => hT (hWT hv)) x := by
              have hIH := ih ((T.erase v) \ W).card hcard_lt
                (T.erase v) hTerase hWTerase hclosedErase x rfl
              simpa [hTerase] using hIH
  exact hP (T \ W).card T hT hWT hclosed x rfl

private lemma latentProduct_singleton_eq_prod
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (ℓ₀ : M.LatentValues) :
    M.latentProduct ({ℓ₀} : Set M.LatentValues) =
      ∏ u : {u // u ∈ M.unobserved},
        M.latentDist u ({ℓ₀ u} : Set (swigΩ Ω u.val)) := by
  classical
  haveI : ∀ u : {u // u ∈ M.unobserved},
      MeasureTheory.IsProbabilityMeasure (M.latentDist u) :=
    M.isProbability_latent
  haveI : ∀ u : {u // u ∈ M.unobserved},
      MeasureTheory.SigmaFinite (M.latentDist u) := fun _ => inferInstance
  unfold SCM.latentProduct
  have hsingleton :
      ({ℓ₀} : Set M.LatentValues) =
        Set.univ.pi (fun u => ({ℓ₀ u} : Set (swigΩ Ω u.val))) := by
    ext ℓ
    simp [Set.mem_pi, funext_iff]
  rw [hsingleton, MeasureTheory.Measure.pi_pi]

private lemma cComponentOf_eq_of_mem_cComponentSet
    (M : Causalean.SCM N Ω) {C : Finset (SWIGNode N)}
    (hC : C ∈ M.toSWIGGraph.cComponentSet) {v : SWIGNode N} (hvC : v ∈ C) :
    M.toSWIGGraph.cComponentOf v = C := by
  classical
  have hvObs : v ∈ M.observed :=
    M.toSWIGGraph.cComponentSet_subset_observed C hC hvC
  have hCv : M.toSWIGGraph.cComponentOf v ∈ M.toSWIGGraph.cComponentSet := by
    rw [SWIGGraph.cComponentSet, Finset.mem_image]
    exact ⟨v, hvObs, rfl⟩
  by_contra hne
  exact Finset.disjoint_left.mp
    (M.toSWIGGraph.cComponentSet_pairwise_disjoint hCv hC hne)
    (M.toSWIGGraph.mem_cComponentOf_self hvObs) hvC

private lemma measurableSet_comap_piFinset_of_depends
    {ι : Type*} [Fintype ι]
    {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    [∀ i, Fintype (α i)] [∀ i, MeasurableSingletonClass (α i)]
    (S : Finset ι) (A : Set (∀ i, α i))
    (hdep : ∀ ξ ξ', (∀ i (_hi : i ∈ S), ξ i = ξ' i) → (ξ ∈ A ↔ ξ' ∈ A)) :
    MeasurableSet[
      MeasurableSpace.comap (fun ξ : (∀ i, α i) => fun i : S => ξ i)
        inferInstance] A := by
  let B : Set (∀ i : S, α i.val) :=
    {η | ∃ ξ ∈ A, (fun i : S => ξ i) = η}
  refine ⟨B, Set.Finite.measurableSet B.toFinite, ?_⟩
  ext ξ
  change ξ ∈ ((fun ξ : (∀ i, α i) => fun i : S => ξ i) ⁻¹' B) ↔ ξ ∈ A
  constructor
  · rintro ⟨ξ', hξ'A, hξ'⟩
    exact (hdep ξ' ξ (by
      intro i hi
      exact congrFun hξ' ⟨i, hi⟩)).mp hξ'A
  · intro hξA
    exact ⟨ξ, hξA, rfl⟩

private noncomputable def latentBlockIndex
    (M : Causalean.SCM N Ω) (C : Finset (SWIGNode N)) :
    Finset {u // u ∈ M.unobserved} :=
  Finset.univ.filter (fun u : {u // u ∈ M.unobserved} => u.val ∈ M.latentBlock C)

private lemma mem_latentBlockIndex_iff
    (M : Causalean.SCM N Ω) (C : Finset (SWIGNode N))
    (u : {u // u ∈ M.unobserved}) :
    u ∈ latentBlockIndex M C ↔ u.val ∈ M.latentBlock C := by
  simp [latentBlockIndex]

private lemma latentBlockIndex_pairwise_disjoint
    (M : Causalean.SCM N Ω) {C D : Finset (SWIGNode N)}
    (hC : C ∈ M.toSWIGGraph.cComponentSet)
    (hD : D ∈ M.toSWIGGraph.cComponentSet) (hne : C ≠ D) :
    Disjoint (latentBlockIndex M C) (latentBlockIndex M D) := by
  classical
  rw [Finset.disjoint_left]
  intro u huC huD
  have huC' : u.val ∈ M.latentBlock C :=
    (mem_latentBlockIndex_iff M C u).mp huC
  have huD' : u.val ∈ M.latentBlock D :=
    (mem_latentBlockIndex_iff M D u).mp huD
  exact Finset.disjoint_left.mp (M.latentBlock_pairwise_disjoint hC hD hne) huC' huD'

private lemma latentBlockIndex_pairwise_disjoint_of_latentBlock
    (M : Causalean.SCM N Ω) {C D : Finset (SWIGNode N)}
    (hdisj : Disjoint (M.latentBlock C) (M.latentBlock D)) :
    Disjoint (latentBlockIndex M C) (latentBlockIndex M D) := by
  classical
  rw [Finset.disjoint_left]
  intro u huC huD
  exact Finset.disjoint_left.mp hdisj
    ((mem_latentBlockIndex_iff M C u).mp huC)
    ((mem_latentBlockIndex_iff M D u).mp huD)

private lemma latentBlockIndex_biUnion_disjoint_of_pairwise
    (M : Causalean.SCM N Ω) {𝒞 S : Finset (Finset (SWIGNode N))}
    {C : Finset (SWIGNode N)} (hS : S ⊆ 𝒞) (hC : C ∈ 𝒞)
    (hCnot : C ∉ S)
    (hblock :
      (↑𝒞 : Set (Finset (SWIGNode N))).Pairwise
        (fun U U' => Disjoint (M.latentBlock U) (M.latentBlock U'))) :
    Disjoint (S.biUnion (latentBlockIndex M)) (latentBlockIndex M C) := by
  classical
  rw [Finset.disjoint_left]
  intro u huS huC
  rw [Finset.mem_biUnion] at huS
  rcases huS with ⟨D, hDS, huD⟩
  have hD : D ∈ 𝒞 := hS hDS
  have hne : D ≠ C := by
    intro hDC
    exact hCnot (hDC ▸ hDS)
  exact Finset.disjoint_left.mp
    (latentBlockIndex_pairwise_disjoint_of_latentBlock M
      (hblock hD hC hne)) huD huC

private lemma latentBlockIndex_biUnion_disjoint
    (M : Causalean.SCM N Ω) {S : Finset (Finset (SWIGNode N))}
    {C : Finset (SWIGNode N)} (hS : S ⊆ M.toSWIGGraph.cComponentSet)
    (hC : C ∈ M.toSWIGGraph.cComponentSet) (hCnot : C ∉ S) :
    Disjoint (S.biUnion (latentBlockIndex M)) (latentBlockIndex M C) := by
  classical
  rw [Finset.disjoint_left]
  intro u huS huC
  rw [Finset.mem_biUnion] at huS
  rcases huS with ⟨D, hDS, huD⟩
  have hne : D ≠ C := by
    intro hDC
    exact hCnot (hDC ▸ hDS)
  exact Finset.disjoint_left.mp
    (latentBlockIndex_pairwise_disjoint M (hS hDS) hC hne) huD huC

private lemma localConsistent_event_measurable_comap_latentBlockIndex
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (s : M.FixedValues)
    (P : Finset (SWIGNode N)) (hP : M.ObsParentClosed P)
    (x : ValuesOn M.observed (swigΩ Ω))
    {C : Finset (SWIGNode N)} (hC : C ∈ M.toSWIGGraph.cComponentSet) :
    MeasurableSet[
      MeasurableSpace.comap
        (fun ℓ : M.LatentValues => fun u : latentBlockIndex M C => ℓ u)
        inferInstance]
      {ℓ : M.LatentValues | ∀ v (hv : v ∈ C ∩ P),
        M.localConsistent s x v
          (hP.1 (Finset.mem_of_mem_inter_right hv)) ℓ} := by
  classical
  refine measurableSet_comap_piFinset_of_depends
    (S := latentBlockIndex M C) _ ?_
  intro ℓ ℓ' hagree
  constructor
  · intro hℓ v hv
    have hvC : v ∈ C := Finset.mem_of_mem_inter_left hv
    have hcomp : M.toSWIGGraph.cComponentOf v = C :=
      cComponentOf_eq_of_mem_cComponentSet M hC hvC
    exact (M.localConsistent_depends_only_on_block s x v
      (hP.1 (Finset.mem_of_mem_inter_right hv)) ℓ ℓ' (by
        intro u hu
        have huC : u ∈ M.latentBlock C := by simpa [hcomp] using hu
        have hmem :
            (⟨u, (Finset.mem_filter.mp huC).1⟩ : {u // u ∈ M.unobserved})
              ∈ latentBlockIndex M C :=
          (mem_latentBlockIndex_iff M C _).mpr huC
        have hcoord := hagree ⟨u, (Finset.mem_filter.mp huC).1⟩ hmem
        simpa using hcoord)).mp (hℓ v hv)
  · intro hℓ' v hv
    have hvC : v ∈ C := Finset.mem_of_mem_inter_left hv
    have hcomp : M.toSWIGGraph.cComponentOf v = C :=
      cComponentOf_eq_of_mem_cComponentSet M hC hvC
    exact (M.localConsistent_depends_only_on_block s x v
      (hP.1 (Finset.mem_of_mem_inter_right hv)) ℓ' ℓ (by
        intro u hu
        have huC : u ∈ M.latentBlock C := by simpa [hcomp] using hu
        have hmem :
            (⟨u, (Finset.mem_filter.mp huC).1⟩ : {u // u ∈ M.unobserved})
              ∈ latentBlockIndex M C :=
          (mem_latentBlockIndex_iff M C _).mpr huC
        have hcoord := hagree ⟨u, (Finset.mem_filter.mp huC).1⟩ hmem
        simpa using hcoord.symm)).mp (hℓ' v hv)

private lemma localConsistent_biInter_event_measurable_comap_latentBlockIndex
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (s : M.FixedValues)
    (P : Finset (SWIGNode N)) (hP : M.ObsParentClosed P)
    (x : ValuesOn M.observed (swigΩ Ω))
    {S : Finset (Finset (SWIGNode N))}
    (hS : S ⊆ M.toSWIGGraph.cComponentSet) :
    MeasurableSet[
      MeasurableSpace.comap
        (fun ℓ : M.LatentValues =>
          fun u : S.biUnion (latentBlockIndex M) => ℓ u)
        inferInstance]
      (⋂ C ∈ S, {ℓ : M.LatentValues | ∀ v (hv : v ∈ C ∩ P),
        M.localConsistent s x v
          (hP.1 (Finset.mem_of_mem_inter_right hv)) ℓ}) := by
  classical
  refine measurableSet_comap_piFinset_of_depends
    (S := S.biUnion (latentBlockIndex M)) _ ?_
  intro ℓ ℓ' hagree
  constructor
  · intro hℓ
    rw [Set.mem_iInter] at hℓ
    rw [Set.mem_iInter]
    intro C
    have hℓC := hℓ C
    rw [Set.mem_iInter] at hℓC
    rw [Set.mem_iInter]
    intro hCS v hv
    have hvC : v ∈ C := Finset.mem_of_mem_inter_left hv
    have hcomp : M.toSWIGGraph.cComponentOf v = C :=
      cComponentOf_eq_of_mem_cComponentSet M (hS hCS) hvC
    exact (M.localConsistent_depends_only_on_block s x v
      (hP.1 (Finset.mem_of_mem_inter_right hv)) ℓ ℓ' (by
        intro u hu
        have huC : u ∈ M.latentBlock C := by simpa [hcomp] using hu
        have hmemBlock :
            (⟨u, (Finset.mem_filter.mp huC).1⟩ : {u // u ∈ M.unobserved})
              ∈ latentBlockIndex M C :=
          (mem_latentBlockIndex_iff M C _).mpr huC
        have hmem :
            (⟨u, (Finset.mem_filter.mp huC).1⟩ : {u // u ∈ M.unobserved})
              ∈ S.biUnion (latentBlockIndex M) := by
          rw [Finset.mem_biUnion]
          exact ⟨C, hCS, hmemBlock⟩
        have hcoord := hagree ⟨u, (Finset.mem_filter.mp huC).1⟩ hmem
        simpa using hcoord)).mp (hℓC hCS v hv)
  · intro hℓ'
    rw [Set.mem_iInter] at hℓ'
    rw [Set.mem_iInter]
    intro C
    have hℓ'C := hℓ' C
    rw [Set.mem_iInter] at hℓ'C
    rw [Set.mem_iInter]
    intro hCS v hv
    have hvC : v ∈ C := Finset.mem_of_mem_inter_left hv
    have hcomp : M.toSWIGGraph.cComponentOf v = C :=
      cComponentOf_eq_of_mem_cComponentSet M (hS hCS) hvC
    exact (M.localConsistent_depends_only_on_block s x v
      (hP.1 (Finset.mem_of_mem_inter_right hv)) ℓ' ℓ (by
        intro u hu
        have huC : u ∈ M.latentBlock C := by simpa [hcomp] using hu
        have hmemBlock :
            (⟨u, (Finset.mem_filter.mp huC).1⟩ : {u // u ∈ M.unobserved})
              ∈ latentBlockIndex M C :=
          (mem_latentBlockIndex_iff M C _).mpr huC
        have hmem :
            (⟨u, (Finset.mem_filter.mp huC).1⟩ : {u // u ∈ M.unobserved})
              ∈ S.biUnion (latentBlockIndex M) := by
          rw [Finset.mem_biUnion]
          exact ⟨C, hCS, hmemBlock⟩
        have hcoord := hagree ⟨u, (Finset.mem_filter.mp huC).1⟩ hmem
        simpa using hcoord.symm)).mp (hℓ'C hCS v hv)

private lemma localConsistent_depends_only_on_latentBlock_of_mem
    (M : Causalean.SCM N Ω) (s : M.FixedValues)
    (x : ValuesOn M.observed (swigΩ Ω)) {U : Finset (SWIGNode N)}
    {v : SWIGNode N} (hvU : v ∈ U) (hv : v ∈ M.observed)
    (ℓ ℓ' : M.LatentValues)
    (hℓ : ∀ u (hu : u ∈ M.latentBlock U),
      ℓ ⟨u, (Finset.mem_filter.mp hu).1⟩ =
        ℓ' ⟨u, (Finset.mem_filter.mp hu).1⟩) :
    M.localConsistent s x v hv ℓ ↔ M.localConsistent s x v hv ℓ' := by
  unfold localConsistent
  set j : Fin M.observed.card := M.observedIndex ⟨v, hv⟩ with hj
  have hat : (M.observedAt j).val = v := by
    rw [hj]
    exact M.observedAt_observedIndex ⟨v, hv⟩
  have hfun :
      M.structFun (M.observedAt j)
          (fun w => M.parentMap s ℓ j.isLt (prevFromObservedValues M x) w)
        =
      M.structFun (M.observedAt j)
          (fun w => M.parentMap s ℓ' j.isLt (prevFromObservedValues M x) w) := by
    congr 1
    funext w
    by_cases huo : w.val ∈ M.unobserved
    · rw [parentMap_unobserved M s ℓ j.isLt _ w huo,
          parentMap_unobserved M s ℓ' j.isLt _ w huo]
      have hedge_v : M.dag.edge w.val v := by
        have hedge_at : M.dag.edge w.val (M.observedAt j).val :=
          M.dag.mem_parents.mp w.property
        simpa [hat] using hedge_at
      have huBlock : w.val ∈ M.latentBlock U := by
        rw [latentBlock, Finset.mem_filter]
        exact ⟨huo, ⟨v, hvU, hedge_v⟩⟩
      exact hℓ w.val huBlock
    · by_cases hfix : w.val ∈ M.fixed
      · rw [parentMap_fixed M s ℓ j.isLt _ w huo hfix,
            parentMap_fixed M s ℓ' j.isLt _ w huo hfix]
      · have hedge : M.dag.edge w.val (M.observedAt j).val :=
          M.dag.mem_parents.mp w.property
        have hobs : w.val ∈ M.observed := by
          rcases Finset.mem_union.mp (M.dag_edges_classified _ _ hedge).1 with h1 | h2
          · rcases Finset.mem_union.mp h1 with hfx | hob
            · exact absurd hfx hfix
            · exact hob
          · exact absurd h2 huo
        rw [parentMap_observed M s ℓ j.isLt _ w huo hfix hobs,
            parentMap_observed M s ℓ' j.isLt _ w huo hfix hobs]
  subst j
  change
    ((M.observedAt_observedIndex ⟨v, hv⟩) ▸
        M.structFun (M.observedAt (M.observedIndex ⟨v, hv⟩))
          (fun w => M.parentMap s ℓ (M.observedIndex ⟨v, hv⟩).isLt
            (prevFromObservedValues M x) w)
        = x ⟨v, hv⟩)
      ↔
    ((M.observedAt_observedIndex ⟨v, hv⟩) ▸
        M.structFun (M.observedAt (M.observedIndex ⟨v, hv⟩))
          (fun w => M.parentMap s ℓ' (M.observedIndex ⟨v, hv⟩).isLt
            (prevFromObservedValues M x) w)
        = x ⟨v, hv⟩)
  rw [hfun]

private lemma localConsistent_event_measurable_comap_latentBlockIndex_of_family
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (s : M.FixedValues)
    (U : Finset (SWIGNode N)) (hUobs : U ⊆ M.observed)
    (x : ValuesOn M.observed (swigΩ Ω)) :
    MeasurableSet[
      MeasurableSpace.comap
        (fun ℓ : M.LatentValues => fun u : latentBlockIndex M U => ℓ u)
        inferInstance]
      {ℓ : M.LatentValues | ∀ v (hv : v ∈ U),
        M.localConsistent s x v (hUobs hv) ℓ} := by
  classical
  refine measurableSet_comap_piFinset_of_depends
    (S := latentBlockIndex M U) _ ?_
  intro ℓ ℓ' hagree
  constructor
  · intro hℓ v hv
    exact (localConsistent_depends_only_on_latentBlock_of_mem M s x hv
      (hUobs hv) ℓ ℓ' (by
        intro u hu
        have hmem :
            (⟨u, (Finset.mem_filter.mp hu).1⟩ : {u // u ∈ M.unobserved})
              ∈ latentBlockIndex M U :=
          (mem_latentBlockIndex_iff M U _).mpr hu
        have hcoord := hagree ⟨u, (Finset.mem_filter.mp hu).1⟩ hmem
        simpa using hcoord)).mp (hℓ v hv)
  · intro hℓ' v hv
    exact (localConsistent_depends_only_on_latentBlock_of_mem M s x hv
      (hUobs hv) ℓ' ℓ (by
        intro u hu
        have hmem :
            (⟨u, (Finset.mem_filter.mp hu).1⟩ : {u // u ∈ M.unobserved})
              ∈ latentBlockIndex M U :=
          (mem_latentBlockIndex_iff M U _).mpr hu
        have hcoord := hagree ⟨u, (Finset.mem_filter.mp hu).1⟩ hmem
        simpa using hcoord.symm)).mp (hℓ' v hv)

private lemma localConsistent_biInter_event_measurable_comap_latentBlockIndex_of_family
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (s : M.FixedValues)
    (𝒞 S : Finset (Finset (SWIGNode N))) (hS : S ⊆ 𝒞)
    (h𝒞obs : ∀ U ∈ 𝒞, U ⊆ M.observed)
    (x : ValuesOn M.observed (swigΩ Ω)) :
    MeasurableSet[
      MeasurableSpace.comap
        (fun ℓ : M.LatentValues =>
          fun u : S.biUnion (latentBlockIndex M) => ℓ u)
        inferInstance]
      (⋂ U ∈ S, {ℓ : M.LatentValues | ∀ v (hv : v ∈ U),
        M.localConsistent s x v (h𝒞obs U (hS ‹U ∈ S›) hv) ℓ}) := by
  classical
  refine measurableSet_comap_piFinset_of_depends
    (S := S.biUnion (latentBlockIndex M)) _ ?_
  intro ℓ ℓ' hagree
  constructor
  · intro hℓ
    rw [Set.mem_iInter] at hℓ
    rw [Set.mem_iInter]
    intro U
    have hℓU := hℓ U
    rw [Set.mem_iInter] at hℓU
    rw [Set.mem_iInter]
    intro hUS v hv
    have hlocal :
        M.localConsistent s x v (h𝒞obs U (hS hUS) hv) ℓ := by
      simpa [hS hUS] using hℓU hUS v hv
    exact (localConsistent_depends_only_on_latentBlock_of_mem M s x hv
      (h𝒞obs U (hS hUS) hv) ℓ ℓ' (by
        intro u hu
        have hmemBlock :
            (⟨u, (Finset.mem_filter.mp hu).1⟩ : {u // u ∈ M.unobserved})
              ∈ latentBlockIndex M U :=
          (mem_latentBlockIndex_iff M U _).mpr hu
        have hmem :
            (⟨u, (Finset.mem_filter.mp hu).1⟩ : {u // u ∈ M.unobserved})
              ∈ S.biUnion (latentBlockIndex M) := by
          rw [Finset.mem_biUnion]
          exact ⟨U, hUS, hmemBlock⟩
        have hcoord := hagree ⟨u, (Finset.mem_filter.mp hu).1⟩ hmem
        simpa using hcoord)).mp hlocal
  · intro hℓ'
    rw [Set.mem_iInter] at hℓ'
    rw [Set.mem_iInter]
    intro U
    have hℓ'U := hℓ' U
    rw [Set.mem_iInter] at hℓ'U
    rw [Set.mem_iInter]
    intro hUS v hv
    have hlocal :
        M.localConsistent s x v (h𝒞obs U (hS hUS) hv) ℓ' := by
      simpa [hS hUS] using hℓ'U hUS v hv
    exact (localConsistent_depends_only_on_latentBlock_of_mem M s x hv
      (h𝒞obs U (hS hUS) hv) ℓ' ℓ (by
        intro u hu
        have hmemBlock :
            (⟨u, (Finset.mem_filter.mp hu).1⟩ : {u // u ∈ M.unobserved})
              ∈ latentBlockIndex M U :=
          (mem_latentBlockIndex_iff M U _).mpr hu
        have hmem :
            (⟨u, (Finset.mem_filter.mp hu).1⟩ : {u // u ∈ M.unobserved})
              ∈ S.biUnion (latentBlockIndex M) := by
          rw [Finset.mem_biUnion]
          exact ⟨U, hUS, hmemBlock⟩
        have hcoord := hagree ⟨u, (Finset.mem_filter.mp hu).1⟩ hmem
        simpa using hcoord.symm)).mp hlocal

private lemma localConsistent_event_eq_component_biInter
    (M : Causalean.SCM N Ω) (s : M.FixedValues)
    (P : Finset (SWIGNode N)) (hP : M.ObsParentClosed P)
    (x : ValuesOn M.observed (swigΩ Ω)) :
    {ℓ : M.LatentValues | ∀ v (hv : v ∈ P),
      M.localConsistent s x v (hP.1 hv) ℓ} =
      ⋂ C ∈ M.toSWIGGraph.cComponentSet,
        {ℓ : M.LatentValues | ∀ v (hv : v ∈ C ∩ P),
          M.localConsistent s x v
            (hP.1 (Finset.mem_of_mem_inter_right hv)) ℓ} := by
  classical
  ext ℓ
  constructor
  · intro hℓ
    rw [Set.mem_iInter]
    intro C
    rw [Set.mem_iInter]
    intro _hC v hv
    exact hℓ v (Finset.mem_of_mem_inter_right hv)
  · intro hℓ v hvP
    rw [Set.mem_iInter] at hℓ
    have hC : M.toSWIGGraph.cComponentOf v ∈ M.toSWIGGraph.cComponentSet := by
      rw [SWIGGraph.cComponentSet, Finset.mem_image]
      exact ⟨v, hP.1 hvP, rfl⟩
    have hvC : v ∈ M.toSWIGGraph.cComponentOf v :=
      M.toSWIGGraph.mem_cComponentOf_self (hP.1 hvP)
    have hℓC := hℓ (M.toSWIGGraph.cComponentOf v)
    rw [Set.mem_iInter] at hℓC
    exact hℓC hC v
      (Finset.mem_inter.mpr ⟨hvC, hvP⟩)

private lemma localConsistent_event_eq_family_biInter
    (M : Causalean.SCM N Ω) (s : M.FixedValues)
    (𝒞 : Finset (Finset (SWIGNode N)))
    (h𝒞obs : ∀ U ∈ 𝒞, U ⊆ M.observed)
    (hSup : 𝒞.sup id ⊆ M.observed)
    (x : ValuesOn M.observed (swigΩ Ω)) :
    {ℓ : M.LatentValues | ∀ v (hv : v ∈ 𝒞.sup id),
      M.localConsistent s x v (hSup hv) ℓ} =
      ⋂ U ∈ 𝒞,
        if hU : U ∈ 𝒞 then
          {ℓ : M.LatentValues | ∀ v (hv : v ∈ U),
            M.localConsistent s x v (h𝒞obs U hU hv) ℓ}
        else Set.univ := by
  classical
  ext ℓ
  constructor
  · intro hℓ
    rw [Set.mem_iInter]
    intro U
    rw [Set.mem_iInter]
    intro hU
    simp [hU]
    intro v hv
    have hvSup : v ∈ 𝒞.sup id := by
      rw [Finset.mem_sup]
      exact ⟨U, hU, hv⟩
    convert hℓ v hvSup using 1
  · intro hℓ v hvSup
    rw [Set.mem_iInter] at hℓ
    rw [Finset.mem_sup] at hvSup
    rcases hvSup with ⟨U, hU, hvU⟩
    have hℓU := hℓ U
    rw [Set.mem_iInter] at hℓU
    have hUevent :
        ℓ ∈ {ℓ : M.LatentValues | ∀ v (hv : v ∈ U),
          M.localConsistent s x v (h𝒞obs U hU hv) ℓ} := by
      simpa [hU] using hℓU hU
    convert hUevent v hvU using 1

private lemma latentProduct_localConsistent_factorization
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (s : M.FixedValues)
    (P : Finset (SWIGNode N)) (hP : M.ObsParentClosed P)
    (x : ValuesOn M.observed (swigΩ Ω)) :
    M.latentProduct {ℓ | ∀ v (hv : v ∈ P),
      M.localConsistent s x v (hP.1 hv) ℓ} =
      ∏ C ∈ M.toSWIGGraph.cComponentSet,
        M.qLocalMass s (C ∩ P)
          (fun _ hv => hP.1 (Finset.mem_of_mem_inter_right hv)) x := by
  rw [localConsistent_event_eq_component_biInter M s P hP x]
  classical
  let E : Finset (SWIGNode N) → Set M.LatentValues := fun C =>
    {ℓ : M.LatentValues | ∀ v (hv : v ∈ C ∩ P),
      M.localConsistent s x v
        (hP.1 (Finset.mem_of_mem_inter_right hv)) ℓ}
  have hcoord :
      iIndepFun
        (fun u : {u // u ∈ M.unobserved} => fun ℓ : M.LatentValues => ℓ u)
        M.latentProduct := by
    haveI : ∀ u : {u // u ∈ M.unobserved},
        MeasureTheory.IsProbabilityMeasure (M.latentDist u) :=
      M.isProbability_latent
    unfold SCM.latentProduct
    exact ProbabilityTheory.iIndepFun_pi
      (X := fun _ : {u // u ∈ M.unobserved} => id)
      (fun _ => aemeasurable_id)
  have hfactor :
      ∀ S : Finset (Finset (SWIGNode N)),
        S ⊆ M.toSWIGGraph.cComponentSet →
          M.latentProduct (⋂ C ∈ S, E C) =
            ∏ C ∈ S, M.latentProduct (E C) := by
    intro S
    refine Finset.induction_on S ?base ?step
    · intro _hS
      simp [E]
    · intro C S hCnot ih hSinsert
      have hS : S ⊆ M.toSWIGGraph.cComponentSet := by
        intro D hD
        exact hSinsert (Finset.mem_insert_of_mem hD)
      have hC : C ∈ M.toSWIGGraph.cComponentSet :=
        hSinsert (Finset.mem_insert_self C S)
      have hdisj :
          Disjoint (S.biUnion (latentBlockIndex M)) (latentBlockIndex M C) :=
        latentBlockIndex_biUnion_disjoint M hS hC hCnot
      have hindep :
          IndepFun
            (fun ℓ : M.LatentValues =>
              fun u : S.biUnion (latentBlockIndex M) => ℓ u)
            (fun ℓ : M.LatentValues =>
              fun u : latentBlockIndex M C => ℓ u)
            M.latentProduct :=
        hcoord.indepFun_finset (S.biUnion (latentBlockIndex M))
          (latentBlockIndex M C) hdisj (fun u => measurable_pi_apply u)
      have hmeasS :
          MeasurableSet[
            MeasurableSpace.comap
              (fun ℓ : M.LatentValues =>
                fun u : S.biUnion (latentBlockIndex M) => ℓ u)
              inferInstance]
            (⋂ D ∈ S, E D) := by
        simpa [E] using
          localConsistent_biInter_event_measurable_comap_latentBlockIndex
            M s P hP x hS
      have hmeasC :
          MeasurableSet[
            MeasurableSpace.comap
              (fun ℓ : M.LatentValues =>
                fun u : latentBlockIndex M C => ℓ u)
              inferInstance]
            (E C) := by
        simpa [E] using
          localConsistent_event_measurable_comap_latentBlockIndex
            M s P hP x hC
      have hinter :=
        hindep.meas_inter (μ := M.latentProduct) hmeasS hmeasC
      calc
        M.latentProduct (⋂ D ∈ insert C S, E D)
            = M.latentProduct ((⋂ D ∈ S, E D) ∩ E C) := by
              congr 1
              ext ℓ
              simp [E, and_comm]
        _ = M.latentProduct (⋂ D ∈ S, E D) * M.latentProduct (E C) := by
              exact hinter
        _ = (∏ D ∈ S, M.latentProduct (E D)) * M.latentProduct (E C) := by
              rw [ih hS]
        _ = ∏ D ∈ insert C S, M.latentProduct (E D) := by
              rw [Finset.prod_insert hCnot]
              rw [mul_comm]
  have hfull := hfactor M.toSWIGGraph.cComponentSet (fun _ h => h)
  simpa [E, qLocalMass] using hfull

/-- Local q-mass over an abstract family factors when the ambient latent blocks
of the family are pairwise disjoint. -/
lemma qLocalMass_prod_of_latentBlock_disjoint
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (s : M.FixedValues)
    (𝒞 : Finset (Finset (SWIGNode N)))
    (h𝒞obs : ∀ U ∈ 𝒞, U ⊆ M.observed)
    (hblock :
      (↑𝒞 : Set (Finset (SWIGNode N))).Pairwise
        (fun U U' => Disjoint (M.latentBlock U) (M.latentBlock U')))
    (_hnode : (↑𝒞 : Set (Finset (SWIGNode N))).Pairwise
        (fun U U' => Disjoint U U'))
    (x : ValuesOn M.observed (swigΩ Ω)) :
    M.qLocalMass s (𝒞.sup id)
        (fun v hv => by
          rw [Finset.mem_sup] at hv
          rcases hv with ⟨U, hU, hvU⟩
          exact h𝒞obs U hU hvU) x =
      ∏ U ∈ 𝒞,
        if hU : U ∈ 𝒞 then M.qLocalMass s U (h𝒞obs U hU) x else 1 := by
  classical
  let hSup : 𝒞.sup id ⊆ M.observed := fun v hv => by
    rw [Finset.mem_sup] at hv
    rcases hv with ⟨U, hU, hvU⟩
    exact h𝒞obs U hU hvU
  let E : Finset (SWIGNode N) → Set M.LatentValues := fun U =>
    if hU : U ∈ 𝒞 then
      {ℓ : M.LatentValues | ∀ v (hv : v ∈ U),
        M.localConsistent s x v (h𝒞obs U hU hv) ℓ}
    else Set.univ
  have hevent :
      {ℓ : M.LatentValues | ∀ v (hv : v ∈ 𝒞.sup id),
        M.localConsistent s x v (hSup hv) ℓ} =
        ⋂ U ∈ 𝒞, E U := by
    simpa [E, hSup] using
      localConsistent_event_eq_family_biInter M s 𝒞 h𝒞obs hSup x
  have hcoord :
      iIndepFun
        (fun u : {u // u ∈ M.unobserved} => fun ℓ : M.LatentValues => ℓ u)
        M.latentProduct := by
    haveI : ∀ u : {u // u ∈ M.unobserved},
        MeasureTheory.IsProbabilityMeasure (M.latentDist u) :=
      M.isProbability_latent
    unfold SCM.latentProduct
    exact ProbabilityTheory.iIndepFun_pi
      (X := fun _ : {u // u ∈ M.unobserved} => id)
      (fun _ => aemeasurable_id)
  have hfactor :
      ∀ S : Finset (Finset (SWIGNode N)), S ⊆ 𝒞 →
        M.latentProduct (⋂ U ∈ S, E U) =
          ∏ U ∈ S, M.latentProduct (E U) := by
    intro S
    refine Finset.induction_on S ?base ?step
    · intro _hS
      simp [E]
    · intro U S hUnot ih hSinsert
      have hS : S ⊆ 𝒞 := by
        intro V hV
        exact hSinsert (Finset.mem_insert_of_mem hV)
      have hU : U ∈ 𝒞 := hSinsert (Finset.mem_insert_self U S)
      have hdisj :
          Disjoint (S.biUnion (latentBlockIndex M)) (latentBlockIndex M U) :=
        latentBlockIndex_biUnion_disjoint_of_pairwise M hS hU hUnot hblock
      have hindep :
          IndepFun
            (fun ℓ : M.LatentValues =>
              fun u : S.biUnion (latentBlockIndex M) => ℓ u)
            (fun ℓ : M.LatentValues =>
              fun u : latentBlockIndex M U => ℓ u)
            M.latentProduct :=
        hcoord.indepFun_finset (S.biUnion (latentBlockIndex M))
          (latentBlockIndex M U) hdisj (fun u => measurable_pi_apply u)
      have hmeasS :
          MeasurableSet[
            MeasurableSpace.comap
              (fun ℓ : M.LatentValues =>
                fun u : S.biUnion (latentBlockIndex M) => ℓ u)
              inferInstance]
            (⋂ V ∈ S, E V) := by
        have hbase :=
          localConsistent_biInter_event_measurable_comap_latentBlockIndex_of_family
            M s 𝒞 S hS h𝒞obs x
        convert hbase using 1
        ext ℓ
        simp only [Set.mem_iInter, Set.mem_setOf_eq]
        constructor
        · intro h V hVS
          have hEV := h V hVS
          simpa [E, hS hVS] using hEV
        · intro h V hVS
          have hEV := h V hVS
          simpa [E, hS hVS] using hEV
      have hmeasU :
          MeasurableSet[
            MeasurableSpace.comap
              (fun ℓ : M.LatentValues =>
                fun u : latentBlockIndex M U => ℓ u)
              inferInstance]
            (E U) := by
        simpa [E, hU] using
          localConsistent_event_measurable_comap_latentBlockIndex_of_family
            M s U (h𝒞obs U hU) x
      have hinter :=
        hindep.meas_inter (μ := M.latentProduct) hmeasS hmeasU
      calc
        M.latentProduct (⋂ V ∈ insert U S, E V)
            = M.latentProduct ((⋂ V ∈ S, E V) ∩ E U) := by
              congr 1
              ext ℓ
              simp [E, and_comm]
        _ = M.latentProduct (⋂ V ∈ S, E V) * M.latentProduct (E U) := by
              exact hinter
        _ = (∏ V ∈ S, M.latentProduct (E V)) * M.latentProduct (E U) := by
              rw [ih hS]
        _ = ∏ V ∈ insert U S, M.latentProduct (E V) := by
              rw [Finset.prod_insert hUnot]
              rw [mul_comm]
  have hfull := hfactor 𝒞 (fun _ h => h)
  unfold qLocalMass
  rw [hevent]
  rw [hfull]
  refine Finset.prod_congr rfl ?_
  intro U hU
  simp [E, hU]

set_option maxHeartbeats 800000 in
-- This proof repeats the latent-block independence argument with an extra
-- intersection parameter, which gives Lean a large dependent event expression.
/-- Local q-mass on a covered set factors over an abstract family after
intersecting each family member with the covered set. -/
lemma qLocalMass_prod_inter_of_latentBlock_disjoint
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (s : M.FixedValues)
    (P : Finset (SWIGNode N)) (hPobs : P ⊆ M.observed)
    (𝒞 : Finset (Finset (SWIGNode N)))
    (h𝒞obs : ∀ U ∈ 𝒞, U ⊆ M.observed)
    (hcover : P ⊆ 𝒞.sup id)
    (hblock :
      (↑𝒞 : Set (Finset (SWIGNode N))).Pairwise
        (fun U U' => Disjoint (M.latentBlock U) (M.latentBlock U')))
    (_hnode : (↑𝒞 : Set (Finset (SWIGNode N))).Pairwise
        (fun U U' => Disjoint U U'))
    (x : ValuesOn M.observed (swigΩ Ω)) :
    M.qLocalMass s P hPobs x =
      ∏ U ∈ 𝒞,
        if hU : U ∈ 𝒞 then
          M.qLocalMass s (U ∩ P)
            (fun _ hv => h𝒞obs U hU (Finset.mem_of_mem_inter_left hv)) x
        else 1 := by
  classical
  let E : Finset (SWIGNode N) → Set M.LatentValues := fun U =>
    if hU : U ∈ 𝒞 then
      {ℓ : M.LatentValues | ∀ v (hv : v ∈ U ∩ P),
        M.localConsistent s x v
          (h𝒞obs U hU (Finset.mem_of_mem_inter_left hv)) ℓ}
    else Set.univ
  have hevent :
      {ℓ : M.LatentValues | ∀ v (hv : v ∈ P),
        M.localConsistent s x v (hPobs hv) ℓ} =
        ⋂ U ∈ 𝒞, E U := by
    ext ℓ
    constructor
    · intro hℓ
      rw [Set.mem_iInter]
      intro U
      rw [Set.mem_iInter]
      intro hU
      simp [E, hU]
      intro v _hvU hvP
      exact hℓ v hvP
    · intro hℓ v hvP
      rw [Set.mem_iInter] at hℓ
      have hvSup : v ∈ 𝒞.sup id := hcover hvP
      rw [Finset.mem_sup] at hvSup
      rcases hvSup with ⟨U, hU, hvU⟩
      have hℓU := hℓ U
      rw [Set.mem_iInter] at hℓU
      have hUevent :
          ℓ ∈ {ℓ : M.LatentValues | ∀ v (hv : v ∈ U ∩ P),
            M.localConsistent s x v
              (h𝒞obs U hU (Finset.mem_of_mem_inter_left hv)) ℓ} := by
        simpa [E, hU] using hℓU hU
      have hvUP : v ∈ U ∩ P := Finset.mem_inter.mpr ⟨hvU, hvP⟩
      convert hUevent v hvUP using 1
  have hcoord :
      iIndepFun
        (fun u : {u // u ∈ M.unobserved} => fun ℓ : M.LatentValues => ℓ u)
        M.latentProduct := by
    haveI : ∀ u : {u // u ∈ M.unobserved},
        MeasureTheory.IsProbabilityMeasure (M.latentDist u) :=
      M.isProbability_latent
    unfold SCM.latentProduct
    exact ProbabilityTheory.iIndepFun_pi
      (X := fun _ : {u // u ∈ M.unobserved} => id)
      (fun _ => aemeasurable_id)
  have hfactor :
      ∀ S : Finset (Finset (SWIGNode N)), S ⊆ 𝒞 →
        M.latentProduct (⋂ U ∈ S, E U) =
          ∏ U ∈ S, M.latentProduct (E U) := by
    intro S
    refine Finset.induction_on S ?base ?step
    · intro _hS
      simp [E]
    · intro U S hUnot ih hSinsert
      have hS : S ⊆ 𝒞 := by
        intro V hV
        exact hSinsert (Finset.mem_insert_of_mem hV)
      have hU : U ∈ 𝒞 := hSinsert (Finset.mem_insert_self U S)
      have hdisj :
          Disjoint (S.biUnion (latentBlockIndex M)) (latentBlockIndex M U) :=
        latentBlockIndex_biUnion_disjoint_of_pairwise M hS hU hUnot hblock
      have hindep :
          IndepFun
            (fun ℓ : M.LatentValues =>
              fun u : S.biUnion (latentBlockIndex M) => ℓ u)
            (fun ℓ : M.LatentValues =>
              fun u : latentBlockIndex M U => ℓ u)
            M.latentProduct :=
        hcoord.indepFun_finset (S.biUnion (latentBlockIndex M))
          (latentBlockIndex M U) hdisj (fun u => measurable_pi_apply u)
      have hmeasS :
          MeasurableSet[
            MeasurableSpace.comap
              (fun ℓ : M.LatentValues =>
                fun u : S.biUnion (latentBlockIndex M) => ℓ u)
              inferInstance]
            (⋂ V ∈ S, E V) := by
        refine measurableSet_comap_piFinset_of_depends
          (S := S.biUnion (latentBlockIndex M)) _ ?_
        intro ℓ ℓ' hagree
        constructor
        · intro hℓ
          rw [Set.mem_iInter] at hℓ
          rw [Set.mem_iInter]
          intro V
          have hℓV := hℓ V
          rw [Set.mem_iInter] at hℓV
          rw [Set.mem_iInter]
          intro hVS
          have hV𝒞 : V ∈ 𝒞 := hS hVS
          simp [E, hV𝒞]
          intro v hvV hvP
          have hlocal :
              M.localConsistent s x v
                (h𝒞obs V hV𝒞 hvV) ℓ := by
            have hEV : ℓ ∈ E V := hℓV hVS
            have hEV' :
                ∀ v (hv : v ∈ V ∩ P),
                  M.localConsistent s x v
                    (h𝒞obs V hV𝒞 (Finset.mem_of_mem_inter_left hv)) ℓ := by
              simpa [E, hV𝒞] using hEV
            exact hEV' v (Finset.mem_inter.mpr ⟨hvV, hvP⟩)
          exact (localConsistent_depends_only_on_latentBlock_of_mem M s x
            hvV (h𝒞obs V hV𝒞 hvV) ℓ ℓ' (by
              intro u hu
              have hmemBlock :
                  (⟨u, (Finset.mem_filter.mp hu).1⟩ : {u // u ∈ M.unobserved})
                    ∈ latentBlockIndex M V :=
                (mem_latentBlockIndex_iff M V _).mpr hu
              have hmem :
                  (⟨u, (Finset.mem_filter.mp hu).1⟩ : {u // u ∈ M.unobserved})
                    ∈ S.biUnion (latentBlockIndex M) := by
                rw [Finset.mem_biUnion]
                exact ⟨V, hVS, hmemBlock⟩
              have hcoord := hagree ⟨u, (Finset.mem_filter.mp hu).1⟩ hmem
              simpa using hcoord)).mp hlocal
        · intro hℓ'
          rw [Set.mem_iInter] at hℓ'
          rw [Set.mem_iInter]
          intro V
          have hℓ'V := hℓ' V
          rw [Set.mem_iInter] at hℓ'V
          rw [Set.mem_iInter]
          intro hVS
          have hV𝒞 : V ∈ 𝒞 := hS hVS
          simp [E, hV𝒞]
          intro v hvV hvP
          have hlocal :
              M.localConsistent s x v
                (h𝒞obs V hV𝒞 hvV) ℓ' := by
            have hEV : ℓ' ∈ E V := hℓ'V hVS
            have hEV' :
                ∀ v (hv : v ∈ V ∩ P),
                  M.localConsistent s x v
                    (h𝒞obs V hV𝒞 (Finset.mem_of_mem_inter_left hv)) ℓ' := by
              simpa [E, hV𝒞] using hEV
            exact hEV' v (Finset.mem_inter.mpr ⟨hvV, hvP⟩)
          exact (localConsistent_depends_only_on_latentBlock_of_mem M s x
            hvV (h𝒞obs V hV𝒞 hvV) ℓ' ℓ (by
              intro u hu
              have hmemBlock :
                  (⟨u, (Finset.mem_filter.mp hu).1⟩ : {u // u ∈ M.unobserved})
                    ∈ latentBlockIndex M V :=
                (mem_latentBlockIndex_iff M V _).mpr hu
              have hmem :
                  (⟨u, (Finset.mem_filter.mp hu).1⟩ : {u // u ∈ M.unobserved})
                    ∈ S.biUnion (latentBlockIndex M) := by
                rw [Finset.mem_biUnion]
                exact ⟨V, hVS, hmemBlock⟩
              have hcoord := hagree ⟨u, (Finset.mem_filter.mp hu).1⟩ hmem
              simpa using hcoord.symm)).mp hlocal
      have hmeasU :
          MeasurableSet[
            MeasurableSpace.comap
              (fun ℓ : M.LatentValues =>
                fun u : latentBlockIndex M U => ℓ u)
              inferInstance]
            (E U) := by
        refine measurableSet_comap_piFinset_of_depends
          (S := latentBlockIndex M U) _ ?_
        intro ℓ ℓ' hagree
        constructor
        · intro hℓ
          simp [E, hU] at hℓ ⊢
          intro v hvU hvP
          have hlocal :
              M.localConsistent s x v
                (h𝒞obs U hU hvU) ℓ := hℓ v hvU hvP
          exact (localConsistent_depends_only_on_latentBlock_of_mem M s x
            hvU (h𝒞obs U hU hvU) ℓ ℓ' (by
              intro u hu
              have hmem :
                  (⟨u, (Finset.mem_filter.mp hu).1⟩ : {u // u ∈ M.unobserved})
                    ∈ latentBlockIndex M U :=
                (mem_latentBlockIndex_iff M U _).mpr hu
              have hcoord := hagree ⟨u, (Finset.mem_filter.mp hu).1⟩ hmem
              simpa using hcoord)).mp hlocal
        · intro hℓ'
          simp [E, hU] at hℓ' ⊢
          intro v hvU hvP
          have hlocal :
              M.localConsistent s x v
                (h𝒞obs U hU hvU) ℓ' := hℓ' v hvU hvP
          exact (localConsistent_depends_only_on_latentBlock_of_mem M s x
            hvU (h𝒞obs U hU hvU) ℓ' ℓ (by
              intro u hu
              have hmem :
                  (⟨u, (Finset.mem_filter.mp hu).1⟩ : {u // u ∈ M.unobserved})
                    ∈ latentBlockIndex M U :=
                (mem_latentBlockIndex_iff M U _).mpr hu
              have hcoord := hagree ⟨u, (Finset.mem_filter.mp hu).1⟩ hmem
              simpa using hcoord.symm)).mp hlocal
      have hinter :=
        hindep.meas_inter (μ := M.latentProduct) hmeasS hmeasU
      calc
        M.latentProduct (⋂ V ∈ insert U S, E V)
            = M.latentProduct ((⋂ V ∈ S, E V) ∩ E U) := by
              congr 1
              ext ℓ
              simp [E, and_comm]
        _ = M.latentProduct (⋂ V ∈ S, E V) * M.latentProduct (E U) := by
              exact hinter
        _ = (∏ V ∈ S, M.latentProduct (E V)) * M.latentProduct (E U) := by
              rw [ih hS]
        _ = ∏ V ∈ insert U S, M.latentProduct (E V) := by
              rw [Finset.prod_insert hUnot]
              rw [mul_comm]
  have hfull := hfactor 𝒞 (fun _ h => h)
  unfold qLocalMass
  rw [hevent]
  rw [hfull]
  refine Finset.prod_congr rfl ?_
  intro U hU
  simp [E, hU]

/-- The observed marginal atom mass factors as a product of local q-masses over
full c-components. -/
theorem obsKernel_marginal_singleton_eq_prod_qLocalMass
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (s : M.FixedValues)
    (P : Finset (SWIGNode N)) (hP : M.ObsParentClosed P)
    (x : ValuesOn M.observed (swigΩ Ω)) :
    ((M.obsKernel s).map (valuesProjection hP.1)) {valuesProjection hP.1 x}
      = ∏ C ∈ M.toSWIGGraph.cComponentSet,
          M.qLocalMass s (C ∩ P)
            (fun _ hv => hP.1 (Finset.mem_of_mem_inter_right hv)) x := by
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
  rw [hset]
  exact latentProduct_localConsistent_factorization M s P hP x

/-- Positive observational mass implies nonzero local q-mass. -/
lemma qLocalMass_pos_of_positiveObs
    (M : Causalean.SCM N Ω) (s : M.FixedValues)
    [MeasurableSingletonClass (ValuesOn M.observed (swigΩ Ω))]
    (hpos : ID.DiscreteID.PositiveMass (M.obsKernel s)) :
    ∀ T hT x, M.qLocalMass s T hT x ≠ 0 := by
  classical
  intro T hT x
  have hobs : M.observed ⊆ M.observed := fun ⦃_⦄ hv => hv
  have hclosed : M.ObsParentClosed M.observed := by
    refine ⟨hobs, ?_⟩
    intro _v _hv _w hw _hedge
    exact hw
  have hmass := obsKernel_marginal_singleton_eq_latentProduct_agree
    M s (P := M.observed) hobs x
  have hset :
      {ℓ : M.LatentValues | ∀ v : {v // v ∈ M.observed},
        M.evalMap s ℓ
            ⟨v.val, Finset.mem_union_left M.unobserved v.property⟩ =
          x ⟨v.val, v.property⟩}
        =
      {ℓ : M.LatentValues | ∀ v (hv : v ∈ M.observed),
        M.localConsistent s x v hv ℓ} := by
    ext ℓ
    constructor
    · intro hEval
      exact (M.evalMap_agree_iff_localConsistent s M.observed hclosed x ℓ).mp
        (fun v hv => hEval ⟨v, hv⟩)
    · intro hLocal v
      exact (M.evalMap_agree_iff_localConsistent s M.observed hclosed x ℓ).mpr
        hLocal v.val v.property
  rw [hset] at hmass
  have hproj_id :
      (valuesProjection (Ω := swigΩ Ω)
        hobs
        : ValuesOn M.observed (swigΩ Ω) → ValuesOn M.observed (swigΩ Ω)) = id := by
    funext ξ
    rfl
  rw [hproj_id, Measure.map_id] at hmass
  have hfull : M.qLocalMass s M.observed hobs x ≠ 0 := by
    have hx :
        (M.obsKernel s) ({x} : Set (ValuesOn M.observed (swigΩ Ω))) ≠ 0 := by
      simpa [ID.DiscreteID.singletonMass_apply] using hpos x
    simpa [qLocalMass] using (hmass ▸ hx)
  have hle :
      M.qLocalMass s M.observed hobs x ≤ M.qLocalMass s T hT x :=
    M.qLocalMass_anti s (T := T) (T' := M.observed) hT hT hobs x
  intro hzero
  exact hfull (le_antisymm (by simpa [hzero] using hle) (zero_le _))

end Causalean.SCM

namespace Causalean.SCM.ID

open scoped MeasureTheory ProbabilityTheory ENNReal BigOperators

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

/-- Positivity of observational kernels gives positivity for the do-model
ancestral marginal used by the ID density assembly. -/
lemma doObsKernelAncestralMarginal_positiveMass
    [∀ n, Nonempty (Ω n)]
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (Y : Finset (SWIGNode N))
    (hpos : ∀ s' : M.FixedValues, DiscreteID.PositiveMass (M.obsKernel s'))
    (hYX : ∀ d ∈ X, SWIGNode.random d ∉ Y)
    (sDo : (M.fixSet X hObs hFix).FixedValues) :
    DiscreteID.PositiveMass (doObsKernelAncestralMarginal M X hObs hFix Y sDo) := by
  classical
  let MX := M.fixSet X hObs hFix
  let D := fixObservedAncestralSet M X hObs hFix Y
  let A := fixAncestralSet M X hObs hFix Y
  have hDclosed : MX.ObsParentClosed D := by
    simpa [MX, D] using fixObservedAncestralSet_obsParent_closed M X hObs hFix Y
  intro xD
  let xFull : ValuesOn M.observed (swigΩ Ω) := fun v =>
    if hvD : v.val ∈ D then
      xD ⟨v.val, hvD⟩
    else
      match v.val with
      | SWIGNode.random d =>
          if hd : d ∈ X then
            sDo ⟨SWIGNode.fixed d,
              Finset.mem_union_right _
                (Finset.mem_image.mpr ⟨d, hd, rfl⟩)⟩
          else
            Classical.choice (inferInstance : Nonempty (swigΩ Ω (SWIGNode.random d)))
      | SWIGNode.fixed d =>
          Classical.choice (inferInstance : Nonempty (swigΩ Ω (SWIGNode.fixed d)))
  let xDo : ValuesOn MX.observed (swigΩ Ω) := fun v =>
    xFull ⟨v.val, by simp [MX, SCM.fixSet_observed]⟩
  have hprojD :
      valuesProjection hDclosed.1 xDo = xD := by
    ext v
    simp [valuesProjection, xDo, xFull, v.property]
  have hpin : ∀ d (hd : d ∈ X),
      xFull ⟨SWIGNode.random d, hObs d hd⟩ =
        sDo ⟨SWIGNode.fixed d,
          Finset.mem_union_right _
            (Finset.mem_image.mpr ⟨d, hd, rfl⟩)⟩ := by
    intro d hd
    have hnotD : SWIGNode.random d ∉ D := by
      intro hdD
      have hdA : SWIGNode.random d ∈ A := (Finset.mem_inter.mp hdD).1
      exact hYX d hd
        ((random_intervened_mem_fixAncestralSet_iff_mem_Y M X hObs hFix Y hd).mp hdA)
    simp [xFull, hnotD, hd]
  have hobsAgree : ∀ w (hw : w ∈ M.observed),
      xDo ⟨w, by simpa [MX, SCM.fixSet_observed] using hw⟩ = xFull ⟨w, hw⟩ := by
    intro w hw
    rfl
  have hq_ne :
      ∀ C ∈ MX.toSWIGGraph.cComponentSet,
        MX.qLocalMass sDo (C ∩ D)
            (fun _ hv => hDclosed.1 (Finset.mem_of_mem_inter_right hv)) xDo ≠ 0 := by
    intro C _hC
    have hsubsetM : C ∩ D ⊆ M.observed := by
      intro v hv
      have hvD : v ∈ D := Finset.mem_of_mem_inter_right hv
      exact Finset.inter_subset_right hvD
    have hqeq :
        MX.qLocalMass sDo (C ∩ D)
            (fun _ hv => hDclosed.1 (Finset.mem_of_mem_inter_right hv)) xDo =
          M.qLocalMass (M.fixSetProj X hObs hFix sDo) (C ∩ D) hsubsetM xFull := by
      unfold qLocalMass
      congr 1
      ext ℓ
      constructor
      · intro hLocal v hv
        have hvD : v ∈ D := Finset.mem_of_mem_inter_right hv
        have hnot : v ∉ X.image SWIGNode.random := by
          intro hvX
          rcases Finset.mem_image.mp hvX with ⟨d, hd, rfl⟩
          have hdA : SWIGNode.random d ∈ A := (Finset.mem_inter.mp hvD).1
          exact hYX d hd
            ((random_intervened_mem_fixAncestralSet_iff_mem_Y M X hObs hFix Y hd).mp hdA)
        exact (localConsistent_fixSet_iff M X hObs hFix sDo
          (M.fixSetProj X hObs hFix sDo) xDo xFull v
          ((fun _ hv => hDclosed.1 (Finset.mem_of_mem_inter_right hv)) v hv)
          (hsubsetM hv) hnot hobsAgree hpin rfl ℓ).mp (hLocal v hv)
      · intro hLocal v hv
        have hvD : v ∈ D := Finset.mem_of_mem_inter_right hv
        have hnot : v ∉ X.image SWIGNode.random := by
          intro hvX
          rcases Finset.mem_image.mp hvX with ⟨d, hd, rfl⟩
          have hdA : SWIGNode.random d ∈ A := (Finset.mem_inter.mp hvD).1
          exact hYX d hd
            ((random_intervened_mem_fixAncestralSet_iff_mem_Y M X hObs hFix Y hd).mp hdA)
        exact (localConsistent_fixSet_iff M X hObs hFix sDo
          (M.fixSetProj X hObs hFix sDo) xDo xFull v
          ((fun _ hv => hDclosed.1 (Finset.mem_of_mem_inter_right hv)) v hv)
          (hsubsetM hv) hnot hobsAgree hpin rfl ℓ).mpr (hLocal v hv)
    rw [hqeq]
    exact M.qLocalMass_pos_of_positiveObs (M.fixSetProj X hObs hFix sDo)
      (hpos (M.fixSetProj X hObs hFix sDo)) (C ∩ D) hsubsetM xFull
  have hmass := MX.obsKernel_marginal_singleton_eq_prod_qLocalMass sDo D hDclosed xDo
  unfold doObsKernelAncestralMarginal DiscreteID.singletonMass
  rw [ProbabilityTheory.Kernel.map_apply _ (measurable_valuesProjection _)]
  rw [← hprojD]
  change ((MX.obsKernel sDo).map (valuesProjection hDclosed.1))
      ({valuesProjection hDclosed.1 xDo} : Set (ValuesOn D (swigΩ Ω))) ≠ 0
  rw [hmass]
  exact Finset.prod_ne_zero_iff.mpr hq_ne

/-- Pure ENNReal telescope for products of selected adjacent ratios. -/
lemma prod_filter_div_telescope
    (a : ℕ → ENNReal) (m : ℕ) (T : Finset ℕ)
    (hT : T ⊆ Finset.range m)
    (hne : ∀ i ≤ m, a i ≠ 0) (hfin : ∀ i ≤ m, a i ≠ ⊤)
    (hconst : ∀ i < m, i ∉ T → a (i + 1) = a i) :
    ∏ i ∈ T, a (i + 1) / a i = a m / a 0 := by
  classical
  have hrange_all :
      ∀ n : ℕ, (∀ i ≤ n, a i ≠ 0) → (∀ i ≤ n, a i ≠ ⊤) →
        ∏ i ∈ Finset.range n, a (i + 1) / a i = a n / a 0 := by
    intro n hnne hnfin
    induction n with
    | zero =>
        simp [ENNReal.div_self (hnne 0 le_rfl) (hnfin 0 le_rfl)]
    | succ m ih =>
        rw [Finset.prod_range_succ]
        have hih :
            ∏ i ∈ Finset.range m, a (i + 1) / a i = a m / a 0 :=
          ih (fun i hi => hnne i (Nat.le_trans hi (Nat.le_succ m)))
            (fun i hi => hnfin i (Nat.le_trans hi (Nat.le_succ m)))
        rw [hih]
        rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
        rw [show a m * (a 0)⁻¹ * (a (m + 1) * (a m)⁻¹)
              = a (m + 1) * (a m * (a m)⁻¹) * (a 0)⁻¹ by ac_rfl]
        rw [ENNReal.mul_inv_cancel (hnne m (Nat.le_succ m)) (hnfin m (Nat.le_succ m))]
        simp
  have hrange :
      ∏ i ∈ Finset.range m, a (i + 1) / a i = a m / a 0 :=
    hrange_all m hne hfin
  have hsubset :
      ∏ i ∈ T, a (i + 1) / a i =
        ∏ i ∈ Finset.range m, a (i + 1) / a i := by
    exact Finset.prod_subset hT (by
      intro i hiRange hiT
      have hi_lt : i < m := Finset.mem_range.mp hiRange
      rw [hconst i hi_lt hiT]
      exact ENNReal.div_self (hne i (Nat.le_of_lt hi_lt))
        (hfin i (Nat.le_of_lt hi_lt)))
  rw [hsubset, hrange]

end Causalean.SCM.ID
