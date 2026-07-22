/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Q-factor Identity (Tian's Lemma), Intervention Target Simplification,
  and District Identification

Formalizes the central identification lemmas underlying the Tian–Pearl
ID algorithm.  Statements are framed against `obsKernel`, `fixSet`,
`induce`, and the `qFactor` constructor from `CComponentFactor.lean`.

* **Proposition 2.19 (Q-factor identity / Tian's lemma).**  For an
  ancestrally-closed `R ⊆ V` and a c-component `T ∈ C(G_R)`, the
  c-factor `qFactor (M.induce R) T` agrees a.e. with the conditional
  `T | qFactorParents T` extracted from the interventional kernel
  `(M.fixSet (R \ T)).obsKernel`.  The marginal fixing identity is proved
  as a helper; the conditional disintegration step is isolated in
  `q_factor_identity`.

* **Proposition (`fact4`, intervention target simplification).**  Doing
  `Dn` then `Yn` agrees with doing `Dn ∪ Yn` directly, as a structural
  equivalence of gSCMs (`SCM.Equiv`).  Composes `swigInterventionSet_insert_equiv`
  along `Yn.toList`.

* **Corollary (district identification).**  The special case `R =
  M.observed` of `q_factor_identity`.

## References

* Basic Concepts.tex, §4.1 (proof sketches embedded in the do-calculus
  chain).  The "Prop 2.19" numbering follows the project's internal
  enumeration; the corresponding result in the literature is Tian's
  Lemma 1 (Tian 2002, "Studies in causal reasoning and learning").
* `ID Alg in 10 mins.tex` — potential-outcome restatement (`fact4`).
-/

import Causalean.SCM.Model.SCM
import Causalean.SCM.Model.Kernel
import Causalean.SCM.Model.InterventionSet
import Causalean.SCM.Model.Induced
import Causalean.SCM.Do.Rule3
import Causalean.SCM.Do.SemiGraphoid
import Causalean.SCM.ID.Identifiable
import Causalean.SCM.ID.GraphicalThms.InducedSubgraph
import Causalean.SCM.ID.GraphicalThms.CComponentFactor

/-! # Q-Factor Identity

This file proves the structural identities behind district-based identification
in the Tian-Pearl style. The main results are the marginal fixing helper
`q_factor_marginal_fixing`, Tian's conditional `q_factor_identity`, the
intervention-order simplification `intervention_target_simp`, and the full-SCM
district specialization `district_id`. These relate c-component factors, induced
subgraphs, and post-fixing kernels so later ID soundness proofs can reuse a
common theorem frame. -/

namespace Causalean.SCM.ID

open scoped MeasureTheory ProbabilityTheory

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

-- ============================================================
-- Proposition 2.19: Q-factor Identity (Tian's Lemma)
-- ============================================================

/-- The proven marginal fixing helper behind Tian's fixing lemma.

    For an ancestrally-closed `R ⊆ M.observed`, a c-component
    `T ⊆ R` of the induced sub-SCM `M.induce R`, and a name set
    `Wn` such that `Wn.image .random = R \ T`, Rule 3 and induced-SCM
    marginal compatibility imply that the `T`-marginal of the
    post-intervention kernel `(M.fixSet Wn _ _).obsKernel` agrees with
    the `T`-marginal of the induced sub-SCM at the projected fixed
    slice.

    This is the measure-level fixing identity used below the full conditional
    `qFactor` statement. -/
def QFactorMarginalFixingConclusion
    (M : Causalean.SCM N Ω)
    (R : Finset (SWIGNode N))
    (T : Finset (SWIGNode N))
    (Wn : Finset N) : Prop :=
  ∀ (hR_ac : M.isAncestrallyClosedSCM R)
    (hT_induce : T ⊆ (M.induce R hR_ac).observed)
    (_hWn_eq : Wn.image SWIGNode.random = R \ T)
    (_hWn_obs : ∀ D ∈ Wn, SWIGNode.random D ∈ M.observed)
    (_hWn_fixed : ∀ D ∈ Wn, SWIGNode.fixed D ∉ M.fixed)
    (_hNoDesc : ∀ z ∈ Wn, ∀ v ∈ T,
      ¬ (M.fixSet Wn _hWn_obs _hWn_fixed).dag.isAncestor (SWIGNode.fixed z) v)
    (s' : (M.fixSet Wn _hWn_obs _hWn_fixed).FixedValues),
    ((M.fixSet Wn _hWn_obs _hWn_fixed).obsKernel s').map
        (valuesProjection
          ((fixSet_observed M Wn _hWn_obs _hWn_fixed).symm ▸
            (show T ⊆ M.observed from
              fun v hv =>
                (Finset.mem_inter.mp
                  (show v ∈ R ∩ M.observed from hT_induce hv)).2)))
      =
    ((M.induce R hR_ac).obsKernel
        (valuesProjection (Finset.filter_subset _ _)
          (M.fixSetProj Wn _hWn_obs _hWn_fixed s'))).map
        (valuesProjection hT_induce)

/-- The conditional conclusion of Tian's fixing lemma (Prop 2.19).

    The left side is the `qFactor` of the induced sub-SCM on `R`, i.e. the
    conditional law of `T` given the induced graph's `qFactorParents T`.  The
    right side is the analogous conditional law extracted from the post-fixing
    kernel `(M.fixSet Wn).obsKernel`, using the same parent coordinates.  Equality
    is stated a.e. under the induced parent marginal, which is the natural
    uniqueness level for `Kernel.condKernel`. -/
def QFactorIdentityConclusion
    (M : Causalean.SCM N Ω)
    (R : Finset (SWIGNode N))
    (T : Finset (SWIGNode N))
    (Wn : Finset N) : Prop :=
  ∀ (hR_ac : M.isAncestrallyClosedSCM R)
    (hT_induce : T ⊆ (M.induce R hR_ac).observed)
    (_hWn_eq : Wn.image SWIGNode.random = R \ T)
    (_hWn_obs : ∀ D ∈ Wn, SWIGNode.random D ∈ M.observed)
    (_hWn_fixed : ∀ D ∈ Wn, SWIGNode.fixed D ∉ M.fixed)
    (_hNoDesc : ∀ z ∈ Wn, ∀ v ∈
      T ∪ (M.induce R hR_ac).toSWIGGraph.qFactorParents T,
      ¬ (M.fixSet Wn _hWn_obs _hWn_fixed).dag.isAncestor (SWIGNode.fixed z) v),
    let MI : Causalean.SCM N Ω := M.induce R hR_ac
    let Mdo : Causalean.SCM N Ω := M.fixSet Wn _hWn_obs _hWn_fixed
    let P : Finset (SWIGNode N) := MI.toSWIGGraph.qFactorParents T
    ∀ [StandardBorelSpace (ValuesOn T (swigΩ Ω))]
      [Nonempty (ValuesOn T (swigΩ Ω))]
      [∀ sI : MI.FixedValues, MeasureTheory.IsFiniteMeasure (MI.obsKernel sI)]
      [∀ sD : Mdo.FixedValues, MeasureTheory.IsFiniteMeasure (Mdo.obsKernel sD)]
      [MeasurableSpace.CountableOrCountablyGenerated
        MI.FixedValues (ValuesOn P (swigΩ Ω))]
      [MeasurableSpace.CountableOrCountablyGenerated
        Mdo.FixedValues (ValuesOn P (swigΩ Ω))]
      (s' : Mdo.FixedValues),
      let sInduce : MI.FixedValues :=
        valuesProjection (Finset.filter_subset _ _)
          (M.fixSetProj Wn _hWn_obs _hWn_fixed s')
      ∀ᵐ c ∂((MI.obsKernel sInduce).map
          (valuesProjection (MI.toSWIGGraph.qFactorParents_subset_observed T))),
        (MI.qFactor T hT_induce sInduce) c =
          (((Mdo.obsCondKernel T P
            (show T ⊆ Mdo.observed from by
              intro v hv
              have hvM : v ∈ M.observed := by
                exact (Finset.mem_inter.mp
                  (show v ∈ R ∩ M.observed from hT_induce hv)).2
              simpa [Mdo, fixSet_observed] using hvM)
            (show P ⊆ Mdo.observed from by
              intro v hv
              have hvMI : v ∈ MI.observed :=
                MI.toSWIGGraph.qFactorParents_subset_observed T hv
              have hvM : v ∈ M.observed := by
                exact (Finset.mem_inter.mp
                  (show v ∈ R ∩ M.observed from hvMI)).2
              simpa [Mdo, fixSet_observed] using hvM)).comap
                (fun c => (s', c))
                (Measurable.prodMk measurable_const measurable_id)) c)

/-- **Marginal fixing form of Tian's Q-factor identity.**

    This is the proven measure-level helper: the `T`-marginal of the
    intervention fixing `R \ T` agrees with the `T`-marginal of the induced
    sub-SCM on `R`. -/
theorem q_factor_marginal_fixing
    (M : Causalean.SCM N Ω)
    (R : Finset (SWIGNode N))
    (T : Finset (SWIGNode N))
    (Wn : Finset N) :
    QFactorMarginalFixingConclusion M R T Wn := by
  classical
  intro hR_ac hT_induce _hWn_eq hWn_obs hWn_fixed hNoDesc s'
  let sTilde : M.FixedValues := M.fixSetProj Wn hWn_obs hWn_fixed s'
  let MI : Causalean.SCM N Ω := M.induce R hR_ac
  have hT_base : T ⊆ M.observed := by
    intro v hv
    exact (Finset.mem_inter.mp
      (show v ∈ R ∩ M.observed from hT_induce hv)).2
  have hMI_obs_base : MI.observed ⊆ M.observed := by
    exact Finset.inter_subset_right
  have hRule3 :
      ((M.fixSet Wn hWn_obs hWn_fixed).obsKernel s').map
          (valuesProjection
            ((fixSet_observed M Wn hWn_obs hWn_fixed).symm ▸ hT_base))
        =
      (M.obsKernel sTilde).map (valuesProjection hT_base) := by
    simpa [sTilde] using
      condDistrib_intervention_ancestral_eq
        M Wn hWn_obs hWn_fixed T hT_base hNoDesc s'
  have hInduced :
      MI.obsKernel
          (valuesProjection (Finset.filter_subset _ _) sTilde)
        =
      (M.obsKernel sTilde).map
          (valuesProjection hMI_obs_base) := by
    simpa [MI] using
      induce_marginal_compat M R hR_ac sTilde
  rw [hRule3, hInduced]
  rw [MeasureTheory.Measure.map_map
    (measurable_valuesProjection hT_induce)
    (measurable_valuesProjection hMI_obs_base)]
  rw [← valuesProjection_comp hT_induce hMI_obs_base hT_base]

/-- Equal pair laws give equal conditional-kernel slices a.e.

    This is the measure-theoretic uniqueness step used by `q_factor_identity`:
    once the pushforward laws of `(CC, Y)` agree, the `obsCondKernel` slices
    agree under the first marginal. -/
theorem obsCondKernel_slice_ae_eq_of_pairMeasure_eq
    (M₁ M₂ : Causalean.SCM N Ω)
    (Y CC : Finset (SWIGNode N))
    (hY₁ : Y ⊆ M₁.observed) (hCC₁ : CC ⊆ M₁.observed)
    (hY₂ : Y ⊆ M₂.observed) (hCC₂ : CC ⊆ M₂.observed)
    [StandardBorelSpace (ValuesOn Y (swigΩ Ω))]
    [Nonempty (ValuesOn Y (swigΩ Ω))]
    [∀ s : M₁.FixedValues, MeasureTheory.IsFiniteMeasure (M₁.obsKernel s)]
    [∀ s : M₂.FixedValues, MeasureTheory.IsFiniteMeasure (M₂.obsKernel s)]
    [MeasurableSpace.CountableOrCountablyGenerated
      M₁.FixedValues (ValuesOn CC (swigΩ Ω))]
    [MeasurableSpace.CountableOrCountablyGenerated
      M₂.FixedValues (ValuesOn CC (swigΩ Ω))]
    (s₁ : M₁.FixedValues) (s₂ : M₂.FixedValues)
    (hPair :
      M₁.obsCondPairKernel Y CC hY₁ hCC₁ s₁ =
        M₂.obsCondPairKernel Y CC hY₂ hCC₂ s₂) :
    (fun c => (M₁.obsCondKernel Y CC hY₁ hCC₁).sectR s₁ c)
      =ᵐ[(M₁.obsKernel s₁).map (valuesProjection hCC₁)]
        fun c => (M₂.obsCondKernel Y CC hY₂ hCC₂).sectR s₂ c := by
  classical
  let μ₁ : MeasureTheory.Measure (ValuesOn CC (swigΩ Ω)) :=
    (M₁.obsKernel s₁).map (valuesProjection hCC₁)
  let μ₂ : MeasureTheory.Measure (ValuesOn CC (swigΩ Ω)) :=
    (M₂.obsKernel s₂).map (valuesProjection hCC₂)
  let κ₁ : ProbabilityTheory.Kernel
      (ValuesOn CC (swigΩ Ω)) (ValuesOn Y (swigΩ Ω)) :=
    (M₁.obsCondKernel Y CC hY₁ hCC₁).sectR s₁
  let κ₂ : ProbabilityTheory.Kernel
      (ValuesOn CC (swigΩ Ω)) (ValuesOn Y (swigΩ Ω)) :=
    (M₂.obsCondKernel Y CC hY₂ hCC₂).sectR s₂
  haveI : ProbabilityTheory.IsMarkovKernel
      (M₁.obsCondKernel Y CC hY₁ hCC₁) := by
    unfold SCM.obsCondKernel
    infer_instance
  haveI : ProbabilityTheory.IsMarkovKernel
      (M₂.obsCondKernel Y CC hY₂ hCC₂) := by
    unfold SCM.obsCondKernel
    infer_instance
  haveI : ProbabilityTheory.IsMarkovKernel κ₁ := by
    dsimp [κ₁]
    infer_instance
  haveI : ProbabilityTheory.IsMarkovKernel κ₂ := by
    dsimp [κ₂]
    infer_instance
  have h₁ :
      M₁.obsCondPairKernel Y CC hY₁ hCC₁ s₁ = μ₁ ⊗ₘ κ₁ := by
    simpa [μ₁, κ₁] using
      SCM.obsCondPairKernel_apply_eq_compProd M₁ Y CC hY₁ hCC₁ s₁
  have h₂ :
      M₂.obsCondPairKernel Y CC hY₂ hCC₂ s₂ = μ₂ ⊗ₘ κ₂ := by
    simpa [μ₂, κ₂] using
      SCM.obsCondPairKernel_apply_eq_compProd M₂ Y CC hY₂ hCC₂ s₂
  have hComp : μ₁ ⊗ₘ κ₁ = μ₂ ⊗ₘ κ₂ := by
    rw [← h₁, ← h₂]
    exact hPair
  have hμ : μ₁ = μ₂ := by
    have hfst := congrArg MeasureTheory.Measure.fst hComp
    simpa [MeasureTheory.Measure.fst_compProd] using hfst
  have hComp' : μ₁ ⊗ₘ κ₁ = μ₁ ⊗ₘ κ₂ := by
    simpa [hμ] using hComp
  simpa [μ₁, κ₁, κ₂] using
    ProbabilityTheory.Kernel.ae_eq_of_compProd_eq hComp'

/-- **Proposition 2.19 (Q-factor identity / Tian's lemma).**

    For ancestrally-closed `R` and c-component `T ∈ C(G_R)`, the
    structurally-defined c-factor on `T` equals a.e. the `T | qFactorParents T`
    conditional extracted from the intervention fixing `R \ T`.  See
    `QFactorIdentityConclusion` for the precise hypothesis frame.

    Proof sketch (Tian 2002, Lemma 1):
    1. By `ancestralFactorization`, the joint law in `M.induce R`
       factors topologically through ancestors of each variable.
    2. Group factors by c-component: factors involving `T` collect into
       `qFactor (M.induce R) T` by definition.
    3. The interventional kernel `(M.fixSet Wn _ _).obsKernel` agrees
       with the c-factor evaluated at the matching parent values
       because (a) intervening on `R \ T` fixes the parents of `T` to
       the same values used in the c-factor, and (b) by Rule 3 (no
       interventional descendant of `T`-non-parents), the
       interventional kernel is independent of the rest. -/
theorem q_factor_identity
    (M : Causalean.SCM N Ω)
    (R : Finset (SWIGNode N))
    (T : Finset (SWIGNode N))
    (Wn : Finset N) :
    QFactorIdentityConclusion M R T Wn := by
  classical
  intro hR_ac hT_induce hWn_eq hWn_obs hWn_fixed hNoDesc
  dsimp only
  intro _ _ _ _ _ _ s'
  -- The conditional-kernel uniqueness argument first proves the joint identity on
  -- `T ∪ qFactorParents T` by combining the marginal helper with Rule 3 at that
  -- larger target, then applies `Kernel.disintegrate`/`condKernel` uniqueness to
  -- identify the two conditional kernels a.e. under the common parent marginal.
  have hMarginal :
      QFactorMarginalFixingConclusion M R T Wn :=
    q_factor_marginal_fixing M R T Wn
  have _hT_marginal :=
    hMarginal hR_ac hT_induce hWn_eq hWn_obs hWn_fixed
      (by
        intro z hz v hv
        exact hNoDesc z hz v (Finset.mem_union_left _ hv))
      s'
  let MI : Causalean.SCM N Ω := M.induce R hR_ac
  let Mdo : Causalean.SCM N Ω := M.fixSet Wn hWn_obs hWn_fixed
  let P : Finset (SWIGNode N) := MI.toSWIGGraph.qFactorParents T
  let sInduce : MI.FixedValues :=
    valuesProjection (Finset.filter_subset _ _)
      (M.fixSetProj Wn hWn_obs hWn_fixed s')
  have hP_induce : P ⊆ MI.observed := by
    simpa [P, MI] using
      (MI.toSWIGGraph.qFactorParents_subset_observed T)
  have hT_base : T ⊆ M.observed := by
    intro v hv
    exact (Finset.mem_inter.mp
      (show v ∈ R ∩ M.observed from hT_induce hv)).2
  have hP_base : P ⊆ M.observed := by
    intro v hv
    have hvMI : v ∈ MI.observed := hP_induce hv
    exact (Finset.mem_inter.mp
      (show v ∈ R ∩ M.observed from hvMI)).2
  have hT_do : T ⊆ Mdo.observed := by
    simpa [Mdo, fixSet_observed] using hT_base
  have hP_do : P ⊆ Mdo.observed := by
    simpa [Mdo, fixSet_observed] using hP_base
  let U : Finset (SWIGNode N) := T ∪ P
  have hU_induce : U ⊆ MI.observed := by
    intro v hv
    rcases Finset.mem_union.mp hv with hvT | hvP
    · exact hT_induce hvT
    · exact hP_induce hvP
  have hU_base : U ⊆ M.observed := by
    intro v hv
    rcases Finset.mem_union.mp hv with hvT | hvP
    · exact hT_base hvT
    · exact hP_base hvP
  have hU_do : U ⊆ Mdo.observed := by
    simpa [Mdo, fixSet_observed] using hU_base
  have hMI_obs_base : MI.observed ⊆ M.observed := by
    exact Finset.inter_subset_right
  have hRule3U :
      (Mdo.obsKernel s').map (valuesProjection hU_do)
        =
      (M.obsKernel (M.fixSetProj Wn hWn_obs hWn_fixed s')).map
        (valuesProjection hU_base) := by
    simpa [Mdo, U] using
      condDistrib_intervention_ancestral_eq
        M Wn hWn_obs hWn_fixed U hU_base
        (by
          intro z hz v hv
          exact hNoDesc z hz v (by simpa [U, P, MI] using hv))
        s'
  have hInduced :
      MI.obsKernel sInduce =
        (M.obsKernel (M.fixSetProj Wn hWn_obs hWn_fixed s')).map
          (valuesProjection hMI_obs_base) := by
    simpa [MI, sInduce] using
      induce_marginal_compat M R hR_ac
        (M.fixSetProj Wn hWn_obs hWn_fixed s')
  have hJointU :
      (Mdo.obsKernel s').map (valuesProjection hU_do)
        =
      (MI.obsKernel sInduce).map (valuesProjection hU_induce) := by
    rw [hRule3U, hInduced]
    rw [MeasureTheory.Measure.map_map
      (measurable_valuesProjection hU_induce)
      (measurable_valuesProjection hMI_obs_base)]
    rw [← valuesProjection_comp hU_induce hMI_obs_base hU_base]
  have hP_U : P ⊆ U := by
    intro v hv
    exact Finset.mem_union_right T hv
  have hT_U : T ⊆ U := by
    intro v hv
    exact Finset.mem_union_left P hv
  let pairU : ValuesOn U (swigΩ Ω) →
      ValuesOn P (swigΩ Ω) × ValuesOn T (swigΩ Ω) :=
    fun ω => (valuesProjection hP_U ω, valuesProjection hT_U ω)
  have hpairU_meas : Measurable pairU := by
    exact (measurable_valuesProjection hP_U).prodMk
      (measurable_valuesProjection hT_U)
  have hPair_do_comp :
      pairU ∘ valuesProjection hU_do =
        (fun ω : Mdo.ObservedValues =>
          (valuesProjection hP_do ω, valuesProjection hT_do ω)) := by
    funext ω
    apply Prod.ext
    · exact congrFun (valuesProjection_comp hP_U hU_do hP_do).symm ω
    · exact congrFun (valuesProjection_comp hT_U hU_do hT_do).symm ω
  have hPair_induce_comp :
      pairU ∘ valuesProjection hU_induce =
        (fun ω : MI.ObservedValues =>
          (valuesProjection hP_induce ω, valuesProjection hT_induce ω)) := by
    funext ω
    apply Prod.ext
    · exact congrFun (valuesProjection_comp hP_U hU_induce hP_induce).symm ω
    · exact congrFun (valuesProjection_comp hT_U hU_induce hT_induce).symm ω
  have hPairMeasure :
      MI.obsCondPairKernel T P hT_induce hP_induce sInduce =
        Mdo.obsCondPairKernel T P hT_do hP_do s' := by
    unfold SCM.obsCondPairKernel
    rw [ProbabilityTheory.Kernel.map_apply _
        ((measurable_valuesProjection hP_induce).prodMk
          (measurable_valuesProjection hT_induce))]
    rw [ProbabilityTheory.Kernel.map_apply _
        ((measurable_valuesProjection hP_do).prodMk
          (measurable_valuesProjection hT_do))]
    rw [← hPair_induce_comp, ← hPair_do_comp]
    rw [← MeasureTheory.Measure.map_map hpairU_meas
      (measurable_valuesProjection hU_induce)]
    rw [← MeasureTheory.Measure.map_map hpairU_meas
      (measurable_valuesProjection hU_do)]
    exact congrArg (MeasureTheory.Measure.map pairU) hJointU.symm
  have hAE :=
    obsCondKernel_slice_ae_eq_of_pairMeasure_eq
      MI Mdo T P hT_induce hP_induce hT_do hP_do
      sInduce s' hPairMeasure
  simpa [MI, Mdo, P, sInduce, SCM.qFactor, ProbabilityTheory.Kernel.sectR]
    using hAE

-- ============================================================
-- Intervention target simplification (fact4)
-- ============================================================

/-- The conclusion of `fact4` (intervention target simplification),
    stated as a structural equivalence of gSCMs.

    Tex (`ID Alg in 10 mins.tex` §3): intervening on `Dn` followed by
    `Yn` equals intervening on `Dn ∪ Yn` directly, in the sense that
    the two SCMs differ only by the order of `fixSet` operations.  Up to
    `SCM.Equiv` (`SCM.lean`), the two constructions agree.

    The hypothesis frame ensures the iterated `fixSet` is well-formed:
    `Dn` consists of observed-random non-fixed targets in `M`; `Yn`
    consists of observed-random non-fixed targets in `M.fixSet Dn`. -/
def InterventionTargetSimpConclusion
    (M : Causalean.SCM N Ω)
    (Dn Yn : Finset N)
    (_T : Finset (SWIGNode N)) : Prop :=
  ∀ (hD_obs : ∀ D ∈ Dn, SWIGNode.random D ∈ M.observed)
    (hD_fixed : ∀ D ∈ Dn, SWIGNode.fixed D ∉ M.fixed)
    (hY_obs : ∀ D ∈ Yn,
      SWIGNode.random D ∈ (M.fixSet Dn hD_obs hD_fixed).observed)
    (hY_fixed : ∀ D ∈ Yn,
      SWIGNode.fixed D ∉ (M.fixSet Dn hD_obs hD_fixed).fixed)
    (hUnion_obs : ∀ D ∈ Dn ∪ Yn, SWIGNode.random D ∈ M.observed)
    (hUnion_fixed : ∀ D ∈ Dn ∪ Yn, SWIGNode.fixed D ∉ M.fixed)
    (_hDY_disjoint : Disjoint Dn Yn),
    SCM.Equiv
      ((M.fixSet Dn hD_obs hD_fixed).fixSet Yn hY_obs hY_fixed)
      (M.fixSet (Dn ∪ Yn) hUnion_obs hUnion_fixed)

/-- **Proposition (`fact4` — intervention target simplification).**

    Up to structural equivalence (`SCM.Equiv`), `(M.fixSet Dn).fixSet Yn`
    and `M.fixSet (Dn ∪ Yn)` are the same gSCM. -/
theorem intervention_target_simp
    (M : Causalean.SCM N Ω)
    (Dn Yn : Finset N)
    (T : Finset (SWIGNode N)) :
    InterventionTargetSimpConclusion M Dn Yn T := by
  classical
  refine Finset.induction_on Yn ?_ ?_
  · intro hD_obs hD_fixed hY_obs hY_fixed hUnion_obs hUnion_fixed _hDY_disjoint
    have hEmpty :
        SCM.Equiv
          ((M.fixSet Dn hD_obs hD_fixed).fixSet ∅ hY_obs hY_fixed)
          (M.fixSet Dn hD_obs hD_fixed) :=
      fixSet_empty_equiv (M.fixSet Dn hD_obs hD_fixed) hY_obs hY_fixed
    have hRhs :
        SCM.Equiv
          (M.fixSet Dn hD_obs hD_fixed)
          (M.fixSet (Dn ∪ ∅) hUnion_obs hUnion_fixed) := by
      simpa [Finset.union_empty] using
        fixSet_equiv_congr (SCM.Equiv.refl M) Dn
          hD_obs hD_fixed
          (fun D hD => hUnion_obs D (Finset.mem_union_left _ hD))
          (fun D hD => hUnion_fixed D (Finset.mem_union_left _ hD))
    exact SCM.Equiv.trans hEmpty hRhs
  · intro y Ys hyYs ih hD_obs hD_fixed hY_obs hY_fixed hUnion_obs hUnion_fixed
      hDY_disjoint
    let M₀ : Causalean.SCM N Ω := M.fixSet Dn hD_obs hD_fixed
    have hYs_obs : ∀ D ∈ Ys, SWIGNode.random D ∈ M₀.observed := by
      intro D hD
      exact hY_obs D (Finset.mem_insert_of_mem hD)
    have hYs_fixed : ∀ D ∈ Ys, SWIGNode.fixed D ∉ M₀.fixed := by
      intro D hD
      exact hY_fixed D (Finset.mem_insert_of_mem hD)
    have hUnionYs_obs : ∀ D ∈ Dn ∪ Ys, SWIGNode.random D ∈ M.observed := by
      intro D hD
      exact hUnion_obs D
        (by
          rcases Finset.mem_union.mp hD with hD | hD
          · exact Finset.mem_union_left _ hD
          · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem hD))
    have hUnionYs_fixed : ∀ D ∈ Dn ∪ Ys, SWIGNode.fixed D ∉ M.fixed := by
      intro D hD
      exact hUnion_fixed D
        (by
          rcases Finset.mem_union.mp hD with hD | hD
          · exact Finset.mem_union_left _ hD
          · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem hD))
    have hDYs_disjoint : Disjoint Dn Ys := by
      exact hDY_disjoint.mono_right (by intro D hD; exact Finset.mem_insert_of_mem hD)
    have hyDn : y ∉ Dn := by
      intro hyD
      have hyMeet : y ∈ Dn ∩ insert y Ys :=
        Finset.mem_inter.mpr ⟨hyD, Finset.mem_insert_self y Ys⟩
      have hyBot : y ∈ (⊥ : Finset N) := hDY_disjoint.le_bot hyMeet
      simp at hyBot
    have hIH :
        SCM.Equiv
          (M₀.fixSet Ys hYs_obs hYs_fixed)
          (M.fixSet (Dn ∪ Ys) hUnionYs_obs hUnionYs_fixed) :=
      ih hD_obs hD_fixed hYs_obs hYs_fixed
        hUnionYs_obs hUnionYs_fixed hDYs_disjoint
    have hy_single_obs₀ : ∀ D ∈ ({y} : Finset N),
        SWIGNode.random D ∈ (M₀.fixSet Ys hYs_obs hYs_fixed).observed := by
      intro D hD
      have hDy : D = y := by simpa using hD
      rw [hDy]
      simpa [M₀, fixSet_observed] using hY_obs y (Finset.mem_insert_self y Ys)
    have hy_single_fixed₀ : ∀ D ∈ ({y} : Finset N),
        SWIGNode.fixed D ∉ (M₀.fixSet Ys hYs_obs hYs_fixed).fixed := by
      intro D hD hmem
      have hDy : D = y := by simpa using hD
      rw [hDy] at hmem
      rw [fixSet_fixed] at hmem
      rcases Finset.mem_union.mp hmem with hM | hImg
      · exact hY_fixed y (Finset.mem_insert_self y Ys) hM
      · rcases Finset.mem_image.mp hImg with ⟨z, hz, hzy⟩
        have hzy' : z = y := SWIGNode.fixed.inj hzy
        exact hyYs (by simpa [hzy'] using hz)
    have hStepL :
        SCM.Equiv
          (M₀.fixSet (insert y Ys) hY_obs hY_fixed)
          ((M₀.fixSet Ys hYs_obs hYs_fixed).fixSet
            ({y} : Finset N) hy_single_obs₀ hy_single_fixed₀) :=
      (swigInterventionSet_insert_equiv M₀ Ys y hyYs hYs_obs hYs_fixed
        hy_single_obs₀ hy_single_fixed₀ hY_obs hY_fixed).symm
    have hy_single_obs₁ : ∀ D ∈ ({y} : Finset N),
        SWIGNode.random D ∈
          (M.fixSet (Dn ∪ Ys) hUnionYs_obs hUnionYs_fixed).observed := by
      intro D hD
      have hDy : D = y := by simpa using hD
      rw [hDy]
      simpa [fixSet_observed] using
        hUnion_obs y (Finset.mem_union_right _ (Finset.mem_insert_self y Ys))
    have hy_single_fixed₁ : ∀ D ∈ ({y} : Finset N),
        SWIGNode.fixed D ∉
          (M.fixSet (Dn ∪ Ys) hUnionYs_obs hUnionYs_fixed).fixed := by
      intro D hD hmem
      have hDy : D = y := by simpa using hD
      rw [hDy] at hmem
      rw [fixSet_fixed] at hmem
      rcases Finset.mem_union.mp hmem with hM | hImg
      · exact hUnion_fixed y
          (Finset.mem_union_right _ (Finset.mem_insert_self y Ys)) hM
      · rcases Finset.mem_image.mp hImg with ⟨z, hz, hzy⟩
        have hzy' : z = y := SWIGNode.fixed.inj hzy
        rcases Finset.mem_union.mp hz with hyD | hyY
        · exact hyDn (by simpa [hzy'] using hyD)
        · exact hyYs (by simpa [hzy'] using hyY)
    have hStepMid :
        SCM.Equiv
          ((M₀.fixSet Ys hYs_obs hYs_fixed).fixSet
            ({y} : Finset N) hy_single_obs₀ hy_single_fixed₀)
          ((M.fixSet (Dn ∪ Ys) hUnionYs_obs hUnionYs_fixed).fixSet
            ({y} : Finset N) hy_single_obs₁ hy_single_fixed₁) :=
      fixSet_equiv_congr hIH ({y} : Finset N)
        hy_single_obs₀ hy_single_fixed₀ hy_single_obs₁ hy_single_fixed₁
    have hInsertUnion_obs : ∀ D ∈ insert y (Dn ∪ Ys),
        SWIGNode.random D ∈ M.observed := by
      intro D hD
      rcases Finset.mem_insert.mp hD with hEq | hD
      · rw [hEq]
        exact hUnion_obs y
          (Finset.mem_union_right _ (Finset.mem_insert_self y Ys))
      · exact hUnion_obs D
          (by
            rcases Finset.mem_union.mp hD with hD | hD
            · exact Finset.mem_union_left _ hD
            · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem hD))
    have hInsertUnion_fixed : ∀ D ∈ insert y (Dn ∪ Ys),
        SWIGNode.fixed D ∉ M.fixed := by
      intro D hD
      rcases Finset.mem_insert.mp hD with hEq | hD
      · rw [hEq]
        exact hUnion_fixed y
          (Finset.mem_union_right _ (Finset.mem_insert_self y Ys))
      · exact hUnion_fixed D
          (by
            rcases Finset.mem_union.mp hD with hD | hD
            · exact Finset.mem_union_left _ hD
            · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem hD))
    have hStepR :
        SCM.Equiv
          ((M.fixSet (Dn ∪ Ys) hUnionYs_obs hUnionYs_fixed).fixSet
            ({y} : Finset N) hy_single_obs₁ hy_single_fixed₁)
          (M.fixSet (insert y (Dn ∪ Ys))
            hInsertUnion_obs hInsertUnion_fixed) :=
      swigInterventionSet_insert_equiv M (Dn ∪ Ys) y
        (by
          intro hyUnion
          rcases Finset.mem_union.mp hyUnion with hyD | hyY
          · exact hyDn hyD
          · exact hyYs hyY)
        hUnionYs_obs hUnionYs_fixed
        hy_single_obs₁ hy_single_fixed₁
        hInsertUnion_obs hInsertUnion_fixed
    have hAll := SCM.Equiv.trans hStepL (SCM.Equiv.trans hStepMid hStepR)
    simpa [M₀, Finset.insert_union, Finset.union_insert, Finset.union_assoc,
      Finset.union_comm, Finset.union_left_comm] using hAll

-- ============================================================
-- Corollary: District identification
-- ============================================================

/-- The conclusion of district identification: for `T ∈ C(G)`, the c-factor
    `Q[T]` of the full SCM equals a.e. the matching do-side conditional after
    fixing `V \ T`.  Special case `R = M.observed` of
    `QFactorIdentityConclusion`. -/
def DistrictIdConclusion
    (M : Causalean.SCM N Ω) (T : Finset (SWIGNode N))
    (Wn : Finset N) : Prop :=
  QFactorIdentityConclusion M M.observed T Wn

/-- **Corollary (District identification).**

    The c-factor of every C-component `T` of the full SCM is equal a.e. to the
    matching do-side conditional obtained by intervening on `V \ T`.
    Specialized from `q_factor_identity` at `R := M.observed`. -/
theorem district_id
    (M : Causalean.SCM N Ω)
    (T : Finset (SWIGNode N))
    (Wn : Finset N) :
    DistrictIdConclusion M T Wn :=
  q_factor_identity M M.observed T Wn

end Causalean.SCM.ID
