/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.SCM.ID.GraphicalThms.IDSoundDiscrete
import Causalean.SCM.ID.GraphicalThms.DoGFormulaRec

/-! # Soundness of the full (recursive) Tian–Shpitser ID algorithm

`id_sound` (in `GraphicalThms.IDAlgorithm`) proves soundness for the *no-fixing*
certificate `idSucceeds`, where every post-intervention ancestral district is
already a full c-component of the original graph.  This file lifts soundness to
the **full recursive certificate** `idSucceedsRec`: each district need only be
*recursively reachable* (`CFactorReachableRec`) from its containing district via
Tian's IDENTIFY fixing sequence.

Since `idSucceeds → idSucceedsRec` (`idSucceeds_toRec`), `id_sound_rec` subsumes
`id_sound`, and `id_sound_rec_discrete` subsumes the frozen `id_sound_discrete`.

## Proof architecture for `id_sound_rec`

The assembly mirrors `id_sound`: the do-law `Y`-marginal factorizes over the
c-components of the post-intervention ancestral graph `H`, and it suffices to
show each district factor `tianDistrictDensity H D (do-law marginal) ref S` is a
functional of the observational kernel.  The ONLY change from `id_sound` is the
per-district recovery step (`id_sound` uses
`doAncestralDistrictDensity_recovered_from_obs`, which needs `S` to be a full
c-component).  The recursive version is:

* **M4a (per-step Lemma 12).**  For `W` ancestrally closed inside a district `T`,
  the `W`-marginal of the `Q[T]`-density equals the `Q[W]`-density.  At the
  measure level this is `q_factor_marginal_fixing` applied inside
  `M_T := M.fixSet (observed ∖ T)`; transport to densities via the
  DoLawMarginal / FiniteReference bridges used by `id_sound`'s base recovery.
* **M4b (recursive recovery).**  By induction on the `CFactorReachableRec C S`
  derivation: the base case (`inducedAncestral G C S = S`) is a marginalization
  of the *full-district* obs-side factor `cComponentDensityFactor ref C` (whose
  recovery is the existing `doAncestralDistrictDensity_recovered_from_obs` at the
  containing full c-component `C`); each `step` composes one M4a fixing step.  The
  recovered value is a functional of `obsKernel`, so equal observational kernels
  give equal district factors — exactly as in `id_sound`'s
  `cComponentDensityFactor_heq_of_obsKernel_heq` step.
* **M4c (assembly).**  Feed the recursive per-district equality into the same
  `Finset.prod` induction as `id_sound`.

Everything downstream of the per-district recovery is verbatim `id_sound`.
-/

namespace Causalean.SCM.ID

open Causalean.SCM Causalean.SCM.ID.DiscreteID
open scoped MeasureTheory ProbabilityTheory ENNReal BigOperators

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

-- Match the finite-reference ID API in `IDAlgorithm.lean`: these statements keep
-- `Fintype` assumptions even when Lean can elaborate a particular wrapper
-- without using them syntactically.
set_option linter.unusedFintypeInType false

/-- Observed-set form of `SCM.marginalizeOn`, used only to expose that the
recursive mass functional is independent of the rest of the SCM record. -/
noncomputable def marginalizeOnObserved [∀ n, Fintype (Ω n)]
    (O W : Finset (SWIGNode N)) (hW : W ⊆ O)
    (q : ValuesOn O (swigΩ Ω) → ENNReal) :
    ValuesOn O (swigΩ Ω) → ENNReal :=
  fun x => ∑ y : ValuesOn W (swigΩ Ω), q (overrideOn hW x y)

/-- Observed-set form of `SCM.extractDistrict`. -/
noncomputable def extractDistrictObserved [∀ n, Fintype (Ω n)]
    (O : Finset (SWIGNode N)) (G' : SWIGGraph N)
    (A C' : Finset (SWIGNode N)) (hA : A ⊆ O)
    (q : ValuesOn O (swigΩ Ω) → ENNReal) :
    ValuesOn O (swigΩ Ω) → ENNReal :=
  fun x =>
    ∏ i ∈ Finset.univ.filter (fun i : Fin A.card => (G'.nodesAt A i).val ∈ C'),
      marginalizeOnObserved O (A \ G'.prefixIn A (i.val + 1))
          (fun _ hv => hA ((Finset.mem_sdiff.mp hv).1)) q x /
        marginalizeOnObserved O (A \ G'.prefixIn A i.val)
          (fun _ hv => hA ((Finset.mem_sdiff.mp hv).1)) q x

/-- Observed-set form of `SCM.identifyMassRec`. -/
noncomputable def identifyMassRecObserved [∀ n, Fintype (Ω n)]
    (O : Finset (SWIGNode N)) (G : SWIGGraph N) :
    (T C : Finset (SWIGNode N)) → (hT : T ⊆ O) →
      (q : ValuesOn O (swigΩ Ω) → ENNReal) →
        ValuesOn O (swigΩ Ω) → ENNReal
  | T, C, hT, q =>
    let A := inducedAncestral G T C
    let hA : A ⊆ O := fun _ hv =>
      hT (inducedAncestral_subset_left G T C hv)
    if _hAC : A = C then
      marginalizeOnObserved O (T \ C)
        (fun _ hv => hT ((Finset.mem_sdiff.mp hv).1)) q
    else if _hAT : A = T then
      q
    else
      let C₁ := containingCComponent (G.induce A) C
      let hC₁ : C₁ ⊆ O := fun _ hv =>
        hT (inducedAncestral_subset_left G T C
          (containingCComponent_induce_subset G A C hv))
      identifyMassRecObserved O G C₁ C hC₁
        (extractDistrictObserved O (G.induce A) A C₁ hA
          (marginalizeOnObserved O (T \ A)
            (fun _ hv => hT ((Finset.mem_sdiff.mp hv).1)) q))
termination_by T _ _ _ => T.card
decreasing_by
  classical
  have hAsubT : A ⊆ T := inducedAncestral_subset_left G T C
  have hAssubT : A ⊂ T := Finset.ssubset_iff_subset_ne.mpr ⟨hAsubT, _hAT⟩
  have hC₁subA : C₁ ⊆ A := containingCComponent_induce_subset G A C
  exact Nat.lt_of_le_of_lt (Finset.card_le_card hC₁subA)
    (Finset.card_lt_card hAssubT)

@[simp] lemma marginalizeOnObserved_eq_marginalizeOn [∀ n, Fintype (Ω n)]
    (M : Causalean.SCM N Ω) (W : Finset (SWIGNode N)) (hW : W ⊆ M.observed)
    (q : ValuesOn M.observed (swigΩ Ω) → ENNReal) :
    marginalizeOnObserved M.observed W hW q = M.marginalizeOn W hW q := by
  rfl

@[simp] lemma extractDistrictObserved_eq_extractDistrict [∀ n, Fintype (Ω n)]
    (M : Causalean.SCM N Ω) (G' : SWIGGraph N)
    (A C' : Finset (SWIGNode N)) (hA : A ⊆ M.observed)
    (q : ValuesOn M.observed (swigΩ Ω) → ENNReal) :
    extractDistrictObserved M.observed G' A C' hA q =
      M.extractDistrict G' A C' hA q := by
  funext x
  unfold extractDistrictObserved SCM.extractDistrict
  rfl

lemma identifyMassRecObserved_eq_identifyMassRec [∀ n, Fintype (Ω n)]
    (M : Causalean.SCM N Ω) (G : SWIGGraph N)
    (T C : Finset (SWIGNode N)) (hT : T ⊆ M.observed)
    (q : ValuesOn M.observed (swigΩ Ω) → ENNReal) :
    identifyMassRecObserved M.observed G T C hT q =
      M.identifyMassRec G T C hT q := by
  classical
  let P : ℕ → Prop := fun n =>
    ∀ (T C : Finset (SWIGNode N)) (hT : T ⊆ M.observed)
      (q : ValuesOn M.observed (swigΩ Ω) → ENNReal),
      T.card = n →
        identifyMassRecObserved M.observed G T C hT q =
          M.identifyMassRec G T C hT q
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
    intro T C hT q hcard
    rw [identifyMassRecObserved, SCM.identifyMassRec]
    by_cases hAC : inducedAncestral G T C = C
    · simp [hAC]
    · by_cases hAT : inducedAncestral G T C = T
      · simp [hAT]
      · simp only [hAC, hAT, marginalizeOnObserved_eq_marginalizeOn,
          extractDistrictObserved_eq_extractDistrict, dite_eq_ite]
        let A := inducedAncestral G T C
        let C₁ := containingCComponent (G.induce A) C
        have hAsubT : A ⊆ T := inducedAncestral_subset_left G T C
        have hAssubT : A ⊂ T := Finset.ssubset_iff_subset_ne.mpr ⟨hAsubT, hAT⟩
        have hC₁subA : C₁ ⊆ A := containingCComponent_induce_subset G A C
        have hlt : C₁.card < n := by
          rw [← hcard]
          exact Nat.lt_of_le_of_lt (Finset.card_le_card hC₁subA)
            (Finset.card_lt_card hAssubT)
        exact ih C₁.card hlt C₁ C _ _ rfl
  exact hP T.card T C hT q rfl

/-- Obs-side recursive recovered factor for a target district.

The seed is the observational mass form of the full containing c-component
factor `Q[C]`: the c-component density factor multiplied by the `C` reference
atom.  The mass-level IDENTIFY recursion then recovers the target mass `Q[S]`,
and the final division converts it back to a density with respect to the `S`
reference atom. -/
@[irreducible] noncomputable def recoveredFactorRec
    (M : Causalean.SCM N Ω) (ref : ReferenceMeasures Ω) (s : M.FixedValues)
    (C S : Finset (SWIGNode N))
    [hfin : ∀ n, Fintype (Ω n)]
    [∀ s' : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.obsKernel s')]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      StandardBorelSpace
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < M.observed.card),
      Nonempty
        (ValuesOn ({(M.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ k : ℕ,
      MeasurableSpace.CountableOrCountablyGenerated
        M.FixedValues (ValuesOn (M.prefixNodes k) (swigΩ Ω))] :
    ValuesOn M.observed (swigΩ Ω) → ENNReal :=
  fun x =>
    if hC : C ⊆ M.observed then
      if hSobs : S ⊆ M.observed then
        M.identifyMassRec M.toSWIGGraph C S hC
          (fun x' =>
            (∏ i ∈ Finset.univ.filter
                (fun i : Fin M.observed.card => (M.observedAt i).val ∈ C),
              M.obsStepCondDensity ref s i x') *
            jointRef ref C
              ({valuesProjection hC x'} : Set (ValuesOn C (swigΩ Ω)))) x /
          jointRef ref S
            ({valuesProjection hSobs x} : Set (ValuesOn S (swigΩ Ω)))
      else 0
    else 0

/-- Equal observational kernels transport the recursive recovered factor. -/
lemma recoveredFactorRec_heq_of_obsKernel_heq
    (M₁ M₂ : Causalean.SCM N Ω) (ref : ReferenceMeasures Ω)
    (C S : Finset (SWIGNode N))
    (hsg : M₁.toSWIGGraph = M₂.toSWIGGraph)
    (hobs : HEq M₁.obsKernel M₂.obsKernel)
    [hfin : ∀ n, Fintype (Ω n)]
    [∀ s' : M₁.FixedValues, MeasureTheory.IsFiniteMeasure (M₁.obsKernel s')]
    [∀ (k : ℕ) (hk : k < M₁.observed.card),
      StandardBorelSpace
        (ValuesOn ({(M₁.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < M₁.observed.card),
      Nonempty
        (ValuesOn ({(M₁.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ k : ℕ,
      MeasurableSpace.CountableOrCountablyGenerated
        M₁.FixedValues (ValuesOn (M₁.prefixNodes k) (swigΩ Ω))]
    [∀ s' : M₂.FixedValues, MeasureTheory.IsFiniteMeasure (M₂.obsKernel s')]
    [∀ (k : ℕ) (hk : k < M₂.observed.card),
      StandardBorelSpace
        (ValuesOn ({(M₂.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ (k : ℕ) (hk : k < M₂.observed.card),
      Nonempty
        (ValuesOn ({(M₂.observedAt ⟨k, hk⟩).val} : Finset (SWIGNode N)) (swigΩ Ω))]
    [∀ k : ℕ,
      MeasurableSpace.CountableOrCountablyGenerated
        M₂.FixedValues (ValuesOn (M₂.prefixNodes k) (swigΩ Ω))] :
    HEq (fun s => recoveredFactorRec M₁ ref s C S)
      (fun s => recoveredFactorRec M₂ ref s C S) := by
  obtain ⟨⟨dag₁, fixed₁, observed₁, unobserved₁,
           fio₁, oi₁, od₁, oou₁, foi₁, fou₁, aic₁, dc₁, foff₁, aco₁⟩,
         eT₁, iota₁, sf₁, mf₁, lD₁, pL₁⟩ := M₁
  obtain ⟨⟨dag₂, fixed₂, observed₂, unobserved₂,
           fio₂, oi₂, od₂, oou₂, foi₂, fou₂, aic₂, dc₂, foff₂, aco₂⟩,
         eT₂, iota₂, sf₂, mf₂, lD₂, pL₂⟩ := M₂
  cases hsg
  have hfio : fio₂ = fio₁ := Subsingleton.elim _ _
  subst fio₂
  have hoi : oi₂ = oi₁ := Subsingleton.elim _ _
  subst oi₂
  have hod : od₂ = od₁ := Subsingleton.elim _ _
  subst od₂
  have hoou : oou₂ = oou₁ := Subsingleton.elim _ _
  subst oou₂
  have hfoi : foi₂ = foi₁ := Subsingleton.elim _ _
  subst foi₂
  have hfou : fou₂ = fou₁ := Subsingleton.elim _ _
  subst fou₂
  have haic : aic₂ = aic₁ := Subsingleton.elim _ _
  subst aic₂
  have hdc : dc₂ = dc₁ := Subsingleton.elim _ _
  subst dc₂
  have hfoff : foff₂ = foff₁ := Subsingleton.elim _ _
  subst foff₂
  have haco : aco₂ = aco₁ := Subsingleton.elim _ _
  subst aco₂
  let M₁' : Causalean.SCM N Ω :=
    { dag := dag₁, fixed := fixed₁, observed := observed₁,
      unobserved := unobserved₁, fixed_is_fixed := fio₁,
      observed_is_random := oi₁, unobserved_is_random := od₁,
      obs_unobs_disjoint := oou₁, dag_edges_classified := foi₁,
      fixed_image_in_observed := fou₁, fixed_are_roots := aic₁,
      unobs_are_roots := dc₁, fixed_outside_fixed_isolated := foff₁,
      all_children_in_observed := aco₁, edgeTypes := eT₁,
      iota_valueSpace := iota₁, structFun := sf₁,
      structFun_measurable := mf₁, latentDist := lD₁,
      isProbability_latent := pL₁ }
  let M₂' : Causalean.SCM N Ω :=
    { dag := dag₁, fixed := fixed₁, observed := observed₁,
      unobserved := unobserved₁, fixed_is_fixed := fio₁,
      observed_is_random := oi₁, unobserved_is_random := od₁,
      obs_unobs_disjoint := oou₁, dag_edges_classified := foi₁,
      fixed_image_in_observed := fou₁, fixed_are_roots := aic₁,
      unobs_are_roots := dc₁, fixed_outside_fixed_isolated := foff₁,
      all_children_in_observed := aco₁, edgeTypes := eT₂,
      iota_valueSpace := iota₂, structFun := sf₂,
      structFun_measurable := mf₂, latentDist := lD₂,
      isProbability_latent := pL₂ }
  have hk : _ = _ := eq_of_heq hobs
  apply heq_of_eq
  funext s x
  unfold recoveredFactorRec
  by_cases hC : C ⊆ observed₁
  · by_cases hSobs : S ⊆ observed₁
    · rw [dif_pos hC, dif_pos hSobs, dif_pos hC, dif_pos hSobs]
      change
        M₁'.identifyMassRec M₁'.toSWIGGraph C S hC _ x / _ =
          M₂'.identifyMassRec M₂'.toSWIGGraph C S hC _ x / _
      rw [← identifyMassRecObserved_eq_identifyMassRec M₁' M₁'.toSWIGGraph C S hC]
      rw [← identifyMassRecObserved_eq_identifyMassRec M₂' M₂'.toSWIGGraph C S hC]
      have hseed :
          (fun x' =>
            (∏ i ∈ Finset.univ.filter
                (fun i : Fin observed₁.card =>
                  (M₁'.observedAt i).val ∈ C),
              M₁'.obsStepCondDensity ref s i x') *
            jointRef ref C
              ({valuesProjection hC x'} : Set (ValuesOn C (swigΩ Ω)))) =
          (fun x' =>
            (∏ i ∈ Finset.univ.filter
                (fun i : Fin observed₁.card =>
                  (M₂'.observedAt i).val ∈ C),
              M₂'.obsStepCondDensity ref s i x') *
            jointRef ref C
              ({valuesProjection hC x'} : Set (ValuesOn C (swigΩ Ω)))) := by
        funext x'
        congr 1
        apply Finset.prod_congr rfl
        intro i _hi
        unfold obsStepCondDensity obsStepCondKernel SCM.obsCondKernel SCM.obsCondPairKernel
        repeat' congr
      rw [hseed]
    · rw [dif_pos hC, dif_neg hSobs, dif_pos hC, dif_neg hSobs]
  · rw [dif_neg hC, dif_neg hC]

/-- Recursive district-density recovery from the observational kernel.

This is the density-level IDENTIFY step needed to replace the no-fixing
`doAncestralDistrictDensity_recovered_from_obs` recovery. -/
theorem doAncestralDistrictDensity_recovered_from_obs_rec
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
    (S C : Finset (SWIGNode N))
    (hS : S ∈ fixTruncCComponentSet M X hObs hFix Y)
    (hReach : CFactorReachableRec M.toSWIGGraph C S)
    (hCmem : C ∈ M.toSWIGGraph.cComponentSet)
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
          recoveredFactorRec M ref
            (M.fixSetProj X hObs hFix sDo) C S (extend xD) := by
  classical
  let MX := M.fixSet X hObs hFix
  let D := fixObservedAncestralSet M X hObs hFix Y
  let H := MX.toSWIGGraph.induce (fixAncestralSet M X hObs hFix Y)
  let sObs := M.fixSetProj X hObs hFix sDo
  have hCobs : C ⊆ M.observed := by
    simpa using M.toSWIGGraph.cComponentSet_subset_observed C hCmem
  have hSobs : S ⊆ M.observed := fun _ hv => hCobs (hReach.target_subset hv)
  have hSD : S ⊆ D := by
    have hScomp : S ∈ H.cComponentSet := by
      change S ∈
        ((M.fixSet X hObs hFix).toSWIGGraph.induce
          (fixAncestralSet M X hObs hFix Y)).cComponentSet
      simpa [fixTruncCComponentSet] using hS
    have hSHobs : S ⊆ H.observed := H.cComponentSet_subset_observed S hScomp
    simpa [H, D, fixObservedAncestralSet] using hSHobs
  have hSX : ∀ n ∈ X, SWIGNode.random n ∉ S := by
    intro n hn hnS
    have hnD : SWIGNode.random n ∈ D := hSD hnS
    have hnA : SWIGNode.random n ∈ fixAncestralSet M X hObs hFix Y := by
      simpa [D, fixObservedAncestralSet] using (Finset.mem_inter.mp hnD).1
    exact hYX n hn
      ((random_intervened_mem_fixAncestralSet_iff_mem_Y M X hObs hFix Y hn).mp hnA)
  filter_upwards with xD
  have hproj :
      valuesProjection hSobs (extend xD) =
        valuesProjection hSD xD := by
    ext v
    have h := congrFun (hExtend xD) ⟨v.val, hSD v.property⟩
    simpa [valuesProjection] using h
  have hdo :
      MX.qLocalMass sDo S (by simpa [MX, SCM.fixSet_observed] using hSobs)
          (extend xD) =
        M.qLocalMass sObs S hSobs (extend xD) := by
    simpa [MX, sObs] using
      qLocalMass_fixSet_invariant M X hObs hFix sDo S hSobs hSX
        (extend xD) (fun D hD => hExtendX xD D hD)
  have hseed :
      (fun x' =>
        (∏ i ∈ Finset.univ.filter
            (fun i : Fin M.observed.card => (M.observedAt i).val ∈ C),
          M.obsStepCondDensity ref sObs i x') *
        jointRef ref C
          ({valuesProjection hCobs x'} : Set (ValuesOn C (swigΩ Ω)))) =
        M.qLocalMass sObs C hCobs := by
    funext x'
    have hprod :
        (∏ i ∈ Finset.univ.filter
            (fun i : Fin M.observed.card => (M.observedAt i).val ∈ C),
          M.obsStepCondDensity ref sObs i x') =
          M.cComponentDensityFactor ref sObs C x' := by
      unfold cComponentDensityFactor
      refine Finset.prod_congr ?_ ?_
      · ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact
          (mem_cComponent_iff_cComponentOf_eq M.toSWIGGraph
            (M.observedAt i).property hCmem)
      · intro i _hi
        rfl
    let atom :=
      jointRef ref C ({valuesProjection hCobs x'} :
        Set (ValuesOn C (swigΩ Ω)))
    have hatom0 : atom ≠ 0 := by
      exact jointRef_singleton_ne_zero ref href C (valuesProjection hCobs x')
    have hatomtop : atom ≠ (⊤ : ENNReal) := by
      exact ne_of_lt (MeasureTheory.measure_lt_top (jointRef ref C)
        ({valuesProjection hCobs x'} : Set (ValuesOn C (swigΩ Ω))))
    have hmech :
        M.mechCFactor ref C hCobs sObs x' =
          M.qLocalMass sObs C hCobs x' / atom := by
      simpa [atom] using
        mechCFactor_eq_qLocalMass_div_jointRef M ref sObs C hCobs href
          (standard_fixed_random_edgeless M hStd) x'
    calc
      (∏ i ∈ Finset.univ.filter
          (fun i : Fin M.observed.card => (M.observedAt i).val ∈ C),
        M.obsStepCondDensity ref sObs i x') *
          jointRef ref C
            ({valuesProjection hCobs x'} : Set (ValuesOn C (swigΩ Ω)))
          = M.cComponentDensityFactor ref sObs C x' * atom := by
              rw [hprod]
      _ = M.mechCFactor ref C hCobs sObs x' * atom := by
              rw [cComponentDensityFactor_eq_mechCFactor
                M ref sObs hStd C hCobs hCmem href (hpos sObs) x']
      _ = (M.qLocalMass sObs C hCobs x' / atom) * atom := by
              rw [hmech]
      _ = M.qLocalMass sObs C hCobs x' := by
              exact ENNReal.div_mul_cancel hatom0 hatomtop
  have hidentify :
      M.identifyMassRec M.toSWIGGraph C S hCobs
          (fun x' =>
            (∏ i ∈ Finset.univ.filter
                (fun i : Fin M.observed.card => (M.observedAt i).val ∈ C),
              M.obsStepCondDensity ref sObs i x') *
            jointRef ref C
              ({valuesProjection hCobs x'} : Set (ValuesOn C (swigΩ Ω))))
          (extend xD) =
        M.qLocalMass sObs S hSobs (extend xD) := by
    rw [hseed]
    exact identifyMassRec_qLocalMass M sObs (hpos sObs) C S hCobs hReach (extend xD)
  have hkey :=
    tianDistrictDensity_eq_qLocalMass_div_jointRef_district
      M X hObs hFix Y ref href sDo hpos hYX S hS extend hExtend xD
  calc
    tianDistrictDensity H D
        (doObsKernelAncestralMarginal M X hObs hFix Y sDo) ref S xD
        =
      MX.qLocalMass sDo S
          (show S ⊆ MX.observed from by
            simpa [MX, SCM.fixSet_observed] using hSobs)
          (extend xD) /
        jointRef ref S
          ({valuesProjection hSD xD} : Set (ValuesOn S (swigΩ Ω))) := by
          simpa [H, D, MX] using hkey
    _ =
      M.qLocalMass sObs S hSobs (extend xD) /
        jointRef ref S
          ({valuesProjection hSD xD} : Set (ValuesOn S (swigΩ Ω))) := by
          rw [hdo]
    _ =
      M.qLocalMass sObs S hSobs (extend xD) /
        jointRef ref S
          ({valuesProjection hSobs (extend xD)} : Set (ValuesOn S (swigΩ Ω))) := by
          rw [hproj]
    _ =
      recoveredFactorRec M ref sObs C S (extend xD) := by
          unfold recoveredFactorRec
          rw [dif_pos hCobs, dif_pos hSobs, hidentify]

/-- Recursive Tian–Shpitser density core for the observed-ancestral do-law.

This is the new mathematical layer beyond `id_sound`: it replaces the no-fixing
per-district recovery step in `doObsKernelAncestralMarginal_heq_of_obsDensity_heq`
with recovery by induction on `CFactorReachableRec`. -/
theorem doObsKernelAncestralMarginal_heq_of_obsDensity_heq_rec
    [∀ n, StandardBorelSpace (Ω n)] [∀ n, Nonempty (Ω n)]
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (X : Finset N) (Y : Finset (SWIGNode N)) (G : SWIGGraph N)
    (ref : ReferenceMeasures Ω)
    (href : ReferenceFaithful ref)
    (_hID : idSucceedsRec X Y G)
    (M₁ M₂ : Causalean.SCM N Ω)
    (_hsg₁ : M₁.toSWIGGraph = G) (_hsg₂ : M₂.toSWIGGraph = G)
    (_hdom₁ : DominatedObs M₁ ref) (_hdom₂ : DominatedObs M₂ ref)
    (hpos₁ : DiscreteID.DiscretePositive M₁) (hpos₂ : DiscreteID.DiscretePositive M₂)
    (hYX : ∀ D ∈ X, SWIGNode.random D ∉ Y)
    (_hden : HEq (M₁.obsDensity ref) (M₂.obsDensity ref))
    (hvalid₁ : interventionalQueryValid X Y M₁)
    (hvalid₂ : interventionalQueryValid X Y M₂) :
    HEq (doObsKernelAncestralMarginal M₁ X hvalid₁.1 hvalid₁.2.1 Y)
        (doObsKernelAncestralMarginal M₂ X hvalid₂.1 hvalid₂.2.1 Y) := by
  classical
  have hobs : HEq M₁.obsKernel M₂.obsKernel :=
    obsKernel_heq_of_obsDensity_heq M₁ M₂ ref (_hsg₁.trans _hsg₂.symm)
      _hdom₁ _hdom₂ _hden
  have hsg : M₁.toSWIGGraph = M₂.toSWIGGraph := _hsg₁.trans _hsg₂.symm
  haveI hfin1 : ∀ s, MeasureTheory.IsFiniteMeasure
      ((doObsKernelAncestralMarginal M₁ X hvalid₁.1 hvalid₁.2.1 Y) s) :=
    fun s => inferInstance
  haveI hfin2 : ∀ s, MeasureTheory.IsFiniteMeasure
      ((doObsKernelAncestralMarginal M₂ X hvalid₂.1 hvalid₂.2.1 Y) s) :=
    fun s => inferInstance
  haveI hobsfin1 : ∀ s, MeasureTheory.IsFiniteMeasure (M₁.obsKernel s) :=
    fun s => inferInstance
  haveI hobsfin2 : ∀ s, MeasureTheory.IsFiniteMeasure (M₂.obsKernel s) :=
    fun s => inferInstance
  obtain ⟨⟨dag₁, fixed₁, observed₁, unobserved₁,
           fio₁, oi₁, od₁, oou₁, foi₁, fou₁, aic₁, dc₁, foff₁, aco₁⟩,
         eT₁, iota₁, sf₁, mf₁, lD₁, pL₁⟩ := M₁
  obtain ⟨⟨dag₂, fixed₂, observed₂, unobserved₂,
           fio₂, oi₂, od₂, oou₂, foi₂, fou₂, aic₂, dc₂, foff₂, aco₂⟩,
         eT₂, iota₂, sf₂, mf₂, lD₂, pL₂⟩ := M₂
  cases hsg
  have hfio : fio₂ = fio₁ := Subsingleton.elim _ _
  subst fio₂
  have hoi : oi₂ = oi₁ := Subsingleton.elim _ _
  subst oi₂
  have hod : od₂ = od₁ := Subsingleton.elim _ _
  subst od₂
  have hoou : oou₂ = oou₁ := Subsingleton.elim _ _
  subst oou₂
  have hfoi : foi₂ = foi₁ := Subsingleton.elim _ _
  subst foi₂
  have hfou : fou₂ = fou₁ := Subsingleton.elim _ _
  subst fou₂
  have haic : aic₂ = aic₁ := Subsingleton.elim _ _
  subst aic₂
  have hdc : dc₂ = dc₁ := Subsingleton.elim _ _
  subst dc₂
  have hfoff : foff₂ = foff₁ := Subsingleton.elim _ _
  subst foff₂
  have haco : aco₂ = aco₁ := Subsingleton.elim _ _
  subst aco₂
  apply heq_of_eq
  refine ProbabilityTheory.Kernel.ext (fun s => ?_)
  refine MeasureTheory.Measure.eq_of_rnDeriv_eq (hfin1 s) (hfin2 s)
    (doObsKernelAncestralMarginal_dominated _ X hvalid₁.1 hvalid₁.2.1 Y ref href s)
    (doObsKernelAncestralMarginal_dominated _ X hvalid₂.1 hvalid₂.2.1 Y ref href s) ?_
  have w1 := doObsKernelAncestralMarginal_tian_cfactorization_density _ X hvalid₁.1 hvalid₁.2.1
    Y ref s
    (doObsKernelAncestralMarginal_dominated _ X hvalid₁.1 hvalid₁.2.1 Y ref href s)
  have w2 := doObsKernelAncestralMarginal_tian_cfactorization_density _ X hvalid₂.1 hvalid₂.2.1
    Y ref s
    (doObsKernelAncestralMarginal_dominated _ X hvalid₂.1 hvalid₂.2.1 Y ref href s)
  refine w1.trans (Filter.EventuallyEq.trans ?_ w2.symm)
  let M₁' : Causalean.SCM N Ω :=
    { dag := dag₁, fixed := fixed₁, observed := observed₁, unobserved := unobserved₁,
      fixed_is_fixed := fio₁, observed_is_random := oi₁, unobserved_is_random := od₁,
      obs_unobs_disjoint := oou₁, dag_edges_classified := foi₁,
      fixed_image_in_observed := fou₁, fixed_are_roots := aic₁, unobs_are_roots := dc₁,
      fixed_outside_fixed_isolated := foff₁, all_children_in_observed := aco₁,
      edgeTypes := eT₁, iota_valueSpace := iota₁, structFun := sf₁,
      structFun_measurable := mf₁, latentDist := lD₁, isProbability_latent := pL₁ }
  let M₂' : Causalean.SCM N Ω :=
    { dag := dag₁, fixed := fixed₁, observed := observed₁, unobserved := unobserved₁,
      fixed_is_fixed := fio₁, observed_is_random := oi₁, unobserved_is_random := od₁,
      obs_unobs_disjoint := oou₁, dag_edges_classified := foi₁,
      fixed_image_in_observed := fou₁, fixed_are_roots := aic₁, unobs_are_roots := dc₁,
      fixed_outside_fixed_isolated := foff₁, all_children_in_observed := aco₁,
      edgeTypes := eT₂, iota_valueSpace := iota₂, structFun := sf₂,
      structFun_measurable := mf₂, latentDist := lD₂, isProbability_latent := pL₂ }
  let D := fixObservedAncestralSet M₁' X hvalid₁.1 hvalid₁.2.1 Y
  let H := (M₁'.fixSet X hvalid₁.1 hvalid₁.2.1).toSWIGGraph.induce
    (fixAncestralSet M₁' X hvalid₁.1 hvalid₁.2.1 Y)
  haveI hν₁ : MeasureTheory.IsFiniteMeasure
      ((doObsKernelAncestralMarginal M₁' X hvalid₁.1 hvalid₁.2.1 Y) s) :=
    hfin1 s
  haveI hν₂ : MeasureTheory.IsFiniteMeasure
      ((doObsKernelAncestralMarginal M₂' X hvalid₂.1 hvalid₂.2.1 Y) s) :=
    hfin2 s
  haveI hν₂D : MeasureTheory.IsFiniteMeasure
      (show MeasureTheory.Measure (ValuesOn D (swigΩ Ω)) from
        ((doObsKernelAncestralMarginal M₂' X hvalid₂.1 hvalid₂.2.1 Y) s)) := by
    change MeasureTheory.IsFiniteMeasure
      ((doObsKernelAncestralMarginal M₂' X hvalid₂.1 hvalid₂.2.1 Y) s)
    exact hfin2 s
  change (fun x => ∏ S ∈ H.cComponentSet,
      tianDistrictDensity H D
        ((doObsKernelAncestralMarginal M₁' X hvalid₁.1 hvalid₁.2.1 Y) s) ref S x)
      =ᵐ[jointRef ref D]
    (fun x => ∏ S ∈ H.cComponentSet,
      tianDistrictDensity H D
        ((doObsKernelAncestralMarginal M₂' X hvalid₂.1 hvalid₂.2.1 Y) s) ref S x)
  have hfac : ∀ S ∈ H.cComponentSet,
      tianDistrictDensity H D
          ((doObsKernelAncestralMarginal M₁' X hvalid₁.1 hvalid₁.2.1 Y) s) ref S
        =ᵐ[jointRef ref D]
      tianDistrictDensity H D
          ((doObsKernelAncestralMarginal M₂' X hvalid₂.1 hvalid₂.2.1 Y) s) ref S := by
    intro S hS
    have hIDM : idSucceedsRec X Y M₁'.toSWIGGraph := by
      rw [_hsg₁]
      exact _hID
    rcases hIDM with ⟨hX, hIDrest⟩
    have hSreach : S ∈ ((M₁'.toSWIGGraph.splitMono X hX.1 hX.2).induce
        ((M₁'.toSWIGGraph.splitMono X hX.1 hX.2).dag.ancestralSet Y)).cComponentSet := by
      simpa [H, fixAncestralSet, fixTruncCComponentSet] using hS
    let C := containingCComponent M₁'.toSWIGGraph S
    have hReach : CFactorReachableRec M₁'.toSWIGGraph C S := by
      simpa [C] using hIDrest.2.2 S hSreach
    have hSne : S.Nonempty := by
      simp only [SWIGGraph.cComponentSet] at hS
      rcases Finset.mem_image.mp hS with ⟨v, hv, rfl⟩
      exact ⟨v, H.mem_cComponentOf_self hv⟩
    have hSobs : S ⊆ M₁'.toSWIGGraph.observed := by
      have hSobsH : S ⊆ H.observed :=
        H.cComponentSet_subset_observed S hS
      intro v hv
      have hvD : v ∈ D := by
        simpa [H, D, fixObservedAncestralSet, SCM.fixSet_observed, SWIGGraph.induce]
          using hSobsH hv
      exact (Finset.mem_inter.mp hvD).2
    have hCmem : C ∈ M₁'.toSWIGGraph.cComponentSet := by
      have hchoose : hSne.choose ∈ M₁'.toSWIGGraph.observed :=
        hSobs hSne.choose_spec
      simp only [C, containingCComponent, dif_pos hSne, SWIGGraph.cComponentSet]
      exact Finset.mem_image.mpr ⟨hSne.choose, hchoose, rfl⟩
    let extend : ValuesOn D (swigΩ Ω) → ValuesOn M₁'.observed (swigΩ Ω) :=
      pinnedExtend M₁' X hvalid₁.1 hvalid₁.2.1 Y s
    have hExtend : ∀ xD, valuesProjection
        (show D ⊆ M₁'.observed from Finset.inter_subset_right) (extend xD) = xD :=
      pinnedExtend_projection_eq M₁' X hvalid₁.1 hvalid₁.2.1 Y s hYX
    have hExtendX : ∀ xD (D : N) (hD : D ∈ X),
        extend xD ⟨SWIGNode.random D, hvalid₁.1 D hD⟩ =
          s ⟨SWIGNode.fixed D,
            Finset.mem_union_right _
              (Finset.mem_image.mpr ⟨D, hD, rfl⟩)⟩ :=
      pinnedExtend_pin_eq M₁' X hvalid₁.1 hvalid₁.2.1 Y s
    have hpos₁' : ∀ s' : M₁'.FixedValues,
        DiscreteID.PositiveMass (M₁'.obsKernel s') :=
      hpos₁
    have hpos₂' : ∀ s' : M₂'.FixedValues,
        DiscreteID.PositiveMass (M₂'.obsKernel s') :=
      hpos₂
    haveI hobsfin₁ : ∀ s' : M₁'.FixedValues,
        MeasureTheory.IsFiniteMeasure (M₁'.obsKernel s') :=
      hobsfin1
    haveI hobsfin₂ : ∀ s' : M₂'.FixedValues,
        MeasureTheory.IsFiniteMeasure (M₂'.obsKernel s') :=
      hobsfin2
    have t1 := doAncestralDistrictDensity_recovered_from_obs_rec M₁'
      X hvalid₁.2.2.2 hvalid₁.1 hvalid₁.2.1 Y ref href s S C
      (by simpa [H, fixTruncCComponentSet] using hS) hReach hCmem hpos₁' hYX extend hExtend
      hExtendX
    have t2 := doAncestralDistrictDensity_recovered_from_obs_rec M₂'
      X hvalid₂.2.2.2 hvalid₂.1 hvalid₂.2.1 Y ref href s S C
      (by simpa [H, fixTruncCComponentSet] using hS)
      (by simpa [M₁', M₂'] using hReach) (by simpa [M₁', M₂'] using hCmem)
      hpos₂' hYX extend (by simpa [M₁', M₂'] using hExtend)
      (by simpa [M₁', M₂'] using hExtendX)
    have hrec := recoveredFactorRec_heq_of_obsKernel_heq M₁' M₂' ref C S rfl hobs
    have hrec_fun : (fun s' => recoveredFactorRec M₁' ref s' C S) =
        (fun s' => recoveredFactorRec M₂' ref s' C S) :=
      eq_of_heq hrec
    have hrec_s := congrFun hrec_fun (M₁'.fixSetProj X hvalid₁.1 hvalid₁.2.1 s)
    refine t1.trans ?_
    filter_upwards [t2.symm] with x hx
    exact hrec_s ▸ hx
  clear w1 w2
  have hprod : ∀ I : Finset (Finset (SWIGNode N)),
      (∀ S ∈ I,
        tianDistrictDensity H D
            ((doObsKernelAncestralMarginal M₁' X hvalid₁.1 hvalid₁.2.1 Y) s) ref S
          =ᵐ[jointRef ref D]
        tianDistrictDensity H D
            ((doObsKernelAncestralMarginal M₂' X hvalid₂.1 hvalid₂.2.1 Y) s) ref S) →
      (fun x => ∏ S ∈ I,
        tianDistrictDensity H D
          ((doObsKernelAncestralMarginal M₁' X hvalid₁.1 hvalid₁.2.1 Y) s) ref S x)
        =ᵐ[jointRef ref D]
      (fun x => ∏ S ∈ I,
        tianDistrictDensity H D
          ((doObsKernelAncestralMarginal M₂' X hvalid₂.1 hvalid₂.2.1 Y) s) ref S x) := by
    intro I hIall
    induction I using Finset.induction_on with
    | empty =>
        simp
    | insert S I hSnot ih =>
        have hS : tianDistrictDensity H D
              ((doObsKernelAncestralMarginal M₁' X hvalid₁.1 hvalid₁.2.1 Y) s) ref S
            =ᵐ[jointRef ref D]
            tianDistrictDensity H D
              ((doObsKernelAncestralMarginal M₂' X hvalid₂.1 hvalid₂.2.1 Y) s) ref S :=
          hIall S (Finset.mem_insert_self S I)
        have hI : (fun x => ∏ T ∈ I,
              tianDistrictDensity H D
                ((doObsKernelAncestralMarginal M₁' X hvalid₁.1 hvalid₁.2.1 Y) s) ref T x)
            =ᵐ[jointRef ref D]
          (fun x => ∏ T ∈ I,
            tianDistrictDensity H D
              ((doObsKernelAncestralMarginal M₂' X hvalid₂.1 hvalid₂.2.1 Y) s) ref T x) :=
          ih (by
            intro T hT
            exact hIall T (Finset.mem_insert_of_mem hT))
        filter_upwards [hS, hI] with x hxS hxI
        simp [Finset.prod_insert hSnot, hxS, hxI]
  exact hprod H.cComponentSet hfac

/-- Recursive density-to-`Y`-marginal wrapper.  The projection from the
observed-ancestral marginal to the query coordinates is identical to the
no-fixing proof; only the ancestral density core changes. -/
theorem doObsKernelYMarginal_heq_of_obsDensity_heq_rec
    [∀ n, StandardBorelSpace (Ω n)] [∀ n, Nonempty (Ω n)]
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (X : Finset N) (Y : Finset (SWIGNode N)) (G : SWIGGraph N)
    (ref : ReferenceMeasures Ω)
    (href : ReferenceFaithful ref)
    (_hID : idSucceedsRec X Y G)
    (M₁ M₂ : Causalean.SCM N Ω)
    (_hsg₁ : M₁.toSWIGGraph = G) (_hsg₂ : M₂.toSWIGGraph = G)
    (_hdom₁ : DominatedObs M₁ ref) (_hdom₂ : DominatedObs M₂ ref)
    (hpos₁ : DiscreteID.DiscretePositive M₁) (hpos₂ : DiscreteID.DiscretePositive M₂)
    (hYX : ∀ D ∈ X, SWIGNode.random D ∉ Y)
    (_hden : HEq (M₁.obsDensity ref) (M₂.obsDensity ref))
    (hvalid₁ : interventionalQueryValid X Y M₁)
    (hvalid₂ : interventionalQueryValid X Y M₂) :
    HEq (doObsKernelYMarginal M₁ X hvalid₁.1 hvalid₁.2.1 Y hvalid₁.2.2.1)
        (doObsKernelYMarginal M₂ X hvalid₂.1 hvalid₂.2.1 Y hvalid₂.2.2.1) := by
  have hsg : M₁.toSWIGGraph = M₂.toSWIGGraph := _hsg₁.trans _hsg₂.symm
  exact doObsKernelYMarginal_heq_of_ancestralMarginal_heq X Y M₁ M₂ hsg
    hvalid₁.1 hvalid₁.2.1 hvalid₂.1 hvalid₂.2.1 hvalid₁.2.2.1 hvalid₂.2.2.1
    (doObsKernelAncestralMarginal_heq_of_obsDensity_heq_rec X Y G ref href _hID M₁ M₂
      _hsg₁ _hsg₂ _hdom₁ _hdom₂ hpos₁ hpos₂ hYX _hden hvalid₁ hvalid₂)

/-- Recursive observational-kernel wrapper.  Equal observational kernels give
equal observational densities, which feed the recursive density core. -/
theorem doObsKernelYMarginal_heq_of_obsKernel_heq_rec
    [∀ n, StandardBorelSpace (Ω n)] [∀ n, Nonempty (Ω n)]
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (X : Finset N) (Y : Finset (SWIGNode N)) (G : SWIGGraph N)
    (ref : ReferenceMeasures Ω)
    (href : ReferenceFaithful ref)
    (hID : idSucceedsRec X Y G)
    (M₁ M₂ : Causalean.SCM N Ω)
    (hsg₁ : M₁.toSWIGGraph = G) (hsg₂ : M₂.toSWIGGraph = G)
    (hdom₁ : DominatedObs M₁ ref) (hdom₂ : DominatedObs M₂ ref)
    (hpos₁ : DiscreteID.DiscretePositive M₁) (hpos₂ : DiscreteID.DiscretePositive M₂)
    (hYX : ∀ D ∈ X, SWIGNode.random D ∉ Y)
    (hobs : HEq M₁.obsKernel M₂.obsKernel)
    (hvalid₁ : interventionalQueryValid X Y M₁)
    (hvalid₂ : interventionalQueryValid X Y M₂) :
    HEq (doObsKernelYMarginal M₁ X hvalid₁.1 hvalid₁.2.1 Y hvalid₁.2.2.1)
        (doObsKernelYMarginal M₂ X hvalid₂.1 hvalid₂.2.1 Y hvalid₂.2.2.1) :=
  doObsKernelYMarginal_heq_of_obsDensity_heq_rec X Y G ref href hID M₁ M₂ hsg₁ hsg₂
    hdom₁ hdom₂ hpos₁ hpos₂ hYX
    (obsDensity_heq_of_obsKernel_heq M₁ M₂ ref (hsg₁.trans hsg₂.symm) hobs)
    hvalid₁ hvalid₂

/-- Recursive valid-branch kernel equality.  This is the same transport as
`doKernelY_eq_cfactor_decomposition`, with the recursive `Y`-marginal wrapper in
place of the no-fixing one. -/
theorem doKernelY_eq_cfactor_decomposition_rec
    [∀ n, StandardBorelSpace (Ω n)] [∀ n, Nonempty (Ω n)]
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (X : Finset N) (Y : Finset (SWIGNode N)) (G : SWIGGraph N)
    (ref : ReferenceMeasures Ω)
    (href : ReferenceFaithful ref)
    (_hID : idSucceedsRec X Y G)
    (M₁ M₂ : Causalean.SCM N Ω)
    (_hsg₁ : M₁.toSWIGGraph = G) (_hsg₂ : M₂.toSWIGGraph = G)
    (_hdom₁ : DominatedObs M₁ ref) (_hdom₂ : DominatedObs M₂ ref)
    (hpos₁ : DiscreteID.DiscretePositive M₁) (hpos₂ : DiscreteID.DiscretePositive M₂)
    (hYX : ∀ D ∈ X, SWIGNode.random D ∉ Y)
    (_hobs : HEq M₁.obsKernel M₂.obsKernel)
    (hvalid₁ : interventionalQueryValid X Y M₁)
    (hvalid₂ : interventionalQueryValid X Y M₂) :
    M₁.doKernelY X hvalid₁.1 hvalid₁.2.1 Y hvalid₁.2.2.1
        (standardFixedValues M₁ hvalid₁.2.2.2)
      =
    M₂.doKernelY X hvalid₂.1 hvalid₂.2.1 Y hvalid₂.2.2.1
        (standardFixedValues M₂ hvalid₂.2.2.2) := by
  have hsg : M₁.toSWIGGraph = M₂.toSWIGGraph := _hsg₁.trans _hsg₂.symm
  exact doKernelY_eq_of_doObsKernel_heq X Y M₁ M₂ hsg
    hvalid₁.1 hvalid₁.2.1 hvalid₂.1 hvalid₂.2.1 hvalid₁.2.2.1 hvalid₂.2.2.1
    (standardFixedValues M₁ hvalid₁.2.2.2) (standardFixedValues M₂ hvalid₂.2.2.2)
    (standardFixedValues_heq M₁ M₂ hsg hvalid₁.2.2.2 hvalid₂.2.2.2)
    (doObsKernelYMarginal_heq_of_obsKernel_heq_rec X Y G ref href _hID M₁ M₂ _hsg₁ _hsg₂
      _hdom₁ _hdom₂ hpos₁ hpos₂ hYX _hobs hvalid₁ hvalid₂)

/-- **Soundness of the full recursive ID algorithm for finite discrete-positive models.**
A successful recursive certificate identifies the interventional query among
finite node-space models whose observational laws are dominated by the chosen
faithful reference family and whose point masses satisfy discrete positivity.
This generalizes `id_sound` from the no-fixing fragment to the full
Tian-Shpitser IDENTIFY recursion; see the module docstring for the proof
architecture. -/
theorem id_sound_rec [∀ n, StandardBorelSpace (Ω n)] [∀ n, Nonempty (Ω n)]
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (X : Finset N) (Y : Finset (SWIGNode N)) (G : SWIGGraph N)
    (ref : ReferenceMeasures Ω) (href : ReferenceFaithful ref) :
    idSucceedsRec X Y G →
      IdentifiableUnder (Ω := Ω) G (fun _ => True)
        (fun M => DominatedObs M ref ∧ DiscreteID.DiscretePositive M)
        (interventionalQuery (Ω := Ω) X Y) := by
  classical
  intro hID M₁ M₂ hsg₁ hsg₂ _ _ hM₁ hM₂ hobs
  have hYX : ∀ D ∈ X, SWIGNode.random D ∉ Y := by
    rcases hID with ⟨_hX, hIDrest⟩
    exact hIDrest.2.1
  have hvalid_iff :
      interventionalQueryValid X Y M₁ ↔ interventionalQueryValid X Y M₂ :=
    interventionalQueryValid_iff_of_obsKernel_heq
      (Ω := Ω) X Y G M₁ M₂ hsg₁ hsg₂ hobs
  by_cases hvalid₁ : interventionalQueryValid X Y M₁
  · have hvalid₂ : interventionalQueryValid X Y M₂ := hvalid_iff.mp hvalid₁
    rw [interventionalQuery_eq_doKernelY_of_valid (Ω := Ω) X Y M₁ hvalid₁,
      interventionalQuery_eq_doKernelY_of_valid (Ω := Ω) X Y M₂ hvalid₂]
    exact doKernelY_eq_cfactor_decomposition_rec
      (Ω := Ω) X Y G ref href hID M₁ M₂ hsg₁ hsg₂ hM₁.1 hM₂.1 hM₁.2 hM₂.2 hYX
      hobs hvalid₁ hvalid₂
  · have hvalid₂ : ¬ interventionalQueryValid X Y M₂ := by
      intro h
      exact hvalid₁ (hvalid_iff.mpr h)
    rw [interventionalQuery_eq_default_of_not_valid (Ω := Ω) X Y M₁ hvalid₁,
      interventionalQuery_eq_default_of_not_valid (Ω := Ω) X Y M₂ hvalid₂]

/-- **Discrete soundness of the full recursive ID algorithm (on-contract).**  The
full Tian–Shpitser identification-soundness headline over the standard discrete
positive class: a successful recursive certificate `idSucceedsRec` identifies the
interventional query.  Obtained from `id_sound_rec` at the counting reference by
collapsing `DominatedObs · countingRef` to `StandardDiscretePositive`, exactly as
`id_sound_discrete` is obtained from `id_sound`.  This subsumes
`id_sound_discrete` (via `idSucceeds_toRec`). -/
theorem id_sound_rec_discrete
    [∀ n, StandardBorelSpace (Ω n)] [∀ n, Nonempty (Ω n)]
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (X : Finset N) (Y : Finset (SWIGNode N)) (G : SWIGGraph N)
    (h : idSucceedsRec X Y G) :
    IdentifiableUnder G (fun _ => True) StandardDiscretePositive
      (interventionalQuery (Ω := Ω) X Y) := by
  have hdom :=
    id_sound_rec X Y G (countingRef (Ω := Ω)) referenceFaithful_countingRef h
  exact identifiableUnder_mono G (fun _ => True) (fun _ => True)
    (fun M => DominatedObs M (countingRef (Ω := Ω)) ∧ DiscretePositive M)
    StandardDiscretePositive (interventionalQuery (Ω := Ω) X Y)
    (fun _ h => h) (fun M hM => ⟨dominatedObs_countingRef M, hM.2⟩) hdom

/-- **The no-fixing discrete headline is subsumed by the recursive one.**  A sanity
corollary: `id_sound_discrete` follows from `id_sound_rec_discrete` through the
certificate subsumption `idSucceeds_toRec`. -/
theorem id_sound_discrete_of_rec
    [∀ n, StandardBorelSpace (Ω n)] [∀ n, Nonempty (Ω n)]
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (X : Finset N) (Y : Finset (SWIGNode N)) (G : SWIGGraph N)
    (h : idSucceeds X Y G) :
    IdentifiableUnder G (fun _ => True) StandardDiscretePositive
      (interventionalQuery (Ω := Ω) X Y) :=
  id_sound_rec_discrete X Y G (idSucceeds_toRec X Y G h)

end Causalean.SCM.ID
