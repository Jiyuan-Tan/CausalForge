/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.SCM.ID.Query
import Causalean.SCM.ID.DiscreteID.Positive
import Causalean.SCM.ID.GraphicalThms.QFactorIdentity
import Causalean.SCM.ID.Density.FiniteReference
import Causalean.SCM.ID.Density.DoLawMarginal
import Causalean.SCM.ID.DoLawTransport
import Causalean.SCM.ID.GraphicalThms.DoGFormula
import Causalean.SCM.ID.GraphicalThms.DoGFormulaTian
import Causalean.Mathlib.MeasureTheory.EqOfRnDerivEq

/-!
# ID Algorithm Soundness for the No-Fixing Fragment

This file records the graph-side success certificate for the ID algorithm and
states that the certificate identifies the interventional outcome kernel. The
proved soundness theorem combines branch alignment for the total query's
well-formedness predicate with the Tian c-factor decomposition for the valid
branch.

The success predicate is structural. It computes the ancestors of the requested
outcomes after splitting the treatment variables in the SWIG, induces the
ancestral subgraph, and checks its c-components against c-components already
available in the original graph. This is the no-additional-fixing case of the
Tian/Shpitser reachability condition; the general fixing-sequence predicate is
deferred here rather than encoded as a circular appeal to identifiability.
-/

namespace Causalean.SCM.ID

open scoped MeasureTheory ProbabilityTheory

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

-- The finite-reference ID API intentionally exposes `Fintype` assumptions,
-- matching the surrounding finite density theorems even when a particular
-- statement could be weakened to `Finite`.
set_option linter.unusedFintypeInType false

/-- Two standard models with the same SWIG graph have the same canonical fixed-value assignment after type transport.

Both fixed-node sets are empty, so each fixed-value product is a one-point space. -/
theorem standardFixedValues_heq (M₁ M₂ : Causalean.SCM N Ω)
    (hsg : M₁.toSWIGGraph = M₂.toSWIGGraph)
    (h₁ : M₁.isStandard) (h₂ : M₂.isStandard) :
    HEq (standardFixedValues M₁ h₁) (standardFixedValues M₂ h₂) := by
  have hf : M₁.fixed = M₂.fixed := congrArg SWIGGraph.fixed hsg
  have h₁' : M₁.fixed = (∅ : Finset (SWIGNode N)) := h₁
  haveI hempty : IsEmpty {v // v ∈ M₁.fixed} :=
    ⟨fun i => absurd (h₁' ▸ i.property) (Finset.notMem_empty i.val)⟩
  haveI hsub₁ : Subsingleton M₁.FixedValues :=
    ⟨fun a b => funext fun i => isEmptyElim i⟩
  exact Subsingleton.helim (congrArg (fun S => ValuesOn S (swigΩ Ω)) hf) _ _

/-- The outcome marginal of the do-law is the projection of the observed-ancestral do-law marginal to the outcome coordinates.

Both measures are pushforwards of the same do-observational law, and the outcome
coordinates lie inside the observed ancestral support. -/
theorem doObsKernelYMarginal_eq_ancestralMarginal_map
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (Y : Finset (SWIGNode N)) (hY : Y ⊆ M.observed) :
    doObsKernelYMarginal M X hObs hFix Y hY
      = (doObsKernelAncestralMarginal M X hObs hFix Y).map
          (valuesProjection (subset_fixObservedAncestralSet M X hObs hFix Y hY)) := by
  unfold doObsKernelYMarginal doObsKernelAncestralMarginal
  rw [← ProbabilityTheory.Kernel.map_comp_right _ (measurable_valuesProjection _)
      (measurable_valuesProjection _),
    valuesProjection_comp (subset_fixObservedAncestralSet M X hObs hFix Y hY)
      Finset.inter_subset_right ((SCM.fixSet_observed M X hObs hFix).symm ▸ hY)]

/-- If two models with the same SWIG graph have equal observed-ancestral do-law marginals, then their outcome marginals agree.

The outcome marginal is the ancestral marginal projected to the outcome
coordinates, and that projection is determined by the shared graph. -/
theorem doObsKernelYMarginal_heq_of_ancestralMarginal_heq
    (X : Finset N) (Y : Finset (SWIGNode N))
    (M₁ M₂ : Causalean.SCM N Ω)
    (hsg : M₁.toSWIGGraph = M₂.toSWIGGraph)
    (hObs₁ : ∀ D ∈ X, SWIGNode.random D ∈ M₁.observed)
    (hFix₁ : ∀ D ∈ X, SWIGNode.fixed D ∉ M₁.fixed)
    (hObs₂ : ∀ D ∈ X, SWIGNode.random D ∈ M₂.observed)
    (hFix₂ : ∀ D ∈ X, SWIGNode.fixed D ∉ M₂.fixed)
    (hY₁ : Y ⊆ M₁.observed) (hY₂ : Y ⊆ M₂.observed)
    (hAnc : HEq (doObsKernelAncestralMarginal M₁ X hObs₁ hFix₁ Y)
                (doObsKernelAncestralMarginal M₂ X hObs₂ hFix₂ Y)) :
    HEq (doObsKernelYMarginal M₁ X hObs₁ hFix₁ Y hY₁)
        (doObsKernelYMarginal M₂ X hObs₂ hFix₂ Y hY₂) := by
  rw [doObsKernelYMarginal_eq_ancestralMarginal_map M₁ X hObs₁ hFix₁ Y hY₁,
      doObsKernelYMarginal_eq_ancestralMarginal_map M₂ X hObs₂ hFix₂ Y hY₂]
  obtain ⟨⟨dag₁, fixed₁, observed₁, unobserved₁,
           fio₁, oi₁, od₁, oou₁, foi₁, fou₁, aic₁, dc₁, foff₁, aco₁⟩,
         eT₁, iota₁, sf₁, mf₁, lD₁, pL₁⟩ := M₁
  obtain ⟨⟨dag₂, fixed₂, observed₂, unobserved₂,
           fio₂, oi₂, od₂, oou₂, foi₂, fou₂, aic₂, dc₂, foff₂, aco₂⟩,
         eT₂, iota₂, sf₂, mf₂, lD₂, pL₂⟩ := M₂
  cases hsg
  apply heq_of_eq
  congr 1
  exact eq_of_heq hAnc

/-- The observed-ancestral marginal of a post-intervention observational law is a finite measure. -/
instance instIsFiniteMeasure_doObsKernelAncestralMarginal
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (Y : Finset (SWIGNode N)) (s : (M.fixSet X hObs hFix).FixedValues) :
    MeasureTheory.IsFiniteMeasure
      (doObsKernelAncestralMarginal M X hObs hFix Y s) := by
  unfold doObsKernelAncestralMarginal
  rw [ProbabilityTheory.Kernel.map_apply]
  · exact ((M.fixSet X hObs hFix).obsKernel s).isFiniteMeasure_map
      (valuesProjection (Finset.inter_subset_right :
        fixObservedAncestralSet M X hObs hFix Y ⊆ (M.fixSet X hObs hFix).observed))
  · exact measurable_valuesProjection _

/-- A faithful finite product reference dominates the post-intervention observed-ancestral marginal.

On finite measurable-singleton node spaces, a faithful reference family gives
nonzero mass to every coordinate atom, hence `jointRef` gives nonzero mass to
every product singleton.  A `jointRef`-null set is therefore empty, so every
measure on the observed-ancestral product space is absolutely continuous with
respect to `jointRef`. -/
theorem doObsKernelAncestralMarginal_dominated
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) (X : Finset N)
    (hObs : ∀ D ∈ X, SWIGNode.random D ∈ M.observed)
    (hFix : ∀ D ∈ X, SWIGNode.fixed D ∉ M.fixed)
    (Y : Finset (SWIGNode N)) (ref : ReferenceMeasures Ω)
    (href : ReferenceFaithful ref)
    (s : (M.fixSet X hObs hFix).FixedValues) :
    doObsKernelAncestralMarginal M X hObs hFix Y s ≪
      jointRef ref (fixObservedAncestralSet M X hObs hFix Y) := by
  exact absolutelyContinuous_jointRef_of_faithful ref href
    (fixObservedAncestralSet M X hObs hFix Y)
    (doObsKernelAncestralMarginal M X hObs hFix Y s)

/-- Two dominated models with the same SWIG graph and observational density have the same
post-intervention law on the observed ancestors selected by a successful ID certificate.

This is the density-level ID theorem behind the no-fixing soundness result. The
proof mirrors Tian's
identification argument, which is inherently a *scalar-density* computation (it
uses marginalization `∑_{h∖h^(i)} Q[H]` and division `Q[H^(i)]/Q[H^(i-1)]`, neither
a kernel operation) — hence the density hypothesis and the dominated model class.
Route, reusing the proven density bricks:

1. *Truncated factorization.*  `P(v∖x ∣ do(x)) = ∏_{Vᵢ∉X} P(vᵢ ∣ v^(i-1))` — the
   do-model `M.fixSet X` is a gSCM, so its joint density factorizes by the chain
   rule (`obsDensity_eq_qFactorDensityProduct`, D1), with the intervened nodes
   contributing graph-and-treatment-determined point masses.  Structurally, each
   `random D` (`D ∈ X`) loses its outgoing edges in `G_X` (`splitMonoEdgeRel`), so
   it is a sink and enters `An_{G_X}(Y)` only if it is itself a query node, where
   its coordinate is identical across the two models.
2. *Marginalize to the ancestral support.*  Sum out the non-ancestral districts
   (`∑_{h∖h^(i)}`), leaving the marginal on `An_{G_X}(Y) ∩ observed`.
3. *Regroup over c-components* of `(G_X).induce (An_{G_X}(Y))` (`fixTruncCComponentSet`)
   — `qFactorDensityProduct_eq_prod_cComponentFactor` (D2), the commutative scalar
   regrouping.
4. *Recover each factor.*  Under `idSucceeds` each truncated component is a full
   c-component of `G` (`cFactorReachable`), so `district_id` identifies its factor
   as a functional of the observational density.
5. *Transport.*  Equal `obsDensity` ⟹ equal recovered factors ⟹ equal product.

Steps 1/3 are the D1/D2 bricks applied to the do-model; steps 2/4/5 perform the
truncation/marginalization and cross-model density recovery, completing the
scalar-density manipulation needed for the dominated finite-state theorem. -/
theorem doObsKernelAncestralMarginal_heq_of_obsDensity_heq
    [∀ n, StandardBorelSpace (Ω n)] [∀ n, Nonempty (Ω n)]
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (X : Finset N) (Y : Finset (SWIGNode N)) (G : SWIGGraph N)
    (ref : ReferenceMeasures Ω)
    (href : ReferenceFaithful ref)
    (_hID : idSucceeds X Y G)
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
  -- Materialize the marginals' finiteness as local instances while the models are
  -- still named; they survive the structural `obtain` below, where the global
  -- instance no longer matches the constructor form.
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
  -- The two ancestral marginals share the coordinate reference `jointRef ref D`
  -- (`D = fixObservedAncestralSet` reads only the shared SWIG graph, so the two
  -- syntactic copies are definitionally equal), and both are dominated by it
  -- (`doObsKernelAncestralMarginal_dominated`).  A measure is determined by its
  -- density against a fixed reference (`Measure.eq_of_rnDeriv_eq`), so it suffices
  -- to show the two Radon–Nikodym derivatives agree a.e.  Applying the lemma as a
  -- term (not by `rw`) lets unification absorb the definitional `D₁ = D₂` gap that
  -- previously made the rewrite route brittle.
  refine MeasureTheory.Measure.eq_of_rnDeriv_eq (hfin1 s) (hfin2 s)
    (doObsKernelAncestralMarginal_dominated _ X hvalid₁.1 hvalid₁.2.1 Y ref href s)
    (doObsKernelAncestralMarginal_dominated _ X hvalid₂.1 hvalid₂.2.1 Y ref href s) ?_
  -- Remaining density (rnDeriv) transport.  By the Tian wrapper each side's density
  -- is the product over the districts of `G_X[D]` of the district factors
  -- (`doObsKernelAncestralMarginal_tian_cfactorization_density`); by T2 each district
  -- factor equals a recovered full-graph c-factor
  -- (`doAncestralDistrictDensity_recovered_from_obs`); and equal observational kernels
  -- give equal recovered factors (`cComponentDensityFactor_heq_of_obsKernel_heq`),
  -- so the two products — hence the two densities — agree a.e.
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
    have hIDM : idSucceeds X Y M₁'.toSWIGGraph := by
      rw [_hsg₁]
      exact _hID
    rcases hIDM with ⟨hX, hIDrest⟩
    have hSreach : S ∈ ((M₁'.toSWIGGraph.splitMono X hX.1 hX.2).induce
        ((M₁'.toSWIGGraph.splitMono X hX.1 hX.2).dag.ancestralSet Y)).cComponentSet := by
      simpa [H, fixAncestralSet, fixTruncCComponentSet] using hS
    let C := containingCComponent M₁'.toSWIGGraph S
    have hReach : cFactorReachable M₁'.toSWIGGraph C S := by
      simpa [C] using hIDrest.2.2 S hSreach
    have hCmem : C ∈ M₁'.toSWIGGraph.cComponentSet := by
      have hSne : S.Nonempty := hReach.1
      have hSobs : S ⊆ M₁'.toSWIGGraph.observed :=
        M₁'.toSWIGGraph.cComponentSet_subset_observed S hReach.2.2
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
    have t1 := doAncestralDistrictDensity_recovered_from_obs M₁' X hvalid₁.2.2.2
      hvalid₁.1 hvalid₁.2.1 Y ref href s S C
      (by simpa [H, fixTruncCComponentSet] using hS) hReach hCmem hpos₁' hYX extend hExtend
      hExtendX
    have t2 := doAncestralDistrictDensity_recovered_from_obs M₂' X hvalid₂.2.2.2
      hvalid₂.1 hvalid₂.2.1
      Y ref href s S C (by simpa [H, fixTruncCComponentSet] using hS)
      (by simpa [M₁', M₂'] using hReach) (by simpa [M₁', M₂'] using hCmem)
      hpos₂' hYX extend (by simpa [M₁', M₂'] using hExtend)
      (by simpa [M₁', M₂'] using hExtendX)
    have hrec := cComponentDensityFactor_heq_of_obsKernel_heq M₁' M₂' ref C rfl hobs
    have hrec_fun : (fun s' => M₁'.cComponentDensityFactor ref s' C) =
        (fun s' => M₂'.cComponentDensityFactor ref s' C) :=
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

/-- Two dominated models with the same SWIG graph and observational density have the same
post-intervention outcome marginal under a successful ID certificate.

This is the `Y`-marginal wrapper around the density-level ID theorem. Under
`idSucceeds` the `Y`-marginal of the do-law `(M.fixSet X).obsKernel` is the truncated
product, over the
c-components of the ancestral subgraph `(G_X).induce (An_{G_X}(Y))`, of the
recovered full-district c-factors; each district c-factor is a functional of the
observational density `obsDensity` by `district_id`/`q_factor_identity`, with the
truncation realized by the *fixing* mechanism (`M.fixSet Wn`, fixing the nodes
outside each district) rather than by `SCM.induce` on the ancestral set — which does
not apply because that set is not ancestrally closed in the SCM sense after the
SWIG split.  Equal `obsDensity` gives equal recovered c-factors, hence equal do-law
`Y`-marginal; the final step is the structural transport
`doKernelY_eq_of_doObsKernel_heq`.

The hypothesis is the observational *density* (not the kernel) because that is the
only part of the observational law the g-formula consumes; the `obsKernel` form is
the trivial wrapper `doObsKernelYMarginal_heq_of_obsKernel_heq` below, obtained via
`obsDensity_heq_of_obsKernel_heq`.  The conclusion is the `Y`-marginal
`doObsKernelYMarginal` rather than the full do-law `obsKernel`: the full
post-intervention joint over *all* observed nodes is not a functional of the
observational law (nodes outside the ancestral set may lie in non-identifiable
c-components), whereas its `Y`-marginal — the only part the query `P(Y ∣ do(X))` and
the transport `doKernelY` consume — is. -/
theorem doObsKernelYMarginal_heq_of_obsDensity_heq
    [∀ n, StandardBorelSpace (Ω n)] [∀ n, Nonempty (Ω n)]
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (X : Finset N) (Y : Finset (SWIGNode N)) (G : SWIGGraph N)
    (ref : ReferenceMeasures Ω)
    (href : ReferenceFaithful ref)
    (_hID : idSucceeds X Y G)
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
  -- Split off the easy `Y ← (Ystar ∩ observed)` projection; the genuine content
  -- is the observed-ancestral marginal identification.
  have hsg : M₁.toSWIGGraph = M₂.toSWIGGraph := _hsg₁.trans _hsg₂.symm
  exact doObsKernelYMarginal_heq_of_ancestralMarginal_heq X Y M₁ M₂ hsg
    hvalid₁.1 hvalid₁.2.1 hvalid₂.1 hvalid₂.2.1 hvalid₁.2.2.1 hvalid₂.2.2.1
    (doObsKernelAncestralMarginal_heq_of_obsDensity_heq X Y G ref href _hID M₁ M₂
      _hsg₁ _hsg₂ _hdom₁ _hdom₂ hpos₁ hpos₂ hYX _hden hvalid₁ hvalid₂)

/-- Two dominated models with the same SWIG graph and observational law have the same
post-intervention outcome marginal under a successful ID certificate.

The observational-law equality is first converted to equality of observational
densities, which is the form consumed by the Tian g-formula core. -/
theorem doObsKernelYMarginal_heq_of_obsKernel_heq
    [∀ n, StandardBorelSpace (Ω n)] [∀ n, Nonempty (Ω n)]
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (X : Finset N) (Y : Finset (SWIGNode N)) (G : SWIGGraph N)
    (ref : ReferenceMeasures Ω)
    (href : ReferenceFaithful ref)
    (hID : idSucceeds X Y G)
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
  -- The observational law enters the do-law `Y`-marginal *only* through its
  -- density: equal `obsKernel` gives equal `obsDensity` (`obsDensity_heq_of_obsKernel_heq`),
  -- and the g-formula core consumes that density.
  doObsKernelYMarginal_heq_of_obsDensity_heq X Y G ref href hID M₁ M₂ hsg₁ hsg₂ hdom₁ hdom₂
    hpos₁ hpos₂ hYX
    (obsDensity_heq_of_obsKernel_heq M₁ M₂ ref (hsg₁.trans hsg₂.symm) hobs)
    hvalid₁ hvalid₂

/-- The valid branch of a successful no-fixing ID certificate gives equal
interventional outcome kernels for observationally equivalent finite
discrete-positive models.

Deep analytic core isolated from `id_sound`: for two finite node-space gSCMs
sharing the SWIG graph `G`, dominated by the same faithful reference and
satisfying discrete positivity, the same observational law implies the same
post-intervention `Y`-marginal kernels.  The proof routes through the joint
density (`obsDensity`, see `Density/ReferenceMeasure.lean`): under `idSucceeds`
the do-query density is the truncated product of the recovered full-district
c-factor densities, and this product is a commutative regrouping of density
factors that the kernel composition `⊗ₖ` cannot perform.  Equal `obsKernel` gives
equal `obsDensity`, hence equal do-query density, hence equal `doKernelY`.

The finite-state and positivity hypotheses supply the atom-level density and
ratio identities used by the finite density route.  The separate
`interventionalQueryValid_iff_of_obsKernel_heq` lemma handles branch alignment. -/
theorem doKernelY_eq_cfactor_decomposition
    [∀ n, StandardBorelSpace (Ω n)] [∀ n, Nonempty (Ω n)]
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (X : Finset N) (Y : Finset (SWIGNode N)) (G : SWIGGraph N)
    (ref : ReferenceMeasures Ω)
    (href : ReferenceFaithful ref)
    (_hID : idSucceeds X Y G)
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
    (doObsKernelYMarginal_heq_of_obsKernel_heq X Y G ref href _hID M₁ M₂ _hsg₁ _hsg₂
      _hdom₁ _hdom₂ hpos₁ hpos₂ hYX _hobs hvalid₁ hvalid₂)

/-- A successful structural ID certificate makes the interventional outcome
kernel identifiable from the observational law within the dominated positive
finite-reference model class.

Dominance and discrete positivity are carried as the structural assumption `As`
of `IdentifiableUnder`; domination makes the density-assisted Tian assembly
available, while positivity supplies the nonzero point masses needed by the
ratio identities.  Proof: branch alignment
(`interventionalQueryValid_iff_of_obsKernel_heq`) reduces to the valid branch,
where `doKernelY_eq_cfactor_decomposition` performs the density-level c-factor
decomposition; the invalid branch returns the fixed fallback kernel for both.

This is soundness of the `idSucceeds` no-additional-fixing approximation.  The
full recursive Tian-Shpitser-Pearl certificate is handled by `id_sound_rec`; this
theorem uses the Tian c-factor core in `SCM/ID/Density/MechCFactor.lean` and
`SCM/ID/Density/QFactor.lean`. -/
theorem id_sound [∀ n, StandardBorelSpace (Ω n)] [∀ n, Nonempty (Ω n)]
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (X : Finset N) (Y : Finset (SWIGNode N)) (G : SWIGGraph N)
    (ref : ReferenceMeasures Ω) (href : ReferenceFaithful ref) :
    idSucceeds X Y G →
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
    exact doKernelY_eq_cfactor_decomposition
      (Ω := Ω) X Y G ref href hID M₁ M₂ hsg₁ hsg₂ hM₁.1 hM₂.1 hM₁.2 hM₂.2 hYX
      hobs hvalid₁ hvalid₂
  · have hvalid₂ : ¬ interventionalQueryValid X Y M₂ := by
      intro h
      exact hvalid₁ (hvalid_iff.mpr h)
    rw [interventionalQuery_eq_default_of_not_valid (Ω := Ω) X Y M₁ hvalid₁,
      interventionalQuery_eq_default_of_not_valid (Ω := Ω) X Y M₂ hvalid₂]

end Causalean.SCM.ID
