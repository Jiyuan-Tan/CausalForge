/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Induced sub-SCM with restricted latent roots

Implementation of an induced sub-SCM construction on an ancestrally closed node
set.  This version restricts observed and fixed nodes according to the induced
SWIG graph and keeps exactly the original latent roots that feed the retained
observed nodes.

## Main declarations

* `SCM.isAncestrallyClosedSCM` — two-clause ancestral closure:
  (a) observed-ancestor closure, (b) pairing closure under `iotaMap`.
  Stricter than `SWIGGraph.isAncestrallyClosed` from
  `SCM/ID/GraphicalThms/InducedSubgraph.lean`; kept here so
  existing graphical theorems are not perturbed.
* `SCM.induce` — the induced sub-SCM `M|_R` for an ancestrally closed
  `R`, with inherited structural functions and restricted latent
  distributions.
* `SCM.induce_marginal_compat` — kernel-level marginal compatibility:
  the induced observational kernel is the `valuesProjection` pushforward
  of the original observational kernel.  The latent-product marginal bridge
  is proved internally from the product-measure projection lemma.
-/

import Causalean.SCM.Model.SCM
import Causalean.SCM.Model.Kernel
import Causalean.Graph.Induce

/-! # Induced Structural Causal Models

This file defines ancestral closure for structural causal models and states an
induced submodel construction on an ancestrally closed set of nodes. The
construction supports marginal-compatibility results that relate a submodel to
the original structural causal model.

## Main definitions and results

* `SCM.isAncestrallyClosedSCM` is the observed-parent and fixed-counterpart
  closure condition needed to inherit structural functions.
* `SCM.induce` builds the induced sub-SCM on an ancestrally closed node set.
* `SCM.measure_pi_map_valuesProjection` and `SCM.induce_latentProduct_eq_map`
  identify the latent product of the induced model as a projected product
  measure.
* `SCM.induce_evalMap_compat` compares evaluation in the induced model with
  evaluation in the original model.
* `SCM.induce_marginal_compat` proves the observational-kernel marginal
  compatibility theorem for induced submodels.
-/

namespace Causalean

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

open scoped ENNReal MeasureTheory ProbabilityTheory

namespace SCM

-- ============================================================
-- § 1. Ancestral closure for SCMs
-- ============================================================

/-- `R ⊆ V ∪ S ∪ L` is **ancestrally closed** in the SCM sense if it
    satisfies both clauses of `def:scm-anc-closed`:

    (a) **Observed-ancestor closure.** For every `v ∈ R` and every
    observed parent `v' ∈ Pa_G(v) ∩ V`, we have `v' ∈ R`.

    (b) **Pairing closure.** For every `v ∈ R` and every fixed parent
    `d ∈ Pa_G(v) ∩ S`, the random counterpart `iotaMap d ∈ R`.

    This is stricter than `SWIGGraph.isAncestrallyClosed` in
    `SCM/ID/GraphicalThms/InducedSubgraph.lean`, which encodes
    only clause (a). -/
def isAncestrallyClosedSCM (M : Causalean.SCM N Ω) (R : Finset (SWIGNode N)) : Prop :=
  (∀ v ∈ R, ∀ v' ∈ M.dag.parents v, v' ∈ M.observed → v' ∈ R) ∧
  (∀ v ∈ R, ∀ d ∈ M.dag.parents v, d ∈ M.fixed → Causalean.iotaMap d ∈ R)

-- ============================================================
-- § 2. Induced sub-SCM
-- ============================================================

/-- Under ancestral closure, every parent (in `M`) of a node `v` in the induced
    observed set survives into the induced DAG: the induced parent set equals
    the original one.  This is the formal content of the footnote on
    `def:scm-induced-sub` in Basic Concepts.tex line 309 — inheriting `structFun`
    unchanged is well-defined *because* `R` is ancestrally closed. -/
private lemma induce_parents_eq_of_ancClosed (M : Causalean.SCM N Ω)
    (R : Finset (SWIGNode N)) (hR : M.isAncestrallyClosedSCM R)
    {v : SWIGNode N} (hv : v ∈ (M.toSWIGGraph.induce R).observed) :
    (M.toSWIGGraph.induce R).dag.parents v = M.dag.parents v := by
  classical
  have hvInter : v ∈ R ∩ M.observed := hv
  have hvR : v ∈ R := (Finset.mem_inter.mp hvInter).1
  have hvMObs : v ∈ M.observed := (Finset.mem_inter.mp hvInter).2
  -- `v` lives in the induced active set via the `newObserved` summand.
  have hvActive :
      v ∈ (M.toSWIGGraph.fixed.filter
              (fun s => Causalean.iotaMap s ∈ R ∩ M.observed))
            ∪ (R ∩ M.observed) ∪
              (M.toSWIGGraph.unobserved.filter
                (fun u => ∃ w ∈ R ∩ M.observed, M.toSWIGGraph.dag.edge u w)) := by
    refine Finset.mem_union_left _ ?_
    exact Finset.mem_union_right _ hvInter
  apply Finset.Subset.antisymm
  · exact M.toSWIGGraph.inducedDag_parents_subset _ v
  · intro u huM
    have huEdge : M.dag.edge u v := M.dag.mem_parents.mp huM
    have huClass : u ∈ M.fixed ∪ M.observed ∪ M.unobserved :=
      (M.dag_edges_classified u v huEdge).1
    have huActive :
        u ∈ (M.toSWIGGraph.fixed.filter
                (fun s => Causalean.iotaMap s ∈ R ∩ M.observed))
              ∪ (R ∩ M.observed) ∪
                (M.toSWIGGraph.unobserved.filter
                  (fun u => ∃ w ∈ R ∩ M.observed, M.toSWIGGraph.dag.edge u w)) := by
      rcases Finset.mem_union.mp huClass with hu | hu
      · rcases Finset.mem_union.mp hu with huFix | huObs
        · -- `u ∈ M.fixed`: use pairing closure (clause b).
          have hIotaR : Causalean.iotaMap u ∈ R := hR.2 v hvR u huM huFix
          have hIotaObs : Causalean.iotaMap u ∈ M.observed :=
            M.fixed_image_in_observed u huFix
          have hIotaNewObs : Causalean.iotaMap u ∈ R ∩ M.observed :=
            Finset.mem_inter.mpr ⟨hIotaR, hIotaObs⟩
          have huNewFixed :
              u ∈ M.toSWIGGraph.fixed.filter
                    (fun s => Causalean.iotaMap s ∈ R ∩ M.observed) :=
            Finset.mem_filter.mpr ⟨huFix, hIotaNewObs⟩
          exact Finset.mem_union_left _ (Finset.mem_union_left _ huNewFixed)
        · -- `u ∈ M.observed`: use observed-ancestor closure (clause a).
          have huR : u ∈ R := hR.1 v hvR u huM huObs
          have huNewObs : u ∈ R ∩ M.observed := Finset.mem_inter.mpr ⟨huR, huObs⟩
          exact Finset.mem_union_left _ (Finset.mem_union_right _ huNewObs)
      · -- `u ∈ M.unobserved`: a latent parent of retained `v` survives the latent filter.
        exact Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨hu, v, hvInter, huEdge⟩)
    refine (M.toSWIGGraph.induce R).dag.mem_parents.mpr ?_
    exact ⟨huEdge, huActive, hvActive⟩

/-- The induced sub-SCM for an ancestrally closed node set keeps the observed
    and fixed parts selected by the induced SWIG graph and keeps exactly the
    original latent roots that feed retained observed nodes.

    The underlying SWIG graph is `M.toSWIGGraph.induce R`. Value spaces,
    structural functions on the retained observed nodes, and each retained
    latent distribution are inherited from `M` unchanged; ancestral closure is
    what makes the structural functions well-defined. -/
noncomputable def induce (M : Causalean.SCM N Ω) (R : Finset (SWIGNode N))
    (hR : M.isAncestrallyClosedSCM R) : Causalean.SCM N Ω :=
  let G : SWIGGraph N := M.toSWIGGraph.induce R
  -- `G.observed = R ∩ M.observed ⊆ M.observed`
  have hObs : G.observed ⊆ M.observed := Finset.inter_subset_right
  -- `G.fixed ⊆ M.fixed` by construction (it's a `filter`)
  have hFix : G.fixed ⊆ M.fixed := Finset.filter_subset _ _
  -- `G.unobserved ⊆ M.unobserved` by construction (it's a `filter`).
  have hUnobs : G.unobserved ⊆ M.unobserved := by
    intro u hu
    simpa [G, SWIGGraph.induce] using (Finset.mem_filter.mp hu).1
  { toSWIGGraph := G
    edgeTypes := { edgeType := fun u v => M.edgeTypes.edgeType u v }
    iota_valueSpace := fun s => M.iota_valueSpace ⟨s.val, hFix s.property⟩
    -- Structural functions are inherited unchanged.  Ancestral closure
    -- (via `induce_parents_eq_of_ancClosed`) ensures that the induced parent
    -- set coincides with the original, so the parent tuple fed to `M.structFun`
    -- is obtained by a coordinate-level rewrite with no pruning.
    structFun := fun v parentVals =>
      M.structFun ⟨v.val, hObs v.property⟩ fun w =>
        parentVals ⟨w.val, by
          rw [induce_parents_eq_of_ancClosed M R hR v.property]
          exact w.property⟩
    structFun_measurable := fun v => by
      refine (M.structFun_measurable ⟨v.val, hObs v.property⟩).comp ?_
      refine measurable_pi_lambda _ (fun w => ?_)
      exact measurable_pi_apply _
    -- Retained latent roots inherit their original distributions.
    latentDist := fun u => M.latentDist ⟨u.val, hUnobs u.property⟩
    isProbability_latent := fun u => M.isProbability_latent ⟨u.val, hUnobs u.property⟩ }

/-- The latent roots of an induced sub-SCM are original latent roots. -/
lemma induce_unobserved_subset (M : Causalean.SCM N Ω) (R : Finset (SWIGNode N))
    (hR : M.isAncestrallyClosedSCM R) :
    (M.induce R hR).unobserved ⊆ M.unobserved := by
  intro u hu
  simpa [SCM.induce, SWIGGraph.induce] using (Finset.mem_filter.mp hu).1

/-- Product measures marginalize under coordinate restriction.

    If `J ⊆ I`, pushing the finite product measure on assignments over `I`
    through coordinate restriction to `J` gives exactly the product measure over
    the retained coordinates, with the same one-coordinate laws. -/
lemma measure_pi_map_valuesProjection {I J : Finset (SWIGNode N)} (hJI : J ⊆ I)
    (μ : (i : {i // i ∈ I}) → MeasureTheory.Measure (swigΩ Ω i.val))
    [∀ i, MeasureTheory.IsProbabilityMeasure (μ i)] :
    (MeasureTheory.Measure.pi μ).map (valuesProjection (Ω := swigΩ Ω) hJI) =
      MeasureTheory.Measure.pi
        (fun j : {j // j ∈ J} => μ ⟨j.val, hJI j.property⟩) := by
  classical
  symm
  refine MeasureTheory.Measure.pi_eq (fun s hs => ?_)
  rw [MeasureTheory.Measure.map_apply (measurable_valuesProjection hJI) (.univ_pi hs)]
  let t : (i : {i // i ∈ I}) → Set (swigΩ Ω i.val) :=
    fun i => if h : i.val ∈ J then s ⟨i.val, h⟩ else Set.univ
  have hpre : valuesProjection (Ω := swigΩ Ω) hJI ⁻¹' Set.pi Set.univ s =
      Set.pi Set.univ t := by
    ext x
    constructor
    · intro hx a _haI
      by_cases haJ : a.val ∈ J
      · have hxj := hx ⟨a.val, haJ⟩ (Set.mem_univ _)
        simpa [t, valuesProjection, haJ] using hxj
      · simp [t, haJ]
    · intro hx a _haJ
      have hxi := hx ⟨a.val, hJI a.property⟩ (Set.mem_univ _)
      simpa [t, valuesProjection, a.property] using hxi
  rw [hpre]
  rw [MeasureTheory.Measure.pi_pi]
  let g : SWIGNode N → ℝ≥0∞ :=
    fun a => if h : a ∈ J then μ ⟨a, hJI h⟩ (s ⟨a, h⟩) else 1
  have hleft : (∏ i, μ i (t i)) = ∏ a ∈ I, g a := by
    calc
      (∏ i : {i // i ∈ I}, μ i (t i)) = ∏ i : {i // i ∈ I}, g i.val := by
        refine Fintype.prod_congr _ _ ?_
        intro i
        by_cases hiJ : i.val ∈ J
        · simp [g, t, hiJ]
        · simp [g, t, hiJ]
      _ = ∏ a ∈ I, g a := Finset.prod_coe_sort (s := I) (f := g)
  have hright : (∏ j : {j // j ∈ J}, μ ⟨j.val, hJI j.property⟩ (s j)) =
      ∏ a ∈ J, g a := by
    calc
      (∏ j : {j // j ∈ J}, μ ⟨j.val, hJI j.property⟩ (s j)) =
          ∏ j : {j // j ∈ J}, g j.val := by
        refine Fintype.prod_congr _ _ ?_
        intro j
        simp [g, j.property]
      _ = ∏ a ∈ J, g a := Finset.prod_coe_sort (s := J) (f := g)
  rw [hleft, hright]
  exact (Finset.prod_subset_one_on_sdiff hJI (fun a ha => by
    have haJ : a ∉ J := (Finset.mem_sdiff.mp ha).2
    simp [g, haJ]) (fun a ha => by simp [g, ha])).symm

/-- The latent product of an induced sub-SCM is the marginal of the original
    latent product.

    Projecting the original independent latent-root product measure to the
    latent roots retained by `M.induce R hR` gives the induced model's latent
    product measure. -/
lemma induce_latentProduct_eq_map (M : Causalean.SCM N Ω) (R : Finset (SWIGNode N))
    (hR : M.isAncestrallyClosedSCM R) :
    (M.induce R hR).latentProduct =
      M.latentProduct.map (valuesProjection (induce_unobserved_subset M R hR)) := by
  classical
  haveI hprob :
      ∀ u : {u // u ∈ M.unobserved}, MeasureTheory.IsProbabilityMeasure (M.latentDist u) :=
    M.isProbability_latent
  rw [SCM.latentProduct, SCM.latentProduct]
  rw [measure_pi_map_valuesProjection (hJI := induce_unobserved_subset M R hR)
    (μ := fun u : {u // u ∈ M.unobserved} => M.latentDist u)]
  simp [SCM.induce]

-- ============================================================
-- § 2b. Evaluation-map bridge for the induced sub-SCM
-- ============================================================

/-- **Evaluation-map bridge** for the induced sub-SCM.  At every random node `v`
    retained by `M.induce R hR`, the induced `evalMap` at the restricted fixing
    `sTilde|_R` and the projected latent assignment computes the same value as
    the original `evalMap` at `sTilde`.

    Proof by strong recursion on the induced `observedIndex` of `v` (for the observed
    branch; the unobserved branch is the coordinate projection from original
    latent assignments to retained latent roots).

    The key structural ingredients:
    * `(M.induce).structFun v` is literally `M.structFun ⟨v, hvMObs⟩` composed with the
      `induce_parents_eq_of_ancClosed` reindexing.
    * Ancestral closure (clauses (a) and (b)) matches the induced parent classification
      (unobserved / fixed / observed) with `M`'s at every parent of every `v ∈ R ∩ M.observed`.
    * The observed-parent recursive call closes by IH at the induced observedIndex. -/
lemma induce_evalMap_compat (M : Causalean.SCM N Ω) (R : Finset (SWIGNode N))
    (hR : M.isAncestrallyClosedSCM R) (sTilde : FixedValues M) (ℓ : LatentValues M) :
    ∀ {v : SWIGNode N} (hvI : v ∈ (M.induce R hR).randomVars) (hvM : v ∈ M.randomVars),
      (M.induce R hR).evalMap
          (valuesProjection (Finset.filter_subset _ _) sTilde)
          (valuesProjection (induce_unobserved_subset M R hR) ℓ) ⟨v, hvI⟩
        = M.evalMap sTilde ℓ ⟨v, hvM⟩ := by
  classical
  -- Reduce to the observed-strong-recursion form.
  suffices h_obs : ∀ (n : ℕ), ∀ (v : SWIGNode N) (hvI : v ∈ (M.induce R hR).observed),
      ((M.induce R hR).observedIndex ⟨v, hvI⟩).val = n →
      (M.induce R hR).evalMap
          (valuesProjection (Finset.filter_subset _ _) sTilde)
          (valuesProjection (induce_unobserved_subset M R hR) ℓ)
          ⟨v, Finset.mem_union_left _ hvI⟩
        = M.evalMap sTilde ℓ
          ⟨v, Finset.mem_union_left _ (Finset.inter_subset_right hvI)⟩ by
    intro v hvI hvM
    -- Dispatch: `v` is either observed or unobserved in the induced SCM.
    rcases Finset.mem_union.mp hvI with hvIObs | hvIUo
    · -- Observed case: apply the strong-recursion helper.
      have := h_obs _ v hvIObs rfl
      -- Witness equality for `hvM` via proof irrelevance.
      convert this using 2
    · -- Unobserved case: both sides unfold to the projected original latent coordinate.
      have hvMUo : v ∈ M.unobserved := induce_unobserved_subset M R hR hvIUo
      rw [SCM.evalMap_unobserved (M.induce R hR) _
          (valuesProjection (induce_unobserved_subset M R hR) ℓ) ⟨v, hvI⟩ hvIUo]
      rw [SCM.evalMap_unobserved M sTilde ℓ ⟨v, hvM⟩ hvMUo]
      rfl
  -- Strong recursion on `n = (M.induce R hR).observedIndex ⟨v, hvI⟩`.
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro v hvI hidx
    have hvMObs : v ∈ M.observed := Finset.inter_subset_right hvI
    have hvR : v ∈ R := (Finset.mem_inter.mp hvI).1
    have h_parents_eq : (M.induce R hR).dag.parents v = M.dag.parents v :=
      induce_parents_eq_of_ancClosed M R hR hvI
    -- Unfold both `evalMap`s via the proved recursive-form helper from
    -- Evaluation.lean.
    rw [SCM.evalMap_observed_unfold (M.induce R hR) _
          (valuesProjection (induce_unobserved_subset M R hR) ℓ) ⟨v, hvI⟩,
        SCM.evalMap_observed_unfold M sTilde ℓ ⟨v, hvMObs⟩]
    -- LHS: (M.induce R hR).structFun ⟨v, hvI⟩ (if-else-dispatch-induced)
    -- RHS: M.structFun ⟨v, hvMObs⟩ (if-else-dispatch-M)
    -- Unfold (M.induce R hR).structFun via the `SCM.induce` definition (beta reduction).
    change M.structFun ⟨v, hvMObs⟩
        (fun w : {w // w ∈ M.dag.parents v} =>
          if huo : w.val ∈ (M.induce R hR).unobserved then
            valuesProjection (induce_unobserved_subset M R hR) ℓ ⟨w.val, huo⟩
          else if hfix : w.val ∈ (M.induce R hR).fixed then
            valuesProjection (Finset.filter_subset _ _) sTilde ⟨w.val, hfix⟩
          else
            have hedge : (M.induce R hR).dag.edge w.val v :=
              (M.induce R hR).dag.mem_parents.mp (h_parents_eq.symm ▸ w.property)
            have hobs : w.val ∈ (M.induce R hR).observed := by
              rcases Finset.mem_union.mp
                ((M.induce R hR).dag_edges_classified _ _ hedge).1 with h1 | h2
              · rcases Finset.mem_union.mp h1 with hfx | hob
                · exact absurd hfx hfix
                · exact hob
              · exact absurd h2 huo
            (M.induce R hR).evalMap
                (valuesProjection (Finset.filter_subset _ _) sTilde)
                (valuesProjection (induce_unobserved_subset M R hR) ℓ)
                ⟨w.val, Finset.mem_union_left _ hobs⟩)
      = M.structFun ⟨v, hvMObs⟩ (fun w : {w // w ∈ M.dag.parents v} =>
          if huo : w.val ∈ M.unobserved then ℓ ⟨w.val, huo⟩
          else if hfix : w.val ∈ M.fixed then sTilde ⟨w.val, hfix⟩
          else
            have hedge : M.dag.edge w.val v := M.dag.mem_parents.mp w.property
            have hobs : w.val ∈ M.observed := by
              rcases Finset.mem_union.mp (M.dag_edges_classified _ _ hedge).1 with h1 | h2
              · rcases Finset.mem_union.mp h1 with hfx | hob
                · exact absurd hfx hfix
                · exact hob
              · exact absurd h2 huo
            M.evalMap sTilde ℓ ⟨w.val, Finset.mem_union_left _ hobs⟩)
    congr 1
    funext w
    -- Per-parent three-way case split.
    have hedge_M : M.dag.edge w.val v := M.dag.mem_parents.mp w.property
    have hcls : w.val ∈ M.fixed ∪ M.observed ∪ M.unobserved :=
      (M.dag_edges_classified _ _ hedge_M).1
    by_cases huo : w.val ∈ M.unobserved
    · -- Unobserved parent of a retained observed node is retained by the induced
      -- latent filter.
      have huoInd : w.val ∈ (M.induce R hR).unobserved := by
        change w.val ∈ M.unobserved.filter
          (fun u => ∃ z ∈ R ∩ M.observed, M.dag.edge u z)
        exact Finset.mem_filter.mpr ⟨huo, v, hvI, hedge_M⟩
      rw [dif_pos huo, dif_pos huoInd]
      change ℓ ⟨w.val, induce_unobserved_subset M R hR huoInd⟩ = ℓ ⟨w.val, huo⟩
      congr
    · have huoInd : w.val ∉ (M.induce R hR).unobserved := by
        intro h
        exact huo (induce_unobserved_subset M R hR h)
      rw [dif_neg huo, dif_neg huoInd]
      by_cases hfix : w.val ∈ M.fixed
      · -- Fixed: by ancestral closure clause (b), `iotaMap w ∈ R ∩ M.observed`, so
        -- `w ∈ (M.induce R hR).fixed` (the filter witness).
        have hIotaR : Causalean.iotaMap w.val ∈ R := hR.2 v hvR w.val w.property hfix
        have hIotaObs : Causalean.iotaMap w.val ∈ M.observed :=
          M.fixed_image_in_observed w.val hfix
        have hIotaInter : Causalean.iotaMap w.val ∈ R ∩ M.observed :=
          Finset.mem_inter.mpr ⟨hIotaR, hIotaObs⟩
        have hfixInd : w.val ∈ (M.induce R hR).fixed := by
          change w.val ∈ M.fixed.filter (fun s => Causalean.iotaMap s ∈ R ∩ M.observed)
          exact Finset.mem_filter.mpr ⟨hfix, hIotaInter⟩
        rw [dif_pos hfix, dif_pos hfixInd]
        -- `(sTilde|_R) ⟨w.val, hfixInd⟩ = sTilde ⟨w.val, hfix⟩` by proof irrelevance
        -- since `valuesProjection` is `fun ξ j => ξ ⟨j.val, hJI j.property⟩`.
        rfl
      · -- Observed: by ancestral closure clause (a), `w ∈ R ∩ M.observed`, so
        -- `w ∈ (M.induce R hR).observed`.  Apply the IH at the induced index.
        have hobs : w.val ∈ M.observed := by
          rcases Finset.mem_union.mp hcls with h1 | h2
          · rcases Finset.mem_union.mp h1 with hfx | hob
            · exact absurd hfx hfix
            · exact hob
          · exact absurd h2 huo
        have hobsR : w.val ∈ R := hR.1 v hvR w.val w.property hobs
        have hobsInd : w.val ∈ (M.induce R hR).observed := by
          change w.val ∈ R ∩ M.observed
          exact Finset.mem_inter.mpr ⟨hobsR, hobs⟩
        have hfixInd : w.val ∉ (M.induce R hR).fixed := by
          intro h
          exact absurd ((Finset.mem_filter.mp h).1) hfix
        rw [dif_neg hfix, dif_neg hfixInd]
        -- Apply strong-recursion IH at `w.val` on the induced side.
        have hidx_w : ((M.induce R hR).observedIndex ⟨w.val, hobsInd⟩).val
                        < ((M.induce R hR).observedIndex ⟨v, hvI⟩).val := by
          have hedge_ind : (M.induce R hR).dag.edge w.val v :=
            (M.induce R hR).dag.mem_parents.mp (h_parents_eq.symm ▸ w.property)
          -- Reindex the target of `hedge_ind` through `observedAt_observedIndex`.
          have hv_eq : ((M.induce R hR).observedAt
              ⟨((M.induce R hR).observedIndex ⟨v, hvI⟩).val,
               ((M.induce R hR).observedIndex ⟨v, hvI⟩).isLt⟩).val = v := by
            have := (M.induce R hR).observedAt_observedIndex ⟨v, hvI⟩
            convert this
          have hedge_ind' : (M.induce R hR).dag.edge w.val
              ((M.induce R hR).observedAt
                ⟨((M.induce R hR).observedIndex ⟨v, hvI⟩).val,
                 ((M.induce R hR).observedIndex ⟨v, hvI⟩).isLt⟩).val := by
            rw [hv_eq]; exact hedge_ind
          exact (M.induce R hR).observed_parent_index_lt
            ((M.induce R hR).observedIndex ⟨v, hvI⟩).isLt hedge_ind' hobsInd
        rw [hidx] at hidx_w
        exact ih _ hidx_w w.val hobsInd rfl

-- ============================================================
-- § 3. Marginal compatibility
-- ============================================================

/-- **Marginal compatibility of the induced sub-SCM**
    (`prop:scm-induced-marginal`).

    For any ancestrally closed `R ⊆ V ∪ S ∪ L` and any extension
    `s̃ : FixedValues M` of the restricted fixing on `S|_R`, the observational
    kernel of the induced sub-SCM at the restricted `s` equals the projection
    of `M.obsKernel s̃` onto the induced observed coordinates
    `R ∩ M.observed`. Both sides are measures on
    `ObservedValues (M.induce R hR)`.

    The proof unfolds both observational kernels to latent pushforwards,
    proves the latent-product marginal internally, composes the projections,
    and closes with `induce_evalMap_compat`. -/
theorem induce_marginal_compat
    (M : Causalean.SCM N Ω) (R : Finset (SWIGNode N))
    (hR : M.isAncestrallyClosedSCM R)
    (sTilde : FixedValues M) :
    (M.induce R hR).obsKernel
        (valuesProjection (Finset.filter_subset _ _) sTilde) =
      (M.obsKernel sTilde).map
        (valuesProjection
          (show (M.induce R hR).observed ⊆ M.observed from
            Finset.inter_subset_right)) := by
  classical
  -- Measurability of the components.
  let MI := M.induce R hR
  have hf_M : Measurable (fun ℓ : LatentValues M => M.evalMap sTilde ℓ) := by
    exact M.evalMap_measurable.comp (Measurable.prodMk measurable_const measurable_id)
  have hf_I : Measurable (fun ℓ : MI.LatentValues =>
      MI.evalMap (valuesProjection (Finset.filter_subset _ _) sTilde) ℓ) := by
    exact MI.evalMap_measurable.comp (Measurable.prodMk measurable_const measurable_id)
  have hRTO_M : Measurable M.randomToObserved := M.measurable_randomToObserved
  have hRTO_I : Measurable MI.randomToObserved := MI.measurable_randomToObserved
  have hπ : Measurable (valuesProjection
      (show MI.observed ⊆ M.observed from Finset.inter_subset_right)
      : ObservedValues M → ObservedValues MI) := by
    refine measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  have hLatentProj :
      Measurable (valuesProjection (induce_unobserved_subset M R hR)
        : LatentValues M → LatentValues MI) :=
    measurable_valuesProjection (induce_unobserved_subset M R hR)
  have hLatent : MI.latentProduct =
      M.latentProduct.map (valuesProjection (induce_unobserved_subset M R hR)) := by
    simpa [MI] using induce_latentProduct_eq_map M R hR
  have hFI : Measurable
      (MI.randomToObserved ∘
        (fun ℓ : LatentValues MI =>
          MI.evalMap (valuesProjection (Finset.filter_subset _ _) sTilde) ℓ)) :=
    hRTO_I.comp hf_I
  -- Step 1: Unfold both obsKernels to `latentProduct.map (composition)`.
  -- LHS: MI.obsKernel (sTilde|_R) = MI.jointKernel (sTilde|_R) |>.map randomToObserved_I
  --     = (MI.latentProduct.map (MI.evalMap (sTilde|_R))) |>.map randomToObserved_I
  -- RHS: (M.obsKernel sTilde).map π = ((M.jointKernel sTilde).map randomToObserved_M).map π
  --     = (M.latentProduct.map (M.evalMap sTilde)).map (π ∘ randomToObserved_M)
  unfold obsKernel
  rw [ProbabilityTheory.Kernel.map_apply _ hRTO_I,
      ProbabilityTheory.Kernel.map_apply _ hRTO_M,
      jointKernel_apply_eq MI (valuesProjection (Finset.filter_subset _ _) sTilde),
      jointKernel_apply_eq M sTilde]
  -- Step 2: Compose maps via Measure.map_map.
  rw [MeasureTheory.Measure.map_map hRTO_I hf_I,
      MeasureTheory.Measure.map_map hRTO_M hf_M,
      MeasureTheory.Measure.map_map hπ (hRTO_M.comp hf_M)]
  -- Step 3: replace the induced latent product by the projected original
  -- latent product and compose maps once more.
  rw [hLatent, MeasureTheory.Measure.map_map hFI hLatentProj]
  -- Step 4: Close via funext + induce_evalMap_compat.
  congr 1
  funext ℓ
  -- Goal: (MI.randomToObserved ∘ MI.evalMap (sTilde|_R) ∘ latentProjection) ℓ
  --     = (π ∘ M.randomToObserved ∘ M.evalMap sTilde) ℓ
  -- Both sides are ObservedValues MI.
  simp only [Function.comp_apply]
  -- Goal: MI.randomToObserved (MI.evalMap (sTilde|_R) ℓ)
  --     = π (M.randomToObserved (M.evalMap sTilde ℓ))
  -- Expand randomToObserved and π as functions on observed subtypes.
  funext v
  -- v : { v // v ∈ MI.observed }
  -- Each side evaluates to an evalMap value at v.
  simp only [randomToObserved, valuesProjection]
  -- Goal: MI.evalMap (sTilde|_R) ℓ ⟨v.val, mem_union_left _ v.property⟩
  --     = M.evalMap sTilde ℓ ⟨v.val, mem_union_left _ (inter_subset_right v.property)⟩
  exact induce_evalMap_compat M R hR sTilde ℓ
    (Finset.mem_union_left _ v.property)
    (Finset.mem_union_left _ (Finset.inter_subset_right v.property))

end SCM

end Causalean
