/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Discovery.InvariantPrediction.Model
import Causalean.Mathlib.CondDistrib
import Causalean.Mathlib.Probability.Kernel.GraphMapProd
import Causalean.SCM.Model.EvalFactorization
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Mechanism-factor helpers for invariant prediction

This file isolates the measure-theoretic and structural helper facts used by
`EnvFamily.mechanism_invariant`: the target mechanism factors through its observed
parents, latent parents, and an explicit fixed-parent value argument.  This
parameterized fixed-parent kernel supports comparing environments without requiring
their fixed-parent assignments to agree.

The main ingredients are:

* `paLat` and `paLat_eq`, the latent parents of the target and their
  environment-independence;
* `mechanismFun` and `mechanismFunCf`, the target structural function as a map of
  observed, latent, and fixed parent values;
* `condDistrib_eq_mechanismKernel_of_indep`, the abstract conditional-law
  factorization under independence of latent noise and predictors;
* `condDistrib_target_eq_mechanismKernel`, the per-environment specialization to
  the target conditional law; and
* `mechanismKernel_cf_env_eq`, the cross-environment equality of the
  fixed-parent-parameterized mechanism kernels.
-/

namespace Causalean.Discovery.InvariantPrediction

open Causalean MeasureTheory ProbabilityTheory

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

namespace EnvFamily

variable {ι : Type*} [Fintype ι]

/-- The latent parents of the target in environment `i`. -/
def paLat (F : EnvFamily N Ω ι) (i : ι) : Finset (SWIGNode N) :=
  (F.M i).dag.parents F.yNode ∩ (F.M i).unobserved

/-- The latent-parent set is environment-independent. -/
theorem paLat_eq (F : EnvFamily N Ω ι) (i j : ι) : F.paLat i = F.paLat j := by
  unfold paLat
  rw [F.hParents i j, F.hUnobs i j]

/-- Observed-coordinate projection after `randomToObserved` is the same as the
corresponding random-coordinate projection. -/
theorem valuesProjection_randomToObserved_eq
    (M : Causalean.SCM N Ω) (S : Finset (SWIGNode N))
    (hSobs : S ⊆ M.observed) (hSrv : S ⊆ M.randomVars) :
    valuesProjection hSobs ∘ M.randomToObserved =
      (valuesProjection hSrv : M.RandomValues → ValuesOn S (swigΩ Ω)) := by
  funext ξ s
  rfl

/-- The observed marginal of `obsKernel` is the corresponding random marginal of
`jointKernel`. -/
theorem obsKernel_map_valuesProjection_eq_jointKernel_map
    (M : Causalean.SCM N Ω) (s : M.FixedValues) (S : Finset (SWIGNode N))
    (hSobs : S ⊆ M.observed) (hSrv : S ⊆ M.randomVars) :
    (M.obsKernel s).map (valuesProjection hSobs) =
      (M.jointKernel s).map (valuesProjection hSrv) := by
  have hcomp := valuesProjection_randomToObserved_eq M S hSobs hSrv
  unfold SCM.obsKernel
  rw [ProbabilityTheory.Kernel.map_apply _ M.measurable_randomToObserved]
  rw [MeasureTheory.Measure.map_map
    (measurable_valuesProjection hSobs) M.measurable_randomToObserved]
  rw [hcomp]

/-- The target mechanism as a measurable map of observed and latent parents. -/
noncomputable def mechanismFun (F : EnvFamily N Ω ι) (i₀ i : ι) :
    ValuesOn (F.paObs i₀) (swigΩ Ω) × ValuesOn (F.paLat i) (swigΩ Ω) →
      ValuesOn ({F.yNode} : Finset (SWIGNode N)) (swigΩ Ω) :=
  fun p w =>
    let val : swigΩ Ω F.yNode :=
      (F.M i).structFun ⟨F.yNode, F.hYobs i⟩
        (fun d : {d // d ∈ (F.M i).dag.parents F.yNode} =>
          if hlat : d.val ∈ (F.M i).unobserved then
            p.2 ⟨d.val, Finset.mem_inter.mpr ⟨d.property, hlat⟩⟩
          else if hfix : d.val ∈ (F.M i).fixed then
            (F.s i) ⟨d.val, hfix⟩
          else
            have hedge : (F.M i).dag.edge d.val F.yNode :=
              (F.M i).dag.mem_parents.mp d.property
            have hobs : d.val ∈ (F.M i).observed := by
              rcases Finset.mem_union.mp
                  ((F.M i).dag_edges_classified d.val F.yNode hedge).1 with hfo | hu
              · rcases Finset.mem_union.mp hfo with hf | ho
                · exact absurd hf hfix
                · exact ho
              · exact absurd hu hlat
            p.1 ⟨d.val, by
              rw [← F.paObs_eq i i₀]
              exact Finset.mem_inter.mpr ⟨d.property, hobs⟩⟩)
    cast (congrArg (swigΩ Ω) (Finset.mem_singleton.mp w.property).symm) val

/-- The target mechanism as a measurable map of observed and latent parents,
**parameterized by an explicit fixed-parent value argument** `cf`.  Identical to
`mechanismFun i₀ i` except that the fixed-parent branch reads its value from `cf`
instead of from the environment's intervention assignment `s i`.  This lets the
mechanism factor be keyed on `paFix`-values (used by the redesigned `Invariant`
witness `κ`), so cross-environment agreement no longer needs the environments to
assign the same value to a fixed parent. -/
noncomputable def mechanismFunCf (F : EnvFamily N Ω ι) (i₀ i : ι)
    (cf : ValuesOn (F.paFix i) (swigΩ Ω)) :
    ValuesOn (F.paObs i₀) (swigΩ Ω) × ValuesOn (F.paLat i) (swigΩ Ω) →
      ValuesOn ({F.yNode} : Finset (SWIGNode N)) (swigΩ Ω) :=
  fun p w =>
    let val : swigΩ Ω F.yNode :=
      (F.M i).structFun ⟨F.yNode, F.hYobs i⟩
        (fun d : {d // d ∈ (F.M i).dag.parents F.yNode} =>
          if hlat : d.val ∈ (F.M i).unobserved then
            p.2 ⟨d.val, Finset.mem_inter.mpr ⟨d.property, hlat⟩⟩
          else if hfix : d.val ∈ (F.M i).fixed then
            cf ⟨d.val, Finset.mem_inter.mpr ⟨d.property, hfix⟩⟩
          else
            have hedge : (F.M i).dag.edge d.val F.yNode :=
              (F.M i).dag.mem_parents.mp d.property
            have hobs : d.val ∈ (F.M i).observed := by
              rcases Finset.mem_union.mp
                  ((F.M i).dag_edges_classified d.val F.yNode hedge).1 with hfo | hu
              · rcases Finset.mem_union.mp hfo with hf | ho
                · exact absurd hf hfix
                · exact ho
              · exact absurd hu hlat
            p.1 ⟨d.val, by
              rw [← F.paObs_eq i i₀]
              exact Finset.mem_inter.mpr ⟨d.property, hobs⟩⟩)
    cast (congrArg (swigΩ Ω) (Finset.mem_singleton.mp w.property).symm) val

/-- At the environment's own fixed-parent values `fixedParentVals i`, the
parameterized mechanism `mechanismFunCf` coincides with the version that reads
fixed-parent values from the environment assignment. -/
theorem mechanismFunCf_fixedParentVals (F : EnvFamily N Ω ι) (i₀ i : ι) :
    F.mechanismFunCf i₀ i (F.fixedParentVals i) = F.mechanismFun i₀ i := by
  rfl

/-- `mechanismFunCf` is measurable. -/
theorem measurable_mechanismFunCf (F : EnvFamily N Ω ι) (i₀ i : ι)
    (cf : ValuesOn (F.paFix i) (swigΩ Ω)) :
    Measurable (F.mechanismFunCf i₀ i cf) := by
  classical
  refine measurable_pi_lambda _ ?_
  rintro ⟨w, hw⟩
  have hwy : w = F.yNode := Finset.mem_singleton.mp hw
  subst hwy
  apply ((F.M i).structFun_measurable ⟨F.yNode, F.hYobs i⟩).comp
  exact measurable_pi_lambda _ (fun d => by
      by_cases hlat : d.val ∈ (F.M i).unobserved
      · simp only [mechanismFunCf, dif_pos hlat]
        exact (measurable_pi_apply _).comp measurable_snd
      · simp only [mechanismFunCf, dif_neg hlat]
        by_cases hfix : d.val ∈ (F.M i).fixed
        · simp only [dif_pos hfix]
          exact measurable_const
        · simp only [dif_neg hfix]
          exact (measurable_pi_apply _).comp measurable_fst)

/-- `mechanismFun` is measurable. -/
theorem measurable_mechanismFun (F : EnvFamily N Ω ι) (i₀ i : ι) :
    Measurable (F.mechanismFun i₀ i) := by
  classical
  refine measurable_pi_lambda _ ?_
  rintro ⟨w, hw⟩
  have hwy : w = F.yNode := Finset.mem_singleton.mp hw
  subst hwy
  apply ((F.M i).structFun_measurable ⟨F.yNode, F.hYobs i⟩).comp
  exact measurable_pi_lambda _ (fun d => by
      by_cases hlat : d.val ∈ (F.M i).unobserved
      · simp only [mechanismFun, dif_pos hlat]
        exact (measurable_pi_apply _).comp measurable_snd
      · simp only [mechanismFun, dif_neg hlat]
        by_cases hfix : d.val ∈ (F.M i).fixed
        · simp only [dif_pos hfix]
          exact measurable_const
        · simp only [dif_neg hfix]
          exact (measurable_pi_apply _).comp measurable_fst)

/-- Pointwise structural equation for the target, expressed through
`mechanismFun` on observed and latent parents. -/
theorem target_projection_evalMap_eq_mechanismFun
    (F : EnvFamily N Ω ι) (i₀ i : ι) (ℓ : (F.M i).LatentValues) :
    valuesProjection
        (show ({F.yNode} : Finset (SWIGNode N)) ⊆ (F.M i).randomVars from by
          intro w hw
          rw [Finset.mem_singleton] at hw
          subst hw
          exact Finset.mem_union_left _ (F.hYobs i))
        ((F.M i).evalMap (F.s i) ℓ) =
      F.mechanismFun i₀ i
        (valuesProjection
          (show F.paObs i₀ ⊆ (F.M i).randomVars from by
            rw [F.paObs_eq i₀ i]
            exact (Finset.inter_subset_right).trans (by
              show (F.M i).observed ⊆ (F.M i).observed ∪ (F.M i).unobserved
              exact Finset.subset_union_left))
          ((F.M i).evalMap (F.s i) ℓ),
         valuesProjection
          (show F.paLat i ⊆ (F.M i).randomVars from by
            exact (Finset.inter_subset_right).trans (by
              show (F.M i).unobserved ⊆ (F.M i).observed ∪ (F.M i).unobserved
              exact Finset.subset_union_right))
          ((F.M i).evalMap (F.s i) ℓ)) := by
  funext w
  rcases w with ⟨w, hw⟩
  have hwy : w = F.yNode := Finset.mem_singleton.mp hw
  subst hwy
  simp only [valuesProjection]
  change (F.M i).evalMap (F.s i) ℓ
      ⟨F.yNode, Finset.mem_union_left _ (F.hYobs i)⟩ =
    F.mechanismFun i₀ i
      (valuesProjection _ ((F.M i).evalMap (F.s i) ℓ),
       valuesProjection _ ((F.M i).evalMap (F.s i) ℓ)) ⟨F.yNode, hw⟩
  rw [Causalean.SCM.evalMap_observed_unfold
    (M := F.M i) (s := F.s i) (ℓ := ℓ) (v := ⟨F.yNode, F.hYobs i⟩)]
  unfold mechanismFun
  simp only
  congr 1
  funext d
  by_cases hlat : d.val ∈ (F.M i).unobserved
  · simp only [dif_pos hlat, valuesProjection]
    rw [SCM.evalMap_unobserved]
  · simp only [dif_neg hlat]
    by_cases hfix : d.val ∈ (F.M i).fixed
    · simp only [dif_pos hfix]
    · simp only [dif_neg hfix, valuesProjection]

/-- Projecting the joint kernel to latent parents is the same as projecting the
latent product directly to those latent coordinates. -/
theorem jointKernel_map_paLat_eq_latentProduct_map
    (F : EnvFamily N Ω ι) (i : ι)
    (hLrv : F.paLat i ⊆ (F.M i).randomVars)
    (hLun : F.paLat i ⊆ (F.M i).unobserved) :
    ((F.M i).jointKernel (F.s i)).map (valuesProjection hLrv) =
      (F.M i).latentProduct.map (valuesProjection hLun) := by
  have hEvalMeas :
      Measurable (fun ℓ : (F.M i).LatentValues => (F.M i).evalMap (F.s i) ℓ) := by
    have : (fun ℓ : (F.M i).LatentValues => (F.M i).evalMap (F.s i) ℓ) =
        fun ℓ => Function.uncurry (F.M i).evalMap (F.s i, ℓ) := rfl
    rw [this]
    exact (F.M i).evalMap_measurable.comp
      (Measurable.prodMk measurable_const measurable_id)
  rw [SCM.jointKernel_apply_eq]
  rw [Measure.map_map (measurable_valuesProjection hLrv) hEvalMeas]
  congr 1
  funext ℓ x
  simp only [Function.comp_apply, valuesProjection]
  rw [SCM.evalMap_unobserved]

/-- Transport a push-forward `μ.map g` across a propositional equality of the
source type together with `HEq` of the measurable structure, the measure, and the
map.  Used to identify latent-parent push-forwards across environments whose
latent index sets coincide propositionally (via `hUnobs`) but whose `latentDist`
families and value-space typing match only up to `HEq`. -/
theorem map_heq_transport {α₁ α₂ δ : Type u}
    [mα₁ : MeasurableSpace α₁] [mα₂ : MeasurableSpace α₂] [MeasurableSpace δ]
    {μ₁ : Measure α₁} {μ₂ : Measure α₂} {g₁ : α₁ → δ} {g₂ : α₂ → δ}
    (hα : α₁ = α₂) (hm : HEq mα₁ mα₂) (hμ : HEq μ₁ μ₂) (hg : HEq g₁ g₂) :
    μ₁.map g₁ = μ₂.map g₂ := by
  subst hα; subst hm; rw [eq_of_heq hμ, eq_of_heq hg]

/-- `ValuesOn` measurable spaces transport heterogeneously across equality of
the finite index sets. -/
theorem valuesOn_measurableSpace_heq {M : Type*} [DecidableEq M] [Fintype M]
    {Ω' : M → Type*} [∀ n, MeasurableSpace (Ω' n)]
    {I J : Finset M} (h : I = J) :
    HEq (inferInstance : MeasurableSpace (ValuesOn I Ω'))
      (inferInstance : MeasurableSpace (ValuesOn J Ω')) := by
  subst h
  rfl

/-- `Measure.pi` transports heterogeneously across equality of the finite index
sets and heterogeneous equality of the coordinate measure families. -/
theorem measure_pi_heq {M : Type*}
    {Ω' : M → Type*} [∀ n, MeasurableSpace (Ω' n)]
    {I J : Finset M}
    {μI : (i : {i // i ∈ I}) → Measure (Ω' i.val)}
    {μJ : (j : {j // j ∈ J}) → Measure (Ω' j.val)}
    (h : I = J) (hμ : HEq μI μJ) :
    HEq (Measure.pi μI) (Measure.pi μJ) := by
  subst h
  have hμeq : μI = μJ := eq_of_heq hμ
  subst hμeq
  rfl

/-- Cross-environment measurable-space transport for latent value spaces. -/
theorem latentValues_measurableSpace_heq (F : EnvFamily N Ω ι) (i j : ι) :
    HEq (inferInstance : MeasurableSpace (F.M i).LatentValues)
      (inferInstance : MeasurableSpace (F.M j).LatentValues) :=
  valuesOn_measurableSpace_heq (Ω' := swigΩ Ω) (F.hUnobs i j)

/-- Cross-environment heterogeneous equality of latent product measures. -/
theorem latentProduct_heq (F : EnvFamily N Ω ι) (i j : ι) :
    HEq (F.M i).latentProduct (F.M j).latentProduct := by
  unfold SCM.latentProduct
  exact measure_pi_heq (F.hUnobs i j) (F.hLatent i j)

/-- If `X` is independent of `L` and `Y = Φ(X,L)` a.e., then the conditional
law of `Y` given `X` is the mechanism kernel obtained by pushing the marginal
law of `L` through the graph of `Φ`.

This is the measure-theoretic factorization used by `mechanism_invariant`: once
the target is generated from predictors and latent parents, and those latent
parents are independent of the predictors, conditioning on the predictors leaves
only the latent-parent marginal to integrate out.  The result only requires
standard-Borel structure on the target space `δ`, not on the conditioning or
latent spaces. -/
theorem condDistrib_eq_mechanismKernel_of_indep
    {α β γ δ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSpace δ] [StandardBorelSpace δ] [Nonempty δ]
    (μ : Measure α) [IsProbabilityMeasure μ]
    {X : α → β} {L : α → γ} {Y : α → δ} {Φ : β × γ → δ}
    (hX : Measurable X) (hL : Measurable L) (hY : Measurable Y)
    (hΦ : Measurable Φ)
    (hind : IndepFun L X μ)
    (hYeq : Y =ᵐ[μ] fun ω => Φ (X ω, L ω)) :
    (fun x => condDistrib Y X μ x)
      =ᵐ[μ.map X] Causalean.Mathlib.GraphMapProd.mechanismKernel (μ.map L) Φ := by
  classical
  haveI : IsFiniteMeasure μ := inferInstance
  haveI : IsProbabilityMeasure (μ.map L) :=
    Measure.isProbabilityMeasure_map hL.aemeasurable
  haveI : IsMarkovKernel
      (Causalean.Mathlib.GraphMapProd.mechanismKernel (μ.map L) Φ) :=
    Causalean.Mathlib.GraphMapProd.instIsMarkovKernelMechanismKernel (μ.map L) hΦ
  have hXL : Measurable (fun ω => (X ω, L ω)) := hX.prodMk hL
  have hgraph : Measurable (fun p : β × γ => (p.1, Φ p)) :=
    measurable_fst.prodMk hΦ
  have hprod :
      μ.map (fun ω => (X ω, L ω)) = (μ.map X).prod (μ.map L) :=
    (indepFun_iff_map_prod_eq_prod_map_map
      hX.aemeasurable hL.aemeasurable).mp hind.symm
  have hpair_congr :
      (fun ω => (X ω, Y ω)) =ᵐ[μ] fun ω => (X ω, Φ (X ω, L ω)) := by
    filter_upwards [hYeq] with ω hω
    rw [hω]
  refine condDistrib_ae_eq_of_measure_eq_compProd X hY.aemeasurable ?_
  calc
    μ.map (fun ω => (X ω, Y ω))
        = μ.map (fun ω => (X ω, Φ (X ω, L ω))) := Measure.map_congr hpair_congr
    _ = Measure.map (fun p : β × γ => (p.1, Φ p)) (μ.map (fun ω => (X ω, L ω))) := by
      rw [Measure.map_map hgraph hXL]
      rfl
    _ = Measure.map (fun p : β × γ => (p.1, Φ p)) ((μ.map X).prod (μ.map L)) := by
      rw [hprod]
    _ = (μ.map X).compProd
        (Causalean.Mathlib.GraphMapProd.mechanismKernel (μ.map L) Φ) :=
      Causalean.Mathlib.GraphMapProd.map_graph_prod_eq_compProd (μ.map X) (μ.map L) hΦ

/-- Variant of `condDistrib_eq_mechanismKernel_of_indep` that takes equality of
the joint `(X,Y)` push-forward measures directly.  This avoids needing a
`MeasurableEq` instance for the target when the equality is proved upstream by
unfolding a map representation of `μ`. -/
theorem condDistrib_eq_mechanismKernel_of_indep_of_pair_map
    {α β γ δ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSpace δ] [StandardBorelSpace δ] [Nonempty δ]
    (μ : Measure α) [IsProbabilityMeasure μ]
    {X : α → β} {L : α → γ} {Y : α → δ} {Φ : β × γ → δ}
    (hX : Measurable X) (hL : Measurable L) (hY : Measurable Y)
    (hΦ : Measurable Φ)
    (hind : IndepFun L X μ)
    (hpair :
      μ.map (fun ω => (X ω, Y ω)) =
        μ.map (fun ω => (X ω, Φ (X ω, L ω)))) :
    (fun x => condDistrib Y X μ x)
      =ᵐ[μ.map X] Causalean.Mathlib.GraphMapProd.mechanismKernel (μ.map L) Φ := by
  classical
  haveI : IsFiniteMeasure μ := inferInstance
  haveI : IsProbabilityMeasure (μ.map L) :=
    Measure.isProbabilityMeasure_map hL.aemeasurable
  haveI : IsMarkovKernel
      (Causalean.Mathlib.GraphMapProd.mechanismKernel (μ.map L) Φ) :=
    Causalean.Mathlib.GraphMapProd.instIsMarkovKernelMechanismKernel (μ.map L) hΦ
  have hXL : Measurable (fun ω => (X ω, L ω)) := hX.prodMk hL
  have hgraph : Measurable (fun p : β × γ => (p.1, Φ p)) :=
    measurable_fst.prodMk hΦ
  have hprod :
      μ.map (fun ω => (X ω, L ω)) = (μ.map X).prod (μ.map L) :=
    (indepFun_iff_map_prod_eq_prod_map_map
      hX.aemeasurable hL.aemeasurable).mp hind.symm
  refine condDistrib_ae_eq_of_measure_eq_compProd X hY.aemeasurable ?_
  calc
    μ.map (fun ω => (X ω, Y ω))
        = μ.map (fun ω => (X ω, Φ (X ω, L ω))) := hpair
    _ = Measure.map (fun p : β × γ => (p.1, Φ p)) (μ.map (fun ω => (X ω, L ω))) := by
      rw [Measure.map_map hgraph hXL]
      rfl
    _ = Measure.map (fun p : β × γ => (p.1, Φ p)) ((μ.map X).prod (μ.map L)) := by
      rw [hprod]
    _ = (μ.map X).compProd
        (Causalean.Mathlib.GraphMapProd.mechanismKernel (μ.map L) Φ) :=
      Causalean.Mathlib.GraphMapProd.map_graph_prod_eq_compProd (μ.map X) (μ.map L) hΦ

/-- Per-environment mechanism factorization of the target conditional law under
the joint kernel. -/
theorem condDistrib_target_eq_mechanismKernel
    (F : EnvFamily N Ω ι) (i₀ i : ι) :
    (by
      classical
      haveI : StandardBorelSpace
          (ValuesOn ({F.yNode} : Finset (SWIGNode N)) (swigΩ Ω)) := F.borelTarget
      haveI : Nonempty
          (ValuesOn ({F.yNode} : Finset (SWIGNode N)) (swigΩ Ω)) := F.neTarget
      let hYrv : ({F.yNode} : Finset (SWIGNode N)) ⊆ (F.M i).randomVars := by
        intro w hw
        rw [Finset.mem_singleton] at hw
        subst hw
        exact Finset.mem_union_left _ (F.hYobs i)
      let hPrv : F.paObs i₀ ⊆ (F.M i).randomVars := by
        rw [F.paObs_eq i₀ i]
        exact (Finset.inter_subset_right).trans (by
          show (F.M i).observed ⊆ (F.M i).observed ∪ (F.M i).unobserved
          exact Finset.subset_union_left)
      let hLrv : F.paLat i ⊆ (F.M i).randomVars := by
        exact (Finset.inter_subset_right).trans (by
          show (F.M i).unobserved ⊆ (F.M i).observed ∪ (F.M i).unobserved
          exact Finset.subset_union_right)
      exact
        (fun c => condDistrib (valuesProjection hYrv) (valuesProjection hPrv)
            ((F.M i).jointKernel (F.s i)) c)
          =ᵐ[((F.M i).jointKernel (F.s i)).map (valuesProjection hPrv)]
            Causalean.Mathlib.GraphMapProd.mechanismKernel
              (((F.M i).jointKernel (F.s i)).map (valuesProjection hLrv))
              (F.mechanismFun i₀ i)) := by
  classical
  dsimp only
  haveI : StandardBorelSpace
      (ValuesOn ({F.yNode} : Finset (SWIGNode N)) (swigΩ Ω)) := F.borelTarget
  haveI : Nonempty
      (ValuesOn ({F.yNode} : Finset (SWIGNode N)) (swigΩ Ω)) := F.neTarget
  have hYrv : ({F.yNode} : Finset (SWIGNode N)) ⊆ (F.M i).randomVars := by
    intro w hw
    rw [Finset.mem_singleton] at hw
    subst hw
    exact Finset.mem_union_left _ (F.hYobs i)
  have hPrv : F.paObs i₀ ⊆ (F.M i).randomVars := by
    rw [F.paObs_eq i₀ i]
    exact (Finset.inter_subset_right).trans (by
      show (F.M i).observed ⊆ (F.M i).observed ∪ (F.M i).unobserved
      exact Finset.subset_union_left)
  have hLrv : F.paLat i ⊆ (F.M i).randomVars := by
    exact (Finset.inter_subset_right).trans (by
      show (F.M i).unobserved ⊆ (F.M i).observed ∪ (F.M i).unobserved
      exact Finset.subset_union_right)
  have hObsExo :
      (F.M i).dag.parents F.yNode ∩ (F.M i).observed ⊆ (F.M i).randomVars :=
    (Finset.inter_subset_right).trans (by
      show (F.M i).observed ⊆ (F.M i).observed ∪ (F.M i).unobserved
      exact Finset.subset_union_left)
  have hLatExo :
      (F.M i).dag.parents F.yNode ∩ (F.M i).unobserved ⊆ (F.M i).randomVars :=
    (Finset.inter_subset_right).trans (by
      show (F.M i).unobserved ⊆ (F.M i).observed ∪ (F.M i).unobserved
      exact Finset.subset_union_right)
  let e := valuesEquivOfEq (Ω := swigΩ Ω) (F.paObs_eq i i₀)
  have hOcomp :
      e ∘ (valuesProjection hObsExo :
        (F.M i).RandomValues → ValuesOn (F.paObs i) (swigΩ Ω)) =
      (valuesProjection hPrv :
        (F.M i).RandomValues → ValuesOn (F.paObs i₀) (swigΩ Ω)) := by
    funext ξ x
    rfl
  have hLcomp :
      (valuesProjection hLatExo :
        (F.M i).RandomValues → ValuesOn (F.paLat i) (swigΩ Ω)) =
      (valuesProjection hLrv :
        (F.M i).RandomValues → ValuesOn (F.paLat i) (swigΩ Ω)) := by
    funext ξ x
    rfl
  have hind :
      IndepFun (valuesProjection hLrv) (valuesProjection hPrv)
        ((F.M i).jointKernel (F.s i)) := by
    have h0 := (F.hExo i).comp (φ := id) (ψ := e) measurable_id e.measurable
    change IndepFun (id ∘ valuesProjection hLatExo)
      (e ∘ valuesProjection hObsExo) ((F.M i).jointKernel (F.s i)) at h0
    rw [hOcomp] at h0
    simpa [Function.comp_def, hLcomp] using h0
  have hEvalMeas :
      Measurable (fun ℓ : (F.M i).LatentValues => (F.M i).evalMap (F.s i) ℓ) := by
    have : (fun ℓ : (F.M i).LatentValues => (F.M i).evalMap (F.s i) ℓ) =
        fun ℓ => Function.uncurry (F.M i).evalMap (F.s i, ℓ) := rfl
    rw [this]
    exact (F.M i).evalMap_measurable.comp
      (Measurable.prodMk measurable_const measurable_id)
  have hpair :
      ((F.M i).jointKernel (F.s i)).map
          (fun ω => (valuesProjection hPrv ω, valuesProjection hYrv ω)) =
        ((F.M i).jointKernel (F.s i)).map
          (fun ω => (valuesProjection hPrv ω,
            F.mechanismFun i₀ i
              (valuesProjection hPrv ω, valuesProjection hLrv ω))) := by
    rw [SCM.jointKernel_apply_eq]
    rw [Measure.map_map
      ((measurable_valuesProjection hPrv).prodMk (measurable_valuesProjection hYrv))
      hEvalMeas]
    have hRightMeas : Measurable
        (fun ω => (valuesProjection hPrv ω,
          F.mechanismFun i₀ i (valuesProjection hPrv ω, valuesProjection hLrv ω))) :=
      (measurable_valuesProjection hPrv).prodMk
        ((F.measurable_mechanismFun i₀ i).comp
          ((measurable_valuesProjection hPrv).prodMk
            (measurable_valuesProjection hLrv)))
    rw [Measure.map_map hRightMeas hEvalMeas]
    congr 1
    funext ℓ
    dsimp
    rw [F.target_projection_evalMap_eq_mechanismFun i₀ i ℓ]
  exact condDistrib_eq_mechanismKernel_of_indep_of_pair_map
    ((F.M i).jointKernel (F.s i))
    (measurable_valuesProjection hPrv) (measurable_valuesProjection hLrv)
    (measurable_valuesProjection hYrv) (F.measurable_mechanismFun i₀ i) hind hpair

-- `fixed_parent_mem_fixed_of_mem` now lives in `Model.lean` (EnvFamily namespace).

/-- Cross-environment equality of the target structural function applied to
coordinatewise-equal target-parent tuples. -/
theorem structFun_yNode_apply_eq (F : EnvFamily N Ω ι) (i j : ι)
    {ξi : (w : {w // w ∈ (F.M i).dag.parents F.yNode}) → swigΩ Ω w.val}
    {ξj : (w : {w // w ∈ (F.M j).dag.parents F.yNode}) → swigΩ Ω w.val}
    (hξ : ∀ (d : SWIGNode N)
        (hdi : d ∈ (F.M i).dag.parents F.yNode)
        (hdj : d ∈ (F.M j).dag.parents F.yNode),
      ξi ⟨d, hdi⟩ = ξj ⟨d, hdj⟩) :
    (F.M i).structFun ⟨F.yNode, F.hYobs i⟩ ξi =
      (F.M j).structFun ⟨F.yNode, F.hYobs j⟩ ξj := by
  have hParentsEq : (F.M i).dag.parents F.yNode = (F.M j).dag.parents F.yNode :=
    F.hParents i j
  have hξHeq : HEq ξi ξj := by
    apply Function.hfunext (by rw [hParentsEq])
    rintro ⟨di, hdi⟩ ⟨dj, hdj⟩ hdij
    have hval : di = dj := by
      exact (Subtype.heq_iff_coe_eq (by intro x; rw [hParentsEq])).mp hdij
    subst hval
    apply heq_of_eq
    exact hξ di hdi hdj
  exact congr_heq (F.hStruct i j) hξHeq

/-- The target-mechanism kernel is invariant across environments after the same
fixed-parent assignment is transported through the shared fixed-parent set.

The kernel first integrates out the latent parents of the target and then applies
the target structural mechanism parameterized by an explicit fixed-parent value
`cf`.  Because all environments in an `EnvFamily` share the target's structural
function, target parent set, and latent-noise law, environment `i` at `cf` gives
the same kernel as environment `j` at the corresponding value transported by
`paFix_eq`.  No separate assumption that environments agree on fixed-parent
values is required; both sides read the same transported assignment. -/
theorem mechanismKernel_cf_env_eq (F : EnvFamily N Ω ι) (i₀ i j : ι)
    (cf : ValuesOn (F.paFix i) (swigΩ Ω))
    (hLrv : F.paLat i ⊆ (F.M i).randomVars)
    (hLrv' : F.paLat j ⊆ (F.M j).randomVars) :
    Causalean.Mathlib.GraphMapProd.mechanismKernel
        (((F.M i).jointKernel (F.s i)).map (valuesProjection hLrv))
        (F.mechanismFunCf i₀ i cf) =
      Causalean.Mathlib.GraphMapProd.mechanismKernel
        (((F.M j).jointKernel (F.s j)).map (valuesProjection hLrv'))
        (F.mechanismFunCf i₀ j (valuesProjection (le_of_eq (F.paFix_eq j i)) cf)) := by
  classical
  apply ProbabilityTheory.Kernel.ext
  intro o
  rw [Causalean.Mathlib.GraphMapProd.mechanismKernel_apply
        _ (F.measurable_mechanismFunCf i₀ i cf) o,
      Causalean.Mathlib.GraphMapProd.mechanismKernel_apply
        _ (F.measurable_mechanismFunCf i₀ j _) o]
  let hLun : F.paLat i ⊆ (F.M i).unobserved := Finset.inter_subset_right
  let hLun' : F.paLat j ⊆ (F.M j).unobserved := Finset.inter_subset_right
  rw [F.jointKernel_map_paLat_eq_latentProduct_map i hLrv hLun,
    F.jointKernel_map_paLat_eq_latentProduct_map j hLrv' hLun']
  have hSliceMeas :
      Measurable (fun l : ValuesOn (F.paLat i) (swigΩ Ω) =>
        F.mechanismFunCf i₀ i cf (o, l)) :=
    (F.measurable_mechanismFunCf i₀ i cf).comp
      (Measurable.prodMk measurable_const measurable_id)
  have hSliceMeas' :
      Measurable (fun l : ValuesOn (F.paLat j) (swigΩ Ω) =>
        F.mechanismFunCf i₀ j (valuesProjection (le_of_eq (F.paFix_eq j i)) cf) (o, l)) :=
    (F.measurable_mechanismFunCf i₀ j _).comp
      (Measurable.prodMk measurable_const measurable_id)
  rw [Measure.map_map hSliceMeas (measurable_valuesProjection hLun),
    Measure.map_map hSliceMeas' (measurable_valuesProjection hLun')]
  exact map_heq_transport (congrArg (fun S => ValuesOn S (swigΩ Ω)) (F.hUnobs i j))
    (F.latentValues_measurableSpace_heq i j) (F.latentProduct_heq i j) <| by
      apply Function.hfunext
        (congrArg (fun S => ValuesOn S (swigΩ Ω)) (F.hUnobs i j))
      intro l l' hl
      apply heq_of_eq
      funext w
      rcases w with ⟨w, hw⟩
      have hwy : w = F.yNode := Finset.mem_singleton.mp hw
      subst hwy
      simp only [Function.comp_apply]
      unfold mechanismFunCf
      simp only
      apply F.structFun_yNode_apply_eq i j
      intro d hdi hdj
      by_cases hlat : d ∈ (F.M i).unobserved
      · have hlat' : d ∈ (F.M j).unobserved := by
          rw [← F.hUnobs i j]
          exact hlat
        simp only [hlat, hlat', dif_pos, valuesProjection]
        have hidx :
            (⟨d, hlat⟩ : {d // d ∈ (F.M i).unobserved}) ≍
              (⟨d, hlat'⟩ : {d // d ∈ (F.M j).unobserved}) := by
          apply (Subtype.heq_iff_coe_eq (by intro x; rw [F.hUnobs i j])).mpr
          rfl
        have hval : HEq (l ⟨d, hlat⟩) (l' ⟨d, hlat'⟩) := by
          apply dcongr_heq hidx
          · intro u u' hu
            have huv : u.val = u'.val := by
              exact (Subtype.heq_iff_coe_eq (by intro x; rw [F.hUnobs i j])).mp hu
            rw [huv]
          · intro _ _
            exact hl
        exact eq_of_heq hval
      · have hlat' : d ∉ (F.M j).unobserved := by
          intro h
          apply hlat
          rw [F.hUnobs i j]
          exact h
        simp only [hlat, hlat']
        by_cases hfix : d ∈ (F.M i).fixed
        · have hfix' : d ∈ (F.M j).fixed :=
            F.fixed_parent_mem_fixed_of_mem (Finset.mem_inter.mpr ⟨hdi, hfix⟩)
          simp only [dif_neg (not_false), dif_pos hfix, dif_pos hfix', valuesProjection]
        · have hfix' : d ∉ (F.M j).fixed := by
            intro h
            apply hfix
            exact F.fixed_parent_mem_fixed_of_mem
              (i := j) (j := i) (d := d) (Finset.mem_inter.mpr ⟨hdj, h⟩)
          simp only [hfix, hfix']
          rfl

end EnvFamily

end Causalean.Discovery.InvariantPrediction
