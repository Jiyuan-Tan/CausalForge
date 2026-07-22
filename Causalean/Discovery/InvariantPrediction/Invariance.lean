/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Discovery.InvariantPrediction.Helpers.MechanismFactor

/-!
# Invariant Causal Prediction: the invariance predicate and mechanism invariance

A predictor set `S` is **invariant** across an environment family when the
conditional law of the target `Y` given `X_S` — read off from
`obsCondKernel {Y} S` evaluated at each environment's intervention values `s i`
— is the *same* in every environment.

The central structural fact is `mechanism_invariant`: the target's own observed
parents `paObs` always form an invariant set, because conditioning on the parents
exposes the target's structural mechanism, which every environment shares
(`hStruct`/`hLatent`/`hParents`).  This is the engine behind soundness
(`S(E) ⊆ PA(Y)`).

Throughout we assume the per-coordinate value spaces are standard Borel and
nonempty; the finite-measure and countably-generated obligations of
`obsCondKernel` are threaded as instance hypotheses.
-/

namespace Causalean.Discovery.InvariantPrediction

open Causalean MeasureTheory ProbabilityTheory

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

namespace EnvFamily

variable {ι : Type*} [Fintype ι]

/-- The singleton node set `{Y}` used as the conditioned target. -/
abbrev targetSet (F : EnvFamily N Ω ι) : Finset (SWIGNode N) := {SWIGNode.random F.Y}

/-- `S` is **invariant** across the environment family `F`.

Faithful to the paper's "condition on `X_{PA(Y)}` regardless of intervention
status": the witness conditional law `κ` may depend on the values of the target's
*fixed parents* `paFix` (those direct causes of `Y` that an intervention pins to a
value, which may legitimately differ between environments), but on nothing else
that varies across environments.  Concretely:

* `κ i` is a conditional law of the target given the predictors `X_S`, allowed to
  read the fixed-parent values `ValuesOn (paFix i)`;
* **(env-independence)** `κ` depends on the environment *only* through those
  fixed-parent values — `κ i` and `κ j` agree once their fixed-parent arguments
  are identified through the shared fixed-parent set (`paFix_eq`); and
* in every environment `i`, the conditional law of the target given `X_S`
  (read off from `obsCondKernel`, evaluated at the intervention values `s i`)
  equals `κ i` applied to that environment's fixed-parent values
  `fixedParentVals i`.

When the target has no fixed parents, `paFix i = ∅` and `κ` collapses to the old
single environment-independent kernel; the redesign is what makes
`mechanism_invariant` hold unconditionally. -/
def Invariant (F : EnvFamily N Ω ι) (S : Finset (SWIGNode N))
    (hS : ∀ i, S ⊆ (F.M i).observed) : Prop :=
  haveI := F.borelTarget
  haveI := F.neTarget
  haveI : ∀ i, MeasurableSpace.CountableOrCountablyGenerated
      ((F.M i).FixedValues) (ValuesOn S (swigΩ Ω)) := fun i => F.cg S i
  ∃ κ : (i : ι) → ValuesOn (F.paFix i) (swigΩ Ω) →
      ValuesOn S (swigΩ Ω) → Measure (ValuesOn F.targetSet (swigΩ Ω)),
    (∀ (i j : ι) (cf : ValuesOn (F.paFix i) (swigΩ Ω)),
        κ i cf = κ j (valuesProjection (le_of_eq (F.paFix_eq j i)) cf)) ∧
    ∀ i : ι,
      (fun c => (F.M i).obsCondKernel F.targetSet S
          (Finset.singleton_subset_iff.mpr (F.hYobs i)) (hS i) (F.s i, c))
        =ᵐ[((F.M i).obsKernel (F.s i)).map (valuesProjection (hS i))]
          (fun c => κ i (F.fixedParentVals i) c)

/-- The observed parents form a valid conditioning set in every environment. -/
theorem paObs_subset_observed (F : EnvFamily N Ω ι) (i j : ι) :
    F.paObs i ⊆ (F.M j).observed := by
  rw [F.paObs_eq i j]
  unfold paObs
  exact Finset.inter_subset_right

private theorem obsCondKernel_ae_eq_joint_condDistrib
    (F : EnvFamily N Ω ι) (i₀ i : ι) :
    (by
      classical
      haveI := F.borelTarget
      haveI := F.neTarget
      haveI : ∀ s : (F.M i).FixedValues, IsFiniteMeasure ((F.M i).obsKernel s) :=
        inferInstance
      haveI : MeasurableSpace.CountableOrCountablyGenerated
          ((F.M i).FixedValues) (ValuesOn (F.paObs i₀) (swigΩ Ω)) :=
        F.cg (F.paObs i₀) i
      let hYobs : F.targetSet ⊆ (F.M i).observed :=
        Finset.singleton_subset_iff.mpr (F.hYobs i)
      let hPobs : F.paObs i₀ ⊆ (F.M i).observed :=
        F.paObs_subset_observed i₀ i
      let hYrv : F.targetSet ⊆ (F.M i).randomVars := by
        intro w hw
        rw [Finset.mem_singleton] at hw
        subst hw
        exact Finset.mem_union_left _ (F.hYobs i)
      let hPrv : F.paObs i₀ ⊆ (F.M i).randomVars := by
        rw [F.paObs_eq i₀ i]
        exact (Finset.inter_subset_right).trans (by
          show (F.M i).observed ⊆ (F.M i).observed ∪ (F.M i).unobserved
          exact Finset.subset_union_left)
      exact
        (fun c => (F.M i).obsCondKernel F.targetSet (F.paObs i₀)
          hYobs hPobs (F.s i, c))
        =ᵐ[((F.M i).jointKernel (F.s i)).map (valuesProjection hPrv)]
          condDistrib (valuesProjection hYrv) (valuesProjection hPrv)
            ((F.M i).jointKernel (F.s i))) := by
  classical
  dsimp only
  haveI := F.borelTarget
  haveI := F.neTarget
  haveI : ∀ s : (F.M i).FixedValues, IsFiniteMeasure ((F.M i).obsKernel s) :=
    inferInstance
  haveI : MeasurableSpace.CountableOrCountablyGenerated
      ((F.M i).FixedValues) (ValuesOn (F.paObs i₀) (swigΩ Ω)) :=
    F.cg (F.paObs i₀) i
  let hYobs : F.targetSet ⊆ (F.M i).observed :=
    Finset.singleton_subset_iff.mpr (F.hYobs i)
  let hPobs : F.paObs i₀ ⊆ (F.M i).observed :=
    F.paObs_subset_observed i₀ i
  let hYrv : F.targetSet ⊆ (F.M i).randomVars := by
    intro w hw
    rw [Finset.mem_singleton] at hw
    subst hw
    exact Finset.mem_union_left _ (F.hYobs i)
  let hPrv : F.paObs i₀ ⊆ (F.M i).randomVars := by
    rw [F.paObs_eq i₀ i]
    exact (Finset.inter_subset_right).trans (by
      show (F.M i).observed ⊆ (F.M i).observed ∪ (F.M i).unobserved
      exact Finset.subset_union_left)
  have hbase :=
    (F.M i).obsCondKernel_ae_eq_condDistrib
      F.targetSet (F.paObs i₀) hYobs hPobs (F.s i)
  have hMarg :=
    Causalean.Discovery.InvariantPrediction.EnvFamily.obsKernel_map_valuesProjection_eq_jointKernel_map
      (F.M i) (F.s i) (F.paObs i₀) hPobs hPrv
  have hObsEq :
      (F.M i).obsKernel (F.s i) =
        Measure.map (F.M i).randomToObserved ((F.M i).jointKernel (F.s i)) := by
    unfold SCM.obsKernel
    rw [ProbabilityTheory.Kernel.map_apply _ (F.M i).measurable_randomToObserved]
  rw [hMarg] at hbase
  haveI : IsFiniteMeasure
      (Measure.map (F.M i).randomToObserved ((F.M i).jointKernel (F.s i))) :=
    hObsEq ▸ (inferInstance : IsFiniteMeasure ((F.M i).obsKernel (F.s i)))
  simp only [hObsEq] at hbase
  have hmap := Causalean.condDistrib_map_comp ((F.M i).jointKernel (F.s i))
    (φ := (F.M i).randomToObserved)
    (g := valuesProjection hYobs) (f := valuesProjection hPobs)
    (F.M i).measurable_randomToObserved
    (measurable_valuesProjection hYobs) (measurable_valuesProjection hPobs)
  have hcompY :
      valuesProjection hYobs ∘ (F.M i).randomToObserved =
        (valuesProjection hYrv :
          (F.M i).RandomValues → ValuesOn F.targetSet (swigΩ Ω)) := by
    funext ξ x
    rfl
  have hcompP :
      valuesProjection hPobs ∘ (F.M i).randomToObserved =
        (valuesProjection hPrv :
          (F.M i).RandomValues → ValuesOn (F.paObs i₀) (swigΩ Ω)) := by
    funext ξ x
    rfl
  rw [Measure.map_map
    (measurable_valuesProjection hPobs) (F.M i).measurable_randomToObserved] at hmap
  rw [hcompY, hcompP] at hmap
  exact hbase.trans hmap

/-- **Mechanism invariance (the heart of soundness).**  The target's observed
parents `paObs` form an invariant set: in every environment the conditional law
of the target given its observed parents equals one fixed structural factor, so
ICP never rejects the parents.

The proof reads off that factor as the law of the target's mechanism
`structFun Y` driven by the latent-parent noise: in each environment, by the
exogeneity assumption `hExo` the latent parents are independent of the observed
parents, so the conditional law of the target given the observed parents is the
push-forward of the latent-parent law through the mechanism slice; this factor is
environment-independent because the mechanism `structFun Y` (E2), the latent-noise
law (E3) and the parent set (E4) are all shared.  The witness conditional law `κ`
is keyed on the fixed-parent values via the parameterized mechanism
`mechanismFunCf`: at environment `i`'s own fixed-parent values it reduces to the
mechanism factor (per-environment a.e. equality, via
`obsCondKernel_ae_eq_joint_condDistrib` and `condDistrib_target_eq_mechanismKernel`),
and across environments it transports cleanly (coherence, via
`mechanismKernel_cf_env_eq`).  No regularity input on environments agreeing about
the values of fixed parents is required — that is the point of the redesign. -/
theorem mechanism_invariant (F : EnvFamily N Ω ι) (i₀ : ι) :
    F.Invariant (F.paObs i₀) (fun j => F.paObs_subset_observed i₀ j) := by
  classical
  haveI := F.borelTarget
  haveI := F.neTarget
  -- The latent-parent set is a random-variable subset in every environment.
  have hLrvOf : ∀ i : ι, F.paLat i ⊆ (F.M i).randomVars := fun i =>
    (Finset.inter_subset_right).trans (by
      show (F.M i).unobserved ⊆ (F.M i).observed ∪ (F.M i).unobserved
      exact Finset.subset_union_right)
  -- The witness conditional law `κ`: the mechanism factor for environment `i`,
  -- parameterized by the explicit fixed-parent values `cf`.
  refine ⟨fun i cf _c =>
      Causalean.Mathlib.GraphMapProd.mechanismKernel
        (((F.M i).jointKernel (F.s i)).map (valuesProjection (hLrvOf i)))
        (F.mechanismFunCf i₀ i cf) _c, ?_, ?_⟩
  · -- Coherence across environments: `κ i cf = κ j (transport cf)`.
    intro i j cf
    funext c
    exact congrFun
      (congrArg DFunLike.coe
        (F.mechanismKernel_cf_env_eq i₀ i j cf (hLrvOf i) (hLrvOf j))) c
  · -- Per-environment a.e. equality at environment `i`'s own fixed-parent values.
    intro i
    have hPrv : F.paObs i₀ ⊆ (F.M i).randomVars := by
      rw [F.paObs_eq i₀ i]
      exact (Finset.inter_subset_right).trans (by
        show (F.M i).observed ⊆ (F.M i).observed ∪ (F.M i).unobserved
        exact Finset.subset_union_left)
    -- Rewrite the ambient a.e. measure from `obsKernel` to `jointKernel`.
    rw [obsKernel_map_valuesProjection_eq_jointKernel_map (F.M i) (F.s i)
        (F.paObs i₀) (F.paObs_subset_observed i₀ i) hPrv]
    -- `obsCondKernel =ᵐ condDistrib =ᵐ mechanismKernel(..., mechanismFun i₀ i)`,
    -- and `mechanismFunCf i₀ i (fixedParentVals i) = mechanismFun i₀ i`.
    have hStep1 := F.obsCondKernel_ae_eq_joint_condDistrib i₀ i
    have hStep2 := F.condDistrib_target_eq_mechanismKernel i₀ i
    simp only [F.mechanismFunCf_fixedParentVals i₀ i]
    exact hStep1.trans hStep2

end EnvFamily

end Causalean.Discovery.InvariantPrediction
