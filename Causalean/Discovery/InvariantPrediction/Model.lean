/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.SCM.Model.Kernel
import Causalean.SCM.Model.InterventionSet
import Causalean.Graph.DAG
import Mathlib.Probability.Independence.Basic

/-!
# Invariant Causal Prediction: environment-family model layer

Formalization of the setup of Peters, Bühlmann & Meinshausen, *Causal inference
using invariant prediction* (JRSS-B 2016, `arXiv:1501.01332`).

An **environment family** is a finite collection of structural causal models
`{M i}` over a common set of observed and latent variables, indexed by an
environment label `i`.  Each `M i` arises from interventions that may differ
between environments, but **never act on the target node `Y`**: every
environment shares the target's structural mechanism (`hStruct`), the target's
parent set (`hParents`), and the latent-noise law (`hLatent`).  Each environment
also carries the values `s i` assigned to its intervened (fixed) coordinates,
because an intervention `do(X = x)` fixes those coordinates to `x`.

The only observable content per environment is the conditional law of the target
`Y` given a set of predictors `X_S`, read off from `(M i).obsCondKernel {Y} S`
evaluated at `s i`.  Invariant Causal Prediction asks which predictor sets `S`
make this conditional law the *same* across all environments.
-/

namespace Causalean.Discovery.InvariantPrediction

open Causalean MeasureTheory ProbabilityTheory

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

/-- An **ICP environment family**: a `Fintype`-indexed family of structural
causal models over common observed/latent variable sets, sharing the target's
mechanism, parents and noise law (so no environment intervenes on the target),
together with the fixed values assigned by each environment's intervention. -/
structure EnvFamily (N : Type*) [DecidableEq N] [Fintype N]
    (Ω : N → Type*) [∀ n, MeasurableSpace (Ω n)]
    (ι : Type*) [Fintype ι] where
  /-- The structural causal model in each environment. -/
  M : ι → Causalean.SCM N Ω
  /-- The target variable; the target node is `SWIGNode.random Y`. -/
  Y : N
  /-- Every environment observes the target. -/
  hYobs : ∀ i, SWIGNode.random Y ∈ (M i).observed
  /-- All environments share the observed-variable set. -/
  hObs : ∀ i j, (M i).observed = (M j).observed
  /-- All environments share the latent-variable set. -/
  hUnobs : ∀ i j, (M i).unobserved = (M j).unobserved
  /-- **(E4)** All environments share the target's parent set. -/
  hParents : ∀ i j, (M i).dag.parents (SWIGNode.random Y)
                  = (M j).dag.parents (SWIGNode.random Y)
  /-- **(E2)** All environments share the target's structural mechanism. -/
  hStruct : ∀ i j, HEq ((M i).structFun ⟨SWIGNode.random Y, hYobs i⟩)
                       ((M j).structFun ⟨SWIGNode.random Y, hYobs j⟩)
  /-- **(E3)** All environments share the latent-noise law. -/
  hLatent : ∀ i j, HEq (M i).latentDist (M j).latentDist
  /-- The values assigned to the intervened (fixed) coordinates in each
  environment (`do(X = x)` fixes `X` to `x`). -/
  s : ∀ i, (M i).FixedValues
  /-- The target's value space is standard Borel (holds automatically when the
  coordinate spaces are standard Borel; bundled so the conditional-kernel
  disintegration machinery is always available). -/
  borelTarget :
    StandardBorelSpace (ValuesOn ({SWIGNode.random Y} : Finset (SWIGNode N)) (swigΩ Ω))
  /-- The target's value space is nonempty. -/
  neTarget :
    Nonempty (ValuesOn ({SWIGNode.random Y} : Finset (SWIGNode N)) (swigΩ Ω))
  /-- The disintegration obligation of `obsCondKernel` holds for every predictor
  set and environment (holds automatically for standard-Borel coordinates). -/
  cg : ∀ (S : Finset (SWIGNode N)) (i : ι),
    MeasurableSpace.CountableOrCountablyGenerated ((M i).FixedValues) (ValuesOn S (swigΩ Ω))
  /-- **Exogeneity** — the ICP invariance assumption `εᵉ ⊥ Xᵉ_{S*}` (Peters–Bühlmann–
  Meinshausen 2016, Assumption 1).  In every environment, the target's exogenous
  (latent) parents are independent of its observed parents under the joint law.
  This rules out hidden confounding between `Y` and its parents, and is exactly
  what makes the conditional law of `Y` given its observed parents an
  environment-invariant structural factor (the engine of soundness). -/
  hExo : ∀ i,
    ProbabilityTheory.IndepFun
      (valuesProjection (Ω := swigΩ Ω)
        (show (M i).dag.parents (SWIGNode.random Y) ∩ (M i).unobserved ⊆ (M i).randomVars from
          (Finset.inter_subset_right).trans
            (by show (M i).unobserved ⊆ (M i).observed ∪ (M i).unobserved
                exact Finset.subset_union_right)))
      (valuesProjection (Ω := swigΩ Ω)
        (show (M i).dag.parents (SWIGNode.random Y) ∩ (M i).observed ⊆ (M i).randomVars from
          (Finset.inter_subset_right).trans
            (by show (M i).observed ⊆ (M i).observed ∪ (M i).unobserved
                exact Finset.subset_union_left)))
      ((M i).jointKernel (s i))

namespace EnvFamily

variable {ι : Type*} [Fintype ι] (F : EnvFamily N Ω ι)

/-- The target node `SWIGNode.random Y`. -/
abbrev yNode : SWIGNode N := SWIGNode.random F.Y

/-- The observed parents of the target in environment `i` — the conditioning
candidates ICP ranges over. Index-independent by `hParents` and `hObs`
(see `paObs_eq`). -/
def paObs (i : ι) : Finset (SWIGNode N) :=
  (F.M i).dag.parents F.yNode ∩ (F.M i).observed

/-- `paObs` does not depend on the chosen environment. -/
theorem paObs_eq (i j : ι) : F.paObs i = F.paObs j := by
  unfold paObs
  rw [F.hParents i j, F.hObs i j]

/-- The **fixed parents** of the target in environment `i` — the parents of `Y`
that are intervened on (fixed) in that environment.  These are the coordinates of
`Y`'s mechanism whose values live in `s i` and may *legitimately differ* across
environments; the redesigned `Invariant` predicate conditions on them. -/
def paFix (i : ι) : Finset (SWIGNode N) :=
  (F.M i).dag.parents F.yNode ∩ (F.M i).fixed

/-- A target parent that is fixed in one environment is fixed in every
environment.  The point is not that `EnvFamily` shares the whole `fixed` set,
but that it shares the target parent set (E4), and a fixed-form SWIG node cannot
be an observed or unobserved random-form node in the other environment, while a
parent of `Y` is always classified as fixed/observed/unobserved
(`dag_edges_classified`). -/
theorem fixed_parent_mem_fixed_of_mem {i j : ι} {d : SWIGNode N}
    (hd : d ∈ (F.M i).dag.parents F.yNode ∩ (F.M i).fixed) :
    d ∈ (F.M j).fixed := by
  classical
  have hd_parent_i : d ∈ (F.M i).dag.parents F.yNode := (Finset.mem_inter.mp hd).1
  have hd_fixed_i : d ∈ (F.M i).fixed := (Finset.mem_inter.mp hd).2
  have hd_parent_j : d ∈ (F.M j).dag.parents F.yNode := by
    rw [← F.hParents i j]
    exact hd_parent_i
  have hedge_j : (F.M j).dag.edge d F.yNode := (F.M j).dag.mem_parents.mp hd_parent_j
  have hclass_j : d ∈ (F.M j).fixed ∪ (F.M j).observed ∪ (F.M j).unobserved :=
    ((F.M j).dag_edges_classified d F.yNode hedge_j).1
  rcases (F.M i).fixed_is_fixed d hd_fixed_i with ⟨n, rfl⟩
  rcases Finset.mem_union.mp hclass_j with hfo | hunobs
  · rcases Finset.mem_union.mp hfo with hfixed | hobs
    · exact hfixed
    · rcases (F.M j).observed_is_random (SWIGNode.fixed n) hobs with ⟨m, hm⟩
      cases hm
  · rcases (F.M j).unobserved_is_random (SWIGNode.fixed n) hunobs with ⟨m, hm⟩
    cases hm

/-- `paFix` does not depend on the chosen environment.  Unlike `paObs`/`paLat`,
this is *not* immediate from a shared-set field — `EnvFamily` does not share the
`fixed` set — but follows from `fixed_parent_mem_fixed_of_mem` together with the
shared parent set (E4). -/
theorem paFix_eq (i j : ι) : F.paFix i = F.paFix j := by
  classical
  apply Finset.ext
  intro d
  simp only [paFix, Finset.mem_inter]
  constructor
  · rintro ⟨hdp, hdf⟩
    refine ⟨?_, F.fixed_parent_mem_fixed_of_mem (Finset.mem_inter.mpr ⟨hdp, hdf⟩)⟩
    rw [← F.hParents i j]; exact hdp
  · rintro ⟨hdp, hdf⟩
    refine ⟨?_, F.fixed_parent_mem_fixed_of_mem (Finset.mem_inter.mpr ⟨hdp, hdf⟩)⟩
    rw [F.hParents i j]; exact hdp

/-- The fixed parents are a subset of the fixed coordinates, so they can be read
off the environment's intervention assignment `s i`. -/
theorem paFix_subset_fixed (i : ι) : F.paFix i ⊆ (F.M i).fixed :=
  Finset.inter_subset_right

/-- The fixed-parent values assigned by environment `i`'s intervention,
projected from `s i`. -/
noncomputable def fixedParentVals (i : ι) : ValuesOn (F.paFix i) (swigΩ Ω) :=
  valuesProjection (F.paFix_subset_fixed i) (F.s i)

end EnvFamily

end Causalean.Discovery.InvariantPrediction
