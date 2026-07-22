/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Observational Global Markov Property

This file projects the full global Markov property (`full_globalMarkov` on
`jointKernel`) to the observational level (`ObsCondIndep` on `obsKernel`) via
the pushforward bridge `condIndepFun_of_map`.

## Main results

* `obs_condIndep_of_full` — projection lemma: `FullCondIndep` on `jointKernel`
  implies `ObsCondIndep` on `obsKernel` whenever all three sets are observed.
* `globalMarkov` — d-separation implies observational conditional independence.
* `globalMarkov_with_fixed` — variant allowing fixed nodes in the conditioning
  set by absorbing them into the full-level conditioning shadow
-/

import Causalean.SCM.Do.GlobalMarkov

/-! # Observational Markov Property

This file transfers conditional independence from the full distribution over
random and latent coordinates to the observational distribution over observed
coordinates. It then packages graphical separation hypotheses as observational
conditional independences for use in do-calculus arguments. -/

namespace Causalean

open scoped MeasureTheory ProbabilityTheory

namespace SCM

universe uN uΩ

variable {N : Type uN} [DecidableEq N] [Fintype N]
variable {Ω : N → Type uΩ} [∀ n, MeasurableSpace (Ω n)]

-- ============================================================
-- § 1. Projection lemma: full CI → observational CI
-- ============================================================

/-- **Projection lemma.** For `X, Y, Z ⊆ V` (all observed), conditional
    independence at the full distribution level (`jointKernel`) implies
    conditional independence at the observational level (`obsKernel`).

    This holds because `obsKernel = jointKernel.map randomToObserved`, and
    for observed sets, `P(V_A ∈ · | V_C = c)` is the same whether computed
    from `P(V, L)` or `P(V)` — the latent marginal cancels since A, C ⊆ V. -/
theorem obs_condIndep_of_full (M : Causalean.SCM N Ω)
    [StandardBorelSpace M.RandomValues]
    [StandardBorelSpace M.ObservedValues]
    [∀ s : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.jointKernel s)]
    [∀ s : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.obsKernel s)]
    {X Y Z : Finset (SWIGNode N)}
    [StandardBorelSpace (ValuesOn X (swigΩ Ω))] [Nonempty (ValuesOn X (swigΩ Ω))]
    [StandardBorelSpace (ValuesOn Y (swigΩ Ω))] [Nonempty (ValuesOn Y (swigΩ Ω))]
    (hX : X ⊆ M.observed) (hY : Y ⊆ M.observed) (hZ : Z ⊆ M.observed)
    (s : M.FixedValues)
    (hfull : FullCondIndep M X Y Z
      (hX.trans (observed_subset_randomVars M))
      (hY.trans (observed_subset_randomVars M))
      (hZ.trans (observed_subset_randomVars M))
      (M.jointKernel s)) :
    ObsCondIndep M X Y Z hX hY hZ (M.obsKernel s) := by
  -- `obsKernel s = (jointKernel s).map randomToObserved` (kernel-level pushforward).
  have hobs_eq : M.obsKernel s = (M.jointKernel s).map M.randomToObserved :=
    ProbabilityTheory.Kernel.map_apply _ M.measurable_randomToObserved s
  -- `IsFiniteMeasure` propagates across the equation; needed since `CondIndepFun`
  -- carries `[IsFiniteMeasure μ]` as an instance argument.
  haveI : MeasureTheory.IsFiniteMeasure ((M.jointKernel s).map M.randomToObserved) :=
    hobs_eq ▸ (inferInstance : MeasureTheory.IsFiniteMeasure (M.obsKernel s))
  -- Apply the pushforward bridge to build CondIndepFun on
  -- `(M.jointKernel s).map M.randomToObserved`.
  unfold FullCondIndep at hfull
  have hresult : ProbabilityTheory.CondIndepFun
      (MeasurableSpace.comap (valuesProjection hZ) inferInstance)
      (comap_valuesProjection_le hZ)
      (valuesProjection hX) (valuesProjection hY)
      ((M.jointKernel s).map M.randomToObserved) :=
    condIndepFun_of_map
      (φ := M.randomToObserved) M.measurable_randomToObserved
      (measurable_valuesProjection hX)
      (measurable_valuesProjection hY)
      (measurable_valuesProjection hZ) hfull
  -- Transport hresult to the `obsKernel s` form. Since `CondIndepFun` has
  -- `[IsFiniteMeasure μ]` as an instance argument, direct `rw`/`▸` fails the motive
  -- check; `convert` handles the measure slot via its built-in congruence machinery.
  unfold ObsCondIndep
  convert hresult using 2

-- ============================================================
-- § 2. Observational Global Markov
-- ============================================================

/-- **Global Markov Property.** If `X` and `Y` are d-separated by `Z` in the
    full DAG of the gSCM (including latent nodes), then the X-projection and
    Y-projection of the observational kernel are conditionally independent
    given the Z-projection, at every fixed-value argument `s : M.FixedValues`.

    The proof first applies `full_globalMarkov` to obtain conditional
    independence under the full joint distribution, then projects that
    independence to the observational law with `obs_condIndep_of_full`. -/
theorem globalMarkov (M : Causalean.SCM N Ω)
    [StandardBorelSpace M.RandomValues]
    [StandardBorelSpace M.ObservedValues]
    [∀ n, StandardBorelSpace (swigΩ Ω n)] [∀ n, Nonempty (swigΩ Ω n)]
    [∀ s : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.jointKernel s)]
    [∀ s : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.obsKernel s)]
    (X Y Z : Finset (SWIGNode N))
    [StandardBorelSpace (ValuesOn X (swigΩ Ω))] [Nonempty (ValuesOn X (swigΩ Ω))]
    [StandardBorelSpace (ValuesOn Y (swigΩ Ω))] [Nonempty (ValuesOn Y (swigΩ Ω))]
    (hX : X ⊆ M.observed) (hY : Y ⊆ M.observed) (hZ : Z ⊆ M.observed)
    (hDisj_XY : Disjoint X Y)
    (hDisj_XZ : Disjoint X Z) (hDisj_YZ : Disjoint Y Z)
    (hdSep : M.dag.dSep X Y Z)
    (s : M.FixedValues) :
    ObsCondIndep M X Y Z hX hY hZ (M.obsKernel s) := by
  -- Stage 1: full global Markov at full distribution level
  have hfull := full_globalMarkov M X Y Z
    (hX.trans (observed_subset_randomVars M))
    (hY.trans (observed_subset_randomVars M))
    (hZ.trans (observed_subset_randomVars M))
    hDisj_XY hDisj_XZ hDisj_YZ
    hdSep s
  -- Stage 2: project to observational level
  exact obs_condIndep_of_full M hX hY hZ s hfull

/-- **Global Markov with fixed-node conditioning.** Generalizes `globalMarkov`
    to allow the d-sep conditioning set to include fixed nodes alongside
    observed ones.

    This is the form consumed by split-language do-calculus: `do_rule1` /
    `do_rule2_kernel` need the post-intervention fixed set (`M'.fixed` or
    `(M'.fixSet Z).fixed`) in the d-sep conditioning set so that paths
    through the new fixed nodes added by `fixSet` are blocked as
    non-colliders.

    **Proof.** Apply `full_globalMarkov_with_fixed` with random conditioning
    part `Z_obs` and fixed conditioning shadow `Z_fix`, then project the
    resulting full conditional independence along `randomToObserved`. -/
theorem globalMarkov_with_fixed (M : Causalean.SCM N Ω)
    [StandardBorelSpace M.RandomValues]
    [StandardBorelSpace M.ObservedValues]
    [∀ n, StandardBorelSpace (swigΩ Ω n)] [∀ n, Nonempty (swigΩ Ω n)]
    [∀ s : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.jointKernel s)]
    [∀ s : M.FixedValues, MeasureTheory.IsFiniteMeasure (M.obsKernel s)]
    (X Y Z_obs Z_fix : Finset (SWIGNode N))
    [StandardBorelSpace (ValuesOn X (swigΩ Ω))] [Nonempty (ValuesOn X (swigΩ Ω))]
    [StandardBorelSpace (ValuesOn Y (swigΩ Ω))] [Nonempty (ValuesOn Y (swigΩ Ω))]
    (hX : X ⊆ M.observed) (hY : Y ⊆ M.observed) (hZ_obs : Z_obs ⊆ M.observed)
    (hZ_fix : Z_fix ⊆ M.fixed)
    (hDisj_XY : Disjoint X Y)
    (hDisj_XZ : Disjoint X Z_obs) (hDisj_YZ : Disjoint Y Z_obs)
    (hdSep : M.dag.dSep X Y (Z_obs ∪ Z_fix))
    (s : M.FixedValues) :
    ObsCondIndep M X Y Z_obs hX hY hZ_obs (M.obsKernel s) := by
  have hfull := full_globalMarkov_with_fixed M X Y Z_obs Z_fix
    (hX.trans (observed_subset_randomVars M))
    (hY.trans (observed_subset_randomVars M))
    (hZ_obs.trans (observed_subset_randomVars M))
    hZ_fix hDisj_XY hDisj_XZ hDisj_YZ hdSep s
  exact obs_condIndep_of_full M hX hY hZ_obs s hfull

end SCM

end Causalean
