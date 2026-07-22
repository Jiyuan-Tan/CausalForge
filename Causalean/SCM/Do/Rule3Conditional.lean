/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.SCM.Do.Rule3
import Causalean.SCM.Do.ValuesProjectionCI

/-! # Conditional Rule 3 of do-Calculus (a.e. `obsCondKernel` form)

The joint-marginal Rule 3\* (`do_rule3` / `condDistrib_intervention_ancestral_eq`)
transports the *joint* law of an ancestrally-blocked outcome block across an
intervention.  This file upgrades it to the **conditional** Rule 3 — Pearl's
`p(Y | do(z), W) = p(Y | W)` — in the honest almost-everywhere form, matching the
style of `do_rule2_kernel`.

The mathematical content is a single disintegration fact: `condDistrib` depends
only on the joint pushforward `μ.map (X, Y)`, and Rule 3\* makes the two joint
pushforwards (under `do(Z)` and under the base model) literally equal on the
target/conditioning block.  No positivity or ratio infrastructure is required
because there is no do-side pinning here (unlike Rule 2); the intervention only
transports a marginal.

## Main declarations

* `condDistrib_eq_of_map_prod_eq` — generic: equal joint pushforwards ⇒ equal `condDistrib`.
* `obsKernel_map_prodWY_eq` — Rule 3\* specialized to the `(W, Y)` joint pushforward.
* `obsKernel_map_W_eq` — Rule 3\* specialized to the `W`-marginal.
* `do_rule3_conditional_condDistrib` — conditional Rule 3, literal `condDistrib` form.
* `do_rule3_conditional` — conditional Rule 3, headline a.e. `obsCondKernel` form.

## References

* Basic Concepts.tex, Proposition (do-Calculus), Rule 3.
* Pearl (2009), Causality, Chapter 3.
-/

namespace Causalean

namespace SCM

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

open scoped MeasureTheory ProbabilityTheory

-- ============================================================
-- § 0. Disintegration uniqueness (the whole mathematical core)
-- ============================================================

/-- Two conditional distributions with the same joint law are equal.

    If the joint pushforward of `(X, Y)` under `μ` equals the joint pushforward
    of `(X', Y')` under `ν`, then the conditional distribution of `Y` given `X`
    under `μ` equals that of `Y'` given `X'` under `ν`.  This is immediate from
    `condDistrib Y X μ = (μ.map (X, Y)).condKernel`: the conditional distribution
    is a pure function of the joint law, so equal joint laws give equal
    conditionals.  The two source measures may live on different spaces. -/
theorem condDistrib_eq_of_map_prod_eq
    {α α' β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace α'] [MeasurableSpace β] [MeasurableSpace γ]
    [StandardBorelSpace β] [Nonempty β]
    {X : α → γ} {Y : α → β} {X' : α' → γ} {Y' : α' → β}
    {μ : MeasureTheory.Measure α} {ν : MeasureTheory.Measure α'}
    [MeasureTheory.IsFiniteMeasure μ] [MeasureTheory.IsFiniteMeasure ν]
    (h : μ.map (fun a => (X a, Y a)) = ν.map (fun a => (X' a, Y' a))) :
    ProbabilityTheory.condDistrib Y X μ = ProbabilityTheory.condDistrib Y' X' ν := by
  rw [ProbabilityTheory.condDistrib, ProbabilityTheory.condDistrib]
  congr 1

-- ============================================================
-- § 1. Rule 3* pushforward specializations
-- ============================================================

/-- Rule 3\* on the `(W, Y)` joint pushforward.

    Under the ancestral no-descendant premise `hNoDesc`, the joint law of the
    conditioning block `W` paired with the target block `Y` is the same after
    intervening on `Z` as under the base model with the induced fixed values.
    This is `condDistrib_intervention_ancestral_eq` at outcome block `T := Y ∪ W`,
    read through the sub-projections `W ⊆ Y ∪ W` and `Y ⊆ Y ∪ W`. -/
theorem obsKernel_map_prodWY_eq
    (M' : Causalean.SCM N Ω) (Z : Finset N)
    (hZ_obs : ∀ D ∈ Z, SWIGNode.random D ∈ M'.observed)
    (hZ_fixed : ∀ D ∈ Z, SWIGNode.fixed D ∉ M'.fixed)
    (Y W : Finset (SWIGNode N))
    (hY : Y ⊆ M'.observed)
    (hW : W ⊆ M'.observed)
    (hNoDesc : ∀ v ∈ Y ∪ W, ∀ d ∈ Z,
      ¬ (M'.fixSet Z hZ_obs hZ_fixed).dag.isAncestor (SWIGNode.fixed d) v)
    (s' : (M'.fixSet Z hZ_obs hZ_fixed).FixedValues) :
    ((M'.fixSet Z hZ_obs hZ_fixed).obsKernel s').map
        (fun ω =>
          (valuesProjection ((fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hW) ω,
           valuesProjection ((fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hY) ω))
      =
    (M'.obsKernel (M'.fixSetProj Z hZ_obs hZ_fixed s')).map
        (fun ω => (valuesProjection hW ω, valuesProjection hY ω)) := by
  -- Factor both pair-maps through the single `Y ∪ W` projection, then apply
  -- Rule 3* (`condDistrib_intervention_ancestral_eq`) on that union block.
  classical
  let M2 := M'.fixSet Z hZ_obs hZ_fixed
  let U := Y ∪ W
  have hU : U ⊆ M'.observed := Finset.union_subset hY hW
  have hU_do : U ⊆ M2.observed := by
    simpa [M2, SCM.fixSet_observed] using hU
  have hW_U : W ⊆ U := Finset.subset_union_right
  have hY_U : Y ⊆ U := Finset.subset_union_left
  let pairU : ValuesOn U (swigΩ Ω) →
      ValuesOn W (swigΩ Ω) × ValuesOn Y (swigΩ Ω) :=
    fun ω => (valuesProjection hW_U ω, valuesProjection hY_U ω)
  have hpairU_meas : Measurable pairU := by
    exact (measurable_valuesProjection hW_U).prodMk (measurable_valuesProjection hY_U)
  have hPair_do_comp :
      pairU ∘ valuesProjection hU_do =
        (fun ω : M2.ObservedValues =>
          (valuesProjection ((fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hW) ω,
           valuesProjection ((fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hY) ω)) := by
    funext ω
    apply Prod.ext
    · simpa [pairU, Function.comp_apply] using
        congrFun (valuesProjection_comp (Ω' := swigΩ Ω) hW_U hU_do
          ((fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hW)).symm ω
    · simpa [pairU, Function.comp_apply] using
        congrFun (valuesProjection_comp (Ω' := swigΩ Ω) hY_U hU_do
          ((fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hY)).symm ω
  have hPair_base_comp :
      pairU ∘ valuesProjection hU =
        (fun ω : M'.ObservedValues => (valuesProjection hW ω, valuesProjection hY ω)) := by
    funext ω
    apply Prod.ext
    · simpa [pairU, Function.comp_apply] using
        congrFun (valuesProjection_comp (Ω' := swigΩ Ω) hW_U hU hW).symm ω
    · simpa [pairU, Function.comp_apply] using
        congrFun (valuesProjection_comp (Ω' := swigΩ Ω) hY_U hU hY).symm ω
  have hR3 :
      (M2.obsKernel s').map (valuesProjection hU_do) =
        (M'.obsKernel (M'.fixSetProj Z hZ_obs hZ_fixed s')).map
          (valuesProjection hU) := by
    simpa [M2, U] using
      condDistrib_intervention_ancestral_eq M' Z hZ_obs hZ_fixed U hU
        (fun z hz v hv => hNoDesc v (by simpa [U] using hv) z hz) s'
  change (M2.obsKernel s').map
      (fun ω =>
        (valuesProjection ((fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hW) ω,
         valuesProjection ((fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hY) ω))
    =
    (M'.obsKernel (M'.fixSetProj Z hZ_obs hZ_fixed s')).map
      (fun ω => (valuesProjection hW ω, valuesProjection hY ω))
  rw [← hPair_do_comp, ← hPair_base_comp]
  rw [← MeasureTheory.Measure.map_map hpairU_meas (measurable_valuesProjection hU_do)]
  rw [← MeasureTheory.Measure.map_map hpairU_meas (measurable_valuesProjection hU)]
  exact congrArg (MeasureTheory.Measure.map pairU) hR3

/-- Rule 3\* on the `W`-marginal.

    Under the ancestral no-descendant premise, the marginal law of the
    conditioning block `W` is unchanged by intervening on `Z`.  This is
    `condDistrib_intervention_ancestral_eq` at outcome block `T := W`. -/
theorem obsKernel_map_W_eq
    (M' : Causalean.SCM N Ω) (Z : Finset N)
    (hZ_obs : ∀ D ∈ Z, SWIGNode.random D ∈ M'.observed)
    (hZ_fixed : ∀ D ∈ Z, SWIGNode.fixed D ∉ M'.fixed)
    (Y W : Finset (SWIGNode N))
    (_hY : Y ⊆ M'.observed)
    (hW : W ⊆ M'.observed)
    (hNoDesc : ∀ v ∈ Y ∪ W, ∀ d ∈ Z,
      ¬ (M'.fixSet Z hZ_obs hZ_fixed).dag.isAncestor (SWIGNode.fixed d) v)
    (s' : (M'.fixSet Z hZ_obs hZ_fixed).FixedValues) :
    ((M'.fixSet Z hZ_obs hZ_fixed).obsKernel s').map
        (valuesProjection ((fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hW))
      =
    (M'.obsKernel (M'.fixSetProj Z hZ_obs hZ_fixed s')).map
        (valuesProjection hW) :=
  condDistrib_intervention_ancestral_eq M' Z hZ_obs hZ_fixed W hW
    (fun z hz v hv => hNoDesc v (Finset.mem_union_right _ hv) z hz) s'

-- ============================================================
-- § 2. Conditional Rule 3
-- ============================================================

/-- **Conditional Rule 3 (literal `condDistrib` form).**

    The conditional distribution of the target block `Y` given the conditioning
    block `W` is the same after intervening on `Z` as under the base model:

        p( Y(z) | W(z) )_{M'.fixSet Z} = p( Y | W )_{M'}.

    Because Rule 3\* makes the two `(W, Y)` joint laws literally equal
    (`obsKernel_map_prodWY_eq`) and `condDistrib` depends only on the joint law
    (`condDistrib_eq_of_map_prod_eq`), the two conditional distributions are
    literally equal — no almost-everywhere qualifier is needed here. -/
theorem do_rule3_conditional_condDistrib
    (M' : Causalean.SCM N Ω) (Z : Finset N)
    (hZ_obs : ∀ D ∈ Z, SWIGNode.random D ∈ M'.observed)
    (hZ_fixed : ∀ D ∈ Z, SWIGNode.fixed D ∉ M'.fixed)
    (Y W : Finset (SWIGNode N))
    (hY : Y ⊆ M'.observed)
    (hW : W ⊆ M'.observed)
    [StandardBorelSpace (ValuesOn Y (swigΩ Ω))]
    [Nonempty (ValuesOn Y (swigΩ Ω))]
    [∀ s : M'.FixedValues, MeasureTheory.IsFiniteMeasure (M'.obsKernel s)]
    [∀ s : (M'.fixSet Z hZ_obs hZ_fixed).FixedValues,
      MeasureTheory.IsFiniteMeasure ((M'.fixSet Z hZ_obs hZ_fixed).obsKernel s)]
    (hNoDesc : ∀ v ∈ Y ∪ W, ∀ d ∈ Z,
      ¬ (M'.fixSet Z hZ_obs hZ_fixed).dag.isAncestor (SWIGNode.fixed d) v)
    (s' : (M'.fixSet Z hZ_obs hZ_fixed).FixedValues) :
    ProbabilityTheory.condDistrib
        (valuesProjection ((fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hY))
        (valuesProjection ((fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hW))
        ((M'.fixSet Z hZ_obs hZ_fixed).obsKernel s')
      =
    ProbabilityTheory.condDistrib (valuesProjection hY) (valuesProjection hW)
        (M'.obsKernel (M'.fixSetProj Z hZ_obs hZ_fixed s')) :=
  condDistrib_eq_of_map_prod_eq
    (obsKernel_map_prodWY_eq M' Z hZ_obs hZ_fixed Y W hY hW hNoDesc s')

/-- **Conditional Rule 3 (headline, a.e. `obsCondKernel` form).**

    Pearl's Rule 3 for the deletion of actions, stated against the project's
    jointly-measurable conditional kernel: for almost every value `w` of the
    conditioning block `W` (w.r.t. its marginal), the `Y | W`-conditional kernel
    of the model intervened at `do(Z)` equals the `Y | W`-conditional kernel of
    the base model.  This is the conditional analogue of the joint Rule 3\*
    `do_rule3`, and the conditional counterpart of the kernel-native Rule 2
    `do_rule2_kernel`.

    The a.e. qualifier is intrinsic to `obsCondKernel` (a disintegration
    representative), not to the intervention: the underlying conditional
    distributions are literally equal by `do_rule3_conditional_condDistrib`; the
    common base measure is the (Rule-3\*-equal) `W`-marginal. -/
theorem do_rule3_conditional
    (M' : Causalean.SCM N Ω) (Z : Finset N)
    (hZ_obs : ∀ D ∈ Z, SWIGNode.random D ∈ M'.observed)
    (hZ_fixed : ∀ D ∈ Z, SWIGNode.fixed D ∉ M'.fixed)
    (Y W : Finset (SWIGNode N))
    (hY : Y ⊆ M'.observed)
    (hW : W ⊆ M'.observed)
    [StandardBorelSpace (ValuesOn Y (swigΩ Ω))]
    [Nonempty (ValuesOn Y (swigΩ Ω))]
    [∀ s : M'.FixedValues, MeasureTheory.IsFiniteMeasure (M'.obsKernel s)]
    [∀ s : (M'.fixSet Z hZ_obs hZ_fixed).FixedValues,
      MeasureTheory.IsFiniteMeasure ((M'.fixSet Z hZ_obs hZ_fixed).obsKernel s)]
    [MeasurableSpace.CountableOrCountablyGenerated
      M'.FixedValues (ValuesOn W (swigΩ Ω))]
    [MeasurableSpace.CountableOrCountablyGenerated
      (M'.fixSet Z hZ_obs hZ_fixed).FixedValues (ValuesOn W (swigΩ Ω))]
    (hNoDesc : ∀ v ∈ Y ∪ W, ∀ d ∈ Z,
      ¬ (M'.fixSet Z hZ_obs hZ_fixed).dag.isAncestor (SWIGNode.fixed d) v)
    (s' : (M'.fixSet Z hZ_obs hZ_fixed).FixedValues) :
    (fun w => (M'.fixSet Z hZ_obs hZ_fixed).obsCondKernel Y W
          ((fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hY)
          ((fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hW)
          (s', w))
      =ᵐ[(M'.obsKernel (M'.fixSetProj Z hZ_obs hZ_fixed s')).map
            (valuesProjection hW)]
    (fun w => M'.obsCondKernel Y W hY hW
          (M'.fixSetProj Z hZ_obs hZ_fixed s', w)) := by
  -- Bridge both `obsCondKernel`s to `condDistrib`, rewrite the do-side base to the
  -- common `W`-marginal (`obsKernel_map_W_eq`) and the do-side conditional to the
  -- base conditional (`do_rule3_conditional_condDistrib`), then chain a.e. equalities.
  have h1 := (M'.fixSet Z hZ_obs hZ_fixed).obsCondKernel_ae_eq_condDistrib Y W
    ((fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hY)
    ((fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hW) s'
  have h2 := M'.obsCondKernel_ae_eq_condDistrib Y W hY hW
    (M'.fixSetProj Z hZ_obs hZ_fixed s')
  have hbase := obsKernel_map_W_eq M' Z hZ_obs hZ_fixed Y W hY hW hNoDesc s'
  have hcd := do_rule3_conditional_condDistrib M' Z hZ_obs hZ_fixed Y W hY hW hNoDesc s'
  rw [hbase] at h1
  rw [hcd] at h1
  exact h1.trans h2.symm

end SCM

end Causalean
