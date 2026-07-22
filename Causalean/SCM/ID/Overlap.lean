/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Rule 2 / backdoor overlap predicate

The kernel-level absolute-continuity (overlap) predicate consumed by the
kernel-native do-calculus Rule 2 and the backdoor / frontdoor identification
theorems.

## Main definition

* `Rule2JointOverlap M' Z hZ_obs hZ_fixed W hZrW s'` — the do-intervened
  model's `(Z.random ∪ W)`-marginal is absolutely continuous w.r.t. the base
  model's `(Z.random ∪ W)`-marginal.  Continuous-friendly: no pointwise
  singleton positivity is required.

## References

* Basic Concepts.tex, Definition 2.12 (overlap assumption); the quantitative
  small-value (weak-overlap) rate analysis — polynomial lower-tail inverse
  moments — is developed separately under `Stat/PolynomialTail/`.
-/

import Causalean.SCM.Model.SCM
import Causalean.SCM.Model.Kernel
import Causalean.SCM.Model.InterventionSet
import Causalean.SCM.Do.Rule2Kernel.Helpers

/-! # Overlap

This file defines the kernel-level overlap condition used by do-calculus
identification rules. The main predicate, `Rule2JointOverlap`, requires the
post-intervention marginal on `Z.random ∪ W` to be absolutely continuous with
respect to the corresponding observational marginal. This continuous-friendly
support condition feeds the kernel-native Rule 2 and the backdoor/frontdoor
identification theorems without imposing pointwise singleton positivity. -/

namespace Causalean.SCM.ID

open scoped MeasureTheory ProbabilityTheory
open Causalean

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

/-- **Rule 2 joint overlap (canonical, continuous-friendly).**  Absolute
    continuity of the `(Z.image .random ∪ W)`-marginal of
    `(M'.fixSet Z).obsKernel s'` w.r.t. the same marginal of
    `M'.obsKernel (fixSetProj s')`.

    A kernel-level absolute-continuity predicate with no pointwise
    singleton positivity requirement.  Holds trivially in the discrete
    case (the two marginals literally agree on the `Z.rand`-level set,
    cf. `obsKernel_inter_singleton_Zrand_eq`); holds in the continuous
    case whenever the SCM's structural functions are measurable and the
    latent measures match (`fixSet` only rewires structural fns at `Z`).

    Used by `obsCondKernel_fixSet_eq` (kernel-native Rule 2) and through
    it by `do_rule2_kernel` and the backdoor / frontdoor identification
    theorems. -/
def Rule2JointOverlap (M' : Causalean.SCM N Ω) (Z : Finset N)
    (hZ_obs : ∀ D ∈ Z, SWIGNode.random D ∈ M'.observed)
    (hZ_fixed : ∀ D ∈ Z, SWIGNode.fixed D ∉ M'.fixed)
    (W : Finset (SWIGNode N))
    (hZrW : Z.image SWIGNode.random ∪ W ⊆ M'.observed)
    (s' : (M'.fixSet Z hZ_obs hZ_fixed).FixedValues) :
    Prop :=
  ((M'.fixSet Z hZ_obs hZ_fixed).obsKernel s'
      |>.map (valuesProjection
        ((SCM.fixSet_observed M' Z hZ_obs hZ_fixed).symm ▸ hZrW)))
    ≪
  (M'.obsKernel (M'.fixSetProj Z hZ_obs hZ_fixed s')
      |>.map (valuesProjection hZrW))

end Causalean.SCM.ID
