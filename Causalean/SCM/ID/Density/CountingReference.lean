/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.SCM.ID.Density.FiniteReference

/-! # The counting reference measure for finite discrete models

On finite node value spaces the canonical reference family is the per-node
counting measure.  It is faithful — every singleton has counting mass one — so,
via `absolutelyContinuous_jointRef_of_faithful`, *every* structural causal model
is dominated by it.  This supplies the domination half of the general
density-route identification theorem `id_sound`, whose model class is
`DominatedObs · ref ∧ DiscretePositive`; the positivity half is supplied by the
standard discrete positive model class.
-/

namespace Causalean.SCM

open scoped MeasureTheory ProbabilityTheory

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

/-- The counting reference family: each SWIG-node coordinate carries the counting
measure.  On finite value spaces this is a finite, hence σ-finite, measure. -/
noncomputable def countingRef
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)] :
    ReferenceMeasures Ω where
  μ := fun _ => MeasureTheory.Measure.count
  sigmaFinite := fun _ => by
    infer_instance

/-- The counting reference family is faithful: every singleton coordinate value
has counting mass one, in particular nonzero. -/
lemma referenceFaithful_countingRef
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)] :
    ReferenceFaithful (countingRef (Ω := Ω)) := by
  intro v x
  unfold countingRef
  rw [MeasureTheory.Measure.count_singleton]
  exact one_ne_zero

/-- Every structural causal model is dominated by the counting reference family:
each observational law is absolutely continuous with respect to the counting
product, because a faithful reference dominates every measure on a finite
product.  Note this holds for *all* `M`, with no positivity or graph hypothesis. -/
lemma dominatedObs_countingRef
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (M : Causalean.SCM N Ω) :
    DominatedObs M (countingRef (Ω := Ω)) := by
  intro s
  exact absolutelyContinuous_jointRef_of_faithful (countingRef (Ω := Ω))
    referenceFaithful_countingRef M.observed (M.obsKernel s)

end Causalean.SCM
