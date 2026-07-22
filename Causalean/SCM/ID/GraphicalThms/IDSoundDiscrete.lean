/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.SCM.ID.GraphicalThms.IDAlgorithm
import Causalean.SCM.ID.Density.CountingReference
import Causalean.SCM.ID.DiscreteID.Positive

/-! # On-contract discrete soundness of the graphical ID assembly

`GraphicalThms.IDAlgorithm.id_sound` concludes over the model class
`fun M => DominatedObs M ref ∧ DiscretePositive M`, parameterised by an
arbitrary faithful reference family.  Instantiating that reference at the
counting measure and using that the counting reference dominates every model
(`dominatedObs_countingRef`), the model class collapses to the frozen
discrete-positive class `StandardDiscretePositive` with no graph side conditions
— this is the discrete identification headline the checker soundness theorem
will wrap.
-/

namespace Causalean.SCM.ID

open Causalean.SCM Causalean.SCM.ID.DiscreteID
open scoped MeasureTheory ProbabilityTheory

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

/-- **Discrete soundness of the ID assembly for the no-additional-fixing
(full-district) fragment (on-contract).**  A successful `idSucceeds` certificate
identifies the interventional query within the standard discrete positive model
class.  This is a *sound sufficient fragment* of Tian–Shpitser ID soundness, not
the full recursive ID algorithm: `idSucceeds` only certifies the case where every
post-intervention ancestral district is already a full c-component of the original
graph (no fixing sequence needed); the recursive case is `id_sound_rec`.  Because
`idSucceeds` requires `Y ⊆ G.observed`, the query lies on its meaningful
`doKernelY` branch, so the conclusion is genuine identification, not a
dummy-kernel triviality.  Obtained from `id_sound` at the counting reference by
collapsing `DominatedObs · countingRef` (which holds for every model) down to
`StandardDiscretePositive` via `identifiableUnder_mono`. -/
theorem id_sound_discrete
    [∀ n, StandardBorelSpace (Ω n)] [∀ n, Nonempty (Ω n)]
    [∀ n, Fintype (Ω n)] [∀ n, MeasurableSingletonClass (Ω n)]
    (X : Finset N) (Y : Finset (SWIGNode N)) (G : SWIGGraph N)
    (h : idSucceeds X Y G) :
    IdentifiableUnder G (fun _ => True) StandardDiscretePositive
      (interventionalQuery (Ω := Ω) X Y) := by
  have hdom :=
    id_sound X Y G (countingRef (Ω := Ω)) referenceFaithful_countingRef h
  exact identifiableUnder_mono G (fun _ => True) (fun _ => True)
    (fun M => DominatedObs M (countingRef (Ω := Ω)) ∧ DiscretePositive M)
    StandardDiscretePositive (interventionalQuery (Ω := Ω) X Y)
    (fun _ h => h) (fun M hM => ⟨dominatedObs_countingRef M, hM.2⟩) hdom

end Causalean.SCM.ID
