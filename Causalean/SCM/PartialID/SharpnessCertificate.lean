/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.SCM.PartialID.CanonicalModel

/-! # Sharpness certificates for graphical partial-identification bounds

For a graphical partial-identification problem, a valid bound `[L, U]` on a real-valued causal
query is **sharp** when the identified set — the range of the query over the compatible class
of structural causal models — is exactly `[L, U]`. Sharpness is *preferred but not required*:
a valid relaxed bound stands on its own; a sharpness claim must additionally exhibit compatible
models attaining each endpoint.

This file records the sharpness predicate and the standard **certificate**: if the identified
set is order-convex, lies inside `[L, U]` (soundness), and the endpoints `L` and `U` are each
attained by some compatible model, then the bound is sharp. The order-convexity hypothesis is
the usual mixing-path input (a continuous family of compatible models interpolating the query
value); it is left as a hypothesis so the certificate applies to any problem that supplies it.
-/

namespace Causalean.SCM.PartialID

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

/-- A bound `[L, U]` is **sharp** for the real-valued query `obj` over the compatible class of
`(G, As, M₀)` when the identified set (the range of `obj` over the compatible class) is exactly
the closed interval `[L, U]`. -/
def IsSharp (G : SWIGGraph N) (As : Causalean.SCM N Ω → Prop) (M₀ : Causalean.SCM N Ω)
    (obj : Causalean.SCM N Ω → ℝ) (L U : ℝ) : Prop :=
  compatibleInterval G As M₀ obj = Set.Icc L U

/-- **Sharpness certificate.** A sound, order-convex bound whose endpoints are both attained by
compatible models is sharp: if the identified set is contained in `[L, U]` (soundness) and is
order-connected, and some compatible model attains `L` while some compatible model attains `U`,
then the identified set equals `[L, U]`. -/
theorem isSharp_of_attaining (G : SWIGGraph N) (As : Causalean.SCM N Ω → Prop)
    (M₀ : Causalean.SCM N Ω) (obj : Causalean.SCM N Ω → ℝ) (L U : ℝ)
    (hsub : compatibleInterval G As M₀ obj ⊆ Set.Icc L U)
    (hconn : (compatibleInterval G As M₀ obj).OrdConnected)
    (hL : ∃ M, CompatibleSCM G As M₀ M ∧ obj M = L)
    (hU : ∃ M, CompatibleSCM G As M₀ M ∧ obj M = U) :
    IsSharp G As M₀ obj L U := by
  refine Set.Subset.antisymm hsub ?_
  obtain ⟨ML, hML, hobjL⟩ := hL
  obtain ⟨MU, hMU, hobjU⟩ := hU
  have memL : L ∈ compatibleInterval G As M₀ obj := ⟨⟨ML, hML⟩, hobjL⟩
  have memU : U ∈ compatibleInterval G As M₀ obj := ⟨⟨MU, hMU⟩, hobjU⟩
  exact hconn.out memL memU

end Causalean.SCM.PartialID
