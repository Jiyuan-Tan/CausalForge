/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.SCM.ID.Identifiable
import Causalean.PO.ID.Partial.Basic

/-! # Compatible structural causal models for graphical partial identification

This file provides the object over which graphical **partial identification** quantifies:
the class of structural causal models that share a given causal diagram, satisfy stated
structural assumptions, and reproduce a reference observational law. A bound on a causal
query is *sound* when every model in this class satisfies it, and the resulting identified
set is the range of the query over the class.

Concretely, fixing a SWIG graph `G`, a structural-assumption predicate `As`, and a reference
model `M₀`, the **compatible class** collects the models `M` that (i) have diagram `G`, (ii)
satisfy `As`, and (iii) are observationally equivalent to `M₀` (same derived observational
kernel). The **compatible interval** of a real-valued query is the range of that query over
the compatible class — an instance of the abstract `IdentifiedInterval` from the
potential-outcomes partial-identification layer, so the existing sharpness / order-convexity
lemmas apply.

## Finite response-function reduction

The finite canonical response-function *reduction* says that every measure-theoretic model in
the compatible class is behaviourally matched by a model over a finite exogenous domain
(Zhang–Tian–Bareinboim). It is not included here: the Causalean SCM layer is
measure-theoretic (`Causalean.SCM` carries `MeasureTheory.Measure` latents), so this reduction
is a genuine theorem, not a definitional unfolding. It is needed only when a *sharpness* claim
must be discharged by enumerating finitely many realising models; soundness of a bound does not
require it. The only finite realisation currently in the library is the Balke–Pearl construction
in the potential-outcomes framework
(`Causalean/PO/ID/Partial/BalkePearl/`).
-/

namespace Causalean.SCM.PartialID

variable {N : Type*} [DecidableEq N] [Fintype N]
variable {Ω : N → Type*} [∀ n, MeasurableSpace (Ω n)]

/-- The **compatible class** for a graphical partial-identification problem: the structural
causal models `M` that share the SWIG graph `G`, satisfy the structural assumptions `As`, and
are observationally equivalent to the reference model `M₀` (their derived observational
kernels agree). This is the class over which a bound must hold to be *sound*. -/
def CompatibleSCM (G : SWIGGraph N) (As : Causalean.SCM N Ω → Prop)
    (M₀ : Causalean.SCM N Ω) : Causalean.SCM N Ω → Prop :=
  fun M => M.toSWIGGraph = G ∧ As M ∧ Causalean.SCM.ID.obsEquiv M M₀

/-- The reference model itself belongs to its compatible class, provided it has the declared
graph and satisfies the structural assumptions. -/
theorem compatibleSCM_self (G : SWIGGraph N) (As : Causalean.SCM N Ω → Prop)
    (M₀ : Causalean.SCM N Ω) (hG : M₀.toSWIGGraph = G) (hAs : As M₀) :
    CompatibleSCM G As M₀ M₀ :=
  ⟨hG, hAs, HEq.rfl⟩

/-- Strengthening the structural assumptions can only shrink the compatible class:
if `As'` implies `As`, every `As'`-compatible model is `As`-compatible. -/
theorem compatibleSCM_mono {G : SWIGGraph N} {As As' : Causalean.SCM N Ω → Prop}
    {M₀ : Causalean.SCM N Ω} (h : ∀ M, As' M → As M) :
    ∀ M, CompatibleSCM G As' M₀ M → CompatibleSCM G As M₀ M :=
  fun _ hM => ⟨hM.1, h _ hM.2.1, hM.2.2⟩

/-- The **compatible interval** of a real-valued causal query: its range over the compatible
class. This is the graphical identified set; a partial-identification bound `[L, U]` is *sound*
exactly when this set is contained in `Set.Icc L U`, and *sharp* when they are equal. Built on
the abstract `IdentifiedInterval`, so the order-convexity / sharpness lemmas of the
partial-identification layer apply. -/
noncomputable def compatibleInterval (G : SWIGGraph N) (As : Causalean.SCM N Ω → Prop)
    (M₀ : Causalean.SCM N Ω) (obj : Causalean.SCM N Ω → ℝ) : Set ℝ :=
  Causalean.PartialID.IdentifiedInterval obj (CompatibleSCM G As M₀)

end Causalean.SCM.PartialID
