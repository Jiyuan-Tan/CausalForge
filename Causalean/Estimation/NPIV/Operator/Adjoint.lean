/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Bundled CLM lift of the projection operator `T` and its adjoint

This file defines the **bounded-linear-operator** layer needed by the
spectral discharge of the Tikhonov bias bound.  The function-level operator
`OperatorSystem.T : Lp ℝ 2 μ → Lp ℝ 2 μ` defined in
`Causalean/Estimation/NPIV/Operator.lean` is here re-packaged as a bundled
`ContinuousLinearMap`

    `S.Tlin : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ`

obtained by composing the orthogonal-projection CLM `Qbar_L2.starProjection`
with the conditional-expectation CLM `condExpL2 ℝ ℝ S.m_Z_le` (and the
canonical inclusion `lpMeas → Lp`).

We then expose the **adjoint** `Tadjoint := S.Tlin.adjoint` and the
self-adjoint composite `Tstar_T := Tadjoint.comp Tlin`, which is the
operator the source condition refers to.  Self-adjointness follows from
`IsSelfAdjoint.star_mul_self` once we identify `Tadjoint` with `star Tlin`
in the C⋆-algebra `Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ`.

All declarations in this file are fully proved (no sorries).
-/

import Causalean.Estimation.NPIV.Operator
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
Builds the bundled continuous-linear-map representation of the NPIV operator
and its adjoint. These operator-theoretic objects feed Tikhonov regularization
and spectral arguments.
-/

namespace Causalean
namespace Estimation
namespace NPIV

namespace OperatorSystem

open MeasureTheory ContinuousLinearMap

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## Bundled CLM `Tlin` -/

/-- The conditional-expectation step `f ↦ E[f | σ(Z)]`, viewed as a
continuous ℝ-linear endomorphism of `Lp ℝ 2 μ`.

This is `condExpL2 ℝ ℝ S.m_Z_le` post-composed with the canonical
inclusion of the closed subspace `lpMeas ℝ ℝ S.m_Z 2 μ` of σ(Z)-measurable
L² classes back into the ambient `Lp ℝ 2 μ`. -/
noncomputable def condExpStepL (S : OperatorSystem Ω μ) :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  haveI := S.isFiniteMeasure
  (lpMeas ℝ ℝ S.m_Z 2 μ).subtypeL.comp (MeasureTheory.condExpL2 ℝ ℝ S.m_Z_le)

/-- The bundled continuous-linear-map version of `OperatorSystem.T`:

    `Tlin = Qbar_L2.starProjection ∘L condExpStepL`.

`starProjection` (from `Mathlib.Analysis.InnerProductSpace.Projection.Basic`)
bundles the orthogonal projection into `Qbar_L2` followed by the subtype
inclusion, both as one CLM `Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ`. -/
noncomputable def Tlin (S : OperatorSystem Ω μ) :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  haveI := S.Qbar_L2_hasProj
  S.Qbar_L2.starProjection.comp S.condExpStepL

/-- Coherence: applying the bundled CLM `Tlin` to `f` agrees with the
function-level operator `T` from `Causalean/Estimation/NPIV/Operator.lean`.
The proof unfolds both sides and uses
`Submodule.starProjection_apply = orthogonalProjectionFn`. -/
lemma Tlin_apply (S : OperatorSystem Ω μ) (f : Lp ℝ 2 μ) :
    S.Tlin f = S.T f := by
  rfl

/-! ## Adjoint and the self-adjoint composite `T*T` -/

/-- The adjoint operator `T† : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ`.

Defined via Mathlib's `ContinuousLinearMap.adjoint` on the Hilbert space
`Lp ℝ 2 μ` (which has the `InnerProductSpace ℝ` instance from
`MeasureTheory.L2Space.innerProductSpace`). -/
noncomputable def Tadjoint (S : OperatorSystem Ω μ) :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  ContinuousLinearMap.adjoint S.Tlin

/-- The self-adjoint, positive-semidefinite composite `T† T`.  This is
the operator the β-source condition refers to:
`h₀ = (T*T)^{β/2} w₀` is interpreted via Mathlib's continuous functional
calculus on this CLM. -/
noncomputable def Tstar_T (S : OperatorSystem Ω μ) :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  S.Tadjoint.comp S.Tlin

/-- `T† T` is self-adjoint.  Follows from `IsSelfAdjoint.star_mul_self`
in the C⋆-algebra `Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ`, after identifying
`Tadjoint` with `star Tlin` and `comp` with `*`
(`ContinuousLinearMap.mul_def`). -/
lemma Tstar_T_isSelfAdjoint (S : OperatorSystem Ω μ) :
    IsSelfAdjoint S.Tstar_T := by
  unfold Tstar_T Tadjoint
  simpa [ContinuousLinearMap.mul_def, ContinuousLinearMap.star_eq_adjoint] using
    IsSelfAdjoint.star_mul_self S.Tlin

end OperatorSystem

end NPIV
end Estimation
end Causalean
