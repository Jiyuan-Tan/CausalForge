/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Complexification layer for the NPIV operator `Tlin`

This file packages the spectral-analysis support used to discharge
`TikhonovBiasBound`.  Its purpose is to provide a **Mathlib gap workaround** so
downstream NPIV rate proofs can apply the continuous functional calculus to the
self-adjoint composite `T†T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ`.

## Why this file exists

Mathlib's `cfc` for self-adjoint operators (see
`Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital`)
requires the typeclasses `Algebra ℂ A` and
`ContinuousFunctionalCalculus ℂ A IsStarNormal`.  For the real-scalar CLM
algebra `A := Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ` neither instance is registered
in Mathlib; see the discussion in `Operator/SpectralCalculus.lean` lines
34–53.

The standard workaround implemented here is:

* Embed `Lp ℝ 2 μ` isometrically into `Lp ℂ 2 μ` as the real subspace
  (`ιLp`), with left-inverse `reLp`.
* Lift any real CLM `A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ` to a complex CLM
  `complexLift A : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ` whose action on the
  real subspace recovers `A`.
* Define a "real CFC by complexification" `realCFC A f` by applying the
  complex `cfc` to `complexLift A` with the lifted symbol
  `fun z : ℂ => (f z.re : ℂ)` and projecting back via `reLp`.

`realCFC` is the real-operator API used by the spectral rate layer in place
of a native real continuous functional calculus.

## Outputs

* `reLp`, `imLp` — pointwise real / imaginary part on `Lp ℂ 2 μ`,
  bundled as `Lp ℂ 2 μ →L[ℝ] Lp ℝ 2 μ`.
* `ιLp` — pointwise inclusion `Lp ℝ 2 μ →L[ℝ] Lp ℂ 2 μ`.
* Section / reconstruction lemmas for the triple `(reLp, imLp, ιLp)`.
* `complexLift A : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ` — complex lift of a real
  CLM `A`, with action equation `complexLift_apply` and section lemma
  `complexLift_real`.
* `complexLift_adjoint`, `complexLift_isSelfAdjoint` — adjoint and
  self-adjointness compatibility with the lift.
* `realCFC A f : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ` — real CFC by
  complexification, with API lemmas `realCFC_apply`, `realCFC_id`,
  `realCFC_isSelfAdjoint`.  The file intentionally exports only the laws
  currently needed by the spectral bias proof; a CFC composition law would need
  the `realCFC (realCFC A g) f` shape, not the false
  `(realCFC A f).comp (realCFC A g)` shape.

All declarations in this file are fully proved (no sorries).
-/

import Causalean.Estimation.NPIV.Operator.Adjoint
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.RCLike.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-!
Provides real-to-complex L2 operator glue for NPIV spectral calculations. The
module relates real conditional-moment operators to complexified continuous
linear maps and their self-adjointness properties.
-/

namespace Causalean
namespace Estimation
namespace NPIV
namespace Complexification

open MeasureTheory ContinuousLinearMap

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## Section 1.  Real ↔ complex `L²` glue -/

/-- Pointwise real part on `L²(Ω, ℂ)`, bundled as a continuous
ℝ-linear map `Lp ℂ 2 μ →L[ℝ] Lp ℝ 2 μ`.

Built from `RCLike.reCLM (K := ℂ) : ℂ →L[ℝ] ℝ` via
`ContinuousLinearMap.compLpL 2 μ`, which lifts a CLM on the value
spaces to a CLM between the corresponding `Lp` spaces.  The `Fact
(1 ≤ (2 : ENNReal))` premise is supplied by `fact_one_le_two_ennreal`. -/
noncomputable def reLp : Lp ℂ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  ContinuousLinearMap.compLpL 2 μ (RCLike.reCLM (K := ℂ))

/-- Pointwise imaginary part on `L²(Ω, ℂ)`, bundled as a continuous
ℝ-linear map `Lp ℂ 2 μ →L[ℝ] Lp ℝ 2 μ`.  Same construction as
`reLp` but with `RCLike.imCLM`. -/
noncomputable def imLp : Lp ℂ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  ContinuousLinearMap.compLpL 2 μ (RCLike.imCLM (K := ℂ))

/-- Pointwise embedding of real-valued `L²` into complex-valued `L²`,
bundled as a continuous ℝ-linear map `Lp ℝ 2 μ →L[ℝ] Lp ℂ 2 μ`.

Built from `RCLike.ofRealCLM (K := ℂ) : ℝ →L[ℝ] ℂ` via
`ContinuousLinearMap.compLpL 2 μ`. -/
noncomputable def ιLp : Lp ℝ 2 μ →L[ℝ] Lp ℂ 2 μ :=
  ContinuousLinearMap.compLpL 2 μ (RCLike.ofRealCLM (K := ℂ))

/-- `reLp` is a left-inverse of `ιLp`.

The pointwise statement is `RCLike.re_ofReal : RCLike.re (r : ℂ) = r`.
The Lp version follows by combining
`ContinuousLinearMap.coeFn_compLpL` (twice — once for `reLp`, once for
`ιLp`) and the pointwise identity, then rewriting back with
`Lp.ext`-style reasoning.  A clean one-liner is:
`simp [reLp, ιLp, ContinuousLinearMap.compLp_compLp, RCLike.reCLM_apply,
RCLike.ofRealCLM_apply, RCLike.re_ofReal]`. -/
lemma reLp_comp_ιLp (f : Lp ℝ 2 μ) : reLp (ιLp f) = f := by
  apply Lp.ext
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (RCLike.reCLM (K := ℂ)) (ιLp f),
                  ContinuousLinearMap.coeFn_compLpL (RCLike.ofRealCLM (K := ℂ)) f]
    with ω h₁ h₂
  simpa [reLp, ιLp, h₂, RCLike.reCLM_apply, RCLike.ofRealCLM_apply,
    RCLike.ofReal_re] using h₁

/-- The imaginary part vanishes on the image of `ιLp` (pointwise
`RCLike.im_ofReal : RCLike.im (r : ℂ) = 0`). -/
lemma imLp_comp_ιLp (f : Lp ℝ 2 μ) : imLp (ιLp f) = 0 := by
  apply Lp.ext
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (RCLike.imCLM (K := ℂ)) (ιLp f),
                  ContinuousLinearMap.coeFn_compLpL (RCLike.ofRealCLM (K := ℂ)) f,
                  (Lp.coeFn_zero ℝ (2 : ENNReal) μ)]
    with ω h₁ h₂ hzero
  have hmain : (((imLp (ιLp f) : Lp ℝ 2 μ) : Ω → ℝ) ω) =
      (RCLike.imCLM (K := ℂ))
        ((RCLike.ofRealCLM (K := ℂ)) (((f : Lp ℝ 2 μ) : Ω → ℝ) ω)) := by
    simpa [imLp, ιLp, h₂] using h₁
  calc
    (((imLp (ιLp f) : Lp ℝ 2 μ) : Ω → ℝ) ω) =
        (RCLike.imCLM (K := ℂ))
          ((RCLike.ofRealCLM (K := ℂ)) (((f : Lp ℝ 2 μ) : Ω → ℝ) ω)) := hmain
    _ = 0 := by
      change RCLike.im
          ((RCLike.ofRealCLM (K := ℂ)) (((f : Lp ℝ 2 μ) : Ω → ℝ) ω)) = 0
      change RCLike.im ((((f : Lp ℝ 2 μ) : Ω → ℝ) ω : ℝ) : ℂ) = 0
      exact RCLike.ofReal_im (((f : Lp ℝ 2 μ) : Ω → ℝ) ω)
    _ = ((0 : Lp ℝ 2 μ) : Ω → ℝ) ω := by rw [hzero]; rfl

/-- `ιLp` is an isometric embedding.  Follows from
`RCLike.ofRealLI` being a `LinearIsometry` and the fact that
`compLpL` of a norm-one CLM preserves norms on `L²`; concretely,
`‖ιLp f‖ = ‖f‖` reduces pointwise to `‖(r : ℂ)‖ = ‖r‖`
(`RCLike.norm_ofReal`). -/
lemma ιLp_isometry (f : Lp ℝ 2 μ) : ‖ιLp f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  apply congrArg ENNReal.toReal
  apply MeasureTheory.eLpNorm_congr_norm_ae
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (RCLike.ofRealCLM (K := ℂ)) f]
    with ω h
  rw [show (((ιLp f : Lp ℂ 2 μ) : Ω → ℂ) ω) =
      (RCLike.ofRealCLM (K := ℂ)) (((f : Lp ℝ 2 μ) : Ω → ℝ) ω) by
    simpa [ιLp] using h]
  change ‖(RCLike.ofRealCLM (K := ℂ)) (((f : Lp ℝ 2 μ) : Ω → ℝ) ω)‖ =
      ‖(((f : Lp ℝ 2 μ) : Ω → ℝ) ω)‖
  rw [show (RCLike.ofRealCLM (K := ℂ)) (((f : Lp ℝ 2 μ) : Ω → ℝ) ω) =
      ((((f : Lp ℝ 2 μ) : Ω → ℝ) ω : ℝ) : ℂ) by
    rw [RCLike.ofRealCLM_apply]
    rfl]
  exact RCLike.norm_ofReal (((f : Lp ℝ 2 μ) : Ω → ℝ) ω)

/-- **Reconstruction identity**: every complex `L²`-class is the
complex combination of its real and imaginary parts re-embedded via
`ιLp`.  Pointwise this is `RCLike.re_add_im : (r.re : ℂ) + I * r.im = r`.

The displayed form uses the ℂ-action on `Lp ℂ 2 μ` (which is the
standard `Lp` module structure when the value space is ℂ). -/
lemma reLp_add_smul_imLp (f : Lp ℂ 2 μ) :
    ιLp (reLp f) + (Complex.I : ℂ) • ιLp (imLp f) = f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (ιLp (reLp f)) ((Complex.I : ℂ) • ιLp (imLp f)),
                  Lp.coeFn_smul (Complex.I : ℂ) (ιLp (imLp f)),
                  ContinuousLinearMap.coeFn_compLpL (RCLike.ofRealCLM (K := ℂ)) (reLp f),
                  ContinuousLinearMap.coeFn_compLpL (RCLike.ofRealCLM (K := ℂ)) (imLp f),
                  ContinuousLinearMap.coeFn_compLpL (RCLike.reCLM (K := ℂ)) f,
                  ContinuousLinearMap.coeFn_compLpL (RCLike.imCLM (K := ℂ)) f]
    with ω h_add h_smul h_re_embed h_im_embed h_re h_im
  rw [h_add]
  simp only [Pi.add_apply]
  rw [h_smul]
  simp only [Pi.smul_apply]
  rw [show (((ιLp (reLp f) : Lp ℂ 2 μ) : Ω → ℂ) ω) =
      (RCLike.ofRealCLM (K := ℂ)) (((reLp f : Lp ℝ 2 μ) : Ω → ℝ) ω) by
    simpa [ιLp] using h_re_embed]
  rw [show (((ιLp (imLp f) : Lp ℂ 2 μ) : Ω → ℂ) ω) =
      (RCLike.ofRealCLM (K := ℂ)) (((imLp f : Lp ℝ 2 μ) : Ω → ℝ) ω) by
    simpa [ιLp] using h_im_embed]
  rw [show (((reLp f : Lp ℝ 2 μ) : Ω → ℝ) ω) =
      (RCLike.reCLM (K := ℂ)) (((f : Lp ℂ 2 μ) : Ω → ℂ) ω) by
    simpa [reLp] using h_re]
  rw [show (((imLp f : Lp ℝ 2 μ) : Ω → ℝ) ω) =
      (RCLike.imCLM (K := ℂ)) (((f : Lp ℂ 2 μ) : Ω → ℂ) ω) by
    simpa [imLp] using h_im]
  change (RCLike.re (((f : Lp ℂ 2 μ) : Ω → ℂ) ω) : ℂ) +
      Complex.I * (RCLike.im (((f : Lp ℂ 2 μ) : Ω → ℂ) ω) : ℂ) =
    (((f : Lp ℂ 2 μ) : Ω → ℂ) ω)
  rw [mul_comm]
  exact RCLike.re_add_im (((f : Lp ℂ 2 μ) : Ω → ℂ) ω)

/-! ## Section 2.  Operator lift `complexLift` -/

/-- The function-level definition of the complex lift.  Given a real
CLM `A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ` and a complex `L²` class `f`, the
lift sends `f = (Re f) + i (Im f)` to `A(Re f) + i · A(Im f)` (with
the real outputs re-embedded via `ιLp`).

This is the candidate underlying function for `complexLift`.  ℂ-linearity
of the corresponding map is the only non-trivial obligation: it follows
from ℝ-linearity of `A`, `reLp`, `imLp`, `ιLp`, plus the fact that
multiplication by `i` permutes real and imaginary parts. -/
noncomputable def complexLiftFun
    (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (f : Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  ιLp (A (reLp f)) + (Complex.I : ℂ) • ιLp (A (imLp f))

private lemma reLp_I_smul (f : Lp ℂ 2 μ) :
    reLp ((Complex.I : ℂ) • f) = -imLp f := by
  apply Lp.ext
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (RCLike.reCLM (K := ℂ))
                    ((Complex.I : ℂ) • f),
                  Lp.coeFn_smul (Complex.I : ℂ) f,
                  Lp.coeFn_neg (imLp f),
                  ContinuousLinearMap.coeFn_compLpL (RCLike.imCLM (K := ℂ)) f]
    with ω h_re h_smul h_neg h_f
  rw [h_neg]
  simp only [Pi.neg_apply]
  rw [show (((reLp ((Complex.I : ℂ) • f) : Lp ℝ 2 μ) : Ω → ℝ) ω) =
      (RCLike.reCLM (K := ℂ)) ((((Complex.I : ℂ) • f : Lp ℂ 2 μ) : Ω → ℂ) ω) by
    simpa [reLp] using h_re]
  rw [h_smul]
  simp only [Pi.smul_apply]
  rw [show (((imLp f : Lp ℝ 2 μ) : Ω → ℝ) ω) =
      (RCLike.imCLM (K := ℂ)) (((f : Lp ℂ 2 μ) : Ω → ℂ) ω) by
    simpa [imLp] using h_f]
  change (Complex.I * (((f : Lp ℂ 2 μ) : Ω → ℂ) ω)).re =
    -((((f : Lp ℂ 2 μ) : Ω → ℂ) ω).im)
  simp

private lemma imLp_I_smul (f : Lp ℂ 2 μ) :
    imLp ((Complex.I : ℂ) • f) = reLp f := by
  apply Lp.ext
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (RCLike.imCLM (K := ℂ))
                    ((Complex.I : ℂ) • f),
                  Lp.coeFn_smul (Complex.I : ℂ) f,
                  ContinuousLinearMap.coeFn_compLpL (RCLike.reCLM (K := ℂ)) f]
    with ω h_im h_smul h_f
  rw [show (((imLp ((Complex.I : ℂ) • f) : Lp ℝ 2 μ) : Ω → ℝ) ω) =
      (RCLike.imCLM (K := ℂ)) ((((Complex.I : ℂ) • f : Lp ℂ 2 μ) : Ω → ℂ) ω) by
    simpa [imLp] using h_im]
  rw [h_smul]
  simp only [Pi.smul_apply]
  rw [show (((reLp f : Lp ℝ 2 μ) : Ω → ℝ) ω) =
      (RCLike.reCLM (K := ℂ)) (((f : Lp ℂ 2 μ) : Ω → ℂ) ω) by
    simpa [reLp] using h_f]
  change (Complex.I * (((f : Lp ℂ 2 μ) : Ω → ℂ) ω)).im =
    (((f : Lp ℂ 2 μ) : Ω → ℂ) ω).re
  simp

private noncomputable def I_smulCLM : Lp ℂ 2 μ →L[ℝ] Lp ℂ 2 μ :=
  let L : Lp ℂ 2 μ →ₗ[ℝ] Lp ℂ 2 μ :=
    { toFun := fun f => (Complex.I : ℂ) • f
      map_add' := by
        intro f g
        simp [smul_add]
      map_smul' := by
        intro r f
        apply Lp.ext
        filter_upwards [Lp.coeFn_smul (Complex.I : ℂ) (r • f),
                        Lp.coeFn_smul r f,
                        Lp.coeFn_smul r ((Complex.I : ℂ) • f),
                        Lp.coeFn_smul (Complex.I : ℂ) f]
          with ω h_left h_rf h_right h_if
        change ((((Complex.I : ℂ) • (r • f : Lp ℂ 2 μ) : Lp ℂ 2 μ) : Ω → ℂ) ω) =
          (((r • ((Complex.I : ℂ) • f) : Lp ℂ 2 μ) : Ω → ℂ) ω)
        rw [h_left, h_right]
        simp only [Pi.smul_apply]
        rw [h_rf, h_if]
        change Complex.I * ((r : ℂ) * (((f : Lp ℂ 2 μ) : Ω → ℂ) ω)) =
          (r : ℂ) * (Complex.I * (((f : Lp ℂ 2 μ) : Ω → ℂ) ω))
        ring }
  L.mkContinuous 1 (by
    intro f
    rw [show ‖L f‖ = ‖f‖ by
      change ‖(Complex.I : ℂ) • f‖ = ‖f‖
      simpa using (norm_smul (Complex.I : ℂ) f)]
    rw [one_mul])

private lemma complexLiftFun_I_smul
    (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (f : Lp ℂ 2 μ) :
    complexLiftFun A ((Complex.I : ℂ) • f) = (Complex.I : ℂ) • complexLiftFun A f := by
  simp [complexLiftFun, reLp_I_smul, imLp_I_smul, map_neg, smul_add, smul_smul,
    add_comm]

private lemma complexLiftFun_map_smul
    (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (c : ℂ) (f : Lp ℂ 2 μ) :
    complexLiftFun A (c • f) = c • complexLiftFun A f := by
  let M : Lp ℂ 2 μ →L[ℝ] Lp ℂ 2 μ :=
    (ιLp.comp (A.comp reLp)) + (I_smulCLM.comp (ιLp.comp (A.comp imLp)))
  have hM : ∀ g, M g = complexLiftFun A g := by
    intro g
    rfl
  have hI : ∀ g, M ((Complex.I : ℂ) • g) = (Complex.I : ℂ) • M g := by
    intro g
    rw [hM, hM]
    exact complexLiftFun_I_smul A g
  calc
    complexLiftFun A (c • f) = M (c • f) := by rw [hM]
    _ = M (((c.re : ℂ) + Complex.I * (c.im : ℂ)) • f) := by
      rw [show (c.re : ℂ) + Complex.I * (c.im : ℂ) = c by
        rw [mul_comm]
        exact RCLike.re_add_im c]
    _ = M (((c.re : ℂ) • f) + ((Complex.I * (c.im : ℂ)) • f)) := by
      rw [add_smul]
    _ = M ((c.re : ℝ) • f) + M ((Complex.I : ℂ) • ((c.im : ℝ) • f)) := by
      rw [map_add, mul_smul]
      rfl
    _ = (c.re : ℝ) • M f + (Complex.I : ℂ) • ((c.im : ℝ) • M f) := by
      rw [M.map_smul, hI, M.map_smul]
    _ = ((c.re : ℂ) + Complex.I * (c.im : ℂ)) • M f := by
      rw [add_smul, mul_smul]
      rfl
    _ = c • complexLiftFun A f := by
      rw [show (c.re : ℂ) + Complex.I * (c.im : ℂ) = c by
        rw [mul_comm]
        exact RCLike.re_add_im c, hM]

/-- **Complex lift** of a real CLM.

`complexLift A : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ` is the unique ℂ-linear
continuous extension of `A` to the complexified `L²`.  Its underlying
function is `complexLiftFun A` (see `complexLift_apply` below).

Construction strategy for the proof-filler: build the bare `LinearMap`
over ℂ from `complexLiftFun A` (additivity is direct from additivity of
`reLp`, `imLp`, `ιLp` and `A`; ℂ-linearity reduces, after writing every
`c : ℂ` as `c.re + i c.im`, to ℝ-linearity of `A`), then bundle to a
`ContinuousLinearMap` via `LinearMap.mkContinuous` with a norm bound of
roughly `2 * ‖A‖` coming from
`‖ιLp (A (reLp f)) + I • ιLp (A (imLp f))‖ ≤ ‖A‖ ‖reLp f‖ + ‖A‖ ‖imLp f‖
≤ 2 ‖A‖ ‖f‖`. -/
noncomputable def complexLift
    (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  let M : Lp ℂ 2 μ →L[ℝ] Lp ℂ 2 μ :=
    (ιLp.comp (A.comp reLp)) + (I_smulCLM.comp (ιLp.comp (A.comp imLp)))
  let L : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ :=
    { toFun := M
      map_add' := by
        intro f g
        exact M.map_add f g
      map_smul' := by
        intro c f
        simpa [M, complexLiftFun, I_smulCLM] using complexLiftFun_map_smul A c f }
  L.mkContinuous ‖M‖ (by
    intro f
    have h := M.le_opNorm f
    simpa [L] using h)

/-- The action equation for `complexLift`: it agrees with
`complexLiftFun A` on every input.

This is the contract that downstream proofs will rewrite by — together
with `reLp_comp_ιLp` and `imLp_comp_ιLp`, it is enough to compute
`complexLift A` on explicit elements of `Lp ℂ 2 μ`. -/
theorem complexLift_apply (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (f : Lp ℂ 2 μ) :
    complexLift A f
      = ιLp (A (reLp f)) + (Complex.I : ℂ) • ιLp (A (imLp f)) := by
  rfl

/-- Restriction of the complex lift to the real subspace recovers `A`.
`reLp_comp_ιLp` gives `reLp (ιLp g) = g` and `imLp_comp_ιLp` gives
`imLp (ιLp g) = 0`, so `complexLift_apply` collapses to
`ιLp (A g) + I • ιLp (A 0) = ιLp (A g)`. -/
theorem complexLift_real
    (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (g : Lp ℝ 2 μ) :
    complexLift A (ιLp g) = ιLp (A g) := by
  rw [complexLift_apply, reLp_comp_ιLp, imLp_comp_ιLp]
  simp

/-- Corollary of `complexLift_real`: projecting back via `reLp` gives
exactly `A g`.  Direct from `reLp_comp_ιLp`. -/
theorem reLp_complexLift_real
    (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (g : Lp ℝ 2 μ) :
    reLp (complexLift A (ιLp g)) = A g := by
  rw [complexLift_real, reLp_comp_ιLp]

/-! ## Section 3.  Adjoint and self-adjointness compatibility -/

private lemma inner_ιLp (u v : Lp ℝ 2 μ) :
    inner ℂ (ιLp u : Lp ℂ 2 μ) (ιLp v) = ((inner ℝ u v : ℝ) : ℂ) := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  calc
    (∫ a : Ω, inner ℂ (((ιLp u : Lp ℂ 2 μ) : Ω → ℂ) a)
        (((ιLp v : Lp ℂ 2 μ) : Ω → ℂ) a) ∂μ)
        = ∫ a : Ω, ((inner ℝ (((u : Lp ℝ 2 μ) : Ω → ℝ) a)
          (((v : Lp ℝ 2 μ) : Ω → ℝ) a) : ℝ) : ℂ) ∂μ := by
          apply integral_congr_ae
          filter_upwards [ContinuousLinearMap.coeFn_compLpL (RCLike.ofRealCLM (K := ℂ)) u,
                          ContinuousLinearMap.coeFn_compLpL (RCLike.ofRealCLM (K := ℂ)) v]
            with ω hu hv
          rw [show (((ιLp u : Lp ℂ 2 μ) : Ω → ℂ) ω) =
              (RCLike.ofRealCLM (K := ℂ)) (((u : Lp ℝ 2 μ) : Ω → ℝ) ω) by
            simpa [ιLp] using hu]
          rw [show (((ιLp v : Lp ℂ 2 μ) : Ω → ℂ) ω) =
              (RCLike.ofRealCLM (K := ℂ)) (((v : Lp ℝ 2 μ) : Ω → ℝ) ω) by
            simpa [ιLp] using hv]
          change inner ℂ (((((u : Lp ℝ 2 μ) : Ω → ℝ) ω : ℝ) : ℂ))
              (((((v : Lp ℝ 2 μ) : Ω → ℝ) ω : ℝ) : ℂ)) =
            ((inner ℝ (((u : Lp ℝ 2 μ) : Ω → ℝ) ω)
              (((v : Lp ℝ 2 μ) : Ω → ℝ) ω) : ℝ) : ℂ)
          rw [RCLike.inner_apply]
          rw [show inner ℝ (((u : Lp ℝ 2 μ) : Ω → ℝ) ω)
              (((v : Lp ℝ 2 μ) : Ω → ℝ) ω) =
              (((v : Lp ℝ 2 μ) : Ω → ℝ) ω) *
                (((u : Lp ℝ 2 μ) : Ω → ℝ) ω) by
            rfl]
          simp [mul_comm]
    _ = ((∫ a : Ω, inner ℝ (((u : Lp ℝ 2 μ) : Ω → ℝ) a)
          (((v : Lp ℝ 2 μ) : Ω → ℝ) a) ∂μ : ℝ) : ℂ) := by
          exact (integral_ofReal (𝕜 := ℂ) (μ := μ)
            (f := fun a : Ω => inner ℝ (((u : Lp ℝ 2 μ) : Ω → ℝ) a)
              (((v : Lp ℝ 2 μ) : Ω → ℝ) a)))

private lemma reLp_complexLift
    (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (f : Lp ℂ 2 μ) :
    reLp (complexLift A f) = A (reLp f) := by
  rw [complexLift_apply]
  simp [map_add, reLp_I_smul, reLp_comp_ιLp, imLp_comp_ιLp]

private lemma imLp_complexLift
    (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (f : Lp ℂ 2 μ) :
    imLp (complexLift A f) = A (imLp f) := by
  rw [complexLift_apply]
  simp [map_add, imLp_I_smul, reLp_comp_ιLp, imLp_comp_ιLp]

private lemma inner_ιLp_right (u : Lp ℝ 2 μ) (f : Lp ℂ 2 μ) :
    inner ℂ (ιLp u : Lp ℂ 2 μ) f =
      ((inner ℝ u (reLp f) : ℝ) : ℂ) +
        Complex.I * ((inner ℝ u (imLp f) : ℝ) : ℂ) := by
  rw [← reLp_add_smul_imLp f]
  simp [inner_add_right, inner_smul_right, inner_ιLp, reLp_comp_ιLp,
    imLp_comp_ιLp, reLp_I_smul, imLp_I_smul]

private lemma complexLift_adjoint_apply_real
    (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (g : Lp ℝ 2 μ) :
    (complexLift A).adjoint (ιLp g) = ιLp (A.adjoint g) := by
  apply ext_inner_right ℂ
  intro f
  rw [ContinuousLinearMap.adjoint_inner_left]
  rw [inner_ιLp_right, inner_ιLp_right]
  rw [reLp_complexLift, imLp_complexLift]
  rw [ContinuousLinearMap.adjoint_inner_left A (reLp f) g,
      ContinuousLinearMap.adjoint_inner_left A (imLp f) g]

/-- The complex lift commutes with taking adjoints.

Proof strategy: by definition of the adjoint via the inner product
identity `⟪(complexLift A).adjoint x, y⟫ = ⟪x, complexLift A y⟫`,
and `⟪ιLp u, ιLp v⟫_ℂ = (⟪u, v⟫_ℝ : ℂ)` (the inner product on
`Lp ℂ 2 μ` restricts on the real subspace to that of `Lp ℝ 2 μ`).  The
key Mathlib lemma is `ContinuousLinearMap.adjoint_inner_left` /
`adjoint_inner_right`. -/
theorem complexLift_adjoint (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) :
    (complexLift A).adjoint = complexLift A.adjoint := by
  ext f
  rw [← reLp_add_smul_imLp f]
  rw [map_add, map_smul]
  rw [complexLift_adjoint_apply_real, complexLift_adjoint_apply_real]
  rw [complexLift_apply]
  simp [map_add, reLp_comp_ιLp, imLp_comp_ιLp, reLp_I_smul, imLp_I_smul]

/-- Self-adjointness is preserved by the complex lift.  Direct
corollary of `complexLift_adjoint` (rewrite `A.adjoint = A` inside the
RHS). -/
theorem complexLift_isSelfAdjoint
    {A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ} (hA : IsSelfAdjoint A) :
    IsSelfAdjoint (complexLift A) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  rw [complexLift_adjoint, hA.adjoint_eq]

/-! ## Section 4.  Real CFC via complexification -/

private lemma reLp_ofReal_smul (r : ℝ) (f : Lp ℂ 2 μ) :
    reLp ((r : ℂ) • f) = r • reLp f := by
  apply Lp.ext
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (RCLike.reCLM (K := ℂ)) ((r : ℂ) • f),
                  Lp.coeFn_smul (r : ℂ) f,
                  Lp.coeFn_smul r (reLp f),
                  ContinuousLinearMap.coeFn_compLpL (RCLike.reCLM (K := ℂ)) f]
    with ω h_re_smul h_smul h_rhs h_re
  rw [h_rhs]
  simp only [Pi.smul_apply]
  rw [show (((reLp ((r : ℂ) • f) : Lp ℝ 2 μ) : Ω → ℝ) ω) =
      (RCLike.reCLM (K := ℂ)) ((((r : ℂ) • f : Lp ℂ 2 μ) : Ω → ℂ) ω) by
    simpa [reLp] using h_re_smul]
  rw [h_smul]
  simp only [Pi.smul_apply]
  rw [show (((reLp f : Lp ℝ 2 μ) : Ω → ℝ) ω) =
      (RCLike.reCLM (K := ℂ)) (((f : Lp ℂ 2 μ) : Ω → ℂ) ω) by
    simpa [reLp] using h_re]
  change ((r : ℂ) * (((f : Lp ℂ 2 μ) : Ω → ℂ) ω)).re =
    r * ((((f : Lp ℂ 2 μ) : Ω → ℂ) ω).re)
  simp

private lemma inner_reLp_left (u : Lp ℂ 2 μ) (v : Lp ℝ 2 μ) :
    inner ℝ (reLp u) v = (inner ℂ u (ιLp v)).re := by
  have h := inner_ιLp_right (μ := μ) v u
  calc
    inner ℝ (reLp u) v = inner ℝ v (reLp u) := by rw [real_inner_comm]
    _ = (inner ℂ (ιLp v) u).re := by
      rw [h]
      simp
    _ = (inner ℂ u (ιLp v)).re := by
      simpa using (inner_re_symm (𝕜 := ℂ) (x := u) (y := ιLp v)).symm

/-- **Real CFC by complexification.**

Given a real CLM `A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ` and a real-to-real
continuous symbol `f : ℝ → ℝ`, this is the operator obtained by
complexifying `A` via `complexLift`, applying Mathlib's complex `cfc`
with the lifted symbol `fun z : ℂ => (f z.re : ℂ)`, and projecting
back via `reLp` (precomposed with `ιLp`).

The action equation is `realCFC_apply` below; the algebra laws
`realCFC_id`, `realCFC_mul`, `realCFC_resolvent_mul_self`, and
`realCFC_norm_le` are the API used by the spectral rate proof.

The construction bundles the function
`fun g : Lp ℝ 2 μ =>
    reLp (cfc (fun z : ℂ => (f z.re : ℂ)) (complexLift A) (ιLp g))`
as a `ContinuousLinearMap` over ℝ.  ℝ-linearity follows from
ℂ-linearity of `cfc … (complexLift A)` and the fact that `ιLp` is
ℝ-linear and `reLp` is ℝ-linear.  Continuity follows from
boundedness of `cfc f a` (mathlib lemma
`cfc_apply_continuous` / `IsometricContinuousFunctionalCalculus`). -/
noncomputable def realCFC
    (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (f : ℝ → ℝ) :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  let C : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
    cfc (fun z : ℂ => (f z.re : ℂ)) (complexLift A)
  let L : Lp ℝ 2 μ →ₗ[ℝ] Lp ℝ 2 μ :=
    { toFun := fun g => reLp (C (ιLp g))
      map_add' := by
        intro x y
        rw [map_add, map_add, map_add]
      map_smul' := by
        intro r x
        simp only [map_smul]
        change reLp (C ((r : ℂ) • ιLp x)) = r • reLp (C (ιLp x))
        rw [C.map_smul]
        exact reLp_ofReal_smul r (C (ιLp x)) }
  L.mkContinuous (‖reLp‖ * ‖C‖ * ‖ιLp‖) (by
    intro x
    calc
      ‖L x‖ = ‖reLp (C (ιLp x))‖ := rfl
      _ ≤ ‖reLp‖ * ‖C (ιLp x)‖ := reLp.le_opNorm (C (ιLp x))
      _ ≤ ‖reLp‖ * (‖C‖ * ‖ιLp x‖) := by
        gcongr
        exact C.le_opNorm (ιLp x)
      _ ≤ ‖reLp‖ * (‖C‖ * (‖ιLp‖ * ‖x‖)) := by
        gcongr
        exact ιLp.le_opNorm x
      _ = ‖reLp‖ * ‖C‖ * ‖ιLp‖ * ‖x‖ := by ring)

/-- **Action equation for `realCFC`** — the basic rewrite rule used by
spectral proofs.

Given a self-adjoint real CLM `A` and a continuous real symbol `f`,
`realCFC A f g` equals the real part of
`cfc (f ∘ Complex.re) (complexLift A) (ιLp g)`. -/
theorem realCFC_apply
    (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (hA : IsSelfAdjoint A)
    (f : ℝ → ℝ) (hf : Continuous f) (g : Lp ℝ 2 μ) :
    realCFC A f g
      = reLp (cfc (fun z : ℂ => (f z.re : ℂ)) (complexLift A) (ιLp g)) := by
  have _hA : IsSelfAdjoint A := hA
  have _hf : Continuous f := hf
  rfl

/-- **`realCFC` of the identity symbol recovers `A`.**

Pointwise on the complex side, `cfc (fun z => z) (complexLift A) =
complexLift A` (`cfc_id`).  Combined with `complexLift_real` and
`reLp_comp_ιLp` this collapses to `A g`.

Note: the symbol here is `(id : ℝ → ℝ)`; the lifted symbol
`fun z : ℂ => ((id z.re : ℝ) : ℂ) = (z.re : ℂ)` is *not* `cfc_id`
directly but rather agrees with the identity on the spectrum of
`complexLift A` because `complexLift` of a self-adjoint real CLM has
real spectrum (`IsSelfAdjoint.spectrumRestricts`). -/
theorem realCFC_id
    (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (hA : IsSelfAdjoint A)
    (g : Lp ℝ 2 μ) :
    realCFC A id g = A g := by
  rw [realCFC_apply A hA id continuous_id g]
  have hcl : IsSelfAdjoint (complexLift A) := complexLift_isSelfAdjoint hA
  rw [← cfc_real_eq_complex (a := complexLift A) (f := id) (ha := hcl)]
  rw [cfc_id ℝ (complexLift A) hcl]
  exact reLp_complexLift_real A g

/- A composition law `realCFC A (f ∘ g) = …` is intentionally not part of
   this API.  The naive shape `realCFC A (f ∘ g) = (realCFC A f).comp
   (realCFC A g)` is mathematically false: composition of CFC operators
   corresponds to *multiplication* of symbols (`cfc f a * cfc g a = cfc
   (f * g) a`), not composition.  The correct CFC composition law
   `cfc (f ∘ g) a = cfc f (cfc g a)` would translate, in this real-CFC
   setting, to `realCFC A (f ∘ g) = realCFC (realCFC A g) f` — which
   additionally requires `complexLift (realCFC A g) = cfc (g ∘ Complex.re)
   (complexLift A)` (real-subspace preservation of the complex CFC of a
   real symbol).  No current rate-proof consumer needs that extra API. -/

/-- **`realCFC` preserves self-adjointness.**

For continuous real `f` and self-adjoint `A`, `realCFC A f` is itself
self-adjoint.  Proof strategy: `cfc (fun z : ℂ => (f z.re : ℂ))
(complexLift A)` is self-adjoint by `IsSelfAdjoint.cfc` (provided the
lifted symbol takes real values on the spectrum, which follows from
`f z.re` being real for real `z`); then `complexLift_adjoint`
combined with `reLp` ∘ `_` ∘ `ιLp` being a real adjunction transports
self-adjointness back to `realCFC A f`. -/
theorem realCFC_isSelfAdjoint
    (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (hA : IsSelfAdjoint A)
    (f : ℝ → ℝ) (hf : Continuous f) :
    IsSelfAdjoint (realCFC A f) := by
  let C : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
    cfc (fun z : ℂ => (f z.re : ℂ)) (complexLift A)
  have hC : IsSelfAdjoint C := by
    have hcl : IsSelfAdjoint (complexLift A) := complexLift_isSelfAdjoint hA
    rw [show C = cfc (fun z : ℂ => (f z.re : ℂ)) (complexLift A) by rfl]
    rw [← cfc_real_eq_complex (a := complexLift A) (f := f) (ha := hcl)]
    exact IsSelfAdjoint.cfc
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  change inner ℝ (realCFC A f x) y = inner ℝ x (realCFC A f y)
  rw [realCFC_apply A hA f hf x, realCFC_apply A hA f hf y]
  rw [inner_reLp_left (C (ιLp x)) y]
  change (inner ℂ (C (ιLp x)) (ιLp y)).re = inner ℝ x (reLp (C (ιLp y)))
  rw [real_inner_comm (reLp (C (ιLp y))) x]
  rw [inner_reLp_left (C (ιLp y)) x]
  calc
    (inner ℂ (C (ιLp x)) (ιLp y)).re =
        (inner ℂ (ιLp x) (C (ιLp y))).re := by
      exact congrArg Complex.re
        ((ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hC) (ιLp x) (ιLp y))
    _ = (inner ℂ (C (ιLp y)) (ιLp x)).re := by
      simpa using (inner_re_symm (𝕜 := ℂ) (x := C (ιLp y)) (y := ιLp x)).symm

private lemma complexLift_one_early :
    complexLift (ContinuousLinearMap.id ℝ (Lp ℝ 2 μ))
      = ContinuousLinearMap.id ℂ (Lp ℂ 2 μ) := by
  ext1 f
  simpa [complexLift_apply] using reLp_add_smul_imLp (μ := μ) f

private lemma complexLift_comp_early (A B : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) :
    complexLift (A.comp B) = (complexLift A).comp (complexLift B) := by
  ext1 f
  rw [ContinuousLinearMap.comp_apply]
  rw [complexLift_apply, complexLift_apply]
  rw [reLp_complexLift, imLp_complexLift]
  rfl

private lemma complexLift_mul_early (A B : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) :
    complexLift (A * B) = complexLift A * complexLift B := by
  exact complexLift_comp_early A B

private lemma complexLift_sub_early (A B : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) :
    complexLift (A - B) = complexLift A - complexLift B := by
  ext1 f
  rw [complexLift_apply]
  change ιLp (A (reLp f) - B (reLp f)) + Complex.I • ιLp (A (imLp f) - B (imLp f)) =
    complexLift A f - complexLift B f
  rw [complexLift_apply A f, complexLift_apply B f]
  rw [map_sub, map_sub, smul_sub]
  abel

private lemma complexLift_algebraMap_real_early (r : ℝ) :
    complexLift (algebraMap ℝ (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) r)
      = algebraMap ℂ (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (r : ℂ) := by
  ext1 f
  rw [complexLift_apply]
  change ιLp (r • reLp f) + Complex.I • ιLp (r • imLp f) = (r : ℂ) • f
  calc
    ιLp (r • reLp f) + Complex.I • ιLp (r • imLp f)
        = (r : ℂ) • (ιLp (reLp f) + Complex.I • ιLp (imLp f)) := by
      rw [smul_add]
      simp only [map_smul]
      congr 1
      change Complex.I • ((r : ℂ) • ιLp (imLp f)) =
        (r : ℂ) • (Complex.I • ιLp (imLp f))
      rw [smul_smul, smul_smul, mul_comm]
    _ = (r : ℂ) • f := by rw [reLp_add_smul_imLp]

private lemma complexLift_resolvent_real_early
    (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (r : ℝ) :
    algebraMap ℂ (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (r : ℂ) - complexLift A =
      complexLift (algebraMap ℝ (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) r - A) := by
  rw [complexLift_sub_early, complexLift_algebraMap_real_early]

private lemma complexLift_isUnit_early
    {B : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ} (hB : IsUnit B) :
    IsUnit (complexLift B) := by
  have hone : complexLift (1 : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) =
      (1 : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) := by
    simpa using complexLift_one_early (μ := μ)
  refine Units.isUnit ⟨complexLift B, complexLift ↑hB.unit⁻¹, ?_, ?_⟩
  · calc
      complexLift B * complexLift ↑hB.unit⁻¹ = complexLift (B * ↑hB.unit⁻¹) := by
        rw [complexLift_mul_early]
      _ = complexLift 1 := congrArg (fun T => complexLift T) hB.mul_val_inv
      _ = 1 := hone
  · calc
      complexLift ↑hB.unit⁻¹ * complexLift B = complexLift (↑hB.unit⁻¹ * B) := by
        rw [complexLift_mul_early]
      _ = complexLift 1 := congrArg (fun T => complexLift T) hB.val_inv_mul
      _ = 1 := hone

private theorem spectrum_complexLift_subset_real_early
    {A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ} (hA : IsSelfAdjoint A) {z : ℂ}
    (hz : z ∈ spectrum ℂ (complexLift A)) :
    z.re ∈ spectrum ℝ A := by
  by_contra hzreal
  have hunitR : IsUnit (algebraMap ℝ (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) z.re - A) :=
    spectrum.notMem_iff.mp hzreal
  have hunitC :
      IsUnit (algebraMap ℂ (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (z.re : ℂ) - complexLift A) := by
    rw [complexLift_resolvent_real_early]
    exact complexLift_isUnit_early hunitR
  have hzreal_eq : z = (z.re : ℂ) :=
    IsSelfAdjoint.mem_spectrum_eq_re (complexLift_isSelfAdjoint hA) hz
  have hnot : (z.re : ℂ) ∉ spectrum ℂ (complexLift A) :=
    spectrum.notMem_iff.mpr hunitC
  exact hnot (by rwa [← hzreal_eq])

private theorem cfc_lifted_preserves_real
    (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (hA : IsSelfAdjoint A)
    (f : ℝ → ℝ) (hf : Continuous f) (v : Lp ℝ 2 μ) :
    ιLp (reLp (cfc (fun z : ℂ => (f z.re : ℂ)) (complexLift A) (ιLp v)))
      = cfc (fun z : ℂ => (f z.re : ℂ)) (complexLift A) (ιLp v) := by
  let a : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ := complexLift A
  let E : Type _ := Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ
  have ha : IsSelfAdjoint a := complexLift_isSelfAdjoint hA
  have hpresHom :
      ∀ F : C(spectrum ℝ a, ℝ),
        ∀ w : Lp ℝ 2 μ,
          ιLp (reLp ((cfcHom ha F : E) (ιLp w))) =
            (cfcHom ha F : E) (ιLp w) := by
    intro F
    open scoped ContinuousFunctionalCalculus in
    induction F using ContinuousMap.induction_on_of_compact with
    | const r =>
        intro w
        rw [show ContinuousMap.const (spectrum ℝ a) r =
            algebraMap ℝ C(spectrum ℝ a, ℝ) r from rfl]
        rw [AlgHomClass.commutes (cfcHom ha) r]
        change ιLp (reLp ((algebraMap ℝ E r) (ιLp w))) =
          (algebraMap ℝ E r) (ιLp w)
        change ιLp (reLp ((r : ℂ) • ιLp w)) = (r : ℂ) • ιLp w
        rw [reLp_ofReal_smul, reLp_comp_ιLp]
        exact map_smul ιLp r w
    | id =>
        rw [cfcHom_id ha]
        intro w
        rw [complexLift_real, reLp_comp_ιLp]
    | star_id =>
        rw [map_star, cfcHom_id ha, ha.star_eq]
        intro w
        rw [complexLift_real, reLp_comp_ιLp]
    | add F G hF hG =>
        rw [map_add]
        intro w
        change ιLp (reLp (((cfcHom ha F : E) + (cfcHom ha G : E)) (ιLp w))) =
          ((cfcHom ha F : E) + (cfcHom ha G : E)) (ιLp w)
        simp only [ContinuousLinearMap.add_apply]
        rw [← hF w, ← hG w]
        simp [map_add, reLp_comp_ιLp]
    | mul F G hF hG =>
        rw [map_mul]
        intro w
        let B : E := cfcHom ha F
        let C : E := cfcHom ha G
        change ιLp (reLp ((B * C) (ιLp w))) = (B * C) (ιLp w)
        change ιLp (reLp (B (C (ιLp w)))) = B (C (ιLp w))
        rw [← hG w]
        exact hF (reLp (C (ιLp w)))
    | frequently F hF =>
        intro w
        have hleft : Continuous (fun B : E => ιLp (reLp (B (ιLp w)))) :=
          ιLp.continuous.comp <| reLp.continuous.comp <|
            (ContinuousLinearMap.apply ℂ (Lp ℂ 2 μ) (ιLp w)).continuous
        have hright : Continuous (fun B : E => B (ιLp w)) :=
          (ContinuousLinearMap.apply ℂ (Lp ℂ 2 μ) (ιLp w)).continuous
        rw [← Set.mem_setOf
            (p := fun B : E => ιLp (reLp (B (ιLp w))) = B (ιLp w)),
          ← (isClosed_eq hleft hright).closure_eq]
        apply mem_closure_of_frequently_of_tendsto
          (hF.mono fun G hG => hG w)
        exact (cfcHom_continuous ha).tendsto F
  change ιLp (reLp ((cfc (fun z : ℂ => (f z.re : ℂ)) a) (ιLp v))) =
    (cfc (fun z : ℂ => (f z.re : ℂ)) a) (ιLp v)
  rw [← cfc_real_eq_complex (a := a) (f := f) (ha := ha)]
  rw [cfc_apply f a ha hf.continuousOn]
  exact hpresHom ⟨_, hf.continuousOn.restrict⟩ v

/-- **Symbol-multiplication law for `realCFC`.**

For self-adjoint `A` and continuous real symbols `f g : ℝ → ℝ`, the
real CFC of the pointwise product `fun x => f x * g x` equals the
operator composition `(realCFC A f).comp (realCFC A g)`.

This is the C*-algebra multiplication law transported through
complexification — `cfc_mul` lifts to the operator algebra
`Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ` (a `CStarAlgebra`), and the composition
projects back through `reLp` because the complex CFC is multiplicative.

NOTE: this is the *symbol-multiplication* law `realCFC A (f·g)`, not
the *symbol-composition* law `realCFC A (f∘g)` discussed in the
comment block above — those are mathematically distinct, and only the
former is exposed here. -/
theorem realCFC_mul
    (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (hA : IsSelfAdjoint A)
    (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
    realCFC A (fun x => f x * g x) = (realCFC A f).comp (realCFC A g) := by
  ext v
  rw [realCFC_apply A hA (fun x => f x * g x) (hf.mul hg) v]
  rw [ContinuousLinearMap.comp_apply]
  rw [realCFC_apply A hA f hf (realCFC A g v),
    realCFC_apply A hA g hg v]
  rw [cfc_lifted_preserves_real A hA g hg v]
  rw [show (fun z : ℂ => ((f z.re * g z.re : ℝ) : ℂ)) =
      fun z : ℂ => (f z.re : ℂ) * (g z.re : ℂ) by
    funext z
    norm_num]
  rw [cfc_mul (fun z : ℂ => (f z.re : ℂ)) (fun z : ℂ => (g z.re : ℂ))
    (complexLift A)
    (hf := (Complex.continuous_ofReal.comp (hf.comp Complex.continuous_re)).continuousOn)
    (hg := (Complex.continuous_ofReal.comp (hg.comp Complex.continuous_re)).continuousOn)]
  rfl

private lemma realCFC_congr_on_spectrum
    (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (f g : ℝ → ℝ)
    (h : ∀ x ∈ spectrum ℝ A, f x = g x) (hA : IsSelfAdjoint A) :
    realCFC A f = realCFC A g := by
  apply ContinuousLinearMap.ext
  intro v
  change reLp (cfc (fun z : ℂ => (f z.re : ℂ)) (complexLift A) (ιLp v)) =
    reLp (cfc (fun z : ℂ => (g z.re : ℂ)) (complexLift A) (ιLp v))
  congr 2
  apply cfc_congr
  intro z hz
  have hzr : z.re ∈ spectrum ℝ A := spectrum_complexLift_subset_real_early hA hz
  simpa using congrArg (fun r : ℝ => (r : ℂ)) (h z.re hzr)

/-- **Resolvent symbol for `realCFC`.**

For self-adjoint `A` with nonnegative real spectrum and `λ > 0`,
the symbol `fun x => (λ + x)⁻¹` is continuous and nonzero on
`spectrum ℝ A` (since `λ + x ≥ λ > 0` there), so its `realCFC` is
defined and is a two-sided inverse of `realCFC A (fun x => λ + x)`
in the operator algebra `Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ`.

Concretely: composition of these two `realCFC` operators equals the
identity `ContinuousLinearMap.id ℝ (Lp ℝ 2 μ)`. This is the
`realCFC`-level resolvent law that the Tikhonov bias proof needs. -/
theorem realCFC_resolvent_mul_self
    (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (hA : IsSelfAdjoint A)
    (hA_spec : ∀ x ∈ spectrum ℝ A, 0 ≤ x)
    (lambda : ℝ) (hlam : 0 < lambda) :
    (realCFC A (fun x => lambda + x)).comp
        (realCFC A (fun x => (lambda + x)⁻¹))
      = ContinuousLinearMap.id ℝ (Lp ℝ 2 μ) := by
  have hsafe_ne : ∀ x : ℝ, lambda + max 0 x ≠ 0 := fun x => by
    have hmax : (0 : ℝ) ≤ max 0 x := le_max_left _ _
    have hpos : 0 < lambda + max 0 x := by linarith
    exact ne_of_gt hpos
  have hsafe_cont : Continuous (fun x : ℝ => (lambda + max 0 x)⁻¹) :=
    (continuous_const.add (continuous_const.max continuous_id)).inv₀ hsafe_ne
  have hagree : ∀ x ∈ spectrum ℝ A,
      (lambda + max 0 x)⁻¹ = (lambda + x)⁻¹ := fun x hx => by
    have hx0 : 0 ≤ x := hA_spec x hx
    rw [max_eq_right hx0]
  rw [← realCFC_congr_on_spectrum A (fun x => (lambda + max 0 x)⁻¹)
    (fun x => (lambda + x)⁻¹) hagree hA]
  rw [← realCFC_mul A hA (fun x => lambda + x)
    (fun x => (lambda + max 0 x)⁻¹) (continuous_const.add continuous_id) hsafe_cont]
  have hprod : ∀ x ∈ spectrum ℝ A,
      (lambda + x) * (lambda + max 0 x)⁻¹ = 1 := fun x hx => by
    have hx0 : 0 ≤ x := hA_spec x hx
    rw [max_eq_right hx0]
    have hne : lambda + x ≠ 0 := by
      have hpos : 0 < lambda + x := by linarith
      exact ne_of_gt hpos
    exact mul_inv_cancel₀ hne
  rw [realCFC_congr_on_spectrum A
    (fun x => (lambda + x) * (lambda + max 0 x)⁻¹)
    (fun _ : ℝ => (1 : ℝ)) hprod hA]
  apply ContinuousLinearMap.ext
  intro v
  rw [realCFC_apply A hA (fun _ : ℝ => (1 : ℝ)) continuous_const v]
  rw [ContinuousLinearMap.id_apply]
  change reLp (cfc (fun _ : ℂ => (1 : ℂ)) (complexLift A) (ιLp v)) = v
  rw [cfc_const_one ℂ (complexLift A)
    (ha := (complexLift_isSelfAdjoint hA).isStarNormal)]
  rw [ContinuousLinearMap.one_apply, reLp_comp_ιLp]

private lemma complexLift_one :
    complexLift (ContinuousLinearMap.id ℝ (Lp ℝ 2 μ))
      = ContinuousLinearMap.id ℂ (Lp ℂ 2 μ) := by
  ext1 f
  simpa [complexLift_apply] using reLp_add_smul_imLp (μ := μ) f

private lemma complexLift_comp (A B : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) :
    complexLift (A.comp B) = (complexLift A).comp (complexLift B) := by
  ext1 f
  rw [ContinuousLinearMap.comp_apply]
  rw [complexLift_apply, complexLift_apply]
  rw [reLp_complexLift, imLp_complexLift]
  rfl

private lemma complexLift_mul (A B : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) :
    complexLift (A * B) = complexLift A * complexLift B := by
  exact complexLift_comp A B

private lemma complexLift_sub (A B : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) :
    complexLift (A - B) = complexLift A - complexLift B := by
  ext1 f
  rw [complexLift_apply]
  change ιLp (A (reLp f) - B (reLp f)) + Complex.I • ιLp (A (imLp f) - B (imLp f)) =
    complexLift A f - complexLift B f
  rw [complexLift_apply A f, complexLift_apply B f]
  rw [map_sub, map_sub, smul_sub]
  abel

private lemma complexLift_algebraMap_real (r : ℝ) :
    complexLift (algebraMap ℝ (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) r)
      = algebraMap ℂ (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (r : ℂ) := by
  ext1 f
  rw [complexLift_apply]
  change ιLp (r • reLp f) + Complex.I • ιLp (r • imLp f) = (r : ℂ) • f
  calc
    ιLp (r • reLp f) + Complex.I • ιLp (r • imLp f)
        = (r : ℂ) • (ιLp (reLp f) + Complex.I • ιLp (imLp f)) := by
      rw [smul_add]
      simp only [map_smul]
      congr 1
      change Complex.I • ((r : ℂ) • ιLp (imLp f)) =
        (r : ℂ) • (Complex.I • ιLp (imLp f))
      rw [smul_smul, smul_smul, mul_comm]
    _ = (r : ℂ) • f := by rw [reLp_add_smul_imLp]

private lemma complexLift_resolvent_real
    (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (r : ℝ) :
    algebraMap ℂ (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (r : ℂ) - complexLift A =
      complexLift (algebraMap ℝ (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) r - A) := by
  rw [complexLift_sub, complexLift_algebraMap_real]

private lemma complexLift_isUnit
    {B : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ} (hB : IsUnit B) :
    IsUnit (complexLift B) := by
  have hone : complexLift (1 : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) =
      (1 : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) := by
    simpa using complexLift_one (μ := μ)
  refine Units.isUnit ⟨complexLift B, complexLift ↑hB.unit⁻¹, ?_, ?_⟩
  · calc
      complexLift B * complexLift ↑hB.unit⁻¹ = complexLift (B * ↑hB.unit⁻¹) := by
        rw [complexLift_mul]
      _ = complexLift 1 := congrArg (fun T => complexLift T) hB.mul_val_inv
      _ = 1 := hone
  · calc
      complexLift ↑hB.unit⁻¹ * complexLift B = complexLift (↑hB.unit⁻¹ * B) := by
        rw [complexLift_mul]
      _ = complexLift 1 := congrArg (fun T => complexLift T) hB.val_inv_mul
      _ = 1 := hone

private theorem spectrum_complexLift_subset_real
    {A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ} (hA : IsSelfAdjoint A) {z : ℂ}
    (hz : z ∈ spectrum ℂ (complexLift A)) :
    z.re ∈ spectrum ℝ A := by
  by_contra hzreal
  have hunitR : IsUnit (algebraMap ℝ (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) z.re - A) :=
    spectrum.notMem_iff.mp hzreal
  have hunitC :
      IsUnit (algebraMap ℂ (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (z.re : ℂ) - complexLift A) := by
    rw [complexLift_resolvent_real]
    exact complexLift_isUnit hunitR
  have hzreal_eq : z = (z.re : ℂ) :=
    IsSelfAdjoint.mem_spectrum_eq_re (complexLift_isSelfAdjoint hA) hz
  have hnot : (z.re : ℂ) ∉ spectrum ℂ (complexLift A) :=
    spectrum.notMem_iff.mpr hunitC
  exact hnot (by rwa [← hzreal_eq])

private lemma norm_reLp_le (u : Lp ℂ 2 μ) : ‖reLp u‖ ≤ ‖u‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (RCLike.reCLM (K := ℂ)) u] with ω h
  rw [show (((reLp u : Lp ℝ 2 μ) : Ω → ℝ) ω) =
      (RCLike.reCLM (K := ℂ)) (((u : Lp ℂ 2 μ) : Ω → ℂ) ω) by
    simpa [reLp] using h]
  change ‖(((u : Lp ℂ 2 μ) : Ω → ℂ) ω).re‖ ≤ ‖(((u : Lp ℂ 2 μ) : Ω → ℂ) ω)‖
  exact RCLike.norm_re_le_norm (((u : Lp ℂ 2 μ) : Ω → ℂ) ω)

/-- **Norm-via-spectrum bound for `realCFC`.**

For self-adjoint `A`, continuous symbol `f : ℝ → ℝ`, and a uniform
bound `|f x| ≤ c` for every `x` in the real spectrum of `A`, the
operator `realCFC A f : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ` satisfies
`‖realCFC A f g‖ ≤ c · ‖g‖` for every `g`.

Proof strategy:
1. Reduce to bounding `‖cfc (fun z : ℂ => (f z.re : ℂ)) (complexLift A) (ιLp g)‖`
   via `realCFC_apply` plus the contraction `‖reLp h‖ ≤ ‖h‖`
   (`reLp` has operator norm ≤ 1 because `RCLike.reCLM` does).
2. Bound that by `‖cfc … (complexLift A)‖ · ‖ιLp g‖`
   (operator norm), then use `‖ιLp g‖ = ‖g‖` (`ιLp_isometry`).
3. Apply `norm_cfc_le_iff` (in
   `Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric`)
   to reduce `‖cfc (fun z => (f z.re : ℂ)) (complexLift A)‖ ≤ c` to
   `∀ z ∈ spectrum ℂ (complexLift A), |f z.re| ≤ c`.
4. For each such `z`, `IsSelfAdjoint.mem_spectrum_eq_re` (applied to
   the self-adjoint `complexLift A`, see
   `complexLift_isSelfAdjoint`) gives `z = (z.re : ℂ)`. Then transport
   `z.re ∈ spectrum ℝ A` via the spectrum-preservation fact for the
   complex lift (this may require a small auxiliary lemma; if mathlib
   doesn't expose it directly, prove it by inverting
   `λ - complexLift A = complexLift (λ - A)` for real `λ`). -/
theorem realCFC_norm_le
    (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (hA : IsSelfAdjoint A)
    (f : ℝ → ℝ) (hf : Continuous f)
    (c : ℝ) (hc : 0 ≤ c) (hsup : ∀ x ∈ spectrum ℝ A, |f x| ≤ c)
    (g : Lp ℝ 2 μ) :
    ‖realCFC A f g‖ ≤ c * ‖g‖ := by
  let Acpx : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ := complexLift A
  let C : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
    cfc (fun z : ℂ => (f z.re : ℂ)) Acpx
  rw [realCFC_apply A hA f hf g]
  change ‖reLp (C (ιLp g))‖ ≤ c * ‖g‖
  have hC_norm : ‖C‖ ≤ c := by
    rw [show C = cfc (fun z : ℂ => (f z.re : ℂ)) Acpx by rfl]
    rw [norm_cfc_le_iff (fun z : ℂ => (f z.re : ℂ)) Acpx hc
      (hf := (Complex.continuous_ofReal.comp (hf.comp Complex.continuous_re)).continuousOn)
      (ha := (complexLift_isSelfAdjoint hA).isStarNormal)]
    intro z hz
    have hzr : z.re ∈ spectrum ℝ A := spectrum_complexLift_subset_real hA hz
    simpa [Complex.norm_real, Real.norm_eq_abs] using hsup z.re hzr
  calc
    ‖reLp (C (ιLp g))‖
        ≤ ‖C (ιLp g)‖ := norm_reLp_le _
    _ = 1 * ‖C (ιLp g)‖ := by rw [one_mul]
    _ ≤ 1 * (‖C‖ * ‖ιLp g‖) := by
      gcongr
      exact C.le_opNorm _
    _ ≤ 1 * (c * ‖ιLp g‖) := by
      gcongr
    _ = c * ‖g‖ := by
      rw [one_mul, ιLp_isometry]

end Complexification
end NPIV
end Estimation
end Causalean
