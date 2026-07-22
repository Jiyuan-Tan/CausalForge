/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Spectral source condition and discharge of the Tikhonov bias bound

Spectral discharge of `TikhonovBiasBound` from the β-source condition
(`def:est-trae-source-condition` in
`doc/basic_concepts/po/estimation/trae_inverse_problems.tex`).

## Pipeline

1.  `Causalean.Estimation.NPIV.SourceCondition` carries the spectral
    identity `(h₀)_{L²} = (T†T)^{β/2} (w₀)_{L²}` inside `Lp ℝ 2 μ`, using
    the real CFC `Complexification.realCFC` built by complexification in
    `Operator/Complexification.lean`.
2.  `SpectralSourceCondition` adds the *structural* assumption needed
    to actually run the spectral argument beyond the base source condition:
    full-space candidate set `Hbar_L2 = ⊤` (so Lax–Milgram coincides
    with the resolvent on the ambient `Lp ℝ 2 μ`).  The closedness
    witness and non-negativity of `spectrum ℝ (T†T)` are derived below
    from these assumptions and the Hilbert-space positivity of `T†T`.
3.  The two Tikhonov bias bounds are **theorems** on
    `SpectralSourceCondition`, proved using `Complexification.realCFC_*`
    plus `OperatorSystem.tikhonovMinimiserL2_optimality`.
4.  `tikhonov_bias_from_spectral` packages the two bias theorems plus
    `tikhonovMinimiserL2_strong_convexity` into a full
    `TikhonovBiasBound`, transported along a function-level pullback.

## Outputs

* `SpectralSourceCondition S β` — `SourceCondition S β` strengthened
  with `Hbar_L2_eq_top`.  No baked bias / convexity / spectral power fields.
* `SpectralSourceCondition.spectralPower` — the operator `(T†T)^{β/2}`,
  *defined* as `Complexification.realCFC S.Tstar_T
  (fun x => Real.rpow (max x 0) (β/2))`.  Action equation is direct
  from `Complexification.realCFC_apply` + `realCFC_isSelfAdjoint`.
* `SpectralSourceCondition.tikhonovMinimiserL2_eq_resolvent` — the
  Lax–Milgram minimiser equals the resolvent expression
  `realCFC (T†T) (x ↦ x/(λ+x)) h₀` when `Hbar_L2 = ⊤`.
* `SpectralSourceCondition.strong_bias` /
  `SpectralSourceCondition.weak_bias` — the two Tikhonov bias bounds,
  proved spectrally with a uniform constant
  `biasConst := (max 1 (‖T†T‖+1))^β`.
* `tikhonov_bias_from_spectral` — produces `TikhonovBiasBound` from
  `SpectralSourceCondition` + `TikhonovPullback`, using the two bias
  theorems and `tikhonovMinimiserL2_strong_convexity`.
-/

import Causalean.Estimation.NPIV.Operator.Adjoint
import Causalean.Estimation.NPIV.Operator.Complexification
import Causalean.Estimation.NPIV.Operator.Tikhonov
import Causalean.Estimation.NPIV.SourceCondition
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Spectral Discharge of Tikhonov Bias

This file proves the Tikhonov bias bounds for the primal NPIV estimator from a
spectral β-source condition. It defines the strengthened
`SpectralSourceCondition`, builds the real functional-calculus operator
`spectralPower = (T†T)^{β/2}`, identifies the full-space Lax–Milgram
Tikhonov minimizer with its resolvent expression, proves the strong- and
weak-metric bias bounds, and packages them as `tikhonov_bias_from_spectral`
for the rate theorem. -/

namespace Causalean
namespace Estimation
namespace NPIV

open MeasureTheory ContinuousLinearMap

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Spectral β-source condition** at the primal nuisance `h₀`.

Strengthens `SourceCondition` with the structural assumption needed by
the spectral discharge of the Tikhonov bias bound:

* `Hbar_L2_eq_top` — the candidate set is L²-dense (i.e. coincides with
  the ambient `Lp ℝ 2 μ`), so the Lax–Milgram minimiser on `Hbar_L2`
  agrees with the resolvent expression `(T*T+λI)⁻¹ T*T h₀`;

The non-negativity of `β` is inherited from `SourceCondition`.
The closedness witness consumed by Lax–Milgram is automatic from
`Hbar_L2_eq_top`, and the real spectrum of `T*T` is automatically
contained in `[0, ∞)` because `T*T` is a positive operator. -/
structure SpectralSourceCondition
    (S : OperatorSystem Ω μ) (β : ℝ) extends SourceCondition S β where
  /-- The primal candidate subspace is the full L² space. -/
  Hbar_L2_eq_top : S.Hbar_L2 = ⊤

namespace SpectralSourceCondition

variable {S : OperatorSystem Ω μ} {β : ℝ}

/-- Closedness witness for the full primal candidate subspace. -/
lemma Hbar_L2_hasProj (sc : SpectralSourceCondition S β) :
    S.Hbar_L2.HasOrthogonalProjection := by
  rw [sc.Hbar_L2_eq_top]
  infer_instance

/-- `T†T` is a positive operator. -/
lemma Tstar_T_isPositive (S : OperatorSystem Ω μ) :
    S.Tstar_T.IsPositive := by
  unfold OperatorSystem.Tstar_T OperatorSystem.Tadjoint
  simpa [ContinuousLinearMap.comp_def, ContinuousLinearMap.comp_apply] using
    ContinuousLinearMap.isPositive_adjoint_comp_self S.Tlin

/-- Positivity of `T†T`: its real spectrum lies in `[0, ∞)`. -/
lemma Tstar_T_spectrum_nonneg (_sc : SpectralSourceCondition S β) :
    ∀ x ∈ spectrum ℝ S.Tstar_T, 0 ≤ x := by
  intro x hx
  exact spectrum_nonneg_of_nonneg (a := S.Tstar_T) (x := x) (by
    rw [ContinuousLinearMap.nonneg_iff_isPositive]
    exact Tstar_T_isPositive S) hx

/-! ## The `(T†T)^{β/2}` operator, defined via real CFC -/

/-- The symbol `x ↦ Real.rpow (max x 0) (β/2)` used by `spectralPower`.
Continuous on all of ℝ for `β ≥ 0`, and agrees with `x^{β/2}` on
`[0, ∞)`. -/
noncomputable def sourceSymbol (β : ℝ) : ℝ → ℝ :=
  fun x => Real.rpow (max x 0) (β/2)

/-- The source symbol is continuous whenever the source exponent is nonnegative. -/
lemma continuous_sourceSymbol {β : ℝ} (h : 0 ≤ β) :
    Continuous (sourceSymbol β) := by
  unfold sourceSymbol
  refine (Real.continuous_rpow_const ?_).comp (continuous_id.max continuous_const)
  linarith

/-- The operator `(T†T)^{β/2}`, defined as the real CFC of `T†T`
applied to the continuous symbol `x ↦ Real.rpow (max x 0) (β/2)`. -/
noncomputable def spectralPower (_sc : SpectralSourceCondition S β) :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  Complexification.realCFC S.Tstar_T (sourceSymbol β)

/-- Restated spectral identity using `spectralPower`. -/
lemma spectral_identity_h₀ (sc : SpectralSourceCondition S β) :
    S.hL2 S.h₀_mem = sc.spectralPower (S.hL2 sc.w₀_mem) :=
  sc.spectral_identity

/-! ## Bias constant -/

/-- Uniform constant absorbing both regimes (β ≤ 2 and β > 2) of the
sup-on-spectrum analysis.

In the small-β regime (β ≤ 2) the constant is `≤ 1` and the rate is
`λ^β`; in the large-β regime (β > 2) the constant is `‖T†T‖^{β−2}` and
the rate saturates at `λ²`.  We bound both uniformly by
`Real.rpow (max 1 (‖T†T‖+1)) β`. -/
noncomputable def biasConst (_sc : SpectralSourceCondition S β) : ℝ :=
  Real.rpow (max 1 (‖S.Tstar_T‖ + 1)) β

/-- The uniform Tikhonov bias constant is nonnegative. -/
lemma biasConst_nonneg (sc : SpectralSourceCondition S β) :
    0 ≤ sc.biasConst := by
  unfold biasConst
  exact Real.rpow_nonneg (le_max_of_le_left zero_le_one) _

/-! ## Lax–Milgram = resolvent on the full space -/

private lemma reLp_I_smul_local (f : Lp ℂ 2 μ) :
    Complexification.reLp ((Complex.I : ℂ) • f) = -Complexification.imLp f := by
  apply Lp.ext
  filter_upwards
      [ContinuousLinearMap.coeFn_compLpL (RCLike.reCLM (K := ℂ)) ((Complex.I : ℂ) • f),
        Lp.coeFn_smul (Complex.I : ℂ) f,
        Lp.coeFn_neg (Complexification.imLp f),
        ContinuousLinearMap.coeFn_compLpL (RCLike.imCLM (K := ℂ)) f]
    with ω h_re h_smul h_neg h_f
  rw [h_neg]
  simp only [Pi.neg_apply]
  rw [show (((Complexification.reLp ((Complex.I : ℂ) • f) : Lp ℝ 2 μ) : Ω → ℝ) ω) =
      (RCLike.reCLM (K := ℂ)) ((((Complex.I : ℂ) • f : Lp ℂ 2 μ) : Ω → ℂ) ω) by
    simpa [Complexification.reLp] using h_re]
  rw [h_smul]
  simp only [Pi.smul_apply]
  rw [show (((Complexification.imLp f : Lp ℝ 2 μ) : Ω → ℝ) ω) =
      (RCLike.imCLM (K := ℂ)) (((f : Lp ℂ 2 μ) : Ω → ℂ) ω) by
    simpa [Complexification.imLp] using h_f]
  change (Complex.I * (((f : Lp ℂ 2 μ) : Ω → ℂ) ω)).re =
    -((((f : Lp ℂ 2 μ) : Ω → ℂ) ω).im)
  simp

private lemma imLp_I_smul_local (f : Lp ℂ 2 μ) :
    Complexification.imLp ((Complex.I : ℂ) • f) = Complexification.reLp f := by
  apply Lp.ext
  filter_upwards
      [ContinuousLinearMap.coeFn_compLpL (RCLike.imCLM (K := ℂ)) ((Complex.I : ℂ) • f),
        Lp.coeFn_smul (Complex.I : ℂ) f,
        ContinuousLinearMap.coeFn_compLpL (RCLike.reCLM (K := ℂ)) f]
    with ω h_im h_smul h_f
  rw [show (((Complexification.imLp ((Complex.I : ℂ) • f) : Lp ℝ 2 μ) : Ω → ℝ) ω) =
      (RCLike.imCLM (K := ℂ)) ((((Complex.I : ℂ) • f : Lp ℂ 2 μ) : Ω → ℂ) ω) by
    simpa [Complexification.imLp] using h_im]
  rw [h_smul]
  simp only [Pi.smul_apply]
  rw [show (((Complexification.reLp f : Lp ℝ 2 μ) : Ω → ℝ) ω) =
      (RCLike.reCLM (K := ℂ)) (((f : Lp ℂ 2 μ) : Ω → ℂ) ω) by
    simpa [Complexification.reLp] using h_f]
  change (Complex.I * (((f : Lp ℂ 2 μ) : Ω → ℂ) ω)).im =
    (((f : Lp ℂ 2 μ) : Ω → ℂ) ω).re
  simp

private lemma reLp_ofReal_smul_local (r : ℝ) (f : Lp ℂ 2 μ) :
    Complexification.reLp ((r : ℂ) • f) = r • Complexification.reLp f := by
  apply Lp.ext
  filter_upwards
      [ContinuousLinearMap.coeFn_compLpL (RCLike.reCLM (K := ℂ)) ((r : ℂ) • f),
        Lp.coeFn_smul (r : ℂ) f,
        Lp.coeFn_smul r (Complexification.reLp f),
        ContinuousLinearMap.coeFn_compLpL (RCLike.reCLM (K := ℂ)) f]
    with ω h_re_smul h_smul h_rhs h_re
  rw [h_rhs]
  simp only [Pi.smul_apply]
  rw [show (((Complexification.reLp ((r : ℂ) • f) : Lp ℝ 2 μ) : Ω → ℝ) ω) =
      (RCLike.reCLM (K := ℂ)) ((((r : ℂ) • f : Lp ℂ 2 μ) : Ω → ℂ) ω) by
    simpa [Complexification.reLp] using h_re_smul]
  rw [h_smul]
  simp only [Pi.smul_apply]
  rw [show (((Complexification.reLp f : Lp ℝ 2 μ) : Ω → ℝ) ω) =
      (RCLike.reCLM (K := ℂ)) (((f : Lp ℂ 2 μ) : Ω → ℂ) ω) by
    simpa [Complexification.reLp] using h_re]
  change ((r : ℂ) * (((f : Lp ℂ 2 μ) : Ω → ℂ) ω)).re =
    r * ((((f : Lp ℂ 2 μ) : Ω → ℂ) ω).re)
  simp

private lemma reLp_complexLift_local
    (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (f : Lp ℂ 2 μ) :
    Complexification.reLp (Complexification.complexLift A f) = A (Complexification.reLp f) := by
  rw [Complexification.complexLift_apply]
  simp [map_add, reLp_I_smul_local, Complexification.reLp_comp_ιLp,
    Complexification.imLp_comp_ιLp]

private lemma imLp_complexLift_local
    (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (f : Lp ℂ 2 μ) :
    Complexification.imLp (Complexification.complexLift A f) = A (Complexification.imLp f) := by
  rw [Complexification.complexLift_apply]
  simp [map_add, imLp_I_smul_local, Complexification.reLp_comp_ιLp,
    Complexification.imLp_comp_ιLp]

private lemma complexLift_one_local :
    Complexification.complexLift (ContinuousLinearMap.id ℝ (Lp ℝ 2 μ))
      = ContinuousLinearMap.id ℂ (Lp ℂ 2 μ) := by
  ext1 f
  simpa [Complexification.complexLift_apply] using
    Complexification.reLp_add_smul_imLp (μ := μ) f

private lemma complexLift_comp_local (A B : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) :
    Complexification.complexLift (A.comp B) =
      (Complexification.complexLift A).comp (Complexification.complexLift B) := by
  ext1 f
  rw [ContinuousLinearMap.comp_apply]
  rw [Complexification.complexLift_apply, Complexification.complexLift_apply]
  rw [reLp_complexLift_local, imLp_complexLift_local]
  rfl

private lemma complexLift_mul_local (A B : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) :
    Complexification.complexLift (A * B) =
      Complexification.complexLift A * Complexification.complexLift B := by
  exact complexLift_comp_local A B

private lemma complexLift_sub_local (A B : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) :
    Complexification.complexLift (A - B) =
      Complexification.complexLift A - Complexification.complexLift B := by
  ext1 f
  rw [Complexification.complexLift_apply]
  change Complexification.ιLp (A (Complexification.reLp f) - B (Complexification.reLp f)) +
      Complex.I • Complexification.ιLp
        (A (Complexification.imLp f) - B (Complexification.imLp f)) =
    Complexification.complexLift A f - Complexification.complexLift B f
  rw [Complexification.complexLift_apply A f, Complexification.complexLift_apply B f]
  rw [map_sub, map_sub, smul_sub]
  abel

private lemma complexLift_algebraMap_real_local (r : ℝ) :
    Complexification.complexLift (algebraMap ℝ (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) r)
      = algebraMap ℂ (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (r : ℂ) := by
  ext1 f
  rw [Complexification.complexLift_apply]
  change Complexification.ιLp (r • Complexification.reLp f) +
      Complex.I • Complexification.ιLp (r • Complexification.imLp f) = (r : ℂ) • f
  calc
    Complexification.ιLp (r • Complexification.reLp f) +
        Complex.I • Complexification.ιLp (r • Complexification.imLp f)
        = (r : ℂ) • (Complexification.ιLp (Complexification.reLp f) +
            Complex.I • Complexification.ιLp (Complexification.imLp f)) := by
      rw [smul_add]
      simp only [map_smul]
      congr 1
      change Complex.I • ((r : ℂ) • Complexification.ιLp (Complexification.imLp f)) =
        (r : ℂ) • (Complex.I • Complexification.ιLp (Complexification.imLp f))
      rw [smul_smul, smul_smul, mul_comm]
    _ = (r : ℂ) • f := by rw [Complexification.reLp_add_smul_imLp]

private lemma complexLift_resolvent_real_local
    (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (r : ℝ) :
    algebraMap ℂ (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (r : ℂ) - Complexification.complexLift A =
      Complexification.complexLift (algebraMap ℝ (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) r - A) := by
  rw [complexLift_sub_local, complexLift_algebraMap_real_local]

private lemma complexLift_isUnit_local
    {B : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ} (hB : IsUnit B) :
    IsUnit (Complexification.complexLift B) := by
  have hone : Complexification.complexLift (1 : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) =
      (1 : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) := by
    simpa using complexLift_one_local (μ := μ)
  refine Units.isUnit
    ⟨Complexification.complexLift B, Complexification.complexLift ↑hB.unit⁻¹, ?_, ?_⟩
  · calc
      Complexification.complexLift B * Complexification.complexLift ↑hB.unit⁻¹
          = Complexification.complexLift (B * ↑hB.unit⁻¹) := by
        rw [complexLift_mul_local]
      _ = Complexification.complexLift 1 := by
        exact congrArg (fun T => Complexification.complexLift T) hB.mul_val_inv
      _ = 1 := hone
  · calc
      Complexification.complexLift ↑hB.unit⁻¹ * Complexification.complexLift B
          = Complexification.complexLift (↑hB.unit⁻¹ * B) := by
        rw [complexLift_mul_local]
      _ = Complexification.complexLift 1 := by
        exact congrArg (fun T => Complexification.complexLift T) hB.val_inv_mul
      _ = 1 := hone

private theorem spectrum_complexLift_subset_real_local
    {A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ} (hA : IsSelfAdjoint A) {z : ℂ}
    (hz : z ∈ spectrum ℂ (Complexification.complexLift A)) :
    z.re ∈ spectrum ℝ A := by
  by_contra hzreal
  have hunitR : IsUnit (algebraMap ℝ (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) z.re - A) :=
    spectrum.notMem_iff.mp hzreal
  have hunitC :
      IsUnit (algebraMap ℂ (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (z.re : ℂ) -
        Complexification.complexLift A) := by
    rw [complexLift_resolvent_real_local]
    exact complexLift_isUnit_local hunitR
  have hzreal_eq : z = (z.re : ℂ) :=
    IsSelfAdjoint.mem_spectrum_eq_re (Complexification.complexLift_isSelfAdjoint hA) hz
  have hnot : (z.re : ℂ) ∉ spectrum ℂ (Complexification.complexLift A) :=
    spectrum.notMem_iff.mpr hunitC
  exact hnot (by rwa [← hzreal_eq])

private lemma realCFC_congr_on_spectrum_local
    (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (f g : ℝ → ℝ)
    (h : ∀ x ∈ spectrum ℝ A, f x = g x) (hA : IsSelfAdjoint A) :
    Complexification.realCFC A f = Complexification.realCFC A g := by
  apply ContinuousLinearMap.ext
  intro v
  change Complexification.reLp (cfc (fun z : ℂ => (f z.re : ℂ))
      (Complexification.complexLift A) (Complexification.ιLp v)) =
    Complexification.reLp (cfc (fun z : ℂ => (g z.re : ℂ))
      (Complexification.complexLift A) (Complexification.ιLp v))
  congr 2
  apply cfc_congr
  intro z hz
  have hzr : z.re ∈ spectrum ℝ A := spectrum_complexLift_subset_real_local hA hz
  simpa using congrArg (fun r : ℝ => (r : ℂ)) (h z.re hzr)

private lemma realCFC_const_add
    (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (hA : IsSelfAdjoint A) (lambda : ℝ) :
    Complexification.realCFC A (fun x => lambda + x)
      = algebraMap ℝ (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) lambda + A := by
  apply ContinuousLinearMap.ext
  intro v
  rw [Complexification.realCFC_apply A hA (fun x => lambda + x)
    (continuous_const.add continuous_id) v]
  rw [show (fun z : ℂ => ((lambda + z.re : ℝ) : ℂ)) =
      fun z : ℂ => (lambda : ℂ) + (z.re : ℂ) by
    funext z
    simp]
  have hcl : IsSelfAdjoint (Complexification.complexLift A) :=
    Complexification.complexLift_isSelfAdjoint hA
  rw [cfc_const_add (lambda : ℂ) (fun z : ℂ => (z.re : ℂ))
    (Complexification.complexLift A)]
  change Complexification.reLp
      (((algebraMap ℂ (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (lambda : ℂ) +
          cfc (fun z : ℂ => ((id z.re : ℝ) : ℂ)) (Complexification.complexLift A))
        (Complexification.ιLp v))) =
    ((algebraMap ℝ (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) lambda + A) v)
  rw [← cfc_real_eq_complex (a := Complexification.complexLift A) (f := id) (ha := hcl)]
  rw [cfc_id ℝ (Complexification.complexLift A) hcl]
  simp only [ContinuousLinearMap.add_apply]
  rw [map_add]
  rw [Algebra.algebraMap_eq_smul_one]
  rw [Algebra.algebraMap_eq_smul_one]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply]
  rw [reLp_ofReal_smul_local, Complexification.reLp_comp_ιLp,
    Complexification.reLp_complexLift_real]

private lemma resolvent_left_inverse
    (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (hA : IsSelfAdjoint A)
    (hA_spec : ∀ x ∈ spectrum ℝ A, 0 ≤ x)
    {lambda : ℝ} (hlam : 0 < lambda) :
    (algebraMap ℝ (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) lambda + A).comp
      (Complexification.realCFC A (fun x => x / (lambda + x)))
      = A := by
  rw [← realCFC_const_add A hA lambda]
  have hsafe_ne : ∀ x : ℝ, lambda + max 0 x ≠ 0 := fun x => by
    have hmax : (0 : ℝ) ≤ max 0 x := le_max_left _ _
    have hpos : 0 < lambda + max 0 x := by linarith
    exact ne_of_gt hpos
  have hsafe_cont : Continuous (fun x : ℝ => x * (lambda + max 0 x)⁻¹) :=
    continuous_id.mul ((continuous_const.add (continuous_const.max continuous_id)).inv₀ hsafe_ne)
  have hquot : Complexification.realCFC A (fun x => x / (lambda + x)) =
      Complexification.realCFC A (fun x => x * (lambda + max 0 x)⁻¹) := by
    apply realCFC_congr_on_spectrum_local A
    · intro x hx
      have hx0 : 0 ≤ x := hA_spec x hx
      rw [max_eq_right hx0]
      rfl
    · exact hA
  rw [hquot]
  rw [← Complexification.realCFC_mul A hA (fun x => lambda + x)
    (fun x => x * (lambda + max 0 x)⁻¹) (continuous_const.add continuous_id) hsafe_cont]
  have hprod : ∀ x ∈ spectrum ℝ A,
      (lambda + x) * (x * (lambda + max 0 x)⁻¹) = id x := fun x hx => by
    have hx0 : 0 ≤ x := hA_spec x hx
    rw [max_eq_right hx0]
    have hne : lambda + x ≠ 0 := by
      have hpos : 0 < lambda + x := by linarith
      exact ne_of_gt hpos
    calc
      (lambda + x) * (x * (lambda + x)⁻¹)
          = ((lambda + x) * (lambda + x)⁻¹) * x := by ring
      _ = x := by rw [mul_inv_cancel₀ hne, one_mul]
  rw [realCFC_congr_on_spectrum_local A
    (fun x => (lambda + x) * (x * (lambda + max 0 x)⁻¹)) id hprod hA]
  apply ContinuousLinearMap.ext
  intro v
  rw [Complexification.realCFC_id A hA v]

/-- **Resolvent identification of the Lax–Milgram minimiser.**

When `Hbar_L2 = ⊤`, the Tikhonov minimiser produced by Lax–Milgram on
`Hbar_L2` is the resolvent expression
`(T†T + λI)⁻¹ T†T h₀ = realCFC (T†T) (x ↦ x/(λ+x)) h₀`.

Proof strategy:
* Set `Aλ := realCFC S.Tstar_T (fun x => x / (lambda + x))` and apply
  to `S.hL2 S.h₀_mem`.  Show `Aλ` is the unique element of the ambient
  `Lp ℝ 2 μ` satisfying `(T†T + λI) Aλ h₀ = T†T h₀`.
* Use `Complexification.realCFC_resolvent_mul_self` to get
  `(λ+x) · (x/(λ+x)) = x` at the symbol level, hence
  `realCFC (T†T) (fun x => (λ+x) · (x/(λ+x))) = realCFC (T†T) id =
  T†T` (via `realCFC_mul` and `realCFC_id`).
* By the variational identity `tikhonovMinimiserL2_optimality` on
  `Hbar_L2 = ⊤`, the minimiser satisfies the same operator equation
  on the full space.  Uniqueness (from coercivity / strict convexity)
  gives the identification. -/
theorem tikhonovMinimiserL2_eq_resolvent
    (sc : SpectralSourceCondition S β) {lambda : ℝ} (lambda_pos : 0 < lambda) :
    haveI := sc.Hbar_L2_hasProj
    S.tikhonovMinimiserL2 lambda
      = Complexification.realCFC S.Tstar_T
          (fun x => x / (lambda + x)) (S.hL2 S.h₀_mem) := by
  haveI := sc.Hbar_L2_hasProj
  set A := S.Tstar_T with hA_def
  set R : Lp ℝ 2 μ :=
    Complexification.realCFC A (fun x => x / (lambda + x)) (S.hL2 S.h₀_mem)
  set h_star : Lp ℝ 2 μ := S.tikhonovMinimiserL2 lambda
  have hvar : ∀ v : Lp ℝ 2 μ,
      inner ℝ (S.Tlin h_star) (S.Tlin v) + lambda * inner ℝ h_star v
        = inner ℝ (S.Tlin (S.hL2 S.h₀_mem)) (S.Tlin v) := by
    intro v
    have hv : v ∈ S.Hbar_L2 := by
      rw [sc.Hbar_L2_eq_top]
      exact Submodule.mem_top
    exact S.tikhonovMinimiserL2_optimality lambda_pos hv
  have hop_star :
      S.Tadjoint (S.Tlin h_star) + lambda • h_star =
        S.Tadjoint (S.Tlin (S.hL2 S.h₀_mem)) := by
    apply ext_inner_right ℝ
    intro v
    rw [inner_add_left, inner_smul_left]
    rw [OperatorSystem.Tadjoint]
    rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left]
    simpa using hvar v
  have hop_star' :
      A h_star + lambda • h_star = A (S.hL2 S.h₀_mem) := by
    simpa [hA_def, OperatorSystem.Tstar_T, ContinuousLinearMap.comp_apply] using hop_star
  have hA_sa : IsSelfAdjoint A := by
    simpa [hA_def] using S.Tstar_T_isSelfAdjoint
  have hres :
      (algebraMap ℝ (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) lambda + A) R =
        A (S.hL2 S.h₀_mem) := by
    have h := resolvent_left_inverse A hA_sa (by
      intro x hx
      exact sc.Tstar_T_spectrum_nonneg x (by simpa [hA_def] using hx)) lambda_pos
    have happ :=
      congrArg (fun T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ => T (S.hL2 S.h₀_mem)) h
    simpa [R] using happ
  have hop_R : A R + lambda • R = A (S.hL2 S.h₀_mem) := by
    simpa [ContinuousLinearMap.add_apply, Algebra.algebraMap_eq_smul_one,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, add_comm] using hres
  have hdiff : A (h_star - R) + lambda • (h_star - R) = 0 := by
    have heq : A h_star + lambda • h_star = A R + lambda • R :=
      hop_star'.trans hop_R.symm
    calc
      A (h_star - R) + lambda • (h_star - R)
          = (A h_star + lambda • h_star) - (A R + lambda • R) := by
        simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      _ = 0 := by rw [heq]; simp
  have hpos_self :
      inner ℝ (A (h_star - R)) (h_star - R) = ‖S.Tlin (h_star - R)‖ ^ 2 := by
    subst A
    change inner ℝ (S.Tadjoint (S.Tlin (h_star - R))) (h_star - R) = _
    rw [OperatorSystem.Tadjoint, ContinuousLinearMap.adjoint_inner_left]
    exact real_inner_self_eq_norm_sq _
  have hzero :
      ‖S.Tlin (h_star - R)‖ ^ 2 + lambda * ‖h_star - R‖ ^ 2 = 0 := by
    have hpair := congrArg (fun u => inner ℝ u (h_star - R)) hdiff
    simp only [inner_zero_left, inner_add_left, inner_smul_left] at hpair
    have hnorm_sq : inner ℝ (h_star - R) (h_star - R) = ‖h_star - R‖ ^ 2 :=
      real_inner_self_eq_norm_sq _
    rw [hpos_self, hnorm_sq] at hpair
    simpa using hpair
  have hsq_zero : ‖h_star - R‖ ^ 2 = 0 := by
    have hT_nn : 0 ≤ ‖S.Tlin (h_star - R)‖ ^ 2 := sq_nonneg _
    have hw_nn : 0 ≤ ‖h_star - R‖ := norm_nonneg _
    nlinarith [hzero, hT_nn, lambda_pos, hw_nn]
  have hnorm_zero : ‖h_star - R‖ = 0 := by
    exact sq_eq_zero_iff.mp hsq_zero
  have hsub_zero : h_star - R = 0 := norm_eq_zero.mp hnorm_zero
  simpa [h_star, R, hA_def] using sub_eq_zero.mp hsub_zero

/-! ## Bias bounds -/

private lemma realCFC_sub_local
    (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (hA : IsSelfAdjoint A)
    (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
    Complexification.realCFC A (fun x => f x - g x) =
      Complexification.realCFC A f - Complexification.realCFC A g := by
  ext1 v
  rw [Complexification.realCFC_apply A hA (fun x => f x - g x) (hf.sub hg) v]
  simp only [ContinuousLinearMap.sub_apply]
  rw [Complexification.realCFC_apply A hA f hf v]
  rw [Complexification.realCFC_apply A hA g hg v]
  rw [show (fun z : ℂ => (((f z.re - g z.re : ℝ) : ℂ))) =
      fun z : ℂ => (f z.re : ℂ) - (g z.re : ℂ) by
    funext z
    norm_num]
  rw [cfc_sub (fun z : ℂ => (f z.re : ℂ)) (fun z : ℂ => (g z.re : ℂ))
    (Complexification.complexLift A)
    (hf := (Complex.continuous_ofReal.comp (hf.comp Complex.continuous_re)).continuousOn)
    (hg := (Complex.continuous_ofReal.comp (hg.comp Complex.continuous_re)).continuousOn)]
  simp

private lemma residual_symbol_bound_small
    {x lambda β B : ℝ} (hl : 0 < lambda) (hx : 0 ≤ x)
    (hβ0 : 0 ≤ β) (hβ2 : β ≤ 2) (hB : 1 ≤ B) :
    |(-lambda * sourceSymbol β x / (lambda + max 0 x))| ≤
      B ^ (β / 2) * lambda ^ (min β 2 / 2) := by
  have hb_nonneg : 0 ≤ β / 2 := by linarith
  have hb_le_one : β / 2 ≤ 1 := by linarith
  have hden_pos : 0 < lambda + x := by linarith
  have hden_max : lambda + max 0 x = lambda + x := by rw [max_eq_right hx]
  have hsrc : sourceSymbol β x = x ^ (β / 2) := by
    simp [sourceSymbol, max_eq_left hx]
  have hmin : min β 2 = β := min_eq_left hβ2
  rw [hden_max, hsrc, hmin]
  rw [abs_div, abs_mul, abs_neg, abs_of_pos hl]
  rw [abs_of_nonneg (Real.rpow_nonneg hx _), abs_of_pos hden_pos]
  have hx_le_den : x ≤ lambda + x := by linarith
  have hl_le_den : lambda ≤ lambda + x := by linarith
  have hpow_le : x ^ (β / 2) ≤ (lambda + x) ^ (β / 2) :=
    Real.rpow_le_rpow hx hx_le_den hb_nonneg
  have hdiv_le : x ^ (β / 2) / (lambda + x) ≤
      (lambda + x) ^ (β / 2) / (lambda + x) :=
    div_le_div_of_nonneg_right hpow_le (le_of_lt hden_pos)
  have hden_pow : (lambda + x) ^ (β / 2) / (lambda + x) =
      (lambda + x) ^ (β / 2 - 1) := by
    rw [Real.rpow_sub hden_pos, Real.rpow_one]
  have hpow_neg : (lambda + x) ^ (β / 2 - 1) ≤ lambda ^ (β / 2 - 1) := by
    exact Real.rpow_le_rpow_of_nonpos hl hl_le_den (by linarith)
  have hmul_lam : lambda * lambda ^ (β / 2 - 1) = lambda ^ (β / 2) := by
    calc
      lambda * lambda ^ (β / 2 - 1) =
          lambda ^ 1 * lambda ^ (β / 2 - 1) := by simp
      _ = lambda ^ (1 + (β / 2 - 1)) := (Real.rpow_add hl 1 (β / 2 - 1)).symm
      _ = lambda ^ (β / 2) := by ring_nf
  have hsmall : lambda * x ^ (β / 2) / (lambda + x) ≤ lambda ^ (β / 2) := by
    calc
      lambda * x ^ (β / 2) / (lambda + x)
          = lambda * (x ^ (β / 2) / (lambda + x)) := by ring
      _ ≤ lambda * ((lambda + x) ^ (β / 2) / (lambda + x)) := by gcongr
      _ = lambda * (lambda + x) ^ (β / 2 - 1) := by rw [hden_pow]
      _ ≤ lambda * lambda ^ (β / 2 - 1) := by gcongr
      _ = lambda ^ (β / 2) := hmul_lam
  have hBpow : 1 ≤ B ^ (β / 2) := Real.one_le_rpow hB hb_nonneg
  have hlpow_nonneg : 0 ≤ lambda ^ (β / 2) := Real.rpow_nonneg (le_of_lt hl) _
  calc
    lambda * x ^ (β / 2) / (lambda + x) ≤ lambda ^ (β / 2) := hsmall
    _ ≤ B ^ (β / 2) * lambda ^ (β / 2) := by nlinarith

private lemma residual_symbol_bound_large
    {x lambda β B : ℝ} (hl : 0 < lambda) (hx : 0 ≤ x) (hxB : x ≤ B)
    (hβ2 : 2 < β) (hB : 1 ≤ B) :
    |(-lambda * sourceSymbol β x / (lambda + max 0 x))| ≤
      B ^ (β / 2) * lambda ^ (min β 2 / 2) := by
  have hb_pos : 0 < β / 2 := by linarith
  have hb_minus_nonneg : 0 ≤ β / 2 - 1 := by linarith
  have hden_pos : 0 < lambda + x := by linarith
  have hden_max : lambda + max 0 x = lambda + x := by rw [max_eq_right hx]
  have hsrc : sourceSymbol β x = x ^ (β / 2) := by
    simp [sourceSymbol, max_eq_left hx]
  have hmin : min β 2 = 2 := min_eq_right (le_of_lt hβ2)
  rw [hden_max, hsrc, hmin]
  rw [abs_div, abs_mul, abs_neg, abs_of_pos hl]
  rw [abs_of_nonneg (Real.rpow_nonneg hx _), abs_of_pos hden_pos]
  rw [show (2 : ℝ) / 2 = 1 by norm_num, Real.rpow_one]
  have hB_pos : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hquot : x ^ (β / 2) / (lambda + x) ≤ B ^ (β / 2) := by
    by_cases hxzero : x = 0
    · subst x
      have hb_ne : β / 2 ≠ 0 := ne_of_gt hb_pos
      rw [Real.zero_rpow hb_ne]
      have hden0 : lambda + 0 = lambda := by ring
      rw [hden0, zero_div]
      exact Real.rpow_nonneg (le_of_lt hB_pos) _
    · have hx_pos : 0 < x := lt_of_le_of_ne hx (Ne.symm hxzero)
      have hx_le_den : x ≤ lambda + x := by linarith
      have hdiv_le : x ^ (β / 2) / (lambda + x) ≤ x ^ (β / 2) / x :=
        div_le_div_of_nonneg_left (Real.rpow_nonneg hx _) hx_pos hx_le_den
      have hxpow_div : x ^ (β / 2) / x = x ^ (β / 2 - 1) := by
        rw [Real.rpow_sub hx_pos, Real.rpow_one]
      have hxBpow : x ^ (β / 2 - 1) ≤ B ^ (β / 2 - 1) :=
        Real.rpow_le_rpow hx hxB hb_minus_nonneg
      have hBexp : B ^ (β / 2 - 1) ≤ B ^ (β / 2) :=
        Real.rpow_le_rpow_of_exponent_le hB (by linarith)
      calc
        x ^ (β / 2) / (lambda + x) ≤ x ^ (β / 2) / x := hdiv_le
        _ = x ^ (β / 2 - 1) := hxpow_div
        _ ≤ B ^ (β / 2 - 1) := hxBpow
        _ ≤ B ^ (β / 2) := hBexp
  calc
    lambda * x ^ (β / 2) / (lambda + x)
        = lambda * (x ^ (β / 2) / (lambda + x)) := by ring
    _ ≤ lambda * B ^ (β / 2) := by gcongr
    _ = B ^ (β / 2) * lambda := by ring

private lemma weak_residual_bound
    {x lambda β B : ℝ} (hl : 0 < lambda) (hx : 0 ≤ x) (hxB : x ≤ B)
    (hβ0 : 0 ≤ β) (hB : 1 ≤ B) :
    |x * (-lambda * sourceSymbol β x / (lambda + max 0 x)) ^ 2|
      ≤ B ^ β * lambda ^ (min (β + 1) 2) := by
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hden_pos : 0 < lambda + x := by linarith
  have hden_max : lambda + max 0 x = lambda + x := by rw [max_eq_right hx]
  have hsrc : sourceSymbol β x = x ^ (β / 2) := by
    simp [sourceSymbol, max_eq_left hx]
  have hbase_nonneg : 0 ≤ x * (-lambda * sourceSymbol β x / (lambda + max 0 x)) ^ 2 :=
    mul_nonneg hx (sq_nonneg _)
  rw [abs_of_nonneg hbase_nonneg, hden_max, hsrc]
  by_cases hβ1 : β ≤ 1
  · have hmin : min (β + 1) 2 = β + 1 := by
      rw [min_eq_left]
      linarith
    rw [hmin]
    have hβp1_nonneg : 0 ≤ β + 1 := by linarith
    have hβp1_pos : 0 < β + 1 := by linarith
    have hx_le_den : x ≤ lambda + x := by linarith
    have hl_le_den : lambda ≤ lambda + x := by linarith
    have hpow_le : x ^ (β + 1) ≤ (lambda + x) ^ (β + 1) :=
      Real.rpow_le_rpow hx hx_le_den hβp1_nonneg
    have hden_sq_pos : 0 < (lambda + x) ^ 2 := sq_pos_of_pos hden_pos
    have hdiv_le : x ^ (β + 1) / (lambda + x) ^ 2 ≤
        (lambda + x) ^ (β + 1) / (lambda + x) ^ 2 :=
      div_le_div_of_nonneg_right hpow_le (le_of_lt hden_sq_pos)
    have hden_pow : (lambda + x) ^ (β + 1) / (lambda + x) ^ 2 =
        (lambda + x) ^ (β - 1) := by
      calc
        (lambda + x) ^ (β + 1) / (lambda + x) ^ 2
            = (lambda + x) ^ (β + 1) / (lambda + x) ^ (2 : ℝ) := by norm_num
        _ = (lambda + x) ^ ((β + 1) - 2) := by rw [Real.rpow_sub hden_pos]
        _ = (lambda + x) ^ (β - 1) := by ring_nf
    have hpow_neg : (lambda + x) ^ (β - 1) ≤ lambda ^ (β - 1) :=
      Real.rpow_le_rpow_of_nonpos hl hl_le_den (by linarith)
    have hmul_lam : lambda ^ 2 * lambda ^ (β - 1) = lambda ^ (β + 1) := by
      rw [show lambda ^ (2 : ℕ) = lambda ^ (2 : ℝ) by norm_num]
      rw [← Real.rpow_add hl]
      congr 1
      ring
    have hmain :
        lambda ^ 2 * x ^ (β + 1) / (lambda + x) ^ 2 ≤ lambda ^ (β + 1) := by
      calc
        lambda ^ 2 * x ^ (β + 1) / (lambda + x) ^ 2
            = lambda ^ 2 * (x ^ (β + 1) / (lambda + x) ^ 2) := by ring
        _ ≤ lambda ^ 2 * ((lambda + x) ^ (β + 1) / (lambda + x) ^ 2) := by
          gcongr
        _ = lambda ^ 2 * (lambda + x) ^ (β - 1) := by rw [hden_pow]
        _ ≤ lambda ^ 2 * lambda ^ (β - 1) := by gcongr
        _ = lambda ^ (β + 1) := hmul_lam
    have hBpow : 1 ≤ B ^ β := Real.one_le_rpow hB hβ0
    have hlpow_nonneg : 0 ≤ lambda ^ (β + 1) := Real.rpow_nonneg (le_of_lt hl) _
    have hxpow : x * (x ^ (β / 2)) ^ 2 = x ^ (β + 1) := by
      by_cases hxzero : x = 0
      · subst x
        rw [zero_mul]
        exact (Real.zero_rpow (ne_of_gt hβp1_pos)).symm
      · have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hxzero)
        rw [sq]
        calc
          x * (x ^ (β / 2) * x ^ (β / 2))
              = (x ^ (1 : ℝ) * x ^ (β / 2)) * x ^ (β / 2) := by
                rw [Real.rpow_one]
                ring
          _ = x ^ ((1 : ℝ) + β / 2) * x ^ (β / 2) := by
                rw [← Real.rpow_add hxp]
          _ = x ^ ((1 : ℝ) + β / 2 + β / 2) := by rw [← Real.rpow_add hxp]
          _ = x ^ (β + 1) := by congr 1; ring
    calc
      x * (-lambda * x ^ (β / 2) / (lambda + x)) ^ 2
          = lambda ^ 2 * x ^ (β + 1) / (lambda + x) ^ 2 := by
            have hden_ne : lambda + x ≠ 0 := ne_of_gt hden_pos
            field_simp [hden_ne]
            exact hxpow
      _ ≤ lambda ^ (β + 1) := hmain
      _ ≤ B ^ β * lambda ^ (β + 1) := by nlinarith
  · have hβgt : 1 < β := lt_of_not_ge hβ1
    have hmin : min (β + 1) 2 = 2 := by
      rw [min_eq_right]
      linarith
    rw [hmin]
    have hβm_nonneg : 0 ≤ β - 1 := by linarith
    have hβp1_pos : 0 < β + 1 := by linarith
    have hBpow : B ^ (β - 1) ≤ B ^ β :=
      Real.rpow_le_rpow_of_exponent_le hB (by linarith)
    by_cases hxzero : x = 0
    · subst x
      rw [zero_mul]
      exact mul_nonneg (Real.rpow_nonneg (le_of_lt hBpos) _)
        (Real.rpow_nonneg (le_of_lt hl) _)
    · have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hxzero)
      have hx_sq_pos : 0 < x ^ 2 := sq_pos_of_pos hxp
      have hx_sq_le_den_sq : x ^ 2 ≤ (lambda + x) ^ 2 := by nlinarith
      have hnum_nonneg : 0 ≤ x ^ (β + 1) := Real.rpow_nonneg hx _
      have hdiv_le : x ^ (β + 1) / (lambda + x) ^ 2 ≤ x ^ (β + 1) / x ^ 2 :=
        div_le_div_of_nonneg_left hnum_nonneg hx_sq_pos hx_sq_le_den_sq
      have hxpow_div : x ^ (β + 1) / x ^ 2 = x ^ (β - 1) := by
        calc
          x ^ (β + 1) / x ^ 2 = x ^ (β + 1) / x ^ (2 : ℝ) := by norm_num
          _ = x ^ ((β + 1) - 2) := by rw [Real.rpow_sub hxp]
          _ = x ^ (β - 1) := by ring_nf
      have hxBpow : x ^ (β - 1) ≤ B ^ (β - 1) :=
        Real.rpow_le_rpow hx hxB hβm_nonneg
      have hquot : x ^ (β + 1) / (lambda + x) ^ 2 ≤ B ^ β := by
        calc
          x ^ (β + 1) / (lambda + x) ^ 2 ≤ x ^ (β + 1) / x ^ 2 := hdiv_le
          _ = x ^ (β - 1) := hxpow_div
          _ ≤ B ^ (β - 1) := hxBpow
          _ ≤ B ^ β := hBpow
      have hxpow : x * (x ^ (β / 2)) ^ 2 = x ^ (β + 1) := by
        rw [sq]
        calc
          x * (x ^ (β / 2) * x ^ (β / 2))
              = (x ^ (1 : ℝ) * x ^ (β / 2)) * x ^ (β / 2) := by
                rw [Real.rpow_one]
                ring
          _ = x ^ ((1 : ℝ) + β / 2) * x ^ (β / 2) := by
                rw [← Real.rpow_add hxp]
          _ = x ^ ((1 : ℝ) + β / 2 + β / 2) := by rw [← Real.rpow_add hxp]
          _ = x ^ (β + 1) := by congr 1; ring
      have hmain :
          lambda ^ 2 * x ^ (β + 1) / (lambda + x) ^ 2 ≤ B ^ β * lambda ^ (2 : ℝ) := by
        rw [show lambda ^ (2 : ℝ) = lambda ^ (2 : ℕ) by norm_num]
        calc
          lambda ^ 2 * x ^ (β + 1) / (lambda + x) ^ 2
              = lambda ^ 2 * (x ^ (β + 1) / (lambda + x) ^ 2) := by ring
          _ ≤ lambda ^ 2 * B ^ β := by gcongr
          _ = B ^ β * lambda ^ 2 := by ring
      calc
        x * (-lambda * x ^ (β / 2) / (lambda + x)) ^ 2
            = lambda ^ 2 * x ^ (β + 1) / (lambda + x) ^ 2 := by
              have hden_ne : lambda + x ≠ 0 := ne_of_gt hden_pos
              field_simp [hden_ne]
              exact hxpow
        _ ≤ B ^ β * lambda ^ (2 : ℝ) := hmain

/-- **Strong-metric Tikhonov bias bound.**

Spectral derivation: by `tikhonovMinimiserL2_eq_resolvent` and the
spectral identity `h₀ = realCFC (T†T) (·^{β/2}) w₀` from
`SourceCondition.spectral_identity`,
    h*_λ − h₀ = realCFC (T†T) (x ↦ −λ x^{β/2}/(λ+x)) w₀.

By `Complexification.realCFC_norm_le` with the uniform sup bound
`sup_{x ≥ 0} (λ x^{β/2}/(λ+x))² ≤ biasConst · λ^{min(β,2)}`, the squared
norm is bounded by `biasConst · ‖w₀‖² · λ^{min(β,2)}`.

Proof strategy:
1.  Apply `tikhonovMinimiserL2_eq_resolvent` and `spectral_identity`.
2.  Use `Complexification.realCFC_mul` to merge the two real CFCs into
    a single CFC with the product symbol.
3.  Apply `Complexification.realCFC_norm_le` with the sup-on-spectrum
    bound (real-analysis lemma: for `x ∈ [0, ‖T†T‖]` and `λ > 0`,
    `(λ x^{β/2}/(λ+x))² ≤ biasConst · λ^{min(β,2)}`).
4.  Square to get the squared-norm bound. -/
theorem strong_bias (sc : SpectralSourceCondition S β)
    {lambda : ℝ} (lambda_pos : 0 < lambda) :
    haveI := sc.Hbar_L2_hasProj
    ‖S.tikhonovMinimiserL2 lambda - S.hL2 S.h₀_mem‖ ^ 2
      ≤ sc.biasConst * ‖S.hL2 sc.w₀_mem‖ ^ 2 * lambda ^ (min β 2) := by
  haveI := sc.Hbar_L2_hasProj
  by_cases hnt : Nontrivial (Lp ℝ 2 μ)
  swap
  · haveI : Subsingleton (Lp ℝ 2 μ) := not_nontrivial_iff_subsingleton.mp hnt
    have hdiff : S.tikhonovMinimiserL2 lambda - S.hL2 S.h₀_mem = 0 := Subsingleton.elim _ _
    have hpow_nonneg : 0 ≤ lambda ^ (min β 2) := Real.rpow_nonneg (le_of_lt lambda_pos) _
    have hrhs_nonneg :
        0 ≤ sc.biasConst * ‖S.hL2 sc.w₀_mem‖ ^ 2 * lambda ^ (min β 2) :=
      mul_nonneg (mul_nonneg sc.biasConst_nonneg (sq_nonneg _)) hpow_nonneg
    simpa [hdiff] using hrhs_nonneg
  haveI : Nontrivial (Lp ℝ 2 μ) := hnt
  haveI : NormOneClass (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) := ContinuousLinearMap.normOneClass
  set A := S.Tstar_T with hA_def
  set w := S.hL2 sc.w₀_mem with hw_def
  set B : ℝ := max 1 (‖A‖ + 1) with hB_def
  set c : ℝ := B ^ (β / 2) * lambda ^ (min β 2 / 2) with hc_def
  have hA_sa : IsSelfAdjoint A := by simpa [hA_def] using S.Tstar_T_isSelfAdjoint
  have hβ : 0 ≤ β := sc.beta_nonneg
  have hB_ge_one : 1 ≤ B := by
    rw [hB_def]
    exact le_max_left _ _
  have hB_pos : 0 < B := lt_of_lt_of_le zero_lt_one hB_ge_one
  have hc_nonneg : 0 ≤ c := by
    rw [hc_def]
    exact mul_nonneg (Real.rpow_nonneg (le_of_lt hB_pos) _)
      (Real.rpow_nonneg (le_of_lt lambda_pos) _)
  have hden : ∀ x : ℝ, lambda + max 0 x ≠ 0 := fun x => by
    have hmax : (0 : ℝ) ≤ max 0 x := le_max_left _ _
    have hpos : 0 < lambda + max 0 x := by linarith
    exact ne_of_gt hpos
  let rSafe : ℝ → ℝ := fun x => x / (lambda + max 0 x)
  let prod : ℝ → ℝ := fun x => rSafe x * sourceSymbol β x
  have hr_cont : Continuous rSafe := by
    dsimp [rSafe]
    exact continuous_id.div (continuous_const.add (continuous_const.max continuous_id)) hden
  have hsrc_cont : Continuous (sourceSymbol β) := continuous_sourceSymbol hβ
  have hsource_eq : (fun x : ℝ => Real.rpow (max x 0) (β / 2)) = sourceSymbol β := rfl
  have hres_safe : Complexification.realCFC A (fun x => x / (lambda + x)) =
      Complexification.realCFC A rSafe := by
    apply realCFC_congr_on_spectrum_local A
    · intro x hx
      have hx0 : 0 ≤ x := sc.Tstar_T_spectrum_nonneg x (by simpa [hA_def] using hx)
      dsimp [rSafe]
      rw [max_eq_right hx0]
    · exact hA_sa
  have hmul : Complexification.realCFC A prod =
      (Complexification.realCFC A rSafe).comp
        (Complexification.realCFC A (sourceSymbol β)) := by
    dsimp [prod]
    exact Complexification.realCFC_mul A hA_sa rSafe (sourceSymbol β) hr_cont hsrc_cont
  have hsub_cfc : Complexification.realCFC A (fun x => prod x - sourceSymbol β x) =
      Complexification.realCFC A prod - Complexification.realCFC A (sourceSymbol β) :=
    realCFC_sub_local A hA_sa prod (sourceSymbol β) (hr_cont.mul hsrc_cont) hsrc_cont
  have hsymbol : Complexification.realCFC A (fun x => prod x - sourceSymbol β x) =
      Complexification.realCFC A
        (fun x => -lambda * sourceSymbol β x / (lambda + max 0 x)) := by
    apply realCFC_congr_on_spectrum_local A
    · intro x hx
      have hx0 : 0 ≤ x := sc.Tstar_T_spectrum_nonneg x (by simpa [hA_def] using hx)
      have hne : lambda + max 0 x ≠ 0 := hden x
      dsimp [prod, rSafe]
      rw [max_eq_right hx0]
      field_simp [hne]
      ring
    · exact hA_sa
  have hresid :
      S.tikhonovMinimiserL2 lambda - S.hL2 S.h₀_mem =
        Complexification.realCFC A
          (fun x => -lambda * sourceSymbol β x / (lambda + max 0 x)) w := by
    calc
      S.tikhonovMinimiserL2 lambda - S.hL2 S.h₀_mem
          = (Complexification.realCFC A rSafe)
              ((Complexification.realCFC A (sourceSymbol β)) w) -
            (Complexification.realCFC A (sourceSymbol β)) w := by
          rw [tikhonovMinimiserL2_eq_resolvent (S := S) (β := β) sc lambda_pos]
          rw [sc.spectral_identity]
          rw [hsource_eq]
          rw [hres_safe]
      _ = ((Complexification.realCFC A rSafe).comp
            (Complexification.realCFC A (sourceSymbol β))) w -
            (Complexification.realCFC A (sourceSymbol β)) w := by rfl
      _ = (Complexification.realCFC A prod -
            Complexification.realCFC A (sourceSymbol β)) w := by
          rw [← hmul]
          simp only [ContinuousLinearMap.sub_apply]
      _ = Complexification.realCFC A (fun x => prod x - sourceSymbol β x) w := by
          rw [hsub_cfc]
      _ = Complexification.realCFC A
            (fun x => -lambda * sourceSymbol β x / (lambda + max 0 x)) w := by
          rw [hsymbol]
  have hsafe_cont :
      Continuous (fun x : ℝ => -lambda * sourceSymbol β x / (lambda + max 0 x)) :=
    (continuous_const.mul hsrc_cont).div
      (continuous_const.add (continuous_const.max continuous_id)) hden
  have hsup : ∀ x ∈ spectrum ℝ A,
      |(-lambda * sourceSymbol β x / (lambda + max 0 x))| ≤ c := by
    intro x hx
    have hx0 : 0 ≤ x := sc.Tstar_T_spectrum_nonneg x (by simpa [hA_def] using hx)
    rw [hc_def]
    by_cases hβ2 : β ≤ 2
    · exact residual_symbol_bound_small lambda_pos hx0 hβ hβ2 hB_ge_one
    · have hxnorm : ‖x‖ ≤ ‖A‖ := spectrum.norm_le_norm_of_mem hx
      have hx_le_norm : x ≤ ‖A‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg hx0] at hxnorm
        exact hxnorm
      have hnorm_le_B : ‖A‖ ≤ B := by
        calc
          ‖A‖ ≤ ‖A‖ + 1 := by linarith [norm_nonneg A]
          _ ≤ max 1 (‖A‖ + 1) := le_max_right _ _
          _ = B := by rw [hB_def]
      have hxB : x ≤ B := le_trans hx_le_norm hnorm_le_B
      exact residual_symbol_bound_large lambda_pos hx0 hxB (lt_of_not_ge hβ2) hB_ge_one
  have hnorm :=
    Complexification.realCFC_norm_le A hA_sa
      (fun x => -lambda * sourceSymbol β x / (lambda + max 0 x)) hsafe_cont
      c hc_nonneg hsup w
  have hsq :
      ‖Complexification.realCFC A
          (fun x => -lambda * sourceSymbol β x / (lambda + max 0 x)) w‖ ^ 2
        ≤ (c * ‖w‖) ^ 2 :=
    sq_le_sq' (by
      have hmul_nonneg : 0 ≤ c * ‖w‖ := mul_nonneg hc_nonneg (norm_nonneg _)
      nlinarith [norm_nonneg
        (Complexification.realCFC A
          (fun x => -lambda * sourceSymbol β x / (lambda + max 0 x)) w), hmul_nonneg]) hnorm
  have hcoef : (c * ‖w‖) ^ 2 =
      sc.biasConst * ‖w‖ ^ 2 * lambda ^ (min β 2) := by
    rw [hc_def, mul_pow, mul_pow]
    rw [show (B ^ (β / 2)) ^ (2 : ℕ) = B ^ β by
      rw [sq, ← Real.rpow_add hB_pos]
      congr 1
      ring]
    rw [show (lambda ^ (min β 2 / 2)) ^ (2 : ℕ) = lambda ^ (min β 2) by
      rw [sq, ← Real.rpow_add lambda_pos]
      congr 1
      ring]
    rw [biasConst]
    simp [hB_def, hA_def]
    ring
  calc
    ‖S.tikhonovMinimiserL2 lambda - S.hL2 S.h₀_mem‖ ^ 2
        = ‖Complexification.realCFC A
            (fun x => -lambda * sourceSymbol β x / (lambda + max 0 x)) w‖ ^ 2 := by
          rw [hresid]
    _ ≤ (c * ‖w‖) ^ 2 := hsq
    _ = sc.biasConst * ‖S.hL2 sc.w₀_mem‖ ^ 2 * lambda ^ (min β 2) := by
          rw [hcoef, hw_def]

/-- **Weak-metric Tikhonov bias bound.**

Spectral derivation: from the same resolvent identity for `h*_λ − h₀`,
    ‖T(h*_λ − h₀)‖² = ⟨T†T (h*_λ − h₀), h*_λ − h₀⟩
                    = ⟨realCFC (T†T) (x · (λ x^{β/2}/(λ+x))²) w₀, w₀⟩.

By Cauchy–Schwarz and `realCFC_norm_le` with the sup bound
`sup_{x ≥ 0} x · (λ x^{β/2}/(λ+x))² ≤ biasConst · λ^{min(β+1, 2)}`,
the LHS is bounded by `biasConst · ‖w₀‖² · λ^{min(β+1, 2)}`.

Proof strategy:
1.  Rewrite `‖T u‖²` as `⟨T†T u, u⟩` (positivity of `T†T`).
2.  Substitute `u = realCFC (T†T) (...) w₀` from the resolvent + source
    identities.
3.  Use `realCFC_mul` and the action of `realCFC (T†T) id = T†T` to
    obtain a single CFC factor.
4.  Use `realCFC_norm_le` + Cauchy–Schwarz with the sup analysis. -/
theorem weak_bias (sc : SpectralSourceCondition S β)
    {lambda : ℝ} (lambda_pos : 0 < lambda) :
    haveI := sc.Hbar_L2_hasProj
    ‖S.Tlin (S.tikhonovMinimiserL2 lambda - S.hL2 S.h₀_mem)‖ ^ 2
      ≤ sc.biasConst * ‖S.hL2 sc.w₀_mem‖ ^ 2 * lambda ^ (min (β + 1) 2) := by
  haveI := sc.Hbar_L2_hasProj
  by_cases hnt : Nontrivial (Lp ℝ 2 μ)
  swap
  · haveI : Subsingleton (Lp ℝ 2 μ) := not_nontrivial_iff_subsingleton.mp hnt
    have hdiff : S.Tlin (S.tikhonovMinimiserL2 lambda - S.hL2 S.h₀_mem) = 0 :=
      Subsingleton.elim _ _
    have hpow_nonneg : 0 ≤ lambda ^ (min (β + 1) 2) :=
      Real.rpow_nonneg (le_of_lt lambda_pos) _
    have hrhs_nonneg :
        0 ≤ sc.biasConst * ‖S.hL2 sc.w₀_mem‖ ^ 2 * lambda ^ (min (β + 1) 2) :=
      mul_nonneg (mul_nonneg sc.biasConst_nonneg (sq_nonneg _)) hpow_nonneg
    simpa [hdiff] using hrhs_nonneg
  haveI : Nontrivial (Lp ℝ 2 μ) := hnt
  haveI : NormOneClass (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) := ContinuousLinearMap.normOneClass
  set A := S.Tstar_T with hA_def
  set w := S.hL2 sc.w₀_mem with hw_def
  set B : ℝ := max 1 (‖A‖ + 1) with hB_def
  set f : ℝ → ℝ := fun x => -lambda * sourceSymbol β x / (lambda + max 0 x) with hf_def
  set q : ℝ → ℝ := fun x => x * f x with hq_def
  set g : ℝ → ℝ := fun x => x * f x ^ 2 with hg_def
  set c : ℝ := sc.biasConst * lambda ^ (min (β + 1) 2) with hc_def
  have hA_sa : IsSelfAdjoint A := by simpa [hA_def] using S.Tstar_T_isSelfAdjoint
  have hβ : 0 ≤ β := sc.beta_nonneg
  have hB_ge_one : 1 ≤ B := by
    rw [hB_def]
    exact le_max_left _ _
  have hB_pos : 0 < B := lt_of_lt_of_le zero_lt_one hB_ge_one
  have hden : ∀ x : ℝ, lambda + max 0 x ≠ 0 := fun x => by
    have hmax : (0 : ℝ) ≤ max 0 x := le_max_left _ _
    have hpos : 0 < lambda + max 0 x := by linarith
    exact ne_of_gt hpos
  let rSafe : ℝ → ℝ := fun x => x / (lambda + max 0 x)
  let prod : ℝ → ℝ := fun x => rSafe x * sourceSymbol β x
  have hr_cont : Continuous rSafe := by
    dsimp [rSafe]
    exact continuous_id.div (continuous_const.add (continuous_const.max continuous_id)) hden
  have hsrc_cont : Continuous (sourceSymbol β) := continuous_sourceSymbol hβ
  have hf_cont : Continuous f := by
    rw [hf_def]
    exact (continuous_const.mul hsrc_cont).div
      (continuous_const.add (continuous_const.max continuous_id)) hden
  have hq_cont : Continuous q := by
    rw [hq_def]
    exact continuous_id.mul hf_cont
  have hg_cont : Continuous g := by
    rw [hg_def]
    exact continuous_id.mul (hf_cont.pow 2)
  have hsource_eq : (fun x : ℝ => Real.rpow (max x 0) (β / 2)) = sourceSymbol β := rfl
  have hres_safe : Complexification.realCFC A (fun x => x / (lambda + x)) =
      Complexification.realCFC A rSafe := by
    apply realCFC_congr_on_spectrum_local A
    · intro x hx
      have hx0 : 0 ≤ x := sc.Tstar_T_spectrum_nonneg x (by simpa [hA_def] using hx)
      dsimp [rSafe]
      rw [max_eq_right hx0]
    · exact hA_sa
  have hmul : Complexification.realCFC A prod =
      (Complexification.realCFC A rSafe).comp
        (Complexification.realCFC A (sourceSymbol β)) := by
    dsimp [prod]
    exact Complexification.realCFC_mul A hA_sa rSafe (sourceSymbol β) hr_cont hsrc_cont
  have hsub_cfc : Complexification.realCFC A (fun x => prod x - sourceSymbol β x) =
      Complexification.realCFC A prod - Complexification.realCFC A (sourceSymbol β) :=
    realCFC_sub_local A hA_sa prod (sourceSymbol β) (hr_cont.mul hsrc_cont) hsrc_cont
  have hsymbol : Complexification.realCFC A (fun x => prod x - sourceSymbol β x) =
      Complexification.realCFC A f := by
    rw [hf_def]
    apply realCFC_congr_on_spectrum_local A
    · intro x hx
      have hx0 : 0 ≤ x := sc.Tstar_T_spectrum_nonneg x (by simpa [hA_def] using hx)
      have hne : lambda + max 0 x ≠ 0 := hden x
      dsimp [prod, rSafe]
      rw [max_eq_right hx0]
      field_simp [hne]
      ring
    · exact hA_sa
  have hresid :
      S.tikhonovMinimiserL2 lambda - S.hL2 S.h₀_mem =
        Complexification.realCFC A f w := by
    calc
      S.tikhonovMinimiserL2 lambda - S.hL2 S.h₀_mem
          = (Complexification.realCFC A rSafe)
              ((Complexification.realCFC A (sourceSymbol β)) w) -
            (Complexification.realCFC A (sourceSymbol β)) w := by
          rw [tikhonovMinimiserL2_eq_resolvent (S := S) (β := β) sc lambda_pos]
          rw [sc.spectral_identity]
          rw [hsource_eq]
          rw [hres_safe]
      _ = ((Complexification.realCFC A rSafe).comp
            (Complexification.realCFC A (sourceSymbol β))) w -
            (Complexification.realCFC A (sourceSymbol β)) w := by rfl
      _ = (Complexification.realCFC A prod -
            Complexification.realCFC A (sourceSymbol β)) w := by
          rw [← hmul]
          simp only [ContinuousLinearMap.sub_apply]
      _ = Complexification.realCFC A (fun x => prod x - sourceSymbol β x) w := by
          rw [hsub_cfc]
      _ = Complexification.realCFC A f w := by rw [hsymbol]
  have hAcomp : A.comp (Complexification.realCFC A f) =
      Complexification.realCFC A q := by
    rw [hq_def]
    rw [show (fun x : ℝ => x * f x) = fun x : ℝ => id x * f x by rfl]
    rw [Complexification.realCFC_mul A hA_sa id f continuous_id hf_cont]
    apply ContinuousLinearMap.ext
    intro v
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
    rw [Complexification.realCFC_id A hA_sa (Complexification.realCFC A f v)]
  have hfg_comp : (Complexification.realCFC A f).comp (Complexification.realCFC A q) =
      Complexification.realCFC A g := by
    rw [← Complexification.realCFC_mul A hA_sa f q hf_cont hq_cont]
    rw [hg_def, hq_def]
    congr 1
    funext x
    ring
  have hTu_sq :
      ‖S.Tlin (S.tikhonovMinimiserL2 lambda - S.hL2 S.h₀_mem)‖ ^ 2 =
        inner ℝ (Complexification.realCFC A g w) w := by
    rw [hresid]
    have hTstar :
        ‖S.Tlin (Complexification.realCFC A f w)‖ ^ 2 =
          inner ℝ (A (Complexification.realCFC A f w))
            (Complexification.realCFC A f w) := by
      rw [← real_inner_self_eq_norm_sq]
      subst A
      change inner ℝ (S.Tlin (Complexification.realCFC S.Tstar_T f w))
          (S.Tlin (Complexification.realCFC S.Tstar_T f w)) =
        inner ℝ (S.Tadjoint (S.Tlin (Complexification.realCFC S.Tstar_T f w)))
          (Complexification.realCFC S.Tstar_T f w)
      rw [OperatorSystem.Tadjoint, ContinuousLinearMap.adjoint_inner_left]
    rw [hTstar]
    have hAu : A (Complexification.realCFC A f w) =
        Complexification.realCFC A q w := by
      change (A.comp (Complexification.realCFC A f)) w =
        Complexification.realCFC A q w
      rw [hAcomp]
    rw [hAu]
    have hf_sa : IsSelfAdjoint (Complexification.realCFC A f) :=
      Complexification.realCFC_isSelfAdjoint A hA_sa f hf_cont
    calc
      inner ℝ (Complexification.realCFC A q w) (Complexification.realCFC A f w)
          = inner ℝ ((Complexification.realCFC A f) (Complexification.realCFC A q w)) w := by
            exact ((ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hf_sa)
              (Complexification.realCFC A q w) w).symm
      _ = inner ℝ (((Complexification.realCFC A f).comp
            (Complexification.realCFC A q)) w) w := by rfl
      _ = inner ℝ (Complexification.realCFC A g w) w := by rw [hfg_comp]
  have hsup : ∀ x ∈ spectrum ℝ A, |g x| ≤ c := by
    intro x hx
    have hx0 : 0 ≤ x := sc.Tstar_T_spectrum_nonneg x (by simpa [hA_def] using hx)
    have hxnorm : ‖x‖ ≤ ‖A‖ := spectrum.norm_le_norm_of_mem hx
    have hx_le_norm : x ≤ ‖A‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg hx0] at hxnorm
      exact hxnorm
    have hnorm_le_B : ‖A‖ ≤ B := by
      calc
        ‖A‖ ≤ ‖A‖ + 1 := by linarith [norm_nonneg A]
        _ ≤ max 1 (‖A‖ + 1) := le_max_right _ _
        _ = B := by rw [hB_def]
    have hxB : x ≤ B := le_trans hx_le_norm hnorm_le_B
    rw [hc_def, hg_def, hf_def]
    have hbound := weak_residual_bound lambda_pos hx0 hxB hβ hB_ge_one
    rw [biasConst]
    simpa [hA_def, hB_def] using hbound
  have hc_nonneg : 0 ≤ c := by
    rw [hc_def]
    exact mul_nonneg sc.biasConst_nonneg (Real.rpow_nonneg (le_of_lt lambda_pos) _)
  have hnorm :=
    Complexification.realCFC_norm_le A hA_sa g hg_cont c hc_nonneg hsup w
  have hcs : inner ℝ (Complexification.realCFC A g w) w ≤ c * ‖w‖ ^ 2 := by
    have hineq : |inner ℝ (Complexification.realCFC A g w) w| ≤
        ‖Complexification.realCFC A g w‖ * ‖w‖ :=
      abs_real_inner_le_norm _ _
    calc
      inner ℝ (Complexification.realCFC A g w) w
          ≤ |inner ℝ (Complexification.realCFC A g w) w| := le_abs_self _
      _ ≤ ‖Complexification.realCFC A g w‖ * ‖w‖ := hineq
      _ ≤ (c * ‖w‖) * ‖w‖ := by
        exact mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
      _ = c * ‖w‖ ^ 2 := by ring
  calc
    ‖S.Tlin (S.tikhonovMinimiserL2 lambda - S.hL2 S.h₀_mem)‖ ^ 2
        = inner ℝ (Complexification.realCFC A g w) w := hTu_sq
    _ ≤ c * ‖w‖ ^ 2 := hcs
    _ = sc.biasConst * ‖S.hL2 sc.w₀_mem‖ ^ 2 * lambda ^ (min (β + 1) 2) := by
      rw [hc_def, hw_def]
      ring

end SpectralSourceCondition

/-- Function-level pullback datum for the discharge.  The user provides
a `Hbar`-element `h_lambda_star_fun` whose L² class equals the
Lax–Milgram minimiser `tikhonovMinimiserL2 S λ` constructed in
`Operator/Tikhonov.lean`.  This single pullback is the only
function-level commitment needed: the bias and convexity inequalities
all live at the L² level and transport along this equation. -/
structure TikhonovPullback
    (S : OperatorSystem Ω μ) (β lambda : ℝ)
    (sc : SpectralSourceCondition S β) where
  /-- Function-level minimiser. -/
  h_lambda_star_fun : S.𝒳 → ℝ
  /-- The function-level minimiser lies in `Hbar`. -/
  h_lambda_star_mem : h_lambda_star_fun ∈ S.Hbar
  /-- Coherence: lifting `h_lambda_star_fun` to `Lp ℝ 2 μ` recovers the
  Lax–Milgram L² minimiser. -/
  h_lambda_star_pullback :
    haveI := sc.Hbar_L2_hasProj
    S.hL2 h_lambda_star_mem = S.tikhonovMinimiserL2 lambda

/-- **Discharge of the Tikhonov bias bound from the spectral source
condition.**

Given a `SpectralSourceCondition` and a `TikhonovPullback` to the
function-level minimiser, packages the spectral `strong_bias` and
`weak_bias` theorems plus `tikhonovMinimiserL2_strong_convexity` into
a full `TikhonovBiasBound`.

The packaged constant is `C := sc.biasConst · ‖w₀‖_{L²}`, so the
`TikhonovBiasBound` statement `LHS² ≤ C · ‖w₀‖ · λ^…` follows from the
spectral statement `LHS² ≤ biasConst · ‖w₀‖² · λ^…`. -/
noncomputable def tikhonov_bias_from_spectral
    (S : OperatorSystem Ω μ) (β : ℝ) (lambda : ℝ)
    (lambda_pos : 0 < lambda)
    (sc : SpectralSourceCondition S β)
    (pb : TikhonovPullback S β lambda sc) :
    TikhonovBiasBound S β lambda sc.toSourceCondition := by
  haveI := sc.Hbar_L2_hasProj
  refine
    { lambda_pos := lambda_pos
      h_lambda_star_fun := pb.h_lambda_star_fun
      h_lambda_star_mem := pb.h_lambda_star_mem
      C := sc.biasConst * ‖S.hL2 sc.w₀_mem‖
      C_nonneg := mul_nonneg sc.biasConst_nonneg (norm_nonneg _)
      strong_bias := ?_
      weak_bias := ?_
      strong_convexity := ?_ }
  · have hb := sc.strong_bias lambda_pos
    have hpull := pb.h_lambda_star_pullback
    have hC :
        sc.biasConst * ‖S.hL2 sc.w₀_mem‖ ^ 2 * lambda ^ (min β 2)
          = sc.biasConst * ‖S.hL2 sc.w₀_mem‖ * S.strongNorm (S.hL2 sc.w₀_mem)
              * lambda ^ (min β 2) := by
      rw [OperatorSystem.strongNorm, sq]
      ring
    simpa [OperatorSystem.strongNorm, hpull, hC] using hb
  · have hb := sc.weak_bias lambda_pos
    have hpull := pb.h_lambda_star_pullback
    have hC :
        sc.biasConst * ‖S.hL2 sc.w₀_mem‖ ^ 2 * lambda ^ (min (β + 1) 2)
          = sc.biasConst * ‖S.hL2 sc.w₀_mem‖ * S.strongNorm (S.hL2 sc.w₀_mem)
              * lambda ^ (min (β + 1) 2) := by
      rw [OperatorSystem.strongNorm, sq]
      ring
    simpa [OperatorSystem.weakNorm, OperatorSystem.strongNorm,
      OperatorSystem.Tlin_apply, hpull, hC] using hb
  · intro h hh
    have hconv :=
      S.tikhonovMinimiserL2_strong_convexity (lambda_pos := lambda_pos)
        (h := S.hL2 hh) (hh := S.hbar_mem_L2 h hh)
    simpa [OperatorSystem.strongNorm, OperatorSystem.weakNorm,
      OperatorSystem.Tlin_apply, pb.h_lambda_star_pullback]
      using hconv

end NPIV
end Estimation
end Causalean
