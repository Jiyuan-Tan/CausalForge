/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Population Tikhonov minimiser via Lax–Milgram

Hilbert-space construction of the population Tikhonov minimiser and the
strong-convexity inequality used by the NPIV primal rate proof.  These facts
are deliberately separated from the spectral source-condition argument: this
file only uses Lax–Milgram on the closed candidate subspace `Hbar_L2`, while
`Operator/SpectralCalculus.lean` supplies the later resolvent and bias bounds.

## Outputs

For an `OperatorSystem Ω μ` with a closed primal candidate subspace
`Hbar_L2` (witnessed by `HasOrthogonalProjection`):

* `OperatorSystem.tikhonovBilin S λ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ →L[ℝ] ℝ` —
  the bilinear form `(u, v) ↦ ⟨T u, T v⟩ + λ ⟨u, v⟩`.
* `OperatorSystem.tikhonovBilin_isCoercive` (for `0 < λ`) — the bilinear
  form, restricted to the closed subspace `Hbar_L2`, is coercive with
  constant `λ`.
* `OperatorSystem.tikhonovMinimiserL2 S λ : Lp ℝ 2 μ` — the L²-level
  Tikhonov minimiser, defined for `0 < λ` via Lax–Milgram on `Hbar_L2`,
  with arbitrary value (`0`) for `λ ≤ 0`.
* `OperatorSystem.tikhonovMinimiserL2_mem` — `tikhonovMinimiserL2 S λ`
  lies in `Hbar_L2`.
* `OperatorSystem.tikhonovMinimiserL2_optimality` — the variational
  identity `⟨T h*, T v⟩ + λ ⟨h*, v⟩ = ⟨T h₀, T v⟩` for all `v ∈ Hbar_L2`.
* `OperatorSystem.tikhonovMinimiserL2_strong_convexity` — the population
  strong-convexity inequality at the minimiser:

      λ ‖ĥ − h*‖² + ‖T(ĥ − h*)‖²
        ≤ ‖T(ĥ − h₀)‖² − ‖T(h* − h₀)‖² + λ(‖ĥ‖² − ‖h*‖²)

  for every `ĥ ∈ Hbar_L2` (`SourceCondition.lean` strong-convexity, lifted
  to the L² level so it does not need a function-level pullback).

The proof of strong convexity is the second-order Taylor identity at the
minimiser; the first-order term vanishes by `tikhonovMinimiserL2_optimality`.

Together these declarations provide the L² minimiser, its variational
identity, and the strong-convexity bound consumed by the spectral discharge in
`Operator/SpectralCalculus.lean`.
-/

import Causalean.Estimation.NPIV.Operator.Adjoint
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
Develops the Hilbert-space Tikhonov interface for NPIV inverse problems.
The module defines `OperatorSystem.tikhonovBilin`,
`OperatorSystem.tikhonovTargetSub`, and
`OperatorSystem.tikhonovMinimiserL2`; proves coercivity and the minimizer's
variational identity; and exposes
`OperatorSystem.tikhonovMinimiserL2_strong_convexity`, the L²-level population
strong-convexity inequality used by the primal rate theorem.
-/

namespace Causalean
namespace Estimation
namespace NPIV

namespace OperatorSystem

open MeasureTheory ContinuousLinearMap

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## The Tikhonov bilinear form on the ambient space -/

/-- The **Tikhonov bilinear form** on the ambient `Lp ℝ 2 μ`:

    `tikhonovBilin λ u v := ⟪T u, T v⟫_{L²(μ)} + λ · ⟪u, v⟫_{L²(μ)}`.

Symmetric (since `T*T` is self-adjoint) and bounded.  When restricted to
the closed subspace `S.Hbar_L2` and `0 < λ`, it is coercive with constant
`λ` (since `λ ‖u‖² ≤ ⟪T u, T u⟫ + λ ‖u‖² = bilin u u`); this is the
content of `tikhonovBilin_isCoercive` below. -/
noncomputable def tikhonovBilin (S : OperatorSystem Ω μ) (lambda : ℝ) :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ →L[ℝ] ℝ :=
  (((innerSL ℝ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ →L[ℝ] ℝ).comp S.Tlin).flip.comp S.Tlin).flip
    + lambda • (innerSL ℝ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ →L[ℝ] ℝ)

/-- Pointwise formula for `tikhonovBilin`. -/
lemma tikhonovBilin_apply (S : OperatorSystem Ω μ) (lambda : ℝ)
    (u v : Lp ℝ 2 μ) :
    S.tikhonovBilin lambda u v
      = inner ℝ (S.Tlin u) (S.Tlin v) + lambda * inner ℝ u v := by
  change (((((innerSL ℝ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ →L[ℝ] ℝ).comp S.Tlin).flip.comp
      S.Tlin).flip + lambda • (innerSL ℝ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ →L[ℝ] ℝ)) u v)
    = inner ℝ (S.Tlin u) (S.Tlin v) + lambda * inner ℝ u v
  simp [coe_innerSL_apply]

/-- Symmetry of `tikhonovBilin`. -/
lemma tikhonovBilin_symm (S : OperatorSystem Ω μ) (lambda : ℝ)
    (u v : Lp ℝ 2 μ) :
    S.tikhonovBilin lambda u v = S.tikhonovBilin lambda v u := by
  simp [tikhonovBilin_apply, real_inner_comm]

/-- The bilinear form, as a bilinear form **on the closed subspace**
`Hbar_L2`.  We pre/post-compose `tikhonovBilin` with the subtype inclusion
`Hbar_L2 →L[ℝ] Lp ℝ 2 μ` so the result lives on the Hilbert space
`Hbar_L2` itself.  This is the form fed into Lax–Milgram. -/
noncomputable def tikhonovBilinSub (S : OperatorSystem Ω μ) (lambda : ℝ) :
    S.Hbar_L2 →L[ℝ] S.Hbar_L2 →L[ℝ] ℝ :=
  (((S.tikhonovBilin lambda).comp S.Hbar_L2.subtypeL).flip.comp S.Hbar_L2.subtypeL).flip

/-- Pointwise formula for the restricted bilinear form. -/
lemma tikhonovBilinSub_apply (S : OperatorSystem Ω μ) (lambda : ℝ)
    (u v : S.Hbar_L2) :
    S.tikhonovBilinSub lambda u v
      = S.tikhonovBilin lambda (u : Lp ℝ 2 μ) (v : Lp ℝ 2 μ) := by
  rfl

/-- **Coercivity** of `tikhonovBilinSub` for `0 < λ`.  Witness constant:
`λ`.  Proof: `bilin u u = ‖T u‖² + λ ‖u‖² ≥ λ ‖u‖²` since `‖T u‖² ≥ 0`. -/
lemma tikhonovBilinSub_isCoercive
    (S : OperatorSystem Ω μ) [S.Hbar_L2.HasOrthogonalProjection]
    {lambda : ℝ} (lambda_pos : 0 < lambda) :
    IsCoercive (S.tikhonovBilinSub lambda) := by
  refine ⟨lambda, lambda_pos, ?_⟩
  intro u
  change lambda * ‖u‖ * ‖u‖ ≤ S.tikhonovBilin lambda (u : Lp ℝ 2 μ) (u : Lp ℝ 2 μ)
  rw [tikhonovBilin_apply]
  simp
  nlinarith [sq_nonneg (‖S.Tlin (u : Lp ℝ 2 μ)‖)]

/-! ## The Tikhonov target functional -/

/-- The **Tikhonov target functional** evaluated on the closed subspace
`Hbar_L2`:

    `tikhonovTargetSub v := ⟪T h₀, T v⟫_{L²(μ)}`

(equivalently `⟪T*T h₀, v⟫`, used in the variational identity for the
minimiser). -/
noncomputable def tikhonovTargetSub (S : OperatorSystem Ω μ) :
    S.Hbar_L2 →L[ℝ] ℝ :=
  ((innerSL ℝ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ →L[ℝ] ℝ) (S.Tlin (S.hL2 S.h₀_mem))).comp
    (S.Tlin.comp S.Hbar_L2.subtypeL)

/-- Pointwise formula for the target functional. -/
lemma tikhonovTargetSub_apply (S : OperatorSystem Ω μ) (v : S.Hbar_L2) :
    S.tikhonovTargetSub v
      = inner ℝ (S.Tlin (S.hL2 S.h₀_mem)) (S.Tlin (v : Lp ℝ 2 μ)) := by
  simp [tikhonovTargetSub, coe_innerSL_apply]

private lemma hbarL2_completeSpace
    (S : OperatorSystem Ω μ) [S.Hbar_L2.HasOrthogonalProjection] :
    CompleteSpace S.Hbar_L2 := by
  rw [← Submodule.range_starProjection S.Hbar_L2]
  exact (Submodule.isIdempotentElem_starProjection S.Hbar_L2).isClosed_range.completeSpace_coe

/-! ## The L²-level Tikhonov minimiser via Lax–Milgram -/

/-- The **population Tikhonov minimiser** at level `λ` (L² level).

For `0 < λ`, defined as the unique `h*_λ ∈ Hbar_L2` such that

    `tikhonovBilin λ h*_λ v = ⟪T h₀, T v⟫_{L²(μ)}`

for all `v ∈ Hbar_L2`, obtained from Mathlib's `IsCoercive.continuousLinearEquivOfBilin`
applied to `tikhonovBilinSub_isCoercive`.  For `λ ≤ 0` this returns `0` —
the optimality and pullback theorems below assume `0 < λ`. -/
noncomputable def tikhonovMinimiserL2
    (S : OperatorSystem Ω μ) [S.Hbar_L2.HasOrthogonalProjection]
    (lambda : ℝ) : Lp ℝ 2 μ :=
  let complete : CompleteSpace S.Hbar_L2 := hbarL2_completeSpace S
  if h : 0 < lambda then
    let coercive := tikhonovBilinSub_isCoercive S h
    let Bsharp :=
      @IsCoercive.continuousLinearEquivOfBilin S.Hbar_L2 _ _ complete
        (S.tikhonovBilinSub lambda) coercive
    let w : S.Hbar_L2 :=
      (@InnerProductSpace.toDual ℝ S.Hbar_L2 _ _ _ complete).symm (S.tikhonovTargetSub)
    ↑(Bsharp.symm w : S.Hbar_L2)
  else
    0

/-- The minimiser lies in `Hbar_L2`. -/
lemma tikhonovMinimiserL2_mem
    (S : OperatorSystem Ω μ) [S.Hbar_L2.HasOrthogonalProjection]
    (lambda : ℝ) :
    S.tikhonovMinimiserL2 lambda ∈ S.Hbar_L2 := by
  by_cases h : 0 < lambda
  · simp [tikhonovMinimiserL2, h]
  · simp [tikhonovMinimiserL2, h]

/-- **Variational identity** for the Tikhonov minimiser at `0 < λ`:

    `⟪T h*_λ, T v⟫ + λ · ⟪h*_λ, v⟫ = ⟪T h₀, T v⟫`

for every `v ∈ Hbar_L2`.  Direct restatement of the Lax–Milgram identity
`tikhonovBilin h*_λ v = tikhonovTarget v`. -/
lemma tikhonovMinimiserL2_optimality
    (S : OperatorSystem Ω μ) [S.Hbar_L2.HasOrthogonalProjection]
    {lambda : ℝ} (lambda_pos : 0 < lambda)
    {v : Lp ℝ 2 μ} (hv : v ∈ S.Hbar_L2) :
    inner ℝ (S.Tlin (S.tikhonovMinimiserL2 lambda)) (S.Tlin v)
        + lambda * inner ℝ (S.tikhonovMinimiserL2 lambda) v
      = inner ℝ (S.Tlin (S.hL2 S.h₀_mem)) (S.Tlin v) := by
  let complete : CompleteSpace S.Hbar_L2 := hbarL2_completeSpace S
  let coercive := tikhonovBilinSub_isCoercive S lambda_pos
  let Bsharp :=
    @IsCoercive.continuousLinearEquivOfBilin S.Hbar_L2 _ _ complete
      (S.tikhonovBilinSub lambda) coercive
  let w : S.Hbar_L2 :=
    (@InnerProductSpace.toDual ℝ S.Hbar_L2 _ _ _ complete).symm (S.tikhonovTargetSub)
  let ustar : S.Hbar_L2 := Bsharp.symm w
  let vsub : S.Hbar_L2 := ⟨v, hv⟩
  have hmin : S.tikhonovMinimiserL2 lambda = (ustar : Lp ℝ 2 μ) := by
    simp [tikhonovMinimiserL2, lambda_pos, Bsharp, w, ustar]
  have hLM :=
    @IsCoercive.continuousLinearEquivOfBilin_apply S.Hbar_L2 _ _ complete
      (S.tikhonovBilinSub lambda) coercive ustar vsub
  have htarget : inner ℝ w vsub = S.tikhonovTargetSub vsub := by
    change inner ℝ ((@InnerProductSpace.toDual ℝ S.Hbar_L2 _ _ _ complete).symm
        S.tikhonovTargetSub) vsub = S.tikhonovTargetSub vsub
    exact @InnerProductSpace.toDual_symm_apply ℝ S.Hbar_L2 _ _ _ complete
      (x := vsub) (y := S.tikhonovTargetSub)
  have hvar : S.tikhonovBilinSub lambda ustar vsub = S.tikhonovTargetSub vsub := by
    calc
      S.tikhonovBilinSub lambda ustar vsub = inner ℝ (Bsharp ustar) vsub :=
        hLM.symm
      _ = inner ℝ w vsub := by simp [ustar]
      _ = S.tikhonovTargetSub vsub := htarget
  rw [hmin]
  simpa [vsub, tikhonovBilinSub_apply, tikhonovBilin_apply, tikhonovTargetSub_apply] using hvar

/-! ## Strong convexity at the minimiser -/

/-- **Population strong convexity at the Tikhonov minimiser** (L² level).

For every `ĥ ∈ Hbar_L2` and every `0 < λ`,

    λ ‖ĥ − h*‖² + ‖T(ĥ − h*)‖²
      ≤ ‖T(ĥ − h₀)‖² − ‖T(h* − h₀)‖² + λ (‖ĥ‖² − ‖h*‖²),

where `h* = tikhonovMinimiserL2 S λ`.

Proof sketch (Taylor at the minimiser).  Expand both sides:

    LHS = λ(‖ĥ‖² − 2⟨ĥ, h*⟩ + ‖h*‖²) + ‖Tĥ‖² − 2⟨Tĥ, Th*⟩ + ‖Th*‖²,
    RHS = ‖Tĥ‖² − 2⟨Tĥ, Th₀⟩ + ‖Th₀‖²
          − ‖Th*‖² + 2⟨Th*, Th₀⟩ − ‖Th₀‖²
          + λ‖ĥ‖² − λ‖h*‖²
        = ‖Tĥ‖² − 2⟨Tĥ, Th₀⟩ − ‖Th*‖² + 2⟨Th*, Th₀⟩ + λ‖ĥ‖² − λ‖h*‖².

`RHS − LHS = 2⟨Tĥ, Th*⟩ − 2⟨Tĥ, Th₀⟩ + 2⟨Th*, Th₀⟩ − 2‖Th*‖²
              + 2λ⟨ĥ, h*⟩ − 2λ‖h*‖²
            = 2 (⟨Tĥ, Th*⟩ − ⟨Tĥ, Th₀⟩ + λ⟨ĥ, h*⟩
                 − (⟨Th*, Th*⟩ − ⟨Th*, Th₀⟩ + λ⟨h*, h*⟩))`.

Both bracketed terms are `B(h*, ĥ) − ⟨T h₀, T ĥ⟩` (resp. with `h*` in
place of `ĥ`), which vanishes by `tikhonovMinimiserL2_optimality`.  So
`RHS − LHS = 0` (in fact equality holds — strong convexity is an
**equality** at the minimiser, not a strict inequality). -/
lemma tikhonovMinimiserL2_strong_convexity
    (S : OperatorSystem Ω μ) [S.Hbar_L2.HasOrthogonalProjection]
    {lambda : ℝ} (lambda_pos : 0 < lambda)
    {h : Lp ℝ 2 μ} (hh : h ∈ S.Hbar_L2) :
    lambda * ‖h - S.tikhonovMinimiserL2 lambda‖ ^ 2
        + ‖S.Tlin (h - S.tikhonovMinimiserL2 lambda)‖ ^ 2
      ≤ ‖S.Tlin (h - S.hL2 S.h₀_mem)‖ ^ 2
          - ‖S.Tlin (S.tikhonovMinimiserL2 lambda - S.hL2 S.h₀_mem)‖ ^ 2
          + lambda * (‖h‖ ^ 2 - ‖S.tikhonovMinimiserL2 lambda‖ ^ 2) := by
  let hstar := S.tikhonovMinimiserL2 lambda
  have hstar_mem : hstar ∈ S.Hbar_L2 := S.tikhonovMinimiserL2_mem lambda
  have hdiff : h - hstar ∈ S.Hbar_L2 := S.Hbar_L2.sub_mem hh hstar_mem
  have hopt := S.tikhonovMinimiserL2_optimality lambda_pos (v := h - hstar) hdiff
  apply le_of_eq
  simp [hstar, norm_sub_sq_real, ContinuousLinearMap.map_sub, inner_sub_right,
    real_inner_comm] at hopt ⊢
  nlinarith [hopt]

end OperatorSystem

end NPIV
end Estimation
end Causalean
