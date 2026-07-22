/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# β-source condition and Tikhonov bias bound for the TRAE primal estimator

Defines the spectral and bias hypotheses used by the TRAE rate theorem of
`doc/basic_concepts/po/estimation/trae_inverse_problems.tex`.

* `SourceCondition S β` — the β-source condition at the primal nuisance
  `h₀` (`def:est-trae-source-condition`, line 47), with `β ≥ 0`.  Carries the witness
  `w₀ ∈ Hbar` and the spectral identity
      `(h₀)_{L²} = (T*T)^{β/2} (w₀)_{L²}`
  inside `Lp ℝ 2 μ`, where `(T*T)^{β/2}` is the real continuous functional
  calculus on the positive self-adjoint composite `T†T` built by
  complexification in `Operator/Complexification.lean`.  The symbol
  `x ↦ Real.rpow (max x 0) (β/2)` is continuous on all of ℝ and agrees
  with `x^{β/2}` on `[0, ∞) ⊇ spectrum ℝ (T†T)`.
* `TikhonovBiasBound S β λ sc` — the two Tikhonov bias bounds the rate
  theorem consumes for a positive regularization level `λ > 0`
  (proof sketch lines 276–285):

      ‖h*_λ − h₀‖²_{L²(P_X)} ≲ ‖w₀‖_{L²(P_X)} λ^{min(β, 2)},
      ‖T(h*_λ − h₀)‖²_{L²(P_Z)} ≲ ‖w₀‖_{L²(P_X)} λ^{min(β+1, 2)}.

  Packaged as a reusable certificate here; `Operator/SpectralCalculus.lean`
  discharges it from `SpectralSourceCondition` via the real-CFC built in
  `Operator/Complexification.lean`.
-/

import Causalean.Estimation.NPIV.Operator.Complexification
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Source Condition and Tikhonov Bias

This file records the β-source condition for the primal NPIV nuisance and the
Tikhonov bias bounds assumed by the primal rate theorem. The source condition
expresses the target nuisance as a spectral power of the normal operator
applied to an admissible witness, while the bias bundle stores the strong and
weak approximation inequalities later discharged by spectral calculus. -/

namespace Causalean
namespace Estimation
namespace NPIV

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The β-source condition represents the true primal nuisance as a
nonnegative spectral power of the normal NPIV operator applied to an
admissible witness in the primal candidate class.

This is the formal interface for the source condition at `h₀`
(`def:est-trae-source-condition`, line 47).

Carries a witness `w₀ ∈ Hbar` together with the spectral identity
`h₀ = (T*T)^{β/2} w₀` inside `Lp ℝ 2 μ`, where `(T*T)^{β/2}` is the
real continuous functional calculus on the self-adjoint composite
`OperatorSystem.Tstar_T` built by complexification in
`Operator/Complexification.lean`.

The continuous symbol used here is
`fun x => Real.rpow (max x 0) (β/2)`, which agrees with `x^{β/2}` on
`[0, ∞) ⊇ spectrum ℝ (T†T)` and is continuous on all of ℝ for `β ≥ 0`. -/
structure SourceCondition (S : OperatorSystem Ω μ) (β : ℝ) where
  /-- The source smoothness exponent is non-negative. -/
  beta_nonneg : 0 ≤ β
  /-- The pre-image of `h₀` under the spectral lift `(T*T)^{β/2}`. -/
  w₀_fun : S.𝒳 → ℝ
  /-- `w₀` lies in the primal candidate set `Hbar`. -/
  w₀_mem : w₀_fun ∈ S.Hbar
  /-- Spectral identity:
      `(h₀)_{L²} = (T†T)^{β/2} (w₀)_{L²}` inside `Lp ℝ 2 μ`. -/
  spectral_identity :
    S.hL2 S.h₀_mem
      = Complexification.realCFC S.Tstar_T
          (fun x : ℝ => Real.rpow (max x 0) (β/2))
          (S.hL2 w₀_mem)

/-- The Tikhonov bias-bound bundle records the population approximation
bounds at a positive regularization level and the strong-convexity inequality
for the corresponding population Tikhonov solution.

This is the Tikhonov bias bound at level `λ` (proof sketch lines 276–285 of
`doc/basic_concepts/po/estimation/trae_inverse_problems.tex`).

Witness: a population Tikhonov solution `h*_λ ∈ Hbar` together with the two
bias inequalities

    ‖h*_λ − h₀‖²_{L²(P_X)} ≤ C ‖w₀‖_{L²(P_X)} λ^{min(β, 2)},
    ‖T(h*_λ − h₀)‖²_{L²(P_Z)} ≤ C ‖w₀‖_{L²(P_X)} λ^{min(β+1, 2)}.

This is a reusable certificate carried alongside `SourceCondition`; spectral
calculus files discharge it from source conditions on `T*T`. -/
structure TikhonovBiasBound (S : OperatorSystem Ω μ) (β lambda : ℝ)
    (sc : SourceCondition S β) where
  /-- The Tikhonov regularization level is positive. -/
  lambda_pos : 0 < lambda
  /-- The population Tikhonov solution at level `λ`. -/
  h_lambda_star_fun : S.𝒳 → ℝ
  /-- `h*_λ` lies in the primal candidate set `Hbar`. -/
  h_lambda_star_mem : h_lambda_star_fun ∈ S.Hbar
  /-- Constant absorbing the proof's `≲`. -/
  C : ℝ
  /-- The constant is non-negative. -/
  C_nonneg : 0 ≤ C
  /-- Strong-metric Tikhonov bias bound:
      `‖h*_λ − h₀‖²_{L²(P_X)} ≤ C · ‖w₀‖_{L²(P_X)} · λ^{min(β, 2)}`. -/
  strong_bias :
    S.strongNorm (S.hL2 h_lambda_star_mem - S.hL2 S.h₀_mem) ^ 2
      ≤ C * S.strongNorm (S.hL2 sc.w₀_mem) * lambda ^ (min β 2)
  /-- Weak-metric Tikhonov bias bound:
      `‖T(h*_λ − h₀)‖²_{L²(P_Z)} ≤ C · ‖w₀‖_{L²(P_X)} · λ^{min(β+1, 2)}`. -/
  weak_bias :
    S.weakNorm (S.hL2 h_lambda_star_mem - S.hL2 S.h₀_mem) ^ 2
      ≤ C * S.strongNorm (S.hL2 sc.w₀_mem) * lambda ^ (min (β + 1) 2)
  /-- **Population strong convexity** at `h*_λ` (proof sketch lines 287–304
      of `doc/basic_concepts/po/estimation/trae_inverse_problems.tex`).

      For any candidate `ĥ ∈ Hbar`,

          λ‖ĥ − h*_λ‖²_{L²(P_X)} + ‖T(ĥ − h*_λ)‖²_{L²(P_Z)}
            ≤ ‖T(ĥ − h₀)‖²_{L²(P_Z)} − ‖T(h*_λ − h₀)‖²_{L²(P_Z)}
              + λ(‖ĥ‖²_{L²(P_X)} − ‖h*_λ‖²_{L²(P_X)}).

      Holds because `h*_λ` is the population minimizer of
      `F(h) := ‖T(h − h₀)‖² + λ‖h‖²` over the closed linear subspace
      `Hbar`, so the first-order term in the quadratic expansion
      vanishes. Spectral-calculus files discharge this inequality from the
      source condition and Tikhonov construction. -/
  strong_convexity :
    ∀ h, ∀ hh : h ∈ S.Hbar,
      lambda * (S.strongNorm (S.hL2 hh - S.hL2 h_lambda_star_mem)) ^ 2
          + (S.weakNorm (S.hL2 hh - S.hL2 h_lambda_star_mem)) ^ 2
        ≤ (S.weakNorm (S.hL2 hh - S.hL2 S.h₀_mem)) ^ 2
            - (S.weakNorm (S.hL2 h_lambda_star_mem - S.hL2 S.h₀_mem)) ^ 2
            + lambda * ((S.strongNorm (S.hL2 hh)) ^ 2
                          - (S.strongNorm (S.hL2 h_lambda_star_mem)) ^ 2)

end NPIV
end Estimation
end Causalean
