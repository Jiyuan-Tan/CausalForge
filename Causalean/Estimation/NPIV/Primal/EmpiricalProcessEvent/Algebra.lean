/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Stat.Concentration.UniformDeviation.UniformDeviationLocalized
import Causalean.Stat.Concentration.Rademacher.StarHull
import Causalean.Stat.Concentration.UniformDeviation.CriticalRadius
import Causalean.Stat.Sample.PiTransport

/-!
Collects deterministic algebra for the NPIV empirical-process master event.
The lemmas turn localized deviation inequalities and regularizer bounds into
the additive envelopes used by the primal rate proof.
-/

namespace Causalean
namespace Estimation
namespace NPIV
namespace Primal

open MeasureTheory Causalean.Stat Causalean.Stat.Concentration

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## Deterministic Young / AM-GM envelope lemma

The lemma below is the deterministic real-analysis step bridging the raw
additive Foster-style deviation bound

    δ · ‖integrand‖_{L²}  +  b · √(log(1/ζ)/n)

(which `localized_uniform_deviation` produces; see
`Causalean/Stat/Concentration/UniformDeviationLocalized.lean`) to the
quadratic envelope shape

    R² + δ · w + δ²

appearing on the RHS of `ep_inequality_from_localized` and of the proof
sketch (`trae_inverse_problems.tex` line 308).  The bridge is two
applications of Young's inequality (`x · y ≤ (x² + y²)/2`) on the cross
terms `δ · R` and `R · κ`, where:

* `R := R_b = ‖T(h*_λ - h_0)‖`  (population weak-norm bias);
* `δ := δ_n`                     (localized rate);
* `w := ‖T(ĥ_n - h*_λ)‖`        (weak-norm gap, *unknown* random scalar);
* `κ`                            (the residual `b · √(log(1/ζ)/n)` McDiarmid term).

Once the EP step produces `δ·(R + w + δ) + R·κ` (via Foster's loss-norm
bound `‖loss(h, f) − loss(h*_λ, f)‖_{L²} ≲ R + w + δ` for `f ∈ F`), the
envelope below absorbs the bilinear `δ·R` and `R·κ` cross terms into
quadratic factors `R²` and `κ²`, leaving only the *honest* dependence on
the unknown `w` as the cross term `δ · w` — which is exactly what gets
absorbed downstream via AM-GM `δ · w ≤ ½ w² + ½ δ²`.
-/

/-- **Young / AM-GM cross-term envelope.**  For any nonneg
`R, δ, w, κ`,

    δ · (R + w + δ) + R · κ
      ≤ R² + δ · w + (3/2) · δ² + (1/2) · κ².

Two applications of Young's inequality on `δ · R` and `R · κ`.  The
remaining `δ · w` term is *not* squared here because `w` is the random
weak-norm gap that gets absorbed downstream (see proof sketch line 365). -/
lemma young_cross_envelope (R δ w κ : ℝ)
    (_hR : 0 ≤ R) (_hδ : 0 ≤ δ) (_hw : 0 ≤ w) (_hκ : 0 ≤ κ) :
    δ * (R + w + δ) + R * κ
      ≤ R ^ 2 + δ * w + (3 / 2) * δ ^ 2 + (1 / 2) * κ ^ 2 := by
  nlinarith [sq_nonneg (R - δ), sq_nonneg (R - κ)]


end Primal
end NPIV
end Estimation
end Causalean
