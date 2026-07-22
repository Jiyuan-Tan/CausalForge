/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import CausalSmith.Experimentation.EXP_SaturationSkewThreshold_Research.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

namespace CausalSmith.Experimentation.SaturationSkew

open MeasureTheory
open scoped BigOperators

-- @node: lem:finite-atomic-grid-split-rounding
/-- Finite atomic grid-split rounding: running `gridSplitRounding` on the atomic data
of a `K ≤ 3`-atom admissible law `ν = ∑_ℓ w_ℓ δ_{u_ℓ}` produces the implementable
vector `πrd = gridSplitRounding M m pbar w u` together with a transport coupling of
`ν` and `L_M(πrd)` whose cost is `≤ 2K/M + 2/m`. The conclusion is now bound to the
`def:grid-split-rounding` construction (its `πrd` is literally that handle) and to
the explicit atomic representation of `ν`. -/
lemma finite_atomic_grid_split_rounding (M m : ℕ) (pbar : ℝ)
    (hp0 : 0 ≤ pbar) (hp1 : pbar ≤ 1) {K : ℕ} (hK : K ≤ 3)
    (w u : Fin K → ℝ) (ν : Law)
    (hνeq : (ν : Measure ℝ) = ∑ ℓ, ENNReal.ofReal (w ℓ) • Measure.dirac (u ℓ))
    (hν : IsAdmissible pbar ν) (hM : 0 < M) (hm : 0 < m)
    (hNp : ∃ z : ℤ, ((M * m : ℕ) : ℝ) * pbar = z) :
    ∃ γ : ProbabilityMeasure (ℝ × ℝ),
      IsImplementable M m pbar (gridSplitRounding M m pbar w u) ∧
      (γ : Measure (ℝ × ℝ)).map Prod.fst = (ν : Measure ℝ) ∧
      (γ : Measure (ℝ × ℝ)).map Prod.snd
          = (empiricalLaw M (gridSplitRounding M m pbar w u) : Measure ℝ) ∧
      ∫ p, |p.1 - p.2| ∂(γ : Measure (ℝ × ℝ)) ≤ 2 * (K : ℝ) / M + 2 / m := by sorry

-- @node: lem:quartic-variance-coupling-lipschitz
/-- Quartic variance coupling Lipschitz bound: the variance functional is Lipschitz
in transport distance with the explicit moment-degree constant. -/
lemma quartic_variance_coupling_lipschitz (V0 V1 V3 V4 pbar Δ : ℝ)
    (hp0 : 0 ≤ pbar) (hp1 : pbar ≤ 1) (η ν : Law)
    (hη : SupportedOn01 η) (hν : SupportedOn01 ν) (γ : ProbabilityMeasure (ℝ × ℝ))
    (hfst : (γ : Measure (ℝ × ℝ)).map Prod.fst = (η : Measure ℝ))
    (hsnd : (γ : Measure (ℝ × ℝ)).map Prod.snd = (ν : Measure ℝ))
    (hcost : ∫ p, |p.1 - p.2| ∂(γ : Measure (ℝ × ℝ)) ≤ Δ) :
    |varianceFunctional V0 V1 V3 V4 pbar η - varianceFunctional V0 V1 V3 V4 pbar ν|
      ≤ (2 * |V1| + 3 * |V3| + 8 * |V4|) * Δ := by sorry

end CausalSmith.Experimentation.SaturationSkew
