/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Liu–Hudgens (2014): consistency of the direct-effect contrast estimator

Along a sequence of two-stage Hudgens–Halloran experiments (`LHExperiment`) in which the number of
groups grows, the Horvitz-Thompson estimator converges in probability to the population average
treatment-minus-control direct-effect contrast.  The argument is the
lightweight finite Chebyshev inequality applied to the two-stage variance: the estimator is
unbiased (so the estimand equals its expectation), Chebyshev bounds the deviation probability by
`directVar / ε²`, and the standard large-sample regularity condition `hVar0` — that the design
variance vanishes as the number of groups → ∞ — drives that bound to `0`.  We take `hVar0` as a
hypothesis here; it follows from bounded outcomes together with `C → ∞` (the number of ψ-selected
groups growing without bound), but the consistency statement only needs the variance to vanish.
-/

import Causalean.Experimentation.TwoStageInterference.Asymptotic.Setup
import Causalean.Experimentation.DesignBased.Chebyshev
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Direct-contrast consistency

The two-stage estimator of the treatment-minus-control direct-effect contrast is consistent when
its design variance vanishes.

This file proves Chebyshev consistency for the Liu-Hudgens direct-contrast estimator along a
sequence of two-stage experiments.
-/

open scoped BigOperators Topology
open Filter

namespace Causalean
namespace Experimentation
namespace TwoStageInterference

open DesignBased

/-- **Consistency of the direct-effect contrast estimator (Liu–Hudgens 2014).** Along a sequence of
two-stage experiments whose closed-form design variance `directVar` vanishes (`hVar0`), the
Horvitz-Thompson estimator is consistent for the population average treatment-minus-control
direct-effect contrast: for every `ε > 0`, `Pr[|estimator − estimand| ≥ ε] → 0`.  Proof: rewrite
the estimand as the estimator's expectation (unbiasedness, `E_estD`), bound the deviation
probability by `directVar / ε²` (Chebyshev + `var_estD`), and squeeze to `0` using `hVar0`. -/
theorem estDirect_consistent (Exp : ℕ → LHExperiment)
    (hVar0 : Tendsto (fun n => (Exp n).directVar) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => (Exp n).jointD.Pr (fun sw => ε ≤ |(Exp n).estD sw - (Exp n).DEbar|))
      atTop (𝓝 0) := by
  refine squeeze_zero (g := fun n => (Exp n).directVar / ε ^ 2)
      (fun n => ?_) (fun n => ?_) ?_
  · -- `0 ≤ Pr_n`: a probability is nonnegative.
    exact (Exp n).jointD.Pr_nonneg _
  · -- `Pr_n ≤ directVar_n / ε²` by Chebyshev, recentering via unbiasedness.
    have hcenter : (Exp n).DEbar = (Exp n).jointD.E (Exp n).estD := ((Exp n).E_estD).symm
    change (Exp n).jointD.Pr (fun sw => ε ≤ |(Exp n).estD sw - (Exp n).DEbar|)
        ≤ (Exp n).directVar / ε ^ 2
    rw [hcenter, ← (Exp n).var_estD]
    exact (Exp n).jointD.chebyshev (Exp n).estD hε
  · -- `directVar_n / ε² → 0 / ε² = 0`.
    simpa using hVar0.div_const (ε ^ 2)

end TwoStageInterference
end Experimentation
end Causalean
