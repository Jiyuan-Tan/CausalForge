/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Local empirical-process modulus for an `LearningSystem`

`LocalEmpProcessModulus S S_iid split ρ δ g` packages the local
empirical-process modulus condition from
`def:est-osl-local-modulus`: with probability at least `1 - δ` (under the
ambient sample measure `μ`), the centred excess risk is bounded by
`ρ_n · ‖θ - θ₀‖ + ρ_n²` uniformly over `Θ_set`, for the realised
nuisance `g`.

This file only defines the predicate. Separate modulus modules discharge it
from empirical-process inputs such as bounded-loss Rademacher bounds and
localized critical-radius bounds, so downstream oracle inequalities can either
assume this condition directly or import a concrete bridge theorem.

See `doc/basic_concepts/po/estimation/orthogonal_statistical_learning.tex`,
`def:est-osl-local-modulus`.
-/

import Causalean.Estimation.OrthogonalLearning.PluginERM

/-! # Local Empirical-Process Modulus

This file states the local empirical-process modulus assumption used in
orthogonal statistical learning: with high probability, empirical excess risk
is uniformly close to population excess risk at a rate depending on the
distance to the population target. The predicate serves as the bridge from
empirical-process theory to oracle inequalities for plug-in estimators. -/

namespace Causalean
namespace Estimation
namespace OrthogonalLearning

open MeasureTheory ProbabilityTheory Filter Topology Causalean.Stat

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
         {Z : Type*} [MeasurableSpace Z] {P_Z : MeasureTheory.Measure Z}
         {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ]
         {G : Type*} [AddCommGroup G] [Module ℝ G]

/-- **Local empirical-process modulus** — the named high-probability
regularity condition on the empirical excess risk.

For each sample size `n`, there is an event `E n ⊆ Ω` of probability at
least `1 - δ` such that, on `E n`, the centred excess risk satisfies
the modulus inequality uniformly over `Θ_set`:

```
∀ θ ∈ Θ_set,
    [L θ g  -  L θ₀ g]   -   [L_emp θ g  -  L_emp θ₀ g]
        ≤  ρ n · ‖θ - θ₀‖ + (ρ n)^2
```

where `L_emp θ g := empRiskFoldB n ω θ g`.

This is a `Prop`-valued *named condition*, not a standing assumption of the
library.  Oracle inequalities (`OracleInequality.lean`) consume it, while the
`Rademacher` and `Localized` bridge theorems in this directory **discharge** it
from empirical-process inputs (bounded-loss Rademacher bounds, localized
critical-radius bounds).  The whole quantifier structure (event,
deterministic-`ρ`-and-`δ`, uniform-in-`θ`) is packaged as a single predicate so
those theorems can pass it around as one object; the event `E n` is
existentially quantified per `n` (a single deterministic event schedule). -/
def LocalEmpProcessModulus
    (S : LearningSystem Ω μ Z P_Z Θ G)
    (S_iid : IIDSample Ω Z μ P_Z)
    (split : OneShotSplit S_iid)
    (ρ : ℕ → ℝ) (δ : ℝ) (g : G) : Prop :=
  ∀ n : ℕ, ∃ E : Set Ω, MeasurableSet E ∧ μ E ≥ 1 - ENNReal.ofReal δ ∧
    ∀ ω ∈ E, ∀ θ ∈ S.Θ_set,
      (S.L θ g - S.L S.θ₀ g)
        - (empRiskFoldB S S_iid split n ω θ g
            - empRiskFoldB S S_iid split n ω S.θ₀ g)
        ≤ ρ n * ‖θ - S.θ₀‖ + (ρ n) ^ 2

end OrthogonalLearning
end Estimation
end Causalean
