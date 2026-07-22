/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.ML.Core.Risk
import Mathlib.Order.Filter.Extr

/-! # Empirical-risk-minimizer predicates

Minimizer predicates for the ML spine, stated **candidate-wise** via Mathlib's
`IsMinOn` (or a comparison `+ ε` form), never via `sInf`/`argmin` — this avoids
pathological real-infimum defaults on empty or unbounded sets, matching the
existing `Estimation.OrthogonalLearning.PluginERM` idiom.

The file provides exact, approximate, and regularized parametric ERM predicates
(`IsERMP`, `IsApproxERMP`, `RegularizedERM`), plus extensional empirical and
population minimizer predicates (`IsERM`, `IsPopulationRiskMinimizer`) over a
`HypothesisClass`.  The parametric and extensional views are connected in
`Causalean.ML.Core.Bridge`.
-/

namespace Causalean.ML

open MeasureTheory

/-- `θhat` exactly minimizes a parametric objective over the admissible set. -/
structure IsERMP {Θ : Type*} (objective : Θ → ℝ) (Θset : Set Θ) (θhat : Θ) : Prop where
  /-- The minimizer is admissible. -/
  mem : θhat ∈ Θset
  /-- It attains the minimum of the objective over `Θset`. -/
  isMin : IsMinOn objective Θset θhat

/-- `θhat` minimizes a parametric objective up to slack `ε ≥ 0`. -/
structure IsApproxERMP {Θ : Type*} (objective : Θ → ℝ) (Θset : Set Θ)
    (θhat : Θ) (ε : ℝ) : Prop where
  /-- The slack is nonnegative. -/
  ε_nonneg : 0 ≤ ε
  /-- The candidate is admissible. -/
  mem : θhat ∈ Θset
  /-- Its objective is within `ε` of every competitor's. -/
  approx_min : ∀ θ ∈ Θset, objective θhat ≤ objective θ + ε

/-- `θhat` minimizes a penalized objective `objective θ + lam · penalty θ` with a
nonnegative regularization weight `lam`. -/
structure RegularizedERM {Θ : Type*} (objective : Θ → ℝ) (penalty : Θ → ℝ)
    (lam : ℝ) (Θset : Set Θ) (θhat : Θ) : Prop where
  /-- The regularization weight is nonnegative. -/
  lam_nonneg : 0 ≤ lam
  /-- The minimizer is admissible. -/
  mem : θhat ∈ Θset
  /-- It minimizes the penalized objective over `Θset`. -/
  isMin : IsMinOn (fun θ => objective θ + lam * penalty θ) Θset θhat

/-- An empirical-risk minimizer is an admissible prediction rule whose
finite-sample risk criterion is no larger than that of any other admissible
rule.  The criterion is the inverse-cardinality-scaled loss sum over a nonempty
finite sample. -/
structure IsERM {ι X Y : Type*} [Fintype ι] [Nonempty ι]
    [MeasurableSpace X] [MeasurableSpace Y]
    (H : HypothesisClass X Y) (loss : Loss Y) (S : ι → X × Y) (hhat : X → Y) : Prop where
  /-- The minimizer belongs to the class. -/
  mem : hhat ∈ H.carrier
  /-- It minimizes empirical risk over the class. -/
  isMin : IsMinOn (fun h => empiricalRisk loss S h) H.carrier hhat

/-- A population-risk minimizer is an admissible prediction rule whose
finite expected loss is no larger than the finite expected loss of any other
admissible rule.  The predicate carries integrability for the minimizer and for
every admissible competitor, so comparisons of Bochner integrals have the usual
population-risk interpretation. -/
structure IsPopulationRiskMinimizer {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (H : HypothesisClass X Y) (loss : Loss Y) (P : Measure (X × Y))
    (hstar : X → Y) : Prop where
  /-- The minimizer belongs to the class. -/
  mem : hstar ∈ H.carrier
  /-- The minimizer has finite expected loss. -/
  finite_self : HasFinitePopulationRisk loss P hstar
  /-- Every admissible competitor has finite expected loss. -/
  finite_competitor : ∀ h ∈ H.carrier, HasFinitePopulationRisk loss P h
  /-- It minimizes population risk over the class. -/
  isMin : IsMinOn (fun h => populationRisk loss P h) H.carrier hstar

end Causalean.ML
