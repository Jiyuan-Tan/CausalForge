/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Stat.Nonparametric.MomentProblems.ResidualQuadratic.MeasureBridge
import Causalean.Stat.Nonparametric.MomentProblems.BoundedOutcomeEnvelope.QuarticRoot

/-!
# Bounded-outcome residual envelope: definitions

This file starts the bounded-outcome branch of `MomentProblems`. It defines the sharp envelope
`ρ(v)` of the `L²` residual of `y²` on `span{1, y}` over probability measures on `[0,1]` with fixed
second moment `v²`.

* `maximizingRoot v` — the unique interior root `μᵥ ∈ (v², v)` of the FOC quartic
  (from `interior_quartic_exists`), extracted by choice.
* `rhoEnvelope v := momentEnvelope μᵥ (v²)` — the closed-form envelope value `ρ(v)`.
* `Admissible v μ` — `μ` is a probability measure a.e. supported in `[0,1]` with `∫ y² ∂μ = v²`.
* `residualSet v` — the set of realized residuals `{ l2ResidualQuadratic μ | Admissible v μ }`,
  whose supremum the main file shows equals `rhoEnvelope v`.
-/

namespace Causalean.Stat.MomentProblems.BoundedOutcomeEnvelope

open Causalean.Stat.MomentProblems.ResidualQuadratic.MomentAlgebra
open Causalean.Stat.MomentProblems.ResidualQuadratic.MeasureBridge
  (moment l2ResidualQuadratic FiniteMoment4)
open MeasureTheory Set
open scoped Real

/-- The envelope maximizer `μᵥ`: the unique root of `envelopeQuartic · (v²)` in `(v², v)`,
extracted by classical choice from `interior_quartic_exists`. Outside the admissible range
`v ∈ (0,1)` it is set to `0` (junk value). -/
noncomputable def maximizingRoot (v : ℝ) : ℝ :=
  if h : 0 < v ∧ v < 1 then (interior_quartic_exists v h.1 h.2).choose else 0

/-- `maximizingRoot v` lies in the open interval `(v², v)`. -/
theorem maximizingRoot_mem (v : ℝ) (hv0 : 0 < v) (hv1 : v < 1) :
    maximizingRoot v ∈ Ioo (v ^ 2) v := by
  rw [maximizingRoot, dif_pos ⟨hv0, hv1⟩]
  exact (interior_quartic_exists v hv0 hv1).choose_spec.1

/-- `maximizingRoot v` is a root of the FOC quartic at `q = v²`. -/
theorem maximizingRoot_quartic (v : ℝ) (hv0 : 0 < v) (hv1 : v < 1) :
    envelopeQuartic (maximizingRoot v) (v ^ 2) = 0 := by
  rw [maximizingRoot, dif_pos ⟨hv0, hv1⟩]
  exact (interior_quartic_exists v hv0 hv1).choose_spec.2

/-- The **measure-level residual envelope** `ρ(v) = momentEnvelope μᵥ (v²)`, evaluated at the
maximizing support parameter `μᵥ = maximizingRoot v`. -/
noncomputable def rhoEnvelope (v : ℝ) : ℝ := momentEnvelope (maximizingRoot v) (v ^ 2)

/-- `ρ(v) > 0` for `v ∈ (0,1)`: `momentEnvelope μᵥ (v²) = (μᵥ − v²)(v² − μᵥ²) / (4 μᵥ (1 − μᵥ))`
has all four factors positive when `μᵥ ∈ (v², v)`. -/
theorem rhoEnvelope_pos (v : ℝ) (hv0 : 0 < v) (hv1 : v < 1) : 0 < rhoEnvelope v := by
  have hmem := maximizingRoot_mem v hv0 hv1
  set u := maximizingRoot v with hu
  have h1 : v ^ 2 < u := hmem.1
  have h2 : u < v := hmem.2
  have hu0 : 0 < u := lt_trans (by positivity) h1
  have hu1 : u < 1 := lt_trans h2 hv1
  have hnum1 : 0 < u - v ^ 2 := by linarith
  have hnum2 : 0 < v ^ 2 - u ^ 2 := by nlinarith
  have hden : 0 < 4 * u * (1 - u) := by nlinarith
  rw [rhoEnvelope, momentEnvelope]
  positivity

/-- `μ` is **admissible** for the envelope at level `v`: a probability measure a.e. supported in
`[0,1]` with second moment `∫ y² ∂μ = v²`. These are exactly the laws over which the residual
`l2ResidualQuadratic` is maximized to give `ρ(v)`. -/
structure Admissible (v : ℝ) (μ : Measure ℝ) : Prop where
  /-- `μ` is a probability measure. -/
  isProb : IsProbabilityMeasure μ
  /-- `μ` is a.e. supported in `[0,1]`. -/
  supp : ∀ᵐ y ∂μ, y ∈ Set.Icc (0 : ℝ) 1
  /-- `μ` has second moment `v²`. -/
  moment2 : ∫ y, y ^ 2 ∂μ = v ^ 2

/-- The set of residual values realized by admissible laws:
`{ r | ∃ μ, Admissible v μ ∧ r = l2ResidualQuadratic μ }`. The main theorem is
`IsLUB (residualSet v) (rhoEnvelope v)`. -/
def residualSet (v : ℝ) : Set ℝ :=
  {r | ∃ μ : Measure ℝ, Admissible v μ ∧ r = l2ResidualQuadratic μ}

/-- Second moment of an admissible law in `moment`-form: `moment μ 2 = v²`. -/
theorem Admissible.moment2_eq {v : ℝ} {μ : Measure ℝ} (h : Admissible v μ) :
    moment μ 2 = v ^ 2 := by
  change ∫ y, y ^ 2 ∂μ = v ^ 2
  exact h.moment2

end Causalean.Stat.MomentProblems.BoundedOutcomeEnvelope
