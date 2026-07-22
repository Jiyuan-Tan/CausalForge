/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Stat.Nonparametric.MomentProblems.ResidualQuadratic.ProjectionResidual

/-!
# Constrained quadratic score program dual to the L² projection residual

This file solves the optimization problem that uses the projection residual from the neighboring
`ProjectionResidual.lean` file. For a probability measure `μ` on `ℝ` with finite fourth moment and
positive variance, consider the **constrained minimum-norm score program**: among all scores
`s ∈ L²(μ)` that are moment-orthogonal to `1` and `y` and carry a prescribed `y²`-moment `x`,

    minimize   ∫ s² dμ
    subject to ∫ s dμ = 0,  ∫ y·s dμ = 0,  ∫ y²·s dμ = x,

what is the least achievable L²(μ) norm² of `s`?

The answer is the **duality identity**

    scoreCost μ x = x² / r,      where  r = l2ResidualQuadratic μ

is the (positive) L² residual of regressing `y²` on `span{1, y}` (`ProjectionResidual.lean`). This
is the classic Lagrangian / minimum-norm-interpolation duality: the constrained least-norm value is
`(prescribed moment)² / (residual variance of the constrained direction)`.

## Contents

* `FeasibleScore μ x s` — feasibility: `s ∈ L²(μ)` with the three moment constraints.
* `optScore μ x`        — the optimal score `s*(y) = (x/r)·q(y)`, `q` the projection residual.
* `optScore_feasible`, `optScore_cost` — `s*` is feasible and achieves cost `x²/r` (attainment).
* `feasibleScore_cost_lower_bound` — every feasible `s` has `∫ s² ≥ x²/r` (completing the square:
  `∫ (s − (x/r)q)² = ∫ s² − x²/r ≥ 0`, using `∫ q·s = x` and `∫ q² = r`).
* `scoreCost`, `scoreCost_eq` — the program value and the headline duality `scoreCost μ x = x²/r`.

## Reuse

The identity is the reusable score-cost primitive for arm-specific moment problems: once an arm law
has residual variance `r_{a,ν}`, a target moment displacement `x` has least score norm
`J_{a,ν}(x) = x² / r_{a,ν}`.
-/

namespace Causalean.Stat.MomentProblems.ScoreProgram

open MeasureTheory
open scoped Real
open Causalean.Stat.MomentProblems.ResidualQuadratic.MeasureBridge
  (moment optIntercept optSlope l2ResidualQuadratic FiniteMoment4)
open Causalean.Stat.MomentProblems.ResidualQuadratic.ProjectionResidual

/-- **Feasibility of a score.** `s : ℝ → ℝ` is feasible for target `x` if it lies in `L²(μ)` and is
moment-orthogonal to `1` and `y` while carrying prescribed `y²`-moment `x`:
`s ∈ L²(μ)`, `∫ s dμ = 0`, `∫ y·s dμ = 0`, `∫ y²·s dμ = x`.

(`MemLp s 2 μ` is the honest formalization of "`s ∈ L²`, i.e. `∫ s² < ∞`" — it additionally supplies
the measurability that makes the three moment constraints meaningful; on the finite measure `μ` it
implies `Integrable (s²) μ` and `Integrable s μ`.) -/
structure FeasibleScore (μ : Measure ℝ) (x : ℝ) (s : ℝ → ℝ) : Prop where
  /-- `s` is square-integrable: `s ∈ L²(μ)`. -/
  memL2 : MemLp s 2 μ
  /-- `s` is orthogonal to the constant `1`: `∫ s dμ = 0`. -/
  mean_zero : ∫ y, s y ∂μ = 0
  /-- `s` is orthogonal to `y`: `∫ y·s dμ = 0`. -/
  cov_id_zero : ∫ y, y * s y ∂μ = 0
  /-- `s` carries the prescribed `y²`-moment: `∫ y²·s dμ = x`. -/
  cov_sq : ∫ y, y ^ 2 * s y ∂μ = x

/-- The **optimal score** `s*(y) = (x / r)·q(y)`, where `q` is the L² projection residual of `y²`
onto `span{1, y}` and `r = l2ResidualQuadratic μ`. This is the minimum-norm feasible score. -/
noncomputable def optScore (μ : Measure ℝ) (x : ℝ) : ℝ → ℝ :=
  fun y => (x / l2ResidualQuadratic μ) * projResidual μ y

/-- The **value of the score program**: the infimum of `∫ s² dμ` over all feasible scores `s`. -/
noncomputable def scoreCost (μ : Measure ℝ) (x : ℝ) : ℝ :=
  sInf {c : ℝ | ∃ s, FeasibleScore μ x s ∧ c = ∫ y, s y ^ 2 ∂μ}

/-- **Feasibility of the optimal score.** `s* = (x/r)·q` is a feasible score for target `x`:
it lies in `L²(μ)` and satisfies the three moment constraints. The `y²`-moment constraint uses
`∫ y²·q = r` and `(x/r)·r = x` (needs `r ≠ 0`). -/
theorem optScore_feasible (μ : Measure ℝ) [IsProbabilityMeasure μ] (h : FiniteMoment4 μ)
    (hnd : moment μ 1 ^ 2 < moment μ 2) (hr : 0 < l2ResidualQuadratic μ) (x : ℝ) :
    FeasibleScore μ x (optScore μ x) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [optScore] using
      (projResidual_memL2 μ h).const_mul (x / l2ResidualQuadratic μ)
  · simp [optScore, integral_const_mul, integral_projResidual μ h hnd]
  · calc
      ∫ y, y * optScore μ x y ∂μ
          = ∫ y, (x / l2ResidualQuadratic μ) * (y * projResidual μ y) ∂μ := by
            apply integral_congr_ae
            filter_upwards with y
            simp [optScore]
            ring
      _ = 0 := by
        simp [integral_const_mul, integral_id_mul_projResidual μ h hnd]
  · calc
      ∫ y, y ^ 2 * optScore μ x y ∂μ
          = ∫ y, (x / l2ResidualQuadratic μ) * (y ^ 2 * projResidual μ y) ∂μ := by
            apply integral_congr_ae
            filter_upwards with y
            simp [optScore]
            ring
      _ = x := by
        rw [integral_const_mul, integral_sq_mul_projResidual μ h hnd]
        exact div_mul_cancel₀ x (ne_of_gt hr)

/-- **Attainment.** The optimal score `s*` achieves cost exactly `x² / r`:
`∫ (s*)² dμ = ∫ (x/r)²·q² dμ = (x/r)²·r = x²/r`. -/
theorem optScore_cost (μ : Measure ℝ) [IsProbabilityMeasure μ] (h : FiniteMoment4 μ)
    (hnd : moment μ 1 ^ 2 < moment μ 2) (hr : 0 < l2ResidualQuadratic μ) (x : ℝ) :
    ∫ y, optScore μ x y ^ 2 ∂μ = x ^ 2 / l2ResidualQuadratic μ := by
  calc
    ∫ y, optScore μ x y ^ 2 ∂μ
        = ∫ y, (x / l2ResidualQuadratic μ) ^ 2 * projResidual μ y ^ 2 ∂μ := by
          apply integral_congr_ae
          filter_upwards with y
          simp [optScore, mul_pow]
    _ = x ^ 2 / l2ResidualQuadratic μ := by
      rw [integral_const_mul, integral_sq_projResidual μ h hnd]
      field_simp [ne_of_gt hr]

/-- **Lower bound (duality `≤`).** Every feasible score has cost at least `x² / r`.

Proof (completing the square). With `r = l2ResidualQuadratic μ`, `c = x/r` and `q = projResidual μ`:
for feasible `s`, `∫ q·s = ∫ y²·s − optIntercept·∫ s − optSlope·∫ y·s = x` (the constraints), and
`∫ q² = r`. Hence
`0 ≤ ∫ (s − c·q)² = ∫ s² − 2c·(∫ q·s) + c²·(∫ q²) = ∫ s² − 2x²/r + x²/r = ∫ s² − x²/r`,
so `x²/r ≤ ∫ s²`. All splits use `Integrable s`, `Integrable (y·s)`, `Integrable (y²·s)`,
`Integrable (s·q)` and `Integrable (s²)`, each obtained from `MemLp _ 2 μ` on the finite measure. -/
theorem feasibleScore_cost_lower_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (h : FiniteMoment4 μ)
    (hnd : moment μ 1 ^ 2 < moment μ 2) (hr : 0 < l2ResidualQuadratic μ) (x : ℝ) {s : ℝ → ℝ}
    (hs : FeasibleScore μ x s) :
    x ^ 2 / l2ResidualQuadratic μ ≤ ∫ y, s y ^ 2 ∂μ := by
  let r := l2ResidualQuadratic μ
  let c := x / r
  let q := projResidual μ
  have hq_mem : MemLp q 2 μ := by
    simpa [q] using projResidual_memL2 μ h
  have hs_int : Integrable s μ := hs.memL2.integrable (by norm_num)
  have hys_int : Integrable (fun y : ℝ => y * s y) μ :=
    (memL2_id μ h).integrable_mul hs.memL2
  have hy2s_int : Integrable (fun y : ℝ => y ^ 2 * s y) μ :=
    (memL2_sq μ h).integrable_mul hs.memL2
  have hqs_int : Integrable (fun y : ℝ => q y * s y) μ :=
    hq_mem.integrable_mul hs.memL2
  have hq2_int : Integrable (fun y : ℝ => q y ^ 2) μ :=
    hq_mem.integrable_sq
  have hs2_int : Integrable (fun y : ℝ => s y ^ 2) μ :=
    hs.memL2.integrable_sq
  have hqs : ∫ y, q y * s y ∂μ = x := by
    calc
      ∫ y, q y * s y ∂μ
          = ∫ y, y ^ 2 * s y - optIntercept μ * s y
              - optSlope μ * (y * s y) ∂μ := by
            apply integral_congr_ae
            filter_upwards with y
            simp [q, projResidual]
            ring
      _ = (∫ y, y ^ 2 * s y - optIntercept μ * s y ∂μ)
          - (∫ y, optSlope μ * (y * s y) ∂μ) := by
            exact integral_sub (hy2s_int.sub (hs_int.const_mul _)) (hys_int.const_mul _)
      _ = ((∫ y, y ^ 2 * s y ∂μ) - (∫ y, optIntercept μ * s y ∂μ))
          - (∫ y, optSlope μ * (y * s y) ∂μ) := by
            rw [integral_sub hy2s_int (hs_int.const_mul _)]
      _ = (∫ y, y ^ 2 * s y ∂μ) - (∫ y, optIntercept μ * s y ∂μ)
          - (∫ y, optSlope μ * (y * s y) ∂μ) := by
            ring
      _ = x := by
        simp [integral_const_mul, hs.cov_sq, hs.mean_zero, hs.cov_id_zero]
  have hnn : 0 ≤ ∫ y, (s y - c * q y) ^ 2 ∂μ :=
    integral_nonneg (fun y => sq_nonneg (s y - c * q y))
  have hexpand : ∫ y, (s y - c * q y) ^ 2 ∂μ =
      (∫ y, s y ^ 2 ∂μ) - 2 * c * (∫ y, q y * s y ∂μ)
        + c ^ 2 * (∫ y, q y ^ 2 ∂μ) := by
    calc
      ∫ y, (s y - c * q y) ^ 2 ∂μ
          = ∫ y, s y ^ 2 - 2 * c * (q y * s y) + c ^ 2 * q y ^ 2 ∂μ := by
            apply integral_congr_ae
            filter_upwards with y
            ring
      _ = (∫ y, s y ^ 2 - 2 * c * (q y * s y) ∂μ)
          + (∫ y, c ^ 2 * q y ^ 2 ∂μ) := by
            exact integral_add (hs2_int.sub (hqs_int.const_mul _)) (hq2_int.const_mul _)
      _ = ((∫ y, s y ^ 2 ∂μ) - (∫ y, 2 * c * (q y * s y) ∂μ))
          + (∫ y, c ^ 2 * q y ^ 2 ∂μ) := by
            rw [integral_sub hs2_int (hqs_int.const_mul _)]
      _ = (∫ y, s y ^ 2 ∂μ) - (∫ y, 2 * c * (q y * s y) ∂μ)
          + (∫ y, c ^ 2 * q y ^ 2 ∂μ) := by
            ring
      _ = (∫ y, s y ^ 2 ∂μ) - 2 * c * (∫ y, q y * s y ∂μ)
          + c ^ 2 * (∫ y, q y ^ 2 ∂μ) := by
            rw [integral_const_mul, integral_const_mul]
  have hnonneg : 0 ≤ (∫ y, s y ^ 2 ∂μ) - 2 * c * x + c ^ 2 * r := by
    rw [hexpand, hqs] at hnn
    simpa [q, r, integral_sq_projResidual μ h hnd] using hnn
  have halg : 2 * c * x - c ^ 2 * r = x ^ 2 / r := by
    subst c
    subst r
    field_simp [ne_of_gt hr]
    ring
  linarith

/-- **The score-program duality (headline).** For a probability measure with finite fourth moment,
positive variance (`m₁² < m₂`) and positive residual (`r = l2ResidualQuadratic μ > 0`), the
constrained minimum-norm score program equals `x² / r`:

    scoreCost μ x = x² / l2ResidualQuadratic μ.

Proof: `x²/r` is attained by `optScore μ x` (`optScore_feasible` + `optScore_cost`), so it lies in
the value set, and it is a lower bound of that set (`feasibleScore_cost_lower_bound`); hence it is
the least element, and `sInf` of the value set equals it (`IsLeast.csInf_eq`). -/
theorem scoreCost_eq (μ : Measure ℝ) [IsProbabilityMeasure μ] (h : FiniteMoment4 μ)
    (hnd : moment μ 1 ^ 2 < moment μ 2) (hr : 0 < l2ResidualQuadratic μ) (x : ℝ) :
    scoreCost μ x = x ^ 2 / l2ResidualQuadratic μ := by
  have hmem : x ^ 2 / l2ResidualQuadratic μ ∈
      {c : ℝ | ∃ s, FeasibleScore μ x s ∧ c = ∫ y, s y ^ 2 ∂μ} :=
    ⟨optScore μ x, optScore_feasible μ h hnd hr x, (optScore_cost μ h hnd hr x).symm⟩
  have hlb : x ^ 2 / l2ResidualQuadratic μ ∈
      lowerBounds {c : ℝ | ∃ s, FeasibleScore μ x s ∧ c = ∫ y, s y ^ 2 ∂μ} := by
    rintro c ⟨s, hs, rfl⟩
    exact feasibleScore_cost_lower_bound μ h hnd hr x hs
  exact IsLeast.csInf_eq ⟨hmem, hlb⟩

end Causalean.Stat.MomentProblems.ScoreProgram
