/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Structure-agnostic minimax risk packaging

Causal-agnostic specialization of the Le Cam two-point bound
(`Causalean/Stat/Minimax/LeCam.lean`) to a **real-valued functional** `τ` estimated
from `n` i.i.d. samples.  This is the shape consumed by minimax lower bounds for
concrete estimands (e.g. the structure-agnostic ATE optimality theorem, which
lives in the causal `Estimation/` tree, not here).

Main results:

* `real_two_point_lower_bound` — Le Cam specialized to `Θ = ℝ`: under `2s`-separation
  `2s ≤ |θ₀ − θ₁|`, every estimator's worst-case miss probability is `≥ ½(1 − tvDist)`.
* `two_point_lower_bound_of_tvDist_le` — same with an explicit upper bound `c` on `tvDist`.
* `iid_two_point_lower_bound` — the `n`-sample version: the data law is the product
  `Measure.pi (fun _ : Fin n ↦ P)` and the separation is on the functional values
  `τ P₀, τ P₁`.
* `two_point_lower_bound_of_chiSqDiv_le` — the χ²-divergence form obtained from
  `tvDist ≤ ½√χ²`, useful when explicit finite or product χ² computations are
  available.
* `mse_integrable_of_estimator_bound` — bounded-estimator bookkeeping for squared
  losses, used before MSE lower bounds can be applied to truncated estimators.

These statements remain project-agnostic: concrete causal or nonparametric lower
bounds import this layer after constructing the two laws, the functional
separation, and the required divergence estimate.
-/

import Causalean.Stat.Minimax.LeCam
import Causalean.Stat.Minimax.ChiSquared
import Mathlib.MeasureTheory.Constructions.Pi

/-! # Minimax Risk Lower Bounds

This file specializes Le Cam's two-point method to real-valued statistical
functionals and to estimators based on independent repeated samples. It records
the total-variation, chi-squared-divergence, and bounded-estimator integrability
forms used to certify concrete minimax rates. -/

namespace Causalean.Stat

open MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P₀ P₁ : Measure Ω}
  [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁]

/-- **Le Cam two-point bound for a real-valued parameter.**  If two candidate values
`θ₀, θ₁ : ℝ` are `2s`-separated, then for any (measurable) estimator `est : Ω → ℝ`
the worst-case probability of missing the truth by `≥ s` is at least `½(1 − tvDist P₀ P₁)`.
Specialization of `half_one_sub_tvDist_le_max_error` to `Θ = ℝ` with `dist a b = |a − b|`. -/
theorem real_two_point_lower_bound {est : Ω → ℝ} (hest : Measurable est)
    {θ₀ θ₁ s : ℝ} (hsep : 2 * s ≤ |θ₀ - θ₁|) :
    (1 - tvDist P₀ P₁) / 2
      ≤ max (P₀.real {ω | s ≤ |est ω - θ₀|}) (P₁.real {ω | s ≤ |est ω - θ₁|}) := by
  have hsep' : 2 * s ≤ dist θ₀ θ₁ := by rwa [Real.dist_eq]
  have h := half_one_sub_tvDist_le_max_error (P₀ := P₀) (P₁ := P₁) (Θ := ℝ) hest hsep'
  simpa only [Real.dist_eq] using h

/-- Variant of `real_two_point_lower_bound` with an explicit upper bound `c` on the
total variation distance: every estimator's worst-case miss probability is `≥ (1 − c)/2`. -/
theorem two_point_lower_bound_of_tvDist_le {est : Ω → ℝ} (hest : Measurable est)
    {θ₀ θ₁ s c : ℝ} (hsep : 2 * s ≤ |θ₀ - θ₁|) (hc : tvDist P₀ P₁ ≤ c) :
    (1 - c) / 2
      ≤ max (P₀.real {ω | s ≤ |est ω - θ₀|}) (P₁.real {ω | s ≤ |est ω - θ₁|}) := by
  have h := real_two_point_lower_bound (P₀ := P₀) (P₁ := P₁) hest hsep
  have : (1 - c) / 2 ≤ (1 - tvDist P₀ P₁) / 2 := by linarith
  exact this.trans h

/-- **`n`-sample structure-agnostic two-point bound.**  Given two single-observation
laws `P₀, P₁` and a real functional `τ` whose values are `2s`-separated, every
estimator `est` built from `n` i.i.d. samples (data law `Measure.pi (fun _ ↦ Pⱼ)`)
has worst-case miss probability at least `½(1 − tvDist)` between the two `n`-fold laws.
The functional values `τ P₀, τ P₁` play the role of the two parameters. -/
theorem iid_two_point_lower_bound {S : Type*} [MeasurableSpace S]
    (P₀ P₁ : Measure S) [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁]
    (τ : Measure S → ℝ) (n : ℕ) {s : ℝ} (hsep : 2 * s ≤ |τ P₀ - τ P₁|)
    {est : (Fin n → S) → ℝ} (hest : Measurable est) :
    (1 - tvDist (Measure.pi fun _ : Fin n => P₀) (Measure.pi fun _ : Fin n => P₁)) / 2
      ≤ max ((Measure.pi fun _ : Fin n => P₀).real {x | s ≤ |est x - τ P₀|})
            ((Measure.pi fun _ : Fin n => P₁).real {x | s ≤ |est x - τ P₁|}) :=
  real_two_point_lower_bound (P₀ := Measure.pi fun _ : Fin n => P₀)
    (P₁ := Measure.pi fun _ : Fin n => P₁) hest hsep

/-- **χ²-form two-point lower bound.**  An upper bound `c` on the χ²-divergence
`chiSqDiv P₀ P₁` yields, via `tvDist ≤ ½√χ²`, a lower bound `(1 − ½√c)/2` on the
worst-case miss probability of every estimator.  Since `chiSqDiv` tensorizes over
i.i.d. samples (`chiSqDiv_prod`) and is computable for explicit families, this is
the form used to certify minimax rates. -/
theorem two_point_lower_bound_of_chiSqDiv_le {est : Ω → ℝ} (hest : Measurable est)
    {θ₀ θ₁ s : ℝ} (hsep : 2 * s ≤ |θ₀ - θ₁|) (hac : P₀ ≪ P₁)
    (hint : Integrable (fun x => ((P₀.rnDeriv P₁ x).toReal - 1) ^ 2) P₁)
    {c : ℝ} (hc : chiSqDiv P₀ P₁ ≤ c) :
    (1 - (1 / 2) * Real.sqrt c) / 2
      ≤ max (P₀.real {ω | s ≤ |est ω - θ₀|}) (P₁.real {ω | s ≤ |est ω - θ₁|}) := by
  have htv : tvDist P₀ P₁ ≤ (1 / 2) * Real.sqrt c := by
    refine (tvDist_le_half_sqrt_chiSqDiv P₀ P₁ hac hint).trans ?_
    gcongr
  exact two_point_lower_bound_of_tvDist_le hest hsep htv

/-- **Squared-loss integrability for a truncated estimator.**  If a measurable estimator `T`
takes values in the bounded interval `[-M, M]` (with `M ≥ 0`), then under any finite measure `Q`
its squared loss `(T − θ)²` against an arbitrary target `θ` is integrable, because it is bounded
by the constant `(M + |θ|)²`.  This is the routine integrability bookkeeping needed before the
worst-case squared risk of a truncated estimator can be compared in a two-point lower bound. -/
lemma mse_integrable_of_estimator_bound {S : Type*} [MeasurableSpace S]
    (Q : Measure S) [IsFiniteMeasure Q] (T : S → ℝ) (hT : Measurable T)
    {M theta : ℝ} (hM : 0 ≤ M) (hbound : ∀ s, T s ∈ Set.Icc (-M) M) :
    Integrable (fun s => (T s - theta) ^ 2) Q := by
  refine Integrable.of_bound
    ((hT.sub measurable_const).pow_const (2 : ℕ)).aestronglyMeasurable
    ((M + |theta|) ^ 2) ?_
  filter_upwards with s
  have hTabs : |T s| ≤ M := abs_le.mpr (hbound s)
  have hsub : |T s - theta| ≤ M + |theta| :=
    (abs_sub (T s) theta).trans (add_le_add hTabs le_rfl)
  have hC : 0 ≤ M + |theta| := add_nonneg hM (abs_nonneg theta)
  have hsq : (T s - theta) ^ 2 ≤ (M + |theta|) ^ 2 := by
    nlinarith [hsub, abs_nonneg (T s - theta), hC, sq_abs (T s - theta)]
  simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (T s - theta))] using hsq

end Causalean.Stat
