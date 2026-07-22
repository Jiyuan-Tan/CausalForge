/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Le Cam's two-point method

The reduction from estimation to hypothesis testing.  Given two probability
measures `P₀, P₁` on a sample space `Ω` whose parameter values `θ₀, θ₁` in a
(pseudo)metric space are `2s`-separated, **every** estimator `est : Ω → Θ` incurs

  `max ( P₀(dist(est, θ₀) ≥ s), P₁(dist(est, θ₁) ≥ s) ) ≥ ½ (1 − tvDist P₀ P₁)`.

This is the canonical minimax lower bound: it certifies that *no* estimator can
drive both error probabilities below `½(1 − tvDist)`.  The proof rests entirely
on the elementary testing bound `one_sub_tvDist_le_test` plus the triangle
inequality, with no measure-theoretic machinery beyond monotonicity.

The companion file `Causalean/Stat/Minimax/Pinsker.lean` supplies the bound on
`tvDist` in terms of Kullback–Leibler divergence that makes this usable for
concrete two-point families.
-/

import Causalean.Stat.Minimax.TotalVariation

/-! # Le Cam Two-Point Method

This file proves the two-point minimax lower bound that reduces estimation risk to
binary testing. It supplies the real-error and worst-case probability inequalities
used by later minimax-risk modules. -/

namespace Causalean.Stat

open MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P₀ P₁ : Measure Ω}
  [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁]
  {Θ : Type*} [PseudoMetricSpace Θ] [MeasurableSpace Θ] [OpensMeasurableSpace Θ]

/-- The error region `{ω | s ≤ dist (est ω) θ}` of an estimator is measurable. -/
theorem measurableSet_error {est : Ω → Θ} (hest : Measurable est) (θ : Θ) (s : ℝ) :
    MeasurableSet {ω | s ≤ dist (est ω) θ} := by
  have hclosed : IsClosed {x : Θ | s ≤ dist x θ} :=
    isClosed_le continuous_const (continuous_id.dist continuous_const)
  exact hest hclosed.measurableSet

/-- **Le Cam two-point bound (summed form).** If the parameter values `θ₀, θ₁`
are `2s`-separated, then for any estimator `est` the two error probabilities sum
to at least `1 − tvDist P₀ P₁`. -/
theorem one_sub_tvDist_le_error_sum {est : Ω → Θ} (hest : Measurable est)
    {θ₀ θ₁ : Θ} {s : ℝ} (hsep : 2 * s ≤ dist θ₀ θ₁) :
    1 - tvDist P₀ P₁
      ≤ P₀.real {ω | s ≤ dist (est ω) θ₀} + P₁.real {ω | s ≤ dist (est ω) θ₁} := by
  set A := {ω | s ≤ dist (est ω) θ₀} with hA
  set B := {ω | s ≤ dist (est ω) θ₁} with hB
  have hAmeas : MeasurableSet A := measurableSet_error hest θ₀ s
  have hBmeas : MeasurableSet B := measurableSet_error hest θ₁ s
  -- Outside the first error region, the second error region is forced.
  have hsub : Aᶜ ⊆ B := by
    intro ω hω
    have hlt : dist (est ω) θ₀ < s := by
      simpa [hA, Set.mem_compl_iff, not_le] using hω
    have htri : dist θ₀ θ₁ ≤ dist (est ω) θ₀ + dist (est ω) θ₁ := by
      simpa [dist_comm] using dist_triangle θ₀ (est ω) θ₁
    have : s ≤ dist (est ω) θ₁ := by nlinarith [htri, hsep, hlt]
    simpa [hB] using this
  -- Monotonicity transports the testing bound from `Aᶜ` to `B`.
  have hmono : P₁.real Aᶜ ≤ P₁.real B :=
    measureReal_mono hsub (measure_ne_top P₁ _)
  have htest := one_sub_tvDist_le_test (μ := P₀) (ν := P₁) hAmeas
  linarith [htest, hmono]

/-- **Le Cam two-point bound (max form).** Under `2s`-separation, every estimator
has worst-case error probability at least `½ (1 − tvDist P₀ P₁)`. -/
theorem half_one_sub_tvDist_le_max_error {est : Ω → Θ} (hest : Measurable est)
    {θ₀ θ₁ : Θ} {s : ℝ} (hsep : 2 * s ≤ dist θ₀ θ₁) :
    (1 - tvDist P₀ P₁) / 2
      ≤ max (P₀.real {ω | s ≤ dist (est ω) θ₀}) (P₁.real {ω | s ≤ dist (est ω) θ₁}) := by
  have hsum := one_sub_tvDist_le_error_sum (P₀ := P₀) (P₁ := P₁) hest hsep
  have h0 : P₀.real {ω | s ≤ dist (est ω) θ₀}
      ≤ max (P₀.real {ω | s ≤ dist (est ω) θ₀}) (P₁.real {ω | s ≤ dist (est ω) θ₁}) :=
    le_max_left _ _
  have h1 : P₁.real {ω | s ≤ dist (est ω) θ₁}
      ≤ max (P₀.real {ω | s ≤ dist (est ω) θ₀}) (P₁.real {ω | s ≤ dist (est ω) θ₁}) :=
    le_max_right _ _
  linarith [hsum, h0, h1]

end Causalean.Stat
