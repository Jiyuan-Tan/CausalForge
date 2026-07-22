/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Stat.Concentration.Rademacher.Contraction

/-! # Clamped square surrogate for squared-loss contraction bounds

The clamped square is a globally Lipschitz surrogate for the squared map on a
bounded prediction range.  The basic loss `squaredLoss` lives in
`ML/Core/Losses`; this separate surrogate file imports the Rademacher
contraction interface and proves the analytic facts needed for squared-loss
complexity bounds.

On the band `[-c, c]`, `clampedSq c t` agrees with `t²`; globally, it is
`2c`-Lipschitz and fixes zero.  This is the standard route for applying a
Ledoux-Talagrand contraction bound to bounded squared-loss classes.

* `clampedSq_eq_sq` — `clampedSq c t = t²` whenever `|t| ≤ c`;
* `lipschitzAt0_clampedSq` — `clampedSq c` is `LipschitzAt0` with constant `2c` for `c ≥ 0`.
-/

namespace Causalean.ML

open Causalean.Stat.Concentration

/-- The square of the projection of `t` onto `[-c, c]`: a globally Lipschitz surrogate that
agrees with `t ↦ t²` on `[-c, c]`. -/
noncomputable def clampedSq (c t : ℝ) : ℝ := (max (-c) (min c t)) ^ 2

/-- The clamped square is continuous. -/
lemma continuous_clampedSq (c : ℝ) : Continuous (clampedSq c) :=
  (continuous_const.max (continuous_const.min continuous_id)).pow 2

/-- On the band `|t| ≤ c`, the clamped square is the genuine square. -/
lemma clampedSq_eq_sq {c t : ℝ} (ht : |t| ≤ c) : clampedSq c t = t ^ 2 := by
  rw [abs_le] at ht
  rw [clampedSq, min_eq_right ht.2, max_eq_right ht.1]

/-- The clamped square is nonnegative. -/
lemma clampedSq_nonneg (c t : ℝ) : 0 ≤ clampedSq c t := sq_nonneg _

/-- The clamped square never exceeds `c²` (for `c ≥ 0`). -/
lemma clampedSq_le_sq {c : ℝ} (hc : 0 ≤ c) (t : ℝ) : clampedSq c t ≤ c ^ 2 := by
  have h : |max (-c) (min c t)| ≤ c := by
    rw [abs_le]
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  have heq : clampedSq c t = |max (-c) (min c t)| ^ 2 := by rw [clampedSq, sq_abs]
  rw [heq]
  nlinarith [abs_nonneg (max (-c) (min c t))]

/-- `clampedSq c` is Lipschitz at `0` with constant `2c` (for `c ≥ 0`): it fixes `0` and the
truncated square is globally `2c`-Lipschitz. -/
lemma lipschitzAt0_clampedSq {c : ℝ} (hc : 0 ≤ c) :
    LipschitzAt0 (clampedSq c) (2 * c) := by
  have hLip : LipschitzWith 1 (fun t : ℝ => max (-c) (min c t)) :=
    (LipschitzWith.id.const_min c).const_max (-c)
  have habs_le : ∀ z, |max (-c) (min c z)| ≤ c := by
    intro z
    rw [abs_le]
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  refine ⟨?_, ?_⟩
  · show (max (-c) (min c 0)) ^ 2 = 0
    rw [min_eq_right hc, max_eq_right (by linarith : -c ≤ (0 : ℝ))]
    ring
  · intro x y
    have hclamp : |max (-c) (min c x) - max (-c) (min c y)| ≤ |x - y| := by
      simpa [Real.dist_eq, one_mul] using hLip.dist_le_mul x y
    have hfac : clampedSq c x - clampedSq c y
        = (max (-c) (min c x) - max (-c) (min c y))
          * (max (-c) (min c x) + max (-c) (min c y)) := by
      show (max (-c) (min c x)) ^ 2 - (max (-c) (min c y)) ^ 2 = _
      ring
    have hsum : |max (-c) (min c x) + max (-c) (min c y)| ≤ 2 * c := by
      have htri := abs_add_le (max (-c) (min c x)) (max (-c) (min c y))
      have hcc := add_le_add (habs_le x) (habs_le y)
      linarith
    rw [hfac, abs_mul]
    have hmul :
        |max (-c) (min c x) - max (-c) (min c y)|
            * |max (-c) (min c x) + max (-c) (min c y)|
          ≤ |x - y| * (2 * c) :=
      mul_le_mul hclamp hsum (abs_nonneg _) (abs_nonneg _)
    rw [show (2 : ℝ) * c * |x - y| = |x - y| * (2 * c) from by ring]
    exact hmul

end Causalean.ML
