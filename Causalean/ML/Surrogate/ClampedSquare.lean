/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Mathlib.Analysis.ClipInterval
import Causalean.Stat.Concentration.Rademacher.Contraction

/-! # Clamped square surrogate for squared-loss contraction bounds

The clamped square is a globally Lipschitz surrogate for the squared map on a
bounded prediction range.  The basic loss `squaredLoss` lives in
`ML/Core/Losses`; this separate surrogate file imports the Rademacher
contraction interface and proves the analytic facts needed for squared-loss
complexity bounds.  The clipping itself is `Causalean.Mathlib.Analysis.clipIcc`
(see `Mathlib/Analysis/ClipInterval`), whose contraction and boundedness lemmas
are reused here.

On the band `[-c, c]`, `clampedSq c t` agrees with `t²`; globally, it is
`2c`-Lipschitz and fixes zero.  This is the standard route for applying a
Ledoux-Talagrand contraction bound to bounded squared-loss classes.

* `clampedSq_eq_sq` — `clampedSq c t = t²` whenever `|t| ≤ c`;
* `lipschitzAt0_clampedSq` — `clampedSq c` is `LipschitzAt0` with constant `2c` for `c ≥ 0`.
-/

namespace Causalean.ML

open Causalean.Stat.Concentration Causalean.Mathlib.Analysis

/-- The square of the projection of `t` onto `[-c, c]`: a globally Lipschitz surrogate that
agrees with `t ↦ t²` on `[-c, c]`. -/
noncomputable def clampedSq (c t : ℝ) : ℝ := (clipIcc (-c) c t) ^ 2

/-- The clamped square is continuous. -/
@[fun_prop]
lemma continuous_clampedSq (c : ℝ) : Continuous (clampedSq c) :=
  (continuous_clipIcc _ _).pow 2

/-- On [the band where `t` lies within `c` in absolute value](hyp:ht), [the clamped square
`clampedSq c t` equals the genuine square `t²`](goal). -/
lemma clampedSq_eq_sq {c t : ℝ} (ht : |t| ≤ c) : clampedSq c t = t ^ 2 := by
  rw [clampedSq, clipIcc_neg_eq_self ht]

/-- The clamped square is nonnegative. -/
lemma clampedSq_nonneg (c t : ℝ) : 0 ≤ clampedSq c t := sq_nonneg _

/-- For [a nonnegative bound `c`](hyp:hc), [the clamped square `clampedSq c t` never exceeds
`c²`](goal), for every real `t`. -/
lemma clampedSq_le_sq {c : ℝ} (hc : 0 ≤ c) (t : ℝ) : clampedSq c t ≤ c ^ 2 := by
  have h := abs_clipIcc_neg_le hc t
  calc clampedSq c t = |clipIcc (-c) c t| ^ 2 := by rw [clampedSq, sq_abs]
    _ ≤ c ^ 2 := by gcongr

/-- For [a nonnegative bound `c`](hyp:hc), [the clamped square `clampedSq c` is Lipschitz at
`0` with constant `2c`: it fixes `0` and is globally `2c`-Lipschitz](goal). -/
lemma lipschitzAt0_clampedSq {c : ℝ} (hc : 0 ≤ c) :
    LipschitzAt0 (clampedSq c) (2 * c) := by
  refine ⟨?_, ?_⟩
  · rw [clampedSq, clipIcc_neg_eq_self (by simpa using hc)]
    ring
  · intro x y
    have hclamp := abs_clipIcc_sub_clipIcc_le (-c) c x y
    have hfac : clampedSq c x - clampedSq c y
        = (clipIcc (-c) c x - clipIcc (-c) c y) * (clipIcc (-c) c x + clipIcc (-c) c y) := by
      simp only [clampedSq]; ring
    have hsum : |clipIcc (-c) c x + clipIcc (-c) c y| ≤ 2 * c := by
      have htri := abs_add_le (clipIcc (-c) c x) (clipIcc (-c) c y)
      have hcc := add_le_add (abs_clipIcc_neg_le hc x) (abs_clipIcc_neg_le hc y)
      linarith
    rw [hfac, abs_mul]
    have hmul :
        |clipIcc (-c) c x - clipIcc (-c) c y| * |clipIcc (-c) c x + clipIcc (-c) c y|
          ≤ |x - y| * (2 * c) :=
      mul_le_mul hclamp hsum (abs_nonneg _) (abs_nonneg _)
    rw [show (2 : ℝ) * c * |x - y| = |x - y| * (2 * c) from by ring]
    exact hmul

end Causalean.ML
