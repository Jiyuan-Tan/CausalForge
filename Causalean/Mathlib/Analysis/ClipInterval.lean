/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Clipping a real number into a closed interval

Truncating (clipping, clamping, winsorising) a real number to a closed interval `[a, b]` is
ubiquitous in estimation: propensity scores are clipped away from `0` and `1`, outcomes and
privatised statistics are clipped to a symmetric band `[-B, B]`, and so on. Every such argument
needs the same four facts — the clipped value lies in the interval, values already inside are
untouched, the map is `1`-Lipschitz, and clipping never increases the distance (nor the squared
distance) to any target that is itself inside the interval.

Mathlib proves the contraction property, but only for the subtype-valued projection
`Set.projIcc : ℝ → Set.Icc a b`, which is awkward to use when the surrounding development works
with plain reals. This file provides the real-valued companion `clipIcc a b x = max a (min b x)`
(definitionally the underlying value of `Set.projIcc`) together with the facts above, so that a
symmetric band `[-B, B]`, an asymmetric propensity band `[q, 1 - q]`, and either the `max`-outside
or the `min`-outside spelling are all instances of one API.
-/

namespace Causalean.Mathlib.Analysis

variable {a b t x B : ℝ}

/-- **Clip to an interval.** `clipIcc a b x` is `x` pushed into the closed interval from `a` to
`b`: it returns `a` when `x` falls below `a`, `b` when `x` exceeds `b`, and `x` itself otherwise.
It is the plain real-valued form of the projection onto the interval. -/
noncomputable def clipIcc (a b x : ℝ) : ℝ := max a (min b x)

/-- Clipping into an interval is exactly Mathlib's projection onto that interval, read as a plain
real number instead of as an element of the interval. This is the bridge that makes every fact
about the projection available to a development that never leaves the reals. -/
lemma coe_projIcc_eq_clipIcc (hab : a ≤ b) (x : ℝ) :
    (Set.projIcc a b hab x : ℝ) = clipIcc a b x := rfl

/-- A clipped value always lies in the interval it was clipped to (provided the interval is
nonempty, i.e. its left endpoint does not exceed its right endpoint). -/
lemma clipIcc_mem_Icc (hab : a ≤ b) (x : ℝ) : clipIcc a b x ∈ Set.Icc a b :=
  (Set.projIcc a b hab x).2

/-- Clipping leaves untouched any number that already lies inside the interval. -/
lemma clipIcc_eq_self (hx : x ∈ Set.Icc a b) : clipIcc a b x = x := by
  rw [clipIcc, min_eq_right hx.2, max_eq_right hx.1]

/-- Clipping from below first and then from above gives the same answer as clipping from above
first and then from below. This reconciles the two spellings of the same operation that occur in
practice, `max a (min b x)` and `min b (max a x)`. -/
lemma clipIcc_eq_min_max (hab : a ≤ b) (x : ℝ) : clipIcc a b x = min b (max a x) := by
  rw [clipIcc, max_min_distrib_left, max_eq_right hab]

/-- Clipping is a contraction: two numbers are never pushed further apart by being clipped to a
common interval. -/
lemma lipschitzWith_clipIcc (a b : ℝ) : LipschitzWith 1 (clipIcc a b) :=
  (LipschitzWith.id.const_min b).const_max a

/-- Clipping two numbers to the same interval never increases the distance between them. -/
lemma abs_clipIcc_sub_clipIcc_le (a b x y : ℝ) :
    |clipIcc a b x - clipIcc a b y| ≤ |x - y| := by
  simpa [Real.dist_eq] using (lipschitzWith_clipIcc a b).dist_le_mul x y

/-- Capping from above and then flooring from below is a contraction as well: two numbers put
through that order of operations are never pushed further apart. Unlike `clipIcc_eq_min_max`, this
needs no assumption on the two thresholds, which is what makes it usable for a propensity band
`[q, 1 - q]` whose definition carries no `q ≤ 1/2` hypothesis. -/
lemma abs_min_max_sub_min_max_le (a b x y : ℝ) :
    |min b (max a x) - min b (max a y)| ≤ |x - y| := by
  have h : LipschitzWith 1 (fun z : ℝ => min b (max a z)) :=
    (LipschitzWith.id.const_max a).const_min b
  simpa [Real.dist_eq] using h.dist_le_mul x y

/-- Clipping a number into an interval never increases its distance to a target that already lies
inside that interval. This is the form used when the target is a true parameter known to obey the
same bounds that the estimator is clipped to. -/
lemma abs_clipIcc_sub_le (ht : t ∈ Set.Icc a b) (x : ℝ) :
    |clipIcc a b x - t| ≤ |x - t| := by
  simpa [clipIcc_eq_self ht] using abs_clipIcc_sub_clipIcc_le a b x t

/-- Clipping a number into an interval never increases its *squared* distance to a target that
already lies inside that interval — so clipping an estimator to a range known to contain the
truth can only reduce squared error. -/
lemma clipIcc_sub_sq_le (ht : t ∈ Set.Icc a b) (x : ℝ) :
    (clipIcc a b x - t) ^ 2 ≤ (x - t) ^ 2 := by
  have h := abs_clipIcc_sub_le ht x
  calc (clipIcc a b x - t) ^ 2 = |clipIcc a b x - t| ^ 2 := (sq_abs _).symm
    _ ≤ |x - t| ^ 2 := by gcongr
    _ = (x - t) ^ 2 := sq_abs _

/-- Clipping to a fixed interval is a continuous operation. -/
lemma continuous_clipIcc (a b : ℝ) : Continuous (clipIcc a b) :=
  continuous_const.max (continuous_const.min continuous_id)

/-- Clipping to a fixed interval is measurable, so clipping a random variable again yields a
random variable. -/
lemma measurable_clipIcc (a b : ℝ) : Measurable (clipIcc a b) :=
  (continuous_clipIcc a b).measurable

/-- Clipping to a symmetric band around zero produces a value whose magnitude is at most the
half-width of the band. -/
lemma abs_clipIcc_neg_le (hB : 0 ≤ B) (x : ℝ) : |clipIcc (-B) B x| ≤ B :=
  abs_le.mpr (clipIcc_mem_Icc (by linarith) x)

/-- Clipping to a symmetric band around zero leaves untouched any number whose magnitude is
already within the half-width of the band. -/
lemma clipIcc_neg_eq_self (hx : |x| ≤ B) : clipIcc (-B) B x = x :=
  clipIcc_eq_self (Set.mem_Icc.mpr (abs_le.mp hx))

end Causalean.Mathlib.Analysis
