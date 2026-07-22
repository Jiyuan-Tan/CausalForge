/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Fréchet–Hoeffding copula bounds and the easy-direction Makarov bound

This file proves, for a fixed joint law of two real random variables `X, Y` on a
probability space, the classical Fréchet–Hoeffding bounds on the joint CDF and the
*easy* (lower) direction of the Makarov bound on the CDF of the difference `X - Y`.

All quantities are written as `.toReal` of measures of the relevant events, e.g.
the joint CDF value is `(P {ω | X ω ≤ u ∧ Y ω ≤ v}).toReal`.

## Main results

* `frechet_upper` — `P(X ≤ u, Y ≤ v) ≤ min (P(X ≤ u)) (P(Y ≤ v))`.
* `frechet_lower` — `max (P(X ≤ u) + P(Y ≤ v) - 1) 0 ≤ P(X ≤ u, Y ≤ v)`.
* `makarov_lower_param` — per-threshold lower bound on the CDF of `X - Y`:
  `max (P(X ≤ a) - P(Y < a - s)) 0 ≤ P(X - Y ≤ s)`.
* `makarov_lower_iSup` — the sup-convolution envelope form of the Makarov lower bound.

These are exactly the directions provable from a *fixed* joint distribution. We do
**not** assert sharpness/attainability of these bounds (that is Makarov's hard
theorem and is out of scope here).
-/
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-! # Fréchet-Hoeffding and Makarov Bounds

This file proves probability bounds for the joint distribution of two real random
variables with a fixed joint law. The Fréchet-Hoeffding theorems
`frechet_upper` and `frechet_lower` bound the joint CDF value
`P(X <= u, Y <= v)` by the marginal CDF values. The Makarov theorems
`makarov_lower_param` and `makarov_lower_iSup` give the elementary lower bound
on the CDF of the difference `X - Y`.

These results are the directions that follow from an already fixed coupling of
`X` and `Y`. The file deliberately does not claim the sharp attainability part
of Makarov's theorem, which would require constructing extremal couplings. -/

open MeasureTheory

namespace Causalean.PartialID

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  {X Y : Ω → ℝ}

/-- The measure of any event in a probability space is `≠ ⊤`, so `.toReal` is well behaved. -/
private lemma measure_ne_top_of_prob (s : Set Ω) : P s ≠ ⊤ :=
  (measure_lt_top P s).ne

/-- Core sub-additivity inequality on an intersection:
`P A + P B - 1 ≤ P (A ∩ B)` in `ℝ` (`.toReal` form). -/
private lemma prob_inter_ge {A B : Set Ω} (hB : MeasurableSet B) :
    (P A).toReal + (P B).toReal - 1 ≤ (P (A ∩ B)).toReal := by
  have hkey : P (A ∪ B) + P (A ∩ B) = P A + P B := measure_union_add_inter A hB
  -- take `.toReal` of the inclusion–exclusion identity
  have htoReal : (P (A ∪ B)).toReal + (P (A ∩ B)).toReal = (P A).toReal + (P B).toReal := by
    rw [← ENNReal.toReal_add (measure_ne_top_of_prob P _) (measure_ne_top_of_prob P _),
        ← ENNReal.toReal_add (measure_ne_top_of_prob P _) (measure_ne_top_of_prob P _), hkey]
  have hunion_le : (P (A ∪ B)).toReal ≤ 1 := by
    have : P (A ∪ B) ≤ 1 := prob_le_one
    calc (P (A ∪ B)).toReal ≤ (1 : ENNReal).toReal :=
          ENNReal.toReal_mono (by simp) this
      _ = 1 := by simp
  linarith

/-- **Fréchet–Hoeffding upper bound.**
`P(X ≤ u, Y ≤ v) ≤ min (P(X ≤ u)) (P(Y ≤ v))`.  Needs no measurability: it is
pure monotonicity of the measure under set inclusion. -/
theorem frechet_upper (u v : ℝ) :
    (P {ω | X ω ≤ u ∧ Y ω ≤ v}).toReal
      ≤ min (P {ω | X ω ≤ u}).toReal (P {ω | Y ω ≤ v}).toReal := by
  refine le_min ?_ ?_
  · exact ENNReal.toReal_mono (measure_ne_top_of_prob P _)
      (measure_mono (fun ω hω => hω.1))
  · exact ENNReal.toReal_mono (measure_ne_top_of_prob P _)
      (measure_mono (fun ω hω => hω.2))

/-- **Fréchet–Hoeffding lower bound.**
`max (P(X ≤ u) + P(Y ≤ v) - 1) 0 ≤ P(X ≤ u, Y ≤ v)`. -/
theorem frechet_lower (hY : Measurable Y) (u v : ℝ) :
    max ((P {ω | X ω ≤ u}).toReal + (P {ω | Y ω ≤ v}).toReal - 1) 0
      ≤ (P {ω | X ω ≤ u ∧ Y ω ≤ v}).toReal := by
  have hseteq : {ω | X ω ≤ u ∧ Y ω ≤ v} = {ω | X ω ≤ u} ∩ {ω | Y ω ≤ v} := by
    ext ω; simp [Set.mem_inter_iff]
  have hB : MeasurableSet {ω : Ω | Y ω ≤ v} := measurableSet_le hY measurable_const
  refine max_le ?_ ENNReal.toReal_nonneg
  rw [hseteq]
  exact prob_inter_ge P hB

/-- **Makarov lower bound (easy direction), per-threshold form.**
For every reference point `a`,
`max (P(X ≤ a) - P(Y < a - s)) 0 ≤ P(X - Y ≤ s)`. -/
theorem makarov_lower_param (hY : Measurable Y) (s a : ℝ) :
    max ((P {ω | X ω ≤ a}).toReal - (P {ω | Y ω < a - s}).toReal) 0
      ≤ (P {ω | X ω - Y ω ≤ s}).toReal := by
  refine max_le ?_ ENNReal.toReal_nonneg
  -- Set inclusion: {X ≤ a} ∩ {a - s ≤ Y} ⊆ {X - Y ≤ s}.
  have hsub : {ω : Ω | X ω ≤ a} ∩ {ω : Ω | a - s ≤ Y ω} ⊆ {ω | X ω - Y ω ≤ s} := by
    intro ω hω
    have hXa : X ω ≤ a := hω.1
    have hYa : a - s ≤ Y ω := hω.2
    change X ω - Y ω ≤ s
    linarith
  -- {a - s ≤ Y} is the complement of {Y < a - s}, so its measure is 1 - P(Y < a - s).
  have hBmeas : MeasurableSet {ω : Ω | a - s ≤ Y ω} := measurableSet_le measurable_const hY
  have hcompl : {ω : Ω | a - s ≤ Y ω} = {ω : Ω | Y ω < a - s}ᶜ := by
    ext ω; simp [not_lt]
  have hBval : (P {ω : Ω | a - s ≤ Y ω}).toReal = 1 - (P {ω : Ω | Y ω < a - s}).toReal := by
    rw [hcompl, prob_compl_eq_one_sub (measurableSet_lt hY measurable_const)]
    rw [ENNReal.toReal_sub_of_le prob_le_one (by simp)]
    simp
  -- Lower bound on the intersection, then monotonicity to the difference event.
  have hinter : (P {ω | X ω ≤ a}).toReal + (P {ω : Ω | a - s ≤ Y ω}).toReal - 1
      ≤ (P ({ω | X ω ≤ a} ∩ {ω : Ω | a - s ≤ Y ω})).toReal :=
    prob_inter_ge P hBmeas
  have hmono : (P ({ω | X ω ≤ a} ∩ {ω : Ω | a - s ≤ Y ω})).toReal
      ≤ (P {ω | X ω - Y ω ≤ s}).toReal :=
    ENNReal.toReal_mono (measure_ne_top_of_prob P _) (measure_mono hsub)
  rw [hBval] at hinter
  linarith

/-- **Makarov lower bound (easy direction), sup-convolution envelope form.**
Taking the supremum over the reference point `a` still lower-bounds the CDF of `X - Y`. -/
theorem makarov_lower_iSup (hY : Measurable Y) (s : ℝ) :
    ⨆ a : ℝ, max ((P {ω | X ω ≤ a}).toReal - (P {ω | Y ω < a - s}).toReal) 0
      ≤ (P {ω | X ω - Y ω ≤ s}).toReal :=
  ciSup_le (fun a => makarov_lower_param P hY s a)

end Causalean.PartialID
