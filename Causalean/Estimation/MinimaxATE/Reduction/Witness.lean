/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Structure-agnostic ATE lower bound: the two-point reduction

This is the abstract reduction layer for the structure-agnostic optimality lower
bound (Jin–Syrgkanis 2024).  It packages a **two-point (Le Cam) witness** and
turns it into a minimax lower bound on the worst-case-over-class probability of
missing the true ATE.

A `TwoPointWitness` provides two `n`-sample data laws `Q false`, `Q true` together
with the data needed to run Le Cam's method:

* `θ` — the true ATE attached to each hypothesis, with a separation `2 s ≤ |θ true − θ false|`;
* `tvBound` — the total-variation distance between the two laws is `≤ c < 1`;
* `dominated` — the **realizability** obligation: each `(Q j)`-probability of missing
  `θ j` by `s` is dominated by the in-class minimax miss probability.  This is what a
  concrete construction discharges by writing `Q j` as a mixture of `n`-fold product
  laws of DGPs in the class, all sharing ATE `θ j` (so an average is `≤` the supremum).

Given such a witness, `twoPointWitness_lower_bound` concludes

  `(1 − c) / 2 ≤ minimaxMiss …`,

via `Causalean.Stat.two_point_lower_bound_of_tvDist_le`.  In particular a witness with
`c ≤ 1/2` forces every estimator to miss the truth by `s` with probability `≥ 1/4`
somewhere in the class (`twoPointWitness_quarter`).

The construction of an explicit witness with `s ≍ √εg · √εm` (the doubly-robust
product rate) and `c ≤ 1/2` in the regime `n · εg · εm ≲ 1` is the genuine
research content of the paper (the Ingster χ² / fuzzy-hypothesis step); this file
is correct regardless of how the witness is built.
-/

import Causalean.Estimation.MinimaxATE.Model
import Causalean.Stat.Minimax.MinimaxRisk

/-! # Two-Point Reduction

This file defines the abstract two-point witness used in structure-agnostic ATE lower bounds.
It turns a pair of statistically close sample laws with separated ATEs and in-class
realizability into a minimax lower bound for the worst-case probability of estimator error.

The structure `TwoPointWitness` packages the two sample laws, their ATE labels, a separation
half-scale, a total-variation budget, and the domination condition connecting each witness law to
`minimaxMiss`.  The theorem `twoPointWitness_lower_bound` gives the Le Cam lower bound
`(1 - c) / 2`, and `twoPointWitness_quarter` specializes it to the common `c ≤ 1/2` case used by
the explicit minimax constructions. -/

namespace Causalean.Estimation.MinimaxATE

open MeasureTheory
open Causalean.Stat
open scoped ENNReal BigOperators

variable {C : Type*} [Fintype C] [Nonempty C] [MeasurableSpace C]

/-- **Two-point (Le Cam) witness** for the structure-agnostic ATE lower bound.

`s` is the separation half-scale, `c` the total-variation budget, `Q j` the
`n`-sample data law of hypothesis `j : Bool`, and `θ j` its true ATE.  The
`dominated` field is the realizability obligation linking the two laws back to the
class: it is discharged by a mixture-of-in-class-DGPs construction. -/
structure TwoPointWitness (C : Type*) [Fintype C] [Nonempty C] [MeasurableSpace C]
    (n : ℕ) (mhat : C → ℝ) (ghat : Bool → C → ℝ) (εg εm : ℝ) where
  /-- Separation half-scale (a concrete witness achieves `s ≍ √εg · √εm`). -/
  s : ℝ
  /-- Total-variation budget between the two `n`-sample laws (`c < 1` is what bites). -/
  c : ℝ
  /-- The `n`-sample data law of each hypothesis. -/
  Q : Bool → Measure (Fin n → Obs C)
  /-- Each law is a probability measure. -/
  prob : ∀ j, IsProbabilityMeasure (Q j)
  /-- The true ATE attached to each hypothesis. -/
  θ : Bool → ℝ
  /-- The two ATE values are `2s`-separated. -/
  sep : 2 * s ≤ |θ true - θ false|
  /-- The two laws are statistically close: `tvDist ≤ c`. -/
  tvBound : tvDist (Q false) (Q true) ≤ c
  /-- **Realizability.** For every estimator, the probability under `Q j` of missing
  `θ j` by `s` is dominated by the in-class minimax miss probability.  A mixture
  witness discharges this because an average of in-class miss probabilities is at
  most their supremum. -/
  dominated : ∀ (est : (Fin n → Obs C) → ℝ) (j : Bool),
    (Q j).real {x | s ≤ |est x - θ j|} ≤ minimaxMiss mhat ghat εg εm n est s

variable {n : ℕ} {mhat : C → ℝ} {ghat : Bool → C → ℝ} {εg εm : ℝ}

/-- **Structure-agnostic two-point lower bound.**  From a `TwoPointWitness`, every
measurable estimator's worst-case-over-class probability of missing the true ATE by
`W.s` is at least `(1 − W.c)/2`.  The proof is `two_point_lower_bound_of_tvDist_le`
applied to the two witness laws, followed by the realizability domination. -/
theorem twoPointWitness_lower_bound
    (W : TwoPointWitness C n mhat ghat εg εm)
    {est : (Fin n → Obs C) → ℝ} (hest : Measurable est) :
    (1 - W.c) / 2 ≤ minimaxMiss mhat ghat εg εm n est W.s := by
  haveI := W.prob false
  haveI := W.prob true
  have hsep : 2 * W.s ≤ |W.θ false - W.θ true| := by
    rw [abs_sub_comm]; exact W.sep
  have h := Causalean.Stat.two_point_lower_bound_of_tvDist_le
    (P₀ := W.Q false) (P₁ := W.Q true) hest hsep W.tvBound
  refine h.trans ?_
  rw [max_le_iff]
  exact ⟨W.dominated est false, W.dominated est true⟩

/-- A witness with total-variation budget `c ≤ 1/2` forces every estimator to miss
the true ATE by `W.s` with probability at least `1/4` somewhere in the class. -/
theorem twoPointWitness_quarter
    (W : TwoPointWitness C n mhat ghat εg εm) (hc : W.c ≤ 1 / 2)
    {est : (Fin n → Obs C) → ℝ} (hest : Measurable est) :
    1 / 4 ≤ minimaxMiss mhat ghat εg εm n est W.s := by
  refine le_trans ?_ (twoPointWitness_lower_bound W hest)
  linarith

end Causalean.Estimation.MinimaxATE
