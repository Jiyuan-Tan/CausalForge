/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# I.i.d. sample model

Causal-agnostic statistical primitive: an i.i.d. sample on a single ambient
probability space, matching Mathlib's `iIndepFun` / `IdentDistrib` idiom rather
than the product-space construction.  See `def:est-iid-sample` in
`doc/basic_concepts/po/estimation.tex`.

This file is intentionally project-agnostic and is a candidate for upstream
contribution to Mathlib.
-/

import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace

/-! # I.i.d. Samples

This file provides the library's causal-agnostic model of an independent and
identically distributed sample on a common ambient probability space. It also
defines sample means of real-valued statistics along the first \(n\) sample
points, supplying the base object used by the limit and inference modules. -/

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory

/-- An independent and identically distributed sample with marginal law `P`, realized as
[a sequence of sample points](hyp:Z) given by [measurable maps](hyp:meas) on a single
ambient probability space: [the family is mutually independent](hyp:indep), [identically
distributed](hyp:identDist), and [the law of each point is the population law `P`](hyp:law).

* `Z i : Ω → X`             — the `i`-th sample point.
* `meas`                    — measurability of each `Z i`.
* `indep`                   — mutual independence of the family under `μ`.
* `identDist`               — every `Z i` is identically distributed with `Z 0`.
* `law`                     — the law of `Z 0` matches the population law `P`.

Together, `identDist` and `law` give `μ.map (Z i) = P` for all `i`. -/
structure IIDSample (Ω X : Type*) [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) (P : Measure X) where
  Z : ℕ → Ω → X
  meas      : ∀ i, Measurable (Z i)
  indep     : iIndepFun Z μ
  identDist : ∀ i, IdentDistrib (Z 0) (Z i) μ μ
  law       : (μ.map (Z 0)) = P

namespace IIDSample

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X}

/-- Each individual sample point of an i.i.d. sample is a measurable map from the ambient
probability space to the observation space.

This is the `meas` field with the sample index instantiated. The field itself is stated for
all indices at once, which the function-property tactics cannot use; this per-index form is
the one they can. -/
@[fun_prop]
theorem measurable_Z (S : IIDSample Ω X μ P) (i : ℕ) : Measurable (S.Z i) := S.meas i

/-- Sample mean of a real-valued statistic `f` along the sample's first `n`
points: `(1/n) Σ_{i < n} f (Z i ω)`. -/
noncomputable def sampleMean (S : IIDSample Ω X μ P) (f : X → ℝ) (n : ℕ) :
    Ω → ℝ :=
  fun ω => (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, f (S.Z i ω)

/-- For [an i.i.d. sample `S`](hyp:S) [and any sample index `i`](hyp:i), [the pushforward law of
the `i`-th sample point equals the population law `P`](goal). -/
theorem map_eq (S : IIDSample Ω X μ P) (i : ℕ) : μ.map (S.Z i) = P := by
  rw [← (S.identDist i).map_eq, S.law]

end IIDSample

end Causalean.Stat
