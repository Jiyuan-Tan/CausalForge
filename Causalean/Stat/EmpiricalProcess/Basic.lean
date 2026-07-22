/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Empirical process: vocabulary for uniform laws of large numbers

Causal-agnostic empirical-process primitives for an `Causalean.Stat.IIDSample`,
written for the econometrics workflow (van der Vaart 1998, Ch. 19; Newey &
McFadden 1994, §2).  A *function class* is an indexed family `f : ι → X → ℝ`;
the empirical process measures how far the sample means `Pₙ f_i` are from the
population means `P f_i = ∫ f_i dP`, *uniformly over the class*.

This file fixes the vocabulary; the uniform law of large numbers (Glivenko–
Cantelli) is proved in `GlivenkoCantelli.lean` and consumed by
`MEstimatorConsistency.lean`.

Main definitions:

* `IIDSample.empiricalProcess f i n` — the centred-and-scaled process
  `√n · (Pₙ f_i − P f_i)` at class member `i`.
* `IIDSample.supDeviation f n` — the finite-class sup deviation
  `⨆ i, |Pₙ f_i − P f_i|` (used as a convenient real-valued statistic when `ι`
  is finite).
* `GlivenkoCantelli S f` — the (weak) uniform law of large numbers: for every
  `ε > 0`, the probability that *some* class member deviates by `≥ ε` tends to
  `0`.  Phrased with an existential rather than `⨆` so it is meaningful for
  infinite (uncountable) classes without lattice-junk artefacts.
* `L1Bracketing f P ε` — a finite `L¹(P)` `ε`-bracketing of the class: finitely
  many `[lo j, hi j]` brackets with `∫ |hi j − lo j| dP ≤ ε`, together with a
  common full-measure support on which every class member is sandwiched.  The
  bracketing number being finite at every `ε` is the classical sufficient
  condition for Glivenko–Cantelli.
-/

import Causalean.Stat.Sample
import Causalean.Stat.Limit.Convergence
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Empirical Process Basics

This file introduces the empirical-process vocabulary for uniform laws of large
numbers over indexed classes of real-valued functions.  It defines
`IIDSample.empiricalProcess`, `IIDSample.supDeviation`, the weak uniform law
predicate `GlivenkoCantelli`, the finite-bracketing structure `L1Bracketing`,
and the arbitrary-small-bracketing hypothesis `HasL1Bracketing` consumed by the
Glivenko-Cantelli and M-estimator consistency files. -/

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω X ι : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X}

namespace IIDSample

/-- **Empirical process** of the class member `f i` at sample size `n`:
`√n · ((1/n) Σ_{k<n} f_i(Z_k) − ∫ f_i dP)`.  The object whose weak limit
(a Gaussian process) is the subject of Donsker theory. -/
noncomputable def empiricalProcess (S : IIDSample Ω X μ P) (f : ι → X → ℝ)
    (i : ι) (n : ℕ) : Ω → ℝ :=
  fun ω => Real.sqrt (n : ℝ) * (S.sampleMean (f i) n ω - ∫ x, f i x ∂P)

/-- **Finite-class sup deviation**: `⨆ i, |Pₙ f_i − P f_i|`.  Meaningful as a
real-valued statistic when the class `ι` is finite (otherwise the `⨆` may
collapse to `0` on an unbounded family, which is why `GlivenkoCantelli` is
stated existentially instead). -/
noncomputable def supDeviation (S : IIDSample Ω X μ P) (f : ι → X → ℝ)
    (n : ℕ) : Ω → ℝ :=
  fun ω => ⨆ i, |S.sampleMean (f i) n ω - ∫ x, f i x ∂P|

end IIDSample

/-- **(Weak) Glivenko–Cantelli property.**  The class `f : ι → X → ℝ` obeys a
uniform law of large numbers for the sample `S`: for every `ε > 0`, the
probability that some class member's empirical mean deviates from its
population mean by at least `ε` tends to `0`.

The existential formulation `{ω | ∃ i, ε ≤ |Pₙ f_i − P f_i|}` (rather than
`{ω | ε ≤ supDeviation}`) is robust to infinite classes and matches how the
property is consumed in `MEstimatorConsistency.lean`. -/
def GlivenkoCantelli (S : IIDSample Ω X μ P) (f : ι → X → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    Tendsto
      (fun n => μ {ω | ∃ i, ε ≤ |S.sampleMean (f i) n ω - ∫ x, f i x ∂P|})
      atTop (𝓝 0)

/-- A finite `L¹(P)` `ε`-bracketing of a real-valued function class consists of
finitely many integrable lower and upper endpoints, a common full-measure
support on which every class member is sandwiched by its assigned bracket, and
an integrated absolute bracket width at most `ε`.

This is the standard almost-everywhere `L¹(P)` bracketing formulation: the
sandwich inequalities need hold only on a single `P`-full support set, and the
width of a bracket is measured by `∫ |hi − lo| dP`. -/
structure L1Bracketing (f : ι → X → ℝ) (P : Measure X) (ε : ℝ) where
  /-- Number of brackets. -/
  m : ℕ
  /-- Lower endpoints. -/
  lo : Fin m → X → ℝ
  /-- Upper endpoints. -/
  hi : Fin m → X → ℝ
  lo_meas : ∀ j, Measurable (lo j)
  hi_meas : ∀ j, Measurable (hi j)
  lo_int : ∀ j, Integrable (lo j) P
  hi_int : ∀ j, Integrable (hi j) P
  /-- Common measurable support on which all bracket inequalities hold. -/
  support : Set X
  support_meas : MeasurableSet support
  /-- The common support has full `P`-measure. -/
  support_ae : ∀ᵐ x ∂P, x ∈ support
  /-- Bracket assigned to each class member. -/
  assign : ι → Fin m
  lo_le : ∀ i, ∀ x ∈ support, lo (assign i) x ≤ f i x
  le_hi : ∀ i, ∀ x ∈ support, f i x ≤ hi (assign i) x
  /-- Each bracket has `L¹(P)` width at most `ε`. -/
  mesh : ∀ j, ∫ x, |hi j x - lo j x| ∂P ≤ ε

/-- A real-valued function class has finite `L¹(P)` brackets of arbitrarily
small width.

For every positive tolerance, there is a finite collection of integrable lower
and upper endpoints whose absolute gap has `P`-integral at most that tolerance,
and every class member is sandwiched by one bracket on a common full-measure
support. This is the standard bracketing hypothesis for the
Glivenko-Cantelli theorem. -/
def HasL1Bracketing (f : ι → X → ℝ) (P : Measure X) : Prop :=
  ∀ ε : ℝ, 0 < ε → Nonempty (L1Bracketing f P ε)

end Causalean.Stat
