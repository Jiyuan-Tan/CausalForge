/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Order.Partition.Finpartition

/-!
# Cumulants of real random variables, and the Gaussian-law predicate

This module provides the general moment-to-cumulant coordinates used throughout the
moment-problem layer: the joint cumulant of a pair of real random variables at a given
bidegree (defined by the set-partition Möbius formula on mixed moments), the univariate
cumulant of a single real random variable obtained by specializing it, and the predicate
"this law on the real line is a Gaussian law".

These are the plain textbook objects: the second cumulant is the variance, the third is the
centered third moment, the fourth is the excess kurtosis, and a Gaussian law is exactly a law
whose cumulants above order two all vanish.  The Gaussian predicate here is the *distributional*
one — being some `gaussianReal` with a mean and a variance, degenerate Diracs included — and is
the form in which non-Gaussianity assumptions (as in linear non-Gaussian causal discovery) are
stated.
-/

namespace Causalean.Stat.MomentProblems

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A probability law on the real line is a **Gaussian law** when it is a normal distribution:
there is a mean and a (possibly zero) variance whose normal distribution is exactly this law.
Allowing zero variance means the point masses (Diracs) count as degenerate Gaussians, so the
negation "not a Gaussian law" is the strongest possible non-Gaussianity requirement. -/
def IsGaussianLaw (ν : Measure ℝ) : Prop :=
  ∃ (mean : ℝ) (v : ℝ≥0), ν = gaussianReal mean v

/-- The **joint cumulant** of two real random variables at bidegree `(p, q)`: the cumulant of the
first variable taken `p` times together with the second taken `q` times.  It is obtained from the
mixed moments by the classical set-partition (Möbius) inversion — sum over all partitions of the
`p + q` slots of a signed factorial weight times the product, over the blocks of the partition, of
the mixed moment matching how many first-variable and second-variable slots that block contains.

For centered variables this reproduces the familiar formulae: bidegree `(2, 0)` is the variance,
`(1, 1)` is the covariance, and bidegree `(4, 0)` is the excess kurtosis. -/
noncomputable def jointCumulant (μ : Measure Ω) (X Y : Ω → ℝ) (p q : ℕ) : ℝ :=
  ∑ π : Finpartition (Finset.univ : Finset (Fin (p + q))),
    (-1 : ℝ) ^ (π.parts.card - 1) * (Nat.factorial (π.parts.card - 1) : ℝ) *
      ∏ B ∈ π.parts,
        ∫ ω, (X ω) ^ (B.filter (fun i => i.val < p)).card
              * (Y ω) ^ (B.filter (fun i => p ≤ i.val)).card ∂μ

/-- The **cumulant of order `r`** of a single real random variable: the joint cumulant of the
variable with itself in which every slot is filled by that one variable.  Order two is the
variance, order three the centered third moment, order four the excess kurtosis. -/
noncomputable def sourceCumulant (μ : Measure Ω) (S : Ω → ℝ) (r : ℕ) : ℝ :=
  jointCumulant μ S S r 0

end Causalean.Stat.MomentProblems
