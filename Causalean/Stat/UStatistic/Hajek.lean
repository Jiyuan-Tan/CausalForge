/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Generic `o_p` transfer helper

This file holds `isLittleOp_of_eventuallyEq`, a generic lemma transferring the
`o_p(rₙ)` property along an eventual pointwise equality of sequences.

The order-2 Hájek decomposition and U-statistic central limit theorem that used
to live here have been superseded by the fixed-order-`m` theory
(`Causalean.Stat.UStatistic.OrderM.CLT`), whose `m = 2` specialization
`uStatistic_clt_of_symmetric_via_orderM` (`OrderM.OrderTwo`) reproduces the order-2
CLT; the bespoke order-2 proofs were removed as redundant.  The exact order-2
variance substrate consumed by the higher-order influence-function estimators lives
in `Causalean.Stat.UStatistic.Variance`.
-/

import Causalean.Stat.Limit.Convergence

/-!
# Generic `o_p` transfer helper

This module provides `isLittleOp_of_eventuallyEq`, a generic transfer lemma that
carries an `o_p` rate across eventual pointwise equality of stochastic
sequences.  The result is used by U-statistic and asymptotic-linearization
arguments when a normalized remainder is replaced by an eventually identical
normal form.

The fixed-order U-statistic Hájek expansion and CLT live in the `OrderM`
subtree; this file remains as the small rate-transfer utility needed by that
development and related statistical limit arguments.
-/

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Transfer `o_p` along an eventual pointwise equality of the sequences. -/
theorem isLittleOp_of_eventuallyEq {f g : ℕ → Ω → ℝ} {r : ℕ → ℝ}
    (hg : IsLittleOp g r μ) (hfg : ∀ᶠ n in atTop, f n = g n) :
    IsLittleOp f r μ := by
  intro ε hε
  refine (hg ε hε).congr' ?_
  filter_upwards [hfg] with n hn
  rw [hn]

end Causalean.Stat
