/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Schedule grid definitions
-/

import CausalSmith.Experimentation.EXP_RolloutChebyshevMinimax_Research.Basic

namespace CausalSmith.Experimentation.RolloutChebyshev

/-- Equal-spacing benchmark schedule `p^eq(β,q) = (0, q/β, 2q/β, ..., q)` on `β+1` nodes.
Carrier `Fin (β+1) → ℝ` (the closed-form grid). Its core space `p^eq(β,q) ∈ [0,1]^(β+1)` is NOT
free from the formula alone: each coordinate `q·j/β` lies in `[0,q] ⊆ [0,1]` precisely when
`β ≥ 1` and `q ∈ (0,1]`. This range clause is realized by the leading conjunct
`∀ j, p^eq(β,q) j ∈ Set.Icc 0 1` of `equal_spacing_benchmark`'s conclusion, holding under its
hypotheses `1 ≤ β` and `hq : 0 < q ∧ q ≤ 1`. The budget parameter `q` (carrier `q : ℝ`) has
space `(0,1]`, pinned by the same range predicate `hq`.
@realizes p^eq(beta,q)(carrier grid q·j/β;
  range [0,1]^(β+1) via equal_spacing_benchmark Icc conjunct, under β≥1, q∈(0,1])
@realizes q(carrier ℝ; range 0 < q ≤ 1 pinned by equal_spacing_benchmark.hq) -/
noncomputable def equalSchedule (beta : ℕ) (q : ℝ) : Fin (beta + 1) → ℝ :=
  fun j => q * (j : ℝ) / (beta : ℝ)

end CausalSmith.Experimentation.RolloutChebyshev
