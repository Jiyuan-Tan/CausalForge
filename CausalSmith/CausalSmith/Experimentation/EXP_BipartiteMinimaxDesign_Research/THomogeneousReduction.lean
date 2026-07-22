/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Bipartite minimax design: homogeneous reduction (sanity benchmark)

`prop:homogeneous-reduction`. Specializing the heterogeneous overlap loads to a
common scalar `p` recovers the published homogeneous Bernoulli Hájek overlap
variance formula of Lu–Shi–Fang–Zhang–Ding (2025).
-/

import CausalSmith.Experimentation.EXP_BipartiteMinimaxDesign_Research.Helpers.Linearization

set_option linter.style.longLine false

open scoped BigOperators
open Finset
open Causalean.Experimentation.DesignBased
open Causalean.Experimentation.UnknownInterference

namespace CausalSmith.Experimentation.BipartiteMinimaxDesign

variable {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I]

-- @node: prop:homogeneous-reduction
/-- **Homogeneous reduction.** Under the independent heterogeneous Bernoulli design,
if `p_k = p` is a common scalar in `(0,1)`, the treated / control overlap loads
collapse to `p^{-|S_{ij}|} − 1` and `(1−p)^{-|S_{ij}|} − 1`, and the variance scale
equals the homogeneous Bernoulli Hájek overlap formula. -/
theorem homogeneous_reduction
    (E : BipartiteExperiment I O)
    (D : FiniteDesign (I → Bool)) (pc : ℝ) (hpc0 : 0 < pc) (hpc1 : pc < 1)
    (p : I → ℝ) (hp0 : ∀ k, 0 ≤ p k) (hp1 : ∀ k, p k ≤ 1)
    (hconst : ∀ k, p k = pc)
    (hBern : IndepHeteroBernoulli D p hp0 hp1) :
    (∀ i j, E.r1 p i j
        = if 0 < (E.shared i j).card then (pc ^ (E.shared i j).card)⁻¹ - 1 else 0) ∧
    (∀ i j, E.r0 p i j
        = if 0 < (E.shared i j).card then ((1 - pc) ^ (E.shared i j).card)⁻¹ - 1 else 0) ∧
    E.varScale D p
      = (Fintype.card O : ℝ)⁻¹ * ∑ i, ∑ j,
          (E.r1 p i j * (E.Y1 i - E.mu1) * (E.Y1 j - E.mu1)
           + E.r0 p i j * (E.Y0 i - E.mu0) * (E.Y0 j - E.mu0)
           + 2 * E.r10 i j * (E.Y1 i - E.mu1) * (E.Y0 j - E.mu0)) := by
  classical
  have hpos : ∀ k, 0 < p k := by
    intro k
    rw [hconst k]
    exact hpc0
  have hlt : ∀ k, p k < 1 := by
    intro k
    rw [hconst k]
    exact hpc1
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    by_cases h : 0 < (E.shared i j).card <;>
      simp [BipartiteExperiment.r1, h, hconst]
  · intro i j
    by_cases h : 0 < (E.shared i j).card <;>
      simp [BipartiteExperiment.r0, h, hconst]
  · exact varScale_homogeneous_formula E D p hp0 hp1 hpos hlt hBern

end CausalSmith.Experimentation.BipartiteMinimaxDesign
