/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.UniformSpace.UniformApproximation

/-!
# Deterministic argmax stability

This module proves convergence of exact maximizers from uniform convergence on
an eventually common compact set and uniqueness of the limiting maximizer.
-/

open Filter Set Topology

namespace Causalean.Stat

-- @node: tendsto_argmax_of_eventually_mem_compact
/-- Maximizers of uniformly convergent criteria converge to the unique limiting
maximizer when they eventually lie in one compact set. -/
lemma tendsto_argmax_of_eventually_mem_compact {E : Type*} [PseudoMetricSpace E]
    [SecondCountableTopology E]
    (criterion : ℕ → E → ℝ) (limitCriterion : E → ℝ)
    (argmax : ℕ → E) (limitArgmax : E) (K : Set E)
    (hK : IsCompact K) (hLimitMem : limitArgmax ∈ K)
    (hLimitContinuous : ContinuousOn limitCriterion K)
    (hLimitMax : ∀ y ∈ K, limitCriterion y ≤ limitCriterion limitArgmax)
    (hUniform : TendstoUniformlyOn criterion limitCriterion atTop K)
    (hArgmaxMem : ∀ᶠ N in atTop, argmax N ∈ K)
    (hArgmax : ∀ᶠ N in atTop, ∀ y ∈ K,
      criterion N y ≤ criterion N (argmax N))
    (hUnique : ∀ y ∈ K, limitCriterion y = limitCriterion limitArgmax →
      y = limitArgmax) :
    Tendsto argmax atTop (nhds limitArgmax) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  let S : Set E := K ∩ {y | ε ≤ dist y limitArgmax}
  have hScompact : IsCompact S := by
    apply hK.inter_right
    exact isClosed_le continuous_const (continuous_id.dist continuous_const)
  by_cases hSne : S.Nonempty
  · obtain ⟨z, hzS, hzmax⟩ :=
      hScompact.exists_isMaxOn hSne (hLimitContinuous.mono inter_subset_left)
    have hzK : z ∈ K := hzS.1
    have hzlt : limitCriterion z < limitCriterion limitArgmax := by
      refine lt_of_le_of_ne (hLimitMax z hzK) ?_
      intro heq
      have hzl := hUnique z hzK heq
      subst z
      have : ε ≤ 0 := by simpa using hzS.2
      exact (not_le_of_gt hε) this
    let d := (limitCriterion limitArgmax - limitCriterion z) / 3
    have hd : 0 < d := div_pos (sub_pos.mpr hzlt) (by norm_num)
    have hU := (Metric.tendstoUniformlyOn_iff.mp hUniform d hd)
    have hevent : ∀ᶠ N in atTop, dist (argmax N) limitArgmax < ε := by
      filter_upwards [hU, hArgmaxMem, hArgmax] with N hUN hmem hmax
      by_contra hdist
      have hargS : argmax N ∈ S :=
        ⟨hmem, le_of_not_gt hdist⟩
      have hlimerr := hUN limitArgmax hLimitMem
      have hargerr := hUN (argmax N) hmem
      have hzbound := hzmax hargS
      change limitCriterion (argmax N) ≤ limitCriterion z at hzbound
      have hselected := hmax limitArgmax hLimitMem
      rw [Real.dist_eq] at hlimerr hargerr
      dsimp [d] at hd hlimerr hargerr
      linarith [abs_lt.mp hlimerr, abs_lt.mp hargerr]
    exact Filter.eventually_atTop.1 hevent
  · have hinside : ∀ y ∈ K, dist y limitArgmax < ε := by
      intro y hy
      by_contra h
      exact hSne ⟨y, hy, le_of_not_gt h⟩
    have hevent : ∀ᶠ N in atTop, dist (argmax N) limitArgmax < ε := by
      filter_upwards [hArgmaxMem] with N hN
      exact hinside (argmax N) hN
    exact Filter.eventually_atTop.1 hevent

end Causalean.Stat
