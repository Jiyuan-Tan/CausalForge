/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Discovery.InvariantPrediction.LinearGaussian.Helpers.Residual

/-!
# Invariant Causal Prediction — non-descendant invariance

The structural backbone of the mean-shift argument (`propos:sem`): under a single
do-intervention `do(X_{k₀} = a)`, every coordinate that is **not a descendant of
`k₀`** and is not `k₀` itself keeps its observational value a.e.

`nonDescendant_invariance` proves, for the single-intervention environment
`e` with `A = {k₀}`, that `e.X ω k = M.X ω k` a.e. for every `k ≠ k₀` with
`¬ dag.isAncestor k₀ k` (i.e. `k` is not a strict descendant of `k₀`).  This
includes nodes incomparable with `k₀` and ancestors of `k₀`, exactly the
"upstream + sideways" part of the graph the intervention cannot reach; the
intervened node `k₀` is excluded because it is pinned to the assigned constant.

The proof is a strong induction along the topological order: each such `k`
satisfies the *same* structural equation in both worlds (`hDoStruct k` vs
`hε k`, since `k ≠ k₀` so `k ∉ A`), and all its parents are also non-descendants
of `k₀` with strictly smaller topological order, so they agree by induction.
-/

namespace Causalean.Discovery.InvariantPrediction.LinearGaussian

open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {p : ℕ}

/-- **Non-descendant invariance.**  For the single do-intervention environment
`e` with `A = {k₀}`, every coordinate `k` that is *neither* `k₀` *nor* a (strict)
descendant of `k₀` keeps its observational value a.e.: `Xₖᵉ = Xₖ¹`.  (The node
`k₀` itself is pinned to the assigned constant, hence excluded.) -/
theorem nonDescendant_invariance (M : ObsSEM p) (e : Env M) (k₀ : Fin (p + 1))
    (hA : e.A = {k₀}) :
    ∀ᵐ ω ∂M.P, ∀ k, k ≠ k₀ → ¬ M.dag.isAncestor k₀ k → e.X ω k = M.X ω k := by
  classical
  -- Combine all the a.e. structural equations (both worlds, all coordinates)
  -- into a single a.e. event.
  have hstruct : ∀ᵐ ω ∂M.P, (∀ k, k ∉ e.A →
        e.X ω k = M.ε ω k + ∑ j ∈ Finset.univ.erase k, M.β k j * e.X ω j) := by
    rw [ae_all_iff]
    intro k
    by_cases hk : k ∈ e.A
    · filter_upwards with ω; intro h; exact absurd hk h
    · filter_upwards [e.hDoStruct k hk] with ω hω _; exact hω
  filter_upwards [hstruct, M.hε] with ω hStruct hEps
  -- Strong induction on the topological order of `k`.
  -- We prove `∀ n k, topoOrder k = n → (k ≠ k₀ → ¬ isAncestor k₀ k → Xₖᵉ = Xₖ¹)`.
  suffices h : ∀ n, ∀ k, M.dag.topoOrder k = n →
      (k ≠ k₀ → ¬ M.dag.isAncestor k₀ k → e.X ω k = M.X ω k) by
    intro k; exact h (M.dag.topoOrder k) k rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro k hk hkk₀ hnonanc
    subst hk
    -- `k ∉ A = {k₀}` because `k ≠ k₀`.
    have hkA : k ∉ e.A := by rw [hA]; simpa using hkk₀
    -- Both worlds' structural equations at `k`.
    have hE := hStruct k hkA
    have hM := hEps k
    -- The two structural sums over the parents agree (parents are non-descendant
    -- of `k₀`, smaller topo order, so equal by induction).
    have hsum : ∑ j ∈ Finset.univ.erase k, M.β k j * e.X ω j
        = ∑ j ∈ Finset.univ.erase k, M.β k j * M.X ω j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_erase] at hj
      obtain ⟨hjk, _⟩ := hj
      -- If `β k j = 0` the terms agree trivially; else `j → k` is an edge.
      by_cases hβ : M.β k j = 0
      · rw [hβ]; ring
      · -- `j` is a parent of `k`: `edge j k`.
        have hedge : M.dag.edge j k := (M.hEdge k j).mpr hβ
        -- `j ≠ k₀`: else `edge k₀ k` ⟹ `isAncestor k₀ k`, contradiction.
        have hjk₀ : j ≠ k₀ := by
          rintro rfl
          exact hnonanc (Causalean.DAG.isAncestor.edge hedge)
        -- `¬ isAncestor k₀ j`: else `isAncestor k₀ j` + `edge j k` ⟹ `isAncestor k₀ k`.
        have hnonanc_j : ¬ M.dag.isAncestor k₀ j := by
          intro hanc
          exact hnonanc (Causalean.DAG.isAncestor.trans hanc hedge)
        -- `topoOrder j < topoOrder k`, so IH applies.
        have hlt : M.dag.topoOrder j < M.dag.topoOrder k := M.dag.topoOrder_lt j k hedge
        rw [IH (M.dag.topoOrder j) hlt j rfl hjk₀ hnonanc_j]
    rw [hE, hM, hsum]; ring

end Causalean.Discovery.InvariantPrediction.LinearGaussian
