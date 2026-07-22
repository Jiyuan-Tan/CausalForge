/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Two-state Markov transition matrix and geometric ergodicity

This file studies the two-state Markov chain on `Fin 2` with transition rows
`(1 - a, a)` and `(b, 1 - b)`. It provides:

* `transitionMatrix a b` — the 2×2 row-stochastic matrix above.
* `stationaryProjection a b` — the rank-one projector whose rows both equal
  the stationary distribution `(b/(a+b), a/(a+b))`.
* `transitionMatrix_pow_eq_spectral` — spectral decomposition
  `M^k = Π + (1 - a - b)^k • (1 - Π)` on the open transition square.
* `one_minus_a_b_abs_lt_one` — pointwise spectral gap on `(0,1)²`.
* `one_minus_a_b_uniform_gap_on_compact` — uniform spectral gap on compact
  subsets of the open square (via `IsCompact.exists_isMaxOn`).
* `transitionMatrix_pow_tendsto_stationary_uniform` - entrywise geometric
  convergence `M^k → Π`, uniform on compact subsets of the open square.

The results are project-generic finite-state Markov-chain facts and depend only
on Mathlib.
-/

import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Real.StarOrdered

/-! # Two-State Markov Chains

This file develops `transitionMatrix`, `stationaryProjection`,
`transitionMatrix_pow_eq_spectral`, the pointwise and compact-uniform spectral
gap bounds, and `transitionMatrix_pow_tendsto_stationary_uniform` for a
two-state Markov chain with transition probabilities in the open unit square. -/

open scoped BigOperators
open Filter Matrix

namespace Causalean
namespace Mathlib
namespace TwoStateMarkov

/-- Transition matrix with rows `(1 - a, a)` and `(b, 1 - b)`. -/
noncomputable def transitionMatrix (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j =>
    if i = (0 : Fin 2) then
      if j = (0 : Fin 2) then 1 - a else a
    else
      if j = (0 : Fin 2) then b else 1 - b

/-- Stationary projection with both rows equal to `(b/(a+b), a/(a+b))`. -/
noncomputable def stationaryProjection (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun _ j => if j = (0 : Fin 2) then b / (a + b) else a / (a + b)

/-- Spectral decomposition of the two-state transition matrix:
`M(a,b)^k = Π(a,b) + (1 - a - b)^k • (1 - Π(a,b))`. -/
theorem transitionMatrix_pow_eq_spectral
    (a b : ℝ) (ha_pos : 0 < a) (ha_lt_one : a < 1)
    (hb_pos : 0 < b) (hb_lt_one : b < 1) :
    ∀ k : ℕ,
      (transitionMatrix a b) ^ k =
        stationaryProjection a b +
          ((1 - a - b) ^ k) • (1 - stationaryProjection a b) := by
  have _ : a < 1 := ha_lt_one
  have _ : b < 1 := hb_lt_one
  let P := stationaryProjection a b
  let Q : Matrix (Fin 2) (Fin 2) ℝ := 1 - P
  let lam := 1 - a - b
  have hs : a + b ≠ 0 := by positivity
  have hM : transitionMatrix a b = P + lam • Q := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [P, Q, lam, transitionMatrix, stationaryProjection, Matrix.smul_apply,
        Matrix.sub_apply, Matrix.add_apply] <;>
      field_simp [hs] <;> ring
  have hP2 : P * P = P := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [P, stationaryProjection, Matrix.mul_apply, Fin.sum_univ_two] <;>
      field_simp [hs] <;> ring
  have hPQ : P * Q = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [P, Q, stationaryProjection, Matrix.mul_apply, Matrix.sub_apply,
        Matrix.one_apply, Fin.sum_univ_two] <;>
      field_simp [hs] <;> ring
  have hQP : Q * P = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [P, Q, stationaryProjection, Matrix.mul_apply, Matrix.sub_apply,
        Matrix.one_apply, Fin.sum_univ_two] <;>
      field_simp [hs] <;> ring
  have hQ2 : Q * Q = Q := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [P, Q, stationaryProjection, Matrix.mul_apply, Matrix.sub_apply,
        Matrix.one_apply, Fin.sum_univ_two] <;>
      field_simp [hs] <;> ring
  intro k
  induction k with
  | zero =>
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [stationaryProjection, Matrix.add_apply, Matrix.sub_apply]
  | succ k ih =>
      calc
        transitionMatrix a b ^ (k + 1)
            = (P + (lam ^ k) • Q) * (P + lam • Q) := by rw [pow_succ, ih, hM]
        _ = P + (lam ^ (k + 1)) • Q := by
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [P, Q, lam, stationaryProjection, Matrix.mul_apply, Matrix.add_apply,
              Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Fin.sum_univ_two,
              pow_succ] <;>
            field_simp [hs] <;> ring

/-- Pointwise spectral gap on the open square: `|1 - a - b| < 1` whenever
`(a,b) ∈ (0,1)²`. -/
theorem one_minus_a_b_abs_lt_one
    {a b : ℝ} (ha_pos : 0 < a) (hb_pos : 0 < b)
    (ha_lt_one : a < 1) (hb_lt_one : b < 1) :
    |1 - a - b| < 1 := by
  by_cases hle : a + b ≤ 1
  · rw [abs_of_nonneg (by linarith)]
    linarith
  · have hgt : 1 < a + b := lt_of_not_ge hle
    rw [abs_of_neg (by linarith)]
    linarith

/-- Uniform spectral gap on compact subsets of the open square: the continuous
function `(a,b) ↦ |1 - a - b|` attains its supremum on a compact `K ⊆ (0,1)²`
at some point of `K`, and that supremum is strictly less than `1` by the
pointwise bound. -/
theorem one_minus_a_b_uniform_gap_on_compact
    (K : Set (ℝ × ℝ)) (hK_compact : IsCompact K)
    (hK_open : K ⊆ {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < 1 ∧ 0 < p.2 ∧ p.2 < 1}) :
    ∃ ρ : ℝ, ρ < 1 ∧ ∀ p ∈ K, |1 - p.1 - p.2| ≤ ρ := by
  by_cases hne : K.Nonempty
  · let f : ℝ × ℝ → ℝ := fun p => |1 - p.1 - p.2|
    have hf : ContinuousOn f K := by
      dsimp [f]
      fun_prop
    rcases hK_compact.exists_isMaxOn hne hf with ⟨pstar, hpstar, hpmax⟩
    have hopen := hK_open hpstar
    have hmax_lt : f pstar < 1 := by
      dsimp [f]
      exact one_minus_a_b_abs_lt_one hopen.1 hopen.2.2.1 hopen.2.1 hopen.2.2.2
    refine ⟨(f pstar + 1) / 2, ?_, ?_⟩
    · linarith
    · intro p hp
      have hle : f p ≤ f pstar := isMaxOn_iff.mp hpmax p hp
      dsimp [f] at hle ⊢
      linarith
  · refine ⟨0, by norm_num, ?_⟩
    intro p hp
    exact False.elim (hne ⟨p, hp⟩)

/-- Uniform geometric convergence to the stationary projection on compact subsets
of the open transition-parameter square.  Combines the spectral decomposition
with the uniform spectral gap: the `(1 - a - b)^k` factor decays at rate
`ρ^k` uniformly on `K`, while the entries of `1 - Π(a,b)` are continuous on
the open square and hence bounded on the compact `K`. -/
theorem transitionMatrix_pow_tendsto_stationary_uniform
    (K : Set (ℝ × ℝ)) (hK_compact : IsCompact K)
    (hK_open : K ⊆ {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < 1 ∧ 0 < p.2 ∧ p.2 < 1}) :
    ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      ∀ p ∈ K, ∀ i j : Fin 2,
        |((transitionMatrix p.1 p.2) ^ k - stationaryProjection p.1 p.2) i j| ≤ ε := by
  intro ε hε
  classical
  by_cases hne : K.Nonempty
  · obtain ⟨ρ, hρ_lt, hρ_bound⟩ :=
      one_minus_a_b_uniform_gap_on_compact K hK_compact hK_open
    rcases hne with ⟨p0, hp0⟩
    have hρ_nonneg : 0 ≤ ρ :=
      (abs_nonneg (1 - p0.1 - p0.2)).trans (hρ_bound p0 hp0)
    have htend := tendsto_pow_atTop_nhds_zero_of_lt_one hρ_nonneg hρ_lt
    have hevent : ∀ᶠ k in Filter.atTop, ρ ^ k < ε := htend.eventually_lt_const hε
    rw [Filter.eventually_atTop] at hevent
    rcases hevent with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro k hk p hp i j
    have hopen := hK_open hp
    have ha_pos : 0 < p.1 := hopen.1
    have hb_pos : 0 < p.2 := hopen.2.2.1
    have hs_pos : 0 < p.1 + p.2 := by linarith
    have hs : p.1 + p.2 ≠ 0 := ne_of_gt hs_pos
    have hqa : |p.1 / (p.1 + p.2)| ≤ 1 := by
      rw [abs_of_nonneg (div_nonneg ha_pos.le hs_pos.le)]
      rw [div_le_one hs_pos]
      linarith
    have hqb : |p.2 / (p.1 + p.2)| ≤ 1 := by
      rw [abs_of_nonneg (div_nonneg hb_pos.le hs_pos.le)]
      rw [div_le_one hs_pos]
      linarith
    have hQ_le : |(1 - stationaryProjection p.1 p.2) i j| ≤ 1 := by
      fin_cases i <;> fin_cases j
      · have h : 1 - p.2 / (p.1 + p.2) = p.1 / (p.1 + p.2) := by
          field_simp [hs]
          ring
        simpa [stationaryProjection, Matrix.sub_apply, h] using hqa
      · simpa [stationaryProjection, Matrix.sub_apply, abs_neg] using hqa
      · simpa [stationaryProjection, Matrix.sub_apply, abs_neg] using hqb
      · have h : 1 - p.1 / (p.1 + p.2) = p.2 / (p.1 + p.2) := by
          field_simp [hs]
          ring
        simpa [stationaryProjection, Matrix.sub_apply, h] using hqb
    have hentry :
        ((transitionMatrix p.1 p.2) ^ k - stationaryProjection p.1 p.2) i j =
          (1 - p.1 - p.2) ^ k * (1 - stationaryProjection p.1 p.2) i j := by
      have hspec :=
        transitionMatrix_pow_eq_spectral p.1 p.2 ha_pos hopen.2.1 hb_pos hopen.2.2.2 k
      calc
        ((transitionMatrix p.1 p.2) ^ k - stationaryProjection p.1 p.2) i j
            =
              (stationaryProjection p.1 p.2 +
                    (1 - p.1 - p.2) ^ k • (1 - stationaryProjection p.1 p.2) -
                  stationaryProjection p.1 p.2) i j := by
                rw [hspec]
        _ = (1 - p.1 - p.2) ^ k * (1 - stationaryProjection p.1 p.2) i j := by
          simp [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply]
    have hgap_pow : |(1 - p.1 - p.2) ^ k| ≤ ρ ^ k := by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg (1 - p.1 - p.2)) (hρ_bound p hp) k
    have hbound :
        |((transitionMatrix p.1 p.2) ^ k - stationaryProjection p.1 p.2) i j| ≤ ρ ^ k := by
      rw [hentry, abs_mul]
      calc
        |(1 - p.1 - p.2) ^ k| * |(1 - stationaryProjection p.1 p.2) i j|
            ≤ ρ ^ k * 1 :=
              mul_le_mul hgap_pow hQ_le (abs_nonneg _) (pow_nonneg hρ_nonneg k)
        _ = ρ ^ k := by ring
    exact hbound.trans (le_of_lt (hN k hk))
  · refine ⟨0, ?_⟩
    intro k hk p hp i j
    exact False.elim (hne ⟨p, hp⟩)

end TwoStateMarkov
end Mathlib
end Causalean
