/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Mathlib.Optimization.SimplexActiveSetDefs

/-! # The κ = 0 exposed face

At `κ = 0` the objective `wsObj α β 0` is the linear functional `Σ αᵢ tᵢ`, whose
minimizers over `Δ_M` are exactly the exposed `α`-minimizing face `exposedMinFace`. -/

namespace Causalean.Mathlib.Optimization

open scoped BigOperators

/-- At `κ = 0` the weighted-simplex objective collapses to the linear form
`Σ αᵢ tᵢ`. -/
lemma wsObj_kappa_zero (α β : Fin 3 → ℝ) (t : Fin 3 → ℝ) :
    wsObj α β 0 t = ∑ i, α i * t i := by
  simp [wsObj]

/-- **The `κ = 0` minimizer set is the exposed `α`-minimizing face.** A point of
`Δ_M` minimizes the linear objective `Σ αᵢ tᵢ` over `Δ_M` iff it is supported only on
the `α`-minimizing coordinates.
Proof plan: pick `k` with `α k = min_j α j` (`Finite.exists_min`). Write
`m₀ = α k`.
* (→) If `t` minimizes, testing against the vertex `M • eₖ ∈ Δ_M` (value `M·m₀`) gives
  `Σ αᵢ tᵢ ≤ M m₀ = Σ m₀ tᵢ`, so `Σ (αᵢ − m₀) tᵢ ≤ 0`; but every summand is `≥ 0`
  (`αᵢ ≥ m₀`, `tᵢ ≥ 0`), forcing each `(αᵢ − m₀) tᵢ = 0`. Hence `tᵢ ≠ 0 ⇒ αᵢ = m₀ ≤ αⱼ`.
* (←) If `t ∈ exposedMinFace`, then `Σ αᵢ tᵢ = Σ m₀ tᵢ = M m₀` (each nonzero coord has
  `αᵢ = m₀`), and for any `s ∈ Δ_M`, `Σ αⱼ sⱼ ≥ Σ m₀ sⱼ = M m₀`. -/
lemma kappa_zero_face (M : ℝ) (hM : 0 < M) (α β : Fin 3 → ℝ) (t : Fin 3 → ℝ) :
    (InSimplex M t ∧
        ∀ s : Fin 3 → ℝ, InSimplex M s → wsObj α β 0 t ≤ wsObj α β 0 s)
      ↔ t ∈ exposedMinFace M α := by
  classical
  obtain ⟨k, hk⟩ := (Finite.exists_min α : ∃ k, ∀ i, α k ≤ α i)
  constructor
  · rintro ⟨htS, hmin⟩
    refine ⟨htS, ?_⟩
    intro i hti j
    let v : Fin 3 → ℝ := fun i => if i = k then M else 0
    have hM_nonneg : 0 ≤ M := le_of_lt hM
    have hv : InSimplex M v := by
      constructor
      · intro i
        dsimp [v]
        by_cases hi : i = k
        · simp [hi, hM_nonneg]
        · simp [hi]
      · dsimp [v]
        fin_cases k <;> simp [Fin.sum_univ_three]
    have hv_sum : ∑ i, α i * v i = α k * M := by
      dsimp [v]
      fin_cases k <;> simp
    have ht_le : ∑ i, α i * t i ≤ α k * M := by
      have h := hmin v hv
      rw [wsObj_kappa_zero, wsObj_kappa_zero] at h
      simpa [hv_sum] using h
    have hsum_diff_le : ∑ i, (α i - α k) * t i ≤ 0 := by
      have hconst : ∑ i, α k * t i = α k * M := by
        rw [← Finset.mul_sum, htS.2]
      calc
        ∑ i, (α i - α k) * t i
            = ∑ i, α i * t i - ∑ i, α k * t i := by
              simp_rw [sub_mul]
              rw [Finset.sum_sub_distrib]
        _ = ∑ i, α i * t i - α k * M := by rw [hconst]
        _ ≤ 0 := by linarith
    have hterm_nonneg (i : Fin 3) : 0 ≤ (α i - α k) * t i := by
      exact mul_nonneg (sub_nonneg.mpr (hk i)) (htS.1 i)
    have hsum_three :
        (α 0 - α k) * t 0 + (α 1 - α k) * t 1 + (α 2 - α k) * t 2 ≤ 0 := by
      simpa [Fin.sum_univ_three] using hsum_diff_le
    have hterm0 : (α 0 - α k) * t 0 = 0 := by
      have h0 := hterm_nonneg 0
      have h1 := hterm_nonneg 1
      have h2 := hterm_nonneg 2
      nlinarith
    have hterm1 : (α 1 - α k) * t 1 = 0 := by
      have h0 := hterm_nonneg 0
      have h1 := hterm_nonneg 1
      have h2 := hterm_nonneg 2
      nlinarith
    have hterm2 : (α 2 - α k) * t 2 = 0 := by
      have h0 := hterm_nonneg 0
      have h1 := hterm_nonneg 1
      have h2 := hterm_nonneg 2
      nlinarith
    have hterm_zero (i : Fin 3) : (α i - α k) * t i = 0 := by
      fin_cases i <;> simp [hterm0, hterm1, hterm2]
    have hai : α i = α k := by
      exact sub_eq_zero.mp ((mul_eq_zero.mp (hterm_zero i)).resolve_right hti)
    rw [hai]
    exact hk j
  · intro htFace
    rcases htFace with ⟨htS, hface⟩
    refine ⟨htS, ?_⟩
    intro s hsS
    rw [wsObj_kappa_zero, wsObj_kappa_zero]
    have ht_term_eq (i : Fin 3) : α i * t i = α k * t i := by
      by_cases hti : t i = 0
      · simp [hti]
      · have hik : α i ≤ α k := hface i hti k
        have hki : α k ≤ α i := hk i
        rw [le_antisymm hik hki]
    have ht_sum : ∑ i, α i * t i = α k * M := by
      calc
        ∑ i, α i * t i = ∑ i, α k * t i := by
          exact Finset.sum_congr rfl (by intro i _; exact ht_term_eq i)
        _ = α k * M := by
          rw [← Finset.mul_sum, htS.2]
    have hs_term_le (i : Fin 3) : α k * s i ≤ α i * s i := by
      have hnonneg : 0 ≤ (α i - α k) * s i :=
        mul_nonneg (sub_nonneg.mpr (hk i)) (hsS.1 i)
      nlinarith
    have hs_sum : α k * M ≤ ∑ i, α i * s i := by
      calc
        α k * M = ∑ i, α k * s i := by
          rw [← hsS.2, Finset.mul_sum]
        _ ≤ ∑ i, α i * s i := by
          exact Finset.sum_le_sum (by intro i _; exact hs_term_le i)
    linarith

end Causalean.Mathlib.Optimization
