/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Mathlib.Optimization.SimplexActiveSetDefs

/-! # Existence of an admissible support (κ > 0)

For `κ > 0` there is an admissible support/multiplier pair `(S, λ)`. Constructed by the
intermediate value theorem applied to the continuous threshold function
`G(λ) = Σᵢ (max(λ − αᵢ, 0))² / βᵢ`: `G` is continuous with `G(min α) = 0 < κ²` and
`G` large for `λ` large, so some `λ` has `G(λ) = κ²`; then `S = {i : αᵢ < λ}` is
admissible (the truncation makes the sum over `S` agree with `G(λ)`, and off `S`,
`αⱼ ≥ λ`). -/

namespace Causalean.Mathlib.Optimization

open scoped BigOperators

/-- The threshold function `G(λ) = Σᵢ (max(λ − αᵢ, 0))² / βᵢ` whose level set
`G(λ) = κ²` selects the active support. -/
noncomputable def kktThreshold (α β : Fin 3 → ℝ) (lam : ℝ) : ℝ :=
  ∑ i, (max (lam - α i) 0) ^ 2 / β i

/-- The active-set threshold function varies continuously with the multiplier. The
positive-weight assumption is carried here to match the surrounding simplex
lemmas, although continuity itself only uses that the weights are fixed real
coefficients. -/
lemma continuous_kktThreshold (α β : Fin 3 → ℝ) (hβ : ∀ i, 0 < β i) :
    Continuous (kktThreshold α β) := by
  have _hβ := hβ
  unfold kktThreshold
  continuity

private lemma kktThreshold_nonneg (α β : Fin 3 → ℝ) (hβ : ∀ i, 0 < β i)
    (lam : ℝ) :
    0 ≤ kktThreshold α β lam := by
  unfold kktThreshold
  exact Finset.sum_nonneg fun i _ =>
    div_nonneg (sq_nonneg _) (le_of_lt (hβ i))

private lemma kktThreshold_eq_zero_of_le (α β : Fin 3 → ℝ) (lam : ℝ)
    (hle : ∀ i, lam ≤ α i) :
    kktThreshold α β lam = 0 := by
  unfold kktThreshold
  apply Finset.sum_eq_zero
  intro i _
  have hdiff : lam - α i ≤ 0 := by linarith [hle i]
  simp [max_eq_right hdiff]

private lemma support_sum_eq_kktThreshold (α β : Fin 3 → ℝ) (lam : ℝ) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin 3 => α i < lam),
        (lam - α i) ^ 2 / β i) = kktThreshold α β lam := by
  classical
  calc
    (∑ i ∈ Finset.univ.filter (fun i : Fin 3 => α i < lam),
        (lam - α i) ^ 2 / β i)
        = ∑ i, if α i < lam then (lam - α i) ^ 2 / β i else 0 := by
          simpa using
            (Finset.sum_filter (s := Finset.univ)
              (p := fun i : Fin 3 => α i < lam)
              (f := fun i => (lam - α i) ^ 2 / β i))
    _ = kktThreshold α β lam := by
      unfold kktThreshold
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : α i < lam
      · have hdiff : 0 ≤ lam - α i := by linarith
        simp [hi, max_eq_left hdiff]
      · have hdiff : lam - α i ≤ 0 := by linarith [not_lt.mp hi]
        simp [hi, max_eq_right hdiff]

/-- **Existence of an admissible support/multiplier pair (κ > 0).**
Proof plan:
* Choose an index attaining the minimum of `α` and set `lo` to that minimum, so every
  squared positive part is zero and the threshold value at `lo` is zero.
* Choose an index attaining the maximum of `α` and set
  `hi = max_j αⱼ + κ * √(β kmax)`, so the `kmax` summand alone equals `κ²` and the
  full threshold value at `hi` is at least `κ²`.
* `intermediate_value_Icc` (continuity of `kktThreshold`) yields `lam ∈ [lo, hi]` with
  `kktThreshold α β lam = κ²`.
* Set `S = Finset.univ.filter (fun i => α i < lam)` (classical decidability). Then
  `Σ_{i∈S}(lam − αᵢ)²/βᵢ = kktThreshold α β lam = κ²` (off `S`, `max (lam − αᵢ) 0 = 0`),
  `S` is nonempty (else `G lam = 0 ≠ κ² > 0`), `αᵢ < lam` on `S`, and `lam ≤ αⱼ` off `S`. -/
lemma exists_admissible (α β : Fin 3 → ℝ) (kappa : ℝ)
    (hβ : ∀ i, 0 < β i) (hk : 0 < kappa) :
    ∃ (S : Finset (Fin 3)) (lam : ℝ), IsAdmissibleSupport α β kappa S lam := by
  classical
  obtain ⟨kmin, hmin⟩ := (Finite.exists_min α : ∃ k : Fin 3, ∀ i, α k ≤ α i)
  obtain ⟨kmax, hmax⟩ := (Finite.exists_max α : ∃ k : Fin 3, ∀ i, α i ≤ α k)
  let lo : ℝ := α kmin
  let hi : ℝ := α kmax + kappa * Real.sqrt (β kmax)
  have hlo_zero : kktThreshold α β lo = 0 := by
    exact kktThreshold_eq_zero_of_le α β lo (by intro i; exact hmin i)
  have hhi_summand :
      (max (hi - α kmax) 0) ^ 2 / β kmax = kappa ^ 2 := by
    have hβpos : 0 < β kmax := hβ kmax
    have hβnonneg : 0 ≤ β kmax := le_of_lt hβpos
    have hsqrt_sq : Real.sqrt (β kmax) ^ 2 = β kmax :=
      Real.sq_sqrt hβnonneg
    have hdiff : hi - α kmax = kappa * Real.sqrt (β kmax) := by
      simp [hi]
    have hdiff_nonneg : 0 ≤ hi - α kmax := by
      rw [hdiff]
      exact mul_nonneg (le_of_lt hk) (Real.sqrt_nonneg _)
    rw [max_eq_left hdiff_nonneg, hdiff]
    field_simp [ne_of_gt hβpos]
    rw [hsqrt_sq]
  have hhi_ge : kappa ^ 2 ≤ kktThreshold α β hi := by
    calc
      kappa ^ 2 = (max (hi - α kmax) 0) ^ 2 / β kmax := by
        exact hhi_summand.symm
      _ ≤ kktThreshold α β hi := by
        unfold kktThreshold
        exact Finset.single_le_sum (s := Finset.univ)
          (f := fun i => (max (hi - α i) 0) ^ 2 / β i)
          (fun i _ => div_nonneg (sq_nonneg _) (le_of_lt (hβ i)))
          (Finset.mem_univ kmax)
  have hlohi : lo ≤ hi := by
    have hmul_nonneg : 0 ≤ kappa * Real.sqrt (β kmax) :=
      mul_nonneg (le_of_lt hk) (Real.sqrt_nonneg _)
    have hle_max : α kmin ≤ α kmax := hmin kmax
    dsimp [lo, hi]
    linarith
  have htarget :
      kappa ^ 2 ∈ Set.Icc (kktThreshold α β lo) (kktThreshold α β hi) := by
    constructor
    · rw [hlo_zero]
      exact sq_nonneg kappa
    · exact hhi_ge
  have hcontOn :
      ContinuousOn (kktThreshold α β) (Set.Icc lo hi) :=
    (continuous_kktThreshold α β hβ).continuousOn
  obtain ⟨lam, -, hlam⟩ :=
    intermediate_value_Icc hlohi hcontOn htarget
  let S : Finset (Fin 3) := Finset.univ.filter (fun i : Fin 3 => α i < lam)
  refine ⟨S, lam, ?_⟩
  have hsum_eq : (∑ i ∈ S, (lam - α i) ^ 2 / β i) = kappa ^ 2 := by
    calc
      (∑ i ∈ S, (lam - α i) ^ 2 / β i)
          = kktThreshold α β lam := by
            simpa [S] using support_sum_eq_kktThreshold α β lam
      _ = kappa ^ 2 := hlam
  refine ⟨?_, hsum_eq, ?_, ?_⟩
  · by_contra hnonempty
    have hSempty : S = ∅ := by
      exact Finset.not_nonempty_iff_eq_empty.mp hnonempty
    have hzero : (∑ i ∈ S, (lam - α i) ^ 2 / β i) = 0 := by
      simp [hSempty]
    have hsquare_zero : kappa ^ 2 = 0 := by
      simpa [hzero] using hsum_eq.symm
    exact (ne_of_gt (sq_pos_of_pos hk)) hsquare_zero
  · intro i hi
    simpa [S] using hi
  · intro j hj
    have hnot : ¬ α j < lam := by
      intro hlt
      exact hj (by simp [S, hlt])
    exact not_lt.mp hnot

end Causalean.Mathlib.Optimization
