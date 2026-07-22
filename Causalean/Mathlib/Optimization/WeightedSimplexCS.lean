/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Mathlib.Optimization.SimplexActiveSetDefs

/-! # Weighted Cauchy–Schwarz on the three-point simplex

Cauchy–Schwarz for the weighted inner product `⟨s,t⟩_β = Σ βᵢ sᵢ tᵢ` on `Fin 3`,
in the squared form `weighted_cs_sq` and the strict simplex-slice form
`weighted_cs_simplex_strict`.  The strict version is used to prove uniqueness for
the weighted-simplex SOCP: on the affine slice `Σ sᵢ = Σ tᵢ = M > 0`, distinct
points are not positive scalar multiples of each other, so equality in
Cauchy–Schwarz cannot occur. -/

namespace Causalean.Mathlib.Optimization

open scoped BigOperators

/-- **Weighted Cauchy–Schwarz (squared form).** For nonnegative weights `β`,
`(Σ βᵢ sᵢ tᵢ)² ≤ (Σ βᵢ sᵢ²)(Σ βᵢ tᵢ²)`. Proof: expand over `Fin 3` and use the
Lagrange identity `PQ − R² = Σ_{i<j} βᵢβⱼ (sᵢtⱼ − sⱼtᵢ)² ≥ 0`. -/
lemma weighted_cs_sq (β s t : Fin 3 → ℝ) (hβ : ∀ i, 0 ≤ β i) :
    (∑ i, β i * (s i * t i)) ^ 2 ≤ (∑ i, β i * s i ^ 2) * (∑ i, β i * t i ^ 2) := by
  simp only [Fin.sum_univ_three]
  nlinarith
    [mul_nonneg (mul_nonneg (hβ 0) (hβ 1)) (sq_nonneg (s 0 * t 1 - s 1 * t 0)),
      mul_nonneg (mul_nonneg (hβ 0) (hβ 2)) (sq_nonneg (s 0 * t 2 - s 2 * t 0)),
      mul_nonneg (mul_nonneg (hβ 1) (hβ 2)) (sq_nonneg (s 1 * t 2 - s 2 * t 1))]

/-- **Strict weighted Cauchy–Schwarz on the simplex slice.** For positive weights,
if `s ≠ t` but `Σ sᵢ = Σ tᵢ = M > 0`, then
`Σ βᵢ sᵢ tᵢ < √(Σ βᵢ sᵢ²) · √(Σ βᵢ tᵢ²)`.

Proof plan:
* Let `P = Σ βᵢ sᵢ²`, `Q = Σ βᵢ tᵢ²`, `R = Σ βᵢ sᵢ tᵢ`. Since `t ≠ 0` (its coords
  sum to `M > 0`) and `β > 0`, `Q > 0`; likewise `P > 0`, so `√P·√Q = √(P·Q) > 0`.
* Show `R² < P·Q`. The Lagrange gap `P·Q − R²` equals
  `β0β1(s0t1−s1t0)² + β0β2(s0t2−s2t0)² + β1β2(s1t2−s2t1)² ≥ 0`. If it were `0` then all
  three cross terms vanish; with `t ≠ 0` this forces `s = c • t` for `c = sₖ/tₖ` at any
  `tₖ ≠ 0`, and then `M = Σ sᵢ = c Σ tᵢ = c M` gives `c = 1`, i.e. `s = t`,
  contradicting `s ≠ t`. Hence the gap is `> 0`.
* Conclude `R ≤ √(R²) < √(P·Q) = √P·√Q` (if `R < 0` it is `< 0 < √P·√Q` directly). -/
lemma weighted_cs_simplex_strict (M : ℝ) (hM : 0 < M) (β s t : Fin 3 → ℝ)
    (hβ : ∀ i, 0 < β i) (hs : ∑ i, s i = M) (ht : ∑ i, t i = M) (hne : s ≠ t) :
    (∑ i, β i * (s i * t i)) <
      Real.sqrt (∑ i, β i * s i ^ 2) * Real.sqrt (∑ i, β i * t i ^ 2) := by
  let P : ℝ := ∑ i, β i * s i ^ 2
  let Q : ℝ := ∑ i, β i * t i ^ 2
  let R : ℝ := ∑ i, β i * (s i * t i)
  have hP_nonneg : 0 ≤ P := by
    simp only [P, Fin.sum_univ_three]
    nlinarith [mul_nonneg (hβ 0).le (sq_nonneg (s 0)),
      mul_nonneg (hβ 1).le (sq_nonneg (s 1)),
      mul_nonneg (hβ 2).le (sq_nonneg (s 2))]
  have hle : R ^ 2 ≤ P * Q := by
    simpa [P, Q, R] using weighted_cs_sq β s t (fun i => (hβ i).le)
  have hlt : R ^ 2 < P * Q := by
    refine lt_of_le_of_ne hle ?_
    intro heq
    have hgap_id :
        P * Q - R ^ 2 =
          β 0 * β 1 * (s 0 * t 1 - s 1 * t 0) ^ 2 +
            β 0 * β 2 * (s 0 * t 2 - s 2 * t 0) ^ 2 +
              β 1 * β 2 * (s 1 * t 2 - s 2 * t 1) ^ 2 := by
      simp only [P, Q, R, Fin.sum_univ_three]
      ring
    have hgap_zero : P * Q - R ^ 2 = 0 := by nlinarith
    have hsum_zero :
        β 0 * β 1 * (s 0 * t 1 - s 1 * t 0) ^ 2 +
            β 0 * β 2 * (s 0 * t 2 - s 2 * t 0) ^ 2 +
              β 1 * β 2 * (s 1 * t 2 - s 2 * t 1) ^ 2 =
          0 := by
      nlinarith
    have h01_nonneg : 0 ≤ β 0 * β 1 * (s 0 * t 1 - s 1 * t 0) ^ 2 :=
      mul_nonneg (mul_nonneg (hβ 0).le (hβ 1).le)
        (sq_nonneg (s 0 * t 1 - s 1 * t 0))
    have h02_nonneg : 0 ≤ β 0 * β 2 * (s 0 * t 2 - s 2 * t 0) ^ 2 :=
      mul_nonneg (mul_nonneg (hβ 0).le (hβ 2).le)
        (sq_nonneg (s 0 * t 2 - s 2 * t 0))
    have h12_nonneg : 0 ≤ β 1 * β 2 * (s 1 * t 2 - s 2 * t 1) ^ 2 :=
      mul_nonneg (mul_nonneg (hβ 1).le (hβ 2).le)
        (sq_nonneg (s 1 * t 2 - s 2 * t 1))
    have h01_zero : β 0 * β 1 * (s 0 * t 1 - s 1 * t 0) ^ 2 = 0 := by
      nlinarith
    have h02_zero : β 0 * β 2 * (s 0 * t 2 - s 2 * t 0) ^ 2 = 0 := by
      nlinarith
    have h12_zero : β 1 * β 2 * (s 1 * t 2 - s 2 * t 1) ^ 2 = 0 := by
      nlinarith
    have h01 : s 0 * t 1 - s 1 * t 0 = 0 := by
      have hpos : 0 < β 0 * β 1 := mul_pos (hβ 0) (hβ 1)
      have hsquare : (s 0 * t 1 - s 1 * t 0) ^ 2 = 0 :=
        Or.resolve_left (mul_eq_zero.mp h01_zero) (ne_of_gt hpos)
      exact sq_eq_zero_iff.mp hsquare
    have h02 : s 0 * t 2 - s 2 * t 0 = 0 := by
      have hpos : 0 < β 0 * β 2 := mul_pos (hβ 0) (hβ 2)
      have hsquare : (s 0 * t 2 - s 2 * t 0) ^ 2 = 0 :=
        Or.resolve_left (mul_eq_zero.mp h02_zero) (ne_of_gt hpos)
      exact sq_eq_zero_iff.mp hsquare
    have h12 : s 1 * t 2 - s 2 * t 1 = 0 := by
      have hpos : 0 < β 1 * β 2 := mul_pos (hβ 1) (hβ 2)
      have hsquare : (s 1 * t 2 - s 2 * t 1) ^ 2 = 0 :=
        Or.resolve_left (mul_eq_zero.mp h12_zero) (ne_of_gt hpos)
      exact sq_eq_zero_iff.mp hsquare
    have h01eq : s 0 * t 1 = s 1 * t 0 := sub_eq_zero.mp h01
    have h02eq : s 0 * t 2 = s 2 * t 0 := sub_eq_zero.mp h02
    have h12eq : s 1 * t 2 = s 2 * t 1 := sub_eq_zero.mp h12
    have hs3 : s 0 + s 1 + s 2 = M := by
      simpa only [Fin.sum_univ_three] using hs
    have ht3 : t 0 + t 1 + t 2 = M := by
      simpa only [Fin.sum_univ_three] using ht
    have hst : s = t := by
      by_cases ht0 : t 0 = 0
      · by_cases ht1 : t 1 = 0
        · by_cases ht2 : t 2 = 0
          · exfalso
            nlinarith only [hM, ht3, ht0, ht1, ht2]
          · have hs2 : s 2 = t 2 := by
              have hscale : M * s 2 = M * t 2 := by
                calc
                  M * s 2 = s 2 * M := by ring
                  _ = s 2 * (t 0 + t 1 + t 2) := by rw [ht3]
                  _ = (s 0 + s 1 + s 2) * t 2 := by nlinarith only [h02, h12]
                  _ = M * t 2 := by rw [hs3]
              exact mul_left_cancel₀ (ne_of_gt hM) hscale
            have hs0 : s 0 = t 0 := by
              have hs0_zero : s 0 = 0 := by
                have hmul : s 0 * t 2 = 0 := by rw [h02eq, ht0, mul_zero]
                exact (mul_eq_zero.mp hmul).resolve_right ht2
              rw [hs0_zero, ht0]
            have hs1 : s 1 = t 1 := by
              have hs1_zero : s 1 = 0 := by
                have hmul : s 1 * t 2 = 0 := by rw [h12eq, ht1, mul_zero]
                exact (mul_eq_zero.mp hmul).resolve_right ht2
              rw [hs1_zero, ht1]
            funext i
            fin_cases i <;> assumption
        · have hs1 : s 1 = t 1 := by
            have hscale : M * s 1 = M * t 1 := by
              calc
                M * s 1 = s 1 * M := by ring
                _ = s 1 * (t 0 + t 1 + t 2) := by rw [ht3]
                _ = (s 0 + s 1 + s 2) * t 1 := by nlinarith only [h01, h12]
                _ = M * t 1 := by rw [hs3]
            exact mul_left_cancel₀ (ne_of_gt hM) hscale
          have hs0 : s 0 = t 0 := by
            have hs0_zero : s 0 = 0 := by
              have hmul : s 0 * t 1 = 0 := by rw [h01eq, ht0, mul_zero]
              exact (mul_eq_zero.mp hmul).resolve_right ht1
            rw [hs0_zero, ht0]
          have hs2 : s 2 = t 2 := by
            have hmul : t 1 * t 2 = t 1 * s 2 := by
              calc
                t 1 * t 2 = s 1 * t 2 := by rw [hs1]
                _ = s 2 * t 1 := h12eq
                _ = t 1 * s 2 := by ring
            exact (mul_left_cancel₀ ht1 hmul).symm
          funext i
          fin_cases i <;> assumption
      · have hs0 : s 0 = t 0 := by
          have hscale : M * s 0 = M * t 0 := by
            calc
              M * s 0 = s 0 * M := by ring
              _ = s 0 * (t 0 + t 1 + t 2) := by rw [ht3]
              _ = (s 0 + s 1 + s 2) * t 0 := by nlinarith only [h01, h02]
              _ = M * t 0 := by rw [hs3]
          exact mul_left_cancel₀ (ne_of_gt hM) hscale
        have hs1 : s 1 = t 1 := by
          have hmul : t 0 * t 1 = t 0 * s 1 := by
            calc
              t 0 * t 1 = s 0 * t 1 := by rw [hs0]
              _ = s 1 * t 0 := h01eq
              _ = t 0 * s 1 := by ring
          exact (mul_left_cancel₀ ht0 hmul).symm
        have hs2 : s 2 = t 2 := by
          have hmul : t 0 * t 2 = t 0 * s 2 := by
            calc
              t 0 * t 2 = s 0 * t 2 := by rw [hs0]
              _ = s 2 * t 0 := h02eq
              _ = t 0 * s 2 := by ring
          exact (mul_left_cancel₀ ht0 hmul).symm
        funext i
        fin_cases i <;> assumption
    exact hne hst
  have hsqrt_lt : Real.sqrt (R ^ 2) < Real.sqrt (P * Q) :=
    Real.sqrt_lt_sqrt (sq_nonneg R) hlt
  have hR_le_sqrt : R ≤ Real.sqrt (R ^ 2) := by
    rw [Real.sqrt_sq_eq_abs]
    exact le_abs_self R
  calc
    (∑ i, β i * (s i * t i)) = R := by rfl
    _ ≤ Real.sqrt (R ^ 2) := hR_le_sqrt
    _ < Real.sqrt (P * Q) := hsqrt_lt
    _ = Real.sqrt P * Real.sqrt Q := by rw [Real.sqrt_mul hP_nonneg]
    _ = Real.sqrt (∑ i, β i * s i ^ 2) * Real.sqrt (∑ i, β i * t i ^ 2) := by rfl

end Causalean.Mathlib.Optimization
