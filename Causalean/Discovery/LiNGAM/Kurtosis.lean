/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Independence.Basic
import Mathlib.Data.Matrix.Mul

/-!
# Kurtosis-based column support for ICA / LiNGAM

This is the **Marcinkiewicz-free** route to LiNGAM identifiability.  Instead of the
general Darmois–Skitovich theorem (which needs Marcinkiewicz), we assume the
sources have **non-zero fourth cumulant of one common sign** (a standard ICA
assumption: all super-Gaussian or all sub-Gaussian).  Then the key column-support
fact `Wᵢⱼ · Wₖⱼ = 0` — the input to `genPerm_of_invertible_of_colSupport` — follows
from a single fourth-cumulant identity and a sum-of-same-sign argument, with no
characteristic-function functional equation at all.

`cross_fourth_cumulant_eq_sum` is the multilinear identity
`cum(yᵢ,yᵢ,yₖ,yₖ) = Σⱼ Wᵢⱼ² Wₖⱼ² κ₄(eⱼ)` for `yᵢ = Σⱼ Wᵢⱼ eⱼ` with independent
centered sources; `colSupport_of_kurtosis` combines it with independence of `yᵢ, yₖ`
(which makes the cross-cumulant vanish) and the same-sign assumption.
-/

namespace Causalean.Discovery.LiNGAM

open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Excess kurtosis, the fourth cumulant of a real random variable.  For a
centered variable `X` it is `E[X⁴] − 3 · (E[X²])²`; Gaussian variables have zero
excess kurtosis, while LiNGAM's kurtosis route assumes every source has nonzero
excess kurtosis of one common sign. -/
noncomputable def kurt (X : Ω → ℝ) (P : Measure Ω) : ℝ :=
  (∫ ω, (X ω) ^ 4 ∂P) - 3 * (∫ ω, (X ω) ^ 2 ∂P) ^ 2

/-- **Fourth cross-cumulant identity (Isserlis / cumulant multilinearity).**  For
independent, centered, finite-fourth-moment sources `eⱼ` and linear forms
`yₐ = Σⱼ aⱼ eⱼ`, `y_b = Σⱼ bⱼ eⱼ`, the joint fourth cumulant `cum(yₐ,yₐ,y_b,y_b)`
equals `Σⱼ aⱼ² bⱼ² κ₄(eⱼ)`. -/
theorem cross_fourth_cumulant_eq_sum {n : ℕ} {e : Ω → Fin n → ℝ} (a b : Fin n → ℝ)
    (hmeas : ∀ j, Measurable (fun ω => e ω j))
    (hindep : iIndepFun (fun j ω => e ω j) P)
    (hL4 : ∀ j, MemLp (fun ω => e ω j) 4 P)
    (hcent : ∀ j, ∫ ω, e ω j ∂P = 0) :
    (∫ ω, (∑ j, a j * e ω j) ^ 2 * (∑ j, b j * e ω j) ^ 2 ∂P)
      - (∫ ω, (∑ j, a j * e ω j) ^ 2 ∂P) * (∫ ω, (∑ j, b j * e ω j) ^ 2 ∂P)
      - 2 * (∫ ω, (∑ j, a j * e ω j) * (∑ j, b j * e ω j) ∂P) ^ 2
      = ∑ j, (a j) ^ 2 * (b j) ^ 2 * kurt (fun ω => e ω j) P := by
  classical
  let m : Fin n → ℝ := fun j => ∫ ω, (e ω j) ^ 2 ∂P
  let q : Fin n → ℝ := fun j => ∫ ω, (e ω j) ^ 4 ∂P
  have hcross : ∀ c d : Fin n → ℝ,
      ∫ ω, (∑ j, c j * e ω j) * (∑ j, d j * e ω j) ∂P =
        ∑ j, c j * d j * m j := by
    intro c d
    have h2 : ∀ j, MemLp (fun ω => e ω j) 2 P := fun j =>
      (hL4 j).mono_exponent (by norm_num)
    have hint_pair : ∀ i j, Integrable (fun ω => (c i * e ω i) * (d j * e ω j)) P := by
      intro i j
      have hmul : MemLp (fun ω => e ω i * e ω j) 1 P := by
        simpa only [Pi.mul_apply] using (h2 j).mul' (h2 i)
      convert (memLp_one_iff_integrable.mp hmul).const_mul (c i * d j) using 1
      ext ω
      ring
    have hpair : ∀ i j, ∫ ω, e ω i * e ω j ∂P = if i = j then m i else 0 := by
      intro i j
      by_cases hij : i = j
      · subst j
        simp [m, pow_two]
      · have h_ind : IndepFun (fun ω => e ω i) (fun ω => e ω j) P := by
          simpa using hindep.indepFun (i := i) (j := j) hij
        have h := h_ind.integral_fun_mul_eq_mul_integral
          (h2 i).aestronglyMeasurable (h2 j).aestronglyMeasurable
        simp [hij, hcent i, hcent j, h]
    have hterm :
        ∀ i j, ∫ ω, (c i * e ω i) * (d j * e ω j) ∂P =
          c i * d j * ∫ ω, e ω i * e ω j ∂P := by
      intro i j
      rw [← MeasureTheory.integral_const_mul]
      congr 1
      ext ω
      ring
    calc
      ∫ ω, (∑ j, c j * e ω j) * (∑ j, d j * e ω j) ∂P
          = ∫ ω, ∑ i, ∑ j, (c i * e ω i) * (d j * e ω j) ∂P := by
            congr 1
            ext ω
            rw [Finset.sum_mul_sum]
      _ = ∑ i, ∑ j, ∫ ω, (c i * e ω i) * (d j * e ω j) ∂P := by
            rw [MeasureTheory.integral_finset_sum Finset.univ]
            · congr with i
              rw [MeasureTheory.integral_finset_sum Finset.univ]
              intro j _
              exact hint_pair i j
            · intro i _
              exact integrable_finset_sum Finset.univ (fun j _ => hint_pair i j)
      _ = ∑ i, ∑ j, c i * d j * (∫ ω, e ω i * e ω j ∂P) := by
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro j _
            exact hterm i j
      _ = ∑ i, ∑ j, c i * d j * (if i = j then m i else 0) := by
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro j _
            rw [hpair i j]
      _ = ∑ i, c i * d i * m i := by
            simp [m, mul_assoc]
  have hAA : ∫ ω, (∑ j, a j * e ω j) ^ 2 ∂P = ∑ j, (a j) ^ 2 * m j := by
    simpa [pow_two, mul_assoc] using hcross a a
  have hBB : ∫ ω, (∑ j, b j * e ω j) ^ 2 ∂P = ∑ j, (b j) ^ 2 * m j := by
    simpa [pow_two, mul_assoc] using hcross b b
  have hAB :
      ∫ ω, (∑ j, a j * e ω j) * (∑ j, b j * e ω j) ∂P =
        ∑ j, a j * b j * m j := hcross a b
  have h4 :
      ∫ ω, (∑ j, a j * e ω j) ^ 2 * (∑ j, b j * e ω j) ^ 2 ∂P =
        (∑ j, (a j) ^ 2 * (b j) ^ 2 * q j)
        + ((∑ j, (a j) ^ 2 * m j) * (∑ j, (b j) ^ 2 * m j)
            - ∑ j, (a j) ^ 2 * (b j) ^ 2 * (m j) ^ 2)
        + 2 * ((∑ j, a j * b j * m j) ^ 2
            - ∑ j, (a j * b j * m j) ^ 2) := by
    -- Fourth-moment expansion under independence and centering:
    -- only the all-equal index and the three pair-partition patterns survive.
    have hI4 : ∀ i i' k k' : Fin n,
        ∫ ω, e ω i * e ω i' * e ω k * e ω k' ∂P =
          ((if i = i' ∧ i = k ∧ i = k' then q i else 0)
            + (if i = i' ∧ k = k' ∧ i ≠ k then m i * m k else 0)
            + (if i = k ∧ i' = k' ∧ i ≠ i' then m i * m i' else 0)
            + (if i = k' ∧ i' = k ∧ i ≠ i' then m i * m i' else 0)) := by
      have h2 : ∀ j, MemLp (fun ω => e ω j) 2 P := fun j =>
        (hL4 j).mono_exponent (by norm_num)
      have hpair : ∀ x y, ∫ ω, e ω x * e ω y ∂P = if x = y then m x else 0 := by
        intro x y
        by_cases hxy : x = y
        · subst y
          simp [m, pow_two]
        · have h_ind : IndepFun (fun ω => e ω x) (fun ω => e ω y) P := by
            simpa using hindep.indepFun (i := x) (j := y) hxy
          have h := h_ind.integral_fun_mul_eq_mul_integral
            (h2 x).aestronglyMeasurable (h2 y).aestronglyMeasurable
          simp [hxy, hcent x, hcent y, h]
      have hpairpair_eval : ∀ x y z w,
          x ≠ z → x ≠ w → y ≠ z → y ≠ w →
          ∫ ω, e ω x * e ω y * e ω z * e ω w ∂P =
            (if x = y then m x else 0) * (if z = w then m z else 0) := by
        intro x y z w hxz hxw hyz hyw
        have h_ind : IndepFun (fun ω => e ω x * e ω y) (fun ω => e ω z * e ω w) P := by
          simpa only [Pi.mul_apply] using
            hindep.indepFun_mul_mul hmeas x y z w hxz hxw hyz hyw
        haveI h442 : ENNReal.HolderTriple 4 4 2 := by
          change ENNReal.HolderTriple ((4 : NNReal) : ENNReal) ((4 : NNReal) : ENNReal)
            ((2 : NNReal) : ENNReal)
          exact NNReal.HolderTriple.coe_ennreal (by norm_num)
            (by constructor <;> norm_num : NNReal.HolderTriple 4 4 2)
        have hxy_mem : MemLp (fun ω => e ω x * e ω y) 2 P := by
          simpa only [Pi.mul_apply] using (hL4 y).mul' (hL4 x)
        have hzw_mem : MemLp (fun ω => e ω z * e ω w) 2 P := by
          simpa only [Pi.mul_apply] using (hL4 w).mul' (hL4 z)
        calc
          ∫ ω, e ω x * e ω y * e ω z * e ω w ∂P
              = ∫ ω, (e ω x * e ω y) * (e ω z * e ω w) ∂P := by
                congr 1
                ext ω
                ring
          _ = (∫ ω, e ω x * e ω y ∂P) * (∫ ω, e ω z * e ω w ∂P) := by
                exact h_ind.integral_fun_mul_eq_mul_integral
                  hxy_mem.aestronglyMeasurable hzw_mem.aestronglyMeasurable
          _ = (if x = y then m x else 0) * (if z = w then m z else 0) := by
                rw [hpair x y, hpair z w]
      have htwoPair : ∀ x y, x ≠ y →
          ∫ ω, e ω x * e ω x * e ω y * e ω y ∂P = m x * m y := by
        intro x y hxy
        simpa using hpairpair_eval x x y y hxy hxy hxy hxy
      have hcube : ∀ x y, x ≠ y →
          ∫ ω, e ω x * e ω y * e ω y * e ω y ∂P = 0 := by
        intro x y hxy
        have h_ind : IndepFun (fun ω => e ω x) (fun ω => (e ω y) ^ 3) P := by
          have h0 : IndepFun (fun ω => e ω x) (fun ω => e ω y) P := by
            simpa using hindep.indepFun (i := x) (j := y) hxy
          simpa [Function.comp_def] using h0.comp measurable_id (measurable_id.pow_const 3)
        have h := h_ind.integral_fun_mul_eq_mul_integral
          (h2 x).aestronglyMeasurable ((hmeas y).pow_const 3).aestronglyMeasurable
        calc
          ∫ ω, e ω x * e ω y * e ω y * e ω y ∂P
              = ∫ ω, e ω x * (e ω y) ^ 3 ∂P := by
                congr 1
                ext ω
                ring
          _ = 0 := by
                simpa [hcent x] using h
      have hall : ∀ x, ∫ ω, e ω x * e ω x * e ω x * e ω x ∂P = q x := by
        intro x
        change ∫ ω, e ω x * e ω x * e ω x * e ω x ∂P =
          ∫ ω, (e ω x) ^ 4 ∂P
        congr 1
        ext ω
        ring
      intro i i' k k'
      by_cases hii' : i = i'
      · subst i'
        by_cases hik : i = k
        · subst k
          by_cases hik' : i = k'
          · subst k'
            calc
              ∫ ω, e ω i * e ω i * e ω i * e ω i ∂P = q i := hall i
              _ = ((if i = i ∧ i = i ∧ i = i then q i else 0)
                    + (if i = i ∧ i = i ∧ i ≠ i then m i * m i else 0)
                    + (if i = i ∧ i = i ∧ i ≠ i then m i * m i else 0)
                    + (if i = i ∧ i = i ∧ i ≠ i then m i * m i else 0)) := by
                    simp
          · calc
              ∫ ω, e ω i * e ω i * e ω i * e ω k' ∂P = 0 := by
                simpa [mul_comm, mul_left_comm, mul_assoc] using hcube k' i (Ne.symm hik')
              _ = ((if i = i ∧ i = i ∧ i = k' then q i else 0)
                    + (if i = i ∧ i = k' ∧ i ≠ i then m i * m i else 0)
                    + (if i = i ∧ i = k' ∧ i ≠ i then m i * m i else 0)
                    + (if i = k' ∧ i = i ∧ i ≠ i then m i * m i else 0)) := by
                    simp [hik']
        · by_cases hkk' : k = k'
          · subst k'
            calc
              ∫ ω, e ω i * e ω i * e ω k * e ω k ∂P = m i * m k := htwoPair i k hik
              _ = ((if i = i ∧ i = k ∧ i = k then q i else 0)
                    + (if i = i ∧ k = k ∧ i ≠ k then m i * m k else 0)
                    + (if i = k ∧ i = k ∧ i ≠ i then m i * m i else 0)
                    + (if i = k ∧ i = k ∧ i ≠ i then m i * m i else 0)) := by
                    simp [hik]
          · by_cases hik' : i = k'
            · subst k'
              calc
                ∫ ω, e ω i * e ω i * e ω k * e ω i ∂P = 0 := by
                  simpa [mul_comm, mul_left_comm, mul_assoc] using hcube k i (Ne.symm hik)
                _ = ((if i = i ∧ i = k ∧ i = i then q i else 0)
                      + (if i = i ∧ k = i ∧ i ≠ k then m i * m k else 0)
                      + (if i = k ∧ i = i ∧ i ≠ i then m i * m i else 0)
                      + (if i = i ∧ i = k ∧ i ≠ i then m i * m i else 0)) := by
                      simp [hik, hkk']
            · calc
                ∫ ω, e ω i * e ω i * e ω k * e ω k' ∂P = 0 := by
                  have h := hpairpair_eval k k' i i (Ne.symm hik) (Ne.symm hik)
                    (Ne.symm hik') (Ne.symm hik')
                  calc
                    ∫ ω, e ω i * e ω i * e ω k * e ω k' ∂P
                        = ∫ ω, e ω k * e ω k' * e ω i * e ω i ∂P := by
                          congr 1
                          ext ω
                          ring
                    _ = 0 := by simpa [hkk'] using h
                _ = ((if i = i ∧ i = k ∧ i = k' then q i else 0)
                      + (if i = i ∧ k = k' ∧ i ≠ k then m i * m k else 0)
                      + (if i = k ∧ i = k' ∧ i ≠ i then m i * m i else 0)
                      + (if i = k' ∧ i = k ∧ i ≠ i then m i * m i else 0)) := by
                      simp [hik, hik', hkk']
      · by_cases hik : i = k
        · subst k
          by_cases hi'k' : i' = k'
          · subst k'
            calc
              ∫ ω, e ω i * e ω i' * e ω i * e ω i' ∂P = m i * m i' := by
                simpa [mul_comm, mul_left_comm, mul_assoc] using htwoPair i i' hii'
              _ = ((if i = i' ∧ i = i ∧ i = i' then q i else 0)
                    + (if i = i' ∧ i = i' ∧ i ≠ i then m i * m i else 0)
                    + (if i = i ∧ i' = i' ∧ i ≠ i' then m i * m i' else 0)
                    + (if i = i' ∧ i' = i ∧ i ≠ i' then m i * m i' else 0)) := by
                    simp [hii']
          · by_cases hik' : i = k'
            · subst k'
              calc
                ∫ ω, e ω i * e ω i' * e ω i * e ω i ∂P = 0 := by
                  simpa [mul_comm, mul_left_comm, mul_assoc] using hcube i' i (Ne.symm hii')
                _ = ((if i = i' ∧ i = i ∧ i = i then q i else 0)
                      + (if i = i' ∧ i = i ∧ i ≠ i then m i * m i else 0)
                      + (if i = i ∧ i' = i ∧ i ≠ i' then m i * m i' else 0)
                      + (if i = i ∧ i' = i ∧ i ≠ i' then m i * m i' else 0)) := by
                      simp [hii', eq_comm]
            · calc
                ∫ ω, e ω i * e ω i' * e ω i * e ω k' ∂P = 0 := by
                  have h := hpairpair_eval i' k' i i (Ne.symm hii') (Ne.symm hii')
                    (Ne.symm hik') (Ne.symm hik')
                  calc
                    ∫ ω, e ω i * e ω i' * e ω i * e ω k' ∂P
                        = ∫ ω, e ω i' * e ω k' * e ω i * e ω i ∂P := by
                          congr 1
                          ext ω
                          ring
                    _ = 0 := by simpa [hi'k'] using h
                _ = ((if i = i' ∧ i = i ∧ i = k' then q i else 0)
                      + (if i = i' ∧ i = k' ∧ i ≠ i then m i * m i else 0)
                      + (if i = i ∧ i' = k' ∧ i ≠ i' then m i * m i' else 0)
                      + (if i = k' ∧ i' = i ∧ i ≠ i' then m i * m i' else 0)) := by
                      simp [hii', hik', hi'k']
        · by_cases hik' : i = k'
          · subst k'
            by_cases hi'k : i' = k
            · subst k
              calc
                ∫ ω, e ω i * e ω i' * e ω i' * e ω i ∂P = m i * m i' := by
                  simpa [mul_comm, mul_left_comm, mul_assoc] using htwoPair i i' hii'
                _ = ((if i = i' ∧ i = i' ∧ i = i then q i else 0)
                      + (if i = i' ∧ i' = i ∧ i ≠ i' then m i * m i' else 0)
                      + (if i = i' ∧ i' = i ∧ i ≠ i' then m i * m i' else 0)
                      + (if i = i ∧ i' = i' ∧ i ≠ i' then m i * m i' else 0)) := by
                      simp [hii']
            · calc
                ∫ ω, e ω i * e ω i' * e ω k * e ω i ∂P = 0 := by
                  have h := hpairpair_eval i' k i i (Ne.symm hii') (Ne.symm hii')
                    (Ne.symm hik) (Ne.symm hik)
                  calc
                    ∫ ω, e ω i * e ω i' * e ω k * e ω i ∂P
                        = ∫ ω, e ω i' * e ω k * e ω i * e ω i ∂P := by
                          congr 1
                          ext ω
                          ring
                    _ = 0 := by simpa [hi'k] using h
                _ = ((if i = i' ∧ i = k ∧ i = i then q i else 0)
                      + (if i = i' ∧ k = i ∧ i ≠ k then m i * m k else 0)
                      + (if i = k ∧ i' = i ∧ i ≠ i' then m i * m i' else 0)
                      + (if i = i ∧ i' = k ∧ i ≠ i' then m i * m i' else 0)) := by
                      simp [hii', hik, hi'k]
          · by_cases hi'k : i' = k
            · subst k
              by_cases hi'k' : i' = k'
              · subst k'
                calc
                  ∫ ω, e ω i * e ω i' * e ω i' * e ω i' ∂P = 0 := by
                    simpa [mul_comm, mul_left_comm, mul_assoc] using hcube i i' hii'
                  _ = ((if i = i' ∧ i = i' ∧ i = i' then q i else 0)
                        + (if i = i' ∧ i' = i' ∧ i ≠ i' then m i * m i' else 0)
                        + (if i = i' ∧ i' = i' ∧ i ≠ i' then m i * m i' else 0)
                        + (if i = i' ∧ i' = i' ∧ i ≠ i' then m i * m i' else 0)) := by
                        simp [hii']
              · calc
                  ∫ ω, e ω i * e ω i' * e ω i' * e ω k' ∂P = 0 := by
                    have h := hpairpair_eval i k' i' i' hii' hii' (Ne.symm hi'k')
                      (Ne.symm hi'k')
                    calc
                      ∫ ω, e ω i * e ω i' * e ω i' * e ω k' ∂P
                          = ∫ ω, e ω i * e ω k' * e ω i' * e ω i' ∂P := by
                            congr 1
                            ext ω
                            ring
                      _ = 0 := by simpa [hik'] using h
                  _ = ((if i = i' ∧ i = i' ∧ i = k' then q i else 0)
                        + (if i = i' ∧ i' = k' ∧ i ≠ i' then m i * m i' else 0)
                        + (if i = i' ∧ i' = k' ∧ i ≠ i' then m i * m i' else 0)
                        + (if i = k' ∧ i' = i' ∧ i ≠ i' then m i * m i' else 0)) := by
                        simp [hii', hik', hi'k']
            · by_cases hi'k' : i' = k'
              · subst k'
                calc
                  ∫ ω, e ω i * e ω i' * e ω k * e ω i' ∂P = 0 := by
                    have h := hpairpair_eval i k i' i' hii' hii' (Ne.symm hi'k)
                      (Ne.symm hi'k)
                    calc
                      ∫ ω, e ω i * e ω i' * e ω k * e ω i' ∂P
                          = ∫ ω, e ω i * e ω k * e ω i' * e ω i' ∂P := by
                            congr 1
                            ext ω
                            ring
                      _ = 0 := by simpa [hik] using h
                  _ = ((if i = i' ∧ i = k ∧ i = i' then q i else 0)
                        + (if i = i' ∧ k = i' ∧ i ≠ k then m i * m k else 0)
                        + (if i = k ∧ i' = i' ∧ i ≠ i' then m i * m i' else 0)
                        + (if i = i' ∧ i' = k ∧ i ≠ i' then m i * m i' else 0)) := by
                        simp [hii', hik, hi'k]
              · by_cases hkk' : k = k'
                · subst k'
                  calc
                    ∫ ω, e ω i * e ω i' * e ω k * e ω k ∂P = 0 := by
                      have h := hpairpair_eval i i' k k hik hik hi'k hi'k
                      simpa [hii'] using h
                    _ = ((if i = i' ∧ i = k ∧ i = k then q i else 0)
                          + (if i = i' ∧ k = k ∧ i ≠ k then m i * m k else 0)
                          + (if i = k ∧ i' = k ∧ i ≠ i' then m i * m i' else 0)
                          + (if i = k ∧ i' = k ∧ i ≠ i' then m i * m i' else 0)) := by
                          simp [hii', hik, hi'k]
                · calc
                    ∫ ω, e ω i * e ω i' * e ω k * e ω k' ∂P = 0 := by
                      have h := hpairpair_eval i i' k k' hik hik' hi'k hi'k'
                      simpa [hii'] using h
                    _ = ((if i = i' ∧ i = k ∧ i = k' then q i else 0)
                          + (if i = i' ∧ k = k' ∧ i ≠ k then m i * m k else 0)
                          + (if i = k ∧ i' = k' ∧ i ≠ i' then m i * m i' else 0)
                          + (if i = k' ∧ i' = k ∧ i ≠ i' then m i * m i' else 0)) := by
                          simp [hii', hik, hik', hi'k, hi'k', hkk']
    have hpoint4 (ω : Ω) :
        (∑ j, a j * e ω j) ^ 2 * (∑ j, b j * e ω j) ^ 2 =
          ∑ i, ∑ k, ∑ i', ∑ k',
            (a i * a i' * b k * b k') *
              (e ω i * e ω i' * e ω k * e ω k') := by
      simp [pow_two, Finset.sum_mul_sum, mul_comm, mul_left_comm]
    have hint_four : ∀ i i' k k',
        Integrable (fun ω =>
          (a i * a i' * b k * b k') *
            (e ω i * e ω i' * e ω k * e ω k')) P := by
      intro i i' k k'
      haveI h442 : ENNReal.HolderTriple 4 4 2 := by
        change ENNReal.HolderTriple ((4 : NNReal) : ENNReal) ((4 : NNReal) : ENNReal)
          ((2 : NNReal) : ENNReal)
        exact NNReal.HolderTriple.coe_ennreal (by norm_num)
          (by constructor <;> norm_num : NNReal.HolderTriple 4 4 2)
      haveI h221 : ENNReal.HolderTriple 2 2 1 := by
        change ENNReal.HolderTriple ((2 : NNReal) : ENNReal) ((2 : NNReal) : ENNReal)
          ((1 : NNReal) : ENNReal)
        exact NNReal.HolderTriple.coe_ennreal (by norm_num)
          (by constructor <;> norm_num : NNReal.HolderTriple 2 2 1)
      have hleft : MemLp (fun ω => e ω i * e ω i') 2 P := by
        simpa only [Pi.mul_apply] using (hL4 i').mul' (hL4 i)
      have hright : MemLp (fun ω => e ω k * e ω k') 2 P := by
        simpa only [Pi.mul_apply] using (hL4 k').mul' (hL4 k)
      have hmul : MemLp (fun ω => (e ω i * e ω i') * (e ω k * e ω k')) 1 P := by
        simpa only [Pi.mul_apply] using hright.mul' hleft
      convert (memLp_one_iff_integrable.mp hmul).const_mul (a i * a i' * b k * b k') using 1
      ext ω
      ring
    have hexpand :
        ∫ ω, (∑ j, a j * e ω j) ^ 2 * (∑ j, b j * e ω j) ^ 2 ∂P =
          ∑ i, ∑ k, ∑ i', ∑ k',
            (a i * a i' * b k * b k') *
              ∫ ω, e ω i * e ω i' * e ω k * e ω k' ∂P := by
      calc
        ∫ ω, (∑ j, a j * e ω j) ^ 2 * (∑ j, b j * e ω j) ^ 2 ∂P
            = ∫ ω, ∑ i, ∑ k, ∑ i', ∑ k',
                (a i * a i' * b k * b k') *
                  (e ω i * e ω i' * e ω k * e ω k') ∂P := by
              congr 1
              ext ω
              exact hpoint4 ω
        _ = ∑ i, ∑ k, ∑ i', ∑ k',
              ∫ ω, (a i * a i' * b k * b k') *
                (e ω i * e ω i' * e ω k * e ω k') ∂P := by
              rw [MeasureTheory.integral_finset_sum Finset.univ]
              · congr with i
                rw [MeasureTheory.integral_finset_sum Finset.univ]
                · congr with k
                  rw [MeasureTheory.integral_finset_sum Finset.univ]
                  · congr with i'
                    rw [MeasureTheory.integral_finset_sum Finset.univ]
                    intro k' _
                    exact hint_four i i' k k'
                  · intro i' _
                    exact integrable_finset_sum Finset.univ (fun k' _ => hint_four i i' k k')
                · intro k _
                  exact integrable_finset_sum Finset.univ (fun i' _ =>
                    integrable_finset_sum Finset.univ (fun k' _ => hint_four i i' k k'))
              · intro i _
                exact integrable_finset_sum Finset.univ (fun k _ =>
                  integrable_finset_sum Finset.univ (fun i' _ =>
                    integrable_finset_sum Finset.univ (fun k' _ => hint_four i i' k k')))
        _ = ∑ i, ∑ k, ∑ i', ∑ k',
              (a i * a i' * b k * b k') *
                ∫ ω, e ω i * e ω i' * e ω k * e ω k' ∂P := by
              congr with i
              congr with k
              congr with i'
              congr with k'
              rw [MeasureTheory.integral_const_mul]
    have hoffdiag (f : Fin n → Fin n → ℝ) :
        (∑ i, ∑ j, if i = j then 0 else f i j) =
          (∑ i, ∑ j, f i j) - ∑ i, f i i := by
      calc
        (∑ i, ∑ j, if i = j then 0 else f i j)
            = ∑ i, ∑ j, (f i j - if i = j then f i j else 0) := by
              congr with i
              congr with j
              split <;> ring
        _ = ∑ i, ((∑ j, f i j) - f i i) := by
              congr with i
              rw [Finset.sum_sub_distrib]
              simp
        _ = (∑ i, ∑ j, f i j) - ∑ i, f i i := by
              rw [Finset.sum_sub_distrib]
    have hfinite_raw :
        (∑ i, ∑ i', ∑ k, ∑ k',
          a i * a i' * b k * b k' *
            ((if i = i' ∧ i = k ∧ i = k' then q i else 0)
              + (if i = i' ∧ k = k' ∧ i ≠ k then m i * m k else 0)
              + (if i = k ∧ i' = k' ∧ i ≠ i' then m i * m i' else 0)
              + (if i = k' ∧ i' = k ∧ i ≠ i' then m i * m i' else 0))) =
          (∑ j, (a j) ^ 2 * (b j) ^ 2 * q j)
            + ((∑ j, (a j) ^ 2 * m j) * (∑ j, (b j) ^ 2 * m j)
                - ∑ j, (a j) ^ 2 * (b j) ^ 2 * (m j) ^ 2)
            + 2 * ((∑ j, a j * b j * m j) ^ 2
                - ∑ j, (a j * b j * m j) ^ 2) := by
      have hdiag :
          (∑ i, ∑ i', ∑ k, ∑ k',
            if i = i' ∧ i = k ∧ i = k' then a i * a i' * b k * b k' * q i else 0) =
          ∑ j, a j ^ 2 * b j ^ 2 * q j := by
        simp_rw [ite_and]
        simp [pow_two]
        ring_nf
      have hp1 :
          (∑ i, ∑ i', ∑ k, ∑ k',
            if i = i' ∧ k = k' ∧ i ≠ k then
              a i * a i' * b k * b k' * m i * m k else 0) =
          (∑ i, a i ^ 2 * m i) * (∑ k, b k ^ 2 * m k)
            - ∑ j, a j ^ 2 * b j ^ 2 * m j ^ 2 := by
        simp_rw [ite_and]
        simp [pow_two]
        rw [hoffdiag]
        rw [Finset.sum_mul_sum]
        congr 1
        · congr with i
          congr with k
          ring
        · congr with j
          ring
      have hp2 :
          (∑ i, ∑ i', ∑ k, ∑ k',
            if i = k ∧ i' = k' ∧ i ≠ i' then
              a i * a i' * b k * b k' * m i * m i' else 0) =
          (∑ j, a j * b j * m j) ^ 2 - ∑ j, (a j * b j * m j) ^ 2 := by
        simp_rw [ite_and]
        simp [pow_two]
        rw [hoffdiag]
        rw [Finset.sum_mul_sum]
        congr 1
        · congr with i
          congr with j
          ring
        · congr with j
          ring
      have hp3 :
          (∑ i, ∑ i', ∑ k, ∑ k',
            if i = k' ∧ i' = k ∧ i ≠ i' then
              a i * a i' * b k * b k' * m i * m i' else 0) =
          (∑ j, a j * b j * m j) ^ 2 - ∑ j, (a j * b j * m j) ^ 2 := by
        simp_rw [ite_and]
        simp [pow_two]
        rw [hoffdiag]
        rw [Finset.sum_mul_sum]
        congr 1
        · congr with i
          congr with j
          ring
        · congr with j
          ring
      calc
        (∑ i, ∑ i', ∑ k, ∑ k',
          a i * a i' * b k * b k' *
            ((if i = i' ∧ i = k ∧ i = k' then q i else 0)
              + (if i = i' ∧ k = k' ∧ i ≠ k then m i * m k else 0)
              + (if i = k ∧ i' = k' ∧ i ≠ i' then m i * m i' else 0)
              + (if i = k' ∧ i' = k ∧ i ≠ i' then m i * m i' else 0)))
            = (∑ i, ∑ i', ∑ k, ∑ k',
                if i = i' ∧ i = k ∧ i = k' then a i * a i' * b k * b k' * q i else 0)
              + (∑ i, ∑ i', ∑ k, ∑ k',
                if i = i' ∧ k = k' ∧ i ≠ k then
                  a i * a i' * b k * b k' * m i * m k else 0)
              + (∑ i, ∑ i', ∑ k, ∑ k',
                if i = k ∧ i' = k' ∧ i ≠ i' then
                  a i * a i' * b k * b k' * m i * m i' else 0)
              + (∑ i, ∑ i', ∑ k, ∑ k',
                if i = k' ∧ i' = k ∧ i ≠ i' then
                  a i * a i' * b k * b k' * m i * m i' else 0) := by
              simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero]
              ring_nf
        _ = _ := by
              rw [hdiag, hp1, hp2, hp3]
              ring
    have hfinite :
        (∑ i, ∑ k, ∑ i', ∑ k',
          a i * a i' * b k * b k' *
            ((if i = i' ∧ i = k ∧ i = k' then q i else 0)
              + (if i = i' ∧ k = k' ∧ i ≠ k then m i * m k else 0)
              + (if i = k ∧ i' = k' ∧ i ≠ i' then m i * m i' else 0)
              + (if i = k' ∧ i' = k ∧ i ≠ i' then m i * m i' else 0))) =
          (∑ j, (a j) ^ 2 * (b j) ^ 2 * q j)
            + ((∑ j, (a j) ^ 2 * m j) * (∑ j, (b j) ^ 2 * m j)
                - ∑ j, (a j) ^ 2 * (b j) ^ 2 * (m j) ^ 2)
            + 2 * ((∑ j, a j * b j * m j) ^ 2
                - ∑ j, (a j * b j * m j) ^ 2) := by
      rw [← hfinite_raw]
      congr with i
      rw [Finset.sum_comm]
    calc
      ∫ ω, (∑ j, a j * e ω j) ^ 2 * (∑ j, b j * e ω j) ^ 2 ∂P
          = ∑ i, ∑ k, ∑ i', ∑ k',
              (a i * a i' * b k * b k') *
                ∫ ω, e ω i * e ω i' * e ω k * e ω k' ∂P := hexpand
      _ = ∑ i, ∑ k, ∑ i', ∑ k',
            a i * a i' * b k * b k' *
              ((if i = i' ∧ i = k ∧ i = k' then q i else 0)
                + (if i = i' ∧ k = k' ∧ i ≠ k then m i * m k else 0)
                + (if i = k ∧ i' = k' ∧ i ≠ i' then m i * m i' else 0)
                + (if i = k' ∧ i' = k ∧ i ≠ i' then m i * m i' else 0)) := by
            congr with i
            congr with k
            congr with i'
            congr with k'
            rw [hI4 i i' k k']
      _ = _ := hfinite
  rw [h4, hAA, hBB, hAB]
  simp only [kurt, m, q]
  ring_nf
  rw [Finset.sum_mul, ← Finset.sum_sub_distrib]

/-- **Kurtosis-based column support.**  If the sources `eⱼ` are independent, centered,
with finite fourth moment and non-zero fourth cumulant of one common sign, and the
two linear forms `Σⱼ Wᵢⱼ eⱼ` and `Σⱼ Wₖⱼ eⱼ` are independent (for `i ≠ k`), then for
every `j`, `Wᵢⱼ · Wₖⱼ = 0`.  This is the input required by
`genPerm_of_invertible_of_colSupport`. -/
theorem colSupport_of_kurtosis {n : ℕ} {e : Ω → Fin n → ℝ} {W : Matrix (Fin n) (Fin n) ℝ}
    (hmeas : ∀ j, Measurable (fun ω => e ω j))
    (hindep : iIndepFun (fun j ω => e ω j) P)
    (hL4 : ∀ j, MemLp (fun ω => e ω j) 4 P)
    (hcent : ∀ j, ∫ ω, e ω j ∂P = 0)
    (hsign : (∀ j, 0 < kurt (fun ω => e ω j) P) ∨ (∀ j, kurt (fun ω => e ω j) P < 0))
    {i k : Fin n} (hik : i ≠ k)
    (hyindep : IndepFun (fun ω => ∑ j, W i j * e ω j) (fun ω => ∑ j, W k j * e ω j) P) :
    ∀ j, W i j * W k j = 0 := by
  classical
  let y : Ω → ℝ := fun ω => ∑ j, W i j * e ω j
  let z : Ω → ℝ := fun ω => ∑ j, W k j * e ω j
  have hy_meas : Measurable y := by
    simp only [y]
    exact Finset.measurable_sum Finset.univ fun j _ => (hmeas j).const_mul _
  have hz_meas : Measurable z := by
    simp only [z]
    exact Finset.measurable_sum Finset.univ fun j _ => (hmeas j).const_mul _
  have hy_int : ∫ ω, y ω ∂P = 0 := by
    have hterm : ∀ j ∈ Finset.univ, Integrable (fun ω => W i j * e ω j) P := by
      intro j _
      have h14 : (1 : ENNReal) ≤ (4 : ENNReal) := by norm_num
      exact (memLp_one_iff_integrable.mp ((hL4 j).mono_exponent h14)).const_mul _
    calc
      ∫ ω, y ω ∂P = ∑ j, ∫ ω, W i j * e ω j ∂P := by
        simp only [y]
        rw [MeasureTheory.integral_finset_sum Finset.univ hterm]
      _ = ∑ j, W i j * ∫ ω, e ω j ∂P := by
        congr 1
        ext j
        rw [MeasureTheory.integral_const_mul]
      _ = 0 := by
        simp [hcent]
  have hz_int : ∫ ω, z ω ∂P = 0 := by
    have hterm : ∀ j ∈ Finset.univ, Integrable (fun ω => W k j * e ω j) P := by
      intro j _
      have h14 : (1 : ENNReal) ≤ (4 : ENNReal) := by norm_num
      exact (memLp_one_iff_integrable.mp ((hL4 j).mono_exponent h14)).const_mul _
    calc
      ∫ ω, z ω ∂P = ∑ j, ∫ ω, W k j * e ω j ∂P := by
        simp only [z]
        rw [MeasureTheory.integral_finset_sum Finset.univ hterm]
      _ = ∑ j, W k j * ∫ ω, e ω j ∂P := by
        congr 1
        ext j
        rw [MeasureTheory.integral_const_mul]
      _ = 0 := by
        simp [hcent]
  have hyz_int : ∫ ω, y ω * z ω ∂P = 0 := by
    have h := hyindep.integral_fun_mul_eq_mul_integral hy_meas.aestronglyMeasurable
      hz_meas.aestronglyMeasurable
    simpa [y, z, hy_int, hz_int] using h
  have hy2z2_int :
      (∫ ω, y ω ^ 2 * z ω ^ 2 ∂P) = (∫ ω, y ω ^ 2 ∂P) * (∫ ω, z ω ^ 2 ∂P) := by
    have hsq_indep : IndepFun (fun ω => y ω ^ 2) (fun ω => z ω ^ 2) P := by
      simpa [y, z] using
        hyindep.comp (measurable_id.pow_const 2) (measurable_id.pow_const 2)
    exact hsq_indep.integral_fun_mul_eq_mul_integral
      (hy_meas.pow_const 2).aestronglyMeasurable (hz_meas.pow_const 2).aestronglyMeasurable
  have hsum0 :
      (∑ j, (W i j) ^ 2 * (W k j) ^ 2 * kurt (fun ω => e ω j) P) = 0 := by
    have hcum := cross_fourth_cumulant_eq_sum (P := P) (e := e)
      (fun j => W i j) (fun j => W k j) hmeas hindep hL4 hcent
    simpa [y, z, hy2z2_int, hyz_int] using hcum.symm
  intro j
  rcases hsign with hpos | hneg
  · have hterm0 :
        (W i j) ^ 2 * (W k j) ^ 2 * kurt (fun ω => e ω j) P = 0 := by
      have hnonneg :
          ∀ x ∈ (Finset.univ : Finset (Fin n)),
            0 ≤ (W i x) ^ 2 * (W k x) ^ 2 * kurt (fun ω => e ω x) P := by
        intro x _
        have hsq : 0 ≤ (W i x) ^ 2 * (W k x) ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
        exact mul_nonneg hsq (le_of_lt (hpos x))
      exact (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum0 j (Finset.mem_univ j)
    have hkurt_ne : kurt (fun ω => e ω j) P ≠ 0 := ne_of_gt (hpos j)
    have hsqsq : (W i j) ^ 2 * (W k j) ^ 2 = 0 := by
      exact (mul_eq_zero.mp hterm0).resolve_right hkurt_ne
    have hpowsq : (W i j * W k j) ^ 2 = 0 := by
      simpa [mul_pow] using hsqsq
    exact eq_zero_of_pow_eq_zero hpowsq
  · have hsum0_neg :
        (∑ x, -((W i x) ^ 2 * (W k x) ^ 2 * kurt (fun ω => e ω x) P)) = 0 := by
      rw [Finset.sum_neg_distrib, hsum0, neg_zero]
    have hterm0_neg :
        -((W i j) ^ 2 * (W k j) ^ 2 * kurt (fun ω => e ω j) P) = 0 := by
      have hnonneg :
          ∀ x ∈ (Finset.univ : Finset (Fin n)),
            0 ≤ -((W i x) ^ 2 * (W k x) ^ 2 * kurt (fun ω => e ω x) P) := by
        intro x _
        have hsq : 0 ≤ (W i x) ^ 2 * (W k x) ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
        have hk : kurt (fun ω => e ω x) P ≤ 0 := le_of_lt (hneg x)
        exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos hsq hk)
      exact (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum0_neg j (Finset.mem_univ j)
    have hterm0 : (W i j) ^ 2 * (W k j) ^ 2 * kurt (fun ω => e ω j) P = 0 := by
      linarith
    have hkurt_ne : kurt (fun ω => e ω j) P ≠ 0 := ne_of_lt (hneg j)
    have hsqsq : (W i j) ^ 2 * (W k j) ^ 2 = 0 := by
      exact (mul_eq_zero.mp hterm0).resolve_right hkurt_ne
    have hpowsq : (W i j * W k j) ^ 2 = 0 := by
      simpa [mul_pow] using hsqsq
    exact eq_zero_of_pow_eq_zero hpowsq

end Causalean.Discovery.LiNGAM
