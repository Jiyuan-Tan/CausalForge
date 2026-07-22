/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Stat.Concentration.Rademacher.Rademacher
import Causalean.ML.Kernel.RKHS
import FoML.RademacherVariableProperty
import Mathlib.Analysis.InnerProductSpace.Basic

/-! # RKHS-ball Rademacher complexity

This file proves the canonical RKHS-ball empirical Rademacher bound
`Rhat_n({‖f‖_H ≤ r}) ≤ κ * r / sqrt n`, where `κ² = sup_x K(x,x)`.  The main
Hilbert-space theorem is `empiricalRademacherComplexity_innerBall_le`; the RKHS
specialization is `rkhs_ball_empiricalRademacher_le`, which uses the reproducing
identity to turn function evaluation into an inner product.  This is the
standard worst-case `O(1 / sqrt n)` kernel learning rate associated with
Bartlett--Mendelson style Rademacher complexity bounds.
-/

namespace Causalean.ML

open Real

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

private theorem weighted_sum_norm_squared_expansion
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} (Y : Fin n → E) (σ : Signs n) :
    ‖∑ k : Fin n, (σ k : ℝ) • Y k‖ ^ 2 =
      ∑ k : Fin n, ∑ l : Fin n, ⟪(σ k : ℝ) • Y k, (σ l : ℝ) • Y l⟫ := by
  let g := fun l => (σ l : ℝ) • Y l
  calc
    _ = ⟪∑ k : Fin n, g k, ∑ l : Fin n, g l⟫ := by
      exact Eq.symm (real_inner_self_eq_norm_sq (∑ k : Fin n, g k))
    _ = ∑ k : Fin n, ⟪g k, ∑ l : Fin n, g l⟫ := by
      exact sum_inner Finset.univ g (∑ l : Fin n, g l)
    _ = ∑ k : Fin n, ∑ l : Fin n, ⟪g k, g l⟫ := by
      apply congrArg
      ext k
      exact inner_sum Finset.univ g (g k)

private theorem individual_weighted_norms_sum
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} (Y : Fin n → E) (σ : Signs n) :
    ∑ k : Fin n, ‖(σ k : ℝ) • Y k‖ ^ 2 =
      ∑ k : Fin n, ∑ l : Fin n,
        if k ≠ l then 0 else ⟪(σ k : ℝ) • Y k, (σ l : ℝ) • Y l⟫ := by
  let g := fun l => (σ l : ℝ) • Y l
  trans ∑ k : Fin n, ⟪g k, g k⟫
  · apply congrArg
    ext k
    exact Eq.symm (real_inner_self_eq_norm_sq (g k))
  · dsimp [g]
    simp

private theorem rademacher_sum_variance_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} (Y : Fin n → E) :
    ∑ σ : Signs n,
      (‖∑ k : Fin n, (σ k : ℝ) • Y k‖ ^ 2 -
        ∑ k : Fin n, ‖(σ k : ℝ) • Y k‖ ^ 2) = 0 := by
  calc
    _ = ∑ σ : Signs n, ∑ k : Fin n, ∑ l : Fin n,
        (if k ≠ l then ⟪(σ k : ℝ) • Y k, (σ l : ℝ) • Y l⟫ else 0) := by
      apply congrArg
      ext σ
      let g (l : Fin n) : E := (σ l : ℝ) • Y l
      rw [weighted_sum_norm_squared_expansion Y σ, individual_weighted_norms_sum Y σ]
      suffices
          (∑ k : Fin n, ∑ l : Fin n, ⟪g k, g l⟫ -
              ∑ k : Fin n, ∑ l : Fin n,
                if k ≠ l then (0 : ℝ) else ⟪g k, g l⟫) =
            ∑ k : Fin n, ∑ l : Fin n,
              if k ≠ l then ⟪g k, g l⟫ else (0 : ℝ) by
        exact this
      calc
        _ = ∑ k : Fin n,
              ((∑ l : Fin n, ⟪g k, g l⟫) -
                (∑ l : Fin n, if k ≠ l then (0 : ℝ) else ⟪g k, g l⟫)) := by
          simp
        _ = ∑ k : Fin n, ∑ l : Fin n,
              (⟪g k, g l⟫ - if k ≠ l then (0 : ℝ) else ⟪g k, g l⟫) := by
          apply congrArg
          ext k
          simp
        _ = ∑ k : Fin n, ∑ l : Fin n,
              if k ≠ l then ⟪g k, g l⟫ - (0 : ℝ) else
                ⟪g k, g l⟫ - ⟪g k, g l⟫ := by
          apply congrArg
          ext k
          apply congrArg
          ext l
          exact sub_ite (k ≠ l) ⟪g k, g l⟫ 0 ⟪g k, g l⟫
        _ = ∑ k : Fin n, ∑ l : Fin n,
              if k ≠ l then ⟪g k, g l⟫ else (0 : ℝ) := by
          simp
    _ = 0 := by
      have e : ∀ (k l : Fin n), k ≠ l →
          ∑ σ : Signs n, ⟪(σ k : ℝ) • Y k, (σ l : ℝ) • Y l⟫ = 0 := by
        intro k l pkl
        have hrewrite :
            ∑ σ : Signs n, ⟪(σ k : ℝ) • Y k, (σ l : ℝ) • Y l⟫ =
              ∑ σ : Signs n, (σ k : ℝ) * (σ l : ℝ) * ⟪Y k, Y l⟫ := by
          calc
            _ = ∑ σ : Signs n, (σ k : ℝ) * ⟪Y k, (σ l : ℝ) • Y l⟫ := by
              apply congrArg
              ext σ
              exact real_inner_smul_left (Y k) ((σ l : ℝ) • Y l) (σ k : ℝ)
            _ = ∑ σ : Signs n, (σ k : ℝ) * ((σ l : ℝ) * ⟪Y k, Y l⟫) := by
              apply congrArg
              ext σ
              apply congrArg
              exact real_inner_smul_right (Y k) (Y l) (σ l : ℝ)
            _ = _ := by
              apply congrArg
              ext σ
              ring
        rw [hrewrite]
        suffices ∑ σ : Signs n, (σ k : ℝ) * (σ l : ℝ) = (0 : ℝ) by
          calc
            _ = (∑ σ : Signs n, (σ k : ℝ) * (σ l : ℝ)) * ⟪Y k, Y l⟫ := by
              symm
              apply Finset.sum_mul Finset.univ
            _ = 0 * ⟪Y k, Y l⟫ := by rw [this]
            _ = 0 := by simp
        exact rademacher_orthogonality n k l pkl
      calc
        _ = ∑ k : Fin n, ∑ σ : Signs n, ∑ l : Fin n,
            (if k ≠ l then ⟪(σ k : ℝ) • Y k, (σ l : ℝ) • Y l⟫ else 0) := by
          rw [Finset.sum_comm]
        _ = ∑ k : Fin n, ∑ l : Fin n, ∑ σ : Signs n,
            (if k ≠ l then ⟪(σ k : ℝ) • Y k, (σ l : ℝ) • Y l⟫ else 0) := by
          apply congrArg
          ext k
          rw [Finset.sum_comm]
        _ = ∑ k : Fin n, ∑ l : Fin n,
            (if k ≠ l then
              ∑ σ : Signs n, ⟪(σ k : ℝ) • Y k, (σ l : ℝ) • Y l⟫ else 0) := by
          apply congrArg
          ext k
          apply congrArg
          ext l
          simp
        _ = ∑ k : Fin n, ∑ l : Fin n, (if k ≠ l then (0 : ℝ) else 0) := by
          apply congrArg
          ext k
          apply congrArg
          ext l
          exact ite_congr rfl (e k l) (congrFun rfl)
        _ = 0 := by simp

private theorem empiricalRademacherComplexity_innerBall_le_nonempty
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} [Nonempty ι] {n : ℕ}
    (κ r : ℝ) (hκ : 0 ≤ κ) (hr : 0 ≤ r)
    (Y : Fin n → E) (hY : ∀ k, ‖Y k‖ ≤ κ)
    (w : ι → E) (hw : ∀ i, ‖w i‖ ≤ r) :
    empiricalRademacherComplexity n (fun i a => inner ℝ (w i) a) Y
      ≤ κ * r / Real.sqrt n := by
  calc
    _ =
        (Fintype.card (Signs n) : ℝ)⁻¹ *
          ∑ σ : Signs n,
            ⨆ i, ((n : ℝ)⁻¹ *
              |∑ k : Fin n, (σ k : ℝ) * ⟪w i, Y k⟫|) := by
      dsimp only [empiricalRademacherComplexity]
      repeat apply congrArg
      ext σ
      apply congrArg
      ext i
      trans |(n : ℝ)⁻¹| * |∑ k : Fin n, (σ k : ℝ) * ⟪w i, Y k⟫|
      · rw [abs_mul]
      · simp
    _ =
        (Fintype.card (Signs n) : ℝ)⁻¹ *
          ∑ σ : Signs n,
            ((n : ℝ)⁻¹ * ⨆ i, |∑ k : Fin n, (σ k : ℝ) * ⟪w i, Y k⟫|) := by
      repeat apply congrArg
      ext σ
      symm
      apply mul_iSup_of_nonneg
      simp
    _ =
        (Fintype.card (Signs n) : ℝ)⁻¹ *
          ((n : ℝ)⁻¹ *
            ∑ σ : Signs n, (⨆ i, |∑ k : Fin n, (σ k : ℝ) * ⟪w i, Y k⟫|)) := by
      apply congrArg
      symm
      apply Finset.mul_sum
    _ =
        (n : ℝ)⁻¹ *
          ((Fintype.card (Signs n) : ℝ)⁻¹ *
            ∑ σ : Signs n, (⨆ i, |∑ k : Fin n, (σ k : ℝ) * ⟪w i, Y k⟫|)) := by
      ring
    _ =
        (n : ℝ)⁻¹ *
          ((Fintype.card (Signs n) : ℝ)⁻¹ *
            ∑ σ : Signs n,
              ⨆ i, |⟪w i, ∑ k : Fin n, (σ k : ℝ) • Y k⟫|) := by
      repeat apply congrArg
      ext σ
      apply congrArg
      ext i
      apply congrArg
      rw [inner_sum]
      apply congrArg
      ext k
      symm
      apply real_inner_smul_right
    _ ≤
        (n : ℝ)⁻¹ *
          ((Fintype.card (Signs n) : ℝ)⁻¹ *
            ∑ σ : Signs n, ⨆ (_i : ι), r * ‖∑ k : Fin n, (σ k : ℝ) • Y k‖) := by
      repeat apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum
        intro σ _hσ
        apply ciSup_mono
        · rw [bddAbove_def]
          use r * (n * κ)
          intro y hy
          simp only [Int.reduceNeg, Set.range_const, Set.mem_singleton_iff] at hy
          rw [hy]
          apply mul_le_mul
          · simp only [le_refl]
          · have hnorm : ‖∑ k : Fin n, (σ k : ℝ) • Y k‖ ≤ (n : ℝ) * κ := by
              calc
                _ ≤ ∑ k : Fin n, ‖(σ k : ℝ) • Y k‖ := by
                  apply norm_sum_le
                _ = ∑ k : Fin n, ‖Y k‖ := by
                  apply congrArg
                  ext k
                  rw [norm_smul]
                  simp
                _ ≤ ∑ _k : Fin n, κ := by
                  apply Finset.sum_le_sum
                  intro k _hk
                  exact hY k
                _ = (n : ℝ) * κ := by simp
            exact hnorm
          · exact norm_nonneg _
          · exact hr
        · intro i
          trans ‖w i‖ * ‖∑ k : Fin n, (σ k : ℝ) • Y k‖
          · apply abs_real_inner_le_norm
          · apply mul_le_mul_of_nonneg_right
            · exact hw i
            · exact norm_nonneg _
      · simp
      · simp
    _ =
        (n : ℝ)⁻¹ *
          ((Fintype.card (Signs n) : ℝ)⁻¹ *
            ∑ σ : Signs n, r * ‖∑ k : Fin n, (σ k : ℝ) • Y k‖) := by
      repeat apply congrArg
      ext σ
      rw [ciSup_const]
    _ =
        (n : ℝ)⁻¹ *
          ((Fintype.card (Signs n) : ℝ)⁻¹ *
            (r * ∑ σ : Signs n, ‖∑ k : Fin n, (σ k : ℝ) • Y k‖)) := by
      repeat apply congrArg
      rw [Finset.mul_sum]
    _ =
        (n : ℝ)⁻¹ *
          (r * ((Fintype.card (Signs n) : ℝ)⁻¹ *
            ∑ σ : Signs n, ‖∑ k : Fin n, (σ k : ℝ) • Y k‖)) := by
      apply congrArg
      ring
    _ =
        r * (n : ℝ)⁻¹ *
          ((Fintype.card (Signs n) : ℝ)⁻¹ *
            ∑ σ : Signs n, ‖∑ k : Fin n, (σ k : ℝ) • Y k‖) := by
      ring
    _ ≤
        r * (n : ℝ)⁻¹ *
          Real.sqrt
            ((Fintype.card (Signs n) : ℝ)⁻¹ *
              ∑ σ : Signs n, ‖∑ k : Fin n, (σ k : ℝ) • Y k‖ ^ 2) := by
      apply mul_le_mul_of_nonneg_left
      · apply le_sqrt_of_sq_le
        let f (σ : Signs n) := (1 : ℝ)
        let g (σ : Signs n) :=
          ‖∑ k : Fin n, (σ k : ℝ) • Y k‖ * (Fintype.card (Signs n) : ℝ)⁻¹
        suffices
            (∑ σ : Signs n, f σ * g σ) ^ 2 ≤
              (∑ σ : Signs n, (f σ) ^ 2) * (∑ σ : Signs n, (g σ) ^ 2) by
          dsimp [f, g] at this
          simp only [Int.reduceNeg, one_mul, one_pow, Finset.sum_const,
            Finset.card_univ, nsmul_eq_mul, mul_one] at this
          have p :
              ((Fintype.card (Signs n) : ℝ)⁻¹ *
                  ∑ σ : Signs n, ‖∑ k : Fin n, (σ k : ℝ) • Y k‖) =
                ∑ σ : Signs n,
                  ‖∑ k : Fin n, (σ k : ℝ) • Y k‖ *
                    (Fintype.card (Signs n) : ℝ)⁻¹ := by
            trans (∑ σ : Signs n, ‖∑ k : Fin n, (σ k : ℝ) • Y k‖) *
                (Fintype.card (Signs n) : ℝ)⁻¹
            · ring
            · apply Finset.sum_mul
          have q :
              (Fintype.card (Signs n) : ℝ) *
                  ∑ σ : Signs n,
                    (‖∑ k : Fin n, (σ k : ℝ) • Y k‖ *
                      (Fintype.card (Signs n) : ℝ)⁻¹) ^ 2 =
                (Fintype.card (Signs n) : ℝ)⁻¹ *
                  ∑ σ : Signs n, ‖∑ k : Fin n, (σ k : ℝ) • Y k‖ ^ 2 := by
            calc
              _ =
                  (Fintype.card (Signs n) : ℝ) *
                    ∑ σ : Signs n,
                      (‖∑ k : Fin n, (σ k : ℝ) • Y k‖ ^ 2 *
                        ((Fintype.card (Signs n) : ℝ)⁻¹) ^ 2) := by
                repeat apply congrArg
                ext σ
                field_simp
              _ =
                  (Fintype.card (Signs n) : ℝ) *
                    ((∑ σ : Signs n,
                        ‖∑ k : Fin n, (σ k : ℝ) • Y k‖ ^ 2) *
                      ((Fintype.card (Signs n) : ℝ)⁻¹) ^ 2) := by
                apply congrArg
                symm
                apply Finset.sum_mul
              _ =
                  (Fintype.card (Signs n) : ℝ) *
                    ((Fintype.card (Signs n) : ℝ)⁻¹) ^ 2 *
                    (∑ σ : Signs n, ‖∑ k : Fin n, (σ k : ℝ) • Y k‖ ^ 2) := by
                ring
              _ = _ := by
                have hcard :
                    (Fintype.card (Signs n) : ℝ) *
                        ((Fintype.card (Signs n) : ℝ)⁻¹) ^ 2 =
                      (Fintype.card (Signs n) : ℝ)⁻¹ := by
                  calc
                    _ =
                        (Fintype.card (Signs n) : ℝ) *
                          ((Fintype.card (Signs n) : ℝ)⁻¹ *
                            (Fintype.card (Signs n) : ℝ)⁻¹) := by
                      apply congrArg
                      apply pow_two
                    _ =
                        ((Fintype.card (Signs n) : ℝ) *
                            (Fintype.card (Signs n) : ℝ)⁻¹) *
                          (Fintype.card (Signs n) : ℝ)⁻¹ := by
                      symm
                      apply mul_assoc
                    _ = _ := by simp
                rw [hcard]
          rw [p, Eq.symm q]
          exact this
        exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f g
      · by_cases hn : 0 < n
        · aesop
        · simp only [not_lt, nonpos_iff_eq_zero] at hn
          rw [hn]
          simp
    _ =
        r * (n : ℝ)⁻¹ *
          Real.sqrt
            ((Fintype.card (Signs n) : ℝ)⁻¹ *
              ∑ σ : Signs n, ∑ k : Fin n, ‖(σ k : ℝ) • Y k‖ ^ 2) := by
      apply congrArg
      apply congrArg
      apply congrArg
      have hzero := rademacher_sum_variance_zero Y
      simp only [Int.reduceNeg, Finset.sum_sub_distrib] at hzero
      linarith
    _ =
        r * (n : ℝ)⁻¹ *
          Real.sqrt
            ((Fintype.card (Signs n) : ℝ)⁻¹ *
              ∑ σ : Signs n, ∑ k : Fin n, ‖Y k‖ ^ 2) := by
      repeat apply congrArg
      ext σ
      apply congrArg
      ext k
      rw [norm_smul]
      simp
    _ ≤
        r * (n : ℝ)⁻¹ *
          Real.sqrt
            ((Fintype.card (Signs n) : ℝ)⁻¹ *
              ∑ σ : Signs n, ∑ _k : Fin n, κ ^ 2) := by
      apply mul_le_mul_of_nonneg_left
      · apply Real.sqrt_le_sqrt
        apply mul_le_mul_of_nonneg_left
        · apply Finset.sum_le_sum
          intro _σ _hσ
          apply Finset.sum_le_sum
          intro k _hk
          rw [sq_le_sq]
          simp only [abs_norm]
          rw [abs_of_nonneg]
          · exact hY k
          · exact hκ
        · exact le_of_lt (by simp)
      · by_cases hn : 0 < n
        · aesop
        · simp only [not_lt, nonpos_iff_eq_zero] at hn
          rw [hn]
          simp
    _ = r * (n : ℝ)⁻¹ * Real.sqrt ((n : ℝ) * κ ^ 2) := by
      have hq :
          ((Fintype.card (Signs n) : ℝ)⁻¹ *
              ∑ σ : Signs n, ∑ _k : Fin n, κ ^ 2) =
            (n : ℝ) * κ ^ 2 := by
        calc
          _ =
              (Fintype.card (Signs n) : ℝ)⁻¹ *
                ((Fintype.card (Signs n) : ℝ) * ((n : ℝ) * κ ^ 2)) := by
            simp
          _ =
              (Fintype.card (Signs n) : ℝ)⁻¹ *
                (Fintype.card (Signs n) : ℝ) * ((n : ℝ) * κ ^ 2) := by
            ring
          _ = (n : ℝ) * κ ^ 2 := by
            field_simp
      rw [hq]
    _ = r * (n : ℝ)⁻¹ * Real.sqrt (n : ℝ) * κ := by
      have hq : Real.sqrt ((n : ℝ) * κ ^ 2) = Real.sqrt (n : ℝ) * κ := by
        simp only [Nat.cast_nonneg, sqrt_mul, mul_eq_mul_left_iff, sqrt_eq_zero,
          Nat.cast_eq_zero]
        left
        exact sqrt_sq hκ
      rw [hq]
      ring
    _ = κ * r * ((n : ℝ)⁻¹ * Real.sqrt (n : ℝ)) := by ring
    _ = κ * r * (1 / Real.sqrt (n : ℝ)) := by
      by_cases hn : 0 < n
      · rw [(by
          apply eq_one_div_of_mul_eq_one_left
          field_simp
          exact sq_sqrt (Nat.cast_nonneg' n) :
            (n : ℝ)⁻¹ * Real.sqrt (n : ℝ) = 1 / Real.sqrt (n : ℝ))]
      · simp only [not_lt, nonpos_iff_eq_zero] at hn
        rw [hn]
        simp
    _ = κ * r / Real.sqrt (n : ℝ) := by ring

/-- For a sample of vectors bounded by κ and linear weights bounded by r, the empirical
Rademacher complexity of the resulting linear class is at most κ times r divided by the
square root of the sample size.

This is the intrinsic Hilbert-space version of the usual Euclidean norm-ball linear
Rademacher bound. -/
theorem empiricalRademacherComplexity_innerBall_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {ι : Type*} {n : ℕ}
    (κ r : ℝ) (hκ : 0 ≤ κ) (hr : 0 ≤ r)
    (Y : Fin n → E) (hY : ∀ k, ‖Y k‖ ≤ κ)
    (w : ι → E) (hw : ∀ i, ‖w i‖ ≤ r) :
    empiricalRademacherComplexity n (fun i a => inner ℝ (w i) a) Y
      ≤ κ * r / Real.sqrt n := by
  classical
  by_cases hι : Nonempty ι
  · letI : Nonempty ι := hι
    exact empiricalRademacherComplexity_innerBall_le_nonempty κ r hκ hr Y hY w hw
  · haveI : IsEmpty ι := not_nonempty_iff.mp hι
    unfold empiricalRademacherComplexity
    simp only [Signs.card, Nat.cast_pow, Nat.cast_ofNat, Int.reduceNeg, abs_mul, abs_inv,
      Nat.abs_cast, iSup_of_isEmpty, Finset.sum_const_zero, mul_zero, ge_iff_le]
    exact div_nonneg (mul_nonneg hκ hr) (Real.sqrt_nonneg _)

/-- In an RKHS whose sampled kernel representers are bounded by κ, the closed ball of
radius r has empirical Rademacher complexity at most κ times r divided by the square root
of the sample size.

This is the canonical bounded-kernel RKHS-ball rate, using the reproducing identity to
reduce function evaluation to the abstract Hilbert-space linear bound. -/
theorem rkhs_ball_empiricalRademacher_le
    {X H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {feval : H → X → ℝ} {representer : X → H} (hK : IsRKHS X H feval representer)
    {n : ℕ} {κ r : ℝ} (hκ : 0 ≤ κ) (hr : 0 ≤ r)
    (xs : Fin n → X) (hbound : ∀ k, ‖representer (xs k)‖ ≤ κ) :
    empiricalRademacherComplexity n
      (fun (f : {f : H // ‖f‖ ≤ r}) (x : X) => feval (f : H) x) xs
      ≤ κ * r / Real.sqrt n := by
  classical
  let ball := {f : H // ‖f‖ ≤ r}
  let Y : Fin n → H := fun k => representer (xs k)
  let w : ball → H := fun f => (f : H)
  have hw : ∀ f : ball, ‖w f‖ ≤ r := by
    intro f
    exact f.2
  have hlinear :
      empiricalRademacherComplexity n
          (fun (f : ball) (a : H) => inner ℝ (w f) a) Y
        ≤ κ * r / Real.sqrt n := by
    exact empiricalRademacherComplexity_innerBall_le κ r hκ hr Y hbound w hw
  simpa [ball, Y, w, hK.reproducing] using hlinear

end Causalean.ML
