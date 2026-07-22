/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Experimentation.SuperPopulation.MeanCLT.Field

/-!
# Field hypotheses for the standardized network field

The abstract network CLT `networkSum_clt` consumes three facts about the summand field: the
summands are **mean-zero**, the network sum has **unit total variance**, and the summands are
**uniformly bounded**.  For the standardized field `centeredNormalizedField` (summand
`Xᵢ = (Yᵢ − E[Yᵢ]) / s`) all three are *derived* here from the outcome-level assumptions — they are
not re-assumed.

* `centeredNormalizedField_integral_eq_zero` — mean-zero: `E[Xᵢ] = (E[Yᵢ] − E[Yᵢ])/s = 0`.
* `centeredNormalizedField_sq_integral` — unit total variance: with `s² = Var(∑ᵢ Yᵢ)`,
  `∫ (∑ᵢ Xᵢ)² = Var(∑ᵢ Yᵢ)/s² = 1`.
* `centeredNormalizedField_abs_le` — uniform bound: `|Xᵢ| ≤ 2c/s` whenever `|Yᵢ − E[Yᵢ]| ≤ c`.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Causalean.Experimentation.SuperPopulation.MeanCLT

open Causalean.Experimentation.SuperPopulation Causalean.SteinMethod

variable {V Ω : Type*} [Fintype V] [DecidableEq V] [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ]
variable (Y : V → Ω → ℝ) (adj : V → V → Prop) [DecidableRel adj]
variable (hrefl : ∀ i, adj i i) (hsymm : ∀ i j, adj i j → adj j i)
variable (hmeasY : ∀ i, Measurable (Y i))
variable (hindepY : ∀ A B : Finset V, (∀ a ∈ A, ∀ b ∈ B, ¬ adj a b) →
    IndepFun (fun ω => fun k : A => Y k ω) (fun ω => fun k : B => Y k ω) μ)

/-- **Mean-zero summands.** Each standardized summand has integral zero:
`E[Xᵢ] = (E[Yᵢ] − E[Yᵢ]) / s = 0`.  (Uses integrability of `Yᵢ`, from `MemLp Yᵢ 2`.) -/
theorem centeredNormalizedField_integral_eq_zero
    (hL2 : ∀ i, MemLp (Y i) 2 μ) (s : ℝ) (i : V) :
    ∫ ω, (centeredNormalizedField Y adj hrefl hsymm hmeasY hindepY s).X i ω ∂μ = 0 := by
  simp only [centeredNormalizedField_X]
  rw [integral_div]
  rw [integral_sub ((hL2 i).integrable (by norm_num)) (integrable_const _)]
  simp [integral_const, probReal_univ]

/-- **Unit total variance.** If `s² = Var(∑ᵢ Yᵢ)` then the standardized network sum
`∑ᵢ Xᵢ = (∑ᵢ Yᵢ − ∑ᵢ E[Yᵢ]) / s` has `∫ (∑ᵢ Xᵢ)² = Var(∑ᵢ Yᵢ)/s² = 1`.  This is the field-variance
hypothesis of `networkSum_clt` (`∫ (depSum X)² = 1`), derived from the outcome sum-variance. -/
theorem centeredNormalizedField_sq_integral
    (hL2 : ∀ i, MemLp (Y i) 2 μ) (s : ℝ) (hs_pos : 0 < s)
    (hs2 : s ^ 2 = variance (fun ω => ∑ i, Y i ω) μ) :
    ∫ ω, (depSum (centeredNormalizedField Y adj hrefl hsymm hmeasY hindepY s).X ω) ^ 2 ∂μ = 1 := by
  let S : Ω → ℝ := fun ω => ∑ i, Y i ω
  let C : ℝ := ∑ i, ∫ x, Y i x ∂μ
  have hs_ne : s ≠ 0 := ne_of_gt hs_pos
  have hS_mem : MemLp S 2 μ := by
    simpa [S] using (memLp_finset_sum Finset.univ (fun i _ => hL2 i))
  have hsum_eq :
      depSum (centeredNormalizedField Y adj hrefl hsymm hmeasY hindepY s).X =
        fun ω => (S ω - C) / s := by
    funext ω
    simp only [depSum, centeredNormalizedField_X]
    dsimp [S, C]
    rw [← Finset.sum_div, Finset.sum_sub_distrib]
  have hS_integral : ∫ ω, S ω ∂μ = C := by
    dsimp [S, C]
    rw [integral_finset_sum Finset.univ]
    intro i _
    exact (hL2 i).integrable (by norm_num)
  have hsum_int_zero :
      ∫ ω, depSum (centeredNormalizedField Y adj hrefl hsymm hmeasY hindepY s).X ω ∂μ =
        0 := by
    rw [hsum_eq, integral_div]
    rw [integral_sub (hS_mem.integrable (by norm_num)) (integrable_const C)]
    simp [hS_integral, integral_const, probReal_univ]
  have hsum_aemeas :
      AEMeasurable
        (depSum (centeredNormalizedField Y adj hrefl hsymm hmeasY hindepY s).X) μ := by
    rw [hsum_eq]
    exact (hS_mem.aemeasurable.sub_const C).div_const s
  rw [← variance_of_integral_eq_zero hsum_aemeas hsum_int_zero, hsum_eq]
  have hscaled_mem : MemLp (fun ω => S ω / s) 2 μ := by
    convert hS_mem.mul_const (1 / s) using 1
    ext ω
    ring
  calc
    variance (fun ω => (S ω - C) / s) μ =
        variance (fun ω => S ω / s) μ := by
      calc
        variance (fun ω => (S ω - C) / s) μ =
            variance (fun ω => S ω / s + (-C / s)) μ := by
          congr
          ext ω
          ring
        _ = variance (fun ω => S ω / s) μ := by
          exact variance_add_const hscaled_mem.aestronglyMeasurable (-C / s)
    _ = variance S μ / s ^ 2 := by
      calc
        variance (fun ω => S ω / s) μ =
            variance (fun ω => S ω * (1 / s)) μ := by
          congr
          ext ω
          ring
        _ = variance S μ * (1 / s) ^ 2 := by
          rw [variance_mul_const]
        _ = variance S μ / s ^ 2 := by
          field_simp [hs_ne]
    _ = 1 := by
      have hvarS : variance S μ = s ^ 2 := by
        simpa [S] using hs2.symm
      rw [hvarS]
      exact div_self (pow_ne_zero 2 hs_ne)

/-- **Uniform summand bound.** If the centered outcomes are bounded, `|Yᵢ − E[Yᵢ]| ≤ c`, then each
standardized summand satisfies `|Xᵢ| ≤ 2c/s` (with `s > 0`).  The tight bound is `c/s`, weakened to
`2c/s` to match the engine's `card·Bₙ³ → 0` smallness with `Bₙ = 2c/s`. -/
theorem centeredNormalizedField_abs_le
    (s : ℝ) (hs_pos : 0 < s) (c : ℝ)
    (hc : ∀ i ω, |Y i ω - ∫ x, Y i x ∂μ| ≤ c) (i : V) (ω : Ω) :
    |(centeredNormalizedField Y adj hrefl hsymm hmeasY hindepY s).X i ω| ≤ 2 * c / s := by
  simp only [centeredNormalizedField_X]
  rw [abs_div, abs_of_pos hs_pos]
  have hc_nonneg : 0 ≤ c := le_trans (abs_nonneg _) (hc i ω)
  calc
    |Y i ω - ∫ x, Y i x ∂μ| / s ≤ c / s := by
      exact div_le_div_of_nonneg_right (hc i ω) hs_pos.le
    _ ≤ 2 * c / s := by
      exact div_le_div_of_nonneg_right (by nlinarith) hs_pos.le

end Causalean.Experimentation.SuperPopulation.MeanCLT
