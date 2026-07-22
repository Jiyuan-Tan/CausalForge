/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Maximal inequality for sub-exponential random variables

A reusable tail bound for the maximum of finitely many mean-zero sub-exponential
random variables, a building block for chaining arguments in empirical-process
theory.

## Main results

* `HasSubexponentialMGF.measure_abs_ge_le` — the two-sided tail bound
  `P(|X| ≥ ε) ≤ 2 exp(−ε² / (2 (v + b ε)))`, obtained from the one-sided
  `measure_ge_le` applied to `X` and `−X`.
* `measure_exists_abs_ge_le` — a finite union bound: for a family `Y i` sharing
  common parameters `(v, b)`, the probability that *some* `|Y i|` exceeds `ε` is
  at most `card · 2 exp(−ε² / (2 (v + b ε)))`.
* `measure_sup'_ge_le` — the same bound rephrased for the pointwise maximum
  `t.sup' (fun i => |Y i ω|)`.
-/

import Causalean.Stat.Concentration.TailBounds.SubExponential

/-! # Finite Maximal Inequalities

This file proves finite-union maximal inequalities for families of
sub-exponential random variables.  The theorem
`HasSubexponentialMGF.measure_abs_ge_le` gives the two-sided tail bound for one
variable, `measure_exists_abs_ge_le` applies a finite union bound to an indexed
family, and `measure_sup'_ge_le` states the same estimate for a finite pointwise
maximum. -/

namespace Causalean.Stat.Concentration

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : Ω → ℝ} {v b : ℝ≥0}

namespace HasSubexponentialMGF

/-- **Two-sided Chernoff bound** for a sub-exponential random variable:
`P(|X| ≥ ε) ≤ 2 exp(−ε² / (2 (v + b ε)))`. -/
theorem measure_abs_ge_le (hX : HasSubexponentialMGF X v b μ) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ |X ω|} ≤ 2 * Real.exp (-ε ^ 2 / (2 * ((v : ℝ) + b * ε))) := by
  haveI := hX.isFiniteMeasure
  have hsub : {ω | ε ≤ |X ω|} ⊆ {ω | ε ≤ X ω} ∪ {ω | ε ≤ -X ω} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω
    rcases le_abs.mp hω with h | h
    · exact Or.inl h
    · exact Or.inr h
  calc μ.real {ω | ε ≤ |X ω|}
      ≤ μ.real ({ω | ε ≤ X ω} ∪ {ω | ε ≤ -X ω}) := measureReal_mono hsub
    _ ≤ μ.real {ω | ε ≤ X ω} + μ.real {ω | ε ≤ -X ω} := measureReal_union_le _ _
    _ ≤ Real.exp (-ε ^ 2 / (2 * ((v : ℝ) + b * ε)))
          + Real.exp (-ε ^ 2 / (2 * ((v : ℝ) + b * ε))) := by
        gcongr
        · exact hX.measure_ge_le hε
        · exact hX.neg.measure_ge_le hε
    _ = 2 * Real.exp (-ε ^ 2 / (2 * ((v : ℝ) + b * ε))) := by ring

end HasSubexponentialMGF

/-- **Maximal inequality (existential form).** For a finite family `Y i`,
`i ∈ t`, of sub-exponential random variables sharing common parameters `(v, b)`,
the probability that some `|Y i|` exceeds `ε` is bounded by the union bound
`card t · 2 exp(−ε² / (2 (v + b ε)))`. -/
theorem measure_exists_abs_ge_le {ι : Type*} (t : Finset ι) (Y : ι → Ω → ℝ) {v b : ℝ≥0}
    (hY : ∀ i ∈ t, HasSubexponentialMGF (Y i) v b μ) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ∃ i ∈ t, ε ≤ |Y i ω|} ≤
      (t.card : ℝ) * (2 * Real.exp (-ε ^ 2 / (2 * ((v : ℝ) + b * ε)))) := by
  have hset : {ω | ∃ i ∈ t, ε ≤ |Y i ω|} = ⋃ i ∈ t, {ω | ε ≤ |Y i ω|} := by
    ext ω; simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
  rw [hset]
  calc μ.real (⋃ i ∈ t, {ω | ε ≤ |Y i ω|})
      ≤ ∑ i ∈ t, μ.real {ω | ε ≤ |Y i ω|} :=
        measureReal_biUnion_finset_le t (fun i => {ω | ε ≤ |Y i ω|})
    _ ≤ ∑ _i ∈ t, (2 * Real.exp (-ε ^ 2 / (2 * ((v : ℝ) + b * ε)))) := by
        apply Finset.sum_le_sum
        intro i hi
        exact (hY i hi).measure_abs_ge_le hε
    _ = (t.card : ℝ) * (2 * Real.exp (-ε ^ 2 / (2 * ((v : ℝ) + b * ε)))) := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- **Maximal inequality (`sup'` form).** The same bound stated for the pointwise
maximum of the `|Y i|`. -/
theorem measure_sup'_ge_le {ι : Type*} (t : Finset ι) (ht : t.Nonempty) (Y : ι → Ω → ℝ)
    {v b : ℝ≥0} (hY : ∀ i ∈ t, HasSubexponentialMGF (Y i) v b μ) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ t.sup' ht (fun i => |Y i ω|)} ≤
      (t.card : ℝ) * (2 * Real.exp (-ε ^ 2 / (2 * ((v : ℝ) + b * ε)))) := by
  have hset : {ω | ε ≤ t.sup' ht (fun i => |Y i ω|)} = {ω | ∃ i ∈ t, ε ≤ |Y i ω|} := by
    ext ω
    simp only [Set.mem_setOf_eq, Finset.le_sup'_iff]
  rw [hset]
  exact measure_exists_abs_ge_le t Y hY hε

end Causalean.Stat.Concentration
