/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Stat.Concentration.Rademacher.Rademacher
import FoML.Main

/-! # Generic ERM oracle inequality via Rademacher complexity

The method-agnostic learning-theory rate: for empirical risk minimization over a
(countable) hypothesis class with a bounded loss, the excess population risk of the
empirical minimizer is controlled by the Rademacher complexity of the loss class plus a
McDiarmid tail term.  This is the engine that turns a complexity bound for a specific
method's loss class into a concrete excess-risk rate.

* `erm_excess_le_two_uniformDeviation` — deterministic ERM basic inequality:
  `R(ĥ) − R(h⋆) ≤ 2·uniformDeviation`.
* `erm_oracle_inequality` — high-probability oracle inequality: chains the basic
  inequality with FoML's symmetrization + McDiarmid tail
  (`uniform_deviation_tail_bound_countable`), giving
  `μⁿ{ 4·𝔯ₙ + 2ε < R(ĥ) − R(h⋆) } ≤ exp(−ε² t n)`.

Built on the FoML `Rademacher`/`uniformDeviation` machinery (re-exported under
`Causalean.Stat.Concentration`).
-/

namespace Causalean.Stat.Concentration

open MeasureTheory ProbabilityTheory Real TopologicalSpace
open scoped ENNReal

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} {𝒳 : Type*}
  {μ : Measure Ω} {f : ι → 𝒳 → ℝ}

local notation "μⁿ" => Measure.pi (fun _ ↦ μ)

/-- **ERM basic inequality (deterministic).** If `ihat` beats the comparator `istar` in
empirical risk on the sample `X ∘ ω` (`Rₙ(ihat) ≤ Rₙ(istar)`), then its excess population
risk is at most twice the uniform deviation of the loss class on that sample. -/
theorem erm_excess_le_two_uniformDeviation [Nonempty ι] [IsProbabilityMeasure μ]
    (X : Ω → 𝒳) (hf : ∀ i, Measurable (f i ∘ X)) (ω : Fin n → Ω)
    {b : ℝ} (hb : 0 ≤ b) (hf' : ∀ i x, |f i x| ≤ b) (ihat istar : ι)
    (hERM : (n : ℝ)⁻¹ * ∑ k, f ihat (X (ω k)) ≤ (n : ℝ)⁻¹ * ∑ k, f istar (X (ω k))) :
    μ[fun ω' => f ihat (X ω')] - μ[fun ω' => f istar (X ω')]
      ≤ 2 * uniformDeviation n f μ X (X ∘ ω) := by
  classical
  let R : ι → ℝ := fun i => μ[fun ω' => f i (X ω')]
  let Rn : ι → ℝ := fun i => (n : ℝ)⁻¹ * ∑ k : Fin n, f i (X (ω k))
  have hRn_bound : ∀ i, |Rn i| ≤ b := by
    intro i
    by_cases hn0 : n = 0
    · simp [Rn, hn0, hb]
    · have hn_pos_nat : 0 < n := Nat.pos_of_ne_zero hn0
      have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn_pos_nat
      calc
        |Rn i| = (n : ℝ)⁻¹ * |∑ k : Fin n, f i (X (ω k))| := by
          dsimp [Rn]
          rw [abs_mul, abs_of_nonneg]
          exact inv_nonneg.mpr (Nat.cast_nonneg _)
        _ ≤ (n : ℝ)⁻¹ * (∑ _k : Fin n, b) := by
          apply mul_le_mul_of_nonneg_left
          · exact (Finset.abs_sum_le_sum_abs (s := Finset.univ)
                (f := fun k : Fin n => f i (X (ω k)))).trans
              (Finset.sum_le_sum fun k _ => hf' i (X (ω k)))
          · positivity
        _ = b := by
          simp
          field_simp [hn_pos.ne']
  have hR_bound : ∀ i, |R i| ≤ b := by
    intro i
    calc
      |R i| ≤ ∫ ω', |f i (X ω')| ∂μ := by
        simpa [R] using
          (MeasureTheory.abs_integral_le_integral_abs
            (μ := μ) (f := fun ω' => f i (X ω')))
      _ ≤ ∫ _ω', b ∂μ := by
        apply integral_mono
        · exact Integrable.of_bound ((hf i).abs.aestronglyMeasurable) b
            (by
              filter_upwards with ω'
              simpa [Real.norm_eq_abs] using hf' i (X ω'))
        · exact integrable_const b
        · intro ω'
          exact hf' i (X ω')
      _ = b := by simp
  have hbdd : BddAbove (Set.range fun i : ι => |Rn i - R i|) := by
    rw [bddAbove_def]
    refine ⟨2 * b, ?_⟩
    intro y hy
    rcases hy with ⟨i, rfl⟩
    calc
      |Rn i - R i| ≤ |Rn i| + |R i| := abs_sub _ _
      _ ≤ 2 * b := by linarith [hRn_bound i, hR_bound i]
  have hdev_le : ∀ i, |Rn i - R i| ≤ uniformDeviation n f μ X (X ∘ ω) := by
    intro i
    dsimp [uniformDeviation]
    simpa [Rn, R, Function.comp_def] using
      (le_ciSup (f := fun j : ι => |Rn j - R j|) hbdd i)
  have hmid : Rn ihat - Rn istar ≤ 0 := by
    dsimp [Rn]
    linarith
  have hleft : R ihat - Rn ihat ≤ |Rn ihat - R ihat| := by
    have h := neg_le_abs (Rn ihat - R ihat)
    linarith
  have hright : Rn istar - R istar ≤ |Rn istar - R istar| := le_abs_self _
  calc
    μ[fun ω' => f ihat (X ω')] - μ[fun ω' => f istar (X ω')]
        = (R ihat - Rn ihat) + (Rn ihat - Rn istar) + (Rn istar - R istar) := by
          simp [R]
    _ ≤ |Rn ihat - R ihat| + 0 + |Rn istar - R istar| := by
      linarith
    _ ≤ uniformDeviation n f μ X (X ∘ ω) + 0 + uniformDeviation n f μ X (X ∘ ω) := by
      linarith [hdev_le ihat, hdev_le istar]
    _ = 2 * uniformDeviation n f μ X (X ∘ ω) := by ring

/-- **Generic ERM oracle inequality (Rademacher).** For the empirical-risk minimizer
`ihat` (beating the comparator `istar` on every sample) over a countable hypothesis class
with `|loss| ≤ b`, the excess population risk exceeds `4·𝔯ₙ + 2ε` with probability at most
`exp(−ε² t n)`, where `𝔯ₙ = rademacherComplexity n f μ X` is the Rademacher complexity of
the loss class.  Chains the deterministic ERM inequality with FoML's symmetrization +
McDiarmid tail. -/
theorem erm_oracle_inequality [MeasurableSpace 𝒳] [Nonempty 𝒳] [Nonempty ι] [Countable ι]
    [IsProbabilityMeasure μ] (hf : ∀ i, Measurable (f i))
    (X : Ω → 𝒳) (hX : Measurable X) {b : ℝ} (hb : 0 ≤ b) (hf' : ∀ i x, |f i x| ≤ b)
    {t : ℝ} (ht' : t * b ^ 2 ≤ 1 / 2) {ε : ℝ} (hε : 0 ≤ ε)
    (ihat : (Fin n → Ω) → ι) (istar : ι)
    (hERM : ∀ ω : Fin n → Ω,
      (n : ℝ)⁻¹ * ∑ k, f (ihat ω) (X (ω k)) ≤ (n : ℝ)⁻¹ * ∑ k, f istar (X (ω k))) :
    (μⁿ (fun ω : Fin n → Ω =>
        4 • rademacherComplexity n f μ X + 2 * ε
          < μ[fun ω' => f (ihat ω) (X ω')] - μ[fun ω' => f istar (X ω')])).toReal
      ≤ (- ε ^ 2 * t * n).exp := by
  classical
  apply le_trans ?_
    (uniform_deviation_tail_bound_countable (μ := μ) (n := n) (f := f) hf X hX hb hf'
      ht' hε)
  rw [ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)]
  apply measure_mono
  intro ω hω
  have hbasic :=
    erm_excess_le_two_uniformDeviation (μ := μ) (n := n) (f := f) X
      (fun i => (hf i).comp hX) ω hb hf' (ihat ω) istar (hERM ω)
  have hlt :
      4 • rademacherComplexity n f μ X + 2 * ε
        < 2 * uniformDeviation n f μ X (X ∘ ω) := by
    exact lt_of_lt_of_le hω hbasic
  have hleft :
      4 • rademacherComplexity n f μ X + 2 * ε
        = 2 * (2 • rademacherComplexity n f μ X + ε) := by
    simp [nsmul_eq_mul]
    ring
  rw [hleft] at hlt
  have hhalf :
      2 • rademacherComplexity n f μ X + ε
        < uniformDeviation n f μ X (X ∘ ω) := by
    nlinarith
  exact le_of_lt hhalf

/-- **Generic ERM oracle inequality (separable class).** Same as `erm_oracle_inequality`
but for a separable, first-countable parameter space `ι` with the loss continuous in the
parameter — the form that applies to the (uncountable but separable) `L²`/`L¹`-ball linear
classes.  Chains the deterministic ERM inequality with FoML's separable tail bound. -/
theorem erm_oracle_inequality_separable [MeasurableSpace 𝒳] [Nonempty 𝒳] [Nonempty ι]
    [TopologicalSpace ι] [SeparableSpace ι] [FirstCountableTopology ι]
    [IsProbabilityMeasure μ] (hf : ∀ i, Measurable (f i))
    (X : Ω → 𝒳) (hX : Measurable X) {b : ℝ} (hb : 0 ≤ b) (hf' : ∀ i x, |f i x| ≤ b)
    (hf'' : ∀ x : 𝒳, Continuous fun i => f i x)
    {t : ℝ} (ht' : t * b ^ 2 ≤ 1 / 2) {ε : ℝ} (hε : 0 ≤ ε)
    (ihat : (Fin n → Ω) → ι) (istar : ι)
    (hERM : ∀ ω : Fin n → Ω,
      (n : ℝ)⁻¹ * ∑ k, f (ihat ω) (X (ω k)) ≤ (n : ℝ)⁻¹ * ∑ k, f istar (X (ω k))) :
    (μⁿ (fun ω : Fin n → Ω =>
        4 • rademacherComplexity n f μ X + 2 * ε
          < μ[fun ω' => f (ihat ω) (X ω')] - μ[fun ω' => f istar (X ω')])).toReal
      ≤ (- ε ^ 2 * t * n).exp := by
  classical
  apply le_trans ?_
    (uniform_deviation_tail_bound_separable (μ := μ) (n := n) (f := f) hf X hX hb hf'
      hf'' ht' hε)
  rw [ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)]
  apply measure_mono
  intro ω hω
  have hbasic :=
    erm_excess_le_two_uniformDeviation (μ := μ) (n := n) (f := f) X
      (fun i => (hf i).comp hX) ω hb hf' (ihat ω) istar (hERM ω)
  have hlt :
      4 • rademacherComplexity n f μ X + 2 * ε
        < 2 * uniformDeviation n f μ X (X ∘ ω) :=
    lt_of_lt_of_le hω hbasic
  have hleft :
      4 • rademacherComplexity n f μ X + 2 * ε
        = 2 * (2 • rademacherComplexity n f μ X + ε) := by
    simp [nsmul_eq_mul]; ring
  rw [hleft] at hlt
  have hhalf :
      2 • rademacherComplexity n f μ X + ε
        < uniformDeviation n f μ X (X ∘ ω) := by nlinarith
  exact le_of_lt hhalf

end Causalean.Stat.Concentration
