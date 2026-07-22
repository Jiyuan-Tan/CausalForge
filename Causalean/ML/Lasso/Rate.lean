/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Stat.Concentration.UniformDeviation.ERMOracle

/-! # Lasso / L¹-ball linear predictors — Rademacher rate

The statistical rate for empirical risk minimization over an `L¹`-norm-bounded class of
linear predictors `a ↦ ∑ⱼ wⱼ aⱼ` (the lasso constraint set).  Over `L∞`-bounded features,
the Rademacher complexity of the `L¹`-ball class carries the characteristic `√(log d)`
dimension factor: `≤ (X∞·W/√n)·√(2 log 2d)`.  Combined with the generic ERM oracle
inequality this gives the `O(√(log d / n))` excess-risk rate that distinguishes lasso in
high dimensions.

Built on FoML's `linear_predictor_l1_bound'` (Massart finite-class bound for the L¹-ball,
lifted here to the expected `rademacherComplexity`).
-/

namespace Causalean.ML

open MeasureTheory ProbabilityTheory Real Causalean.Stat.Concentration

/-- **Rademacher complexity of the L¹-ball linear class.**  Over `L∞`-bounded features
(`|Xⱼ| ≤ X∞`), the expected Rademacher complexity of the class of linear predictors with
`L¹` weight norm `≤ W` is at most `(X∞·W/√n)·√(2 log 2d)`. -/
theorem rademacherComplexity_l1_ball_le {d n : ℕ} (hd : 0 < d) (hn : 0 < n) {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {Xinf W : ℝ}
    (hXinf : 0 ≤ Xinf) (hW : 0 ≤ W)
    (X : Ω → EuclideanSpace ℝ (Fin d))
    (hXbound : ∀ ω j, |X ω j| ≤ Xinf) :
    rademacherComplexity n
      (fun w : L1Ball (d := d) W =>
        fun a : EuclideanSpace ℝ (Fin d) => ∑ j, w.1 j * a j)
      μ X ≤ (Xinf * W / Real.sqrt (n : ℝ)) * Real.sqrt (2 * Real.log (2 * d)) := by
  classical
  letI : Nonempty (L1Ball (d := d) W) := ⟨⟨0, by simpa [l1Norm] using hW⟩⟩
  let C : ℝ := (Xinf * W / Real.sqrt (n : ℝ)) * Real.sqrt (2 * Real.log (2 * d))
  have hpoint : ∀ ω : Fin n → Ω,
      empiricalRademacherComplexity n
        (fun w : L1Ball (d := d) W =>
          fun a : EuclideanSpace ℝ (Fin d) => ∑ j, w.1 j * a j)
        (X ∘ ω) ≤ C := by
    intro ω
    have h := linear_predictor_l1_bound' (ι := L1Ball (d := d) W)
      (Xinf := Xinf) (W := W) hXinf hW hd hn
      (Y' := fun k => ⟨X (ω k), fun j => hXbound (ω k) j⟩)
      (w' := id)
    simpa [C, Function.comp_def] using h
  unfold rademacherComplexity
  calc
    (∫ ω : Fin n → Ω,
        empiricalRademacherComplexity n
          (fun w : L1Ball (d := d) W =>
            fun a : EuclideanSpace ℝ (Fin d) => ∑ j, w.1 j * a j)
          (X ∘ ω) ∂Measure.pi (fun _ => μ))
        ≤ ∫ _ω : Fin n → Ω, C ∂Measure.pi (fun _ => μ) := by
          apply MeasureTheory.integral_mono_of_nonneg
          · exact Filter.Eventually.of_forall fun _ω => by
              unfold empiricalRademacherComplexity
              exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
                (Finset.sum_nonneg fun _σ _ => Real.iSup_nonneg fun _i => abs_nonneg _)
          · exact integrable_const C
          · exact Filter.Eventually.of_forall hpoint
    _ = (Xinf * W / Real.sqrt (n : ℝ)) * Real.sqrt (2 * Real.log (2 * d)) := by
      simp [C]

/-- **Lasso ERM excess-risk rate over the L¹ ball.**  For `L∞`-bounded feature vectors
and linear predictors indexed by the `L¹` ball, any empirical-risk minimizer against a
comparator `wstar` has excess population risk larger than
`4·(X∞·W/√n)·√(2 log 2d) + 2ε` with probability at most `exp(-ε²tn)`. -/
theorem lasso_erm_excess_rate {d n : ℕ} (hd : 0 < d) (hn : 0 < n) {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] {Xinf W : ℝ}
    (hXinf : 0 ≤ Xinf) (hW : 0 ≤ W)
    (X : Ω → LinftyBall (d := d) Xinf)
    (hX : Measurable fun ω => (X ω).1)
    {t : ℝ} (ht' : t * (Xinf * W) ^ 2 ≤ 1 / 2) {ε : ℝ} (hε : 0 ≤ ε)
    (ŵ : (Fin n → Ω) → L1Ball (d := d) W) (wstar : L1Ball (d := d) W)
    (hERM : ∀ ω : Fin n → Ω,
      (n : ℝ)⁻¹ * ∑ k, ∑ j, (ŵ ω).1 j * (X (ω k)).1 j
        ≤ (n : ℝ)⁻¹ * ∑ k, ∑ j, wstar.1 j * (X (ω k)).1 j) :
    (Measure.pi (fun _ : Fin n => μ)
      (fun ω => 4 * ((Xinf * W / Real.sqrt (n : ℝ)) *
          Real.sqrt (2 * Real.log (2 * d))) + 2 * ε
        < μ[fun ω' => ∑ j, (ŵ ω).1 j * (X ω').1 j]
          - μ[fun ω' => ∑ j, wstar.1 j * (X ω').1 j])).toReal
      ≤ (- ε ^ 2 * t * n).exp := by
  classical
  let 𝒳 := LinftyBall (d := d) Xinf
  let ι := L1Ball (d := d) W
  letI : MeasurableSpace 𝒳 :=
    MeasurableSpace.comap (fun a : 𝒳 => (a.1 : EuclideanSpace ℝ (Fin d))) inferInstance
  letI : TopologicalSpace ι :=
    inferInstanceAs
      (TopologicalSpace {w : EuclideanSpace ℝ (Fin d) // l1Norm (d := d) w ≤ W})
  haveI : TopologicalSpace.SeparableSpace ι :=
    inferInstanceAs
      (TopologicalSpace.SeparableSpace
        {w : EuclideanSpace ℝ (Fin d) // l1Norm (d := d) w ≤ W})
  haveI : FirstCountableTopology ι :=
    inferInstanceAs
      (FirstCountableTopology {w : EuclideanSpace ℝ (Fin d) // l1Norm (d := d) w ≤ W})
  let f : ι → 𝒳 → ℝ := fun w a => ∑ j, w.1 j * a.1 j
  have hXmeas : Measurable X := by
    rw [measurable_comap_iff]
    exact hX
  haveI : Nonempty 𝒳 := ⟨⟨0, by intro j; simpa using hXinf⟩⟩
  haveI : Nonempty ι := ⟨⟨0, by simpa [l1Norm, ι] using hW⟩⟩
  have hb : 0 ≤ Xinf * W := mul_nonneg hXinf hW
  have hf : ∀ w : ι, Measurable (f w) := by
    intro w
    let g : EuclideanSpace ℝ (Fin d) → ℝ := fun a => ∑ j, w.1 j * a j
    have hg : Measurable g := by
      dsimp [g]
      fun_prop
    change Measurable (g ∘ fun a : 𝒳 => (a.1 : EuclideanSpace ℝ (Fin d)))
    exact hg.comp (comap_measurable (fun a : 𝒳 => (a.1 : EuclideanSpace ℝ (Fin d))))
  have hf' : ∀ w : ι, ∀ a : 𝒳, |f w a| ≤ Xinf * W := by
    intro w a
    have hlinear :
        |∑ j : Fin d, w.1 j * a.1 j| ≤ l1Norm (d := d) w.1 * Xinf := by
      exact abs_sum_mul_le_l1_mul (d := d) (w := w.1) (z := a.1) (M := Xinf) a.2
    calc
      |f w a| ≤ l1Norm (d := d) w.1 * Xinf := by
        simpa [f]
          using hlinear
      _ ≤ W * Xinf := mul_le_mul_of_nonneg_right w.2 hXinf
      _ = Xinf * W := by ring
  have hf'' : ∀ a : 𝒳, Continuous fun w : ι => f w a := by
    intro a
    let g : EuclideanSpace ℝ (Fin d) → ℝ := fun w => ∑ j, w j * a.1 j
    have hg : Continuous g := by
      dsimp [g]
      fun_prop
    change Continuous (g ∘ fun w : ι => (w.1 : EuclideanSpace ℝ (Fin d)))
    exact hg.comp continuous_subtype_val
  have hRC :
      rademacherComplexity n f μ X ≤
        (Xinf * W / Real.sqrt (n : ℝ)) * Real.sqrt (2 * Real.log (2 * d)) := by
    let C : ℝ := (Xinf * W / Real.sqrt (n : ℝ)) * Real.sqrt (2 * Real.log (2 * d))
    have hpoint : ∀ ω : Fin n → Ω, empiricalRademacherComplexity n f (X ∘ ω) ≤ C := by
      intro ω
      have h := linear_predictor_l1_bound' (ι := ι)
        (Xinf := Xinf) (W := W) hXinf hW hd hn
        (Y' := X ∘ ω)
        (w' := id)
      simpa [C, f, 𝒳, ι, Function.comp_def] using h
    unfold rademacherComplexity
    calc
      (∫ ω : Fin n → Ω, empiricalRademacherComplexity n f (X ∘ ω)
          ∂Measure.pi (fun _ => μ))
          ≤ ∫ _ω : Fin n → Ω, C ∂Measure.pi (fun _ => μ) := by
            apply MeasureTheory.integral_mono_of_nonneg
            · exact Filter.Eventually.of_forall fun _ω => by
                unfold empiricalRademacherComplexity
                exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
                  (Finset.sum_nonneg fun _σ _ => Real.iSup_nonneg fun _i => abs_nonneg _)
            · exact integrable_const C
            · exact Filter.Eventually.of_forall hpoint
      _ = (Xinf * W / Real.sqrt (n : ℝ)) * Real.sqrt (2 * Real.log (2 * d)) := by
        simp [C]
  have key := erm_oracle_inequality_separable (μ := μ) (n := n) (f := f)
    hf X hXmeas (b := Xinf * W) hb hf' hf'' ht' hε ŵ wstar hERM
  refine le_trans ?_ key
  rw [ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)]
  apply measure_mono
  intro ω hω
  have hthreshold :
      4 • rademacherComplexity n f μ X + 2 * ε
        ≤ 4 * ((Xinf * W / Real.sqrt (n : ℝ)) *
            Real.sqrt (2 * Real.log (2 * d))) + 2 * ε := by
    calc
      4 • rademacherComplexity n f μ X + 2 * ε
          = 4 * rademacherComplexity n f μ X + 2 * ε := by simp [nsmul_eq_mul]
      _ ≤ 4 * ((Xinf * W / Real.sqrt (n : ℝ)) *
            Real.sqrt (2 * Real.log (2 * d))) + 2 * ε := by
        nlinarith [hRC]
  exact lt_of_le_of_lt hthreshold hω

end Causalean.ML
