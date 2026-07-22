/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.ML.Kernel.SquaredLoss

/-! # Margin-based classification — Lipschitz surrogate excess-risk rate

The statistical rate for empirical risk minimization of a **margin surrogate** loss
`φ(y·⟪w, x⟩)` over the `W`-ball of linear classifiers, for any `L`-Lipschitz surrogate `φ`
(hinge, logistic, smoothed 0–1, …).  Features lie in the `Xb`-ball and labels in `[-Yb, Yb]`
(`Yb = 1` for `±1` classification).

The Rademacher complexity of the surrogate-loss class is bounded by a single application of the
infinite-index Ledoux–Talagrand contraction: the margin `g_w(x,y) = y·⟪w,x⟩ = ⟪w, y·x⟩` is a
linear class over the rescaled features `y·x` (bound `Yb·Xb`), and the centered surrogate
`φ̃ = φ − φ(0)` is `LipschitzAt0` with constant `L`, so
`RC(φ̃ ∘ g) ≤ 2L·RC(g) ≤ 2L·Yb·Xb·W/√n`.  The constant `φ(0)` cancels in both the ERM
comparison and the excess risk.  Combined with the separable ERM oracle inequality this gives
`margin_erm_surrogate_excess_rate`, a tail bound at threshold `8·L·Yb·Xb·W/√n + 2ε`.
-/

namespace Causalean.ML

open MeasureTheory ProbabilityTheory Real Causalean.Stat.Concentration

/-- **Margin surrogate ERM excess-risk rate.**  For an `L`-Lipschitz surrogate `φ`, features in
the `Xb`-ball, labels in `[-Yb, Yb]`, and linear classifiers in the `W`-ball, any empirical
surrogate-risk minimizer `ŵ` against a comparator `wstar` has excess population surrogate risk
exceeding `8·L·Yb·Xb·W/√n + 2ε` with probability at most `exp(-ε²tn)`. -/
theorem margin_erm_surrogate_excess_rate {d n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Xb Yb W L : ℝ}
    (hXb : 0 ≤ Xb) (hYb : 0 ≤ Yb) (hW : 0 ≤ W) (hL : 0 ≤ L)
    (φ : ℝ → ℝ) (hLip : ∀ s t, |φ s - φ t| ≤ L * |s - t|)
    (X : Ω → KFeat d Xb Yb) (hX : Measurable X)
    {t : ℝ} (ht' : t * (L * (Yb * Xb * W)) ^ 2 ≤ 1 / 2) {ε : ℝ} (hε : 0 ≤ ε)
    (ŵ : (Fin n → Ω) → KWeight d W) (wstar : KWeight d W)
    (hERM : ∀ ω : Fin n → Ω,
      (n : ℝ)⁻¹ * ∑ k, φ (((X (ω k)).2 : ℝ) *
            inner ℝ ((ŵ ω) : EuclideanSpace ℝ (Fin d)) ((X (ω k)).1 : EuclideanSpace ℝ (Fin d)))
        ≤ (n : ℝ)⁻¹ * ∑ k, φ (((X (ω k)).2 : ℝ) *
            inner ℝ (wstar : EuclideanSpace ℝ (Fin d)) ((X (ω k)).1 : EuclideanSpace ℝ (Fin d)))) :
    (Measure.pi (fun _ : Fin n => μ)
      (fun ω => 8 * L * (Yb * Xb * W) / Real.sqrt (n : ℝ) + 2 * ε
        < μ[fun ω' => φ (((X ω').2 : ℝ) *
              inner ℝ ((ŵ ω) : EuclideanSpace ℝ (Fin d)) ((X ω').1 : EuclideanSpace ℝ (Fin d)))]
          - μ[fun ω' => φ (((X ω').2 : ℝ) *
              inner ℝ (wstar : EuclideanSpace ℝ (Fin d))
                ((X ω').1 : EuclideanSpace ℝ (Fin d)))])).toReal
      ≤ (- ε ^ 2 * t * n).exp := by
  classical
  haveI : Nonempty (KFeat d Xb Yb) := ⟨(⟨0, by simpa using hXb⟩, ⟨0, by simpa using hYb⟩)⟩
  haveI : Nonempty (KWeight d W) := ⟨⟨0, by simpa using hW⟩⟩
  -- the margin `g w a = y·⟪w,x⟩`, the centered surrogate `f`, and the genuine surrogate
  set p : KWeight d W → KFeat d Xb Yb → ℝ :=
    fun w a => ((a.2 : ℝ)) * inner ℝ (w : EuclideanSpace ℝ (Fin d))
      (a.1 : EuclideanSpace ℝ (Fin d)) with hp
  set f : KWeight d W → KFeat d Xb Yb → ℝ := fun w a => φ (p w a) - φ 0 with hf
  set surr : KWeight d W → KFeat d Xb Yb → ℝ := fun w a => φ (p w a) with hsurr
  -- Lipschitz surrogate facts
  have hφlipWith : LipschitzWith (Real.toNNReal L) φ := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal L hL]
    exact hLip x y
  have hφcont : Continuous φ := hφlipWith.continuous
  have hφtilde : LipschitzAt0 (fun s => φ s - φ 0) L := by
    refine ⟨by simp, fun x y => ?_⟩
    have hrw : (φ x - φ 0) - (φ y - φ 0) = φ x - φ y := by ring
    simpa [hrw] using hLip x y
  have hYbXbW : 0 ≤ Yb * Xb * W := by positivity
  -- pointwise bound on the margin
  have hpbound : ∀ (w : KWeight d W) (a : KFeat d Xb Yb), |p w a| ≤ Yb * Xb * W := by
    intro w a
    have hw : ‖(w : EuclideanSpace ℝ (Fin d))‖ ≤ W := by
      simpa using (mem_closedBall_zero_iff.mp w.2)
    have hx : ‖(a.1 : EuclideanSpace ℝ (Fin d))‖ ≤ Xb := by
      simpa using (mem_closedBall_zero_iff.mp a.1.2)
    have hy : |(a.2 : ℝ)| ≤ Yb := by simpa using (mem_closedBall_zero_iff.mp a.2.2)
    have hinner : |inner ℝ (w : EuclideanSpace ℝ (Fin d)) (a.1 : EuclideanSpace ℝ (Fin d))|
        ≤ Xb * W := by
      calc |inner ℝ (w : EuclideanSpace ℝ (Fin d)) (a.1 : EuclideanSpace ℝ (Fin d))|
            ≤ ‖(w : EuclideanSpace ℝ (Fin d))‖ * ‖(a.1 : EuclideanSpace ℝ (Fin d))‖ :=
              abs_real_inner_le_norm _ _
        _ ≤ W * Xb := mul_le_mul hw hx (norm_nonneg _) hW
        _ = Xb * W := by ring
    rw [hp, abs_mul]
    nlinarith [hy, hinner, abs_nonneg ((a.2 : ℝ)),
      abs_nonneg (inner ℝ (w : EuclideanSpace ℝ (Fin d)) (a.1 : EuclideanSpace ℝ (Fin d))),
      hYb, hXb, hW]
  -- `f` uniform bound `b = L·Yb·Xb·W`
  have hb0 : (0 : ℝ) ≤ L * (Yb * Xb * W) := by positivity
  have hfbound : ∀ (w : KWeight d W) (a : KFeat d Xb Yb), |f w a| ≤ L * (Yb * Xb * W) := by
    intro w a
    have h := hφtilde.2 (p w a) 0
    rw [hφtilde.1, sub_zero, sub_zero] at h
    calc |f w a| = |φ (p w a) - φ 0| := by rw [hf]
      _ ≤ L * |p w a| := h
      _ ≤ L * (Yb * Xb * W) := mul_le_mul_of_nonneg_left (hpbound w a) hL
  -- continuity of margin and surrogate
  have hcont_x1 : Continuous (fun a : KFeat d Xb Yb => (a.1 : EuclideanSpace ℝ (Fin d))) :=
    continuous_subtype_val.comp continuous_fst
  have hcont_x2 : Continuous (fun a : KFeat d Xb Yb => (a.2 : ℝ)) :=
    continuous_subtype_val.comp continuous_snd
  have hpcont_a : ∀ w : KWeight d W, Continuous (fun a : KFeat d Xb Yb => p w a) := by
    intro w
    exact hcont_x2.mul (continuous_const.inner hcont_x1)
  have hpcont_w : ∀ a : KFeat d Xb Yb, Continuous (fun w : KWeight d W => p w a) := by
    intro a
    exact continuous_const.mul (continuous_subtype_val.inner continuous_const)
  have hfcont_a : ∀ w : KWeight d W, Continuous (fun a : KFeat d Xb Yb => f w a) := by
    intro w
    exact (hφcont.comp (hpcont_a w)).sub continuous_const
  have hfcont_w : ∀ a : KFeat d Xb Yb, Continuous (fun w : KWeight d W => f w a) := by
    intro a
    exact (hφcont.comp (hpcont_w a)).sub continuous_const
  have hfmeas : ∀ w : KWeight d W, Measurable (f w) := fun w => (hfcont_a w).measurable
  -- Rademacher complexity of the centered surrogate class via contraction
  have hRC : rademacherComplexity n f μ X ≤ 2 * L * (Yb * Xb * W) / Real.sqrt (n : ℝ) := by
    have hemp : ∀ S : Fin n → KFeat d Xb Yb,
        empiricalRademacherComplexity n f S ≤ 2 * L * (Yb * Xb * W) / Real.sqrt (n : ℝ) := by
      intro S
      -- margin complexity from the linear L²-ball bound over features `y·x`
      set featM : KFeat d Xb Yb → EuclideanSpace ℝ (Fin d) :=
        fun a => (a.2 : ℝ) • (a.1 : EuclideanSpace ℝ (Fin d)) with hfeatM
      have hmem : ∀ a : KFeat d Xb Yb,
          featM a ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (Yb * Xb) := by
        intro a
        rw [mem_closedBall_zero_iff, hfeatM, norm_smul, Real.norm_eq_abs]
        have hy : |(a.2 : ℝ)| ≤ Yb := by simpa using (mem_closedBall_zero_iff.mp a.2.2)
        have hx : ‖(a.1 : EuclideanSpace ℝ (Fin d))‖ ≤ Xb := by
          simpa using (mem_closedBall_zero_iff.mp a.1.2)
        nlinarith [hy, hx, abs_nonneg ((a.2 : ℝ)),
          norm_nonneg (a.1 : EuclideanSpace ℝ (Fin d)), hYb, hXb]
      have hpfun : p
          = (fun (w : KWeight d W) (a : KFeat d Xb Yb) =>
              inner ℝ (w : EuclideanSpace ℝ (Fin d)) (featM a)) := by
        funext w a
        rw [hp, hfeatM, real_inner_smul_right]
      have hpS : empiricalRademacherComplexity n p S ≤ Yb * Xb * W / Real.sqrt (n : ℝ) := by
        rw [hpfun]
        have h := linear_predictor_l2_bound' (d := d) (n := n) (ι := KWeight d W)
          (W := W) (X := Yb * Xb) (by positivity) hW
          (fun k => ⟨featM (S k), hmem (S k)⟩) (fun w => w)
        simpa [Function.comp_def, mul_assoc] using h
      have hcontr := empiricalRademacherComplexity_contraction_abs_of_bddAbove
        (ι := KWeight d W) (fun s => φ s - φ 0) (L := L) hL hφtilde p
        (M := Yb * Xb * W) hYbXbW hpbound n S
      have hfeq : empiricalRademacherComplexity n f S
          = empiricalRademacherComplexity n
              (fun (w : KWeight d W) (a : KFeat d Xb Yb) => (fun s => φ s - φ 0) (p w a)) S :=
        rfl
      rw [hfeq]
      calc empiricalRademacherComplexity n
            (fun (w : KWeight d W) (a : KFeat d Xb Yb) => (fun s => φ s - φ 0) (p w a)) S
            ≤ 2 * L * empiricalRademacherComplexity n p S := hcontr
        _ ≤ 2 * L * (Yb * Xb * W / Real.sqrt (n : ℝ)) :=
              mul_le_mul_of_nonneg_left hpS (by positivity)
        _ = 2 * L * (Yb * Xb * W) / Real.sqrt (n : ℝ) := by ring
    have hnn : ∀ ω : Fin n → Ω, 0 ≤ empiricalRademacherComplexity n f (X ∘ ω) := by
      intro ω
      unfold empiricalRademacherComplexity
      refine mul_nonneg (by positivity) (Finset.sum_nonneg fun σ _ => ?_)
      exact Real.iSup_nonneg fun i => abs_nonneg _
    unfold rademacherComplexity
    calc ∫ ω, empiricalRademacherComplexity n f (X ∘ ω) ∂(Measure.pi fun _ : Fin n => μ)
          ≤ ∫ _ω, 2 * L * (Yb * Xb * W) / Real.sqrt (n : ℝ) ∂(Measure.pi fun _ : Fin n => μ) := by
            apply integral_mono_of_nonneg (Filter.Eventually.of_forall hnn) (integrable_const _)
            exact Filter.Eventually.of_forall (fun ω => hemp (X ∘ ω))
      _ = 2 * L * (Yb * Xb * W) / Real.sqrt (n : ℝ) := by simp
  -- `f`-ERM from the surrogate ERM hypothesis (constant `φ 0` cancels)
  have hERMf : ∀ ω : Fin n → Ω,
      (n : ℝ)⁻¹ * ∑ k, f (ŵ ω) (X (ω k)) ≤ (n : ℝ)⁻¹ * ∑ k, f wstar (X (ω k)) := by
    intro ω
    have hrw : ∀ w : KWeight d W, (n : ℝ)⁻¹ * ∑ k, f w (X (ω k))
        = (n : ℝ)⁻¹ * ∑ k, surr w (X (ω k)) - (n : ℝ)⁻¹ * ∑ _k : Fin n, φ 0 := by
      intro w
      rw [← mul_sub, ← Finset.sum_sub_distrib]
    rw [hrw (ŵ ω), hrw wstar]
    have hE := hERM ω
    simp only [hsurr, hp]
    linarith [hE]
  have key := erm_oracle_inequality_separable (μ := μ) (n := n) (f := f)
    hfmeas X hX (b := L * (Yb * Xb * W)) hb0 hfbound hfcont_w ht' hε ŵ wstar hERMf
  refine le_trans ?_ key
  rw [ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)]
  apply measure_mono
  intro ω hω
  -- population split: `∫ f w = ∫ surr w − φ 0`
  have hpop : ∀ w : KWeight d W, μ[fun ω' => f w (X ω')]
      = μ[fun ω' => surr w (X ω')] - φ 0 := by
    intro w
    have hInt_surr : Integrable (fun ω' => surr w (X ω')) μ := by
      have hmeas := ((hφcont.comp (hpcont_a w)).measurable.comp hX).aestronglyMeasurable (μ := μ)
      refine Integrable.of_bound hmeas (|φ 0| + L * (Yb * Xb * W)) ?_
      filter_upwards with ω'
      have h := hφtilde.2 (p w (X ω')) 0
      rw [hφtilde.1, sub_zero, sub_zero] at h
      rw [Real.norm_eq_abs]
      calc |surr w (X ω')| = |φ (p w (X ω'))| := by rw [hsurr]
        _ = |φ 0 + (φ (p w (X ω')) - φ 0)| := by ring_nf
        _ ≤ |φ 0| + |φ (p w (X ω')) - φ 0| := abs_add_le _ _
        _ ≤ |φ 0| + L * (Yb * Xb * W) := by
            have := h.trans (mul_le_mul_of_nonneg_left (hpbound w (X ω')) hL)
            linarith
    have hpt : (fun ω' => f w (X ω')) = (fun ω' => surr w (X ω') - φ 0) := by
      funext ω'; rw [hf, hsurr]
    rw [hpt, integral_sub hInt_surr (integrable_const _)]
    simp
  have hexc : μ[fun ω' => f (ŵ ω) (X ω')] - μ[fun ω' => f wstar (X ω')]
      = μ[fun ω' => surr (ŵ ω) (X ω')] - μ[fun ω' => surr wstar (X ω')] := by
    rw [hpop (ŵ ω), hpop wstar]; ring
  have hgoal_eq :
      μ[fun ω' => φ (((X ω').2 : ℝ) *
            inner ℝ ((ŵ ω) : EuclideanSpace ℝ (Fin d)) ((X ω').1 : EuclideanSpace ℝ (Fin d)))]
        - μ[fun ω' => φ (((X ω').2 : ℝ) *
            inner ℝ (wstar : EuclideanSpace ℝ (Fin d)) ((X ω').1 : EuclideanSpace ℝ (Fin d)))]
        = μ[fun ω' => surr (ŵ ω) (X ω')] - μ[fun ω' => surr wstar (X ω')] := by
    simp only [hsurr, hp]
  have hthr : 4 • rademacherComplexity n f μ X + 2 * ε
      ≤ 8 * L * (Yb * Xb * W) / Real.sqrt (n : ℝ) + 2 * ε := by
    have he : 4 • rademacherComplexity n f μ X = 4 * rademacherComplexity n f μ X := by
      simp [nsmul_eq_mul]
    rw [he]
    have h4 : 4 * rademacherComplexity n f μ X
        ≤ 8 * L * (Yb * Xb * W) / Real.sqrt (n : ℝ) := by
      calc 4 * rademacherComplexity n f μ X
            ≤ 4 * (2 * L * (Yb * Xb * W) / Real.sqrt (n : ℝ)) :=
              mul_le_mul_of_nonneg_left hRC (by norm_num)
        _ = 8 * L * (Yb * Xb * W) / Real.sqrt (n : ℝ) := by ring
    linarith
  change 4 • rademacherComplexity n f μ X + 2 * ε
      < μ[fun ω' => f (ŵ ω) (X ω')] - μ[fun ω' => f wstar (X ω')]
  refine lt_of_le_of_lt hthr ?_
  rw [hexc, ← hgoal_eq]
  exact hω

end Causalean.ML
