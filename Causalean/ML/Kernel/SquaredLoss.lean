/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.ML.Surrogate.ClampedSquare
import Causalean.Stat.Concentration.UniformDeviation.ERMOracle
import FoML.Main

/-! # Kernel / L²-ball linear predictors — squared-loss excess-risk rate

The genuine **squared-loss** statistical rate for empirical risk minimization over an
`L²`-norm-bounded class of linear predictors `a ↦ ⟪w, a⟫` (the dual/feature-space view of
kernel ridge).  Unlike the bare-linear-functional version, the loss here is the regression
loss `(⟪w, x⟩ − y)²`.

The Rademacher complexity of the squared-loss class is bounded by decomposing the *centered*
loss `(⟪w,x⟩ − y)² − y² = ⟪w,x⟩² − 2y⟪w,x⟩`:

* the **quadratic part** `⟪w,x⟩²` is handled by the (infinite-index) Ledoux–Talagrand
  contraction with the clamped square as the Lipschitz surrogate, reducing to the linear
  L²-ball bound;
* the **cross part** `2y⟪w,x⟩ = ⟪w, 2y·x⟩` is *itself* a linear class over rescaled features,
  handled directly by the linear L²-ball bound.

Combined with the generic ERM oracle inequality (`erm_oracle_inequality_separable`) this gives
the `O(1/√n)` squared-loss excess-risk rate `kernel_erm_squaredLoss_excess_rate`.
-/

namespace Causalean.ML

open MeasureTheory ProbabilityTheory Real Causalean.Stat.Concentration

/-- Feature × response data space: `Xb`-ball features paired with `[-Yb, Yb]` responses. -/
abbrev KFeat (d : ℕ) (Xb Yb : ℝ) : Type :=
  Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) Xb × Metric.closedBall (0 : ℝ) Yb

/-- The `W`-ball of weight vectors. -/
abbrev KWeight (d : ℕ) (W : ℝ) : Type :=
  Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) W

/-- **Kernel ERM squared-loss excess-risk rate over the L² ball.**  Features lie in the closed
`Xb`-ball, responses in `[-Yb, Yb]`, and linear predictors are indexed by the closed `W`-ball.
For the squared (regression) loss `(⟪w, x⟩ − y)²`, any empirical-risk minimizer `ŵ` against a
comparator `wstar` has excess population risk exceeding
`4·(4(XbW)² + 2·Yb·Xb·W)/√n + 2ε` with probability at most `exp(-ε²tn)`. -/
theorem kernel_erm_squaredLoss_excess_rate {d n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Xb Yb W : ℝ}
    (hXb : 0 ≤ Xb) (hYb : 0 ≤ Yb) (hW : 0 ≤ W)
    (X : Ω → KFeat d Xb Yb) (hX : Measurable X)
    {t : ℝ} (ht' : t * ((Xb * W) ^ 2 + 2 * Yb * (Xb * W)) ^ 2 ≤ 1 / 2) {ε : ℝ} (hε : 0 ≤ ε)
    (ŵ : (Fin n → Ω) → KWeight d W) (wstar : KWeight d W)
    (hERM : ∀ ω : Fin n → Ω,
      (n : ℝ)⁻¹ * ∑ k, (inner ℝ ((ŵ ω) : EuclideanSpace ℝ (Fin d))
            ((X (ω k)).1 : EuclideanSpace ℝ (Fin d)) - ((X (ω k)).2 : ℝ)) ^ 2
        ≤ (n : ℝ)⁻¹ * ∑ k, (inner ℝ (wstar : EuclideanSpace ℝ (Fin d))
            ((X (ω k)).1 : EuclideanSpace ℝ (Fin d)) - ((X (ω k)).2 : ℝ)) ^ 2) :
    (Measure.pi (fun _ : Fin n => μ)
      (fun ω => 4 * ((4 * (Xb * W) ^ 2 + 2 * Yb * Xb * W) / Real.sqrt (n : ℝ)) + 2 * ε
        < μ[fun ω' => (inner ℝ ((ŵ ω) : EuclideanSpace ℝ (Fin d))
              ((X ω').1 : EuclideanSpace ℝ (Fin d)) - ((X ω').2 : ℝ)) ^ 2]
          - μ[fun ω' => (inner ℝ (wstar : EuclideanSpace ℝ (Fin d))
              ((X ω').1 : EuclideanSpace ℝ (Fin d)) - ((X ω').2 : ℝ)) ^ 2])).toReal
      ≤ (- ε ^ 2 * t * n).exp := by
  classical
  haveI : Nonempty (KFeat d Xb Yb) := ⟨(⟨0, by simpa using hXb⟩, ⟨0, by simpa using hYb⟩)⟩
  haveI : Nonempty (KWeight d W) := ⟨⟨0, by simpa using hW⟩⟩
  -- linear predictor and squared/centered losses
  set p : KWeight d W → KFeat d Xb Yb → ℝ :=
    fun w a => inner ℝ (w : EuclideanSpace ℝ (Fin d)) (a.1 : EuclideanSpace ℝ (Fin d)) with hp
  set φ : ℝ → ℝ := clampedSq (Xb * W) with hφdef
  set f : KWeight d W → KFeat d Xb Yb → ℝ :=
    fun w a => φ (p w a) - 2 * (a.2 : ℝ) * p w a with hf
  set sqLoss : KWeight d W → KFeat d Xb Yb → ℝ :=
    fun w a => (p w a - (a.2 : ℝ)) ^ 2 with hsq
  have hXbW : 0 ≤ Xb * W := mul_nonneg hXb hW
  -- pointwise bounds on the predictor
  have hpbound : ∀ (w : KWeight d W) (a : KFeat d Xb Yb), |p w a| ≤ Xb * W := by
    intro w a
    have hw : ‖(w : EuclideanSpace ℝ (Fin d))‖ ≤ W := by
      simpa using (mem_closedBall_zero_iff.mp w.2)
    have ha : ‖(a.1 : EuclideanSpace ℝ (Fin d))‖ ≤ Xb := by
      simpa using (mem_closedBall_zero_iff.mp a.1.2)
    calc |p w a| ≤ ‖(w : EuclideanSpace ℝ (Fin d))‖ * ‖(a.1 : EuclideanSpace ℝ (Fin d))‖ :=
          abs_real_inner_le_norm _ _
      _ ≤ W * Xb := mul_le_mul hw ha (norm_nonneg _) hW
      _ = Xb * W := by ring
  have hybound : ∀ a : KFeat d Xb Yb, |(a.2 : ℝ)| ≤ Yb := by
    intro a
    simpa using (mem_closedBall_zero_iff.mp a.2.2)
  -- `f` is the centered squared loss: `sqLoss = f + y²`
  have hsqf : ∀ (w : KWeight d W) (a : KFeat d Xb Yb), sqLoss w a = f w a + ((a.2 : ℝ)) ^ 2 := by
    intro w a
    have hclamp : φ (p w a) = (p w a) ^ 2 := by
      rw [hφdef]; exact clampedSq_eq_sq (hpbound w a)
    simp only [hsq, hf, hclamp]
    ring
  -- uniform bound on `f`
  have hb0 : (0 : ℝ) ≤ (Xb * W) ^ 2 + 2 * Yb * (Xb * W) := by positivity
  have hfbound : ∀ (w : KWeight d W) (a : KFeat d Xb Yb),
      |f w a| ≤ (Xb * W) ^ 2 + 2 * Yb * (Xb * W) := by
    intro w a
    have h1 : |φ (p w a)| ≤ (Xb * W) ^ 2 := by
      rw [hφdef, abs_of_nonneg (clampedSq_nonneg _ _)]
      exact clampedSq_le_sq hXbW _
    have h2 : |2 * (a.2 : ℝ) * p w a| ≤ 2 * Yb * (Xb * W) := by
      rw [abs_mul, abs_mul, show |(2 : ℝ)| = 2 from by norm_num]
      nlinarith [hybound a, hpbound w a, abs_nonneg ((a.2 : ℝ)), abs_nonneg (p w a), hYb, hXbW]
    calc |f w a| = |φ (p w a) - 2 * (a.2 : ℝ) * p w a| := by rw [hf]
      _ ≤ |φ (p w a)| + |2 * (a.2 : ℝ) * p w a| := abs_sub _ _
      _ ≤ (Xb * W) ^ 2 + 2 * Yb * (Xb * W) := add_le_add h1 h2
  -- continuity of the predictor and losses
  have hcont_x1 : Continuous (fun a : KFeat d Xb Yb => (a.1 : EuclideanSpace ℝ (Fin d))) :=
    continuous_subtype_val.comp continuous_fst
  have hcont_x2 : Continuous (fun a : KFeat d Xb Yb => (a.2 : ℝ)) :=
    continuous_subtype_val.comp continuous_snd
  have hpcont_a : ∀ w : KWeight d W, Continuous (fun a : KFeat d Xb Yb => p w a) := by
    intro w
    exact continuous_const.inner hcont_x1
  have hpcont_w : ∀ a : KFeat d Xb Yb, Continuous (fun w : KWeight d W => p w a) := by
    intro a
    exact continuous_subtype_val.inner continuous_const
  have hfcont_a : ∀ w : KWeight d W, Continuous (fun a : KFeat d Xb Yb => f w a) := by
    intro w
    exact ((continuous_clampedSq _).comp (hpcont_a w)).sub
      ((continuous_const.mul hcont_x2).mul (hpcont_a w))
  have hfcont_w : ∀ a : KFeat d Xb Yb, Continuous (fun w : KWeight d W => f w a) := by
    intro a
    exact ((continuous_clampedSq _).comp (hpcont_w a)).sub
      (continuous_const.mul (hpcont_w a))
  have hfmeas : ∀ w : KWeight d W, Measurable (f w) := fun w => (hfcont_a w).measurable
  -- Rademacher-complexity bound for the centered squared-loss class
  set Cf : ℝ := 4 * (Xb * W) ^ 2 + 2 * Yb * Xb * W with hCf
  have hRC : rademacherComplexity n f μ X ≤ Cf / Real.sqrt (n : ℝ) := by
    -- uniform empirical bound, over every sample
    have hemp : ∀ S : Fin n → KFeat d Xb Yb,
        empiricalRademacherComplexity n f S ≤ Cf / Real.sqrt (n : ℝ) := by
      intro S
      -- (1) predictor complexity from the linear L²-ball bound
      have hpS : empiricalRademacherComplexity n p S ≤ Xb * W / Real.sqrt (n : ℝ) := by
        have h := linear_predictor_l2_bound' (d := d) (n := n) (ι := KWeight d W) (W := W)
          (X := Xb) hXb hW (fun k => (S k).1) (fun w => w)
        simpa [hp, Function.comp_def] using h
      -- (2) quadratic part via contraction with the clamped square
      have hquadbd : ∀ (w : KWeight d W) (a : KFeat d Xb Yb), |φ (p w a)| ≤ (Xb * W) ^ 2 := by
        intro w a
        rw [hφdef, abs_of_nonneg (clampedSq_nonneg _ _)]
        exact clampedSq_le_sq hXbW _
      have hcontr := empiricalRademacherComplexity_contraction_abs_of_bddAbove
        (ι := KWeight d W) φ (L := 2 * (Xb * W)) (by positivity)
        (by rw [hφdef]; exact lipschitzAt0_clampedSq hXbW) p (M := Xb * W) hXbW hpbound n S
      have hquad : empiricalRademacherComplexity n
          (fun (w : KWeight d W) (a : KFeat d Xb Yb) => φ (p w a)) S
            ≤ 4 * (Xb * W) ^ 2 / Real.sqrt (n : ℝ) := by
        calc empiricalRademacherComplexity n
              (fun (w : KWeight d W) (a : KFeat d Xb Yb) => φ (p w a)) S
              ≤ 2 * (2 * (Xb * W)) * empiricalRademacherComplexity n p S := hcontr
          _ ≤ 2 * (2 * (Xb * W)) * (Xb * W / Real.sqrt (n : ℝ)) :=
                mul_le_mul_of_nonneg_left hpS (by positivity)
          _ = 4 * (Xb * W) ^ 2 / Real.sqrt (n : ℝ) := by ring
      -- (3) cross part: a linear class over rescaled features `2y·x`
      set featCross : KFeat d Xb Yb → EuclideanSpace ℝ (Fin d) :=
        fun a => (2 * (a.2 : ℝ)) • (a.1 : EuclideanSpace ℝ (Fin d)) with hfeat
      have hmem : ∀ a : KFeat d Xb Yb,
          featCross a ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (2 * Yb * Xb) := by
        intro a
        rw [mem_closedBall_zero_iff, hfeat, norm_smul, Real.norm_eq_abs, abs_mul,
          show |(2 : ℝ)| = 2 from by norm_num]
        have hx : ‖(a.1 : EuclideanSpace ℝ (Fin d))‖ ≤ Xb := by
          simpa using mem_closedBall_zero_iff.mp a.1.2
        nlinarith [hybound a, hx, abs_nonneg ((a.2 : ℝ)),
          norm_nonneg (a.1 : EuclideanSpace ℝ (Fin d)), hYb, hXb]
      have hcrossfun : (fun (w : KWeight d W) (a : KFeat d Xb Yb) => 2 * (a.2 : ℝ) * p w a)
          = (fun (w : KWeight d W) (a : KFeat d Xb Yb) =>
              inner ℝ (w : EuclideanSpace ℝ (Fin d)) (featCross a)) := by
        funext w a
        rw [hfeat, real_inner_smul_right, hp]
      have hcrossS : empiricalRademacherComplexity n
          (fun (w : KWeight d W) (a : KFeat d Xb Yb) => 2 * (a.2 : ℝ) * p w a) S
            ≤ 2 * Yb * Xb * W / Real.sqrt (n : ℝ) := by
        rw [hcrossfun]
        have h := linear_predictor_l2_bound' (d := d) (n := n) (ι := KWeight d W)
          (W := W) (X := 2 * Yb * Xb) (by positivity) hW
          (fun k => ⟨featCross (S k), hmem (S k)⟩) (fun w => w)
        simpa [Function.comp_def] using h
      -- (4) combine the two parts via sub-additivity
      have hcrossbd : ∀ (w : KWeight d W) (a : KFeat d Xb Yb),
          |2 * (a.2 : ℝ) * p w a| ≤ 2 * Yb * (Xb * W) := by
        intro w a
        rw [abs_mul, abs_mul, show |(2 : ℝ)| = 2 from by norm_num]
        nlinarith [hybound a, hpbound w a, abs_nonneg ((a.2 : ℝ)), abs_nonneg (p w a), hYb, hXbW]
      have hsub := empiricalRademacherComplexity_sub_le (ι := KWeight d W)
        (fun (w : KWeight d W) (a : KFeat d Xb Yb) => φ (p w a))
        (fun (w : KWeight d W) (a : KFeat d Xb Yb) => 2 * (a.2 : ℝ) * p w a)
        (MF := (Xb * W) ^ 2) (MG := 2 * Yb * (Xb * W)) (by positivity) (by positivity)
        hquadbd hcrossbd n S
      have hfeq : empiricalRademacherComplexity n f S
          = empiricalRademacherComplexity n
              (fun (w : KWeight d W) (a : KFeat d Xb Yb) => φ (p w a) - 2 * (a.2 : ℝ) * p w a) S :=
        rfl
      rw [hfeq]
      calc empiricalRademacherComplexity n
            (fun (w : KWeight d W) (a : KFeat d Xb Yb) => φ (p w a) - 2 * (a.2 : ℝ) * p w a) S
            ≤ empiricalRademacherComplexity n
                (fun (w : KWeight d W) (a : KFeat d Xb Yb) => φ (p w a)) S
              + empiricalRademacherComplexity n
                (fun (w : KWeight d W) (a : KFeat d Xb Yb) => 2 * (a.2 : ℝ) * p w a) S := hsub
        _ ≤ 4 * (Xb * W) ^ 2 / Real.sqrt (n : ℝ) + 2 * Yb * Xb * W / Real.sqrt (n : ℝ) :=
              add_le_add hquad hcrossS
        _ = Cf / Real.sqrt (n : ℝ) := by rw [← add_div]
    -- integrate the uniform empirical bound
    have hnn : ∀ ω : Fin n → Ω, 0 ≤ empiricalRademacherComplexity n f (X ∘ ω) := by
      intro ω
      unfold empiricalRademacherComplexity
      refine mul_nonneg (by positivity) (Finset.sum_nonneg fun σ _ => ?_)
      exact Real.iSup_nonneg fun i => abs_nonneg _
    unfold rademacherComplexity
    calc ∫ ω, empiricalRademacherComplexity n f (X ∘ ω) ∂(Measure.pi fun _ : Fin n => μ)
          ≤ ∫ _ω, Cf / Real.sqrt (n : ℝ) ∂(Measure.pi fun _ : Fin n => μ) := by
            apply integral_mono_of_nonneg (Filter.Eventually.of_forall hnn) (integrable_const _)
            exact Filter.Eventually.of_forall (fun ω => hemp (X ∘ ω))
      _ = Cf / Real.sqrt (n : ℝ) := by simp
  -- the `f`-ERM hypothesis follows from the squared-loss ERM hypothesis
  have hERMf : ∀ ω : Fin n → Ω,
      (n : ℝ)⁻¹ * ∑ k, f (ŵ ω) (X (ω k)) ≤ (n : ℝ)⁻¹ * ∑ k, f wstar (X (ω k)) := by
    intro ω
    have hrw : ∀ w : KWeight d W, (n : ℝ)⁻¹ * ∑ k, f w (X (ω k))
        = (n : ℝ)⁻¹ * ∑ k, sqLoss w (X (ω k)) - (n : ℝ)⁻¹ * ∑ k, ((X (ω k)).2 : ℝ) ^ 2 := by
      intro w
      rw [← mul_sub, ← Finset.sum_sub_distrib]
      refine congrArg _ (Finset.sum_congr rfl fun k _ => ?_)
      have := hsqf w (X (ω k))
      linarith
    rw [hrw (ŵ ω), hrw wstar]
    have hE := hERM ω
    simp only [hsq, hp]
    linarith [hE]
  have key := erm_oracle_inequality_separable (μ := μ) (n := n) (f := f)
    hfmeas X hX (b := (Xb * W) ^ 2 + 2 * Yb * (Xb * W)) hb0 hfbound hfcont_w ht' hε ŵ wstar hERMf
  -- transport from `f`-excess to genuine squared-loss excess
  refine le_trans ?_ key
  rw [ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)]
  apply measure_mono
  intro ω hω
  -- population split: `∫ f w = ∫ sqLoss w − ∫ y²`
  have hsqcont_a : ∀ w : KWeight d W, Continuous (fun a : KFeat d Xb Yb => sqLoss w a) := by
    intro w
    exact ((hpcont_a w).sub hcont_x2).pow 2
  have hpop : ∀ w : KWeight d W, μ[fun ω' => f w (X ω')]
      = μ[fun ω' => sqLoss w (X ω')] - μ[fun ω' => ((X ω').2 : ℝ) ^ 2] := by
    intro w
    have hInt_sq : Integrable (fun ω' => sqLoss w (X ω')) μ := by
      refine Integrable.of_bound (((hsqcont_a w).measurable.comp hX).aestronglyMeasurable)
        ((Xb * W + Yb) ^ 2) ?_
      filter_upwards with ω'
      have hpy : |p w (X ω') - ((X ω').2 : ℝ)| ≤ Xb * W + Yb :=
        (abs_sub _ _).trans (add_le_add (hpbound w (X ω')) (hybound (X ω')))
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ sqLoss w (X ω'))]
      have heq : sqLoss w (X ω') = |p w (X ω') - ((X ω').2 : ℝ)| ^ 2 := by
        rw [hsq, sq_abs]
      rw [heq]
      nlinarith [hpy, abs_nonneg (p w (X ω') - ((X ω').2 : ℝ))]
    have hInt_y : Integrable (fun ω' => ((X ω').2 : ℝ) ^ 2) μ := by
      refine Integrable.of_bound ((hcont_x2.pow 2).measurable.comp hX).aestronglyMeasurable
        (Yb ^ 2) ?_
      filter_upwards with ω'
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [hybound (X ω'), sq_abs ((X ω').2 : ℝ), abs_nonneg ((X ω').2 : ℝ)]
    have hpt : (fun ω' => f w (X ω'))
        = (fun ω' => sqLoss w (X ω') - ((X ω').2 : ℝ) ^ 2) := by
      funext ω'; have := hsqf w (X ω'); linarith
    rw [hpt, integral_sub hInt_sq hInt_y]
  -- f-excess equals squared-loss excess (the `y²` term cancels)
  have hexc : μ[fun ω' => f (ŵ ω) (X ω')] - μ[fun ω' => f wstar (X ω')]
      = μ[fun ω' => sqLoss (ŵ ω) (X ω')] - μ[fun ω' => sqLoss wstar (X ω')] := by
    rw [hpop (ŵ ω), hpop wstar]; ring
  have hgoal_eq :
      μ[fun ω' => (inner ℝ ((ŵ ω) : EuclideanSpace ℝ (Fin d))
            ((X ω').1 : EuclideanSpace ℝ (Fin d)) - ((X ω').2 : ℝ)) ^ 2]
        - μ[fun ω' => (inner ℝ (wstar : EuclideanSpace ℝ (Fin d))
            ((X ω').1 : EuclideanSpace ℝ (Fin d)) - ((X ω').2 : ℝ)) ^ 2]
        = μ[fun ω' => sqLoss (ŵ ω) (X ω')] - μ[fun ω' => sqLoss wstar (X ω')] := by
    simp only [hsq, hp]
  have hthr : 4 • rademacherComplexity n f μ X + 2 * ε
      ≤ 4 * (Cf / Real.sqrt (n : ℝ)) + 2 * ε := by
    have he : 4 • rademacherComplexity n f μ X = 4 * rademacherComplexity n f μ X := by
      simp [nsmul_eq_mul]
    rw [he]; nlinarith [hRC, Real.sqrt_nonneg (n : ℝ)]
  change 4 • rademacherComplexity n f μ X + 2 * ε
      < μ[fun ω' => f (ŵ ω) (X ω')] - μ[fun ω' => f wstar (X ω')]
  refine lt_of_le_of_lt hthr ?_
  rw [hexc, ← hgoal_eq]
  exact hω

end Causalean.ML
