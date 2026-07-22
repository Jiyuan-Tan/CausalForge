/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.ML.Lasso.Rate
import Causalean.ML.Surrogate.ClampedSquare

/-! # Lasso / L¹-ball linear predictors — squared-loss excess-risk rate

The genuine **squared-loss** statistical rate for empirical risk minimization over an
`L¹`-norm-bounded class of linear predictors `a ↦ ∑ⱼ wⱼ aⱼ`.  Features are
`L∞`-bounded and responses are bounded, so the rate carries the lasso
`√(2 log 2d)` dimension factor.

The Rademacher complexity of the squared-loss class is bounded by decomposing the
*centered* loss `(∑ⱼ wⱼxⱼ - y)² - y² = (∑ⱼ wⱼxⱼ)² - 2y∑ⱼ wⱼxⱼ`:

* the **quadratic part** is handled by the infinite-index Ledoux--Talagrand contraction
  with the clamped square as the Lipschitz surrogate, reducing to the lasso linear-class
  bound;
* the **cross part** `2y∑ⱼ wⱼxⱼ` is itself a lasso linear class over the rescaled
  `L∞`-bounded features `2y·x`.

Combined with the generic ERM oracle inequality (`erm_oracle_inequality_separable`) this
gives the `O(√(log d / n))` squared-loss excess-risk rate
`lasso_erm_squaredLoss_excess_rate`.
-/

namespace Causalean.ML

open MeasureTheory ProbabilityTheory Real Causalean.Stat.Concentration

/-- Feature × response data space: `Xinf`-bounded coordinates paired with `[-Yb,Yb]`
responses. -/
abbrev LassoFeat (d : ℕ) (Xinf Yb : ℝ) : Type :=
  LinftyBall (d := d) Xinf × Metric.closedBall (0 : ℝ) Yb

/-- The `W`-ball of weight vectors in coordinate `ℓ¹` norm. -/
abbrev LassoWeight (d : ℕ) (W : ℝ) : Type :=
  L1Ball (d := d) W

/-- **Lasso ERM squared-loss excess-risk rate over the L¹ ball.**  Features are
coordinatewise `L∞`-bounded by `Xinf`, responses lie in `[-Yb,Yb]`, and predictors are
indexed by the coordinate `L¹` ball of radius `W`.  For the squared regression loss
`(∑ⱼ wⱼxⱼ - y)²`, any empirical-risk minimizer `ŵ` against a comparator `wstar` has
excess population risk exceeding
`4·((4(XinfW)² + 2·Yb·Xinf·W)/√n)·√(2 log 2d) + 2ε` with probability at most
`exp(-ε²tn)`. -/
theorem lasso_erm_squaredLoss_excess_rate {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Xinf Yb W : ℝ} (hXinf : 0 ≤ Xinf) (hYb : 0 ≤ Yb) (hW : 0 ≤ W)
    (X : Ω → LassoFeat d Xinf Yb)
    (hXfeat : Measurable fun ω => ((X ω).1).1)
    (hXresp : Measurable fun ω => ((X ω).2 : ℝ))
    {t : ℝ} (ht' : t * ((Xinf * W) ^ 2 + 2 * Yb * (Xinf * W)) ^ 2 ≤ 1 / 2)
    {ε : ℝ} (hε : 0 ≤ ε)
    (ŵ : (Fin n → Ω) → LassoWeight d W) (wstar : LassoWeight d W)
    (hERM : ∀ ω : Fin n → Ω,
      (n : ℝ)⁻¹ * ∑ k,
          (∑ j, (ŵ ω).1 j * ((X (ω k)).1).1 j - ((X (ω k)).2 : ℝ)) ^ 2
        ≤ (n : ℝ)⁻¹ * ∑ k,
          (∑ j, wstar.1 j * ((X (ω k)).1).1 j - ((X (ω k)).2 : ℝ)) ^ 2) :
    (Measure.pi (fun _ : Fin n => μ)
      (fun ω => 4 * (((4 * (Xinf * W) ^ 2 + 2 * Yb * Xinf * W) /
            Real.sqrt (n : ℝ)) * Real.sqrt (2 * Real.log (2 * d))) + 2 * ε
        < μ[fun ω' =>
            (∑ j, (ŵ ω).1 j * ((X ω').1).1 j - ((X ω').2 : ℝ)) ^ 2]
          - μ[fun ω' =>
            (∑ j, wstar.1 j * ((X ω').1).1 j - ((X ω').2 : ℝ)) ^ 2])).toReal
      ≤ (- ε ^ 2 * t * n).exp := by
  classical
  let 𝒳 := LassoFeat d Xinf Yb
  let ι := LassoWeight d W
  let dataVal : 𝒳 → EuclideanSpace ℝ (Fin d) × ℝ :=
    fun a => (((a.1).1 : EuclideanSpace ℝ (Fin d)), (a.2 : ℝ))
  letI : MeasurableSpace 𝒳 := MeasurableSpace.comap dataVal inferInstance
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
  haveI : Nonempty 𝒳 := ⟨(⟨0, by intro j; simpa using hXinf⟩, ⟨0, by simpa using hYb⟩)⟩
  haveI : Nonempty ι := ⟨⟨0, by simpa [l1Norm, ι, LassoWeight] using hW⟩⟩
  have hXmeas : Measurable X := by
    rw [measurable_comap_iff]
    exact hXfeat.prod hXresp
  -- linear predictor and squared/centered losses
  set p : ι → 𝒳 → ℝ := fun w a => ∑ j, w.1 j * ((a.1).1 j) with hp
  set φ : ℝ → ℝ := clampedSq (Xinf * W) with hφdef
  set f : ι → 𝒳 → ℝ :=
    fun w a => φ (p w a) - 2 * (a.2 : ℝ) * p w a with hf
  set sqLoss : ι → 𝒳 → ℝ :=
    fun w a => (p w a - (a.2 : ℝ)) ^ 2 with hsq
  have hXinfW : 0 ≤ Xinf * W := mul_nonneg hXinf hW
  -- pointwise bounds on the predictor
  have hpbound : ∀ (w : ι) (a : 𝒳), |p w a| ≤ Xinf * W := by
    intro w a
    have hlinear :
        |∑ j : Fin d, w.1 j * (a.1).1 j| ≤ l1Norm (d := d) w.1 * Xinf := by
      exact abs_sum_mul_le_l1_mul (d := d) (w := w.1) (z := (a.1).1)
        (M := Xinf) a.1.2
    calc
      |p w a| ≤ l1Norm (d := d) w.1 * Xinf := by
        simpa [hp] using hlinear
      _ ≤ W * Xinf := mul_le_mul_of_nonneg_right w.2 hXinf
      _ = Xinf * W := by ring
  have hybound : ∀ a : 𝒳, |(a.2 : ℝ)| ≤ Yb := by
    intro a
    simpa using (mem_closedBall_zero_iff.mp a.2.2)
  -- `f` is the centered squared loss: `sqLoss = f + y²`
  have hsqf : ∀ (w : ι) (a : 𝒳), sqLoss w a = f w a + ((a.2 : ℝ)) ^ 2 := by
    intro w a
    have hclamp : φ (p w a) = (p w a) ^ 2 := by
      rw [hφdef]; exact clampedSq_eq_sq (hpbound w a)
    simp only [hsq, hf, hclamp]
    ring
  -- uniform bound on `f`
  have hb0 : (0 : ℝ) ≤ (Xinf * W) ^ 2 + 2 * Yb * (Xinf * W) := by positivity
  have hfbound : ∀ (w : ι) (a : 𝒳),
      |f w a| ≤ (Xinf * W) ^ 2 + 2 * Yb * (Xinf * W) := by
    intro w a
    have h1 : |φ (p w a)| ≤ (Xinf * W) ^ 2 := by
      rw [hφdef, abs_of_nonneg (clampedSq_nonneg _ _)]
      exact clampedSq_le_sq hXinfW _
    have h2 : |2 * (a.2 : ℝ) * p w a| ≤ 2 * Yb * (Xinf * W) := by
      rw [abs_mul, abs_mul, show |(2 : ℝ)| = 2 from by norm_num]
      nlinarith [hybound a, hpbound w a, abs_nonneg ((a.2 : ℝ)), abs_nonneg (p w a),
        hYb, hXinfW]
    calc |f w a| = |φ (p w a) - 2 * (a.2 : ℝ) * p w a| := by rw [hf]
      _ ≤ |φ (p w a)| + |2 * (a.2 : ℝ) * p w a| := abs_sub _ _
      _ ≤ (Xinf * W) ^ 2 + 2 * Yb * (Xinf * W) := add_le_add h1 h2
  -- measurability and continuity needed by the oracle
  have hfmeas : ∀ w : ι, Measurable (f w) := by
    intro w
    let g : EuclideanSpace ℝ (Fin d) × ℝ → ℝ :=
      fun z => φ (∑ j, w.1 j * z.1 j) - 2 * z.2 * (∑ j, w.1 j * z.1 j)
    have hg : Measurable g := by
      let lin : EuclideanSpace ℝ (Fin d) × ℝ → ℝ := fun z => ∑ j, w.1 j * z.1 j
      have hlin : Measurable lin := by
        dsimp [lin]
        fun_prop
      have hφlin : Measurable (fun z => φ (lin z)) := by
        rw [hφdef]
        exact (continuous_clampedSq _).measurable.comp hlin
      change Measurable (fun z => φ (lin z) - 2 * z.2 * lin z)
      exact hφlin.sub ((measurable_const.mul measurable_snd).mul hlin)
    change Measurable (g ∘ dataVal)
    exact hg.comp (comap_measurable dataVal)
  have hpcont_w : ∀ a : 𝒳, Continuous (fun w : ι => p w a) := by
    intro a
    let g : EuclideanSpace ℝ (Fin d) → ℝ := fun w => ∑ j, w j * (a.1).1 j
    have hg : Continuous g := by
      dsimp [g]
      fun_prop
    change Continuous (g ∘ fun w : ι => (w.1 : EuclideanSpace ℝ (Fin d)))
    exact hg.comp continuous_subtype_val
  have hfcont_w : ∀ a : 𝒳, Continuous (fun w : ι => f w a) := by
    intro a
    exact ((continuous_clampedSq _).comp (hpcont_w a)).sub
      (continuous_const.mul (hpcont_w a))
  -- Rademacher-complexity bound for the centered squared-loss class
  set logFactor : ℝ := Real.sqrt (2 * Real.log (2 * d)) with hlogFactor
  set Cf : ℝ := 4 * (Xinf * W) ^ 2 + 2 * Yb * Xinf * W with hCf
  have hRC : rademacherComplexity n f μ X ≤ (Cf / Real.sqrt (n : ℝ)) * logFactor := by
    -- uniform empirical bound, over every sample
    have hemp : ∀ S : Fin n → 𝒳,
        empiricalRademacherComplexity n f S ≤ (Cf / Real.sqrt (n : ℝ)) * logFactor := by
      intro S
      -- (1) predictor complexity from the lasso linear-class bound
      have hpS : empiricalRademacherComplexity n p S
          ≤ (Xinf * W / Real.sqrt (n : ℝ)) * logFactor := by
        have h := linear_predictor_l1_bound' (ι := ι)
          (Xinf := Xinf) (W := W) hXinf hW hd hn
          (Y' := fun k => (S k).1)
          (w' := id)
        simpa [p, hp, logFactor, hlogFactor, Function.comp_def] using h
      -- (2) quadratic part via contraction with the clamped square
      have hquadbd : ∀ (w : ι) (a : 𝒳), |φ (p w a)| ≤ (Xinf * W) ^ 2 := by
        intro w a
        rw [hφdef, abs_of_nonneg (clampedSq_nonneg _ _)]
        exact clampedSq_le_sq hXinfW _
      have hcontr := empiricalRademacherComplexity_contraction_abs_of_bddAbove
        (ι := ι) φ (L := 2 * (Xinf * W)) (by positivity)
        (by rw [hφdef]; exact lipschitzAt0_clampedSq hXinfW) p
        (M := Xinf * W) hXinfW hpbound n S
      have hquad : empiricalRademacherComplexity n
          (fun (w : ι) (a : 𝒳) => φ (p w a)) S
            ≤ (4 * (Xinf * W) ^ 2 / Real.sqrt (n : ℝ)) * logFactor := by
        calc empiricalRademacherComplexity n
              (fun (w : ι) (a : 𝒳) => φ (p w a)) S
              ≤ 2 * (2 * (Xinf * W)) * empiricalRademacherComplexity n p S := hcontr
          _ ≤ 2 * (2 * (Xinf * W)) *
                ((Xinf * W / Real.sqrt (n : ℝ)) * logFactor) :=
                mul_le_mul_of_nonneg_left hpS (by positivity)
          _ = (4 * (Xinf * W) ^ 2 / Real.sqrt (n : ℝ)) * logFactor := by ring
      -- (3) cross part: a linear class over rescaled features `2y·x`
      set featCross : 𝒳 → EuclideanSpace ℝ (Fin d) :=
        fun a => (2 * (a.2 : ℝ)) • ((a.1).1 : EuclideanSpace ℝ (Fin d)) with hfeat
      have hmem : ∀ a : 𝒳, ∀ j, |(featCross a) j| ≤ 2 * Yb * Xinf := by
        intro a j
        rw [hfeat]
        simp only [PiLp.smul_apply, smul_eq_mul]
        rw [abs_mul, abs_mul, show |(2 : ℝ)| = 2 from by norm_num]
        nlinarith [hybound a, a.1.2 j, abs_nonneg ((a.2 : ℝ)), abs_nonneg ((a.1).1 j),
          hYb, hXinf]
      have hcrossfun :
          (fun (w : ι) (a : 𝒳) => 2 * (a.2 : ℝ) * p w a)
            = (fun (w : ι) (a : 𝒳) => ∑ j, w.1 j * (featCross a) j) := by
        funext w a
        rw [hp, hfeat]
        simp only [PiLp.smul_apply, smul_eq_mul]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro j _
        ring
      have hcrossS : empiricalRademacherComplexity n
          (fun (w : ι) (a : 𝒳) => 2 * (a.2 : ℝ) * p w a) S
            ≤ (2 * Yb * Xinf * W / Real.sqrt (n : ℝ)) * logFactor := by
        rw [hcrossfun]
        have h := linear_predictor_l1_bound' (ι := ι)
          (Xinf := 2 * Yb * Xinf) (W := W) (by positivity) hW hd hn
          (Y' := fun k => ⟨featCross (S k), hmem (S k)⟩)
          (w' := id)
        simpa [logFactor, hlogFactor, Function.comp_def] using h
      -- (4) combine the two parts via sub-additivity
      have hcrossbd : ∀ (w : ι) (a : 𝒳),
          |2 * (a.2 : ℝ) * p w a| ≤ 2 * Yb * (Xinf * W) := by
        intro w a
        rw [abs_mul, abs_mul, show |(2 : ℝ)| = 2 from by norm_num]
        nlinarith [hybound a, hpbound w a, abs_nonneg ((a.2 : ℝ)), abs_nonneg (p w a),
          hYb, hXinfW]
      have hsub := empiricalRademacherComplexity_sub_le (ι := ι)
        (fun (w : ι) (a : 𝒳) => φ (p w a))
        (fun (w : ι) (a : 𝒳) => 2 * (a.2 : ℝ) * p w a)
        (MF := (Xinf * W) ^ 2) (MG := 2 * Yb * (Xinf * W))
        (by positivity) (by positivity) hquadbd hcrossbd n S
      have hfeq : empiricalRademacherComplexity n f S
          = empiricalRademacherComplexity n
              (fun (w : ι) (a : 𝒳) => φ (p w a) - 2 * (a.2 : ℝ) * p w a) S :=
        rfl
      rw [hfeq]
      calc empiricalRademacherComplexity n
            (fun (w : ι) (a : 𝒳) => φ (p w a) - 2 * (a.2 : ℝ) * p w a) S
            ≤ empiricalRademacherComplexity n
                (fun (w : ι) (a : 𝒳) => φ (p w a)) S
              + empiricalRademacherComplexity n
                (fun (w : ι) (a : 𝒳) => 2 * (a.2 : ℝ) * p w a) S := hsub
        _ ≤ (4 * (Xinf * W) ^ 2 / Real.sqrt (n : ℝ)) * logFactor
              + (2 * Yb * Xinf * W / Real.sqrt (n : ℝ)) * logFactor :=
              add_le_add hquad hcrossS
        _ = (Cf / Real.sqrt (n : ℝ)) * logFactor := by rw [hCf]; ring
    -- integrate the uniform empirical bound
    have hnn : ∀ ω : Fin n → Ω, 0 ≤ empiricalRademacherComplexity n f (X ∘ ω) := by
      intro ω
      unfold empiricalRademacherComplexity
      refine mul_nonneg (by positivity) (Finset.sum_nonneg fun σ _ => ?_)
      exact Real.iSup_nonneg fun i => abs_nonneg _
    unfold rademacherComplexity
    calc ∫ ω, empiricalRademacherComplexity n f (X ∘ ω) ∂(Measure.pi fun _ : Fin n => μ)
          ≤ ∫ _ω, (Cf / Real.sqrt (n : ℝ)) * logFactor
              ∂(Measure.pi fun _ : Fin n => μ) := by
            apply integral_mono_of_nonneg (Filter.Eventually.of_forall hnn) (integrable_const _)
            exact Filter.Eventually.of_forall (fun ω => hemp (X ∘ ω))
      _ = (Cf / Real.sqrt (n : ℝ)) * logFactor := by simp
  -- the `f`-ERM hypothesis follows from the squared-loss ERM hypothesis
  have hERMf : ∀ ω : Fin n → Ω,
      (n : ℝ)⁻¹ * ∑ k, f (ŵ ω) (X (ω k)) ≤ (n : ℝ)⁻¹ * ∑ k, f wstar (X (ω k)) := by
    intro ω
    have hrw : ∀ w : ι, (n : ℝ)⁻¹ * ∑ k, f w (X (ω k))
        = (n : ℝ)⁻¹ * ∑ k, sqLoss w (X (ω k))
          - (n : ℝ)⁻¹ * ∑ k, ((X (ω k)).2 : ℝ) ^ 2 := by
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
    hfmeas X hXmeas (b := (Xinf * W) ^ 2 + 2 * Yb * (Xinf * W)) hb0 hfbound
    hfcont_w ht' hε ŵ wstar hERMf
  -- transport from `f`-excess to genuine squared-loss excess
  refine le_trans ?_ key
  rw [ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)]
  apply measure_mono
  intro ω hω
  -- population split: `∫ f w = ∫ sqLoss w − ∫ y²`
  have hpop : ∀ w : ι, μ[fun ω' => f w (X ω')]
      = μ[fun ω' => sqLoss w (X ω')] - μ[fun ω' => ((X ω').2 : ℝ) ^ 2] := by
    intro w
    have hMeas_sq : Measurable (fun ω' => sqLoss w (X ω')) := by
      let g : EuclideanSpace ℝ (Fin d) × ℝ → ℝ :=
        fun z => (∑ j, w.1 j * z.1 j - z.2) ^ 2
      have hg : Measurable g := by
        dsimp [g]
        fun_prop
      change Measurable (g ∘ fun ω' => (((X ω').1).1, ((X ω').2 : ℝ)))
      exact hg.comp (hXfeat.prod hXresp)
    have hInt_sq : Integrable (fun ω' => sqLoss w (X ω')) μ := by
      refine Integrable.of_bound hMeas_sq.aestronglyMeasurable ((Xinf * W + Yb) ^ 2) ?_
      filter_upwards with ω'
      have hpy : |p w (X ω') - ((X ω').2 : ℝ)| ≤ Xinf * W + Yb :=
        (abs_sub _ _).trans (add_le_add (hpbound w (X ω')) (hybound (X ω')))
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ sqLoss w (X ω'))]
      have heq : sqLoss w (X ω') = |p w (X ω') - ((X ω').2 : ℝ)| ^ 2 := by
        rw [hsq, sq_abs]
      rw [heq]
      nlinarith [hpy, abs_nonneg (p w (X ω') - ((X ω').2 : ℝ))]
    have hMeas_y : Measurable (fun ω' => ((X ω').2 : ℝ) ^ 2) := by
      fun_prop
    have hInt_y : Integrable (fun ω' => ((X ω').2 : ℝ) ^ 2) μ := by
      refine Integrable.of_bound hMeas_y.aestronglyMeasurable (Yb ^ 2) ?_
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
      μ[fun ω' => (∑ j, (ŵ ω).1 j * ((X ω').1).1 j - ((X ω').2 : ℝ)) ^ 2]
        - μ[fun ω' => (∑ j, wstar.1 j * ((X ω').1).1 j - ((X ω').2 : ℝ)) ^ 2]
        = μ[fun ω' => sqLoss (ŵ ω) (X ω')] - μ[fun ω' => sqLoss wstar (X ω')] := by
    simp only [hsq, hp]
  have hthr : 4 • rademacherComplexity n f μ X + 2 * ε
      ≤ 4 * ((Cf / Real.sqrt (n : ℝ)) * logFactor) + 2 * ε := by
    have he : 4 • rademacherComplexity n f μ X = 4 * rademacherComplexity n f μ X := by
      simp [nsmul_eq_mul]
    rw [he]; nlinarith [hRC]
  change 4 • rademacherComplexity n f μ X + 2 * ε
      < μ[fun ω' => f (ŵ ω) (X ω')] - μ[fun ω' => f wstar (X ω')]
  refine lt_of_le_of_lt hthr ?_
  rw [hexc, ← hgoal_eq, hCf, hlogFactor]
  exact hω

end Causalean.ML
