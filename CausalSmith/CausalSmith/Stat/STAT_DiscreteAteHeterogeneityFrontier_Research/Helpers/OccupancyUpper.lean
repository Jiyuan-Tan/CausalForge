/- Occupancy-weighted estimator upper bounds. -/

import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.OccupancyDischarge
import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.Estimators
import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.FactorialCovariance
import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.HeavyCellMoments
import Causalean.Mathlib.Probability.VarianceProd
import Causalean.Stat.Sample.OccupancyWeightedMean

namespace CausalSmith.Stat.DiscreteAteHeterogeneityFrontier

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

-- @node: collisionDesignCenter
/-- The conditional-on-design center of the unclipped occupancy estimator,
totalized by zero when no cell contains both treatment arms. -/
noncomputable def collisionDesignCenter {n d : ℕ} {epsilon M sigma : ℝ}
    (P : ModelClass d epsilon M sigma) (sample : Fin n → Obs d) : ℝ :=
  if 0 < usableTotal sample then
    (∑ k : Fin d, if usableCell sample k then
      (cellCount sample k : ℝ) * cellEffect P.law k else 0) /
        usableTotal sample
  else 0

-- @node: collisionDesignCenter_sub_ate_eq
/-- If [the cell is usable](hyp:husable), [on the usable event, subtracting the ATE from the
  conditional design center is exactly the occupancy-weighted average of the cell
  deviations](goal). -/
lemma collisionDesignCenter_sub_ate_eq {n d : ℕ} {epsilon M sigma : ℝ}
    (P : ModelClass d epsilon M sigma) (sample : Fin n → Obs d)
    (husable : 0 < usableTotal sample) :
    collisionDesignCenter P sample - rawAteFormula P.law =
      (∑ k : Fin d, if usableCell sample k then
        (cellCount sample k : ℝ) * cellDeviation P.law k else 0) /
          usableTotal sample := by
  have hsumNat :
      (∑ k : Fin d, if usableCell sample k then cellCount sample k else 0) =
        usableTotal sample := rfl
  have hsumReal :
      (∑ k : Fin d, if usableCell sample k then
          (cellCount sample k : ℝ) else 0) = (usableTotal sample : ℝ) := by
    exact_mod_cast hsumNat
  have hden : (usableTotal sample : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt husable)
  let w : Fin d → ℝ := fun k =>
    if usableCell sample k then (cellCount sample k : ℝ) else 0
  have hw_sum : ∑ k : Fin d, w k = (usableTotal sample : ℝ) := by
    simpa [w] using hsumReal
  have hcenter :
      (∑ k : Fin d, if usableCell sample k then
          (cellCount sample k : ℝ) * cellEffect P.law k else 0) =
        ∑ k : Fin d, w k * cellEffect P.law k := by
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hu : usableCell sample k <;> simp [w, hu]
  have hdeviation :
      (∑ k : Fin d, if usableCell sample k then
          (cellCount sample k : ℝ) * cellDeviation P.law k else 0) =
        ∑ k : Fin d, w k * cellDeviation P.law k := by
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hu : usableCell sample k <;> simp [w, hu]
  unfold collisionDesignCenter
  rw [if_pos husable]
  rw [hcenter, hdeviation]
  simp_rw [cellDeviation, mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hw_sum]
  field_simp

-- @node: collisionDesignCenter_bias_abs_le
/-- If [the cell is usable](hyp:husable) and [the stated support-size bound holds](hyp:hsupport),
  [if every empirically usable cell is in the population support, approximate homogeneity bounds
  the conditional design bias by `sigma * M`](goal). -/
lemma collisionDesignCenter_bias_abs_le {n d : ℕ} {epsilon M sigma : ℝ}
    (P : ModelClass d epsilon M sigma) (sample : Fin n → Obs d)
    (husable : 0 < usableTotal sample)
    (hsupport : ∀ k, usableCell sample k → 0 < P.law.cellMass k) :
    |collisionDesignCenter P sample - rawAteFormula P.law| ≤ sigma * M := by
  rw [collisionDesignCenter_sub_ate_eq P sample husable, abs_div]
  have hden : (0 : ℝ) < usableTotal sample := by exact_mod_cast husable
  have hnum :
      |∑ k : Fin d, if usableCell sample k then
          (cellCount sample k : ℝ) * cellDeviation P.law k else 0| ≤
        (usableTotal sample : ℝ) * (sigma * M) := by
    calc
      _ ≤ ∑ k : Fin d, |if usableCell sample k then
          (cellCount sample k : ℝ) * cellDeviation P.law k else 0| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k : Fin d, if usableCell sample k then
          (cellCount sample k : ℝ) * (sigma * M) else 0 := by
        apply Finset.sum_le_sum
        intro k hk
        by_cases hu : usableCell sample k
        · simp only [if_pos hu, abs_mul,
            abs_of_nonneg (show (0 : ℝ) ≤ cellCount sample k by positivity)]
          exact mul_le_mul_of_nonneg_left
            (P.homogeneity k (hsupport k hu)) (by positivity)
        · simp [hu]
      _ = (usableTotal sample : ℝ) * (sigma * M) := by
        have hrewrite :
            (∑ k : Fin d, if usableCell sample k then
                (cellCount sample k : ℝ) * (sigma * M) else 0) =
              (∑ k : Fin d, if usableCell sample k then
                (cellCount sample k : ℝ) else 0) * (sigma * M) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro k hk
          by_cases hu : usableCell sample k <;> simp [hu]
        rw [hrewrite]
        congr 1
        exact_mod_cast
          (show (∑ k : Fin d, if usableCell sample k then
              cellCount sample k else 0) = usableTotal sample from rfl)
  rw [abs_of_pos hden]
  exact (div_le_iff₀ hden).2 (by simpa [mul_comm] using hnum)

-- @node: modelClass_rawAte_abs_le
/-- [Mean normalization bounds the ATE of every radius-indexed model by the outcome scale](goal). -/
lemma modelClass_rawAte_abs_le {d : ℕ} {epsilon M sigma : ℝ}
    (P : ModelClass d epsilon M sigma) : |rawAteFormula P.law| ≤ M := by
  let Q : UnrestrictedClass d epsilon M := {
    law := P.law
    epsilon_pos := P.epsilon_pos
    epsilon_lt_half := P.epsilon_lt_half
    M_ge_one := P.M_ge_one
    consistency := P.consistency
    exchangeability := P.exchangeability
    overlap := P.overlap
    mean_normalization := P.mean_normalization
    second_moment := P.second_moment }
  exact (scale_sanity.1 Q).2.1

-- @node: collisionDesignCenter_bias_sq_le
/-- If [the stated support-size bound holds](hyp:hsupport), [the conditional-design squared bias
  is bounded by the homogeneity radius, plus the indicator of the zero-usable-occupancy
  fallback](goal). -/
lemma collisionDesignCenter_bias_sq_le {n d : ℕ} {epsilon M sigma : ℝ}
    (P : ModelClass d epsilon M sigma) (sample : Fin n → Obs d)
    (hsupport : ∀ k, usableCell sample k → 0 < P.law.cellMass k) :
    (collisionDesignCenter P sample - rawAteFormula P.law) ^ 2 ≤
      M ^ 2 * (sigma ^ 2 + if usableTotal sample = 0 then 1 else 0) := by
  have hM : 0 ≤ M := le_trans zero_le_one P.M_ge_one
  by_cases husable : 0 < usableTotal sample
  · have hne : usableTotal sample ≠ 0 := Nat.ne_of_gt husable
    have hbias := collisionDesignCenter_bias_abs_le P sample husable hsupport
    rw [if_neg hne]
    simp only [add_zero]
    calc
      (collisionDesignCenter P sample - rawAteFormula P.law) ^ 2 =
          |collisionDesignCenter P sample - rawAteFormula P.law| ^ 2 :=
        (sq_abs _).symm
      _ ≤ (sigma * M) ^ 2 :=
        (sq_le_sq₀ (abs_nonneg _) (mul_nonneg P.sigma_nonneg hM)).2 hbias
      _ = M ^ 2 * sigma ^ 2 := by ring
  · have hzero : usableTotal sample = 0 := Nat.eq_zero_of_not_pos husable
    have hate := modelClass_rawAte_abs_le P
    rw [if_pos hzero]
    simp only [collisionDesignCenter, hzero, lt_self_iff_false, ↓reduceIte,
      zero_sub] at hate ⊢
    calc
      (-rawAteFormula P.law) ^ 2 = |rawAteFormula P.law| ^ 2 := by
        rw [sq_abs]
        ring
      _ ≤ M ^ 2 := (sq_le_sq₀ (abs_nonneg _) hM).2 hate
      _ ≤ M ^ 2 * (sigma ^ 2 + 1) := by
        nlinarith [sq_nonneg M, sq_nonneg sigma,
          mul_nonneg (sq_nonneg M) (sq_nonneg sigma)]

/-- [Empirically usable cells have positive population mass almost surely under the product
  experiment](goal). -/
-- @node: usableCell_supported_ae
lemma usableCell_supported_ae {n d : ℕ} (P : RealLaw d) :
    ∀ᵐ sample ∂productLaw n P, ∀ k, usableCell sample k → 0 < P.cellMass k := by
  have hcoord (i : Fin n) (k : Fin d) :
      ∀ᵐ sample ∂productLaw n P, (sample i).x = k → 0 < P.cellMass k := by
    by_cases hk : 0 < P.cellMass k
    · exact Filter.Eventually.of_forall (fun _ _ => hk)
    · have hkzero : P.cellMass k = 0 :=
        le_antisymm (not_lt.mp hk) (P.cellMass_range k).1
      let S : Set (Obs d) := {o | o.x = k}
      have hSzero : P.observedLaw S = 0 := by
        have htoreal : (P.observedLaw S).toReal = 0 := by
          change realMass P.observedLaw {o | o.x = k} = 0
          rw [← P.cellMass_eq k, hkzero]
        rcases (ENNReal.toReal_eq_zero_iff _).mp htoreal with hzero | htop
        · exact hzero
        · exact (measure_ne_top P.observedLaw S htop).elim
      have hpre : (productLaw n P) (Function.eval i ⁻¹' S) = 0 := by
        simpa [productLaw] using
          (Measure.pi_eval_preimage_null
            (μ := fun _ : Fin n => P.observedLaw) (i := i) hSzero)
      have hae : ∀ᵐ sample ∂productLaw n P, sample i ∉ S :=
        measure_eq_zero_iff_ae_notMem.mp hpre
      filter_upwards [hae] with sample hs hxi
      exact (hs hxi).elim
  filter_upwards [Filter.eventually_all.2 (fun i =>
      Filter.eventually_all.2 (fun k => hcoord i k))] with sample hs
  intro k hu
  have hcounts : 0 < armCount sample false k ∧ 0 < armCount sample true k := by
    simpa [usableCell] using hu
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hcounts.1
  have hix : (sample i).x = k ∧ (sample i).a = false := by
    simpa [armCount] using hi
  exact hs i k hix.1

/-- [The conditional design center is measurable because it factors through the finite
  cell-and-treatment design](goal). -/
-- @node: measurable_collisionDesignCenter
lemma measurable_collisionDesignCenter {n d : ℕ} {epsilon M sigma : ℝ}
    (P : ModelClass d epsilon M sigma) :
    Measurable (collisionDesignCenter P : (Fin n → Obs d) → ℝ) := by
  let design : (Fin n → Obs d) → (Fin n → Fin d × Bool) :=
    fun s i => ((s i).x, (s i).a)
  let f : (Fin n → Fin d × Bool) → ℝ := fun z =>
    collisionDesignCenter P (fun i => ⟨(z i).1, (z i).2, 0⟩)
  have hdesign : Measurable design := by
    have hobs : Measurable (fun o : Obs d => (o.x, o.a, o.y)) :=
      measurable_iff_comap_le.mpr le_rfl
    have hx : Measurable (fun o : Obs d => o.x) := measurable_fst.comp hobs
    have ha : Measurable (fun o : Obs d => o.a) :=
      measurable_fst.comp (measurable_snd.comp hobs)
    fun_prop
  rw [show (collisionDesignCenter P : (Fin n → Obs d) → ℝ) = f ∘ design by
    funext s
    rfl]
  exact (measurable_of_finite f).comp hdesign

/-- [The usable total is a measurable finite-design statistic](goal). -/
lemma measurable_usableTotal {n d : ℕ} :
    Measurable (usableTotal : (Fin n → Obs d) → ℕ) := by
  let design : (Fin n → Obs d) → (Fin n → Fin d × Bool) :=
    fun s i => ((s i).x, (s i).a)
  let f : (Fin n → Fin d × Bool) → ℕ := fun z =>
    usableTotal (fun i => ⟨(z i).1, (z i).2, 0⟩)
  have hdesign : Measurable design := by
    have hobs : Measurable (fun o : Obs d => (o.x, o.a, o.y)) :=
      measurable_iff_comap_le.mpr le_rfl
    have hx : Measurable (fun o : Obs d => o.x) := measurable_fst.comp hobs
    have ha : Measurable (fun o : Obs d => o.a) :=
      measurable_fst.comp (measurable_snd.comp hobs)
    fun_prop
  rw [show (usableTotal : (Fin n → Obs d) → ℕ) = f ∘ design by
    funext s
    rfl]
  exact (measurable_of_finite f).comp hdesign

/-- [Integrating the conditional-design squared bias introduces exactly the zero-usable-occupancy
  probability and no unsupported-cell contribution](goal). -/
-- @node: integral_collisionDesignCenter_bias_sq_le
lemma integral_collisionDesignCenter_bias_sq_le {n d : ℕ}
    {epsilon M sigma : ℝ} (P : ModelClass d epsilon M sigma) :
    (∫ sample, (collisionDesignCenter P sample - rawAteFormula P.law) ^ 2
        ∂productLaw n P.law) ≤
      M ^ 2 * (sigma ^ 2 +
        realMass (productLaw n P.law) {sample | usableTotal sample = 0}) := by
  let μ := productLaw n P.law
  let bad : Set (Fin n → Obs d) := {sample | usableTotal sample = 0}
  let f : (Fin n → Obs d) → ℝ := fun sample =>
    (collisionDesignCenter P sample - rawAteFormula P.law) ^ 2
  let g : (Fin n → Obs d) → ℝ := fun sample =>
    M ^ 2 * (sigma ^ 2 + if usableTotal sample = 0 then 1 else 0)
  have hbad : MeasurableSet bad := by
    exact (measurableSet_singleton 0).preimage measurable_usableTotal
  have hfmeas : Measurable f := by
    exact ((measurable_collisionDesignCenter P).sub measurable_const).pow_const 2
  have hgmeas : Measurable g := by
    apply measurable_const.mul
    apply measurable_const.add
    exact Measurable.ite
      ((measurableSet_singleton 0).preimage measurable_usableTotal)
      measurable_const measurable_const
  have hgint : Integrable g μ := by
    refine (integrable_const (M ^ 2 * (sigma ^ 2 + 1) : ℝ)).mono
      hgmeas.aestronglyMeasurable ?_
    filter_upwards with sample
    dsimp [g]
    by_cases hs : usableTotal sample = 0
    · rw [if_pos hs]
    · rw [if_neg hs, add_zero]
      rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
      nlinarith [sq_nonneg M]
  have hfle : f ≤ᵐ[μ] g := by
    filter_upwards [usableCell_supported_ae P.law] with sample hs
    exact collisionDesignCenter_bias_sq_le P sample hs
  have hfint : Integrable f μ := by
    refine hgint.mono hfmeas.aestronglyMeasurable ?_
    filter_upwards [hfle] with sample hle
    have hfnonneg : 0 ≤ f sample := by dsimp [f]; positivity
    have hgnonneg : 0 ≤ g sample := hfnonneg.trans hle
    simpa [Real.norm_eq_abs, abs_of_nonneg hfnonneg, abs_of_nonneg hgnonneg]
  have hint := integral_mono_ae hfint hgint hfle
  change (∫ sample, f sample ∂μ) ≤ _
  calc
    (∫ sample, f sample ∂μ) ≤ ∫ sample, g sample ∂μ := hint
    _ = M ^ 2 * (sigma ^ 2 + realMass μ bad) := by
      have hindicator : (fun sample : Fin n → Obs d =>
          if usableTotal sample = 0 then (1 : ℝ) else 0) = bad.indicator 1 := by
        funext sample
        by_cases hs : usableTotal sample = 0 <;> simp [bad, hs]
      rw [show g = fun sample =>
          M ^ 2 * sigma ^ 2 + M ^ 2 *
            (if usableTotal sample = 0 then 1 else 0) by
        funext sample
        dsimp [g]
        ring]
      rw [integral_add]
      · rw [integral_const, integral_const_mul, hindicator,
          integral_indicator_one hbad]
        simp [μ, realMass]
        change M ^ 2 * sigma ^ 2 + M ^ 2 * (μ bad).toReal =
          M ^ 2 * (sigma ^ 2 + (μ bad).toReal)
        ring
      · exact integrable_const _
      · have hi :=
          ((integrable_const (μ := μ) (1 : ℝ)).indicator hbad).const_mul (M ^ 2)
        simpa [bad, Set.indicator, mul_ite] using hi
    _ = _ := by rfl

-- @node: occupancy_max_rate_le
/-- If [the sample is nonempty](hyp:hn), [the de-Poissonization occupancy scale is bounded by the
  advertised parametric-plus-alphabet rate](goal). -/
lemma occupancy_max_rate_le {n d : ℕ} (hn : 0 < n) :
    ((max n d : ℕ) : ℝ) / (n : ℝ) ^ 2 ≤
      1 / (n : ℝ) + (d : ℝ) / (n : ℝ) ^ 2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Nat.cast_max]
  by_cases hnd : n ≤ d
  · rw [max_eq_right (by exact_mod_cast hnd)]
    have hone : 0 ≤ 1 / (n : ℝ) := by positivity
    linarith
  · have hdn : d ≤ n := Nat.le_of_not_ge hnd
    rw [max_eq_left (by exact_mod_cast hdn)]
    have hne : (n : ℝ) ≠ 0 := hnR.ne'
    have hrewrite : (n : ℝ) / (n : ℝ) ^ 2 = 1 / (n : ℝ) := by
      field_simp
    rw [hrewrite]
    have hdnonneg : 0 ≤ (d : ℝ) / (n : ℝ) ^ 2 := by positivity
    linarith

-- @node: exp_neg_div_absorbed_by_linear_rate
/-- If [the radial cap satisfies its stated bound](hyp:hb) and [the scalar satisfies the stated
  range condition](hyp:hx), [an inverse-scale exponential tail is absorbed by a constant multiple
  of the scale, uniformly over every positive scale](goal). -/
lemma exp_neg_div_absorbed_by_linear_rate {b x : ℝ} (hb : 0 < b) (hx : 0 < x) :
    Real.exp (-b / x) ≤ (1 / b) * x := by
  let y := b / x
  have hy : 0 < y := div_pos hb hx
  have hy_exp : y ≤ Real.exp y :=
    le_trans (by linarith : y ≤ y + 1) (Real.add_one_le_exp y)
  have hinv : (Real.exp y)⁻¹ ≤ y⁻¹ :=
    (inv_le_inv₀ (Real.exp_pos y) hy).2 hy_exp
  have harg : -b / x = -y := by
    dsimp [y]
    ring
  rw [harg, Real.exp_neg]
  calc
    (Real.exp y)⁻¹ ≤ y⁻¹ := hinv
    _ = (1 / b) * x := by
      dsimp [y]
      field_simp

-- @node: observed_arm_cell_centered_integral_eq_zero
/-- [Within one supported arm and cell, the observed centered outcome has zero integral. The
  statement is totalized over zero-mass cells, where the arm-cell event is null](goal). -/
lemma observed_arm_cell_centered_integral_eq_zero {d : ℕ}
    {epsilon M sigma : ℝ} (P : ModelClass d epsilon M sigma)
    (a : Bool) (k : Fin d) :
    (∫ o in {o : Obs d | o.x = k ∧ o.a = a},
      (o.y - P.law.outcomeMean a k) ∂P.law.observedLaw) = 0 := by
  let E : Set (Obs d) := {o | o.x = k ∧ o.a = a}
  have htuple : Measurable (fun o : Obs d => (o.x, o.a, o.y)) :=
    measurable_iff_comap_le.mpr le_rfl
  have hy : Measurable (fun o : Obs d => o.y) :=
    measurable_snd.comp (measurable_snd.comp htuple)
  by_cases hk : P.law.cellMass k = 0
  · have hnull := observed_arm_cell_measure_eq_zero_of_cellMass_eq_zero
      P.law a k hk
    exact MeasureTheory.setIntegral_measure_zero _ hnull
  · have hkpos : 0 < P.law.cellMass k :=
      lt_of_le_of_ne (P.law.cellMass_range k).1 (Ne.symm hk)
    let _ : IsProbabilityMeasure (P.law.outcomeLaw a k) :=
      P.law.outcome_isProbability a k
    have hc := (P.second_moment a k hkpos).1
    have hcLp : MemLp (fun y : ℝ => y - P.law.outcomeMean a k) 2
        (P.law.outcomeLaw a k) :=
      (memLp_two_iff_integrable_sq
        ((measurable_id.sub measurable_const).aestronglyMeasurable)).2 hc
    have hcInt : Integrable (fun y : ℝ => y - P.law.outcomeMean a k)
        (P.law.outcomeLaw a k) := hcLp.integrable (by norm_num)
    have hyInt : Integrable (fun y : ℝ => y) (P.law.outcomeLaw a k) := by
      refine (hcInt.add (integrable_const (P.law.outcomeMean a k))).congr ?_
      filter_upwards with y
      simp
    have hmap := observed_arm_cell_outcome_measure P.law a k
    have hcenter : (∫ y, y - P.law.outcomeMean a k
        ∂P.law.outcomeLaw a k) = 0 := by
      rw [integral_sub hyInt
        (integrable_const (P.law.outcomeMean a k)), integral_const,
        ← P.law.outcomeMean_eq]
      simp
    calc
      (∫ o in {o : Obs d | o.x = k ∧ o.a = a},
          (o.y - P.law.outcomeMean a k) ∂P.law.observedLaw) =
          ∫ y, y - P.law.outcomeMean a k
            ∂Measure.map (fun o : Obs d => o.y)
              (P.law.observedLaw.restrict E) := by
        convert (integral_map hy.aemeasurable
          (measurable_id.sub measurable_const).aestronglyMeasurable).symm using 1 <;>
          rfl
      _ = ∫ y, y - P.law.outcomeMean a k ∂(
          ENNReal.ofReal (P.law.cellMass k *
            (if a then P.law.propensity k else 1 - P.law.propensity k)) •
              P.law.outcomeLaw a k) := by rw [hmap]
      _ = 0 := by rw [integral_smul_measure, hcenter]; simp

-- @node: observed_arm_cell_centered_sq_integral_le
/-- [The observed centered second moment on an arm-cell event is bounded by its arm-cell
  probability times `M²`, including the null-cell boundary](goal). -/
lemma observed_arm_cell_centered_sq_integral_le {d : ℕ}
    {epsilon M sigma : ℝ} (P : ModelClass d epsilon M sigma)
    (a : Bool) (k : Fin d) :
    (∫ o in {o : Obs d | o.x = k ∧ o.a = a},
      (o.y - P.law.outcomeMean a k) ^ 2 ∂P.law.observedLaw) ≤
      P.law.cellMass k *
        (if a then P.law.propensity k else 1 - P.law.propensity k) * M ^ 2 := by
  let E : Set (Obs d) := {o | o.x = k ∧ o.a = a}
  have htuple : Measurable (fun o : Obs d => (o.x, o.a, o.y)) :=
    measurable_iff_comap_le.mpr le_rfl
  have hy : Measurable (fun o : Obs d => o.y) :=
    measurable_snd.comp (measurable_snd.comp htuple)
  have hq : 0 ≤ if a then P.law.propensity k else 1 - P.law.propensity k := by
    split
    · exact (P.law.propensity_range k).1
    · linarith [(P.law.propensity_range k).2]
  by_cases hk : P.law.cellMass k = 0
  · have hnull := observed_arm_cell_measure_eq_zero_of_cellMass_eq_zero
      P.law a k hk
    rw [MeasureTheory.setIntegral_measure_zero _ hnull, hk, zero_mul]
    positivity
  · have hkpos : 0 < P.law.cellMass k :=
      lt_of_le_of_ne (P.law.cellMass_range k).1 (Ne.symm hk)
    have hc := P.second_moment a k hkpos
    have hmap := observed_arm_cell_outcome_measure P.law a k
    have hscale : 0 ≤ P.law.cellMass k *
        (if a then P.law.propensity k else 1 - P.law.propensity k) :=
      mul_nonneg hkpos.le hq
    calc
      (∫ o in {o : Obs d | o.x = k ∧ o.a = a},
          (o.y - P.law.outcomeMean a k) ^ 2 ∂P.law.observedLaw) =
          ∫ y, (y - P.law.outcomeMean a k) ^ 2
            ∂Measure.map (fun o : Obs d => o.y)
              (P.law.observedLaw.restrict E) := by
        convert (integral_map hy.aemeasurable
          ((measurable_id.sub measurable_const).pow_const 2).aestronglyMeasurable).symm using 1 <;>
          rfl
      _ = ∫ y, (y - P.law.outcomeMean a k) ^ 2 ∂(
          ENNReal.ofReal (P.law.cellMass k *
            (if a then P.law.propensity k else 1 - P.law.propensity k)) •
              P.law.outcomeLaw a k) := by rw [hmap]
      _ = (P.law.cellMass k *
          (if a then P.law.propensity k else 1 - P.law.propensity k)) *
            (∫ y, (y - P.law.outcomeMean a k) ^ 2
              ∂P.law.outcomeLaw a k) := by
        rw [integral_smul_measure]
        rw [ENNReal.toReal_ofReal hscale]
        rfl
      _ ≤ P.law.cellMass k *
          (if a then P.law.propensity k else 1 - P.law.propensity k) * M ^ 2 :=
        mul_le_mul_of_nonneg_left hc.2 hscale

end CausalSmith.Stat.DiscreteAteHeterogeneityFrontier
