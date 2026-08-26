/- Model-class membership for the canonical binary-to-real affine law. -/

import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.AffineRealLaw

namespace CausalSmith.Stat.DiscreteAteHeterogeneityFrontier

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
noncomputable section

private abbrev BinLaw := CausalSmith.Stat.DiscreteAteMinimaxLoggap.DiscreteLaw

-- @node: affineBinaryRealLaw_overlap
/-- If [the source law satisfies the stated model condition](hyp:hP), [affine outcome scaling
  preserves the binary source law's overlap condition](goal). -/
lemma affineBinaryRealLaw_overlap {d : ℕ} {epsilon M : ℝ} {P : BinLaw d}
    (hP : CausalSmith.Stat.DiscreteAteMinimaxLoggap.Overlap epsilon P) :
    Overlap epsilon (affineBinaryRealLaw M P) := by
  intro k hk
  exact hP k hk

-- @node: affineBinaryRealLaw_meanNormalization
/-- If [the outcome scale satisfies its stated bound](hyp:hM), [the affine binary real-outcome law
  has conditional means bounded in absolute value by half the outcome scale](goal). -/
lemma affineBinaryRealLaw_meanNormalization {d : ℕ} {M : ℝ} {P : BinLaw d}
    (hM : 0 ≤ M) : MeanNormalization M (affineBinaryRealLaw M P) := by
  intro a k _hk
  rcases CausalSmith.Stat.DiscreteAteMinimaxLoggap.outcomeMean_mem_unitInterval P a k with
    ⟨hmu0, hmu1⟩
  change |M *
    (CausalSmith.Stat.DiscreteAteMinimaxLoggap.outcomeMean P a k - 1 / 2)| ≤ M / 2
  rw [abs_mul, abs_of_nonneg hM]
  have : |CausalSmith.Stat.DiscreteAteMinimaxLoggap.outcomeMean P a k - 1 / 2| ≤
      1 / 2 := by
    rw [abs_le]
    constructor <;> linarith
  nlinarith

-- @node: affineBinaryRealLaw_secondCentralMoment
/-- If [the outcome scale satisfies its stated bound](hyp:hM), [the affine binary real-outcome law
  has conditional second central moments bounded by the squared outcome scale](goal). -/
lemma affineBinaryRealLaw_secondCentralMoment {d : ℕ} {M : ℝ} {P : BinLaw d}
    (hM : 0 ≤ M) : SecondCentralMoment M (affineBinaryRealLaw M P) := by
  intro a k _hk
  let scale : Bool → ℝ := fun b => M * ((if b then 1 else 0) - 1 / 2)
  let mu : ℝ := M *
    (CausalSmith.Stat.DiscreteAteMinimaxLoggap.outcomeMean P a k - 1 / 2)
  have hscale : Measurable scale := by fun_prop
  have hbound (b : Bool) : (scale b - mu) ^ 2 ≤ M ^ 2 := by
    rcases CausalSmith.Stat.DiscreteAteMinimaxLoggap.outcomeMean_mem_unitInterval P a k with
      ⟨heta0, heta1⟩
    cases b
    · simp only [scale, mu, Bool.false_eq_true, if_false]
      ring_nf
      have hs := (sq_le_sq₀ (mul_nonneg hM heta0) hM).2
        (by simpa using mul_le_mul_of_nonneg_left heta1 hM)
      nlinarith [hs]
    · simp only [scale, mu, if_true]
      ring_nf
      have hs := (sq_le_sq₀ (mul_nonneg hM (sub_nonneg.mpr heta1)) hM).2
        (by simpa using mul_le_mul_of_nonneg_left (sub_le_self 1 heta0) hM)
      nlinarith [hs]
  have hint : Integrable (fun b : Bool => (scale b - mu) ^ 2)
      (binaryOutcomePMF P a k).toMeasure := by
    apply Integrable.of_bound (by fun_prop) (M ^ 2)
    filter_upwards [] with b
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hbound b
  change Integrable (fun y => (y - mu) ^ 2)
      ((PMF.map scale (binaryOutcomePMF P a k)).toMeasure) ∧
    ∫ y, (y - mu) ^ 2 ∂((PMF.map scale (binaryOutcomePMF P a k)).toMeasure) ≤ M ^ 2
  rw [← PMF.toMeasure_map scale _ hscale]
  constructor
  · rw [integrable_map_measure (by fun_prop) hscale.aemeasurable]
    exact hint
  · rw [integral_map hscale.aemeasurable (by fun_prop)]
    have hconst : Integrable (fun _ : Bool => M ^ 2)
        (binaryOutcomePMF P a k).toMeasure := integrable_const _
    calc
      ∫ b, (scale b - mu) ^ 2 ∂(binaryOutcomePMF P a k).toMeasure ≤
          ∫ _b : Bool, M ^ 2 ∂(binaryOutcomePMF P a k).toMeasure :=
        integral_mono hint hconst hbound
      _ = M ^ 2 := by simp only [integral_const, probReal_univ, one_smul]

-- @node: affineBinaryRealLaw_unrestricted
/-- This packages an affine binary source law as a member of the unrestricted real-outcome class. -/
def affineBinaryRealLaw_unrestricted {d : ℕ} {epsilon M : ℝ} (P : BinLaw d)
    (he0 : 0 < epsilon) (he1 : epsilon < 1 / 2) (hM : 1 ≤ M)
    (hP : CausalSmith.Stat.DiscreteAteMinimaxLoggap.Overlap epsilon P) :
    UnrestrictedClass d epsilon M where
  law := affineBinaryRealLaw M P
  epsilon_pos := he0
  epsilon_lt_half := he1
  M_ge_one := hM
  consistency := affineBinaryRealLaw_consistency M P
  exchangeability := affineBinaryRealLaw_exchangeability M P
  overlap := affineBinaryRealLaw_overlap hP
  mean_normalization := affineBinaryRealLaw_meanNormalization (le_trans zero_le_one hM)
  second_moment := affineBinaryRealLaw_secondCentralMoment (le_trans zero_le_one hM)

-- @node: affineBinaryRealLaw_exactHomogeneity
/-- If [the source law satisfies the stated model condition](hyp:hP), [an exactly homogeneous
  binary source remains exactly homogeneous after affine embedding into real outcomes](goal). -/
lemma affineBinaryRealLaw_exactHomogeneity {d : ℕ} {epsilon M : ℝ} {P : BinLaw d}
    (hP : BinaryExactHomogeneous epsilon P) :
    ApproximateHomogeneity M 0 (affineBinaryRealLaw M P) := by
  intro k _hk
  have heffect (l : Fin d) :
      cellEffect (affineBinaryRealLaw M P) l =
        M * (CausalSmith.Stat.DiscreteAteMinimaxLoggap.outcomeMean P true k -
          CausalSmith.Stat.DiscreteAteMinimaxLoggap.outcomeMean P false k) := by
    unfold cellEffect
    change M * (_ - 1 / 2) - M * (_ - 1 / 2) = _
    calc
      M * (_ - 1 / 2) - M * (_ - 1 / 2) =
          M * (CausalSmith.Stat.DiscreteAteMinimaxLoggap.outcomeMean P true l -
            CausalSmith.Stat.DiscreteAteMinimaxLoggap.outcomeMean P false l) := by ring
      _ = _ := congrArg (fun x : ℝ => M * x) (hP.2.2 l k)
  have hraw : rawAteFormula (affineBinaryRealLaw M P) =
      M * (CausalSmith.Stat.DiscreteAteMinimaxLoggap.outcomeMean P true k -
        CausalSmith.Stat.DiscreteAteMinimaxLoggap.outcomeMean P false k) := by
    unfold rawAteFormula
    simp_rw [heffect]
    rw [← Finset.sum_mul, sum_cellMass_eq_one]
    simp
  unfold cellDeviation
  rw [heffect k, hraw]
  simp

-- @node: affineBinaryRealLaw_model_zero
/-- This packages an exactly homogeneous affine binary law as a zero-radius member of the model
  class. -/
def affineBinaryRealLaw_model_zero {d : ℕ} {epsilon M : ℝ} (P : BinLaw d)
    (he0 : 0 < epsilon) (he1 : epsilon < 1 / 2) (hM : 1 ≤ M)
    (hP : BinaryExactHomogeneous epsilon P) : ModelClass d epsilon M 0 where
  law := affineBinaryRealLaw M P
  epsilon_pos := he0
  epsilon_lt_half := he1
  M_ge_one := hM
  sigma_nonneg := le_rfl
  sigma_le_two := by norm_num
  consistency := affineBinaryRealLaw_consistency M P
  exchangeability := affineBinaryRealLaw_exchangeability M P
  overlap := affineBinaryRealLaw_overlap hP.1
  mean_normalization := affineBinaryRealLaw_meanNormalization (le_trans zero_le_one hM)
  second_moment := affineBinaryRealLaw_secondCentralMoment (le_trans zero_le_one hM)
  homogeneity := affineBinaryRealLaw_exactHomogeneity hP

-- @node: affineBinaryRealLaw_ne_testModelLaw
/-- If [the overlap constant is positive](hyp:he0) and [the overlap constant is below one
  half](hyp:he1) and [the outcome scale satisfies its stated bound](hyp:hM) and [the heterogeneity
  radius is nonnegative](hyp:hs0) and [the heterogeneity radius is at most two](hyp:hs2), [a model
  whose control outcome is identically zero is outside the affine binary image, since a nonzero
  affine scale only takes the values `±M/2`](goal). -/
lemma affineBinaryRealLaw_ne_testModelLaw {d : ℕ} (k : Fin d)
    {epsilon M sigma : ℝ} (he0 : 0 < epsilon) (he1 : epsilon < 1 / 2)
    (hM : 1 ≤ M) (hs0 : 0 ≤ sigma) (hs2 : sigma ≤ 2) (P : BinLaw d) :
    affineBinaryRealLaw M P ≠
      (testModelClass k epsilon M sigma 0 he0 he1 hM hs0 hs2
        (by rw [abs_zero]; positivity)).law := by
  intro heq
  have hout := congrArg (fun R : RealLaw d => R.outcomeLaw false k {0}) heq
  change ((PMF.map (fun b : Bool => M * ((if b then 1 else 0) - 1 / 2))
      (binaryOutcomePMF P false k)).toMeasure) {0} =
    testOutcomeLaw (M / 2) 0 false {0} at hout
  have hscale : Measurable (fun b : Bool => M * ((if b then 1 else 0) - 1 / 2)) := by
    fun_prop
  rw [← PMF.toMeasure_map _ _ hscale,
    Measure.map_apply hscale (measurableSet_singleton 0)] at hout
  have hpre : (fun b : Bool => M * ((if b then 1 else 0) - 1 / 2)) ⁻¹' {0} = ∅ := by
    have hM0 : M ≠ 0 := by linarith
    ext b
    cases b <;> simp [hM0] <;> norm_num
  rw [hpre] at hout
  simp [testOutcomeLaw] at hout

end

end CausalSmith.Stat.DiscreteAteHeterogeneityFrontier
