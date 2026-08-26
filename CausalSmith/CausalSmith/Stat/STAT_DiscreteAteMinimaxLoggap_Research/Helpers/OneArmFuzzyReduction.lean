import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.LowerBound
import Causalean.Stat.Minimax.Mixture
import Causalean.Stat.Minimax.MinimaxRisk

namespace CausalSmith.Stat.DiscreteAteMinimaxLoggap

open MeasureTheory Causalean.Stat
open scoped ENNReal BigOperators

/-- Count-space Le Cam bound in squared-risk form.  This is the testing step
used after Rao--Blackwellization and Poisson-total mixing in Appendix D.2. -/
theorem max_squaredRisk_lower_of_tvDist_le
    {Ω : Type*} [MeasurableSpace Ω]
    (Q₀ Q₁ : Measure Ω) [IsProbabilityMeasure Q₀] [IsProbabilityMeasure Q₁]
    (est : Ω → ℝ) (hest : Measurable est)
    {theta₀ theta₁ s c : ℝ}
    (hs : 0 ≤ s) (hsep : 2 * s ≤ |theta₀ - theta₁|)
    (htv : tvDist Q₀ Q₁ ≤ c)
    (hint₀ : Integrable (fun x => (est x - theta₀) ^ 2) Q₀)
    (hint₁ : Integrable (fun x => (est x - theta₁) ^ 2) Q₁) :
    s ^ 2 * ((1 - c) / 2) ≤
      max (∫ x, (est x - theta₀) ^ 2 ∂Q₀)
        (∫ x, (est x - theta₁) ^ 2 ∂Q₁) := by
  have htest := two_point_lower_bound_of_tvDist_le
    (P₀ := Q₀) (P₁ := Q₁) hest hsep htv
  have hside₀ :
      s ^ 2 * Q₀.real {x | s ≤ |est x - theta₀|} ≤
        ∫ x, (est x - theta₀) ^ 2 ∂Q₀ := by
    have hset : {x : Ω | s ≤ |est x - theta₀|} =
        {x | s ^ 2 ≤ (est x - theta₀) ^ 2} := by
      ext x
      simp only [Set.mem_setOf_eq]
      constructor <;> intro h <;>
        nlinarith [abs_nonneg (est x - theta₀), sq_abs (est x - theta₀)]
    rw [hset]
    exact mul_meas_ge_le_integral_of_nonneg
      (Filter.Eventually.of_forall fun x => sq_nonneg _) hint₀ (s ^ 2)
  have hside₁ :
      s ^ 2 * Q₁.real {x | s ≤ |est x - theta₁|} ≤
        ∫ x, (est x - theta₁) ^ 2 ∂Q₁ := by
    have hset : {x : Ω | s ≤ |est x - theta₁|} =
        {x | s ^ 2 ≤ (est x - theta₁) ^ 2} := by
      ext x
      simp only [Set.mem_setOf_eq]
      constructor <;> intro h <;>
        nlinarith [abs_nonneg (est x - theta₁), sq_abs (est x - theta₁)]
    rw [hset]
    exact mul_meas_ge_le_integral_of_nonneg
      (Filter.Eventually.of_forall fun x => sq_nonneg _) hint₁ (s ^ 2)
  by_cases hle : Q₀.real {x | s ≤ |est x - theta₀|} ≤
      Q₁.real {x | s ≤ |est x - theta₁|}
  · rw [max_eq_right hle] at htest
    exact (mul_le_mul_of_nonneg_left htest (sq_nonneg s)).trans
      (hside₁.trans (le_max_right _ _))
  · rw [max_eq_left (le_of_not_ge hle)] at htest
    exact (mul_le_mul_of_nonneg_left htest (sq_nonneg s)).trans
      (hside₀.trans (le_max_left _ _))

/-- Re-centering squared loss at a nearby fuzzy-prior center costs at most a
factor two plus twice the squared target radius. -/
lemma mse_center_le_two_mse_add_two_radius_sq
    {n d : ℕ} (P : DiscreteLaw d) (est : (Fin n → Obs d) → ℝ)
    {theta center r : ℝ} (htheta : |theta - center| ≤ r) :
    mse (productLaw P n) est center ≤
      2 * mse (productLaw P n) est theta + 2 * r ^ 2 := by
  unfold mse
  calc
    (∫ x, (est x - center) ^ 2 ∂productLaw P n) ≤
        ∫ x, (2 * (est x - theta) ^ 2 + 2 * r ^ 2)
          ∂productLaw P n := by
      apply integral_mono Integrable.of_finite Integrable.of_finite
      intro x
      have htri : |est x - center| ≤
          |est x - theta| + |theta - center| := by
        calc
          |est x - center| = |(est x - theta) + (theta - center)| := by
            ring_nf
          _ ≤ _ := abs_add_le _ _
      have hr0 : 0 ≤ r := (abs_nonneg _).trans htheta
      have hw2 : |est x - center| ^ 2 ≤
          (|est x - theta| + |theta - center|) ^ 2 := by
        nlinarith [abs_nonneg (est x - center),
          abs_nonneg (est x - theta), abs_nonneg (theta - center)]
      have hv2 : |theta - center| ^ 2 ≤ r ^ 2 := by
        nlinarith [abs_nonneg (theta - center)]
      have huv : (|est x - theta| + |theta - center|) ^ 2 ≤
          2 * |est x - theta| ^ 2 + 2 * |theta - center| ^ 2 := by
        nlinarith [sq_nonneg (|est x - theta| - |theta - center|)]
      simp only [sq_abs] at hw2 hv2 huv
      dsimp
      nlinarith
    _ = 2 * (∫ x, (est x - theta) ^ 2 ∂productLaw P n) +
          2 * r ^ 2 := by
      rw [integral_add Integrable.of_finite (integrable_const _),
        integral_const_mul, integral_const]
      simp

/-- Final scalar accounting in the D.2 transfer: two center-risk upper bounds
and the count-space testing lower bound imply a fixed-sample risk lower bound. -/
lemma d2_fixedRisk_lower_of_countRisk_bounds
    {testing risk₀ risk₁ fixed radius tail : ℝ}
    (htest : testing ≤ max risk₀ risk₁)
    (hrisk₀ : risk₀ ≤ 2 * fixed + 2 * radius ^ 2 + tail)
    (hrisk₁ : risk₁ ≤ 2 * fixed + 2 * radius ^ 2 + tail) :
    (testing - 2 * radius ^ 2 - tail) / 2 ≤ fixed := by
  rcases le_total risk₀ risk₁ with hle | hle
  · rw [max_eq_right hle] at htest
    linarith
  · rw [max_eq_left hle] at htest
    linarith

/-- A squared-error risk dominates the squared threshold times the probability of
missing the target by that threshold. -/
lemma miss_sq_le_mse {n d : ℕ} (P : DiscreteLaw d)
    (est : (Fin n → Obs d) → ℝ) {theta s : ℝ} (hs : 0 ≤ s) :
    s ^ 2 * (productLaw P n).real {x | s ≤ |est x - theta|} ≤
      mse (productLaw P n) est theta := by
  have hset : {x : Fin n → Obs d | s ≤ |est x - theta|} =
      {x | s ^ 2 ≤ (est x - theta) ^ 2} := by
    ext x
    simp only [Set.mem_setOf_eq]
    constructor <;> intro h <;>
      nlinarith [abs_nonneg (est x - theta), sq_abs (est x - theta),
        sq_nonneg (est x - theta)]
  unfold mse
  rw [hset]
  exact mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall fun x => sq_nonneg _) Integrable.of_finite (s ^ 2)

/-- If the true target is within `r` of a prior center, missing that center by
`s` forces a miss of the true target by `s-r`. -/
lemma centered_miss_sq_le_mse {n d : ℕ} (P : DiscreteLaw d)
    (est : (Fin n → Obs d) → ℝ) {theta center s r : ℝ}
    (hr : 0 ≤ r) (hsr : r ≤ s) (htheta : |theta - center| ≤ r) :
    (s - r) ^ 2 * (productLaw P n).real {x | s ≤ |est x - center|} ≤
      mse (productLaw P n) est theta := by
  have hsubset : {x : Fin n → Obs d | s ≤ |est x - center|} ⊆
      {x | s - r ≤ |est x - theta|} := by
    intro x hx
    change s ≤ |est x - center| at hx
    change s - r ≤ |est x - theta|
    have htri : |est x - center| ≤ |est x - theta| + |theta - center| := by
      calc
        |est x - center| = |(est x - theta) + (theta - center)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    linarith
  have hprob := measureReal_mono (μ := productLaw P n) hsubset
  exact (mul_le_mul_of_nonneg_left hprob (sq_nonneg (s - r))).trans
    (miss_sq_le_mse P est (sub_nonneg.mpr hsr))

/-- Finite fuzzy hypotheses reduce a total-variation comparison of two prior
predictives to a lower bound on the control-zero one-arm minimax MSE. -/
theorem oneArmMinimaxRisk_lower_of_finite_mixtures
    {n d : ℕ} {epsilon theta₀ theta₁ s c : ℝ}
    {ι₀ ι₁ : Type*} [Fintype ι₀] [Nonempty ι₀]
    [Fintype ι₁] [Nonempty ι₁]
    (P₀ : ι₀ → ControlZeroLaw n d epsilon)
    (P₁ : ι₁ → ControlZeroLaw n d epsilon)
    (w₀ : ι₀ → ℝ≥0∞) (w₁ : ι₁ → ℝ≥0∞)
    (hw₀ : ∑ i, w₀ i = 1) (hw₁ : ∑ i, w₁ i = 1)
    (hθ₀ : ∀ i, treatedFunctional (P₀ i).1 = theta₀)
    (hθ₁ : ∀ i, treatedFunctional (P₁ i).1 = theta₁)
    (hs : 0 ≤ s) (hsep : 2 * s ≤ |theta₀ - theta₁|)
    (htv : tvDist
      (mixture w₀ (fun i => productLaw (P₀ i).1 n))
      (mixture w₁ (fun i => productLaw (P₁ i).1 n)) ≤ c) :
    s ^ 2 * ((1 - c) / 2) ≤ oneArmMinimaxRisk n d epsilon := by
  let Q₀ := mixture w₀ (fun i => productLaw (P₀ i).1 n)
  let Q₁ := mixture w₁ (fun i => productLaw (P₁ i).1 n)
  letI : IsProbabilityMeasure Q₀ := mixture_isProbabilityMeasure w₀ hw₀ _
  letI : IsProbabilityMeasure Q₁ := mixture_isProbabilityMeasure w₁ hw₁ _
  letI : Nonempty {f : (Fin n → Obs d) → ℝ // Measurable f} :=
    ⟨⟨0, measurable_const⟩⟩
  unfold oneArmMinimaxRisk
  apply le_ciInf
  intro est
  have htest := two_point_lower_bound_of_tvDist_le
    (P₀ := Q₀) (P₁ := Q₁) est.2 hsep htv
  change (1 - c) / 2 ≤
    max (Q₀.real {x | s ≤ |est.1 x - theta₀|})
      (Q₁.real {x | s ≤ |est.1 x - theta₁|}) at htest
  have hside₀ : s ^ 2 * Q₀.real {x | s ≤ |est.1 x - theta₀|} ≤
      oneArmWorstCaseMSE n d epsilon est.1 := by
    obtain ⟨i, hi⟩ := exists_real_ge_mixture w₀ hw₀
      (fun i => productLaw (P₀ i).1 n) {x | s ≤ |est.1 x - theta₀|}
    have hmul := mul_le_mul_of_nonneg_left hi (sq_nonneg s)
    refine hmul.trans ((miss_sq_le_mse (P₀ i).1 est.1 hs).trans ?_)
    rw [← hθ₀ i]
    unfold oneArmWorstCaseMSE
    refine le_ciSup (f := fun R : ControlZeroLaw n d epsilon =>
      mse (productLaw R.1 n) est.1 (treatedFunctional R.1)) ?_ (P₀ i)
    refine ⟨((∑ sample : Fin n → Obs d, |est.1 sample|) + 1) ^ 2, ?_⟩
    rintro _ ⟨R, rfl⟩
    change mse (productLaw R.1 n) est.1 (treatedFunctional R.1) ≤ _
    rw [← ateFunctional_eq_treated_on_controlZero R]
    exact mse_le_estimator_abs_sum_bound R.1 R.2.overlap est.1
  have hside₁ : s ^ 2 * Q₁.real {x | s ≤ |est.1 x - theta₁|} ≤
      oneArmWorstCaseMSE n d epsilon est.1 := by
    obtain ⟨i, hi⟩ := exists_real_ge_mixture w₁ hw₁
      (fun i => productLaw (P₁ i).1 n) {x | s ≤ |est.1 x - theta₁|}
    have hmul := mul_le_mul_of_nonneg_left hi (sq_nonneg s)
    refine hmul.trans ((miss_sq_le_mse (P₁ i).1 est.1 hs).trans ?_)
    rw [← hθ₁ i]
    unfold oneArmWorstCaseMSE
    refine le_ciSup (f := fun R : ControlZeroLaw n d epsilon =>
      mse (productLaw R.1 n) est.1 (treatedFunctional R.1)) ?_ (P₁ i)
    refine ⟨((∑ sample : Fin n → Obs d, |est.1 sample|) + 1) ^ 2, ?_⟩
    rintro _ ⟨R, rfl⟩
    change mse (productLaw R.1 n) est.1 (treatedFunctional R.1) ≤ _
    rw [← ateFunctional_eq_treated_on_controlZero R]
    exact mse_le_estimator_abs_sum_bound R.1 R.2.overlap est.1
  by_cases hle : Q₀.real {x | s ≤ |est.1 x - theta₀|} ≤
      Q₁.real {x | s ≤ |est.1 x - theta₁|}
  · rw [max_eq_right hle] at htest
    exact (mul_le_mul_of_nonneg_left htest (sq_nonneg s)).trans hside₁
  · rw [max_eq_left (le_of_not_ge hle)] at htest
    exact (mul_le_mul_of_nonneg_left htest (sq_nonneg s)).trans hside₀

/-- Fuzzy two-prior reduction when every component target lies within radius
`r` of its side's center. -/
theorem oneArmMinimaxRisk_lower_of_finite_mixtures_near_centers
    {n d : ℕ} {epsilon theta₀ theta₁ s r c : ℝ}
    {ι₀ ι₁ : Type*} [Fintype ι₀] [Nonempty ι₀]
    [Fintype ι₁] [Nonempty ι₁]
    (P₀ : ι₀ → ControlZeroLaw n d epsilon)
    (P₁ : ι₁ → ControlZeroLaw n d epsilon)
    (w₀ : ι₀ → ℝ≥0∞) (w₁ : ι₁ → ℝ≥0∞)
    (hw₀ : ∑ i, w₀ i = 1) (hw₁ : ∑ i, w₁ i = 1)
    (hθ₀ : ∀ i, |treatedFunctional (P₀ i).1 - theta₀| ≤ r)
    (hθ₁ : ∀ i, |treatedFunctional (P₁ i).1 - theta₁| ≤ r)
    (hr : 0 ≤ r) (hsr : r ≤ s) (hsep : 2 * s ≤ |theta₀ - theta₁|)
    (htv : tvDist
      (mixture w₀ (fun i => productLaw (P₀ i).1 n))
      (mixture w₁ (fun i => productLaw (P₁ i).1 n)) ≤ c) :
    (s - r) ^ 2 * ((1 - c) / 2) ≤ oneArmMinimaxRisk n d epsilon := by
  let Q₀ := mixture w₀ (fun i => productLaw (P₀ i).1 n)
  let Q₁ := mixture w₁ (fun i => productLaw (P₁ i).1 n)
  letI : IsProbabilityMeasure Q₀ := mixture_isProbabilityMeasure w₀ hw₀ _
  letI : IsProbabilityMeasure Q₁ := mixture_isProbabilityMeasure w₁ hw₁ _
  letI : Nonempty {f : (Fin n → Obs d) → ℝ // Measurable f} :=
    ⟨⟨0, measurable_const⟩⟩
  unfold oneArmMinimaxRisk
  apply le_ciInf
  intro est
  have htest := two_point_lower_bound_of_tvDist_le
    (P₀ := Q₀) (P₁ := Q₁) est.2 hsep htv
  change (1 - c) / 2 ≤
    max (Q₀.real {x | s ≤ |est.1 x - theta₀|})
      (Q₁.real {x | s ≤ |est.1 x - theta₁|}) at htest
  have hside₀ : (s - r) ^ 2 * Q₀.real {x | s ≤ |est.1 x - theta₀|} ≤
      oneArmWorstCaseMSE n d epsilon est.1 := by
    obtain ⟨i, hi⟩ := exists_real_ge_mixture w₀ hw₀
      (fun i => productLaw (P₀ i).1 n) {x | s ≤ |est.1 x - theta₀|}
    refine (mul_le_mul_of_nonneg_left hi (sq_nonneg (s - r))).trans
      ((centered_miss_sq_le_mse (P₀ i).1 est.1 hr hsr (hθ₀ i)).trans ?_)
    unfold oneArmWorstCaseMSE
    refine le_ciSup (f := fun R : ControlZeroLaw n d epsilon =>
      mse (productLaw R.1 n) est.1 (treatedFunctional R.1)) ?_ (P₀ i)
    refine ⟨((∑ sample : Fin n → Obs d, |est.1 sample|) + 1) ^ 2, ?_⟩
    rintro _ ⟨R, rfl⟩
    change mse (productLaw R.1 n) est.1 (treatedFunctional R.1) ≤ _
    rw [← ateFunctional_eq_treated_on_controlZero R]
    exact mse_le_estimator_abs_sum_bound R.1 R.2.overlap est.1
  have hside₁ : (s - r) ^ 2 * Q₁.real {x | s ≤ |est.1 x - theta₁|} ≤
      oneArmWorstCaseMSE n d epsilon est.1 := by
    obtain ⟨i, hi⟩ := exists_real_ge_mixture w₁ hw₁
      (fun i => productLaw (P₁ i).1 n) {x | s ≤ |est.1 x - theta₁|}
    refine (mul_le_mul_of_nonneg_left hi (sq_nonneg (s - r))).trans
      ((centered_miss_sq_le_mse (P₁ i).1 est.1 hr hsr (hθ₁ i)).trans ?_)
    unfold oneArmWorstCaseMSE
    refine le_ciSup (f := fun R : ControlZeroLaw n d epsilon =>
      mse (productLaw R.1 n) est.1 (treatedFunctional R.1)) ?_ (P₁ i)
    refine ⟨((∑ sample : Fin n → Obs d, |est.1 sample|) + 1) ^ 2, ?_⟩
    rintro _ ⟨R, rfl⟩
    change mse (productLaw R.1 n) est.1 (treatedFunctional R.1) ≤ _
    rw [← ateFunctional_eq_treated_on_controlZero R]
    exact mse_le_estimator_abs_sum_bound R.1 R.2.overlap est.1
  by_cases hle : Q₀.real {x | s ≤ |est.1 x - theta₀|} ≤
      Q₁.real {x | s ≤ |est.1 x - theta₁|}
  · rw [max_eq_right hle] at htest
    exact (mul_le_mul_of_nonneg_left htest (sq_nonneg (s - r))).trans hside₁
  · rw [max_eq_left (le_of_not_ge hle)] at htest
    exact (mul_le_mul_of_nonneg_left htest (sq_nonneg (s - r))).trans hside₀

end CausalSmith.Stat.DiscreteAteMinimaxLoggap
