import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.OneArmFinalAssembly
import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.OneArmPoissonHistogramLaw
import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.OneArmTripleLabelTransport
import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.OneArmRelaxedAnchorCounts
import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.OneArmGoodConditioning

/-!
# High-dimensional D.2 assembly

This module packages the final implication from the calibrated shifted-grid
separation and the two count-risk bounds to the high-dimensional minimax term.
-/

namespace CausalSmith.Stat.DiscreteAteMinimaxLoggap

open MeasureTheory ProbabilityTheory Causalean.Stat
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open scoped BigOperators ENNReal NNReal

noncomputable local instance oneArmTripleLabelLaw_isProbabilityMeasure
    {d : ℕ} (P : DiscreteLaw d) :
    IsProbabilityMeasure
      (Measure.map oneArmObservationTripleLabel (obsLaw P)) :=
  Measure.isProbabilityMeasure_map (measurable_of_finite _).aemeasurable

/-- Flatten a category-indexed family of triple counts. -/
def uncurryOneArmTripleCounts {d : ℕ}
    (c : Fin d → Fin 3 → ℕ) : Fin d × Fin 3 → ℕ :=
  fun u => c u.1 u.2

lemma uncurryOneArmTripleCounts_curry {d : ℕ}
    (c : Fin d × Fin 3 → ℕ) :
    uncurryOneArmTripleCounts (curryOneArmTripleCounts c) = c := by
  rfl

lemma curryOneArmTripleCounts_uncurry {d : ℕ}
    (c : Fin d → Fin 3 → ℕ) :
    curryOneArmTripleCounts (uncurryOneArmTripleCounts c) = c := by
  rfl

lemma map_finiteMixture
    {ι Ω Ξ : Type*} [Fintype ι] [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (w : ι → ℝ≥0∞) (K : ι → Measure Ω) (f : Ω → Ξ)
    (hf : Measurable f) :
    Measure.map f (mixture w K) =
      mixture w (fun i => Measure.map f (K i)) := by
  unfold mixture
  rw [Measure.map_finset_sum hf.aemeasurable]
  apply Finset.sum_congr rfl
  intro i _
  exact Measure.map_smul (w i) (K i) f

/-- Currying is a measurable bijection, hence preserves total variation. -/
lemma tvDist_map_curryOneArmTripleCounts_eq
    {d : ℕ} (Q₀ Q₁ : Measure (Fin d × Fin 3 → ℕ))
    [IsProbabilityMeasure Q₀] [IsProbabilityMeasure Q₁] :
    Causalean.Stat.tvDist
        (Measure.map curryOneArmTripleCounts Q₀)
        (Measure.map curryOneArmTripleCounts Q₁) =
      Causalean.Stat.tvDist Q₀ Q₁ := by
  apply le_antisymm
  · exact tvDist_map_le Q₀ Q₁ curryOneArmTripleCounts
      (measurable_of_countable _)
  · have hmap (Q : Measure (Fin d × Fin 3 → ℕ)) :
        Measure.map uncurryOneArmTripleCounts
            (Measure.map curryOneArmTripleCounts Q) = Q := by
      rw [Measure.map_map (measurable_of_countable _)
        (measurable_of_countable _)]
      have hfun : uncurryOneArmTripleCounts ∘ curryOneArmTripleCounts =
          (id : (Fin d × Fin 3 → ℕ) → (Fin d × Fin 3 → ℕ)) := by
        funext c
        exact uncurryOneArmTripleCounts_curry c
      rw [hfun, Measure.map_id]
    letI : IsProbabilityMeasure (Measure.map curryOneArmTripleCounts Q₀) :=
      Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
    letI : IsProbabilityMeasure (Measure.map curryOneArmTripleCounts Q₁) :=
      Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
    calc
      Causalean.Stat.tvDist Q₀ Q₁ =
          Causalean.Stat.tvDist
            (Measure.map uncurryOneArmTripleCounts
              (Measure.map curryOneArmTripleCounts Q₀))
            (Measure.map uncurryOneArmTripleCounts
              (Measure.map curryOneArmTripleCounts Q₁)) := by
        rw [hmap Q₀, hmap Q₁]
      _ ≤ Causalean.Stat.tvDist
          (Measure.map curryOneArmTripleCounts Q₀)
          (Measure.map curryOneArmTripleCounts Q₁) :=
        tvDist_map_le
          (Measure.map curryOneArmTripleCounts Q₀)
          (Measure.map curryOneArmTripleCounts Q₁)
          uncurryOneArmTripleCounts (measurable_of_countable _)

/-- Squared risk transports exactly from a flat count table to its curried
representation. -/
lemma integral_map_curryOneArmTripleCounts_sq
    {d : ℕ} (Q : Measure (Fin d × Fin 3 → ℕ))
    (est : (Fin d × Fin 3 → ℕ) → ℝ) (theta : ℝ) :
    (∫ c, (est (uncurryOneArmTripleCounts c) - theta) ^ 2
        ∂Measure.map curryOneArmTripleCounts Q) =
      ∫ c, (est c - theta) ^ 2 ∂Q := by
  rw [integral_map (measurable_of_countable _).aemeasurable
    (measurable_of_countable _).aestronglyMeasurable]
  rfl

private lemma integral_finiteMixture_le
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (w : ι → ℝ≥0∞) (hw : ∑ i, w i = 1)
    (K : ι → Measure Ω) (loss : Ω → ℝ)
    (hint : ∀ i, Integrable loss (K i)) {B : ℝ}
    (hB : ∀ i, (∫ x, loss x ∂(K i)) ≤ B) :
    Integrable loss (mixture w K) ∧
      (∫ x, loss x ∂(mixture w K)) ≤ B := by
  have hwtop (i : ι) : w i ≠ ⊤ := by
    have hwi : w i ≤ 1 := by
      calc
        w i ≤ ∑ j, w j := Finset.single_le_sum
          (fun j _ => bot_le) (Finset.mem_univ i)
        _ = 1 := hw
    exact ne_top_of_le_ne_top ENNReal.one_ne_top hwi
  have hsmul (i : ι) : Integrable loss (w i • K i) :=
    (hint i).smul_measure (hwtop i)
  have hmix : Integrable loss (mixture w K) := by
    unfold mixture
    exact integrable_finsetSum_measure.2 fun i _ => hsmul i
  refine ⟨hmix, ?_⟩
  unfold mixture
  rw [integral_finsetSum_measure (fun i _ => hsmul i)]
  simp_rw [integral_smul_measure, smul_eq_mul]
  calc
    ∑ i, (w i).toReal * (∫ x, loss x ∂(K i)) ≤
        ∑ i, (w i).toReal * B := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (hB i) ENNReal.toReal_nonneg
    _ = B := by
      rw [← Finset.sum_mul]
      have hsum : ∑ i, (w i).toReal = 1 := by
        rw [← ENNReal.toReal_sum (fun i _ => hwtop i), hw,
          ENNReal.toReal_one]
      rw [hsum, one_mul]

private lemma mse_le_oneArmWorstCase_of_controlZero
    {n d : ℕ} {epsilon : ℝ} (P : ControlZeroLaw n d epsilon)
    (est : (Fin n → Obs d) → ℝ) :
    mse (productLaw P.1 n) est (treatedFunctional P.1) ≤
      oneArmWorstCaseMSE n d epsilon est := by
  unfold oneArmWorstCaseMSE
  refine le_ciSup (f := fun R : ControlZeroLaw n d epsilon =>
    mse (productLaw R.1 n) est (treatedFunctional R.1)) ?_ P
  refine ⟨((∑ sample : Fin n → Obs d, |est sample|) + 1) ^ 2, ?_⟩
  rintro _ ⟨R, rfl⟩
  change mse (productLaw R.1 n) est (treatedFunctional R.1) ≤ _
  rw [← ateFunctional_eq_treated_on_controlZero R]
  exact mse_le_estimator_abs_sum_bound R.1 R.2.overlap est

private lemma tvDist_conditionedPredictive_le_badMassENN
    {Ω : Type*} [MeasurableSpace Ω]
    (Q QE QB : Measure Ω)
    [IsProbabilityMeasure Q] [IsProbabilityMeasure QE] [IsProbabilityMeasure QB]
    (q : ℝ≥0∞) (hq : q ≤ 1)
    (hdecomp : Q = q • QE + (1 - q) • QB) :
    Causalean.Stat.tvDist QE Q ≤ (1 - q).toReal := by
  unfold Causalean.Stat.tvDist
  apply ciSup_le
  intro A
  have hqtop : q ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hq
  have hqEtop : (q • QE) A.1 ≠ ⊤ := by
    rw [Measure.smul_apply]
    exact ENNReal.mul_ne_top hqtop (measure_ne_top QE A.1)
  have hsubtop : 1 - q ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (tsub_le_self : 1 - q ≤ 1)
  have hqBtop : ((1 - q) • QB) A.1 ≠ ⊤ := by
    rw [Measure.smul_apply]
    exact ENNReal.mul_ne_top hsubtop (measure_ne_top QB A.1)
  rw [hdecomp,
    measureReal_add_apply hqEtop hqBtop,
    measureReal_ennreal_smul_apply,
    measureReal_ennreal_smul_apply]
  have hqexpr : q.toReal = 1 - (1 - q).toReal := by
    rw [ENNReal.toReal_sub_of_le hq ENNReal.one_ne_top,
      ENNReal.toReal_one]
    ring
  rw [hqexpr]
  have hrewrite :
      QE.real A.1 -
          ((1 - (1 - q).toReal) * QE.real A.1 +
            (1 - q).toReal * QB.real A.1) =
        (1 - q).toReal * (QE.real A.1 - QB.real A.1) := by ring
  rw [hrewrite, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
  exact mul_le_of_le_one_right ENNReal.toReal_nonneg
    (abs_measureReal_sub_le_one (μ := QE) (ν := QB) A.1)

lemma tvDist_two_finiteConditionedMixtures_le
    {α₀ α₁ Ω : Type*} [Fintype α₀] [Fintype α₁]
    [MeasurableSpace Ω]
    (ω₀ : PMF α₀) (ω₁ : PMF α₁)
    (G₀ : α₀ → Prop) (G₁ : α₁ → Prop)
    [DecidablePred G₀] [DecidablePred G₁]
    (hG₀ : oneArmFiniteEventMass ω₀ G₀ ≠ 0)
    (hG₁ : oneArmFiniteEventMass ω₁ G₁ ≠ 0)
    (K₀ : α₀ → Measure Ω) (K₁ : α₁ → Measure Ω)
    [∀ i, IsProbabilityMeasure (K₀ i)]
    [∀ i, IsProbabilityMeasure (K₁ i)] :
    Causalean.Stat.tvDist
        (oneArmFiniteConditionedMixture ω₀ G₀ hG₀ K₀)
        (oneArmFiniteConditionedMixture ω₁ G₁ hG₁ K₁) ≤
      (oneArmFiniteEventMass ω₀ (fun x => ¬ G₀ x)).toReal +
        Causalean.Stat.tvDist (mixture (fun x => ω₀ x) K₀)
          (mixture (fun x => ω₁ x) K₁) +
      (oneArmFiniteEventMass ω₁ (fun x => ¬ G₁ x)).toReal := by
  let Q₀ := mixture (fun x => ω₀ x) K₀
  let Q₁ := mixture (fun x => ω₁ x) K₁
  let QE₀ := oneArmFiniteConditionedMixture ω₀ G₀ hG₀ K₀
  let QE₁ := oneArmFiniteConditionedMixture ω₁ G₁ hG₁ K₁
  let B₀ := oneArmFiniteEventMass ω₀ (fun x => ¬ G₀ x)
  let B₁ := oneArmFiniteEventMass ω₁ (fun x => ¬ G₁ x)
  letI : IsProbabilityMeasure Q₀ := mixture_isProbabilityMeasure
    (fun x => ω₀ x) (by simpa only [tsum_fintype] using ω₀.tsum_coe) K₀
  letI : IsProbabilityMeasure Q₁ := mixture_isProbabilityMeasure
    (fun x => ω₁ x) (by simpa only [tsum_fintype] using ω₁.tsum_coe) K₁
  by_cases hB₀ : B₀ = 0
  · have hEq₀ := oneArmFiniteMixture_eq_conditioned_of_compl_mass_eq_zero
      ω₀ G₀ hG₀ hB₀ K₀
    by_cases hB₁ : B₁ = 0
    · have hEq₁ := oneArmFiniteMixture_eq_conditioned_of_compl_mass_eq_zero
        ω₁ G₁ hG₁ hB₁ K₁
      simpa [Q₀, Q₁, QE₀, QE₁, B₀, B₁, hB₀, hB₁, hEq₀, hEq₁]
    · let QB₁ := oneArmFiniteConditionedMixture ω₁ (fun x => ¬ G₁ x) hB₁ K₁
      have hdec₁ := oneArmFiniteMixture_conditioning_decomposition
        ω₁ G₁ hG₁ hB₁ K₁
      have hq₁ := oneArmFiniteEventMass_le_one ω₁ G₁
      have hbadENN₁ : 1 - oneArmFiniteEventMass ω₁ G₁ = B₁ := by
        exact ENNReal.sub_eq_of_eq_add_rev' ENNReal.one_ne_top
          (oneArmFiniteEventMass_add_compl ω₁ G₁).symm
      have hbad₁ : (1 - oneArmFiniteEventMass ω₁ G₁).toReal = B₁.toReal := by
        rw [hbadENN₁]
      have hb := tvDist_conditionedPredictive_le_badMassENN Q₁ QE₁ QB₁
        (oneArmFiniteEventMass ω₁ G₁) hq₁
        (by simpa [Q₁, QE₁, QB₁, hbadENN₁] using hdec₁)
      rw [Causalean.Stat.tvDist_symm QE₁ Q₁, hbad₁] at hb
      rw [← hEq₀]
      have htri := tvDist_triangle' Q₀ Q₁ QE₁
      simpa [Q₀, Q₁, QE₀, QE₁, B₀, B₁, hB₀] using
        htri.trans (add_le_add_right hb (Causalean.Stat.tvDist Q₀ Q₁))
  · by_cases hB₁ : B₁ = 0
    · have hEq₁ := oneArmFiniteMixture_eq_conditioned_of_compl_mass_eq_zero
        ω₁ G₁ hG₁ hB₁ K₁
      let QB₀ := oneArmFiniteConditionedMixture ω₀ (fun x => ¬ G₀ x) hB₀ K₀
      have hdec₀ := oneArmFiniteMixture_conditioning_decomposition
        ω₀ G₀ hG₀ hB₀ K₀
      have hq₀ := oneArmFiniteEventMass_le_one ω₀ G₀
      have hbadENN₀ : 1 - oneArmFiniteEventMass ω₀ G₀ = B₀ := by
        exact ENNReal.sub_eq_of_eq_add_rev' ENNReal.one_ne_top
          (oneArmFiniteEventMass_add_compl ω₀ G₀).symm
      have hbad₀ : (1 - oneArmFiniteEventMass ω₀ G₀).toReal = B₀.toReal := by
        rw [hbadENN₀]
      have hb := tvDist_conditionedPredictive_le_badMassENN Q₀ QE₀ QB₀
        (oneArmFiniteEventMass ω₀ G₀) hq₀
        (by simpa [Q₀, QE₀, QB₀, hbadENN₀] using hdec₀)
      rw [hbad₀] at hb
      rw [← hEq₁]
      have htri := tvDist_triangle' QE₀ Q₀ Q₁
      simpa [Q₀, Q₁, QE₀, QE₁, B₀, B₁, hB₁] using
        htri.trans (add_le_add_left hb (Causalean.Stat.tvDist Q₀ Q₁))
    · let QB₀ := oneArmFiniteConditionedMixture ω₀ (fun x => ¬ G₀ x) hB₀ K₀
      let QB₁ := oneArmFiniteConditionedMixture ω₁ (fun x => ¬ G₁ x) hB₁ K₁
      have hdec₀ := oneArmFiniteMixture_conditioning_decomposition
        ω₀ G₀ hG₀ hB₀ K₀
      have hdec₁ := oneArmFiniteMixture_conditioning_decomposition
        ω₁ G₁ hG₁ hB₁ K₁
      have hq₀ := oneArmFiniteEventMass_le_one ω₀ G₀
      have hq₁ := oneArmFiniteEventMass_le_one ω₁ G₁
      have hbadENN₀ : 1 - oneArmFiniteEventMass ω₀ G₀ = B₀ := by
        exact ENNReal.sub_eq_of_eq_add_rev' ENNReal.one_ne_top
          (oneArmFiniteEventMass_add_compl ω₀ G₀).symm
      have hbadENN₁ : 1 - oneArmFiniteEventMass ω₁ G₁ = B₁ := by
        exact ENNReal.sub_eq_of_eq_add_rev' ENNReal.one_ne_top
          (oneArmFiniteEventMass_add_compl ω₁ G₁).symm
      have hbad₀ : (1 - oneArmFiniteEventMass ω₀ G₀).toReal = B₀.toReal := by
        rw [hbadENN₀]
      have hbad₁ : (1 - oneArmFiniteEventMass ω₁ G₁).toReal = B₁.toReal := by
        rw [hbadENN₁]
      have hb₀ := tvDist_conditionedPredictive_le_badMassENN Q₀ QE₀ QB₀
        (oneArmFiniteEventMass ω₀ G₀) hq₀
        (by simpa [Q₀, QE₀, QB₀, hbadENN₀] using hdec₀)
      have hb₁ := tvDist_conditionedPredictive_le_badMassENN Q₁ QE₁ QB₁
        (oneArmFiniteEventMass ω₁ G₁) hq₁
        (by simpa [Q₁, QE₁, QB₁, hbadENN₁] using hdec₁)
      rw [hbad₀] at hb₀
      rw [Causalean.Stat.tvDist_symm QE₁ Q₁, hbad₁] at hb₁
      have htri₀ := tvDist_triangle' QE₀ Q₀ QE₁
      have htri₁ := tvDist_triangle' Q₀ Q₁ QE₁
      linarith

/-- Concrete D.2 reduction for finite conditioned priors.  The hypotheses are
the two actual histogram predictives, their TV bound, fuzzy target radii, and
the two uniform Poisson lower-tail penalties; the conclusion is directly on
the fixed-sample one-arm minimax risk. -/
theorem oneArmMinimaxRisk_lower_of_conditioned_count_tv
    {n d : ℕ} {epsilon theta₀ theta₁ s radius c tail : ℝ}
    {ι₀ ι₁ : Type*} [Fintype ι₀] [Fintype ι₁]
    (P₀ : ι₀ → ControlZeroLaw n d epsilon)
    (P₁ : ι₁ → ControlZeroLaw n d epsilon)
    (w₀ : ι₀ → ℝ≥0∞) (w₁ : ι₁ → ℝ≥0∞)
    (hw₀ : ∑ i, w₀ i = 1) (hw₁ : ∑ i, w₁ i = 1)
    (lam₀ : ι₀ → ℝ≥0) (lam₁ : ι₁ → ℝ≥0)
    (htarget₀ : ∀ i, |treatedFunctional (P₀ i).1 - theta₀| ≤ radius)
    (htarget₁ : ∀ i, |treatedFunctional (P₁ i).1 - theta₁| ≤ radius)
    (hradius : 0 ≤ radius) (hs : 0 ≤ s)
    (hsep : 2 * s ≤ |theta₀ - theta₁|)
    (htv : Causalean.Stat.tvDist
      (mixture w₀ (fun i =>
        Measure.map (fun u : FiniteSample (Fin d × Fin 3) =>
          finiteSampleHistogram u.points)
          (finitePoissonSampleLaw
            (Measure.map oneArmObservationTripleLabel (obsLaw (P₀ i).1))
            (lam₀ i))))
      (mixture w₁ (fun i =>
        Measure.map (fun u : FiniteSample (Fin d × Fin 3) =>
          finiteSampleHistogram u.points)
          (finitePoissonSampleLaw
            (Measure.map oneArmObservationTripleLabel (obsLaw (P₁ i).1))
            (lam₁ i)))) ≤ c)
    (htail₀ : ∀ i,
      theta₀ ^ 2 * (poissonMeasure (lam₀ i)).real {k | k < n} ≤ tail)
    (htail₁ : ∀ i,
      theta₁ ^ 2 * (poissonMeasure (lam₁ i)).real {k | k < n} ≤ tail) :
    (s ^ 2 * ((1 - c) / 2) - 2 * radius ^ 2 - tail) / 2 ≤
      oneArmMinimaxRisk n d epsilon := by
  let H₀ : ι₀ → Measure (Fin d × Fin 3 → ℕ) := fun i =>
    Measure.map (fun u : FiniteSample (Fin d × Fin 3) =>
      finiteSampleHistogram u.points)
      (finitePoissonSampleLaw
        (Measure.map oneArmObservationTripleLabel (obsLaw (P₀ i).1)) (lam₀ i))
  let H₁ : ι₁ → Measure (Fin d × Fin 3 → ℕ) := fun i =>
    Measure.map (fun u : FiniteSample (Fin d × Fin 3) =>
      finiteSampleHistogram u.points)
      (finitePoissonSampleLaw
        (Measure.map oneArmObservationTripleLabel (obsLaw (P₁ i).1)) (lam₁ i))
  let Q₀ := mixture w₀ H₀
  let Q₁ := mixture w₁ H₁
  letI (i : ι₀) : IsProbabilityMeasure (H₀ i) := by
    dsimp [H₀]
    exact Measure.isProbabilityMeasure_map
      (measurable_of_countable _).aemeasurable
  letI (i : ι₁) : IsProbabilityMeasure (H₁ i) := by
    dsimp [H₁]
    exact Measure.isProbabilityMeasure_map
      (measurable_of_countable _).aemeasurable
  letI : IsProbabilityMeasure Q₀ := mixture_isProbabilityMeasure w₀ hw₀ H₀
  letI : IsProbabilityMeasure Q₁ := mixture_isProbabilityMeasure w₁ hw₁ H₁
  letI : Nonempty {f : (Fin n → Obs d) → ℝ // Measurable f} :=
    ⟨⟨0, measurable_const⟩⟩
  unfold oneArmMinimaxRisk
  apply le_ciInf
  intro est
  let labelEst : (Fin n → Fin d × Fin 3) → ℝ := fun z =>
    est.1 (fun i => oneArmTripleRepresentative (z i))
  let countEst : (Fin d × Fin 3 → ℕ) → ℝ :=
    poissonHistogramEstimator labelEst
  have hcountMeas : Measurable countEst := measurable_of_countable _
  have hcomponent₀ (i : ι₀) :
      Integrable (fun z => (countEst z - theta₀) ^ 2) (H₀ i) ∧
      (∫ z, (countEst z - theta₀) ^ 2 ∂(H₀ i)) ≤
        2 * oneArmWorstCaseMSE n d epsilon est.1 +
          2 * radius ^ 2 + tail := by
    have hRB := integral_poissonHistogramRisk_le_fixedRisk_add_tail
      (Measure.map oneArmObservationTripleLabel (obsLaw (P₀ i).1))
      (lam₀ i) labelEst theta₀
    have hcenter := mse_center_le_two_mse_add_two_radius_sq
      (P₀ i).1 est.1 (htarget₀ i)
    have hsup := mse_le_oneArmWorstCase_of_controlZero (P₀ i) est.1
    refine ⟨hRB.1, hRB.2.trans ?_⟩
    rw [productRisk_oneArmTripleRepresentative_eq (P₀ i) est.1 theta₀]
    dsimp [H₀, labelEst, countEst] at hRB ⊢
    nlinarith [htail₀ i]
  have hcomponent₁ (i : ι₁) :
      Integrable (fun z => (countEst z - theta₁) ^ 2) (H₁ i) ∧
      (∫ z, (countEst z - theta₁) ^ 2 ∂(H₁ i)) ≤
        2 * oneArmWorstCaseMSE n d epsilon est.1 +
          2 * radius ^ 2 + tail := by
    have hRB := integral_poissonHistogramRisk_le_fixedRisk_add_tail
      (Measure.map oneArmObservationTripleLabel (obsLaw (P₁ i).1))
      (lam₁ i) labelEst theta₁
    have hcenter := mse_center_le_two_mse_add_two_radius_sq
      (P₁ i).1 est.1 (htarget₁ i)
    have hsup := mse_le_oneArmWorstCase_of_controlZero (P₁ i) est.1
    refine ⟨hRB.1, hRB.2.trans ?_⟩
    rw [productRisk_oneArmTripleRepresentative_eq (P₁ i) est.1 theta₁]
    dsimp [H₁, labelEst, countEst] at hRB ⊢
    nlinarith [htail₁ i]
  have hmix₀ := integral_finiteMixture_le w₀ hw₀ H₀
    (fun z => (countEst z - theta₀) ^ 2)
    (fun i => (hcomponent₀ i).1) (fun i => (hcomponent₀ i).2)
  have hmix₁ := integral_finiteMixture_le w₁ hw₁ H₁
    (fun z => (countEst z - theta₁) ^ 2)
    (fun i => (hcomponent₁ i).1) (fun i => (hcomponent₁ i).2)
  have htest := max_squaredRisk_lower_of_tvDist_le Q₀ Q₁ countEst
    hcountMeas hs hsep (by simpa [Q₀, Q₁, H₀, H₁] using htv)
    hmix₀.1 hmix₁.1
  exact d2_fixedRisk_lower_of_countRisk_bounds htest hmix₀.2 hmix₁.2

/-- The normalized relaxed law at its realization-dependent Poisson intensity
has the unnormalized common-anchor and active-cell rates. -/
lemma map_finiteSampleHistogram_relaxedAnchored_eq_pi
    {n m : ℕ} {epsilon anchor sampleScale : ℝ} (q pi mu : Fin m → ℝ)
    (he0 : 0 < epsilon) (hehalf : epsilon ≤ 1 / 2)
    (ha : 0 ≤ anchor) (hq : ∀ i, 0 ≤ q i)
    (hS : 0 < anchor + ∑ i, q i)
    (hpi : ∀ i, pi i ∈ Set.Icc epsilon (1 - epsilon))
    (hmu : ∀ i, mu i ∈ Set.Icc (0 : ℝ) 1)
    (hscale : 0 ≤ sampleScale) :
    Measure.map
        (fun s : FiniteSample (Fin (m + 1) × Fin 3) =>
          finiteSampleHistogram s.points)
        (finitePoissonSampleLaw
          (Measure.map oneArmObservationTripleLabel
            (obsLaw ((oneArmRelaxedAnchoredControlZero (n := n) q pi mu
              he0 hehalf ha hq hS hpi hmu).1)))
          (sampleScale * (anchor + ∑ i, q i)).toNNReal) =
      Measure.pi (fun u : Fin (m + 1) × Fin 3 =>
        poissonMeasure (Fin.cases
          (![0, (sampleScale * anchor * epsilon).toNNReal,
              (sampleScale * anchor * (1 - epsilon)).toNNReal] u.2)
          (fun i =>
            ![(sampleScale * q i * pi i * mu i).toNNReal,
              (sampleScale * q i * pi i * (1 - mu i)).toNNReal,
              (sampleScale * q i * (1 - pi i)).toNNReal] u.2)
          u.1)) := by
  let P := obsLaw ((oneArmRelaxedAnchoredControlZero (n := n) q pi mu
    he0 hehalf ha hq hS hpi hmu).1)
  let labelLaw := Measure.map oneArmObservationTripleLabel P
  let lam := (sampleScale * (anchor + ∑ i, q i)).toNNReal
  have hlabel : Measurable
      (oneArmObservationTripleLabel : Obs (m + 1) → Fin (m + 1) × Fin 3) :=
    measurable_of_finite _
  letI : IsProbabilityMeasure labelLaw :=
    Measure.isProbabilityMeasure_map hlabel.aemeasurable
  rw [map_finiteSampleHistogram_finitePoissonSampleLaw_eq_pi_singleton
    labelLaw lam]
  congr with u
  congr 1
  have hcell : (labelLaw {u}).toNNReal =
      (oneArmObservationTriplePartition (m + 1)).cellMass P u := by
    rw [Measure.map_apply hlabel (MeasurableSet.singleton u)]
    rfl
  rw [hcell]
  rcases u with ⟨r, j⟩
  refine Fin.cases ?_ (fun i => ?_) r
  · apply congrArg poissonMeasure
    simpa [lam, P] using
      oneArmRelaxedAnchored_anchor_rates q pi mu he0 hehalf ha hq hS
        hpi hmu hscale j
  · apply congrArg poissonMeasure
    simpa [lam, P] using
      oneArmRelaxedAnchored_active_rates q pi mu he0 hehalf ha hq hS
        hpi hmu hscale i j

lemma map_curry_histogram_relaxedAnchored_eq_pi
    {n m : ℕ} {epsilon anchor sampleScale : ℝ} (q pi mu : Fin m → ℝ)
    (he0 : 0 < epsilon) (hehalf : epsilon ≤ 1 / 2)
    (ha : 0 ≤ anchor) (hq : ∀ i, 0 ≤ q i)
    (hS : 0 < anchor + ∑ i, q i)
    (hpi : ∀ i, pi i ∈ Set.Icc epsilon (1 - epsilon))
    (hmu : ∀ i, mu i ∈ Set.Icc (0 : ℝ) 1)
    (hscale : 0 ≤ sampleScale) :
    Measure.map curryOneArmTripleCounts
        (Measure.map
          (fun s : FiniteSample (Fin (m + 1) × Fin 3) ↦
            finiteSampleHistogram s.points)
          (finitePoissonSampleLaw
            (Measure.map oneArmObservationTripleLabel
              (obsLaw ((oneArmRelaxedAnchoredControlZero (n := n) q pi mu
                he0 hehalf ha hq hS hpi hmu).1)))
            (sampleScale * (anchor + ∑ i, q i)).toNNReal)) =
      Measure.pi (fun k : Fin (m + 1) ↦
        (triplePoissonPMF
          (Fin.cases 0 (fun i ↦
            (sampleScale * q i * pi i * mu i).toNNReal) k)
          (Fin.cases (sampleScale * anchor * epsilon).toNNReal (fun i ↦
            (sampleScale * q i * pi i * (1 - mu i)).toNNReal) k)
          (Fin.cases (sampleScale * anchor * (1 - epsilon)).toNNReal (fun i ↦
            (sampleScale * q i * (1 - pi i)).toNNReal) k)).toMeasure) := by
  rw [map_finiteSampleHistogram_relaxedAnchored_eq_pi q pi mu he0 hehalf
    ha hq hS hpi hmu hscale]
  let lam11 : Fin (m + 1) → ℝ≥0 := fun k ↦
    Fin.cases 0 (fun i ↦
      (sampleScale * q i * pi i * mu i).toNNReal) k
  let lam10 : Fin (m + 1) → ℝ≥0 := fun k ↦
    Fin.cases (sampleScale * anchor * epsilon).toNNReal (fun i ↦
      (sampleScale * q i * pi i * (1 - mu i)).toNNReal) k
  let lam0 : Fin (m + 1) → ℝ≥0 := fun k ↦
    Fin.cases (sampleScale * anchor * (1 - epsilon)).toNNReal (fun i ↦
      (sampleScale * q i * (1 - pi i)).toNNReal) k
  have hkernel :
      (fun u : Fin (m + 1) × Fin 3 ↦
        poissonMeasure (Fin.cases
          (![0, (sampleScale * anchor * epsilon).toNNReal,
              (sampleScale * anchor * (1 - epsilon)).toNNReal] u.2)
          (fun i ↦
            ![(sampleScale * q i * pi i * mu i).toNNReal,
              (sampleScale * q i * pi i * (1 - mu i)).toNNReal,
              (sampleScale * q i * (1 - pi i)).toNNReal] u.2)
          u.1)) =
        (fun u ↦ poissonMeasure (![lam11 u.1, lam10 u.1, lam0 u.1] u.2)) := by
    funext u
    rcases u with ⟨k, j⟩
    refine Fin.cases ?_ (fun i ↦ ?_) k <;> fin_cases j <;> rfl
  rw [hkernel]
  exact map_curryOneArmTripleCounts_pi_poisson lam11 lam10 lam0

/-- Total functional separation contributed by `d` active shifted-grid
coordinates at the four-`n` Poissonization scale. -/
noncomputable def oneArmCalibratedSeparation
    (n d D : ℕ) (κ : ℝ) : ℝ :=
  (d : ℝ) * ((D : ℝ) / (128 * (n : ℝ))) *
    oneArmShiftedPoleScale κ D * oneArmShiftedJordanGap κ

/-- Once the two conditioned count risks satisfy the calibrated D.2 bounds,
the shifted-grid signal yields the explicit high-dimensional minimax term. -/
theorem oneArmHighDimensional_calibrated_lower
    {n d D : ℕ} {epsilon κ tail risk₀ risk₁ : ℝ}
    (hn : 0 < n) (hlog : 0 < Real.log n)
    (hDnat : 1 ≤ D) (hDlog : (D : ℝ) ≤ 20 * Real.log n)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (htail : tail ≤ (oneArmCalibratedSeparation n d D κ) ^ 2 / 32)
    (htest :
      ((oneArmCalibratedSeparation n d D κ / 2) ^ 2 *
          ((1 - (1 / 4 : ℝ)) / 2)) ≤ max risk₀ risk₁)
    (hrisk₀ : risk₀ ≤
      2 * oneArmMinimaxRisk n d epsilon +
        2 * (oneArmCalibratedSeparation n d D κ / 8) ^ 2 + tail)
    (hrisk₁ : risk₁ ≤
      2 * oneArmMinimaxRisk n d epsilon +
        2 * (oneArmCalibratedSeparation n d D κ / 8) ^ 2 + tail) :
    (κ ^ 14 / (25600 * (153600000000000 : ℝ) ^ 2)) *
        ((d : ℝ) ^ 2 / ((n : ℝ) ^ 2 * (Real.log n) ^ 2)) ≤
      oneArmMinimaxRisk n d epsilon := by
  let Δ := oneArmCalibratedSeparation n d D κ
  have hΔ : 0 ≤ Δ := by
    have hpole0 : 0 ≤ oneArmShiftedPoleScale κ D :=
      (oneArmShiftedPoleScale_pos hκ hDnat).le
    have hgap0 : 0 ≤ oneArmShiftedJordanGap κ :=
      (by positivity : 0 ≤ κ ^ 2 / 120).trans
        (oneArmShiftedJordanGap_lower hκ hκ1)
    dsimp [Δ, oneArmCalibratedSeparation]
    positivity
  have hD2 : Δ ^ 2 / 64 ≤ oneArmMinimaxRisk n d epsilon :=
    oneArmCalibratedD2_lower hΔ htail htest hrisk₀ hrisk₁
  have hcell := oneArmCalibratedSignal_lower hn hDnat hκ hκ1
  have hd0 : (0 : ℝ) ≤ d := by positivity
  have hsignal :
      (d : ℝ) *
          (κ ^ 7 / (153600000000000 * (n : ℝ) * (D : ℝ))) ≤ Δ := by
    dsimp [Δ, oneArmCalibratedSeparation]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hcell hd0
  have hsquare :
      ((((d : ℝ) * κ ^ 7 /
          (153600000000000 * (n : ℝ) * (D : ℝ))) ^ 2) / 64) ≤
        Δ ^ 2 / 64 := by
    have hleft0 : 0 ≤
        (d : ℝ) * κ ^ 7 /
          (153600000000000 * (n : ℝ) * (D : ℝ)) := by positivity
    have hsignal' :
        (d : ℝ) * κ ^ 7 /
            (153600000000000 * (n : ℝ) * (D : ℝ)) ≤ Δ := by
      simpa [mul_div_assoc] using hsignal
    nlinarith
  apply oneArmHighDimensional_rate_of_calibrated_signal
    hn hlog hDnat hDlog
  exact hsquare.trans hD2

end CausalSmith.Stat.DiscreteAteMinimaxLoggap
