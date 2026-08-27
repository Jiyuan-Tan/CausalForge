import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.OneArmHighDimensionalAssembly
import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.OneArmConcentrationEnvelope
import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.OneArmLogCalibration
import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.OneArmQuantitativePredictive
import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.OneArmShiftedPredictiveTV

/-!
# Quantitative shifted-prior assembly

This file packages the two inverse-tilted shifted-grid priors used by the
high-dimensional branch.  It records their raw moment matching, functional
separation, and common expected active mass in the exact form required by the
conditioning and count-risk assembly.
-/

namespace CausalSmith.Stat.DiscreteAteMinimaxLoggap

open MeasureTheory ProbabilityTheory Causalean.Stat
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open scoped BigOperators ENNReal NNReal

/-- The law of the observed triple label under a discrete law is a probability
measure, being the pushforward of the observation law along a measurable map on
a finite space. -/
noncomputable local instance shiftedTripleLabelLaw_isProbabilityMeasure
    {d : ℕ} (P : DiscreteLaw d) :
    IsProbabilityMeasure
      (Measure.map oneArmObservationTripleLabel (obsLaw P)) :=
  Measure.isProbabilityMeasure_map (measurable_of_finite _).aemeasurable

/-- The propensity produced by lifting the shifted grid through the inverse tilt
lies in the admissible overlap band `[ε, 1 − ε]` at every cell, including the
"no cell" value, provided the inflated overlap level `ε·(1 + κ)` stays below
`1 − ε`. -/
lemma oneArmShiftedLiftedPropensity_mem_Icc
    {D : ℕ} {epsilon κ : ℝ}
    (he0 : 0 < epsilon) (hoverlap : epsilon * (1 + κ) ≤ 1 - epsilon)
    (hD : 1 ≤ D) (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    ∀ z : Option (Fin (2 * D + 4)),
      liftedPropensity epsilon (oneArmShiftedPoleScale κ D)
          (oneArmShiftedSelectionGrid κ D) z ∈
        Set.Icc epsilon (1 - epsilon) := by
  apply liftedPropensity_mem_Icc_of_shift_le he0.le
    (oneArmShiftedPoleScale_pos hκ hD).le hκ.le
    (oneArmShiftedSelectionGrid_pos hκ hκ1 hD)
  · intro i
    unfold oneArmShiftedPoleScale
    exact mul_le_mul_of_nonneg_left
      (oneArmShiftedSelectionGrid_mem_Icc hκ hκ1 hD i).1 hκ.le
  · exact hoverlap

/-- The outcome mean produced by lifting the shifted grid lies in `[0,1]` at
every cell, so it is a legitimate success probability. -/
lemma oneArmShiftedLiftedOutcomeMean_mem_Icc
    {D : ℕ} {κ : ℝ} (hD : 1 ≤ D) (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    ∀ z : Option (Fin (2 * D + 4)),
      liftedOutcomeMean (oneArmShiftedPoleScale κ D)
          (oneArmShiftedSelectionGrid κ D) z ∈ Set.Icc (0 : ℝ) 1 :=
  liftedOutcomeMean_mem_Icc (oneArmShiftedPoleScale_pos hκ hD).le
    (oneArmShiftedPole_le_grid hκ hκ1 hD)

/-- The Jordan construction on the shifted selected grid produces two
inverse-tilted priors with all three quantitative properties needed later:
raw moment matching, the calibrated functional gap, and a common mass center. -/
theorem exists_oneArmShiftedInverseTiltPriors
    {D : ℕ} {epsilon κ scale : ℝ}
    (hD : 1 ≤ D) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hscale : 0 ≤ scale) :
    ∃ ν₀ ν₁ : PMF (Option (Fin (2 * D + 4))),
      (∀ i j k : ℕ, i + j + k ≤ D →
        ∑ z, (ν₀ z).toReal *
            (liftedCellMass scale (oneArmShiftedSelectionGrid κ D) z ^ i *
              (liftedCellMass scale (oneArmShiftedSelectionGrid κ D) z *
                liftedPropensity epsilon (oneArmShiftedPoleScale κ D)
                  (oneArmShiftedSelectionGrid κ D) z) ^ j *
              (liftedCellMass scale (oneArmShiftedSelectionGrid κ D) z *
                liftedPropensity epsilon (oneArmShiftedPoleScale κ D)
                  (oneArmShiftedSelectionGrid κ D) z *
                liftedOutcomeMean (oneArmShiftedPoleScale κ D)
                  (oneArmShiftedSelectionGrid κ D) z) ^ k) =
          ∑ z, (ν₁ z).toReal *
            (liftedCellMass scale (oneArmShiftedSelectionGrid κ D) z ^ i *
              (liftedCellMass scale (oneArmShiftedSelectionGrid κ D) z *
                liftedPropensity epsilon (oneArmShiftedPoleScale κ D)
                  (oneArmShiftedSelectionGrid κ D) z) ^ j *
              (liftedCellMass scale (oneArmShiftedSelectionGrid κ D) z *
                liftedPropensity epsilon (oneArmShiftedPoleScale κ D)
                  (oneArmShiftedSelectionGrid κ D) z *
                liftedOutcomeMean (oneArmShiftedPoleScale κ D)
                  (oneArmShiftedSelectionGrid κ D) z) ^ k)) ∧
      scale * oneArmShiftedPoleScale κ D * oneArmShiftedJordanGap κ ≤
        (∑ z, (ν₀ z).toReal *
            (liftedCellMass scale (oneArmShiftedSelectionGrid κ D) z *
              liftedOutcomeMean (oneArmShiftedPoleScale κ D)
                (oneArmShiftedSelectionGrid κ D) z)) -
          ∑ z, (ν₁ z).toReal *
            (liftedCellMass scale (oneArmShiftedSelectionGrid κ D) z *
              liftedOutcomeMean (oneArmShiftedPoleScale κ D)
                (oneArmShiftedSelectionGrid κ D) z) ∧
      (∑ z, (ν₀ z).toReal *
          liftedCellMass scale (oneArmShiftedSelectionGrid κ D) z =
        scale * oneArmShiftedPoleScale κ D) ∧
      (∑ z, (ν₁ z).toReal *
          liftedCellMass scale (oneArmShiftedSelectionGrid κ D) z =
        scale * oneArmShiftedPoleScale κ D) := by
  obtain ⟨v, hvzero, hvpos, _hvnorm, hvmom, hvgap⟩ :=
    exists_oneArmShiftedSelectionGrid_jordan_priors D hD hκ hκ1
  let ω₀ := positiveJordanPMF v hvpos
  have hvneg : 0 < negativeJordanMass v := by
    simpa [positiveJordanMass_eq_negativeJordanMass v hvzero] using hvpos
  let ω₁ := negativeJordanPMF v hvneg
  let ht₀ := oneArmShiftedSelectionGrid_inverseTiltWeight_nonneg
    D hκ hκ1 hD ω₀
  let ht₁ := oneArmShiftedSelectionGrid_inverseTiltWeight_nonneg
    D hκ hκ1 hD ω₁
  let ν₀ := inverseTiltPMF ω₀ (oneArmShiftedSelectionGrid κ D)
    (oneArmShiftedPoleScale κ D) ht₀
  let ν₁ := inverseTiltPMF ω₁ (oneArmShiftedSelectionGrid κ D)
    (oneArmShiftedPoleScale κ D) ht₁
  refine ⟨ν₀, ν₁, ?_, ?_, ?_, ?_⟩
  · intro i j k hdeg
    exact oneArmShiftedSelection_inverseTilt_liftedRawMoment_eq
      hD hκ hκ1 ω₀ ω₁ hvmom scale epsilon i j k hdeg
  · apply inverseTilt_shifted_liftedFunctional_gap
      hκ hκ1 hD hscale ω₀ ω₁
    simpa [oneArmShiftedJordanGap, ω₀, ω₁, hvneg] using hvgap
  · exact inverseTilt_liftedCellMass_sum ω₀
      (oneArmShiftedSelectionGrid κ D) ht₀
      (fun i => ne_of_gt (oneArmShiftedSelectionGrid_pos hκ hκ1 hD i))
  · exact inverseTilt_liftedCellMass_sum ω₁
      (oneArmShiftedSelectionGrid κ D) ht₁
      (fun i => ne_of_gt (oneArmShiftedSelectionGrid_pos hκ hκ1 hD i))

/-- The explicit two-statistic envelope gives positive mass to the relaxed
good event used for conditioning either shifted inverse-tilted product prior. -/
lemma oneArmShiftedRelaxedGood_eventMass_ne_zero
    {D m : ℕ} {κ scale δ : ℝ}
    (hD : 1 ≤ D) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hscale : 0 ≤ scale) (hδ : 0 < δ) (hδ1 : δ < 1)
    [MeasurableSpace (Option (Fin (2 * D + 4)))]
    [DiscreteMeasurableSpace (Option (Fin (2 * D + 4)))]
    (nu : PMF (Option (Fin (2 * D + 4))))
    (hbad :
      ENNReal.ofReal (m * scale ^ 2 / δ ^ 2) +
          ENNReal.ofReal (m * scale ^ 2 / δ ^ 2) < 1) :
    let p := oneArmProductMassAtom scale (oneArmShiftedSelectionGrid κ D)
    let mu := liftedOutcomeMean (oneArmShiftedPoleScale κ D)
      (oneArmShiftedSelectionGrid κ D)
    let massCenter := m * ∫ u, p u ∂nu.toMeasure
    let theta := m * ∫ u,
      oneArmProductFunctionalAtom scale (oneArmShiftedPoleScale κ D)
        (oneArmShiftedSelectionGrid κ D) u ∂nu.toMeasure
    let G := oneArmRelaxedAnchoredGood (m := m)
      (1 - massCenter) p mu theta δ δ
    @oneArmFiniteEventMass _ _ (oneArmFiniteIidPMF nu m) G
      (Classical.decPred G) ≠ 0 := by
  classical
  dsimp only
  let p := oneArmProductMassAtom scale (oneArmShiftedSelectionGrid κ D)
  let mu := liftedOutcomeMean (oneArmShiftedPoleScale κ D)
    (oneArmShiftedSelectionGrid κ D)
  let f := oneArmProductFunctionalAtom scale (oneArmShiftedPoleScale κ D)
    (oneArmShiftedSelectionGrid κ D)
  let massCenter := m * ∫ u, p u ∂nu.toMeasure
  let theta := m * ∫ u, f u ∂nu.toMeasure
  let G := oneArmRelaxedAnchoredGood (m := m)
    (1 - massCenter) p mu theta δ δ
  change oneArmFiniteEventMass (oneArmFiniteIidPMF nu m) G ≠ 0
  have hsubset : {z : Fin m → Option (Fin (2 * D + 4)) | ¬ G z} ⊆
      ({z | δ ≤ |(∑ i, p (z i)) - massCenter|} ∪
        {z | δ ≤ |(∑ i, f (z i)) - theta|}) := by
    intro z hz
    by_cases hm : δ ≤ |(∑ i, p (z i)) - massCenter|
    · exact Set.mem_union_left _ hm
    · by_cases hf : δ ≤ |(∑ i, f (z i)) - theta|
      · exact Set.mem_union_right _ hf
      · exfalso
        apply hz
        exact oneArmProductConcentrationGood_relaxed p mu massCenter theta δ δ
          hδ1 z (lt_of_not_ge hm) (by
            simpa only [f, p, mu, oneArmProductFunctionalAtom,
              oneArmProductMassAtom] using
              lt_of_not_ge hf)
  have henv := oneArmShifted_mass_functional_bad_le_sq_envelope
    (m := m) hκ hκ1 hD hscale nu hδ
  have hcompl : oneArmFiniteEventMass (oneArmFiniteIidPMF nu m)
      (fun z => ¬ G z) < 1 := by
    rw [oneArmFiniteEventMass_eq_toMeasure,
      oneArmFiniteIidPMF_toMeasure]
    exact (measure_mono hsubset |>.trans henv).trans_lt hbad
  intro hzero
  have hsum := oneArmFiniteEventMass_add_compl
    (oneArmFiniteIidPMF nu m) G
  rw [hzero, zero_add] at hsum
  exact (ne_of_lt hcompl) hsum

/-- End-to-end high-dimensional gate from the two conditioned count
predictives.  All constants are fixed here; later instantiations only need to
construct the shifted priors and discharge their target, TV, and tail bounds. -/
theorem oneArmHighDimensional_lower_of_conditioned_count_tv
    {n d D : ℕ} {epsilon κ theta₀ theta₁ : ℝ}
    {ι₀ ι₁ : Type*} [Fintype ι₀] [Fintype ι₁]
    (hn : 0 < n) (hlog : 0 < Real.log n)
    (hDnat : 1 ≤ D) (hDlog : (D : ℝ) ≤ 20 * Real.log n)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (P₀ : ι₀ → ControlZeroLaw n d epsilon)
    (P₁ : ι₁ → ControlZeroLaw n d epsilon)
    (w₀ : ι₀ → ℝ≥0∞) (w₁ : ι₁ → ℝ≥0∞)
    (hw₀ : ∑ i, w₀ i = 1) (hw₁ : ∑ i, w₁ i = 1)
    (lam₀ : ι₀ → ℝ≥0) (lam₁ : ι₁ → ℝ≥0)
    (htarget₀ : ∀ i,
      |treatedFunctional (P₀ i).1 - theta₀| ≤
        oneArmCalibratedSeparation n d D κ / 8)
    (htarget₁ : ∀ i,
      |treatedFunctional (P₁ i).1 - theta₁| ≤
        oneArmCalibratedSeparation n d D κ / 8)
    (hsep : oneArmCalibratedSeparation n d D κ ≤ |theta₀ - theta₁|)
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
            (lam₁ i)))) ≤ 1 / 4)
    (htail₀ : ∀ i, theta₀ ^ 2 *
      (poissonMeasure (lam₀ i)).real {k | k < n} ≤
        oneArmCalibratedSeparation n d D κ ^ 2 / 32)
    (htail₁ : ∀ i, theta₁ ^ 2 *
      (poissonMeasure (lam₁ i)).real {k | k < n} ≤
        oneArmCalibratedSeparation n d D κ ^ 2 / 32) :
    (κ ^ 14 / (25600 * (153600000000000 : ℝ) ^ 2)) *
        ((d : ℝ) ^ 2 / ((n : ℝ) ^ 2 * Real.log n ^ 2)) ≤
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
  have hraw := oneArmMinimaxRisk_lower_of_conditioned_count_tv
    (radius := Δ / 8) (s := Δ / 2) (c := 1 / 4)
    (tail := Δ ^ 2 / 32)
    P₀ P₁ w₀ w₁ hw₀ hw₁ lam₀ lam₁ htarget₀ htarget₁
    (div_nonneg hΔ (by norm_num)) (div_nonneg hΔ (by norm_num))
    (by convert hsep using 1 <;> ring)
    htv htail₀ htail₁
  have hD2 : Δ ^ 2 / 64 ≤ oneArmMinimaxRisk n d epsilon := by
    dsimp [Δ] at hraw ⊢
    nlinarith
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
