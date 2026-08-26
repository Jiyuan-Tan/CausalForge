import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.OneArmShiftedQuantitativeAssembly
import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.OneArmScalarFinalAssembly
import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.OneArmPoissonMonotonicity

/-!
# Headline assembly for the one-arm converse

This module instantiates the shifted finite-grid priors on their relaxed
good events and closes the cited one-arm minimax gate.
-/

namespace CausalSmith.Stat.DiscreteAteMinimaxLoggap

open MeasureTheory ProbabilityTheory Causalean.Stat
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open scoped BigOperators ENNReal NNReal

local instance headlineOptionMeasurableSpace (N : ℕ) :
    MeasurableSpace (Option (Fin N)) := ⊤

noncomputable local instance headlineTripleLabelLaw_isProbabilityMeasure
    {d : ℕ} (P : DiscreteLaw d) :
    IsProbabilityMeasure
      (Measure.map oneArmObservationTripleLabel (obsLaw P)) :=
  Measure.isProbabilityMeasure_map (measurable_of_finite _).aemeasurable

private lemma oneArmRelaxedGood_compl_mass_le
    {D m : ℕ} {κ scale δ : ℝ}
    (hD : 1 ≤ D) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hscale : 0 ≤ scale) (hδ : 0 < δ) (hδ1 : δ < 1)
    [MeasurableSpace (Option (Fin (2 * D + 4)))]
    [DiscreteMeasurableSpace (Option (Fin (2 * D + 4)))]
    (nu : PMF (Option (Fin (2 * D + 4)))) :
    let p := oneArmProductMassAtom scale (oneArmShiftedSelectionGrid κ D)
    let mu := liftedOutcomeMean (oneArmShiftedPoleScale κ D)
      (oneArmShiftedSelectionGrid κ D)
    let massCenter := m * ∫ u, p u ∂nu.toMeasure
    let theta := m * ∫ u,
      oneArmProductFunctionalAtom scale (oneArmShiftedPoleScale κ D)
        (oneArmShiftedSelectionGrid κ D) u ∂nu.toMeasure
    let G := oneArmRelaxedAnchoredGood (m := m)
      (1 - massCenter) p mu theta δ δ
    @oneArmFiniteEventMass _ _ (oneArmFiniteIidPMF nu m) (fun z ↦ ¬ G z)
        (Classical.decPred (fun z ↦ ¬ G z)) ≤
      ENNReal.ofReal (m * scale ^ 2 / δ ^ 2) +
        ENNReal.ofReal (m * scale ^ 2 / δ ^ 2) := by
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
  rw [oneArmFiniteEventMass_eq_toMeasure, oneArmFiniteIidPMF_toMeasure]
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
              oneArmProductMassAtom] using lt_of_not_ge hf)
  exact (measure_mono hsubset).trans
    (oneArmShifted_mass_functional_bad_le_sq_envelope
      (m := m) hκ hκ1 hD hscale nu hδ)

set_option maxHeartbeats 800000 in
-- The fully concrete finite-mixture transport elaborates several large measure terms.
/-- The concrete shifted-prior good-event construction gives the logarithmic
high-dimensional one-arm lower bound whenever its elementary scalar budgets
hold. -/
theorem oneArmHighDimensional_shiftedPrior
    {n d : ℕ} {epsilon κ : ℝ}
    (hn : 400 ≤ n) (hd : 0 < d)
    (he0 : 0 < epsilon) (hehalf : epsilon < 1 / 2)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hoverlap : epsilon * (1 + κ) ≤ 1 - epsilon)
    (hcap : (d : ℝ) *
        ((oneArmLogDegree n : ℝ) / (128 * (n : ℝ))) *
          oneArmShiftedPoleScale κ (oneArmLogDegree n) ≤ 1)
    (hbad :
      ENNReal.ofReal ((d : ℝ) *
          ((oneArmLogDegree n : ℝ) / (128 * (n : ℝ))) ^ 2 /
            (oneArmCalibratedSeparation n d (oneArmLogDegree n) κ / 16) ^ 2) +
        ENNReal.ofReal ((d : ℝ) *
          ((oneArmLogDegree n : ℝ) / (128 * (n : ℝ))) ^ 2 /
            (oneArmCalibratedSeparation n d (oneArmLogDegree n) κ / 16) ^ 2) ≤
        ENNReal.ofReal (1 / 32 : ℝ))
    (hraw : 2 * (d : ℝ) / (n : ℝ) ^ 4 ≤ 1 / 8)
    (htail : ((d : ℝ) *
          ((oneArmLogDegree n : ℝ) / (128 * (n : ℝ)))) ^ 2 *
        (n : ℝ)⁻¹ ^ 2 ≤
          oneArmCalibratedSeparation n d (oneArmLogDegree n) κ ^ 2 / 32) :
    (κ ^ 14 / (25600 * (153600000000000 : ℝ) ^ 2)) *
        ((d : ℝ) ^ 2 / ((n : ℝ) ^ 2 * Real.log n ^ 2)) ≤
      oneArmMinimaxRisk n (d + 1) epsilon := by
  classical
  let D := oneArmLogDegree n
  let scale : ℝ := (D : ℝ) / (128 * (n : ℝ))
  let pole := oneArmShiftedPoleScale κ D
  let x := oneArmShiftedSelectionGrid κ D
  let p := oneArmProductMassAtom scale x
  let pi := liftedPropensity epsilon pole x
  let mu := liftedOutcomeMean pole x
  let sampleScale : ℝ := 4 * (n : ℝ)
  let Δ := oneArmCalibratedSeparation n d D κ
  let δ := Δ / 16
  have hn2 : 2 ≤ n := by omega
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hD : 1 ≤ D := oneArmLogDegree_pos hn2
  have hlog : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hDlog : (D : ℝ) ≤ 20 * Real.log n :=
    oneArmLogDegree_le_twenty_log (by omega)
  have hscale : 0 ≤ scale := by dsimp [scale]; positivity
  have hpole : 0 < pole := oneArmShiftedPoleScale_pos hκ hD
  have hgap : 0 < oneArmShiftedJordanGap κ := by
    unfold oneArmShiftedJordanGap
    positivity
  have hΔ : 0 < Δ := by
    dsimp [Δ, oneArmCalibratedSeparation]
    positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ < 1 := by
    have hgap1 : oneArmShiftedJordanGap κ ≤ 1 := by
      unfold oneArmShiftedJordanGap
      have hden : 2 ≤ (1 + κ) * (2 + κ) * (3 + κ) := by
        calc
          (2 : ℝ) ≤ 1 * 2 * 3 := by norm_num
          _ ≤ (1 + κ) * (2 + κ) * (3 + κ) := by
            gcongr <;> linarith
      have hκ2 : κ ^ 2 ≤ 1 := by nlinarith [sq_nonneg (1 - κ)]
      have hdenpos : 0 < (1 + κ) * (2 + κ) * (3 + κ) := by positivity
      rw [div_div, div_le_iff₀ (mul_pos hdenpos (by norm_num : (0 : ℝ) < 10))]
      nlinarith
    have hactive : (d : ℝ) * scale * pole ≤ 1 := by
      simpa [D, scale, pole, mul_assoc] using hcap
    dsimp [δ, Δ, oneArmCalibratedSeparation]
    nlinarith [mul_nonneg (mul_nonneg (Nat.cast_nonneg d) hscale) hpole.le,
      mul_le_mul_of_nonneg_left hgap1
        (mul_nonneg (mul_nonneg (Nat.cast_nonneg d) hscale) hpole.le)]
  obtain ⟨v, hvzero, hvpos, _hvnorm, hvmom, hvgap⟩ :=
    exists_oneArmShiftedSelectionGrid_jordan_priors D hD hκ hκ1
  have hvneg : 0 < negativeJordanMass v := by
    simpa [positiveJordanMass_eq_negativeJordanMass v hvzero] using hvpos
  let omega₀ := positiveJordanPMF v hvpos
  let omega₁ := negativeJordanPMF v hvneg
  let hw₀ := oneArmShiftedSelectionGrid_inverseTiltWeight_nonneg
    D hκ hκ1 hD omega₀
  let hw₁ := oneArmShiftedSelectionGrid_inverseTiltWeight_nonneg
    D hκ hκ1 hD omega₁
  let nu₀ := inverseTiltPMF omega₀ x pole hw₀
  let nu₁ := inverseTiltPMF omega₁ x pole hw₁
  have hmass₀ : ∫ u, p u ∂nu₀.toMeasure = scale * pole := by
    rw [PMF.integral_eq_sum]
    exact inverseTilt_liftedCellMass_sum omega₀ x hw₀
      (fun i ↦ ne_of_gt (oneArmShiftedSelectionGrid_pos hκ hκ1 hD i))
  have hmass₁ : ∫ u, p u ∂nu₁.toMeasure = scale * pole := by
    rw [PMF.integral_eq_sum]
    exact inverseTilt_liftedCellMass_sum omega₁ x hw₁
      (fun i ↦ ne_of_gt (oneArmShiftedSelectionGrid_pos hκ hκ1 hD i))
  let massCenter : ℝ := (d : ℝ) * scale * pole
  let anchor : ℝ := 1 - massCenter
  let theta₀ : ℝ := (d : ℝ) * ∫ u,
    oneArmProductFunctionalAtom scale pole x u ∂nu₀.toMeasure
  let theta₁ : ℝ := (d : ℝ) * ∫ u,
    oneArmProductFunctionalAtom scale pole x u ∂nu₁.toMeasure
  let G₀ := oneArmRelaxedAnchoredGood (m := d) anchor p mu theta₀ δ δ
  let G₁ := oneArmRelaxedAnchoredGood (m := d) anchor p mu theta₁ δ δ
  let ω₀ := oneArmFiniteIidPMF nu₀ d
  let ω₁ := oneArmFiniteIidPMF nu₁ d
  have hmc₀ : (d : ℝ) * ∫ u, p u ∂nu₀.toMeasure = massCenter := by
    rw [hmass₀]
    dsimp [massCenter]
    ring
  have hmc₁ : (d : ℝ) * ∫ u, p u ∂nu₁.toMeasure = massCenter := by
    rw [hmass₁]
    dsimp [massCenter]
    ring
  have ha : 0 ≤ anchor := by
    dsimp [anchor, massCenter]
    linarith [hcap]
  have hp : ∀ z, 0 ≤ p z := by
    intro z
    exact (oneArmShifted_massAtom_mem_Icc hκ hκ1 hD hscale z).1
  have hpi : ∀ z, pi z ∈ Set.Icc epsilon (1 - epsilon) := by
    simpa [pi, pole, x] using
      oneArmShiftedLiftedPropensity_mem_Icc he0 hoverlap hD hκ hκ1
  have hmu : ∀ z, mu z ∈ Set.Icc (0 : ℝ) 1 := by
    simpa [mu, pole, x] using
      oneArmShiftedLiftedOutcomeMean_mem_Icc hD hκ hκ1
  have hpi_pos : ∀ z, 0 < pi z := fun z ↦ he0.trans_le (hpi z).1
  have hbadBudget :
      ENNReal.ofReal ((d : ℝ) * scale ^ 2 / δ ^ 2) +
        ENNReal.ofReal ((d : ℝ) * scale ^ 2 / δ ^ 2) ≤
          ENNReal.ofReal (1 / 32 : ℝ) := by
    simpa only [D, scale, δ, Δ] using hbad
  have hbad₀ : oneArmFiniteEventMass ω₀ (fun z ↦ ¬ G₀ z) ≤
      ENNReal.ofReal (1 / 32 : ℝ) := by
    have h := oneArmRelaxedGood_compl_mass_le (m := d)
      hD hκ hκ1 hscale hδ hδ1 nu₀
    have hh := h.trans hbadBudget
    change oneArmFiniteEventMass (oneArmFiniteIidPMF nu₀ d)
      (fun z : Fin d → Option (Fin (2 * D + 4)) ↦ ¬ oneArmRelaxedAnchoredGood anchor p mu theta₀ δ δ z) ≤ _
    have hpred : (fun z : Fin d → Option (Fin (2 * D + 4)) ↦ ¬ oneArmRelaxedAnchoredGood anchor p mu theta₀ δ δ z) =
        (fun z : Fin d → Option (Fin (2 * D + 4)) ↦ ¬ oneArmRelaxedAnchoredGood
          (1 - (d : ℝ) * ∫ u, p u ∂nu₀.toMeasure) p mu theta₀ δ δ z) := by
      funext z
      rw [hmc₀]
    change @LE.le ℝ≥0∞ ENNReal.instPartialOrder.toLE _ _
    convert hh using 1
    rw [oneArmFiniteEventMass_eq_toMeasure,
      oneArmFiniteEventMass_eq_toMeasure]
    simpa only [p, mu, x, pole, theta₀, oneArmProductFunctionalAtom] using
      congrArg (fun G ↦ (oneArmFiniteIidPMF nu₀ d).toMeasure {z | G z}) hpred
  have hbad₁ : oneArmFiniteEventMass ω₁ (fun z ↦ ¬ G₁ z) ≤
      ENNReal.ofReal (1 / 32 : ℝ) := by
    have h := oneArmRelaxedGood_compl_mass_le (m := d)
      hD hκ hκ1 hscale hδ hδ1 nu₁
    have hh := h.trans hbadBudget
    change oneArmFiniteEventMass (oneArmFiniteIidPMF nu₁ d)
      (fun z : Fin d → Option (Fin (2 * D + 4)) ↦ ¬ oneArmRelaxedAnchoredGood anchor p mu theta₁ δ δ z) ≤ _
    have hpred : (fun z : Fin d → Option (Fin (2 * D + 4)) ↦ ¬ oneArmRelaxedAnchoredGood anchor p mu theta₁ δ δ z) =
        (fun z : Fin d → Option (Fin (2 * D + 4)) ↦ ¬ oneArmRelaxedAnchoredGood
          (1 - (d : ℝ) * ∫ u, p u ∂nu₁.toMeasure) p mu theta₁ δ δ z) := by
      funext z
      rw [hmc₁]
    change @LE.le ℝ≥0∞ ENNReal.instPartialOrder.toLE _ _
    convert hh using 1
    rw [oneArmFiniteEventMass_eq_toMeasure,
      oneArmFiniteEventMass_eq_toMeasure]
    simpa only [p, mu, x, pole, theta₁, oneArmProductFunctionalAtom] using
      congrArg (fun G ↦ (oneArmFiniteIidPMF nu₁ d).toMeasure {z | G z}) hpred
  have hG₀ : oneArmFiniteEventMass ω₀ G₀ ≠ 0 := by
    have h := oneArmShiftedRelaxedGood_eventMass_ne_zero (m := d) hD hκ hκ1
      hscale hδ hδ1 nu₀
    have hh := h (lt_of_le_of_lt hbadBudget (by norm_num))
    change oneArmFiniteEventMass (oneArmFiniteIidPMF nu₀ d)
      (oneArmRelaxedAnchoredGood anchor p mu theta₀ δ δ) ≠ 0
    have hpred :
        (oneArmRelaxedAnchoredGood anchor p mu theta₀ δ δ :
          (Fin d → Option (Fin (2 * D + 4))) → Prop) =
        oneArmRelaxedAnchoredGood
          (1 - (d : ℝ) * ∫ u, p u ∂nu₀.toMeasure) p mu theta₀ δ δ := by
      funext z
      rw [hmc₀]
    convert hh using 1
    exact congrArg (fun G ↦ @oneArmFiniteEventMass _ _
      (oneArmFiniteIidPMF nu₀ d) G (Classical.decPred G)) hpred
  have hG₁ : oneArmFiniteEventMass ω₁ G₁ ≠ 0 := by
    have h := oneArmShiftedRelaxedGood_eventMass_ne_zero (m := d) hD hκ hκ1
      hscale hδ hδ1 nu₁
    have hh := h (lt_of_le_of_lt hbadBudget (by norm_num))
    change oneArmFiniteEventMass (oneArmFiniteIidPMF nu₁ d)
      (oneArmRelaxedAnchoredGood anchor p mu theta₁ δ δ) ≠ 0
    have hpred :
        (oneArmRelaxedAnchoredGood anchor p mu theta₁ δ δ :
          (Fin d → Option (Fin (2 * D + 4))) → Prop) =
        oneArmRelaxedAnchoredGood
          (1 - (d : ℝ) * ∫ u, p u ∂nu₁.toMeasure) p mu theta₁ δ δ := by
      funext z
      rw [hmc₁]
    convert hh using 1
    exact congrArg (fun G ↦ @oneArmFiniteEventMass _ _
      (oneArmFiniteIidPMF nu₁ d) G (Classical.decPred G)) hpred
  let P₀ : {z // G₀ z} → ControlZeroLaw n (d + 1) epsilon := fun z ↦
    oneArmRelaxedLawOfGoodAtoms p pi mu he0 hehalf.le ha hp hpi hmu z
  let P₁ : {z // G₁ z} → ControlZeroLaw n (d + 1) epsilon := fun z ↦
    oneArmRelaxedLawOfGoodAtoms p pi mu he0 hehalf.le ha hp hpi hmu z
  let w₀ : {z // G₀ z} → ℝ≥0∞ := oneArmFiniteConditionedWeight ω₀ G₀
  let w₁ : {z // G₁ z} → ℝ≥0∞ := oneArmFiniteConditionedWeight ω₁ G₁
  have hwSum₀ : ∑ z, w₀ z = 1 := oneArmFiniteConditionedWeight_sum ω₀ G₀ hG₀
  have hwSum₁ : ∑ z, w₁ z = 1 := oneArmFiniteConditionedWeight_sum ω₁ G₁ hG₁
  let lam₀ : {z // G₀ z} → ℝ≥0 := fun z ↦
    (sampleScale * (anchor + ∑ i, p (z.1 i))).toNNReal
  let lam₁ : {z // G₁ z} → ℝ≥0 := fun z ↦
    (sampleScale * (anchor + ∑ i, p (z.1 i))).toNNReal
  have htarget₀ : ∀ z, |treatedFunctional (P₀ z).1 - theta₀| ≤ Δ / 8 := by
    intro z
    have h := oneArmRelaxedLawOfGoodAtoms_target (n := n) p pi mu he0 hehalf.le
      ha hp hpi hmu hpi_pos z
    dsimp [P₀]
    dsimp [δ] at h
    nlinarith
  have htarget₁ : ∀ z, |treatedFunctional (P₁ z).1 - theta₁| ≤ Δ / 8 := by
    intro z
    have h := oneArmRelaxedLawOfGoodAtoms_target (n := n) p pi mu he0 hehalf.le
      ha hp hpi hmu hpi_pos z
    dsimp [P₁]
    dsimp [δ] at h
    nlinarith
  have hsep : Δ ≤ |theta₀ - theta₁| := by
    have hfun := inverseTilt_shifted_liftedFunctional_gap hκ hκ1 hD
      hscale omega₀ omega₁ (by
        simpa [oneArmShiftedJordanGap, omega₀, omega₁, hvneg] using hvgap)
    have hfun' : scale * pole * oneArmShiftedJordanGap κ ≤
        (∑ z, (nu₀ z).toReal * (liftedCellMass scale x z *
          liftedOutcomeMean pole x z)) -
        ∑ z, (nu₁ z).toReal * (liftedCellMass scale x z *
          liftedOutcomeMean pole x z) := by
      simpa [oneArmShiftedJordanGap, nu₀, nu₁, hw₀, hw₁,
        omega₀, omega₁, x, pole] using hfun
    have hd0 : (0 : ℝ) ≤ d := by positivity
    have hmul := mul_le_mul_of_nonneg_left hfun' hd0
    have horder : 0 ≤ theta₀ - theta₁ := by
      dsimp [theta₀, theta₁]
      rw [PMF.integral_eq_sum, PMF.integral_eq_sum]
      have hleft : 0 ≤ (d : ℝ) *
          (scale * pole * oneArmShiftedJordanGap κ) := by positivity
      exact hleft.trans (by
        simpa only [nu₀, nu₁, x, pole, oneArmProductFunctionalAtom,
          smul_eq_mul, mul_sub]
          using hmul)
    rw [abs_of_nonneg horder]
    dsimp [theta₀, theta₁]
    rw [PMF.integral_eq_sum, PMF.integral_eq_sum]
    change (d : ℝ) * scale * pole * oneArmShiftedJordanGap κ ≤ _
    simpa only [oneArmProductFunctionalAtom, smul_eq_mul, mul_sub, mul_assoc]
      using hmul
  let anchorLaw : PMF (Fin 3 → ℕ) := triplePoissonPMF 0
    (sampleScale * anchor * epsilon).toNNReal
    (sampleScale * anchor * (1 - epsilon)).toNNReal
  let K : (Fin d → Option (Fin (2 * D + 4))) →
      Measure (Fin (d + 1) → Fin 3 → ℕ) := fun z ↦
    Measure.pi fun r ↦ Fin.cases (motive := fun _ ↦ Measure (Fin 3 → ℕ))
      anchorLaw.toMeasure
      (fun i ↦ (triplePoissonPMF
        (sampleScale * p (z i) * pi (z i) * mu (z i)).toNNReal
        (sampleScale * p (z i) * pi (z i) * (1 - mu (z i))).toNNReal
        (sampleScale * p (z i) * (1 - pi (z i))).toNNReal).toMeasure) r
  letI (z : Fin d → Option (Fin (2 * D + 4)))
      (r : Fin (d + 1)) : IsProbabilityMeasure
        (Fin.cases (motive := fun _ ↦ Measure (Fin 3 → ℕ))
          anchorLaw.toMeasure
          (fun i ↦ (triplePoissonPMF
            (sampleScale * p (z i) * pi (z i) * mu (z i)).toNNReal
            (sampleScale * p (z i) * pi (z i) * (1 - mu (z i))).toNNReal
            (sampleScale * p (z i) * (1 - pi (z i))).toNNReal).toMeasure) r) := by
    refine Fin.cases (motive := fun r ↦ IsProbabilityMeasure
      (Fin.cases (motive := fun _ ↦ Measure (Fin 3 → ℕ))
        anchorLaw.toMeasure
        (fun i ↦ (triplePoissonPMF
          (sampleScale * p (z i) * pi (z i) * mu (z i)).toNNReal
          (sampleScale * p (z i) * pi (z i) * (1 - mu (z i))).toNNReal
          (sampleScale * p (z i) * (1 - pi (z i))).toNNReal).toMeasure) r))
      (by dsimp; infer_instance) (fun i ↦ by dsimp; infer_instance) r
  letI (z : Fin d → Option (Fin (2 * D + 4))) :
      IsProbabilityMeasure (K z) := by dsimp [K]; infer_instance
  have hrawTV : tvDist (mixture (fun z ↦ ω₀ z) K)
      (mixture (fun z ↦ ω₁ z) K) ≤ 1 / 8 := by
    have h := tvDist_oneArmShiftedPriorPredictive_le (d := d)
      hn2 hκ hκ1 he0 hoverlap
      omega₀ omega₁ (by
        simpa only [omega₀, omega₁, hvneg] using hvmom) anchorLaw
    dsimp only [D, scale, x, pole, hw₀, hw₁, nu₀, nu₁, p, pi,
      mu, sampleScale, ω₀, ω₁, K] at h
    exact h.trans hraw
  have hbadReal₀ : (oneArmFiniteEventMass ω₀ (fun z ↦ ¬ G₀ z)).toReal ≤
      1 / 32 := by
    have h := ENNReal.toReal_mono (by norm_num : ENNReal.ofReal (1 / 32 : ℝ) ≠ ⊤) hbad₀
    simpa using h
  have hbadReal₁ : (oneArmFiniteEventMass ω₁ (fun z ↦ ¬ G₁ z)).toReal ≤
      1 / 32 := by
    have h := ENNReal.toReal_mono (by norm_num : ENNReal.ofReal (1 / 32 : ℝ) ≠ ⊤) hbad₁
    simpa using h
  have hcondTV : tvDist
      (oneArmFiniteConditionedMixture ω₀ G₀ hG₀ K)
      (oneArmFiniteConditionedMixture ω₁ G₁ hG₁ K) ≤ 1 / 4 := by
    have h := tvDist_two_finiteConditionedMixtures_le
      ω₀ ω₁ G₀ G₁ hG₀ hG₁ K K
    linarith
  have hcomponent₀ (z : {z // G₀ z}) :
      Measure.map curryOneArmTripleCounts
        (Measure.map (fun u : FiniteSample (Fin (d + 1) × Fin 3) ↦
          finiteSampleHistogram u.points)
          (finitePoissonSampleLaw
            (Measure.map oneArmObservationTripleLabel (obsLaw (P₀ z).1))
            (lam₀ z))) = K z.1 := by
    have h := map_curry_histogram_relaxedAnchored_eq_pi
      (n := n) (m := d) (epsilon := epsilon) (anchor := anchor)
      (sampleScale := sampleScale)
      (fun i ↦ p (z.1 i)) (fun i ↦ pi (z.1 i)) (fun i ↦ mu (z.1 i))
      he0 hehalf.le ha (fun i ↦ hp _) z.2.1 (fun i ↦ hpi _)
      (fun i ↦ hmu _) (by dsimp [sampleScale]; positivity)
    convert h using 1
    rfl
    rw [show K z.1 = Measure.pi (fun r ↦
      Fin.cases (motive := fun _ ↦ Measure (Fin 3 → ℕ)) anchorLaw.toMeasure
        (fun i ↦ (triplePoissonPMF
          (sampleScale * p (z.1 i) * pi (z.1 i) * mu (z.1 i)).toNNReal
          (sampleScale * p (z.1 i) * pi (z.1 i) * (1 - mu (z.1 i))).toNNReal
          (sampleScale * p (z.1 i) * (1 - pi (z.1 i))).toNNReal).toMeasure) r) by rfl]
    congr 1
    funext k
    refine Fin.cases ?_ (fun _ ↦ ?_) k <;> rfl
  have hcomponent₁ (z : {z // G₁ z}) :
      Measure.map curryOneArmTripleCounts
        (Measure.map (fun u : FiniteSample (Fin (d + 1) × Fin 3) ↦
          finiteSampleHistogram u.points)
          (finitePoissonSampleLaw
            (Measure.map oneArmObservationTripleLabel (obsLaw (P₁ z).1))
            (lam₁ z))) = K z.1 := by
    have h := map_curry_histogram_relaxedAnchored_eq_pi
      (n := n) (m := d) (epsilon := epsilon) (anchor := anchor)
      (sampleScale := sampleScale)
      (fun i ↦ p (z.1 i)) (fun i ↦ pi (z.1 i)) (fun i ↦ mu (z.1 i))
      he0 hehalf.le ha (fun i ↦ hp _) z.2.1 (fun i ↦ hpi _)
      (fun i ↦ hmu _) (by dsimp [sampleScale]; positivity)
    convert h using 1
    rfl
    rw [show K z.1 = Measure.pi (fun r ↦
      Fin.cases (motive := fun _ ↦ Measure (Fin 3 → ℕ)) anchorLaw.toMeasure
        (fun i ↦ (triplePoissonPMF
          (sampleScale * p (z.1 i) * pi (z.1 i) * mu (z.1 i)).toNNReal
          (sampleScale * p (z.1 i) * pi (z.1 i) * (1 - mu (z.1 i))).toNNReal
          (sampleScale * p (z.1 i) * (1 - pi (z.1 i))).toNNReal).toMeasure) r) by rfl]
    congr 1
    funext k
    refine Fin.cases ?_ (fun _ ↦ ?_) k <;> rfl
  have htv : tvDist
      (mixture w₀ (fun z ↦
        Measure.map (fun u : FiniteSample (Fin (d + 1) × Fin 3) ↦
          finiteSampleHistogram u.points)
          (finitePoissonSampleLaw
            (Measure.map oneArmObservationTripleLabel (obsLaw (P₀ z).1))
            (lam₀ z))))
      (mixture w₁ (fun z ↦
        Measure.map (fun u : FiniteSample (Fin (d + 1) × Fin 3) ↦
          finiteSampleHistogram u.points)
          (finitePoissonSampleLaw
            (Measure.map oneArmObservationTripleLabel (obsLaw (P₁ z).1))
            (lam₁ z)))) ≤ 1 / 4 := by
    let Q₀ := mixture w₀ (fun z ↦
      Measure.map (fun u : FiniteSample (Fin (d + 1) × Fin 3) ↦
        finiteSampleHistogram u.points)
        (finitePoissonSampleLaw
          (Measure.map oneArmObservationTripleLabel (obsLaw (P₀ z).1)) (lam₀ z)))
    let Q₁ := mixture w₁ (fun z ↦
      Measure.map (fun u : FiniteSample (Fin (d + 1) × Fin 3) ↦
        finiteSampleHistogram u.points)
        (finitePoissonSampleLaw
          (Measure.map oneArmObservationTripleLabel (obsLaw (P₁ z).1)) (lam₁ z)))
    letI (z : {z // G₀ z}) : IsProbabilityMeasure
        (Measure.map (fun u : FiniteSample (Fin (d + 1) × Fin 3) ↦
          finiteSampleHistogram u.points)
          (finitePoissonSampleLaw
            (Measure.map oneArmObservationTripleLabel (obsLaw (P₀ z).1))
            (lam₀ z))) :=
      Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
    letI (z : {z // G₁ z}) : IsProbabilityMeasure
        (Measure.map (fun u : FiniteSample (Fin (d + 1) × Fin 3) ↦
          finiteSampleHistogram u.points)
          (finitePoissonSampleLaw
            (Measure.map oneArmObservationTripleLabel (obsLaw (P₁ z).1))
            (lam₁ z))) :=
      Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
    letI : IsProbabilityMeasure Q₀ := mixture_isProbabilityMeasure w₀ hwSum₀ _
    letI : IsProbabilityMeasure Q₁ := mixture_isProbabilityMeasure w₁ hwSum₁ _
    rw [← tvDist_map_curryOneArmTripleCounts_eq Q₀ Q₁]
    rw [map_finiteMixture _ _ _ (measurable_of_countable _),
      map_finiteMixture _ _ _ (measurable_of_countable _)]
    simp_rw [hcomponent₀, hcomponent₁]
    simpa only [Q₀, Q₁, w₀, w₁,
      oneArmFiniteConditionedMixture] using hcondTV
  have hgap_le_one : oneArmShiftedJordanGap κ ≤ 1 := by
    unfold oneArmShiftedJordanGap
    have hden : 2 ≤ (1 + κ) * (2 + κ) * (3 + κ) := by
      calc
        (2 : ℝ) ≤ 1 * 2 * 3 := by norm_num
        _ ≤ (1 + κ) * (2 + κ) * (3 + κ) := by
          gcongr <;> linarith
    have hκ2 : κ ^ 2 ≤ 1 := pow_le_one₀ hκ.le hκ1
    have hdenpos : 0 < (1 + κ) * (2 + κ) * (3 + κ) := by positivity
    rw [div_div, div_le_iff₀ (mul_pos hdenpos (by norm_num : (0 : ℝ) < 10))]
    calc
      2 * κ ^ 2 ≤ 2 :=
        by simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hκ2 (show (0 : ℝ) ≤ 2 by norm_num)
      _ ≤ (1 + κ) * (2 + κ) * (3 + κ) := hden
      _ ≤ 1 * ((1 + κ) * (2 + κ) * (3 + κ) * 10) := by
        rw [one_mul]
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ 10 by norm_num)
            hdenpos.le
  have hΔle : Δ ≤ 1 := by
    have hactive : (d : ℝ) * scale * pole ≤ 1 := by
      simpa [D, scale, pole, mul_assoc] using hcap
    dsimp [Δ, oneArmCalibratedSeparation]
    have h := mul_le_mul_of_nonneg_left hgap_le_one
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg d) hscale) hpole.le)
    exact h.trans (by simpa only [mul_one] using hactive)
  have hδhalf : δ ≤ 1 / 2 := by
    dsimp [δ]
    linarith
  have htheta_bound (nu : PMF (Option (Fin (2 * D + 4)))) :
      |(d : ℝ) * ∫ u, oneArmProductFunctionalAtom scale pole x u ∂nu.toMeasure| ≤
        (d : ℝ) * scale := by
    have hf (u : Option (Fin (2 * D + 4))) :
        oneArmProductFunctionalAtom scale pole x u ∈ Set.Icc (0 : ℝ) scale := by
      simpa only [pole, x] using
        oneArmShifted_functionalAtom_mem_Icc hκ hκ1 hD hscale u
    have hsum : ∑ u, (nu u).toReal = 1 := by
      simpa only [tsum_fintype] using tsum_pmf_toReal_eq_one nu
    rw [PMF.integral_eq_sum]
    simp only [smul_eq_mul]
    have hint0 : 0 ≤ ∑ u, (nu u).toReal *
        oneArmProductFunctionalAtom scale pole x u := by
      exact Finset.sum_nonneg fun u _ ↦
        mul_nonneg ENNReal.toReal_nonneg (hf u).1
    have hintle : ∑ u, (nu u).toReal *
        oneArmProductFunctionalAtom scale pole x u ≤ scale := by
      calc
        _ ≤ ∑ u, (nu u).toReal * scale := by
          gcongr with u
          exact (hf u).2
        _ = scale := by rw [← Finset.sum_mul, hsum, one_mul]
    rw [abs_of_nonneg (mul_nonneg (Nat.cast_nonneg d) hint0)]
    exact mul_le_mul_of_nonneg_left hintle (Nat.cast_nonneg d)
  have htailSide₀ : ∀ z, theta₀ ^ 2 *
      (poissonMeasure (lam₀ z)).real {k | k < n} ≤ Δ ^ 2 / 32 := by
    intro z
    have hS : (1 / 2 : ℝ) ≤ anchor + ∑ i, p (z.1 i) := by
      have hz := z.2.2.1
      have hlower := (abs_le.mp hz).1
      linarith
    have hmeanR : (2 * (n : ℕ) : ℝ) ≤
        sampleScale * (anchor + ∑ i, p (z.1 i)) := by
      calc
        (2 * (n : ℕ) : ℝ) = (4 * (n : ℝ)) * (1 / 2) := by norm_num; ring
        _ ≤ (4 * (n : ℝ)) * (anchor + ∑ i, p (z.1 i)) := by
          exact mul_le_mul_of_nonneg_left hS (by positivity)
        _ = _ := by rfl
    have hmeanNN : (2 : ℝ≥0) * (n : ℝ≥0) ≤ lam₀ z := by
      apply NNReal.coe_le_coe.mp
      rw [show lam₀ z =
        (sampleScale * (anchor + ∑ i, p (z.1 i))).toNNReal by rfl,
        Real.coe_toNNReal]
      · exact hmeanR
      · positivity
    have hpois := poisson_lower_tail_le_inv_sq (lam := lam₀ z) hn hmeanNN
    have hpoisR := ENNReal.toReal_mono
      (by norm_num : ENNReal.ofReal ((n : ℝ)⁻¹ ^ 2) ≠ ⊤) hpois
    have hprob : (poissonMeasure (lam₀ z)).real {k | k < n} ≤
        (n : ℝ)⁻¹ ^ 2 := by
      change (poissonMeasure (lam₀ z) {k | k < n}).toReal ≤ _
      simpa using hpoisR
    have ht := htheta_bound nu₀
    have hsq : theta₀ ^ 2 ≤ ((d : ℝ) * scale) ^ 2 := by
      dsimp [theta₀]
      rw [← sq_abs]
      exact (sq_le_sq₀ (abs_nonneg _)
        (mul_nonneg (Nat.cast_nonneg d) hscale)).2 ht
    calc
      theta₀ ^ 2 * (poissonMeasure (lam₀ z)).real {k | k < n} ≤
          ((d : ℝ) * scale) ^ 2 * ((n : ℝ)⁻¹ ^ 2) := by
        exact mul_le_mul hsq hprob (by positivity)
          (sq_nonneg ((d : ℝ) * scale))
      _ ≤ Δ ^ 2 / 32 := by simpa only [D, scale, Δ] using htail
  have htailSide₁ : ∀ z, theta₁ ^ 2 *
      (poissonMeasure (lam₁ z)).real {k | k < n} ≤ Δ ^ 2 / 32 := by
    intro z
    have hS : (1 / 2 : ℝ) ≤ anchor + ∑ i, p (z.1 i) := by
      have hz := z.2.2.1
      have hlower := (abs_le.mp hz).1
      linarith
    have hmeanR : (2 * (n : ℕ) : ℝ) ≤
        sampleScale * (anchor + ∑ i, p (z.1 i)) := by
      calc
        (2 * (n : ℕ) : ℝ) = (4 * (n : ℝ)) * (1 / 2) := by norm_num; ring
        _ ≤ (4 * (n : ℝ)) * (anchor + ∑ i, p (z.1 i)) := by
          exact mul_le_mul_of_nonneg_left hS (by positivity)
        _ = _ := by rfl
    have hmeanNN : (2 : ℝ≥0) * (n : ℝ≥0) ≤ lam₁ z := by
      apply NNReal.coe_le_coe.mp
      rw [show lam₁ z =
        (sampleScale * (anchor + ∑ i, p (z.1 i))).toNNReal by rfl,
        Real.coe_toNNReal]
      · exact hmeanR
      · positivity
    have hpois := poisson_lower_tail_le_inv_sq (lam := lam₁ z) hn hmeanNN
    have hpoisR := ENNReal.toReal_mono
      (by norm_num : ENNReal.ofReal ((n : ℝ)⁻¹ ^ 2) ≠ ⊤) hpois
    have hprob : (poissonMeasure (lam₁ z)).real {k | k < n} ≤
        (n : ℝ)⁻¹ ^ 2 := by
      change (poissonMeasure (lam₁ z) {k | k < n}).toReal ≤ _
      simpa using hpoisR
    have ht := htheta_bound nu₁
    have hsq : theta₁ ^ 2 ≤ ((d : ℝ) * scale) ^ 2 := by
      dsimp [theta₁]
      rw [← sq_abs]
      exact (sq_le_sq₀ (abs_nonneg _)
        (mul_nonneg (Nat.cast_nonneg d) hscale)).2 ht
    calc
      theta₁ ^ 2 * (poissonMeasure (lam₁ z)).real {k | k < n} ≤
          ((d : ℝ) * scale) ^ 2 * ((n : ℝ)⁻¹ ^ 2) := by
        exact mul_le_mul hsq hprob (by positivity)
          (sq_nonneg ((d : ℝ) * scale))
      _ ≤ Δ ^ 2 / 32 := by simpa only [D, scale, Δ] using htail
  have hrawRisk := oneArmMinimaxRisk_lower_of_conditioned_count_tv
    (radius := Δ / 8) (s := Δ / 2) (c := 1 / 4) (tail := Δ ^ 2 / 32)
    P₀ P₁ w₀ w₁ hwSum₀ hwSum₁ lam₀ lam₁ htarget₀ htarget₁
    (by positivity) (by positivity) (by convert hsep using 1 <;> ring)
    htv htailSide₀ htailSide₁
  have hD2 : Δ ^ 2 / 64 ≤ oneArmMinimaxRisk n (d + 1) epsilon := by
    nlinarith
  have hcell := oneArmCalibratedSignal_lower hn0 hD hκ hκ1
  have hsignal : (d : ℝ) *
      (κ ^ 7 / (153600000000000 * (n : ℝ) * (D : ℝ))) ≤ Δ := by
    dsimp [Δ, oneArmCalibratedSeparation]
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left hcell (Nat.cast_nonneg d)
  have hsquare : ((((d : ℝ) * κ ^ 7 /
      (153600000000000 * (n : ℝ) * (D : ℝ))) ^ 2) / 64) ≤
      Δ ^ 2 / 64 := by
    have hleft0 : 0 ≤ (d : ℝ) * κ ^ 7 /
        (153600000000000 * (n : ℝ) * (D : ℝ)) := by positivity
    have hs : (d : ℝ) * κ ^ 7 /
        (153600000000000 * (n : ℝ) * (D : ℝ)) ≤ Δ := by
      simpa [mul_div_assoc] using hsignal
    nlinarith
  apply oneArmHighDimensional_rate_of_calibrated_signal hn0 hlog hD hDlog
  exact hsquare.trans hD2

set_option maxHeartbeats 2000000 in
-- The asymptotic wrapper normalizes several large explicit polynomial constants.
/-- The shifted-prior construction discharges the cited one-arm minimax gate
for every fixed interior overlap constant. -/
theorem zengOneArmMinimaxLower (epsilon : ℝ) :
    ZengOneArmMinimaxLower epsilon := by
  intro he
  rcases he with ⟨he0, hehalf⟩
  let κ := oneArmOverlapShiftRatio epsilon
  have hκ : 0 < κ := oneArmOverlapShiftRatio_pos he0 hehalf
  have hκ1 : κ ≤ 1 := oneArmOverlapShiftRatio_le_one epsilon
  have hoverlap : epsilon * (1 + κ) ≤ 1 - epsilon :=
    epsilon_mul_one_add_overlapShiftRatio_le he0 hehalf
  let A : ℝ := κ ^ 14 /
    (4 * (25600 * (153600000000000 : ℝ) ^ 2))
  let Kc : ℝ := (10 : ℝ) ^ 50 / κ ^ 14
  have hA : 0 < A := by dsimp [A]; positivity
  have hK : 0 < Kc := by dsimp [Kc]; positivity
  have hevent := (Real.isLittleO_pow_log_id_atTop (n := 4)).bound
    (show 0 < κ ^ 14 / (10 : ℝ) ^ 50 by positivity)
  have heventNat : ∀ᶠ n : ℕ in Filter.atTop,
      |Real.log (n : ℝ) ^ 4| ≤
        (κ ^ 14 / (10 : ℝ) ^ 50) * |(n : ℝ)| :=
    tendsto_natCast_atTop_atTop.eventually hevent
  have hall : ∀ᶠ n : ℕ in Filter.atTop,
      400 ≤ n ∧ |Real.log (n : ℝ) ^ 4| ≤
        (κ ^ 14 / (10 : ℝ) ^ 50) * |(n : ℝ)| :=
    (Filter.eventually_ge_atTop 400).and heventNat
  rw [Filter.eventually_atTop] at hall
  obtain ⟨N₀, hN₀⟩ := hall
  have hhigh : ∀ n q : ℕ, 0 < q → N₀ ≤ n →
      Kc * Real.log (n : ℝ) ^ 4 ≤ (q : ℝ) →
      (q : ℝ) ≤ n * Real.log n →
      A * ((q : ℝ) ^ 2 /
          ((n : ℝ) ^ 2 * Real.log (n : ℝ) ^ 2)) ≤
        oneArmMinimaxRisk n q epsilon := by
    intro n q hq hn hdim hcapq
    obtain ⟨hn400, hlogpow⟩ := hN₀ n hn
    have hn0 : 0 < n := by omega
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
    have hlog : 0 < Real.log (n : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    have hlogpow' : Real.log (n : ℝ) ^ 4 ≤
        (κ ^ 14 / (10 : ℝ) ^ 50) * (n : ℝ) := by
      simpa [abs_of_nonneg (pow_nonneg hlog.le 4), abs_of_pos hnR] using hlogpow
    have hqlarge : (2 : ℝ) ≤ q := by
      have hKone : 1 ≤ Kc := by
        dsimp [Kc]
        have hpow : κ ^ 14 ≤ 1 := pow_le_one₀ hκ.le hκ1
        rw [le_div_iff₀ (by positivity : 0 < κ ^ 14)]
        nlinarith [show (2 : ℝ) ≤ (10 : ℝ) ^ 50 by norm_num]
      have hlogone : 1 ≤ Real.log (n : ℝ) := by
        have hn3R : (3 : ℝ) ≤ n := by
          exact_mod_cast (show 3 ≤ n by omega)
        have hlog3le := Real.log_le_log (by norm_num : (0 : ℝ) < 3) hn3R
        nlinarith [Real.log_three_gt_d9]
      have : 1 ≤ Kc * Real.log (n : ℝ) ^ 4 := by
        have hlogpowone : 1 ≤ Real.log (n : ℝ) ^ 4 := by
          nlinarith [sq_nonneg (Real.log (n : ℝ) ^ 2 - 1)]
        calc
          (1 : ℝ) = 1 * 1 := by ring
          _ ≤ Kc * Real.log (n : ℝ) ^ 4 :=
            mul_le_mul hKone hlogpowone (by norm_num) hK.le
      have hqone : (1 : ℝ) < q := by
        have hlogstrict : 1 < Real.log (n : ℝ) ^ 4 := by
          have : 1 < Real.log (n : ℝ) := by
            have hn3R : (3 : ℝ) ≤ n := by
              exact_mod_cast (show 3 ≤ n by omega)
            have hlog3le := Real.log_le_log (by norm_num : (0 : ℝ) < 3) hn3R
            nlinarith [Real.log_three_gt_d9]
          nlinarith [sq_nonneg (Real.log (n : ℝ) ^ 2 - 1)]
        have hscaleK : Real.log (n : ℝ) ^ 4 ≤
            Kc * Real.log (n : ℝ) ^ 4 := by
          simpa only [one_mul] using
            mul_le_mul_of_nonneg_right hKone
              (pow_nonneg hlog.le 4)
        exact lt_of_lt_of_le (hlogstrict.trans_le hscaleK) hdim
      have hqoneNat : 1 < q := by exact_mod_cast hqone
      exact_mod_cast (show 2 ≤ q by omega)
    have hqlargeNat : 2 ≤ q := by exact_mod_cast hqlarge
    let m := q - 1
    have hm : 0 < m := by dsimp [m]; omega
    have hmq : (q : ℝ) / 2 ≤ m := by
      dsimp [m]
      rw [Nat.cast_sub (by omega : 1 ≤ q)]
      norm_num
      linarith
    let D := oneArmLogDegree n
    let scale : ℝ := (D : ℝ) / (128 * (n : ℝ))
    let pole := oneArmShiftedPoleScale κ D
    let gap := oneArmShiftedJordanGap κ
    have hD : 1 ≤ D := oneArmLogDegree_pos (by omega)
    have hDlog : (D : ℝ) ≤ 20 * Real.log n :=
      oneArmLogDegree_le_twenty_log (by omega)
    have hscale : 0 < scale := by dsimp [scale]; positivity
    have hpole : 0 < pole := oneArmShiftedPoleScale_pos hκ hD
    have hgap : κ ^ 2 / 120 ≤ gap := oneArmShiftedJordanGap_lower hκ hκ1
    have hpoleEq : pole = κ ^ 5 / (10000000000 * (D : ℝ) ^ 2) := by
      dsimp [pole, oneArmShiftedPoleScale, oneArmShiftedNodeScale]
      ring
    have hcap : (m : ℝ) * scale * pole ≤ 1 := by
      have hmqcap : (m : ℝ) ≤ n * Real.log n := by
        have hmle : (m : ℝ) ≤ q := by
          exact_mod_cast (Nat.sub_le q 1)
        exact hmle.trans hcapq
      rw [hpoleEq]
      dsimp [scale]
      have hDpos : (0 : ℝ) < D := by exact_mod_cast Nat.zero_lt_of_lt hD
      have hκpow : κ ^ 5 ≤ 1 := pow_le_one₀ hκ.le hκ1
      have hDlower := oneArmLogDegree_lower (n := n) (by omega)
      have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hlog2le : Real.log 2 ≤ 1 := Real.log_two_lt_d9.le.trans (by norm_num)
      have hlogD : 8 * Real.log (n : ℝ) ≤ (D : ℝ) := by
        calc
          8 * Real.log (n : ℝ) ≤ 8 * Real.log (n : ℝ) / Real.log 2 := by
            rw [le_div_iff₀ hlog2]
            nlinarith
          _ ≤ (D : ℝ) := by simpa only [D] using hDlower
      have hnum : (m : ℝ) * κ ^ 5 ≤ (n : ℝ) * Real.log n :=
        (mul_le_mul_of_nonneg_left hκpow (Nat.cast_nonneg m)).trans
          (by simpa only [mul_one] using hmqcap)
      rw [show (m : ℝ) * ((D : ℝ) / (128 * (n : ℝ))) *
          (κ ^ 5 / (10000000000 * (D : ℝ) ^ 2)) =
          ((m : ℝ) * κ ^ 5) /
            (128 * (n : ℝ) * 10000000000 * (D : ℝ)) by
        field_simp
        <;> ring]
      rw [div_le_one (by positivity :
        0 < 128 * (n : ℝ) * 10000000000 * (D : ℝ))]
      have hscaled := mul_le_mul_of_nonneg_left hlogD hnR.le
      exact hnum.trans (by nlinarith)
    have hpolegap : κ ^ 7 /
        (1200000000000 * (D : ℝ) ^ 2) ≤ pole * gap := by
      rw [hpoleEq]
      have hnonneg : 0 ≤ κ ^ 5 / (10000000000 * (D : ℝ) ^ 2) := by positivity
      calc
        _ = (κ ^ 5 / (10000000000 * (D : ℝ) ^ 2)) * (κ ^ 2 / 120) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hgap hnonneg
    have hbadReal : 2 * ((m : ℝ) * scale ^ 2 /
        (oneArmCalibratedSeparation n m D κ / 16) ^ 2) ≤ 1 / 32 := by
      have hmlarge : (10 : ℝ) ^ 50 / κ ^ 14 *
          Real.log (n : ℝ) ^ 4 / 2 ≤ m := by
        have := mul_le_mul_of_nonneg_left hdim (by norm_num : (0 : ℝ) ≤ 1 / 2)
        dsimp [Kc] at this
        have this' : (10 : ℝ) ^ 50 / κ ^ 14 *
            Real.log (n : ℝ) ^ 4 / 2 ≤ (q : ℝ) / 2 := by
          simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
        exact this'.trans hmq
      dsimp [oneArmCalibratedSeparation, scale]
      have hDpos : (0 : ℝ) < D := by exact_mod_cast Nat.zero_lt_of_lt hD
      have hmR : (0 : ℝ) < m := by exact_mod_cast hm
      have hpg0 : 0 < pole * gap :=
        mul_pos hpole (lt_of_lt_of_le (by positivity) hgap)
      field_simp
      have hD4 : (D : ℝ) ^ 4 ≤ 20 ^ 4 * Real.log (n : ℝ) ^ 4 := by
        simpa only [mul_pow] using
          pow_le_pow_left₀ (Nat.cast_nonneg D) hDlog 4
      have hmlarge' := hmlarge
      field_simp at hmlarge'
      have hpgsq := sq_le_sq₀ (by positivity : 0 ≤ κ ^ 7 /
        (1200000000000 * (D : ℝ) ^ 2)) hpg0.le |>.mpr hpolegap
      field_simp at hpgsq
      have hpglog : κ ^ 14 ≤
          1200000000000 ^ 2 * (20 ^ 4 * Real.log (n : ℝ) ^ 4) *
            pole ^ 2 * gap ^ 2 := by
        calc
          _ ≤ 1200000000000 ^ 2 * (D : ℝ) ^ 4 * pole ^ 2 * gap ^ 2 := hpgsq
          _ ≤ _ := by gcongr
      have hchain : (10 : ℝ) ^ 50 * Real.log (n : ℝ) ^ 4 ≤
          (2 * (m : ℝ)) *
            (1200000000000 ^ 2 * (20 ^ 4 * Real.log (n : ℝ) ^ 4) *
              pole ^ 2 * gap ^ 2) := by
        calc
          _ ≤ κ ^ 14 * 2 * (m : ℝ) := hmlarge'
          _ = (2 * (m : ℝ)) * κ ^ 14 := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hpglog (by positivity)
      have hlog4 : 0 < Real.log (n : ℝ) ^ 4 := pow_pos hlog 4
      have hcancel : (10 : ℝ) ^ 50 ≤
          (2 * (m : ℝ)) * (1200000000000 ^ 2 * 20 ^ 4 *
            pole ^ 2 * gap ^ 2) := by
        nlinarith [hchain]
      have hbudget : (2 * 16 ^ 2 * 32 : ℝ) ≤
          (m : ℝ) * pole ^ 2 * gap ^ 2 := by
        nlinarith
      have hdiv : (2 * 16 ^ 2 * 32 : ℝ) / (pole ^ 2 * gap ^ 2) ≤
          (m : ℝ) := by
        rw [div_le_iff₀ (mul_pos (sq_pos_of_pos hpole)
          (sq_pos_of_pos (lt_of_lt_of_le (by positivity) hgap)))]
        nlinarith [hbudget]
      nlinarith [hdiv]
    have hbadENN :
        ENNReal.ofReal ((m : ℝ) * scale ^ 2 /
            (oneArmCalibratedSeparation n m D κ / 16) ^ 2) +
          ENNReal.ofReal ((m : ℝ) * scale ^ 2 /
            (oneArmCalibratedSeparation n m D κ / 16) ^ 2) ≤
            ENNReal.ofReal (1 / 32 : ℝ) := by
      have hterm : 0 ≤ (m : ℝ) * scale ^ 2 /
          (oneArmCalibratedSeparation n m D κ / 16) ^ 2 := by positivity
      rw [← ENNReal.ofReal_add hterm] <;> try exact hterm
      apply ENNReal.ofReal_le_ofReal
      nlinarith
    have hraw : 2 * (m : ℝ) / (n : ℝ) ^ 4 ≤ 1 / 8 := by
      have hmcap : (m : ℝ) ≤ n * Real.log n := by
        have hmle : (m : ℝ) ≤ q := by
          exact_mod_cast (Nat.sub_le q 1)
        exact hmle.trans hcapq
      have hlogn := Real.log_le_sub_one_of_pos hnR
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
      have hm_n2 : (m : ℝ) ≤ (n : ℝ) ^ 2 := by
        calc
          (m : ℝ) ≤ (n : ℝ) * Real.log n := hmcap
          _ ≤ (n : ℝ) * (n : ℝ) := by
            gcongr
            linarith
          _ = (n : ℝ) ^ 2 := by ring
      have hn4R : (4 : ℝ) ≤ n := by exact_mod_cast (show 4 ≤ n by omega)
      have hnSq : (16 : ℝ) ≤ (n : ℝ) ^ 2 := by
        nlinarith [mul_nonneg (hnR.le) (sub_nonneg.mpr hn4R)]
      rw [div_le_iff₀ (pow_pos hnR 4)]
      calc
        2 * (m : ℝ) ≤ (1 / 8) * (16 * (m : ℝ)) := by
          have : 2 * (m : ℝ) = (1 / 8) * (16 * (m : ℝ)) := by ring
          exact this.le
        _ ≤ (1 / 8) * (16 * (n : ℝ) ^ 2) := by gcongr
        _ ≤ (1 / 8) * ((n : ℝ) ^ 2 * (n : ℝ) ^ 2) := by gcongr
        _ = 1 / 8 * (n : ℝ) ^ 4 := by ring
    have htail : ((m : ℝ) * scale) ^ 2 * (n : ℝ)⁻¹ ^ 2 ≤
        oneArmCalibratedSeparation n m D κ ^ 2 / 32 := by
      dsimp [oneArmCalibratedSeparation, scale]
      have hDpos : (0 : ℝ) < D := by exact_mod_cast Nat.zero_lt_of_lt hD
      have hmR : (0 : ℝ) < m := by exact_mod_cast hm
      have hpg0 : 0 < pole * gap := mul_pos hpole (lt_of_lt_of_le (by positivity) hgap)
      field_simp
      have hD4 : (D : ℝ) ^ 4 ≤ 20 ^ 4 * Real.log (n : ℝ) ^ 4 := by
        simpa only [mul_pow] using
          pow_le_pow_left₀ (Nat.cast_nonneg D) hDlog 4
      have hlogpow'' := hlogpow'
      field_simp at hlogpow''
      have hpgsq := sq_le_sq₀ (by positivity : 0 ≤ κ ^ 7 /
        (1200000000000 * (D : ℝ) ^ 2)) hpg0.le |>.mpr hpolegap
      field_simp at hpgsq
      have hpglog : κ ^ 14 ≤
          1200000000000 ^ 2 * (20 ^ 4 * Real.log (n : ℝ) ^ 4) *
            pole ^ 2 * gap ^ 2 := by
        calc
          _ ≤ 1200000000000 ^ 2 * (D : ℝ) ^ 4 * pole ^ 2 * gap ^ 2 := hpgsq
          _ ≤ _ := by gcongr
      have hchain : Real.log (n : ℝ) ^ 4 * (10 : ℝ) ^ 50 ≤
          (1200000000000 ^ 2 * (20 ^ 4 * Real.log (n : ℝ) ^ 4) *
            pole ^ 2 * gap ^ 2) * (n : ℝ) := by
        exact hlogpow''.trans
          (mul_le_mul_of_nonneg_right hpglog hnR.le)
      have hlog4 : 0 < Real.log (n : ℝ) ^ 4 := pow_pos hlog 4
      have hcancel : (10 : ℝ) ^ 50 ≤
          1200000000000 ^ 2 * 20 ^ 4 * pole ^ 2 * gap ^ 2 * (n : ℝ) := by
        nlinarith [hchain]
      have hbase : (32 : ℝ) ≤ (n : ℝ) * (pole ^ 2 * gap ^ 2) := by
        nlinarith
      have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
      have hbudget : (32 : ℝ) ≤ (n : ℝ) ^ 2 * pole ^ 2 * gap ^ 2 := by
        calc
          _ ≤ (n : ℝ) * (pole ^ 2 * gap ^ 2) := hbase
          _ ≤ (n : ℝ) * ((n : ℝ) * (pole ^ 2 * gap ^ 2)) := by
            simpa only [one_mul] using
              mul_le_mul_of_nonneg_right hn1R
                (mul_nonneg hnR.le (mul_nonneg (sq_nonneg pole) (sq_nonneg gap)))
          _ = _ := by ring
      nlinarith
    have hmLower := oneArmHighDimensional_shiftedPrior hn400 hm he0 hehalf
      hκ hκ1 hoverlap hcap hbadENN hraw htail
    have hrate0 : 0 ≤ (q : ℝ) ^ 2 /
        ((n : ℝ) ^ 2 * Real.log (n : ℝ) ^ 2) := by positivity
    have hcompare : A * ((q : ℝ) ^ 2 /
        ((n : ℝ) ^ 2 * Real.log (n : ℝ) ^ 2)) ≤
      (κ ^ 14 / (25600 * (153600000000000 : ℝ) ^ 2)) *
        ((m : ℝ) ^ 2 / ((n : ℝ) ^ 2 * Real.log n ^ 2)) := by
      dsimp [A]
      have hmSq : (q : ℝ) ^ 2 / 4 ≤ (m : ℝ) ^ 2 := by nlinarith
      field_simp
      nlinarith
    exact hcompare.trans (by
      simpa only [m, Nat.sub_add_cancel (by omega : 1 ≤ q)] using hmLower)
  exact (zengOneArmMinimaxLower_of_highDimensional hA hK
    (by norm_num : (0 : ℝ) < 1) (N₀ := N₀) (b := 1)
    (by simpa only [one_mul] using hhigh)) ⟨he0, hehalf⟩

end CausalSmith.Stat.DiscreteAteMinimaxLoggap
