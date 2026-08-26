import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.OneArmObservationCounts
import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.OneArmRelaxedAnchor

/-!
# Count rates for relaxed anchored configurations

Scaling the Poisson intensity by the unnormalized total mass cancels the
normalization and recovers the raw active-cell rates.
-/

namespace CausalSmith.Stat.DiscreteAteMinimaxLoggap

open MeasureTheory
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open scoped BigOperators NNReal

lemma oneArmRelaxedAnchored_active_treatedSuccess_rate
    {n m : ℕ} {epsilon anchor sampleScale : ℝ} (q pi mu : Fin m → ℝ)
    (he0 : 0 < epsilon) (hehalf : epsilon ≤ 1 / 2)
    (ha : 0 ≤ anchor) (hq : ∀ i, 0 ≤ q i)
    (hS : 0 < anchor + ∑ i, q i)
    (hpi : ∀ i, pi i ∈ Set.Icc epsilon (1 - epsilon))
    (hmu : ∀ i, mu i ∈ Set.Icc (0 : ℝ) 1)
    (hscale : 0 ≤ sampleScale) (i : Fin m) :
    (sampleScale * (anchor + ∑ j, q j)).toNNReal *
        (oneArmObservationTriplePartition (m + 1)).cellMass
          (obsLaw ((oneArmRelaxedAnchoredControlZero (n := n) q pi mu
            he0 hehalf ha hq hS hpi hmu).1)) (Fin.succ i, 0) =
      (sampleScale * q i * pi i * mu i).toNNReal := by
  let raw := oneArmRelaxedAnchoredMass anchor q
  have hraw : ∀ r, 0 ≤ raw r := oneArmRelaxedAnchoredMass_nonneg q ha hq
  have hrawIcc : ∀ r, oneArmNormalizedMass raw r ∈ Set.Icc (0 : ℝ) 1 :=
    fun r => ⟨oneArmNormalizedMass_nonneg raw hraw
        (by simpa [raw, oneArmRelaxedAnchoredMass_sum] using hS) r,
      oneArmNormalizedMass_le_one raw hraw
        (by simpa [raw, oneArmRelaxedAnchoredMass_sum] using hS) r⟩
  have hpiIcc : ∀ r, oneArmAnchoredPropensity epsilon pi r ∈
      Set.Icc (0 : ℝ) 1 := by
    intro r
    refine Fin.cases ?_ (fun j => ?_) r
    · simpa [oneArmAnchoredPropensity] using
        (show epsilon ∈ Set.Icc (0 : ℝ) 1 from ⟨he0.le, by linarith⟩)
    · simpa [oneArmAnchoredPropensity] using
        (show pi j ∈ Set.Icc (0 : ℝ) 1 from
          ⟨he0.le.trans (hpi j).1, by linarith [(hpi j).2, he0]⟩)
  have hmuIcc : ∀ r, oneArmAnchoredOutcomeMean mu r ∈ Set.Icc (0 : ℝ) 1 := by
    intro r
    refine Fin.cases ?_ (fun j => ?_) r
    · simp [oneArmAnchoredOutcomeMean]
    · simpa [oneArmAnchoredOutcomeMean] using hmu j
  simp only [oneArmRelaxedAnchoredControlZero, oneArmNormalizedControlZero,
    oneArmConfigurationControlZero]
  apply NNReal.eq
  rw [NNReal.coe_mul, Real.coe_toNNReal _
    (mul_nonneg hscale hS.le)]
  rw [oneArmObservationTriplePartition_cellMass_treatedSuccess
    (oneArmNormalizedMass raw) (oneArmAnchoredPropensity epsilon pi)
    (oneArmAnchoredOutcomeMean mu) hrawIcc hpiIcc hmuIcc
    (oneArmNormalizedMass_sum raw
      (by simpa [raw, oneArmRelaxedAnchoredMass_sum] using hS))]
  rw [Real.coe_toNNReal _ (mul_nonneg
    (mul_nonneg (mul_nonneg hscale (hq i))
      (he0.le.trans (hpi i).1)) (hmu i).1)]
  simp only [oneArmNormalizedMass]
  rw [show (∑ x, raw x) = anchor + ∑ j, q j by
    simpa [raw] using oneArmRelaxedAnchoredMass_sum anchor q]
  simp [raw, oneArmRelaxedAnchoredMass, oneArmAnchoredPropensity,
    oneArmAnchoredOutcomeMean]
  field_simp [ne_of_gt hS]

lemma oneArmRelaxedAnchored_active_rates
    {n m : ℕ} {epsilon anchor sampleScale : ℝ} (q pi mu : Fin m → ℝ)
    (he0 : 0 < epsilon) (hehalf : epsilon ≤ 1 / 2)
    (ha : 0 ≤ anchor) (hq : ∀ i, 0 ≤ q i)
    (hS : 0 < anchor + ∑ i, q i)
    (hpi : ∀ i, pi i ∈ Set.Icc epsilon (1 - epsilon))
    (hmu : ∀ i, mu i ∈ Set.Icc (0 : ℝ) 1)
    (hscale : 0 ≤ sampleScale) (i : Fin m) (j : Fin 3) :
    (sampleScale * (anchor + ∑ k, q k)).toNNReal *
        (oneArmObservationTriplePartition (m + 1)).cellMass
          (obsLaw ((oneArmRelaxedAnchoredControlZero (n := n) q pi mu
            he0 hehalf ha hq hS hpi hmu).1)) (Fin.succ i, j) =
      ![(sampleScale * q i * pi i * mu i).toNNReal,
        (sampleScale * q i * pi i * (1 - mu i)).toNNReal,
        (sampleScale * q i * (1 - pi i)).toNNReal] j := by
  fin_cases j
  · exact oneArmRelaxedAnchored_active_treatedSuccess_rate q pi mu
      he0 hehalf ha hq hS hpi hmu hscale i
  all_goals
    let raw := oneArmRelaxedAnchoredMass anchor q
    have hraw : ∀ r, 0 ≤ raw r := oneArmRelaxedAnchoredMass_nonneg q ha hq
    have hrawIcc : ∀ r, oneArmNormalizedMass raw r ∈ Set.Icc (0 : ℝ) 1 :=
      fun r => ⟨oneArmNormalizedMass_nonneg raw hraw
          (by simpa [raw, oneArmRelaxedAnchoredMass_sum] using hS) r,
        oneArmNormalizedMass_le_one raw hraw
          (by simpa [raw, oneArmRelaxedAnchoredMass_sum] using hS) r⟩
    have hpiIcc : ∀ r, oneArmAnchoredPropensity epsilon pi r ∈
        Set.Icc (0 : ℝ) 1 := by
      intro r
      refine Fin.cases ?_ (fun k => ?_) r
      · simpa [oneArmAnchoredPropensity] using
          (show epsilon ∈ Set.Icc (0 : ℝ) 1 from ⟨he0.le, by linarith⟩)
      · simpa [oneArmAnchoredPropensity] using
          (show pi k ∈ Set.Icc (0 : ℝ) 1 from
            ⟨he0.le.trans (hpi k).1, by linarith [(hpi k).2, he0]⟩)
    have hmuIcc : ∀ r, oneArmAnchoredOutcomeMean mu r ∈ Set.Icc (0 : ℝ) 1 := by
      intro r
      refine Fin.cases ?_ (fun k => ?_) r
      · simp [oneArmAnchoredOutcomeMean]
      · simpa [oneArmAnchoredOutcomeMean] using hmu k
  · change (sampleScale * (anchor + ∑ k, q k)).toNNReal *
        (oneArmObservationTriplePartition (m + 1)).cellMass
          (obsLaw ((oneArmRelaxedAnchoredControlZero (n := n) q pi mu
            he0 hehalf ha hq hS hpi hmu).1)) (Fin.succ i, 1) =
      (sampleScale * q i * pi i * (1 - mu i)).toNNReal
    apply NNReal.eq
    rw [NNReal.coe_mul, Real.coe_toNNReal _ (mul_nonneg hscale hS.le)]
    have hcell :
        ((oneArmObservationTriplePartition (m + 1)).cellMass
          (obsLaw ((oneArmRelaxedAnchoredControlZero (n := n) q pi mu
            he0 hehalf ha hq hS hpi hmu).1)) (Fin.succ i, 1) : ℝ) =
          oneArmNormalizedMass raw (Fin.succ i) *
            oneArmAnchoredPropensity epsilon pi (Fin.succ i) *
              (1 - oneArmAnchoredOutcomeMean mu (Fin.succ i)) := by
      simpa only [oneArmRelaxedAnchoredControlZero, oneArmNormalizedControlZero,
        oneArmConfigurationControlZero, raw] using
        oneArmObservationTriplePartition_cellMass_treatedFailure
          (oneArmNormalizedMass raw) (oneArmAnchoredPropensity epsilon pi)
          (oneArmAnchoredOutcomeMean mu) hrawIcc hpiIcc hmuIcc
          (oneArmNormalizedMass_sum raw
            (by simpa [raw, oneArmRelaxedAnchoredMass_sum] using hS)) (Fin.succ i)
    rw [hcell]
    rw [Real.coe_toNNReal _ (mul_nonneg
      (mul_nonneg (mul_nonneg hscale (hq i))
        (he0.le.trans (hpi i).1)) (sub_nonneg.mpr (hmu i).2))]
    simp only [oneArmNormalizedMass]
    rw [show (∑ x, raw x) = anchor + ∑ k, q k by
      simpa [raw] using oneArmRelaxedAnchoredMass_sum anchor q]
    simp [raw, oneArmRelaxedAnchoredMass, oneArmAnchoredPropensity,
      oneArmAnchoredOutcomeMean]
    field_simp [ne_of_gt hS]
  · change (sampleScale * (anchor + ∑ k, q k)).toNNReal *
        (oneArmObservationTriplePartition (m + 1)).cellMass
          (obsLaw ((oneArmRelaxedAnchoredControlZero (n := n) q pi mu
            he0 hehalf ha hq hS hpi hmu).1)) (Fin.succ i, 2) =
      (sampleScale * q i * (1 - pi i)).toNNReal
    apply NNReal.eq
    rw [NNReal.coe_mul, Real.coe_toNNReal _ (mul_nonneg hscale hS.le)]
    have hcell :
        ((oneArmObservationTriplePartition (m + 1)).cellMass
          (obsLaw ((oneArmRelaxedAnchoredControlZero (n := n) q pi mu
            he0 hehalf ha hq hS hpi hmu).1)) (Fin.succ i, 2) : ℝ) =
          oneArmNormalizedMass raw (Fin.succ i) *
            (1 - oneArmAnchoredPropensity epsilon pi (Fin.succ i)) := by
      simpa only [oneArmRelaxedAnchoredControlZero, oneArmNormalizedControlZero,
        oneArmConfigurationControlZero, raw] using
        oneArmObservationTriplePartition_cellMass_control
          (oneArmNormalizedMass raw) (oneArmAnchoredPropensity epsilon pi)
          (oneArmAnchoredOutcomeMean mu) hrawIcc hpiIcc hmuIcc
          (oneArmNormalizedMass_sum raw
            (by simpa [raw, oneArmRelaxedAnchoredMass_sum] using hS)) (Fin.succ i)
    rw [hcell]
    rw [Real.coe_toNNReal _ (mul_nonneg
      (mul_nonneg hscale (hq i))
      (sub_nonneg.mpr (by linarith [(hpi i).2, he0])))]
    simp only [oneArmNormalizedMass]
    rw [show (∑ x, raw x) = anchor + ∑ k, q k by
      simpa [raw] using oneArmRelaxedAnchoredMass_sum anchor q]
    simp [raw, oneArmRelaxedAnchoredMass, oneArmAnchoredPropensity]
    field_simp [ne_of_gt hS]

lemma oneArmRelaxedAnchored_anchor_rates
    {n m : ℕ} {epsilon anchor sampleScale : ℝ} (q pi mu : Fin m → ℝ)
    (he0 : 0 < epsilon) (hehalf : epsilon ≤ 1 / 2)
    (ha : 0 ≤ anchor) (hq : ∀ i, 0 ≤ q i)
    (hS : 0 < anchor + ∑ i, q i)
    (hpi : ∀ i, pi i ∈ Set.Icc epsilon (1 - epsilon))
    (hmu : ∀ i, mu i ∈ Set.Icc (0 : ℝ) 1)
    (hscale : 0 ≤ sampleScale) (j : Fin 3) :
    (sampleScale * (anchor + ∑ k, q k)).toNNReal *
        (oneArmObservationTriplePartition (m + 1)).cellMass
          (obsLaw ((oneArmRelaxedAnchoredControlZero (n := n) q pi mu
            he0 hehalf ha hq hS hpi hmu).1)) (0, j) =
      ![0, (sampleScale * anchor * epsilon).toNNReal,
        (sampleScale * anchor * (1 - epsilon)).toNNReal] j := by
  let raw := oneArmRelaxedAnchoredMass anchor q
  have hraw : ∀ r, 0 ≤ raw r := oneArmRelaxedAnchoredMass_nonneg q ha hq
  have hrawIcc : ∀ r, oneArmNormalizedMass raw r ∈ Set.Icc (0 : ℝ) 1 :=
    fun r => ⟨oneArmNormalizedMass_nonneg raw hraw
        (by simpa [raw, oneArmRelaxedAnchoredMass_sum] using hS) r,
      oneArmNormalizedMass_le_one raw hraw
        (by simpa [raw, oneArmRelaxedAnchoredMass_sum] using hS) r⟩
  have hpiIcc : ∀ r, oneArmAnchoredPropensity epsilon pi r ∈
      Set.Icc (0 : ℝ) 1 := by
    intro r
    refine Fin.cases ?_ (fun k => ?_) r
    · simpa [oneArmAnchoredPropensity] using
        (show epsilon ∈ Set.Icc (0 : ℝ) 1 from ⟨he0.le, by linarith⟩)
    · simpa [oneArmAnchoredPropensity] using
        (show pi k ∈ Set.Icc (0 : ℝ) 1 from
          ⟨he0.le.trans (hpi k).1, by linarith [(hpi k).2, he0]⟩)
  have hmuIcc : ∀ r, oneArmAnchoredOutcomeMean mu r ∈ Set.Icc (0 : ℝ) 1 := by
    intro r
    refine Fin.cases ?_ (fun k => ?_) r
    · simp [oneArmAnchoredOutcomeMean]
    · simpa [oneArmAnchoredOutcomeMean] using hmu k
  fin_cases j
  · change (sampleScale * (anchor + ∑ k, q k)).toNNReal *
        (oneArmObservationTriplePartition (m + 1)).cellMass
          (obsLaw ((oneArmRelaxedAnchoredControlZero (n := n) q pi mu
            he0 hehalf ha hq hS hpi hmu).1)) (0, 0) = 0
    have hcell :
        ((oneArmObservationTriplePartition (m + 1)).cellMass
          (obsLaw ((oneArmRelaxedAnchoredControlZero (n := n) q pi mu
            he0 hehalf ha hq hS hpi hmu).1)) (0, 0) : ℝ) =
          oneArmNormalizedMass raw 0 *
            oneArmAnchoredPropensity epsilon pi 0 *
              oneArmAnchoredOutcomeMean mu 0 := by
      simpa only [oneArmRelaxedAnchoredControlZero, oneArmNormalizedControlZero,
        oneArmConfigurationControlZero, raw] using
        oneArmObservationTriplePartition_cellMass_treatedSuccess
          (oneArmNormalizedMass raw) (oneArmAnchoredPropensity epsilon pi)
          (oneArmAnchoredOutcomeMean mu) hrawIcc hpiIcc hmuIcc
          (oneArmNormalizedMass_sum raw
            (by simpa [raw, oneArmRelaxedAnchoredMass_sum] using hS)) 0
    apply NNReal.eq
    rw [NNReal.coe_mul, Real.coe_toNNReal _ (mul_nonneg hscale hS.le), hcell]
    simp [oneArmAnchoredOutcomeMean]
  · change (sampleScale * (anchor + ∑ k, q k)).toNNReal *
        (oneArmObservationTriplePartition (m + 1)).cellMass
          (obsLaw ((oneArmRelaxedAnchoredControlZero (n := n) q pi mu
            he0 hehalf ha hq hS hpi hmu).1)) (0, 1) =
      (sampleScale * anchor * epsilon).toNNReal
    have hcell :
        ((oneArmObservationTriplePartition (m + 1)).cellMass
          (obsLaw ((oneArmRelaxedAnchoredControlZero (n := n) q pi mu
            he0 hehalf ha hq hS hpi hmu).1)) (0, 1) : ℝ) =
          oneArmNormalizedMass raw 0 *
            oneArmAnchoredPropensity epsilon pi 0 *
              (1 - oneArmAnchoredOutcomeMean mu 0) := by
      simpa only [oneArmRelaxedAnchoredControlZero, oneArmNormalizedControlZero,
        oneArmConfigurationControlZero, raw] using
        oneArmObservationTriplePartition_cellMass_treatedFailure
          (oneArmNormalizedMass raw) (oneArmAnchoredPropensity epsilon pi)
          (oneArmAnchoredOutcomeMean mu) hrawIcc hpiIcc hmuIcc
          (oneArmNormalizedMass_sum raw
            (by simpa [raw, oneArmRelaxedAnchoredMass_sum] using hS)) 0
    apply NNReal.eq
    rw [NNReal.coe_mul, Real.coe_toNNReal _ (mul_nonneg hscale hS.le), hcell]
    rw [Real.coe_toNNReal _ (mul_nonneg
      (mul_nonneg hscale ha) he0.le)]
    simp only [oneArmNormalizedMass]
    rw [show (∑ x, raw x) = anchor + ∑ k, q k by
      simpa [raw] using oneArmRelaxedAnchoredMass_sum anchor q]
    simp [raw, oneArmRelaxedAnchoredMass, oneArmAnchoredPropensity,
      oneArmAnchoredOutcomeMean]
    field_simp [ne_of_gt hS]
  · change (sampleScale * (anchor + ∑ k, q k)).toNNReal *
        (oneArmObservationTriplePartition (m + 1)).cellMass
          (obsLaw ((oneArmRelaxedAnchoredControlZero (n := n) q pi mu
            he0 hehalf ha hq hS hpi hmu).1)) (0, 2) =
      (sampleScale * anchor * (1 - epsilon)).toNNReal
    have hcell :
        ((oneArmObservationTriplePartition (m + 1)).cellMass
          (obsLaw ((oneArmRelaxedAnchoredControlZero (n := n) q pi mu
            he0 hehalf ha hq hS hpi hmu).1)) (0, 2) : ℝ) =
          oneArmNormalizedMass raw 0 *
            (1 - oneArmAnchoredPropensity epsilon pi 0) := by
      simpa only [oneArmRelaxedAnchoredControlZero, oneArmNormalizedControlZero,
        oneArmConfigurationControlZero, raw] using
        oneArmObservationTriplePartition_cellMass_control
          (oneArmNormalizedMass raw) (oneArmAnchoredPropensity epsilon pi)
          (oneArmAnchoredOutcomeMean mu) hrawIcc hpiIcc hmuIcc
          (oneArmNormalizedMass_sum raw
            (by simpa [raw, oneArmRelaxedAnchoredMass_sum] using hS)) 0
    apply NNReal.eq
    rw [NNReal.coe_mul, Real.coe_toNNReal _ (mul_nonneg hscale hS.le), hcell]
    rw [Real.coe_toNNReal _ (mul_nonneg (mul_nonneg hscale ha)
      (sub_nonneg.mpr (by linarith [hehalf])))]
    simp only [oneArmNormalizedMass]
    rw [show (∑ x, raw x) = anchor + ∑ k, q k by
      simpa [raw] using oneArmRelaxedAnchoredMass_sum anchor q]
    simp [raw, oneArmRelaxedAnchoredMass, oneArmAnchoredPropensity]
    field_simp [ne_of_gt hS]

end CausalSmith.Stat.DiscreteAteMinimaxLoggap
