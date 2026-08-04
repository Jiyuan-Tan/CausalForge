/-
# Affine inversion length and risk

Transported-LATE specializations of Causalean's model-free affine-inversion
geometry and expected-volume frontier bounds.
-/

import CausalSmith.Stat.STAT_TransportedLateStrengthFrontier_Research.Helpers.ScoreInversion
import CausalSmith.Stat.STAT_TransportedLateStrengthFrontier_Research.Helpers.CellEstimators
import Causalean.Stat.Inference.AffineInversion

namespace CausalSmith.Stat.TransportedLateStrengthFrontier

open MeasureTheory

/-- The model-free confidence set obtained by inverting one affine inequality. -/
noncomputable abbrev affineInversionSet (A B r : ℝ) : Set ℝ :=
  Causalean.Stat.affineInversionSet parameterSpace A B r

/-- Score inversion is an instance of model-free affine inversion. -/
lemma inversionHandle_eq_affineInversionSet
    {𝒳 : Type*} [MeasurableSpace 𝒳]
    (weight e : 𝒳 → ℝ) (n : ℕ) (L : ℝ) (sample : SourceSample 𝒳 n) :
    inversionHandle weight e n L sample =
      affineInversionSet (scoreOutcomeMean weight e n sample)
        (scoreReceiptMean weight e n sample)
        (L * Real.sqrt (empiricalKish weight n sample / n)) := by
  rfl

/-- On the nondegenerate target-sample branch, regular-cell inversion is
model-free affine inversion. -/
lemma regularCellInversion_eq_affineInversionSet
    {𝒳 : Type*} [MeasurableSpace 𝒳]
    (q e : 𝒳 → ℝ) {n N : ℕ} (L : ℝ)
    (source : SourceSample 𝒳 n) (target : TargetSample 𝒳 N)
    (hN : 2 ≤ N) :
    regularCellInversion q e L source target =
      affineInversionSet
        (crossAverage q source target
          (fun o => oracleInstrumentScore e o * o.2.2.2))
        (crossAverage q source target
          (fun o => oracleInstrumentScore e o * boolReal o.2.2.1))
        (L * Real.sqrt ((1 + collisionScale q target) / n)) := by
  simp [regularCellInversion, affineInversionSet,
    Causalean.Stat.affineInversionSet, Nat.not_lt.mpr hN]

/-- On the degenerate target-sample branch, regular-cell inversion returns the
whole parameter space. -/
lemma regularCellInversion_eq_parameterSpace
    {𝒳 : Type*} [MeasurableSpace 𝒳]
    (q e : 𝒳 → ℝ) {n N : ℕ} (L : ℝ)
    (source : SourceSample 𝒳 n) (target : TargetSample 𝒳 N)
    (hN : N < 2) :
    regularCellInversion q e L source target = parameterSpace := by
  simp [regularCellInversion, hN]

/-- Affine inversion has length at most twice its radius divided by its
nonzero slope, as well as at most the diameter of the parameter space. -/
lemma affineInversionSet_length_le (A B r : ℝ) (hB : B ≠ 0) (hr : 0 ≤ r) :
    setLength (affineInversionSet A B r) ≤ min 2 (2 * r / |B|) := by
  change Causalean.Stat.restrictedSetVolume parameterSpace
    (Causalean.Stat.affineInversionSet parameterSpace A B r) ≤
      min 2 (2 * r / |B|)
  have hvol : (volume parameterSpace).toReal = 2 := by
    simp [parameterSpace, Real.volume_Icc, ENNReal.toReal_ofReal]
    norm_num
  have h := Causalean.Stat.affineInversionSet_restrictedVolume_le
      parameterSpace (by simp [parameterSpace, Real.volume_Icc])
      A B r hB hr
  rw [hvol] at h
  exact h

/-- Affine inversion is always bounded by the diameter of the parameter space. -/
lemma affineInversionSet_length_le_two (A B r : ℝ) :
    setLength (affineInversionSet A B r) ≤ 2 := by
  change Causalean.Stat.restrictedSetVolume parameterSpace
    (Causalean.Stat.affineInversionSet parameterSpace A B r) ≤ 2
  have hvol : (volume parameterSpace).toReal = 2 := by
    simp [parameterSpace, Real.volume_Icc, ENNReal.toReal_ofReal]
    norm_num
  have h := Causalean.Stat.affineInversionSet_restrictedVolume_le_region
      parameterSpace (by simp [parameterSpace, Real.volume_Icc]) A B r
  rw [hvol] at h
  exact h

/-- Expected affine-inversion length is controlled by the mean radius and the
probability that the random slope is less than half its positive mean target. -/
lemma expectedLength_affineInversion_le
    {Omega : Type*} [MeasurableSpace Omega]
    (Q : Measure Omega) [IsProbabilityMeasure Q]
    (A B K : Omega → ℝ) (n : ℕ) (L mu Kbar q : ℝ)
    (hL : 0 ≤ L) (hmu : 0 < mu) (hn : 0 < n)
    (hK : ∀ w, 0 ≤ K w)
    (hKint : Integrable K Q)
    (hKbar : (∫ w, K w ∂Q) ≤ Kbar)
    (hbad : (Q {w | mu / 2 < |B w - mu|}).toReal ≤ q) :
    (∫ w, setLength (affineInversionSet (A w) (B w)
      (L * Real.sqrt (K w / n))) ∂Q) ≤
        4 * L * Real.sqrt (Kbar / n) / mu + 2 * q := by
  change (∫ w, Causalean.Stat.restrictedSetVolume parameterSpace
    (Causalean.Stat.affineInversionSet parameterSpace (A w) (B w)
      (L * Real.sqrt (K w / n))) ∂Q) ≤ _
  have hvol : (volume parameterSpace).toReal = 2 := by
    simp [parameterSpace, Real.volume_Icc, ENNReal.toReal_ofReal]
    norm_num
  have h := Causalean.Stat.expectedRestrictedVolume_affineInversion_le
      Q parameterSpace (by simp [parameterSpace, Real.volume_Icc])
      A B K n L mu Kbar q hL hmu hn hK hKint hKbar hbad
  rw [hvol] at h
  exact h

/-- Frontier conversion when the mean radius proxy is inflated by at most a
factor two. The resulting inverse-root constant is exactly `4 * sqrt 2 * L`. -/
lemma expectedLength_affineInversion_frontier_le_inflated
    {Omega : Type*} [MeasurableSpace Omega]
    (Q : Measure Omega) [IsProbabilityMeasure Q]
    (A B K : Omega → ℝ) (n : ℕ)
    (L mu Kbar q kappa Y t : ℝ)
    (hL : 0 ≤ L) (hmu : 0 < mu) (hn : 0 < n)
    (hK : ∀ w, 0 ≤ K w)
    (hKint : Integrable K Q)
    (hKbar : (∫ w, K w ∂Q) ≤ Kbar)
    (hbad : (Q {w | mu / 2 < |B w - mu|}).toReal ≤ q)
    (hkappa : 0 < kappa) (hY : 0 ≤ Y)
    (hKbar_le : Kbar ≤ 2 * kappa)
    (hq : q ≤ Y / (2 * t))
    (ht : t = (n : ℝ) * mu ^ 2 / kappa) :
    (∫ w, setLength (affineInversionSet (A w) (B w)
      (L * Real.sqrt (K w / n))) ∂Q) ≤
        max 2 (4 * Real.sqrt 2 * L + Y) *
          min 1 (t ^ (-1 / 2 : ℝ)) := by
  have htpos : 0 < t := by rw [ht]; positivity
  have hbadContribution : 2 * q ≤ Y / t := by
    calc
      2 * q ≤ 2 * (Y / (2 * t)) :=
        mul_le_mul_of_nonneg_left hq (by norm_num)
      _ = Y / t := by field_simp [htpos.ne']
  have hvol : (volume parameterSpace).toReal = 2 := by
    simp [parameterSpace, Real.volume_Icc, ENNReal.toReal_ofReal]
    norm_num
  have hbadContribution' : (volume parameterSpace).toReal * q ≤ Y / t := by
    rw [hvol]
    exact hbadContribution
  change (∫ w, Causalean.Stat.restrictedSetVolume parameterSpace
    (Causalean.Stat.affineInversionSet parameterSpace (A w) (B w)
      (L * Real.sqrt (K w / n))) ∂Q) ≤ _
  have h := Causalean.Stat.expectedRestrictedVolume_affineInversion_frontier_le
      Q parameterSpace (by simp [parameterSpace, Real.volume_Icc])
      A B K n L mu Kbar q kappa 2 Y t hL hmu hn hK hKint hKbar
      hbad hkappa (by norm_num) hY hKbar_le hbadContribution' ht
  rw [hvol] at h
  exact h

/-- Frontier conversion without radius-proxy inflation. The resulting
inverse-root constant is exactly `4 * L`. -/
lemma expectedLength_affineInversion_frontier_le_uninflated
    {Omega : Type*} [MeasurableSpace Omega]
    (Q : Measure Omega) [IsProbabilityMeasure Q]
    (A B K : Omega → ℝ) (n : ℕ)
    (L mu Kbar q kappa Y t : ℝ)
    (hL : 0 ≤ L) (hmu : 0 < mu) (hn : 0 < n)
    (hK : ∀ w, 0 ≤ K w)
    (hKint : Integrable K Q)
    (hKbar : (∫ w, K w ∂Q) ≤ Kbar)
    (hbad : (Q {w | mu / 2 < |B w - mu|}).toReal ≤ q)
    (hkappa : 0 < kappa) (hY : 0 ≤ Y)
    (hKbar_le : Kbar ≤ kappa)
    (hq : q ≤ Y / (2 * t))
    (ht : t = (n : ℝ) * mu ^ 2 / kappa) :
    (∫ w, setLength (affineInversionSet (A w) (B w)
      (L * Real.sqrt (K w / n))) ∂Q) ≤
        max 2 (4 * L + Y) * min 1 (t ^ (-1 / 2 : ℝ)) := by
  have htpos : 0 < t := by rw [ht]; positivity
  have hbadContribution : 2 * q ≤ Y / t := by
    calc
      2 * q ≤ 2 * (Y / (2 * t)) :=
        mul_le_mul_of_nonneg_left hq (by norm_num)
      _ = Y / t := by field_simp [htpos.ne']
  have hKbar_le' : Kbar ≤ 1 * kappa := by simpa using hKbar_le
  have hvol : (volume parameterSpace).toReal = 2 := by
    simp [parameterSpace, Real.volume_Icc, ENNReal.toReal_ofReal]
    norm_num
  have hbadContribution' : (volume parameterSpace).toReal * q ≤ Y / t := by
    rw [hvol]
    exact hbadContribution
  change (∫ w, Causalean.Stat.restrictedSetVolume parameterSpace
    (Causalean.Stat.affineInversionSet parameterSpace (A w) (B w)
      (L * Real.sqrt (K w / n))) ∂Q) ≤ _
  have h := Causalean.Stat.expectedRestrictedVolume_affineInversion_frontier_le
      Q parameterSpace (by simp [parameterSpace, Real.volume_Icc])
      A B K n L mu Kbar q kappa 1 Y t hL hmu hn hK hKint hKbar
      hbad hkappa (by norm_num) hY hKbar_le' hbadContribution' ht
  rw [hvol] at h
  simpa using h

end CausalSmith.Stat.TransportedLateStrengthFrontier
