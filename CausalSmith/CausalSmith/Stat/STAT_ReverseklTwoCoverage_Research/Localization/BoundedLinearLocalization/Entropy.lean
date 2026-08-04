import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Localization.BoundedLinearLocalization.Adapters

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-!
# Entropy adapter for bounded linear localization
-/

namespace CausalSmith.Stat.ReverseKLTwoCoverage.BoundedLinearLocalizationEntropy

open MeasureTheory
open scoped BigOperators

open CausalSmith.Substrate
open CausalSmith.Stat.ReverseKLTwoCoverage.LinearExactShellTypeFit

noncomputable section

variable {d n : ℕ} {𝒳 𝒜 : Type*}
  [Fintype 𝒳] [Fintype 𝒜] [DecidableEq 𝒳] [DecidableEq 𝒜]
  [LinearOrder 𝒳] [LinearOrder 𝒜]
  [MeasurableSpace 𝒳] [MeasurableSpace 𝒜]
  [MeasurableSingletonClass 𝒳] [MeasurableSingletonClass 𝒜]

abbrev PredictionRange (E : CommonExperiment d 𝒳 𝒜) :=
  LinearMap.range (featureMap E)

noncomputable def boundedPredictionRange (E : CommonExperiment d 𝒳 𝒜) :
    Set (PredictionRange E) :=
  {v | ∀ i, (v : Fin (Fintype.card 𝒳 * Fintype.card 𝒜) → ℝ) i ∈
    Set.Icc (0 : ℝ) 1}

lemma boundedPredictionRange_unit
    (E : CommonExperiment d 𝒳 𝒜) :
    ∀ v ∈ boundedPredictionRange E, ‖v‖ ≤ 1 := by
  intro v hv
  change ‖(v : Fin (Fintype.card 𝒳 * Fintype.card 𝒜) → ℝ)‖ ≤ 1
  rw [Pi.norm_def]
  norm_cast
  apply Finset.sup_le
  intro i _
  change ‖(v : Fin (Fintype.card 𝒳 * Fintype.card 𝒜) → ℝ) i‖₊ ≤ 1
  exact_mod_cast (abs_le.2 ⟨by linarith [(hv i).1], (hv i).2⟩)

lemma boundedPredictionRange_nonempty
    (E : CommonExperiment d 𝒳 𝒜) :
    (boundedPredictionRange E).Nonempty := by
  refine ⟨⟨0, (featureMap E).map_zero ▸ LinearMap.mem_range_self
    (featureMap E) 0⟩, ?_⟩
  intro i
  simp

lemma finrank_predictionRange_le
    (E : CommonExperiment d 𝒳 𝒜) :
    Module.finrank ℝ (PredictionRange E) ≤ d := by
  calc
    Module.finrank ℝ (PredictionRange E) ≤
        Module.finrank ℝ (Fin d → ℝ) :=
      (featureMap E).finrank_range_le
    _ = d := by simp [Module.finrank_pi_fintype]

lemma prediction_of_boundedRange_mem
    (E : CommonExperiment d 𝒳 𝒜) (v : PredictionRange E)
    (hv : v ∈ boundedPredictionRange E) :
    decodePrediction (v : Fin (Fintype.card 𝒳 * Fintype.card 𝒜) → ℝ) ∈
      predictionPolytope E := by
  apply (encode_mem_coordinatePolytope_iff E _).mp
  rw [encode_decode]
  exact ⟨⟨fun i => (hv i).1, fun i => (hv i).2⟩, v.2⟩

lemma coordinate_abs_le_norm
    (v w : PredictionRange E)
    (i : Fin (Fintype.card 𝒳 * Fintype.card 𝒜)) :
    |v.1 i - w.1 i| ≤
      ‖v - w‖ := by
  change
    |((v - w : PredictionRange E) :
      Fin (Fintype.card 𝒳 * Fintype.card 𝒜) → ℝ) i| ≤
      ‖((v - w : PredictionRange E) :
        Fin (Fintype.card 𝒳 * Fintype.card 𝒜) → ℝ)‖
  rw [Pi.norm_def]
  have hi := Finset.le_sup
    (s := Finset.univ)
    (f := fun j =>
      ‖((v - w : PredictionRange E) :
        Fin (Fintype.card 𝒳 * Fintype.card 𝒜) → ℝ) j‖₊)
    (Finset.mem_univ i)
  exact_mod_cast hi

lemma exists_prediction_net
    (E : CommonExperiment d 𝒳 𝒜) (u : ℝ) (hu : 0 < u) :
    ∃ net : Finset (Prediction (𝒳 := 𝒳) (𝒜 := 𝒜)),
      (∀ h ∈ net, h ∈ predictionPolytope E) ∧
      (∀ f ∈ predictionPolytope E, ∃ h ∈ net,
        ∀ x a, |f x a - h x a| ≤ u) ∧
      (net.card : ℝ) ≤
        (1 + 2 / u) ^ Module.finrank ℝ (PredictionRange E) := by
  classical
  obtain ⟨N, hNsub, hNcover, hNcard⟩ :=
    Causalean.exists_internal_net_card_le
      (PredictionRange E) (boundedPredictionRange E)
      (boundedPredictionRange_unit E) hu
  let decodeRange : PredictionRange E →
      Prediction (𝒳 := 𝒳) (𝒜 := 𝒜) :=
    fun v => decodePrediction
      (v : Fin (Fintype.card 𝒳 * Fintype.card 𝒜) → ℝ)
  let net := N.image decodeRange
  refine ⟨net, ?_, ?_, ?_⟩
  · intro h hh
    rcases Finset.mem_image.mp hh with ⟨v, hvN, rfl⟩
    exact prediction_of_boundedRange_mem E v (hNsub v hvN)
  · intro f hf
    have hcoord := (encode_mem_coordinatePolytope_iff E f).mpr hf
    let v : PredictionRange E :=
      ⟨encodePrediction f, hcoord.2⟩
    have hv : v ∈ boundedPredictionRange E :=
      fun i => ⟨hcoord.1.1 i, hcoord.1.2 i⟩
    obtain ⟨w, hwN, hvw⟩ := hNcover v hv
    refine ⟨decodeRange w, Finset.mem_image.mpr ⟨w, hwN, rfl⟩, ?_⟩
    intro x a
    have hcoordBound := coordinate_abs_le_norm v w
      (coordOrderIso.symm (toLex (x, a)))
    have := hcoordBound.trans hvw
    simpa [v, decodeRange, encodePrediction, decodePrediction] using this
  · exact (Nat.cast_le.mpr (Finset.card_image_le (s := N) (f := decodeRange))).trans
      hNcard

lemma supCoveringNumber_le
    (E : CommonExperiment d 𝒳 𝒜) (u : ℝ) (hu : 0 < u) :
    (supCoveringNumber (predictionPolytope E) u : ℝ) ≤
      (1 + 2 / u) ^ d := by
  obtain ⟨net, _, hcover, hcard⟩ := exists_prediction_net E u hu
  have hsinf : supCoveringNumber (predictionPolytope E) u ≤ net.card := by
    apply Nat.sInf_le
    exact ⟨net, rfl, hcover⟩
  calc
    (supCoveringNumber (predictionPolytope E) u : ℝ) ≤ net.card := by
      exact_mod_cast hsinf
    _ ≤ (1 + 2 / u) ^ Module.finrank ℝ (PredictionRange E) := hcard
    _ ≤ (1 + 2 / u) ^ d := by
      have hbase : 1 ≤ 1 + 2 / u := by
        have : 0 ≤ 2 / u := (div_pos (by norm_num) hu).le
        linarith
      exact pow_le_pow_right₀ hbase (finrank_predictionRange_le E)

lemma supCoveringNumber_pos
    (E : CommonExperiment d 𝒳 𝒜) (u : ℝ) (hu : 0 < u) :
    0 < supCoveringNumber (predictionPolytope E) u := by
  let S : Set ℕ :=
    {k : ℕ | ∃ net : Finset (Prediction (𝒳 := 𝒳) (𝒜 := 𝒜)),
      net.card = k ∧ ∀ g ∈ predictionPolytope E, ∃ h ∈ net,
        ∀ x a, |g x a - h x a| ≤ u}
  have hSne : S.Nonempty := by
    obtain ⟨net, _, hcover, _⟩ := exists_prediction_net E u hu
    exact ⟨net.card, net, rfl, hcover⟩
  have hmem : sInf S ∈ S := Nat.sInf_mem hSne
  change 0 < sInf S
  by_contra hzero
  have hz : sInf S = 0 := Nat.eq_zero_of_not_pos hzero
  rcases hmem with ⟨net, hcard, hcover⟩
  have hnet : net = ∅ := Finset.card_eq_zero.mp (hcard.trans hz)
  have hzeroPoly : (fun _ _ => (0 : ℝ)) ∈ predictionPolytope E := by
    refine ⟨fun _ _ => by simp, 0, ?_⟩
    intro x a
    simp
  rcases hcover _ hzeroPoly with ⟨h, hh, _⟩
  simpa [hnet] using hh

end

end CausalSmith.Stat.ReverseKLTwoCoverage.BoundedLinearLocalizationEntropy
