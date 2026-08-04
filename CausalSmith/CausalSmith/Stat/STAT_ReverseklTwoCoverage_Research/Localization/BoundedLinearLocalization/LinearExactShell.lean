import CausalSmith.Stat.STAT_ReverseklTwoCoverage_Research.Learner.PredictionPolytope
import CausalSmith.Substrate.MeasurableFiniteLinearERM
import Mathlib.Data.Finset.Sort

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-!
# Exact linear-shell adapters for bounded linear localization

This paper-local module supplies the deterministic selector and sample-design
projector interfaces needed by `bounded_linear_localization`.
-/

namespace CausalSmith.Stat.ReverseKLTwoCoverage.LinearExactShellTypeFit

open MeasureTheory
open InnerProductSpace
open scoped BigOperators RealInnerProductSpace

open CausalSmith.Substrate.MeasurableFiniteLinearERM

variable {d n : ℕ} {𝒳 𝒜 : Type*}
  [Fintype 𝒳] [Fintype 𝒜] [DecidableEq 𝒳] [DecidableEq 𝒜]
  [LinearOrder 𝒳] [LinearOrder 𝒜]
  [MeasurableSpace 𝒳] [MeasurableSpace 𝒜]
  [MeasurableSingletonClass 𝒳] [MeasurableSingletonClass 𝒜]

private lemma realInnerEqMul (x y : ℝ) :
    @inner ℝ ℝ _ x y = x * y := by
  change RCLike.re (y * star x) = x * y
  simp [mul_comm]

noncomputable def coordOrderIso :
    Fin (Fintype.card 𝒳 * Fintype.card 𝒜) ≃o (𝒳 ×ₗ 𝒜) :=
  Fintype.orderIsoFinOfCardEq (𝒳 ×ₗ 𝒜) (by simp)

noncomputable def encodePrediction
    (f : Prediction (𝒳 := 𝒳) (𝒜 := 𝒜)) :
    Fin (Fintype.card 𝒳 * Fintype.card 𝒜) → ℝ :=
  fun i => f (ofLex (coordOrderIso i)).1 (ofLex (coordOrderIso i)).2

noncomputable def decodePrediction
    (v : Fin (Fintype.card 𝒳 * Fintype.card 𝒜) → ℝ) :
    Prediction (𝒳 := 𝒳) (𝒜 := 𝒜) :=
  fun x a => v (coordOrderIso.symm (toLex (x, a)))

lemma decode_encode
    (f : Prediction (𝒳 := 𝒳) (𝒜 := 𝒜)) :
    decodePrediction (encodePrediction f) = f := by
  funext x a
  simp [decodePrediction, encodePrediction]

lemma encode_decode
    (v : Fin (Fintype.card 𝒳 * Fintype.card 𝒜) → ℝ) :
    encodePrediction (decodePrediction v) = v := by
  funext i
  simp [decodePrediction, encodePrediction]

lemma finLexLT_encode_iff
    (f g : Prediction (𝒳 := 𝒳) (𝒜 := 𝒜)) :
    FinLexLT (encodePrediction f) (encodePrediction g) ↔
      PredictionLexLT f g := by
  constructor
  · rintro ⟨i, heq, hlt⟩
    refine ⟨(ofLex (coordOrderIso i)).1, (ofLex (coordOrderIso i)).2, ?_,
      (by simpa [encodePrediction] using hlt)⟩
    intro x' a' hbefore
    have hcoord :
        coordOrderIso.symm (toLex (x', a')) < i := by
      apply (coordOrderIso.lt_iff_lt).1
      simpa [PredictionCoordinateEarlier, Prod.Lex.lt_iff] using hbefore
    have h := heq (coordOrderIso.symm (toLex (x', a'))) hcoord
    simpa [encodePrediction] using h
  · rintro ⟨x, a, heq, hlt⟩
    refine ⟨coordOrderIso.symm (toLex (x, a)), ?_, ?_⟩
    · intro i hi
      apply heq (ofLex (coordOrderIso i)).1 (ofLex (coordOrderIso i)).2
      have hcoord :
          coordOrderIso i < toLex (x, a) := by
        simpa using (coordOrderIso.lt_iff_lt).2 hi
      simpa [PredictionCoordinateEarlier, Prod.Lex.lt_iff] using hcoord
    · simpa [encodePrediction] using hlt

noncomputable def featureMap (E : CommonExperiment d 𝒳 𝒜) :
    (Fin d → ℝ) →ₗ[ℝ]
      (Fin (Fintype.card 𝒳 * Fintype.card 𝒜) → ℝ) where
  toFun θ i :=
    ∑ j, E.feature (ofLex (coordOrderIso i)).1 (ofLex (coordOrderIso i)).2 j * θ j
  map_add' θ ψ := by
    funext i
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c θ := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    calc
      (∑ j, E.feature (ofLex (coordOrderIso i)).1
          (ofLex (coordOrderIso i)).2 j * (c * θ j)) =
          ∑ j, c * (E.feature (ofLex (coordOrderIso i)).1
            (ofLex (coordOrderIso i)).2 j * θ j) := by
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = c * ∑ j, E.feature (ofLex (coordOrderIso i)).1
          (ofLex (coordOrderIso i)).2 j * θ j := by
        rw [Finset.mul_sum]

def coordinatePolytope (E : CommonExperiment d 𝒳 𝒜) :
    Set (Fin (Fintype.card 𝒳 * Fintype.card 𝒜) → ℝ) :=
  Set.Icc 0 1 ∩ LinearMap.range (featureMap E)

lemma encode_mem_coordinatePolytope_iff
    (E : CommonExperiment d 𝒳 𝒜)
    (f : Prediction (𝒳 := 𝒳) (𝒜 := 𝒜)) :
    encodePrediction f ∈ coordinatePolytope E ↔ f ∈ predictionPolytope E := by
  constructor
  · rintro ⟨hbox, θ, hθ⟩
    refine ⟨?_, θ, ?_⟩
    · intro x a
      exact ⟨by
          have hi := hbox.1 (coordOrderIso.symm (toLex (x, a)))
          simpa [encodePrediction] using hi,
        by
          have hi := hbox.2 (coordOrderIso.symm (toLex (x, a)))
          simpa [encodePrediction] using hi⟩
    · intro x a
      have hi := congrFun hθ (coordOrderIso.symm (toLex (x, a)))
      simpa [featureMap, encodePrediction] using hi.symm
  · rintro ⟨hbox, θ, hθ⟩
    refine ⟨?_, θ, ?_⟩
    · constructor
      · intro i
        simpa [encodePrediction] using
          (hbox (ofLex (coordOrderIso i)).1
            (ofLex (coordOrderIso i)).2).1
      · intro i
        simpa [encodePrediction] using
          (hbox (ofLex (coordOrderIso i)).1
            (ofLex (coordOrderIso i)).2).2
    · funext i
      simpa [featureMap, encodePrediction] using
        (hθ (ofLex (coordOrderIso i)).1
          (ofLex (coordOrderIso i)).2).symm

lemma coordinatePolytope_nonempty (E : CommonExperiment d 𝒳 𝒜) :
    (coordinatePolytope E).Nonempty := by
  refine ⟨0, ?_, 0, ?_⟩
  · exact ⟨le_rfl, by norm_num⟩
  · exact (featureMap E).map_zero

lemma coordinatePolytope_compact (E : CommonExperiment d 𝒳 𝒜) :
    IsCompact (coordinatePolytope E) := by
  rw [Metric.isCompact_iff_isClosed_bounded]
  exact ⟨isClosed_Icc.inter (Submodule.closed_of_finiteDimensional _),
    (Metric.isBounded_Icc 0 1).subset Set.inter_subset_left⟩

lemma observationTuple_measurable :
    Measurable (fun z : BanditObservation 𝒳 𝒜 =>
      (z.context, z.action, z.reward)) := by
  change Measurable[MeasurableSpace.comap
    (fun z : BanditObservation 𝒳 𝒜 => (z.context, z.action, z.reward)) inferInstance] _
  exact comap_measurable _

lemma sample_eval_measurable (i : Fin n) :
    Measurable (fun sample : LoggedSample n 𝒳 𝒜 => sample i) :=
  measurable_pi_apply i

noncomputable def coordinateLoss
    (E : CommonExperiment d 𝒳 𝒜)
    (sample : LoggedSample n 𝒳 𝒜)
    (v : Fin (Fintype.card 𝒳 * Fintype.card 𝒜) → ℝ) : ℝ :=
  empiricalLoss sample (decodePrediction v)

lemma coordinateLoss_measurable
    (E : CommonExperiment d 𝒳 𝒜)
    (v : Fin (Fintype.card 𝒳 * Fintype.card 𝒜) → ℝ) :
    Measurable fun sample : LoggedSample n 𝒳 𝒜 => coordinateLoss E sample v := by
  unfold coordinateLoss empiricalLoss decodePrediction
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro i _
  apply Measurable.pow_const
  apply Measurable.sub
  · exact observationTuple_measurable.snd.snd.comp (sample_eval_measurable i)
  · exact (measurable_of_finite
      (fun w : 𝒳 × 𝒜 => v (coordOrderIso.symm (toLex w)))).comp
        ((Measurable.prodMk observationTuple_measurable.fst
          observationTuple_measurable.snd.fst).comp (sample_eval_measurable i))

lemma coordinateLoss_continuous
    (E : CommonExperiment d 𝒳 𝒜) (sample : LoggedSample n 𝒳 𝒜) :
    Continuous fun v => coordinateLoss E sample v := by
  unfold coordinateLoss empiricalLoss decodePrediction
  fun_prop

noncomputable def canonicalCoordinateERM
    (E : CommonExperiment d 𝒳 𝒜) :
    LoggedSample n 𝒳 𝒜 →
      (Fin (Fintype.card 𝒳 * Fintype.card 𝒜) → ℝ) :=
  Classical.choose (measurable_lex_argmin (Ω := LoggedSample n 𝒳 𝒜)
    (coordinatePolytope E) (coordinatePolytope_compact E)
    (coordinatePolytope_nonempty E) (coordinateLoss (n := n) E)
    (coordinateLoss_measurable (n := n) E)
    (coordinateLoss_continuous (n := n) E))

lemma canonicalCoordinateERM_spec
    (E : CommonExperiment d 𝒳 𝒜) (sample : LoggedSample n 𝒳 𝒜) :
    IsLexArgmin (coordinatePolytope E) (coordinateLoss E sample)
      (canonicalCoordinateERM E sample) := by
  have hs := Classical.choose_spec (measurable_lex_argmin
    (Ω := LoggedSample n 𝒳 𝒜)
    (coordinatePolytope E) (coordinatePolytope_compact E)
    (coordinatePolytope_nonempty E) (coordinateLoss (n := n) E)
    (coordinateLoss_measurable (n := n) E)
    (coordinateLoss_continuous (n := n) E))
  exact ⟨hs.2.1 sample, hs.2.2.1 sample, hs.2.2.2.1 sample⟩

noncomputable def canonicalPredictionERM
    (E : CommonExperiment d 𝒳 𝒜) :
    LoggedSample n 𝒳 𝒜 → Prediction (𝒳 := 𝒳) (𝒜 := 𝒜) :=
  fun sample => decodePrediction (canonicalCoordinateERM E sample)

lemma canonicalPredictionERM_isLexicographicERM
    (E : CommonExperiment d 𝒳 𝒜) (sample : LoggedSample n 𝒳 𝒜) :
    IsLexicographicERM E sample (canonicalPredictionERM E sample) := by
  have hs := canonicalCoordinateERM_spec E sample
  refine ⟨(encode_mem_coordinatePolytope_iff E _).mp ?_, ?_, ?_⟩
  · simpa [canonicalPredictionERM, encode_decode] using hs.1
  · intro g hg
    have hg' := (encode_mem_coordinatePolytope_iff E g).mpr hg
    have hmin := hs.2.1 (encodePrediction g) hg'
    simpa [coordinateLoss, canonicalPredictionERM, encode_decode,
      decode_encode] using hmin
  · intro g hg hEq hlt
    apply hs.2.2 (encodePrediction g)
      ((encode_mem_coordinatePolytope_iff E g).mpr hg)
    · simpa [coordinateLoss, canonicalPredictionERM, encode_decode,
        decode_encode] using hEq
    · simpa [canonicalPredictionERM, encode_decode] using
        (finLexLT_encode_iff g (canonicalPredictionERM E sample)).2 hlt

lemma selectedERM_isLexicographicERM
    (E : CommonExperiment d 𝒳 𝒜) (sample : LoggedSample n 𝒳 𝒜) :
    IsLexicographicERM E sample (selectedERM E sample) := by
  unfold selectedERM
  split_ifs with h
  · exact Classical.choose_spec h
  · exact (h ⟨canonicalPredictionERM E sample,
      canonicalPredictionERM_isLexicographicERM E sample⟩).elim

lemma selectedERM_eq_canonicalPredictionERM
    (E : CommonExperiment d 𝒳 𝒜) :
    selectedERM (n := n) E = canonicalPredictionERM E := by
  funext sample
  have hs := Classical.choose_spec (measurable_lex_argmin
    (Ω := LoggedSample n 𝒳 𝒜)
    (coordinatePolytope E) (coordinatePolytope_compact E)
    (coordinatePolytope_nonempty E) (coordinateLoss (n := n) E)
    (coordinateLoss_measurable (n := n) E)
    (coordinateLoss_continuous (n := n) E))
  have hencoded :
      (fun s : LoggedSample n 𝒳 𝒜 => encodePrediction (selectedERM E s)) =
        canonicalCoordinateERM (n := n) E := by
    apply hs.2.2.2.2
    intro s
    have hsel := selectedERM_isLexicographicERM E s
    refine ⟨(encode_mem_coordinatePolytope_iff E _).2 hsel.1, ?_, ?_⟩
    · intro v hv
      simpa [coordinateLoss, decode_encode] using
        hsel.2.1 (decodePrediction v)
          ((encode_mem_coordinatePolytope_iff E _).1
            (by simpa [encode_decode] using hv))
    · intro v hv heq
      exact fun hlt => hsel.2.2 (decodePrediction v)
        ((encode_mem_coordinatePolytope_iff E _).1
          (by simpa [encode_decode] using hv))
        (by simpa [coordinateLoss, decode_encode] using heq)
        ((finLexLT_encode_iff _ _).1
          (by simpa [encode_decode] using hlt))
  have := congrFun hencoded sample
  simpa [canonicalPredictionERM, decode_encode] using congrArg decodePrediction this

noncomputable def designMatrix (E : CommonExperiment d 𝒳 𝒜)
    (sample : LoggedSample n 𝒳 𝒜) : Matrix (Fin n) (Fin d) ℝ :=
  fun i j => E.feature (sample i).context (sample i).action j

lemma designMatrix_measurable_coord (E : CommonExperiment d 𝒳 𝒜) (i j) :
    Measurable fun sample : LoggedSample n 𝒳 𝒜 => designMatrix E sample i j := by
  unfold designMatrix
  exact (measurable_of_finite
    (fun w : 𝒳 × 𝒜 => E.feature w.1 w.2 j)).comp
      ((Measurable.prodMk observationTuple_measurable.fst
        observationTuple_measurable.snd.fst).comp (sample_eval_measurable i))

lemma designProjector_spec (E : CommonExperiment d 𝒳 𝒜) :
    (∀ i k, Measurable fun sample : LoggedSample n 𝒳 𝒜 =>
      rangeProjector (designMatrix E sample) i k) ∧
    (∀ sample : LoggedSample n 𝒳 𝒜,
      (rangeProjector (designMatrix E sample)).transpose =
      rangeProjector (designMatrix E sample)) ∧
    (∀ sample : LoggedSample n 𝒳 𝒜,
      rangeProjector (designMatrix E sample) *
      rangeProjector (designMatrix E sample) =
      rangeProjector (designMatrix E sample)) ∧
    ∀ sample : LoggedSample n 𝒳 𝒜,
      Matrix.rank (rangeProjector (designMatrix E sample)) ≤ d := by
  refine ⟨rangeProjector_measurable_coord (designMatrix E)
      (designMatrix_measurable_coord E), ?_, ?_, ?_⟩
  · exact fun sample => rangeProjector_transpose _
  · exact fun sample => rangeProjector_mul_self _
  · exact fun sample => rangeProjector_rank_le _

lemma designProjector_fixed_iff (E : CommonExperiment d 𝒳 𝒜)
    (sample : LoggedSample n 𝒳 𝒜) (v : Fin n → ℝ) :
    Matrix.toLin' (rangeProjector (designMatrix E sample)) v = v ↔
      v ∈ LinearMap.range (Matrix.toLin' (designMatrix E sample)) :=
  rangeProjector_fixed_iff _ _

noncomputable def sampleEvaluation (sample : LoggedSample n 𝒳 𝒜)
    (f : Prediction (𝒳 := 𝒳) (𝒜 := 𝒜)) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun i => f (sample i).context (sample i).action

noncomputable def responseVector (sample : LoggedSample n 𝒳 𝒜) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun i => (sample i).reward

noncomputable def centeredNoise (E : CommonExperiment d 𝒳 𝒜) (P : BanditLaw E)
    (sample : LoggedSample n 𝒳 𝒜) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun i =>
    (sample i).reward -
      linearReward P (sample i).context (sample i).action

def evaluationSet (E : CommonExperiment d 𝒳 𝒜)
    (sample : LoggedSample n 𝒳 𝒜) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {v | ∃ f ∈ predictionPolytope E, v = sampleEvaluation sample f}

lemma sampleEvaluation_mem_designRange
    (E : CommonExperiment d 𝒳 𝒜) (sample : LoggedSample n 𝒳 𝒜)
    (f : Prediction (𝒳 := 𝒳) (𝒜 := 𝒜))
    (hf : f ∈ predictionPolytope E) :
    (sampleEvaluation sample f : Fin n → ℝ) ∈
      LinearMap.range (Matrix.toLin' (designMatrix E sample)) := by
  rcases hf with ⟨_, θ, hθ⟩
  refine ⟨θ, ?_⟩
  funext i
  simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
    sampleEvaluation]
  simpa [designMatrix] using (hθ (sample i).context (sample i).action).symm

noncomputable def euclideanProjector (E : CommonExperiment d 𝒳 𝒜)
    (sample : LoggedSample n 𝒳 𝒜) :
    EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
  (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm.toLinearMap.comp
    ((Matrix.toLin' (rangeProjector (designMatrix E sample))).comp
      (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).toLinearMap)

lemma euclideanProjector_apply (E : CommonExperiment d 𝒳 𝒜)
    (sample : LoggedSample n 𝒳 𝒜) (v : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    euclideanProjector E sample v i =
      Matrix.toLin' (rangeProjector (designMatrix E sample)) v i := by
  rfl

lemma evaluationSet_subset_projectorRange
    (E : CommonExperiment d 𝒳 𝒜) (sample : LoggedSample n 𝒳 𝒜) :
    evaluationSet E sample ⊆
      LinearMap.range (euclideanProjector E sample) := by
  rintro v ⟨f, hf, rfl⟩
  refine ⟨sampleEvaluation sample f, ?_⟩
  ext i
  rw [euclideanProjector_apply]
  exact congrFun ((designProjector_fixed_iff E sample _).2
    (sampleEvaluation_mem_designRange E sample f hf)) i

lemma response_eq_truth_add_noise
    (P : BanditLaw E) (sample : LoggedSample n 𝒳 𝒜) :
    responseVector sample =
      sampleEvaluation sample (linearReward P) + centeredNoise E P sample := by
  ext i
  simp [responseVector, sampleEvaluation, centeredNoise]

lemma selectedEvaluation_minimizes
    (E : CommonExperiment d 𝒳 𝒜) (sample : LoggedSample n 𝒳 𝒜)
    (hn : 0 < n) :
    ∀ v ∈ evaluationSet E sample,
      ‖responseVector sample - sampleEvaluation sample (selectedERM E sample)‖ ^ 2 ≤
        ‖responseVector sample - v‖ ^ 2 := by
  rintro v ⟨f, hf, rfl⟩
  have hopt := (selectedERM_isLexicographicERM E sample).2.1 f hf
  unfold empiricalLoss at hopt
  have hn0 : 0 < (n : ℝ)⁻¹ := inv_pos.mpr (Nat.cast_pos.mpr hn)
  have hsum := le_of_mul_le_mul_left hopt hn0
  rw [norm_sq_eq_sum_sq, norm_sq_eq_sum_sq]
  simpa [responseVector, sampleEvaluation, Pi.sub_apply] using hsum

lemma selectedERM_empirical_projection_bound
    (E : CommonExperiment d 𝒳 𝒜) (P : BanditLaw E) (C D : ℝ)
    (hshell : ExactShell E P C D) (sample : LoggedSample n 𝒳 𝒜)
    (hn : 0 < n) :
    empiricalSqNorm
        (sampleEvaluation sample (selectedERM E sample) -
          sampleEvaluation sample (linearReward P)) ≤
      4 * empiricalSqNorm
        (euclideanProjector E sample (centeredNoise E P sample)) := by
  let Pi := euclideanProjector E sample
  let V := LinearMap.range Pi
  let K := evaluationSet E sample
  apply constrainedLeastSquares_empiricalSqNorm_bound hn V K Pi
    (sampleEvaluation sample (linearReward P))
    (sampleEvaluation sample (selectedERM E sample))
    (centeredNoise E P sample) (responseVector sample)
  · exact evaluationSet_subset_projectorRange E sample
  · exact ⟨linearReward P, ⟨hshell.linearRealizability.1, P.theta,
      fun _ _ => rfl⟩, rfl⟩
  · exact ⟨selectedERM E sample,
      (selectedERM_isLexicographicERM E sample).1, rfl⟩
  · exact response_eq_truth_add_noise P sample
  · exact selectedEvaluation_minimizes E sample hn
  · intro x z
    simp only [Pi, euclideanProjector_apply, Matrix.toLin'_apply,
      PiLp.inner_apply, realInnerEqMul,
      Matrix.mulVec, dotProduct]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [show rangeProjector (designMatrix E sample) i j =
      rangeProjector (designMatrix E sample) j i by
        have h := congrFun₂ (rangeProjector_transpose (designMatrix E sample)) j i
        simpa using h]
    ring
  · intro x
    ext i
    change Matrix.mulVec (rangeProjector (designMatrix E sample))
      (Matrix.mulVec (rangeProjector (designMatrix E sample))
        (x : Fin n → ℝ)) i =
      Matrix.mulVec (rangeProjector (designMatrix E sample))
        (x : Fin n → ℝ) i
    rw [Matrix.mulVec_mulVec, rangeProjector_mul_self]
  · rfl

noncomputable def loggedDesign (sample : LoggedSample n 𝒳 𝒜) :
    Fin n → 𝒳 × 𝒜 :=
  fun i => ((sample i).context, (sample i).action)

noncomputable def designSigma : MeasurableSpace (LoggedSample n 𝒳 𝒜) :=
  MeasurableSpace.comap loggedDesign inferInstance

def rewardNoise (E : CommonExperiment d 𝒳 𝒜) (P : BanditLaw E) (i : Fin n)
    (sample : LoggedSample n 𝒳 𝒜) : ℝ :=
  (sample i).reward -
    linearReward P (sample i).context (sample i).action

lemma loggedDesign_measurable :
    Measurable (loggedDesign :
      LoggedSample n 𝒳 𝒜 → Fin n → 𝒳 × 𝒜) := by
  rw [measurable_pi_iff]
  intro i
  exact (Measurable.prodMk observationTuple_measurable.fst
    observationTuple_measurable.snd.fst).comp (sample_eval_measurable i)

lemma designSigma_le :
    (designSigma : MeasurableSpace (LoggedSample n 𝒳 𝒜)) ≤
      (inferInstance : MeasurableSpace (LoggedSample n 𝒳 𝒜)) :=
  loggedDesign_measurable.comap_le

lemma rewardNoise_measurable (E : CommonExperiment d 𝒳 𝒜)
    (P : BanditLaw E) (i : Fin n) :
    Measurable (rewardNoise E P i) := by
  unfold rewardNoise
  apply Measurable.sub
  · exact observationTuple_measurable.snd.snd.comp (sample_eval_measurable i)
  · exact (measurable_of_finite
      (fun w : 𝒳 × 𝒜 => linearReward P w.1 w.2)).comp
        ((Measurable.prodMk observationTuple_measurable.fst
          observationTuple_measurable.snd.fst).comp (sample_eval_measurable i))

lemma rewardNoise_ae_bound
    (E : CommonExperiment d 𝒳 𝒜) (P : BanditLaw E) (C D : ℝ)
    (hshell : ExactShell E P C D) (i : Fin n) :
    ∀ᵐ sample ∂productLaw E P n, |rewardNoise E P i sample| ≤ 1 := by
  letI : IsProbabilityMeasure P.dataMeasure := P.isProbability
  change ∀ᵐ sample ∂Measure.pi (fun _ : Fin n => P.dataMeasure),
    |rewardNoise E P i sample| ≤ 1
  have hsingle :
      ∀ᵐ z ∂P.dataMeasure,
        |z.reward - linearReward P z.context z.action| ≤ 1 := by
    filter_upwards [P.reward_mem] with z hz
    have hr := hshell.linearRealizability.1 z.context z.action
    change 0 ≤ z.reward ∧ z.reward ≤ 1 at hz
    change 0 ≤ linearReward P z.context z.action ∧
      linearReward P z.context z.action ≤ 1 at hr
    rw [abs_le]
    constructor <;> linarith
  simpa [rewardNoise] using
    (measurePreserving_eval (fun _ : Fin n => P.dataMeasure) i).quasiMeasurePreserving.ae
      hsingle

end CausalSmith.Stat.ReverseKLTwoCoverage.LinearExactShellTypeFit
