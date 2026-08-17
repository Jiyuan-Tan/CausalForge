import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Helpers.FiniteMaxExperiment
import Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.Depoissonization

/-!
# Direct-product error and finite packing risk

This file converts the coordinatewise direct-product testing error into a
finite-coordinate Poissonized loss and then back into the retained fixed-size
sample loss.
-/

open MeasureTheory ProbabilityTheory Set Filter Asymptotics
open scoped ENNReal NNReal BigOperators

namespace CausalSmith.Stat.BddUniformLogPenalty

open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

/-- The Poissonized value at one center as a function of the synthesized
canonical global marked configuration. -/
-- @node: globalPackingPoissonValue
noncomputable def globalPackingPoissonValue {n : ℕ}
    (T : PIRule n) (x : Score) (s : FiniteSample (Observation × ℝ)) : ℝ :=
  if n ≤ s.count then
    T.map x (canonicalPrefixObservations (0, 0) n
      (finiteSampleMap (packingMarkedDistance x) s))
  else 0

-- @node: globalPackingPoissonValue_measurable
/-- The stated statistic is a measurable function of the observed data, so it is a valid random quantity. -/
lemma globalPackingPoissonValue_measurable {n : ℕ}
    (T : PIRule n) (x : Score) : Measurable (globalPackingPoissonValue T x) := by
  apply Measurable.ite
  · exact measurable_finiteSample_count measurableSet_Ici
  · exact (T.section_measurable x).comp
      ((measurable_canonicalPrefixObservations (0, 0) n).comp
        (measurable_finiteSampleMap _ (packingMarkedDistance_measurable x)))
  · exact measurable_const

/-- The average probability that at least one coordinate decoder is wrong. -/
-- @node: coordinatewiseErrorProbability
noncomputable def coordinatewiseErrorProbability
    {M : ℕ} {Z S : Fin M → Type*} {A : Type*}
    [∀ j, MeasurableSpace (Z j)] [∀ j, MeasurableSpace (S j)]
    [MeasurableSpace A]
    (Q : ∀ j, Bool → Measure (Z j)) (R : Measure A)
    [∀ j b, IsProbabilityMeasure (Q j b)] [IsProbabilityMeasure R]
    (compress : ∀ j, Z j → S j)
    (decoder : ∀ j, S j → ((k : Fin M) → Z k) → A → Bool) : ℝ≥0∞ :=
  (∑ omega : Fin M → Bool,
      (R.prod (Measure.pi (fun j => Q j (omega j))))
        {data | ∃ j,
          decoder j (compress j (data.2 j)) data.2 data.1 ≠ omega j}) /
    ((2 : ℝ≥0∞) ^ M)

/-- For measurable decoders, average simultaneous error is exactly one minus
average simultaneous success. -/
-- @node: coordinatewiseErrorProbability_eq_one_sub_success
lemma coordinatewiseErrorProbability_eq_one_sub_success
    {M : ℕ} {Z S : Fin M → Type*} {A : Type*}
    [∀ j, MeasurableSpace (Z j)] [∀ j, StandardBorelSpace (Z j)]
    [∀ j, MeasurableSpace (S j)] [∀ j, StandardBorelSpace (S j)]
    [MeasurableSpace A] [StandardBorelSpace A]
    (Q : ∀ j, Bool → Measure (Z j)) (R : Measure A)
    [∀ j b, IsProbabilityMeasure (Q j b)] [IsProbabilityMeasure R]
    (compress : ∀ j, Z j → S j) (hcompress : ∀ j, Measurable (compress j))
    (decoder : ∀ j, S j → ((k : Fin M) → Z k) → A → Bool)
    (hdecoder : ∀ j, Measurable
      (fun p : S j × ((k : Fin M) → Z k) × A => decoder j p.1 p.2.1 p.2.2)) :
    coordinatewiseErrorProbability Q R compress decoder =
      1 - coordinatewiseSuccessProbability Q R compress decoder := by
  classical
  let μ (omega : Fin M → Bool) := R.prod (Measure.pi fun j => Q j (omega j))
  let good (omega : Fin M → Bool) :=
    {data : A × ((j : Fin M) → Z j) | ∀ j,
      decoder j (compress j (data.2 j)) data.2 data.1 = omega j}
  let bad (omega : Fin M → Bool) :=
    {data : A × ((j : Fin M) → Z j) | ∃ j,
      decoder j (compress j (data.2 j)) data.2 data.1 ≠ omega j}
  have hgood (omega : Fin M → Bool) : MeasurableSet (good omega) := by
    rw [show good omega = ⋂ j, {data |
        decoder j (compress j (data.2 j)) data.2 data.1 = omega j} by
      ext data
      simp [good]]
    apply MeasurableSet.iInter
    intro j
    apply measurableSet_eq_fun _ measurable_const
    have hm := (hdecoder j).comp
      (((hcompress j).comp ((measurable_pi_apply j).comp measurable_snd)).prodMk
        (measurable_snd.prodMk measurable_fst))
    exact hm
  have hbad (omega : Fin M → Bool) : bad omega = (good omega)ᶜ := by
    ext data
    simp [bad, good]
  have hmeasure (omega : Fin M → Bool) :
      μ omega (bad omega) = 1 - μ omega (good omega) := by
    rw [hbad, measure_compl (hgood omega) (measure_ne_top _ _), measure_univ]
  unfold coordinatewiseErrorProbability coordinatewiseSuccessProbability
  simp only [μ, good, bad] at hmeasure ⊢
  simp_rw [hmeasure]
  have hpow : (2 : ℝ≥0∞) ^ M ≠ 0 := pow_ne_zero _ (by norm_num)
  have hpowtop : (2 : ℝ≥0∞) ^ M ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  have hle (omega : Fin M → Bool) : μ omega (good omega) ≤ 1 := by
    calc
      μ omega (good omega) ≤ μ omega Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  have hsumle : ∑ omega : Fin M → Bool, μ omega (good omega) ≤
      (2 : ℝ≥0∞) ^ M := by
    calc
      ∑ omega : Fin M → Bool, μ omega (good omega) ≤ ∑ _omega : Fin M → Bool, 1 :=
        Finset.sum_le_sum fun omega _ => hle omega
      _ = (2 : ℝ≥0∞) ^ M := by simp [Fintype.card_fun]
  have hsum : (∑ omega : Fin M → Bool,
      (1 - μ omega (good omega))) =
      (2 : ℝ≥0∞) ^ M - ∑ omega : Fin M → Bool, μ omega (good omega) := by
    have hleft : (∑ omega : Fin M → Bool,
        (1 - μ omega (good omega))) ≠ ⊤ :=
      (ENNReal.sum_ne_top).2 fun _ _ => ENNReal.sub_ne_top ENNReal.one_ne_top
    have hright : (2 : ℝ≥0∞) ^ M -
        ∑ omega : Fin M → Bool, μ omega (good omega) ≠ ⊤ :=
      ENNReal.sub_ne_top hpowtop
    apply (ENNReal.toReal_eq_toReal_iff' hleft hright).mp
    rw [ENNReal.toReal_sum (fun _ _ => ENNReal.sub_ne_top ENNReal.one_ne_top),
      ENNReal.toReal_sub_of_le hsumle hpowtop,
      ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _)]
    conv_lhs =>
      enter [2, omega]
      rw [ENNReal.toReal_sub_of_le (hle omega) ENNReal.one_ne_top]
    rw [Finset.sum_sub_distrib]
    simp [Fintype.card_fun] <;> exact hpowtop
  rw [hsum, ENNReal.sub_div, ENNReal.div_self hpow hpowtop]
  intro _ _
  exact hpow

/-- The angular cell experiment inherits the finite direct-product lower
bound after midpoint decoding. -/
-- @node: packingCoordinatewiseError_lower_bound
lemma packingCoordinatewiseError_lower_bound {M n : ℕ}
    (hn : 1 ≤ n) (hM : 1 ≤ M)
    (T : PIRule n) (centers : Fin M → Score)
    (values : Fin M → Bool → ℝ) (w m alpha : ℝ)
    (hdis : ∀ i j, i ≠ j →
      Disjoint (packingCell centers w i) (packingCell centers w j))
    (laws : (Fin M → Bool) → CtyLaw)
    (hsupport : ∀ omega, (laws omega).support = packingSquare)
    (hm : 0 < m)
    (hmass : ∀ omega j,
      Measure.map Prod.snd (laws omega).law (packingCell centers w j) =
        ENNReal.ofReal m)
    (halpha : 0 ≤ alpha) (halpha' : 2 * alpha < 1)
    (hpi : ∀ omega j,
      InformationTheory.klDiv
        (compressedSampleLaw (laws omega) n (centers j))
        (compressedSampleLaw
          (laws (Causalean.Stat.flipBit j omega)) n (centers j)) ≤
        ENNReal.ofReal (alpha * Real.log M)) :
    ENNReal.ofReal ((1 / 2 : ℝ) *
        (1 - Real.exp (-((M : ℝ) ^ (1 - 2 * alpha)) / 2))) ≤
      coordinatewiseErrorProbability
        (fun j b => packingCellExperiment
          (packingFinitePartition centers w hdis) laws (2 * n) j b)
        (packingCommonExperiment
          (packingFinitePartition centers w hdis) laws (2 * n))
        (compressPackingCell centers)
        (packingPoissonDecoder T centers values) := by
  letI : StandardBorelSpace (FiniteSample (Observation × ℝ)) :=
    finiteSample_standardBorelSpace
  letI : StandardBorelSpace (FiniteSample ((ℝ × ℝ) × ℝ)) :=
    finiteSample_standardBorelSpace
  let p := packingFinitePartition centers w hdis
  let Q : ∀ j : Fin M, Bool → Measure (FiniteSample (Observation × ℝ)) :=
    fun j b => packingCellExperiment p laws (2 * n) j b
  let R : Measure (Unit → FiniteSample (Observation × ℝ)) :=
    packingCommonExperiment p laws (2 * n)
  let compress : ∀ j : Fin M,
      FiniteSample (Observation × ℝ) → FiniteSample ((ℝ × ℝ) × ℝ) :=
    compressPackingCell centers
  let decoder := packingPoissonDecoder T centers values
  have hcompress : ∀ j, Measurable (compress j) :=
    fun j => compressPackingCell_measurable centers j
  have hdecoder : ∀ j, Measurable
      (fun z : FiniteSample ((ℝ × ℝ) × ℝ) ×
          (Fin M → FiniteSample (Observation × ℝ)) ×
          (Unit → FiniteSample (Observation × ℝ)) =>
        decoder j z.1 z.2.1 z.2.2) :=
    fun j => packingPoissonDecoder_measurable T centers values j
  have hlocal : ∀ j s z z' a,
      (∀ k, k ≠ j → z k = z' k) →
      decoder j s z a = decoder j s z' a := by
    intro j s z z' a hz
    exact packingPoissonDecoder_local T centers values j s z z' a hz
  have hdp := (coordinatewise_overlap_direct_product hM Q R compress
    hcompress decoder hdecoder hlocal).2 (2 * alpha) halpha'
  have hkl : ∀ j,
      InformationTheory.klDiv
        (compressedCoordinateLaw (compress j) (Q j false))
        (compressedCoordinateLaw (compress j) (Q j true)) ≤
      ENNReal.ofReal ((2 * alpha) * Real.log M) := by
    intro j
    exact compressedPackingCellExperiment_klDiv_le hn hM centers w m alpha
      hdis laws hsupport hm hmass halpha hpi j
  rw [coordinatewiseErrorProbability_eq_one_sub_success Q R compress hcompress
    decoder hdecoder]
  exact hdp hkl

/-- Reassembling the distance-compressed own cell with the other raw cells is
the same as mapping the synthesized global configuration. -/
-- @node: assemblePackingDistanceBlocks_eq_globalMap
lemma assemblePackingDistanceBlocks_eq_globalMap {M : ℕ}
    (centers : Fin M → Score) (j : Fin M)
    (cells : Fin M → FiniteSample (Observation × ℝ))
    (common : Unit → FiniteSample (Observation × ℝ)) :
    assemblePackingDistanceBlocks centers j
        (compressPackingCell centers j (cells j)) cells common =
      finiteSampleMap (packingMarkedDistance (centers j))
        (synthesizePackingConfiguration (common, cells)) := by
  unfold assemblePackingDistanceBlocks compressPackingCell
    synthesizePackingConfiguration superposeByMarks
  rw [show finiteSampleMap (packingMarkedDistance (centers j)) (orderByMarks
        (superpose ((MeasurableEquiv.sumPiEquivProdPi
          (fun _ : Unit ⊕ Fin M => FiniteSample (Observation × ℝ))).symm
            (common, cells)))) =
      orderByMarks (finiteSampleMap (packingMarkedDistance (centers j))
        (superpose ((MeasurableEquiv.sumPiEquivProdPi
          (fun _ : Unit ⊕ Fin M => FiniteSample (Observation × ℝ))).symm
            (common, cells)))) by rfl]
  congr 1
  change superpose _ = finiteSampleMap _ (superpose _)
  rw [show finiteSampleMap (packingMarkedDistance (centers j))
        (superpose ((MeasurableEquiv.sumPiEquivProdPi
          (fun _ : Unit ⊕ Fin M => FiniteSample (Observation × ℝ))).symm
            (common, cells))) =
      superpose (fun k => finiteSampleMap (packingMarkedDistance (centers j))
        (((MeasurableEquiv.sumPiEquivProdPi
          (fun _ : Unit ⊕ Fin M => FiniteSample (Observation × ℝ))).symm
            (common, cells)) k)) by rfl]
  congr 1
  funext k
  cases k with
  | inl u => rfl
  | inr k =>
      change (if k = j then finiteSampleMap _ (cells j)
        else finiteSampleMap _ (cells k)) = finiteSampleMap _ (cells k)
      by_cases h : k = j <;> simp [h]

/-- Maximum Poissonized center loss on a global marked configuration. -/
-- @node: globalPackingPoissonLoss
noncomputable def globalPackingPoissonLoss {M n : ℕ}
    (T : PIRule n) (centers : Fin M → Score)
    (values : Fin M → Bool → ℝ) (omega : Fin M → Bool)
    (s : FiniteSample (Observation × ℝ)) : ℝ≥0∞ :=
  ⨆ j, ENNReal.ofReal
    |globalPackingPoissonValue T (centers j) s - values j (omega j)|

-- @node: globalPackingPoissonLoss_measurable
/-- The stated statistic is a measurable function of the observed data, so it is a valid random quantity. -/
lemma globalPackingPoissonLoss_measurable {M n : ℕ}
    (T : PIRule n) (centers : Fin M → Score)
    (values : Fin M → Bool → ℝ) (omega : Fin M → Bool) :
    Measurable (globalPackingPoissonLoss T centers values omega) := by
  unfold globalPackingPoissonLoss
  apply Measurable.iSup
  intro j
  exact Measurable.ennreal_ofReal
    (((globalPackingPoissonValue_measurable T (centers j)).sub_const _).abs)

/-- The corresponding loss on the independent common/cell blocks. -/
-- @node: blockPackingPoissonLoss
noncomputable def blockPackingPoissonLoss {M n : ℕ}
    (T : PIRule n) (centers : Fin M → Score)
    (values : Fin M → Bool → ℝ) (omega : Fin M → Bool)
    (data : (Unit → FiniteSample (Observation × ℝ)) ×
      (Fin M → FiniteSample (Observation × ℝ))) : ℝ≥0∞ :=
  ⨆ j, ENNReal.ofReal
    |packingPoissonValue T centers j
        (compressPackingCell centers j (data.2 j)) data.2 data.1 -
      values j (omega j)|

-- @node: blockPackingPoissonLoss_measurable
/-- The stated statistic is a measurable function of the observed data, so it is a valid random quantity. -/
lemma blockPackingPoissonLoss_measurable {M n : ℕ}
    (T : PIRule n) (centers : Fin M → Score)
    (values : Fin M → Bool → ℝ) (omega : Fin M → Bool) :
    Measurable (blockPackingPoissonLoss T centers values omega) := by
  unfold blockPackingPoissonLoss
  apply Measurable.iSup
  intro j
  apply Measurable.ennreal_ofReal
  apply Measurable.abs
  apply Measurable.sub_const
  have hm := (packingPoissonValue_measurable T centers j).comp
    (((compressPackingCell_measurable centers j).comp
      ((measurable_pi_apply j).comp measurable_snd)).prodMk
        (measurable_snd.prodMk measurable_fst))
  exact hm

-- @node: blockPackingPoissonLoss_eq_global
/-- The two stated constructions agree under the theorem's assumptions. -/
lemma blockPackingPoissonLoss_eq_global {M n : ℕ}
    (T : PIRule n) (centers : Fin M → Score)
    (values : Fin M → Bool → ℝ) (omega : Fin M → Bool)
    (data : (Unit → FiniteSample (Observation × ℝ)) ×
      (Fin M → FiniteSample (Observation × ℝ))) :
    blockPackingPoissonLoss T centers values omega data =
      globalPackingPoissonLoss T centers values omega
        (synthesizePackingConfiguration data) := by
  rcases data with ⟨common, cells⟩
  unfold blockPackingPoissonLoss globalPackingPoissonLoss
  congr 1
  funext j
  congr 2
  unfold packingPoissonValue globalPackingPoissonValue
  rw [assemblePackingDistanceBlocks_eq_globalMap]
  rfl

/-- Averaging the direct-product decoder error selects one Boolean vertex
whose canonical marked-Poisson maximum loss is at least separation/2 times
the average error probability. -/
-- @node: exists_vertex_poissonLoss_ge_coordinatewiseError
lemma exists_vertex_poissonLoss_ge_coordinatewiseError {M n : ℕ}
    (T : PIRule n) (centers : Fin M → Score)
    (values : Fin M → Bool → ℝ) (w m delta : ℝ)
    (hdis : ∀ i j, i ≠ j →
      Disjoint (packingCell centers w i) (packingCell centers w j))
    (laws : (Fin M → Bool) → CtyLaw)
    (hsupport : ∀ omega, (laws omega).support = packingSquare)
    (hm : 0 < m)
    (hmass : ∀ omega j,
      Measure.map Prod.snd (laws omega).law (packingCell centers w j) =
        ENNReal.ofReal m)
    (hlocal : ∀ omega omega' j, omega j = omega' j →
      (laws omega).law.restrict {o | o.2 ∈ packingCell centers w j} =
        (laws omega').law.restrict {o | o.2 ∈ packingCell centers w j})
    (hoff : ∀ omega omega',
      (laws omega).law.restrict
          {o | o.2 ∈ packingSquare \ ⋃ j, packingCell centers w j} =
        (laws omega').law.restrict
          {o | o.2 ∈ packingSquare \ ⋃ j, packingCell centers w j})
    (hvalues : ∀ omega j,
      (laws omega).mu (centers j) = values j (omega j))
    (hsep : ∀ j, delta ≤ |values j true - values j false|) :
    ∃ omega : Fin M → Bool,
      letI : IsProbabilityMeasure (laws omega).law := (laws omega).law_isProbability
      ENNReal.ofReal (delta / 2) *
          coordinatewiseErrorProbability
            (fun j b => packingCellExperiment
              (packingFinitePartition centers w hdis) laws (2 * n) j b)
            (packingCommonExperiment
              (packingFinitePartition centers w hdis) laws (2 * n))
            (compressPackingCell centers)
            (packingPoissonDecoder T centers values) ≤
        ∫⁻ s, globalPackingPoissonLoss T centers values omega s
          ∂canonicalMarkedPoissonSampleLaw (laws omega).law packingMarkLaw (2 * n) := by
  classical
  letI lawProb (omega : Fin M → Bool) : IsProbabilityMeasure (laws omega).law :=
    (laws omega).law_isProbability
  let p := packingFinitePartition centers w hdis
  let Q : ∀ j : Fin M, Bool → Measure (FiniteSample (Observation × ℝ)) :=
    fun j b => packingCellExperiment p laws (2 * n) j b
  let R : Measure (Unit → FiniteSample (Observation × ℝ)) :=
    packingCommonExperiment p laws (2 * n)
  let μ (omega : Fin M → Bool) := R.prod (Measure.pi fun j => Q j (omega j))
  let bad (omega : Fin M → Bool) :=
    {data : (Unit → FiniteSample (Observation × ℝ)) ×
        (Fin M → FiniteSample (Observation × ℝ)) |
      ∃ j, packingPoissonDecoder T centers values j
        (compressPackingCell centers j (data.2 j)) data.2 data.1 ≠ omega j}
  let risk (omega : Fin M → Bool) :=
    ∫⁻ data, blockPackingPoissonLoss T centers values omega data ∂μ omega
  have hrisk (omega : Fin M → Bool) :
      ENNReal.ofReal (delta / 2) * μ omega (bad omega) ≤ risk omega := by
    rw [← setLIntegral_const]
    calc
      (∫⁻ _ in bad omega, ENNReal.ofReal (delta / 2) ∂μ omega) ≤
          ∫⁻ data in bad omega,
            blockPackingPoissonLoss T centers values omega data ∂μ omega := by
        apply setLIntegral_mono
          (blockPackingPoissonLoss_measurable T centers values omega)
        intro data hdata
        obtain ⟨j, hj⟩ := hdata
        unfold blockPackingPoissonLoss
        refine le_trans (ENNReal.ofReal_le_ofReal
          (midpointDecoder_wrong_bit_error (values j)
            (packingPoissonValue T centers j
              (compressPackingCell centers j (data.2 j)) data.2 data.1)
            delta (hsep j) (omega j) hj)) ?_
        exact le_iSup (fun k : Fin M => ENNReal.ofReal
          |packingPoissonValue T centers k
              (compressPackingCell centers k (data.2 k)) data.2 data.1 -
            values k (omega k)|) j
      _ ≤ risk omega := by
        exact setLIntegral_le_lintegral _ _
  obtain ⟨omegaMax, -, hmax⟩ := Finset.exists_max_image
    (Finset.univ : Finset (Fin M → Bool)) risk Finset.univ_nonempty
  refine ⟨omegaMax, ?_⟩
  have hsum : ENNReal.ofReal (delta / 2) *
        (∑ omega : Fin M → Bool, μ omega (bad omega)) ≤
      ((2 : ℝ≥0∞) ^ M) * risk omegaMax := by
    calc
      ENNReal.ofReal (delta / 2) *
          (∑ omega : Fin M → Bool, μ omega (bad omega)) =
          ∑ omega : Fin M → Bool,
            ENNReal.ofReal (delta / 2) * μ omega (bad omega) := by
              rw [Finset.mul_sum]
      _ ≤ ∑ omega : Fin M → Bool, risk omega :=
        Finset.sum_le_sum fun omega _ => hrisk omega
      _ ≤ ∑ _omega : Fin M → Bool, risk omegaMax :=
        Finset.sum_le_sum fun omega homega => hmax omega homega
      _ = ((2 : ℝ≥0∞) ^ M) * risk omegaMax := by
        simp [Fintype.card_fun]
  have hpow : (2 : ℝ≥0∞) ^ M ≠ 0 := pow_ne_zero _ (by norm_num)
  have hpowtop : (2 : ℝ≥0∞) ^ M ≠ ⊤ :=
    ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  have havg : ENNReal.ofReal (delta / 2) *
      ((∑ omega : Fin M → Bool, μ omega (bad omega)) /
        ((2 : ℝ≥0∞) ^ M)) ≤ risk omegaMax := by
    rw [← mul_div_assoc]
    apply (ENNReal.div_le_iff_le_mul (Or.inl hpow) (Or.inl hpowtop)).2
    simpa [mul_comm] using hsum
  have hsynth := packingExperiment_synthesis_law centers w m hdis laws hm
    hmass hlocal hsupport hoff (2 * n) omegaMax
  have hriskEq : risk omegaMax =
      ∫⁻ s, globalPackingPoissonLoss T centers values omegaMax s
        ∂canonicalMarkedPoissonSampleLaw (laws omegaMax).law packingMarkLaw (2 * n) := by
    unfold risk μ R Q p
    rw [← hsynth]
    rw [lintegral_map'
      (globalPackingPoissonLoss_measurable T centers values omegaMax).aemeasurable
      synthesizePackingConfiguration_measurable.aemeasurable]
    apply lintegral_congr
    intro data
    exact blockPackingPoissonLoss_eq_global T centers values omegaMax data
  rw [← hriskEq]
  simpa [coordinatewiseErrorProbability, Q, R, μ, bad, p] using havg

end CausalSmith.Stat.BddUniformLogPenalty
