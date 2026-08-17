/-
# Oracle score-inversion risk engine

Leaf lemmas for the common score-inversion calculation used by the global
oracle class and by a fixed-geometry slice.  Model-class quantification is
kept abstract; this file does not close either paper theorem.
-/

import CausalSmith.Stat.STAT_TransportedLateStrengthFrontier_Research.Helpers.InversionRisk
import CausalSmith.Stat.STAT_TransportedLateStrengthFrontier_Research.Helpers.RegularCellRisk_Part1
import CausalSmith.Stat.STAT_TransportedLateStrengthFrontier_Research.T_CompactCausalRange
import Causalean.Stat.Minimax.HonestConfidenceSet
import Causalean.Mathlib.MeasureTheory.SetIntegralRecovery
import Causalean.Stat.Concentration.Chebyshev
import Causalean.Stat.Sample.EffectiveSampleSize

namespace CausalSmith.Stat.TransportedLateStrengthFrontier

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

/-- Atom-by-atom interface required of an abstract model predicate by the
score-risk calculation.  Each field is an implication schema, so a fixed
geometry slice supplies the same atoms through its first component. -/
structure ScoreRiskClassAtoms
    (cls : ℕ → TransportedArray 𝒳 → Prop)
    (N k : ℕ → ℕ) (c epsilon : ℝ) : Prop where
  fullDataSupport : ∀ n P, cls n P → FullDataSupport P n
  populationPresence : ∀ n P, cls n P → PopulationPresence P n
  twoSampleArray : ∀ n P, cls n P → TwoSampleArray P N c
  instrumentOverlap : ∀ n P, cls n P → InstrumentOverlap P n epsilon
  sourceObservation : ∀ n P, cls n P → SourceAssignmentConsistency P n
  ivRandomization : ∀ n P, cls n P → IVRandomization P n
  ivExclusion : ∀ n P, cls n P → IVExclusion P n
  ivMonotonicity : ∀ n P, cls n P → IVMonotonicity P n
  outcomeTransport : ∀ n P, cls n P → OutcomeTransport P n
  receiptTransport : ∀ n P, cls n P → ReceiptTransport P n
  targetComplierPositivity :
    ∀ n P, cls n P → TargetComplierPositivity P n
  transportDomination : ∀ n P, cls n P → TransportDomination P n
  weightEnvelope : ∀ n P, cls n P → WeightEnvelope P k n
  weightSecondMoment : ∀ n P, cls n P → WeightSecondMoment P k n
  degradingArray : ∀ n P, cls n P → DegradingArray P k

/-- The global transported-IV class instantiates the abstract atom interface. -/
def transportedIVScoreRiskAtoms (N k : ℕ → ℕ) (c epsilon : ℝ) :
    ScoreRiskClassAtoms
      (fun n (P : TransportedArray 𝒳) =>
        TransportedIVClass P N k c epsilon n) N k c epsilon where
  fullDataSupport := fun _ _ h => h.fullDataSupport
  populationPresence := fun _ _ h => h.populationPresence
  twoSampleArray := fun _ _ h => h.twoSampleArray
  instrumentOverlap := fun _ _ h => h.instrumentOverlap
  sourceObservation := fun _ _ h => h.sourceObservation
  ivRandomization := fun _ _ h => h.ivRandomization
  ivExclusion := fun _ _ h => h.ivExclusion
  ivMonotonicity := fun _ _ h => h.ivMonotonicity
  outcomeTransport := fun _ _ h => h.outcomeTransport
  receiptTransport := fun _ _ h => h.receiptTransport
  targetComplierPositivity := fun _ _ h => h.targetComplierPositivity
  transportDomination := fun _ _ h => h.transportDomination
  weightEnvelope := fun _ _ h => h.weightEnvelope
  weightSecondMoment := fun _ _ h => h.weightSecondMoment
  degradingArray := fun _ _ h => h.degradingArray

/-- Every fixed-geometry slice instantiates the same abstract atom interface. -/
def fixedGeometryScoreRiskAtoms (g : Geometry 𝒳)
    (N k : ℕ → ℕ) (c epsilon : ℝ) :
    ScoreRiskClassAtoms
      (fun n (P : TransportedArray 𝒳) =>
        fixedGeometrySlice P g N k c epsilon n) N k c epsilon where
  fullDataSupport := fun _ _ h => h.1.fullDataSupport
  populationPresence := fun _ _ h => h.1.populationPresence
  twoSampleArray := fun _ _ h => h.1.twoSampleArray
  instrumentOverlap := fun _ _ h => h.1.instrumentOverlap
  sourceObservation := fun _ _ h => h.1.sourceObservation
  ivRandomization := fun _ _ h => h.1.ivRandomization
  ivExclusion := fun _ _ h => h.1.ivExclusion
  ivMonotonicity := fun _ _ h => h.1.ivMonotonicity
  outcomeTransport := fun _ _ h => h.1.outcomeTransport
  receiptTransport := fun _ _ h => h.1.receiptTransport
  targetComplierPositivity := fun _ _ h => h.1.targetComplierPositivity
  transportDomination := fun _ _ h => h.1.transportDomination
  weightEnvelope := fun _ _ h => h.1.weightEnvelope
  weightSecondMoment := fun _ _ h => h.1.weightSecondMoment
  degradingArray := fun _ _ h => h.1.degradingArray

/-- The one-observation affine oracle score. -/
noncomputable def oracleAffineScore (weight e : 𝒳 → ℝ) (theta : ℝ)
    (o : SourceObs 𝒳) : ℝ :=
  weight o.1 * oracleInstrumentScore e o *
    (o.2.2.2 - theta * boolReal o.2.2.1)

/-- The score average is the difference of the outcome and receipt averages. -/
lemma scoreOutcomeMean_sub_receiptMean
    (weight e : 𝒳 → ℝ) (theta : ℝ) (n : ℕ)
    (sample : SourceSample 𝒳 n) :
    scoreOutcomeMean weight e n sample -
        theta * scoreReceiptMean weight e n sample =
      (n : ℝ)⁻¹ * ∑ i, oracleAffineScore weight e theta (sample i) := by
  simp only [scoreOutcomeMean, scoreReceiptMean, oracleAffineScore]
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- S1.1: component score means imply the affine score identity, and the
identifying ratio centers the score at the target effect. -/
lemma oracleAffineScore_mean_zero
    (Q : Measure (SourceObs 𝒳)) [IsProbabilityMeasure Q]
    (weight e : 𝒳 → ℝ) (theta muY mu : ℝ)
    (hY : Integrable
      (fun o => weight o.1 * oracleInstrumentScore e o * o.2.2.2) Q)
    (hD : Integrable
      (fun o => weight o.1 * oracleInstrumentScore e o *
        boolReal o.2.2.1) Q)
    (hYmean : (∫ o, weight o.1 * oracleInstrumentScore e o * o.2.2.2 ∂Q) =
      muY)
    (hDmean : (∫ o, weight o.1 * oracleInstrumentScore e o *
        boolReal o.2.2.1 ∂Q) = mu)
    (hmu : mu ≠ 0) (hratio : muY / mu = theta) :
    (∫ o, oracleAffineScore weight e theta o ∂Q) = 0 := by
  have hpoint :
      oracleAffineScore weight e theta =
        fun o => weight o.1 * oracleInstrumentScore e o * o.2.2.2 -
          theta * (weight o.1 * oracleInstrumentScore e o *
            boolReal o.2.2.1) := by
    funext o
    simp [oracleAffineScore]
    ring
  rw [hpoint, integral_sub hY (hD.const_mul theta), integral_const_mul,
    hYmean, hDmean]
  apply (sub_eq_zero.mpr ?_)
  rw [← hratio]
  field_simp [hmu]

/-- S1.2: overlap and the outcome/parameter ranges give the exact
`2 / epsilon` envelope for the oracle affine score without the weight. -/
lemma abs_oracleInstrumentScore_residual_le
    (e : 𝒳 → ℝ) (epsilon theta : ℝ) (o : SourceObs 𝒳)
    (hepsilon : 0 < epsilon)
    (hoverlap : epsilon ≤ e o.1 ∧ e o.1 ≤ 1 - epsilon)
    (htheta : theta ∈ parameterSpace)
    (hy : o.2.2.2 ∈ Set.Icc (0 : ℝ) 1) :
    |oracleInstrumentScore e o *
      (o.2.2.2 - theta * boolReal o.2.2.1)| ≤ 2 / epsilon := by
  simpa [regularCellScore] using
    abs_regularCellScore_le e epsilon theta o hepsilon hoverlap htheta hy

/-- S1.2, squared form: after multiplying by a nonnegative weight, the score
square is bounded by `4 w² / epsilon²`. -/
lemma oracleAffineScore_sq_le
    (weight e : 𝒳 → ℝ) (epsilon theta : ℝ) (o : SourceObs 𝒳)
    (hepsilon : 0 < epsilon)
    (hoverlap : epsilon ≤ e o.1 ∧ e o.1 ≤ 1 - epsilon)
    (htheta : theta ∈ parameterSpace)
    (hy : o.2.2.2 ∈ Set.Icc (0 : ℝ) 1) :
    oracleAffineScore weight e theta o ^ 2 ≤
      4 * weight o.1 ^ 2 / epsilon ^ 2 := by
  have hscore := abs_oracleInstrumentScore_residual_le
    e epsilon theta o hepsilon hoverlap htheta hy
  have hbound : 0 ≤ 2 / epsilon := by positivity
  have hsq :
      |oracleInstrumentScore e o *
        (o.2.2.2 - theta * boolReal o.2.2.1)| ^ 2 ≤
        (2 / epsilon) ^ 2 := by
    have hfactor :
        0 ≤ (2 / epsilon -
            |oracleInstrumentScore e o *
              (o.2.2.2 - theta * boolReal o.2.2.1)|) *
          (2 / epsilon +
            |oracleInstrumentScore e o *
              (o.2.2.2 - theta * boolReal o.2.2.1)|) :=
      mul_nonneg (sub_nonneg.mpr hscore)
        (add_nonneg hbound (abs_nonneg _))
    nlinarith
  rw [sq_abs] at hsq
  rw [oracleAffineScore, mul_assoc, mul_pow]
  calc
    weight o.1 ^ 2 *
        (oracleInstrumentScore e o *
          (o.2.2.2 - theta * boolReal o.2.2.1)) ^ 2 ≤
        weight o.1 ^ 2 * (2 / epsilon) ^ 2 := by
      gcongr
    _ = 4 * weight o.1 ^ 2 / epsilon ^ 2 := by ring

/-- S1.3: the paper's weight envelope implies
`w⁴ ≤ 4 k_n² w²` pointwise. -/
lemma weight_fourth_le_envelope
    (w k : ℝ) (hw : 0 ≤ w) (hwk : w ≤ 2 * k) :
    w ^ 4 ≤ 4 * k ^ 2 * w ^ 2 := by
  have hk : 0 ≤ k := by linarith
  have hfactor :
      0 ≤ (2 * k - w) * (2 * k + w) :=
    mul_nonneg (sub_nonneg.mpr hwk) (add_nonneg (by positivity) hw)
  nlinarith [sq_nonneg w]

/-- Exact mean and variance of an i.i.d. empirical average.  This is the
model-free sampling leaf used for both the score and empirical Kish moments. -/
lemma iid_empiricalAverage_mean_variance
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (n : ℕ) (hn : 0 < n)
    (F : Ω → ℝ) (hF : MemLp F 2 μ) :
    (∫ sample : Fin n → Ω,
        (n : ℝ)⁻¹ * ∑ i, F (sample i)
        ∂Measure.pi (fun _ : Fin n => μ)) = ∫ o, F o ∂μ ∧
    variance
        (fun sample : Fin n → Ω => (n : ℝ)⁻¹ * ∑ i, F (sample i))
        (Measure.pi (fun _ : Fin n => μ)) =
      (n : ℝ)⁻¹ * variance F μ := by
  exact ⟨iid_average_integral μ n hn F hF,
    iid_average_variance μ n hn F hF⟩

/-- S1.3: an i.i.d. empirical Kish average has variance at most
`4 k² kappa / n` under the paper's fourth-moment envelope. -/
lemma empiricalKish_variance_le
    (μ : Measure (SourceObs 𝒳)) [IsProbabilityMeasure μ]
    (w : 𝒳 → ℝ) (n : ℕ) (k kappa : ℝ) (hn : 0 < n)
    (hF : MemLp (fun o => w o.1 ^ 2) 2 μ)
    (hkappa : (∫ o, w o.1 ^ 2 ∂μ) = kappa)
    (hfourth : ∀ᵐ o ∂μ, w o.1 ^ 4 ≤ 4 * k ^ 2 * w o.1 ^ 2) :
    variance
        (fun sample : SourceSample 𝒳 n => empiricalKish w n sample)
        (Measure.pi (fun _ : Fin n => μ)) ≤
      4 * k ^ 2 * kappa / n := by
  exact Causalean.Stat.empiricalKishDispersion_variance_le μ
    (fun o : SourceObs 𝒳 => w o.1) n k kappa hn hF hkappa hfourth

/-- S1.4: a probability density of mean one has second moment at least one. -/
lemma one_le_secondMoment_of_mean_one
    (μ : Measure 𝒳) [IsProbabilityMeasure μ] (w : 𝒳 → ℝ)
    (hw : MemLp w 2 μ) (hmean : (∫ x, w x ∂μ) = 1) :
    1 ≤ ∫ x, w x ^ 2 ∂μ := by
  exact Causalean.Stat.one_le_secondMoment_of_mean_one μ w hw hmean

/-- A reusable Chebyshev leaf with a supplied exact mean and variance bound. -/
lemma probability_abs_sub_mean_gt_le
    {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω)
    [IsProbabilityMeasure Q] (F : Ω → ℝ) (mean v a : ℝ)
    (hF : MemLp F 2 Q) (ha : 0 < a)
    (hmean : (∫ x, F x ∂Q) = mean)
    (hvar : variance F Q ≤ v) :
    (Q {x | a < |F x - mean|}).toReal ≤ v / a ^ 2 := by
  exact Causalean.Stat.Concentration.probability_abs_sub_mean_gt_le
    Q F mean v a hF ha hmean hvar

/-- S1.4: the lower tail of empirical Kish is bounded by the paper's exact
`16 k² / (n kappa)` expression. -/
lemma empiricalKish_lower_tail_le
    (n : ℕ) (Q : Measure (SourceSample 𝒳 n)) [IsProbabilityMeasure Q]
    (w : 𝒳 → ℝ) (k kappa : ℝ)
    (hn : 0 < n) (hkappa : 0 < kappa)
    (hF : MemLp (empiricalKish w n) 2 Q)
    (hmean : (∫ sample, empiricalKish w n sample ∂Q) = kappa)
    (hvar : variance (empiricalKish w n) Q ≤
      4 * k ^ 2 * kappa / n) :
    (Q {sample | empiricalKish w n sample < kappa / 2}).toReal ≤
      16 * k ^ 2 / ((n : ℝ) * kappa) := by
  exact Causalean.Stat.empiricalKishDispersion_lower_tail_le n Q
    (fun o : SourceObs 𝒳 => w o.1) k kappa hn hkappa hF hmean hvar

/-- S1.5 order leaf: pointwise rows with a vanishing uniform error imply the
paper's exact liminf honesty statement.  Eventual inhabitation is essential
only to bound the infimum rows from above; without it an empty real-valued
indexed infimum is zero. -/
lemma abstractClass_coverage_liminf
    (cls : ℕ → TransportedArray 𝒳 → Prop)
    (coverage : ℕ → TransportedArray 𝒳 → ℝ)
    (alpha : ℝ) (delta : ℕ → ℝ)
    (hdelta : Tendsto delta atTop (𝓝 0))
    (hInhab : ∀ᶠ n in atTop, ∃ P, cls n P)
    (hcoverage : ∀ n P, cls n P →
      0 ≤ coverage n P ∧ coverage n P ≤ 1)
    (hrow : ∀ n P, cls n P →
      1 - alpha - delta n ≤ coverage n P) :
    1 - alpha ≤ Filter.liminf
      (fun n => ⨅ P : {P : TransportedArray 𝒳 // cls n P},
        coverage n P) atTop := by
  exact Causalean.Stat.classCoverage_liminf cls coverage alpha delta hdelta
    hInhab hcoverage hrow

/-- S1.6: the receipt mean/variance calculation gives exactly the paper's
`4 / (epsilon² t)` bad-slope bound. -/
lemma scoreReceiptMean_bad_probability
    {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω)
    [IsProbabilityMeasure Q] (B : Ω → ℝ)
    (n : ℕ) (epsilon mu kappa t : ℝ)
    (hn : 0 < n) (hepsilon : 0 < epsilon) (hmu : 0 < mu)
    (hkappa : 0 < kappa) (hB : MemLp B 2 Q)
    (hmean : (∫ x, B x ∂Q) = mu)
    (hvar : variance B Q ≤ kappa / (epsilon ^ 2 * n))
    (ht : t = (n : ℝ) * mu ^ 2 / kappa) :
    (Q {x | mu / 2 < |B x - mu|}).toReal ≤
      4 / (epsilon ^ 2 * t) := by
  have hcheb := probability_abs_sub_mean_gt_le Q B mu
    (kappa / (epsilon ^ 2 * n)) (mu / 2)
    hB (half_pos hmu) hmean hvar
  calc
    _ ≤ (kappa / (epsilon ^ 2 * n)) / (mu / 2) ^ 2 := hcheb
    _ = 4 / (epsilon ^ 2 * t) := by
      rw [ht]
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      field_simp [hnR.ne', hepsilon.ne', hmu.ne', hkappa.ne']
      ring

/-- S1.7: the empirical Kish statistic has exactly the population second
moment as its expectation. -/
lemma empiricalKish_mean
    (μ : Measure (SourceObs 𝒳)) [IsProbabilityMeasure μ]
    (w : 𝒳 → ℝ) (n : ℕ) (hn : 0 < n)
    (hF : MemLp (fun o => w o.1 ^ 2) 2 μ) :
    (∫ sample : SourceSample 𝒳 n, empiricalKish w n sample
        ∂Measure.pi (fun _ : Fin n => μ)) =
      ∫ o, w o.1 ^ 2 ∂μ := by
  exact Causalean.Stat.empiricalKishDispersion_mean μ
    (fun o : SourceObs 𝒳 => w o.1) n hn (hF.integrable (by norm_num))

/-- S1.8: direct uninflated affine-inversion frontier bound.  The statement is
law- and class-agnostic, so both oracle model classes feed it the same moment
facts. -/
lemma scoreInversion_expectedLength_frontier_le
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (A B K : Ω → ℝ) (n : ℕ)
    (L mu kappa q epsilon t : ℝ)
    (hL : 0 ≤ L) (hmu : 0 < mu) (hn : 0 < n)
    (hK : ∀ w, 0 ≤ K w)
    (hKint : Integrable K Q)
    (hKmean : (∫ w, K w ∂Q) = kappa)
    (hbad : (Q {w | mu / 2 < |B w - mu|}).toReal ≤ q)
    (hkappa : 0 < kappa) (hepsilon : 0 < epsilon)
    (hq : q ≤ 4 / (epsilon ^ 2 * t))
    (ht : t = (n : ℝ) * mu ^ 2 / kappa) :
    (∫ w, setLength (affineInversionSet (A w) (B w)
      (L * Real.sqrt (K w / n))) ∂Q) ≤
      max 2 (4 * L + 8 / epsilon ^ 2) *
        min 1 (t ^ (-1 / 2 : ℝ)) := by
  apply expectedLength_affineInversion_frontier_le_uninflated
    Q A B K n L mu kappa q kappa (8 / epsilon ^ 2) t
  · exact hL
  · exact hmu
  · exact hn
  · exact hK
  · exact hKint
  · exact hKmean.le
  · exact hbad
  · exact hkappa
  · positivity
  · exact le_rfl
  · calc
      q ≤ 4 / (epsilon ^ 2 * t) := hq
      _ = (8 / epsilon ^ 2) / (2 * t) := by
        have htpos : 0 < t := by rw [ht]; positivity
        field_simp [hepsilon.ne', htpos.ne']
        ring
  · exact ht

/-- The inverse-root cap is antitone on positive strengths. -/
lemma min_one_inverseSqrt_anti
    {t0 t : ℝ} (ht0 : 0 < t0) (htt : t0 ≤ t) :
    min 1 (t ^ (-1 / 2 : ℝ)) ≤
      min 1 (t0 ^ (-1 / 2 : ℝ)) := by
  exact Causalean.Stat.inverseSqrtCap_anti ht0 htt

/-- Abstract version of the paper's frontier risk, with the model class
represented by a per-index predicate. -/
noncomputable abbrev abstractClassFrontierRisk
    (cls : ℕ → TransportedArray 𝒳 → Prop)
    (strength expectedLength : ℕ → TransportedArray 𝒳 → ℝ)
    (t0 : ℝ) : ℝ :=
  Causalean.Stat.classFrontierRisk cls strength expectedLength t0

/-- S1.8 order leaf: a pointwise uninflated frontier bound collapses both the
class supremum and the asymptotic limsup at the threshold value.  The capped
`min` is retained, including both of its branches. -/
lemma abstractClassFrontierRisk_le
    (cls : ℕ → TransportedArray 𝒳 → Prop)
    (strength expectedLength : ℕ → TransportedArray 𝒳 → ℝ)
    (C0 t0 : ℝ) (hC0 : 0 ≤ C0) (ht0 : 0 < t0)
    (hLengthNonneg : ∀ n P, cls n P → 0 ≤ expectedLength n P)
    (hpoint : ∀ n P, cls n P →
      expectedLength n P ≤
        C0 * min 1 (strength n P ^ (-1 / 2 : ℝ))) :
    abstractClassFrontierRisk cls strength expectedLength t0 ≤
      C0 * min 1 (t0 ^ (-1 / 2 : ℝ)) := by
  exact Causalean.Stat.classFrontierRisk_le cls strength expectedLength
    C0 t0 hC0 ht0 hLengthNonneg hpoint

/-! ## S1.0: the contrast functions are bounded, hence integrable

`prop:compact-causal-range` is stated in the source for every `P` in the class,
with no integrability hypothesis, and its own proof (`writeup.tex:382`) applies
the change-of-measure identity to `Delta_Y` as a BOUNDED measurable function.
In the Lean encoding that boundedness is not a structure field: the contrast
functions are pinned only through the set-integral identities of
`OutcomeTransport` and `ReceiptTransport`.  It is nevertheless forced by them,
because those identities equate a set integral of the contrast with a set
integral of an integrand bounded by one. -/

/-- A measurable function whose set integrals are dominated by the measure of
the set is almost everywhere bounded by one.  Truncation to the bounded slices
`{m < f ≤ m + 1}` is what makes this hold without assuming `f` integrable: on
each slice `f` is bounded, so the set integral is genuine rather than Lean's
junk value for a non-integrable integrand. -/
lemma abs_le_one_ae_of_setIntegral_le
    {Ω : Type*} [MeasurableSpace Ω] (mu : Measure Ω)
    [IsFiniteMeasure mu] (f : Ω → ℝ) (hf : Measurable f)
    (hdom : ∀ A, MeasurableSet A →
      |∫ x in A, f x ∂mu| ≤ (mu A).toReal) :
    ∀ᵐ x ∂mu, |f x| ≤ 1 := by
  exact Causalean.Mathlib.MeasureTheory.abs_le_one_ae_of_setIntegral_le_measure
    mu f hf hdom

/-- On a global class member both population contrast functions are integrable
against the source covariate law.  This is what lets `compact_causal_range` be
applied on the global class without carrying its two integrability hypotheses
as assumptions; every regular-cell consumer already discharges them from the
finite cell support, and this is the corresponding global discharge. -/
lemma transportedIVClass_contrast_integrable
    (P : TransportedArray 𝒳) (N k : ℕ → ℕ) (c epsilon : ℝ) (n : ℕ)
    (hP : TransportedIVClass P N k c epsilon n) :
    Integrable (P.assignmentContrast n true) (sourceXLaw P n) ∧
    Integrable (P.receiptContrast n true) (sourceXLaw P n) := by
  have hFullX : Measurable (fullX : FullData 𝒳 → 𝒳) := by
    unfold fullX
    fun_prop
  haveI : IsProbabilityMeasure (P.assignedSourceLaw n) :=
    (sourceObservationFacts_of_class P N k c epsilon n hP).1
  haveI hPopulationProb :
      IsProbabilityMeasure (populationLaw P n true) := by
    rw [← (sourceObservationFacts_of_class P N k c epsilon n hP).2.2.2.1]
    exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  haveI hPopulationXProb :
      IsProbabilityMeasure (populationXLaw P n true) :=
    Measure.isProbabilityMeasure_map hFullX.aemeasurable
  have hSupportSource : ∀ᵐ o ∂populationLaw P n true,
      fullY0 o ∈ Set.Icc (0 : ℝ) 1 ∧
        fullY1 o ∈ Set.Icc (0 : ℝ) 1 :=
    ProbabilityTheory.cond_absolutelyContinuous.ae_le
      hP.fullDataSupport.2
  have hAssignmentBound :
      ∀ᵐ o ∂populationLaw P n true,
        |P.assignmentOutcome n true o -
          P.assignmentOutcome n false o| ≤ 1 := by
    filter_upwards [hSupportSource,
      hP.ivExclusion true true, hP.ivExclusion true false]
      with o ho htrue hfalse
    rw [htrue, hfalse]
    unfold derivedAssignmentOutcome potentialOutcome potentialReceipt
    cases fullD0 o <;> cases fullD1 o <;>
      simp only [Bool.false_eq_true, ↓reduceIte]
    all_goals
      rw [abs_le]
      constructor <;> linarith [ho.1.1, ho.1.2, ho.2.1, ho.2.2]
  have hReceiptBound :
      ∀ᵐ o ∂populationLaw P n true,
        |boolReal (fullD1 o) - boolReal (fullD0 o)| ≤ 1 := by
    filter_upwards with o
    cases fullD0 o <;> cases fullD1 o <;> norm_num [boolReal]
  have hAssignmentDom : ∀ A, MeasurableSet A →
      |∫ x in A, P.assignmentContrast n true x
          ∂populationXLaw P n true| ≤
        (populationXLaw P n true A).toReal := by
    intro A hA
    rw [← hP.outcomeTransport.1 true A hA]
    have hbound := norm_setIntegral_le_of_norm_le_const_ae'
      (f := fun o : FullData 𝒳 =>
        P.assignmentOutcome n true o -
          P.assignmentOutcome n false o)
      (s := {o | fullX o ∈ A}) (C := 1)
      (measure_lt_top (populationLaw P n true) _) (by
        filter_upwards [hAssignmentBound] with o ho
        intro _
        simpa [Real.norm_eq_abs] using ho)
    rw [one_mul] at hbound
    rw [populationXLaw, Measure.map_apply hFullX hA, ← measureReal_def]
    simp only [Real.norm_eq_abs] at hbound
    exact hbound
  have hReceiptDom : ∀ A, MeasurableSet A →
      |∫ x in A, P.receiptContrast n true x
          ∂populationXLaw P n true| ≤
        (populationXLaw P n true A).toReal := by
    intro A hA
    rw [← hP.receiptTransport.1 true A hA]
    have hbound := norm_setIntegral_le_of_norm_le_const_ae'
      (f := fun o : FullData 𝒳 =>
        boolReal (fullD1 o) - boolReal (fullD0 o))
      (s := {o | fullX o ∈ A}) (C := 1)
      (measure_lt_top (populationLaw P n true) _) (by
        filter_upwards [hReceiptBound] with o ho
        intro _
        simpa [Real.norm_eq_abs] using ho)
    rw [one_mul] at hbound
    rw [populationXLaw, Measure.map_apply hFullX hA, ← measureReal_def]
    simp only [Real.norm_eq_abs] at hbound
    exact hbound
  have hAssignmentAE :
      ∀ᵐ x ∂populationXLaw P n true,
        |P.assignmentContrast n true x| ≤ 1 :=
    abs_le_one_ae_of_setIntegral_le
      (populationXLaw P n true) (P.assignmentContrast n true)
      (P.assignmentContrast_measurable n true) hAssignmentDom
  have hReceiptAE :
      ∀ᵐ x ∂populationXLaw P n true,
        |P.receiptContrast n true x| ≤ 1 :=
    abs_le_one_ae_of_setIntegral_le
      (populationXLaw P n true) (P.receiptContrast n true)
      (P.receiptContrast_measurable n true) hReceiptDom
  rw [sourceXLaw_eq_populationXLaw_source P n
    (sourceObservationFacts_of_class P N k c epsilon n hP)]
  constructor
  · exact Integrable.of_bound
      (P.assignmentContrast_measurable n true).aestronglyMeasurable 1
      (by simpa [Real.norm_eq_abs] using hAssignmentAE)
  · exact Integrable.of_bound
      (P.receiptContrast_measurable n true).aestronglyMeasurable 1
      (by simpa [Real.norm_eq_abs] using hReceiptAE)

/-- The abstract atom interface reconstructs the paper's transported-IV class
for each of its members. -/
lemma ScoreRiskClassAtoms.toTransportedIVClass
    {cls : ℕ → TransportedArray 𝒳 → Prop}
    {N k : ℕ → ℕ} {c epsilon : ℝ}
    (atoms : ScoreRiskClassAtoms cls N k c epsilon)
    {n : ℕ} {P : TransportedArray 𝒳} (hP : cls n P) :
    TransportedIVClass P N k c epsilon n where
  fullDataSupport := atoms.fullDataSupport n P hP
  populationPresence := atoms.populationPresence n P hP
  twoSampleArray := atoms.twoSampleArray n P hP
  instrumentOverlap := atoms.instrumentOverlap n P hP
  sourceObservation := atoms.sourceObservation n P hP
  ivRandomization := atoms.ivRandomization n P hP
  ivExclusion := atoms.ivExclusion n P hP
  ivMonotonicity := atoms.ivMonotonicity n P hP
  outcomeTransport := atoms.outcomeTransport n P hP
  receiptTransport := atoms.receiptTransport n P hP
  targetComplierPositivity := atoms.targetComplierPositivity n P hP
  transportDomination := atoms.transportDomination n P hP
  weightEnvelope := atoms.weightEnvelope n P hP
  weightSecondMoment := atoms.weightSecondMoment n P hP
  degradingArray := atoms.degradingArray n P hP

/-- Consequently `compact_causal_range` applies to every member of any
abstract score-risk class, without an integrability hypothesis in the class
interface. -/
lemma scoreRiskClass_compact_causal_range
    {cls : ℕ → TransportedArray 𝒳 → Prop}
    {N k : ℕ → ℕ} {c epsilon : ℝ}
    (atoms : ScoreRiskClassAtoms cls N k c epsilon)
    {n : ℕ} {P : TransportedArray 𝒳} (hP : cls n P) :
    (P.deltaY n =ᵐ[sourceXLaw P n] P.assignmentContrast n true) ∧
    (P.deltaD n =ᵐ[sourceXLaw P n] P.receiptContrast n true) ∧
    transportedOutcomeITT P n =
      ∫ o, (fullY1 o - fullY0 o) *
        (if fullD1 o = true ∧ fullD0 o = false then 1 else 0)
        ∂populationLaw P n false ∧
    transportedFirstStage P n = targetComplierShare P n ∧
    transportedOutcomeITT P n / transportedFirstStage P n =
      targetCACE P n ∧
    targetCACE P n ∈ parameterSpace := by
  have hIV := atoms.toTransportedIVClass hP
  obtain ⟨hY, hD⟩ :=
    transportedIVClass_contrast_integrable P N k c epsilon n hIV
  rcases compact_causal_range P N k c epsilon n hY hD hIV with
    ⟨_, _, hOutcome, hFirst, hRatio, hRange⟩
  exact ⟨Filter.Eventually.of_forall fun _ => rfl,
    Filter.Eventually.of_forall fun _ => rfl,
    hOutcome, hFirst, hRatio, hRange⟩

end CausalSmith.Stat.TransportedLateStrengthFrontier
