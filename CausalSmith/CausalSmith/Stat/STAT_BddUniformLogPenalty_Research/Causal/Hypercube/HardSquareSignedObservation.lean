import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Causal.Hypercube.Family
import Causalean.Mathlib.InformationTheory.KLBind
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Causalean.Mathlib.InformationTheory.CommonStatisticBernoulli

/-!
# Normalized signed-observation laws on hard cells

This module isolates the measure normalization used by the hard-square
hypercube.  The quantitative KL comparison can therefore work directly with
probability laws, while the final constructor recovers the original
restricted law by multiplying by the exact cell mass.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace CausalSmith.Stat.BddUniformLogPenalty

/-- The one-observation pair `(Y,D^{±})` at a fixed interface point. -/
-- @node: signedObservationAt
noncomputable def signedObservationAt (P : A1A2Law) (x : Score)
    (z : CausalObservation) : ℝ × ℝ :=
  (observedOutcome P z, signedDistance (knownGeometry P) x (causalScore z))

/-- On the treated arm, the observed coordinate of a signed observation is
the treated potential outcome. -/
-- @node: signedObservationAt_eq_armOne
lemma signedObservationAt_eq_armOne (P : A1A2Law) (x : Score)
    (z : CausalObservation) (hz : causalScore z ∈ P.A1) :
    signedObservationAt P x z =
      (armCoord true z,
        signedDistance (knownGeometry P) x (causalScore z)) := by
  simp [signedObservationAt, observedOutcome, treatment, hz]

/-- Off the treated arm, the observed coordinate of a signed observation is
the control potential outcome. -/
-- @node: signedObservationAt_eq_armZero
lemma signedObservationAt_eq_armZero (P : A1A2Law) (x : Score)
    (z : CausalObservation) (hz : causalScore z ∉ P.A1) :
    signedObservationAt P x z =
      (armCoord false z,
        signedDistance (knownGeometry P) x (causalScore z)) := by
  simp [signedObservationAt, observedOutcome, treatment, hz]

/-- On the arm-one part of a partition, signed distance is positive
Euclidean distance. -/
-- @node: signedDistance_knownGeometry_eq_dist
lemma signedDistance_knownGeometry_eq_dist (P : A1A2Law) (x z : Score)
    (hz1 : z ∈ P.A1) (hz0 : z ∉ P.A0) :
    signedDistance (knownGeometry P) x z = dist z x := by
  simp [signedDistance, knownGeometry, hz1, hz0]

/-- On the arm-zero part of a partition, signed distance is negative
Euclidean distance. -/
-- @node: signedDistance_knownGeometry_eq_neg_dist
lemma signedDistance_knownGeometry_eq_neg_dist (P : A1A2Law) (x z : Score)
    (hz0 : z ∈ P.A0) (hz1 : z ∉ P.A1) :
    signedDistance (knownGeometry P) x z = -dist z x := by
  simp [signedDistance, knownGeometry, hz1, hz0]

-- @node: signedObservationAt_measurable
/-- The stated statistic is a measurable function of the observed data, so it is a valid random quantity. -/
lemma signedObservationAt_measurable (P : A1A2Law) (x : Score) :
    Measurable (signedObservationAt P x) := by
  have hs : Measurable (causalScore : CausalObservation → Score) := by
    unfold causalScore
    fun_prop
  have ht : Measurable (treatment P) := by
    unfold treatment
    exact (measurable_const.indicator P.A1_measurable).comp hs
  have ha1 : Measurable (armCoord true : CausalObservation → ℝ) := by
    exact (measurable_fst.comp measurable_snd :
      Measurable (fun w : CausalObservation => w.2.1))
  have ha0 : Measurable (armCoord false : CausalObservation → ℝ) := by
    exact (measurable_fst :
      Measurable (fun w : CausalObservation => w.1))
  have ho : Measurable (observedOutcome P) := by
    unfold observedOutcome
    exact (ht.mul ha1).add ((measurable_const.sub ht).mul ha0)
  have hd0 : Measurable (fun z : Score =>
      signedDistance (knownGeometry P) x z) := by
    unfold signedDistance knownGeometry
    exact ((measurable_const.indicator P.A1_measurable).sub
      (measurable_const.indicator P.A0_measurable)).mul (by fun_prop)
  exact ho.prodMk (hd0.comp hs)

/-- The sign-dependent Bernoulli success profile of the observed outcome in
the explicit hard family.  The upper arm uses the perturbed treatment
profile, while the lower arm uses the common control profile. -/
-- @node: causalHardObservedSuccessProfile
noncomputable def causalHardObservedSuccessProfile {M : ℕ} (delta w : ℝ)
    (centers : Fin M → Score) (omega : Fin M → Bool) (z : Score) : ℝ := by
  classical
  exact if z ∈ causalHardArmOne then
      causalHardTreatmentProfile delta w centers omega z
    else causalHardControlProfile z

/-- The observed hard-family Bernoulli parameter is Borel measurable. -/
-- @node: causalHardObservedSuccessProfile_measurable
lemma causalHardObservedSuccessProfile_measurable {M : ℕ} (delta w : ℝ)
    (centers : Fin M → Score) (omega : Fin M → Bool) :
    Measurable (causalHardObservedSuccessProfile delta w centers omega) := by
  unfold causalHardObservedSuccessProfile
  exact Measurable.ite causalHardArmOne_measurableSet
    (causalHardProfiles_measurable delta w centers omega).2
    (causalHardProfiles_measurable delta w centers omega).1

/-- Throughout the hard square, the observed-outcome success probability is
uniformly bounded in the middle half of the Bernoulli parameter interval. -/
-- @node: causalHardObservedSuccessProfile_mem_middleHalf
lemma causalHardObservedSuccessProfile_mem_middleHalf {M : ℕ}
    {delta w : ℝ} (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ 1 / 16)
    (hw : 0 < w) {centers : Fin M → Score}
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
    (omega : Fin M → Bool) {z : Score} (hz : z ∈ causalHardSquare) :
    causalHardObservedSuccessProfile delta w centers omega z ∈
      Icc (1 / 4 : ℝ) (3 / 4 : ℝ) := by
  classical
  unfold causalHardObservedSuccessProfile
  split_ifs
  · exact causalHardTreatmentProfile_mem_middleHalf hdelta0 hdelta hw hsep
      omega hz
  · change (1 / 2 : ℝ) ∈ Icc (1 / 4 : ℝ) (3 / 4 : ℝ)
    norm_num

/-- Signed Euclidean distance for the fixed hard-square assignment geometry,
written directly as a score statistic. -/
-- @node: causalHardSignedStatistic
noncomputable def causalHardSignedStatistic (c z : Score) : ℝ :=
  (causalHardArmOne.indicator (fun _ => (1 : ℝ)) z -
    (causalHardSquare \ causalHardArmOne).indicator (fun _ => (1 : ℝ)) z) *
      dist z c

/-- The fixed-geometry signed-distance statistic is Borel measurable. -/
-- @node: causalHardSignedStatistic_measurable
lemma causalHardSignedStatistic_measurable (c : Score) :
    Measurable (causalHardSignedStatistic c) := by
  unfold causalHardSignedStatistic
  exact ((measurable_const.indicator causalHardArmOne_measurableSet).sub
    (measurable_const.indicator
      (causalHardSquare_measurableSet.diff causalHardArmOne_measurableSet))).mul
        (by fun_prop)

/-- The signed distance carried by every explicit hard-family law is the
fixed score statistic above; in particular it is independent of the vertex. -/
-- @node: signedDistance_causalHardA1A2Law_eq_causalHardSignedStatistic
lemma signedDistance_causalHardA1A2Law_eq_causalHardSignedStatistic {M : ℕ}
    (b cA delta w : ℝ) (centers : Fin M → Score) (omega : Fin M → Bool)
    (hb : 0 < b) (hscale : 0 < cA * delta) (hcA : 8 ≤ cA)
    (hdelta : 0 < delta) (hw : 0 < w)
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
    (hcell : ∀ j, causalHardCell (centers j) w ⊆ causalHardSquare)
    (c z : Score) :
    signedDistance (knownGeometry
      (causalHardA1A2Law b cA delta w centers omega hb hscale hcA hdelta hw
        hsep hcell)) c z = causalHardSignedStatistic c z := by
  simp [signedDistance, knownGeometry, causalHardSignedStatistic,
    causalHardA1A2Law_geometry b cA delta w centers omega hb hscale hcA
      hdelta hw hsep hcell]

/-- The finite signed-observation measure obtained by restricting a hard law
to one packing cell and then applying the signed-distance compression. -/
-- @node: causalHardCellSignedObservationMeasure
noncomputable def causalHardCellSignedObservationMeasure
    (P : A1A2Law) (x : Score) (w : ℝ) : Measure (ℝ × ℝ) :=
  Measure.map (signedObservationAt P x)
    (P.law.restrict {z | causalScore z ∈ causalHardCell x w})

-- @node: causalHardCellSignedObservationMeasure_isFiniteMeasure
/-- The stated signed-observation measure has finite total mass. -/
noncomputable instance causalHardCellSignedObservationMeasure_isFiniteMeasure
    (P : A1A2Law) (x : Score) (w : ℝ) :
    IsFiniteMeasure (causalHardCellSignedObservationMeasure P x w) := by
  letI : IsProbabilityMeasure P.law := P.law_isProbability
  constructor
  rw [causalHardCellSignedObservationMeasure,
    Measure.map_apply (signedObservationAt_measurable P x) MeasurableSet.univ,
    preimage_univ]
  exact lt_of_le_of_lt (Measure.restrict_apply_le _ _) (measure_lt_top P.law univ)

/-- The normalized probability law of a signed observation conditional on
the observation lying in the selected hard cell. -/
-- @node: causalHardCellSignedObservationLaw
noncomputable def causalHardCellSignedObservationLaw
    (P : A1A2Law) (x : Score) (w : ℝ) : Measure (ℝ × ℝ) :=
  letI : IsProbabilityMeasure P.law := P.law_isProbability
  let μ : FiniteMeasure (ℝ × ℝ) :=
    ⟨causalHardCellSignedObservationMeasure P x w, inferInstance⟩
  μ.normalize

-- @node: causalHardCellSignedObservationLaw_isProbabilityMeasure
/-- The stated experiment law has total mass one and therefore defines a probability distribution. -/
noncomputable instance causalHardCellSignedObservationLaw_isProbabilityMeasure
    (P : A1A2Law) (x : Score) (w : ℝ) :
    IsProbabilityMeasure (causalHardCellSignedObservationLaw P x w) := by
  unfold causalHardCellSignedObservationLaw
  infer_instance

/-- A positive exact cell mass lets normalization be undone without a
zero-measure fallback branch. -/
-- @node: causalHardCellSignedObservationMeasure_eq_mass_smul_law
lemma causalHardCellSignedObservationMeasure_eq_mass_smul_law
    (P : A1A2Law) (x : Score) (w ρ : ℝ) (hρ : 0 < ρ)
    (hmass : P.law {z | causalScore z ∈ causalHardCell x w} =
      ENNReal.ofReal ρ) :
    causalHardCellSignedObservationMeasure P x w =
      ENNReal.ofReal ρ • causalHardCellSignedObservationLaw P x w := by
  letI : IsProbabilityMeasure P.law := P.law_isProbability
  let μ : FiniteMeasure (ℝ × ℝ) :=
    ⟨causalHardCellSignedObservationMeasure P x w, inferInstance⟩
  have hmeas : Measurable (signedObservationAt P x) := by
    exact signedObservationAt_measurable P x
  have hcell : MeasurableSet {z | causalScore z ∈ causalHardCell x w} := by
    exact Metric.isClosed_closedBall.measurableSet.preimage (by
      unfold causalScore
      fun_prop)
  have hμmass : (μ : Measure (ℝ × ℝ)) Set.univ = ENNReal.ofReal ρ := by
    rw [show (μ : Measure (ℝ × ℝ)) =
      causalHardCellSignedObservationMeasure P x w by rfl]
    rw [causalHardCellSignedObservationMeasure, Measure.map_apply hmeas
      MeasurableSet.univ, preimage_univ]
    simpa [Measure.restrict_apply, hcell] using hmass
  have hμ0 : μ ≠ 0 := by
    intro hz
    have : (μ : Measure (ℝ × ℝ)) Set.univ = 0 := by simp [hz]
    rw [hμmass, ENNReal.ofReal_eq_zero] at this
    linarith
  have hmassNN : (μ.mass : ℝ≥0∞) = ENNReal.ofReal ρ := by
    rw [FiniteMeasure.ennreal_mass, hμmass]
  change (μ : Measure (ℝ × ℝ)) =
    ENNReal.ofReal ρ • (μ.normalize : Measure (ℝ × ℝ))
  rw [μ.toMeasure_normalize_eq_of_nonzero hμ0]
  ext s hs
  rw [Measure.smul_apply, Measure.smul_apply]
  change (μ : Measure (ℝ × ℝ)) s =
    ENNReal.ofReal ρ * ((↑(μ.mass⁻¹) : ℝ≥0∞) * (μ : Measure (ℝ × ℝ)) s)
  have hmass0 : μ.mass ≠ 0 := by
    intro hz
    rw [hz, ENNReal.coe_zero] at hmassNN
    have := ENNReal.ofReal_pos.mpr hρ
    exact this.ne' hmassNN.symm
  rw [← hmassNN, ENNReal.coe_inv hmass0, ← mul_assoc,
    ENNReal.mul_inv_cancel (ENNReal.coe_ne_zero.mpr hmass0) ENNReal.coe_ne_top,
    one_mul]

/-- Equality after multiplication by a strictly positive finite cell mass
can be cancelled.  This is the normalization bridge used when a geometric
calculation first identifies the signed-radius marginals of the restricted
hard-cell measures. -/
-- @node: measure_eq_of_pos_ofReal_smul_eq
lemma measure_eq_of_pos_ofReal_smul_eq {A : Type*} [MeasurableSpace A]
    (mu nu : Measure A) {rho : ℝ} (hrho : 0 < rho)
    (h : ENNReal.ofReal rho • mu = ENNReal.ofReal rho • nu) :
    mu = nu := by
  ext s hs
  have hs_eq := congrArg (fun m : Measure A => m s) h
  simp only [Measure.smul_apply] at hs_eq
  let a := ENNReal.ofReal rho
  change a * mu s = a * nu s at hs_eq
  have ha0 : a ≠ 0 := (ENNReal.ofReal_pos.mpr hrho).ne'
  have hatop : a ≠ ⊤ := ENNReal.ofReal_ne_top
  by_cases hmutop : mu s = ⊤
  · have hprod : a * nu s = ⊤ := by
      rw [← hs_eq]
      simp [a, hmutop, ha0]
    have hnutop : nu s = ⊤ := by
      rcases ENNReal.mul_eq_top.mp hprod with hcase | hcase
      · exact hcase.2
      · exact (hatop hcase.1).elim
    exact hmutop.trans hnutop.symm
  · have hnutop : nu s ≠ ⊤ := by
      intro hnu
      have hleft : a * mu s ≠ ⊤ := ENNReal.mul_ne_top hatop hmutop
      apply hleft
      rw [hs_eq, hnu]
      simp [a, ha0]
    rw [← ENNReal.toReal_eq_toReal_iff' hmutop hnutop]
    have hreal := congrArg ENNReal.toReal hs_eq
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul] at hreal
    exact mul_left_cancel₀ (ENNReal.toReal_pos ha0 hatop).ne' hreal

/-- On a fixed hard cell, equality of the underlying restricted laws implies
equality of the normalized signed-observation laws.  This is the locality
bridge that makes the final conditional law depend only on the cell bit. -/
-- @node: causalHardCellSignedObservationLaw_eq_of_restrict_eq
lemma causalHardCellSignedObservationLaw_eq_of_restrict_eq
    (P P' : A1A2Law) (x : Score) (w ρ : ℝ) (hρ : 0 < ρ)
    (hmass : P.law {z | causalScore z ∈ causalHardCell x w} =
      ENNReal.ofReal ρ)
    (hmass' : P'.law {z | causalScore z ∈ causalHardCell x w} =
      ENNReal.ofReal ρ)
    (hrestrict : P.law.restrict
        {z | causalScore z ∈ causalHardCell x w} =
      P'.law.restrict {z | causalScore z ∈ causalHardCell x w})
    (hobs : signedObservationAt P x = signedObservationAt P' x) :
    causalHardCellSignedObservationLaw P x w =
      causalHardCellSignedObservationLaw P' x w := by
  apply measure_eq_of_pos_ofReal_smul_eq _ _ hρ
  rw [← causalHardCellSignedObservationMeasure_eq_mass_smul_law
      P x w ρ hρ hmass,
    ← causalHardCellSignedObservationMeasure_eq_mass_smul_law
      P' x w ρ hρ hmass']
  unfold causalHardCellSignedObservationMeasure
  rw [hrestrict, hobs]

export Causalean.Mathlib.InformationTheory (commonStatisticBernoulliKernel commonStatisticBernoulliKernel_isMarkovKernel commonStatisticBernoulli_klDiv_le_of_localized_parameter commonStatisticBernoulliOutcome_klDiv_le_of_localized_parameter)

end CausalSmith.Stat.BddUniformLogPenalty
