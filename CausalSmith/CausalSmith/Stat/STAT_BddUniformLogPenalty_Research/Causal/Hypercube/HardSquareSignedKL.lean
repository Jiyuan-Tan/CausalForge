import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Causal.Hypercube.CommonStatisticBernoulli
import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Causal.Hypercube.HardSquareSignedCancellation

/-!
# Signed-observation KL certificate for the hard square

This module identifies the observed outcome after signed-distance compression
with an explicit Bernoulli mixture over the score law.  It then combines the
half-disc cancellation estimate with the common-statistic Bernoulli KL bound.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace CausalSmith.Stat.BddUniformLogPenalty

/-- Inside an arbitrary separated packing cell, switching its active bit from
false to true changes the regression-density product by the radial bump plus
the angular cross term.  Unlike the older lower-support-edge identity, this
version applies to the interior hard-square cells. -/
-- @node: packingRegression_mul_density_enable_cell_identity
lemma packingRegression_mul_density_enable_cell_identity
    {M : ℕ} (j : Fin M) {b cA delta w : ℝ} (centers : Fin M → Score)
    (hw : 0 < w)
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
    (omega : Fin M → Bool) (hj : omega j = false) {x : Score}
    (hx : x ∈ Metric.closedBall (centers j) w) :
    packingRegression b delta w centers (Function.update omega j true) x *
          packingAngularDensity b cA delta w centers
            (Function.update omega j true) x -
        packingRegression b delta w centers omega x *
          packingAngularDensity b cA delta w centers omega x =
      localizedPackingBump delta w (centers j) x +
        (packingAffineBaseline b x +
            localizedPackingBump delta w (centers j) x) *
          packingAngularTerm b cA delta w (centers j) x := by
  have hfar : ∀ i : Fin M, i ≠ j → w ≤ dist x (centers i) := by
    intro i hij
    have htri : dist (centers i) (centers j) ≤
        dist (centers i) x + dist x (centers j) := dist_triangle _ _ _
    have hs := hsep i j hij
    rw [Metric.mem_closedBall] at hx
    rw [dist_comm (centers i) x] at htri
    linarith
  have hregOn : packingRegression b delta w centers
      (Function.update omega j true) x =
        packingAffineBaseline b x + localizedPackingBump delta w (centers j) x := by
    unfold packingRegression
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      rw [localizedPackingBump_eq_zero_of_bandwidth_le_dist hw (hfar i hij)]
      simp [Function.update, hij]
    · simp
  have hregOff : packingRegression b delta w centers omega x =
      packingAffineBaseline b x := by
    unfold packingRegression
    rw [Finset.sum_eq_zero]
    · simp
    · intro i _
      by_cases hij : i = j
      · subst i
        simp [hj]
      · rw [localizedPackingBump_eq_zero_of_bandwidth_le_dist hw (hfar i hij)]
        simp
  have hdensOn : packingAngularDensity b cA delta w centers
      (Function.update omega j true) x =
        1 + packingAngularTerm b cA delta w (centers j) x := by
    unfold packingAngularDensity
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      rw [packingAngularTerm_eq_zero_of_bandwidth_le_dist hw (hfar i hij)]
      simp [Function.update, hij]
    · simp
  have hdensOff : packingAngularDensity b cA delta w centers omega x = 1 := by
    unfold packingAngularDensity
    rw [Finset.sum_eq_zero]
    · simp
    · intro i _
      by_cases hij : i = j
      · subst i
        simp [hj]
      · rw [packingAngularTerm_eq_zero_of_bandwidth_le_dist hw (hfar i hij)]
        simp
  rw [hregOn, hregOff, hdensOn, hdensOff]
  ring

/-- The arbitrary-cell enable identity in the radial and direction-cosine
coordinates used by the signed half-disc cancellation estimate. -/
-- @node: packingRegression_mul_density_enable_cell_radial_identity
lemma packingRegression_mul_density_enable_cell_radial_identity
    {M : ℕ} (j : Fin M) {b cA delta w : ℝ} (centers : Fin M → Score)
    (hw : 0 < w)
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
    (omega : Fin M → Bool) (hj : omega j = false) {x : Score}
    (hx : x ∈ Metric.closedBall (centers j) w) :
    packingRegression b delta w centers (Function.update omega j true) x *
          packingAngularDensity b cA delta w centers
            (Function.update omega j true) x -
        packingRegression b delta w centers omega x *
          packingAngularDensity b cA delta w centers omega x =
      delta * angularRadialProfile w (dist x (centers j)) +
        (packingAffineBaseline b x +
            delta * angularRadialProfile w (dist x (centers j))) *
          angularTilt b cA delta w (dist x (centers j)) *
          ((scoreCoordinates x - scoreCoordinates (centers j)).1 /
            dist x (centers j)) := by
  rw [packingRegression_mul_density_enable_cell_identity j centers hw hsep
      omega hj hx, localizedPackingBump_eq_delta_mul_angularRadialProfile]
  rw [packingAngularTerm, packingDirectionCos_eq_planarFirst_div_radius,
    planarRadius_scoreCoordinates_sub]
  ring

/-- The success profile obtained by selecting the treatment profile on a
measurable arm and the control profile off that arm. -/
-- @node: selectedArmSuccessProfile
noncomputable def selectedArmSuccessProfile
    (A : Set Score) (p0 p1 : Score → ℝ) (x : Score) : ℝ := by
  classical
  exact if x ∈ A then p1 x else p0 x

-- @node: selectedArmSuccessProfile_measurable
/-- The stated statistic is a measurable function of the observed data, so it is a valid random quantity. -/
lemma selectedArmSuccessProfile_measurable
    {A : Set Score} (hA : MeasurableSet A) {p0 p1 : Score → ℝ}
    (hp0 : Measurable p0) (hp1 : Measurable p1) :
    Measurable (selectedArmSuccessProfile A p0 p1) := by
  classical
  unfold selectedArmSuccessProfile
  exact Measurable.ite hA hp1 hp0

/-- The potential outcome selected by membership of the score in an arm. -/
-- @node: selectedArmOutcome
noncomputable def selectedArmOutcome
    (A : Set Score) (z : CausalObservation) : ℝ := by
  classical
  exact if causalScore z ∈ A then armCoord true z else armCoord false z

/-- Restricting an explicit two-Bernoulli potential-outcome law to a score set
and selecting the outcome according to a measurable arm gives the corresponding
piecewise Bernoulli composition product. -/
-- @node: causalBernoulliPotentialOutcomeMeasure_restrict_map_selected
lemma causalBernoulliPotentialOutcomeMeasure_restrict_map_selected
    (nu : Measure Score) [IsProbabilityMeasure nu]
    (p0 p1 : Score → ℝ) (hp0 : Measurable p0) (hp1 : Measurable p1)
    (hp0lo : ∀ x, 0 ≤ p0 x) (hp0hi : ∀ x, p0 x ≤ 1)
    (hp1lo : ∀ x, 0 ≤ p1 x) (hp1hi : ∀ x, p1 x ≤ 1)
    (A C : Set Score) (hA : MeasurableSet A) (hC : MeasurableSet C)
    (stat : Score → ℝ) (hstat : Measurable stat) :
    let p : Score → ℝ := selectedArmSuccessProfile A p0 p1
    let hp : Measurable p := selectedArmSuccessProfile_measurable hA hp0 hp1
    Measure.map
        (fun z : CausalObservation => (selectedArmOutcome A z,
          stat (causalScore z)))
        ((causalBernoulliPotentialOutcomeMeasure nu p0 p1 hp0 hp1).restrict
          {z | causalScore z ∈ C}) =
      Measure.map (fun z : Score × ℝ => (z.2, stat z.1))
        (Measure.compProd (nu.restrict C) (causalSelectedBernoulliKernel p hp)) := by
  classical
  dsimp only
  let k0 := causalSelectedBernoulliKernel p0 hp0
  let k1 := causalSelectedBernoulliKernel p1 hp1
  let p : Score → ℝ := selectedArmSuccessProfile A p0 p1
  let hp : Measurable p := selectedArmSuccessProfile_measurable hA hp0 hp1
  let k := causalSelectedBernoulliKernel p hp
  letI : IsMarkovKernel k0 :=
    causalSelectedBernoulliKernel_isMarkovKernel p0 hp0 hp0lo hp0hi
  letI : IsMarkovKernel k1 :=
    causalSelectedBernoulliKernel_isMarkovKernel p1 hp1 hp1lo hp1hi
  letI : IsMarkovKernel k :=
    causalSelectedBernoulliKernel_isMarkovKernel p hp
      (fun x => by simp only [p, selectedArmSuccessProfile]; split_ifs <;> simp_all)
      (fun x => by simp only [p, selectedArmSuccessProfile]; split_ifs <;> simp_all)
  have hscore : Measurable (causalScore : CausalObservation → Score) := by
    unfold causalScore
    fun_prop
  have harm1 : Measurable (armCoord true : CausalObservation → ℝ) := by
    exact (measurable_fst.comp measurable_snd :
      Measurable (fun w : CausalObservation => w.2.1))
  have harm0 : Measurable (armCoord false : CausalObservation → ℝ) := by
    exact (measurable_fst :
      Measurable (fun w : CausalObservation => w.1))
  have hselected : Measurable (selectedArmOutcome A) := by
    unfold selectedArmOutcome
    exact Measurable.ite (hA.preimage hscore) harm1 harm0
  have hobs : Measurable (fun z : CausalObservation =>
      (selectedArmOutcome A z, stat (causalScore z))) :=
    hselected.prodMk (hstat.comp hscore)
  ext S hS
  rw [Measure.map_apply hobs hS]
  rw [Measure.restrict_apply (hS.preimage hobs)]
  unfold causalBernoulliPotentialOutcomeMeasure
  have htarget : MeasurableSet
      ((fun z : CausalObservation =>
        (selectedArmOutcome A z, stat (causalScore z))) ⁻¹' S ∩
          {z | causalScore z ∈ C}) :=
    (hS.preimage hobs).inter (hC.preimage hscore)
  rw [Measure.map_apply (by fun_prop) htarget]
  have hout : Measurable (fun z : Score × ℝ => (z.2, stat z.1)) := by
    fun_prop
  have hreorder : Measurable (fun z : Score × (ℝ × ℝ) =>
      (z.2.1, z.2.2, z.1)) := by fun_prop
  rw [Measure.map_apply hout hS]
  rw [Measure.compProd_apply, Measure.compProd_apply]
  rw [← lintegral_indicator hC]
  · apply lintegral_congr
    intro x
    by_cases hxC : x ∈ C
    · rw [indicator_of_mem hxC]
      by_cases hxA : x ∈ A
      · have hmap := Kernel.snd_prod k0 k1
        have heval := congrArg (fun q : Kernel Score ℝ => q x) hmap
        have hB : MeasurableSet ((fun y : ℝ => (y, stat x)) ⁻¹' S) :=
          hS.preimage (measurable_id.prodMk measurable_const)
        have hset := congrArg (fun m : Measure ℝ =>
          m ((fun y : ℝ => (y, stat x)) ⁻¹' S)) heval
        change (Kernel.snd (Kernel.prod k0 k1) x)
          ((fun y : ℝ => (y, stat x)) ⁻¹' S) =
            k1 x ((fun y : ℝ => (y, stat x)) ⁻¹' S) at hset
        rw [Kernel.snd_apply' _ x hB] at hset
        have hpre :
            Prod.mk x ⁻¹' ((fun z : Score × (ℝ × ℝ) => (z.2.1, z.2.2, z.1)) ⁻¹'
              ((fun z : CausalObservation =>
                (selectedArmOutcome A z, stat (causalScore z))) ⁻¹' S ∩
                  {z | causalScore z ∈ C})) =
              Prod.snd ⁻¹' ((fun y : ℝ => (y, stat x)) ⁻¹' S) := by
          ext yy
          simp [selectedArmOutcome, causalScore, armCoord, hxA, hxC]
        rw [hpre]
        change ((k0 ×ₖ k1) x) (Prod.snd ⁻¹' ((fun y : ℝ => (y, stat x)) ⁻¹' S)) =
          (Causalean.Mathlib.Probability.bernoulliLaw
              (if x ∈ A then p1 x else p0 x))
            (Prod.mk x ⁻¹' ((fun z : Score × ℝ => (z.2, stat z.1)) ⁻¹' S))
        rw [if_pos hxA]
        exact hset
      · have hmap := Kernel.fst_prod k0 k1
        have heval := congrArg (fun q : Kernel Score ℝ => q x) hmap
        have hB : MeasurableSet ((fun y : ℝ => (y, stat x)) ⁻¹' S) :=
          hS.preimage (measurable_id.prodMk measurable_const)
        have hset := congrArg (fun m : Measure ℝ =>
          m ((fun y : ℝ => (y, stat x)) ⁻¹' S)) heval
        change (Kernel.fst (Kernel.prod k0 k1) x)
          ((fun y : ℝ => (y, stat x)) ⁻¹' S) =
            k0 x ((fun y : ℝ => (y, stat x)) ⁻¹' S) at hset
        rw [Kernel.fst_apply' _ x hB] at hset
        have hpre :
            Prod.mk x ⁻¹' ((fun z : Score × (ℝ × ℝ) => (z.2.1, z.2.2, z.1)) ⁻¹'
              ((fun z : CausalObservation =>
                (selectedArmOutcome A z, stat (causalScore z))) ⁻¹' S ∩
                  {z | causalScore z ∈ C})) =
              Prod.fst ⁻¹' ((fun y : ℝ => (y, stat x)) ⁻¹' S) := by
          ext yy
          simp [selectedArmOutcome, causalScore, armCoord, hxA, hxC]
        rw [hpre]
        change ((k0 ×ₖ k1) x) (Prod.fst ⁻¹' ((fun y : ℝ => (y, stat x)) ⁻¹' S)) =
          (Causalean.Mathlib.Probability.bernoulliLaw
              (if x ∈ A then p1 x else p0 x))
            (Prod.mk x ⁻¹' ((fun z : Score × ℝ => (z.2, stat z.1)) ⁻¹' S))
        rw [if_neg hxA]
        exact hset
    · have : x ∉ C := hxC
      have hpre : Prod.mk x ⁻¹' ((fun z : Score × (ℝ × ℝ) => (z.2.1, z.2.2, z.1)) ⁻¹' ((fun z : CausalObservation =>
          (selectedArmOutcome A z, stat (causalScore z))) ⁻¹' S ∩
            {z | causalScore z ∈ C})) = ∅ := by
        ext yy
        simp [causalScore, hxC]
      rw [hpre, measure_empty]
      rw [indicator_of_notMem hxC]
  · exact hS.preimage hout
  · exact htarget.preimage hreorder

/-- On a hard cell, the raw signed observation measure is the explicit
piecewise-Bernoulli composition product over the restricted score design. -/
-- @node: causalHardCellSignedObservationMeasure_eq_scoreBernoulli
lemma causalHardCellSignedObservationMeasure_eq_scoreBernoulli
    {M : ℕ} (j : Fin M) (b cA delta w : ℝ)
    (centers : Fin M → Score) (omega : Fin M → Bool)
    (hb : 0 < b) (hscale : 0 < cA * delta) (hcA : 8 ≤ cA)
    (hdelta : 0 < delta) (hw : 0 < w)
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
    (hcell : ∀ k, causalHardCell (centers k) w ⊆ causalHardSquare) :
    let nu := causalHardScoreMeasure b cA delta w centers omega
    let p := causalHardObservedSuccessProfile delta w centers omega
    let hp := causalHardObservedSuccessProfile_measurable delta w centers omega
    let P := causalHardA1A2Law b cA delta w centers omega hb hscale hcA
      hdelta hw hsep hcell
    causalHardCellSignedObservationMeasure P (centers j) w =
      Measure.map
        (fun z : Score × ℝ => (z.2, causalHardSignedStatistic (centers j) z.1))
        (Measure.compProd (nu.restrict (causalHardCell (centers j) w))
          (causalSelectedBernoulliKernel p hp)) := by
  dsimp only
  let nu := causalHardScoreMeasure b cA delta w centers omega
  let p0 := causalHardControlProfile
  let p1 := causalHardTreatmentProfile delta w centers omega
  have hpPair := causalHardProfiles_measurable delta w centers omega
  letI : IsProbabilityMeasure nu :=
    causalHardScoreMeasure_isProbabilityMeasure centers omega hb hscale hcA
      hdelta hw hsep hcell
  have hbase := causalBernoulliPotentialOutcomeMeasure_restrict_map_selected
    nu p0 p1 hpPair.1 hpPair.2
    (fun x => (causalHardProfiles_mem_unitInterval delta w centers omega x).1.1)
    (fun x => (causalHardProfiles_mem_unitInterval delta w centers omega x).1.2)
    (fun x => (causalHardProfiles_mem_unitInterval delta w centers omega x).2.1)
    (fun x => (causalHardProfiles_mem_unitInterval delta w centers omega x).2.2)
    causalHardArmOne (causalHardCell (centers j) w)
    causalHardArmOne_measurableSet Metric.isClosed_closedBall.measurableSet
    (causalHardSignedStatistic (centers j))
    (causalHardSignedStatistic_measurable (centers j))
  change _ = _ at hbase
  let P := causalHardA1A2Law b cA delta w centers omega hb hscale hcA
    hdelta hw hsep hcell
  have hleft : (fun z : CausalObservation =>
      (selectedArmOutcome causalHardArmOne z,
        causalHardSignedStatistic (centers j) (causalScore z))) =
      signedObservationAt P (centers j) := by
    funext z
    rw [← signedDistance_causalHardA1A2Law_eq_causalHardSignedStatistic
      b cA delta w centers omega hb hscale hcA hdelta hw hsep hcell]
    by_cases hz : causalScore z ∈ causalHardArmOne
    · simp [P, selectedArmOutcome, signedObservationAt, observedOutcome,
        treatment, causalHardA1A2Law, causalBernoulliA1A2Law, hz]
    · simp [P, selectedArmOutcome, signedObservationAt, observedOutcome,
        treatment, causalHardA1A2Law, causalBernoulliA1A2Law, hz]
  have hparam : selectedArmSuccessProfile causalHardArmOne p0 p1 =
      causalHardObservedSuccessProfile delta w centers omega := by
    funext x
    rfl
  have hk : causalSelectedBernoulliKernel
      (selectedArmSuccessProfile causalHardArmOne p0 p1)
        (selectedArmSuccessProfile_measurable causalHardArmOne_measurableSet
          hpPair.1 hpPair.2) =
      causalSelectedBernoulliKernel
        (causalHardObservedSuccessProfile delta w centers omega)
        (causalHardObservedSuccessProfile_measurable delta w centers omega) := by
    cases hparam
    rfl
  rw [hleft, hk] at hbase
  simpa [causalHardCellSignedObservationMeasure, P, causalHardA1A2Law,
    causalBernoulliA1A2Law] using hbase

/-- The normalized signed-observation law on a hard cell depends on a vertex
only through that cell's bit. -/
-- @node: causalHardCellSignedObservationLaw_eq_of_bit_eq
lemma causalHardCellSignedObservationLaw_eq_of_bit_eq
    {M : ℕ} (j : Fin M) (b cA delta w : ℝ)
    (centers : Fin M → Score) (omega omega' : Fin M → Bool)
    (hb : 0 < b) (hscale : 0 < cA * delta) (hcA : 8 ≤ cA)
    (hdelta : 0 < delta) (hw : 0 < w)
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
    (hcell : ∀ k, causalHardCell (centers k) w ⊆ causalHardSquare)
    (hbit : omega j = omega' j) :
    let P := causalHardA1A2Law b cA delta w centers omega hb hscale hcA
      hdelta hw hsep hcell
    let P' := causalHardA1A2Law b cA delta w centers omega' hb hscale hcA
      hdelta hw hsep hcell
    causalHardCellSignedObservationLaw P (centers j) w =
      causalHardCellSignedObservationLaw P' (centers j) w := by
  dsimp only
  let P := causalHardA1A2Law b cA delta w centers omega hb hscale hcA
    hdelta hw hsep hcell
  let P' := causalHardA1A2Law b cA delta w centers omega' hb hscale hcA
    hdelta hw hsep hcell
  let rho : ℝ := Real.pi * w ^ 2 / 36
  have hrho : 0 < rho := by
    dsimp [rho]
    positivity
  apply causalHardCellSignedObservationLaw_eq_of_restrict_eq
    P P' (centers j) w rho hrho
  · exact causalHardA1A2Law_cell_mass j b cA delta w centers omega hb hscale
      hcA hdelta hw hsep hcell
  · exact causalHardA1A2Law_cell_mass j b cA delta w centers omega' hb hscale
      hcA hdelta hw hsep hcell
  · exact causalHardA1A2Law_restrict_cell_eq hb hscale hcA hdelta hw hsep
      hcell hbit
  · funext z
    have hsigned : signedDistance (knownGeometry P) (centers j) (causalScore z) =
        signedDistance (knownGeometry P') (centers j) (causalScore z) := by
      rw [signedDistance_causalHardA1A2Law_eq_causalHardSignedStatistic
          b cA delta w centers omega hb hscale hcA hdelta hw hsep hcell,
        signedDistance_causalHardA1A2Law_eq_causalHardSignedStatistic
          b cA delta w centers omega' hb hscale hcA hdelta hw hsep hcell]
    have hA : P.A1 = P'.A1 := by
      simp [P, P', causalHardA1A2Law, causalBernoulliA1A2Law]
    simp only [signedObservationAt, Prod.mk.injEq]
    exact ⟨by simp [observedOutcome, treatment, hA], hsigned⟩

/-- The hard family admits a bit-indexed choice of normalized cell laws, and
every vertex's raw signed-observation measure is its common cell mass times
the law selected by the corresponding bit. -/
-- @node: causalHardCellSignedObservationLaw_vertex_package
lemma causalHardCellSignedObservationLaw_vertex_package
    {M : ℕ} (b cA delta w : ℝ) (centers : Fin M → Score)
    (hb : 0 < b) (hscale : 0 < cA * delta) (hcA : 8 ≤ cA)
    (hdelta : 0 < delta) (hw : 0 < w)
    (hsep : ∀ i k, i ≠ k → 3 * w ≤ dist (centers i) (centers k))
    (hcell : ∀ k, causalHardCell (centers k) w ⊆ causalHardSquare) :
    ∃ Q : Fin M → Bool → Measure (ℝ × ℝ),
      (∀ j bit, IsProbabilityMeasure (Q j bit)) ∧
      ∀ omega j,
        causalHardCellSignedObservationMeasure
            (causalHardA1A2Law b cA delta w centers omega hb hscale hcA
              hdelta hw hsep hcell) (centers j) w =
          ENNReal.ofReal (Real.pi * w ^ 2 / 36) • Q j (omega j) := by
  let representative (j : Fin M) (bit : Bool) : Fin M → Bool :=
    fun k => if k = j then bit else false
  let P (omega : Fin M → Bool) :=
    causalHardA1A2Law b cA delta w centers omega hb hscale hcA hdelta hw
      hsep hcell
  let Q (j : Fin M) (bit : Bool) : Measure (ℝ × ℝ) :=
    causalHardCellSignedObservationLaw (P (representative j bit))
      (centers j) w
  refine ⟨Q, ?_, ?_⟩
  · intro j bit
    dsimp [Q]
    infer_instance
  · intro omega j
    have hbit : omega j = representative j (omega j) j := by
      simp [representative]
    have hlaw := causalHardCellSignedObservationLaw_eq_of_bit_eq
      j b cA delta w centers omega (representative j (omega j)) hb hscale
      hcA hdelta hw hsep hcell hbit
    have hmass := causalHardA1A2Law_cell_mass j b cA delta w centers omega hb
      hscale hcA hdelta hw hsep hcell
    rw [causalHardCellSignedObservationMeasure_eq_mass_smul_law
      (P omega) (centers j) w (Real.pi * w ^ 2 / 36) (by positivity) hmass]
    change _ = ENNReal.ofReal (Real.pi * w ^ 2 / 36) • Q j (omega j)
    rw [hlaw]

end CausalSmith.Stat.BddUniformLogPenalty
