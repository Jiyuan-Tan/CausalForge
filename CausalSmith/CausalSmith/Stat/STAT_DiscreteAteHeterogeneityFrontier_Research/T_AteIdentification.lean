/- Finite-cell identification of the causal ATE. -/

import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Basic
import Causalean.Mathlib.MeasureTheory.PartitionIntegral

namespace CausalSmith.Stat.DiscreteAteHeterogeneityFrontier

open scoped BigOperators

open MeasureTheory Set

-- @node: fullObs_measurable_x
/-- [the full-data covariate coordinate is measurable](goal). -/
lemma fullObs_measurable_x {d : ℕ} : Measurable (FullObs.x : FullObs d → Fin d) := by
  exact (show Measurable (fun z : FullObs d => (z.x, z.a, z.y0, z.y1, z.y)) by
    rw [measurable_iff_comap_le]
    rfl).fst

-- @node: fullObs_measurable_a
/-- [the full-data treatment coordinate is measurable](goal). -/
lemma fullObs_measurable_a {d : ℕ} : Measurable (FullObs.a : FullObs d → Bool) := by
  exact (show Measurable (fun z : FullObs d => (z.x, z.a, z.y0, z.y1, z.y)) by
    rw [measurable_iff_comap_le]
    rfl).snd.fst

-- @node: fullObs_measurable_y0
/-- [the control potential-outcome coordinate is measurable](goal). -/
lemma fullObs_measurable_y0 {d : ℕ} : Measurable (FullObs.y0 : FullObs d → ℝ) := by
  exact (show Measurable (fun z : FullObs d => (z.x, z.a, z.y0, z.y1, z.y)) by
    rw [measurable_iff_comap_le]
    rfl).snd.snd.fst

-- @node: fullObs_measurable_y1
/-- [the treated potential-outcome coordinate is measurable](goal). -/
lemma fullObs_measurable_y1 {d : ℕ} : Measurable (FullObs.y1 : FullObs d → ℝ) := by
  exact (show Measurable (fun z : FullObs d => (z.x, z.a, z.y0, z.y1, z.y)) by
    rw [measurable_iff_comap_le]
    rfl).snd.snd.snd.fst

-- @node: fullObs_measurable_y
/-- [the full-data observed-outcome coordinate is measurable](goal). -/
lemma fullObs_measurable_y {d : ℕ} : Measurable (FullObs.y : FullObs d → ℝ) := by
  exact (show Measurable (fun z : FullObs d => (z.x, z.a, z.y0, z.y1, z.y)) by
    rw [measurable_iff_comap_le]
    rfl).snd.snd.snd.snd

-- @node: obs_measurable_x
/-- [the observed covariate coordinate is measurable](goal). -/
lemma obs_measurable_x {d : ℕ} : Measurable (Obs.x : Obs d → Fin d) := by
  exact (show Measurable (fun o : Obs d => (o.x, o.a, o.y)) by
    rw [measurable_iff_comap_le]
    rfl).fst

-- @node: obs_measurable_a
/-- [the observed treatment coordinate is measurable](goal). -/
lemma obs_measurable_a {d : ℕ} : Measurable (Obs.a : Obs d → Bool) := by
  exact (show Measurable (fun o : Obs d => (o.x, o.a, o.y)) by
    rw [measurable_iff_comap_le]
    rfl).snd.fst

-- @node: obs_measurable_y
/-- [the observed outcome coordinate is measurable](goal). -/
lemma obs_measurable_y {d : ℕ} : Measurable (Obs.y : Obs d → ℝ) := by
  exact (show Measurable (fun o : Obs d => (o.x, o.a, o.y)) by
    rw [measurable_iff_comap_le]
    rfl).snd.snd

-- @node: fullObs_measurable_potential
/-- [the selected potential-outcome coordinate is measurable](goal). -/
lemma fullObs_measurable_potential {d : ℕ} (a : Bool) :
    Measurable (fun z : FullObs d => if a then z.y1 else z.y0) := by
  cases a <;> simp [fullObs_measurable_y0, fullObs_measurable_y1]

-- @node: fullObs_observed_measurable
/-- [the projection from full data to observed data is measurable](goal). -/
lemma fullObs_observed_measurable {d : ℕ} :
    Measurable (FullObs.observed : FullObs d → Obs d) := by
  have htuple : Measurable (fun z : FullObs d => (z.x, z.a, z.y)) :=
    fullObs_measurable_x.prodMk
      (fullObs_measurable_a.prodMk fullObs_measurable_y)
  simpa [instMeasurableSpaceObs, FullObs.observed,
    measurable_iff_comap_le, Function.comp_def] using htuple

-- @node: full_cell_mass
/-- [the full-data probability of a covariate cell equals its observed cell probability](goal). -/
lemma full_cell_mass {d : ℕ} (P : RealLaw d) (k : Fin d) :
    P.fullLaw {z | z.x = k} = ENNReal.ofReal (P.cellMass k) := by
  have hs : MeasurableSet {o : Obs d | o.x = k} :=
    obs_measurable_x (measurableSet_singleton k)
  rw [P.cellMass_eq, realMass, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rw [← P.observed_margin, Measure.map_apply fullObs_observed_measurable hs]
  rfl

-- @node: full_arm_cell_mass
/-- [the full-data probability of an arm-cell event equals the observed arm-cell
  probability](goal). -/
lemma full_arm_cell_mass {d : ℕ} (P : RealLaw d) (a : Bool) (k : Fin d) :
    P.fullLaw {z | z.x = k ∧ z.a = a} =
      ENNReal.ofReal
        (P.cellMass k * (if a then P.propensity k else 1 - P.propensity k)) := by
  let q := if a then P.propensity k else 1 - P.propensity k
  have hs : MeasurableSet {o : Obs d | o.x = k ∧ o.a = a} := by
    convert (obs_measurable_x.prodMk obs_measurable_a)
      (measurableSet_singleton (k, a)) using 1 <;> ext o <;> simp
  have hfactor := P.arm_outcome_factorization a k Set.univ MeasurableSet.univ
  let _ : IsProbabilityMeasure (P.outcomeLaw a k) := P.outcome_isProbability a k
  have hout : realMass (P.outcomeLaw a k) Set.univ = 1 := by
    simp [realMass]
  rw [hout, mul_one] at hfactor
  have hfactor' : P.cellMass k * q =
      realMass P.observedLaw {o : Obs d | o.x = k ∧ o.a = a} := by
    simpa only [q, Set.mem_univ, and_true] using hfactor
  have hobs : P.observedLaw {o : Obs d | o.x = k ∧ o.a = a} =
      ENNReal.ofReal (P.cellMass k * q) := by
    rw [hfactor']
    simp only [realMass]
    rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rw [← P.observed_margin] at hobs
  rw [Measure.map_apply fullObs_observed_measurable hs] at hobs
  simpa [FullObs.observed, q] using hobs

-- @node: observed_arm_outcome_measure
/-- [the observed arm-cell outcome measure factors into cell probability, arm propensity, and the
  conditional outcome law](goal). -/
lemma observed_arm_outcome_measure {d : ℕ} (P : RealLaw d) (a : Bool) (k : Fin d) :
    Measure.map Obs.y
        (P.observedLaw.restrict {o | o.x = k ∧ o.a = a}) =
      ENNReal.ofReal
          (P.cellMass k * (if a then P.propensity k else 1 - P.propensity k)) •
        P.outcomeLaw a k := by
  let _ : IsProbabilityMeasure (P.outcomeLaw a k) := P.outcome_isProbability a k
  let q := if a then P.propensity k else 1 - P.propensity k
  have hp : 0 ≤ P.cellMass k := (P.cellMass_range k).1
  have hq : 0 ≤ q := by
    rcases P.propensity_range k with ⟨hpi0, hpi1⟩
    cases a <;> simp [q] <;> linarith
  have hc : 0 ≤ P.cellMass k * q := mul_nonneg hp hq
  have hE : MeasurableSet {o : Obs d | o.x = k ∧ o.a = a} := by
    convert (obs_measurable_x.prodMk obs_measurable_a)
      (measurableSet_singleton (k, a)) using 1 <;> ext o <;> simp
  ext s hs
  rw [Measure.map_apply obs_measurable_y hs,
    Measure.restrict_apply (obs_measurable_y hs), Measure.smul_apply]
  have hf := P.arm_outcome_factorization a k s hs
  have hf' := congrArg ENNReal.ofReal hf
  simp only [realMass] at hf'
  rw [ENNReal.ofReal_mul hc, ENNReal.ofReal_toReal (measure_ne_top _ _),
    ENNReal.ofReal_toReal (measure_ne_top _ _)] at hf'
  rw [show Obs.y ⁻¹' s ∩ {o : Obs d | o.x = k ∧ o.a = a} =
      {o : Obs d | o.x = k ∧ o.a = a ∧ o.y ∈ s} by
        ext o
        simp [and_assoc, and_left_comm, and_comm]]
  simpa only [q, smul_eq_mul] using hf'.symm

-- @node: consistency_ae
/-- If [consistency holds](hyp:hP), [consistency implies that the observed outcome equals the
  treatment-selected potential outcome almost surely](goal). -/
lemma consistency_ae {d : ℕ} (P : RealLaw d) (hP : Consistency P) :
    (fun z : FullObs d => z.y) =ᵐ[P.fullLaw]
      (fun z => if z.a then z.y1 else z.y0) := by
  rw [Filter.EventuallyEq, ae_iff]
  change P.fullLaw {z | z.y ≠ if z.a then z.y1 else z.y0} = 0
  exact hP

-- @node: full_arm_potential_measure
/-- If [consistency holds](hyp:hcons), [under exchangeability, the full-data arm-cell
  potential-outcome measure factors into the arm-cell probability and conditional outcome
  law](goal). -/
lemma full_arm_potential_measure {d : ℕ} (P : RealLaw d)
    (hcons : Consistency P) (a : Bool) (k : Fin d) :
    Measure.map (fun z : FullObs d => if a then z.y1 else z.y0)
        (P.fullLaw.restrict {z | z.x = k ∧ z.a = a}) =
      Measure.map Obs.y
        (P.observedLaw.restrict {o | o.x = k ∧ o.a = a}) := by
  have hObsE : MeasurableSet {o : Obs d | o.x = k ∧ o.a = a} := by
    convert (obs_measurable_x.prodMk obs_measurable_a)
      (measurableSet_singleton (k, a)) using 1 <;> ext o <;> simp
  have hFullE : MeasurableSet {z : FullObs d | z.x = k ∧ z.a = a} := by
    convert (fullObs_measurable_x.prodMk fullObs_measurable_a)
      (measurableSet_singleton (k, a)) using 1 <;> ext z <;> simp
  have hpot_y :
      (fun z : FullObs d => if a then z.y1 else z.y0) =ᵐ[
        P.fullLaw.restrict {z | z.x = k ∧ z.a = a}] fun z => z.y := by
    filter_upwards [ae_restrict_mem hFullE,
      ae_restrict_of_ae (consistency_ae P hcons)] with z hz hzy
    have hza : z.a = a := hz.2
    simpa only [hza] using hzy.symm
  rw [Measure.map_congr hpot_y]
  have hrestrict :
      P.observedLaw.restrict {o : Obs d | o.x = k ∧ o.a = a} =
        Measure.map FullObs.observed
          (P.fullLaw.restrict {z : FullObs d | z.x = k ∧ z.a = a}) := by
    rw [← P.observed_margin, Measure.restrict_map fullObs_observed_measurable hObsE]
    rfl
  rw [hrestrict, Measure.map_map obs_measurable_y fullObs_observed_measurable]
  rfl

-- @node: full_cell_potential_measure
/-- If [the stated condition on the cell holds](hyp:hk), [under exchangeability and overlap, the
  full-data cell potential-outcome measure factors into the cell probability and conditional
  outcome law](goal). -/
lemma full_cell_potential_measure {d : ℕ} {epsilon M sigma : ℝ}
    (P : ModelClass d epsilon M sigma) (a : Bool) (k : Fin d)
    (hk : 0 < P.law.cellMass k) :
    Measure.map (fun z : FullObs d => if a then z.y1 else z.y0)
        (P.law.fullLaw.restrict {z | z.x = k}) =
      ENNReal.ofReal (P.law.cellMass k) • P.law.outcomeLaw a k := by
  let pot : FullObs d → ℝ := fun z => if a then z.y1 else z.y0
  let q : ℝ := if a then P.law.propensity k else 1 - P.law.propensity k
  have hq : 0 < q := by
    rcases P.overlap k hk with ⟨hlow, hupp⟩
    cases a <;> simp [q] <;> linarith [P.epsilon_pos]
  have hc : 0 < P.law.cellMass k * q := mul_pos hk hq
  have hpot : Measurable pot := fullObs_measurable_potential a
  have hcell : MeasurableSet {z : FullObs d | z.x = k} :=
    fullObs_measurable_x (measurableSet_singleton k)
  ext s hs
  have harmMap := (full_arm_potential_measure P.law P.consistency a k).trans
    (observed_arm_outcome_measure P.law a k)
  have harm := congrArg (fun mu : Measure ℝ => mu s) harmMap
  rw [Measure.map_apply hpot hs, Measure.restrict_apply (hpot hs),
    Measure.smul_apply] at harm
  have hci := P.exchangeability k a
    (if a then Set.univ else s) (if a then s else Set.univ)
    (by cases a <;> simp [hs]) (by cases a <;> simp [hs])
  have hind :
      P.law.fullLaw {z | z.x = k ∧ z.a = a ∧ pot z ∈ s} *
          P.law.fullLaw {z | z.x = k} =
        P.law.fullLaw {z | z.x = k ∧ z.a = a} *
          P.law.fullLaw {z | z.x = k ∧ pot z ∈ s} := by
    cases a <;>
      simpa [pot, and_assoc, and_left_comm, and_comm] using hci
  rw [full_cell_mass P.law k, full_arm_cell_mass P.law a k] at hind
  have hleft : P.law.fullLaw {z | z.x = k ∧ z.a = a ∧ pot z ∈ s} =
      ENNReal.ofReal (P.law.cellMass k * q) * P.law.outcomeLaw a k s := by
    calc
      P.law.fullLaw {z | z.x = k ∧ z.a = a ∧ pot z ∈ s} =
          P.law.fullLaw (pot ⁻¹' s ∩ {z | z.x = k ∧ z.a = a}) := by
            congr 1
            ext z
            simp [pot, and_assoc, and_left_comm, and_comm]
      _ = ENNReal.ofReal (P.law.cellMass k * q) *
          P.law.outcomeLaw a k s := by
            simpa only [q, smul_eq_mul] using harm
  rw [hleft] at hind
  have hcancel : ENNReal.ofReal (P.law.cellMass k * q) ≠ 0 := by
    exact (ENNReal.ofReal_pos.mpr hc).ne'
  have hfinite : ENNReal.ofReal (P.law.cellMass k * q) ≠ ⊤ := ENNReal.ofReal_ne_top
  have heq :
      ENNReal.ofReal (P.law.cellMass k * q) *
          (P.law.fullLaw {z | z.x = k ∧ pot z ∈ s}) =
        ENNReal.ofReal (P.law.cellMass k * q) *
          (ENNReal.ofReal (P.law.cellMass k) * P.law.outcomeLaw a k s) := by
    simpa only [q, mul_assoc, mul_left_comm, mul_comm] using hind.symm
  have hdesired : P.law.fullLaw {z | z.x = k ∧ pot z ∈ s} =
      ENNReal.ofReal (P.law.cellMass k) * P.law.outcomeLaw a k s := by
    apply le_antisymm
    · rw [← ENNReal.mul_le_mul_iff_right hcancel hfinite]
      exact heq.le
    · rw [← ENNReal.mul_le_mul_iff_right hcancel hfinite]
      exact heq.ge
  rw [Measure.map_apply hpot hs, Measure.restrict_apply (hpot hs),
    Measure.smul_apply]
  rw [show pot ⁻¹' s ∩ {z : FullObs d | z.x = k} =
      {z | z.x = k ∧ pot z ∈ s} by ext z; simp [and_comm]]
  simpa only [smul_eq_mul] using hdesired

-- @node: full_potential_integrable
/-- [each potential outcome is integrable under the full-data law](goal). -/
lemma full_potential_integrable {d : ℕ} {epsilon M sigma : ℝ}
    (P : ModelClass d epsilon M sigma) (a : Bool) :
    Integrable (fun z : FullObs d => if a then z.y1 else z.y0) P.law.fullLaw := by
  let pot : FullObs d → ℝ := fun z => if a then z.y1 else z.y0
  have hpot : Measurable pot := fullObs_measurable_potential a
  have hcell : ∀ k : Fin d, MeasurableSet {z : FullObs d | z.x = k} :=
    fun k => fullObs_measurable_x (measurableSet_singleton k)
  have hcellInt : ∀ k : Fin d, IntegrableOn pot {z | z.x = k} P.law.fullLaw := by
    intro k
    change Integrable pot (P.law.fullLaw.restrict {z | z.x = k})
    by_cases hk : 0 < P.law.cellMass k
    · have hout := P.identifiedLaw.outcome_integrable a k hk
      have hmap : Integrable (fun y : ℝ => y)
          (Measure.map pot (P.law.fullLaw.restrict {z | z.x = k})) := by
        rw [full_cell_potential_measure P a k hk]
        exact hout.smul_measure ENNReal.ofReal_ne_top
      refine (hmap.comp_measurable hpot).congr ?_
      filter_upwards with z
      rfl
    · have hmass : P.law.fullLaw {z : FullObs d | z.x = k} = 0 := by
        rw [full_cell_mass P.law k]
        have hnonneg := (P.law.cellMass_range k).1
        have hz : P.law.cellMass k = 0 := le_antisymm (le_of_not_gt hk) hnonneg
        simp [hz]
      rw [show P.law.fullLaw.restrict {z : FullObs d | z.x = k} = 0 by
        exact Measure.restrict_eq_zero.mpr hmass]
      exact integrable_zero_measure
  rw [← integrableOn_univ (μ := P.law.fullLaw)]
  rw [show (Set.univ : Set (FullObs d)) = ⋃ k : Fin d, {z | z.x = k} by
    ext z
    simp]
  rw [integrableOn_finite_iUnion]
  exact hcellInt

-- @node: full_potential_cell_integral
/-- [the full-data integral of a potential outcome within a cell equals cell probability times its
  conditional mean](goal). -/
lemma full_potential_cell_integral {d : ℕ} {epsilon M sigma : ℝ}
    (P : ModelClass d epsilon M sigma) (a : Bool) (k : Fin d) :
    (∫ z in {z : FullObs d | z.x = k},
        (if a then z.y1 else z.y0) ∂P.law.fullLaw) =
      P.law.cellMass k * P.law.outcomeMean a k := by
  let pot : FullObs d → ℝ := fun z => if a then z.y1 else z.y0
  have hpot : Measurable pot := fullObs_measurable_potential a
  by_cases hk : 0 < P.law.cellMass k
  · have hout := P.identifiedLaw.outcome_integrable a k hk
    calc
      (∫ z in {z : FullObs d | z.x = k}, pot z ∂P.law.fullLaw) =
          ∫ y : ℝ, y ∂Measure.map pot
            (P.law.fullLaw.restrict {z : FullObs d | z.x = k}) := by
              have hmeas : AEStronglyMeasurable (fun y : ℝ => y)
                  (Measure.map pot
                    (P.law.fullLaw.restrict {z : FullObs d | z.x = k})) :=
                measurable_id.aestronglyMeasurable
              simpa only [Function.comp_apply] using
                (integral_map hpot.aemeasurable hmeas).symm
      _ = ∫ y : ℝ, y ∂(ENNReal.ofReal (P.law.cellMass k) •
            P.law.outcomeLaw a k) := by
              rw [full_cell_potential_measure P a k hk]
      _ = P.law.cellMass k * ∫ y : ℝ, y ∂P.law.outcomeLaw a k := by
              rw [integral_smul_measure]
              simp [(P.law.cellMass_range k).1, smul_eq_mul]
      _ = P.law.cellMass k * P.law.outcomeMean a k := by
              rw [P.law.outcomeMean_eq]
  · have hp0 : P.law.cellMass k = 0 :=
      le_antisymm (le_of_not_gt hk) (P.law.cellMass_range k).1
    have hmass : P.law.fullLaw {z : FullObs d | z.x = k} = 0 := by
      rw [full_cell_mass P.law k, hp0]
      simp
    rw [MeasureTheory.setIntegral_measure_zero pot hmass, hp0, zero_mul]

-- @node: prop:ate-identification
/-- [Consistency, conditional exchangeability, overlap, and the moment envelope identify the
  causal ATE from the observed margin by the finite g-formula](goal). -/
theorem ate_identification {d : ℕ} {epsilon M sigma : ℝ}
    (P : ModelClass d epsilon M sigma) :
    causalATE P.law = ateFunctional P.law P.identifiedLaw := by
  have hcell : ∀ k : Fin d, MeasurableSet
      ((fun z : FullObs d => z.x) ⁻¹' {k}) :=
    fun k => fullObs_measurable_x (measurableSet_singleton k)
  have h1 := full_potential_integrable P true
  have h0 := full_potential_integrable P false
  have h1' : Integrable (fun z : FullObs d => z.y1) P.law.fullLaw := by
    simpa using h1
  have h0' : Integrable (fun z : FullObs d => z.y0) P.law.fullLaw := by
    simpa using h0
  have hsum1 := Causalean.Mathlib.MeasureTheory.integral_eq_sum_setIntegral_fiber
    (μ := P.law.fullLaw) hcell h1'
  have hsum0 := Causalean.Mathlib.MeasureTheory.integral_eq_sum_setIntegral_fiber
    (μ := P.law.fullLaw) hcell h0'
  change causalATE P.law = rawAteFormula P.law
  unfold causalATE rawAteFormula cellEffect
  rw [integral_sub h1' h0', hsum1, hsum0, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  have hk1 := full_potential_cell_integral P true k
  have hk0 := full_potential_cell_integral P false k
  change (∫ z in (fun z : FullObs d => z.x) ⁻¹' {k}, z.y1 ∂P.law.fullLaw) =
    P.law.cellMass k * P.law.outcomeMean true k at hk1
  change (∫ z in (fun z : FullObs d => z.x) ⁻¹' {k}, z.y0 ∂P.law.fullLaw) =
    P.law.cellMass k * P.law.outcomeMean false k at hk0
  rw [hk1, hk0]
  ring

end CausalSmith.Stat.DiscreteAteHeterogeneityFrontier
