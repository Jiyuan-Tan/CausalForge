/-
# Finite-cell procedure and regular-class bridge
-/

import CausalSmith.Stat.STAT_TransportedLateStrengthFrontier_Research.Helpers.RegularCellRisk
import Causalean.Stat.Minimax.HonestConfidenceSet
import Causalean.Stat.Sample.CollisionEstimator

namespace CausalSmith.Stat.TransportedLateStrengthFrontier

open Filter MeasureTheory

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

private lemma coverageInfOrOne_of_nonempty_local {ι : Sort*} [Nonempty ι]
    (f : ι → ℝ) : coverageInfOrOne f = ⨅ i, f i := by
  exact Causalean.Stat.coverageInfOrOne_of_nonempty f

/-- The sample-only uniform-cell specialization of the regular-cell inversion
procedure. -/
noncomputable def finiteCellProcedure (N k : ℕ → ℕ) (L : ℝ) :
    FiniteCellProcedure 𝒳 N k where
  set n input := finiteCellInversion (k n) n (N n) L input.1 input.2
  subset n input := by
    intro theta htheta
    by_cases hsmall : N n < 2
    · simpa [finiteCellInversion, regularCellInversion, hsmall] using htheta
    · simp only [finiteCellInversion, regularCellInversion, hsmall,
        ↓reduceIte] at htheta
      exact htheta.1
  measurableGraph n cell hcell := by
    simpa [finiteCellInversion] using
      regularCellInversion_measurableGraph_on_cells N k L n cell hcell
        (fun _ : 𝒳 => (k n : ℝ)⁻¹) (fun _ : 𝒳 => (1 : ℝ) / 2)
        measurable_const measurable_const

/-- A uniform finite-cell law belongs to the regular finite-cell class with
unit lower and upper cell-mass constants at any smaller overlap radius. -/
lemma FiniteCellClass.toRegularFiniteCellClass
    {P : TransportedArray 𝒳} {N k : ℕ → ℕ} {c epsilon epsilonBar : ℝ}
    {n : ℕ} (hP : FiniteCellClass P N k c epsilon n)
    (hBar : 0 < epsilonBar ∧ epsilonBar < 1 / 2) :
    RegularFiniteCellClass P N k c epsilonBar 1 1 n := by
  have hoverlap : InstrumentOverlap P n epsilonBar := by
    refine ⟨hBar.1, hBar.2, ?_⟩
    filter_upwards [hP.finiteCellSource.2.2.choose_spec.2.2.2.2] with x hx
    rw [hx]
    constructor <;> linarith [hBar.2]
  have hIV : TransportedIVClass P N k c epsilonBar n :=
    { hP with instrumentOverlap := hoverlap }
  obtain ⟨cell, hcell, hrange, hatom, _, _⟩ :=
    hP.finiteCellSource.2.2
  refine ⟨hIV, hP.finiteCellSource.1, by norm_num, by norm_num,
    by norm_num, cell, hcell, hrange, ?_⟩
  intro i
  rw [hatom i]
  constructor <;> simp [div_eq_mul_inv]

/-- On a uniform finite-cell law, the regular procedure fed the law's cell
masses and propensity agrees almost surely with the sample-only specialization. -/
lemma finiteCellProcedure_eq_regularCellSet_ae
    {c epsilon : ℝ} (N k : ℕ → ℕ) (L : ℝ) (n : ℕ)
    (P : TransportedArray 𝒳)
    (hP : FiniteCellClass P N k c epsilon n) :
    ∀ᵐ s ∂twoSampleLaw P N n,
      (finiteCellProcedure (𝒳 := 𝒳) N k L).set n s =
        regularCellSet (regularCellProcedure (𝒳 := 𝒳) N k L) n P
          (hP.toRegularFiniteCellClass
            ⟨hP.instrumentOverlap.1, hP.instrumentOverlap.2.1⟩) s := by
  classical
  let hPreg := hP.toRegularFiniteCellClass
    ⟨hP.instrumentOverlap.1, hP.instrumentOverlap.2.1⟩
  let design := regularCellDesignOfClass P hPreg
  let cell := design.cell
  have hcell : ∀ i, MeasurableSet {cell i} := design.measurableCell
  have hrange : sourceXLaw P n (Set.range cell) = 1 := by
    exact (Classical.choose_spec hPreg.2.2.2.2.2).2.1
  have hatom : ∀ i, sourceCellMass P n (cell i) = (k n : ℝ)⁻¹ := by
    intro i
    have hb := (Classical.choose_spec hPreg.2.2.2.2.2).2.2 i
    change sourceCellMass P n
      ((Classical.choose hPreg.2.2.2.2.2) i) = (k n : ℝ)⁻¹
    exact le_antisymm (by simpa [sourceCellMass, one_div] using hb.2)
      (by simpa [sourceCellMass, one_div] using hb.1)
  have hprop := hP.finiteCellSource.2.2.choose_spec.2.2.2.2
  letI : IsProbabilityMeasure (sourceXLaw P n) :=
    hP.finiteCellSource.2.1
  letI : IsProbabilityMeasure (sourceObsLaw P n) :=
    hP.twoSampleArray.2.1 n
  letI : IsProbabilityMeasure (targetXLaw P n) :=
    hP.twoSampleArray.2.2.1 n
  have hrangeMeas : MeasurableSet (Set.range cell) := by
    rw [show Set.range cell = ⋃ i, {cell i} by
      ext x
      simp]
    exact MeasurableSet.iUnion hcell
  have hrangeCompl : sourceXLaw P n (Set.range cell)ᶜ = 0 := by
    rw [measure_compl hrangeMeas (measure_ne_top _ _), hrange, measure_univ]
    simp
  have htargetRange :
      ∀ᵐ x ∂targetXLaw P n, x ∈ Set.range cell := by
    have hc := hP.transportDomination hrangeCompl
    change Set.range cell ∈ ae (targetXLaw P n)
    rw [mem_ae_iff]
    exact hc
  have hsourceProp :
      ∀ᵐ o ∂sourceObsLaw P n, P.propensity n o.1 = 1 / 2 := by
    unfold sourceXLaw at hprop
    exact ae_of_ae_map measurable_fst.aemeasurable hprop
  let SG : Set (SourceSample 𝒳 n) :=
    {source | (∀ i, (source i).1 ∈ Set.range cell) ∧
      ∀ i, P.propensity n (source i).1 = 1 / 2}
  let TG : Set (TargetSample 𝒳 (N n)) :=
    {target | ∀ j, target j ∈ Set.range cell}
  have hSGmeas : MeasurableSet SG := by
    rw [show SG = (⋂ i, {source | (source i).1 ∈ Set.range cell}) ∩
        ⋂ i, {source | P.propensity n (source i).1 = 1 / 2} by
      ext source
      simp [SG]]
    exact (MeasurableSet.iInter fun i =>
      hrangeMeas.preimage
        (measurable_fst.comp (measurable_pi_apply i))).inter
      (MeasurableSet.iInter fun i =>
        (MeasurableSet.singleton (1 / 2 : ℝ)).preimage
          ((P.propensity_measurable n).comp
            (measurable_fst.comp (measurable_pi_apply i))))
  have hTGmeas : MeasurableSet TG := by
    rw [show TG = ⋂ j, {target | target j ∈ Set.range cell} by
      ext target
      simp [TG]]
    exact MeasurableSet.iInter fun j =>
      hrangeMeas.preimage (measurable_pi_apply j)
  have hSGAE :
      ∀ᵐ source ∂Measure.pi (fun _ : Fin n => sourceObsLaw P n),
        source ∈ SG := by
    have hsourceXAE : ∀ᵐ x ∂sourceXLaw P n, x ∈ Set.range cell :=
      (mem_ae_iff_prob_eq_one hrangeMeas).2 hrange
    have hsourceObsAE :
        ∀ᵐ o ∂sourceObsLaw P n, o.1 ∈ Set.range cell := by
      unfold sourceXLaw at hsourceXAE
      exact ae_of_ae_map measurable_fst.aemeasurable hsourceXAE
    filter_upwards
      [Measure.ae_pi_le_pi
        (Filter.eventually_pi fun _ : Fin n => hsourceObsAE),
       Measure.ae_pi_le_pi
        (Filter.eventually_pi fun _ : Fin n => hsourceProp)] with source hs hp
    exact ⟨hs, hp⟩
  have hTGAE :
      ∀ᵐ target ∂Measure.pi (fun _ : Fin (N n) => targetXLaw P n),
        target ∈ TG := by
    apply Measure.ae_pi_le_pi
    exact Filter.eventually_pi fun _ => htargetRange
  have hSGone :
      Measure.pi (fun _ : Fin n => sourceObsLaw P n) SG = 1 :=
    (mem_ae_iff_prob_eq_one hSGmeas).1 hSGAE
  have hTGone :
      Measure.pi (fun _ : Fin (N n) => targetXLaw P n) TG = 1 :=
    (mem_ae_iff_prob_eq_one hTGmeas).1 hTGAE
  have hprod :
      twoSampleLaw P N n (SG ×ˢ TG) = 1 := by
    unfold twoSampleLaw
    rw [Measure.prod_prod, hSGone, hTGone]
    simp
  letI : IsProbabilityMeasure (twoSampleLaw P N n) := by
    unfold twoSampleLaw
    infer_instance
  have hprodAE : ∀ᵐ s ∂twoSampleLaw P N n, s ∈ SG ×ˢ TG := by
    exact (mem_ae_iff_prob_eq_one (hSGmeas.prod hTGmeas)).2 hprod
  filter_upwards [hprodAE] with s hs
  have hmass (j : Fin (N n)) :
      sourceCellMass P n (s.2 j) = (k n : ℝ)⁻¹ := by
    obtain ⟨i, hi⟩ := hs.2 j
    rw [← hi]
    exact hatom i
  have hprop' (i : Fin n) :
      P.propensity n (s.1 i).1 = 1 / 2 :=
    hs.1.2 i
  change finiteCellInversion (k n) n (N n) L s.1 s.2 =
    regularCellInversion
      (cellVectorExtension design
        (fun i => sourceCellMass P n (design.cell i)))
      (cellVectorExtension design
        (fun i => P.propensity n (design.cell i))) L s.1 s.2
  have hqExt (j : Fin (N n)) :
      cellVectorExtension design
          (fun i => sourceCellMass P n (design.cell i)) (s.2 j) =
        (k n : ℝ)⁻¹ := by
    obtain ⟨i, hi⟩ := hs.2 j
    rw [← hi, cellVectorExtension_apply_cell]
    exact hatom i
  have heExt (i : Fin n) :
      cellVectorExtension design
          (fun j => P.propensity n (design.cell j)) (s.1 i).1 =
        1 / 2 := by
    obtain ⟨j, hj⟩ := hs.1.1 i
    calc
      cellVectorExtension design
          (fun j => P.propensity n (design.cell j)) (s.1 i).1 =
          P.propensity n (s.1 i).1 := by
            rw [← hj, cellVectorExtension_apply_cell]
      _ = 1 / 2 := hprop' i
  unfold finiteCellInversion
  have hinv :
      regularCellInversion
          (cellVectorExtension design
            (fun i => sourceCellMass P n (design.cell i)))
          (cellVectorExtension design
            (fun i => P.propensity n (design.cell i))) L s.1 s.2 =
        regularCellInversion (fun _ : 𝒳 => (k n : ℝ)⁻¹)
          (fun _ : 𝒳 => 1 / 2) L s.1 s.2 := by
    unfold regularCellInversion crossAverage collisionScale
      Causalean.Stat.crossAverage Causalean.Stat.cellMoment
      Causalean.Stat.collisionScale Causalean.Stat.collisionKernel
      oracleInstrumentScore
    simp_rw [hqExt, heExt]
  exact hinv.symm

/-- On a uniform finite-cell law, the sample-only and regular specialized
procedures have the same coverage. -/
lemma finiteCellProcedure_coverage_eq_regular
    {c epsilon : ℝ} (N k : ℕ → ℕ) (L : ℝ) (n : ℕ)
    (P : TransportedArray 𝒳) (hP : FiniteCellClass P N k c epsilon n) :
    finiteCellCoverage (finiteCellProcedure (𝒳 := 𝒳) N k L) n P =
      regularCellCoverage (regularCellProcedure (𝒳 := 𝒳) N k L) n
        ⟨P, hP.toRegularFiniteCellClass
          ⟨hP.instrumentOverlap.1, hP.instrumentOverlap.2.1⟩⟩ := by
  unfold finiteCellCoverage regularCellCoverage
  congr 1
  apply measure_congr
  filter_upwards [finiteCellProcedure_eq_regularCellSet_ae N k L n P hP]
    with s hs
  change (targetCACE P n ∈
      (finiteCellProcedure (𝒳 := 𝒳) N k L).set n s) =
    (targetCACE P n ∈
      regularCellSet (regularCellProcedure (𝒳 := 𝒳) N k L) n P
        (hP.toRegularFiniteCellClass
          ⟨hP.instrumentOverlap.1, hP.instrumentOverlap.2.1⟩) s)
  rw [hs]

/-- On a uniform finite-cell law, the sample-only and regular specialized
procedures have the same expected set length. -/
lemma finiteCellProcedure_expectedLength_eq_regular
    {c epsilon : ℝ} (N k : ℕ → ℕ) (L : ℝ) (n : ℕ)
    (P : TransportedArray 𝒳) (hP : FiniteCellClass P N k c epsilon n) :
    finiteCellExpectedLength (finiteCellProcedure (𝒳 := 𝒳) N k L) n P =
      regularCellExpectedLength
        (regularCellProcedure (𝒳 := 𝒳) N k L) n
        ⟨P, hP.toRegularFiniteCellClass
          ⟨hP.instrumentOverlap.1, hP.instrumentOverlap.2.1⟩⟩ := by
  unfold finiteCellExpectedLength regularCellExpectedLength
  apply integral_congr_ae
  filter_upwards [finiteCellProcedure_eq_regularCellSet_ae N k L n P hP]
    with s hs
  rw [hs]

private lemma setLength_le_two (A : Set ℝ) : setLength A ≤ 2 := by
  unfold setLength parameterSpace
  calc
    (volume (A ∩ Set.Icc (-1 : ℝ) 1)).toReal ≤
        (volume (Set.Icc (-1 : ℝ) 1)).toReal :=
      ENNReal.toReal_mono (by simp [Real.volume_Icc])
        (measure_mono Set.inter_subset_right)
    _ = 2 := by
      rw [Real.volume_Icc, ENNReal.toReal_ofReal (by norm_num)]
      norm_num

private lemma regularCellExpectedLength_le_two
    {c epsilon cminus cplus : ℝ} (N k : ℕ → ℕ)
    (C : RegularCellProcedure 𝒳 N k) (n : ℕ)
    (P : TransportedArray 𝒳)
    (hP : RegularFiniteCellClass P N k c epsilon cminus cplus n) :
    regularCellExpectedLength C n ⟨P, hP⟩ ≤ 2 := by
  letI : IsProbabilityMeasure (sourceObsLaw P n) :=
    hP.1.twoSampleArray.2.1 n
  letI : IsProbabilityMeasure (targetXLaw P n) :=
    hP.1.twoSampleArray.2.2.1 n
  letI : IsProbabilityMeasure (twoSampleLaw P N n) := by
    unfold twoSampleLaw
    infer_instance
  exact (integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg)
    (integrable_const 2)
    (Filter.Eventually.of_forall fun s =>
      setLength_le_two (regularCellSet C n P hP s))).trans_eq (by simp)

/-- Honesty and worst-case expected length transfer from the unit-regular
procedure to its sample-only uniform-cell specialization. -/
lemma finiteCellProcedure_upper_bridge
    (N k : ℕ → ℕ) (c epsilon epsilonBar alpha L : ℝ)
    (hBar : 0 < epsilonBar ∧ epsilonBar < 1 / 2)
    (hClass : ∀ n, ∃ P : TransportedArray 𝒳,
      FiniteCellClass P N k c epsilon n)
    (Creg : RegularCellProcedure 𝒳 N k)
    (hSetEq : ∀ n P, (hP : FiniteCellClass P N k c epsilon n) →
      ∀ᵐ s ∂twoSampleLaw P N n,
        (finiteCellProcedure (𝒳 := 𝒳) N k L).set n s =
          regularCellSet Creg n P
            (hP.toRegularFiniteCellClass hBar) s)
    (hHonest : RegularCellHonest N k c epsilonBar alpha 1 1
      Creg) :
    FiniteCellHonest N k c epsilon alpha
        (finiteCellProcedure (𝒳 := 𝒳) N k L) ∧
      ∀ t0,
        feasibleFiniteCellRisk N k c epsilon
            (finiteCellProcedure (𝒳 := 𝒳) N k L) t0 ≤
          regularCellRisk N k c epsilonBar 1 1
            Creg t0 := by
  classical
  let Cfin := finiteCellProcedure (𝒳 := 𝒳) N k L
  have hcoverageEq : ∀ n P, (hP : FiniteCellClass P N k c epsilon n) →
      finiteCellCoverage Cfin n P = regularCellCoverage Creg n
        ⟨P, hP.toRegularFiniteCellClass hBar⟩ := by
    intro n P hP
    unfold finiteCellCoverage regularCellCoverage
    congr 1
    apply measure_congr
    filter_upwards [hSetEq n P hP] with s hs
    change (targetCACE P n ∈ Cfin.set n s) =
      (targetCACE P n ∈ regularCellSet Creg n P
        (hP.toRegularFiniteCellClass hBar) s)
    rw [hs]
  have hlengthEq : ∀ n P, (hP : FiniteCellClass P N k c epsilon n) →
      finiteCellExpectedLength Cfin n P =
        regularCellExpectedLength Creg n
          ⟨P, hP.toRegularFiniteCellClass hBar⟩ := by
    intro n P hP
    unfold finiteCellExpectedLength regularCellExpectedLength
    apply integral_congr_ae
    filter_upwards [hSetEq n P hP] with s hs
    rw [hs]
  let covF : ℕ → ℝ := fun n =>
    coverageInfOrOne fun P : {P : TransportedArray 𝒳 //
        FiniteCellClass P N k c epsilon n} =>
      finiteCellCoverage Cfin n P
  let covR : ℕ → ℝ := fun n =>
    coverageInfOrOne fun P : {P : TransportedArray 𝒳 //
        RegularFiniteCellClass P N k c epsilonBar 1 1 n} =>
      regularCellCoverage Creg n P
  have hcoverageRange : ∀ n P,
      (hP : RegularFiniteCellClass P N k c epsilonBar 1 1 n) →
        0 ≤ regularCellCoverage Creg n ⟨P, hP⟩ ∧
          regularCellCoverage Creg n ⟨P, hP⟩ ≤ 1 := by
    intro n P hP
    letI : IsProbabilityMeasure (sourceObsLaw P n) :=
      hP.1.twoSampleArray.2.1 n
    letI : IsProbabilityMeasure (targetXLaw P n) :=
      hP.1.twoSampleArray.2.2.1 n
    letI : IsProbabilityMeasure (twoSampleLaw P N n) := by
      unfold twoSampleLaw
      infer_instance
    exact ⟨ENNReal.toReal_nonneg, measureReal_le_one⟩
  have hcovRows : ∀ n, covR n ≤ covF n := by
    intro n
    obtain ⟨P0, hP0⟩ := hClass n
    letI : Nonempty {P : TransportedArray 𝒳 //
        FiniteCellClass P N k c epsilon n} := ⟨⟨P0, hP0⟩⟩
    letI : Nonempty {P : TransportedArray 𝒳 //
        RegularFiniteCellClass P N k c epsilonBar 1 1 n} :=
      ⟨⟨P0, hP0.toRegularFiniteCellClass hBar⟩⟩
    change (coverageInfOrOne fun P : {P : TransportedArray 𝒳 //
        RegularFiniteCellClass P N k c epsilonBar 1 1 n} =>
          regularCellCoverage Creg n P) ≤
      coverageInfOrOne fun P : {P : TransportedArray 𝒳 //
        FiniteCellClass P N k c epsilon n} => finiteCellCoverage Cfin n P
    rw [coverageInfOrOne_of_nonempty_local,
      coverageInfOrOne_of_nonempty_local]
    apply le_ciInf
    intro P
    have hbdd' : BddBelow (Set.range fun Q :
        {Q : TransportedArray 𝒳 //
          RegularFiniteCellClass Q N k c epsilonBar 1 1 n} =>
          regularCellCoverage Creg n Q) :=
      ⟨0, by
        rintro y ⟨Q, rfl⟩
        exact (hcoverageRange n Q Q.2).1⟩
    exact (ciInf_le hbdd'
      ⟨P, P.2.toRegularFiniteCellClass hBar⟩).trans_eq (by
        exact (hcoverageEq n P P.2).symm)
  have hcovRnonneg : ∀ n, 0 ≤ covR n := by
    intro n
    obtain ⟨P0, hP0⟩ := hClass n
    letI : Nonempty {P : TransportedArray 𝒳 //
        RegularFiniteCellClass P N k c epsilonBar 1 1 n} :=
      ⟨⟨P0, hP0.toRegularFiniteCellClass hBar⟩⟩
    change 0 ≤ coverageInfOrOne fun P : {P : TransportedArray 𝒳 //
      RegularFiniteCellClass P N k c epsilonBar 1 1 n} =>
        regularCellCoverage Creg n P
    rw [coverageInfOrOne_of_nonempty_local]
    exact le_ciInf fun P => (hcoverageRange n P P.2).1
  have hcovFone : ∀ n, covF n ≤ 1 := by
    intro n
    obtain ⟨P0, hP0⟩ := hClass n
    letI : Nonempty {P : TransportedArray 𝒳 //
        FiniteCellClass P N k c epsilon n} := ⟨⟨P0, hP0⟩⟩
    change (coverageInfOrOne fun P : {P : TransportedArray 𝒳 //
      FiniteCellClass P N k c epsilon n} => finiteCellCoverage Cfin n P) ≤ 1
    rw [coverageInfOrOne_of_nonempty_local]
    have hbdd : BddBelow (Set.range fun P :
        {P : TransportedArray 𝒳 //
          FiniteCellClass P N k c epsilon n} =>
          finiteCellCoverage Cfin n P) :=
      ⟨0, by
        rintro y ⟨P, rfl⟩
        change 0 ≤ finiteCellCoverage Cfin n (P : TransportedArray 𝒳)
        rw [hcoverageEq n P P.2]
        exact (hcoverageRange n P
          (P.2.toRegularFiniteCellClass hBar)).1⟩
    exact (ciInf_le hbdd ⟨P0, hP0⟩).trans
      ((hcoverageEq n P0 hP0).le.trans
        (hcoverageRange n P0
          (hP0.toRegularFiniteCellClass hBar)).2)
  have hcovRbounded : IsBoundedUnder (· ≥ ·) atTop covR := by
    change ∃ b, ∀ᶠ n in atTop, b ≤ covR n
    exact ⟨0, Filter.Eventually.of_forall hcovRnonneg⟩
  have hcovFcobounded : IsCoboundedUnder (· ≥ ·) atTop covF := by
    change ∃ b, ∀ a, (∀ᶠ n in atTop, a ≤ covF n) → a ≤ b
    refine ⟨1, fun a ha => ?_⟩
    have haone := (ha.and (Filter.Eventually.of_forall hcovFone)).exists.choose_spec
    exact haone.1.trans haone.2
  have hfiniteHonest : FiniteCellHonest N k c epsilon alpha Cfin := by
    refine ⟨hHonest.1, hHonest.2.1, hHonest.2.2.trans ?_⟩
    exact Filter.liminf_le_liminf
      (Filter.Eventually.of_forall hcovRows) hcovRbounded hcovFcobounded
  refine ⟨hfiniteHonest, ?_⟩
  intro t0
  let rowF : ℕ → ℝ := fun n =>
    ⨆ P : {P : TransportedArray 𝒳 //
        FiniteCellClass P N k c epsilon n ∧
          t0 ≤ effectiveStrength P n},
      finiteCellExpectedLength Cfin n P
  let rowR : ℕ → ℝ := fun n =>
    ⨆ P : {P : TransportedArray 𝒳 //
        RegularFiniteCellClass P N k c epsilonBar 1 1 n ∧
          t0 ≤ effectiveStrength P n},
      regularCellExpectedLength Creg n ⟨P.1, P.2.1⟩
  have hrowRnonneg : ∀ n, 0 ≤ rowR n := by
    intro n
    cases isEmpty_or_nonempty
        {P : TransportedArray 𝒳 //
          RegularFiniteCellClass P N k c epsilonBar 1 1 n ∧
            t0 ≤ effectiveStrength P n} with
    | inl h =>
        letI := h
        simp [rowR]
    | inr h =>
        letI := h
        let P := Classical.choice h
        have hbdd : BddAbove (Set.range fun Q :
            {Q : TransportedArray 𝒳 //
              RegularFiniteCellClass Q N k c epsilonBar 1 1 n ∧
                t0 ≤ effectiveStrength Q n} =>
              regularCellExpectedLength Creg n ⟨Q.1, Q.2.1⟩) :=
          ⟨2, by
            rintro y ⟨Q, rfl⟩
            exact regularCellExpectedLength_le_two N k Creg n Q Q.2.1⟩
        exact (integral_nonneg fun _ => ENNReal.toReal_nonneg).trans
          (le_ciSup hbdd P)
  have hrowRisk : ∀ n, rowF n ≤ rowR n := by
    intro n
    cases isEmpty_or_nonempty
        {P : TransportedArray 𝒳 //
          FiniteCellClass P N k c epsilon n ∧
            t0 ≤ effectiveStrength P n} with
    | inl h =>
        letI := h
        simpa [rowF] using hrowRnonneg n
    | inr h =>
        letI := h
        apply ciSup_le
        intro P
        have hbdd : BddAbove (Set.range fun Q :
            {Q : TransportedArray 𝒳 //
              RegularFiniteCellClass Q N k c epsilonBar 1 1 n ∧
                t0 ≤ effectiveStrength Q n} =>
              regularCellExpectedLength Creg n ⟨Q.1, Q.2.1⟩) :=
          ⟨2, by
            rintro y ⟨Q, rfl⟩
            exact regularCellExpectedLength_le_two N k Creg n Q Q.2.1⟩
        exact (hlengthEq n P P.2.1).le.trans
            (le_ciSup hbdd
              ⟨P, P.2.1.toRegularFiniteCellClass hBar, P.2.2⟩)
  have hrowFnonneg : ∀ n, 0 ≤ rowF n := by
    intro n
    cases isEmpty_or_nonempty
        {P : TransportedArray 𝒳 //
          FiniteCellClass P N k c epsilon n ∧
            t0 ≤ effectiveStrength P n} with
    | inl h =>
        letI := h
        simp [rowF]
    | inr h =>
        letI := h
        let P := Classical.choice h
        have hbdd : BddAbove (Set.range fun Q :
            {Q : TransportedArray 𝒳 //
              FiniteCellClass Q N k c epsilon n ∧
                t0 ≤ effectiveStrength Q n} =>
              finiteCellExpectedLength Cfin n Q) :=
          ⟨2, by
            rintro y ⟨Q, rfl⟩
            change finiteCellExpectedLength Cfin n
              (Q : TransportedArray 𝒳) ≤ 2
            rw [hlengthEq n Q Q.2.1]
            exact regularCellExpectedLength_le_two N k Creg n Q
              (Q.2.1.toRegularFiniteCellClass hBar)⟩
        exact (integral_nonneg fun _ => ENNReal.toReal_nonneg).trans
          (le_ciSup hbdd P)
  have hrowRtwo : ∀ n, rowR n ≤ 2 := by
    intro n
    cases isEmpty_or_nonempty
        {P : TransportedArray 𝒳 //
          RegularFiniteCellClass P N k c epsilonBar 1 1 n ∧
            t0 ≤ effectiveStrength P n} with
    | inl h =>
        letI := h
        simp [rowR]
    | inr h =>
        letI := h
        apply ciSup_le
        intro P
        exact regularCellExpectedLength_le_two N k Creg n P P.2.1
  have hFcob : IsCoboundedUnder (· ≤ ·) atTop rowF := by
    change ∃ b, ∀ a, (∀ᶠ n in atTop, rowF n ≤ a) → b ≤ a
    refine ⟨0, fun a ha => ?_⟩
    have h := ((Filter.Eventually.of_forall hrowFnonneg).and ha).exists.choose_spec
    exact h.1.trans h.2
  have hRbdd : IsBoundedUnder (· ≤ ·) atTop rowR := by
    change ∃ b, ∀ᶠ n in atTop, rowR n ≤ b
    exact ⟨2, Filter.Eventually.of_forall hrowRtwo⟩
  exact Filter.limsup_le_limsup
    (Filter.Eventually.of_forall hrowRisk) hFcob hRbdd

end CausalSmith.Stat.TransportedLateStrengthFrontier
