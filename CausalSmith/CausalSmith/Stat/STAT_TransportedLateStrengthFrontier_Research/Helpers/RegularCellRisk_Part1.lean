/-
# Regular-cell risk engine

Leaf lemmas for the honesty and variance half of the regular finite-cell
attainment argument.  The ambient covariate carrier remains arbitrary: every
finite calculation is scoped to the injected support supplied by
`RegularFiniteCellClass`.
-/

import CausalSmith.Stat.STAT_TransportedLateStrengthFrontier_Research.Helpers.InversionRisk
import CausalSmith.Stat.STAT_TransportedLateStrengthFrontier_Research.Helpers.Witness
import CausalSmith.Stat.STAT_TransportedLateStrengthFrontier_Research.T_CompactCausalRange
import Causalean.Mathlib.MeasureTheory.FiniteAtomicMeasure
import Causalean.Mathlib.Probability.IidMeanVariance
import Causalean.Stat.Sample.EmpiricalMass

namespace CausalSmith.Stat.TransportedLateStrengthFrontier

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

/-! ## Statistics and deterministic constants -/
/-- The constant in the regular-cell variance calculation. -/
noncomputable def regularCellVarianceConstant (epsilon c : ℝ) : ℝ :=
  8 * (epsilon⁻¹ ^ 2 + c⁻¹)

/-- Empirical target mass of one ambient point. -/
noncomputable abbrev targetEmpiricalMass {N : ℕ}
    (target : TargetSample 𝒳 N) (x : 𝒳) : ℝ :=
  Causalean.Stat.empiricalMass target x

/-- The affine source score at a candidate effect. -/
noncomputable def regularCellScore (e : 𝒳 → ℝ) (theta : ℝ)
    (o : SourceObs 𝒳) : ℝ :=
  oracleInstrumentScore e o * (o.2.2.2 - theta * boolReal o.2.2.1)

/-- The conditional score mean represented by the model's contrast versions. -/
noncomputable def regularCellScoreMean (P : TransportedArray 𝒳)
    (n : ℕ) (theta : ℝ) (x : 𝒳) : ℝ :=
  P.deltaY n x - theta * P.deltaD n x

/-- Cross-averaged outcome score. -/
noncomputable def regularCellOutcomeMoment (q e : 𝒳 → ℝ) {n N : ℕ}
    (source : SourceSample 𝒳 n) (target : TargetSample 𝒳 N) : ℝ :=
  crossAverage q source target
    (fun o => oracleInstrumentScore e o * o.2.2.2)

/-- Cross-averaged receipt score. -/
noncomputable def regularCellReceiptMoment (q e : 𝒳 → ℝ) {n N : ℕ}
    (source : SourceSample 𝒳 n) (target : TargetSample 𝒳 N) : ℝ :=
  crossAverage q source target
    (fun o => oracleInstrumentScore e o * boolReal o.2.2.1)

/-- Cross-averaged affine score. -/
noncomputable def regularCellContrastMoment (q e : 𝒳 → ℝ) (theta : ℝ)
    {n N : ℕ} (source : SourceSample 𝒳 n)
    (target : TargetSample 𝒳 N) : ℝ :=
  regularCellOutcomeMoment q e source target -
    theta * regularCellReceiptMoment q e source target

/-- The collision proxy used by the feasible regular-cell rule. -/
noncomputable def regularCellKhat (q : 𝒳 → ℝ) {N : ℕ}
    (target : TargetSample 𝒳 N) : ℝ :=
  1 + collisionScale q target

/-! ## The feasible procedure bundle -/

/-- The zero-extended cell-value function returns a cell's assigned value at every point in that cell. -/
lemma cellVectorExtension_apply_cell
    {m : ℕ} (design : RegularCellDesign 𝒳 m)
    (v : Fin m → ℝ) (i : Fin m) :
    cellVectorExtension design v (design.cell i) = v i := by
  classical
  unfold cellVectorExtension
  split
  · congr 1
    exact design.cell.injective (Classical.choose_spec ‹∃ j, design.cell j = design.cell i›)
  · exact (‹¬∃ j, design.cell j = design.cell i› ⟨i, rfl⟩).elim

/-- Extending a finite vector of cell values by zero outside the cells defines a measurable covariate function. -/
lemma measurable_cellVectorExtension
    {m : ℕ} (design : RegularCellDesign 𝒳 m)
    (v : Fin m → ℝ) :
    Measurable (cellVectorExtension design v) := by
  classical
  have hrepr : cellVectorExtension design v = fun x =>
      ∑ i : Fin m, if x = design.cell i then v i else 0 := by
    funext x
    by_cases hx : ∃ i, design.cell i = x
    · let i := Classical.choose hx
      have hi : design.cell i = x := Classical.choose_spec hx
      rw [show cellVectorExtension design v x = v i by
        rw [← hi]
        exact cellVectorExtension_apply_cell design v i]
      rw [Finset.sum_eq_single i]
      · simp [hi]
      · intro j _ hji
        have hne : x ≠ design.cell j := by
          intro h
          exact hji (design.cell.injective (hi.trans h)).symm
        simp [hne]
      · simp
    · unfold cellVectorExtension
      rw [dif_neg hx]
      symm
      apply Finset.sum_eq_zero
      intro i _
      rw [if_neg]
      intro hxi
      exact hx ⟨i, hxi.symm⟩
  rw [hrepr]
  apply Finset.measurable_sum
  intro i _
  apply Measurable.ite
  · simpa [eq_comm] using design.measurableCell i
  · exact measurable_const
  · exact measurable_const

/-- Cell-scoped graph measurability of regular-cell inversion. -/
lemma regularCellInversion_measurableGraph_on_cells
    (N k : ℕ → ℕ) (L : ℝ) (n : ℕ)
    (cell : Fin (k n) ↪ 𝒳) (hcell : ∀ i, MeasurableSet {cell i})
    (q e : 𝒳 → ℝ) (hq : Measurable q) (he : Measurable e) :
    MeasurableSet {p : TwoSample 𝒳 n (N n) × ℝ |
      ((∀ i, (p.1.1 i).1 ∈ Set.range cell) ∧
        (∀ j, p.1.2 j ∈ Set.range cell)) ∧
      p.2 ∈ regularCellInversion q e L p.1.1 p.1.2} := by
  classical
  let sameCell : 𝒳 → 𝒳 → Prop := fun x y =>
    ∃ i : Fin (k n), x = cell i ∧ y = cell i
  have hsameCell : MeasurableSet {z : 𝒳 × 𝒳 | sameCell z.1 z.2} := by
    rw [show {z : 𝒳 × 𝒳 | sameCell z.1 z.2} =
        ⋃ i : Fin (k n), {z | z.1 = cell i ∧ z.2 = cell i} by
      ext z
      simp [sameCell]]
    apply MeasurableSet.iUnion
    intro i
    exact ((hcell i).preimage measurable_fst).inter
      ((hcell i).preimage measurable_snd)
  let kernel : 𝒳 → 𝒳 → ℝ := fun x y =>
    if sameCell x y then 1 / q x else 0
  have hkernel : Measurable (Function.uncurry kernel) := by
    exact Measurable.ite hsameCell
      (measurable_const.div (hq.comp measurable_fst)) measurable_const
  have hInstrument : Measurable (oracleInstrumentScore e) := by
    unfold oracleInstrumentScore
    have hz : Measurable fun o : SourceObs 𝒳 => o.2.1 := by fun_prop
    have he' : Measurable fun o : SourceObs 𝒳 => e o.1 :=
      he.comp measurable_fst
    exact Measurable.ite (hz (MeasurableSet.singleton true))
      (measurable_const.div he')
      (measurable_const.neg.div (measurable_const.sub he'))
  have hBool : Measurable (fun o : SourceObs 𝒳 => boolReal o.2.2.1) := by
    unfold boolReal
    have hd : Measurable fun o : SourceObs 𝒳 => o.2.2.1 := by fun_prop
    exact Measurable.ite (hd (MeasurableSet.singleton true))
      measurable_const measurable_const
  let Gy : SourceObs 𝒳 → ℝ := fun o =>
    oracleInstrumentScore e o * o.2.2.2
  let Gd : SourceObs 𝒳 → ℝ := fun o =>
    oracleInstrumentScore e o * boolReal o.2.2.1
  have hGy : Measurable Gy := hInstrument.mul (by fun_prop)
  have hGd : Measurable Gd := hInstrument.mul hBool
  let moment : (SourceSample 𝒳 n × TargetSample 𝒳 (N n)) →
      (SourceObs 𝒳 → ℝ) → ℝ := fun s G =>
    (N n : ℝ)⁻¹ * ∑ j,
      (n : ℝ)⁻¹ / q (s.2 j) *
        ∑ i, if sameCell (s.1 i).1 (s.2 j) then G (s.1 i) else 0
  have hmoment (G : SourceObs 𝒳 → ℝ) (hG : Measurable G) :
      Measurable (fun s => moment s G) := by
    unfold moment
    apply measurable_const.mul
    apply Finset.measurable_sum
    intro j hj
    have htj : Measurable (fun s :
        SourceSample 𝒳 n × TargetSample 𝒳 (N n) => s.2 j) :=
      (measurable_pi_apply j).comp measurable_snd
    apply (measurable_const.div (hq.comp htj)).mul
    apply Finset.measurable_sum
    intro i hi
    have hsi : Measurable (fun s :
        SourceSample 𝒳 n × TargetSample 𝒳 (N n) => s.1 i) :=
      (measurable_pi_apply i).comp measurable_fst
    have hsix : Measurable (fun s :
        SourceSample 𝒳 n × TargetSample 𝒳 (N n) => (s.1 i).1) :=
      measurable_fst.comp hsi
    apply Measurable.ite
    · exact hsameCell.preimage (hsix.prodMk htj)
    · exact hG.comp hsi
    · exact measurable_const
  let scale : TargetSample 𝒳 (N n) → ℝ := fun target =>
    ((N n : ℝ) * (N n - 1 : ℕ))⁻¹ *
      ∑ j, ∑ l, if j ≠ l then kernel (target j) (target l) else 0
  have hscale : Measurable scale := by
    unfold scale
    apply measurable_const.mul
    apply Finset.measurable_sum
    intro j hj
    apply Finset.measurable_sum
    intro l hl
    split_ifs
    · have hp : Measurable (fun target : TargetSample 𝒳 (N n) =>
          (target j, target l)) :=
        (measurable_pi_apply j).prodMk (measurable_pi_apply l)
      simpa [Function.uncurry] using hkernel.fun_comp hp
    · exact measurable_const
  have hrange : MeasurableSet (Set.range cell) := by
    rw [show Set.range cell = ⋃ i, {cell i} by
      ext x
      simp]
    exact MeasurableSet.iUnion hcell
  let support : Set (TwoSample 𝒳 n (N n) × ℝ) :=
    {p | (∀ i, (p.1.1 i).1 ∈ Set.range cell) ∧
      (∀ j, p.1.2 j ∈ Set.range cell)}
  have hsupport : MeasurableSet support := by
    rw [show support =
        (⋂ i, {p | (p.1.1 i).1 ∈ Set.range cell}) ∩
          ⋂ j, {p | p.1.2 j ∈ Set.range cell} by
      ext p
      simp [support]]
    exact (MeasurableSet.iInter fun i =>
        hrange.preimage
          (measurable_fst.comp
            ((measurable_pi_apply i).comp
              (measurable_fst.comp measurable_fst)))).inter
      (MeasurableSet.iInter fun j =>
        hrange.preimage
          ((measurable_pi_apply j).comp
            (measurable_snd.comp measurable_fst)))
  have hmoment_eq (p : TwoSample 𝒳 n (N n) × ℝ) (hp : p ∈ support)
      (G : SourceObs 𝒳 → ℝ) :
      crossAverage q p.1.1 p.1.2 G = moment p.1 G := by
    unfold crossAverage Causalean.Stat.crossAverage
      Causalean.Stat.cellMoment moment
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    have hiRange := hp.1 i
    have hjRange := hp.2 j
    simp only [Set.mem_range] at hiRange hjRange
    rcases hiRange with ⟨a, ha⟩
    rcases hjRange with ⟨b, hb⟩
    by_cases hEq : (p.1.1 i).1 = p.1.2 j
    · have hs : sameCell (p.1.1 i).1 (p.1.2 j) :=
        ⟨b, hEq.trans hb.symm, hb.symm⟩
      have hs' : sameCell (p.1.2 j) (p.1.2 j) :=
        ⟨b, hb.symm, hb.symm⟩
      simp [hEq, hs, hs']
    · have hnot : ¬ sameCell (p.1.1 i).1 (p.1.2 j) := by
        rintro ⟨a, ha', hb'⟩
        exact hEq (ha'.trans hb'.symm)
      simp [hEq, hnot]
  have hscale_eq (p : TwoSample 𝒳 n (N n) × ℝ) (hp : p ∈ support) :
      collisionScale q p.1.2 = scale p.1.2 := by
    unfold collisionScale Causalean.Stat.collisionScale scale
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro l hl
    by_cases hjl : j = l
    · simp [hjl]
    · unfold Causalean.Stat.collisionKernel kernel
      have hjRange := hp.2 j
      have hlRange := hp.2 l
      simp only [Set.mem_range] at hjRange hlRange
      rcases hjRange with ⟨a, ha⟩
      rcases hlRange with ⟨b, hb⟩
      by_cases hEq : p.1.2 j = p.1.2 l
      · have hs : sameCell (p.1.2 j) (p.1.2 l) :=
          ⟨b, hEq.trans hb.symm, hb.symm⟩
        have hs' : sameCell (p.1.2 l) (p.1.2 l) :=
          ⟨b, hb.symm, hb.symm⟩
        simp [hjl, hEq, hs, hs']
      · have hnot : ¬ sameCell (p.1.2 j) (p.1.2 l) := by
          rintro ⟨a, ha', hb'⟩
          exact hEq (ha'.trans hb'.symm)
        simp [hEq, hnot]
  by_cases hsmall : N n < 2
  · have hparam : MeasurableSet parameterSpace := by
      simp [parameterSpace]
    change MeasurableSet (support ∩
      {p : TwoSample 𝒳 n (N n) × ℝ | p.2 ∈
        regularCellInversion q e L p.1.1 p.1.2})
    simp only [regularCellInversion, hsmall, ↓reduceIte]
    exact hsupport.inter (hparam.preimage measurable_snd)
  · have htheta : MeasurableSet {p : TwoSample 𝒳 n (N n) × ℝ |
        p.2 ∈ parameterSpace} := by
      exact (by simp [parameterSpace] :
        MeasurableSet parameterSpace).preimage measurable_snd
    have hineq : MeasurableSet {p : TwoSample 𝒳 n (N n) × ℝ |
        |moment p.1 Gy - p.2 * moment p.1 Gd| ≤
          L * Real.sqrt ((1 + scale p.1.2) / n)} := by
      exact measurableSet_le
        (((hmoment Gy hGy).comp measurable_fst).sub
          (measurable_snd.mul
            ((hmoment Gd hGd).comp measurable_fst))).abs
        (measurable_const.mul
          (Real.continuous_sqrt.measurable.comp
            ((measurable_const.add (hscale.comp (by fun_prop))).div_const n)))
    change MeasurableSet (support ∩
      {p : TwoSample 𝒳 n (N n) × ℝ |
        p.2 ∈ regularCellInversion q e L p.1.1 p.1.2})
    rw [show support ∩ {p : TwoSample 𝒳 n (N n) × ℝ |
          p.2 ∈ regularCellInversion q e L p.1.1 p.1.2} =
        support ∩ ({p | p.2 ∈ parameterSpace} ∩
          {p | |moment p.1 Gy - p.2 * moment p.1 Gd| ≤
            L * Real.sqrt ((1 + scale p.1.2) / n)}) by
      ext p
      by_cases hp : p ∈ support
      · simp only [Set.mem_setOf_eq, hp, true_and, Set.mem_inter_iff]
        simp only [regularCellInversion, hsmall, ↓reduceIte,
          Set.mem_setOf_eq]
        rw [hmoment_eq p hp Gy, hmoment_eq p hp Gd, hscale_eq p hp]
      · simp [hp]]
    exact hsupport.inter (htheta.inter hineq)

/-- The regular-cell procedure, which receives cell masses and propensity but
not the transport weight. -/
noncomputable def regularCellProcedure (N k : ℕ → ℕ) (L : ℝ) :
    RegularCellProcedure 𝒳 N k where
  set n input :=
    regularCellInversion
      (cellVectorExtension input.design input.q)
      (cellVectorExtension input.design input.e)
      L input.sample.1 input.sample.2
  subset n input := by
    intro theta htheta
    by_cases hsmall : N n < 2
    · simpa [regularCellInversion, hsmall] using htheta
    · simp only [regularCellInversion, hsmall, ↓reduceIte] at htheta
      exact htheta.1
  measurableGraph n design q e :=
    regularCellInversion_measurableGraph_on_cells N k L n
      design.cell design.measurableCell
      (cellVectorExtension design q) (cellVectorExtension design e)
      (measurable_cellVectorExtension design q)
      (measurable_cellVectorExtension design e)

/-- On a regular finite-cell law, the bundled finite-vector input agrees
almost surely with the ambient mass-and-propensity inversion. -/
lemma regularCellProcedure_set_eq_ambient_ae
    {N k : ℕ → ℕ} {c epsilon cminus cplus : ℝ}
    (L : ℝ) (n : ℕ) (P : TransportedArray 𝒳)
    (hP : RegularFiniteCellClass P N k c epsilon cminus cplus n) :
    ∀ᵐ s ∂twoSampleLaw P N n,
      (regularCellProcedure (𝒳 := 𝒳) N k L).set n
          (regularCellInputOfClass P hP s) =
        regularCellInversion (sourceCellMass P n) (P.propensity n)
          L s.1 s.2 := by
  classical
  let design := regularCellDesignOfClass P hP
  have hrange : sourceXLaw P n (Set.range design.cell) = 1 :=
    (Classical.choose_spec hP.2.2.2.2.2).2.1
  have hrangeMeas : MeasurableSet (Set.range design.cell) := by
    rw [show Set.range design.cell = ⋃ i, {design.cell i} by
      ext x
      simp]
    exact MeasurableSet.iUnion design.measurableCell
  letI : IsProbabilityMeasure (sourceObsLaw P n) :=
    hP.1.twoSampleArray.2.1 n
  letI : IsProbabilityMeasure (targetXLaw P n) :=
    hP.1.twoSampleArray.2.2.1 n
  letI : IsProbabilityMeasure (sourceXLaw P n) := by
    unfold sourceXLaw
    exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  letI : IsProbabilityMeasure (twoSampleLaw P N n) := by
    unfold twoSampleLaw
    infer_instance
  have hsourceX : ∀ᵐ x ∂sourceXLaw P n, x ∈ Set.range design.cell :=
    (mem_ae_iff_prob_eq_one hrangeMeas).2 hrange
  have hsourceObs :
      ∀ᵐ o ∂sourceObsLaw P n, o.1 ∈ Set.range design.cell := by
    unfold sourceXLaw at hsourceX
    exact ae_of_ae_map measurable_fst.aemeasurable hsourceX
  have hsource :
      ∀ᵐ source ∂Measure.pi (fun _ : Fin n => sourceObsLaw P n),
        ∀ i, (source i).1 ∈ Set.range design.cell := by
    apply Measure.ae_pi_le_pi
    exact Filter.eventually_pi fun _ => hsourceObs
  have hrangeCompl : sourceXLaw P n (Set.range design.cell)ᶜ = 0 := by
    rw [measure_compl hrangeMeas (measure_ne_top _ _), hrange, measure_univ]
    simp
  have htargetX :
      ∀ᵐ x ∂targetXLaw P n, x ∈ Set.range design.cell := by
    have hzero := hP.1.transportDomination hrangeCompl
    change Set.range design.cell ∈ ae (targetXLaw P n)
    rw [mem_ae_iff]
    exact hzero
  have htarget :
      ∀ᵐ target ∂Measure.pi (fun _ : Fin (N n) => targetXLaw P n),
        ∀ j, target j ∈ Set.range design.cell := by
    apply Measure.ae_pi_le_pi
    exact Filter.eventually_pi fun _ => htargetX
  let SG : Set (SourceSample 𝒳 n) :=
    {source | ∀ i, (source i).1 ∈ Set.range design.cell}
  let TG : Set (TargetSample 𝒳 (N n)) :=
    {target | ∀ j, target j ∈ Set.range design.cell}
  have hSGmeas : MeasurableSet SG := by
    rw [show SG = ⋂ i, {source | (source i).1 ∈ Set.range design.cell} by
      ext source
      simp [SG]]
    exact MeasurableSet.iInter fun i => hrangeMeas.preimage
      (measurable_fst.comp (measurable_pi_apply i))
  have hTGmeas : MeasurableSet TG := by
    rw [show TG = ⋂ j, {target | target j ∈ Set.range design.cell} by
      ext target
      simp [TG]]
    exact MeasurableSet.iInter fun j =>
      hrangeMeas.preimage (measurable_pi_apply j)
  have hprod : twoSampleLaw P N n (SG ×ˢ TG) = 1 := by
    unfold twoSampleLaw
    rw [Measure.prod_prod,
      (mem_ae_iff_prob_eq_one hSGmeas).1 hsource,
      (mem_ae_iff_prob_eq_one hTGmeas).1 htarget]
    simp
  have hprodAE : ∀ᵐ s ∂twoSampleLaw P N n, s ∈ SG ×ˢ TG :=
    (mem_ae_iff_prob_eq_one (hSGmeas.prod hTGmeas)).2 hprod
  filter_upwards [hprodAE] with s hs
  have hq : ∀ j,
      cellVectorExtension design
          (fun i => sourceCellMass P n (design.cell i)) (s.2 j) =
        sourceCellMass P n (s.2 j) := by
    intro j
    obtain ⟨i, hi⟩ := hs.2 j
    rw [← hi, cellVectorExtension_apply_cell]
  have he : ∀ i,
      cellVectorExtension design
          (fun j => P.propensity n (design.cell j)) (s.1 i).1 =
        P.propensity n (s.1 i).1 := by
    intro i
    obtain ⟨j, hj⟩ := hs.1 i
    rw [← hj, cellVectorExtension_apply_cell]
  unfold regularCellInputOfClass regularCellProcedure
  change regularCellInversion
      (cellVectorExtension design
        (fun i => sourceCellMass P n (design.cell i)))
      (cellVectorExtension design
        (fun i => P.propensity n (design.cell i))) L s.1 s.2 = _
  unfold regularCellInversion crossAverage collisionScale
    Causalean.Stat.crossAverage Causalean.Stat.cellMoment
    Causalean.Stat.collisionScale Causalean.Stat.collisionKernel
    oracleInstrumentScore
  simp_rw [hq, he]

/-! ## R1.1: finite-cell transport geometry -/

/-- A probability distribution supported on finitely many measurable cells is the sum of point masses at those cells, each weighted by its cell probability. -/
lemma measure_eq_fin_sum_smul_dirac_of_range
    (μ : Measure 𝒳) [IsProbabilityMeasure μ] {m : ℕ}
    (cell : Fin m ↪ 𝒳) (hcell : ∀ i, MeasurableSet {cell i})
    (hrange : μ (Set.range cell) = 1) :
    μ = ∑ i, μ {cell i} • Measure.dirac (cell i) := by
  exact Causalean.Mathlib.MeasureTheory.measure_eq_fin_sum_smul_dirac_of_range
    μ cell hcell (by simpa only [measure_univ] using hrange)

/-- A property that holds almost everywhere also holds at any point assigned strictly positive probability. -/
lemma property_at_of_ae_of_singleton_pos
    (μ : Measure 𝒳) (p : 𝒳 → Prop) {x : 𝒳}
    (hp : ∀ᵐ y ∂μ, p y) (hx : 0 < (μ {x}).toReal) :
    p x := by
  exact Causalean.Mathlib.MeasureTheory.property_at_of_ae_of_singleton_pos
    μ p hp (by
      intro hzero
      simp [hzero] at hx)

/-- Every strongly measurable real-valued function is integrable under a probability distribution supported on finitely many measurable cells. -/
lemma integrable_of_finite_support
    (μ : Measure 𝒳) [IsProbabilityMeasure μ] {m : ℕ}
    (cell : Fin m ↪ 𝒳) (hcell : ∀ i, MeasurableSet {cell i})
    (hrange : μ (Set.range cell) = 1) (f : 𝒳 → ℝ)
    (hf : StronglyMeasurable f) :
    Integrable f μ := by
  exact Causalean.Mathlib.MeasureTheory.integrable_of_finite_atomic_support
    μ cell hcell (by simpa only [measure_univ] using hrange) f hf

/-- On the class-supplied finite support the RN weight is the target/source
point-mass ratio, and Kish dispersion is the corresponding finite sum. -/
lemma regularCell_transportWeight_and_kish
    (P : TransportedArray 𝒳) (N k : ℕ → ℕ)
    (c epsilon cminus cplus : ℝ) (n : ℕ)
    (hP : RegularFiniteCellClass P N k c epsilon cminus cplus n) :
    ∃ cell : Fin (k n) ↪ 𝒳,
      sourceXLaw P n (Set.range cell) = 1 ∧
      (∀ i, transportWeight P n (cell i) =
        (targetXLaw P n {cell i}).toReal /
          sourceCellMass P n (cell i)) ∧
      kishDispersion P n =
        ∑ i, (targetXLaw P n {cell i}).toReal ^ 2 /
          sourceCellMass P n (cell i) := by
  classical
  rcases hP with
    ⟨hIV, hk, hcminus, hcminus_one, hcplus, cell, hcell, hrange, hmass⟩
  letI : IsProbabilityMeasure (sourceObsLaw P n) :=
    hIV.twoSampleArray.2.1 n
  letI : IsProbabilityMeasure (sourceXLaw P n) := by
    unfold sourceXLaw
    exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  letI : IsProbabilityMeasure (targetXLaw P n) :=
    hIV.twoSampleArray.2.2.1 n
  have hsourcePos (i : Fin (k n)) :
      0 < sourceCellMass P n (cell i) := by
    exact lt_of_lt_of_le
      (div_pos hcminus (by exact_mod_cast hk))
      (hmass i).1
  have hrnStrong :
      StronglyMeasurable
        (fun x => ((targetXLaw P n).rnDeriv (sourceXLaw P n) x).toReal) :=
    (Measure.measurable_rnDeriv (targetXLaw P n) (sourceXLaw P n)).ennreal_toReal
      |>.stronglyMeasurable
  have hratio (i : Fin (k n)) :
      transportWeight P n (cell i) =
        (targetXLaw P n {cell i}).toReal /
          sourceCellMass P n (cell i) := by
    have hRN :=
      Measure.setIntegral_toReal_rnDeriv'
        hIV.transportDomination (hcell i)
    rw [integral_singleton' hrnStrong] at hRN
    apply (eq_div_iff (hsourcePos i).ne').2
    simpa [transportWeight, sourceCellMass, measureReal_def, mul_comm] using hRN
  refine ⟨cell, hrange, hratio, ?_⟩
  have hmeasure :
      sourceXLaw P n =
        ∑ i, sourceXLaw P n {cell i} • Measure.dirac (cell i) :=
    measure_eq_fin_sum_smul_dirac_of_range
      (sourceXLaw P n) cell hcell hrange
  have hweightStrong :
      StronglyMeasurable (fun x => (transportWeight P n x) ^ 2) := by
    exact
      ((Measure.measurable_rnDeriv (targetXLaw P n) (sourceXLaw P n)).ennreal_toReal
        |>.pow_const 2).stronglyMeasurable
  rw [kishDispersion, hmeasure,
    integral_finset_sum_measure]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [integral_smul_measure,
      integral_dirac' _ _ hweightStrong]
    simp only [smul_eq_mul]
    change
      sourceCellMass P n (cell i) * transportWeight P n (cell i) ^ 2 =
        (targetXLaw P n {cell i}).toReal ^ 2 /
          sourceCellMass P n (cell i)
    rw [hratio i]
    field_simp [(hsourcePos i).ne']
  · intro i hi
    exact
      (integrable_dirac' hweightStrong (by simp)).smul_measure
        (measure_ne_top (sourceXLaw P n) {cell i})

/-! ## R1.2: score means and envelopes -/

/-- The inverse-propensity affine score has the paper's `2 / epsilon`
envelope. -/
lemma abs_regularCellScore_le
    (e : 𝒳 → ℝ) (epsilon theta : ℝ) (o : SourceObs 𝒳)
    (hepsilon : 0 < epsilon)
    (hoverlap : epsilon ≤ e o.1 ∧ e o.1 ≤ 1 - epsilon)
    (htheta : theta ∈ parameterSpace)
    (hy : o.2.2.2 ∈ Set.Icc (0 : ℝ) 1) :
    |regularCellScore e theta o| ≤ 2 / epsilon := by
  unfold parameterSpace at htheta
  have hthetaAbs : |theta| ≤ 1 := (abs_le).2 htheta
  have hyAbs : |o.2.2.2| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hy.1, hy.2]
  have hdAbs : |boolReal o.2.2.1| ≤ 1 := by
    cases o.2.2.1 <;> simp [boolReal]
  have hres : |o.2.2.2 - theta * boolReal o.2.2.1| ≤ 2 := by
    calc
      _ ≤ |o.2.2.2| + |theta * boolReal o.2.2.1| := abs_sub _ _
      _ = |o.2.2.2| + |theta| * |boolReal o.2.2.1| := by rw [abs_mul]
      _ ≤ 1 + 1 * 1 := by gcongr
      _ = 2 := by norm_num
  have hscore : |oracleInstrumentScore e o| ≤ 1 / epsilon := by
    unfold oracleInstrumentScore
    split
    · rw [abs_div, abs_one,
        abs_of_pos (lt_of_lt_of_le hepsilon hoverlap.1)]
      exact one_div_le_one_div_of_le hepsilon hoverlap.1
    · have hden : 0 < 1 - e o.1 := by linarith
      rw [abs_div, abs_neg, abs_one, abs_of_pos hden]
      exact one_div_le_one_div_of_le hepsilon (by linarith)
  rw [regularCellScore, abs_mul]
  calc
    |oracleInstrumentScore e o| *
        |o.2.2.2 - theta * boolReal o.2.2.1| ≤
        (1 / epsilon) * 2 :=
      mul_le_mul hscore hres (abs_nonneg _) (by positivity)
    _ = 2 / epsilon := by ring

/-- On every realized cell, the score conditional mean is
`DeltaY - theta * DeltaD`; it is bounded by two, and at the target CACE its
target-mass average is zero. -/
lemma regularCell_score_mean_properties_for_witness
    (P : TransportedArray 𝒳) (N k : ℕ → ℕ)
    (c epsilon cminus cplus : ℝ) (n : ℕ)
    (hAssignmentContrastIntegrable :
      Integrable (P.assignmentContrast n true) (sourceXLaw P n))
    (hReceiptContrastIntegrable :
      Integrable (P.receiptContrast n true) (sourceXLaw P n))
    (hP : RegularFiniteCellClass P N k c epsilon cminus cplus n)
    (cell : Fin (k n) ↪ 𝒳)
    (hcell : ∀ i, MeasurableSet {cell i})
    (hrange : sourceXLaw P n (Set.range cell) = 1)
    (hmass : ∀ i,
      cminus / (k n : ℝ) ≤ (sourceXLaw P n {cell i}).toReal ∧
      (sourceXLaw P n {cell i}).toReal ≤ cplus / (k n : ℝ)) :
    (∀ theta ∈ parameterSpace, ∀ i,
        (∫ o in {o | o.1 = cell i},
          regularCellScore (P.propensity n) theta o ∂sourceObsLaw P n) /
            sourceCellMass P n (cell i) =
          regularCellScoreMean P n theta (cell i)) ∧
      (∀ theta ∈ parameterSpace, ∀ i,
        |regularCellScoreMean P n theta (cell i)| ≤ 2) ∧
      (∑ i, (targetXLaw P n {cell i}).toReal *
        regularCellScoreMean P n (targetCACE P n) (cell i)) = 0 := by
  classical
  have hcompact :=
    compact_causal_range P N k c epsilon n
      hAssignmentContrastIntegrable hReceiptContrastIntegrable hP.1
  rcases hcompact with
    ⟨hDeltaYEq, hDeltaDEq, hOutcomeEq, hFirstEq, hRatio, hTheta⟩
  rcases hP with
    ⟨hIV, hk, hcminus, hcminus_one, hcplus, _⟩
  letI : IsProbabilityMeasure (sourceObsLaw P n) :=
    hIV.twoSampleArray.2.1 n
  letI : IsProbabilityMeasure (sourceXLaw P n) := by
    unfold sourceXLaw
    exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  letI : IsProbabilityMeasure (targetXLaw P n) :=
    hIV.twoSampleArray.2.2.1 n
  have hsourcePos (i : Fin (k n)) :
      0 < sourceCellMass P n (cell i) := by
    exact lt_of_lt_of_le
      (div_pos hcminus (by exact_mod_cast hk))
      (hmass i).1
  have hOverlapObs : ∀ᵐ o ∂sourceObsLaw P n,
      epsilon ≤ P.propensity n o.1 ∧
        P.propensity n o.1 ≤ 1 - epsilon := by
    have hx := hIV.instrumentOverlap.2.2
    unfold sourceXLaw at hx
    exact ae_of_ae_map measurable_fst.aemeasurable hx
  have hInstrumentMeasurable : Measurable (instrumentScore P n) := by
    have hz : Measurable fun o : SourceObs 𝒳 => o.2.1 := by
      fun_prop
    have he : Measurable fun o : SourceObs 𝒳 => P.propensity n o.1 :=
      (P.propensity_measurable n).comp measurable_fst
    unfold instrumentScore
    exact Measurable.ite (hz (MeasurableSet.singleton true))
      (measurable_const.div he)
      (measurable_const.neg.div (measurable_const.sub he))
  have hInstrumentBound : ∀ᵐ o ∂sourceObsLaw P n,
      |instrumentScore P n o| ≤ 1 / epsilon := by
    filter_upwards [hOverlapObs] with o ho
    rcases o with ⟨x, z, d, y⟩
    cases z
    · simp only [instrumentScore, Bool.false_eq_true, ↓reduceIte, abs_neg,
        abs_div, abs_one]
      rw [abs_of_pos (sub_pos.mpr (lt_of_le_of_lt ho.2
        (by linarith [hIV.instrumentOverlap.1])))]
      exact one_div_le_one_div_of_le hIV.instrumentOverlap.1
        (by linarith [ho.2])
    · simp only [instrumentScore, ↓reduceIte, abs_div, abs_one]
      rw [abs_of_pos (lt_of_lt_of_le hIV.instrumentOverlap.1 ho.1)]
      exact one_div_le_one_div_of_le hIV.instrumentOverlap.1 ho.1
  have hBoolMeasurable :
      Measurable (fun o : SourceObs 𝒳 => boolReal o.2.2.1) := by
    unfold boolReal
    have hd : Measurable fun o : SourceObs 𝒳 => o.2.2.1 := by
      fun_prop
    exact Measurable.ite (hd (MeasurableSet.singleton true))
      measurable_const measurable_const
  have hOutcomeScoreIntegrable :
      Integrable (fun o =>
        instrumentScore P n o * o.2.2.2) (sourceObsLaw P n) := by
    refine Integrable.of_bound
      (hInstrumentMeasurable.mul (by fun_prop)).aestronglyMeasurable
      (1 / epsilon) ?_
    filter_upwards [hInstrumentBound, (sourceObservationFacts_of_class P N k c epsilon n hIV).2.2.1]
      with o hs hy
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hy.1]
    exact (mul_le_mul hs hy.2 hy.1
      (one_div_nonneg.mpr hIV.instrumentOverlap.1.le)).trans_eq (mul_one _)
  have hReceiptScoreIntegrable :
      Integrable (fun o =>
        instrumentScore P n o * boolReal o.2.2.1)
        (sourceObsLaw P n) := by
    refine Integrable.of_bound
      (hInstrumentMeasurable.mul hBoolMeasurable).aestronglyMeasurable
      (1 / epsilon) ?_
    filter_upwards [hInstrumentBound] with o hs
    have hd : |boolReal o.2.2.1| ≤ 1 := by
      cases o.2.2.1 <;> simp [boolReal]
    rw [Real.norm_eq_abs, abs_mul]
    exact (mul_le_mul hs hd (abs_nonneg _)
      (one_div_nonneg.mpr hIV.instrumentOverlap.1.le)).trans_eq (mul_one _)
  have hmean (theta : ℝ) (htheta : theta ∈ parameterSpace)
      (i : Fin (k n)) :
      (∫ o in {o | o.1 = cell i},
        regularCellScore (P.propensity n) theta o ∂sourceObsLaw P n) /
          sourceCellMass P n (cell i) =
        regularCellScoreMean P n theta (cell i) := by
    have hOutcomeSet :=
      (sourceObservationFacts_of_class P N k c epsilon n hIV).2.2.2.2.2.1
        ({cell i} : Set 𝒳) (hcell i)
    have hReceiptSet :=
      (sourceObservationFacts_of_class P N k c epsilon n hIV).2.2.2.2.2.2.2.1
        ({cell i} : Set 𝒳) (hcell i)
    have hscore :
        (∫ o in {o | o.1 = cell i},
          regularCellScore (P.propensity n) theta o ∂sourceObsLaw P n) =
          (∫ o in {o | o.1 ∈ ({cell i} : Set 𝒳)},
            instrumentScore P n o * o.2.2.2 ∂sourceObsLaw P n) -
          theta * (∫ o in {o | o.1 ∈ ({cell i} : Set 𝒳)},
            instrumentScore P n o * boolReal o.2.2.1
              ∂sourceObsLaw P n) := by
      change
        (∫ o in {o | o.1 ∈ ({cell i} : Set 𝒳)},
          instrumentScore P n o *
            (o.2.2.2 - theta * boolReal o.2.2.1)
            ∂sourceObsLaw P n) = _
      rw [show (fun o : SourceObs 𝒳 =>
          instrumentScore P n o *
            (o.2.2.2 - theta * boolReal o.2.2.1)) =
          (fun o => instrumentScore P n o * o.2.2.2 -
            theta * (instrumentScore P n o * boolReal o.2.2.1)) by
        funext o
        ring]
      rw [integral_sub hOutcomeScoreIntegrable.integrableOn
        (hReceiptScoreIntegrable.const_mul theta).integrableOn,
        integral_const_mul]
    rw [hscore, hOutcomeSet, hReceiptSet,
      integral_singleton' (P.deltaY_measurable n).stronglyMeasurable,
      integral_singleton' (P.deltaD_measurable n).stronglyMeasurable]
    change
      (sourceCellMass P n (cell i) * P.deltaY n (cell i) -
        theta * (sourceCellMass P n (cell i) * P.deltaD n (cell i))) /
          sourceCellMass P n (cell i) =
        P.deltaY n (cell i) - theta * P.deltaD n (cell i)
    field_simp [(hsourcePos i).ne']
  have hbound (theta : ℝ) (htheta : theta ∈ parameterSpace)
      (i : Fin (k n)) :
      |regularCellScoreMean P n theta (cell i)| ≤ 2 := by
    have hy := property_at_of_ae_of_singleton_pos
      (sourceXLaw P n) (fun x => P.deltaY n x ∈ Set.Icc (-1 : ℝ) 1)
      (sourceObservationFacts_of_class P N k c epsilon n hIV).2.2.2.2.2.2.1 (hsourcePos i)
    have hd := property_at_of_ae_of_singleton_pos
      (sourceXLaw P n) (fun x => P.deltaD n x ∈ Set.Icc (0 : ℝ) 1)
      (sourceObservationFacts_of_class P N k c epsilon n hIV).2.2.2.2.2.2.2.2 (hsourcePos i)
    have hthetaAbs : |theta| ≤ 1 := by
      exact (abs_le).2 htheta
    have hyAbs : |P.deltaY n (cell i)| ≤ 1 :=
      (abs_le).2 hy
    have hdAbs : |P.deltaD n (cell i)| ≤ 1 := by
      rw [abs_of_nonneg hd.1]
      exact hd.2
    unfold regularCellScoreMean
    calc
      |P.deltaY n (cell i) - theta * P.deltaD n (cell i)| ≤
          |P.deltaY n (cell i)| +
            |theta| * |P.deltaD n (cell i)| := by
          simpa [abs_mul] using
            (abs_sub (P.deltaY n (cell i))
              (theta * P.deltaD n (cell i)))
      _ ≤ 1 + 1 * 1 := by gcongr
      _ = 2 := by norm_num
  refine ⟨hmean, hbound, ?_⟩
  have hrangeMeas : MeasurableSet (Set.range cell) := by
    rw [show Set.range cell = ⋃ i, {cell i} by
      ext x
      simp]
    exact MeasurableSet.iUnion hcell
  have hsourceCompl : sourceXLaw P n (Set.range cell)ᶜ = 0 := by
    rw [measure_compl hrangeMeas (measure_ne_top _ _), hrange, measure_univ]
    simp
  have htargetCompl : targetXLaw P n (Set.range cell)ᶜ = 0 :=
    hIV.transportDomination hsourceCompl
  have htargetRange : targetXLaw P n (Set.range cell) = 1 := by
    calc
      targetXLaw P n (Set.range cell) =
          targetXLaw P n Set.univ :=
        measure_of_measure_compl_eq_zero htargetCompl
      _ = 1 := measure_univ
  have htargetMeasure :
      targetXLaw P n =
        ∑ i, targetXLaw P n {cell i} • Measure.dirac (cell i) :=
    measure_eq_fin_sum_smul_dirac_of_range
      (targetXLaw P n) cell hcell htargetRange
  have hscoreMeanStrong :
      StronglyMeasurable
        (regularCellScoreMean P n (targetCACE P n)) :=
    ((P.deltaY_measurable n).sub
      (measurable_const.mul (P.deltaD_measurable n))).stronglyMeasurable
  have hsum :
      (∑ i, (targetXLaw P n {cell i}).toReal *
        regularCellScoreMean P n (targetCACE P n) (cell i)) =
        ∫ x, regularCellScoreMean P n (targetCACE P n) x
          ∂targetXLaw P n := by
    conv_rhs => rw [htargetMeasure]
    rw [integral_finset_sum_measure]
    · apply Finset.sum_congr rfl
      intro i hi
      rw [integral_smul_measure,
        integral_dirac' _ _ hscoreMeanStrong]
      simp
    · intro i hi
      exact
        (integrable_dirac' hscoreMeanStrong (by simp)).smul_measure
          (measure_ne_top (targetXLaw P n) {cell i})
  rw [hsum]
  have hDeltaYTargetAE :
      ∀ᵐ x ∂targetXLaw P n, |P.deltaY n x| ≤ 1 := by
    apply hIV.transportDomination.ae_le
    filter_upwards [(sourceObservationFacts_of_class P N k c epsilon n hIV).2.2.2.2.2.2.1] with x hx
    exact (abs_le).2 hx
  have hDeltaDTargetAE :
      ∀ᵐ x ∂targetXLaw P n, |P.deltaD n x| ≤ 1 := by
    apply hIV.transportDomination.ae_le
    filter_upwards [(sourceObservationFacts_of_class P N k c epsilon n hIV).2.2.2.2.2.2.2.2] with x hx
    rw [abs_of_nonneg hx.1]
    exact hx.2
  have hDeltaYTargetInt :
      Integrable (P.deltaY n) (targetXLaw P n) :=
    Integrable.of_bound (P.deltaY_measurable n).aestronglyMeasurable
      1 (hDeltaYTargetAE.mono fun x hx => by simpa [Real.norm_eq_abs] using hx)
  have hDeltaDTargetInt :
      Integrable (P.deltaD n) (targetXLaw P n) :=
    Integrable.of_bound (P.deltaD_measurable n).aestronglyMeasurable
      1 (hDeltaDTargetAE.mono fun x hx => by simpa [Real.norm_eq_abs] using hx)
  have hOutcomeTarget :
      (∫ x, P.deltaY n x ∂targetXLaw P n) =
        transportedOutcomeITT P n := by
    simpa [transportedOutcomeITT, transportWeight, smul_eq_mul] using
      (integral_rnDeriv_smul
        (μ := targetXLaw P n) (ν := sourceXLaw P n)
        (f := P.deltaY n) hIV.transportDomination).symm
  have hFirstTarget :
      (∫ x, P.deltaD n x ∂targetXLaw P n) =
        transportedFirstStage P n := by
    rw [transportedFirstStage_eq_weighted_deltaD P k epsilon n
      (sourceObservationFacts_of_class P N k c epsilon n hIV)
      hIV.instrumentOverlap hIV.weightEnvelope]
    simpa [transportWeight, smul_eq_mul] using
      (integral_rnDeriv_smul
        (μ := targetXLaw P n) (ν := sourceXLaw P n)
        (f := P.deltaD n) hIV.transportDomination).symm
  simp only [regularCellScoreMean]
  rw [integral_sub hDeltaYTargetInt
      (hDeltaDTargetInt.const_mul (targetCACE P n)),
    integral_const_mul, hOutcomeTarget, hFirstTarget]
  have hfirstPos : 0 < transportedFirstStage P n := by
    rw [hFirstEq]
    exact hIV.targetComplierPositivity
  rw [div_eq_iff hfirstPos.ne'] at hRatio
  linarith

/-- On every realized cell, the score conditional mean is
`DeltaY - theta * DeltaD`; it is bounded by two, and at the target CACE its
target-mass average is zero. -/
lemma regularCell_score_mean_properties
    (P : TransportedArray 𝒳) (N k : ℕ → ℕ)
    (c epsilon cminus cplus : ℝ) (n : ℕ)
    (hAssignmentContrastIntegrable :
      Integrable (P.assignmentContrast n true) (sourceXLaw P n))
    (hReceiptContrastIntegrable :
      Integrable (P.receiptContrast n true) (sourceXLaw P n))
    (hP : RegularFiniteCellClass P N k c epsilon cminus cplus n) :
    ∃ cell : Fin (k n) ↪ 𝒳,
      (∀ theta ∈ parameterSpace, ∀ i,
        (∫ o in {o | o.1 = cell i},
          regularCellScore (P.propensity n) theta o ∂sourceObsLaw P n) /
            sourceCellMass P n (cell i) =
          regularCellScoreMean P n theta (cell i)) ∧
      (∀ theta ∈ parameterSpace, ∀ i,
        |regularCellScoreMean P n theta (cell i)| ≤ 2) ∧
      (∑ i, (targetXLaw P n {cell i}).toReal *
        regularCellScoreMean P n (targetCACE P n) (cell i)) = 0 := by
  rcases hP with
    ⟨hIV, hk, hcminus, hcminus_one, hcplus,
      cell, hcell, hrange, hmass⟩
  refine ⟨cell, regularCell_score_mean_properties_for_witness
    P N k c epsilon cminus cplus n
    hAssignmentContrastIntegrable hReceiptContrastIntegrable
    ⟨hIV, hk, hcminus, hcminus_one, hcplus,
      cell, hcell, hrange, hmass⟩
    cell hcell hrange hmass⟩

/-! ## R1.3: cross-average identity -/

/-- The cross average equals the source-sample average of the score weighted by each source observation's empirical target-cell mass divided by its cell mass. -/
lemma crossAverage_eq_empirical
    (q : 𝒳 → ℝ) {n N : ℕ}
    (source : SourceSample 𝒳 n) (target : TargetSample 𝒳 N)
    (G : SourceObs 𝒳 → ℝ) :
    crossAverage q source target G =
      (n : ℝ)⁻¹ * ∑ i,
        (targetEmpiricalMass target (source i).1 / q (source i).1) *
          G (source i) := by
  classical
  unfold crossAverage targetEmpiricalMass Causalean.Stat.crossAverage
    Causalean.Stat.cellMoment Causalean.Stat.empiricalMass
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  ring_nf
  rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hji : target j = (source i).1
  · rw [hji]
    simp only [ite_true]
    ring
  · have hij : (source i).1 ≠ target j := by simpa [eq_comm] using hji
    simp only [if_neg hji, if_neg hij]
    ring

/-- The difference of the two cross averages is the source average weighted
by empirical target masses. -/
lemma regularCell_crossAverage_identity
    (q e : 𝒳 → ℝ) (theta : ℝ) {n N : ℕ}
    (source : SourceSample 𝒳 n) (target : TargetSample 𝒳 N) :
    regularCellContrastMoment q e theta source target =
      (n : ℝ)⁻¹ * ∑ i,
        (targetEmpiricalMass target (source i).1 / q (source i).1) *
          regularCellScore e theta (source i) := by
  rw [regularCellContrastMoment, regularCellOutcomeMoment,
    regularCellReceiptMoment, crossAverage_eq_empirical,
    crossAverage_eq_empirical]
  simp only [regularCellScore]
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-! ## R1.4--R1.6: conditional and multinomial moments -/

/-- The expectation of an average of independent draws equals the population expectation of the summand. -/
lemma iid_average_integral
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (m : ℕ) (hm : 0 < m)
    (F : Ω → ℝ) (hF : MemLp F 2 μ) :
    (∫ sample : Fin m → Ω,
        (m : ℝ)⁻¹ * ∑ i, F (sample i)
        ∂Measure.pi (fun _ : Fin m => μ)) =
      ∫ o, F o ∂μ := by
  exact Causalean.Mathlib.Probability.iid_average_integral μ m hm F
    (hF.integrable (by norm_num))

/-- The variance of an average of positive-number independent draws equals the summand variance divided by the sample size. -/
lemma iid_average_variance
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (m : ℕ) (hm : 0 < m)
    (F : Ω → ℝ) (hF : MemLp F 2 μ) :
    variance
        (fun sample : Fin m → Ω =>
          (m : ℝ)⁻¹ * ∑ i, F (sample i))
      (Measure.pi (fun _ : Fin m => μ)) =
      (m : ℝ)⁻¹ * variance F μ := by
  exact Causalean.Mathlib.Probability.iid_average_variance μ m F hF

end CausalSmith.Stat.TransportedLateStrengthFrontier
