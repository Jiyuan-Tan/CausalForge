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
import CausalSmith.Stat.STAT_TransportedLateStrengthFrontier_Research.Helpers.RegularCellRisk_Part1
import CausalSmith.Stat.STAT_TransportedLateStrengthFrontier_Research.Helpers.RegularCellRisk_Part2
import CausalSmith.Stat.STAT_TransportedLateStrengthFrontier_Research.Helpers.RegularCellRisk_Part3
import CausalSmith.Stat.STAT_TransportedLateStrengthFrontier_Research.Helpers.RegularCellRisk_Part4
import CausalSmith.Stat.STAT_TransportedLateStrengthFrontier_Research.Helpers.RegularCellRisk_Part5_Part1
import CausalSmith.Stat.STAT_TransportedLateStrengthFrontier_Research.Helpers.RegularCellRisk_Part5_Part2
import CausalSmith.Stat.STAT_TransportedLateStrengthFrontier_Research.Helpers.RegularCellRisk_Part5_Part3
import Causalean.Stat.Sample.EmpiricalMass
import Causalean.Stat.Sample.CollisionEstimator

namespace CausalSmith.Stat.TransportedLateStrengthFrontier

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology

variable {𝒳 : Type*} [MeasurableSpace 𝒳]
/-- On a regular finite-cell class member the known source-cell mass function
is measurable.  It vanishes off the class's finite cell support, because that
support carries full source mass, and on the support it is constant on each of
the class's measurable atoms; so it is a finite sum of scaled indicators. -/
lemma regularCell_sourceCellMass_measurable
    (P : TransportedArray 𝒳) (N k : ℕ → ℕ)
    (c epsilon cminus cplus : ℝ) (n : ℕ)
    (hP : RegularFiniteCellClass P N k c epsilon cminus cplus n) :
    Measurable (sourceCellMass P n) := by
  classical
  rcases hP with
    ⟨hIV, hk, hcminus, hcminusOne, hcplus, cell, hcell, hrange, hmass⟩
  letI : IsProbabilityMeasure (sourceObsLaw P n) :=
    hIV.twoSampleArray.2.1 n
  letI : IsProbabilityMeasure (sourceXLaw P n) := by
    unfold sourceXLaw
    exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  have hrangeMeas : MeasurableSet (Set.range cell) := by
    rw [show Set.range cell = ⋃ i, {cell i} by
      ext x
      simp]
    exact MeasurableSet.iUnion hcell
  have hcompl : sourceXLaw P n (Set.range cell)ᶜ = 0 := by
    rw [measure_compl hrangeMeas (measure_ne_top _ _), hrange, measure_univ]
    simp
  have hoff (x : 𝒳) (hx : x ∉ Set.range cell) :
      sourceCellMass P n x = 0 := by
    unfold sourceCellMass
    have hsub : ({x} : Set 𝒳) ⊆ (Set.range cell)ᶜ := by
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      exact hx
    have hzero : sourceXLaw P n {x} = 0 :=
      nonpos_iff_eq_zero.mp ((measure_mono hsub).trans_eq hcompl)
    simp [hzero]
  rw [show sourceCellMass P n =
      fun x => ∑ i : Fin (k n),
        if x = cell i then sourceCellMass P n (cell i) else 0 by
    funext x
    by_cases hx : x ∈ Set.range cell
    · rcases hx with ⟨i, rfl⟩
      simp
    · rw [hoff x hx]
      symm
      apply Finset.sum_eq_zero
      intro i hi
      simp [show x ≠ cell i by
        intro h
        exact hx ⟨i, h.symm⟩]]
  apply Finset.measurable_sum
  intro i hi
  exact Measurable.ite (hcell i) measurable_const measurable_const

/-- The expected empirical target mass of a measurable cell equals its population target probability. -/
lemma integral_targetEmpiricalMass
    (μ : Measure 𝒳) [IsProbabilityMeasure μ] {m : ℕ} (hm : 0 < m)
    (a : 𝒳) (ha : MeasurableSet {a}) :
    (∫ target : Fin m → 𝒳, targetEmpiricalMass target a
        ∂Measure.pi (fun _ : Fin m => μ)) =
      μ.real {a} := by
  exact Causalean.Stat.integral_empiricalMass μ hm a ha

/-- At the target CACE the two-sample contrast moment is exactly centered: its
mean under the sampling law is zero.  This is the identification identity
`theta_T = mu_{Y,n} / mu_n` transported to the level of the cross-averaged
moments, and it is what makes the paper's Chebyshev step at
`writeup.tex:925-930` a bound on a *centered* moment. -/
lemma regularCell_contrastMoment_mean_zero
    (P : TransportedArray 𝒳) (N k : ℕ → ℕ)
    (c epsilon cminus cplus : ℝ) (n : ℕ)
    (hn : 0 < n) (hNpos : 0 < N n)
    (hP : RegularFiniteCellClass P N k c epsilon cminus cplus n) :
    (∫ s : TwoSample 𝒳 n (N n),
        regularCellContrastMoment (sourceCellMass P n) (P.propensity n)
          (targetCACE P n) s.1 s.2 ∂twoSampleLaw P N n) = 0 := by
  classical
  rcases hP with
    ⟨hIV, hk, hcm, hcmOne, hcp, cell, hcell, hrange, hmass⟩
  letI : IsProbabilityMeasure (sourceObsLaw P n) :=
    hIV.twoSampleArray.2.1 n
  letI : IsProbabilityMeasure (sourceXLaw P n) := by
    unfold sourceXLaw
    exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  letI : IsProbabilityMeasure (targetXLaw P n) :=
    hIV.twoSampleArray.2.2.1 n
  letI : IsProbabilityMeasure (twoSampleLaw P N n) := by
    unfold twoSampleLaw
    infer_instance
  have hAssignmentInt :
      Integrable (P.assignmentContrast n true) (sourceXLaw P n) :=
    integrable_of_finite_support (sourceXLaw P n) cell hcell hrange _
      (P.assignmentContrast_measurable n true).stronglyMeasurable
  have hReceiptInt :
      Integrable (P.receiptContrast n true) (sourceXLaw P n) :=
    integrable_of_finite_support (sourceXLaw P n) cell hcell hrange _
      (P.receiptContrast_measurable n true).stronglyMeasurable
  have hTheta : targetCACE P n ∈ parameterSpace := by
    rcases compact_causal_range P N k c epsilon n
      hAssignmentInt hReceiptInt hIV with ⟨_, _, _, _, _, htheta⟩
    exact htheta
  have hPfull :
      RegularFiniteCellClass P N k c epsilon cminus cplus n :=
    ⟨hIV, hk, hcm, hcmOne, hcp, cell, hcell, hrange, hmass⟩
  have hcond (target : TargetSample 𝒳 (N n)) :=
    regularCell_source_conditional_mean_variance_for_witness
      P N k c epsilon cminus cplus (targetCACE P n) n target hn
      hIV hk hcm hcmOne hcp cell hcell hrange hmass hTheta
  have hscore :=
    regularCell_score_mean_properties_for_witness
      P N k c epsilon cminus cplus n hAssignmentInt hReceiptInt hPfull
      cell hcell hrange hmass
  have hmem :=
    (regularCell_moments_memLp
      P N k c epsilon cminus cplus (targetCACE P n) n
      hn hNpos hPfull hTheta).1
  let μT := Measure.pi (fun _ : Fin (N n) => targetXLaw P n)
  have hphatMem (i : Fin (k n)) :
      MemLp (fun target : TargetSample 𝒳 (N n) =>
        targetEmpiricalMass target (cell i)) 2 μT := by
    unfold targetEmpiricalMass Causalean.Stat.empiricalMass
    apply MemLp.const_mul
    apply memLp_finset_sum
    intro j hj
    refine MemLp.of_bound ?_ 1 ?_
    · have hjmeas : Measurable fun target :
          TargetSample 𝒳 (N n) => target j :=
        measurable_pi_apply j
      exact
        (Measurable.ite (hjmeas (hcell i))
          measurable_const measurable_const).aestronglyMeasurable
    · filter_upwards with target
      split_ifs <;> simp
  unfold twoSampleLaw
  rw [integral_prod_symm _ (hmem.integrable (by norm_num))]
  calc
    (∫ target, ∫ source,
        regularCellContrastMoment (sourceCellMass P n) (P.propensity n)
          (targetCACE P n) source target
        ∂Measure.pi (fun _ : Fin n => sourceObsLaw P n)
        ∂Measure.pi (fun _ : Fin (N n) => targetXLaw P n)) =
        ∫ target, ∑ i, targetEmpiricalMass target (cell i) *
          regularCellScoreMean P n (targetCACE P n) (cell i) ∂μT := by
      apply integral_congr_ae
      filter_upwards with target
      simpa only [μT] using (hcond target).1
    _ = ∑ i, (targetXLaw P n {cell i}).toReal *
          regularCellScoreMean P n (targetCACE P n) (cell i) := by
      rw [integral_finset_sum]
      · apply Finset.sum_congr rfl
        intro i hi
        rw [integral_mul_const,
          integral_targetEmpiricalMass
            (targetXLaw P n) hNpos (cell i) (hcell i)]
        simp only [Measure.real]
      · intro i hi
        exact (hphatMem i).integrable (by norm_num) |>.mul_const _
    _ = 0 := hscore.2.2

/-! ## R1.10: honesty in the exact liminf form -/

/-- The regular-cell inversion procedure is uniformly asymptotically honest.
The conclusion is deliberately the coverage component of
`RegularCellHonest`, so the theorem assembly can use it directly. -/
lemma regularCellProcedure_coverage_liminf
    (N k : ℕ → ℕ) (c epsilon alpha cminus cplus L : ℝ)
    (hc : 0 < c)
    (hepsilon : 0 < epsilon ∧ epsilon < 1 / 2)
    (halpha : 0 < alpha ∧ alpha < 1)
    (hcminus : 0 < cminus ∧ cminus ≤ 1)
    (hcplus : 1 ≤ cplus)
    (hN : Tendsto (fun n : ℕ => (N n : ℝ) / (n : ℝ)) atTop (𝓝 c))
    (hkPos : ∀ n, 0 < k n)
    (hkInf : Tendsto (fun n : ℕ => (k n : ℝ)) atTop atTop)
    (hkRoot : Tendsto (fun n : ℕ => (k n : ℝ) / Real.sqrt n)
      atTop (𝓝 0))
    (hCarrier : ∀ n, ∃ cell : Fin (k n) ↪ 𝒳,
      ∀ i, MeasurableSet {cell i})
    (hL : Real.sqrt
      (2 * regularCellVarianceConstant epsilon c / alpha) ≤ L) :
    1 - alpha ≤ Filter.liminf
      (fun n => ⨅ P : {P : TransportedArray 𝒳 //
          RegularFiniteCellClass P N k c epsilon cminus cplus n},
        regularCellCoverage (regularCellProcedure (𝒳 := 𝒳) N k L) n P)
      atTop := by
  classical
  let δ : ℕ → ℝ := fun n =>
    ⨆ P : {P : TransportedArray 𝒳 //
        RegularFiniteCellClass P N k c epsilon cminus cplus n},
      (Measure.pi (fun _ : Fin (N n) => targetXLaw P.1 n)
        {target | regularCellKhat (sourceCellMass P.1 n) target <
          kishDispersion P.1 n / 2}).toReal
  have hδ : Tendsto δ atTop (𝓝 0) :=
    regularCell_Khat_lower_tail_uniform
      N k c epsilon cminus cplus hc hcminus hN hkRoot
  have hnpos : ∀ᶠ n : ℕ in atTop, 0 < n :=
    eventually_atTop.2 ⟨1, fun n hn => Nat.zero_lt_of_lt hn⟩
  have hNratio :
      ∀ᶠ n : ℕ in atTop, c / 2 < (N n : ℝ) / (n : ℝ) :=
    (tendsto_order.1 hN).1 _ (by linarith)
  obtain ⟨m : ℕ, hm : 2 / c < m⟩ := exists_nat_gt (2 / c)
  have hm_event : ∀ᶠ n : ℕ in atTop, m ≤ n :=
    eventually_atTop.2 ⟨m, fun _ hn => hn⟩
  have hNtwo : ∀ᶠ n : ℕ in atTop, 2 ≤ N n := by
    filter_upwards [hnpos, hNratio, hm_event] with n hn hratio hmn
    have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
    have hmnreal : (m : ℝ) ≤ n := by exact_mod_cast hmn
    have hc_n : 2 < c * (n : ℝ) := by
      have hcm : 2 < (m : ℝ) * c := (div_lt_iff₀ hc).mp hm
      have hmcn : (m : ℝ) * c ≤ (n : ℝ) * c :=
        mul_le_mul_of_nonneg_right hmnreal hc.le
      nlinarith
    have hNreal : c * (n : ℝ) / 2 < (N n : ℝ) := by
      apply (lt_div_iff₀ hnreal).mp at hratio
      nlinarith
    exact_mod_cast (show (1 : ℝ) < N n by linarith)
  have hvariance :=
    regularCell_eventually_uniform_moment_variance
      (𝒳 := 𝒳)
      N k c epsilon cminus cplus hc hepsilon hcminus hcplus
      hN hkPos hkRoot
  have hrows :
      ∀ᶠ n in atTop,
        1 - alpha - δ n ≤
          ⨅ P : {P : TransportedArray 𝒳 //
              RegularFiniteCellClass P N k c epsilon cminus cplus n},
            regularCellCoverage
              (regularCellProcedure (𝒳 := 𝒳) N k L) n P := by
    filter_upwards [hnpos, hNtwo, hvariance] with n hn hN2 hvar
    obtain ⟨P₀, hP₀⟩ :=
      regularFiniteCellClass_inhabited
        N k c epsilon cminus cplus hCarrier hc hepsilon hcminus hcplus
        hN hkPos hkInf hkRoot n
    letI : Nonempty {P : TransportedArray 𝒳 //
        RegularFiniteCellClass P N k c epsilon cminus cplus n} :=
      ⟨⟨P₀, hP₀⟩⟩
    apply le_ciInf
    intro Psub
    let P := Psub.1
    have hP : RegularFiniteCellClass P N k c epsilon cminus cplus n :=
      Psub.2
    have hIV := hP.1
    have hk := hP.2.1
    have hcm := hP.2.2.1
    have hcmOne := hP.2.2.2.1
    have hcp := hP.2.2.2.2.1
    let hw := hP.2.2.2.2.2
    let cell := Classical.choose hw
    have hcell := (Classical.choose_spec hw).1
    have hrange := (Classical.choose_spec hw).2.1
    have hmass := (Classical.choose_spec hw).2.2
    have hPfull := hP
    let design := regularCellDesignOfClass P hPfull
    letI : IsProbabilityMeasure (sourceObsLaw P n) :=
      hIV.twoSampleArray.2.1 n
    letI : IsProbabilityMeasure (sourceXLaw P n) := by
      unfold sourceXLaw
      exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
    letI : IsProbabilityMeasure (targetXLaw P n) :=
      hIV.twoSampleArray.2.2.1 n
    letI : IsProbabilityMeasure (twoSampleLaw P N n) := by
      unfold twoSampleLaw
      infer_instance
    let q := sourceCellMass P n
    let e := P.propensity n
    let theta := targetCACE P n
    let R : Set (TwoSample 𝒳 n (N n)) :=
      {s | (∀ i, (s.1 i).1 ∈ Set.range cell) ∧
        (∀ j, s.2 j ∈ Set.range cell)}
    let A : Set (TwoSample 𝒳 n (N n)) :=
      {s | theta ∈
        regularCellSet (regularCellProcedure (𝒳 := 𝒳) N k L) n P hPfull s}
    let S := R ∩ A
    have hq : Measurable q := by
      exact regularCell_sourceCellMass_measurable
        P N k c epsilon cminus cplus n hPfull
    have hgraph :=
      (regularCellProcedure (𝒳 := 𝒳) N k L).measurableGraph
        n design
        (fun i => sourceCellMass P n (design.cell i))
        (fun i => P.propensity n (design.cell i))
    have hSmeas : MeasurableSet S := by
      have hp :
          Measurable fun s : TwoSample 𝒳 n (N n) => (s, theta) :=
        measurable_id.prodMk measurable_const
      have hpre := hgraph.preimage hp
      convert hpre using 1
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
      exact (prob_compl_eq_zero_iff hrangeMeas).1 htargetCompl
    let SG : Set (SourceSample 𝒳 n) :=
      {source | ∀ i, (source i).1 ∈ Set.range cell}
    let TG : Set (TargetSample 𝒳 (N n)) :=
      {target | ∀ j, target j ∈ Set.range cell}
    have hSGmeas : MeasurableSet SG := by
      rw [show SG = ⋂ i,
          {source | (source i).1 ∈ Set.range cell} by
        ext source
        simp [SG]]
      exact MeasurableSet.iInter fun i =>
        hrangeMeas.preimage
          (measurable_fst.comp (measurable_pi_apply i))
    have hTGmeas : MeasurableSet TG := by
      rw [show TG = ⋂ j,
          {target | target j ∈ Set.range cell} by
        ext target
        simp [TG]]
      exact MeasurableSet.iInter fun j =>
        hrangeMeas.preimage (measurable_pi_apply j)
    have hsourceXAE :
        ∀ᵐ x ∂sourceXLaw P n, x ∈ Set.range cell :=
      (mem_ae_iff_prob_eq_one hrangeMeas).2 hrange
    have hsourceObsAE :
        ∀ᵐ o ∂sourceObsLaw P n, o.1 ∈ Set.range cell := by
      unfold sourceXLaw at hsourceXAE
      exact ae_of_ae_map measurable_fst.aemeasurable hsourceXAE
    have hSGAE :
        ∀ᵐ source ∂Measure.pi (fun _ : Fin n => sourceObsLaw P n),
          source ∈ SG := by
      apply Measure.ae_pi_le_pi
      exact Filter.eventually_pi fun i => hsourceObsAE
    have htargetXAE :
        ∀ᵐ x ∂targetXLaw P n, x ∈ Set.range cell :=
      (mem_ae_iff_prob_eq_one hrangeMeas).2 htargetRange
    have hTGAE :
        ∀ᵐ target ∂Measure.pi (fun _ : Fin (N n) => targetXLaw P n),
          target ∈ TG := by
      apply Measure.ae_pi_le_pi
      exact Filter.eventually_pi fun j => htargetXAE
    have hSGone :
        Measure.pi (fun _ : Fin n => sourceObsLaw P n) SG = 1 :=
      (mem_ae_iff_prob_eq_one hSGmeas).1 hSGAE
    have hTGone :
        Measure.pi (fun _ : Fin (N n) => targetXLaw P n) TG = 1 :=
      (mem_ae_iff_prob_eq_one hTGmeas).1 hTGAE
    have hReq : R = SG ×ˢ TG := by
      ext s
      simp [R, SG, TG]
    have hRone : twoSampleLaw P N n R = 1 := by
      rw [hReq]
      unfold twoSampleLaw
      rw [Measure.prod_prod, hSGone, hTGone]
      simp
    have hRmeas : MeasurableSet R := by
      rw [hReq]
      exact hSGmeas.prod hTGmeas
    have hRcompl : twoSampleLaw P N n Rᶜ = 0 :=
      (prob_compl_eq_zero_iff hRmeas).2 hRone
    have hAssignmentInt :
        Integrable (P.assignmentContrast n true) (sourceXLaw P n) :=
      integrable_of_finite_support (sourceXLaw P n) cell hcell hrange _
        (P.assignmentContrast_measurable n true).stronglyMeasurable
    have hReceiptInt :
        Integrable (P.receiptContrast n true) (sourceXLaw P n) :=
      integrable_of_finite_support (sourceXLaw P n) cell hcell hrange _
        (P.receiptContrast_measurable n true).stronglyMeasurable
    have hTheta : theta ∈ parameterSpace := by
      rcases compact_causal_range P N k c epsilon n
        hAssignmentInt hReceiptInt hIV with ⟨_, _, _, _, _, htheta⟩
      exact htheta
    let Z : TwoSample 𝒳 n (N n) → ℝ := fun s =>
      regularCellContrastMoment q e theta s.1 s.2
    let KB : Set (TwoSample 𝒳 n (N n)) :=
      {s | regularCellKhat q s.2 < kishDispersion P n / 2}
    let threshold : ℝ :=
      L * Real.sqrt (kishDispersion P n / (2 * n))
    let ZB : Set (TwoSample 𝒳 n (N n)) :=
      {s | threshold < |Z s|}
    have hkappa :=
      one_le_regularCell_kish
        P N k c epsilon n hIV cell hcell hrange
    have hkappaPos : 0 < kishDispersion P n :=
      lt_of_lt_of_le zero_lt_one hkappa
    have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
    have hBpos : 0 < regularCellVarianceConstant epsilon c := by
      unfold regularCellVarianceConstant
      have heps : 0 < epsilon := hepsilon.1
      positivity
    have hargPos :
        0 < 2 * regularCellVarianceConstant epsilon c / alpha := by
      exact div_pos (mul_pos (by norm_num) hBpos) halpha.1
    have hLpos : 0 < L :=
      lt_of_lt_of_le (Real.sqrt_pos.2 hargPos) hL
    have hthresholdPos : 0 < threshold := by
      unfold threshold
      apply mul_pos hLpos
      apply Real.sqrt_pos.2
      positivity
    have hmean :
        (∫ s : TwoSample 𝒳 n (N n), Z s ∂twoSampleLaw P N n) = 0 := by
      simpa [Z, q, e, theta] using
        regularCell_contrastMoment_mean_zero
          P N k c epsilon cminus cplus n hn
            (lt_of_lt_of_le (by omega) hN2) hPfull
    have hmem : MemLp Z 2 (twoSampleLaw P N n) := by
      simpa [Z, q, e, theta] using
        (regularCell_moments_memLp
          P N k c epsilon cminus cplus (targetCACE P n) n hn
          (lt_of_lt_of_le (by omega) hN2) hPfull hTheta).1
    have hZsubset :
        ZB ⊆
          {s | threshold ≤
            |Z s - ∫ t, Z t ∂twoSampleLaw P N n|} := by
      intro s hs
      simp only [Set.mem_setOf_eq, hmean, sub_zero]
      exact le_of_lt hs
    have hcheb :=
      meas_ge_le_variance_div_sq hmem hthresholdPos
    have hZtail :
        (twoSampleLaw P N n ZB).toReal ≤ alpha := by
      calc
        (twoSampleLaw P N n ZB).toReal ≤
            (twoSampleLaw P N n
              {s | threshold ≤
                |Z s - ∫ t, Z t ∂twoSampleLaw P N n|}).toReal :=
          measureReal_mono hZsubset
        _ ≤ (ENNReal.ofReal
              (variance Z (twoSampleLaw P N n) / threshold ^ 2)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hcheb
        _ = variance Z (twoSampleLaw P N n) / threshold ^ 2 := by
          rw [ENNReal.toReal_ofReal]
          exact div_nonneg (variance_nonneg _ _) (sq_nonneg _)
        _ ≤ (regularCellVarianceConstant epsilon c *
              kishDispersion P n / n) / threshold ^ 2 := by
          gcongr
          simpa [Z, q, e, theta] using (hvar P hPfull).1
        _ = 2 * regularCellVarianceConstant epsilon c / L ^ 2 := by
          have hsqrt :
              Real.sqrt (kishDispersion P n / (2 * n)) ^ 2 =
                kishDispersion P n / (2 * n) := by
            rw [Real.sq_sqrt]
            positivity
          unfold threshold
          rw [mul_pow, hsqrt]
          field_simp [hnreal.ne', hkappaPos.ne', hLpos.ne']
        _ ≤ alpha := by
          have hsqrtSq :
              Real.sqrt
                  (2 * regularCellVarianceConstant epsilon c / alpha) ^ 2 =
                2 * regularCellVarianceConstant epsilon c / alpha := by
            rw [Real.sq_sqrt hargPos.le]
          have hLsq :
              2 * regularCellVarianceConstant epsilon c / alpha ≤ L ^ 2 := by
            have hsqrtNonneg :=
              Real.sqrt_nonneg
                (2 * regularCellVarianceConstant epsilon c / alpha)
            nlinarith
          rw [div_le_iff₀ (sq_pos_of_pos hLpos)]
          have halphaPos := halpha.1
          have := (div_le_iff₀ halphaPos).1 hLsq
          nlinarith
    have hKBtail :
        (twoSampleLaw P N n KB).toReal ≤ δ n := by
      let μS := Measure.pi (fun _ : Fin n => sourceObsLaw P n)
      let μT := Measure.pi (fun _ : Fin (N n) => targetXLaw P n)
      let Kset : Set (TargetSample 𝒳 (N n)) :=
        {target | regularCellKhat q target < kishDispersion P n / 2}
      have hpre :
          twoSampleLaw P N n KB ≤ μT Kset := by
        simpa [twoSampleLaw, KB, Kset, μS, μT] using
          (measurePreserving_snd (μ := μS) (ν := μT)).measure_preimage_le
            Kset
      have hbdd :
          BddAbove
            (Set.range fun Q :
              {Q : TransportedArray 𝒳 //
                RegularFiniteCellClass Q N k c epsilon cminus cplus n} =>
              (Measure.pi (fun _ : Fin (N n) => targetXLaw Q.1 n)
                {target |
                  regularCellKhat (sourceCellMass Q.1 n) target <
                    kishDispersion Q.1 n / 2}).toReal) := by
        refine ⟨1, ?_⟩
        rintro y ⟨Q, rfl⟩
        letI : IsProbabilityMeasure (targetXLaw Q.1 n) :=
          Q.2.1.twoSampleArray.2.2.1 n
        letI : IsProbabilityMeasure
            (Measure.pi (fun _ : Fin (N n) => targetXLaw Q.1 n)) := by
          infer_instance
        exact measureReal_le_one
      calc
        (twoSampleLaw P N n KB).toReal ≤ (μT Kset).toReal :=
          ENNReal.toReal_mono (measure_ne_top _ _) hpre
        _ ≤ δ n := by
          change
            (Measure.pi (fun _ : Fin (N n) => targetXLaw P n)
              {target |
                regularCellKhat (sourceCellMass P n) target <
                  kishDispersion P n / 2}).toReal ≤ δ n
          exact le_ciSup hbdd Psub
    have hScompSubset :
        Sᶜ ⊆ Rᶜ ∪ (KB ∪ ZB) := by
      intro s hs
      by_cases hsR : s ∈ R
      · by_cases hsK : s ∈ KB
        · exact Set.mem_union_right _ (Set.mem_union_left _ hsK)
        · by_cases hsZ : s ∈ ZB
          · exact Set.mem_union_right _ (Set.mem_union_right _ hsZ)
          · exfalso
            apply hs
            refine ⟨hsR, ?_⟩
            have hK :
                kishDispersion P n / 2 ≤ regularCellKhat q s.2 :=
              le_of_not_gt hsK
            have hZ : |Z s| ≤ threshold := le_of_not_gt hsZ
            have hratio :
                kishDispersion P n / (2 * n) ≤
                  regularCellKhat q s.2 / n := by
              calc
                kishDispersion P n / (2 * n) =
                    (kishDispersion P n / 2) / n := by ring
                _ ≤ regularCellKhat q s.2 / n := by gcongr
            have hmoment :
                |Z s| ≤
                  L * Real.sqrt (regularCellKhat q s.2 / n) := by
              exact hZ.trans
                (mul_le_mul_of_nonneg_left
                  (Real.sqrt_le_sqrt hratio) hLpos.le)
            unfold A
            change theta ∈
              regularCellInversion
                (cellVectorExtension design
                  (fun i => sourceCellMass P n (design.cell i)))
                (cellVectorExtension design
                  (fun i => P.propensity n (design.cell i)))
                L s.1 s.2
            have hqTarget : ∀ j,
                cellVectorExtension design
                    (fun i => sourceCellMass P n (design.cell i)) (s.2 j) =
                  q (s.2 j) := by
              intro j
              obtain ⟨i, hi⟩ := hsR.2 j
              rw [← hi]
              exact cellVectorExtension_apply_cell design _ i
            have heSource : ∀ i,
                cellVectorExtension design
                    (fun j => P.propensity n (design.cell j)) (s.1 i).1 =
                  e (s.1 i).1 := by
              intro i
              obtain ⟨j, hj⟩ := hsR.1 i
              rw [← hj]
              exact cellVectorExtension_apply_cell design _ j
            have hinv :
                regularCellInversion
                    (cellVectorExtension design
                      (fun i => sourceCellMass P n (design.cell i)))
                    (cellVectorExtension design
                      (fun i => P.propensity n (design.cell i)))
                    L s.1 s.2 =
                  regularCellInversion q e L s.1 s.2 := by
              unfold regularCellInversion crossAverage collisionScale
                Causalean.Stat.crossAverage Causalean.Stat.cellMoment
                Causalean.Stat.collisionScale Causalean.Stat.collisionKernel
                oracleInstrumentScore
              simp_rw [hqTarget, heSource]
            rw [hinv]
            unfold regularCellInversion
            simp only [show ¬N n < 2 by omega, ↓reduceIte,
              Set.mem_setOf_eq]
            refine ⟨hTheta, ?_⟩
            simpa [Z, q, e, theta, regularCellContrastMoment,
              regularCellOutcomeMoment, regularCellReceiptMoment,
              regularCellKhat] using hmoment
      · exact Set.mem_union_left _ hsR
    have hScomp :
        (twoSampleLaw P N n Sᶜ).toReal ≤ δ n + alpha := by
      calc
        (twoSampleLaw P N n Sᶜ).toReal ≤
            (twoSampleLaw P N n (Rᶜ ∪ (KB ∪ ZB))).toReal :=
          measureReal_mono hScompSubset
        _ ≤ (twoSampleLaw P N n Rᶜ).toReal +
              (twoSampleLaw P N n (KB ∪ ZB)).toReal :=
          by
            simpa only [Measure.real] using
              (measureReal_union_le
                (μ := twoSampleLaw P N n) Rᶜ (KB ∪ ZB))
        _ ≤ (twoSampleLaw P N n Rᶜ).toReal +
              ((twoSampleLaw P N n KB).toReal +
                (twoSampleLaw P N n ZB).toReal) := by
          gcongr
          simpa only [Measure.real] using
            (measureReal_union_le
              (μ := twoSampleLaw P N n) KB ZB)
        _ ≤ 0 + (δ n + alpha) := by
          rw [hRcompl]
          simpa using add_le_add hKBtail hZtail
        _ = δ n + alpha := zero_add _
    have hSreal :
        1 - alpha - δ n ≤ (twoSampleLaw P N n S).toReal := by
      have hcomp := hScomp
      change (twoSampleLaw P N n).real Sᶜ ≤ δ n + alpha at hcomp
      rw [probReal_compl_eq_one_sub hSmeas] at hcomp
      change 1 - alpha - δ n ≤ (twoSampleLaw P N n).real S
      linarith
    calc
      1 - alpha - δ n ≤ (twoSampleLaw P N n S).toReal := hSreal
      _ ≤ (twoSampleLaw P N n A).toReal :=
        measureReal_mono Set.inter_subset_right
      _ = regularCellCoverage
          (regularCellProcedure (𝒳 := 𝒳) N k L) n ⟨P, hPfull⟩ := by
        rfl
  have hrowUpper :
      ∀ n,
        (⨅ P : {P : TransportedArray 𝒳 //
            RegularFiniteCellClass P N k c epsilon cminus cplus n},
          regularCellCoverage
            (regularCellProcedure (𝒳 := 𝒳) N k L) n P) ≤ 1 := by
    intro n
    obtain ⟨P₀, hP₀⟩ :=
      regularFiniteCellClass_inhabited
        N k c epsilon cminus cplus hCarrier hc hepsilon hcminus hcplus
        hN hkPos hkInf hkRoot n
    have hbdd :
        BddBelow
          (Set.range fun P :
            {P : TransportedArray 𝒳 //
              RegularFiniteCellClass P N k c epsilon cminus cplus n} =>
            regularCellCoverage
              (regularCellProcedure (𝒳 := 𝒳) N k L) n P) := by
      refine ⟨0, ?_⟩
      rintro y ⟨P, rfl⟩
      exact ENNReal.toReal_nonneg
    refine (ciInf_le hbdd ⟨P₀, hP₀⟩).trans ?_
    letI : IsProbabilityMeasure (sourceObsLaw P₀ n) :=
      hP₀.1.twoSampleArray.2.1 n
    letI : IsProbabilityMeasure (targetXLaw P₀ n) :=
      hP₀.1.twoSampleArray.2.2.1 n
    letI : IsProbabilityMeasure (twoSampleLaw P₀ N n) := by
      unfold twoSampleLaw
      infer_instance
    exact measureReal_le_one
  have hlowerBounded :
      IsBoundedUnder (· ≥ ·) atTop
        (fun n => 1 - alpha - δ n) := by
    change ∃ b, ∀ᶠ n in atTop, b ≤ 1 - alpha - δ n
    have hδlt : ∀ᶠ n in atTop, δ n < 1 :=
      (tendsto_order.1 hδ).2 1 zero_lt_one
    exact ⟨-alpha, hδlt.mono fun n hn => by linarith⟩
  have hrowCobounded :
      IsCoboundedUnder (· ≥ ·) atTop
        (fun n => ⨅ P : {P : TransportedArray 𝒳 //
            RegularFiniteCellClass P N k c epsilon cminus cplus n},
          regularCellCoverage
            (regularCellProcedure (𝒳 := 𝒳) N k L) n P) := by
    change ∃ b, ∀ a, (∀ᶠ n in atTop, a ≤
      ⨅ P : {P : TransportedArray 𝒳 //
          RegularFiniteCellClass P N k c epsilon cminus cplus n},
        regularCellCoverage
          (regularCellProcedure (𝒳 := 𝒳) N k L) n P) → a ≤ b
    refine ⟨1, fun a ha => ?_⟩
    obtain ⟨n, han, hn1⟩ :=
      (ha.and (Filter.Eventually.of_forall hrowUpper)).exists
    exact han.trans hn1
  have hlowerTendsto :
      Tendsto (fun n => 1 - alpha - δ n) atTop (𝓝 (1 - alpha)) := by
    simpa using
      ((tendsto_const_nhds.sub tendsto_const_nhds).sub hδ)
  rw [← hlowerTendsto.liminf_eq]
  exact Filter.liminf_le_liminf hrows hlowerBounded hrowCobounded

/-! ## R1.11: inputs to the expected-length half -/

end CausalSmith.Stat.TransportedLateStrengthFrontier
