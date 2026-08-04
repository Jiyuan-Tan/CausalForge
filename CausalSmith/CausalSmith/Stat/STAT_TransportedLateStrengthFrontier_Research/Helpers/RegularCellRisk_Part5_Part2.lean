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
import Causalean.Stat.UStatistic.Variance
import Causalean.Stat.Sample.CollisionEstimator

namespace CausalSmith.Stat.TransportedLateStrengthFrontier

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology

variable {𝒳 : Type*} [MeasurableSpace 𝒳]
/-- Under the regular finite-cell witness conditions, the target-sample collision-scale statistic is square-integrable. -/
lemma collisionScale_memLp_for_witness
    (P : TransportedArray 𝒳) (N k : ℕ → ℕ)
    (c epsilon : ℝ) (n : ℕ)
    (hNpos : 0 < N n)
    (hIV : TransportedIVClass P N k c epsilon n)
    {m : ℕ} (hm : 0 < m) (cminus : ℝ) (hcminus : 0 < cminus)
    (cell : Fin m ↪ 𝒳)
    (hcell : ∀ i, MeasurableSet {cell i})
    (hrange : sourceXLaw P n (Set.range cell) = 1)
    (hmass : ∀ i : Fin m,
      cminus / (m : ℝ) ≤ sourceCellMass P n (cell i)) :
    MemLp (collisionScale (sourceCellMass P n)) 2
      (Measure.pi (fun _ : Fin (N n) => targetXLaw P n)) := by
  classical
  letI : IsProbabilityMeasure (sourceObsLaw P n) :=
    hIV.twoSampleArray.2.1 n
  letI : IsProbabilityMeasure (sourceXLaw P n) := by
    unfold sourceXLaw
    exact Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  letI : IsProbabilityMeasure (targetXLaw P n) :=
    hIV.twoSampleArray.2.2.1 n
  let μT := Measure.pi (fun _ : Fin (N n) => targetXLaw P n)
  let q := sourceCellMass P n
  let kernel : 𝒳 → 𝒳 → ℝ := fun x y =>
    ∑ i : Fin m, if x = cell i ∧ y = cell i then 1 / q (cell i) else 0
  let scale : TargetSample 𝒳 (N n) → ℝ := fun target =>
    ((N n : ℝ) * (N n - 1 : ℕ))⁻¹ *
      ∑ j, ∑ l, if j ≠ l then kernel (target j) (target l) else 0
  have hkernel : Measurable (Function.uncurry kernel) := by
    dsimp only [kernel]
    apply Finset.measurable_sum
    intro i hi
    apply Measurable.ite
    · exact (((hcell i).preimage measurable_fst).inter
        ((hcell i).preimage measurable_snd))
    · exact measurable_const
    · exact measurable_const
  have hscale : Measurable scale := by
    dsimp only [scale]
    apply measurable_const.mul
    apply Finset.measurable_sum
    intro j hj
    apply Finset.measurable_sum
    intro l hl
    split_ifs
    · have hp : Measurable (fun target : TargetSample 𝒳 (N n) =>
          (target j, target l)) :=
        (measurable_pi_apply j).prodMk (measurable_pi_apply l)
      simpa [Function.uncurry] using hkernel.comp hp
    · exact measurable_const
  have hmreal : 0 < (m : ℝ) := by exact_mod_cast hm
  have hcmreal : 0 < cminus / (m : ℝ) := div_pos hcminus hmreal
  have hqpos (i : Fin m) : 0 < q (cell i) :=
    hcmreal.trans_le (hmass i)
  have hqinv (i : Fin m) : 1 / q (cell i) ≤ (m : ℝ) / cminus := by
    calc
      1 / q (cell i) ≤ 1 / (cminus / (m : ℝ)) :=
        one_div_le_one_div_of_le hcmreal (hmass i)
      _ = (m : ℝ) / cminus := by
        field_simp [hcminus.ne', hmreal.ne']
  have hkernel_nonneg (x y : 𝒳) : 0 ≤ kernel x y := by
    dsimp only [kernel]
    apply Finset.sum_nonneg
    intro i hi
    split_ifs
    · exact one_div_nonneg.mpr (hqpos i).le
    · exact le_rfl
  have hkernel_bound (x y : 𝒳) :
      |kernel x y| ≤ (m : ℝ) / cminus := by
    rw [abs_of_nonneg (hkernel_nonneg x y)]
    by_cases hxy : ∃ i : Fin m, x = cell i ∧ y = cell i
    · obtain ⟨i, hxi, hyi⟩ := hxy
      dsimp only [kernel]
      rw [Finset.sum_eq_single i]
      · simpa [hxi, hyi] using hqinv i
      · intro i' hi' hne
        have hxne : x ≠ cell i' := by
          rw [hxi]
          exact fun h => hne (cell.injective h).symm
        simp [hxne]
      · simp
    · dsimp only [kernel]
      simp only [not_exists, not_and] at hxy
      have hzero :
          (∑ i : Fin m,
            if x = cell i ∧ y = cell i then 1 / q (cell i) else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        rw [if_neg]
        intro h
        exact (hxy i h.1) h.2
      rw [hzero]
      exact div_nonneg hmreal.le hcminus.le
  have hscale_bound (target : TargetSample 𝒳 (N n)) :
      |scale target| ≤ 2 * ((m : ℝ) / cminus) := by
    by_cases hNtwo : 2 ≤ N n
    · have hNreal : 0 < (N n : ℝ) := by positivity
      have hNm1real : 0 < ((N n - 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.sub_pos_of_lt hNtwo
      let S : ℝ := ∑ j, ∑ l,
        if j ≠ l then kernel (target j) (target l) else 0
      have hsum_nonneg : 0 ≤ S := by
        dsimp only [S]
        apply Finset.sum_nonneg
        intro j hj
        apply Finset.sum_nonneg
        intro l hl
        split_ifs
        · exact hkernel_nonneg _ _
        · exact le_rfl
      have hsum_le :
          S ≤ (N n : ℝ) ^ 2 * ((m : ℝ) / cminus) := by
        dsimp only [S]
        calc
          _ ≤ ∑ _j : Fin (N n), ∑ _l : Fin (N n),
              ((m : ℝ) / cminus) := by
            apply Finset.sum_le_sum
            intro j hj
            apply Finset.sum_le_sum
            intro l hl
            by_cases hjl : j ≠ l
            · rw [if_pos hjl]
              exact (le_abs_self _).trans (hkernel_bound _ _)
            · rw [if_neg hjl]
              exact (div_nonneg hmreal.le hcminus.le)
          _ = (N n : ℝ) ^ 2 * ((m : ℝ) / cminus) := by
            simp
            ring
      change
        |((N n : ℝ) * (N n - 1 : ℕ))⁻¹ * S| ≤
          2 * ((m : ℝ) / cminus)
      rw [abs_mul, abs_of_pos (inv_pos.mpr (mul_pos hNreal hNm1real)),
        abs_of_nonneg hsum_nonneg]
      calc
        ((N n : ℝ) * (N n - 1 : ℕ))⁻¹ * S ≤
            ((N n : ℝ) * (N n - 1 : ℕ))⁻¹ *
              ((N n : ℝ) ^ 2 * ((m : ℝ) / cminus)) :=
          mul_le_mul_of_nonneg_left hsum_le
            (inv_nonneg.mpr (mul_pos hNreal hNm1real).le)
        _ ≤ 2 * ((m : ℝ) / cminus) := by
          have hNm1 : (N n : ℝ) ≤ 2 * ((N n - 1 : ℕ) : ℝ) := by
            exact_mod_cast (show N n ≤ 2 * (N n - 1) by omega)
          have hratio :
              (N n : ℝ) / ((N n - 1 : ℕ) : ℝ) ≤ 2 :=
            (div_le_iff₀ hNm1real).2 hNm1
          calc
            ((N n : ℝ) * (N n - 1 : ℕ))⁻¹ *
                ((N n : ℝ) ^ 2 * ((m : ℝ) / cminus)) =
                ((N n : ℝ) / (N n - 1 : ℕ)) *
                  ((m : ℝ) / cminus) := by
              field_simp [hNreal.ne', hNm1real.ne']
              <;> ring
            _ ≤ 2 * ((m : ℝ) / cminus) :=
              mul_le_mul_of_nonneg_right hratio
                (div_nonneg hmreal.le hcminus.le)
    · have hNone : N n = 1 := by omega
      simp [scale, hNone]
      positivity
  have hscaleMem : MemLp scale 2 μT :=
    MemLp.of_bound hscale.aestronglyMeasurable
      (2 * ((m : ℝ) / cminus))
      (Filter.Eventually.of_forall fun target => by
        simpa [Real.norm_eq_abs] using hscale_bound target)
  have hrangeMeas : MeasurableSet (Set.range cell) := by
    rw [show Set.range cell = ⋃ i, {cell i} by
      ext x
      simp]
    exact MeasurableSet.iUnion hcell
  have hrangeCompl : sourceXLaw P n (Set.range cell)ᶜ = 0 := by
    rw [measure_compl hrangeMeas (measure_ne_top _ _), hrange, measure_univ]
    simp
  have htargetRange : ∀ᵐ x ∂targetXLaw P n, x ∈ Set.range cell := by
    have hc := hIV.transportDomination hrangeCompl
    change Set.range cell ∈ ae (targetXLaw P n)
    rw [mem_ae_iff]
    exact hc
  have htargetSample :
      ∀ᵐ target ∂μT, ∀ j, target j ∈ Set.range cell := by
    rw [ae_all_iff]
    intro j
    have hx : ∀ᵐ x ∂Measure.map
        (fun target : TargetSample 𝒳 (N n) => target j) μT,
        x ∈ Set.range cell := by
      rw [(measurePreserving_eval
        (fun _ : Fin (N n) => targetXLaw P n) j).map_eq]
      exact htargetRange
    exact ae_of_ae_map (measurable_pi_apply j).aemeasurable hx
  have hkernel_eq (x y : 𝒳)
      (hx : x ∈ Set.range cell) (hy : y ∈ Set.range cell) :
      collisionKernel q x y = kernel x y := by
    obtain ⟨i, hi⟩ := hx
    obtain ⟨j, hj⟩ := hy
    by_cases hxy : x = y
    · have hij : i = j := by
        apply cell.injective
        exact hi.trans (hxy.trans hj.symm)
      subst j
      have hcoll : collisionKernel q x y = 1 / q x := by
        simp [collisionKernel, Causalean.Stat.collisionKernel, hxy]
      rw [hcoll]
      dsimp only [kernel]
      rw [Finset.sum_eq_single i]
      · rw [if_pos ⟨hi.symm, hj.symm⟩, hi]
      · intro i' hi' hne
        have hxne : x ≠ cell i' := by
          intro h
          exact hne (cell.injective (hi.trans h)).symm
        simp [hxne]
      · simp
    · unfold collisionKernel Causalean.Stat.collisionKernel kernel
      rw [if_neg hxy]
      symm
      apply Finset.sum_eq_zero
      intro i' hi'
      have hnot : ¬(x = cell i' ∧ y = cell i') := by
        rintro ⟨hxi, hyi⟩
        exact hxy (hxi.trans hyi.symm)
      simp [hnot]
  have heq : scale =ᵐ[μT] collisionScale q := by
    filter_upwards [htargetSample] with target ht
    unfold scale collisionScale Causalean.Stat.collisionScale
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro l hl
    split_ifs
    · exact hkernel_eq _ _ (ht j) (ht l) |>.symm
    · rfl
  exact (memLp_congr_ae heq).1 hscaleMem

/-- The two cross moments and the collision proxy are square-integrable under
the sampling law.  The paper applies Chebyshev's inequality to each of these
three statistics (writeup.tex:918-924 and 931-934) and so presupposes exactly
this; it is pure regularity, carrying no rate or constant.  Each holds because
on a `RegularFiniteCellClass` member every ingredient is bounded: the affine
score by `2 / epsilon`, and the cell weights by `k n / cminus` on the class's
finite support. -/
lemma regularCell_moments_memLp
    (P : TransportedArray 𝒳) (N k : ℕ → ℕ)
    (c epsilon cminus cplus theta : ℝ) (n : ℕ)
    (hn : 0 < n) (hNpos : 0 < N n)
    (hP : RegularFiniteCellClass P N k c epsilon cminus cplus n)
    (htheta : theta ∈ parameterSpace) :
    MemLp
        (fun s : TwoSample 𝒳 n (N n) =>
          regularCellContrastMoment (sourceCellMass P n)
            (P.propensity n) theta s.1 s.2) 2
        (twoSampleLaw P N n) ∧
    MemLp
        (fun s : TwoSample 𝒳 n (N n) =>
          regularCellReceiptMoment (sourceCellMass P n)
            (P.propensity n) s.1 s.2) 2
        (twoSampleLaw P N n) ∧
    MemLp (collisionScale (sourceCellMass P n)) 2
        (Measure.pi (fun _ : Fin (N n) => targetXLaw P n)) := by
  classical
  rcases hP with
    ⟨hIV, hk, hcm, hcmOne, hcp, cell, hcell, hrange, hmass⟩
  have hInstrumentMeasurable : Measurable (instrumentScore P n) := by
    have hz : Measurable fun o : SourceObs 𝒳 => o.2.1 := by fun_prop
    have he : Measurable fun o : SourceObs 𝒳 => P.propensity n o.1 :=
      (P.propensity_measurable n).comp measurable_fst
    unfold instrumentScore
    exact Measurable.ite (hz (MeasurableSet.singleton true))
      (measurable_const.div he)
      (measurable_const.neg.div (measurable_const.sub he))
  have hBoolMeasurable :
      Measurable (fun o : SourceObs 𝒳 => boolReal o.2.2.1) := by
    unfold boolReal
    have hd : Measurable fun o : SourceObs 𝒳 => o.2.2.1 := by fun_prop
    exact Measurable.ite (hd (MeasurableSet.singleton true))
      measurable_const measurable_const
  have hScoreMeas :
      Measurable (regularCellScore (P.propensity n) theta) := by
    change Measurable (fun o : SourceObs 𝒳 =>
      instrumentScore P n o * (o.2.2.2 - theta * boolReal o.2.2.1))
    have hy : Measurable fun o : SourceObs 𝒳 => o.2.2.2 := by fun_prop
    exact hInstrumentMeasurable.mul
      (hy.sub (measurable_const.mul hBoolMeasurable))
  have hScoreBound : ∀ᵐ o ∂sourceObsLaw P n,
      |regularCellScore (P.propensity n) theta o| ≤ 2 / epsilon := by
    have hoverlap : ∀ᵐ o ∂sourceObsLaw P n,
        epsilon ≤ P.propensity n o.1 ∧
          P.propensity n o.1 ≤ 1 - epsilon := by
      have hx := hIV.instrumentOverlap.2.2
      unfold sourceXLaw at hx
      exact ae_of_ae_map measurable_fst.aemeasurable hx
    filter_upwards [hoverlap, (sourceObservationFacts_of_class P N k c epsilon n hIV).2.2.1] with o hoverlap hy
    exact abs_regularCellScore_le (P.propensity n) epsilon theta o
      hIV.instrumentOverlap.1 hoverlap htheta hy
  let Gd : SourceObs 𝒳 → ℝ := fun o =>
    oracleInstrumentScore (P.propensity n) o * boolReal o.2.2.1
  have hGdMeas : Measurable Gd :=
    hInstrumentMeasurable.mul hBoolMeasurable
  have hGdBound : ∀ᵐ o ∂sourceObsLaw P n, |Gd o| ≤ 1 / epsilon := by
    have hInstrumentBound : ∀ᵐ o ∂sourceObsLaw P n,
        |instrumentScore P n o| ≤ 1 / epsilon := by
      have hoverlap : ∀ᵐ o ∂sourceObsLaw P n,
          epsilon ≤ P.propensity n o.1 ∧
            P.propensity n o.1 ≤ 1 - epsilon := by
        have hx := hIV.instrumentOverlap.2.2
        unfold sourceXLaw at hx
        exact ae_of_ae_map measurable_fst.aemeasurable hx
      filter_upwards [hoverlap] with o ho
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
    filter_upwards [hInstrumentBound] with o ho
    have hd : |boolReal o.2.2.1| ≤ 1 := by
      cases o.2.2.1 <;> simp [boolReal]
    change |instrumentScore P n o * boolReal o.2.2.1| ≤ 1 / epsilon
    rw [abs_mul]
    exact (mul_le_mul ho hd (abs_nonneg _)
      (one_div_nonneg.mpr hIV.instrumentOverlap.1.le)).trans_eq (mul_one _)
  have hContrast := regularCell_cross_memLp_for_witness
    P N k c epsilon n hn hNpos hIV hk cminus hcm cell hcell hrange
    (fun i => (hmass i).1)
    (regularCellScore (P.propensity n) theta) (2 / epsilon)
    (div_nonneg (by norm_num) hIV.instrumentOverlap.1.le)
    hScoreMeas hScoreBound
  have hReceipt := regularCell_cross_memLp_for_witness
    P N k c epsilon n hn hNpos hIV hk cminus hcm cell hcell hrange
    (fun i => (hmass i).1) Gd (1 / epsilon)
    (one_div_nonneg.mpr hIV.instrumentOverlap.1.le) hGdMeas hGdBound
  refine ⟨?_, ?_, ?_⟩
  · simpa only [regularCell_crossAverage_identity] using hContrast
  · simpa only [regularCellReceiptMoment, crossAverage_eq_empirical, Gd] using
      hReceipt
  · exact collisionScale_memLp_for_witness P N k c epsilon n hNpos hIV hk
      cminus hcm cell hcell hrange (fun i => (hmass i).1)

/-! ## R1.8--R1.9: collision scale -/

set_option maxHeartbeats 800000 in
/-- A bounded off-diagonal kernel average from an independent sample has variance at most 32 times the squared kernel bound divided by the sample size. -/
lemma variance_offDiag_kernel_le
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (N : ℕ)
    (kernel : X → X → ℝ) (hkernel : Measurable (Function.uncurry kernel))
    (M : ℝ) (_hM : 0 ≤ M)
    (hbound : ∀ x y, |kernel x y| ≤ M) :
    variance
        (fun target : Fin N → X =>
          ((N : ℝ) * (N - 1 : ℕ))⁻¹ *
            ∑ i, ∑ j, if i ≠ j then kernel (target i) (target j) else 0)
        (Measure.pi (fun _ : Fin N => μ)) ≤
      32 * M ^ 2 / (N : ℝ) := by
  exact Causalean.Stat.variance_offDiag_kernel_le
    μ N kernel hkernel M hbound

end CausalSmith.Stat.TransportedLateStrengthFrontier
