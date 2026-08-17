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
import Causalean.Stat.Sample.CollisionEstimator

namespace CausalSmith.Stat.TransportedLateStrengthFrontier

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology

variable {𝒳 : Type*} [MeasurableSpace 𝒳]
/-- The collision component is unbiased, is bounded on the realized target
support, and has the paper's variance bound. -/
lemma regularCell_collision_moments
    (P : TransportedArray 𝒳) (N k : ℕ → ℕ)
    (c epsilon cminus cplus : ℝ) (n : ℕ)
    (hNtwo : 2 ≤ N n)
    (hP : RegularFiniteCellClass P N k c epsilon cminus cplus n) :
    (∫ target : TargetSample 𝒳 (N n),
        collisionScale (sourceCellMass P n) target
        ∂Measure.pi (fun _ : Fin (N n) => targetXLaw P n)) =
      kishDispersion P n ∧
    (∀ᵐ z : 𝒳 × 𝒳 ∂(targetXLaw P n).prod (targetXLaw P n),
      |collisionKernel (sourceCellMass P n) z.1 z.2| ≤
        (k n : ℝ) / cminus) ∧
    variance
        (collisionScale (sourceCellMass P n))
        (Measure.pi (fun _ : Fin (N n) => targetXLaw P n)) ≤
      32 * (k n : ℝ) ^ 2 / (cminus ^ 2 * (N n : ℝ)) := by
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
  let μT := targetXLaw P n
  let μN := Measure.pi (fun _ : Fin (N n) => μT)
  let q := sourceCellMass P n
  let kernel : 𝒳 → 𝒳 → ℝ := fun x y =>
    ∑ i : Fin (k n),
      if x = cell i ∧ y = cell i then 1 / q (cell i) else 0
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
  have hkreal : 0 < (k n : ℝ) := by exact_mod_cast hk
  have hqpos (i : Fin (k n)) : 0 < q (cell i) :=
    (div_pos hcm hkreal).trans_le (hmass i).1
  have hqinv (i : Fin (k n)) :
      1 / q (cell i) ≤ (k n : ℝ) / cminus := by
    calc
      1 / q (cell i) ≤ 1 / (cminus / (k n : ℝ)) :=
        one_div_le_one_div_of_le (div_pos hcm hkreal) (hmass i).1
      _ = (k n : ℝ) / cminus := by
        field_simp [hcm.ne', hkreal.ne']
  have hkernel_nonneg (x y : 𝒳) : 0 ≤ kernel x y := by
    dsimp only [kernel]
    apply Finset.sum_nonneg
    intro i hi
    split_ifs
    · exact one_div_nonneg.mpr (hqpos i).le
    · exact le_rfl
  have hkernel_bound (x y : 𝒳) :
      |kernel x y| ≤ (k n : ℝ) / cminus := by
    rw [abs_of_nonneg (hkernel_nonneg x y)]
    by_cases hxy : ∃ i : Fin (k n), x = cell i ∧ y = cell i
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
    · have hzero : kernel x y = 0 := by
        dsimp only [kernel]
        apply Finset.sum_eq_zero
        intro i hi
        rw [if_neg]
        exact fun h => hxy ⟨i, h⟩
      rw [hzero]
      exact div_nonneg hkreal.le hcm.le
  have hrangeMeas : MeasurableSet (Set.range cell) := by
    rw [show Set.range cell = ⋃ i, {cell i} by
      ext x
      simp]
    exact MeasurableSet.iUnion hcell
  have hrangeCompl : sourceXLaw P n (Set.range cell)ᶜ = 0 := by
    rw [measure_compl hrangeMeas (measure_ne_top _ _), hrange, measure_univ]
    simp
  have htargetRange : ∀ᵐ x ∂μT, x ∈ Set.range cell := by
    have hc := hIV.transportDomination hrangeCompl
    change Set.range cell ∈ ae μT
    rw [mem_ae_iff]
    exact hc
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
      rw [if_neg]
      rintro ⟨hxi, hyi⟩
      exact hxy (hxi.trans hyi.symm)
  have htargetSample :
      ∀ᵐ target ∂μN, ∀ j, target j ∈ Set.range cell := by
    rw [ae_all_iff]
    intro j
    have hx : ∀ᵐ x ∂Measure.map
        (fun target : TargetSample 𝒳 (N n) => target j) μN,
        x ∈ Set.range cell := by
      rw [(measurePreserving_eval
        (fun _ : Fin (N n) => μT) j).map_eq]
      exact htargetRange
    exact ae_of_ae_map (measurable_pi_apply j).aemeasurable hx
  have hscale_eq : scale =ᵐ[μN] collisionScale q := by
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
  have hprodSupport :
      ∀ᵐ z : 𝒳 × 𝒳 ∂μT.prod μT,
        z.1 ∈ Set.range cell ∧ z.2 ∈ Set.range cell := by
    have hfst : ∀ᵐ z : 𝒳 × 𝒳 ∂μT.prod μT,
        z.1 ∈ Set.range cell := by
      have hm : ∀ᵐ x ∂Measure.map Prod.fst (μT.prod μT),
          x ∈ Set.range cell := by
        simpa [MeasurePreserving.map_eq
          (measurePreserving_fst (μ := μT) (ν := μT))] using htargetRange
      exact (ae_map_iff
        (measurePreserving_fst (μ := μT) (ν := μT)).aemeasurable
        hrangeMeas).mp hm
    have hsnd : ∀ᵐ z : 𝒳 × 𝒳 ∂μT.prod μT,
        z.2 ∈ Set.range cell := by
      have hm : ∀ᵐ x ∂Measure.map Prod.snd (μT.prod μT),
          x ∈ Set.range cell := by
        simpa [MeasurePreserving.map_eq
          (measurePreserving_snd (μ := μT) (ν := μT))] using htargetRange
      exact (ae_map_iff
        (measurePreserving_snd (μ := μT) (ν := μT)).aemeasurable
        hrangeMeas).mp hm
    exact hfst.and hsnd
  have horiginalBound :
      ∀ᵐ z : 𝒳 × 𝒳 ∂μT.prod μT,
        |collisionKernel q z.1 z.2| ≤ (k n : ℝ) / cminus := by
    filter_upwards [hprodSupport] with z hz
    rw [hkernel_eq z.1 z.2 hz.1 hz.2]
    exact hkernel_bound _ _
  have hpairIntegral :
      (∫ z : 𝒳 × 𝒳, kernel z.1 z.2 ∂μT.prod μT) =
        ∑ i : Fin (k n),
          (μT {cell i}).toReal ^ 2 / q (cell i) := by
    have htermInt (i : Fin (k n)) :
        Integrable
          (fun z : 𝒳 × 𝒳 =>
            if z.1 = cell i ∧ z.2 = cell i then 1 / q (cell i) else 0)
          (μT.prod μT) := by
      apply Integrable.of_bound
        (Measurable.ite
          (((hcell i).preimage measurable_fst).inter
            ((hcell i).preimage measurable_snd))
          measurable_const measurable_const).aestronglyMeasurable
        |1 / q (cell i)|
      filter_upwards with z
      split_ifs with hsplit <;> simp [hsplit]
    rw [show (fun z : 𝒳 × 𝒳 => kernel z.1 z.2) =
        fun z => ∑ i : Fin (k n),
          if z.1 = cell i ∧ z.2 = cell i then 1 / q (cell i) else 0 by
      rfl]
    rw [integral_finset_sum _ (fun i _ => htermInt i)]
    apply Finset.sum_congr rfl
    intro i hi
    let f : 𝒳 → ℝ := fun x => if x = cell i then 1 / q (cell i) else 0
    let g : 𝒳 → ℝ := fun y => if y = cell i then 1 else 0
    have hf : Integrable f μT := by
      apply Integrable.of_bound
        (Measurable.ite (hcell i) measurable_const measurable_const
          |>.aestronglyMeasurable) |1 / q (cell i)|
      filter_upwards with x
      split_ifs with hsplit <;> simp [hsplit]
    have hg : Integrable g μT := by
      apply Integrable.of_bound
        (Measurable.ite (hcell i) measurable_const measurable_const
          |>.aestronglyMeasurable) 1
      filter_upwards with x
      split_ifs with hsplit <;> simp [hsplit]
    have hfg :
        (fun z : 𝒳 × 𝒳 =>
          if z.1 = cell i ∧ z.2 = cell i then 1 / q (cell i) else 0) =
          fun z => f z.1 * g z.2 := by
      funext z
      by_cases hx : z.1 = cell i <;> by_cases hy : z.2 = cell i
      <;> simp [f, g, hx, hy]
    rw [hfg, integral_prod_mul f g]
    have hfint : (∫ x, f x ∂μT) =
        (μT {cell i}).toReal * (1 / q (cell i)) := by
      rw [show f = Set.indicator {cell i} (fun _ => 1 / q (cell i)) by
        funext x
        dsimp only [f]
        rw [Set.indicator_apply]
        by_cases hx : x = cell i
        · rw [if_pos hx, if_pos]
          exact hx
        · rw [if_neg hx, if_neg]
          exact fun h => hx h]
      rw [integral_indicator (hcell i)]
      simp [measureReal_def]
    have hgint : (∫ x, g x ∂μT) = (μT {cell i}).toReal := by
      rw [show g = Set.indicator {cell i} (fun _ => (1 : ℝ)) by
        funext x
        dsimp only [g]
        rw [Set.indicator_apply]
        by_cases hx : x = cell i
        · rw [if_pos hx, if_pos]
          exact hx
        · rw [if_neg hx, if_neg]
          exact fun h => hx h]
      rw [integral_indicator (hcell i)]
      simp [measureReal_def]
    rw [hfint, hgint]
    ring
  have hpairEval (j l : Fin (N n)) (hjl : j ≠ l) :
      (∫ target, kernel (target j) (target l) ∂μN) =
        ∫ z : 𝒳 × 𝒳, kernel z.1 z.2 ∂μT.prod μT := by
    have hcoords :
        iIndepFun
          (fun r : Fin (N n) =>
            fun target : TargetSample 𝒳 (N n) => target r) μN :=
      iIndepFun_pi (fun _ : Fin (N n) =>
        (show AEMeasurable (fun x : 𝒳 => x) μT from
          measurable_id.aemeasurable))
    have hindep := hcoords.indepFun hjl
    have hmap :
        Measure.map (fun target : TargetSample 𝒳 (N n) =>
          (target j, target l)) μN = μT.prod μT := by
      have hraw :=
        (indepFun_iff_map_prod_eq_prod_map_map
          (measurable_pi_apply j).aemeasurable
          (measurable_pi_apply l).aemeasurable).1 hindep
      rw [(measurePreserving_eval (fun _ : Fin (N n) => μT) j).map_eq,
        (measurePreserving_eval (fun _ : Fin (N n) => μT) l).map_eq] at hraw
      exact hraw
    have hp : AEMeasurable
        (fun target : TargetSample 𝒳 (N n) => (target j, target l)) μN :=
      ((measurable_pi_apply j).prodMk
        (measurable_pi_apply l)).aemeasurable
    calc
      (∫ target, kernel (target j) (target l) ∂μN) =
          ∫ z : 𝒳 × 𝒳, kernel z.1 z.2
            ∂Measure.map
              (fun target : TargetSample 𝒳 (N n) => (target j, target l)) μN :=
        (integral_map hp hkernel.aestronglyMeasurable).symm
      _ = ∫ z : 𝒳 × 𝒳, kernel z.1 z.2 ∂μT.prod μT := by rw [hmap]
  have hscaleMean :
      (∫ target, scale target ∂μN) =
        ∑ i : Fin (k n),
          (μT {cell i}).toReal ^ 2 / q (cell i) := by
    unfold scale
    rw [integral_const_mul]
    have htermIntegrable (j l : Fin (N n)) :
        Integrable
          (fun target : TargetSample 𝒳 (N n) =>
            if j ≠ l then kernel (target j) (target l) else 0) μN := by
      by_cases hjl : j ≠ l
      · simp only [if_pos hjl]
        have hp : Measurable (fun target : TargetSample 𝒳 (N n) =>
            (target j, target l)) :=
          (measurable_pi_apply j).prodMk (measurable_pi_apply l)
        have hm : Measurable (fun target : TargetSample 𝒳 (N n) =>
            kernel (target j) (target l)) :=
          (show Measurable (fun target : TargetSample 𝒳 (N n) =>
            Function.uncurry kernel (target j, target l)) from hkernel.comp hp)
        apply Integrable.of_bound hm.aestronglyMeasurable
          ((k n : ℝ) / cminus)
        filter_upwards with target
        simpa [Real.norm_eq_abs] using hkernel_bound (target j) (target l)
      · simp [hjl]
    have hinnerIntegrable (j : Fin (N n)) :
        Integrable
          (fun target : TargetSample 𝒳 (N n) =>
            ∑ l, if j ≠ l then kernel (target j) (target l) else 0) μN :=
      integrable_finset_sum _ (fun l _ => htermIntegrable j l)
    have hintegralSum :
        (∫ target, ∑ j, ∑ l,
          if j ≠ l then kernel (target j) (target l) else 0 ∂μN) =
          ∑ j : Fin (N n), ∑ l : Fin (N n), if j ≠ l then
            (∫ z : 𝒳 × 𝒳, kernel z.1 z.2 ∂μT.prod μT) else 0 := by
      rw [integral_finset_sum _ (fun j _ => hinnerIntegrable j)]
      apply Finset.sum_congr rfl
      intro j hj
      rw [integral_finset_sum _ (fun l _ => htermIntegrable j l)]
      apply Finset.sum_congr rfl
      intro l hl
      by_cases hjl : j ≠ l
      · simp only [if_pos hjl]
        exact hpairEval j l hjl
      · simp [hjl]
    rw [hintegralSum]
    have hcount (j : Fin (N n)) :
        ((Finset.univ.filter fun l : Fin (N n) => j ≠ l).card) = N n - 1 := by
      have heq :
          (Finset.univ.filter fun l : Fin (N n) => j ≠ l) =
            Finset.univ.erase j := by
        ext l
        simp [eq_comm]
      rw [heq, Finset.card_erase_of_mem (Finset.mem_univ j)]
      simp
    have hsum :
        (∑ j : Fin (N n), ∑ l : Fin (N n),
          if j ≠ l then
            (∫ z : 𝒳 × 𝒳, kernel z.1 z.2 ∂μT.prod μT) else 0) =
          (N n : ℝ) * (N n - 1 : ℕ) *
            (∫ z : 𝒳 × 𝒳, kernel z.1 z.2 ∂μT.prod μT) := by
      simp_rw [Finset.sum_ite]
      simp [hcount]
      ring
    rw [hsum, hpairIntegral]
    have hNreal : 0 < (N n : ℝ) := by positivity
    have hNm1real : 0 < ((N n - 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.sub_pos_of_lt hNtwo
    field_simp [hNreal.ne', hNm1real.ne']
  have hkish' :
      kishDispersion P n =
        ∑ i : Fin (k n), (μT {cell i}).toReal ^ 2 / q (cell i) := by
    have hrnStrong :
        StronglyMeasurable
          (fun x => ((targetXLaw P n).rnDeriv
            (sourceXLaw P n) x).toReal) :=
      (Measure.measurable_rnDeriv (targetXLaw P n)
        (sourceXLaw P n)).ennreal_toReal.stronglyMeasurable
    have hratio (i : Fin (k n)) :
        transportWeight P n (cell i) =
          (targetXLaw P n {cell i}).toReal /
            sourceCellMass P n (cell i) := by
      have hRN :=
        Measure.setIntegral_toReal_rnDeriv'
          hIV.transportDomination (hcell i)
      rw [integral_singleton' hrnStrong] at hRN
      apply (eq_div_iff (hqpos i).ne').2
      simpa [q, transportWeight, sourceCellMass, measureReal_def, mul_comm] using hRN
    have hmeasure :
        sourceXLaw P n =
          ∑ i, sourceXLaw P n {cell i} • Measure.dirac (cell i) :=
      measure_eq_fin_sum_smul_dirac_of_range
        (sourceXLaw P n) cell hcell hrange
    have hweightStrong :
        StronglyMeasurable (fun x => (transportWeight P n x) ^ 2) := by
      exact
        ((Measure.measurable_rnDeriv (targetXLaw P n)
          (sourceXLaw P n)).ennreal_toReal.pow_const 2).stronglyMeasurable
    rw [kishDispersion, hmeasure, integral_finset_sum_measure]
    · apply Finset.sum_congr rfl
      intro i hi
      rw [integral_smul_measure,
        integral_dirac' _ _ hweightStrong]
      simp only [smul_eq_mul]
      change
        q (cell i) * transportWeight P n (cell i) ^ 2 =
          (μT {cell i}).toReal ^ 2 / q (cell i)
      rw [hratio i]
      dsimp only [q, μT]
      field_simp [(hqpos i).ne']
    · intro i hi
      exact
        (integrable_dirac' hweightStrong (by simp)).smul_measure
          (measure_ne_top (sourceXLaw P n) {cell i})
  have hmeanOriginal :
      (∫ target, collisionScale q target ∂μN) = kishDispersion P n := by
    rw [integral_congr_ae hscale_eq.symm, hscaleMean, hkish']
  have hvarRep :=
    variance_offDiag_kernel_le μT (N n) kernel hkernel
      ((k n : ℝ) / cminus) (div_nonneg hkreal.le hcm.le) hkernel_bound
  have hvarOriginal :
      variance (collisionScale q) μN ≤
        32 * (k n : ℝ) ^ 2 / (cminus ^ 2 * (N n : ℝ)) := by
    rw [variance_congr hscale_eq.symm]
    calc
      variance scale μN ≤
          32 * ((k n : ℝ) / cminus) ^ 2 / (N n : ℝ) := hvarRep
      _ = 32 * (k n : ℝ) ^ 2 /
          (cminus ^ 2 * (N n : ℝ)) := by
        field_simp [hcm.ne']
  exact ⟨hmeanOriginal, horiginalBound, hvarOriginal⟩

/-- The lower-tail failure probability for `Khat` has the two paper branches. -/
lemma regularCell_Khat_lower_tail
    (P : TransportedArray 𝒳) (N k : ℕ → ℕ)
    (c epsilon cminus cplus : ℝ) (n : ℕ)
    (hNtwo : 2 ≤ N n)
    (hP : RegularFiniteCellClass P N k c epsilon cminus cplus n) :
    (kishDispersion P n ≤ 2 →
      ∀ target : TargetSample 𝒳 (N n),
        kishDispersion P n / 2 ≤
          regularCellKhat (sourceCellMass P n) target) ∧
    (2 < kishDispersion P n →
      (Measure.pi (fun _ : Fin (N n) => targetXLaw P n)
        {target | regularCellKhat (sourceCellMass P n) target <
          kishDispersion P n / 2}).toReal ≤
        128 * (k n : ℝ) ^ 2 /
          (cminus ^ 2 * (N n : ℝ) * kishDispersion P n ^ 2)) := by
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
  let μN := Measure.pi (fun _ : Fin (N n) => targetXLaw P n)
  let q := sourceCellMass P n
  have hscale_nonneg (target : TargetSample 𝒳 (N n)) :
      0 ≤ collisionScale q target := by
    unfold collisionScale Causalean.Stat.collisionScale
    apply mul_nonneg (inv_nonneg.mpr (mul_nonneg (by positivity) (by positivity)))
    apply Finset.sum_nonneg
    intro j hj
    apply Finset.sum_nonneg
    intro l hl
    split_ifs
    · unfold Causalean.Stat.collisionKernel
      split_ifs
      · exact one_div_nonneg.mpr measureReal_nonneg
      · exact le_rfl
    · exact le_rfl
  have hPfull : RegularFiniteCellClass P N k c epsilon cminus cplus n :=
    ⟨hIV, hk, hcm, hcmOne, hcp, cell, hcell, hrange, hmass⟩
  have hcoll := regularCell_collision_moments
    P N k c epsilon cminus cplus n hNtwo hPfull
  have hmem : MemLp (collisionScale q) 2 μN :=
    collisionScale_memLp_for_witness P N k c epsilon n
      (lt_of_lt_of_le (by omega) hNtwo) hIV hk cminus hcm cell hcell
      hrange (fun i => (hmass i).1)
  constructor
  · intro hkish target
    unfold regularCellKhat
    linarith [hscale_nonneg target]
  · intro hkish
    have hkappa : 0 < kishDispersion P n / 2 := by linarith
    have hsubset :
        {target : TargetSample 𝒳 (N n) |
          regularCellKhat q target < kishDispersion P n / 2} ⊆
        {target |
          kishDispersion P n / 2 ≤
            |collisionScale q target -
              ∫ t, collisionScale q t ∂μN|} := by
      intro target ht
      rw [hcoll.1]
      unfold regularCellKhat at ht
      change 1 + collisionScale (𝒳 := 𝒳) q target <
        kishDispersion P n / 2 at ht
      have hneg :
          collisionScale (𝒳 := 𝒳) q target - kishDispersion P n < 0 := by
        linarith
      have habs :
          kishDispersion P n / 2 ≤
            |collisionScale q target - kishDispersion P n| := by
        rw [abs_of_neg hneg]
        linarith
      exact habs
    have hcheb :=
      meas_ge_le_variance_div_sq hmem hkappa
    have hvar := hcoll.2.2
    calc
      (μN {target | regularCellKhat q target <
          kishDispersion P n / 2}).toReal ≤
          (μN {target | kishDispersion P n / 2 ≤
            |collisionScale q target -
              ∫ t, collisionScale q t ∂μN|}).toReal :=
        measureReal_mono hsubset
      _ ≤ (ENNReal.ofReal
          (variance (collisionScale q) μN /
            (kishDispersion P n / 2) ^ 2)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hcheb
      _ = variance (collisionScale q) μN /
          (kishDispersion P n / 2) ^ 2 := by
        rw [ENNReal.toReal_ofReal]
        exact div_nonneg (variance_nonneg _ _) (sq_nonneg _)
      _ ≤ (32 * (k n : ℝ) ^ 2 /
          (cminus ^ 2 * (N n : ℝ))) /
            (kishDispersion P n / 2) ^ 2 := by
        gcongr
      _ = 128 * (k n : ℝ) ^ 2 /
          (cminus ^ 2 * (N n : ℝ) *
            kishDispersion P n ^ 2) := by
        have hNreal : 0 < (N n : ℝ) := by positivity
        have hkappa0 : kishDispersion P n ≠ 0 := by linarith
        field_simp [hcm.ne', hNreal.ne', hkappa0]
        ring

/-- Uniformly, the probability that the collision proxy undershoots half the
true dispersion vanishes. -/
lemma regularCell_Khat_lower_tail_uniform
    (N k : ℕ → ℕ) (c epsilon cminus cplus : ℝ)
    (hc : 0 < c) (hcminus : 0 < cminus ∧ cminus ≤ 1)
    (hN : Tendsto (fun n : ℕ => (N n : ℝ) / (n : ℝ)) atTop (𝓝 c))
    (hkRoot : Tendsto (fun n : ℕ => (k n : ℝ) / Real.sqrt n)
      atTop (𝓝 0)) :
    Tendsto
      (fun n => ⨆ P : {P : TransportedArray 𝒳 //
          RegularFiniteCellClass P N k c epsilon cminus cplus n},
        (Measure.pi (fun _ : Fin (N n) => targetXLaw P.1 n)
          {target | regularCellKhat (sourceCellMass P.1 n) target <
            kishDispersion P.1 n / 2}).toReal)
      atTop (𝓝 0) := by
  classical
  let R : ℕ → ℝ := fun n =>
    128 * (k n : ℝ) ^ 2 / (cminus ^ 2 * (N n : ℝ))
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
  have hkSq :
      Tendsto (fun n : ℕ => ((k n : ℝ) / Real.sqrt n) ^ 2)
        atTop (𝓝 0) := by
    simpa using hkRoot.pow 2
  have hquot :
      Tendsto
        (fun n : ℕ =>
          (((k n : ℝ) / Real.sqrt n) ^ 2) /
            ((N n : ℝ) / (n : ℝ))) atTop (𝓝 0) := by
    have hdiv := hkSq.div hN hc.ne'
    rw [zero_div] at hdiv
    exact hdiv
  have hk2N :
      Tendsto (fun n : ℕ => (k n : ℝ) ^ 2 / (N n : ℝ))
        atTop (𝓝 0) := by
    apply hquot.congr'
    filter_upwards [hnpos, hNratio] with n hn hratio
    have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
    have hNreal : 0 < (N n : ℝ) := by
      have : 0 < (N n : ℝ) / (n : ℝ) :=
        lt_trans (half_pos hc) hratio
      rcases div_pos_iff.mp this with h | h
      · exact h.1
      · exact (not_lt_of_ge hnreal.le h.2).elim
    have hsqrt : Real.sqrt (n : ℝ) ≠ 0 := by positivity
    rw [div_pow]
    rw [Real.sq_sqrt hnreal.le]
    field_simp [hnreal.ne', hNreal.ne', hsqrt]
  have hR : Tendsto R atTop (𝓝 0) := by
    have hconst :
        Tendsto (fun _ : ℕ => (128 : ℝ)) atTop (𝓝 128) :=
      tendsto_const_nhds
    have ht := (hconst.mul hk2N).div_const (cminus ^ 2)
    have ht' :
        Tendsto
          (fun n : ℕ => 128 * ((k n : ℝ) ^ 2 / (N n : ℝ)) /
            cminus ^ 2) atTop (𝓝 0) := by
      simpa using ht
    apply ht'.congr'
    exact Filter.Eventually.of_forall fun n => by
      unfold R
      simp only [div_eq_mul_inv]
      ring
  refine squeeze_zero' (g := R) ?_ ?_ hR
  · exact Filter.Eventually.of_forall fun n =>
      Real.iSup_nonneg fun P => measureReal_nonneg
  · filter_upwards [hNtwo] with n hn
    cases isEmpty_or_nonempty {P : TransportedArray 𝒳 //
      RegularFiniteCellClass P N k c epsilon cminus cplus n}
    · simp
      unfold R
      positivity
    apply ciSup_le
    intro P
    by_cases hsmall : kishDispersion P.1 n ≤ 2
    · have hdet := (regularCell_Khat_lower_tail
          P.1 N k c epsilon cminus cplus n hn P.2).1 hsmall
      have hempty :
          {target : TargetSample 𝒳 (N n) |
            regularCellKhat (sourceCellMass P.1 n) target <
              kishDispersion P.1 n / 2} =
            (∅ : Set (TargetSample 𝒳 (N n))) := by
        ext target
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        exact not_lt_of_ge (hdet target)
      rw [hempty]
      simp
      unfold R
      have hNpos : 0 < (N n : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hn)
      positivity
    · have hlarge : 2 < kishDispersion P.1 n := lt_of_not_ge hsmall
      have htail := (regularCell_Khat_lower_tail
        P.1 N k c epsilon cminus cplus n hn P.2).2 hlarge
      calc
        _ ≤ 128 * (k n : ℝ) ^ 2 /
            (cminus ^ 2 * (N n : ℝ) * kishDispersion P.1 n ^ 2) := htail
        _ ≤ R n := by
          unfold R
          have hNpos : 0 < (N n : ℝ) := by
            exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hn)
          have hden : 0 < cminus ^ 2 * (N n : ℝ) :=
            mul_pos (sq_pos_of_pos hcminus.1) hNpos
          have hkappaSq : 1 ≤ kishDispersion P.1 n ^ 2 := by nlinarith
          apply div_le_div_of_nonneg_left (by positivity) hden
          nlinarith

/-! ## R1.9b: measurability of the known design input, and exact centering -/

end CausalSmith.Stat.TransportedLateStrengthFrontier
