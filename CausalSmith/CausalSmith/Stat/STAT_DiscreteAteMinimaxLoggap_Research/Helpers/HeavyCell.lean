import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.PilotSandwich
import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.PilotConditioning
import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.LightCell
import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.HeavyCellMoments
import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.HybridProgram
import Mathlib.Probability.Moments.Variance

namespace CausalSmith.Stat.DiscreteAteMinimaxLoggap

open MeasureTheory
open ProbabilityTheory
open scoped BigOperators

/-- The deterministic half split used by the estimator, packaged in the
generic one-shot independence interface. -/
noncomputable def balancedOneShotSplit {d : ℕ} (P : DiscreteLaw d) :
    Causalean.Stat.OneShotSplit
      (Causalean.Stat.iidSample_infinitePi (obsLaw P)) where
  n₁ n := n / 2
  bound n := Nat.div_le_self n 2
  grow := Nat.tendsto_div_const_atTop (by norm_num)
  cogrow := by
    show Filter.Tendsto (fun n : ℕ ↦ n - n / 2) Filter.atTop Filter.atTop
    apply Filter.tendsto_atTop_mono
      (f := fun n : ℕ ↦ n / 2) (g := fun n ↦ n - n / 2)
    · intro n
      omega
    · exact Nat.tendsto_div_const_atTop (by norm_num)

/-- Transport a finite-sample integral to the canonical infinite IID sample.
This lets the heavy branch use the same tail-count realization as the light
branch while keeping the theorem stated under `productLaw`. -/
lemma integral_productLaw_eq_infinite_trunc {n d : ℕ} (P : DiscreteLaw d)
    (f : (Fin n → Obs d) → ℝ) :
    ∫ sample, f sample ∂productLaw P n =
      ∫ ω : ℕ → Obs d, f (fun i : Fin n ↦ ω i)
        ∂(Measure.infinitePi (fun _ : ℕ ↦ obsLaw P)) := by
  let trunc : (ℕ → Obs d) → (Fin n → Obs d) := fun ω i ↦ ω i
  have htrunc : Measurable trunc := by fun_prop
  rw [productLaw, ← finProductLaw_eq_map (obsLaw P) n,
    integral_map htrunc.aemeasurable (measurable_of_finite f).aestronglyMeasurable]

lemma componentErrorMSE_productLaw_eq_infinite_trunc {n d : ℕ}
    (P : DiscreteLaw d) (component target : (Fin n → Obs d) → ℝ) :
    componentErrorMSE (productLaw P n) component target =
      ∫ ω : ℕ → Obs d,
        (component (fun i : Fin n ↦ ω i) - target (fun i : Fin n ↦ ω i)) ^ 2
        ∂(Measure.infinitePi (fun _ : ℕ ↦ obsLaw P)) := by
  unfold componentErrorMSE
  exact integral_productLaw_eq_infinite_trunc P _

/-- Defines target Heavy, the stated quantity or construction used in the discrete average-treatment-effect estimator. -/
noncomputable def targetHeavy {n d : ℕ} (P : DiscreteLaw d)
    (sample : Fin n → Obs d) : ℝ :=
  ∑ k ∈ heavyCells sample, cellPhi (cellVector P k)

/-- Defines fixed Heavy Contribution, the stated quantity or construction used in the discrete average-treatment-effect estimator. -/
noncomputable def fixedHeavyContribution {n d : ℕ}
    (sample : Fin n → Obs d) (H : Finset (Fin d)) : ℝ :=
  ∑ k ∈ H, empiricalRatioCell sample k

/-- Defines fixed Target Heavy, the stated quantity or construction used in the discrete average-treatment-effect estimator. -/
noncomputable def fixedTargetHeavy {d : ℕ} (P : DiscreteLaw d)
    (H : Finset (Fin d)) : ℝ :=
  ∑ k ∈ H, cellPhi (cellVector P k)

/-- Defines fixed Heavy Arm Contribution, the stated quantity or construction used in the discrete average-treatment-effect estimator. -/
noncomputable def fixedHeavyArmContribution {n d : ℕ}
    (sample : Fin n → Obs d) (H : Finset (Fin d)) (a : Fin 2) : ℝ :=
  ∑ k ∈ H,
    (splitCategoryCount sample 1 k : ℝ) / splitSize n 1 *
      ((splitCellCount sample 1 k a 1 : ℝ) /
        (splitCellCount sample 1 k a 0 + splitCellCount sample 1 k a 1 : ℕ))

/-- Defines fixed Target Arm, the stated quantity or construction used in the discrete average-treatment-effect estimator. -/
noncomputable def fixedTargetArm {d : ℕ} (P : DiscreteLaw d)
    (H : Finset (Fin d)) (a : Fin 2) : ℝ :=
  ∑ k ∈ H, cellMass P k * outcomeMean P (finTwoEquiv a) k

/-- Defines fixed Empirical Mass Arm, the stated quantity or construction used in the discrete average-treatment-effect estimator. -/
noncomputable def fixedEmpiricalMassArm {n d : ℕ}
    (P : DiscreteLaw d) (sample : Fin n → Obs d)
    (H : Finset (Fin d)) (a : Fin 2) : ℝ :=
  ∑ k ∈ H, (splitCategoryCount sample 1 k : ℝ) / splitSize n 1 *
    outcomeMean P (finTwoEquiv a) k

/-- One-observation bounded score whose sample mean is the empirical
category-mass centering of a fixed arm. -/
noncomputable def fixedMassScore {d : ℕ} (P : DiscreteLaw d)
    (H : Finset (Fin d)) (a : Fin 2) (z : Obs d) : ℝ :=
  ∑ k ∈ H, if z.1 = k then outcomeMean P (finTwoEquiv a) k else 0

lemma fixedMassScore_eq {d : ℕ} (P : DiscreteLaw d)
    (H : Finset (Fin d)) (a : Fin 2) (z : Obs d) :
    fixedMassScore P H a z =
      if z.1 ∈ H then outcomeMean P (finTwoEquiv a) z.1 else 0 := by
  classical
  unfold fixedMassScore
  by_cases hz : z.1 ∈ H
  · rw [Finset.sum_eq_single z.1]
    · simp [hz]
    · intro k hk hne
      simp [hne.symm]
    · intro hnot
      exact (hnot hz).elim
  · rw [if_neg hz]
    apply Finset.sum_eq_zero
    intro k hk
    have hne : z.1 ≠ k := fun h => hz (h ▸ hk)
    simp [hne]

/-- Shows that fixed Mass Score mem unit Interval lies in the stated set or interval. -/
lemma fixedMassScore_mem_unitInterval {d : ℕ} (P : DiscreteLaw d)
    (H : Finset (Fin d)) (a : Fin 2) (z : Obs d) :
    fixedMassScore P H a z ∈ Set.Icc (0 : ℝ) 1 := by
  rw [fixedMassScore_eq]
  split_ifs
  · exact outcomeMean_mem_unitInterval P (finTwoEquiv a) z.1
  · exact ⟨le_rfl, zero_le_one⟩

/-- Evaluates or bounds the stated integral involving integral fixed Mass Score eq. -/
lemma integral_fixedMassScore_eq {d : ℕ} (P : DiscreteLaw d)
    (H : Finset (Fin d)) (a : Fin 2) :
    ∫ z, fixedMassScore P H a z ∂obsLaw P = fixedTargetArm P H a := by
  classical
  unfold fixedMassScore fixedTargetArm
  rw [integral_finset_sum H (fun _ _ => Integrable.of_finite)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [show (fun z : Obs d =>
      if z.1 = k then outcomeMean P (finTwoEquiv a) k else 0) =
      (categorySet k).indicator
        (fun _ => outcomeMean P (finTwoEquiv a) k) by
          funext z
          simp [categorySet, Set.indicator]]
  rw [integral_indicator MeasurableSet.of_discrete]
  simp [obsLaw_categorySet_mass]

/-- Establishes the stated equality relating heavy Contribution eq fixed. -/
lemma heavyContribution_eq_fixed {n d : ℕ} (sample : Fin n → Obs d) :
    heavyContribution sample = fixedHeavyContribution sample (heavyCells sample) := rfl

/-- Establishes the stated equality relating target Heavy eq fixed. -/
lemma targetHeavy_eq_fixed {n d : ℕ} (P : DiscreteLaw d)
    (sample : Fin n → Obs d) :
    targetHeavy P sample = fixedTargetHeavy P (heavyCells sample) := rfl

/-- Establishes the stated equality relating fixed Heavy Contribution eq arm sub. -/
lemma fixedHeavyContribution_eq_arm_sub {n d : ℕ}
    (sample : Fin n → Obs d) (H : Finset (Fin d)) :
    fixedHeavyContribution sample H =
      fixedHeavyArmContribution sample H 1 - fixedHeavyArmContribution sample H 0 := by
  unfold fixedHeavyContribution fixedHeavyArmContribution empiricalRatioCell
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]

/-- Establishes the stated upper bound for fixed Heavy Arm error sq le noise mass. -/
lemma fixedHeavyArm_error_sq_le_noise_mass {n d : ℕ} (P : DiscreteLaw d)
    (sample : Fin n → Obs d) (H : Finset (Fin d)) (a : Fin 2) :
    (fixedHeavyArmContribution sample H a - fixedTargetArm P H a) ^ 2 ≤
      2 * (fixedHeavyArmContribution sample H a -
        fixedEmpiricalMassArm P sample H a) ^ 2 +
      2 * (fixedEmpiricalMassArm P sample H a - fixedTargetArm P H a) ^ 2 := by
  nlinarith [sq_nonneg
    ((fixedHeavyArmContribution sample H a - fixedEmpiricalMassArm P sample H a) -
      (fixedEmpiricalMassArm P sample H a - fixedTargetArm P H a))]

/-- Above the calibration cutoff, the estimator's heavy set is exactly the
pilot set controlled by the sandwich theorem at its calibrated threshold. -/
lemma heavyCells_eq_pilotHeavyAt_of_cutoff_le {n d : ℕ}
    (sample : Fin n → Obs d) (hcut : calibrationCutoff ≤ n) :
    heavyCells sample = pilotHeavyAt sample 256 := by
  classical
  rw [heavyCells_eq_filter_of_cutoff_le sample hcut]
  ext k
  simp only [pilotHeavyAt, Finset.mem_filter, Finset.mem_univ, true_and,
    lambda0]
  exact (Int.floor_lt).symm

/-- On the pilot-sandwich event, every selected heavy category has the
deterministic mass lower bound required by the missing-arm estimates. -/
lemma heavy_cell_mass_lower_of_good_pilot {n d : ℕ} (P : DiscreteLaw d)
    (sample : Fin n → Obs d) (hcut : calibrationCutoff ≤ n)
    (hgood : sample ∉ pilotBadEvent P 256) :
    ∀ k ∈ heavyCells sample,
      256 * logScale n / (2 * splitSize n 0) ≤ cellMass P k := by
  have hsand :
      (∀ k ∈ pilotHeavyAt sample 256,
        256 * logScale n / (2 * splitSize n 0) ≤ cellMass P k) ∧
      (∀ k ∉ pilotHeavyAt sample 256,
        cellMass P k ≤ 2 * 256 * logScale n / splitSize n 0) := by
    simpa only [pilotBadEvent, Set.mem_setOf_eq, not_or, not_not] using hgood
  rw [heavyCells_eq_pilotHeavyAt_of_cutoff_le sample hcut]
  exact hsand.1

lemma splitCellCount_le_splitCategoryCount {n d : ℕ}
    (sample : Fin n → Obs d) (j : Fin 2) (k : Fin d) (a y : Fin 2) :
    splitCellCount sample j k a y ≤ splitCategoryCount sample j k := by
  rw [splitCategoryCount_eq_sum_cell]
  calc
    splitCellCount sample j k a y ≤
        ∑ y' : Fin 2, splitCellCount sample j k a y' :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ y)
    _ ≤ ∑ a' : Fin 2, ∑ y' : Fin 2, splitCellCount sample j k a' y' :=
      Finset.single_le_sum
        (fun _ _ => Finset.sum_nonneg fun _ _ => Nat.zero_le _)
        (Finset.mem_univ a)

/-- The tuple obtained by restricting a finite sample to one deterministic
split. -/
noncomputable def splitTuple {n d : ℕ} (sample : Fin n → Obs d) (j : Fin 2) :
    {i : Fin n // i ∈ splitIndices n j} → Obs d :=
  fun i => sample i.1

/-- The abstract category index set is exactly the implemented split category
count. -/
lemma indexSet_splitTuple_category_card {n d : ℕ}
    (sample : Fin n → Obs d) (j : Fin 2) (k : Fin d) :
    (indexSet (splitTuple sample j) (categorySet k)).card =
      splitCategoryCount sample j k := by
  classical
  unfold indexSet splitTuple categorySet splitCategoryCount
  apply Finset.card_bij (fun i _hi => i.1)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact Finset.mem_filter.mpr ⟨i.2, hi⟩
  · intro i₁ hi₁ i₂ hi₂ heq
    exact Subtype.ext heq
  · intro b hb
    simp only [Finset.mem_filter] at hb
    exact ⟨⟨b, hb.1⟩, by simp [hb.2], rfl⟩

/-- The abstract nested arm index set is exactly the sum of the two
implemented outcome counts in that arm. -/
lemma indexSet_splitTuple_arm_card {n d : ℕ}
    (sample : Fin n → Obs d) (j : Fin 2) (k : Fin d) (a : Fin 2) :
    (indexSet (splitTuple sample j)
      (categoryArmSet k (finTwoEquiv a))).card =
      splitCellCount sample j k a 0 + splitCellCount sample j k a 1 := by
  classical
  unfold indexSet splitTuple categoryArmSet splitCellCount
  rw [← Finset.card_union_of_disjoint]
  · apply Finset.card_bij (fun i _hi => i.1)
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rcases hi with ⟨hx, ha⟩
      rcases (show (sample i.1).2.2 = false ∨ (sample i.1).2.2 = true by
        cases (sample i.1).2.2 <;> simp) with hy | hy
      · apply Finset.mem_union_left
        exact Finset.mem_filter.mpr ⟨i.2, by
          ext <;> simp_all [finTwoEquiv]⟩
      · apply Finset.mem_union_right
        exact Finset.mem_filter.mpr ⟨i.2, by
          ext <;> simp_all [finTwoEquiv]⟩
    · intro i₁ hi₁ i₂ hi₂ heq
      exact Subtype.ext heq
    · intro b hb
      simp only [Finset.mem_union, Finset.mem_filter] at hb
      rcases hb with hb | hb
      · exact ⟨⟨b, hb.1⟩, by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨by simpa using congrArg Prod.fst hb.2,
            by simpa using congrArg (fun z => z.2.1) hb.2⟩, rfl⟩
      · exact ⟨⟨b, hb.1⟩, by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨by simpa using congrArg Prod.fst hb.2,
            by simpa using congrArg (fun z => z.2.1) hb.2⟩, rfl⟩
  · apply Finset.disjoint_left.mpr
    intro i hi0 hi1
    simp only [Finset.mem_filter] at hi0 hi1
    have hy0 := congrArg (fun z => z.2.2) hi0.2
    have hy1 := congrArg (fun z => z.2.2) hi1.2
    simp [finTwoEquiv] at hy0 hy1
    rw [hy0] at hy1
    simp at hy1

/-- Establishes the stated upper bound for missing Index Count split Tuple. -/
lemma missingIndexCount_splitTuple {n d : ℕ}
    (sample : Fin n → Obs d) (j : Fin 2) (k : Fin d) (a : Fin 2) :
    missingIndexCount (splitTuple sample j) (categorySet k)
        (categoryArmSet k (finTwoEquiv a)) =
      if splitCellCount sample j k a 0 + splitCellCount sample j k a 1 = 0
      then splitCategoryCount sample j k else 0 := by
  unfold missingIndexCount
  rw [indexSet_splitTuple_category_card, indexSet_splitTuple_arm_card]

/-- The abstract residual sum on a split tuple is the implemented arm-success
count minus its conditional-mean centering. -/
lemma sum_armOutcomeResidual_splitTuple {n d : ℕ}
    (P : DiscreteLaw d) (sample : Fin n → Obs d) (j : Fin 2)
    (k : Fin d) (a : Fin 2) :
    (∑ i, armOutcomeResidual P k a (splitTuple sample j i)) =
      (splitCellCount sample j k a 1 : ℝ) -
        outcomeMean P (finTwoEquiv a) k *
          (splitCellCount sample j k a 0 + splitCellCount sample j k a 1 : ℕ) := by
  classical
  unfold armOutcomeResidual splitTuple splitCellCount
  simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  simp_rw [Finset.sum_filter]
  rw [show (∑ x : { i // i ∈ splitIndices n j },
      if (sample x.val).fst = k ∧ (sample x.val).snd.fst = finTwoEquiv a then
        (if (sample x.val).snd.snd then 1 else 0) -
          outcomeMean P (finTwoEquiv a) k
      else 0) =
    ∑ i ∈ splitIndices n j,
      if (sample i).fst = k ∧ (sample i).snd.fst = finTwoEquiv a then
        (if (sample i).snd.snd then 1 else 0) -
          outcomeMean P (finTwoEquiv a) k
      else 0 by
        exact (Finset.sum_subtype (splitIndices n j)
          (fun _ => Iff.rfl) (fun i =>
            if (sample i).fst = k ∧ (sample i).snd.fst = finTwoEquiv a then
              (if (sample i).snd.snd then 1 else 0) -
                outcomeMean P (finTwoEquiv a) k
            else 0)).symm]
  rw [← Finset.sum_add_distrib, Nat.cast_sum]
  simp_rw [Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  fin_cases a <;> rcases (sample i) with ⟨x, aa, y⟩ <;>
    fin_cases aa <;> fin_cases y <;> by_cases hx : x = k <;>
      simp [finTwoEquiv, hx] <;> ring

/-- Restricting the canonical finite product sample to either deterministic
split again has the corresponding finite product law. -/
lemma productLaw_map_splitTuple {n d : ℕ} (P : DiscreteLaw d)
    (j : Fin 2) :
    (productLaw P n).map (fun sample => splitTuple sample j) =
      Measure.pi
        (fun _ : {i : Fin n // i ∈ splitIndices n j} => obsLaw P) := by
  have hindepAll : iIndepFun
      (fun i : Fin n => fun sample : Fin n → Obs d => sample i)
      (productLaw P n) := by
    unfold productLaw
    exact ProbabilityTheory.iIndepFun_pi
      (X := fun _ => (id : Obs d → Obs d)) (fun _ => aemeasurable_id)
  have hindep : iIndepFun
      (fun i : {i : Fin n // i ∈ splitIndices n j} =>
        fun sample : Fin n → Obs d => sample i.1)
      (productLaw P n) :=
    hindepAll.precomp Subtype.val_injective
  have hmap := (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
    (fun i : {i : Fin n // i ∈ splitIndices n j} =>
      (measurable_pi_apply i.1).aemeasurable)).mp hindep
  change (productLaw P n).map
      (fun sample (i : {i : Fin n // i ∈ splitIndices n j}) =>
        sample i.1) = _
  calc
    _ = Measure.pi
        (fun i : {i : Fin n // i ∈ splitIndices n j} =>
          (productLaw P n).map (fun sample => sample i.1)) := hmap
    _ = Measure.pi
        (fun _ : {i : Fin n // i ∈ splitIndices n j} => obsLaw P) := by
      congr with i
      simp [productLaw, Measure.pi_map_eval]

/-- Integral transport from the full sample to either deterministic split. -/
lemma integral_comp_splitTuple {n d : ℕ} (P : DiscreteLaw d)
    (j : Fin 2) (g : ({i : Fin n // i ∈ splitIndices n j} → Obs d) → ℝ) :
    ∫ sample : Fin n → Obs d, g (splitTuple sample j) ∂productLaw P n =
      ∫ z, g z ∂Measure.pi
        (fun _ : {i : Fin n // i ∈ splitIndices n j} => obsLaw P) := by
  rw [← productLaw_map_splitTuple P j]
  rw [integral_map (measurable_of_finite _).aemeasurable
    (measurable_of_finite g).aestronglyMeasurable]

lemma sum_fixedMassScore_splitTuple {n d : ℕ} (P : DiscreteLaw d)
    (sample : Fin n → Obs d) (j : Fin 2) (H : Finset (Fin d)) (a : Fin 2) :
    ∑ i, fixedMassScore P H a (splitTuple sample j i) =
      ∑ k ∈ H, (splitCategoryCount sample j k : ℝ) *
        outcomeMean P (finTwoEquiv a) k := by
  classical
  unfold fixedMassScore splitTuple splitCategoryCount
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [show (∑ x : { i // i ∈ splitIndices n j },
      if (sample x.val).fst = k then
        outcomeMean P (finTwoEquiv a) k else 0) =
      (∑ x : { i // i ∈ splitIndices n j },
        if (sample x.val).fst = k then (1 : ℝ) else 0) *
          outcomeMean P (finTwoEquiv a) k by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro x hx
        by_cases h : (sample x.val).fst = k <;> simp [h]]
  congr 1
  rw [show (∑ x : { i // i ∈ splitIndices n j },
      if (sample x.val).fst = k then (1 : ℝ) else 0) =
    ∑ i ∈ splitIndices n j,
      if (sample i).fst = k then (1 : ℝ) else 0 by
        exact (Finset.sum_subtype (splitIndices n j)
          (fun _ => Iff.rfl) (fun i =>
            if (sample i).fst = k then (1 : ℝ) else 0)).symm]
  simp

/-- Establishes the stated equality relating fixed Empirical Mass Arm sub target eq score. -/
lemma fixedEmpiricalMassArm_sub_target_eq_score {n d : ℕ}
    (P : DiscreteLaw d) (sample : Fin n → Obs d)
    (H : Finset (Fin d)) (a : Fin 2) :
    fixedEmpiricalMassArm P sample H a - fixedTargetArm P H a =
      (∑ i, fixedMassScore P H a (splitTuple sample 1 i)) /
          splitSize n 1 - fixedTargetArm P H a := by
  unfold fixedEmpiricalMassArm
  rw [sum_fixedMassScore_splitTuple]
  rw [Finset.sum_div]
  apply congrArg (fun x : ℝ => x - fixedTargetArm P H a)
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- A fixed empirical category-mass arm score has variance at most one over
the estimation-fold size. -/
lemma integral_fixedEmpiricalMassArm_sub_target_sq_le {n d : ℕ}
    (P : DiscreteLaw d) (H : Finset (Fin d)) (a : Fin 2)
    (hm : 0 < splitSize n 1) :
    ∫ sample : Fin n → Obs d,
        (fixedEmpiricalMassArm P sample H a - fixedTargetArm P H a) ^ 2
        ∂productLaw P n ≤ 1 / (splitSize n 1 : ℝ) := by
  classical
  let J := {i : Fin n // i ∈ splitIndices n (1 : Fin 2)}
  let m : ℝ := splitSize n 1
  let g : Obs d → ℝ := fixedMassScore P H a
  let S : (J → Obs d) → ℝ := fun z => ∑ i, g (z i)
  let avg : (J → Obs d) → ℝ := fun z => S z / m
  have hmcard : Fintype.card J = splitSize n 1 := by simp [J, splitSize]
  have hmR : 0 < m := by
    dsimp [m]
    exact_mod_cast hm
  have hgmean : ∫ z, g z ∂obsLaw P = fixedTargetArm P H a := by
    exact integral_fixedMassScore_eq P H a
  have havgmean : ∫ z : J → Obs d, avg z
      ∂Measure.pi (fun _ : J => obsLaw P) = fixedTargetArm P H a := by
    unfold avg S
    rw [integral_div]
    simp_rw [integral_finset_sum (Finset.univ : Finset J)
      (fun _ _ => Integrable.of_finite)]
    have heval (i : J) :
        ∫ z : J → Obs d, g (z i) ∂Measure.pi (fun _ : J => obsLaw P) =
          ∫ x, g x ∂obsLaw P := by
      exact integral_comp_eval (measurable_of_finite g).aestronglyMeasurable
    simp_rw [heval, hgmean]
    rw [Finset.sum_const, nsmul_eq_mul]
    rw [show Finset.univ.card = splitSize n 1 by exact hmcard]
    field_simp
    dsimp [m]
    ring
  have hvarScore : Var[g; obsLaw P] ≤ 1 := by
    calc
      Var[g; obsLaw P] ≤ ((1 - 0) / 2 : ℝ) ^ 2 := by
        apply variance_le_sq_of_bounded
        · filter_upwards with z
          exact fixedMassScore_mem_unitInterval P H a z
        · exact (measurable_of_finite g).aemeasurable
      _ ≤ 1 := by norm_num
  have hvarS : Var[S; Measure.pi (fun _ : J => obsLaw P)] ≤ m := by
    have hvarExact :
        Var[S; Measure.pi (fun _ : J => obsLaw P)] =
          ∑ i : J, Var[g; obsLaw P] := by
      calc
        _ = Var[(∑ i : J, fun z : J → Obs d => g (z i));
            Measure.pi (fun _ : J => obsLaw P)] := by
              congr 2
              funext z
              simp [S]
        _ = _ := variance_sum_pi (ι := J) (Ω := fun _ => Obs d)
          (μ := fun _ => obsLaw P) (fun _ =>
            (MemLp.of_discrete : MemLp g 2 (obsLaw P)))
    rw [hvarExact]
    rw [Finset.sum_const, nsmul_eq_mul]
    rw [show Finset.univ.card = splitSize n 1 by exact hmcard]
    dsimp [m]
    nlinarith [show 0 ≤ (splitSize n 1 : ℝ) by positivity]
  have hvarAvg : Var[avg; Measure.pi (fun _ : J => obsLaw P)] ≤ 1 / m := by
    rw [show Var[avg; Measure.pi (fun _ : J => obsLaw P)] =
        (1 / m) ^ 2 * Var[S; Measure.pi (fun _ : J => obsLaw P)] by
      unfold avg
      rw [show (fun z => S z / m) = fun z => (1 / m) * S z by
        funext z; ring]
      exact variance_const_mul (1 / m) S _]
    calc
      _ ≤ (1 / m) ^ 2 * m := by gcongr
      _ = 1 / m := by field_simp
  rw [show (∫ sample : Fin n → Obs d,
        (fixedEmpiricalMassArm P sample H a - fixedTargetArm P H a) ^ 2
        ∂productLaw P n) =
      ∫ z : J → Obs d, (avg z - fixedTargetArm P H a) ^ 2
        ∂Measure.pi (fun _ : J => obsLaw P) by
      simpa only [J, avg, S, g, m, fixedEmpiricalMassArm_sub_target_eq_score]
        using integral_comp_splitTuple P 1
          (fun z => ((∑ i, fixedMassScore P H a (z i)) /
            splitSize n 1 - fixedTargetArm P H a) ^ 2)]
  rw [← havgmean, ← variance_eq_integral (measurable_of_finite avg).aemeasurable]
  exact hvarAvg

/-- Exact pointwise decomposition of the implemented arm ratio error about
its empirical category-mass centering.  The first term is centered ratio
noise; the second is precisely the bias from an unobserved treatment arm. -/
lemma fixedHeavyArm_noise_decomposition {n d : ℕ}
    (P : DiscreteLaw d) (sample : Fin n → Obs d)
    (H : Finset (Fin d)) (a : Fin 2) :
    fixedHeavyArmContribution sample H a - fixedEmpiricalMassArm P sample H a =
      (fixedRatioResidual P (splitTuple sample 1) H a -
        fixedMissingOutcomeBias P (splitTuple sample 1) H a) /
          splitSize n 1 := by
  classical
  unfold fixedHeavyArmContribution fixedEmpiricalMassArm fixedRatioResidual
    fixedMissingOutcomeBias tupleRatioCoeff
  rw [← Finset.sum_sub_distrib]
  rw [sub_div, Finset.sum_div, Finset.sum_div,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [indexSet_splitTuple_category_card,
    indexSet_splitTuple_arm_card,
    sum_armOutcomeResidual_splitTuple,
    missingIndexCount_splitTuple]
  let N : ℕ := splitCategoryCount sample 1 k
  let D : ℕ := splitCellCount sample 1 k a 0 + splitCellCount sample 1 k a 1
  let Y : ℕ := splitCellCount sample 1 k a 1
  let m : ℕ := splitSize n 1
  let mu : ℝ := outcomeMean P (finTwoEquiv a) k
  change (N : ℝ) / m * ((Y : ℝ) / D) - (N : ℝ) / m * mu =
    ((N : ℝ) * (if 0 < D then (D : ℝ)⁻¹ else 0) *
      ((Y : ℝ) - mu * D)) / m -
        mu * (if D = 0 then N else 0) / m
  by_cases hD : 0 < D
  · have hD0 : D ≠ 0 := Nat.ne_of_gt hD
    rw [if_pos hD, if_neg hD0]
    field_simp
    ring
  · have hDz : D = 0 := Nat.eq_zero_of_not_pos hD
    simp [hD, hDz]
    ring

/-- Fixed-set product-law MSE of the arm ratio about its empirical mass
centering.  The first two terms are parametric ratio and missing-label
diagonals; the final term is the aggregate exponentially damped missing-arm
bias envelope. -/
lemma integral_fixedHeavyArm_noise_sq_le {n d : ℕ} {epsilon B : ℝ}
    (P : DiscreteLaw d) (H : Finset (Fin d)) (a : Fin 2)
    (hm : 3 ≤ splitSize n 1) (hOverlap : Overlap epsilon P)
    (hepsilon : 0 < epsilon) (hB : 0 < B)
    (hp : ∀ k ∈ H, B ≤ cellMass P k) :
    ∫ sample : Fin n → Obs d,
        (fixedHeavyArmContribution sample H a -
          fixedEmpiricalMassArm P sample H a) ^ 2 ∂productLaw P n ≤
      4 * (∑ k ∈ H, cellMass P k) /
          ((splitSize n 1 : ℝ) * epsilon) +
        2 / (splitSize n 1 : ℝ) +
        2 * (H.card /
          (((((splitSize n 1 - 2 : ℕ) : ℝ) / 2 * epsilon) ^ 2) * B)) ^ 2 := by
  classical
  let J := {i : Fin n // i ∈ splitIndices n (1 : Fin 2)}
  let m : ℝ := splitSize n 1
  let R : (Fin n → Obs d) → ℝ := fun sample =>
    fixedRatioResidual P (splitTuple sample 1) H a
  let M : (Fin n → Obs d) → ℝ := fun sample =>
    fixedMissingOutcomeBias P (splitTuple sample 1) H a
  have hmcard : Fintype.card J = splitSize n 1 := by simp [J, splitSize]
  have hmpos : 0 < m := by dsimp [m]; positivity
  have hpoint : ∀ sample : Fin n → Obs d,
      (fixedHeavyArmContribution sample H a -
          fixedEmpiricalMassArm P sample H a) ^ 2 ≤
        2 / m ^ 2 * (R sample) ^ 2 + 2 / m ^ 2 * (M sample) ^ 2 := by
    intro sample
    rw [fixedHeavyArm_noise_decomposition]
    dsimp only [R, M, m]
    have hsq := sq_nonneg
      (fixedRatioResidual P (splitTuple sample 1) H a +
        fixedMissingOutcomeBias P (splitTuple sample 1) H a)
    field_simp
    nlinarith
  have hR : ∫ sample : Fin n → Obs d, (R sample) ^ 2 ∂productLaw P n ≤
      (2 * m / epsilon) * ∑ k ∈ H, cellMass P k := by
    rw [show (∫ sample : Fin n → Obs d, (R sample) ^ 2 ∂productLaw P n) =
      ∫ z : J → Obs d, (fixedRatioResidual P z H a) ^ 2
        ∂Measure.pi (fun _ : J => obsLaw P) by
          simpa only [R, J] using integral_comp_splitTuple P 1
            (fun z => (fixedRatioResidual P z H a) ^ 2)]
    simpa [m, hmcard] using integral_fixedRatioResidual_sq_le
      (I := J) P hOverlap hepsilon H a
        (fun k hk => hB.trans_le (hp k hk))
  have hM : ∫ sample : Fin n → Obs d, (M sample) ^ 2 ∂productLaw P n ≤
      m + m ^ 2 * (H.card /
        (((((splitSize n 1 - 2 : ℕ) : ℝ) / 2 * epsilon) ^ 2) * B)) ^ 2 := by
    rw [show (∫ sample : Fin n → Obs d, (M sample) ^ 2 ∂productLaw P n) =
      ∫ z : J → Obs d, (fixedMissingOutcomeBias P z H a) ^ 2
        ∂Measure.pi (fun _ : J => obsLaw P) by
          simpa only [M, J] using integral_comp_splitTuple P 1
            (fun z => (fixedMissingOutcomeBias P z H a) ^ 2)]
    calc
      _ ≤ ∫ z : J → Obs d,
          (fixedMissingCount z H (finTwoEquiv a)) ^ 2
          ∂Measure.pi (fun _ : J => obsLaw P) := by
        apply integral_mono (Integrable.of_finite) (Integrable.of_finite)
        intro z
        exact fixedMissingOutcomeBias_sq_le P z H a
      _ ≤ (Fintype.card J : ℝ) + (Fintype.card J : ℝ) ^ 2 *
          (H.card /
            (((((Fintype.card J - 2 : ℕ) : ℝ) / 2 * epsilon) ^ 2) * B)) ^ 2 :=
        integral_fixedMissingCount_sq_le P H (finTwoEquiv a)
          (by simpa [hmcard] using hm) hOverlap hepsilon hB hp
      _ = m + m ^ 2 * (H.card /
          (((((splitSize n 1 - 2 : ℕ) : ℝ) / 2 * epsilon) ^ 2) * B)) ^ 2 := by
        simp [hmcard, m]
  calc
    _ ≤ ∫ sample : Fin n → Obs d,
        (2 / m ^ 2 * (R sample) ^ 2 + 2 / m ^ 2 * (M sample) ^ 2)
        ∂productLaw P n := by
      apply integral_mono (Integrable.of_finite) (Integrable.of_finite)
      exact hpoint
    _ = 2 / m ^ 2 * (∫ sample : Fin n → Obs d, (R sample) ^ 2
          ∂productLaw P n) +
        2 / m ^ 2 * (∫ sample : Fin n → Obs d, (M sample) ^ 2
          ∂productLaw P n) := by
      rw [integral_add Integrable.of_finite Integrable.of_finite,
        integral_const_mul, integral_const_mul]
    _ ≤ 2 / m ^ 2 * ((2 * m / epsilon) * ∑ k ∈ H, cellMass P k) +
        2 / m ^ 2 * (m + m ^ 2 * (H.card /
          (((((splitSize n 1 - 2 : ℕ) : ℝ) / 2 * epsilon) ^ 2) * B)) ^ 2) := by
      gcongr
    _ = 4 * (∑ k ∈ H, cellMass P k) /
          ((splitSize n 1 : ℝ) * epsilon) +
        2 / (splitSize n 1 : ℝ) +
        2 * (H.card /
          (((((splitSize n 1 - 2 : ℕ) : ℝ) / 2 * epsilon) ^ 2) * B)) ^ 2 := by
      dsimp [m]
      field_simp
      ring

/-- The implemented category and arm counts satisfy the sharp aggregate
inverse-count bound on either split. -/
lemma integral_fixedHeavyArm_error_sq_le {n d : ℕ} {epsilon B : ℝ}
    (P : DiscreteLaw d) (H : Finset (Fin d)) (a : Fin 2)
    (hm : 3 ≤ splitSize n 1) (hOverlap : Overlap epsilon P)
    (hepsilon : 0 < epsilon) (hB : 0 < B)
    (hp : ∀ k ∈ H, B ≤ cellMass P k) :
    ∫ sample : Fin n → Obs d,
        (fixedHeavyArmContribution sample H a - fixedTargetArm P H a) ^ 2
        ∂productLaw P n ≤
      8 * (∑ k ∈ H, cellMass P k) /
          ((splitSize n 1 : ℝ) * epsilon) +
        6 / (splitSize n 1 : ℝ) +
        4 * (H.card /
          (((((splitSize n 1 - 2 : ℕ) : ℝ) / 2 * epsilon) ^ 2) * B)) ^ 2 := by
  have hmpos : 0 < splitSize n 1 := by omega
  calc
    _ ≤ ∫ sample : Fin n → Obs d,
        (2 * (fixedHeavyArmContribution sample H a -
            fixedEmpiricalMassArm P sample H a) ^ 2 +
          2 * (fixedEmpiricalMassArm P sample H a -
            fixedTargetArm P H a) ^ 2) ∂productLaw P n := by
      apply integral_mono Integrable.of_finite Integrable.of_finite
      intro sample
      exact fixedHeavyArm_error_sq_le_noise_mass P sample H a
    _ = 2 * (∫ sample : Fin n → Obs d,
          (fixedHeavyArmContribution sample H a -
            fixedEmpiricalMassArm P sample H a) ^ 2 ∂productLaw P n) +
        2 * (∫ sample : Fin n → Obs d,
          (fixedEmpiricalMassArm P sample H a -
            fixedTargetArm P H a) ^ 2 ∂productLaw P n) := by
      rw [integral_add Integrable.of_finite Integrable.of_finite,
        integral_const_mul, integral_const_mul]
    _ ≤ 2 * (4 * (∑ k ∈ H, cellMass P k) /
          ((splitSize n 1 : ℝ) * epsilon) +
        2 / (splitSize n 1 : ℝ) +
        2 * (H.card /
          (((((splitSize n 1 - 2 : ℕ) : ℝ) / 2 * epsilon) ^ 2) * B)) ^ 2) +
        2 * (1 / (splitSize n 1 : ℝ)) := by
      gcongr
      · exact integral_fixedHeavyArm_noise_sq_le P H a hm hOverlap
          hepsilon hB hp
      · exact integral_fixedEmpiricalMassArm_sub_target_sq_le P H a hmpos
    _ = 8 * (∑ k ∈ H, cellMass P k) /
          ((splitSize n 1 : ℝ) * epsilon) +
        6 / (splitSize n 1 : ℝ) +
        4 * (H.card /
          (((((splitSize n 1 - 2 : ℕ) : ℝ) / 2 * epsilon) ^ 2) * B)) ^ 2 := by
      ring

/-- Establishes the stated property of heavy Cells rebuild Pilot in the discrete average-treatment-effect construction. -/
lemma heavyCells_rebuildPilot {n d : ℕ} (P : DiscreteLaw d)
    (base : Obs d) (ω : ℕ → Obs d) :
    heavyCells (rebuildPilotSample P base
      (fun i : (lightBalancedSplit P).foldA n => ω i)) =
      heavyCells (fun i : Fin n => ω i) := by
  classical
  unfold heavyCells
  by_cases hn : n < calibrationCutoff
  · simp [hn]
  · ext k
    simp only [hn, if_false, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [splitCategoryCount_rebuildPilot P base ω k]

/-- Establishes the stated property of split Category Count rebuild Estimation in the discrete average-treatment-effect construction. -/
lemma splitCategoryCount_rebuildEstimation {n d : ℕ}
    (P : DiscreteLaw d) (base : Obs d) (ω : ℕ → Obs d)
    (k : Fin d) :
    splitCategoryCount (rebuildEstimationSample P base
      (fun i : (lightBalancedSplit P).foldB n => ω i)) 1 k =
      splitCategoryCount (fun i : Fin n => ω i) 1 k := by
  rw [splitCategoryCount_eq_sum_cell, splitCategoryCount_eq_sum_cell]
  simp_rw [splitCellCount_rebuildEstimation P base ω]

/-- Establishes the stated property of fixed Heavy Arm Contribution rebuild Estimation in the discrete average-treatment-effect construction. -/
lemma fixedHeavyArmContribution_rebuildEstimation {n d : ℕ}
    (P : DiscreteLaw d) (base : Obs d) (ω : ℕ → Obs d)
    (H : Finset (Fin d)) (a : Fin 2) :
    fixedHeavyArmContribution (rebuildEstimationSample P base
      (fun i : (lightBalancedSplit P).foldB n => ω i)) H a =
      fixedHeavyArmContribution (fun i : Fin n => ω i) H a := by
  unfold fixedHeavyArmContribution
  simp_rw [splitCategoryCount_rebuildEstimation P base ω,
    splitCellCount_rebuildEstimation P base ω]

/-- Freezing one pilot-selected set factors its fiber probability from every
fixed-set estimation-fold arm error. -/
lemma infinite_fixedHeavyArm_fiber_factorization {n d : ℕ}
    (P : DiscreteLaw d) (base : Obs d) (H : Finset (Fin d)) (a : Fin 2) :
    ∫ ω : ℕ → Obs d in
        {ω | heavyCells (fun i : Fin n => ω i) = H},
        (fixedHeavyArmContribution (fun i : Fin n => ω i) H a -
          fixedTargetArm P H a) ^ 2
        ∂Measure.infinitePi (fun _ : ℕ => obsLaw P) =
      (Measure.infinitePi (fun _ : ℕ => obsLaw P)).real
          {ω | heavyCells (fun i : Fin n => ω i) = H} *
        ∫ ω : ℕ → Obs d,
          (fixedHeavyArmContribution (fun i : Fin n => ω i) H a -
            fixedTargetArm P H a) ^ 2
          ∂Measure.infinitePi (fun _ : ℕ => obsLaw P) := by
  letI : MeasurableSpace (Finset (Fin d)) := ⊤
  let pilot := fun x : (lightBalancedSplit P).foldA n → Obs d =>
    heavyCells (rebuildPilotSample P base x)
  let estimate := fun x : (lightBalancedSplit P).foldB n → Obs d =>
    (fixedHeavyArmContribution (rebuildEstimationSample P base x) H a -
      fixedTargetArm P H a) ^ 2
  have h := oneShot_integral_estimate_restrict_pilot
    (lightBalancedSplit P) n pilot estimate
    (measurable_of_finite _) (measurable_of_finite _) ({H})
    (by exact MeasurableSet.of_discrete)
  have hp : (fun ω : ℕ → Obs d =>
      pilot (fun i : (lightBalancedSplit P).foldA n => ω i)) =
      fun ω => heavyCells (fun i : Fin n => ω i) := by
    funext ω
    exact heavyCells_rebuildPilot P base ω
  have he : (fun ω : ℕ → Obs d =>
      estimate (fun i : (lightBalancedSplit P).foldB n => ω i)) =
      fun ω => (fixedHeavyArmContribution (fun i : Fin n => ω i) H a -
        fixedTargetArm P H a) ^ 2 := by
    funext ω
    unfold estimate
    rw [fixedHeavyArmContribution_rebuildEstimation P base ω]
  dsimp only [Causalean.Stat.iidSample_infinitePi] at h
  change
    (∫ ω : ℕ → Obs d in
        (fun ω => heavyCells (fun i : Fin n => ω i)) ⁻¹' {H},
        (fun ω => (fixedHeavyArmContribution (fun i : Fin n => ω i) H a -
          fixedTargetArm P H a) ^ 2) ω
        ∂Measure.infinitePi (fun _ : ℕ => obsLaw P)) =
      (Measure.infinitePi (fun _ : ℕ => obsLaw P)).real
          ((fun ω => heavyCells (fun i : Fin n => ω i)) ⁻¹' {H}) *
        ∫ ω : ℕ → Obs d,
          (fun ω => (fixedHeavyArmContribution (fun i : Fin n => ω i) H a -
            fixedTargetArm P H a) ^ 2) ω
          ∂Measure.infinitePi (fun _ : ℕ => obsLaw P)
  rw [← hp, ← he]
  exact h

/-- Evaluates or bounds the stated integral involving integral split count ratio le. -/
lemma integral_split_count_ratio_le {n d : ℕ} {epsilon : ℝ}
    (P : DiscreteLaw d) (hOverlap : Overlap epsilon P) (hepsilon : 0 < epsilon)
    (j : Fin 2) (k : Fin d) (a : Fin 2) (hp : 0 < cellMass P k) :
    ∫ sample : Fin n → Obs d,
        (splitCategoryCount sample j k : ℝ) ^ 2 *
          (if 0 < splitCellCount sample j k a 0 +
              splitCellCount sample j k a 1 then
            ((splitCellCount sample j k a 0 +
              splitCellCount sample j k a 1 : ℕ) : ℝ)⁻¹ else 0)
        ∂productLaw P n ≤
      2 * (splitSize n j : ℝ) * cellMass P k / epsilon := by
  let g : ({i : Fin n // i ∈ splitIndices n j} → Obs d) → ℝ := fun z =>
    ((indexSet z (categorySet k)).card : ℝ) ^ 2 *
      (if 0 < (indexSet z
          (categoryArmSet k (finTwoEquiv a))).card then
        ((indexSet z
          (categoryArmSet k (finTwoEquiv a))).card : ℝ)⁻¹ else 0)
  have hsplit : Measurable
      (fun sample : Fin n → Obs d => splitTuple sample j) :=
    measurable_of_finite _
  have hg : Measurable g := measurable_of_finite _
  calc
    _ = ∫ sample : Fin n → Obs d, g (splitTuple sample j)
        ∂productLaw P n := by
      apply integral_congr_ae
      filter_upwards with sample
      simp only [g, indexSet_splitTuple_category_card,
        indexSet_splitTuple_arm_card]
    _ = ∫ z, g z ∂((productLaw P n).map
        (fun sample => splitTuple sample j)) := by
      rw [integral_map hsplit.aemeasurable hg.aestronglyMeasurable]
    _ = ∫ z, g z ∂(Measure.pi
        (fun _ : {i : Fin n // i ∈ splitIndices n j} => obsLaw P)) := by
      rw [productLaw_map_splitTuple]
    _ ≤ 2 * (Fintype.card {i : Fin n // i ∈ splitIndices n j} : ℝ) *
        cellMass P k / epsilon := by
      exact ate_nested_count_ratio_integral_le P hOverlap hepsilon k
        (finTwoEquiv a) hp
    _ = 2 * (splitSize n j : ℝ) * cellMass P k / epsilon := by
      congr 3
      simp [splitSize]

/-- Shows that empirical arm ratio mem unit Interval lies in the stated set or interval. -/
lemma empirical_arm_ratio_mem_unitInterval {n d : ℕ}
    (sample : Fin n → Obs d) (k : Fin d) (a : Fin 2) :
    (splitCellCount sample 1 k a 1 : ℝ) /
        (splitCellCount sample 1 k a 0 + splitCellCount sample 1 k a 1 : ℕ) ∈
      Set.Icc (0 : ℝ) 1 := by
  have hnum : splitCellCount sample 1 k a 1 ≤
      splitCellCount sample 1 k a 0 + splitCellCount sample 1 k a 1 := by omega
  constructor
  · positivity
  · exact div_le_one_of_le₀ (by exact_mod_cast hnum) (by positivity)

/-- Establishes the stated upper bound for abs empirical Ratio Cell le. -/
lemma abs_empiricalRatioCell_le {n d : ℕ} (sample : Fin n → Obs d)
    (k : Fin d) :
    |empiricalRatioCell sample k| ≤
      (splitCategoryCount sample 1 k : ℝ) / splitSize n 1 := by
  let r1 : ℝ := (splitCellCount sample 1 k 1 1 : ℝ) /
    (splitCellCount sample 1 k 1 0 + splitCellCount sample 1 k 1 1 : ℕ)
  let r0 : ℝ := (splitCellCount sample 1 k 0 1 : ℝ) /
    (splitCellCount sample 1 k 0 0 + splitCellCount sample 1 k 0 1 : ℕ)
  have hr1 := empirical_arm_ratio_mem_unitInterval sample k 1
  have hr0 := empirical_arm_ratio_mem_unitInterval sample k 0
  rcases hr1 with ⟨hr1lo, hr1hi⟩
  rcases hr0 with ⟨hr0lo, hr0hi⟩
  have hdiff : |r1 - r0| ≤ 1 := by
    rw [abs_le]
    constructor <;> dsimp [r1, r0] at hr1lo hr1hi hr0lo hr0hi ⊢ <;> linarith
  have hweight : 0 ≤
      (splitCategoryCount sample 1 k : ℝ) / splitSize n 1 := by positivity
  change |((splitCategoryCount sample 1 k : ℝ) / splitSize n 1) * (r1 - r0)| ≤ _
  rw [abs_mul, abs_of_nonneg hweight]
  exact mul_le_of_le_one_right hweight hdiff

/-- Establishes the stated summation identity or bound for sum split Category Count. -/
lemma sum_splitCategoryCount {n d : ℕ} (sample : Fin n → Obs d) (j : Fin 2) :
    ∑ k : Fin d, splitCategoryCount sample j k = splitSize n j := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise
    (s := splitIndices n j) (t := (Finset.univ : Finset (Fin d)))
    (f := fun i => (sample i).1) (fun _i _hi => Finset.mem_univ _)
  simpa [splitCategoryCount, splitSize] using h.symm

/-- Establishes the stated upper bound for abs heavy Contribution le one. -/
lemma abs_heavyContribution_le_one {n d : ℕ} (sample : Fin n → Obs d) :
    |heavyContribution sample| ≤ 1 := by
  calc
    |heavyContribution sample| ≤
        ∑ k ∈ heavyCells sample, |empiricalRatioCell sample k| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ heavyCells sample,
        (splitCategoryCount sample 1 k : ℝ) / splitSize n 1 := by
      exact Finset.sum_le_sum fun k _hk => abs_empiricalRatioCell_le sample k
    _ ≤ ∑ k : Fin d,
        (splitCategoryCount sample 1 k : ℝ) / splitSize n 1 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro k _hk _hnot
      positivity
    _ = (splitSize n 1 : ℝ) / splitSize n 1 := by
      rw [← Finset.sum_div]
      congr 1
      exact_mod_cast sum_splitCategoryCount sample 1
    _ ≤ 1 := div_le_one_of_le₀ le_rfl (by positivity)

/-- Establishes the stated equality relating cell Phi cell Vector eq weighted. -/
lemma cellPhi_cellVector_eq_weighted {d : ℕ} (P : DiscreteLaw d) (k : Fin d) :
    cellPhi (cellVector P k) =
      cellMass P k * (outcomeMean P true k - outcomeMean P false k) := by
  by_cases hz : cellVector P k = 0
  · have h00 := congrFun hz (0, 0)
    have h01 := congrFun hz (0, 1)
    have h10 := congrFun hz (1, 0)
    have h11 := congrFun hz (1, 1)
    simp [cellVector, finTwoEquiv] at h00 h01 h10 h11
    simp [cellPhi, hz, cellMass, outcomeMean, armMass, h00, h01, h10, h11]
  · simp [cellPhi, hz, cellVector, vectorMass, vectorArmMass, cellMass,
      outcomeMean, armMass, finTwoEquiv]
    <;> ring

/-- Establishes the stated equality relating fixed Target Heavy eq arm sub. -/
lemma fixedTargetHeavy_eq_arm_sub {d : ℕ} (P : DiscreteLaw d)
    (H : Finset (Fin d)) :
    fixedTargetHeavy P H = fixedTargetArm P H 1 - fixedTargetArm P H 0 := by
  unfold fixedTargetHeavy fixedTargetArm
  simp_rw [cellPhi_cellVector_eq_weighted, mul_sub]
  rw [Finset.sum_sub_distrib]
  simp [finTwoEquiv]

/-- Establishes the stated upper bound for fixed Heavy error sq le two arms. -/
lemma fixedHeavy_error_sq_le_two_arms {n d : ℕ} (P : DiscreteLaw d)
    (sample : Fin n → Obs d) (H : Finset (Fin d)) :
    (fixedHeavyContribution sample H - fixedTargetHeavy P H) ^ 2 ≤
      2 * (fixedHeavyArmContribution sample H 1 - fixedTargetArm P H 1) ^ 2 +
      2 * (fixedHeavyArmContribution sample H 0 - fixedTargetArm P H 0) ^ 2 := by
  rw [fixedHeavyContribution_eq_arm_sub, fixedTargetHeavy_eq_arm_sub]
  nlinarith [sq_nonneg
    ((fixedHeavyArmContribution sample H 1 - fixedTargetArm P H 1) +
      (fixedHeavyArmContribution sample H 0 - fixedTargetArm P H 0))]

/-- Establishes the stated upper bound for abs cell Phi cell Vector le mass unconditional. -/
lemma abs_cellPhi_cellVector_le_mass_unconditional {d : ℕ}
    (P : DiscreteLaw d) (k : Fin d) :
    |cellPhi (cellVector P k)| ≤ cellMass P k := by
  rw [cellPhi_cellVector_eq_weighted]
  have hp := cellMass_mem_unitInterval P k
  have hm1 := outcomeMean_mem_unitInterval P true k
  have hm0 := outcomeMean_mem_unitInterval P false k
  rw [abs_mul, abs_of_nonneg hp.1]
  apply mul_le_of_le_one_right hp.1
  rw [abs_le]
  constructor <;> linarith [hm1.1, hm1.2, hm0.1, hm0.2]

/-- Establishes the stated equality relating sum cell Mass eq one. -/
lemma sum_cellMass_eq_one {d : ℕ} (P : DiscreteLaw d) :
    ∑ k : Fin d, cellMass P k = 1 := by
  have htotal : ∑ z : Obs d, (P.pmf z).toReal = 1 := by
    simpa using (PMF.integral_eq_sum P.pmf (fun _ : Obs d => (1 : ℝ))).symm
  calc
    ∑ k : Fin d, cellMass P k = ∑ z : Obs d, (P.pmf z).toReal := by
      simp [cellMass, jointMass, Fintype.sum_prod_type]
    _ = 1 := htotal

/-- Establishes the stated upper bound for abs target Heavy le one. -/
lemma abs_targetHeavy_le_one {n d : ℕ} (P : DiscreteLaw d)
    (sample : Fin n → Obs d) : |targetHeavy P sample| ≤ 1 := by
  calc
    |targetHeavy P sample| ≤
        ∑ k ∈ heavyCells sample, |cellPhi (cellVector P k)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ heavyCells sample, cellMass P k := by
      exact Finset.sum_le_sum fun k _hk ↦
        abs_cellPhi_cellVector_le_mass_unconditional P k
    _ ≤ ∑ k : Fin d, cellMass P k := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro k _hk _hnot
      exact (cellMass_mem_unitInterval P k).1
    _ = 1 := sum_cellMass_eq_one P

/-- Establishes the stated upper bound for heavy component sq le four. -/
lemma heavy_component_sq_le_four {n d : ℕ} (P : DiscreteLaw d)
    (sample : Fin n → Obs d) :
    (heavyContribution sample - targetHeavy P sample) ^ 2 ≤ 4 := by
  have hh := abs_heavyContribution_le_one sample
  have ht := abs_targetHeavy_le_one P sample
  have habs : |heavyContribution sample - targetHeavy P sample| ≤ 2 :=
    (abs_sub _ _).trans (by linarith)
  calc
    (heavyContribution sample - targetHeavy P sample) ^ 2 =
        |heavyContribution sample - targetHeavy P sample| ^ 2 := by
      rw [sq_abs]
    _ ≤ (2 : ℝ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) habs 2
    _ = 4 := by norm_num

/-- Pilot failure costs at most four times its probability, using the global
range bound for the heavy component and its target. -/
lemma heavy_bad_pilot_setIntegral_le {n d : ℕ} (P : DiscreteLaw d) :
    ∫ sample in pilotBadEvent P 256,
        (heavyContribution sample - targetHeavy P sample) ^ 2
        ∂productLaw P n ≤
      4 * (productLaw P n).real (pilotBadEvent P 256) := by
  let err : (Fin n → Obs d) → ℝ := fun sample ↦
    (heavyContribution sample - targetHeavy P sample) ^ 2
  have herrInt : IntegrableOn err (pilotBadEvent P 256) (productLaw P n) :=
    Integrable.of_finite
  have hfourInt : IntegrableOn (fun _sample : Fin n → Obs d ↦ (4 : ℝ))
      (pilotBadEvent P 256) (productLaw P n) := integrableOn_const
  have hmono :
      ∫ sample in pilotBadEvent P 256, err sample ∂productLaw P n ≤
        ∫ _sample in pilotBadEvent P 256, (4 : ℝ) ∂productLaw P n := by
    apply integral_mono_ae herrInt hfourInt
    filter_upwards with sample
    exact heavy_component_sq_le_four P sample
  simpa [err, MeasureTheory.setIntegral_const, mul_comm] using hmono

/-- The complete pilot-failure contribution is fourth-order polynomially
small, uniformly over the calibrated dimension range. -/
lemma heavy_bad_pilot_rate :
    ∀ c : ℝ, 0 < c → ∃ C N, 0 < C ∧
      ∀ (n d : ℕ) (P : DiscreteLaw d),
        N ≤ n → (d : ℝ) ≤ c * n * logScale n →
        ∫ sample in pilotBadEvent P 256,
            (heavyContribution sample - targetHeavy P sample) ^ 2
            ∂productLaw P n ≤ C * Real.rpow n (-4) := by
  intro c hc
  rcases pilot_sandwich_256 c hc with ⟨C, N, hC, hpilot⟩
  refine ⟨4 * C, N, by positivity, ?_⟩
  intro n d P hn hd
  calc
    ∫ sample in pilotBadEvent P 256,
        (heavyContribution sample - targetHeavy P sample) ^ 2
        ∂productLaw P n ≤
        4 * (productLaw P n).real (pilotBadEvent P 256) :=
      heavy_bad_pilot_setIntegral_le P
    _ ≤ 4 * (C * Real.rpow n (-4)) := by
      gcongr
      exact hpilot n d P (productLaw P n) hn hd rfl
    _ = (4 * C) * Real.rpow n (-4) := by ring

/-- Any uniform fixed-set arm bound transfers unchanged to the random
pilot-selected set on the pilot-good event. -/
lemma heavy_good_arm_setIntegral_le {n d : ℕ} {epsilon B V : ℝ}
    (P : DiscreteLaw d) (a : Fin 2) (base : Obs d)
    (hm : 3 ≤ splitSize n 1) (hOverlap : Overlap epsilon P)
    (hepsilon : 0 < epsilon) (hB : 0 < B)
    (hpGood : ∀ sample : Fin n → Obs d, sample ∉ pilotBadEvent P 256 →
      ∀ k ∈ heavyCells sample, B ≤ cellMass P k)
    (hV : ∀ H : Finset (Fin d), (∀ k ∈ H, B ≤ cellMass P k) →
      8 * (∑ k ∈ H, cellMass P k) /
          ((splitSize n 1 : ℝ) * epsilon) +
        6 / (splitSize n 1 : ℝ) +
        4 * (H.card /
          (((((splitSize n 1 - 2 : ℕ) : ℝ) / 2 * epsilon) ^ 2) * B)) ^ 2 ≤ V) :
    ∫ sample in (pilotBadEvent P 256)ᶜ,
        (fixedHeavyArmContribution sample (heavyCells sample) a -
          fixedTargetArm P (heavyCells sample) a) ^ 2
        ∂productLaw P n ≤ V := by
  classical
  letI : MeasurableSpace (Finset (Fin d)) := ⊤
  let muInf := Measure.infinitePi (fun _ : ℕ => obsLaw P)
  let trunc : (ℕ → Obs d) → (Fin n → Obs d) := fun ω i => ω i
  let eligible : Finset (Finset (Fin d)) :=
    Finset.univ.filter (fun H => ∀ k ∈ H, B ≤ cellMass P k)
  let errH : Finset (Fin d) → (ℕ → Obs d) → ℝ := fun H ω =>
    (fixedHeavyArmContribution (trunc ω) H a - fixedTargetArm P H a) ^ 2
  let fiber : Finset (Fin d) → Set (ℕ → Obs d) := fun H =>
    {ω | heavyCells (trunc ω) = H}
  have htruncMeas : Measurable trunc := by fun_prop
  have htruncMP : MeasurePreserving trunc muInf (productLaw P n) := by
    refine ⟨htruncMeas, ?_⟩
    exact finProductLaw_eq_map (obsLaw P) n
  have hintegrable_comp (f : (Fin n → Obs d) → ℝ) :
      Integrable (fun ω => f (trunc ω)) muInf := by
    change Integrable (f ∘ trunc) muInf
    exact htruncMP.integrable_comp_of_integrable Integrable.of_finite
  have hfiberMeas (H : Finset (Fin d)) : MeasurableSet (fiber H) := by
    unfold fiber
    exact (MeasurableSet.of_discrete :
      MeasurableSet {sample : Fin n → Obs d | heavyCells sample = H}).preimage
        htruncMeas
  have htransport :
      (∫ sample in (pilotBadEvent P 256)ᶜ,
          (fixedHeavyArmContribution sample (heavyCells sample) a -
            fixedTargetArm P (heavyCells sample) a) ^ 2
          ∂productLaw P n) =
        ∫ ω in (trunc ⁻¹' (pilotBadEvent P 256)ᶜ),
          (fixedHeavyArmContribution (trunc ω) (heavyCells (trunc ω)) a -
            fixedTargetArm P (heavyCells (trunc ω)) a) ^ 2 ∂muInf := by
    rw [← integral_indicator MeasurableSet.of_discrete,
      integral_productLaw_eq_infinite_trunc,
      ← integral_indicator
        (MeasurableSet.of_discrete.preimage htruncMeas)]
    rfl
  rw [htransport]
  have hpoint (ω : ℕ → Obs d) :
      (trunc ⁻¹' (pilotBadEvent P 256)ᶜ).indicator
          (fun ω => (fixedHeavyArmContribution (trunc ω)
            (heavyCells (trunc ω)) a -
              fixedTargetArm P (heavyCells (trunc ω)) a) ^ 2) ω ≤
        ∑ H ∈ eligible, (fiber H).indicator (errH H) ω := by
    by_cases hgood : trunc ω ∉ pilotBadEvent P 256
    · have helig : heavyCells (trunc ω) ∈ eligible := by
        simp only [eligible, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hpGood (trunc ω) hgood
      rw [Set.indicator_of_mem (by simpa using hgood)]
      rw [Finset.sum_eq_single (heavyCells (trunc ω))]
      · simp [fiber, errH]
      · intro H hH hne
        simp [fiber, hne.symm]
      · intro hnot
        exact (hnot helig).elim
    · rw [Set.indicator_of_notMem (by simpa using hgood)]
      exact Finset.sum_nonneg fun H hH =>
        Set.indicator_nonneg (fun _ _ => sq_nonneg _) _
  calc
    (∫ ω in (trunc ⁻¹' (pilotBadEvent P 256)ᶜ),
        (fixedHeavyArmContribution (trunc ω) (heavyCells (trunc ω)) a -
          fixedTargetArm P (heavyCells (trunc ω)) a) ^ 2 ∂muInf) ≤
      ∫ ω, ∑ H ∈ eligible, (fiber H).indicator (errH H) ω ∂muInf := by
        rw [← integral_indicator]
        · apply integral_mono
            (by
              simpa only [Function.comp_apply] using hintegrable_comp
                (fun sample => ((pilotBadEvent P 256)ᶜ).indicator
                  (fun sample => (fixedHeavyArmContribution sample
                    (heavyCells sample) a -
                    fixedTargetArm P (heavyCells sample) a) ^ 2) sample))
            (by
              let F : (Fin n → Obs d) → ℝ := fun sample =>
                ∑ H ∈ eligible,
                  (if heavyCells sample = H then
                    (fixedHeavyArmContribution sample H a -
                      fixedTargetArm P H a) ^ 2 else 0)
              have hF := hintegrable_comp F
              simpa only [F, fiber, errH, Set.indicator_apply,
                Set.mem_setOf_eq, Function.comp_apply] using hF)
          exact hpoint
        · exact MeasurableSet.of_discrete.preimage htruncMeas
    _ = ∑ H ∈ eligible, ∫ ω in fiber H, errH H ω ∂muInf := by
      rw [integral_finset_sum eligible (fun H _ => by
        have hcomp := hintegrable_comp (fun sample =>
          ({sample | heavyCells sample = H}).indicator
            (fun sample => (fixedHeavyArmContribution sample H a -
              fixedTargetArm P H a) ^ 2) sample)
        change Integrable
          (fun ω => ({sample | heavyCells sample = H}).indicator
            (fun sample => (fixedHeavyArmContribution sample H a -
              fixedTargetArm P H a) ^ 2) (trunc ω)) muInf
        exact hcomp)]
      apply Finset.sum_congr rfl
      intro H hH
      rw [integral_indicator]
      exact hfiberMeas H
    _ = ∑ H ∈ eligible,
        muInf.real (fiber H) * ∫ ω, errH H ω ∂muInf := by
      apply Finset.sum_congr rfl
      intro H hH
      exact infinite_fixedHeavyArm_fiber_factorization P base H a
    _ ≤ ∑ H ∈ eligible, muInf.real (fiber H) * V := by
      apply Finset.sum_le_sum
      intro H hH
      apply mul_le_mul_of_nonneg_left _ (measureReal_nonneg)
      calc
        ∫ ω, errH H ω ∂muInf =
            ∫ sample : Fin n → Obs d,
              (fixedHeavyArmContribution sample H a - fixedTargetArm P H a) ^ 2
              ∂productLaw P n := by
          symm
          exact integral_productLaw_eq_infinite_trunc P _
        _ ≤ 8 * (∑ k ∈ H, cellMass P k) /
              ((splitSize n 1 : ℝ) * epsilon) +
            6 / (splitSize n 1 : ℝ) +
            4 * (H.card /
              (((((splitSize n 1 - 2 : ℕ) : ℝ) / 2 * epsilon) ^ 2) * B)) ^ 2 := by
          exact integral_fixedHeavyArm_error_sq_le P H a hm hOverlap hepsilon hB
            (by simpa only [eligible, Finset.mem_filter, Finset.mem_univ,
              true_and] using hH)
        _ ≤ V := hV H (by simpa only [eligible, Finset.mem_filter,
          Finset.mem_univ, true_and] using hH)
    _ = (∑ H ∈ eligible, muInf.real (fiber H)) * V := by
      rw [Finset.sum_mul]
    _ ≤ 1 * V := by
      have hsumle : (∑ H ∈ eligible, muInf.real (fiber H)) ≤ 1 := by
        calc
          ∑ H ∈ eligible, muInf.real (fiber H) ≤
              ∑ H ∈ (Finset.univ : Finset (Finset (Fin d))),
                muInf.real (fiber H) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            intro H hH hnot
            exact measureReal_nonneg
          _ = 1 := by
            rw [show (∑ H ∈ (Finset.univ : Finset (Finset (Fin d))),
                muInf.real (fiber H)) = muInf.real
                  ((fun ω => heavyCells (trunc ω)) ⁻¹'
                    (Finset.univ : Finset (Finset (Fin d)))) by
              exact sum_measureReal_preimage_singleton _
                (fun H _ => hfiberMeas H)]
            simp [muInf]
      have hVnonneg : (0 : ℝ) ≤ V := by
        have hH0 : (0 : ℝ) ≤
            8 * (∑ k ∈ (∅ : Finset (Fin d)), cellMass P k) /
                ((splitSize n 1 : ℝ) * epsilon) +
              6 / (splitSize n 1 : ℝ) +
              4 * ((∅ : Finset (Fin d)).card /
                (((((splitSize n 1 - 2 : ℕ) : ℝ) / 2 * epsilon) ^ 2) * B)) ^ 2 := by
          simp
          positivity
        exact hH0.trans (hV ∅ (by simp))
      exact mul_le_mul_of_nonneg_right hsumle hVnonneg
    _ = V := one_mul V

/-- The deterministic fixed-heavy-set envelope has the target minimax rate,
uniformly in the set and the underlying discrete law. -/
lemma heavy_fixed_envelope_rate {n d : ℕ} (P : DiscreteLaw d)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hn8 : 8 ≤ n)
    (H : Finset (Fin d)) :
    8 * (∑ k ∈ H, cellMass P k) /
          ((splitSize n 1 : ℝ) * epsilon) +
        6 / (splitSize n 1 : ℝ) +
        4 * (H.card /
          (((((splitSize n 1 - 2 : ℕ) : ℝ) / 2 * epsilon) ^ 2) *
            (256 * logScale n / (2 * splitSize n 0)))) ^ 2 ≤
      (16 / epsilon + 12 + 1 / epsilon ^ 4) * minimaxRate n d := by
  classical
  have hn : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hscale : logScale n = 1 + Real.log (n : ℝ) := by
    rw [logScale, Real.log_mul (by positivity : Real.exp 1 ≠ 0)
      (by positivity : (n : ℝ) ≠ 0)]
    simp
  have hL : 0 < logScale n := by rw [hscale]; positivity
  have hlogL : Real.log (n : ℝ) ≤ logScale n := by rw [hscale]; linarith
  have hmEq : splitSize n 1 = n - n / 2 := splitSize_one_eq n
  have hm0Eq : splitSize n 0 = n / 2 := splitSize_zero_eq n
  have hmNat : n ≤ 2 * splitSize n 1 := by rw [hmEq]; omega
  have hm : (n : ℝ) / 2 ≤ (splitSize n 1 : ℝ) := by
    exact (div_le_iff₀' (by norm_num : (0 : ℝ) < 2)).mpr
      (by exact_mod_cast hmNat)
  have hmpos : (0 : ℝ) < splitSize n 1 := lt_of_lt_of_le (by positivity) hm
  have hm2Nat : n ≤ 4 * (splitSize n 1 - 2) := by rw [hmEq]; omega
  have hm2 : (n : ℝ) / 8 ≤ ((splitSize n 1 - 2 : ℕ) : ℝ) / 2 := by
    have hcast : (n : ℝ) ≤ 4 * ((splitSize n 1 - 2 : ℕ) : ℝ) := by
      exact_mod_cast hm2Nat
    linarith
  have hm0Nat : 2 * splitSize n 0 ≤ n := by rw [hm0Eq]; omega
  have hm0NatPos : 0 < splitSize n 0 := by rw [hm0Eq]; omega
  have hm0pos : (0 : ℝ) < 2 * splitSize n 0 := by
    exact mul_pos (by norm_num) (by exact_mod_cast hm0NatPos)
  let B : ℝ := 256 * logScale n / (2 * splitSize n 0)
  let D : ℝ :=
    (((((splitSize n 1 - 2 : ℕ) : ℝ) / 2 * epsilon) ^ 2) * B)
  have hB : 256 * logScale n / (n : ℝ) ≤ B := by
    dsimp [B]
    apply div_le_div_of_nonneg_left (by positivity) hm0pos
    exact_mod_cast hm0Nat
  have hBpos : 0 < B := lt_of_lt_of_le (by positivity) hB
  have hq : (n : ℝ) / 8 * epsilon ≤
      ((splitSize n 1 - 2 : ℕ) : ℝ) / 2 * epsilon := by
    exact mul_le_mul_of_nonneg_right hm2 hepsilon.le
  have hq0 : 0 ≤ (n : ℝ) / 8 * epsilon := by positivity
  have hq2 := pow_le_pow_left₀ hq0 hq 2
  have hD : 4 * (n : ℝ) * epsilon ^ 2 * logScale n ≤ D := by
    calc
      4 * (n : ℝ) * epsilon ^ 2 * logScale n =
          ((n : ℝ) / 8 * epsilon) ^ 2 *
            (256 * logScale n / (n : ℝ)) := by field_simp; ring
      _ ≤ (((splitSize n 1 - 2 : ℕ) : ℝ) / 2 * epsilon) ^ 2 * B := by
        exact mul_le_mul hq2 hB (by positivity) (by positivity)
      _ = D := rfl
  have hDpos : 0 < D := lt_of_lt_of_le (by positivity) hD
  have hsum : ∑ k ∈ H, cellMass P k ≤ 1 := by
    calc
      _ ≤ ∑ k : Fin d, cellMass P k := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        intro k hk hnot
        exact (cellMass_mem_unitInterval P k).1
      _ = 1 := sum_cellMass_eq_one P
  have hcard : (H.card : ℝ) ≤ d := by
    exact_mod_cast (by simpa using H.card_le_univ)
  have hparam :
      8 * (∑ k ∈ H, cellMass P k) /
            ((splitSize n 1 : ℝ) * epsilon) ≤ 16 / epsilon / n := by
    calc
      _ ≤ 8 * 1 / ((splitSize n 1 : ℝ) * epsilon) := by gcongr
      _ ≤ 16 / epsilon / n := by
        field_simp
        nlinarith [hm]
  have hmass : 6 / (splitSize n 1 : ℝ) ≤ 12 / n := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    have hi : ((splitSize n 1 : ℝ))⁻¹ ≤ ((n : ℝ) / 2)⁻¹ :=
      inv_anti₀ (by positivity) hm
    calc
      6 * (splitSize n 1 : ℝ)⁻¹ ≤ 6 * ((n : ℝ) / 2)⁻¹ := by gcongr
      _ = 12 * (n : ℝ)⁻¹ := by field_simp; norm_num
  have hmiss0 : (H.card : ℝ) / D ≤
      (d : ℝ) / (4 * n * epsilon ^ 2 * logScale n) := by
    exact div_le_div₀ (by positivity) hcard (by positivity) hD
  have hmiss : 4 * ((H.card : ℝ) / D) ^ 2 ≤
      (1 / epsilon ^ 4) *
        ((d : ℝ) ^ 2 / ((n : ℝ) ^ 2 * (Real.log n) ^ 2)) := by
    have hsq := pow_le_pow_left₀
      (by positivity : 0 ≤ (H.card : ℝ) / D) hmiss0 2
    calc
      4 * ((H.card : ℝ) / D) ^ 2 ≤
          4 * ((d : ℝ) / (4 * n * epsilon ^ 2 * logScale n)) ^ 2 := by
        gcongr
      _ ≤ (1 / epsilon ^ 4) *
          ((d : ℝ) ^ 2 / ((n : ℝ) ^ 2 * (Real.log n) ^ 2)) := by
        have hsquares : (Real.log (n : ℝ)) ^ 2 ≤ (logScale n) ^ 2 :=
          pow_le_pow_left₀ hlog.le hlogL 2
        have hmul :=
          mul_le_mul_of_nonneg_left hsquares (sq_nonneg (d : ℝ))
        field_simp
        nlinarith [sq_nonneg (d : ℝ), sq_nonneg (Real.log (n : ℝ)),
          sq_nonneg (logScale n)]
  dsimp [B, D] at hmiss
  calc
    _ ≤ (16 / epsilon + 12) / n +
        (1 / epsilon ^ 4) *
          ((d : ℝ) ^ 2 / ((n : ℝ) ^ 2 * (Real.log n) ^ 2)) := by
      have hadd := add_le_add (add_le_add hparam hmass) hmiss
      convert hadd using 1 <;> ring
    _ ≤ (16 / epsilon + 12 + 1 / epsilon ^ 4) * minimaxRate n d := by
      unfold minimaxRate
      have hr0 : 0 ≤ 1 / (n : ℝ) := by positivity
      have hr1 : 0 ≤ (d : ℝ) ^ 2 /
          ((n : ℝ) ^ 2 * (Real.log n) ^ 2) := by positivity
      have hc0 : 0 ≤ 16 / epsilon + 12 := by positivity
      have hc1 : 0 ≤ 1 / epsilon ^ 4 := by positivity
      let K : ℝ := 16 / epsilon + 12 + 1 / epsilon ^ 4
      have hAle : 16 / epsilon + 12 ≤ K := by dsimp [K]; linarith
      have hc1le : 1 / epsilon ^ 4 ≤ K := by dsimp [K]; linarith
      calc
        _ = (16 / epsilon + 12) * (1 / (n : ℝ)) +
            (1 / epsilon ^ 4) *
              ((d : ℝ) ^ 2 / ((n : ℝ) ^ 2 * (Real.log n) ^ 2)) := by ring
        _ ≤ K * (1 / (n : ℝ)) + K *
              ((d : ℝ) ^ 2 / ((n : ℝ) ^ 2 * (Real.log n) ^ 2)) := by
          exact add_le_add (mul_le_mul_of_nonneg_right hAle hr0)
            (mul_le_mul_of_nonneg_right hc1le hr1)
        _ = (16 / epsilon + 12 + 1 / epsilon ^ 4) *
            (1 / (n : ℝ) +
              (d : ℝ) ^ 2 / ((n : ℝ) ^ 2 * (Real.log n) ^ 2)) := by
          dsimp [K]
          ring

-- @node: lem:universal-heavy-cell-rate
/-- The aggregate ratio branch has the same rate on pilot-heavy categories. -/
lemma universal_heavy_cell_rate (epsilon : ℝ) (he0 : 0 < epsilon)
    (he1 : epsilon < 1 / 2) :
    ∃ C_epsilon rho_epsilon : ℝ, ∃ N_epsilon : ℕ,
      0 < C_epsilon ∧ 0 < rho_epsilon ∧
      ∀ (n d : ℕ) (P : DiscreteLaw d)
        (mu_n : Measure (Fin n → Obs d)),
        N_epsilon ≤ n →
        (d : ℝ) ≤ rho_epsilon * n * Real.log n →
        ExperimentClass n epsilon P mu_n →
        componentErrorMSE mu_n heavyContribution (targetHeavy P) ≤
          C_epsilon * minimaxRate n d := by
  rcases heavy_bad_pilot_rate 1 (by norm_num) with
    ⟨Cbad, Nbad, hCbad, hbad⟩
  let K : ℝ := 16 / epsilon + 12 + 1 / epsilon ^ 4
  refine ⟨4 * K + Cbad, 1, max 8 (max calibrationCutoff Nbad), ?_,
    by norm_num, ?_⟩
  · dsimp [K]
    positivity
  intro n d P mu_n hn hd hclass
  have hn8 : 8 ≤ n := le_trans (le_max_left _ _) hn
  have hcut : calibrationCutoff ≤ n :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hnBad : Nbad ≤ n :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hn : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hscale : logScale n = 1 + Real.log (n : ℝ) := by
    rw [logScale, Real.log_mul (by positivity : Real.exp 1 ≠ 0)
      (by positivity : (n : ℝ) ≠ 0)]
    simp
  have hL : 0 < logScale n := by rw [hscale]; positivity
  have hdPilot : (d : ℝ) ≤ 1 * n * logScale n := by
    have hlogL : Real.log (n : ℝ) ≤ logScale n := by
      rw [hscale]
      linarith
    calc
      (d : ℝ) ≤ 1 * n * Real.log n := by simpa using hd
      _ ≤ 1 * n * logScale n := by gcongr
  have hm : 3 ≤ splitSize n 1 := by rw [splitSize_one_eq]; omega
  have hm0 : 0 < splitSize n 0 := by rw [splitSize_zero_eq]; omega
  let B : ℝ := 256 * logScale n / (2 * splitSize n 0)
  have hB : 0 < B := by
    dsimp [B]
    positivity
  let V : ℝ := K * minimaxRate n d
  let base : Obs d := P.pmf.support_nonempty.some
  have hpGood : ∀ sample : Fin n → Obs d,
      sample ∉ pilotBadEvent P 256 →
      ∀ k ∈ heavyCells sample, B ≤ cellMass P k := by
    intro sample hgood
    exact heavy_cell_mass_lower_of_good_pilot P sample hcut hgood
  have hV : ∀ H : Finset (Fin d), (∀ k ∈ H, B ≤ cellMass P k) →
      8 * (∑ k ∈ H, cellMass P k) /
          ((splitSize n 1 : ℝ) * epsilon) +
        6 / (splitSize n 1 : ℝ) +
        4 * (H.card /
          (((((splitSize n 1 - 2 : ℕ) : ℝ) / 2 * epsilon) ^ 2) * B)) ^ 2 ≤ V := by
    intro H hmass
    exact heavy_fixed_envelope_rate P he0 hn8 H
  have harm (a : Fin 2) :
      ∫ sample in (pilotBadEvent P 256)ᶜ,
          (fixedHeavyArmContribution sample (heavyCells sample) a -
            fixedTargetArm P (heavyCells sample) a) ^ 2
          ∂productLaw P n ≤ V :=
    heavy_good_arm_setIntegral_le P a base hm hclass.overlap he0 hB hpGood hV
  have hgood :
      ∫ sample in (pilotBadEvent P 256)ᶜ,
          (heavyContribution sample - targetHeavy P sample) ^ 2
          ∂productLaw P n ≤ 4 * V := by
    calc
      _ ≤ ∫ sample in (pilotBadEvent P 256)ᶜ,
          (2 * (fixedHeavyArmContribution sample (heavyCells sample) 1 -
              fixedTargetArm P (heavyCells sample) 1) ^ 2 +
            2 * (fixedHeavyArmContribution sample (heavyCells sample) 0 -
              fixedTargetArm P (heavyCells sample) 0) ^ 2)
          ∂productLaw P n := by
        apply integral_mono Integrable.of_finite Integrable.of_finite
        intro sample
        simpa only [heavyContribution_eq_fixed, targetHeavy_eq_fixed] using
          fixedHeavy_error_sq_le_two_arms P sample (heavyCells sample)
      _ = 2 * (∫ sample in (pilotBadEvent P 256)ᶜ,
            (fixedHeavyArmContribution sample (heavyCells sample) 1 -
              fixedTargetArm P (heavyCells sample) 1) ^ 2
            ∂productLaw P n) +
          2 * (∫ sample in (pilotBadEvent P 256)ᶜ,
            (fixedHeavyArmContribution sample (heavyCells sample) 0 -
              fixedTargetArm P (heavyCells sample) 0) ^ 2
            ∂productLaw P n) := by
        rw [integral_add Integrable.of_finite Integrable.of_finite,
          integral_const_mul, integral_const_mul]
      _ ≤ 2 * V + 2 * V := by gcongr <;> exact harm _
      _ = 4 * V := by ring
  have hbad' :
      ∫ sample in pilotBadEvent P 256,
          (heavyContribution sample - targetHeavy P sample) ^ 2
          ∂productLaw P n ≤ Cbad * Real.rpow n (-4) :=
    hbad n d P hnBad hdPilot
  have hrpow : Real.rpow n (-4) ≤ 1 / (n : ℝ) := by
    change (n : ℝ) ^ (-4 : ℝ) ≤ 1 / (n : ℝ)
    rw [show (-4 : ℝ) = -(4 : ℝ) by norm_num,
      Real.rpow_neg (Nat.cast_nonneg n) 4]
    rw [one_div]
    apply inv_anti₀ hnR
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    simpa using (pow_le_pow_right₀ hn1 (by norm_num : 1 ≤ 4))
  have hrate0 : 0 ≤ minimaxRate n d := by
    unfold minimaxRate
    positivity
  have honeRate : 1 / (n : ℝ) ≤ minimaxRate n d := by
    unfold minimaxRate
    exact le_add_of_nonneg_right (by positivity)
  have hbadRate :
      ∫ sample in pilotBadEvent P 256,
          (heavyContribution sample - targetHeavy P sample) ^ 2
          ∂productLaw P n ≤ Cbad * minimaxRate n d := by
    calc
      _ ≤ Cbad * Real.rpow n (-4) := hbad'
      _ ≤ Cbad * (1 / (n : ℝ)) := by gcongr
      _ ≤ Cbad * minimaxRate n d := by gcongr
  have hprod : mu_n = productLaw P n := hclass.product_law
  unfold componentErrorMSE
  rw [hprod]
  calc
    (∫ sample,
        (heavyContribution sample - targetHeavy P sample) ^ 2
        ∂productLaw P n) =
      (∫ sample in pilotBadEvent P 256,
          (heavyContribution sample - targetHeavy P sample) ^ 2
          ∂productLaw P n) +
        ∫ sample in (pilotBadEvent P 256)ᶜ,
          (heavyContribution sample - targetHeavy P sample) ^ 2
          ∂productLaw P n := by
      symm
      exact integral_add_compl MeasurableSet.of_discrete Integrable.of_finite
    _ ≤ Cbad * minimaxRate n d + 4 * V := add_le_add hbadRate hgood
    _ = (4 * K + Cbad) * minimaxRate n d := by dsimp [V]; ring

end CausalSmith.Stat.DiscreteAteMinimaxLoggap

/-- The fixed missing-outcome bias is unchanged when the law, sample, selected categories, and
treatment arm are replaced by equal values. -/
add_decl_doc CausalSmith.Stat.DiscreteAteMinimaxLoggap.fixedMissingOutcomeBias.congr_simp
