/- Final assembly of the occupancy-weighted estimator risk bound. -/

import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.OccupancyUpper
import Causalean.Mathlib.Analysis.ClipInterval

namespace CausalSmith.Stat.DiscreteAteHeterogeneityFrontier

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

open Causalean.Stat

-- @node: test_groupArm
/-- [the test sample's arm-cell count agrees with the generic grouped count](goal). -/
lemma test_groupArm {n d : ℕ} (sample : Fin n → Obs d) (a : Bool) (k : Fin d) :
    groupArmCount (fun o : Obs d => o.x) (fun o => o.a) sample a k =
      armCount sample a k := by
  rfl

-- @node: test_group
/-- [the sum of arm-specific group counts equals the total count for the cell](goal). -/
lemma test_group {n d : ℕ} (sample : Fin n → Obs d) (k : Fin d) :
    groupCount (fun o : Obs d => o.x) (fun o => o.a) sample k =
      cellCount sample k := by
  rfl

example {n d : ℕ} (sample : Fin n → Obs d) (k : Fin d) :
    usableGroup (fun o : Obs d => o.x) (fun o => o.a) sample k ↔
      usableCell sample k := by
  simp only [usableGroup, usableCell, test_groupArm, decide_eq_true_eq]

-- @node: test_group_total
/-- [summing the test sample's cell counts gives the sample size](goal). -/
lemma test_group_total {n d : ℕ} (sample : Fin n → Obs d) :
    usableGroupTotal (fun o : Obs d => o.x) (fun o => o.a) sample =
      usableTotal sample := by
  unfold usableGroupTotal usableTotal
  apply Finset.sum_congr rfl
  intro k _
  rw [show usableGroup (fun o : Obs d => o.x) (fun o => o.a) sample k ↔
      usableCell sample k by
        simp only [usableGroup, usableCell, test_groupArm, decide_eq_true_eq]]
  simp only [test_group]

-- @node: testUnclipped
/-- This is the untruncated occupancy estimator before final clipping. -/
noncomputable def testUnclipped {n d : ℕ} (sample : Fin n → Obs d) : ℝ :=
  if 0 < usableTotal sample then
    (∑ k : Fin d, if usableCell sample k then
      (cellCount sample k : ℝ) *
        (empiricalArmMean sample true k - empiricalArmMean sample false k)
      else 0) / usableTotal sample
  else 0

-- @node: test_armResidualMean
/-- If [the stated count condition holds](hyp:hcount), [the arm-specific residual contribution has
  mean zero](goal). -/
lemma test_armResidualMean {n d : ℕ} (P : RealLaw d)
    (sample : Fin n → Obs d) (a : Bool) (k : Fin d)
    (hcount : 0 < armCount sample a k) :
    armResidualMean (fun o : Obs d => o.x) (fun o => o.a) (fun o => o.y)
      P.outcomeMean sample a k =
      empiricalArmMean sample a k - P.outcomeMean a k := by
  rw [armResidualMean, if_pos]
  · rw [empiricalArmMean, if_pos hcount]
    unfold armResidualSum supportedArmGroupResidual armGroupResidual armGroupEvent armSum
    simp only [Set.indicator_apply]
    have hcountR : (armCount sample a k : ℝ) ≠ 0 := by exact_mod_cast hcount.ne'
    simp only [test_groupArm]
    have hsum : (∑ i : Fin n, if sample i ∈
          {omega : Obs d | omega.x = k ∧ omega.a = a}
        then (sample i).y - P.outcomeMean a k else 0) =
        (∑ i : Fin n, if (sample i).x = k ∧ (sample i).a = a
          then (sample i).y else 0) -
        (armCount sample a k : ℝ) * P.outcomeMean a k := by
      unfold armCount
      simp only [Set.mem_ofPred_eq]
      rw [← Finset.sum_filter, ← Finset.sum_filter]
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    rw [hsum]
    field_simp
  · simpa only [test_groupArm] using hcount

-- @node: testUnclipped_sub_center_eq
/-- [the untruncated occupancy estimator minus its design center equals the sum of its
  arm-specific residual contributions](goal). -/
lemma testUnclipped_sub_center_eq {n d : ℕ} {epsilon M sigma : ℝ}
    (P : ModelClass d epsilon M sigma) (sample : Fin n → Obs d) :
    testUnclipped sample - collisionDesignCenter P sample =
      occupancyWeightedResidual P.law.observedLaw
        (fun o : Obs d => o.x) (fun o => o.a) (fun o => o.y)
        P.law.outcomeMean sample := by
  unfold testUnclipped collisionDesignCenter occupancyWeightedResidual
  rw [test_group_total]
  by_cases ht : 0 < usableTotal sample
  · simp only [if_pos ht]
    rw [div_eq_inv_mul, div_eq_inv_mul]
    rw [← mul_sub]
    congr 1
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    have hu : usableGroup (fun o : Obs d => o.x) (fun o => o.a) sample k ↔
        usableCell sample k := by
      simp only [usableGroup, usableCell, test_groupArm, decide_eq_true_eq]
    rw [hu]
    by_cases huk : usableCell sample k
    · rw [if_pos huk, if_pos huk, test_group]
      have hcounts : 0 < armCount sample false k ∧ 0 < armCount sample true k := by
        simpa [usableCell] using huk
      rw [test_armResidualMean P.law sample true k hcounts.2,
        test_armResidualMean P.law sample false k hcounts.1]
      simp only [if_pos huk]
      unfold cellEffect
      ring
    · simp [huk]
  · simp only [if_neg ht]
    ring

-- @node: test_arm_mass
/-- [the integral of an arm indicator equals its treatment-arm probability](goal). -/
lemma test_arm_mass {d : ℕ} (P : RealLaw d) (a : Bool) (k : Fin d) :
    realMass P.observedLaw (armGroupEvent (fun o : Obs d => o.x)
      (fun o => o.a) a k) =
      P.cellMass k * (if a then P.propensity k else 1 - P.propensity k) := by
  let _ : IsProbabilityMeasure (P.outcomeLaw a k) := P.outcome_isProbability a k
  have h := P.arm_outcome_factorization a k Set.univ MeasurableSet.univ
  simp [realMass] at h
  simpa [armGroupEvent, realMass] using h.symm

-- @node: test_memLp
/-- [the untruncated occupancy estimator has a finite second moment](goal). -/
lemma test_memLp {d : ℕ} {epsilon M sigma : ℝ}
    (P : ModelClass d epsilon M sigma) (a : Bool) (k : Fin d) :
    MemLp (supportedArmGroupResidual (fun o : Obs d => o.x) (fun o => o.a)
      (fun o => o.y) P.law.outcomeMean a k) 2 P.law.observedLaw := by
  have hM : M ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) P.M_ge_one)
  have hy : MemLp (fun o : Obs d => o.y) 2 P.law.observedLaw := by
    have h := (memLp_two_observed_normalized_outcome P).const_mul M
    convert h using 1
    funext o
    field_simp
  have hr : MemLp (fun o : Obs d => o.y - P.law.outcomeMean a k) 2
      P.law.observedLaw := hy.sub (memLp_const _)
  have htuple : Measurable (fun o : Obs d => (o.x, o.a, o.y)) :=
    measurable_iff_comap_le.mpr le_rfl
  have hx : Measurable (fun o : Obs d => o.x) := measurable_fst.comp htuple
  have ha : Measurable (fun o : Obs d => o.a) :=
    measurable_fst.comp (measurable_snd.comp htuple)
  have hevent := measurableSet_armGroupEvent (fun o : Obs d => o.x)
    (fun o => o.a) hx ha a k
  change MemLp ((armGroupEvent (fun o : Obs d => o.x) (fun o => o.a) a k).indicator
    (fun o => o.y - P.law.outcomeMean a k)) 2 P.law.observedLaw
  exact hr.indicator hevent

-- @node: test_center_memLp
/-- [the centered occupancy estimator has a finite second moment](goal). -/
lemma test_center_memLp {n d : ℕ} {epsilon M sigma : ℝ}
    (P : ModelClass d epsilon M sigma) :
    MemLp (fun sample : Fin n → Obs d =>
      collisionDesignCenter P sample - rawAteFormula P.law) 2
      (productLaw n P.law) := by
  have hm : Measurable (fun sample : Fin n → Obs d =>
      collisionDesignCenter P sample - rawAteFormula P.law) :=
    (measurable_collisionDesignCenter P).sub measurable_const
  apply MemLp.of_bound hm.aestronglyMeasurable
    (M * Real.sqrt (sigma ^ 2 + 1))
  filter_upwards [usableCell_supported_ae P.law] with sample hs
  have hsq := collisionDesignCenter_bias_sq_le P sample hs
  rw [Real.norm_eq_abs]
  have hnonneg : 0 ≤ sigma ^ 2 + 1 := by positivity
  have hsqrt : 0 ≤ Real.sqrt (sigma ^ 2 + 1) := Real.sqrt_nonneg _
  have hM : 0 ≤ M := le_trans zero_le_one P.M_ge_one
  have hboundnonneg : 0 ≤ M * Real.sqrt (sigma ^ 2 + 1) := mul_nonneg hM hsqrt
  apply (sq_le_sq₀ (abs_nonneg _) hboundnonneg).mp
  rw [sq_abs, mul_pow, Real.sq_sqrt hnonneg]
  have hfactor : sigma ^ 2 + (if usableTotal sample = 0 then 1 else 0) ≤
      sigma ^ 2 + 1 := by
    split <;> simp
  exact hsq.trans (mul_le_mul_of_nonneg_left hfactor (sq_nonneg M))

-- @node: lem:continuous-occupancy-collision-upper-all-d
/-- [for every alphabet size, the collision estimator achieves the stated continuous-outcome risk
  upper bound](goal). -/
lemma continuous_occupancy_collision_upper_all_d :
    ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 / 2 →
    ∃ C_epsilon : ℝ, 0 < C_epsilon ∧
      ∀ n d : ℕ, ∀ M sigma : ℝ,
        0 < n → 0 < d →
        ∀ P : ModelClass d epsilon M sigma,
          mse P.law (collisionEstimator (n := n) (d := d) M) ≤
            C_epsilon * M ^ 2 *
              (1 / (n : ℝ) + sigma ^ 2 + (d : ℝ) / (n : ℝ) ^ 2) := by
  intro epsilon hepsilon hepsilon_half
  rcases zengUsableOccupancyReciprocal epsilon with
    ⟨b, B, hb, hB, hoccupancy⟩
  let K : ℝ := 16 / (epsilon ^ 2 * (1 - epsilon))
  let C : ℝ := 2 * K * B + (2 * K * B + 4) / b + 2
  have hK : 0 < K := by
    dsimp [K]
    have : 0 < 1 - epsilon := by linarith
    positivity
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro n d M sigma hn hd P
  have hM : 0 ≤ M := le_trans zero_le_one P.M_ge_one
  have htuple : Measurable (fun o : Obs d => (o.x, o.a, o.y)) :=
    measurable_iff_comap_le.mpr le_rfl
  have hx : Measurable (fun o : Obs d => o.x) := measurable_fst.comp htuple
  have ha : Measurable (fun o : Obs d => o.a) :=
    measurable_fst.comp (measurable_snd.comp htuple)
  have hy : Measurable (fun o : Obs d => o.y) :=
    measurable_snd.comp (measurable_snd.comp htuple)
  have hmem : ∀ a k, MemLp
      (supportedArmGroupResidual (fun o : Obs d => o.x) (fun o => o.a)
        (fun o => o.y) P.law.outcomeMean a k) 2 P.law.observedLaw :=
    fun a k => test_memLp P a k
  have hcenter : ∀ a k,
      ∫ o in armGroupEvent (fun o : Obs d => o.x) (fun o => o.a) a k,
        armGroupResidual (fun o : Obs d => o.y) P.law.outcomeMean a k o
        ∂P.law.observedLaw = 0 := by
    intro a k
    simpa [armGroupEvent, armGroupResidual] using
      observed_arm_cell_centered_integral_eq_zero P a k
  have hsq : ∀ a k,
      ∫ o in armGroupEvent (fun o : Obs d => o.x) (fun o => o.a) a k,
          (armGroupResidual (fun o : Obs d => o.y) P.law.outcomeMean a k o) ^ 2
          ∂P.law.observedLaw ≤
        (P.law.observedLaw
          (armGroupEvent (fun o : Obs d => o.x) (fun o => o.a) a k)).toReal * M ^ 2 := by
    intro a k
    rw [show (P.law.observedLaw
        (armGroupEvent (fun o : Obs d => o.x) (fun o => o.a) a k)).toReal =
        P.law.cellMass k * (if a then P.law.propensity k else 1 - P.law.propensity k) by
      simpa [realMass] using test_arm_mass P.law a k]
    simpa [armGroupEvent, armGroupResidual] using
      observed_arm_cell_centered_sq_integral_le P a k
  have hoverlap : ∀ k,
      0 < (P.law.observedLaw
        (groupEvent (fun o : Obs d => o.x) k)).toReal → ∀ a,
      epsilon * (P.law.observedLaw
        (groupEvent (fun o : Obs d => o.x) k)).toReal ≤
        (P.law.observedLaw
          (armGroupEvent (fun o : Obs d => o.x) (fun o => o.a) a k)).toReal := by
    intro k hk a
    have hg : (P.law.observedLaw
        (groupEvent (fun o : Obs d => o.x) k)).toReal = P.law.cellMass k := by
      simpa [groupEvent, realMass] using (P.law.cellMass_eq k).symm
    rw [hg, show (P.law.observedLaw
        (armGroupEvent (fun o : Obs d => o.x) (fun o => o.a) a k)).toReal =
        P.law.cellMass k * (if a then P.law.propensity k else 1 - P.law.propensity k) by
      simpa [realMass] using test_arm_mass P.law a k]
    have hov := P.overlap k (by simpa [hg] using hk)
    cases a <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
      nlinarith [P.law.cellMass_range k]
  have hnoise0 := Causalean.Stat.integral_occupancyWeightedResidual_sq_le_reciprocal
    (n := n) P.law.observedLaw (fun o : Obs d => o.x) (fun o => o.a)
      (fun o => o.y) P.law.outcomeMean M epsilon hx ha hy hmem hcenter hsq
      hepsilon hepsilon_half.le hoverlap
  have hnoise :
      (∫ s, (testUnclipped s - collisionDesignCenter P s) ^ 2 ∂productLaw n P.law) ≤
        K * M ^ 2 *
          (∫ s, (if 0 < usableTotal s then (1 : ℝ) / usableTotal s else 0)
            ∂productLaw n P.law) := by
    rw [show productLaw n P.law = Measure.pi (fun _ : Fin n => P.law.observedLaw) from rfl]
    simpa only [test_group_total, one_div, K, testUnclipped_sub_center_eq] using hnoise0
  have hbias := integral_collisionDesignCenter_bias_sq_le (n := n) P
  have hocc := hoccupancy n d M sigma P
  let x : ℝ := (max n d : ℕ) / (n : ℝ) ^ 2
  have hxpos : 0 < x := by dsimp [x]; positivity
  have hexpeq : -b * (n : ℝ) ^ 2 / (max n d : ℕ) = -b / x := by
    dsimp [x]
    field_simp
  have hexp : Real.exp (-b * (n : ℝ) ^ 2 / (max n d : ℕ)) ≤ (1 / b) * x := by
    rw [hexpeq]
    exact exp_neg_div_absorbed_by_linear_rate hb hxpos
  have hxrate := occupancy_max_rate_le (d := d) hn
  have hnoise' :
      (∫ s, (testUnclipped s - collisionDesignCenter P s) ^ 2 ∂productLaw n P.law) ≤
        K * M ^ 2 * B * (x + Real.exp (-b * (n : ℝ) ^ 2 / (max n d : ℕ))) := by
    have hocc2 : (∫ s, (if 0 < usableTotal s then (1 : ℝ) / usableTotal s else 0)
        ∂productLaw n P.law) ≤
        B * (x + Real.exp (-b * (n : ℝ) ^ 2 / (max n d : ℕ))) := by
      simpa [x] using hocc.2
    calc
      _ ≤ K * M ^ 2 * (B * (x + Real.exp (-b * (n : ℝ) ^ 2 / (max n d : ℕ)))) :=
        hnoise.trans (mul_le_mul_of_nonneg_left hocc2
          (mul_nonneg hK.le (sq_nonneg M)))
      _ = _ := by ring
  have hbias' :
      (∫ s, (collisionDesignCenter P s - rawAteFormula P.law) ^ 2
        ∂productLaw n P.law) ≤
        M ^ 2 * (sigma ^ 2 + 2 * Real.exp (-b * (n : ℝ) ^ 2 / (max n d : ℕ))) := by
    exact hbias.trans (mul_le_mul_of_nonneg_left
      (add_le_add (le_refl (sigma ^ 2)) hocc.1) (sq_nonneg M))
  have hresLp := Causalean.Stat.occupancyWeightedResidual_memLp_two
    (n := n) P.law.observedLaw (fun o : Obs d => o.x) (fun o => o.a)
      (fun o => o.y) P.law.outcomeMean hx ha hy hmem
  have hnoiseLp : MemLp (fun s : Fin n → Obs d =>
      testUnclipped s - collisionDesignCenter P s) 2 (productLaw n P.law) := by
    rw [show productLaw n P.law = Measure.pi (fun _ : Fin n => P.law.observedLaw) from rfl]
    convert hresLp using 1
    funext s
    exact testUnclipped_sub_center_eq P s
  have hrawLp : MemLp (fun s : Fin n → Obs d =>
      testUnclipped s - rawAteFormula P.law) 2 (productLaw n P.law) := by
    convert hnoiseLp.add (test_center_memLp (n := n) P) using 1
    funext s
    change testUnclipped s - rawAteFormula P.law =
      (testUnclipped s - collisionDesignCenter P s) +
        (collisionDesignCenter P s - rawAteFormula P.law)
    ring
  have hrawSq := hrawLp.integrable_sq
  have hclipMeas := (collisionEstimator_admissible (n := n) (d := d) hM).1
  have hclipLp : MemLp (fun s : Fin n → Obs d =>
      collisionEstimator M s - rawAteFormula P.law) 2 (productLaw n P.law) := by
    apply hrawLp.of_le (hclipMeas.sub measurable_const).aestronglyMeasurable
    filter_upwards with s
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    have ht : rawAteFormula P.law ∈ Icc (-M) M := by
      have habs := modelClass_rawAte_abs_le P
      exact (abs_le.mp habs)
    simpa [collisionEstimator, clip, testUnclipped,
      Causalean.Mathlib.Analysis.clipIcc] using
      Causalean.Mathlib.Analysis.abs_clipIcc_sub_le ht (testUnclipped s)
  have hclipSq := hclipLp.integrable_sq
  have hclipRaw : mse P.law (collisionEstimator (n := n) (d := d) M) ≤
      ∫ s, (testUnclipped s - rawAteFormula P.law) ^ 2 ∂productLaw n P.law := by
    unfold mse
    apply integral_mono hclipSq hrawSq
    intro s
    have ht : rawAteFormula P.law ∈ Icc (-M) M := by
      have habs := modelClass_rawAte_abs_le P
      exact (abs_le.mp habs)
    simpa [collisionEstimator, clip, testUnclipped,
      Causalean.Mathlib.Analysis.clipIcc] using
      Causalean.Mathlib.Analysis.clipIcc_sub_sq_le ht (testUnclipped s)
  calc
    mse P.law (collisionEstimator M) ≤
        ∫ s, (testUnclipped s - rawAteFormula P.law) ^ 2 ∂productLaw n P.law := hclipRaw
    _ ≤ 2 * (∫ s, (testUnclipped s - collisionDesignCenter P s) ^ 2 ∂productLaw n P.law) +
        2 * (∫ s, (collisionDesignCenter P s - rawAteFormula P.law) ^ 2 ∂productLaw n P.law) := by
      rw [← integral_const_mul, ← integral_const_mul, ← integral_add]
      · apply integral_mono hrawSq
          ((hnoiseLp.integrable_sq.const_mul 2).add
            ((test_center_memLp (n := n) P).integrable_sq.const_mul 2))
        intro s
        change (testUnclipped s - rawAteFormula P.law) ^ 2 ≤
          2 * (testUnclipped s - collisionDesignCenter P s) ^ 2 +
            2 * (collisionDesignCenter P s - rawAteFormula P.law) ^ 2
        nlinarith [sq_nonneg (testUnclipped s - collisionDesignCenter P s -
          (collisionDesignCenter P s - rawAteFormula P.law))]
      · exact hnoiseLp.integrable_sq.const_mul 2
      · exact (test_center_memLp (n := n) P).integrable_sq.const_mul 2
    _ ≤ 2 * (K * M ^ 2 * B * (x + Real.exp (-b * (n : ℝ) ^ 2 / (max n d : ℕ)))) +
        2 * (M ^ 2 * (sigma ^ 2 + 2 * Real.exp (-b * (n : ℝ) ^ 2 / (max n d : ℕ)))) :=
      add_le_add (mul_le_mul_of_nonneg_left hnoise' (by norm_num))
        (mul_le_mul_of_nonneg_left hbias' (by norm_num))
    _ ≤ C * M ^ 2 * (1 / (n : ℝ) + sigma ^ 2 + (d : ℝ) / (n : ℝ) ^ 2) := by
      have hsig : 0 ≤ sigma ^ 2 := sq_nonneg sigma
      have hrate : 0 ≤ 1 / (n : ℝ) + (d : ℝ) / (n : ℝ) ^ 2 := by positivity
      have hKB : 0 ≤ K * B := (mul_pos hK hB).le
      have hMb : 0 ≤ (2 * K * B + 4) / b := by positivity
      have hcoef : 0 ≤ 2 * K * B + 4 := by positivity
      have hexpCoef := mul_le_mul_of_nonneg_left hexp hcoef
      have hD : 0 ≤ 2 * K * B + (2 * K * B + 4) / b := by positivity
      have hxrate' : x ≤ 1 / (n : ℝ) + (d : ℝ) / (n : ℝ) ^ 2 := by
        simpa [x] using hxrate
      have hxD := mul_le_mul_of_nonneg_left hxrate' hD
      have hinter :
          2 * K * B * (x + Real.exp (-b * (n : ℝ) ^ 2 / (max n d : ℕ))) +
            2 * (sigma ^ 2 + 2 * Real.exp (-b * (n : ℝ) ^ 2 / (max n d : ℕ))) ≤
          C * (1 / (n : ℝ) + sigma ^ 2 + (d : ℝ) / (n : ℝ) ^ 2) := by
        calc
          _ = 2 * K * B * x + (2 * K * B + 4) *
                Real.exp (-b * (n : ℝ) ^ 2 / (max n d : ℕ)) + 2 * sigma ^ 2 := by ring
          _ ≤ 2 * K * B * x + (2 * K * B + 4) * ((1 / b) * x) +
                2 * sigma ^ 2 := by linarith
          _ = (2 * K * B + (2 * K * B + 4) / b) * x + 2 * sigma ^ 2 := by ring
          _ ≤ (2 * K * B + (2 * K * B + 4) / b) *
                (1 / (n : ℝ) + (d : ℝ) / (n : ℝ) ^ 2) + 2 * sigma ^ 2 := by
            linarith
          _ ≤ C * (1 / (n : ℝ) + sigma ^ 2 + (d : ℝ) / (n : ℝ) ^ 2) := by
            dsimp [C]
            nlinarith [mul_nonneg hD hrate, mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hsig]
      have := mul_le_mul_of_nonneg_left hinter (sq_nonneg M)
      nlinarith

-- @node: lem:continuous-occupancy-collision-upper
/-- [Restricted-range form of the occupancy estimator upper bound](goal). -/
lemma continuous_occupancy_collision_upper :
    ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 / 2 →
    ∃ C_epsilon c_epsilon : ℝ, 0 < C_epsilon ∧ 0 < c_epsilon ∧
      ∀ n d : ℕ, ∀ M sigma : ℝ,
        0 < n → 0 < d →
        (d : ℝ) ≤ c_epsilon * (n : ℝ) ^ 2 / logEN n →
        ∀ P : ModelClass d epsilon M sigma,
          mse P.law (collisionEstimator (n := n) (d := d) M) ≤
            C_epsilon * M ^ 2 *
              (1 / (n : ℝ) + sigma ^ 2 + (d : ℝ) / (n : ℝ) ^ 2) := by
  intro epsilon hepsilon hepsilon_half
  obtain ⟨C_epsilon, hC, hbound⟩ :=
    continuous_occupancy_collision_upper_all_d epsilon hepsilon hepsilon_half
  refine ⟨C_epsilon, 1, hC, zero_lt_one, ?_⟩
  intro n d M sigma hn hd _ P
  exact hbound n d M sigma hn hd P

end CausalSmith.Stat.DiscreteAteHeterogeneityFrontier
