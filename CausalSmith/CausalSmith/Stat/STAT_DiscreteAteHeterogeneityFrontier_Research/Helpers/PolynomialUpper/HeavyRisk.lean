/- Fixed-heavy risk bridge for the polynomial upper construction. -/

import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.OccupancyUpperAssembly
import Causalean.Stat.Sample.FiniteStratumMarkedRatioMse

namespace CausalSmith.Stat.DiscreteAteHeterogeneityFrontier

open MeasureTheory ProbabilityTheory
open Causalean.Stat
open Causalean.Stat.FiniteStratumMarkedRatioMse

-- @node: polynomialSupportedCenter
/-- The arm-cell center agrees with the model mean on supported cells and is
zero on null cells, making the fixed-stratum center envelope total. -/
noncomputable def polynomialSupportedCenter {d : ℕ} (P : RealLaw d)
    (a : Bool) (k : Fin d) : ℝ :=
  if 0 < P.cellMass k then P.outcomeMean a k else 0

-- @node: polynomialSupportedCenter_abs_le
/-- [The support-totalized center obeys the model's half-scale envelope on every cell, including
  null cells](goal). -/
lemma polynomialSupportedCenter_abs_le {d : ℕ} {epsilon M sigma : ℝ}
    (P : ModelClass d epsilon M sigma) (a : Bool) (k : Fin d) :
    |polynomialSupportedCenter P.law a k| ≤ M := by
  unfold polynomialSupportedCenter
  split_ifs with hk
  · exact (P.mean_normalization a k hk).trans (by linarith [P.M_ge_one])
  · simp
    exact le_trans zero_le_one P.M_ge_one

-- @node: polynomialSupportedCenter_residual_memLp
/-- [Supported residuals about the totalized centers are square-integrable under the observed
  law](goal). -/
lemma polynomialSupportedCenter_residual_memLp {d : ℕ}
    {epsilon M sigma : ℝ} (P : ModelClass d epsilon M sigma)
    (a : Bool) (k : Fin d) :
    MemLp (supportedArmResidual (fun o : Obs d => o.x) (fun o => o.a)
      (fun o => o.y) (polynomialSupportedCenter P.law) a k) 2
      P.law.observedLaw := by
  let f := supportedArmResidual (fun o : Obs d => o.x) (fun o => o.a)
    (fun o => o.y) P.law.outcomeMean a k
  let g := supportedArmResidual (fun o : Obs d => o.x) (fun o => o.a)
    (fun o => o.y) (polynomialSupportedCenter P.law) a k
  have hf : MemLp f 2 P.law.observedLaw := test_memLp P a k
  have hfg : f =ᵐ[P.law.observedLaw] g := by
    by_cases hk : 0 < P.law.cellMass k
    · filter_upwards with o
      by_cases ho : o.x = k ∧ o.a = a
      · rcases ho with ⟨rfl, hoa⟩
        simp [f, g, supportedArmResidual, supportedArmGroupResidual,
          armGroupEvent, hoa]
        unfold Causalean.Stat.armGroupResidual
        simp [polynomialSupportedCenter, hk]
      · simp [f, g, supportedArmResidual, supportedArmGroupResidual,
          armGroupEvent, ho]
    · have hkzero : P.law.cellMass k = 0 :=
        le_antisymm (not_lt.mp hk) (P.law.cellMass_range k).1
      have hnull := observed_arm_cell_measure_eq_zero_of_cellMass_eq_zero
        P.law a k hkzero
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with o ho
      simp [f, g, supportedArmResidual, supportedArmGroupResidual,
        armGroupEvent, ho]
  have hgmeas : AEStronglyMeasurable g P.law.observedLaw := hf.1.congr hfg
  exact hf.congr_norm hgmeas (hfg.mono fun _ h => by rw [h])

-- @node: polynomialSupportedCenter_centered_integral
/-- [Each support-totalized arm-cell residual has zero integral](goal). -/
lemma polynomialSupportedCenter_centered_integral {d : ℕ}
    {epsilon M sigma : ℝ} (P : ModelClass d epsilon M sigma)
    (a : Bool) (k : Fin d) :
    ∫ o in armCategoryEvent (fun o : Obs d => o.x) (fun o => o.a) a k,
        (o.y - polynomialSupportedCenter P.law a k) ∂P.law.observedLaw = 0 := by
  by_cases hk : 0 < P.law.cellMass k
  · simpa [polynomialSupportedCenter, hk, armCategoryEvent, armGroupEvent] using
      observed_arm_cell_centered_integral_eq_zero P a k
  · have hkzero : P.law.cellMass k = 0 :=
      le_antisymm (not_lt.mp hk) (P.law.cellMass_range k).1
    have hnull := observed_arm_cell_measure_eq_zero_of_cellMass_eq_zero
      P.law a k hkzero
    simpa [armCategoryEvent, armGroupEvent] using
      (setIntegral_measure_zero
        (fun o : Obs d => o.y - polynomialSupportedCenter P.law a k) hnull)

-- @node: polynomialSupportedCenter_centered_sq_le
/-- [Each support-totalized arm-cell residual obeys the conditional second-moment envelope with
  the exact observed arm-cell mass](goal). -/
lemma polynomialSupportedCenter_centered_sq_le {d : ℕ}
    {epsilon M sigma : ℝ} (P : ModelClass d epsilon M sigma)
    (a : Bool) (k : Fin d) :
    ∫ o in armCategoryEvent (fun o : Obs d => o.x) (fun o => o.a) a k,
        (o.y - polynomialSupportedCenter P.law a k) ^ 2 ∂P.law.observedLaw ≤
      armCategoryMass P.law.observedLaw (fun o : Obs d => o.x)
        (fun o => o.a) a k * M ^ 2 := by
  rw [show armCategoryMass P.law.observedLaw (fun o : Obs d => o.x)
      (fun o => o.a) a k =
      P.law.cellMass k *
        (if a then P.law.propensity k else 1 - P.law.propensity k) by
    change realMass P.law.observedLaw
      (armGroupEvent (fun o : Obs d => o.x) (fun o => o.a) a k) = _
    exact test_arm_mass P.law a k]
  by_cases hk : 0 < P.law.cellMass k
  · simpa [polynomialSupportedCenter, hk, armCategoryEvent, armGroupEvent] using
      observed_arm_cell_centered_sq_integral_le P a k
  · have hkzero : P.law.cellMass k = 0 :=
      le_antisymm (not_lt.mp hk) (P.law.cellMass_range k).1
    have hnull := observed_arm_cell_measure_eq_zero_of_cellMass_eq_zero
      P.law a k hkzero
    rw [hkzero, zero_mul, zero_mul]
    rw [show armCategoryEvent (fun o : Obs d => o.x) (fun o => o.a) a k =
        {o : Obs d | o.x = k ∧ o.a = a} by rfl,
      setIntegral_measure_zero _ hnull]

-- @node: polynomialPopulationArmMean_eq_outcomeMean
/-- If [the stated condition on the cell holds](hyp:hk), [on every supported cell, the generic
  fixed-stratum population arm mean is exactly the model's declared conditional outcome
  mean](goal). -/
lemma polynomialPopulationArmMean_eq_outcomeMean {d : ℕ}
    {epsilon M sigma : ℝ} (P : ModelClass d epsilon M sigma)
    (a : Bool) (k : Fin d) (hk : 0 < P.law.cellMass k) :
    populationArmMean P.law.observedLaw (fun o : Obs d => o.x)
        (fun o => o.a) (fun o => o.y) a k = P.law.outcomeMean a k := by
  have htuple : Measurable (fun o : Obs d => (o.x, o.a, o.y)) :=
    measurable_iff_comap_le.mpr le_rfl
  have hy : Measurable (fun o : Obs d => o.y) :=
    measurable_snd.comp (measurable_snd.comp htuple)
  let c : ℝ := P.law.cellMass k *
    (if a then P.law.propensity k else 1 - P.law.propensity k)
  have hc : armCategoryMass P.law.observedLaw (fun o : Obs d => o.x)
      (fun o => o.a) a k = c := by
    change realMass P.law.observedLaw
      (armGroupEvent (fun o : Obs d => o.x) (fun o => o.a) a k) = c
    simpa [c] using test_arm_mass P.law a k
  have hc0 : 0 ≤ c := by
    dsimp [c]
    apply mul_nonneg (P.law.cellMass_range k).1
    split <;> simp_all [(P.law.propensity_range k).1,
      (P.law.propensity_range k).2]
  have hcpos : 0 < c := by
    rcases P.overlap k hk with ⟨hlower, hupper⟩
    cases a <;> simp [c] <;> nlinarith [P.epsilon_pos]
  have hmap := observed_arm_cell_outcome_measure P.law a k
  unfold populationArmMean
  rw [if_pos (hc ▸ hcpos), hc]
  have hmeas : AEStronglyMeasurable (fun y : ℝ => y)
      (Measure.map (fun o : Obs d => o.y)
        (P.law.observedLaw.restrict
          (armCategoryEvent (fun o : Obs d => o.x) (fun o => o.a) a k))) :=
    measurable_id.aestronglyMeasurable
  rw [← integral_map hy.aemeasurable hmeas]
  change c⁻¹ * (∫ y, y ∂Measure.map (fun o : Obs d => o.y)
    (P.law.observedLaw.restrict {o : Obs d | o.x = k ∧ o.a = a})) = _
  rw [hmap, integral_smul_measure]
  rw [show P.law.cellMass k *
      (if a then P.law.propensity k else 1 - P.law.propensity k) = c by rfl]
  simp only [smul_eq_mul]
  change c⁻¹ * ((ENNReal.ofReal c).toReal *
    (∫ y, y ∂P.law.outcomeLaw a k)) = _
  rw [ENNReal.toReal_ofReal hc0, ← P.law.outcomeMean_eq]
  field_simp [hcpos.ne']

-- @node: polynomialFixedStratumMarkedTarget_eq_cellEffectSum
/-- If [the selected heavy set is fixed](hyp:hH), [for a deterministic supported heavy set, the
  generic marked-ratio target is the corresponding cell-mass-weighted sum of model treatment
  effects](goal). -/
lemma polynomialFixedStratumMarkedTarget_eq_cellEffectSum {d : ℕ}
    {epsilon M sigma : ℝ} (P : ModelClass d epsilon M sigma)
    (H : Finset (Fin d)) (hH : ∀ k ∈ H, 0 < P.law.cellMass k) :
    fixedStratumMarkedTarget P.law.observedLaw
        (fun o : Obs d => o.x) (fun o => o.a) (fun o => o.y) H =
      ∑ k ∈ H, P.law.cellMass k * cellEffect P.law k := by
  unfold fixedStratumMarkedTarget fixedStratumArmTarget cellEffect
  have hmass (k : Fin d) :
      categoryMass P.law.observedLaw (fun o : Obs d => o.x) k =
        P.law.cellMass k := by
    simpa [categoryMass, categoryEvent, groupEvent, realMass] using
      (P.law.cellMass_eq k).symm
  simp_rw [hmass]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [polynomialPopulationArmMean_eq_outcomeMean P true k (hH k hk),
    polynomialPopulationArmMean_eq_outcomeMean P false k (hH k hk)]
  ring

-- @node: fixedHeavyMarkedRatio_error_sq_le
/-- If [the truncation threshold satisfies its stated bound](hyp:hB), [for every deterministic
  heavy set whose cells have mass at least `B`, the fixed-heavy marked-ratio score satisfies the
  generic boundary-safe parametric and missing-arm risk bound under the real-outcome model
  assumptions](goal). -/
lemma fixedHeavyMarkedRatio_error_sq_le {d m : ℕ}
    {epsilon M sigma B : ℝ} (P : ModelClass d epsilon M sigma)
    (H : Finset (Fin d)) (hB : ∀ k ∈ H, B ≤ P.law.cellMass k) :
    ∫ z : Fin m → Obs d,
        (fixedStratumMarkedRatio (fun o : Obs d => o.x) (fun o => o.a)
          (fun o => o.y) H z -
        fixedStratumMarkedTarget P.law.observedLaw
          (fun o : Obs d => o.x) (fun o => o.a) (fun o => o.y) H) ^ 2
        ∂(productLaw m P.law) ≤
      4 * M ^ 2 *
        (8 * (∑ k ∈ H, categoryMass P.law.observedLaw
            (fun o : Obs d => o.x) k) /
            (safeSampleSize m * epsilon) +
          6 / safeSampleSize m +
          4 * (lowerMassMissingEnvelope P.law.observedLaw
            (fun o : Obs d => o.x) m epsilon B H) ^ 2) := by
  have htuple : Measurable (fun o : Obs d => (o.x, o.a, o.y)) :=
    measurable_iff_comap_le.mpr le_rfl
  have hx : Measurable (fun o : Obs d => o.x) := measurable_fst.comp htuple
  have ha : Measurable (fun o : Obs d => o.a) :=
    measurable_fst.comp (measurable_snd.comp htuple)
  have hy : Measurable (fun o : Obs d => o.y) :=
    measurable_snd.comp (measurable_snd.comp htuple)
  have hmass (k : Fin d) :
      categoryMass P.law.observedLaw (fun o : Obs d => o.x) k =
        P.law.cellMass k := by
    simpa [categoryMass, categoryEvent, groupEvent, realMass] using
      (P.law.cellMass_eq k).symm
  have hoverlap : ∀ k, 0 < categoryMass P.law.observedLaw
      (fun o : Obs d => o.x) k → ∀ a,
      epsilon * categoryMass P.law.observedLaw (fun o : Obs d => o.x) k ≤
        armCategoryMass P.law.observedLaw (fun o : Obs d => o.x)
          (fun o => o.a) a k := by
    intro k hk a
    rw [hmass] at hk ⊢
    rw [show armCategoryMass P.law.observedLaw (fun o : Obs d => o.x)
        (fun o => o.a) a k = P.law.cellMass k *
          (if a then P.law.propensity k else 1 - P.law.propensity k) by
      change realMass P.law.observedLaw
        (armGroupEvent (fun o : Obs d => o.x) (fun o => o.a) a k) = _
      exact test_arm_mass P.law a k]
    have hov := P.overlap k hk
    cases a <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
      nlinarith [P.law.cellMass_range k]
  rw [show productLaw m P.law =
      Measure.pi (fun _ : Fin m => P.law.observedLaw) from rfl]
  apply integral_fixedStratumMarkedRatio_error_sq_le
    P.law.observedLaw (fun o : Obs d => o.x) (fun o => o.a)
      (fun o => o.y) (polynomialSupportedCenter P.law) H M epsilon B
      hx ha hy
  · exact polynomialSupportedCenter_residual_memLp P
  · exact polynomialSupportedCenter_centered_integral P
  · exact polynomialSupportedCenter_centered_sq_le P
  · exact polynomialSupportedCenter_abs_le P
  · exact P.epsilon_pos
  · exact hoverlap
  · intro k hk
    simpa [hmass] using hB k hk

end CausalSmith.Stat.DiscreteAteHeterogeneityFrontier
