import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.FactorialCovariance

/-! # Paper-local moment bounds for marked factorial coordinates -/

namespace CausalSmith.Stat.DiscreteAteHeterogeneityFrontier

open MeasureTheory ProbabilityTheory

-- @node: observed_normalized_outcome_sq_arm_cell_integral_le
/-- [The squared normalized mark restricted to one arm-cell has mass-weighted second moment at
  most `5/4` times the cell mass](goal). -/
lemma observed_normalized_outcome_sq_arm_cell_integral_le
    {d : ℕ} {epsilon M sigma : ℝ}
    (P : ModelClass d epsilon M sigma) (a : Bool) (k : Fin d) :
    ∫ o : Obs d, {z : Obs d | z.x = k ∧ z.a = a}.indicator
        (fun z => (z.y / M) ^ 2) o ∂P.law.observedLaw ≤
      (5 / 4 : ℝ) * P.law.cellMass k := by
  have htuple : Measurable (fun o : Obs d => (o.x, o.a, o.y)) :=
    measurable_iff_comap_le.mpr le_rfl
  have hy : Measurable (fun o : Obs d => o.y) :=
    measurable_snd.comp (measurable_snd.comp htuple)
  have hxa : MeasurableSet {o : Obs d | o.x = k ∧ o.a = a} := by
    have hx : Measurable (fun o : Obs d => o.x) := measurable_fst.comp htuple
    have ha : Measurable (fun o : Obs d => o.a) :=
      measurable_fst.comp (measurable_snd.comp htuple)
    simpa only [Set.preimage, Set.mem_singleton_iff, Prod.mk.injEq] using
      (measurableSet_singleton (k, a)).preimage (Measurable.prodMk hx ha)
  by_cases hk : P.law.cellMass k = 0
  · have hnull := observed_arm_cell_measure_eq_zero_of_cellMass_eq_zero
      P.law a k hk
    rw [integral_indicator hxa]
    have hr : P.law.observedLaw.restrict {o : Obs d | o.x = k ∧ o.a = a} = 0 :=
      Measure.restrict_eq_zero.mpr hnull
    rw [hr, integral_zero_measure, hk, mul_zero]
  · have hkpos : 0 < P.law.cellMass k :=
      lt_of_le_of_ne (P.law.cellMass_range k).1 (Ne.symm hk)
    have hc := normalized_outcome_second_moment_le_five_fourths P a k hkpos
    have hprop : 0 ≤ if a then P.law.propensity k else 1 - P.law.propensity k := by
      split <;> simp_all [(P.law.propensity_range k).1,
        (P.law.propensity_range k).2]
    have hprop1 : (if a then P.law.propensity k else 1 - P.law.propensity k) ≤ 1 := by
      split <;> simp_all [(P.law.propensity_range k).1,
        (P.law.propensity_range k).2]
    let c := P.law.cellMass k *
      (if a then P.law.propensity k else 1 - P.law.propensity k)
    have hc0 : 0 ≤ c := mul_nonneg (P.law.cellMass_range k).1 hprop
    rw [integral_indicator hxa]
    have hmap := observed_arm_cell_outcome_measure P.law a k
    have hmeasf : AEStronglyMeasurable (fun y : ℝ => (y / M) ^ 2)
        (Measure.map (fun o : Obs d => o.y)
          (P.law.observedLaw.restrict {o : Obs d | o.x = k ∧ o.a = a})) :=
      ((measurable_id.div measurable_const).pow_const 2).aestronglyMeasurable
    rw [← integral_map hy.aemeasurable hmeasf, hmap, integral_smul_measure]
    change ENNReal.toReal (ENNReal.ofReal c) *
      (∫ y, (y / M) ^ 2 ∂P.law.outcomeLaw a k) ≤ _
    rw [ENNReal.toReal_ofReal hc0]
    calc
      c * (∫ y, (y / M) ^ 2 ∂P.law.outcomeLaw a k) ≤ c * (5 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_left hc.2 hc0
      _ ≤ (5 / 4 : ℝ) * P.law.cellMass k := by
        dsimp [c]
        nlinarith [P.law.cellMass_range k |>.1]

-- @node: integral_markedFactorialCoordinate_zero_abs_le
/-- [The unique marked coordinate has mean bounded by one half of its cell mass; this is the
  normalized conditional-mean audit](goal). -/
lemma integral_markedFactorialCoordinate_zero_abs_le
    {d : ℕ} {epsilon M sigma : ℝ}
    (P : ModelClass d epsilon M sigma) (a : Bool) (k : Fin d) (j : ℕ) :
    |∫ o : Obs d, markedFactorialCoordinate M k a j 0 o
        ∂P.law.observedLaw| ≤ (1 / 2 : ℝ) * P.law.cellMass k := by
  have htuple : Measurable (fun o : Obs d => (o.x, o.a, o.y)) :=
    measurable_iff_comap_le.mpr le_rfl
  have hy : Measurable (fun o : Obs d => o.y) :=
    measurable_snd.comp (measurable_snd.comp htuple)
  have hxa : MeasurableSet {o : Obs d | o.x = k ∧ o.a = a} := by
    have hx : Measurable (fun o : Obs d => o.x) := measurable_fst.comp htuple
    have ha : Measurable (fun o : Obs d => o.a) :=
      measurable_fst.comp (measurable_snd.comp htuple)
    simpa only [Set.preimage, Set.mem_singleton_iff, Prod.mk.injEq] using
      (measurableSet_singleton (k, a)).preimage (Measurable.prodMk hx ha)
  have hcoord : (fun o : Obs d => markedFactorialCoordinate M k a j 0 o) =
      {o : Obs d | o.x = k ∧ o.a = a}.indicator (fun o => o.y / M) := by
    funext o
    by_cases ho : o.x = k ∧ o.a = a <;>
      simp [markedFactorialCoordinate, Set.indicator, ho]
  rw [hcoord, integral_indicator hxa]
  by_cases hk : P.law.cellMass k = 0
  · have hnull := observed_arm_cell_measure_eq_zero_of_cellMass_eq_zero
      P.law a k hk
    have hr : P.law.observedLaw.restrict {o : Obs d | o.x = k ∧ o.a = a} = 0 :=
      Measure.restrict_eq_zero.mpr hnull
    rw [hr, integral_zero_measure, abs_zero, hk, mul_zero]
  · have hkpos : 0 < P.law.cellMass k :=
      lt_of_le_of_ne (P.law.cellMass_range k).1 (Ne.symm hk)
    have hc := normalized_outcome_mean_abs_le_half P a k hkpos
    have hprop : 0 ≤ if a then P.law.propensity k else 1 - P.law.propensity k := by
      split <;> simp_all [(P.law.propensity_range k).1,
        (P.law.propensity_range k).2]
    have hprop1 : (if a then P.law.propensity k else 1 - P.law.propensity k) ≤ 1 := by
      split <;> simp_all [(P.law.propensity_range k).1,
        (P.law.propensity_range k).2]
    let c := P.law.cellMass k *
      (if a then P.law.propensity k else 1 - P.law.propensity k)
    have hc0 : 0 ≤ c := mul_nonneg (P.law.cellMass_range k).1 hprop
    have hmap := observed_arm_cell_outcome_measure P.law a k
    have hmeasf : AEStronglyMeasurable (fun y : ℝ => y / M)
        (Measure.map (fun o : Obs d => o.y)
          (P.law.observedLaw.restrict {o : Obs d | o.x = k ∧ o.a = a})) :=
      (measurable_id.div measurable_const).aestronglyMeasurable
    rw [← integral_map hy.aemeasurable hmeasf, hmap, integral_smul_measure]
    change |ENNReal.toReal (ENNReal.ofReal c) *
      (∫ y, y / M ∂P.law.outcomeLaw a k)| ≤ _
    rw [ENNReal.toReal_ofReal hc0, abs_mul, abs_of_nonneg hc0]
    calc
      c * |∫ y, y / M ∂P.law.outcomeLaw a k| ≤ c * (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left hc.2 hc0
      _ ≤ (1 / 2 : ℝ) * P.law.cellMass k := by
        dsimp [c]
        nlinarith [P.law.cellMass_range k |>.1]

-- @node: integral_markedFactorialCoordinate_abs_le_cellMass
/-- [Every coordinate mean is bounded by the cell mass. The marked coordinate uses the preceding
  mean audit; selector-only coordinates are event masses](goal). -/
lemma integral_markedFactorialCoordinate_abs_le_cellMass
    {d : ℕ} {epsilon M sigma : ℝ}
    (P : ModelClass d epsilon M sigma) (a : Bool) (k : Fin d)
    (j : ℕ) (q : Fin (j + 2)) :
    |∫ o : Obs d, markedFactorialCoordinate M k a j q o
        ∂P.law.observedLaw| ≤ P.law.cellMass k := by
  by_cases hq0 : q.val = 0
  · have hq : q = 0 := Fin.ext hq0
    subst q
    exact (integral_markedFactorialCoordinate_zero_abs_le P a k j).trans (by
      have hp := P.law.cellMass_range k |>.1
      nlinarith)
  · have htuple : Measurable (fun o : Obs d => (o.x, o.a, o.y)) :=
      measurable_iff_comap_le.mpr le_rfl
    have hx : Measurable (fun o : Obs d => o.x) := measurable_fst.comp htuple
    have ha : Measurable (fun o : Obs d => o.a) :=
      measurable_fst.comp (measurable_snd.comp htuple)
    have hxset : MeasurableSet {o : Obs d | o.x = k} :=
      (measurableSet_singleton k).preimage hx
    by_cases hq1 : q.val = 1
    · have heq : (fun o : Obs d => markedFactorialCoordinate M k a j q o) =
          {o : Obs d | o.x = k}.indicator (fun _ => (1 : ℝ)) := by
        funext o
        simp [markedFactorialCoordinate, hq1, Set.indicator]
      rw [heq]
      have hi : (∫ o : Obs d, {o : Obs d | o.x = k}.indicator
          (fun _ => (1 : ℝ)) o ∂P.law.observedLaw) =
          (P.law.observedLaw {o : Obs d | o.x = k}).toReal := by
        rw [integral_indicator hxset]
        simp [Measure.real_def]
      rw [hi, abs_of_nonneg ENNReal.toReal_nonneg]
      exact (P.law.cellMass_eq k).ge
    · have hxa : MeasurableSet {o : Obs d | o.x = k ∧ o.a = a} := by
        simpa only [Set.preimage, Set.mem_singleton_iff, Prod.mk.injEq] using
          (measurableSet_singleton (k, a)).preimage (Measurable.prodMk hx ha)
      have heq : (fun o : Obs d => markedFactorialCoordinate M k a j q o) =
          {o : Obs d | o.x = k ∧ o.a = a}.indicator (fun _ => (1 : ℝ)) := by
        funext o
        simp [markedFactorialCoordinate, hq0, hq1, Set.indicator]
      rw [heq]
      have hi : (∫ o : Obs d, {o : Obs d | o.x = k ∧ o.a = a}.indicator
          (fun _ => (1 : ℝ)) o ∂P.law.observedLaw) =
          (P.law.observedLaw {o : Obs d | o.x = k ∧ o.a = a}).toReal := by
        rw [integral_indicator hxa]
        simp [Measure.real_def]
      rw [hi, abs_of_nonneg ENNReal.toReal_nonneg, P.law.cellMass_eq]
      exact ENNReal.toReal_mono (measure_ne_top _ _)
        (measure_mono (by intro o (ho : o.x = k ∧ o.a = a); exact ho.1))

-- @node: integral_markedFactorialCoordinate_sq_le
/-- [Every coordinate has second moment at most `5/4` times its cell mass. The marked coordinate
  uses the outcome envelope, while every other coordinate is an idempotent selector](goal). -/
lemma integral_markedFactorialCoordinate_sq_le
    {d : ℕ} {epsilon M sigma : ℝ}
    (P : ModelClass d epsilon M sigma) (a : Bool) (k : Fin d)
    (j : ℕ) (q : Fin (j + 2)) :
    (∫ o : Obs d, (markedFactorialCoordinate M k a j q o) ^ 2
        ∂P.law.observedLaw) ≤ (5 / 4 : ℝ) * P.law.cellMass k := by
  by_cases hq0 : q.val = 0
  · have hq : q = 0 := Fin.ext hq0
    subst q
    simpa [markedFactorialCoordinate, Set.indicator, mul_pow] using
      observed_normalized_outcome_sq_arm_cell_integral_le P a k
  · have hsq :
        (fun o : Obs d => (markedFactorialCoordinate M k a j q o) ^ 2) =
          markedFactorialCoordinate M k a j q := by
      funext o
      simp only [markedFactorialCoordinate, hq0, if_false]
      split <;> split <;> norm_num
    rw [hsq]
    calc
      (∫ o : Obs d, markedFactorialCoordinate M k a j q o
          ∂P.law.observedLaw) ≤
          |∫ o : Obs d, markedFactorialCoordinate M k a j q o
            ∂P.law.observedLaw| := le_abs_self _
      _ ≤ P.law.cellMass k :=
        integral_markedFactorialCoordinate_abs_le_cellMass P a k j q
      _ ≤ (5 / 4 : ℝ) * P.law.cellMass k := by
        have hp := P.law.cellMass_range k |>.1
        nlinarith

-- @node: integral_markedFactorialCoordinate_mul_abs_le
/-- [When two coordinate factors are assigned to the same observation in a partial matching, their
  product moment is still bounded by `5/4` times the cell mass. This uniformly covers a collision
  of the two real marks](goal). -/
lemma integral_markedFactorialCoordinate_mul_abs_le
    {d : ℕ} {epsilon M sigma : ℝ}
    (P : ModelClass d epsilon M sigma) (k : Fin d) (a b : Bool)
    (j r : ℕ) (q : Fin (j + 2)) (s : Fin (r + 2)) :
    |∫ o : Obs d,
        markedFactorialCoordinate M k a j q o *
          markedFactorialCoordinate M k b r s o
        ∂P.law.observedLaw| ≤ (5 / 4 : ℝ) * P.law.cellMass k := by
  let f : Obs d → ℝ := markedFactorialCoordinate M k a j q
  let g : Obs d → ℝ := markedFactorialCoordinate M k b r s
  have hf2 : MemLp f 2 P.law.observedLaw :=
    memLp_two_markedFactorialCoordinate P k a j q
  have hg2 : MemLp g 2 P.law.observedLaw :=
    memLp_two_markedFactorialCoordinate P k b r s
  have hfg : Integrable (fun o => f o * g o) P.law.observedLaw := by
    exact (hg2.mul' hf2 : MemLp (fun o => f o * g o) 1
      P.law.observedLaw).integrable (by norm_num)
  calc
    |∫ o, f o * g o ∂P.law.observedLaw| ≤
        ∫ o, |f o * g o| ∂P.law.observedLaw :=
      abs_integral_le_integral_abs
    _ ≤ ∫ o, ((f o) ^ 2 + (g o) ^ 2) / 2
        ∂P.law.observedLaw := by
      apply integral_mono_ae hfg.abs
      · exact (hf2.integrable_sq.add hg2.integrable_sq).div_const 2
      · filter_upwards with o
        rw [abs_mul]
        have h := two_mul_le_add_sq (|f o|) (|g o|)
        rw [sq_abs, sq_abs] at h
        linarith
    _ = ((∫ o, (f o) ^ 2 ∂P.law.observedLaw) +
          ∫ o, (g o) ^ 2 ∂P.law.observedLaw) / 2 := by
      rw [integral_div]
      congr 1
      rw [integral_add hf2.integrable_sq hg2.integrable_sq]
    _ ≤ (5 / 4 : ℝ) * P.law.cellMass k := by
      have hf := integral_markedFactorialCoordinate_sq_le P a k j q
      have hg := integral_markedFactorialCoordinate_sq_le P b k r s
      dsimp [f, g] at hf hg ⊢
      linarith

-- @node: mergedMarkedCoordinateFactor
/-- The factors assigned to one merged observation by a partial matching.  Each
fiber contains at most one coordinate from either ordered kernel. -/
noncomputable def mergedMarkedCoordinateFactor
    {d : ℕ} (M : ℝ) (k : Fin d) (a b : Bool) (j r : ℕ)
    (N : Causalean.Stat.PartialMatching (j + 2) (r + 2))
    (t : N.MergedIndex) (o : Obs d) : ℝ :=
  (∏ q ∈ (Finset.univ : Finset (Fin (j + 2))).filter
      (fun q => N.leftInjection q = t),
      markedFactorialCoordinate M k a j q o) *
    ∏ s ∈ (Finset.univ : Finset (Fin (r + 2))).filter
      (fun s => N.rightInjection s = t),
      markedFactorialCoordinate M k b r s o

-- @node: mergedProductKernel_markedFactorialCoordinate_eq_prod_fibers
/-- [The merged marked kernel factors over its genuinely distinct observation indices, grouping
  the possible left/right coordinate collision in one fiber](goal). -/
lemma mergedProductKernel_markedFactorialCoordinate_eq_prod_fibers
    {d : ℕ} (M : ℝ) (k : Fin d) (a b : Bool) (j r : ℕ)
    (N : Causalean.Stat.PartialMatching (j + 2) (r + 2))
    (z : N.MergedIndex → Obs d) :
    Causalean.Stat.mergedProductKernel
        (markedFactorialCoordinate M k a j)
        (markedFactorialCoordinate M k b r) N z =
      ∏ t : N.MergedIndex,
        mergedMarkedCoordinateFactor M k a b j r N t (z t) := by
  classical
  unfold Causalean.Stat.mergedProductKernel mergedMarkedCoordinateFactor
  rw [← Finset.prod_fiberwise (Finset.univ : Finset (Fin (j + 2)))
      N.leftInjection
      (fun q => markedFactorialCoordinate M k a j q (z (N.leftInjection q)))]
  rw [← Finset.prod_fiberwise (Finset.univ : Finset (Fin (r + 2)))
      N.rightInjection
      (fun s => markedFactorialCoordinate M k b r s (z (N.rightInjection s)))]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro t ht
  congr 1
  · apply Finset.prod_congr rfl
    intro q hq
    rw [(Finset.mem_filter.mp hq).2]
  · apply Finset.prod_congr rfl
    intro s hs
    rw [(Finset.mem_filter.mp hs).2]

-- @node: orderedProductMean_markedFactorialCoordinate_abs_le
/-- [Independence across the ordered kernel coordinates bounds its population mean by the
  corresponding power of the cell mass](goal). -/
lemma orderedProductMean_markedFactorialCoordinate_abs_le
    {d : ℕ} {epsilon M sigma : ℝ}
    (P : ModelClass d epsilon M sigma) (a : Bool) (k : Fin d) (j : ℕ) :
    |Causalean.Stat.orderedProductMean P.law.observedLaw
      (markedFactorialCoordinate M k a j)| ≤ P.law.cellMass k ^ (j + 2) := by
  unfold Causalean.Stat.orderedProductMean Causalean.Stat.orderedProductKernel
  rw [MeasureTheory.integral_fintype_prod_eq_prod]
  rw [← Real.norm_eq_abs, norm_prod Finset.univ]
  simp only [Real.norm_eq_abs]
  calc
    (∏ q : Fin (j + 2),
        |∫ x, markedFactorialCoordinate M k a j q x ∂P.law.observedLaw|) ≤
        ∏ _q : Fin (j + 2), P.law.cellMass k := by
      apply Finset.prod_le_prod
      · intro q _
        exact abs_nonneg _
      · intro q _
        exact integral_markedFactorialCoordinate_abs_le_cellMass P a k j q
    _ = P.law.cellMass k ^ (j + 2) := by simp

end CausalSmith.Stat.DiscreteAteHeterogeneityFrontier
