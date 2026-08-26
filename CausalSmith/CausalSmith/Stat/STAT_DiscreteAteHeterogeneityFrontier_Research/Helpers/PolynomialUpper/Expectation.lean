/- Exact expectation identities for the polynomial estimator's marked factorials. -/

import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.FactorialCovariance

namespace CausalSmith.Stat.DiscreteAteHeterogeneityFrontier

open MeasureTheory ProbabilityTheory

-- @node: integral_markedFactorialCoordinate_exact
/-- [The marked coordinate has mean `p_k q_{ak} μ_{ak}/M`, the cell-only coordinate has mean
  `p_k`, and every later arm-cell coordinate has mean `p_k q_{ak}`. This is the exact coordinate
  audit behind the marked-factorial expectation formula](goal). -/
lemma integral_markedFactorialCoordinate_exact
    {d : ℕ} {epsilon M sigma : ℝ}
    (P : ModelClass d epsilon M sigma) (k : Fin d) (a : Bool) (j : ℕ)
    (q : Fin (j + 2)) :
    (∫ o : Obs d, markedFactorialCoordinate M k a j q o
        ∂P.law.observedLaw) =
      if q.val = 0 then
        P.law.cellMass k *
          (if a then P.law.propensity k else 1 - P.law.propensity k) *
          (P.law.outcomeMean a k / M)
      else if q.val = 1 then P.law.cellMass k
      else P.law.cellMass k *
        (if a then P.law.propensity k else 1 - P.law.propensity k) := by
  have htuple : Measurable (fun o : Obs d => (o.x, o.a, o.y)) :=
    measurable_iff_comap_le.mpr le_rfl
  have hx : Measurable (fun o : Obs d => o.x) := measurable_fst.comp htuple
  have ha : Measurable (fun o : Obs d => o.a) :=
    measurable_fst.comp (measurable_snd.comp htuple)
  have hy : Measurable (fun o : Obs d => o.y) :=
    measurable_snd.comp (measurable_snd.comp htuple)
  have hxset : MeasurableSet {o : Obs d | o.x = k} :=
    (measurableSet_singleton k).preimage hx
  have hxa : MeasurableSet {o : Obs d | o.x = k ∧ o.a = a} := by
    simpa only [Set.preimage, Set.mem_singleton_iff, Prod.mk.injEq] using
      (measurableSet_singleton (k, a)).preimage (Measurable.prodMk hx ha)
  let c : ℝ := P.law.cellMass k *
    (if a then P.law.propensity k else 1 - P.law.propensity k)
  have hc0 : 0 ≤ c := by
    dsimp [c]
    apply mul_nonneg (P.law.cellMass_range k).1
    split <;> simp_all [(P.law.propensity_range k).1,
      (P.law.propensity_range k).2]
  by_cases hq0 : q.val = 0
  · rw [if_pos hq0]
    have hq : q = 0 := Fin.ext hq0
    subst q
    simp only [markedFactorialCoordinate, Fin.val_zero, ↓reduceIte]
    have hmark :
        (fun o : Obs d => o.y / M * if o.x = k ∧ o.a = a then 1 else 0) =
          {o : Obs d | o.x = k ∧ o.a = a}.indicator (fun o => o.y / M) := by
      funext o
      by_cases ho : o.x = k ∧ o.a = a <;> simp [Set.indicator, ho]
    rw [hmark]
    by_cases hk : P.law.cellMass k = 0
    · have hnull := observed_arm_cell_measure_eq_zero_of_cellMass_eq_zero
        P.law a k hk
      rw [integral_indicator hxa]
      have hr : P.law.observedLaw.restrict {o : Obs d | o.x = k ∧ o.a = a} = 0 :=
        Measure.restrict_eq_zero.mpr hnull
      simp [hr, hk]
    · have hkpos : 0 < P.law.cellMass k :=
        lt_of_le_of_ne (P.law.cellMass_range k).1 (Ne.symm hk)
      have hint := (normalized_outcome_mean_abs_le_half P a k hkpos).1
      rw [integral_indicator hxa]
      have hmap := observed_arm_cell_outcome_measure P.law a k
      have hmeas : AEStronglyMeasurable (fun y : ℝ => y / M)
          (Measure.map (fun o : Obs d => o.y)
            (P.law.observedLaw.restrict {o : Obs d | o.x = k ∧ o.a = a})) :=
        (measurable_id.div measurable_const).aestronglyMeasurable
      rw [← integral_map hy.aemeasurable hmeas, hmap, integral_smul_measure]
      change ENNReal.toReal (ENNReal.ofReal c) *
          (∫ y, y / M ∂P.law.outcomeLaw a k) = _
      rw [ENNReal.toReal_ofReal hc0, integral_div, ← P.law.outcomeMean_eq]
  · rw [if_neg hq0]
    by_cases hq1 : q.val = 1
    · rw [if_pos hq1]
      have heq : (fun o : Obs d => markedFactorialCoordinate M k a j q o) =
          {o : Obs d | o.x = k}.indicator (fun _ => (1 : ℝ)) := by
        funext o
        simp [markedFactorialCoordinate, hq1, Set.indicator]
      rw [heq, integral_indicator hxset]
      rw [show (∫ _x : Obs d in {o : Obs d | o.x = k}, (1 : ℝ)
          ∂P.law.observedLaw) = realMass P.law.observedLaw {o | o.x = k} by
        simp [realMass, Measure.real_def]]
      exact (P.law.cellMass_eq k).symm
    · rw [if_neg hq1]
      have heq : (fun o : Obs d => markedFactorialCoordinate M k a j q o) =
          {o : Obs d | o.x = k ∧ o.a = a}.indicator (fun _ => (1 : ℝ)) := by
        funext o
        simp [markedFactorialCoordinate, hq0, hq1, Set.indicator]
      rw [heq, integral_indicator hxa]
      have hmass := P.law.arm_outcome_factorization a k Set.univ MeasurableSet.univ
      let _ : IsProbabilityMeasure (P.law.outcomeLaw a k) :=
        P.law.outcome_isProbability a k
      simp [realMass] at hmass
      simpa [Measure.real_def, realMass] using hmass.symm

-- @node: orderedProductMean_markedFactorialCoordinate_exact
/-- [Independence across the ordered coordinates gives exactly one normalized outcome mark, one
  cell selector, and `j` additional arm-cell selectors](goal). -/
lemma orderedProductMean_markedFactorialCoordinate_exact
    {d : ℕ} {epsilon M sigma : ℝ}
    (P : ModelClass d epsilon M sigma) (k : Fin d) (a : Bool) (j : ℕ) :
    Causalean.Stat.orderedProductMean P.law.observedLaw
        (markedFactorialCoordinate M k a j) =
      (P.law.cellMass k *
          (if a then P.law.propensity k else 1 - P.law.propensity k) *
          (P.law.outcomeMean a k / M)) *
        P.law.cellMass k *
        (P.law.cellMass k *
          (if a then P.law.propensity k else 1 - P.law.propensity k)) ^ j := by
  classical
  unfold Causalean.Stat.orderedProductMean Causalean.Stat.orderedProductKernel
  rw [MeasureTheory.integral_fintype_prod_eq_prod]
  simp_rw [integral_markedFactorialCoordinate_exact P k a j]
  rw [Fin.prod_univ_succ]
  simp only [Fin.val_zero, ↓reduceIte]
  rw [Fin.prod_univ_succ]
  cases a <;> simp <;> ring

-- @node: allBlockOrderedMarkedFactorial_expectation_eq_orderedProductMean
/-- If [the factorial order fits in the estimation block](hyp:hjm), [an all-block marked factorial
  is exactly unbiased for its coordinatewise product-law moment whenever its order fits in the
  estimation block](goal). -/
lemma allBlockOrderedMarkedFactorial_expectation_eq_orderedProductMean
    {d m : ℕ} {epsilon M sigma : ℝ}
    (P : ModelClass d epsilon M sigma) (k : Fin d) (a : Bool) (j : ℕ)
    (hjm : j + 2 ≤ m) :
    ∫ ω : ℕ → Obs d,
        allBlockOrderedMarkedFactorial M (fun i : Fin m ↦ ω i) k a j
          ∂(Measure.infinitePi fun _ : ℕ ↦ P.law.observedLaw) =
      Causalean.Stat.orderedProductMean P.law.observedLaw
        (markedFactorialCoordinate M k a j) := by
  let S0 := Causalean.Stat.iidSample_infinitePi P.law.observedLaw
  have hstat :
      (fun ω : ℕ → Obs d ↦
        allBlockOrderedMarkedFactorial M (fun i : Fin m ↦ ω i) k a j) =
        Causalean.Stat.normalizedOrderedProductStatistic S0
          (markedFactorialCoordinate M k a j) m := by
    funext ω
    exact allBlockOrderedMarkedFactorial_eq_normalizedOrderedProductStatistic
      (m := m) S0 M k a j ω
  rw [hstat]
  unfold Causalean.Stat.normalizedOrderedProductStatistic
    Causalean.Stat.orderedProductMean
  have hcard : Fintype.card (Fin (j + 2)) ≤ m := by simpa using hjm
  exact Causalean.Stat.integral_normalizedFiniteKernelStatistic S0 hcard
    (measurable_orderedProductKernel_markedFactorialCoordinate M k a j)
    (integrable_orderedProductKernel_markedFactorialCoordinate P k a j)

-- @node: integral_allBlockOrderedMarkedFactorial_eq_orderedProductMean
/-- If [the factorial order fits in the estimation block](hyp:hjm), [the same exact
  marked-factorial expectation identity holds directly under the finite product experiment used by
  the estimator](goal). -/
lemma integral_allBlockOrderedMarkedFactorial_eq_orderedProductMean
    {d m : ℕ} {epsilon M sigma : ℝ}
    (P : ModelClass d epsilon M sigma) (k : Fin d) (a : Bool) (j : ℕ)
    (hjm : j + 2 ≤ m) :
    ∫ s : Fin m → Obs d, allBlockOrderedMarkedFactorial M s k a j
        ∂(productLaw m P.law) =
      Causalean.Stat.orderedProductMean P.law.observedLaw
        (markedFactorialCoordinate M k a j) := by
  let S0 := Causalean.Stat.iidSample_infinitePi P.law.observedLaw
  have hpush := Causalean.Stat.iidSample_finN_pushforward S0 m
  have hprefix : Measurable (fun ω : ℕ → Obs d ↦ fun i : Fin m ↦ ω i) :=
    Causalean.Stat.iidSample_finN_measurable S0 m
  dsimp [S0, Causalean.Stat.iidSample_infinitePi] at hpush hprefix
  unfold productLaw
  rw [← hpush, integral_map hprefix.aemeasurable
    (measurable_allBlockOrderedMarkedFactorial M k a j).aestronglyMeasurable]
  exact allBlockOrderedMarkedFactorial_expectation_eq_orderedProductMean
    P k a j hjm

-- @node: integral_allBlockOrderedMarkedFactorial_exact
/-- If [the factorial order fits in the estimation block](hyp:hjm), [the all-block statistic has
  the paper's exact marked-factorial expectation: one normalized marked arm-cell moment, one cell
  mass, and `j` further arm-cell masses](goal). -/
lemma integral_allBlockOrderedMarkedFactorial_exact
    {d m : ℕ} {epsilon M sigma : ℝ}
    (P : ModelClass d epsilon M sigma) (k : Fin d) (a : Bool) (j : ℕ)
    (hjm : j + 2 ≤ m) :
    (∫ s : Fin m → Obs d, allBlockOrderedMarkedFactorial M s k a j
        ∂productLaw m P.law) =
      (P.law.cellMass k *
          (if a then P.law.propensity k else 1 - P.law.propensity k) *
          (P.law.outcomeMean a k / M)) *
        P.law.cellMass k *
        (P.law.cellMass k *
          (if a then P.law.propensity k else 1 - P.law.propensity k)) ^ j := by
  rw [integral_allBlockOrderedMarkedFactorial_eq_orderedProductMean P k a j hjm]
  exact orderedProductMean_markedFactorialCoordinate_exact P k a j

end CausalSmith.Stat.DiscreteAteHeterogeneityFrontier
