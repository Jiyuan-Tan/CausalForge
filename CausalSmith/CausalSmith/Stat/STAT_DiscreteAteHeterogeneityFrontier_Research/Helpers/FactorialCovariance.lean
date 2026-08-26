/- Covariance bound for signed one-mark falling-factorial statistics. -/

import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.Estimators
import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.FactorialCovarianceCoefficients
import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.FactorialMoments
import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.ShiftedChebyshev
import Causalean.Stat.UStatistic.OrderM.MixedOrderBounds
import Mathlib.Data.Nat.Choose.Bounds

namespace CausalSmith.Stat.DiscreteAteHeterogeneityFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- The paper's unsplit all-block statistic: all `m` observations participate,
and normalization is by `(m)_{j+2}` rather than the estimation-half factorial. -/
noncomputable def allBlockOrderedMarkedFactorial {m d : ℕ} (M : ℝ)
    (sample : Fin m → Obs d) (k : Fin d) (a : Bool) (j : ℕ) : ℝ :=
  (∑ idx : Fin (j + 2) → Fin m,
    if Function.Injective idx then
      ((sample (idx 0)).y / M) *
        (if (sample (idx 0)).x = k ∧ (sample (idx 0)).a = a then 1 else 0) *
        (if (sample (idx 1)).x = k then 1 else 0) *
        (∏ q : Fin (j + 2),
          if 2 ≤ q.val then
            if (sample (idx q)).x = k ∧ (sample (idx q)).a = a then 1 else 0
          else 1)
    else 0) / m.descFactorial (j + 2)

/-- One all-block light-cell polynomial contribution. -/
noncomputable def allBlockLightPolynomialTerm {m d : ℕ} (M B : ℝ) (K : ℕ)
    (sample : Fin m → Obs d) (k : Fin d) : ℝ :=
  ∑ j ∈ Finset.range (K - 1),
    shiftedCoefficient K j / B ^ (j + 1) *
      (allBlockOrderedMarkedFactorial M sample k true j -
        allBlockOrderedMarkedFactorial M sample k false j)

/-- Sum of the unsplit all-block statistics over deterministic light cells. -/
noncomputable def allBlockMarkedPolynomialSum {m d : ℕ} (M B : ℝ) (K : ℕ)
    (S : Finset (Fin d)) (sample : Fin m → Obs d) : ℝ :=
  ∑ k ∈ S, allBlockLightPolynomialTerm M B K sample k

-- @node: markedFactorialCoordinate
/-- Coordinate factors whose ordered product is one all-block marked factorial
kernel: the zeroth coordinate carries the outcome mark, the first only selects
the cell, and all later coordinates select the arm and cell. -/
noncomputable def markedFactorialCoordinate {d : ℕ} (M : ℝ) (k : Fin d)
    (a : Bool) (j : ℕ) (q : Fin (j + 2)) (o : Obs d) : ℝ :=
  if q.val = 0 then
    (o.y / M) * (if o.x = k ∧ o.a = a then 1 else 0)
  else if q.val = 1 then
    if o.x = k then 1 else 0
  else if o.x = k ∧ o.a = a then 1 else 0

-- @node: prod_markedFactorialCoordinate
/-- [Multiplying the coordinate factors recovers the paper's displayed marked kernel, including
  its redundant later-coordinate product](goal). -/
lemma prod_markedFactorialCoordinate {d : ℕ} (M : ℝ) (k : Fin d)
    (a : Bool) (j : ℕ) (z : Fin (j + 2) → Obs d) :
    (∏ q, markedFactorialCoordinate M k a j q (z q)) =
      ((z 0).y / M) * (if (z 0).x = k ∧ (z 0).a = a then 1 else 0) *
        (if (z 1).x = k then 1 else 0) *
        (∏ q : Fin (j + 2),
          if 2 ≤ q.val then
            if (z q).x = k ∧ (z q).a = a then 1 else 0
          else 1) := by
  classical
  simp [markedFactorialCoordinate, Fin.prod_univ_succ]
  by_cases h0 : (z 0).x = k ∧ (z 0).a = a <;>
    by_cases h1 : (z 1).x = k <;> simp [h0, h1]

-- @node: measurable_markedFactorialCoordinate
/-- [Every coordinate of the marked factorial kernel is measurable. This is the regularity input
  needed by the generic mixed-order covariance expansion](goal). -/
lemma measurable_markedFactorialCoordinate {d : ℕ} (M : ℝ) (k : Fin d)
    (a : Bool) (j : ℕ) (q : Fin (j + 2)) :
    Measurable (markedFactorialCoordinate M k a j q) := by
  have htuple : Measurable (fun o : Obs d => (o.x, o.a, o.y)) :=
    measurable_iff_comap_le.mpr le_rfl
  have hx : Measurable (fun o : Obs d => o.x) := measurable_fst.comp htuple
  have ha : Measurable (fun o : Obs d => o.a) :=
    measurable_fst.comp (measurable_snd.comp htuple)
  have hy : Measurable (fun o : Obs d => o.y) :=
    measurable_snd.comp (measurable_snd.comp htuple)
  unfold markedFactorialCoordinate
  split
  · apply Measurable.mul (hy.div measurable_const)
    apply Measurable.ite
    · simpa only [Set.preimage, Set.mem_singleton_iff, Prod.mk.injEq] using
        ((measurableSet_singleton (k, a)).preimage (Measurable.prodMk hx ha))
    · exact measurable_const
    · exact measurable_const
  · split
    · apply Measurable.ite
      · exact (measurableSet_singleton k).preimage hx
      · exact measurable_const
      · exact measurable_const
    · apply Measurable.ite
      · simpa only [Set.preimage, Set.mem_singleton_iff, Prod.mk.injEq] using
          ((measurableSet_singleton (k, a)).preimage (Measurable.prodMk hx ha))
      · exact measurable_const
      · exact measurable_const

-- @node: measurable_orderedProductKernel_markedFactorialCoordinate
/-- [The full coordinate product defining one marked factorial kernel is measurable under the
  finite product measurable space](goal). -/
lemma measurable_orderedProductKernel_markedFactorialCoordinate {d : ℕ}
    (M : ℝ) (k : Fin d) (a : Bool) (j : ℕ) :
    Measurable (Causalean.Stat.orderedProductKernel
      (markedFactorialCoordinate M k a j)) := by
  unfold Causalean.Stat.orderedProductKernel
  apply Finset.measurable_prod
  intro q _
  exact (measurable_markedFactorialCoordinate M k a j q).comp
    (measurable_pi_apply q)

-- @node: measurable_mergedProductKernel_markedFactorialCoordinate
/-- [Every partial-matching merge of two marked factorial kernels is measurable, including the
  possible collision of their two real-valued marks](goal). -/
lemma measurable_mergedProductKernel_markedFactorialCoordinate {d : ℕ}
    (M : ℝ) (k l : Fin d) (a b : Bool) (j r : ℕ)
    (N : Causalean.Stat.PartialMatching (j + 2) (r + 2)) :
    Measurable (Causalean.Stat.mergedProductKernel
      (markedFactorialCoordinate M k a j)
      (markedFactorialCoordinate M l b r) N) := by
  unfold Causalean.Stat.mergedProductKernel
  apply Measurable.mul
  · apply Finset.measurable_prod
    intro q _
    exact (measurable_markedFactorialCoordinate M k a j q).comp
      (measurable_pi_apply (N.leftInjection q))
  · apply Finset.measurable_prod
    intro q _
    exact (measurable_markedFactorialCoordinate M l b r q).comp
      (measurable_pi_apply (N.rightInjection q))

-- @node: markedFactorialCoordinate_eq_zero_of_cell_ne
/-- If [the observation belongs to a different cell](hyp:ho), [every coordinate factor vanishes
  away from its designated cell](goal). -/
lemma markedFactorialCoordinate_eq_zero_of_cell_ne {d : ℕ} (M : ℝ)
    (k : Fin d) (a : Bool) (j : ℕ) (q : Fin (j + 2)) (o : Obs d)
    (ho : o.x ≠ k) : markedFactorialCoordinate M k a j q o = 0 := by
  simp [markedFactorialCoordinate, ho]

-- @node: mergedProductKernel_markedFactorialCoordinate_eq_zero_of_cell_ne
/-- If [the sampling budget satisfies the stated lower bound](hyp:hN) and [the two cells are
  distinct](hyp:hkl), [a positive-size matching between statistics from different cells has zero
  merged kernel: a matched observation cannot satisfy both cell selectors](goal). -/
lemma mergedProductKernel_markedFactorialCoordinate_eq_zero_of_cell_ne
    {d : ℕ} (M : ℝ) (k l : Fin d) (a b : Bool) (j r : ℕ)
    (N : Causalean.Stat.PartialMatching (j + 2) (r + 2))
    (hN : 0 < N.size) (hkl : k ≠ l)
    (z : N.MergedIndex → Obs d) :
    Causalean.Stat.mergedProductKernel
      (markedFactorialCoordinate M k a j)
      (markedFactorialCoordinate M l b r) N z = 0 := by
  classical
  obtain ⟨i, hi⟩ := Finset.card_pos.mp
    (by simpa [Causalean.Stat.PartialMatching.size] using hN)
  let j' : Fin (r + 2) := (N.equiv ⟨i, hi⟩).1
  have hj' : j' ∈ N.right := (N.equiv ⟨i, hi⟩).2
  have hinj : N.rightInjection j' = N.leftInjection i := by
    simp only [Causalean.Stat.PartialMatching.rightInjection, hj', dite_true,
      Causalean.Stat.PartialMatching.leftInjection]
    congr
    simpa [j'] using N.equiv.symm_apply_apply ⟨i, hi⟩
  unfold Causalean.Stat.mergedProductKernel
  by_cases hx : (z (N.leftInjection i)).x = k
  · have hxl : (z (N.rightInjection j')).x ≠ l := by
      rw [hinj]
      exact fun h => hkl (hx.symm.trans h)
    rw [Finset.prod_eq_zero (Finset.mem_univ j')
      (markedFactorialCoordinate_eq_zero_of_cell_ne M l b r j'
        (z (N.rightInjection j')) hxl), mul_zero]
  · rw [Finset.prod_eq_zero (Finset.mem_univ i)
      (markedFactorialCoordinate_eq_zero_of_cell_ne M k a j i
        (z (N.leftInjection i)) hx), zero_mul]

-- @node: mergedProductMoment_markedFactorialCoordinate_eq_zero_of_cell_ne
/-- If [the sampling budget satisfies the stated lower bound](hyp:hN) and [the two cells are
  distinct](hyp:hkl), [consequently every positive-overlap merged moment from two different cells
  is exactly zero](goal). -/
lemma mergedProductMoment_markedFactorialCoordinate_eq_zero_of_cell_ne
    {d : ℕ} (P0 : Measure (Obs d)) (M : ℝ) (k l : Fin d)
    (a b : Bool) (j r : ℕ)
    (N : Causalean.Stat.PartialMatching (j + 2) (r + 2))
    (hN : 0 < N.size) (hkl : k ≠ l) :
    Causalean.Stat.mergedProductMoment P0
      (markedFactorialCoordinate M k a j)
      (markedFactorialCoordinate M l b r) N = 0 := by
  unfold Causalean.Stat.mergedProductMoment
  apply integral_eq_zero_of_ae
  filter_upwards with z
  exact mergedProductKernel_markedFactorialCoordinate_eq_zero_of_cell_ne
    M k l a b j r N hN hkl z

-- @node: allBlockOrderedMarkedFactorial_eq_normalizedOrderedProductStatistic
/-- [The paper's all-block marked factorial statistic is exactly the generic normalized
  ordered-product statistic evaluated on the finite sample prefix](goal). -/
lemma allBlockOrderedMarkedFactorial_eq_normalizedOrderedProductStatistic
    {Ω : Type*} [MeasurableSpace Ω] {m d : ℕ} {μ : Measure Ω}
    {P0 : Measure (Obs d)} (S0 : Causalean.Stat.IIDSample Ω (Obs d) μ P0)
    (M : ℝ) (k : Fin d) (a : Bool) (j : ℕ) (ω : Ω) :
    allBlockOrderedMarkedFactorial M (fun i : Fin m => S0.Z i ω) k a j =
      Causalean.Stat.normalizedOrderedProductStatistic S0
        (markedFactorialCoordinate M k a j) m ω := by
  classical
  unfold allBlockOrderedMarkedFactorial
    Causalean.Stat.normalizedOrderedProductStatistic
    Causalean.Stat.normalizedFiniteKernelStatistic
    Causalean.Stat.orderedProductKernel
    Causalean.Stat.finiteInjectiveTuples
  simp only [Fintype.card_fin]
  rw [div_eq_mul_inv, mul_comm]
  congr 1
  rw [Finset.sum_filter]
  simp_rw [prod_markedFactorialCoordinate]
  congr 1
  ext
  simp

-- @node: observed_arm_cell_measure_eq_zero_of_cellMass_eq_zero
/-- If [the stated condition on the cell holds](hyp:hk), [a zero-mass cell makes each of its
  observed arm-cell events null. This discharges the unsupported-cell branch of the marked moment
  audit without requesting conditional moments where the model deliberately supplies none](goal). -/
lemma observed_arm_cell_measure_eq_zero_of_cellMass_eq_zero {d : ℕ}
    (P : RealLaw d) (a : Bool) (k : Fin d) (hk : P.cellMass k = 0) :
    P.observedLaw {o : Obs d | o.x = k ∧ o.a = a} = 0 := by
  have hfactor := P.arm_outcome_factorization a k Set.univ MeasurableSet.univ
  let _ : IsProbabilityMeasure (P.outcomeLaw a k) := P.outcome_isProbability a k
  have hout : realMass (P.outcomeLaw a k) Set.univ = 1 := by
    simp [realMass]
  rw [hout, mul_one, hk, zero_mul] at hfactor
  have hreal : realMass P.observedLaw {o : Obs d | o.x = k ∧ o.a = a} = 0 := by
    simpa using hfactor.symm
  rw [realMass, ENNReal.toReal_eq_zero_iff] at hreal
  exact hreal.resolve_right (measure_ne_top _ _)

-- @node: observed_arm_cell_outcome_measure
/-- [Restricting the observed law to one arm and cell and then projecting the outcome gives its
  conditional outcome law scaled by the arm-cell mass](goal). -/
lemma observed_arm_cell_outcome_measure {d : ℕ}
    (P : RealLaw d) (a : Bool) (k : Fin d) :
    Measure.map (fun o : Obs d => o.y)
        (P.observedLaw.restrict {o : Obs d | o.x = k ∧ o.a = a}) =
      ENNReal.ofReal
          (P.cellMass k * (if a then P.propensity k else 1 - P.propensity k)) •
        P.outcomeLaw a k := by
  let _ : IsProbabilityMeasure (P.outcomeLaw a k) := P.outcome_isProbability a k
  have hc : 0 ≤ P.cellMass k *
      (if a then P.propensity k else 1 - P.propensity k) :=
    mul_nonneg (P.cellMass_range k).1 (by
      split <;> simp_all [(P.propensity_range k).1, (P.propensity_range k).2])
  apply Measure.ext
  intro s hs
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
  rw [Measure.map_apply hy hs, Measure.restrict_apply (hy hs)]
  simp only [Measure.smul_apply, Set.preimage]
  have hfac := P.arm_outcome_factorization a k s hs
  apply (ENNReal.toReal_eq_toReal_iff'
    (measure_ne_top _ _)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))).mp
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc]
  simpa [realMass, Set.inter_def, and_assoc, and_left_comm, and_comm] using hfac.symm

-- @node: outcome_second_moment_le_five_fourths
/-- If [the stated condition on the cell holds](hyp:hk), [on every positive-mass arm and cell, the
  central-moment and mean envelopes imply integrability of the raw squared outcome and the bound
  `E[Y²] ≤ 5M²/4`. This is the paper's moment audit before normalizing the unique real
  mark](goal). -/
lemma outcome_second_moment_le_five_fourths {d : ℕ} {epsilon M sigma : ℝ}
    (P : ModelClass d epsilon M sigma) (a : Bool) (k : Fin d)
    (hk : 0 < P.law.cellMass k) :
    Integrable (fun y : ℝ => y ^ 2) (P.law.outcomeLaw a k) ∧
      ∫ y, y ^ 2 ∂P.law.outcomeLaw a k ≤ (5 / 4 : ℝ) * M ^ 2 := by
  let _ : IsProbabilityMeasure (P.law.outcomeLaw a k) :=
    P.law.outcome_isProbability a k
  have hc := (P.second_moment a k hk).1
  have hcL2 : MemLp (fun y : ℝ => y - P.law.outcomeMean a k) 2
      (P.law.outcomeLaw a k) :=
    (memLp_two_iff_integrable_sq (by fun_prop)).2 hc
  have hyL2 : MemLp (fun y : ℝ => y) 2 (P.law.outcomeLaw a k) := by
    convert hcL2.add (memLp_const (P.law.outcomeMean a k)) using 1
    ext y
    simp
  have hy2 := hyL2.integrable_sq
  refine ⟨hy2, ?_⟩
  have hmean : |P.law.outcomeMean a k| ≤ M / 2 :=
    P.mean_normalization a k hk
  have hmean_sq : P.law.outcomeMean a k ^ 2 ≤ M ^ 2 / 4 := by
    have hM : 0 ≤ M / 2 := by nlinarith [P.M_ge_one]
    calc
      P.law.outcomeMean a k ^ 2 = |P.law.outcomeMean a k| ^ 2 := by
        rw [sq_abs]
      _ ≤ (M / 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hmean 2
      _ = M ^ 2 / 4 := by ring
  have hcenter := (P.second_moment a k hk).2
  have hcenter_eq :
      (∫ y, (y - P.law.outcomeMean a k) ^ 2 ∂P.law.outcomeLaw a k) =
        (∫ y, y ^ 2 ∂P.law.outcomeLaw a k) - P.law.outcomeMean a k ^ 2 := by
    have hy : Integrable (fun y : ℝ => y) (P.law.outcomeLaw a k) :=
      hyL2.integrable (by norm_num)
    have hlin : Integrable (fun y : ℝ =>
        (2 * P.law.outcomeMean a k) * y) (P.law.outcomeLaw a k) :=
      hy.const_mul _
    calc
      (∫ y, (y - P.law.outcomeMean a k) ^ 2 ∂P.law.outcomeLaw a k) =
          ∫ y, (y ^ 2 - (2 * P.law.outcomeMean a k) * y) +
            P.law.outcomeMean a k ^ 2 ∂P.law.outcomeLaw a k := by
              congr 1
              funext y
              ring
      _ = (∫ y, y ^ 2 - (2 * P.law.outcomeMean a k) * y
            ∂P.law.outcomeLaw a k) + P.law.outcomeMean a k ^ 2 := by
              simpa [integral_const, probReal_univ] using
                (integral_add (hy2.sub hlin)
                  (integrable_const (P.law.outcomeMean a k ^ 2)))
      _ = ((∫ y, y ^ 2 ∂P.law.outcomeLaw a k) -
            (2 * P.law.outcomeMean a k) *
              (∫ y, y ∂P.law.outcomeLaw a k)) +
            P.law.outcomeMean a k ^ 2 := by
              rw [integral_sub hy2 hlin, integral_const_mul]
      _ = (∫ y, y ^ 2 ∂P.law.outcomeLaw a k) -
            P.law.outcomeMean a k ^ 2 := by
              rw [← P.law.outcomeMean_eq]
              ring
  rw [hcenter_eq] at hcenter
  nlinarith

-- @node: normalized_outcome_second_moment_le_five_fourths
/-- If [the stated condition on the cell holds](hyp:hk), [dividing by the model scale turns the
  raw outcome-moment audit into the dimensionless bound `E[(Y/M)²] ≤ 5/4` used for a collision of
  two marks](goal). -/
lemma normalized_outcome_second_moment_le_five_fourths
    {d : ℕ} {epsilon M sigma : ℝ}
    (P : ModelClass d epsilon M sigma) (a : Bool) (k : Fin d)
    (hk : 0 < P.law.cellMass k) :
    Integrable (fun y : ℝ => (y / M) ^ 2) (P.law.outcomeLaw a k) ∧
      ∫ y, (y / M) ^ 2 ∂P.law.outcomeLaw a k ≤ (5 / 4 : ℝ) := by
  have h := outcome_second_moment_le_five_fourths P a k hk
  have hM : 0 < M := lt_of_lt_of_le (by norm_num) P.M_ge_one
  have hM2 : 0 < M ^ 2 := sq_pos_of_pos hM
  have heq : (fun y : ℝ => (y / M) ^ 2) = fun y => y ^ 2 / M ^ 2 := by
    funext y
    ring
  rw [heq]
  refine ⟨h.1.div_const _, ?_⟩
  have heq' : (fun y : ℝ => y ^ 2 / M ^ 2) =
      fun y => (M ^ 2)⁻¹ * y ^ 2 := by
    funext y
    rw [inv_mul_eq_div]
  rw [heq', integral_const_mul, inv_mul_eq_div]
  apply (div_le_iff₀ hM2).2
  nlinarith [h.2]

-- @node: integrable_observed_normalized_outcome_sq
/-- [The normalized squared outcome is integrable under the full observed law. This packages the
  finite arm-cell partition needed whenever two marked coordinates collide in a partial
  matching](goal). -/
lemma integrable_observed_normalized_outcome_sq
    {d : ℕ} {epsilon M sigma : ℝ}
    (P : ModelClass d epsilon M sigma) :
    Integrable (fun o : Obs d => (o.y / M) ^ 2) P.law.observedLaw := by
  have htuple : Measurable (fun o : Obs d => (o.x, o.a, o.y)) :=
    measurable_iff_comap_le.mpr le_rfl
  have hy : Measurable (fun o : Obs d => o.y) :=
    measurable_snd.comp (measurable_snd.comp htuple)
  have hcell : ∀ k : Fin d, ∀ a : Bool,
      Integrable
        ({o : Obs d | o.x = k ∧ o.a = a}.indicator
          (fun o => (o.y / M) ^ 2)) P.law.observedLaw := by
    intro k a
    have hxa : MeasurableSet {o : Obs d | o.x = k ∧ o.a = a} := by
      have hx : Measurable (fun o : Obs d => o.x) := measurable_fst.comp htuple
      have ha : Measurable (fun o : Obs d => o.a) :=
        measurable_fst.comp (measurable_snd.comp htuple)
      simpa only [Set.preimage, Set.mem_singleton_iff, Prod.mk.injEq] using
        (measurableSet_singleton (k, a)).preimage (Measurable.prodMk hx ha)
    by_cases hk : P.law.cellMass k = 0
    · have hnull := observed_arm_cell_measure_eq_zero_of_cellMass_eq_zero
        P.law a k hk
      have hzero : Integrable (fun _ : Obs d => (0 : ℝ)) P.law.observedLaw :=
        integrable_const 0
      refine hzero.congr (ae_iff.mpr ?_)
      apply measure_mono_null _ hnull
      intro o ho
      by_contra hout
      change ¬(o.x = k ∧ o.a = a) at hout
      have hz : {z : Obs d | z.x = k ∧ z.a = a}.indicator
          (fun z => (z.y / M) ^ 2) o = 0 := by
        simp [Set.indicator, hout]
      exact ho hz.symm
    · have hkpos : 0 < P.law.cellMass k :=
        lt_of_le_of_ne (P.law.cellMass_range k).1 (Ne.symm hk)
      have hc := (normalized_outcome_second_moment_le_five_fourths P a k hkpos).1
      have hc' := hc.smul_measure (c := ENNReal.ofReal
        (P.law.cellMass k *
          (if a then P.law.propensity k else 1 - P.law.propensity k)))
        ENNReal.ofReal_ne_top
      rw [← observed_arm_cell_outcome_measure P.law a k] at hc'
      have hrestrict : Integrable (fun o : Obs d => (o.y / M) ^ 2)
          (P.law.observedLaw.restrict {o | o.x = k ∧ o.a = a}) :=
        (MeasureTheory.integrable_map_measure
          (((measurable_id.div measurable_const).pow_const 2).aestronglyMeasurable)
          hy.aemeasurable).mp hc'
      exact (integrable_indicator_iff hxa).2 hrestrict
  have hsum : Integrable
      (fun o : Obs d => ∑ k : Fin d, ∑ a : Bool,
        {z : Obs d | z.x = k ∧ z.a = a}.indicator
          (fun z => (z.y / M) ^ 2) o) P.law.observedLaw :=
    integrable_finset_sum Finset.univ fun k _ =>
      integrable_finset_sum Finset.univ fun a _ => hcell k a
  convert hsum using 1
  funext o
  rw [Finset.sum_eq_single o.x]
  · cases o.a <;> simp [Set.indicator]
  · intro k _ hk
    have hx : ¬o.x = k := fun h => hk h.symm
    simp [Set.indicator, hx]
  · simp

-- @node: memLp_two_observed_normalized_outcome
/-- [The normalized observed outcome itself is square-integrable](goal). -/
lemma memLp_two_observed_normalized_outcome
    {d : ℕ} {epsilon M sigma : ℝ}
    (P : ModelClass d epsilon M sigma) :
    MemLp (fun o : Obs d => o.y / M) 2 P.law.observedLaw := by
  have htuple : Measurable (fun o : Obs d => (o.x, o.a, o.y)) :=
    measurable_iff_comap_le.mpr le_rfl
  have hy : Measurable (fun o : Obs d => o.y) :=
    measurable_snd.comp (measurable_snd.comp htuple)
  exact (memLp_two_iff_integrable_sq
    (hy.div measurable_const).aestronglyMeasurable).2
    (integrable_observed_normalized_outcome_sq P)

-- @node: markedFactorialCoordinate_norm_le_mark
/-- [Selector coordinates have norm at most one, while the unique marked coordinate has norm at
  most the normalized outcome magnitude](goal). -/
lemma markedFactorialCoordinate_norm_le_mark {d : ℕ} (M : ℝ)
    (k : Fin d) (a : Bool) (j : ℕ) (q : Fin (j + 2)) (o : Obs d) :
    ‖markedFactorialCoordinate M k a j q o‖ ≤
      if q.val = 0 then |o.y / M| else 1 := by
  by_cases hq : q.val = 0
  · by_cases ho : o.x = k ∧ o.a = a
    · simp only [markedFactorialCoordinate, hq, if_pos, ho, mul_one,
        Real.norm_eq_abs, norm_div]
      simp [abs_div]
    · simp [markedFactorialCoordinate, hq, ho]
  · rw [if_neg hq, markedFactorialCoordinate, if_neg hq]
    split <;> split <;> norm_num

-- @node: normalized_outcome_mean_abs_le_half
/-- If [the stated condition on the cell holds](hyp:hk), [the normalized outcome mark is
  integrable in each supported arm-cell law, and its conditional mean has absolute value at most
  one half](goal). -/
lemma normalized_outcome_mean_abs_le_half
    {d : ℕ} {epsilon M sigma : ℝ}
    (P : ModelClass d epsilon M sigma) (a : Bool) (k : Fin d)
    (hk : 0 < P.law.cellMass k) :
    Integrable (fun y : ℝ => y / M) (P.law.outcomeLaw a k) ∧
      |∫ y, y / M ∂P.law.outcomeLaw a k| ≤ (1 / 2 : ℝ) := by
  let _ : IsProbabilityMeasure (P.law.outcomeLaw a k) :=
    P.law.outcome_isProbability a k
  have h2 := outcome_second_moment_le_five_fourths P a k hk
  have hyL2 : MemLp (fun y : ℝ => y) 2 (P.law.outcomeLaw a k) :=
    (memLp_two_iff_integrable_sq (by fun_prop)).2 h2.1
  have hy : Integrable (fun y : ℝ => y) (P.law.outcomeLaw a k) :=
    hyL2.integrable (by norm_num)
  have hM : 0 < M := lt_of_lt_of_le (by norm_num) P.M_ge_one
  have heq : (fun y : ℝ => y / M) = fun y => M⁻¹ * y := by
    funext y
    rw [inv_mul_eq_div]
  rw [heq]
  refine ⟨hy.const_mul _, ?_⟩
  rw [integral_const_mul, ← P.law.outcomeMean_eq, abs_mul, abs_inv,
    abs_of_pos hM]
  rw [← div_eq_inv_mul]
  apply (div_le_iff₀ hM).2
  simpa [div_eq_mul_inv, mul_comm] using P.mean_normalization a k hk

-- @node: integrable_markedFactorialCoordinate
/-- [Every individual marked-factorial coordinate is integrable under the observed law; the unique
  outcome coordinate uses the arm-cell transport](goal). -/
lemma integrable_markedFactorialCoordinate {d : ℕ}
    {epsilon M sigma : ℝ} (P : ModelClass d epsilon M sigma)
    (k : Fin d) (a : Bool) (j : ℕ) (q : Fin (j + 2)) :
    Integrable (markedFactorialCoordinate M k a j q) P.law.observedLaw := by
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
  by_cases hq : q.val = 0
  · by_cases hk : P.law.cellMass k = 0
    · have hnull := observed_arm_cell_measure_eq_zero_of_cellMass_eq_zero
        P.law a k hk
      have hzero : Integrable (fun _ : Obs d => (0 : ℝ)) P.law.observedLaw :=
        integrable_const 0
      refine hzero.congr (ae_iff.mpr ?_)
      apply measure_mono_null _ hnull
      intro o ho
      by_contra hout
      change ¬(o.x = k ∧ o.a = a) at hout
      have hz : markedFactorialCoordinate M k a j q o = 0 := by
        simp [markedFactorialCoordinate, hq, hout]
      exact ho hz.symm
    · have hkpos : 0 < P.law.cellMass k :=
        lt_of_le_of_ne (P.law.cellMass_range k).1 (Ne.symm hk)
      have hc := (normalized_outcome_mean_abs_le_half P a k hkpos).1
      have hc' := hc.smul_measure (c := ENNReal.ofReal
        (P.law.cellMass k *
          (if a then P.law.propensity k else 1 - P.law.propensity k)))
        ENNReal.ofReal_ne_top
      rw [← observed_arm_cell_outcome_measure P.law a k] at hc'
      have hrestrict : Integrable (fun o : Obs d => o.y / M)
          (P.law.observedLaw.restrict {o | o.x = k ∧ o.a = a}) :=
        (MeasureTheory.integrable_map_measure
          ((measurable_id.div measurable_const).aestronglyMeasurable)
          hy.aemeasurable).mp hc'
      have hind : Integrable
          ({o : Obs d | o.x = k ∧ o.a = a}.indicator (fun o => o.y / M))
          P.law.observedLaw :=
        (integrable_indicator_iff hxa).2 hrestrict
      apply hind.congr
      filter_upwards with o
      simp [markedFactorialCoordinate, hq, Set.indicator, mul_ite]
  · have hbound : ∀ o, ‖markedFactorialCoordinate M k a j q o‖ ≤ 1 := by
      intro o
      rw [markedFactorialCoordinate, if_neg hq]
      split <;> split <;> norm_num
    exact Integrable.of_bound
      (measurable_markedFactorialCoordinate M k a j q).aestronglyMeasurable 1
      (Filter.Eventually.of_forall hbound)

-- @node: memLp_two_markedFactorialCoordinate
/-- [Every marked coordinate is square-integrable. The marked position uses the observed
  normalized second-moment audit; every selector-only position is uniformly bounded by one](goal). -/
lemma memLp_two_markedFactorialCoordinate {d : ℕ}
    {epsilon M sigma : ℝ} (P : ModelClass d epsilon M sigma)
    (k : Fin d) (a : Bool) (j : ℕ) (q : Fin (j + 2)) :
    MemLp (markedFactorialCoordinate M k a j q) 2 P.law.observedLaw := by
  have hmeas : AEStronglyMeasurable (markedFactorialCoordinate M k a j q)
      P.law.observedLaw :=
    (measurable_markedFactorialCoordinate M k a j q).aestronglyMeasurable
  by_cases hq : q.val = 0
  · have htuple : Measurable (fun o : Obs d => (o.x, o.a, o.y)) :=
      measurable_iff_comap_le.mpr le_rfl
    have hx : Measurable (fun o : Obs d => o.x) := measurable_fst.comp htuple
    have ha : Measurable (fun o : Obs d => o.a) :=
      measurable_fst.comp (measurable_snd.comp htuple)
    have hxa : MeasurableSet {o : Obs d | o.x = k ∧ o.a = a} := by
      simpa only [Set.preimage, Set.mem_singleton_iff, Prod.mk.injEq] using
        (measurableSet_singleton (k, a)).preimage (Measurable.prodMk hx ha)
    apply (memLp_two_iff_integrable_sq hmeas).2
    have hi := (integrable_observed_normalized_outcome_sq P).indicator hxa
    apply hi.congr
    filter_upwards with o
    by_cases ho : o.x = k ∧ o.a = a <;>
      simp [markedFactorialCoordinate, hq, Set.indicator, ho]
  · apply MemLp.of_bound hmeas 1
    filter_upwards with o
    rw [markedFactorialCoordinate, if_neg hq]
    split <;> split <;> norm_num

-- @node: integrable_orderedProductKernel_markedFactorialCoordinate
/-- [A whole marked factorial kernel is integrable under the corresponding finite product
  law](goal). -/
lemma integrable_orderedProductKernel_markedFactorialCoordinate {d : ℕ}
    {epsilon M sigma : ℝ} (P : ModelClass d epsilon M sigma)
    (k : Fin d) (a : Bool) (j : ℕ) :
    Integrable (Causalean.Stat.orderedProductKernel
      (markedFactorialCoordinate M k a j))
      (Measure.pi fun _ : Fin (j + 2) => P.law.observedLaw) := by
  exact Integrable.fintype_prod fun q =>
    integrable_markedFactorialCoordinate P k a j q

-- @node: integrable_mergedProductKernel_markedFactorialCoordinate
/-- [Every partial-matching merge is integrable. After bounded selectors are discarded, the only
  possible unbounded factor is the product of the two marked coordinates; distinct marks factor
  across product coordinates, while a collision is controlled by the observed second
  moment](goal). -/
lemma integrable_mergedProductKernel_markedFactorialCoordinate {d : ℕ}
    {epsilon M sigma : ℝ} (P : ModelClass d epsilon M sigma)
    (k l : Fin d) (a b : Bool) (j r : ℕ)
    (N : Causalean.Stat.PartialMatching (j + 2) (r + 2)) :
    Integrable (Causalean.Stat.mergedProductKernel
      (markedFactorialCoordinate M k a j)
      (markedFactorialCoordinate M l b r) N)
      (Measure.pi fun _ : N.MergedIndex => P.law.observedLaw) := by
  classical
  let uL : N.MergedIndex := N.leftInjection 0
  let uR : N.MergedIndex := N.rightInjection 0
  let v : Obs d → ℝ := fun o => o.y / M
  let phi : N.MergedIndex → Obs d → ℝ := fun u o =>
    (if u = uL then |v o| else 1) * (if u = uR then |v o| else 1)
  have hv2 : Integrable (fun o : Obs d => (v o) ^ 2) P.law.observedLaw := by
    simpa [v] using integrable_observed_normalized_outcome_sq P
  have hv : Integrable (fun o : Obs d => |v o|) P.law.observedLaw := by
    exact (memLp_two_observed_normalized_outcome P).integrable (by norm_num) |>.norm
  have hphi : ∀ u : N.MergedIndex, Integrable (phi u) P.law.observedLaw := by
    intro u
    by_cases huL : u = uL
    · by_cases huR : u = uR
      · have hLR : uL = uR := huL.symm.trans huR
        simpa [phi, huL, huR, hLR, pow_two] using hv2
      · have hLR : uL ≠ uR := fun h => huR (huL.trans h)
        simpa [phi, huL, huR, hLR] using hv
    · by_cases huR : u = uR
      · have hRL : uR ≠ uL := fun h => huL (huR.trans h)
        simpa [phi, huL, huR, hRL] using hv
      · simpa [phi, huL, huR] using (integrable_const (1 : ℝ))
  have hdom : Integrable (fun z : N.MergedIndex → Obs d => ∏ u, phi u (z u))
      (Measure.pi fun _ : N.MergedIndex => P.law.observedLaw) :=
    Integrable.fintype_prod hphi
  apply hdom.mono'
  · exact (measurable_mergedProductKernel_markedFactorialCoordinate
      M k l a b j r N).aestronglyMeasurable
  · filter_upwards with z
    unfold Causalean.Stat.mergedProductKernel
    rw [norm_mul, norm_prod, norm_prod]
    have hleft : (∏ q : Fin (j + 2),
        ‖markedFactorialCoordinate M k a j q (z (N.leftInjection q))‖) ≤
        |v (z uL)| := by
      calc
        _ ≤ ∏ q : Fin (j + 2), if q.val = 0 then
              |v (z (N.leftInjection q))| else 1 := by
          apply Finset.prod_le_prod
          · intro q _
            positivity
          · intro q _
            simpa [v] using markedFactorialCoordinate_norm_le_mark M k a j q
              (z (N.leftInjection q))
        _ = |v (z uL)| := by
          simp [uL]
    have hright : (∏ q : Fin (r + 2),
        ‖markedFactorialCoordinate M l b r q (z (N.rightInjection q))‖) ≤
        |v (z uR)| := by
      calc
        _ ≤ ∏ q : Fin (r + 2), if q.val = 0 then
              |v (z (N.rightInjection q))| else 1 := by
          apply Finset.prod_le_prod
          · intro q _
            positivity
          · intro q _
            simpa [v] using markedFactorialCoordinate_norm_le_mark M l b r q
              (z (N.rightInjection q))
        _ = |v (z uR)| := by
          simp [uR]
    calc
      _ ≤ |v (z uL)| * |v (z uR)| :=
        mul_le_mul hleft hright (by positivity) (by positivity)
      _ = ∏ u, phi u (z u) := by
        simp only [phi, Finset.prod_mul_distrib]
        simp [uL, uR]

-- @node: memLp_two_orderedProductKernel_markedFactorialCoordinate
/-- [The ordered marked kernel is square-integrable under its finite product law, obtained by
  factoring its square coordinatewise](goal). -/
lemma memLp_two_orderedProductKernel_markedFactorialCoordinate {d : ℕ}
    {epsilon M sigma : ℝ} (P : ModelClass d epsilon M sigma)
    (k : Fin d) (a : Bool) (j : ℕ) :
    MemLp (Causalean.Stat.orderedProductKernel
      (markedFactorialCoordinate M k a j)) 2
      (Measure.pi fun _ : Fin (j + 2) => P.law.observedLaw) := by
  have hmeas : AEStronglyMeasurable
      (Causalean.Stat.orderedProductKernel
        (markedFactorialCoordinate M k a j))
      (Measure.pi fun _ : Fin (j + 2) => P.law.observedLaw) :=
    (measurable_orderedProductKernel_markedFactorialCoordinate M k a j).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq hmeas).2
  have hcoord : ∀ q : Fin (j + 2),
      Integrable (fun o => (markedFactorialCoordinate M k a j q o) ^ 2)
        P.law.observedLaw := by
    intro q
    exact (memLp_two_iff_integrable_sq
      (measurable_markedFactorialCoordinate M k a j q).aestronglyMeasurable).1
      (memLp_two_markedFactorialCoordinate P k a j q)
  have hprod := Integrable.fintype_prod hcoord
  convert hprod using 1
  funext z
  simp [Causalean.Stat.orderedProductKernel, Finset.prod_pow]

-- @node: partialMatching_count_le_order_power
/-- If [the second factorial order is admissible](hyp:hr) and [the stated size condition
  holds](hyp:hs), [if both coordinate families have order at most `K`, the number of size-`h`
  partial matchings is at most `K^(2h) / h!`. This is the matching-count factor used when the
  covariance expansion is summed by overlap size](goal). -/
lemma partialMatching_count_le_order_power {r s h K : ℕ}
    (hr : r ≤ K) (hs : s ≤ K) :
    ((Causalean.Stat.partialMatchingsOfSize r s h).card : ℝ) ≤
      (K : ℝ) ^ (2 * h) / h.factorial := by
  rw [Causalean.Stat.card_partialMatchingsOfSize]
  have hf : (0 : ℝ) < h.factorial := by positivity
  have hrb : (Nat.choose r h : ℝ) ≤ (r : ℝ) ^ h / h.factorial :=
    Nat.choose_le_pow_div h r
  have hsb : (Nat.choose s h : ℝ) ≤ (s : ℝ) ^ h / h.factorial :=
    Nat.choose_le_pow_div h s
  have hr0 : (0 : ℝ) ≤ Nat.choose r h := by positivity
  have hs0 : (0 : ℝ) ≤ Nat.choose s h := by positivity
  have hprod : (Nat.choose r h : ℝ) * Nat.choose s h ≤
      ((r : ℝ) ^ h / h.factorial) * ((s : ℝ) ^ h / h.factorial) :=
    mul_le_mul hrb hsb hs0 (by positivity)
  have hrp : (r : ℝ) ^ h ≤ (K : ℝ) ^ h :=
    pow_le_pow_left₀ (by positivity) (by exact_mod_cast hr) h
  have hsp : (s : ℝ) ^ h ≤ (K : ℝ) ^ h :=
    pow_le_pow_left₀ (by positivity) (by exact_mod_cast hs) h
  calc
    ((Nat.choose r h * Nat.choose s h * h.factorial : ℕ) : ℝ) =
        (Nat.choose r h : ℝ) * Nat.choose s h * h.factorial := by
          push_cast
          ring
    _ ≤ (((r : ℝ) ^ h / h.factorial) *
        ((s : ℝ) ^ h / h.factorial)) * h.factorial :=
      mul_le_mul_of_nonneg_right hprod hf.le
    _ = (r : ℝ) ^ h * (s : ℝ) ^ h / h.factorial := by field_simp
    _ ≤ (K : ℝ) ^ h * (K : ℝ) ^ h / h.factorial := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul hrp hsp (by positivity) (by positivity)) hf.le
    _ = (K : ℝ) ^ (2 * h) / h.factorial := by rw [two_mul, pow_add]

-- @node: marked_matchingNormalization_le
/-- If [the first factorial order is admissible](hyp:hj) and [the second factorial order is
  admissible](hyp:hr) and [the stated condition on the source size or matching order
  holds](hyp:hm) and [the sampling budget satisfies the stated lower bound](hyp:hN), [the generic
  mixed-order normalization bound specialized to the marked factorial orders occurring in the
  paper](goal). -/
lemma marked_matchingNormalization_le {m K j r h : ℕ}
    {N : Causalean.Stat.PartialMatching (j + 2) (r + 2)}
    (hj : j + 2 ≤ K) (hr : r + 2 ≤ K) (hm : 4 * (K + 2) ^ 2 ≤ m)
    (hN : N ∈ Causalean.Stat.partialMatchingsOfSize (j + 2) (r + 2) h) :
    Causalean.Stat.matchingNormalization m N ≤
      Real.exp 1 / (m : ℝ) ^ h := by
  exact Causalean.Stat.matchingNormalization_le
    (R := K + 2) (hj.trans (by omega)) (hr.trans (by omega)) hm hN

-- @node: marked_emptyMatchingNormalization_sub_one_le
/-- If [the first factorial order is admissible](hyp:hj) and [the second factorial order is
  admissible](hyp:hr) and [the stated condition on the source size or matching order
  holds](hyp:hm), [the disjoint-tuple correction for two marked factorial orders is at most
  `2(K+2)²/m`, uniformly over the polynomial degrees](goal). -/
lemma marked_emptyMatchingNormalization_sub_one_le {m K j r : ℕ}
    (hj : j + 2 ≤ K) (hr : r + 2 ≤ K) (hm : 4 * (K + 2) ^ 2 ≤ m) :
    |Causalean.Stat.matchingNormalization m
        (Causalean.Stat.PartialMatching.empty (j + 2) (r + 2)) - 1| ≤
      2 * ((K + 2 : ℕ) : ℝ) ^ 2 / m := by
  exact Causalean.Stat.emptyMatchingNormalization_sub_one_le
    (R := K + 2) (hj.trans (by omega)) (hr.trans (by omega)) hm

-- @node: marked_matchingNormalization_sum_le
/-- If [the first factorial order is admissible](hyp:hj) and [the second factorial order is
  admissible](hyp:hr) and [the stated condition on the source size or matching order
  holds](hyp:hm), [summing the normalization over all size-`h` overlaps costs at most the paper's
  `K^(2h)/h!` matching count times the generic `exp(1)/m^h` ratio](goal). -/
lemma marked_matchingNormalization_sum_le {m K j r h : ℕ}
    (hj : j + 2 ≤ K) (hr : r + 2 ≤ K) (hm : 4 * (K + 2) ^ 2 ≤ m) :
    ∑ N ∈ Causalean.Stat.partialMatchingsOfSize (j + 2) (r + 2) h,
        Causalean.Stat.matchingNormalization m N ≤
      ((K : ℝ) ^ (2 * h) / h.factorial) *
        (Real.exp 1 / (m : ℝ) ^ h) := by
  calc
    ∑ N ∈ Causalean.Stat.partialMatchingsOfSize (j + 2) (r + 2) h,
        Causalean.Stat.matchingNormalization m N ≤
        ∑ _N ∈ Causalean.Stat.partialMatchingsOfSize (j + 2) (r + 2) h,
          (Real.exp 1 / (m : ℝ) ^ h) := by
            apply Finset.sum_le_sum
            intro N hN
            exact marked_matchingNormalization_le hj hr hm hN
    _ = ((Causalean.Stat.partialMatchingsOfSize (j + 2) (r + 2) h).card : ℝ) *
          (Real.exp 1 / (m : ℝ) ^ h) := by
            simp [mul_comm]
    _ ≤ ((K : ℝ) ^ (2 * h) / h.factorial) *
          (Real.exp 1 / (m : ℝ) ^ h) := by
            exact mul_le_mul_of_nonneg_right
              (partialMatching_count_le_order_power hj hr)
              (by positivity)

-- @node: measurable_allBlockOrderedMarkedFactorial
/-- [The all-block version of each marked factorial statistic is measurable on the finite product
  sample space](goal). -/
lemma measurable_allBlockOrderedMarkedFactorial {m d : ℕ} (M : ℝ)
    (k : Fin d) (a : Bool) (j : ℕ) :
    Measurable (fun s : Fin m → Obs d =>
      allBlockOrderedMarkedFactorial M s k a j) := by
  unfold allBlockOrderedMarkedFactorial
  apply Measurable.div
  · apply Finset.measurable_sum
    intro idx _
    apply Measurable.ite
    · by_cases hidx : Function.Injective idx
      · simpa [hidx] using (measurableSet_univ :
          MeasurableSet (Set.univ : Set (Fin m → Obs d)))
      · simpa [hidx] using (measurableSet_empty :
          MeasurableSet (∅ : Set (Fin m → Obs d)))
    · have hmap : Measurable (fun s : Fin m → Obs d =>
          fun q : Fin (j + 2) => s (idx q)) :=
        measurable_pi_lambda _ fun q => measurable_pi_apply (idx q)
      convert
        (measurable_orderedProductKernel_markedFactorialCoordinate M k a j).comp
          hmap using 1
      funext s
      exact (prod_markedFactorialCoordinate M k a j
        (fun q => s (idx q))).symm
    · exact measurable_const
  · exact measurable_const

-- @node: measurable_allBlockMarkedPolynomialSum
/-- [Finite summation preserves measurability of the complete deterministic light-cell
  statistic](goal). -/
lemma measurable_allBlockMarkedPolynomialSum {m d : ℕ} (M B : ℝ) (K : ℕ)
    (S : Finset (Fin d)) :
    Measurable (allBlockMarkedPolynomialSum (m := m) M B K S) := by
  unfold allBlockMarkedPolynomialSum allBlockLightPolynomialTerm
  apply Finset.measurable_sum
  intro k _
  apply Finset.measurable_sum
  intro j _
  exact measurable_const.mul
    ((measurable_allBlockOrderedMarkedFactorial M k true j).sub
      (measurable_allBlockOrderedMarkedFactorial M k false j))

-- @node: variance_allBlockMarkedPolynomialSum_eq_infinitePi
/-- [The variance under the finite product law can be evaluated on the canonical infinite-product
  IID realization by restricting it to the first `m` coordinates](goal). -/
lemma variance_allBlockMarkedPolynomialSum_eq_infinitePi {m d : ℕ}
    (P0 : Measure (Obs d)) [IsProbabilityMeasure P0]
    (M B : ℝ) (K : ℕ) (S : Finset (Fin d)) :
    variance (allBlockMarkedPolynomialSum (m := m) M B K S)
        (Measure.pi fun _ : Fin m => P0) =
      variance (fun ω : ℕ → Obs d =>
        allBlockMarkedPolynomialSum M B K S (fun i : Fin m => ω i))
        (Measure.infinitePi fun _ : ℕ => P0) := by
  let S0 := Causalean.Stat.iidSample_infinitePi P0
  have hpush := Causalean.Stat.iidSample_finN_pushforward S0 m
  have hprefix : Measurable (fun ω : ℕ → Obs d => fun i : Fin m => ω i) :=
    Causalean.Stat.iidSample_finN_measurable S0 m
  dsimp [S0, Causalean.Stat.iidSample_infinitePi] at hpush hprefix
  rw [← hpush]
  simpa [Function.comp_def] using
    (variance_map
      (measurable_allBlockMarkedPolynomialSum (m := m) M B K S).aemeasurable
      hprefix.aemeasurable)

end CausalSmith.Stat.DiscreteAteHeterogeneityFrontier
