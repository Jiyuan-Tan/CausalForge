/- Same-cell partial-matching and coefficient assembly. -/

import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.FactorialCovarianceExpansion

namespace CausalSmith.Stat.DiscreteAteHeterogeneityFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators

-- @node: mergedMarkedCoordinateFactor_integral_abs_le
/-- [the absolute integral of a merged marked-coordinate factor satisfies the stated
  cell-probability bound](goal). -/
lemma mergedMarkedCoordinateFactor_integral_abs_le {d : ℕ} {epsilon M sigma : ℝ}
    (P : ModelClass d epsilon M sigma) (k : Fin d) (a b : Bool)
    (j r : ℕ) (N : Causalean.Stat.PartialMatching (j + 2) (r + 2))
    (t : N.MergedIndex) :
    |∫ o : Obs d, mergedMarkedCoordinateFactor M k a b j r N t o
      ∂P.law.observedLaw| ≤ (5 / 4 : ℝ) * P.law.cellMass k := by
  classical
  cases t with
  | inl q =>
      unfold mergedMarkedCoordinateFactor
      simp only [Causalean.Stat.PartialMatching.leftInjection, Sum.inl.injEq,
        Finset.filter_eq']
      by_cases hq : q ∈ N.left
      · let s : Fin (r + 2) := (N.equiv ⟨q, hq⟩).1
        have hs : s ∈ N.right := (N.equiv ⟨q, hq⟩).2
        have hfilter : (Finset.univ : Finset (Fin (r + 2))).filter
            (fun x => N.rightInjection x = Sum.inl q) = {s} := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_singleton]
          constructor
          · intro hx
            by_cases hxr : x ∈ N.right
            · simp only [Causalean.Stat.PartialMatching.rightInjection, hxr,
                dite_true] at hx
              have he : N.equiv.symm ⟨x, hxr⟩ = ⟨q, hq⟩ := by
                apply Subtype.ext
                exact Sum.inl.inj hx
              have he' := congrArg N.equiv he
              simpa [s] using congrArg Subtype.val he'
            · simp [Causalean.Stat.PartialMatching.rightInjection, hxr] at hx
          · intro hx
            subst x
            simp [Causalean.Stat.PartialMatching.rightInjection, hs, s]
        rw [hfilter]
        simpa using integral_markedFactorialCoordinate_mul_abs_le P k a b j r q s
      · have hfilter : (Finset.univ : Finset (Fin (r + 2))).filter
            (fun x => N.rightInjection x = Sum.inl q) = ∅ := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · intro hx
            by_cases hxr : x ∈ N.right
            · simp only [Causalean.Stat.PartialMatching.rightInjection, hxr,
                dite_true] at hx
              have hval : (N.equiv.symm ⟨x, hxr⟩).1 = q := Sum.inl.inj hx
              have hf : False := hq (by
                simpa [hval] using (N.equiv.symm ⟨x, hxr⟩).2)
              exact hf.elim
            · simp [Causalean.Stat.PartialMatching.rightInjection, hxr] at hx
          · intro hx
            have hf : False := by simpa using hx
            exact hf.elim
        rw [hfilter]
        simpa using (integral_markedFactorialCoordinate_abs_le_cellMass P a k j q).trans
          (by have hp := P.law.cellMass_range k |>.1; nlinarith)
  | inr s =>
      unfold mergedMarkedCoordinateFactor
      simp only [Causalean.Stat.PartialMatching.leftInjection, Sum.inl.injEq,
        Finset.filter_false, Finset.prod_empty, one_mul]
      have hfilter : (Finset.univ : Finset (Fin (r + 2))).filter
          (fun x => N.rightInjection x = Sum.inr s) = {s.1} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_singleton]
        constructor
        · intro hx
          by_cases hxr : x ∈ N.right
          · simp [Causalean.Stat.PartialMatching.rightInjection, hxr] at hx
          · simp only [Causalean.Stat.PartialMatching.rightInjection, hxr,
              dite_false] at hx
            apply Fin.ext
            exact congrArg (fun z => z.1.1) (Sum.inr.inj hx)
        · intro hx
          subst x
          simp [Causalean.Stat.PartialMatching.rightInjection, s.2]
      rw [hfilter]
      simpa using (integral_markedFactorialCoordinate_abs_le_cellMass
        P b k r s.1).trans
          (by have hp := P.law.cellMass_range k |>.1; nlinarith)

-- @node: mergedProductMoment_markedFactorialCoordinate_same_cell_abs_le
/-- If [the sampling budget satisfies the stated lower bound](hyp:hN), [the same-cell merged
  product moment of marked factorial coordinates satisfies the stated bound](goal). -/
lemma mergedProductMoment_markedFactorialCoordinate_same_cell_abs_le {d : ℕ} {epsilon M sigma : ℝ}
    (P : ModelClass d epsilon M sigma) (k : Fin d) (a b : Bool)
    (j r h : ℕ) (N : Causalean.Stat.PartialMatching (j + 2) (r + 2))
    (hN : N.size = h) :
    |Causalean.Stat.mergedProductMoment P.law.observedLaw
      (markedFactorialCoordinate M k a j)
      (markedFactorialCoordinate M k b r) N| ≤
        ((5 / 4 : ℝ) * P.law.cellMass k) ^ ((j + 2) + (r + 2) - h) := by
  classical
  unfold Causalean.Stat.mergedProductMoment
  simp_rw [mergedProductKernel_markedFactorialCoordinate_eq_prod_fibers]
  rw [MeasureTheory.integral_fintype_prod_eq_prod, ← Real.norm_eq_abs,
    norm_prod]
  simp only [Real.norm_eq_abs]
  calc
    (∏ t : N.MergedIndex,
        |∫ o : Obs d, mergedMarkedCoordinateFactor M k a b j r N t o
          ∂P.law.observedLaw|) ≤
        ∏ _t : N.MergedIndex, (5 / 4 : ℝ) * P.law.cellMass k := by
      apply Finset.prod_le_prod
      · intro t _
        exact abs_nonneg _
      · intro t _
        exact mergedMarkedCoordinateFactor_integral_abs_le P k a b j r N t
    _ = ((5 / 4 : ℝ) * P.law.cellMass k) ^ ((j + 2) + (r + 2) - h) := by
      rw [Finset.prod_const, Finset.card_univ,
        Causalean.Stat.PartialMatching.mergedIndex_card, hN]

-- @node: centeredCrossMoment_allBlockOrderedMarkedFactorial_same_cell_abs_le
/-- If [the first factorial order is admissible](hyp:hj) and [the second factorial order is
  admissible](hyp:hr) and [the stated condition on the source size or matching order
  holds](hyp:hm), [the centered cross-moment of two marked factorial statistics from the same cell
  satisfies the stated bound](goal). -/
lemma centeredCrossMoment_allBlockOrderedMarkedFactorial_same_cell_abs_le {d m K : ℕ} {epsilon M sigma : ℝ}
    (P : ModelClass d epsilon M sigma) (k : Fin d) (a b : Bool)
    (j r : ℕ) (hj : j + 2 ≤ K) (hr : r + 2 ≤ K)
    (hm : 4 * (K + 2) ^ 2 ≤ m) :
    |Causalean.Stat.centeredCrossMoment
      (Measure.infinitePi fun _ : ℕ => P.law.observedLaw)
      (fun ω : ℕ → Obs d =>
        allBlockOrderedMarkedFactorial M (fun i : Fin m => ω i) k a j)
      (fun ω : ℕ → Obs d =>
        allBlockOrderedMarkedFactorial M (fun i : Fin m => ω i) k b r)| ≤
      (2 * ((K + 2 : ℕ) : ℝ) ^ 2 / m) *
          P.law.cellMass k ^ (j + 2) * P.law.cellMass k ^ (r + 2) +
        Real.exp 1 * ((5 / 4 : ℝ) * P.law.cellMass k) ^ (r + 2) *
          ((5 / 4 : ℝ) * P.law.cellMass k + (r + 2 : ℕ) / m) ^ (j + 2) := by
  classical
  rw [centeredCrossMoment_allBlockOrderedMarkedFactorial P k k a b j r hj hr hm]
  have hp : 0 ≤ (5 / 4 : ℝ) * P.law.cellMass k := by
    exact mul_nonneg (by norm_num) (P.law.cellMass_range k).1
  have hpos :
      |∑ h ∈ (Finset.range (min (j + 2) (r + 2) + 1)).filter (fun h => 0 < h),
          ∑ N ∈ Causalean.Stat.partialMatchingsOfSize (j + 2) (r + 2) h,
            Causalean.Stat.matchingNormalization m N *
              Causalean.Stat.mergedProductMoment P.law.observedLaw
                (markedFactorialCoordinate M k a j)
                (markedFactorialCoordinate M k b r) N| ≤
        Real.exp 1 * ((5 / 4 : ℝ) * P.law.cellMass k) ^ (r + 2) *
          ((5 / 4 : ℝ) * P.law.cellMass k + (r + 2 : ℕ) / m) ^ (j + 2) := by
    calc
      _ ≤ ∑ h ∈ (Finset.range (min (j + 2) (r + 2) + 1)).filter
            (fun h => 0 < h),
          (∑ N ∈ Causalean.Stat.partialMatchingsOfSize (j + 2) (r + 2) h,
            Causalean.Stat.matchingNormalization m N) *
              ((5 / 4 : ℝ) * P.law.cellMass k) ^ ((j + 2) + (r + 2) - h) := by
        calc
          _ ≤ ∑ h ∈ (Finset.range (min (j + 2) (r + 2) + 1)).filter
              (fun h => 0 < h),
              |∑ N ∈ Causalean.Stat.partialMatchingsOfSize (j + 2) (r + 2) h,
                Causalean.Stat.matchingNormalization m N *
                  Causalean.Stat.mergedProductMoment P.law.observedLaw
                    (markedFactorialCoordinate M k a j)
                    (markedFactorialCoordinate M k b r) N| :=
            Finset.abs_sum_le_sum_abs _ _
          _ ≤ _ := by
            apply Finset.sum_le_sum
            intro h hh
            calc
              _ ≤ ∑ N ∈ Causalean.Stat.partialMatchingsOfSize (j + 2) (r + 2) h,
              |Causalean.Stat.matchingNormalization m N *
                Causalean.Stat.mergedProductMoment P.law.observedLaw
                  (markedFactorialCoordinate M k a j)
                  (markedFactorialCoordinate M k b r) N| :=
                Finset.abs_sum_le_sum_abs _ _
              _ ≤
              ∑ N ∈ Causalean.Stat.partialMatchingsOfSize (j + 2) (r + 2) h,
                Causalean.Stat.matchingNormalization m N *
                  ((5 / 4 : ℝ) * P.law.cellMass k) ^ ((j + 2) + (r + 2) - h) := by
                apply Finset.sum_le_sum
                intro N hN
                rw [abs_mul, abs_of_nonneg (by
                  unfold Causalean.Stat.matchingNormalization
                  positivity)]
                exact mul_le_mul_of_nonneg_left
                  (mergedProductMoment_markedFactorialCoordinate_same_cell_abs_le P k a b j r h N (by simpa using hN))
                  (by unfold Causalean.Stat.matchingNormalization; positivity)
              _ = _ := by rw [Finset.sum_mul]
      _ ≤ _ := positiveMatchingNormalization_weighted_sum_le
        (R := K + 2) (hj.trans (by omega)) (hr.trans (by omega)) hm hp
  have hempty :
      |(Causalean.Stat.matchingNormalization m
          (Causalean.Stat.PartialMatching.empty (j + 2) (r + 2)) - 1) *
          Causalean.Stat.orderedProductMean P.law.observedLaw
            (markedFactorialCoordinate M k a j) *
          Causalean.Stat.orderedProductMean P.law.observedLaw
            (markedFactorialCoordinate M k b r)| ≤
        (2 * ((K + 2 : ℕ) : ℝ) ^ 2 / m) *
          P.law.cellMass k ^ (j + 2) * P.law.cellMass k ^ (r + 2) := by
    rw [abs_mul, abs_mul]
    have hn := marked_emptyMatchingNormalization_sub_one_le hj hr hm
    have hjm := orderedProductMean_markedFactorialCoordinate_abs_le P a k j
    have hrm := orderedProductMean_markedFactorialCoordinate_abs_le P b k r
    have hmpos : (0 : ℝ) < m := by
      exact_mod_cast (lt_of_lt_of_le (by positivity : 0 < 4 * (K + 2) ^ 2) hm)
    gcongr
    exact mul_nonneg (by positivity) (pow_nonneg (P.law.cellMass_range k).1 _)
  exact (abs_add_le _ _).trans (add_le_add hempty hpos)

-- @node: shiftedCoefficient_weighted_sum_le_of_le
/-- If [the polynomial or elbow parameter satisfies its stated bound](hyp:hK) and [the outcome
  bound is positive](hyp:hB) and [the cell probability is nonnegative](hyp:hp0) and [the scaled
  cell probability satisfies the budget bound](hyp:hpB), [a pointwise coefficient bound implies
  the corresponding weighted-sum bound](goal). -/
lemma shiftedCoefficient_weighted_sum_le_of_le {K : ℕ} (hK : 0 < K) {B p : ℝ} (hB : 0 < B)
    (hp0 : 0 ≤ p) (hpB : p ≤ B) :
    ∑ j ∈ Finset.range (K - 1),
        |shiftedCoefficient K j / B ^ (j + 1)| * p ^ (j + 2) ≤
      B * (6 : ℝ) ^ K := by
  have hB0 : 0 ≤ B := hB.le
  have hratio0 : 0 ≤ p / B := div_nonneg hp0 hB0
  have hratio1 : p / B ≤ 1 := (div_le_one hB).2 hpB
  have hrewrite :
      (∑ j ∈ Finset.range (K - 1),
          |shiftedCoefficient K j / B ^ (j + 1)| * p ^ (j + 2)) =
        (p ^ 2 / B) * shiftedCoefficientEnvelope K (p / B) := by
    unfold shiftedCoefficientEnvelope
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [abs_div, abs_pow, abs_of_pos hB]
    have hBne : B ≠ 0 := ne_of_gt hB
    rw [div_pow]
    field_simp
    ring
  rw [hrewrite]
  have henv := shiftedCoefficientEnvelope_le_six_pow hK hratio0 hratio1
  have hp2 : p ^ 2 / B ≤ B := by
    apply (div_le_iff₀ hB).2
    nlinarith
  exact (mul_le_mul_of_nonneg_left henv
      (div_nonneg (sq_nonneg p) hB0)).trans
    (mul_le_mul_of_nonneg_right hp2 (by positivity))

-- @node: weighted_centeredCrossMoment_same_cell_sum_le
/-- If [the polynomial or elbow parameter satisfies its stated bound](hyp:hK) and [the outcome
  bound is positive](hyp:hB) and [the stated condition on the cell holds](hyp:hk) and [the stated
  condition on the source size or matching order holds](hyp:hm) and [the stated shift condition
  holds](hyp:hshift), [the weighted sum of same-cell centered cross-moments satisfies the stated
  bound](goal). -/
lemma weighted_centeredCrossMoment_same_cell_sum_le {d m K : ℕ} {epsilon M sigma B : ℝ}
    (P : ModelClass d epsilon M sigma) (k : Fin d)
    (hK : 2 ≤ K) (hB : 0 < B) (hk : P.law.cellMass k ≤ B / 4)
    (hm : 4 * (K + 2) ^ 2 ≤ m)
    (hshift : (4 : ℝ) * (K + 2) / m ≤ 3 * B / 4) :
    ∑ a : Bool, ∑ b : Bool,
      ∑ j ∈ Finset.range (K - 1), ∑ r ∈ Finset.range (K - 1),
        |shiftedCoefficient K j / B ^ (j + 1)| *
          |shiftedCoefficient K r / B ^ (r + 1)| *
          |Causalean.Stat.centeredCrossMoment
            (Measure.infinitePi fun _ : ℕ => P.law.observedLaw)
            (fun ω : ℕ → Obs d =>
              allBlockOrderedMarkedFactorial M (fun i : Fin m => ω i) k a j)
            (fun ω : ℕ → Obs d =>
              allBlockOrderedMarkedFactorial M (fun i : Fin m => ω i) k b r)| ≤
      16 * (B * (6 : ℝ) ^ K) ^ 2 := by
  classical
  let p : ℝ := P.law.cellMass k
  let p' : ℝ := (5 / 4 : ℝ) * p
  let c : ℕ → ℝ := fun j => |shiftedCoefficient K j / B ^ (j + 1)|
  have hmpos : (0 : ℝ) < m := by
    exact_mod_cast (lt_of_lt_of_le (by positivity : 0 < 4 * (K + 2) ^ 2) hm)
  have hp0 : 0 ≤ p := P.law.cellMass_range k |>.1
  have hp'0 : 0 ≤ p' := by dsimp [p']; positivity
  have hp'B : p' ≤ B := by dsimp [p', p]; nlinarith
  have hvm (r : ℕ) (hr : r ∈ Finset.range (K - 1)) :
      p' + (r + 2 : ℕ) / m ≤ B := by
    have hrK : r + 2 ≤ K := by have := Finset.mem_range.mp hr; omega
    have hcast : ((r + 2 : ℕ) : ℝ) ≤ K + 2 := by exact_mod_cast (hrK.trans (by omega))
    have hdiv : ((r + 2 : ℕ) : ℝ) / m ≤ (K + 2 : ℝ) / m := by
      exact (div_le_div_iff_of_pos_right hmpos).2 hcast
    have hs : 4 * ((K + 2 : ℝ) / m) ≤ 3 * B / 4 := by
      convert hshift using 1 <;> ring
    have hKm : (K + 2 : ℝ) / m ≤ 3 * B / 16 := by nlinarith
    dsimp [p', p]
    nlinarith
  have hq : 2 * ((K + 2 : ℕ) : ℝ) ^ 2 / m ≤ 1 / 2 := by
    apply (div_le_iff₀ hmpos).2
    have hmR : (4 : ℝ) * ((K + 2 : ℕ) : ℝ) ^ 2 ≤ m := by exact_mod_cast hm
    nlinarith
  have hterm (a b : Bool) (j r : ℕ)
      (hj : j ∈ Finset.range (K - 1)) (hr : r ∈ Finset.range (K - 1)) :
      c j * c r *
          |Causalean.Stat.centeredCrossMoment
            (Measure.infinitePi fun _ : ℕ => P.law.observedLaw)
            (fun ω : ℕ → Obs d =>
              allBlockOrderedMarkedFactorial M (fun i : Fin m => ω i) k a j)
            (fun ω : ℕ → Obs d =>
              allBlockOrderedMarkedFactorial M (fun i : Fin m => ω i) k b r)| ≤
        c j * c r * ((1 / 2 : ℝ) * p ^ (j + 2) * p ^ (r + 2) +
          Real.exp 1 * p' ^ (r + 2) *
            (p' + (r + 2 : ℕ) / m) ^ (j + 2)) := by
    have hjK : j + 2 ≤ K := by have := Finset.mem_range.mp hj; omega
    have hrK : r + 2 ≤ K := by have := Finset.mem_range.mp hr; omega
    have hc := centeredCrossMoment_allBlockOrderedMarkedFactorial_same_cell_abs_le P k a b j r hjK hrK hm
    dsimp [c, p, p']
    refine mul_le_mul_of_nonneg_left (hc.trans ?_)
      (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    exact add_le_add (by gcongr) le_rfl
  calc
    _ ≤ ∑ _a : Bool, ∑ _b : Bool,
        ∑ j ∈ Finset.range (K - 1), ∑ r ∈ Finset.range (K - 1),
          c j * c r * ((1 / 2 : ℝ) * p ^ (j + 2) * p ^ (r + 2) +
            Real.exp 1 * p' ^ (r + 2) *
              (p' + (r + 2 : ℕ) / m) ^ (j + 2)) := by
      apply Finset.sum_le_sum; intro a ha
      apply Finset.sum_le_sum; intro b hb
      apply Finset.sum_le_sum; intro j hj
      apply Finset.sum_le_sum; intro r hr
      exact hterm a b j r hj hr
    _ ≤ 16 * (B * (6 : ℝ) ^ K) ^ 2 := by
      have hpSum : ∑ j ∈ Finset.range (K - 1), c j * p ^ (j + 2) ≤
          B * (6 : ℝ) ^ K := by
        exact shiftedCoefficient_weighted_sum_le_of_le (show 0 < K by omega) hB hp0 (by dsimp [p]; linarith)
      have hp'Sum : ∑ r ∈ Finset.range (K - 1), c r * p' ^ (r + 2) ≤
          B * (6 : ℝ) ^ K := shiftedCoefficient_weighted_sum_le_of_le (show 0 < K by omega) hB hp'0 hp'B
      have hxSum (r : ℕ) (hr : r ∈ Finset.range (K - 1)) :
          ∑ j ∈ Finset.range (K - 1),
            c j * (p' + (r + 2 : ℕ) / m) ^ (j + 2) ≤
            B * (6 : ℝ) ^ K :=
        shiftedCoefficient_weighted_sum_le_of_le (show 0 < K by omega) hB (by positivity) (hvm r hr)
      have he : Real.exp 1 ≤ 3 := by
        exact Real.exp_one_lt_d9.le.trans (by norm_num)
      have hR0 : 0 ≤ B * (6 : ℝ) ^ K := by positivity
      have hA0 : 0 ≤ ∑ j ∈ Finset.range (K - 1), c j * p ^ (j + 2) :=
        Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (pow_nonneg hp0 _)
      have hfirst :
          (1 / 2 : ℝ) *
            (∑ j ∈ Finset.range (K - 1), c j * p ^ (j + 2)) *
            (∑ r ∈ Finset.range (K - 1), c r * p ^ (r + 2)) ≤
            (1 / 2 : ℝ) * (B * 6 ^ K) ^ 2 := by
        calc
          _ ≤ (1 / 2 : ℝ) * (B * 6 ^ K) *
              (∑ r ∈ Finset.range (K - 1), c r * p ^ (r + 2)) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hpSum (by norm_num)) hA0
          _ ≤ (1 / 2 : ℝ) * (B * 6 ^ K) * (B * 6 ^ K) := by
            exact mul_le_mul_of_nonneg_left hpSum
              (mul_nonneg (by norm_num) hR0)
          _ = _ := by ring
      have hsecond :
          ∑ r ∈ Finset.range (K - 1),
            c r * (Real.exp 1 * p' ^ (r + 2) *
              (∑ j ∈ Finset.range (K - 1),
                c j * (p' + (r + 2 : ℕ) / m) ^ (j + 2))) ≤
            3 * (B * 6 ^ K) ^ 2 := by
        calc
          _ ≤ ∑ r ∈ Finset.range (K - 1),
              c r * (3 * p' ^ (r + 2) * (B * 6 ^ K)) := by
            apply Finset.sum_le_sum
            intro r hr
            have hc0 : 0 ≤ c r := abs_nonneg _
            have hpw0 : 0 ≤ p' ^ (r + 2) := pow_nonneg hp'0 _
            have hx0 : 0 ≤ ∑ j ∈ Finset.range (K - 1),
                c j * (p' + (r + 2 : ℕ) / m) ^ (j + 2) :=
              Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (by positivity)
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul
                (mul_le_mul_of_nonneg_right he hpw0)
                (hxSum r hr) hx0 (mul_nonneg (by positivity) hpw0)) hc0
          _ = 3 * (B * 6 ^ K) *
              (∑ r ∈ Finset.range (K - 1), c r * p' ^ (r + 2)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro r hr
            ring
          _ ≤ 3 * (B * 6 ^ K) ^ 2 := by
            rw [pow_two]
            calc
              _ ≤ (3 * (B * 6 ^ K)) * (B * 6 ^ K) :=
                mul_le_mul_of_nonneg_left hp'Sum
                  (show (0 : ℝ) ≤ 3 * (B * 6 ^ K) by positivity)
              _ = _ := by ring
      have hdegree :
          (∑ j ∈ Finset.range (K - 1), ∑ r ∈ Finset.range (K - 1),
              c j * c r * ((1 / 2 : ℝ) * p ^ (j + 2) * p ^ (r + 2) +
                Real.exp 1 * p' ^ (r + 2) *
                  (p' + (r + 2 : ℕ) / m) ^ (j + 2))) =
            (1 / 2 : ℝ) *
                (∑ j ∈ Finset.range (K - 1), c j * p ^ (j + 2)) *
                (∑ r ∈ Finset.range (K - 1), c r * p ^ (r + 2)) +
              ∑ r ∈ Finset.range (K - 1),
                c r * (Real.exp 1 * p' ^ (r + 2) *
                  (∑ j ∈ Finset.range (K - 1),
                    c j * (p' + (r + 2 : ℕ) / m) ^ (j + 2))) := by
        simp_rw [mul_add, Finset.sum_add_distrib]
        congr 1
        · calc
            (∑ j ∈ Finset.range (K - 1), ∑ r ∈ Finset.range (K - 1),
                c j * c r * ((1 / 2 : ℝ) * p ^ (j + 2) * p ^ (r + 2))) =
                ∑ j ∈ Finset.range (K - 1),
                  ((1 / 2 : ℝ) * c j * p ^ (j + 2)) *
                    (∑ r ∈ Finset.range (K - 1), c r * p ^ (r + 2)) := by
              apply Finset.sum_congr rfl
              intro j hj
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro r hr
              ring
            _ = _ := by
              rw [← Finset.sum_mul]
              congr 1
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j hj
              ring
        · rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro r hr
          rw [Finset.mul_sum]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          ring
      have hrewrite :
          (∑ _a : Bool, ∑ _b : Bool,
            ∑ j ∈ Finset.range (K - 1), ∑ r ∈ Finset.range (K - 1),
              c j * c r * ((1 / 2 : ℝ) * p ^ (j + 2) * p ^ (r + 2) +
                Real.exp 1 * p' ^ (r + 2) *
                  (p' + (r + 2 : ℕ) / m) ^ (j + 2))) =
            4 * ((1 / 2 : ℝ) *
                (∑ j ∈ Finset.range (K - 1), c j * p ^ (j + 2)) *
                (∑ r ∈ Finset.range (K - 1), c r * p ^ (r + 2)) +
              ∑ r ∈ Finset.range (K - 1),
                c r * (Real.exp 1 * p' ^ (r + 2) *
                  (∑ j ∈ Finset.range (K - 1),
                    c j * (p' + (r + 2 : ℕ) / m) ^ (j + 2)))) := by
        simp only [hdegree, Finset.sum_const]
        rw [show Finset.univ.card = 2 by decide]
        norm_num
        ring
      rw [hrewrite]
      nlinarith

end CausalSmith.Stat.DiscreteAteHeterogeneityFrontier
