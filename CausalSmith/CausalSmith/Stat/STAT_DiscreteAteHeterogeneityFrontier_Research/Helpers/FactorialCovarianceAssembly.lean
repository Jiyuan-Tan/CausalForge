/- Final partial-matching assembly for the marked-factorial covariance bound. -/

import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Helpers.FactorialCovarianceSameCell

namespace CausalSmith.Stat.DiscreteAteHeterogeneityFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators

-- @node: centeredCrossMoment_allBlockOrderedMarkedFactorial_cell_ne_abs_le
/-- If [the two cells are distinct](hyp:hkl) and [the first factorial order is admissible](hyp:hj)
  and [the second factorial order is admissible](hyp:hr) and [the stated condition on the source
  size or matching order holds](hyp:hm), [for different cells every positive partial matching is
  incompatible, so only the disjoint-tuple normalization correction remains](goal). -/
lemma centeredCrossMoment_allBlockOrderedMarkedFactorial_cell_ne_abs_le
    {d m K : ℕ} {epsilon M sigma : ℝ}
    (P : ModelClass d epsilon M sigma) (k l : Fin d) (hkl : k ≠ l)
    (a b : Bool) (j r : ℕ) (hj : j + 2 ≤ K) (hr : r + 2 ≤ K)
    (hm : 4 * (K + 2) ^ 2 ≤ m) :
    |Causalean.Stat.centeredCrossMoment
      (Measure.infinitePi fun _ : ℕ => P.law.observedLaw)
      (fun ω : ℕ → Obs d =>
        allBlockOrderedMarkedFactorial M (fun i : Fin m => ω i) k a j)
      (fun ω : ℕ → Obs d =>
        allBlockOrderedMarkedFactorial M (fun i : Fin m => ω i) l b r)| ≤
      (2 * ((K + 2 : ℕ) : ℝ) ^ 2 / m) *
        P.law.cellMass k ^ (j + 2) * P.law.cellMass l ^ (r + 2) := by
  classical
  rw [centeredCrossMoment_allBlockOrderedMarkedFactorial P k l a b j r hj hr hm]
  have hpositive :
      (∑ h ∈ (Finset.range (min (j + 2) (r + 2) + 1)).filter
          (fun h => 0 < h),
        ∑ N ∈ Causalean.Stat.partialMatchingsOfSize (j + 2) (r + 2) h,
          Causalean.Stat.matchingNormalization m N *
            Causalean.Stat.mergedProductMoment P.law.observedLaw
              (markedFactorialCoordinate M k a j)
              (markedFactorialCoordinate M l b r) N) = 0 := by
    apply Finset.sum_eq_zero
    intro h hh
    apply Finset.sum_eq_zero
    intro N hN
    have hhpos : 0 < h := (Finset.mem_filter.mp hh).2
    have hsize : N.size = h := by
      simpa [Causalean.Stat.partialMatchingsOfSize] using hN
    rw [mergedProductMoment_markedFactorialCoordinate_eq_zero_of_cell_ne
      P.law.observedLaw M k l a b j r N (hsize.symm ▸ hhpos) hkl, mul_zero]
  rw [hpositive, add_zero, abs_mul, abs_mul]
  have hnorm := marked_emptyMatchingNormalization_sub_one_le hj hr hm
  have hkmean := orderedProductMean_markedFactorialCoordinate_abs_le P a k j
  have hlmean := orderedProductMean_markedFactorialCoordinate_abs_le P b l r
  have hmpos : (0 : ℝ) < m := by
    exact_mod_cast (lt_of_lt_of_le (by positivity : 0 < 4 * (K + 2) ^ 2) hm)
  have hnormR : 0 ≤ 2 * ((K + 2 : ℕ) : ℝ) ^ 2 / m := by positivity
  have hk0 := P.law.cellMass_range k |>.1
  have hfactor : 0 ≤
      (2 * ((K + 2 : ℕ) : ℝ) ^ 2 / m) *
        P.law.cellMass k ^ (j + 2) :=
    mul_nonneg hnormR (pow_nonneg hk0 _)
  exact mul_le_mul
    (mul_le_mul hnorm hkmean (abs_nonneg _) hnormR) hlmean
    (abs_nonneg _) hfactor

-- @node: weighted_centeredCrossMoment_cell_ne_sum_le
/-- If [the two cells are distinct](hyp:hkl) and [the polynomial or elbow parameter satisfies its
  stated bound](hyp:hK) and [the outcome bound is positive](hyp:hB) and [the stated condition on
  the cell holds](hyp:hk) and [the stated l condition holds](hyp:hl) and [the stated condition on
  the source size or matching order holds](hyp:hm), [summing the different-cell correction over
  both arms and all polynomial degrees gives the required `K²/m` cross-cell scale](goal). -/
lemma weighted_centeredCrossMoment_cell_ne_sum_le
    {d m K : ℕ} {epsilon M sigma B : ℝ}
    (P : ModelClass d epsilon M sigma) (k l : Fin d) (hkl : k ≠ l)
    (hK : 2 ≤ K) (hB : 0 < B)
    (hk : P.law.cellMass k ≤ B / 4)
    (hl : P.law.cellMass l ≤ B / 4)
    (hm : 4 * (K + 2) ^ 2 ≤ m) :
    ∑ a : Bool, ∑ b : Bool,
      ∑ j ∈ Finset.range (K - 1), ∑ r ∈ Finset.range (K - 1),
        |shiftedCoefficient K j / B ^ (j + 1)| *
          |shiftedCoefficient K r / B ^ (r + 1)| *
          |Causalean.Stat.centeredCrossMoment
            (Measure.infinitePi fun _ : ℕ => P.law.observedLaw)
            (fun ω : ℕ → Obs d =>
              allBlockOrderedMarkedFactorial M (fun i : Fin m => ω i) k a j)
            (fun ω : ℕ → Obs d =>
              allBlockOrderedMarkedFactorial M (fun i : Fin m => ω i) l b r)| ≤
      32 * (K : ℝ) ^ 2 / m * (B * (6 : ℝ) ^ K) ^ 2 := by
  classical
  let q : ℝ := 2 * ((K + 2 : ℕ) : ℝ) ^ 2 / m
  let A : ℕ → ℝ := fun j =>
    |shiftedCoefficient K j / B ^ (j + 1)| *
      P.law.cellMass k ^ (j + 2)
  let D : ℕ → ℝ := fun r =>
    |shiftedCoefficient K r / B ^ (r + 1)| *
      P.law.cellMass l ^ (r + 2)
  have hterm (a b : Bool) (j r : ℕ)
      (hj : j ∈ Finset.range (K - 1)) (hr : r ∈ Finset.range (K - 1)) :
      |shiftedCoefficient K j / B ^ (j + 1)| *
          |shiftedCoefficient K r / B ^ (r + 1)| *
          |Causalean.Stat.centeredCrossMoment
            (Measure.infinitePi fun _ : ℕ => P.law.observedLaw)
            (fun ω : ℕ → Obs d =>
              allBlockOrderedMarkedFactorial M (fun i : Fin m => ω i) k a j)
            (fun ω : ℕ → Obs d =>
              allBlockOrderedMarkedFactorial M (fun i : Fin m => ω i) l b r)| ≤
        q * A j * D r := by
    have hjK : j + 2 ≤ K := by
      have := Finset.mem_range.mp hj
      omega
    have hrK : r + 2 ≤ K := by
      have := Finset.mem_range.mp hr
      omega
    have hc := centeredCrossMoment_allBlockOrderedMarkedFactorial_cell_ne_abs_le
      P k l hkl a b j r hjK hrK hm
    dsimp only [q, A, D]
    calc
      _ ≤ |shiftedCoefficient K j / B ^ (j + 1)| *
          |shiftedCoefficient K r / B ^ (r + 1)| *
          ((2 * ((K + 2 : ℕ) : ℝ) ^ 2 / m) *
            P.law.cellMass k ^ (j + 2) *
            P.law.cellMass l ^ (r + 2)) := by
        gcongr
      _ = _ := by ring
  have hkSum : ∑ j ∈ Finset.range (K - 1), A j ≤ B * (6 : ℝ) ^ K := by
    exact shiftedCoefficient_weighted_cellMass_sum_le
      (show 0 < K by omega) hB (P.law.cellMass_range k).1 hk
  have hlSum : ∑ r ∈ Finset.range (K - 1), D r ≤ B * (6 : ℝ) ^ K := by
    exact shiftedCoefficient_weighted_cellMass_sum_le
      (show 0 < K by omega) hB (P.law.cellMass_range l).1 hl
  have hmpos : (0 : ℝ) < m := by
    exact_mod_cast (lt_of_lt_of_le (by positivity : 0 < 4 * (K + 2) ^ 2) hm)
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hA0 : ∀ j, 0 ≤ A j := fun j => by
    exact mul_nonneg (abs_nonneg _) (pow_nonneg (P.law.cellMass_range k).1 _)
  have hD0 : ∀ r, 0 ≤ D r := fun r => by
    exact mul_nonneg (abs_nonneg _) (pow_nonneg (P.law.cellMass_range l).1 _)
  have hAsum0 : 0 ≤ ∑ j ∈ Finset.range (K - 1), A j :=
    Finset.sum_nonneg fun j _ => hA0 j
  have hDsum0 : 0 ≤ ∑ r ∈ Finset.range (K - 1), D r :=
    Finset.sum_nonneg fun r _ => hD0 r
  have hsum :
      (∑ j ∈ Finset.range (K - 1), ∑ r ∈ Finset.range (K - 1),
          q * A j * D r) =
        q * (∑ j ∈ Finset.range (K - 1), A j) *
          (∑ r ∈ Finset.range (K - 1), D r) := by
    calc
      _ = ∑ j ∈ Finset.range (K - 1),
          (q * A j) * (∑ r ∈ Finset.range (K - 1), D r) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact (Finset.mul_sum (s := Finset.range (K - 1))
          (f := D) (q * A j)).symm
      _ = (∑ j ∈ Finset.range (K - 1), q * A j) *
          (∑ r ∈ Finset.range (K - 1), D r) := by
        exact (Finset.sum_mul (s := Finset.range (K - 1))
          (f := fun j => q * A j)
          (∑ r ∈ Finset.range (K - 1), D r)).symm
      _ = _ := by
        congr 1
        exact (Finset.mul_sum (s := Finset.range (K - 1)) (f := A) q).symm
  calc
    _ ≤ ∑ _a : Bool, ∑ _b : Bool,
        ∑ j ∈ Finset.range (K - 1), ∑ r ∈ Finset.range (K - 1),
          q * A j * D r := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro r hr
      exact hterm a b j r hj hr
    _ = 4 * q * (∑ j ∈ Finset.range (K - 1), A j) *
        (∑ r ∈ Finset.range (K - 1), D r) := by
      simp only [hsum, Finset.sum_const]
      rw [show Finset.univ.card = 2 by decide]
      norm_num
      ring
    _ ≤ 4 * q * (B * (6 : ℝ) ^ K) * (B * (6 : ℝ) ^ K) := by
      have hR0 : 0 ≤ B * (6 : ℝ) ^ K := by positivity
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hkSum (mul_nonneg (by positivity) hq0))
        hlSum hDsum0 (mul_nonneg (mul_nonneg (by positivity) hq0) hR0)
    _ ≤ 32 * (K : ℝ) ^ 2 / m * (B * (6 : ℝ) ^ K) ^ 2 := by
      dsimp [q]
      have hK2 : ((K + 2 : ℕ) : ℝ) ^ 2 ≤ 4 * (K : ℝ) ^ 2 := by
        push_cast
        have hKreal : (2 : ℝ) ≤ K := by exact_mod_cast hK
        nlinarith
      have hcoef :
          4 * (2 * ((K + 2 : ℕ) : ℝ) ^ 2 / m) ≤
            32 * (K : ℝ) ^ 2 / m := by
        rw [show 4 * (2 * ((K + 2 : ℕ) : ℝ) ^ 2 / (m : ℝ)) =
          (8 * ((K + 2 : ℕ) : ℝ) ^ 2) / m by ring]
        apply (div_le_div_iff_of_pos_right hmpos).2
        nlinarith
      rw [pow_two (B * (6 : ℝ) ^ K)]
      calc
        4 * (2 * ((K + 2 : ℕ) : ℝ) ^ 2 / m) *
            (B * 6 ^ K) * (B * 6 ^ K) =
            (4 * (2 * ((K + 2 : ℕ) : ℝ) ^ 2 / m)) *
              ((B * 6 ^ K) * (B * 6 ^ K)) := by ring
        _ ≤ (32 * (K : ℝ) ^ 2 / m) *
              ((B * 6 ^ K) * (B * 6 ^ K)) :=
          mul_le_mul_of_nonneg_right hcoef (mul_self_nonneg _)

-- @node: memLp_allBlockOrderedMarkedFactorial
/-- [every all-block ordered marked factorial statistic has a finite second moment](goal). -/
lemma memLp_allBlockOrderedMarkedFactorial {d m : ℕ} {epsilon M sigma : ℝ}
    (P : ModelClass d epsilon M sigma) (k : Fin d) (a : Bool) (j : ℕ) :
    MemLp (fun ω : ℕ → Obs d =>
      allBlockOrderedMarkedFactorial M (fun i : Fin m => ω i) k a j) 2
      (Measure.infinitePi fun _ : ℕ => P.law.observedLaw) := by
  let S0 := Causalean.Stat.iidSample_infinitePi P.law.observedLaw
  have hk : MemLp (Causalean.Stat.orderedProductKernel
      (markedFactorialCoordinate M k a j)) 2
      (Measure.pi fun _ : Fin (j + 2) => P.law.observedLaw) :=
    memLp_two_orderedProductKernel_markedFactorialCoordinate P k a j
  have hsum := S0.memLp_injectiveTuples_sum
    (measurable_orderedProductKernel_markedFactorialCoordinate M k a j)
    hk.integrable_sq m
  have hnorm : MemLp (Causalean.Stat.normalizedOrderedProductStatistic S0
      (markedFactorialCoordinate M k a j) m) 2
      (Measure.infinitePi fun _ : ℕ => P.law.observedLaw) := by
    unfold Causalean.Stat.normalizedOrderedProductStatistic
      Causalean.Stat.normalizedFiniteKernelStatistic
    refine (hsum.const_mul ((m.descFactorial (j + 2) : ℝ)⁻¹)).ae_eq ?_
    filter_upwards with ω
    have ht : Causalean.Stat.finiteInjectiveTuples (Fin (j + 2)) m =
        Causalean.Stat.injectiveTuples (j + 2) m := by
      ext t
      simp [Causalean.Stat.finiteInjectiveTuples,
        Causalean.Stat.injectiveTuples]
    rw [Fintype.card_fin, ht]
  convert hnorm using 1
  funext ω
  exact allBlockOrderedMarkedFactorial_eq_normalizedOrderedProductStatistic
    (m := m) S0 M k a j ω

-- @node: memLp_allBlockLightPolynomialTerm
/-- [every all-block light polynomial term has a finite second moment](goal). -/
lemma memLp_allBlockLightPolynomialTerm {d m K : ℕ} {epsilon M sigma B : ℝ}
    (P : ModelClass d epsilon M sigma) (k : Fin d) :
    MemLp (fun ω : ℕ → Obs d =>
      allBlockLightPolynomialTerm M B K (fun i : Fin m => ω i) k) 2
      (Measure.infinitePi fun _ : ℕ => P.law.observedLaw) := by
  unfold allBlockLightPolynomialTerm
  apply memLp_finset_sum
  intro j hj
  exact ((memLp_allBlockOrderedMarkedFactorial P k true j).sub (memLp_allBlockOrderedMarkedFactorial P k false j)).const_mul _

-- @node: covariance_allBlockLightPolynomialTerm_abs_le
/-- [the absolute covariance between two all-block light polynomial terms satisfies the stated
  bound](goal). -/
lemma covariance_allBlockLightPolynomialTerm_abs_le {d m K : ℕ} {epsilon M sigma B : ℝ}
    (P : ModelClass d epsilon M sigma) (k l : Fin d) :
    |covariance
      (fun ω : ℕ → Obs d =>
        allBlockLightPolynomialTerm M B K (fun i : Fin m => ω i) k)
      (fun ω : ℕ → Obs d =>
        allBlockLightPolynomialTerm M B K (fun i : Fin m => ω i) l)
      (Measure.infinitePi fun _ : ℕ => P.law.observedLaw)| ≤
      ∑ a : Bool, ∑ b : Bool,
        ∑ j ∈ Finset.range (K - 1), ∑ r ∈ Finset.range (K - 1),
          |shiftedCoefficient K j / B ^ (j + 1)| *
            |shiftedCoefficient K r / B ^ (r + 1)| *
            |Causalean.Stat.centeredCrossMoment
              (Measure.infinitePi fun _ : ℕ => P.law.observedLaw)
              (fun ω : ℕ → Obs d =>
                allBlockOrderedMarkedFactorial M (fun i : Fin m => ω i) k a j)
              (fun ω : ℕ → Obs d =>
                allBlockOrderedMarkedFactorial M (fun i : Fin m => ω i) l b r)| := by
  classical
  let μ := Measure.infinitePi fun _ : ℕ => P.law.observedLaw
  let U := fun (k : Fin d) (a : Bool) (j : ℕ) (ω : ℕ → Obs d) =>
    allBlockOrderedMarkedFactorial M (fun i : Fin m => ω i) k a j
  let c := fun j : ℕ => shiftedCoefficient K j / B ^ (j + 1)
  have hU (q : Fin d) (a : Bool) (j : ℕ) : MemLp (U q a j) 2 μ :=
    memLp_allBlockOrderedMarkedFactorial P q a j
  have hsum (q : Fin d) :
      (fun ω : ℕ → Obs d =>
        allBlockLightPolynomialTerm M B K (fun i : Fin m => ω i) q) =
        fun ω => ∑ j ∈ Finset.range (K - 1), c j * (U q true j ω - U q false j ω) := by
    rfl
  rw [hsum k, hsum l]
  have hterm (q : Fin d) (j : ℕ) :
      MemLp (fun ω => c j * (U q true j ω - U q false j ω)) 2 μ :=
    ((hU q true j).sub (hU q false j)).const_mul _
  rw [covariance_fun_sum_fun_sum'
    (fun j _ => hterm k j) (fun r _ => hterm l r)]
  calc
    _ ≤ ∑ j ∈ Finset.range (K - 1), ∑ r ∈ Finset.range (K - 1),
        |covariance (fun ω => c j * (U k true j ω - U k false j ω))
          (fun ω => c r * (U l true r ω - U l false r ω)) μ| :=
      Finset.abs_sum_le_sum_abs _ _ |>.trans
        (Finset.sum_le_sum fun j hj => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ j ∈ Finset.range (K - 1), ∑ r ∈ Finset.range (K - 1),
        ∑ a : Bool, ∑ b : Bool,
          |shiftedCoefficient K j / B ^ (j + 1)| *
            |shiftedCoefficient K r / B ^ (r + 1)| *
            |Causalean.Stat.centeredCrossMoment
              (Measure.infinitePi fun _ : ℕ => P.law.observedLaw)
              (fun ω : ℕ → Obs d =>
                allBlockOrderedMarkedFactorial M (fun i : Fin m => ω i) k a j)
              (fun ω : ℕ → Obs d =>
                allBlockOrderedMarkedFactorial M (fun i : Fin m => ω i) l b r)| := by
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro r hr
      rw [covariance_const_mul_left, covariance_const_mul_right,
        abs_mul, abs_mul]
      have hsub := covariance_sub_sub (hU k true j) (hU k false j)
        (hU l true r) (hU l false r)
      change |c j| * (|c r| *
        |covariance (U k true j - U k false j)
          (U l true r - U l false r) μ|) ≤ _
      rw [hsub]
      have hfour :
          |covariance (U k true j) (U l true r) μ -
              covariance (U k true j) (U l false r) μ -
              covariance (U k false j) (U l true r) μ +
              covariance (U k false j) (U l false r) μ| ≤
            ∑ a : Bool, ∑ b : Bool,
              |Causalean.Stat.centeredCrossMoment μ (U k a j) (U l b r)| := by
        let A := covariance (U k true j) (U l true r) μ
        let B0 := covariance (U k true j) (U l false r) μ
        let C := covariance (U k false j) (U l true r) μ
        let D := covariance (U k false j) (U l false r) μ
        have hAB : |A - B0| ≤ |A| + |B0| := by
          simpa [sub_eq_add_neg] using abs_add_le A (-B0)
        have hABC : |A - B0 - C| ≤ (|A| + |B0|) + |C| := by
          have h0 : |A - B0 - C| ≤ |A - B0| + |C| := by
            simpa [sub_eq_add_neg] using abs_add_le (A - B0) (-C)
          exact h0.trans (add_le_add hAB le_rfl)
        have htri : |A - B0 - C + D| ≤ ((|A| + |B0|) + |C|) + |D| :=
          (abs_add_le _ _).trans (add_le_add hABC le_rfl)
        have hsumEq :
            (∑ a : Bool, ∑ b : Bool,
              |Causalean.Stat.centeredCrossMoment μ (U k a j) (U l b r)|) =
              |A| + |B0| + (|C| + |D|) := by
          simp [A, B0, C, D, Causalean.Stat.centeredCrossMoment,
            covariance_eq_sub (hU k true j) (hU l true r),
            covariance_eq_sub (hU k true j) (hU l false r),
            covariance_eq_sub (hU k false j) (hU l true r),
            covariance_eq_sub (hU k false j) (hU l false r)]
        rw [hsumEq]
        dsimp [A, B0, C, D] at htri ⊢
        convert htri using 1 <;> ring
      rw [← mul_assoc]
      calc
        |c j| * |c r| *
            |covariance (U k true j) (U l true r) μ -
              covariance (U k true j) (U l false r) μ -
              covariance (U k false j) (U l true r) μ +
              covariance (U k false j) (U l false r) μ| ≤
            |c j| * |c r| *
              (∑ a : Bool, ∑ b : Bool,
                |Causalean.Stat.centeredCrossMoment μ (U k a j) (U l b r)|) := by
          gcongr
        _ = ∑ a : Bool, ∑ b : Bool,
            |c j| * |c r| *
              |Causalean.Stat.centeredCrossMoment μ (U k a j) (U l b r)| := by
          simp only [Finset.mul_sum]
    _ = _ := by
      calc
        _ = ∑ j ∈ Finset.range (K - 1), ∑ a : Bool,
            ∑ r ∈ Finset.range (K - 1), ∑ b : Bool,
              |shiftedCoefficient K j / B ^ (j + 1)| *
                |shiftedCoefficient K r / B ^ (r + 1)| *
                |Causalean.Stat.centeredCrossMoment μ (U k a j) (U l b r)| := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.sum_comm]
        _ = ∑ a : Bool, ∑ j ∈ Finset.range (K - 1),
            ∑ r ∈ Finset.range (K - 1), ∑ b : Bool,
              |shiftedCoefficient K j / B ^ (j + 1)| *
                |shiftedCoefficient K r / B ^ (r + 1)| *
                |Causalean.Stat.centeredCrossMoment μ (U k a j) (U l b r)| := by
          rw [Finset.sum_comm]
        _ = ∑ a : Bool, ∑ j ∈ Finset.range (K - 1), ∑ b : Bool,
            ∑ r ∈ Finset.range (K - 1),
              |shiftedCoefficient K j / B ^ (j + 1)| *
                |shiftedCoefficient K r / B ^ (r + 1)| *
                |Causalean.Stat.centeredCrossMoment μ (U k a j) (U l b r)| := by
          apply Finset.sum_congr rfl
          intro a ha
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.sum_comm]
        _ = _ := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [Finset.sum_comm]


-- @node: lem:linear-mark-factorial-covariance
/-- [Under only the conditional second-moment envelope, a deterministic collection of signed
  one-mark ordered factorial statistics has the covariance bound used by the heavy/light
  estimator](goal). -/
lemma linear_mark_factorial_covariance :
    ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 / 2 →
    ∃ C_epsilon : ℝ, 0 < C_epsilon ∧
    ∀ d m K : ℕ, ∀ M sigma B : ℝ,
      ∀ P : ModelClass d epsilon M sigma, ∀ S : Finset (Fin d),
      2 ≤ K → 0 < B →
      (∀ k ∈ S, P.law.cellMass k ≤ B / 4) →
      4 * (K + 2) ^ 2 ≤ m →
      (4 : ℝ) * (K + 2) / m ≤ 3 * B / 4 →
      variance (allBlockMarkedPolynomialSum M B K S) (productLaw m P.law) ≤
        C_epsilon / m + C_epsilon * 6 ^ (2 * K) *
          ((d : ℝ) * B ^ 2 + (d : ℝ) ^ 2 * K ^ 2 * B ^ 2 / m) := by
  intro epsilon hepsilon hepsilon_half
  refine ⟨64, by norm_num, ?_⟩
  intro d m K M sigma B P S hK hB hlight hm hshift
  let μ := Measure.infinitePi fun _ : ℕ => P.law.observedLaw
  let F := fun (k : Fin d) (ω : ℕ → Obs d) =>
    allBlockLightPolynomialTerm M B K (fun i : Fin m => ω i) k
  have hmem (k : Fin d) : MemLp (F k) 2 μ := memLp_allBlockLightPolynomialTerm P k
  have hsame (k : Fin d) (hk : k ∈ S) :
      |covariance (F k) (F k) μ| ≤ 16 * (B * (6 : ℝ) ^ K) ^ 2 := by
    exact (covariance_allBlockLightPolynomialTerm_abs_le P k k).trans
      (weighted_centeredCrossMoment_same_cell_sum_le P k hK hB
        (hlight k hk) hm hshift)
  have hdiff (k l : Fin d) (hk : k ∈ S) (hl : l ∈ S) (hkl : k ≠ l) :
      |covariance (F k) (F l) μ| ≤
        32 * (K : ℝ) ^ 2 / m * (B * (6 : ℝ) ^ K) ^ 2 := by
    exact (covariance_allBlockLightPolynomialTerm_abs_le P k l).trans
      (weighted_centeredCrossMoment_cell_ne_sum_le P k l hkl hK hB
        (hlight k hk) (hlight l hl) hm)
  change variance (allBlockMarkedPolynomialSum M B K S)
      (Measure.pi fun _ : Fin m => P.law.observedLaw) ≤ _
  rw [variance_allBlockMarkedPolynomialSum_eq_infinitePi P.law.observedLaw M B K S]
  change variance (fun ω => ∑ k ∈ S, F k ω) μ ≤ _
  rw [variance_fun_sum' (fun k hk => hmem k)]
  have hcard : (S.card : ℝ) ≤ d := by
    have hcNat : S.card ≤ d := by simpa using S.card_le_univ
    exact_mod_cast hcNat
  have hcard0 : (0 : ℝ) ≤ S.card := by positivity
  have hd0 : (0 : ℝ) ≤ d := by positivity
  have hmpos : (0 : ℝ) < m := by
    exact_mod_cast (lt_of_lt_of_le (by positivity : 0 < 4 * (K + 2) ^ 2) hm)
  have hR0 : 0 ≤ (B * (6 : ℝ) ^ K) ^ 2 := sq_nonneg _
  calc
    (∑ k ∈ S, ∑ l ∈ S, covariance (F k) (F l) μ) ≤
        ∑ k ∈ S, ∑ l ∈ S, |covariance (F k) (F l) μ| := by
      apply Finset.sum_le_sum
      intro k hk
      apply Finset.sum_le_sum
      intro l hl
      exact le_abs_self _
    _ = ∑ k ∈ S, (|covariance (F k) (F k) μ| +
          ∑ l ∈ S.erase k, |covariance (F k) (F l) μ|) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [← Finset.add_sum_erase _ _ hk]
    _ ≤ ∑ _k ∈ S, (16 * (B * (6 : ℝ) ^ K) ^ 2 +
          (d : ℝ) * (32 * (K : ℝ) ^ 2 / m *
            (B * (6 : ℝ) ^ K) ^ 2)) := by
      apply Finset.sum_le_sum
      intro k hk
      apply add_le_add (hsame k hk)
      calc
        (∑ l ∈ S.erase k, |covariance (F k) (F l) μ|) ≤
            ∑ _l ∈ S.erase k,
              32 * (K : ℝ) ^ 2 / m * (B * (6 : ℝ) ^ K) ^ 2 := by
          exact Finset.sum_le_sum fun l hl =>
            hdiff k l hk (Finset.mem_of_mem_erase hl)
              (Finset.ne_of_mem_erase hl).symm
        _ = ((S.erase k).card : ℝ) *
              (32 * (K : ℝ) ^ 2 / m * (B * (6 : ℝ) ^ K) ^ 2) := by
          simp
        _ ≤ (d : ℝ) *
              (32 * (K : ℝ) ^ 2 / m * (B * (6 : ℝ) ^ K) ^ 2) := by
          gcongr
          exact_mod_cast (calc (S.erase k).card ≤ S.card := Finset.card_erase_le
            _ ≤ d := by simpa using S.card_le_univ)
    _ ≤ 16 * (d : ℝ) * (B * (6 : ℝ) ^ K) ^ 2 +
          32 * (d : ℝ) ^ 2 * (K : ℝ) ^ 2 / m *
            (B * (6 : ℝ) ^ K) ^ 2 := by
      simp only [Finset.sum_const]
      push_cast
      have hinside0 : 0 ≤ 16 * (B * (6 : ℝ) ^ K) ^ 2 +
          (d : ℝ) * (32 * (K : ℝ) ^ 2 / m *
            (B * (6 : ℝ) ^ K) ^ 2) := by positivity
      rw [nsmul_eq_mul]
      push_cast
      calc
        (S.card : ℝ) * (16 * (B * 6 ^ K) ^ 2 +
            (d : ℝ) * (32 * (K : ℝ) ^ 2 / m * (B * 6 ^ K) ^ 2)) ≤
            (d : ℝ) * (16 * (B * 6 ^ K) ^ 2 +
              (d : ℝ) * (32 * (K : ℝ) ^ 2 / m *
                (B * 6 ^ K) ^ 2)) :=
          mul_le_mul_of_nonneg_right hcard hinside0
        _ = _ := by ring
    _ ≤ 64 / m + 64 * 6 ^ (2 * K) *
          ((d : ℝ) * B ^ 2 + (d : ℝ) ^ 2 * K ^ 2 * B ^ 2 / m) := by
      have hpow : ((6 : ℝ) ^ K) ^ 2 = 6 ^ (2 * K) := by
        rw [← pow_mul]
        congr 1
        omega
      rw [mul_pow, hpow]
      have hA0 : 0 ≤ (d : ℝ) * B ^ 2 := by positivity
      have hC0 : 0 ≤ (d : ℝ) ^ 2 * (K : ℝ) ^ 2 * B ^ 2 / m := by
        positivity
      have hsix0 : 0 ≤ (6 : ℝ) ^ (2 * K) := by positivity
      have ht1 : 0 ≤ (d : ℝ) * B ^ 2 * 6 ^ (K * 2) := by positivity
      have ht2 : 0 ≤ (d : ℝ) ^ 2 * B ^ 2 * (K : ℝ) ^ 2 *
          (m : ℝ)⁻¹ * 6 ^ (K * 2) := by positivity
      have hminv : 0 ≤ (m : ℝ)⁻¹ := by positivity
      ring_nf
      nlinarith

  -- @realizes Q_P^{(m)}(variance under the m-fold observed product law)
  -- @realizes m(block size for the factorial statistic)

end CausalSmith.Stat.DiscreteAteHeterogeneityFrontier
