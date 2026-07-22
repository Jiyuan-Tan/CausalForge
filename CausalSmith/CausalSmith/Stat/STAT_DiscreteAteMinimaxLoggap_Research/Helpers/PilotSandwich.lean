import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.Estimator
import Causalean.Stat.Concentration.TailBounds.Bernstein
import Causalean.Stat.Concentration.TailBounds.Hoeffding
import Causalean.Stat.Sample.PiTransport
import Causalean.Stat.Concentration.TailBounds.BinomialCount
import Mathlib.Probability.ProbabilityMassFunction.Integrals

namespace CausalSmith.Stat.DiscreteAteMinimaxLoggap

open MeasureTheory
open ProbabilityTheory
open scoped BigOperators

-- @node: categoryIndicator
/-- Defines category Indicator, the stated quantity or construction used in the discrete average-treatment-effect estimator. -/
noncomputable def categoryIndicator {d : ℕ} (k : Fin d) (z : Obs d) : ℝ :=
  if z.1 = k then 1 else 0

-- @node: categoryIndicator_mean
/-- Establishes the stated property of category Indicator mean in the discrete average-treatment-effect construction. -/
lemma categoryIndicator_mean {d : ℕ} (P : DiscreteLaw d) (k : Fin d) :
    ∫ z, categoryIndicator k z ∂obsLaw P = cellMass P k := by
  classical
  rw [show obsLaw P = P.pmf.toMeasure by rfl, PMF.integral_eq_sum]
  simp [categoryIndicator, cellMass, jointMass, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _hb hne
    simp [hne]
  · simp

-- @node: pilot_count_eq_bernoulliCount
/-- Establishes the stated equality relating pilot count eq bernoulli Count. -/
lemma pilot_count_eq_bernoulliCount {n d : ℕ} (P : DiscreteLaw d)
    (k : Fin d) (ω : ℕ → Obs d) :
    (splitCategoryCount (fun i : Fin n => ω i) 0 k : ℝ) =
      Causalean.Stat.Concentration.bernoulliCount
        (Causalean.Stat.iidSample_infinitePi (obsLaw P))
        (categoryIndicator k) (n / 2) ω := by
  simp only [splitCategoryCount, splitIndices, if_pos, Finset.mem_filter,
    Finset.mem_univ, true_and,
    Causalean.Stat.Concentration.bernoulliCount, categoryIndicator,
    Causalean.Stat.iidSample_infinitePi, Function.comp_apply]
  have hsum : (∑ x ∈ Finset.range (n / 2),
      if (ω x).1 = k then (1 : ℝ) else 0) =
      ({x ∈ Finset.range (n / 2) | (ω x).1 = k}.card : ℝ) :=
    Finset.sum_boole (R := ℝ) (fun x : ℕ ↦ (ω x).1 = k) (Finset.range (n / 2))
  calc
    ((((Finset.univ : Finset (Fin n)).filter fun i ↦ i.1 < n / 2).filter
        (fun i : Fin n ↦ (ω i).1 = k)).card : ℝ) =
        ((Finset.range (n / 2)).filter (fun x : ℕ ↦ (ω x).1 = k)).card := by
      norm_cast
      apply Finset.card_bij (fun i _hi ↦ i.1)
      · intro i hi
        simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
        exact ⟨hi.1.2, hi.2⟩
      · intro i₁ _hi₁ i₂ _hi₂ heq
        exact Fin.ext heq
      · intro j hj
        simp only [Finset.mem_filter, Finset.mem_range] at hj
        let i : Fin n := ⟨j, lt_of_lt_of_le hj.1 (Nat.div_le_self n 2)⟩
        refine ⟨i, ?_, rfl⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hj.1, hj.2⟩
    _ = ∑ x ∈ Finset.range (n / 2),
        if (ω x).1 = k then (1 : ℝ) else 0 := hsum.symm

-- @node: pilotCategory_upper_tail
/-- Establishes the stated property of pilot Category upper tail in the discrete average-treatment-effect construction. -/
lemma pilotCategory_upper_tail {n d : ℕ} (P : DiscreteLaw d) (k : Fin d)
    {a : ℝ} (hmean_lt : (n / 2 : ℕ) * cellMass P k < a / 2) :
    (productLaw P n).real
      {sample | a < (splitCategoryCount sample 0 k : ℝ)} ≤
        Real.exp (-a * (Real.log 2 - 1 / 2)) := by
  let trunc : (ℕ → Obs d) → (Fin n → Obs d) := fun ω i ↦ ω i
  have htrunc : Measurable trunc := by fun_prop
  have hE : MeasurableSet {sample : Fin n → Obs d |
      a < (splitCategoryCount sample 0 k : ℝ)} := MeasurableSet.of_discrete
  rw [productLaw, ← finProductLaw_eq_map (obsLaw P) n,
    map_measureReal_apply htrunc hE]
  have hpre : trunc ⁻¹' {sample : Fin n → Obs d |
      a < (splitCategoryCount sample 0 k : ℝ)} =
      {ω | a < Causalean.Stat.Concentration.bernoulliCount
        (Causalean.Stat.iidSample_infinitePi (obsLaw P))
        (categoryIndicator k) (n / 2) ω} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_setOf_eq, trunc]
    rw [← pilot_count_eq_bernoulliCount P]
  rw [hpre]
  apply Causalean.Stat.Concentration.bernoulliCount_upper_tail
    (Causalean.Stat.iidSample_infinitePi (obsLaw P))
    (measurable_of_finite _) (fun z ↦ ?_)
    (categoryIndicator_mean P k) hmean_lt
  by_cases hz : z.1 = k <;> simp [categoryIndicator, hz]

-- @node: pilotCategory_lower_tail
/-- Establishes the stated property of pilot Category lower tail in the discrete average-treatment-effect construction. -/
lemma pilotCategory_lower_tail {n d : ℕ} (P : DiscreteLaw d) (k : Fin d)
    {a : ℝ} (hmean_gt : 2 * a < (n / 2 : ℕ) * cellMass P k) :
    (productLaw P n).real
      {sample | (splitCategoryCount sample 0 k : ℝ) ≤ a} ≤
        Real.exp (-((n / 2 : ℕ) * cellMass P k) / 8) := by
  let trunc : (ℕ → Obs d) → (Fin n → Obs d) := fun ω i ↦ ω i
  have htrunc : Measurable trunc := by fun_prop
  have hE : MeasurableSet {sample : Fin n → Obs d |
      (splitCategoryCount sample 0 k : ℝ) ≤ a} := MeasurableSet.of_discrete
  rw [productLaw, ← finProductLaw_eq_map (obsLaw P) n,
    map_measureReal_apply htrunc hE]
  have hpre : trunc ⁻¹' {sample : Fin n → Obs d |
      (splitCategoryCount sample 0 k : ℝ) ≤ a} =
      {ω | Causalean.Stat.Concentration.bernoulliCount
        (Causalean.Stat.iidSample_infinitePi (obsLaw P))
        (categoryIndicator k) (n / 2) ω ≤ a} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_setOf_eq, trunc]
    rw [← pilot_count_eq_bernoulliCount P]
  rw [hpre]
  apply Causalean.Stat.Concentration.bernoulliCount_lower_tail
    (Causalean.Stat.iidSample_infinitePi (obsLaw P))
    (measurable_of_finite _) (fun z ↦ ?_)
    (cellMass_mem_unitInterval P k).1 (categoryIndicator_mean P k) hmean_gt
  by_cases hz : z.1 = k <;> simp [categoryIndicator, hz]

/-- Defines pilot Heavy At, the stated quantity or construction used in the discrete average-treatment-effect estimator. -/
noncomputable def pilotHeavyAt {n d : ℕ} (sample : Fin n → Obs d)
    (t : ℝ) : Finset (Fin d) :=
  Finset.univ.filter
    (fun k => ⌊t * logScale n⌋ < (splitCategoryCount sample 0 k : ℤ))

/-- Defines pilot Bad Event, the stated quantity or construction used in the discrete average-treatment-effect estimator. -/
noncomputable def pilotBadEvent {n d : ℕ} (P : DiscreteLaw d) (t : ℝ) :
    Set (Fin n → Obs d) :=
  {sample |
    ¬ (∀ k ∈ pilotHeavyAt sample t,
          t * logScale n / (2 * splitSize n 0) ≤ cellMass P k) ∨
    ¬ (∀ k ∉ pilotHeavyAt sample t,
          cellMass P k ≤ 2 * t * logScale n / splitSize n 0)}

-- @node: pilotBadEvent_subset_cellwise
/-- Establishes the stated property of pilot Bad Event subset cellwise in the discrete average-treatment-effect construction. -/
lemma pilotBadEvent_subset_cellwise {n d : ℕ} (P : DiscreteLaw d) (t : ℝ) :
    pilotBadEvent P t ⊆
      (⋃ k : Fin d, {sample : Fin n → Obs d |
        cellMass P k < t * logScale n / (2 * splitSize n 0) ∧
        t * logScale n < (splitCategoryCount sample 0 k : ℝ)}) ∪
      (⋃ k : Fin d, {sample : Fin n → Obs d |
        2 * t * logScale n / splitSize n 0 < cellMass P k ∧
        (splitCategoryCount sample 0 k : ℝ) ≤ t * logScale n}) := by
  intro sample hs
  rw [pilotBadEvent] at hs
  rcases hs with hs | hs
  · push_neg at hs
    rcases hs with ⟨k, hk⟩
    rcases hk with ⟨hkHeavy, hkMass⟩
    apply Set.mem_union_left
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    refine ⟨k, hkMass, ?_⟩
    have hcount : ⌊t * logScale n⌋ < (splitCategoryCount sample 0 k : ℤ) := by
      simpa [pilotHeavyAt] using hkHeavy
    exact Int.floor_lt.mp hcount
  · push_neg at hs
    rcases hs with ⟨k, hk⟩
    rcases hk with ⟨hkLight, hkMass⟩
    apply Set.mem_union_right
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    refine ⟨k, hkMass, ?_⟩
    have hnot : ¬ ⌊t * logScale n⌋ < (splitCategoryCount sample 0 k : ℤ) := by
      simpa [pilotHeavyAt] using hkLight
    have hle : (splitCategoryCount sample 0 k : ℤ) ≤ ⌊t * logScale n⌋ :=
      le_of_not_gt hnot
    exact_mod_cast (Int.le_floor.mp hle)

-- @node: pilotBadEvent_probability
/-- Establishes the stated property of pilot Bad Event probability in the discrete average-treatment-effect construction. -/
lemma pilotBadEvent_probability {n d : ℕ} (P : DiscreteLaw d) (t : ℝ)
    (ht : 0 ≤ t) (hn : 2 ≤ n) :
    (productLaw P n).real (pilotBadEvent P t) ≤
      d * (Real.exp (-(t * logScale n) * (Real.log 2 - 1 / 2)) +
        Real.exp (-(t * logScale n) / 4)) := by
  calc
    (productLaw P n).real (pilotBadEvent P t) ≤
        (productLaw P n).real
          ((⋃ k : Fin d, {sample |
            cellMass P k < t * logScale n / (2 * splitSize n 0) ∧
            t * logScale n < (splitCategoryCount sample 0 k : ℝ)}) ∪
          (⋃ k : Fin d, {sample |
            2 * t * logScale n / splitSize n 0 < cellMass P k ∧
            (splitCategoryCount sample 0 k : ℝ) ≤ t * logScale n})) :=
      measureReal_mono (pilotBadEvent_subset_cellwise P t)
    _ ≤ ∑ k : Fin d,
          (productLaw P n).real {sample |
            cellMass P k < t * logScale n / (2 * splitSize n 0) ∧
            t * logScale n < (splitCategoryCount sample 0 k : ℝ)} +
        ∑ k : Fin d,
          (productLaw P n).real {sample |
            2 * t * logScale n / splitSize n 0 < cellMass P k ∧
            (splitCategoryCount sample 0 k : ℝ) ≤ t * logScale n} := by
      exact (measureReal_union_le _ _).trans
        (add_le_add (measureReal_iUnion_fintype_le _)
          (measureReal_iUnion_fintype_le _))
    _ ≤ ∑ _k : Fin d,
          Real.exp (-(t * logScale n) * (Real.log 2 - 1 / 2)) +
        ∑ _k : Fin d, Real.exp (-(t * logScale n) / 4) := by
      apply add_le_add
      · apply Finset.sum_le_sum
        intro k _hk_univ
        by_cases hk : cellMass P k < t * logScale n / (2 * splitSize n 0)
        · apply (measureReal_mono (fun sample hs ↦ hs.2)).trans
          have hs : splitSize n 0 = n / 2 := by
            simp [splitSize, splitIndices, Fin.card_filter_val_lt,
              Nat.min_eq_right (Nat.div_le_self n 2)]
          rw [hs] at hk
          apply pilotCategory_upper_tail P k
          have hmNat : 0 < n / 2 := Nat.div_pos (by omega) (by omega)
          have hm : (0 : ℝ) < ((n / 2 : ℕ) : ℝ) := by exact_mod_cast hmNat
          have hmult := (lt_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hm)).mp hk
          nlinarith
        · simp only [hk, false_and, Set.setOf_false, measureReal_empty]
          positivity
      · apply Finset.sum_le_sum
        intro k _hk_univ
        by_cases hk : 2 * t * logScale n / splitSize n 0 < cellMass P k
        · apply (measureReal_mono (fun sample hs ↦ hs.2)).trans
          have hs : splitSize n 0 = n / 2 := by
            simp [splitSize, splitIndices, Fin.card_filter_val_lt,
              Nat.min_eq_right (Nat.div_le_self n 2)]
          rw [hs] at hk
          have hmNat : 0 < n / 2 := Nat.div_pos (by omega) (by omega)
          have hm : (0 : ℝ) < ((n / 2 : ℕ) : ℝ) := by exact_mod_cast hmNat
          have hmean_gt : 2 * (t * logScale n) <
              (n / 2 : ℕ) * cellMass P k := by
            have hmult := (div_lt_iff₀ hm).mp hk
            nlinarith
          have htail := pilotCategory_lower_tail P k hmean_gt
          exact htail.trans (Real.exp_le_exp.mpr (by nlinarith))
        · simp only [hk, false_and, Set.setOf_false, measureReal_empty]
          positivity
    _ = d * (Real.exp (-(t * logScale n) * (Real.log 2 - 1 / 2)) +
        Real.exp (-(t * logScale n) / 4)) := by simp [Nat.cast_ofNat]; ring

-- @node: exp_neg_mul_logScale
/-- Establishes the stated upper bound for exp neg mul log Scale. -/
lemma exp_neg_mul_logScale (n : ℕ) (hn : 0 < n) (q : ℝ) :
    Real.exp (-q * logScale n) = Real.exp (-q) * Real.rpow n (-q) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  change Real.exp (-q * logScale n) = Real.exp (-q) * (n : ℝ) ^ (-q)
  rw [Real.rpow_def_of_pos hnR]
  unfold logScale
  rw [Real.log_mul (Real.exp_ne_zero 1) (ne_of_gt hnR), Real.log_exp]
  rw [← Real.exp_add]
  congr 1
  ring

-- @node: pilot_decay_bound
/-- Establishes the stated upper bound for pilot decay bound. -/
lemma pilot_decay_bound (K c t : ℝ) (hK : 0 < K) (hc : 0 < c)
    (ht : 0 ≤ t)
    (htUpper : K + 4 ≤ t * (Real.log 2 - 1 / 2))
    (htLower : K + 4 ≤ t / 4) :
    ∀ n d : ℕ, 1 ≤ n →
      (d : ℝ) ≤ c * n * logScale n →
      d * (Real.exp (-(t * logScale n) * (Real.log 2 - 1 / 2)) +
        Real.exp (-(t * logScale n) / 4)) ≤ (2 * c) * Real.rpow n (-K) := by
  intro n d hn hd
  have hnpos : 0 < n := Nat.zero_lt_of_lt hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hnR1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hLpos : 0 < logScale n := by
    unfold logScale
    apply Real.log_pos
    calc
      1 < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
      _ ≤ Real.exp 1 * (n : ℝ) :=
        le_mul_of_one_le_right (Real.exp_pos 1).le hnR1
  have hLle : logScale n ≤ (n : ℝ) := by
    unfold logScale
    rw [Real.log_mul (Real.exp_ne_zero 1) (ne_of_gt hnR), Real.log_exp]
    have hlog : Real.log (n : ℝ) ≤ n - 1 := Real.log_le_sub_one_of_pos hnR
    linarith
  have hupper : Real.exp (-(t * logScale n) * (Real.log 2 - 1 / 2)) ≤
      Real.exp (-(K + 4) * logScale n) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hlower : Real.exp (-(t * logScale n) / 4) ≤
      Real.exp (-(K + 4) * logScale n) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  calc
    (d : ℝ) * (Real.exp (-(t * logScale n) * (Real.log 2 - 1 / 2)) +
        Real.exp (-(t * logScale n) / 4)) ≤
        (c * n * logScale n) *
          (2 * Real.exp (-(K + 4) * logScale n)) := by gcongr <;> nlinarith
    _ ≤ (c * n * n) * (2 * Real.exp (-(K + 4) * logScale n)) := by
      gcongr
    _ = 2 * c * Real.exp (-(K + 4)) *
          ((n : ℝ) ^ 2 * Real.rpow n (-(K + 4))) := by
      rw [exp_neg_mul_logScale n hnpos]
      ring
    _ ≤ 2 * c * ((n : ℝ) ^ 2 * Real.rpow n (-(K + 4))) := by
      have hexp : Real.exp (-(K + 4)) ≤ 1 := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr (by linarith)
      have hfactor : 0 ≤ 2 * c *
          ((n : ℝ) ^ 2 * Real.rpow n (-(K + 4))) := by
        exact mul_nonneg (mul_nonneg (by positivity) hc.le)
          (mul_nonneg (sq_nonneg _) (Real.rpow_pos_of_pos hnR _).le)
      calc
        2 * c * Real.exp (-(K + 4)) *
            ((n : ℝ) ^ 2 * Real.rpow n (-(K + 4))) =
            Real.exp (-(K + 4)) *
              (2 * c * ((n : ℝ) ^ 2 * Real.rpow n (-(K + 4))) ) := by ring
        _ ≤ 1 * (2 * c * ((n : ℝ) ^ 2 * Real.rpow n (-(K + 4)))) :=
          mul_le_mul_of_nonneg_right hexp hfactor
        _ = 2 * c * ((n : ℝ) ^ 2 * Real.rpow n (-(K + 4))) := by ring
    _ = 2 * c * Real.rpow n (-K - 2) := by
      have hpow : ((n : ℝ) ^ 2) = Real.rpow n 2 := by
        symm
        exact Real.rpow_natCast n 2
      have hrpow : Real.rpow n 2 * Real.rpow n (-(K + 4)) =
          Real.rpow n (-K - 2) := by
        calc
          Real.rpow n 2 * Real.rpow n (-(K + 4)) =
              Real.rpow n (2 + -(K + 4)) :=
            (Real.rpow_add hnR 2 (-(K + 4))).symm
          _ = Real.rpow n (-K - 2) := by congr 1 <;> ring
      rw [hpow, hrpow]
    _ ≤ 2 * c * Real.rpow n (-K) := by
      gcongr
      exact Real.rpow_le_rpow_of_exponent_le hnR1 (by linarith)

-- @node: lem:pilot-sandwich
/-- Polynomially small failure probability for the pilot heavy/light sandwich. -/
lemma pilot_sandwich :
    (∀ K c : ℝ, 0 < K → 0 < c →
        -- @realizes c(positive constant in d ≤ c n log n)
        ∃ t₀ C N, 0 < t₀ ∧ 0 < C ∧ ∀ t : ℝ, t₀ ≤ t →
            ∀ (n d : ℕ) (P : DiscreteLaw d)
              (mu_n : Measure (Fin n → Obs d)),
              N ≤ n → (d : ℝ) ≤ c * n * logScale n →
              IidSampling P mu_n →
              mu_n.real (pilotBadEvent P t) ≤ C * Real.rpow n (-K)) ∧
      (∀ c : ℝ, 0 < c →
        -- @realizes c(positive constant in the K=4 specialization)
        ∃ C N, 0 < C ∧
          ∀ (n d : ℕ) (P : DiscreteLaw d)
            (mu_n : Measure (Fin n → Obs d)),
            N ≤ n → (d : ℝ) ≤ c * n * logScale n →
            IidSampling P mu_n →
            mu_n.real (pilotBadEvent P 256) ≤ C * Real.rpow n (-4)) := by
  have hA : 0 < Real.log 2 - 1 / 2 := by
    nlinarith [Real.log_two_gt_d9]
  constructor
  · intro K c hK hc
    let t₀ := max ((K + 4) / (Real.log 2 - 1 / 2)) (4 * (K + 4))
    have hK4 : 0 < K + 4 := by linarith
    have ht₀ : 0 < t₀ := lt_of_lt_of_le (div_pos hK4 hA) (le_max_left _ _)
    refine ⟨t₀, 2 * c, 2, ht₀, by positivity, ?_⟩
    intro t htt n d P mu_n hn hd hiid
    have ht : 0 ≤ t := (ht₀.trans_le htt).le
    have htUpper : K + 4 ≤ t * (Real.log 2 - 1 / 2) := by
      have := le_trans (le_max_left ((K + 4) / (Real.log 2 - 1 / 2))
        (4 * (K + 4))) htt
      calc
        K + 4 = ((K + 4) / (Real.log 2 - 1 / 2)) *
            (Real.log 2 - 1 / 2) := by
              exact (div_mul_cancel₀ (K + 4) (ne_of_gt hA)).symm
        _ ≤ t * (Real.log 2 - 1 / 2) :=
          mul_le_mul_of_nonneg_right this hA.le
    have htLower : K + 4 ≤ t / 4 := by
      have := le_trans (le_max_right ((K + 4) / (Real.log 2 - 1 / 2))
        (4 * (K + 4))) htt
      linarith
    rw [hiid]
    exact (pilotBadEvent_probability P t ht hn).trans
      (pilot_decay_bound K c t hK hc ht htUpper htLower
        n d (le_trans (by omega) hn) hd)
  · intro c hc
    have ht : (0 : ℝ) ≤ 256 := by norm_num
    have htUpper : (4 : ℝ) + 4 ≤ 256 * (Real.log 2 - 1 / 2) := by
      nlinarith [Real.log_two_gt_d9]
    have htLower : (4 : ℝ) + 4 ≤ 256 / 4 := by norm_num
    refine ⟨2 * c, 2, by positivity, ?_⟩
    intro n d P mu_n hn hd hiid
    rw [hiid]
    exact (pilotBadEvent_probability P 256 ht hn).trans
      (pilot_decay_bound 4 c 256 (by norm_num) hc ht htUpper htLower
        n d (le_trans (by omega) hn) hd)

/-- The paper's explicit threshold `t=256` works for exponent `K=4`. -/
lemma pilot_sandwich_256 :
    ∀ c : ℝ, 0 < c → ∃ C N, 0 < C ∧
      ∀ (n d : ℕ) (P : DiscreteLaw d)
        (mu_n : Measure (Fin n → Obs d)),
        N ≤ n → (d : ℝ) ≤ c * n * logScale n →
        IidSampling P mu_n →
        mu_n.real (pilotBadEvent P 256) ≤ C * Real.rpow n (-4) := by
  exact pilot_sandwich.2

end CausalSmith.Stat.DiscreteAteMinimaxLoggap

/-- The infinite sequence of independent draws from a distribution is unchanged when that
underlying distribution is replaced by an equal one. -/
add_decl_doc Causalean.Stat.iidSample_infinitePi.congr_simp
