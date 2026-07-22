import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.ChebyshevCertificate
import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.MultinomialMoments
import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.PilotConditioning
import CausalSmith.Stat.STAT_DiscreteAteMinimaxLoggap_Research.Helpers.PilotSandwich

namespace CausalSmith.Stat.DiscreteAteMinimaxLoggap

open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- Equips the stated space with the measurable structure used in this construction. -/
instance optionCellMeasurableSpace : MeasurableSpace (Option Cell) := ⊤

-- @node: iidSample_shift
/-- Defines iid Sample Shift, the stated quantity or construction used in the discrete average-treatment-effect estimator. -/
noncomputable def iidSampleShift {Ω X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] {μ : Measure Ω} {Q : Measure X}
    (S : Causalean.Stat.IIDSample Ω X μ Q) (offset : ℕ) :
    Causalean.Stat.IIDSample Ω X μ Q where
  Z i := S.Z (offset + i)
  meas i := S.meas (offset + i)
  indep := S.indep.precomp (fun _ _ h ↦ Nat.add_left_cancel h)
  identDist i := by
    simpa using (S.identDist offset).symm.trans (S.identDist (offset + i))
  law := by simpa using S.map_eq offset

-- @node: iidSample_map
/-- Defines iid Sample Map, the stated quantity or construction used in the discrete average-treatment-effect estimator. -/
noncomputable def iidSampleMap {Ω X Y : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure Ω} {Q : Measure X}
    (S : Causalean.Stat.IIDSample Ω X μ Q) (f : X → Y) (hf : Measurable f) :
    Causalean.Stat.IIDSample Ω Y μ (Q.map f) where
  Z i := f ∘ S.Z i
  meas i := hf.comp (S.meas i)
  indep := S.indep.comp (fun _ => f) (fun _ => hf)
  identDist i := (S.identDist i).comp hf
  law := by
    rw [← Measure.map_map hf (S.meas 0), S.law]

-- @node: categoryCellLabel
/-- Defines category Cell Label, the stated quantity or construction used in the discrete average-treatment-effect estimator. -/
def categoryCellLabel {d : ℕ} (k : Fin d) (z : Obs d) : Option Cell :=
  if z.1 = k then
    some (finTwoEquiv.symm z.2.1, finTwoEquiv.symm z.2.2)
  else none

-- @node: categoryCellLabel_measurable
/-- Establishes the stated upper bound for category Cell Label measurable. -/
lemma categoryCellLabel_measurable {d : ℕ} (k : Fin d) :
    Measurable (categoryCellLabel k) := measurable_of_finite _

-- @node: optionCellExponent
/-- Defines option Cell Exponent, the stated quantity or construction used in the discrete average-treatment-effect estimator. -/
def optionCellExponent (r : MultiIndex) : Option Cell → ℕ
  | none => 0
  | some ay => r ay

-- @node: exponentDegree_optionCellExponent
/-- Establishes the stated property of exponent Degree option Cell Exponent in the discrete average-treatment-effect construction. -/
lemma exponentDegree_optionCellExponent (r : MultiIndex) :
    exponentDegree (optionCellExponent r) = multiDegree r := by
  classical
  simp [exponentDegree, optionCellExponent, multiDegree, Finsupp.sum_fintype]

-- @node: categoryCellLabel_atom_mass
/-- Establishes the stated property of category Cell Label atom mass in the discrete average-treatment-effect construction. -/
lemma categoryCellLabel_atom_mass {d : ℕ} (P : DiscreteLaw d) (k : Fin d)
    (ay : Cell) :
    ((obsLaw P).map (categoryCellLabel k)).real {some ay} =
      cellVector P k ay := by
  rw [map_measureReal_apply (categoryCellLabel_measurable k)
    (MeasurableSet.singleton (some ay))]
  have hpre : categoryCellLabel k ⁻¹' {some ay} =
      {(k, finTwoEquiv ay.1, finTwoEquiv ay.2)} := by
    rcases ay with ⟨a₀, y₀⟩
    fin_cases a₀ <;> fin_cases y₀ <;>
      ext z <;> rcases z with ⟨j, a, y⟩ <;>
      cases a <;> cases y <;> simp [categoryCellLabel, finTwoEquiv]
  rw [hpre]
  change (P.pmf.toMeasure).real
      {(k, finTwoEquiv ay.1, finTwoEquiv ay.2)} = _
  rw [show (P.pmf.toMeasure).real
      {(k, finTwoEquiv ay.1, finTwoEquiv ay.2)} =
      (P.pmf (k, finTwoEquiv ay.1, finTwoEquiv ay.2)).toReal by
    exact congrArg ENNReal.toReal
      (P.pmf.toMeasure_apply_singleton _ (MeasurableSet.singleton _))]
  rfl

-- @node: splitSize_zero_eq
/-- Establishes the stated equality relating split Size zero eq. -/
lemma splitSize_zero_eq (n : ℕ) : splitSize n 0 = n / 2 := by
  simp [splitSize, splitIndices, Fin.card_filter_val_lt,
    Nat.min_eq_right (Nat.div_le_self n 2)]

-- @node: splitSize_one_eq
/-- Establishes the stated equality relating split Size one eq. -/
lemma splitSize_one_eq (n : ℕ) : splitSize n 1 = n - n / 2 := by
  unfold splitSize splitIndices
  simp only [show (1 : Fin 2) ≠ 0 by decide, if_false]
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n))) (p := fun i => i.1 < n / 2)
  have hfirst : ((Finset.univ : Finset (Fin n)).filter
      (fun i => i.1 < n / 2)).card = n / 2 := by
    simpa [Fin.card_filter_val_lt, Nat.min_eq_right (Nat.div_le_self n 2)]
  have hsum : n / 2 + ((Finset.univ : Finset (Fin n)).filter
      (fun i => n / 2 ≤ i.1)).card = n := by
    simpa only [not_lt, hfirst, Finset.card_univ, Fintype.card_fin] using hpartition
  omega

-- @node: estimationTailIndex
/-- Defines estimation Tail Index, the stated quantity or construction used in the discrete average-treatment-effect estimator. -/
def estimationTailIndex (n : ℕ) (j : Fin (splitSize n 1)) : Fin n :=
  ⟨n / 2 + j, by
    have hhalf : n / 2 ≤ n := Nat.div_le_self n 2
    have hdecomp : n / 2 + (n - n / 2) = n := Nat.add_sub_of_le hhalf
    have hj : j.1 < n - n / 2 := by
      simpa [splitSize_one_eq] using j.2
    omega⟩

-- @node: splitCellCount_eq_tail_count
/-- Establishes the stated equality relating split Cell Count eq tail count. -/
lemma splitCellCount_eq_tail_count {n d : ℕ} (sample : Fin n → Obs d)
    (k : Fin d) (a y : Fin 2) :
    splitCellCount sample 1 k a y =
      ((Finset.univ : Finset (Fin (splitSize n 1))).filter
        (fun j => sample (estimationTailIndex n j) =
          (k, finTwoEquiv a, finTwoEquiv y))).card := by
  classical
  let atom : Obs d := (k, finTwoEquiv a, finTwoEquiv y)
  let s : Finset (Fin n) :=
    (splitIndices n 1).filter (fun i => sample i = atom)
  let t : Finset (Fin (splitSize n 1)) :=
    Finset.univ.filter (fun j => sample (estimationTailIndex n j) = atom)
  have hcard : s.card = t.card := by
    refine Finset.card_bij
      (s := s) (t := t)
      (fun i hi =>
        (⟨i.1 - n / 2, by
          have hi' := hi
          simp only [s, Finset.mem_filter] at hi'
          have hiSplit : n / 2 ≤ i.1 := by
            simpa [splitIndices] using hi'.1
          rw [splitSize_one_eq]
          omega⟩ : Fin (splitSize n 1))) ?_ ?_ ?_
    · intro i hi
      have hi' := hi
      simp only [s, Finset.mem_filter] at hi'
      have hiSplit : n / 2 ≤ i.1 := by
        simpa [splitIndices] using hi'.1
      simp only [t, Finset.mem_filter, Finset.mem_univ, true_and]
      simpa [estimationTailIndex, Nat.add_sub_of_le hiSplit] using hi'.2
    · intro i hi j hj hij
      have hi' := hi
      have hj' := hj
      simp only [s, Finset.mem_filter] at hi' hj'
      have hiSplit : n / 2 ≤ i.1 := by
        simpa [splitIndices] using hi'.1
      have hjSplit : n / 2 ≤ j.1 := by
        simpa [splitIndices] using hj'.1
      have hij' := congrArg Fin.val hij
      apply Fin.ext
      dsimp at hij'
      omega
    · intro j hj
      refine ⟨estimationTailIndex n j, ?_, ?_⟩
      · simp only [s, Finset.mem_filter]
        constructor
        · simp [estimationTailIndex, splitIndices]
        · simpa [t] using hj
      · apply Fin.ext
        dsimp [estimationTailIndex]
        omega
  simpa [s, t, atom, splitCellCount] using hcard

-- @node: categoryCellLabel_fiber_card
/-- Establishes the stated property of category Cell Label fiber card in the discrete average-treatment-effect construction. -/
lemma categoryCellLabel_fiber_card {n d : ℕ} (sample : Fin n → Obs d)
    (k : Fin d) (ay : Cell) :
    Fintype.card (PatternFiber
      (fun j : Fin (splitSize n 1) =>
        categoryCellLabel k (sample (estimationTailIndex n j))) (some ay)) =
      splitCellCount sample 1 k ay.1 ay.2 := by
  classical
  rw [Fintype.card_of_subtype
    ((Finset.univ : Finset (Fin (splitSize n 1))).filter
      (fun j => categoryCellLabel k (sample (estimationTailIndex n j)) = some ay))]
  · rw [splitCellCount_eq_tail_count]
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases ay with ⟨a, y⟩
    fin_cases a <;> fin_cases y <;>
      generalize hobs : sample (estimationTailIndex n j) = z <;>
      rcases z with ⟨l, a', y'⟩ <;>
      cases a' <;> cases y' <;> simp [categoryCellLabel, finTwoEquiv] at hobs ⊢ <;>
      simpa [hobs]
  · intro j
    simp

-- @node: estimationLabelSample
/-- Defines estimation Label Sample, the stated quantity or construction used in the discrete average-treatment-effect estimator. -/
def estimationLabelSample {n d : ℕ} (sample : Fin n → Obs d) (k : Fin d) :
    Fin (splitSize n 1) → Option Cell :=
  fun j => categoryCellLabel k (sample (estimationTailIndex n j))

-- @node: multinomialFactorialCount_estimationLabelSample
/-- Establishes the stated upper bound for multinomial Factorial Count estimation Label Sample. -/
lemma multinomialFactorialCount_estimationLabelSample {n d : ℕ}
    (sample : Fin n → Obs d) (k : Fin d) (r : MultiIndex) :
    multinomialFactorialCount (optionCellExponent r)
        (estimationLabelSample sample k) =
      ∏ ay : Cell,
        ((splitCellCount sample 1 k ay.1 ay.2).descFactorial (r ay) : ℝ) := by
  rw [multinomialFactorialCount_eq_prod]
  simp only [Fintype.prod_option, optionCellExponent, Nat.descFactorial_zero,
    Nat.cast_one, one_mul]
  apply Finset.prod_congr rfl
  intro ay _hay
  change ((Fintype.card (PatternFiber
      (fun j : Fin (splitSize n 1) =>
        categoryCellLabel k (sample (estimationTailIndex n j))) (some ay))).descFactorial
      (r ay) : ℝ) = _
  rw [categoryCellLabel_fiber_card]

-- @node: factorialMonomial_eq_normalized_multinomialCount
/-- Establishes the stated equality relating factorial Monomial eq normalized multinomial Count. -/
lemma factorialMonomial_eq_normalized_multinomialCount {n d : ℕ}
    (sample : Fin n → Obs d) (k : Fin d) (r : MultiIndex) :
    factorialMonomial sample k r =
      multinomialFactorialCount (optionCellExponent r)
          (estimationLabelSample sample k) /
        ((splitSize n 1).descFactorial
          (exponentDegree (optionCellExponent r)) : ℝ) := by
  rw [multinomialFactorialCount_estimationLabelSample,
    exponentDegree_optionCellExponent]
  rfl

-- @node: lightCellEstimationIID
/-- Defines light Cell Estimation IID, the stated quantity or construction used in the discrete average-treatment-effect estimator. -/
noncomputable def lightCellEstimationIID {d : ℕ} (P : DiscreteLaw d)
    (k : Fin d) (offset : ℕ) :
    Causalean.Stat.IIDSample (ℕ → Obs d) (Option Cell)
      (Measure.infinitePi (fun _ : ℕ => obsLaw P))
      ((obsLaw P).map (categoryCellLabel k)) :=
  iidSampleMap
    (iidSampleShift (Causalean.Stat.iidSample_infinitePi (obsLaw P)) offset)
    (categoryCellLabel k) (categoryCellLabel_measurable k)

-- @node: factorialMonomial_trunc_eq_iidCount
/-- Establishes the stated equality relating factorial Monomial trunc eq iid Count. -/
lemma factorialMonomial_trunc_eq_iidCount {n d : ℕ} (P : DiscreteLaw d)
    (k : Fin d) (r : MultiIndex) (ω : ℕ → Obs d) :
    factorialMonomial (fun i : Fin n => ω i) k r =
      multinomialFactorialCount (optionCellExponent r)
          (fun j : Fin (splitSize n 1) =>
            (lightCellEstimationIID P k (n / 2)).Z j ω) /
        ((splitSize n 1).descFactorial
          (exponentDegree (optionCellExponent r)) : ℝ) := by
  rw [factorialMonomial_eq_normalized_multinomialCount]
  congr 2

-- @node: integrable_factorialMonomial_trunc
/-- Shows that integrable factorial Monomial trunc is integrable under the stated sampling distribution. -/
lemma integrable_factorialMonomial_trunc {n d : ℕ} (P : DiscreteLaw d)
    (k : Fin d) (r : MultiIndex) :
    Integrable (fun ω : ℕ → Obs d =>
      factorialMonomial (fun i : Fin n => ω i) k r)
      (Measure.infinitePi (fun _ : ℕ => obsLaw P)) := by
  letI : IsProbabilityMeasure ((obsLaw P).map (categoryCellLabel k)) :=
    Measure.isProbabilityMeasure_map (categoryCellLabel_measurable k).aemeasurable
  simp_rw [factorialMonomial_trunc_eq_iidCount P k r]
  exact (integrable_multinomialFactorialCount_sample
    (lightCellEstimationIID P k (n / 2)) (optionCellExponent r)
    (splitSize n 1)).div_const _

-- @node: integral_factorialMonomial_trunc
/-- Evaluates or bounds the stated integral involving integral factorial Monomial trunc. -/
lemma integral_factorialMonomial_trunc {n d : ℕ} (P : DiscreteLaw d)
    (k : Fin d) (r : MultiIndex) (hdeg : multiDegree r ≤ splitSize n 1) :
    ∫ ω : ℕ → Obs d, factorialMonomial (fun i : Fin n => ω i) k r
        ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P)) =
      r.prod fun ay e => (cellVector P k ay) ^ e := by
  letI : IsProbabilityMeasure ((obsLaw P).map (categoryCellLabel k)) :=
    Measure.isProbabilityMeasure_map (categoryCellLabel_measurable k).aemeasurable
  simp_rw [factorialMonomial_trunc_eq_iidCount P k r]
  rw [integral_div, integral_multinomialFactorialCount_sample]
  have hfacpos : 0 < (splitSize n 1).descFactorial
      (exponentDegree (optionCellExponent r)) := by
    rw [exponentDegree_optionCellExponent]
    exact Nat.descFactorial_pos.mpr hdeg
  rw [mul_div_cancel_left₀ _ (by exact_mod_cast hfacpos.ne')]
  simp only [Fintype.prod_option, optionCellExponent, pow_zero, one_mul]
  rw [r.prod_fintype _ (fun _ => pow_zero _)]
  apply Finset.prod_congr rfl
  intro ay _hay
  rw [categoryCellLabel_atom_mass]

-- @node: integral_factorialMonomial_mul_trunc_le
/-- Evaluates or bounds the stated integral involving integral factorial Monomial mul trunc le. -/
lemma integral_factorialMonomial_mul_trunc_le {n d : ℕ} (P : DiscreteLaw d)
    (k : Fin d) (r s : MultiIndex)
    (hn : 0 < splitSize n 1) (hdeg : multiDegree r ≤ multiDegree s)
    (hsize : 4 * (multiDegree s) ^ 2 ≤ splitSize n 1) :
    ∫ ω : ℕ → Obs d,
        factorialMonomial (fun i : Fin n => ω i) k r *
          factorialMonomial (fun i : Fin n => ω i) k s
        ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P)) ≤
      Real.exp 1 *
        (∏ ay : Cell, (cellVector P k ay) ^ (r ay)) *
        ∏ ay : Cell,
          (cellVector P k ay + (multiDegree s : ℝ) / splitSize n 1) ^ (s ay) := by
  letI : IsProbabilityMeasure ((obsLaw P).map (categoryCellLabel k)) :=
    Measure.isProbabilityMeasure_map (categoryCellLabel_measurable k).aemeasurable
  simp_rw [factorialMonomial_trunc_eq_iidCount P]
  have h := normalized_multinomial_joint_moment_bound
    (lightCellEstimationIID P k (n / 2))
    (optionCellExponent r) (optionCellExponent s) (splitSize n 1) hn
    (by simpa only [exponentDegree_optionCellExponent] using hdeg)
    (by simpa only [exponentDegree_optionCellExponent] using hsize)
  simpa only [exponentDegree_optionCellExponent, Fintype.prod_option,
    optionCellExponent, pow_zero, one_mul, categoryCellLabel_atom_mass] using h

-- @node: integrable_factorialMonomial_mul_trunc
/-- Shows that integrable factorial Monomial mul trunc is integrable under the stated sampling distribution. -/
lemma integrable_factorialMonomial_mul_trunc {n d : ℕ} (P : DiscreteLaw d)
    (k : Fin d) (r s : MultiIndex) :
    Integrable (fun ω : ℕ → Obs d =>
      factorialMonomial (fun i : Fin n => ω i) k r *
        factorialMonomial (fun i : Fin n => ω i) k s)
      (Measure.infinitePi (fun _ : ℕ => obsLaw P)) := by
  letI : IsProbabilityMeasure ((obsLaw P).map (categoryCellLabel k)) :=
    Measure.isProbabilityMeasure_map (categoryCellLabel_measurable k).aemeasurable
  simp_rw [factorialMonomial_trunc_eq_iidCount P k]
  have hraw : Integrable (fun ω : ℕ → Obs d =>
      multinomialFactorialCount (optionCellExponent r)
          (fun j : Fin (splitSize n 1) =>
            (lightCellEstimationIID P k (n / 2)).Z j ω) *
        multinomialFactorialCount (optionCellExponent s)
          (fun j : Fin (splitSize n 1) =>
            (lightCellEstimationIID P k (n / 2)).Z j ω))
      (Measure.infinitePi (fun _ : ℕ => obsLaw P)) := by
    simp_rw [multinomialFactorialCount_mul]
    apply integrable_finset_sum
    intro H _hH
    exact Integrable.const_mul
      (integrable_multinomialFactorialCount_sample
        (lightCellEstimationIID P k (n / 2))
        (mergedExponent (optionCellExponent r) (optionCellExponent s) H)
        (splitSize n 1)) _
  convert hraw.div_const
    (((splitSize n 1).descFactorial
        (exponentDegree (optionCellExponent r)) : ℝ) *
      (splitSize n 1).descFactorial
        (exponentDegree (optionCellExponent s))) using 1
  funext ω
  ring

-- @node: observationExponent
/-- Defines observation Exponent, the stated quantity or construction used in the discrete average-treatment-effect estimator. -/
def observationExponent {d : ℕ} (k : Fin d) (r : MultiIndex) : Obs d → ℕ :=
  fun z => if z.1 = k then
    r (finTwoEquiv.symm z.2.1, finTwoEquiv.symm z.2.2) else 0

-- @node: exponentDegree_observationExponent
/-- Establishes the stated property of exponent Degree observation Exponent in the discrete average-treatment-effect construction. -/
lemma exponentDegree_observationExponent {d : ℕ} (k : Fin d) (r : MultiIndex) :
    exponentDegree (observationExponent k r) = multiDegree r := by
  classical
  simp only [exponentDegree, observationExponent, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single k]
  · simp [multiDegree, Finsupp.sum_fintype, Fintype.sum_bool,
      Fintype.sum_prod_type, Fin.sum_univ_two, finTwoEquiv]
    omega
  · intro j _hj hjk
    simp [hjk]
  · simp

-- @node: estimationTail_fiber_card
/-- Establishes the stated property of estimation Tail fiber card in the discrete average-treatment-effect construction. -/
lemma estimationTail_fiber_card {n d : ℕ} (sample : Fin n → Obs d) (z : Obs d) :
    Fintype.card (PatternFiber
      (fun j : Fin (splitSize n 1) => sample (estimationTailIndex n j)) z) =
      ((Finset.univ : Finset (Fin (splitSize n 1))).filter
        (fun j => sample (estimationTailIndex n j) = z)).card := by
  classical
  apply Fintype.card_of_subtype
  intro j
  simp

-- @node: observationExponent_fiber_count
/-- Establishes the stated property of observation Exponent fiber count in the discrete average-treatment-effect construction. -/
lemma observationExponent_fiber_count {n d : ℕ} (sample : Fin n → Obs d)
    (k : Fin d) (r : MultiIndex) (z : Obs d) :
    ((Fintype.card (PatternFiber
        (fun j : Fin (splitSize n 1) => sample (estimationTailIndex n j)) z)).descFactorial
      (observationExponent k r z) : ℝ) =
      if z.1 = k then
        ((splitCellCount sample 1 k (finTwoEquiv.symm z.2.1)
          (finTwoEquiv.symm z.2.2)).descFactorial
            (r (finTwoEquiv.symm z.2.1, finTwoEquiv.symm z.2.2)) : ℝ)
      else 1 := by
  by_cases hz : z.1 = k
  · rw [if_pos hz]
    rcases z with ⟨j, a, y⟩
    have hjk : j = k := hz
    subst j
    rw [observationExponent, if_pos rfl, estimationTail_fiber_card,
      splitCellCount_eq_tail_count]
    simp
  · rw [if_neg hz, observationExponent, if_neg hz]
    simp

-- @node: multinomialFactorialCount_observationExponent
/-- Establishes the stated property of multinomial Factorial Count observation Exponent in the discrete average-treatment-effect construction. -/
lemma multinomialFactorialCount_observationExponent {n d : ℕ}
    (sample : Fin n → Obs d) (k : Fin d) (r : MultiIndex) :
    multinomialFactorialCount (observationExponent k r)
        (fun j : Fin (splitSize n 1) => sample (estimationTailIndex n j)) =
      ∏ ay : Cell,
        ((splitCellCount sample 1 k ay.1 ay.2).descFactorial (r ay) : ℝ) := by
  rw [multinomialFactorialCount_eq_prod]
  simp_rw [observationExponent_fiber_count sample k r]
  classical
  simp only [Fintype.prod_prod_type]
  rw [Finset.prod_eq_single k]
  · simp [Fintype.prod_bool, Fin.prod_univ_two, finTwoEquiv]
    ring
  · intro j _hj hjk
    simp [hjk]
  · simp

-- @node: factorialMonomial_eq_normalized_observationCount
/-- Establishes the stated equality relating factorial Monomial eq normalized observation Count. -/
lemma factorialMonomial_eq_normalized_observationCount {n d : ℕ}
    (sample : Fin n → Obs d) (k : Fin d) (r : MultiIndex) :
    factorialMonomial sample k r =
      multinomialFactorialCount (observationExponent k r)
          (fun j : Fin (splitSize n 1) => sample (estimationTailIndex n j)) /
        ((splitSize n 1).descFactorial
          (exponentDegree (observationExponent k r)) : ℝ) := by
  rw [multinomialFactorialCount_observationExponent,
    exponentDegree_observationExponent]
  rfl

-- @node: factorialMonomial_trunc_eq_observationCount
/-- Establishes the stated equality relating factorial Monomial trunc eq observation Count. -/
lemma factorialMonomial_trunc_eq_observationCount {n d : ℕ}
    (P : DiscreteLaw d) (k : Fin d) (r : MultiIndex) (ω : ℕ → Obs d) :
    factorialMonomial (fun i : Fin n => ω i) k r =
      multinomialFactorialCount (observationExponent k r)
          (fun j : Fin (splitSize n 1) =>
            (iidSampleShift
              (Causalean.Stat.iidSample_infinitePi (obsLaw P)) (n / 2)).Z j ω) /
        ((splitSize n 1).descFactorial
          (exponentDegree (observationExponent k r)) : ℝ) := by
  rw [factorialMonomial_eq_normalized_observationCount]
  congr 2

-- @node: obsLaw_real_cellAtom
/-- Establishes the stated property of obs Law real cell Atom in the discrete average-treatment-effect construction. -/
lemma obsLaw_real_cellAtom {d : ℕ} (P : DiscreteLaw d) (k : Fin d)
    (ay : Cell) :
    (obsLaw P).real {(k, finTwoEquiv ay.1, finTwoEquiv ay.2)} =
      cellVector P k ay := by
  change (P.pmf.toMeasure).real
      {(k, finTwoEquiv ay.1, finTwoEquiv ay.2)} = _
  rw [show (P.pmf.toMeasure).real
      {(k, finTwoEquiv ay.1, finTwoEquiv ay.2)} =
      (P.pmf (k, finTwoEquiv ay.1, finTwoEquiv ay.2)).toReal by
    exact congrArg ENNReal.toReal
      (P.pmf.toMeasure_apply_singleton _ (MeasurableSet.singleton _))]
  rfl

-- @node: observationExponent_mass_prod
/-- Establishes the stated property of observation Exponent mass prod in the discrete average-treatment-effect construction. -/
lemma observationExponent_mass_prod {d : ℕ} (P : DiscreteLaw d)
    (k : Fin d) (r : MultiIndex) :
    ∏ z : Obs d, ((obsLaw P).real {z}) ^ (observationExponent k r z) =
      ∏ ay : Cell, (cellVector P k ay) ^ (r ay) := by
  classical
  simp only [Fintype.prod_prod_type]
  rw [Finset.prod_eq_single k]
  · simp only [observationExponent, if_pos, Fintype.prod_bool]
    have h00 := obsLaw_real_cellAtom P k (0, 0)
    have h01 := obsLaw_real_cellAtom P k (0, 1)
    have h10 := obsLaw_real_cellAtom P k (1, 0)
    have h11 := obsLaw_real_cellAtom P k (1, 1)
    simp [finTwoEquiv] at h00 h01 h10 h11
    rw [h00, h01, h10, h11]
    simp [Fin.prod_univ_two, finTwoEquiv]
    ring
  · intro j _hj hjk
    simp [observationExponent, hjk]
  · simp

-- @node: integral_factorialMonomial_cross_trunc
/-- Evaluates or bounds the stated integral involving integral factorial Monomial cross trunc. -/
lemma integral_factorialMonomial_cross_trunc {n d : ℕ} (P : DiscreteLaw d)
    (k l : Fin d) (hkl : k ≠ l) (r s : MultiIndex) :
    ∫ ω : ℕ → Obs d,
        factorialMonomial (fun i : Fin n => ω i) k r *
          factorialMonomial (fun i : Fin n => ω i) l s
        ∂(Measure.infinitePi (fun _ : ℕ => obsLaw P)) =
      ((splitSize n 1).descFactorial (multiDegree r + multiDegree s) : ℝ) /
          (((splitSize n 1).descFactorial (multiDegree r) : ℝ) *
            (splitSize n 1).descFactorial (multiDegree s)) *
        (∏ ay : Cell, (cellVector P k ay) ^ (r ay)) *
        ∏ ay : Cell, (cellVector P l ay) ^ (s ay) := by
  simp_rw [factorialMonomial_trunc_eq_observationCount P]
  let S := iidSampleShift (Causalean.Stat.iidSample_infinitePi (obsLaw P)) (n / 2)
  have hdisj : ∀ (i : MultiSlot (observationExponent k r))
      (j : MultiSlot (observationExponent l s)),
      multiPattern (observationExponent k r) i ≠
        multiPattern (observationExponent l s) j := by
    intro i j hij
    have hik : i.1.1 = k := by
      by_contra hi
      have := i.2
      simp [observationExponent, hi] at this
      exact Fin.elim0 this
    have hjl : j.1.1 = l := by
      by_contra hj
      have := j.2
      simp [observationExponent, hj] at this
      exact Fin.elim0 this
    apply hkl
    have hx : i.1.1 = j.1.1 := congrArg Prod.fst hij
    exact hik.symm.trans (hx.trans hjl)
  have h := integral_normalized_matchingCount_mul_sample S
    (multiPattern (observationExponent k r))
    (multiPattern (observationExponent l s)) (splitSize n 1) hdisj
  simp only [multinomialFactorialCount] at h ⊢
  rw [multiSlot_card, multiSlot_card,
    exponentDegree_observationExponent, exponentDegree_observationExponent] at h
  rw [multiPattern_mass_prod, multiPattern_mass_prod,
    observationExponent_mass_prod, observationExponent_mass_prod] at h
  simpa [S, exponentDegree_observationExponent] using h

-- @node: vectorMass_cellVector
/-- Establishes the stated property of vector Mass cell Vector in the discrete average-treatment-effect construction. -/
lemma vectorMass_cellVector {d : ℕ} (P : DiscreteLaw d) (k : Fin d) :
    vectorMass (cellVector P k) = cellMass P k := by
  simp [vectorMass, vectorArmMass, cellVector, cellMass, armMass, finTwoEquiv]
  ring

-- @node: vectorArmMass_cellVector
/-- Establishes the stated property of vector Arm Mass cell Vector in the discrete average-treatment-effect construction. -/
lemma vectorArmMass_cellVector {d : ℕ} (P : DiscreteLaw d) (k : Fin d)
    (a : Fin 2) :
    vectorArmMass (cellVector P k) a = armMass P k (finTwoEquiv a) := by
  rcases a with ⟨a, ha⟩
  interval_cases a <;>
    simp [vectorArmMass, cellVector, armMass, finTwoEquiv] <;> ring

-- @node: obsLaw_real_singleton
/-- Establishes the stated upper bound for obs Law real singleton. -/
lemma obsLaw_real_singleton {d : ℕ} (P : DiscreteLaw d) (z : Obs d) :
    (obsLaw P).real {z} = (P.pmf z).toReal := by
  rw [show obsLaw P = P.pmf.toMeasure by rfl]
  exact congrArg ENNReal.toReal
    (P.pmf.toMeasure_apply_singleton z (MeasurableSet.singleton z))

-- @node: obsLaw_real_atom
/-- Establishes the stated property of obs Law real atom in the discrete average-treatment-effect construction. -/
lemma obsLaw_real_atom {d : ℕ} (P : DiscreteLaw d) (k : Fin d)
    (a y : Fin 2) :
    (obsLaw P).real {(k, finTwoEquiv a, finTwoEquiv y)} = cellVector P k (a, y) := by
  simp [obsLaw_real_singleton, cellVector, jointMass]

-- @node: cellVector_mem_overlapCone
/-- Shows that cell Vector mem overlap Cone lies in the stated set or interval. -/
lemma cellVector_mem_overlapCone {d : ℕ} {epsilon : ℝ} (P : DiscreteLaw d)
    (hOverlap : Overlap epsilon P) (k : Fin d) :
    cellVector P k ∈ overlapCone epsilon := by
  refine ⟨fun ay => (jointMass_mem_unitInterval P k (finTwoEquiv ay.1)
    (finTwoEquiv ay.2)).1, ?_, ?_⟩
  rw [vectorMass_cellVector, vectorArmMass_cellVector]
  by_cases hp : 0 < cellMass P k
  · have hk := hOverlap k hp
    exact (le_div_iff₀ hp).mp (by simpa [propensity] using hk.1)
  · have hp0 : cellMass P k = 0 := le_antisymm (le_of_not_gt hp)
      (cellMass_mem_unitInterval P k).1
    have ha0 : armMass P k true = 0 := by
      have ha : 0 ≤ armMass P k true := by
        unfold armMass
        exact Finset.sum_nonneg fun y _ => (jointMass_mem_unitInterval P k true y).1
      have hle : armMass P k true ≤ cellMass P k := by
        have hfalse0 := (jointMass_mem_unitInterval P k false false).1
        have hfalse1 := (jointMass_mem_unitInterval P k false true).1
        simp [armMass, cellMass]
        linarith
      linarith
    simpa [hp0, ha0, finTwoEquiv] using
      (show (0 : ℝ) ≤ armMass P k true by rw [ha0])
  · rw [vectorMass_cellVector, vectorArmMass_cellVector]
    by_cases hp : 0 < cellMass P k
    · have hk := hOverlap k hp
      exact (div_le_iff₀ hp).mp (by simpa [propensity] using hk.2)
    · have hp0 : cellMass P k = 0 := le_antisymm (le_of_not_gt hp)
        (cellMass_mem_unitInterval P k).1
      have ha0 : armMass P k true = 0 := by
        have ha : 0 ≤ armMass P k true := by
          unfold armMass
          exact Finset.sum_nonneg fun y _ =>
            (jointMass_mem_unitInterval P k true y).1
        have hle : armMass P k true ≤ cellMass P k := by
          have hfalse0 := (jointMass_mem_unitInterval P k false false).1
          have hfalse1 := (jointMass_mem_unitInterval P k false true).1
          simp [armMass, cellMass]
          linarith
        linarith
      simpa [hp0, ha0, finTwoEquiv]

-- @node: abs_cellPhi_cellVector_le_mass
/-- Establishes the stated upper bound for abs cell Phi cell Vector le mass. -/
lemma abs_cellPhi_cellVector_le_mass {d : ℕ} {epsilon : ℝ}
    (P : DiscreteLaw d) (hOverlap : Overlap epsilon P) (k : Fin d) :
    |cellPhi (cellVector P k)| ≤ cellMass P k := by
  by_cases hz : cellVector P k = 0
  · simp [cellPhi, hz, (cellMass_mem_unitInterval P k).1]
  · simp only [cellPhi, hz, if_false]
    rw [vectorMass_cellVector, vectorArmMass_cellVector,
      vectorArmMass_cellVector]
    have hm1 := outcomeMean_mem_unitInterval P true k
    have hm0 := outcomeMean_mem_unitInterval P false k
    have hp := cellMass_mem_unitInterval P k
    rcases hm1 with ⟨hm1lo, hm1hi⟩
    rcases hm0 with ⟨hm0lo, hm0hi⟩
    have hdiff : |outcomeMean P true k - outcomeMean P false k| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith
    change |cellMass P k *
      (outcomeMean P true k - outcomeMean P false k)| ≤ cellMass P k
    rw [abs_mul, abs_of_nonneg hp.1]
    exact mul_le_of_le_one_right hp.1 hdiff

-- @node: multiDegree_factorialExpansionIndex
/-- Establishes the stated property of multi Degree factorial Expansion Index in the discrete average-treatment-effect construction. -/
lemma multiDegree_factorialExpansionIndex (a : Fin 2) (ay : Cell) (j t : ℕ)
    (ht : t ≤ j) : multiDegree (factorialExpansionIndex a ay j t) = j + 2 := by
  classical
  rcases ay with ⟨a', y'⟩
  fin_cases a <;> fin_cases a' <;> fin_cases y' <;>
    simp [multiDegree, Finsupp.sum_fintype, factorialExpansionIndex,
      Fintype.sum_prod_type, Fin.sum_univ_two] <;> omega

-- @node: factorialExpansionIndex_prod
/-- Establishes the stated property of factorial Expansion Index prod in the discrete average-treatment-effect construction. -/
lemma factorialExpansionIndex_prod (v : Cell → ℝ) (a : Fin 2)
    (ay : Cell) (j t : ℕ) :
    (factorialExpansionIndex a ay j t).prod (fun ay' e => v ay' ^ e) =
      v ay * v (a, 1) * v (a, 0) ^ t * v (a, 1) ^ (j - t) := by
  classical
  rcases ay with ⟨a', y'⟩
  fin_cases a <;> fin_cases a' <;> fin_cases y' <;>
    simp [factorialExpansionIndex, Finsupp.prod_fintype,
      Fintype.prod_prod_type, Fin.prod_univ_two] <;> ring

-- @node: factorialExpansionIndex_binomial_sum
/-- Establishes the stated summation identity or bound for factorial Expansion Index binomial sum. -/
lemma factorialExpansionIndex_binomial_sum (v : Cell → ℝ)
    (a : Fin 2) (j : ℕ) :
    ∑ t ∈ Finset.range (j + 1), ∑ ay : Cell,
        (Nat.choose j t : ℝ) *
          (factorialExpansionIndex a ay j t).prod
            (fun ay' e => v ay' ^ e) =
      (∑ ay : Cell, v ay) * v (a, 1) * (v (a, 0) + v (a, 1)) ^ j := by
  classical
  simp_rw [factorialExpansionIndex_prod]
  have hay (t : ℕ) :
      ∑ ay : Cell, (Nat.choose j t : ℝ) *
          (v ay * v (a, 1) * v (a, 0) ^ t * v (a, 1) ^ (j - t)) =
        (Nat.choose j t : ℝ) *
          ((∑ ay : Cell, v ay) * v (a, 1) *
            v (a, 0) ^ t * v (a, 1) ^ (j - t)) := by
    calc
      _ = ∑ ay : Cell, v ay *
          ((Nat.choose j t : ℝ) * v (a, 1) *
            v (a, 0) ^ t * v (a, 1) ^ (j - t)) := by
        apply Finset.sum_congr rfl
        intro ay _hay
        ring
      _ = (∑ ay : Cell, v ay) *
          ((Nat.choose j t : ℝ) * v (a, 1) *
            v (a, 0) ^ t * v (a, 1) ^ (j - t)) := by
        rw [Finset.sum_mul]
      _ = _ := by ring
  simp_rw [hay]
  rw [show ∑ t ∈ Finset.range (j + 1),
      (Nat.choose j t : ℝ) *
        ((∑ ay : Cell, v ay) * v (a, 1) *
          v (a, 0) ^ t * v (a, 1) ^ (j - t)) =
      ((∑ ay : Cell, v ay) * v (a, 1)) *
        ∑ t ∈ Finset.range (j + 1),
          v (a, 0) ^ t * v (a, 1) ^ (j - t) *
            (Nat.choose j t : ℝ) by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _ht
    ring]
  rw [← add_pow]

end CausalSmith.Stat.DiscreteAteMinimaxLoggap
