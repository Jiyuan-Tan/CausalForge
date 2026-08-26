import CausalSmith.Stat.STAT_DiscreteAteHeterogeneityFrontier_Research.Basic
import Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.Partition.CellLaws
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Occupancy transport and monotone de-Poissonization

This file forgets real outcomes while retaining the finite cell-and-arm marks
that determine usable occupancy.  It also supplies deterministic prefix
monotonicity and a paper-independent transfer from an i.i.d. stream stopped at
an independent Poisson count to a fixed prefix.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace CausalSmith.Stat.DiscreteAteHeterogeneityFrontier

open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

/-- The finite cell-and-arm mark obtained by forgetting an observation's outcome. -/
def observedMark {d : ℕ} (o : Obs d) : Fin d × Bool := (o.x, o.a)

/-- [Forgetting the outcome is measurable](goal). -/
lemma measurable_observedMark {d : ℕ} : Measurable (observedMark : Obs d → Fin d × Bool) := by
  have htuple : Measurable (fun o : Obs d => (o.x, o.a, o.y)) := by
    rw [measurable_iff_comap_le]
    rfl
  exact Measurable.prodMk htuple.fst htuple.snd.fst

/-- The one-observation law of the finite cell-and-arm mark. -/
noncomputable def observedMarkLaw {d : ℕ} (P : RealLaw d) : Measure (Fin d × Bool) :=
  Measure.map observedMark P.observedLaw

/-- The finite product law of observed binary marks is a probability measure. -/
instance {d : ℕ} (P : RealLaw d) : IsProbabilityMeasure (observedMarkLaw P) :=
  Measure.isProbabilityMeasure_map measurable_observedMark.aemeasurable

/-- [The factorization field of a real law gives the exact mass of every cell-and-arm atom after
  outcomes are forgotten](goal). -/
lemma realMass_observedMarkLaw_singleton {d : ℕ} (P : RealLaw d)
    (k : Fin d) (a : Bool) :
    realMass (observedMarkLaw P) {(k, a)} =
      P.cellMass k * (if a then P.propensity k else 1 - P.propensity k) := by
  unfold observedMarkLaw realMass
  rw [Measure.map_apply measurable_observedMark
    (measurableSet_singleton (k, a))]
  have hfactor := P.arm_outcome_factorization a k Set.univ MeasurableSet.univ
  let _ : IsProbabilityMeasure (P.outcomeLaw a k) := P.outcome_isProbability a k
  have hout : realMass (P.outcomeLaw a k) Set.univ = 1 := by
    simp [realMass]
  rw [hout, mul_one] at hfactor
  rw [show observedMark ⁻¹' {(k, a)} =
      {o : Obs d | o.x = k ∧ o.a = a ∧ o.y ∈ Set.univ} by
    ext o
    simp [observedMark]]
  simpa only [realMass, Set.mem_univ, and_true] using hfactor.symm

/-- [Mapping every coordinate of a real-outcome product sample to its finite cell-and-arm mark
  gives the product of the corresponding mark law](goal). -/
lemma productLaw_map_observedMarks {n d : ℕ} (P : RealLaw d) :
    Measure.map (fun sample : Fin n → Obs d => fun i => observedMark (sample i))
        (productLaw n P) =
      Measure.pi (fun _ : Fin n => observedMarkLaw P) := by
  unfold productLaw observedMarkLaw
  exact Measure.pi_map_pi (fun _ : Fin n => measurable_observedMark.aemeasurable)

/-- Number of occurrences of one arm and cell in the first `n` marks of a stream. -/
def streamArmCount {d : ℕ} (z : ℕ → Fin d × Bool)
    (n : ℕ) (a : Bool) (k : Fin d) : ℕ :=
  ((Finset.range n).filter fun i => (z i).1 = k ∧ (z i).2 = a).card

/-- Total number of marks in a cell in the first `n` stream positions. -/
def streamCellCount {d : ℕ} (z : ℕ → Fin d × Bool)
    (n : ℕ) (k : Fin d) : ℕ :=
  streamArmCount z n false k + streamArmCount z n true k

/-- Usable occupancy in the first `n` positions of a cell-and-arm stream. -/
def streamUsableTotal {d : ℕ} (z : ℕ → Fin d × Bool) (n : ℕ) : ℕ :=
  ∑ k : Fin d,
    if 0 < streamArmCount z n false k ∧ 0 < streamArmCount z n true k then
      streamCellCount z n k
    else 0

/-- If [the shorter prefix is contained in the longer prefix](hyp:hmn), [arm counts cannot
  decrease when a stream prefix is enlarged](goal). -/
lemma streamArmCount_mono {d : ℕ} (z : ℕ → Fin d × Bool)
    {m n : ℕ} (hmn : m ≤ n) (a : Bool) (k : Fin d) :
    streamArmCount z m a k ≤ streamArmCount z n a k := by
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
  exact ⟨lt_of_lt_of_le hi.1 hmn, hi.2⟩

/-- If [the shorter prefix is contained in the longer prefix](hyp:hmn), [usable occupancy cannot
  decrease when a stream prefix is enlarged](goal). -/
lemma streamUsableTotal_mono {d : ℕ} (z : ℕ → Fin d × Bool)
    {m n : ℕ} (hmn : m ≤ n) :
    streamUsableTotal z m ≤ streamUsableTotal z n := by
  unfold streamUsableTotal
  apply Finset.sum_le_sum
  intro k _
  by_cases hm : 0 < streamArmCount z m false k ∧ 0 < streamArmCount z m true k
  · have hn : 0 < streamArmCount z n false k ∧ 0 < streamArmCount z n true k :=
      ⟨lt_of_lt_of_le hm.1 (streamArmCount_mono z hmn false k),
        lt_of_lt_of_le hm.2 (streamArmCount_mono z hmn true k)⟩
    rw [if_pos hm, if_pos hn]
    unfold streamCellCount
    exact Nat.add_le_add (streamArmCount_mono z hmn false k)
      (streamArmCount_mono z hmn true k)
  · rw [if_neg hm]
    exact Nat.zero_le _

/-- If [the specified object](hyp:lam) and [the specified function or embedding](hyp:g) and [the
  stream functional is measurable](hyp:hg) and [the stream functional decreases with sample
  size](hyp:hanti), [a reusable monotone de-Poissonization inequality. If a nonnegative stream
  statistic decreases with the prefix length, then its fixed-`n` expectation, multiplied by the
  probability that the independent Poisson count does not exceed `n`, is bounded by the statistic
  evaluated at that random count](goal). -/
lemma iidStream_antitone_depoissonization
    {X : Type*} [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P]
    (lam : ℝ≥0) (n : ℕ) (g : ℕ → (ℕ → X) → ℝ≥0∞)
    (hg : Measurable (fun z : ℕ × (ℕ → X) => g z.1 z.2))
    (hanti : ∀ z m n, m ≤ n → g n z ≤ g m z) :
    (poissonMeasure lam) (Iic n) *
        (∫⁻ z, g n z ∂iidStreamLaw P) ≤
      ∫⁻ z, g z.1 z.2 ∂poissonIIDStreamLaw P lam := by
  let A : ℝ≥0∞ := ∫⁻ z, g n z ∂iidStreamLaw P
  have hiter : Measurable (fun m : ℕ => ∫⁻ z, g m z ∂iidStreamLaw P) :=
    hg.lintegral_prod_right'
  calc
    (poissonMeasure lam) (Iic n) * A =
        ∫⁻ _m in Iic n, A ∂poissonMeasure lam := by
          rw [setLIntegral_const]
          simp [mul_comm]
    _ ≤ ∫⁻ m in Iic n, ∫⁻ z, g m z ∂iidStreamLaw P ∂poissonMeasure lam := by
      apply setLIntegral_mono hiter
      intro m hm
      apply lintegral_mono
      intro z
      exact hanti z m n hm
    _ ≤ ∫⁻ m, ∫⁻ z, g m z ∂iidStreamLaw P ∂poissonMeasure lam :=
      setLIntegral_le_lintegral _ _
    _ = ∫⁻ z, g z.1 z.2 ∂poissonIIDStreamLaw P lam := by
      unfold poissonIIDStreamLaw
      exact (lintegral_prod _ hg.aemeasurable).symm

private lemma occupancy_poissonPMFReal_succ_mul (r : ℝ≥0) (n : ℕ) :
    (n + 1 : ℝ) * poissonPMFReal r (n + 1) =
      (r : ℝ) * poissonPMFReal r n := by
  rw [poissonPMFReal, poissonPMFReal, Nat.factorial_succ, pow_succ]
  push_cast
  field_simp

private lemma occupancy_poissonPMF_succ_mul (r : ℝ≥0) (n : ℕ) :
    ((n + 1 : ℕ) : ℝ≥0∞) * poissonPMF r (n + 1) =
      (r : ℝ≥0∞) * poissonPMF r n := by
  change ((n + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (poissonPMFReal r (n + 1)) =
    (r : ℝ≥0∞) * ENNReal.ofReal (poissonPMFReal r n)
  have h := congrArg ENNReal.ofReal (occupancy_poissonPMFReal_succ_mul r n)
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)] at h
  rw [ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_natCast, ENNReal.ofReal_one] at h
  simpa using h

/-- If [the specified object](hyp:r), [the first moment of a Poisson count is its intensity, in
  `lintegral` form](goal). -/
lemma poisson_lintegral_natCast (r : ℝ≥0) :
    ∫⁻ n : ℕ, (n : ℝ≥0∞) ∂poissonMeasure r = (r : ℝ≥0∞) := by
  rw [lintegral_countable']
  simp_rw [poissonMeasure_singleton_eq_poissonPMF]
  rw [tsum_eq_zero_add' ENNReal.summable]
  simp only [Nat.cast_zero, zero_mul, zero_add]
  simp_rw [occupancy_poissonPMF_succ_mul]
  rw [ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]

/-- [A Poisson count with mean `n/2` is at most `n` with probability at least one half](goal). -/
lemma poisson_half_intensity_Iic (n : ℕ) :
    (1 / 2 : ℝ≥0∞) ≤
      (poissonMeasure ((n : ℝ≥0) / 2)) (Iic n) := by
  let r : ℝ≥0 := (n : ℝ≥0) / 2
  let tail : Set ℕ := {m | n + 1 ≤ m}
  have hmarkov := meas_ge_le_lintegral_div
    (μ := poissonMeasure r) (f := fun m : ℕ => (m : ℝ≥0∞))
    (measurable_of_countable _).aemeasurable
    (ε := ((n + 1 : ℕ) : ℝ≥0∞)) (by simp) (by simp)
  rw [poisson_lintegral_natCast] at hmarkov
  have htail_set : {m : ℕ | ((n + 1 : ℕ) : ℝ≥0∞) ≤ (m : ℝ≥0∞)} = tail := by
    ext m
    simp only [tail]
    norm_cast
  rw [htail_set] at hmarkov
  have hratio : (r : ℝ≥0∞) / ((n + 1 : ℕ) : ℝ≥0∞) ≤ 1 / 2 := by
    rw [ENNReal.div_le_iff_le_mul (Or.inl (by simp)) (Or.inl (by simp))]
    change (((n : ℝ≥0) / 2 : ℝ≥0) : ℝ≥0∞) ≤
      (1 / 2 : ℝ≥0∞) * (n + 1 : ℕ)
    rw [ENNReal.coe_div (by norm_num)]
    change (n : ℝ≥0∞) / 2 ≤ 1 / 2 * (n + 1 : ℕ)
    rw [div_eq_mul_inv, one_div, mul_comm (n : ℝ≥0∞)]
    gcongr
    exact_mod_cast Nat.le_succ n
  have htail : (poissonMeasure r) tail ≤ 1 / 2 := hmarkov.trans hratio
  have hcompl : tail = (Iic n)ᶜ := by
    ext m
    simp [tail]
  have htail_meas : MeasurableSet tail := by
    rw [hcompl]
    exact measurableSet_Iic.compl
  have hIic : (poissonMeasure r) (Iic n) = 1 - (poissonMeasure r) tail := by
    rw [← compl_compl (Iic n), ← hcompl,
      measure_compl htail_meas (measure_ne_top _ _), measure_univ]
  rw [hIic]
  apply ENNReal.le_sub_of_add_le_right
    (ne_top_of_le_ne_top ENNReal.one_ne_top (htail.trans (by norm_num)))
  calc
    (1 / 2 : ℝ≥0∞) + (poissonMeasure r) tail ≤ 1 / 2 + 1 / 2 :=
      add_le_add_right htail _
    _ = 1 := by simpa only [one_div] using ENNReal.inv_two_add_inv_two

/-- The zero-occupancy indicator on a stream prefix. -/
def streamUsableZero {d : ℕ} (n : ℕ) (z : ℕ → Fin d × Bool) : ℝ≥0∞ :=
  if streamUsableTotal z n = 0 then 1 else 0

/-- The combined zero-event and reciprocal penalty used for monotone
de-Poissonization. -/
noncomputable def streamUsablePenalty {d : ℕ} (n : ℕ)
    (z : ℕ → Fin d × Bool) : ℝ≥0∞ :=
  if streamUsableTotal z n = 0 then 1
  else ((streamUsableTotal z n : ℕ) : ℝ≥0∞)⁻¹

/-- Usable occupancy computed directly on a finite tuple of cell-and-arm marks. -/
def finiteMarkUsableTotal {n d : ℕ} (sample : Fin n → Fin d × Bool) : ℕ :=
  ∑ k : Fin d,
    let n0 := (Finset.univ.filter fun i => (sample i).1 = k ∧ (sample i).2 = false).card
    let n1 := (Finset.univ.filter fun i => (sample i).1 = k ∧ (sample i).2 = true).card
    if 0 < n0 ∧ 0 < n1 then n0 + n1 else 0

/-- [Range-based stream occupancy equals direct occupancy of the finite prefix](goal). -/
lemma streamUsableTotal_eq_finiteMarkUsableTotal {d : ℕ}
    (z : ℕ → Fin d × Bool) (n : ℕ) :
    streamUsableTotal z n = finiteMarkUsableTotal (fun i : Fin n => z i) := by
  classical
  unfold streamUsableTotal streamCellCount streamArmCount finiteMarkUsableTotal
  apply Finset.sum_congr rfl
  intro k _
  have hcount (a : Bool) :
      ((Finset.range n).filter fun i => (z i).1 = k ∧ (z i).2 = a).card =
        (Finset.univ.filter fun i : Fin n => (z i).1 = k ∧ (z i).2 = a).card := by
    rw [← Finset.image_fin_univ, Finset.filter_image]
    exact Finset.card_image_of_injective _ Fin.val_injective
  rw [hcount false, hcount true]

/-- [Fixed-prefix usable occupancy is measurable as a function of the stream](goal). -/
lemma measurable_streamUsableTotal_fixed {d : ℕ} (n : ℕ) :
    Measurable (fun z : ℕ → Fin d × Bool => streamUsableTotal z n) := by
  have hprefix : Measurable (fun z : ℕ → Fin d × Bool => fun i : Fin n => z i) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply (i : ℕ)
  rw [show (fun z : ℕ → Fin d × Bool => streamUsableTotal z n) =
      finiteMarkUsableTotal ∘ (fun z => fun i : Fin n => z i) by
    funext z
    exact streamUsableTotal_eq_finiteMarkUsableTotal z n]
  exact (measurable_of_countable finiteMarkUsableTotal).comp hprefix

/-- If [the shorter prefix is contained in the longer prefix](hyp:hmn), [the zero-occupancy
  indicator decreases along stream prefixes](goal). -/
lemma streamUsableZero_antitone {d : ℕ} (z : ℕ → Fin d × Bool)
    {m n : ℕ} (hmn : m ≤ n) :
    streamUsableZero n z ≤ streamUsableZero m z := by
  unfold streamUsableZero
  by_cases hm : streamUsableTotal z m = 0
  · rw [if_pos hm]
    split <;> simp
  · have hn : streamUsableTotal z n ≠ 0 := by
      exact Nat.ne_zero_of_lt (lt_of_lt_of_le (Nat.pos_of_ne_zero hm)
        (streamUsableTotal_mono z hmn))
    simp [hm, hn]

/-- If [the shorter prefix is contained in the longer prefix](hyp:hmn), [the combined
  zero-event/reciprocal penalty decreases along stream prefixes](goal). -/
lemma streamUsablePenalty_antitone {d : ℕ} (z : ℕ → Fin d × Bool)
    {m n : ℕ} (hmn : m ≤ n) :
    streamUsablePenalty n z ≤ streamUsablePenalty m z := by
  unfold streamUsablePenalty
  by_cases hm : streamUsableTotal z m = 0
  · rw [if_pos hm]
    by_cases hn : streamUsableTotal z n = 0
    · simp [hn]
    · rw [if_neg hn]
      apply (ENNReal.inv_le_one).2
      exact_mod_cast Nat.one_le_iff_ne_zero.2 hn
  · have hn : streamUsableTotal z n ≠ 0 := by
      exact Nat.ne_zero_of_lt (lt_of_lt_of_le (Nat.pos_of_ne_zero hm)
        (streamUsableTotal_mono z hmn))
    rw [if_neg hm, if_neg hn]
    exact ENNReal.inv_le_inv.mpr (by exact_mod_cast streamUsableTotal_mono z hmn)

/-! ## Independent Poisson arm-cell counts -/

/-- The identity partition of the finite cell-and-arm mark space. -/
def armCellPartition (d : ℕ) :
    FiniteMeasurablePartition (Fin d × Bool) (Fin d × Bool) where
  cell := id
  measurable_cell := measurable_id

/-- Counts of every arm-cell atom in a finite marked sample. -/
noncomputable def markedArmCellCounts {d : ℕ}
    (s : FiniteSample ((Fin d × Bool) × ℝ)) : Fin d × Bool → ℕ :=
  fun j => ((armCellPartition d).restrictCell j s).count

/-- [The arm-cell count vector is measurable](goal). -/
lemma measurable_markedArmCellCounts {d : ℕ} :
    Measurable (markedArmCellCounts :
      FiniteSample ((Fin d × Bool) × ℝ) → Fin d × Bool → ℕ) := by
  unfold markedArmCellCounts
  exact measurable_pi_lambda _ fun j =>
    measurable_finiteSample_count.comp ((armCellPartition d).measurable_restrictCell j)

/-- If [the specified object](hyp:lam), [under the marked Poisson construction, all arm-cell
  counts are jointly independent Poisson variables with their atom-specific intensities](goal). -/
lemma map_markedArmCellCounts_finiteMarkedPoissonSampleLaw
    (P : Measure (Fin d × Bool)) [IsProbabilityMeasure P]
    (lam : ℝ≥0) :
    Measure.map markedArmCellCounts
        (finiteMarkedPoissonSampleLaw P (Measure.dirac 0) lam) =
      Measure.pi (fun j : Fin d × Bool =>
        poissonMeasure (lam * (P {j}).toNNReal)) := by
  let p := armCellPartition d
  let R : Measure ℝ := Measure.dirac 0
  let mu := finiteMarkedPoissonSampleLaw P R lam
  have hjoint := FiniteMeasurablePartition.map_restrictPartition_finiteMarkedPoissonSampleLaw
    p P R lam
  let countFamily : (Fin d × Bool → FiniteSample ((Fin d × Bool) × ℝ)) →
      (Fin d × Bool → ℕ) := fun q j => (q j).count
  have hcountFamily : Measurable countFamily :=
    measurable_pi_lambda _ fun j => measurable_finiteSample_count.comp (measurable_pi_apply j)
  calc
    Measure.map markedArmCellCounts mu =
        Measure.map countFamily (Measure.map p.restrictPartition mu) := by
      rw [Measure.map_map hcountFamily p.measurable_restrictPartition]
      rfl
    _ = Measure.map countFamily
        (Measure.pi (fun j : Fin d × Bool =>
          finiteMarkedPoissonSampleLaw (p.cellObservationLaw P j) R
            (lam * p.cellMass P j))) := by rw [hjoint]
    _ = Measure.pi (fun j : Fin d × Bool =>
        Measure.map FiniteSample.count
          (finiteMarkedPoissonSampleLaw (p.cellObservationLaw P j) R
            (lam * p.cellMass P j))) := by
      exact Measure.pi_map_pi (fun _ => measurable_finiteSample_count.aemeasurable)
    _ = Measure.pi (fun j : Fin d × Bool =>
        poissonMeasure (lam * (P {j}).toNNReal)) := by
      congr with j
      rw [finiteMarkedPoissonSampleLaw_map_count]
      rfl

/-- Regroup an arm-cell count vector into false/true counts within each cell. -/
def regroupArmCellCounts {d : ℕ} (c : Fin d × Bool → ℕ) : Fin d → ℕ × ℕ :=
  fun k => (c (k, false), c (k, true))

/-- Usable occupancy computed from a regrouped pair of arm counts. -/
def usableTotalOfRegroupedCounts {d : ℕ} (c : Fin d → ℕ × ℕ) : ℕ :=
  ∑ k : Fin d, if 0 < (c k).1 ∧ 0 < (c k).2 then (c k).1 + (c k).2 else 0

/-- If [the specified object](hyp:lam), [the regrouped arm-count vector is the pushforward of the
  independent atom-count product law](goal). -/
lemma map_regroupedArmCellCounts_finiteMarkedPoissonSampleLaw
    (P : Measure (Fin d × Bool)) [IsProbabilityMeasure P]
    (lam : ℝ≥0) :
    Measure.map (regroupArmCellCounts ∘ markedArmCellCounts)
        (finiteMarkedPoissonSampleLaw P (Measure.dirac 0) lam) =
      Measure.map regroupArmCellCounts
        (Measure.pi (fun j : Fin d × Bool =>
          poissonMeasure (lam * (P {j}).toNNReal))) := by
  rw [← Measure.map_map (measurable_of_countable regroupArmCellCounts)
    measurable_markedArmCellCounts,
    map_markedArmCellCounts_finiteMarkedPoissonSampleLaw]

/-- [Regrouping the atom counts preserves the stream usable-total formula](goal). -/
lemma usableTotalOfRegroupedCounts_eq {d : ℕ} (z : ℕ → Fin d × Bool) (n : ℕ) :
    usableTotalOfRegroupedCounts
        (regroupArmCellCounts (fun j => streamArmCount z n j.2 j.1)) =
      streamUsableTotal z n := by
  rfl

/-- The marked finite-sample usable total is exactly the deterministic
regrouping of its arm-cell count vector. -/
noncomputable def markedUsableTotal {d : ℕ}
    (s : FiniteSample ((Fin d × Bool) × ℝ)) : ℕ :=
  usableTotalOfRegroupedCounts (regroupArmCellCounts (markedArmCellCounts s))

/-- [Restricting a retained marked prefix to an arm-cell and counting it agrees with the
  corresponding range count in the underlying stream](goal). -/
lemma markedArmCellCounts_streamToFiniteSample {d : ℕ}
    (q : ℕ × (ℕ → (Fin d × Bool) × ℝ)) (j : Fin d × Bool) :
    markedArmCellCounts (streamToFiniteSample q) j =
      streamArmCount (fun i => (q.2 i).1) q.1 j.2 j.1 := by
  classical
  unfold markedArmCellCounts FiniteMeasurablePartition.restrictCell
    FiniteMeasurablePartition.cellIndices armCellPartition streamToFiniteSample
    streamArmCount FiniteSample.count FiniteSample.points
  dsimp only
  rw [← Finset.image_fin_univ, Finset.filter_image]
  rw [Finset.card_image_of_injective _ Fin.val_injective]
  congr 1
  ext i
  simp [Prod.ext_iff]

/-- [Marked-sample usable occupancy is exactly usable occupancy of the retained random prefix
  after the auxiliary real marks are forgotten](goal). -/
lemma markedUsableTotal_streamToFiniteSample {d : ℕ}
    (q : ℕ × (ℕ → (Fin d × Bool) × ℝ)) :
    markedUsableTotal (streamToFiniteSample q) =
      streamUsableTotal (fun i => (q.2 i).1) q.1 := by
  unfold markedUsableTotal
  rw [← usableTotalOfRegroupedCounts_eq (fun i => (q.2 i).1) q.1]
  congr 2
  funext j
  exact markedArmCellCounts_streamToFiniteSample q j

/-- If [the specified object](hyp:lam), [the marked Poisson law is the random-prefix iid-stream
  law on observation-mark pairs](goal). -/
lemma finiteMarkedPoissonSampleLaw_eq_randomPrefixLaw
    (P : Measure (Fin d × Bool)) [IsProbabilityMeasure P] (lam : ℝ≥0) :
    finiteMarkedPoissonSampleLaw P (Measure.dirac 0) lam =
      Measure.map streamToFiniteSample
        (poissonIIDStreamLaw (P.prod (Measure.dirac 0)) lam) := by
  rfl

end CausalSmith.Stat.DiscreteAteHeterogeneityFrontier
