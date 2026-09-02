/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.Partition.CellLaws
import Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.Superposition.Retention
import Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.KL
import Causalean.Mathlib.InformationTheory.KLBind
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Finite-sample maps and de-Poissonization

This file provides measurable maps between dependent finite samples, padded
streams, and canonical marked configurations. It also records the Poisson
count identity and a reusable exponential lower-tail bound used to transfer
random-size experiments to fixed sample sizes.
-/

open MeasureTheory ProbabilityTheory Set Filter Asymptotics
open scoped ENNReal NNReal

namespace Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

/-- Mapping every point of a finite sample preserves its random count. -/
-- @node: finiteSampleMap
def finiteSampleMap {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (f : X → Y) (s : FiniteSample X) : FiniteSample Y :=
  ⟨s.count, fun i => f (s.points i)⟩

/-- Pointwise mapping of dependent finite samples is measurable. -/
-- @node: measurable_finiteSampleMap
@[fun_prop]
lemma measurable_finiteSampleMap {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (f : X → Y) (hf : Measurable f) :
    Measurable (finiteSampleMap f : FiniteSample X → FiniteSample Y) := by
  intro s hs
  rw [MeasurableSpace.measurableSet_iInf] at hs ⊢
  intro n
  let g : (Fin n → X) → (Fin n → Y) := fun x i => f (x i)
  have hg : Measurable g :=
    measurable_pi_lambda _ fun i => hf.comp (measurable_pi_apply i)
  have hsn := hs n
  change MeasurableSet (fixedSizeEmbed n ⁻¹' s) at hsn
  change MeasurableSet ((fun x : Fin n → X =>
    ⟨n, fun i => f (x i)⟩) ⁻¹' s)
  exact hsn.preimage hg

/-- Mapping commutes with fixed-size embedding. -/
-- @node: finiteSampleMap_fixedSizeEmbed
lemma finiteSampleMap_fixedSizeEmbed {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] (f : X → Y) (n : ℕ) (x : Fin n → X) :
    finiteSampleMap f (fixedSizeEmbed n x) =
      fixedSizeEmbed n (fun i => f (x i)) := rfl

/-- Equal restrictions and equal cell masses give equal normalized cell laws. -/
-- @node: cellObservationLaw_eq_of_restrict_eq
lemma cellObservationLaw_eq_of_restrict_eq
    {X ι : Type*} [MeasurableSpace X] [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι]
    (p : FiniteMeasurablePartition X ι) (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (j : ι)
    (hpos : μ (p.cellSet j) ≠ 0)
    (hmass : μ (p.cellSet j) = ν (p.cellSet j))
    (hrest : μ.restrict (p.cellSet j) = ν.restrict (p.cellSet j)) :
    p.cellObservationLaw μ j = p.cellObservationLaw ν j := by
  unfold FiniteMeasurablePartition.cellObservationLaw
  have hν : ν (p.cellSet j) ≠ 0 := by simpa [← hmass]
  rw [dif_neg hpos, dif_neg hν, ← hmass, hrest]

/-- Consider [a sample size `n` that is at least `1`](hyp:hn) and [a nonnegative
KL budget `B`](hyp:hB), and suppose [the KL divergence between `n` independent
identically distributed draws from `P` and from `Q` is at most `B`](hyp:hpi).
Then [the KL divergence between the marked Poisson experiments with mean count
`2n`, mark law `R`, and intensity measures `P` and `Q` respectively (both built
over the same baseline `P`) is at most `2B`](goal). -/
-- @node: markedPoissonKL_le_two_mul_of_piKL
lemma markedPoissonKL_le_two_mul_of_piKL
    {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    (P Q : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (R : Measure ℝ) [IsProbabilityMeasure R]
    (n : ℕ) (hn : 1 ≤ n) {B : ℝ} (hB : 0 ≤ B)
    (hpi : InformationTheory.klDiv
      (Measure.pi (fun _ : Fin n => P))
      (Measure.pi (fun _ : Fin n => Q)) ≤ ENNReal.ofReal B) :
    InformationTheory.klDiv
        (finiteMeasureMarkedPoissonLaw P P R (2 * n))
        (finiteMeasureMarkedPoissonLaw Q P R (2 * n)) ≤
      ENNReal.ofReal (2 * B) := by
  let i : Fin n := ⟨0, lt_of_lt_of_le Nat.zero_lt_one hn⟩
  have hone_le : InformationTheory.klDiv P Q ≤
      InformationTheory.klDiv (Measure.pi (fun _ : Fin n => P))
        (Measure.pi (fun _ : Fin n => Q)) := by
    have h := Causalean.Mathlib.InformationTheory.Measure.klDiv_map_le
      (measurable_pi_apply i) (μ := Measure.pi (fun _ : Fin n => P))
        (ν := Measure.pi (fun _ : Fin n => Q))
    rw [Measure.pi_map_eval, Measure.pi_map_eval] at h
    simpa using h
  have hprod_ne : InformationTheory.klDiv
      (Measure.pi (fun _ : Fin n => P))
      (Measure.pi (fun _ : Fin n => Q)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hpi
  have hone_ne : InformationTheory.klDiv P Q ≠ ⊤ :=
    ne_top_of_le_ne_top hprod_ne hone_le
  have hguards := InformationTheory.klDiv_ne_top_iff.mp hone_ne
  have hreal := Causalean.Mathlib.InformationTheory.productKL_tensorization_of_finite
    n P Q hguards.1 hguards.2
  have heq : InformationTheory.klDiv
      (Measure.pi (fun _ : Fin n => P))
      (Measure.pi (fun _ : Fin n => Q)) =
      (n : ℝ≥0∞) * InformationTheory.klDiv P Q := by
    have hmul : (n : ℝ≥0∞) * InformationTheory.klDiv P Q ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.natCast_ne_top n) hone_ne
    apply (ENNReal.toReal_eq_toReal_iff' hprod_ne hmul).mp
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast]
    exact hreal
  rw [klDiv_finiteMeasureMarkedPoissonLaw P Q P R (2 * n) (by simp)]
  rw [show (((2 : ℝ≥0) * (n : ℝ≥0) : ℝ≥0) : ℝ≥0∞) =
      (2 : ℝ≥0∞) * (n : ℝ≥0∞) by norm_num,
    mul_assoc, ← heq]
  calc
    (2 : ℝ≥0∞) * InformationTheory.klDiv
        (Measure.pi (fun _ : Fin n => P))
        (Measure.pi (fun _ : Fin n => Q)) ≤
        2 * ENNReal.ofReal B := mul_le_mul_right hpi 2
    _ = ENNReal.ofReal (2 * B) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num

/-- A marked finite sample supplies its first `n` observation coordinates when
it is long enough, and otherwise supplies a fixed fallback tuple. -/
-- @node: canonicalPrefixObservations
def canonicalPrefixObservations {X : Type*} [MeasurableSpace X]
    (x₀ : X) (n : ℕ) (s : FiniteSample (X × ℝ)) : Fin n → X :=
  if h : n ≤ s.count then fun k => (s.points (Fin.castLE h k)).1
  else fun _ => x₀

/-- Reading a fixed prefix from a canonical finite configuration is measurable. -/
-- @node: measurable_canonicalPrefixObservations
@[fun_prop]
lemma measurable_canonicalPrefixObservations {X : Type*} [MeasurableSpace X]
    (x₀ : X) (n : ℕ) :
    Measurable (canonicalPrefixObservations x₀ n :
      FiniteSample (X × ℝ) → Fin n → X) := by
  unfold canonicalPrefixObservations
  apply measurable_pi_lambda
  intro k t ht
  rw [MeasurableSpace.measurableSet_iInf]
  intro m
  change MeasurableSet ((fun x : Fin m → X × ℝ =>
    (if h : n ≤ m then fun k => (x (Fin.castLE h k)).1 else fun _ => x₀) k) ⁻¹' t)
  by_cases h : n ≤ m
  · simp only [dif_pos h]
    exact ht.preimage ((measurable_pi_apply (Fin.castLE h k)).fst)
  · simp only [dif_neg h]
    exact measurable_const ht

/-- On the successful-count event, the canonical marked-Poisson
configuration's first `n` observations have the unnormalised product law. -/
-- @node: map_canonicalPrefixObservations_restrict_count_ge
lemma map_canonicalPrefixObservations_restrict_count_ge
    {X : Type*} [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P]
    (R : Measure ℝ) [IsProbabilityMeasure R] [NullSingletonClass R]
    (lam : ℝ≥0) (x₀ : X) (n : ℕ) :
    Measure.map (canonicalPrefixObservations x₀ n)
        ((canonicalMarkedPoissonSampleLaw P R lam).restrict
          (FiniteSample.count ⁻¹' Ici n)) =
      (poissonMeasure lam) (Ici n) • Measure.pi (fun _ : Fin n => P) := by
  let μ := finiteMarkedPoissonSampleLaw P R lam
  have hcount : orderByMarks ⁻¹'
      (FiniteSample.count ⁻¹' Ici n : Set (FiniteSample (X × ℝ))) =
      FiniteSample.count ⁻¹' Ici n := by
    ext s
    change (n ≤ (orderByMarks s).count) ↔ n ≤ s.count
    rw [orderByMarks_count]
  rw [canonicalMarkedPoissonSampleLaw,
    Measure.restrict_map measurable_orderByMarks
      (measurable_finiteSample_count (measurableSet_Ici)),
    hcount,
    Measure.map_map (measurable_canonicalPrefixObservations x₀ n)
      measurable_orderByMarks]
  have hfun : canonicalPrefixObservations x₀ n ∘ orderByMarks =
      retainedObservations x₀ n := by
    funext s
    unfold canonicalPrefixObservations retainedObservations
    by_cases h : n ≤ s.count
    · simp only [orderByMarks_count, dif_pos h, Function.comp_apply]
      funext k
      congr 2
    · simp only [orderByMarks_count, dif_neg h, Function.comp_apply]
  rw [hfun]
  exact map_retainedObservations_restrict_count_ge P R lam x₀ n

/-- The lower tail used in de-Poissonization is exponentially small. -/
lemma poisson_two_n_lower_tail (n : ℕ) :
    (poissonMeasure (2 * n)) {k | k < n} ≤
      ENNReal.ofReal (Real.exp (-(n : ℝ) * (1 - Real.log 2))) := by
  rw [show {k : ℕ | k < n} = (↑(Finset.range n) : Set ℕ) by ext k; simp]
  rw [← MeasureTheory.sum_measure_singleton]
  simp_rw [poissonMeasure_singleton_eq_poissonPMF]
  have hterm : ∀ k ∈ Finset.range n,
      poissonPMF (2 * n) k ≤
        ENNReal.ofReal (Real.exp (-(n : ℝ) * (1 - Real.log 2))) * poissonPMF n k := by
    intro k hk
    have hreal : poissonPMFReal (2 * (n : ℝ≥0)) k ≤
        Real.exp (-(n : ℝ) * (1 - Real.log 2)) *
          poissonPMFReal (n : ℝ≥0) k := by
      unfold poissonPMFReal
      rw [← mul_div_assoc]
      apply (div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < k.factorial)).2
      have hn0 : (0 : ℝ) ≤ n := by positivity
      have hpow : (2 : ℝ) ^ k ≤ 2 ^ n :=
        pow_le_pow_right₀ (by norm_num) (Finset.mem_range.1 hk).le
      have htarget : Real.exp (-(n : ℝ) * (1 - Real.log 2)) =
          Real.exp (-(n : ℝ)) * (2 : ℝ) ^ n := by
        rw [show -(n : ℝ) * (1 - Real.log 2) =
            -(n : ℝ) + Real.log 2 * n by ring,
          Real.exp_add, show Real.log 2 * (n : ℝ) = (n : ℝ) * Real.log 2 by ring,
          Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      have hexp2 : Real.exp (-((2 : ℝ) * (n : ℝ))) =
          Real.exp (-(n : ℝ)) * Real.exp (-(n : ℝ)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      norm_num only [NNReal.smul_def, NNReal.coe_natCast, NNReal.coe_mul, Nat.cast_ofNat]
      rw [mul_pow, htarget]
      change Real.exp (-(2 * (n : ℝ))) * ((2 : ℝ) ^ k * (n : ℝ) ^ k) ≤ _
      rw [hexp2]
      calc
        Real.exp (-(n : ℝ)) * Real.exp (-(n : ℝ)) *
              ((2 : ℝ) ^ k * (n : ℝ) ^ k) =
            (Real.exp (-(n : ℝ)) * Real.exp (-(n : ℝ)) * (n : ℝ) ^ k) * 2 ^ k := by
              ring
        _ ≤ (Real.exp (-(n : ℝ)) * Real.exp (-(n : ℝ)) * (n : ℝ) ^ k) * 2 ^ n :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
        _ = Real.exp (-(n : ℝ)) * 2 ^ n *
            (Real.exp (-(n : ℝ)) * (n : ℝ) ^ k) := by ring
    unfold poissonPMF
    change ENNReal.ofReal (poissonPMFReal (2 * n) k) ≤
      ENNReal.ofReal (Real.exp (-(n : ℝ) * (1 - Real.log 2))) *
        ENNReal.ofReal (poissonPMFReal n k)
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    exact ENNReal.ofReal_le_ofReal hreal
  calc
    ∑ k ∈ Finset.range n, poissonPMF (2 * n) k
        ≤ ∑ k ∈ Finset.range n,
            ENNReal.ofReal (Real.exp (-(n : ℝ) * (1 - Real.log 2))) * poissonPMF n k :=
      Finset.sum_le_sum hterm
    _ = ENNReal.ofReal (Real.exp (-(n : ℝ) * (1 - Real.log 2))) *
          ∑ k ∈ Finset.range n, poissonPMF n k := by rw [Finset.mul_sum]
    _ ≤ ENNReal.ofReal (Real.exp (-(n : ℝ) * (1 - Real.log 2))) * 1 := by
      gcongr
      exact ((poissonPMF n).property.summable.sum_le_tsum _ (fun _ _ => bot_le)).trans_eq
        (poissonPMF n).property.tsum_eq
    _ = _ := mul_one _

/-- A finite sample embeds into a count-and-stream representation by padding
all coordinates beyond its count with a fixed fallback observation. -/
-- @node: finiteSamplePaddedStream
def finiteSamplePaddedStream {X : Type*} [MeasurableSpace X]
    (x0 : X) (s : FiniteSample X) : ℕ × (ℕ → X) :=
  (s.count, fun k => if h : k < s.count then s.points ⟨k, h⟩ else x0)

-- @node: finiteSamplePaddedStream_measurable
@[fun_prop]
lemma finiteSamplePaddedStream_measurable {X : Type*} [MeasurableSpace X]
    (x0 : X) : Measurable (finiteSamplePaddedStream x0) := by
  intro t ht
  rw [MeasurableSpace.measurableSet_iInf]
  intro n
  change MeasurableSet ((fun s : Fin n → X =>
    finiteSamplePaddedStream x0 ⟨n, s⟩) ⁻¹' t)
  apply ht.preimage
  apply measurable_const.prodMk
  apply measurable_pi_lambda
  intro k
  by_cases hk : k < n
  · let i : Fin n := ⟨k, hk⟩
    simpa [finiteSamplePaddedStream, FiniteSample.count, FiniteSample.points, hk, i]
      using (measurable_pi_apply i : Measurable (fun s : Fin n → X => s i))
  · simp [finiteSamplePaddedStream, FiniteSample.count, hk]

-- @node: streamToFiniteSample_paddedStream
lemma streamToFiniteSample_paddedStream {X : Type*} [MeasurableSpace X]
    (x0 : X) (s : FiniteSample X) :
    streamToFiniteSample (finiteSamplePaddedStream x0 s) = s := by
  cases s with
  | mk n s =>
      change (⟨n, fun k => if h : k < n then s ⟨k, h⟩ else x0⟩ :
        Σ n : ℕ, Fin n → X) = ⟨n, s⟩
      congr
      funext k
      simp

-- @node: finiteSamplePaddedStream_range
lemma finiteSamplePaddedStream_range {X : Type*} [MeasurableSpace X]
    (x0 : X) :
    Set.range (finiteSamplePaddedStream x0) =
      {z : ℕ × (ℕ → X) | ∀ k, z.1 ≤ k → z.2 k = x0} := by
  ext z
  constructor
  · rintro ⟨s, rfl⟩ k hk
    have hnot : ¬k < s.count := Nat.not_lt_of_ge hk
    simp [finiteSamplePaddedStream, hnot]
  · intro hz
    refine ⟨streamToFiniteSample z, ?_⟩
    apply Prod.ext
    · rfl
    · funext k
      by_cases hk : k < z.1
      · simp [finiteSamplePaddedStream, FiniteSample.count,
          FiniteSample.points, streamToFiniteSample, hk]
      · simp [finiteSamplePaddedStream, FiniteSample.count,
          FiniteSample.points, streamToFiniteSample, hk, hz k (Nat.le_of_not_gt hk)]

/-- Finite samples over a nonempty standard Borel space are standard Borel.
The explicit padded-stream presentation supplies the compatible Polish
topology missing from the generic dependent-sum instance. -/
-- @node: finiteSample_standardBorelSpace
noncomputable instance finiteSample_standardBorelSpace
    {X : Type*} [MeasurableSpace X] [StandardBorelSpace X] [Nonempty X] :
    StandardBorelSpace (FiniteSample X) := by
  let x0 : X := Classical.choice ‹Nonempty X›
  let rangeSet : Set (ℕ × (ℕ → X)) := Set.range (finiteSamplePaddedStream x0)
  have hrange : MeasurableSet rangeSet := by
    dsimp [rangeSet]
    rw [finiteSamplePaddedStream_range x0]
    rw [show {z : ℕ × (ℕ → X) | ∀ k, z.1 ≤ k → z.2 k = x0} =
        ⋂ k : ℕ, {z | k < z.1} ∪ {z | z.2 k = x0} by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_union]
      constructor
      · intro h k
        by_cases hk : k < z.1
        · exact Or.inl hk
        · exact Or.inr (h k (Nat.le_of_not_gt hk))
      · intro h k hk
        exact (h k).resolve_left (Nat.not_lt_of_ge hk)]
    apply MeasurableSet.iInter
    intro k
    exact (measurableSet_lt measurable_const measurable_fst).union
      ((measurableSet_singleton x0).preimage
        ((measurable_pi_apply k).comp measurable_snd))
  let e : FiniteSample X ≃ᵐ rangeSet :=
    { toEquiv :=
        { toFun := fun s => ⟨finiteSamplePaddedStream x0 s, ⟨s, rfl⟩⟩
          invFun := fun z => streamToFiniteSample z.1
          left_inv := streamToFiniteSample_paddedStream x0
          right_inv := by
            intro z
            apply Subtype.ext
            obtain ⟨s, hs⟩ := z.2
            change finiteSamplePaddedStream x0 (streamToFiniteSample z.1) = z.1
            rw [← hs, streamToFiniteSample_paddedStream] }
      measurable_toFun := by
        exact (finiteSamplePaddedStream_measurable x0).subtype_mk
          (h := fun s => ⟨s, rfl⟩)
      measurable_invFun := by
        exact measurable_streamToFiniteSample.comp measurable_subtype_coe }
  letI hsb : StandardBorelSpace rangeSet := hrange.standardBorel
  letI upgraded : UpgradedStandardBorel rangeSet := upgradeStandardBorel rangeSet
  letI : TopologicalSpace rangeSet := upgraded.toTopologicalSpace
  letI : BorelSpace rangeSet := upgraded.toBorelSpace
  letI : PolishSpace rangeSet := upgraded.toPolishSpace
  let tau : TopologicalSpace (FiniteSample X) :=
    (inferInstance : TopologicalSpace rangeSet).induced e
  refine ⟨⟨tau, ?_, ?_⟩⟩
  · exact e.measurableEmbedding.borelSpace ⟨rfl⟩
  · exact e.toEquiv.polishSpace_induced

-- @node: canonicalMarkedPoissonSampleLaw_map_count
lemma canonicalMarkedPoissonSampleLaw_map_count
    {X : Type*} [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P]
    (R : Measure ℝ) [IsProbabilityMeasure R] (lam : ℝ≥0) :
    Measure.map FiniteSample.count
        (canonicalMarkedPoissonSampleLaw P R lam) = poissonMeasure lam := by
  unfold canonicalMarkedPoissonSampleLaw
  rw [Measure.map_map measurable_finiteSample_count measurable_orderByMarks]
  simpa only [Function.comp_def, orderByMarks_count] using
    finiteMarkedPoissonSampleLaw_map_count P R lam

/-- When the intensity measure is already a probability law, the finite-measure
Poisson wrapper agrees with the ordinary marked-Poisson sample law. -/
theorem finiteMeasureMarkedPoissonLaw_probability_eq
    {X : Type*} [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P]
    (P0 : Measure X) [IsProbabilityMeasure P0]
    (R : Measure ℝ) [IsProbabilityMeasure R] (lam : ℝ≥0) :
    finiteMeasureMarkedPoissonLaw P P0 R lam =
      finiteMarkedPoissonSampleLaw P R lam := by
  have hP : P ≠ 0 := by
    intro h
    have : P Set.univ = 1 := by simp
    simp [h] at this
  have hnorm : normalizedFiniteMeasure P P0 = P := by
    unfold normalizedFiniteMeasure
    rw [dif_neg hP]
    simp
  have hmass : finiteMeasureMass P = 1 := by
    unfold finiteMeasureMass
    simp
  unfold finiteMeasureMarkedPoissonLaw
  rw [hmass, mul_one]
  congr 2

end Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
