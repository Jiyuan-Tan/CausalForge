import Causalean.Stat.Concentration.Covering.RealValuedVCSubgraph.Algebra
import Causalean.Stat.Concentration.Covering.DudleyEntropy

/-!
# Empirical-measure and Dudley bridges

This module specializes the arbitrary-probability-measure VC-subgraph theorem
to the empirical law of a nonempty finite sample, translates its `L²` distance
to the existing empirical pseudometric, and exposes a fixed total-boundedness
witness and covering-number bound consumable by Dudley chaining.
-/

namespace Causalean.Stat.Concentration

open MeasureTheory
open Causalean.Stat.Concentration
open scoped BigOperators ENNReal

universe u v

variable {𝒳 : Type u} [MeasurableSpace 𝒳] {ι : Type v}

/-- The empirical probability law of a nonempty sample is the normalized sum
of Dirac masses at its observations. -/
noncomputable def finiteSampleMeasure {n : ℕ} (S : Fin n → 𝒳) : Measure 𝒳 :=
  (ENNReal.ofReal (n : ℝ))⁻¹ • ∑ i : Fin n, Measure.dirac (S i)

/-- The empirical law of a positive-size finite sample is a probability
measure. -/
theorem finiteSampleMeasure_isProbabilityMeasure
    {n : ℕ} (S : Fin n → 𝒳) (hn : 0 < n) :
    IsProbabilityMeasure (finiteSampleMeasure S) := by
  refine ⟨?_⟩
  simp only [finiteSampleMeasure, Measure.smul_apply,
    Measure.finset_sum_apply, Measure.dirac_apply_of_mem (Set.mem_univ _),
    Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.ofReal_natCast]
  simpa [nsmul_eq_mul] using
    ENNReal.inv_mul_cancel (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn))
      (ENNReal.natCast_ne_top n)

/-- Integration against the empirical law is the arithmetic average of a
measurable real-valued function over the sample. -/
theorem integral_finiteSampleMeasure
    {n : ℕ} (S : Fin n → 𝒳) (hn : 0 < n)
    {f : 𝒳 → ℝ} (hf : Measurable f) :
    ∫ x, f x ∂finiteSampleMeasure S =
      (1 / (n : ℝ)) * ∑ i : Fin n, f (S i) := by
  rw [finiteSampleMeasure, integral_smul_measure]
  rw [integral_finset_sum_measure]
  · simp only [integral_dirac' f _ hf.stronglyMeasurable,
      ENNReal.toReal_inv, ENNReal.ofReal_natCast, ENNReal.toReal_natCast, smul_eq_mul]
    rw [one_div]
  · intro i hi
    exact integrable_dirac' hf.stronglyMeasurable (by simp)

/-- `L²` distance under the empirical law agrees exactly with the empirical
root-mean-square distance used by the existing Dudley API. -/
theorem measureL2Dist_finiteSampleMeasure_eq_empiricalDist
    {n : ℕ} (S : Fin n → 𝒳) (hn : 0 < n)
    {f g : 𝒳 → ℝ} (hf : Measurable f) (hg : Measurable g) :
    measureL2Dist (finiteSampleMeasure S) f g = empiricalDist S f g := by
  rw [measureL2Dist, empiricalDist, empiricalNorm,
    integral_finiteSampleMeasure S hn ((hf.fun_sub hg).pow_const 2)]
  simp only [Pi.sub_apply, one_div]

/-- The arbitrary-measure VC-subgraph theorem specializes to the empirical
law of every positive-size finite sample. -/
theorem real_vcSubgraph_empirical_l2_covering
    [Nonempty ι] {F : ι → 𝒳 → ℝ} {d n : ℕ}
    (hmeas : ∀ i, Measurable (F i))
    (hpdim : HasPseudoDimAtMost F d)
    {U ε : ℝ} (hU : 0 < U) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (henvelope : ∀ i x, |F i x| ≤ U)
    (S : Fin n → 𝒳) (hn : 0 < n) :
    L2CoveringNumberLe (finiteSampleMeasure S) F (ε * U)
      (vcSubgraphCoverBound d ε) := by
  letI : IsProbabilityMeasure (finiteSampleMeasure S) :=
    finiteSampleMeasure_isProbabilityMeasure S hn
  exact real_vcSubgraph_l2_covering F d hmeas hpdim hU hε hε1 henvelope
    (finiteSampleMeasure S)

/-- A pseudo-dimension certificate makes the existing empirical function
space totally bounded on every positive-size finite sample. -/
theorem real_vcSubgraph_empirical_totallyBounded
    [Nonempty ι] {F : ι → 𝒳 → ℝ} {d n : ℕ}
    (hmeas : ∀ i, Measurable (F i))
    (hpdim : HasPseudoDimAtMost F d)
    {U : ℝ} (hU : 0 < U)
    (henvelope : ∀ i x, |F i x| ≤ U)
    (S : Fin n → 𝒳) (hn : 0 < n) :
    TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S)) := by
  classical
  rw [Metric.totallyBounded_iff]
  intro r hr
  let ε : ℝ := min 1 (r / U)
  have hε : 0 < ε := lt_min (by norm_num) (div_pos hr hU)
  have hε1 : ε ≤ 1 := min_le_left _ _
  obtain ⟨C, hCcard, hCcover⟩ :=
    real_vcSubgraph_empirical_l2_covering hmeas hpdim hU hε hε1
      henvelope S hn
  let T : Finset (EmpiricalFunctionSpace F S) :=
    C.image fun j => ⟨j⟩
  refine ⟨(T : Set (EmpiricalFunctionSpace F S)), T.finite_toSet, ?_⟩
  intro q hq
  obtain ⟨j, hjC, hj⟩ := hCcover q.index
  have hεU : ε * U ≤ r := by
    calc
      ε * U ≤ (r / U) * U :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) (le_of_lt hU)
      _ = r := by field_simp
  have hj' : empiricalDist S (F q.index) (F j) < r := by
    rw [← measureL2Dist_finiteSampleMeasure_eq_empiricalDist S hn
      (hmeas q.index) (hmeas j)]
    exact lt_of_lt_of_le hj hεU
  refine Set.mem_iUnion_of_mem (⟨j⟩ : EmpiricalFunctionSpace F S) ?_
  refine Set.mem_iUnion_of_mem ?_ ?_
  · exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨j, hjC, rfl⟩)
  · exact hj'

/-- The empirical covering number used by Dudley is polynomially bounded at
every envelope-relative radius, with the same arbitrary-measure constants. -/
theorem real_vcSubgraph_empirical_coveringNumber_le
    [Nonempty ι] {F : ι → 𝒳 → ℝ} {d n : ℕ}
    (hmeas : ∀ i, Measurable (F i))
    (hpdim : HasPseudoDimAtMost F d)
    {U ε : ℝ} (hU : 0 < U) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (henvelope : ∀ i x, |F i x| ≤ U)
    (S : Fin n → 𝒳) (hn : 0 < n) :
    let htot := real_vcSubgraph_empirical_totallyBounded
      hmeas hpdim hU henvelope S hn
    coveringNumber htot (ε * U) ≤ vcSubgraphCoverBound d ε := by
  classical
  dsimp only
  let htot := real_vcSubgraph_empirical_totallyBounded
    hmeas hpdim hU henvelope S hn
  let r := ε * U
  have hr : 0 < r := mul_pos hε hU
  obtain ⟨C, hCcard, hCcover⟩ :=
    real_vcSubgraph_empirical_l2_covering hmeas hpdim hU hε hε1
      henvelope S hn
  let T : Finset (EmpiricalFunctionSpace F S) :=
    C.image fun j => ⟨j⟩
  have hTcover : (Set.univ : Set (EmpiricalFunctionSpace F S)) ⊆
      ⋃ y ∈ T, Metric.ball y r := by
    intro q hq
    obtain ⟨j, hjC, hj⟩ := hCcover q.index
    have hj' : empiricalDist S (F q.index) (F j) < r := by
      rw [← measureL2Dist_finiteSampleMeasure_eq_empiricalDist S hn
        (hmeas q.index) (hmeas j)]
      exact hj
    refine Set.mem_iUnion_of_mem (⟨j⟩ : EmpiricalFunctionSpace F S) ?_
    refine Set.mem_iUnion_of_mem ?_ ?_
    · exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨j, hjC, rfl⟩)
    · exact hj'
  rw [coveringNumber_eq htot hr]
  calc
    Nat.find (coveringNumber_exists htot hr) ≤ T.card :=
      Nat.find_min' (coveringNumber_exists htot hr) ⟨T, rfl, hTcover⟩
    _ ≤ C.card := Finset.card_image_le
    _ ≤ vcSubgraphCoverBound d ε := hCcard

/-- **Direct application to the fixed-sample Dudley bound.** For
[a measurable](hyp:hmeas) class of [pseudo-dimension at most d](hyp:hpdim),
[uniformly bounded by a positive envelope U](hyp:hU,henvelope), and
[a positive scale δ strictly less than U/2](hyp:hδ,hδU), evaluated on
[a sample S of positive size n](hyp:hn), [the class's empirical restriction
is totally bounded, its covering number at every relative radius ε in
`(0,1]` obeys the same polynomial bound `vcSubgraphCoverBound d ε`, and
consequently its empirical Rademacher complexity without the outer absolute
value is at most the Dudley entropy-integral bound `4δ + (12/√n) ∫_δ^(U/2)
√(log(coveringNumber x)) dx`](goal). -/
theorem real_vcSubgraph_dudley_example
    [Nonempty ι] {F : ι → 𝒳 → ℝ} {d n : ℕ}
    (hmeas : ∀ i, Measurable (F i))
    (hpdim : HasPseudoDimAtMost F d)
    {U δ : ℝ} (hU : 0 < U) (hδ : 0 < δ) (hδU : δ < U / 2)
    (henvelope : ∀ i x, |F i x| ≤ U)
    (S : Fin n → 𝒳) (hn : 0 < n) :
    ∃ htot : TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S)),
      (∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        coveringNumber htot (ε * U) ≤ vcSubgraphCoverBound d ε) ∧
      empiricalRademacherComplexity_without_abs n F S ≤
        4 * δ + (12 / Real.sqrt n) *
          (∫ x in δ..(U / 2), Real.sqrt (Real.log (coveringNumber htot x))) := by
  let htot := real_vcSubgraph_empirical_totallyBounded
    hmeas hpdim hU henvelope S hn
  refine ⟨htot, ?_, ?_⟩
  · intro ε hε hε1
    simpa [htot] using
      (real_vcSubgraph_empirical_coveringNumber_le hmeas hpdim hU hε hε1
        henvelope S hn)
  · apply dudley_entropy_integral_bound (c := U) hδ htot hn
    · intro i
      classical
      have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
      have hsum :
          (∑ j : Fin n, (F i (S j)) ^ 2) ≤ ∑ _j : Fin n, U ^ 2 := by
        refine Finset.sum_le_sum ?_
        intro j _
        calc
          (F i (S j)) ^ 2 = |F i (S j)| ^ 2 := by rw [sq_abs]
          _ ≤ U ^ 2 :=
            sq_le_sq.mpr (by
              simpa [abs_of_pos hU] using henvelope i (S j))
      have harg :
          (1 / (n : ℝ)) * ∑ j : Fin n, (F i (S j)) ^ 2 ≤ U ^ 2 := by
        calc
          (1 / (n : ℝ)) * ∑ j : Fin n, (F i (S j)) ^ 2
              ≤ (1 / (n : ℝ)) * ∑ _j : Fin n, U ^ 2 :=
                mul_le_mul_of_nonneg_left hsum (by positivity)
          _ = (1 / (n : ℝ)) * ((n : ℝ) * U ^ 2) := by simp
          _ = U ^ 2 := by field_simp [Finset.card_fin, hnR.ne']
      calc
        empiricalNorm S (F i) =
            Real.sqrt ((1 / (n : ℝ)) * ∑ j : Fin n, (F i (S j)) ^ 2) := rfl
        _ ≤ Real.sqrt (U ^ 2) := Real.sqrt_le_sqrt harg
        _ = U := by rw [Real.sqrt_sq_eq_abs, abs_of_pos hU]
    · exact hδU

end Causalean.Stat.Concentration
