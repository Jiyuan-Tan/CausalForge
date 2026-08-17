import Causalean.Stat.Concentration.VarianceAdaptiveVCExpectedMaximal.Basic
import Causalean.Stat.Concentration.Covering.CoveringNumber

/-!
# Polynomial empirical covers in Dudley's metric space

This module translates the finite-cover certificate used by the
variance-adaptive maximal inequality into total boundedness and a numerical
covering-number bound for Causalean's empirical function space.  These are the
two deterministic inputs expected by the existing Dudley theorem.
-/

namespace Causalean.Stat.Concentration

open MeasureTheory

universe u v

variable {𝒳 : Type u} [MeasurableSpace 𝒳] {ι : Type v}

/-- A positive-envelope polynomial empirical covering certificate makes the
class image totally bounded in the empirical root-mean-square pseudometric on
every nonempty finite sample. -/
theorem HasPolynomialEmpiricalL2Cover.totallyBounded
    {F : ι → 𝒳 → ℝ} {U A v : ℝ}
    (hcover : HasPolynomialEmpiricalL2Cover F U A v)
    (hmeas : ∀ i, Measurable (F i)) (hU : 0 < U)
    {n : ℕ} (S : Fin n → 𝒳) (hn : 0 < n) :
    TotallyBounded (Set.univ : Set (EmpiricalFunctionSpace F S)) := by
  /-
  Follow `real_vcSubgraph_empirical_totallyBounded`: at an arbitrary radius
  `r > 0`, use relative scale `min 1 (r/U)`, map the finite index cover into
  `EmpiricalFunctionSpace F S`, and rewrite its `L²(Pₙ)` distances with
  `measureL2Dist_finiteSampleMeasure_eq_empiricalDist`.
  -/
  classical
  rw [Metric.totallyBounded_iff]
  intro r hr
  let ε : ℝ := min 1 (r / U)
  have hε : 0 < ε := lt_min (by norm_num) (div_pos hr hU)
  have hε1 : ε ≤ 1 := min_le_left _ _
  obtain ⟨C, hCcover, _hCcard⟩ := hcover S hn ε hε hε1
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

/-- **Covering-number bound from an empirical cover.** Suppose [`F` has polynomial empirical
$L^2$ covering numbers with envelope `U`, base `A`, and exponent `v`](hyp:hcover), [every member
of `F` is measurable](hyp:hmeas), [the envelope `U` is strictly positive](hyp:hU), [the sample `S`
has positive size `n`](hyp:hn), and [the relative scale `ε` lies in the interval $(0,1]$
](hyp:hε,hε1); then [Dudley's empirical covering number of the class at radius `ε * U`, taken in
the totally bounded empirical pseudometric space this cover furnishes, is at most the real power
`(A / ε) ^ v`](goal). -/
theorem HasPolynomialEmpiricalL2Cover.coveringNumber_le
    {F : ι → 𝒳 → ℝ} {U A v : ℝ}
    (hcover : HasPolynomialEmpiricalL2Cover F U A v)
    (hmeas : ∀ i, Measurable (F i)) (hU : 0 < U)
    {n : ℕ} (S : Fin n → 𝒳) (hn : 0 < n)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    let htot := hcover.totallyBounded hmeas hU S hn
    (coveringNumber htot (ε * U) : ℝ) ≤ Real.rpow (A / ε) v := by
  /-
  Follow `real_vcSubgraph_empirical_coveringNumber_le`, using the explicit
  `hcover S hn ε hε hε1` witness instead of the pseudo-dimension cover.  The
  minimal covering cardinality is at most the image of that witness, whose
  cardinality is bounded by the supplied real power.
  -/
  classical
  dsimp only
  let htot := hcover.totallyBounded hmeas hU S hn
  let r := ε * U
  have hr : 0 < r := mul_pos hε hU
  obtain ⟨C, hCcover, hCcard⟩ := hcover S hn ε hε hε1
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
    (Nat.find (coveringNumber_exists htot hr) : ℝ) ≤ T.card := by
      exact_mod_cast
        Nat.find_min' (coveringNumber_exists htot hr) ⟨T, rfl, hTcover⟩
    _ ≤ C.card := by exact_mod_cast Finset.card_image_le
    _ ≤ Real.rpow (A / ε) v := hCcard

end Causalean.Stat.Concentration
