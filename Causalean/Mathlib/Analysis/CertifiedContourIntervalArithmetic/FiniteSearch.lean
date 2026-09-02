import Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.CertifiedReal
import Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Quadrature
import Mathlib.Data.Prod.Lex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Total finite searches, deterministic ties, and measurability

This module provides the finite control flow used by certified numerical
procedures.  It returns a least successful candidate with an explicit fallback,
breaks equal real scores by index, and proves that the resulting finite outputs
are Borel measurable.
-/

namespace Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic
namespace FiniteSearch

private theorem countable_ratInterval : Countable RatInterval :=
  Function.Injective.countable (f := fun x : RatInterval => (x.lo, x.hi)) (by
    intro a b h
    cases a
    cases b
    simp_all)

private theorem countable_complexRatInterval : Countable ComplexRatInterval := by
  letI : Countable RatInterval := countable_ratInterval
  exact Function.Injective.countable
    (f := fun x : ComplexRatInterval => (x.re, x.im)) (by
      intro a b h
      cases a
      cases b
      simp_all)

/-- Rational intervals carry the countable discrete measurable space used for certified outputs. -/
instance : MeasurableSpace RatInterval := ⊤

/-- Complex rational rectangles carry the countable discrete measurable space
used for certified outputs. -/
instance : MeasurableSpace ComplexRatInterval := ⊤

/-- The least successful index of a nonempty finite Boolean family is returned,
or zero if none succeeds. -/
def leastTrue {n : ℕ} (accept : Fin (n + 1) → Bool) : Fin (n + 1) :=
  if h : (Finset.univ.filter fun i => accept i).Nonempty then
    (Finset.univ.filter fun i => accept i).min' h
  else 0

/-- When at least one Boolean test succeeds, the returned index succeeds. -/
theorem leastTrue_accepts {n : ℕ} {accept : Fin (n + 1) → Bool}
    (h : ∃ i, accept i = true) : accept (leastTrue accept) = true := by
  unfold leastTrue
  split_ifs with hne
  · have hm := Finset.min'_mem (Finset.univ.filter fun i => accept i) hne
    exact (Finset.mem_filter.mp hm).2
  · obtain ⟨i, hi⟩ := h
    exfalso
    apply hne
    refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, ?_⟩⟩
    exact hi

/-- Every successful index is no smaller than the successful index returned by the search. -/
theorem leastTrue_le {n : ℕ} {accept : Fin (n + 1) → Bool}
    {i : Fin (n + 1)} (hi : accept i = true) : leastTrue accept ≤ i := by
  unfold leastTrue
  split_ifs with hne
  · apply Finset.min'_le
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
  · exfalso
    apply hne
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩

/-- If no Boolean test succeeds, the total search returns index zero. -/
theorem leastTrue_eq_zero {n : ℕ} {accept : Fin (n + 1) → Bool}
    (h : ∀ i, accept i = false) : leastTrue accept = 0 := by
  unfold leastTrue
  split_ifs with hne
  · obtain ⟨i, hi⟩ := hne
    have hait : accept i = true := (Finset.mem_filter.mp hi).2
    rw [h i] at hait
    contradiction
  · rfl

/-- Finite refinement returns the first candidate interval meeting a rational
width tolerance, with a total fallback. -/
def finiteRefine {n : ℕ} (candidates : Fin (n + 1) → RatInterval) (ε : PosRat) :
    RatInterval :=
  candidates (leastTrue fun i => decide ((candidates i).width ≤ ε.1))

/-- If a candidate meets the requested width, finite refinement returns the
least such candidate and meets the width. -/
theorem finiteRefine_width {n : ℕ} {candidates : Fin (n + 1) → RatInterval}
    (ε : PosRat) (h : ∃ i, (candidates i).width ≤ ε.1) :
    (finiteRefine candidates ε).width ≤ ε.1 := by
  unfold finiteRefine
  apply of_decide_eq_true
  apply leastTrue_accepts (accept := fun i => decide ((candidates i).width ≤ ε.1))
  obtain ⟨i, hi⟩ := h
  refine ⟨i, ?_⟩
  rw [decide_eq_true_eq]
  exact hi

/-- Finite refinement is measurable as a function of a finite vector of
rational interval candidates. -/
@[fun_prop]
theorem measurable_finiteRefine {n : ℕ} (ε : PosRat) :
    Measurable (fun candidates : Fin (n + 1) → RatInterval => finiteRefine candidates ε) := by
  letI : Countable RatInterval := countable_ratInterval
  exact fun s _ => (Set.to_countable _).measurableSet

/-- The least-score index minimizes lexicographically by real score and then by
the original finite index. -/
noncomputable def leastScoreIndex {n : ℕ} (score : Fin (n + 1) → ℝ) : Fin (n + 1) := by
  classical
  let keys : Finset (ℝ ×ₗ Fin (n + 1)) :=
    Finset.univ.image (fun i => toLex (score i, i))
  have hkeys : keys.Nonempty := by
    refine ⟨toLex (score 0, 0), ?_⟩
    exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  exact (ofLex (keys.min' hkeys)).2

/-- The selected least-score index has score no larger than every competing score. -/
theorem leastScoreIndex_minimal {n : ℕ} (score : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) : score (leastScoreIndex score) ≤ score i := by
  classical
  let keys : Finset (ℝ ×ₗ Fin (n + 1)) :=
    Finset.univ.image (fun j => toLex (score j, j))
  have hkeys : keys.Nonempty := by
    refine ⟨toLex (score 0, 0), ?_⟩
    exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  have hm := Finset.min'_mem keys hkeys
  obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hm
  have hselected : leastScoreIndex score = j := by
    rw [leastScoreIndex]
    change (ofLex (keys.min' hkeys)).2 = j
    rw [← hj]
    rfl
  rw [hselected]
  have hle := Finset.min'_le keys (toLex (score i, i))
    (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  rw [← hj] at hle
  exact le_of_not_gt fun hgt => by
    have hlex : toLex (score i, i) < toLex (score j, j) :=
      Prod.Lex.left _ _ hgt
    exact (not_lt_of_ge hle) hlex

/-- Equal minimal scores are resolved in favor of the smaller original index. -/
theorem leastScoreIndex_tie {n : ℕ} (score : Fin (n + 1) → ℝ)
    {i : Fin (n + 1)} (hi : score i = score (leastScoreIndex score)) :
    leastScoreIndex score ≤ i := by
  classical
  let keys : Finset (ℝ ×ₗ Fin (n + 1)) :=
    Finset.univ.image (fun j => toLex (score j, j))
  have hkeys : keys.Nonempty := by
    refine ⟨toLex (score 0, 0), ?_⟩
    exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  have hm := Finset.min'_mem keys hkeys
  obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hm
  have hselected : leastScoreIndex score = j := by
    rw [leastScoreIndex]
    change (ofLex (keys.min' hkeys)).2 = j
    rw [← hj]
    rfl
  rw [hselected] at hi ⊢
  have hle := Finset.min'_le keys (toLex (score i, i))
    (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  rw [← hj] at hle
  exact le_of_not_gt fun hgt => by
    have hlex : toLex (score i, i) < toLex (score j, j) := by
      rw [hi]
      exact Prod.Lex.right _ hgt
    exact (not_lt_of_ge hle) hlex

/-- For [a sample-size index `n`](hyp:n), [the function that selects, from a vector of `n+1`
real scores, the smallest index attaining the least score is measurable with respect to the
Borel σ-algebra on the score vector space and the discrete σ-algebra on the finite index
set](goal). -/
@[fun_prop]
theorem measurable_leastScoreIndex {n : ℕ} :
    Measurable (leastScoreIndex : (Fin (n + 1) → ℝ) → Fin (n + 1)) := by
  apply measurable_to_countable'
  intro i
  have hmeas : MeasurableSet {score : Fin (n + 1) → ℝ |
      ∀ j, score i < score j ∨ (score i = score j ∧ i ≤ j)} := by
    rw [show {score : Fin (n + 1) → ℝ |
        ∀ j, score i < score j ∨ (score i = score j ∧ i ≤ j)} =
        ⋂ j, {score | score i < score j ∨ (score i = score j ∧ i ≤ j)} by
      ext score
      simp]
    apply MeasurableSet.iInter
    intro j
    apply MeasurableSet.union
    · exact measurableSet_lt (measurable_pi_apply i) (measurable_pi_apply j)
    · apply MeasurableSet.inter
      · exact measurableSet_eq_fun (measurable_pi_apply i) (measurable_pi_apply j)
      · exact MeasurableSet.const _
  rw [show (leastScoreIndex : (Fin (n + 1) → ℝ) → Fin (n + 1)) ⁻¹' {i} =
      {score | ∀ j, score i < score j ∨ (score i = score j ∧ i ≤ j)} by
    ext score
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
    constructor
    · intro hselected j
      have hmin := leastScoreIndex_minimal score j
      rw [hselected] at hmin
      rcases lt_or_eq_of_le hmin with hlt | heq
      · exact Or.inl hlt
      · exact Or.inr ⟨heq, by
          have htie := leastScoreIndex_tie score (i := j) (by
            rw [hselected]
            exact heq.symm)
          rwa [hselected] at htie⟩
    · intro hall
      let k := leastScoreIndex score
      have hik : i ≤ k := by
        rcases hall k with hlt | heq
        · exact False.elim ((not_lt_of_ge (leastScoreIndex_minimal score i)) hlt)
        · exact heq.2
      have hki : k ≤ i := by
        apply leastScoreIndex_tie score
        rcases hall k with hlt | heq
        · exact False.elim ((not_lt_of_ge (leastScoreIndex_minimal score i)) hlt)
        · exact heq.1
      exact le_antisymm hki hik]
  exact hmeas

/-- A finite least-success search is measurable when every individual success
event is measurable. -/
@[fun_prop]
theorem measurable_leastTrue {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (accept : Fin (n + 1) → Ω → Bool)
    (haccept : ∀ i, Measurable (accept i)) :
    Measurable (fun ω => leastTrue (fun i => accept i ω)) := by
  have hvector : Measurable (fun ω => fun i => accept i ω) :=
    by fun_prop
  apply (show Measurable (leastTrue : (Fin (n + 1) → Bool) → Fin (n + 1)) from ?_).comp hvector
  exact fun s _ => (Set.to_countable _).measurableSet

/-- The rational infimum enclosure is measurable as a function of its finite
rational node vector. -/
@[fun_prop]
theorem measurable_infEnclosure {n : ℕ} (hn : 0 < n) (L : ℚ) (hL : 0 ≤ L) :
    Measurable (fun nodes : Fin (n + 1) → RatInterval =>
      CircleMesh.infEnclosure
        (fun k => if hk : k < n + 1 then nodes ⟨k, hk⟩ else nodes 0) L hL n hn) := by
  letI : Countable RatInterval := countable_ratInterval
  exact fun s _ => (Set.to_countable _).measurableSet

/-- The rational supremum enclosure is measurable as a function of its finite
rational node vector. -/
@[fun_prop]
theorem measurable_supEnclosure {n : ℕ} (hn : 0 < n) (L : ℚ) (hL : 0 ≤ L) :
    Measurable (fun nodes : Fin (n + 1) → RatInterval =>
      CircleMesh.supEnclosure
        (fun k => if hk : k < n + 1 then nodes ⟨k, hk⟩ else nodes 0) L hL n hn) := by
  letI : Countable RatInterval := countable_ratInterval
  exact fun s _ => (Set.to_countable _).measurableSet

/-- The rational complex integral enclosure is measurable as a function of its
finite node rectangles. -/
@[fun_prop]
theorem measurable_integralEnclosure {n : ℕ} (hn : 0 < n) (L : ℚ) (hL : 0 ≤ L) :
    Measurable (fun nodes : Fin (n + 1) → ComplexRatInterval =>
      CircleMesh.integralEnclosure
        (fun k => if hk : k < n + 1 then nodes ⟨k, hk⟩ else nodes 0) L hL n hn) := by
  letI : Countable ComplexRatInterval := countable_complexRatInterval
  exact fun s _ => (Set.to_countable _).measurableSet

end FiniteSearch
end Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic
