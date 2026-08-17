import CausalSmith.Stat.STAT_BddUniformLogPenalty_Research.Causal.Basic
import Mathlib.Combinatorics.SetFamily.Shatter
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# VC index of planar Euclidean balls

The statement is phrased directly as non-shattering of finite point sets of
cardinality at least four, which is the paper's “VC index at most four”.
-/

open Set

namespace CausalSmith.Stat.BddUniformLogPenalty

/-- A finite planar set is shattered by closed Euclidean balls. -/
def ShatteredByClosedBalls (S : Finset Score) : Prop :=
  ∀ T : Finset Score, T ⊆ S →
    ∃ c : Score, ∃ r : ℝ, 0 ≤ r ∧
      ∀ z ∈ S, (z ∈ T ↔ dist z c ≤ r)

/-- Closed planar Euclidean balls have VC index at most four. -/
def EuclideanBallsVCProperty : Prop :=
  ∀ S : Finset Score, 4 ≤ S.card → ¬ ShatteredByClosedBalls S
  -- @realizes d_P(closed Euclidean balls have VC index at most four)
  -- @realizes K_\square(kernel support induces closed balls)

-- @node: lem:euclidean-balls-vc
/-- The collection of all closed Euclidean balls in `ℝ²` has VC index at most
four. Consequently the fixed Euclidean metric and uniform kernel meet CTY's
actual VC alternative. -/
lemma euclidean_balls_vc : EuclideanBallsVCProperty := by
  classical
  intro S hcard hshatter
  obtain ⟨U, hUS, hUcard⟩ := Finset.exists_subset_card_eq hcard
  let e : Fin 4 ≃ U := (U.equivFinOfCardEq hUcard).symm
  let z : Fin 4 → Score := fun i ↦ (e i : Score)
  have hzS (i : Fin 4) : z i ∈ S := hUS (e i).property
  let Φ : Score → (Fin 4 → ℝ) := fun x ↦ ![1, x 0, x 1, ‖x‖ ^ 2]
  have hweighted (l : Fin 4 → ℝ) (w : Fin 4 → ℝ)
      (hsum : ∑ i, l i • Φ (z i) = w) (c : Score) (r : ℝ) :
      ∑ i, l i * (dist (z i) c ^ 2 - r ^ 2) =
        w 3 - 2 * c 0 * w 1 - 2 * c 1 * w 2 + (‖c‖ ^ 2 - r ^ 2) * w 0 := by
    have hc (j : Fin 4) : ∑ i, l i * Φ (z i) j = w j := by
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using congrFun hsum j
    have hc0 := hc 0
    have hc1 := hc 1
    have hc2 := hc 2
    have hc3 := hc 3
    simp [Φ] at hc0 hc1 hc2 hc3
    simp only [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two,
      Real.norm_eq_abs, sq_abs] at hc3
    simp only [EuclideanSpace.dist_sq_eq, EuclideanSpace.norm_sq_eq,
      Fin.sum_univ_two, Real.norm_eq_abs, Real.dist_eq, sq_abs]
    simp only [Fin.sum_univ_four] at hc0 hc1 hc2 hc3 ⊢
    ring_nf at hc0 hc1 hc2 hc3 ⊢
    linear_combination hc3 - 2 * c 0 * hc1 - 2 * c 1 * hc2 +
      (c 0 ^ 2 + c 1 ^ 2 - r ^ 2) * hc0
  have hsign_contra (l : Fin 4 → ℝ) (w : Fin 4 → ℝ)
      (hsum : ∑ i, l i • Φ (z i) = w) (hw0 : w 0 = 0)
      (hwEval : ∀ c : Score, ∀ r : ℝ, 0 ≤ r →
        ¬ (∑ i, l i * (dist (z i) c ^ 2 - r ^ 2) < 0))
      (hnz : ∃ i, l i ≠ 0) : False := by
    have hlsum : ∑ i, l i = 0 := by
      have h := congrFun hsum 0
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Φ,
        Matrix.cons_val_zero, mul_one] using h.trans hw0
    obtain ⟨ineg, hineg⟩ : ∃ i, l i < 0 := by
      by_contra hn
      push_neg at hn
      obtain ⟨i, hi⟩ := hnz
      have hi' : 0 < l i := lt_of_le_of_ne (hn i) (Ne.symm hi)
      have hpos : 0 < ∑ i, l i := Finset.sum_pos' (fun j _ ↦ hn j)
        ⟨i, Finset.mem_univ i, hi'⟩
      linarith
    let T : Finset Score := S.filter fun x ↦ ∃ i, z i = x ∧ 0 < l i
    have hTS : T ⊆ S := Finset.filter_subset _ _
    obtain ⟨c, r, hr, hball⟩ := hshatter T hTS
    have hterm (i : Fin 4) : l i * (dist (z i) c ^ 2 - r ^ 2) ≤ 0 := by
      by_cases hi : 0 < l i
      · have hmem : z i ∈ T := Finset.mem_filter.mpr ⟨hzS i, ⟨i, rfl, hi⟩⟩
        have hd := (hball (z i) (hzS i)).mp hmem
        have hdist : 0 ≤ dist (z i) c := dist_nonneg
        have hsq : dist (z i) c ^ 2 ≤ r ^ 2 := by nlinarith
        exact mul_nonpos_of_nonneg_of_nonpos hi.le (sub_nonpos.mpr hsq)
      · have hmem : z i ∉ T := by
          simp only [T, Finset.mem_filter, hzS i, true_and, not_exists, not_and]
          intro j hj
          have : j = i := by
            apply e.injective
            exact Subtype.ext hj
          simpa [this] using hi
        have hd : r < dist (z i) c := lt_of_not_ge ((hball (z i) (hzS i)).not.mp hmem)
        have hdist : 0 ≤ dist (z i) c := dist_nonneg
        have hsq : 0 < dist (z i) c ^ 2 - r ^ 2 := by nlinarith
        exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hi) hsq.le
    have hstrict : l ineg * (dist (z ineg) c ^ 2 - r ^ 2) < 0 := by
      have hmem : z ineg ∉ T := by
        simp only [T, Finset.mem_filter, hzS ineg, true_and, not_exists, not_and]
        intro j hj
        have : j = ineg := by
          apply e.injective
          exact Subtype.ext hj
        simpa [this] using hineg.not_gt
      have hd : r < dist (z ineg) c := lt_of_not_ge ((hball (z ineg) (hzS ineg)).not.mp hmem)
      have hdist : 0 ≤ dist (z ineg) c := dist_nonneg
      have hsq : 0 < dist (z ineg) c ^ 2 - r ^ 2 := by nlinarith
      exact mul_neg_of_neg_of_pos hineg hsq
    have htotal : ∑ i, l i * (dist (z i) c ^ 2 - r ^ 2) < 0 := by
      have hlt := Finset.sum_lt_sum (s := Finset.univ)
        (fun i _ ↦ hterm i) ⟨ineg, Finset.mem_univ ineg, hstrict⟩
      simpa using hlt
    exact hwEval c r hr htotal
  by_cases hlin : LinearIndependent ℝ (fun i ↦ Φ (z i))
  · let b : Module.Basis (Fin 4) ℝ (Fin 4 → ℝ) :=
      basisOfLinearIndependentOfCardEqFinrank hlin (by simp)
    let w : Fin 4 → ℝ := Pi.single 3 1
    let l : Fin 4 → ℝ := fun i ↦ b.repr w i
    have hsum : ∑ i, l i • Φ (z i) = w := by
      simpa only [l, b, coe_basisOfLinearIndependentOfCardEqFinrank] using b.sum_repr w
    apply hsign_contra l w hsum (by simp [w])
    · intro c r hr hneg
      have heq := hweighted l w hsum c r
      have hw3 : w 3 = 1 := by simp [w]
      have hw1 : w 1 = 0 := by simp [w]
      have hw2 : w 2 = 0 := by simp [w]
      have hw0' : w 0 = 0 := by simp [w]
      rw [hw3, hw1, hw2, hw0'] at heq
      norm_num at heq
      linarith
    · have hwne : w ≠ 0 := by
        intro hw
        have := congrFun hw 3
        simp [w] at this
      by_contra hn
      push_neg at hn
      have : l = 0 := funext hn
      rw [this] at hsum
      simp at hsum
      exact hwne hsum.symm
  · obtain ⟨l, hsum, hnz⟩ := Fintype.not_linearIndependent_iff.mp hlin
    exact hsign_contra l 0 hsum rfl (by
      intro c r hr hneg
      have heq := hweighted l 0 hsum c r
      simp at heq
      linarith) hnz

end CausalSmith.Stat.BddUniformLogPenalty
