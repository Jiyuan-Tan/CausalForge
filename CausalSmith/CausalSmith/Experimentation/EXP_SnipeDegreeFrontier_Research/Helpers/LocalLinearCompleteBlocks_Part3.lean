import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.LocalLinearClass
import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.SnipeVariance
import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.LeastFavourable
import Mathlib.Algebra.Order.Chebyshev
import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.LocalLinearCompleteBlocks_Part1
import CausalSmith.Experimentation.EXP_SnipeDegreeFrontier_Research.Helpers.LocalLinearCompleteBlocks_Part2

/-!
# Signed convex weights: absolute-sum bounds and extreme-point attainment

A self-contained convexity chain: the absolute row sums of a signed convex
combination are controlled by a signed supremum, and the supremum over rows of a
quadratic form is attained at a signed extreme point.
-/

open scoped BigOperators
open Finset

namespace CausalSmith.Experimentation.SnipeDegreeFrontier

open Causalean.Experimentation.DesignBased
/-- Establishes the stated mathematical result for abs sum signed convex weights. -/
lemma absSum_signed_convex_weights
    {K : Type*} [Fintype K] [DecidableEq K]
    (J : Finset K) (hJ : J.Nonempty)
    (B : ℝ) (hB : 0 < B) (a : K → ℝ)
    (ha : ∑ j ∈ J, |a j| ≤ B) :
    ∃ lam : Bool × K → ℝ,
      (∀ c, 0 ≤ lam c) ∧
      (∀ c, c.2 ∉ J → lam c = 0) ∧
      (∑ c, lam c) = 1 ∧
      ∀ (X : K → ℝ),
        ∑ c, lam c * ((if c.1 then (1 : ℝ) else -1) * B * X c.2) =
          ∑ j ∈ J, a j * X j := by
  classical
  let j₀ := hJ.choose
  have hj₀ : j₀ ∈ J := hJ.choose_spec
  let q : K → ℝ := fun j => |a j| / B
  let r : ℝ := 1 - ∑ j ∈ J, q j
  have hq (j : K) : 0 ≤ q j := div_nonneg (abs_nonneg _) hB.le
  have hr : 0 ≤ r := by
    dsimp [r, q]
    rw [sub_nonneg, ← Finset.sum_div]
    exact (div_le_one hB).2 ha
  let sgn : K → Bool := fun j => if 0 ≤ a j then true else false
  let lam : Bool × K → ℝ := fun c =>
    (if c.2 ∈ J ∧ c.1 = sgn c.2 then q c.2 else 0) +
      if c.2 = j₀ then r / 2 else 0
  refine ⟨lam, ?_, ?_, ?_, ?_⟩
  · intro c
    dsimp [lam]
    positivity
  · intro c hc
    dsimp [lam]
    have hcj : c.2 ≠ j₀ := by
      intro h
      apply hc
      simpa [h] using hj₀
    simp [hc, hcj]
  · rw [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    rw [show
        (∑ j : K, ∑ b : Bool, lam (b, j)) =
          (∑ j ∈ J, q j) + r by
      rw [show
          (∑ j : K, ∑ b : Bool, lam (b, j)) =
            ∑ j : K,
              ((if j ∈ J then q j else 0) +
                (if j = j₀ then r else 0)) by
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hjJ : j ∈ J
        · by_cases hs : 0 ≤ a j <;>
            simp [lam, sgn, hs, hjJ, Bool.false_eq_true,
              Bool.true_eq_false] <;>
            split_ifs <;> ring
        · simp [lam, hjJ]
          split_ifs <;> ring]
      rw [Finset.sum_add_distrib]
      simp [hj₀]]
    dsimp [r]
    ring
  · intro X
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    rw [show
        (∑ j : K, ∑ b : Bool,
          lam (b, j) *
            ((if b then (1 : ℝ) else -1) * B * X j)) =
          ∑ j ∈ J, a j * X j by
      rw [show
          (∑ j ∈ J, a j * X j) =
            ∑ j : K, if j ∈ J then a j * X j else 0 by simp]
      apply Finset.sum_congr rfl
      intro j hjmem
      by_cases hj : j ∈ J
      · by_cases hs : 0 ≤ a j
        · have habs : |a j| = a j := abs_of_nonneg hs
          by_cases hj0 : j = j₀
          · have hs0 : 0 ≤ a j₀ := by simpa [← hj0] using hs
            have habs0 : |a j₀| = a j₀ := abs_of_nonneg hs0
            simp [lam, sgn, hj, hs, q, habs, hj0, hj₀, hs0, habs0]
            field_simp [hB.ne'] <;> ring
          · simp [lam, sgn, hj, hs, q, habs, hj0]
            field_simp [hB.ne'] <;> ring
        · have hs' : a j < 0 := lt_of_not_ge hs
          have habs : |a j| = -a j := abs_of_neg hs'
          by_cases hj0 : j = j₀
          · have hs0 : ¬0 ≤ a j₀ := by simpa [← hj0] using hs
            have hs0' : a j₀ < 0 := lt_of_not_ge hs0
            have habs0 : |a j₀| = -a j₀ := abs_of_neg hs0'
            simp [lam, sgn, hj, hs, q, habs, hj0, hj₀, hs0, habs0]
            field_simp [hB.ne'] <;> ring
          · simp [lam, sgn, hj, hs, q, habs, hj0]
            field_simp [hB.ne'] <;> ring
      · simp [lam, hj]]

/-- Establishes the stated mathematical result for abs sum row quadratic le signed sup. -/
lemma absSum_row_quadratic_le_signed_sup
    {Ω K : Type*} [Fintype Ω] [Fintype K] [DecidableEq K]
    (D : FiniteDesign Ω)
    (J : Finset K) (hJ : J.Nonempty)
    (B : ℝ) (hB : 0 < B) (a : K → ℝ)
    (ha : ∑ j ∈ J, |a j| ≤ B)
    (X : K → Ω → ℝ) (Y : Ω → ℝ) :
    D.E (fun z => (Y z + ∑ j ∈ J, a j * X j z) ^ 2) ≤
      (Finset.univ.filter (fun c : Bool × K => c.2 ∈ J)).sup'
        (by
          rcases hJ with ⟨j, hj⟩
          exact ⟨(true, j), by simp [hj]⟩)
        (fun c =>
          D.E (fun z =>
            (Y z + (if c.1 then (1 : ℝ) else -1) * B * X c.2 z) ^ 2)) := by
  classical
  obtain ⟨lam, hlam0, hlamsupp, hlamsum, hlamrep⟩ :=
    absSum_signed_convex_weights J hJ B hB a ha
  let C : Finset (Bool × K) :=
    Finset.univ.filter (fun c : Bool × K => c.2 ∈ J)
  let Q : (Bool × K) → Ω → ℝ := fun c z =>
    Y z + (if c.1 then (1 : ℝ) else -1) * B * X c.2 z
  have hrepr (z : Ω) :
      Y z + ∑ j ∈ J, a j * X j z =
        ∑ c, lam c * Q c z := by
    rw [show (Y z : ℝ) = ∑ c, lam c * Y z by
      rw [← Finset.sum_mul, hlamsum, one_mul]]
    rw [← hlamrep (fun j => X j z)]
    symm
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro c hc
    dsimp [Q]
    ring
  have hjensen (z : Ω) :
      (∑ c, lam c * Q c z) ^ 2 ≤
        ∑ c, lam c * (Q c z) ^ 2 := by
    have hn :
        0 ≤ ∑ c, lam c * (Q c z - ∑ e, lam e * Q e z) ^ 2 := by
      apply Finset.sum_nonneg
      intro c hc
      exact mul_nonneg (hlam0 c) (sq_nonneg _)
    rw [show
        (∑ c, lam c * (Q c z - ∑ e, lam e * Q e z) ^ 2) =
          (∑ c, lam c * (Q c z) ^ 2) -
            (∑ c, lam c * Q c z) ^ 2 by
      let m := ∑ e, lam e * Q e z
      have hexpand :
          (∑ c, lam c * (Q c z - m) ^ 2) =
            (∑ c, lam c * (Q c z) ^ 2) -
              2 * m * (∑ c, lam c * Q c z) +
                m ^ 2 * ∑ c, lam c := by
        rw [show
            (∑ c, lam c * (Q c z - m) ^ 2) =
              ∑ c,
                ((lam c * (Q c z) ^ 2 -
                  2 * m * (lam c * Q c z)) +
                    m ^ 2 * lam c) by
          apply Finset.sum_congr rfl
          intro c hc
          ring]
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
        rw [← Finset.mul_sum, ← Finset.mul_sum]
      rw [hexpand]
      rw [hlamsum]
      dsimp [m]
      ring] at hn
    linarith
  rw [show
      (fun z => (Y z + ∑ j ∈ J, a j * X j z) ^ 2) =
        (fun z => (∑ c, lam c * Q c z) ^ 2) by
    funext z
    rw [hrepr z]]
  calc
    D.E (fun z => (∑ c, lam c * Q c z) ^ 2) ≤
        D.E (fun z => ∑ c, lam c * (Q c z) ^ 2) := by
      have hp (z : Ω) :
          0 ≤ (∑ c, lam c * (Q c z) ^ 2) -
            (∑ c, lam c * Q c z) ^ 2 := sub_nonneg.mpr (hjensen z)
      have hn := D.E_nonneg hp
      rw [FiniteDesign.E_sub] at hn
      linarith
    _ = ∑ c, lam c * D.E (fun z => (Q c z) ^ 2) := by
      rw [FiniteDesign.E_sum]
      apply Finset.sum_congr rfl
      intro c hc
      rw [FiniteDesign.E_const_mul]
    _ ≤ ∑ c, lam c *
        (C.sup'
          (by
            rcases hJ with ⟨j, hj⟩
            exact ⟨(true, j), by simp [C, hj]⟩)
          (fun c => D.E (fun z => (Q c z) ^ 2))) := by
      apply Finset.sum_le_sum
      intro c hc
      by_cases hcC : c ∈ C
      · exact mul_le_mul_of_nonneg_left
          (Finset.le_sup' (fun c => D.E (fun z => (Q c z) ^ 2)) hcC)
          (hlam0 c)
      · have hzero : lam c = 0 := by
          apply hlamsupp
          simpa [C] using hcC
        rw [hzero]
        simp
    _ = C.sup'
        (by
          rcases hJ with ⟨j, hj⟩
          exact ⟨(true, j), by simp [C, hj]⟩)
        (fun c => D.E (fun z => (Q c z) ^ 2)) := by
      rw [← Finset.sum_mul, hlamsum, one_mul]
    _ = (Finset.univ.filter (fun c : Bool × K => c.2 ∈ J)).sup'
        (by
          rcases hJ with ⟨j, hj⟩
          exact ⟨(true, j), by simp [hj]⟩)
        (fun c =>
          D.E (fun z =>
            (Y z + (if c.1 then (1 : ℝ) else -1) * B * X c.2 z) ^ 2)) := by
      rfl

/-- Establishes the stated mathematical result for abs sum rows quadratic exists signed extreme. -/
lemma absSum_rows_quadratic_exists_signed_extreme
    {Ω I K : Type*} [Fintype Ω] [Fintype I] [Fintype K]
    [DecidableEq I] [DecidableEq K]
    (D : FiniteDesign Ω)
    (rows : Finset I)
    (J : I → Finset K)
    (hJ : ∀ i, (J i).Nonempty)
    (B : ℝ) (hB : 0 < B)
    (a : I → K → ℝ)
    (ha : ∀ i ∈ rows, ∑ j ∈ J i, |a i j| ≤ B)
    (X : I → K → Ω → ℝ)
    (Y : Ω → ℝ) :
    ∃ c : I → Bool × K,
      (∀ i ∈ rows, (c i).2 ∈ J i) ∧
      D.E (fun z =>
          (Y z + ∑ i ∈ rows, ∑ j ∈ J i, a i j * X i j z) ^ 2) ≤
        D.E (fun z =>
          (Y z + ∑ i ∈ rows,
            (if (c i).1 then (1 : ℝ) else -1) * B * X i (c i).2 z) ^ 2) := by
  classical
  induction rows using Finset.induction_on generalizing Y with
  | empty =>
      let c : I → Bool × K := fun i => (true, (hJ i).choose)
      refine ⟨c, ?_, ?_⟩
      · intro i hi
        simp at hi
      · simp
  | @insert i rows hi ih =>
      let Yrest : Ω → ℝ := fun z =>
        Y z + ∑ k ∈ rows, ∑ j ∈ J k, a k j * X k j z
      let C : Finset (Bool × K) :=
        Finset.univ.filter (fun c : Bool × K => c.2 ∈ J i)
      have hC : C.Nonempty := by
        rcases hJ i with ⟨j, hj⟩
        exact ⟨(true, j), by simp [C, hj]⟩
      have hrow := absSum_row_quadratic_le_signed_sup
        D (J i) (hJ i) B hB (a i) (ha i (by simp)) (X i) Yrest
      obtain ⟨ci, hciC, hciMax⟩ :=
        Finset.exists_mem_eq_sup' hC
          (fun c : Bool × K =>
            D.E (fun z =>
              (Yrest z +
                (if c.1 then (1 : ℝ) else -1) * B * X i c.2 z) ^ 2))
      have hrow' :
          D.E (fun z =>
              (Yrest z + ∑ j ∈ J i, a i j * X i j z) ^ 2) ≤
            D.E (fun z =>
              (Yrest z +
                (if ci.1 then (1 : ℝ) else -1) * B * X i ci.2 z) ^ 2) := by
        rw [← hciMax]
        exact hrow
      let Yi : Ω → ℝ := fun z =>
        Y z + (if ci.1 then (1 : ℝ) else -1) * B * X i ci.2 z
      have haRows : ∀ k ∈ rows, ∑ j ∈ J k, |a k j| ≤ B := by
        intro k hk
        exact ha k (by simp [hk])
      obtain ⟨c, hcJ, hcBound⟩ := ih haRows Yi
      let c' : I → Bool × K := Function.update c i ci
      refine ⟨c', ?_, ?_⟩
      · intro k hk
        rcases Finset.mem_insert.mp hk with hki | hk
        · subst k
          simpa [c'] using (show ci.2 ∈ J i by simpa [C] using hciC)
        · have hne : k ≠ i := by
            intro h
            apply hi
            simpa [h] using hk
          simpa [c', hne] using hcJ k hk
      · calc
          D.E (fun z =>
              (Y z + ∑ k ∈ insert i rows,
                ∑ j ∈ J k, a k j * X k j z) ^ 2) =
              D.E (fun z =>
                (Yrest z + ∑ j ∈ J i, a i j * X i j z) ^ 2) := by
                congr 1
                funext z
                rw [Finset.sum_insert hi]
                simp only [Yrest]
                ring
          _ ≤ D.E (fun z =>
                (Yrest z +
                  (if ci.1 then (1 : ℝ) else -1) * B * X i ci.2 z) ^ 2) :=
                hrow'
          _ = D.E (fun z =>
                (Yi z + ∑ k ∈ rows,
                  ∑ j ∈ J k, a k j * X k j z) ^ 2) := by
                congr 1
                funext z
                simp only [Yrest, Yi]
                ring
          _ ≤ D.E (fun z =>
                (Yi z + ∑ k ∈ rows,
                  (if (c k).1 then (1 : ℝ) else -1) * B *
                    X k (c k).2 z) ^ 2) :=
                hcBound
          _ = D.E (fun z =>
                (Y z + ∑ k ∈ insert i rows,
                  (if (c' k).1 then (1 : ℝ) else -1) * B *
                    X k (c' k).2 z) ^ 2) := by
                congr 1
                funext z
                rw [Finset.sum_insert hi]
                simp only [Yi]
                have hc'i : c' i = ci := by simp [c']
                rw [hc'i]
                have hsum :
                    ∑ k ∈ rows,
                        (if ((Function.update c i ci) k).1 then (1 : ℝ) else -1) *
                          B * X k ((Function.update c i ci) k).2 z =
                      ∑ k ∈ rows,
                        (if (c k).1 then (1 : ℝ) else -1) *
                          B * X k (c k).2 z := by
                  apply Finset.sum_congr rfl
                  intro k hk
                  have hne : k ≠ i := by
                    intro h
                    apply hi
                    simpa [h] using hk
                  simp [hne]
                rw [hsum]
                ring

end CausalSmith.Experimentation.SnipeDegreeFrontier
