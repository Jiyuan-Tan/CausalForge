/- Exact implementability of the balanced covariance hull. -/
import CausalSmith.Experimentation.EXP_PrognosticDesignAdmissibility_Research.Helpers.CovarianceHull

namespace CausalSmith.Experimentation.PrognosticDesignAdmissibility

open Causalean.Experimentation.DesignBased
open scoped BigOperators Matrix

-- @node: assignmentComplement
private def assignmentComplement (z : Assignment n) : Assignment n := fun i => !z i

-- @node: assignmentComplement_involutive
@[simp] private lemma assignmentComplement_involutive (z : Assignment n) :
    assignmentComplement (assignmentComplement z) = z := by
  funext i
  simp [assignmentComplement]

-- @node: signOf_complement
private lemma signOf_complement (z : Assignment n) :
    signOf (assignmentComplement z) = -signOf z := by
  funext i
  change (if !z i then 1 else -1) = -(if z i then 1 else -1)
  cases z i <;> norm_num

-- @node: isBalanced_complement
private lemma isBalanced_complement {z : Assignment n} (hz : IsBalanced z) :
    IsBalanced (assignmentComplement z) := by
  unfold IsBalanced at hz ⊢
  rw [signOf_complement]
  simpa using congrArg Neg.neg hz

/-- Every balanced covariance-hull point is realized by a sign-symmetric design. -/
-- @node: covarianceHull_has_symmetric_design
private lemma covarianceHull_has_symmetric_design (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A ∈ covarianceHull n) :
    ∃ D ∈ balancedDesignSpace n,
      designCovariance D = A ∧ ∀ z, D.p z = D.p (assignmentComplement z) := by
  classical
  unfold covarianceHull at hA
  obtain ⟨I, hI, w, B, hw0, hw1, hB, hsum⟩ :=
    (mem_convexHull_iff_exists_fintype
      (R := ℝ) (E := Fin n → Fin n → ℝ)).mp hA
  letI : Fintype I := hI
  have hassign : ∀ i : I, ∃ z : Assignment n,
      IsBalanced z ∧ signOuter z = B i := by
    intro i
    rcases hB i with ⟨z, hz, hzB⟩
    exact ⟨z, hz, hzB⟩
  choose a ha_bal ha_outer using hassign
  let W : FiniteDesign (I × Bool) := {
    p := fun ib => w ib.1 / 2
    p_nonneg := fun ib => div_nonneg (hw0 ib.1) (by norm_num)
    p_sum := by
      rw [Fintype.sum_prod_type]
      simp_rw [Fintype.sum_bool]
      convert hw1 using 1
      simp }
  let orient : I × Bool → Assignment n := fun ib =>
    if ib.2 then a ib.1 else assignmentComplement (a ib.1)
  let D := W.map orient
  refine ⟨D, ?_, ?_, ?_⟩
  · constructor
    · intro z hz
      rw [FiniteDesign.map_p] at hz
      by_contra hzb
      have hzero : ∀ ib : I × Bool,
          (if orient ib = z then W.p ib else 0) = 0 := by
        intro ib
        by_cases heq : orient ib = z
        · exfalso
          apply hzb
          rw [← heq]
          rcases ib with ⟨i, b⟩
          cases b <;> simp [orient, ha_bal i, isBalanced_complement]
        · simp [heq]
      apply hz
      apply Finset.sum_eq_zero
      intro ib hib
      by_cases heq : orient ib = z
      · simp only [heq, if_true]
        simpa [heq] using hzero ib
      · simp [heq]
    · intro j
      rw [FiniteDesign.E_map]
      unfold W FiniteDesign.E
      rw [Fintype.sum_prod_type]
      apply Finset.sum_eq_zero
      intro i hi
      rw [Fintype.sum_bool]
      simp only [orient, Bool.false_eq_true, ↓reduceIte]
      rw [show signOf (assignmentComplement (a i)) j = -signOf (a i) j by
        rw [signOf_complement]; rfl]
      ring
  · ext i j
    rw [show designCovariance D i j =
        ∑ k : I, w k * (signOf (a k) i * signOf (a k) j) by
      rw [designCovariance, FiniteDesign.E_map]
      unfold W FiniteDesign.E
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Fintype.sum_bool]
      simp only [orient, Bool.false_eq_true, ↓reduceIte]
      rw [show signOf (assignmentComplement (a k)) i = -signOf (a k) i by
        rw [signOf_complement]; rfl]
      rw [show signOf (assignmentComplement (a k)) j = -signOf (a k) j by
        rw [signOf_complement]; rfl]
      ring]
    rw [← hsum]
    simp only [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro k hk
    rw [← ha_outer k]
    rfl
  · intro z
    unfold D
    simp only [FiniteDesign.map_p]
    simp_rw [Fintype.sum_prod_type, Fintype.sum_bool]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [orient, Bool.false_eq_true, ↓reduceIte, W]
    have h₁ : a k = assignmentComplement z ↔ assignmentComplement (a k) = z := by
      constructor
      · intro h
        rw [h, assignmentComplement_involutive]
      · intro h
        rw [← h, assignmentComplement_involutive]
    have h₂ : assignmentComplement (a k) = assignmentComplement z ↔ a k = z := by
      constructor
      · intro h
        simpa using congrArg assignmentComplement h
      · exact fun h => congrArg assignmentComplement h
    rw [if_congr h₁ rfl rfl, if_congr h₂ rfl rfl]
    ac_rfl

-- @node: lem:balanced-covariance-realizability
/-- The covariance image of the balanced mean-zero design class is exactly the
balanced cut hull; every hull point has a sign-symmetric attaining design. -/
lemma balanced_covariance_realizability (n : ℕ) (hn : 4 ≤ n) (hpar : Even n) :
    designCovariance '' balancedDesignSpace n = covarianceHull n ∧
      ∀ A ∈ covarianceHull n, ∃ D ∈ balancedDesignSpace n,
        designCovariance D = A ∧ ∀ z, D.p z = D.p (fun i => !z i) := by
  classical
  have realize := covarianceHull_has_symmetric_design n
  constructor
  · apply Set.Subset.antisymm
    · rintro A ⟨D, hD, rfl⟩
      unfold covarianceHull
      have hex : ∃ z : Assignment n, D.p z ≠ 0 := by
        by_contra h
        push_neg at h
        have : (∑ z, D.p z) = 0 := Finset.sum_eq_zero (fun z _ => h z)
        linarith [D.p_sum]
      obtain ⟨z0, hz0⟩ := hex
      let v : Assignment n → Matrix (Fin n) (Fin n) ℝ := fun z =>
        if D.p z = 0 then signOuter z0 else signOuter z
      refine mem_convexHull_of_exists_fintype
        (R := ℝ) (E := Matrix (Fin n) (Fin n) ℝ)
        D.p v ?_ ?_ ?_ ?_
      · exact D.p_nonneg
      · exact D.p_sum
      · intro z
        by_cases hz : D.p z = 0
        · exact ⟨z0, hD.1 z0 hz0, by simp [v, hz]⟩
        · exact ⟨z, hD.1 z hz, by simp [v, hz]⟩
      · ext i j
        simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
          designCovariance, FiniteDesign.E]
        apply Finset.sum_congr rfl
        intro z hzmem
        by_cases hz : D.p z = 0 <;> simp [v, hz, signOuter]
    · intro A hA
      obtain ⟨D, hD, hcov, _⟩ := realize A hA
      exact ⟨D, hD, hcov⟩
  · exact realize

end CausalSmith.Experimentation.PrognosticDesignAdmissibility
