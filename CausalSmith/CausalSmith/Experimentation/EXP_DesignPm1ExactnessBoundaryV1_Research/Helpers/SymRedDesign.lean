/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import CausalSmith.Experimentation.EXP_DesignPm1ExactnessBoundaryV1_Research.Helpers.SymRedMatrix

/-! # Design-side symmetry reduction (orbit averaging over the automorphism group)

The block-automorphism group `H` acts on sign assignments by pull-back
`(σ · z) i = z (σ i)`.  Averaging a balanced law `D` over `H` gives
`D'.p z = |H|⁻¹ ∑_{σ∈H} D.p (z∘σ)`, a genuine PMF that is balanced and
`H`-invariant, hence block-exchangeable, with zero one-point margins.  Its second
moment is the orbit average `X(D')ᵢⱼ = |H|⁻¹ ∑_σ X(D)_{σi,σj}`.  Because each `σ∈H`
permutes the within/cross pair-Finsets, the block sums are preserved
(`Ssame(X(D')) = Ssame(X(D))`, likewise `Scross`), so every trace term is unchanged,
while the Frobenius norm drops by convexity — giving a no-worse block-exchangeable law. -/

namespace CausalSmith.Experimentation.DesignPm1

open scoped BigOperators
open Causalean.Experimentation.DesignBased
open Classical

/-- The pull-back action of a permutation on sign assignments. -/
def pbAct (m : ℕ) (σ : Equiv.Perm (Fin (2 * m))) (z : Fin (2 * m) → Bool) :
    Fin (2 * m) → Bool := fun i => z (σ i)

/-- The block-automorphism group as a `Finset` of permutations. -/
noncomputable def blockAutoFinset (m : ℕ) : Finset (Equiv.Perm (Fin (2 * m))) :=
  Finset.univ.filter (fun σ => IsBlockAuto m σ)

/-- The identity is a block automorphism. -/
lemma one_mem_blockAutoFinset (m : ℕ) : (1 : Equiv.Perm (Fin (2 * m))) ∈ blockAutoFinset m := by
  simp [blockAutoFinset, IsBlockAuto]

/-- `blockAutoFinset` is nonempty (so `|H| > 0`). -/
lemma blockAutoFinset_card_pos (m : ℕ) : 0 < (blockAutoFinset m).card := by
  exact Finset.card_pos.mpr ⟨1, one_mem_blockAutoFinset m⟩

/-- The block-automorphism set is closed under composition. -/
lemma mul_mem_blockAutoFinset (m : ℕ) {σ τ : Equiv.Perm (Fin (2 * m))}
    (hσ : σ ∈ blockAutoFinset m) (hτ : τ ∈ blockAutoFinset m) :
    σ * τ ∈ blockAutoFinset m := by
  rw [blockAutoFinset] at hσ hτ ⊢
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ hτ ⊢
  rcases hσ with hσ | hσ <;> rcases hτ with hτ | hτ
  · left
    intro i
    exact (hσ (τ i)).trans (hτ i)
  · right
    intro i
    exact (hσ (τ i)).trans (hτ i)
  · right
    intro i
    have h1 := hσ (τ i)
    have h2 := hτ i
    tauto
  · left
    intro i
    have h1 := hσ (τ i)
    have h2 := hτ i
    tauto

/-- The block-automorphism set is closed under inverse. -/
lemma inv_mem_blockAutoFinset (m : ℕ) {σ : Equiv.Perm (Fin (2 * m))}
    (hσ : σ ∈ blockAutoFinset m) : σ⁻¹ ∈ blockAutoFinset m := by
  rw [blockAutoFinset] at hσ ⊢
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
  rcases hσ with hσ | hσ
  · left
    intro i
    have h := hσ (σ⁻¹ i)
    simpa using h.symm
  · right
    intro i
    have h := hσ (σ⁻¹ i)
    have h' : i.val < m ↔ ¬ (σ⁻¹ i).val < m := by simpa using h
    tauto

/-- A block automorphism maps within-community pairs to within-community pairs
(and preserves distinctness); i.e. it permutes `sameOffPairs`. -/
lemma blockAuto_maps_sameOffPairs (m : ℕ) {σ : Equiv.Perm (Fin (2 * m))}
    (hσ : σ ∈ blockAutoFinset m) {i j : Fin (2 * m)}
    (h : (i, j) ∈ sameOffPairs m) : (σ i, σ j) ∈ sameOffPairs m := by
  rw [sameOffPairs] at h ⊢
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢
  rcases h with ⟨hij, hsame⟩
  constructor
  · exact fun hEq => hij (σ.injective hEq)
  · rw [blockAutoFinset] at hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    rcases hσ with hpres | hswap
    · simpa [hpres i, hpres j] using hsame
    · by_cases hi : i.val < m <;> by_cases hj : j.val < m <;>
        simp [hi, hj] at hsame ⊢ <;>
        simp [hswap i, hswap j, hi, hj]

/-- A block automorphism permutes `crossPairs`. -/
lemma blockAuto_maps_crossPairs (m : ℕ) {σ : Equiv.Perm (Fin (2 * m))}
    (hσ : σ ∈ blockAutoFinset m) {i j : Fin (2 * m)}
    (h : (i, j) ∈ crossPairs m) : (σ i, σ j) ∈ crossPairs m := by
  rw [crossPairs] at h ⊢
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢
  rw [blockAutoFinset] at hσ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
  rcases hσ with hpres | hswap
  · intro hsame
    apply h
    simpa [hpres i, hpres j] using hsame
  · intro hsame
    apply h
    have hnot : decide (¬ i.val < m) = decide (¬ j.val < m) := by
      simpa [hswap i, hswap j] using hsame
    by_cases hi : i.val < m <;> by_cases hj : j.val < m <;>
      simp [hi, hj] at hnot ⊢

/-- The orbit-averaged design `D'.p z = |H|⁻¹ ∑_{σ∈H} D.p (z∘σ)`. -/
noncomputable def orbitAvgDesign (m : ℕ) (D : FiniteDesign (Fin (2 * m) → Bool)) :
    FiniteDesign (Fin (2 * m) → Bool) where
  p := fun z => (∑ σ ∈ blockAutoFinset m, D.p (pbAct m σ z)) / (blockAutoFinset m).card
  p_nonneg := by
    intro z
    exact div_nonneg (Finset.sum_nonneg (fun σ _ => D.p_nonneg (pbAct m σ z)))
      (by exact_mod_cast Nat.zero_le (blockAutoFinset m).card)
  p_sum := by
    classical
    have hcard_ne : ((blockAutoFinset m).card : ℝ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (blockAutoFinset_card_pos m))
    have hinner : ∀ σ : Equiv.Perm (Fin (2 * m)), ∑ z, D.p (pbAct m σ z) = 1 := by
      intro σ
      let e : (Fin (2 * m) → Bool) ≃ (Fin (2 * m) → Bool) :=
        { toFun := fun z => pbAct m σ z
          invFun := fun z => pbAct m σ⁻¹ z
          left_inv := by
            intro z
            funext i
            simp [pbAct]
          right_inv := by
            intro z
            funext i
            simp [pbAct] }
      calc
        (∑ z, D.p (pbAct m σ z)) = ∑ z, D.p z := by
          simpa [e, pbAct] using (Equiv.sum_comp e D.p)
        _ = 1 := D.p_sum
    simp only [div_eq_mul_inv]
    rw [← Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_mul]
    calc
      (∑ x ∈ blockAutoFinset m, ∑ i, D.p (pbAct m x i) *
          (((blockAutoFinset m).card : ℝ)⁻¹))
          = ∑ x ∈ blockAutoFinset m, (1 : ℝ) *
              (((blockAutoFinset m).card : ℝ)⁻¹) := by
            apply Finset.sum_congr rfl
            intro σ hσ
            rw [← Finset.sum_mul, hinner σ]
      _ = 1 := by
            rw [Finset.sum_const, nsmul_eq_mul]
            field_simp [hcard_ne]

/-- The orbit average of a balanced design is balanced. -/
lemma orbitAvgDesign_balanced (m : ℕ) (D : FiniteDesign (Fin (2 * m) → Bool))
    (hD : BalancedSignDesign m D) : BalancedSignDesign m (orbitAvgDesign m D) := by
  intro z
  simp [orbitAvgDesign, pbAct]
  apply congrArg (fun x : ℝ => x / ((blockAutoFinset m).card : ℝ))
  apply Finset.sum_congr rfl
  intro σ _
  exact hD (pbAct m σ z)

/-- The orbit average is invariant under the block-automorphism group. -/
lemma orbitAvgDesign_blockAuto_invariant (m : ℕ) (D : FiniteDesign (Fin (2 * m) → Bool))
    (σ : Equiv.Perm (Fin (2 * m))) (hσ : IsBlockAuto m σ) (z : Fin (2 * m) → Bool) :
    (orbitAvgDesign m D).p (fun i => z (σ i)) = (orbitAvgDesign m D).p z := by
  classical
  have hσmem : σ ∈ blockAutoFinset m := by
    rw [blockAutoFinset]
    simp [hσ]
  simp [orbitAvgDesign, pbAct]
  apply congrArg (fun x : ℝ => x / ((blockAutoFinset m).card : ℝ))
  refine Finset.sum_bij' (fun τ _ => σ * τ) (fun ρ _ => σ⁻¹ * ρ) ?_ ?_ ?_ ?_ ?_
  · intro τ hτ
    exact mul_mem_blockAutoFinset m hσmem hτ
  · intro ρ hρ
    exact mul_mem_blockAutoFinset m (inv_mem_blockAutoFinset m hσmem) hρ
  · intro τ hτ
    ext i
    simp [Equiv.Perm.mul_apply]
  · intro ρ hρ
    ext i
    simp [Equiv.Perm.mul_apply]
  · intro τ hτ
    congr 1

/-- A balanced design has zero one-point margins. -/
lemma balanced_zero_margin (m : ℕ) (D : FiniteDesign (Fin (2 * m) → Bool))
    (hD : BalancedSignDesign m D) (i : Fin (2 * m)) :
    D.E (fun z => signOf m z i) = 0 := by
  classical
  let e : (Fin (2 * m) → Bool) ≃ (Fin (2 * m) → Bool) :=
    { toFun := fun z k => ! z k
      invFun := fun z k => ! z k
      left_inv := by intro z; funext k; simp
      right_inv := by intro z; funext k; simp }
  have hflip :
      D.E (fun z => signOf m z i)
        = ∑ z : Fin (2 * m) → Bool, D.p (fun k => ! z k) *
            signOf m (fun k => ! z k) i := by
    simpa [FiniteDesign.E, e] using
      (Equiv.sum_comp e (fun z => D.p z * signOf m z i)).symm
  have hneg :
      (∑ z : Fin (2 * m) → Bool, D.p (fun k => ! z k) *
          signOf m (fun k => ! z k) i)
        = - D.E (fun z => signOf m z i) := by
    rw [FiniteDesign.E, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro z _
    have hs : signOf m (fun k => ! z k) i = - signOf m z i := by
      unfold signOf
      by_cases h : z i <;> simp [h]
    rw [← hD z, hs]
    ring
  have hself : D.E (fun z => signOf m z i) = -D.E (fun z => signOf m z i) :=
    hflip.trans hneg
  linarith

/-- The orbit average lands in the block-exchangeable class. -/
lemma orbitAvgDesign_mem_class (m : ℕ) (D : FiniteDesign (Fin (2 * m) → Bool))
    (hD : BalancedDesignClass m D) :
    orbitAvgDesign m D ∈ blockExchangeableDesignClass m := by
  exact ⟨⟨orbitAvgDesign_balanced m D hD.balanced⟩,
    fun σ hσ z => orbitAvgDesign_blockAuto_invariant m D σ hσ z⟩

/-- Second moments are symmetric. -/
lemma assignmentSecondMoment_symm (m : ℕ) (D : FiniteDesign (Fin (2 * m) → Bool))
    (i j : Fin (2 * m)) :
    assignmentSecondMoment m D i j = assignmentSecondMoment m D j i := by
  simp [assignmentSecondMoment, mul_comm]

/-- Second moments have unit diagonal. -/
lemma assignmentSecondMoment_diag (m : ℕ) (D : FiniteDesign (Fin (2 * m) → Bool))
    (i : Fin (2 * m)) : assignmentSecondMoment m D i i = 1 := by
  have hs : ∀ z : Fin (2 * m) → Bool, signOf m z i * signOf m z i = 1 := by
    intro z
    unfold signOf
    by_cases h : z i <;> simp [h]
  simp [assignmentSecondMoment, hs]

/-- Second moments are positive semidefinite (Gram matrix `E[Z Zᵀ]`). -/
lemma assignmentSecondMoment_posSemidef (m : ℕ) (D : FiniteDesign (Fin (2 * m) → Bool)) :
    (assignmentSecondMoment m D).PosSemidef := by
  classical
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · exact Matrix.IsHermitian.ext fun i j => by
      simp [assignmentSecondMoment, mul_comm]
  · intro x
    have hquad :
        dotProduct x ((assignmentSecondMoment m D).mulVec x)
          = ∑ z, D.p z * (∑ i, signOf m z i * x i) ^ 2 := by
      simp [dotProduct, Matrix.mulVec, assignmentSecondMoment, FiniteDesign.E,
        Finset.mul_sum, Finset.sum_mul, sq, mul_assoc, mul_left_comm, mul_comm]
      calc
        (∑ x_1, ∑ x_2, ∑ i, x x_1 *
            (x x_2 * (signOf m i x_1 * (signOf m i x_2 * D.p i))))
            = ∑ x_1, ∑ i, ∑ x_2, x x_1 *
                (x x_2 * (signOf m i x_1 * (signOf m i x_2 * D.p i))) := by
              apply Finset.sum_congr rfl
              intro a _
              rw [Finset.sum_comm]
        _ = ∑ i, ∑ x_1, ∑ x_2, x x_1 *
              (x x_2 * (signOf m i x_1 * (signOf m i x_2 * D.p i))) := by
              rw [Finset.sum_comm]
        _ = ∑ x_1, ∑ x_2, ∑ x_3, x x_2 *
              (x x_3 * (signOf m x_1 x_2 * (signOf m x_1 x_3 * D.p x_1))) := by
              rfl
    simpa [hquad] using
      Finset.sum_nonneg (fun z _ => mul_nonneg (D.p_nonneg z) (sq_nonneg _))

/-- The uniform iid Rademacher design is block-exchangeable (a nonempty witness). -/
lemma iidDesign_mem_blockExchangeable (m : ℕ) :
    iidDesign m ∈ blockExchangeableDesignClass m := by
  refine ⟨⟨fun z => rfl⟩, fun σ _ z => rfl⟩

/-- The second moment of the orbit average is the orbit average of the second moment:
`X(D')ᵢⱼ = |H|⁻¹ ∑_{σ∈H} X(D)_{σi,σj}`. -/
lemma orbitAvg_secondMoment_entry (m : ℕ) (D : FiniteDesign (Fin (2 * m) → Bool))
    (i j : Fin (2 * m)) :
    assignmentSecondMoment m (orbitAvgDesign m D) i j
      = (∑ σ ∈ blockAutoFinset m, assignmentSecondMoment m D (σ i) (σ j))
          / (blockAutoFinset m).card := by
  classical
  have hinner : ∀ σ : Equiv.Perm (Fin (2 * m)),
      (∑ z : Fin (2 * m) → Bool,
        D.p (pbAct m σ z) * (signOf m z i * signOf m z j))
        = assignmentSecondMoment m D (σ⁻¹ i) (σ⁻¹ j) := by
    intro σ
    let e : (Fin (2 * m) → Bool) ≃ (Fin (2 * m) → Bool) :=
      { toFun := fun z => pbAct m σ z
        invFun := fun z => pbAct m σ⁻¹ z
        left_inv := by intro z; funext k; simp [pbAct]
        right_inv := by intro z; funext k; simp [pbAct] }
    simpa [assignmentSecondMoment, FiniteDesign.E, e, pbAct, signOf] using
      (Equiv.sum_comp e (fun w => D.p w *
        (signOf m (pbAct m σ⁻¹ w) i * signOf m (pbAct m σ⁻¹ w) j)))
  have hinvsum :
      (∑ σ ∈ blockAutoFinset m, assignmentSecondMoment m D (σ⁻¹ i) (σ⁻¹ j))
        = ∑ σ ∈ blockAutoFinset m, assignmentSecondMoment m D (σ i) (σ j) := by
    refine Finset.sum_bij' (fun σ _ => σ⁻¹) (fun σ _ => σ⁻¹) ?_ ?_ ?_ ?_ ?_
    · intro σ hσ
      exact inv_mem_blockAutoFinset m hσ
    · intro σ hσ
      exact inv_mem_blockAutoFinset m hσ
    · intro σ hσ
      simp
    · intro σ hσ
      simp
    · intro σ hσ
      simp
  calc
    assignmentSecondMoment m (orbitAvgDesign m D) i j
        = (∑ σ ∈ blockAutoFinset m,
            assignmentSecondMoment m D (σ⁻¹ i) (σ⁻¹ j)) / (blockAutoFinset m).card := by
          simp only [assignmentSecondMoment, Matrix.of_apply, FiniteDesign.E, orbitAvgDesign]
          simp_rw [div_eq_mul_inv]
          simp_rw [Finset.sum_mul]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro σ hσ
          calc
            (∑ x, D.p (pbAct m σ x) * (((blockAutoFinset m).card : ℝ)⁻¹) *
                (signOf m x i * signOf m x j))
                = ∑ x, D.p (pbAct m σ x) * (signOf m x i * signOf m x j) *
                    (((blockAutoFinset m).card : ℝ)⁻¹) := by
                  apply Finset.sum_congr rfl
                  intro z _
                  ring
            _ = (∑ x, D.p (pbAct m σ x) * (signOf m x i * signOf m x j)) *
                    (((blockAutoFinset m).card : ℝ)⁻¹) := by
                  rw [← Finset.sum_mul]
            _ = (∑ x, D.p x * (signOf m x (σ⁻¹ i) * signOf m x (σ⁻¹ j))) *
                    (((blockAutoFinset m).card : ℝ)⁻¹) := by
                  simpa [assignmentSecondMoment, FiniteDesign.E] using
                    congrArg (fun t : ℝ => t * (((blockAutoFinset m).card : ℝ)⁻¹))
                      (hinner σ)
            _ = ∑ x, D.p x * (signOf m x (σ⁻¹ i) * signOf m x (σ⁻¹ j)) *
                    (((blockAutoFinset m).card : ℝ)⁻¹) := by
                  rw [Finset.sum_mul]
    _ = (∑ σ ∈ blockAutoFinset m, assignmentSecondMoment m D (σ i) (σ j)) /
        (blockAutoFinset m).card := by rw [hinvsum]

/-- Orbit averaging preserves the within-community entry sum. -/
lemma Ssame_orbitAvg (m : ℕ) (D : FiniteDesign (Fin (2 * m) → Bool)) :
    Ssame m (assignmentSecondMoment m (orbitAvgDesign m D))
      = Ssame m (assignmentSecondMoment m D) := by
  classical
  have hcard_ne : ((blockAutoFinset m).card : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (blockAutoFinset_card_pos m))
  have hpair : ∀ σ ∈ blockAutoFinset m,
      (∑ p ∈ sameOffPairs m, assignmentSecondMoment m D (σ p.1) (σ p.2))
        = Ssame m (assignmentSecondMoment m D) := by
    intro σ hσ
    unfold Ssame
    refine Finset.sum_bij' (fun p _ => (σ p.1, σ p.2))
        (fun q _ => (σ⁻¹ q.1, σ⁻¹ q.2)) ?_ ?_ ?_ ?_ ?_
    · intro p hp; exact blockAuto_maps_sameOffPairs m hσ hp
    · intro q hq; exact blockAuto_maps_sameOffPairs m (inv_mem_blockAutoFinset m hσ) hq
    · intro p hp; ext <;> simp
    · intro q hq; ext <;> simp
    · intro p hp; rfl
  unfold Ssame
  simp_rw [orbitAvg_secondMoment_entry m D]
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_mul]
  calc
    (∑ x ∈ blockAutoFinset m,
        ∑ i ∈ sameOffPairs m, assignmentSecondMoment m D (x i.1) (x i.2) *
          (((blockAutoFinset m).card : ℝ)⁻¹))
        = ∑ x ∈ blockAutoFinset m,
            Ssame m (assignmentSecondMoment m D) * (((blockAutoFinset m).card : ℝ)⁻¹) := by
          apply Finset.sum_congr rfl
          intro σ hσ
          rw [← Finset.sum_mul, hpair σ hσ]
    _ = ∑ p ∈ sameOffPairs m, assignmentSecondMoment m D p.1 p.2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
          field_simp [hcard_ne]
          rfl

/-- Orbit averaging preserves the cross-community entry sum. -/
lemma Scross_orbitAvg (m : ℕ) (D : FiniteDesign (Fin (2 * m) → Bool)) :
    Scross m (assignmentSecondMoment m (orbitAvgDesign m D))
      = Scross m (assignmentSecondMoment m D) := by
  classical
  have hcard_ne : ((blockAutoFinset m).card : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (blockAutoFinset_card_pos m))
  have hpair : ∀ σ ∈ blockAutoFinset m,
      (∑ p ∈ crossPairs m, assignmentSecondMoment m D (σ p.1) (σ p.2))
        = Scross m (assignmentSecondMoment m D) := by
    intro σ hσ
    unfold Scross
    refine Finset.sum_bij' (fun p _ => (σ p.1, σ p.2))
        (fun q _ => (σ⁻¹ q.1, σ⁻¹ q.2)) ?_ ?_ ?_ ?_ ?_
    · intro p hp; exact blockAuto_maps_crossPairs m hσ hp
    · intro q hq; exact blockAuto_maps_crossPairs m (inv_mem_blockAutoFinset m hσ) hq
    · intro p hp; ext <;> simp
    · intro q hq; ext <;> simp
    · intro p hp; rfl
  unfold Scross
  simp_rw [orbitAvg_secondMoment_entry m D]
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_mul]
  calc
    (∑ x ∈ blockAutoFinset m,
        ∑ i ∈ crossPairs m, assignmentSecondMoment m D (x i.1) (x i.2) *
          (((blockAutoFinset m).card : ℝ)⁻¹))
        = ∑ x ∈ blockAutoFinset m,
            Scross m (assignmentSecondMoment m D) * (((blockAutoFinset m).card : ℝ)⁻¹) := by
          apply Finset.sum_congr rfl
          intro σ hσ
          rw [← Finset.sum_mul, hpair σ hσ]
    _ = ∑ p ∈ crossPairs m, assignmentSecondMoment m D p.1 p.2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
          field_simp [hcard_ne]
          rfl

/-- Orbit averaging weakly decreases the Frobenius norm of the second moment. -/
lemma frobeniusNorm_orbitAvg_le (m : ℕ) (D : FiniteDesign (Fin (2 * m) → Bool)) :
    frobeniusNorm (assignmentSecondMoment m (orbitAvgDesign m D))
      ≤ frobeniusNorm (assignmentSecondMoment m D) := by
  classical
  let X := assignmentSecondMoment m D
  let Y := assignmentSecondMoment m (orbitAvgDesign m D)
  have hcard_pos : (0 : ℝ) < ((blockAutoFinset m).card : ℝ) := by
    exact_mod_cast blockAutoFinset_card_pos m
  have hcard_ne : ((blockAutoFinset m).card : ℝ) ≠ 0 := ne_of_gt hcard_pos
  have hentry : ∀ i j : Fin (2 * m),
      (Y i j) ^ 2 ≤ (∑ σ ∈ blockAutoFinset m, (X (σ i) (σ j)) ^ 2) /
        ((blockAutoFinset m).card : ℝ) := by
    intro i j
    have hcs := sq_sum_le_card_mul_sum_sq (s := blockAutoFinset m)
        (f := fun σ : Equiv.Perm (Fin (2 * m)) => X (σ i) (σ j))
    have hY : Y i j = (∑ σ ∈ blockAutoFinset m, X (σ i) (σ j)) /
        ((blockAutoFinset m).card : ℝ) := by
      dsimp [Y, X]
      exact orbitAvg_secondMoment_entry m D i j
    rw [hY]
    rw [show ((∑ σ ∈ blockAutoFinset m, X (σ i) (σ j)) /
        ((blockAutoFinset m).card : ℝ)) ^ 2 =
        ((∑ σ ∈ blockAutoFinset m, X (σ i) (σ j)) ^ 2) /
        ((blockAutoFinset m).card : ℝ) ^ 2 by ring]
    field_simp [hcard_ne]
    nlinarith [hcs]
  have hperm_sum : ∀ σ : Equiv.Perm (Fin (2 * m)),
      (∑ i : Fin (2 * m), ∑ j : Fin (2 * m), (X (σ i) (σ j)) ^ 2)
        = ∑ i : Fin (2 * m), ∑ j : Fin (2 * m), (X i j) ^ 2 := by
    intro σ
    have hrow : ∀ i : Fin (2 * m),
        (∑ j : Fin (2 * m), (X (σ i) (σ j)) ^ 2)
          = ∑ j : Fin (2 * m), (X (σ i) j) ^ 2 := by
      intro i
      exact Fintype.sum_bijective (fun j : Fin (2 * m) => σ j) σ.bijective
        (fun j => (X (σ i) (σ j)) ^ 2) (fun j => (X (σ i) j) ^ 2) (fun j => rfl)
    calc
      (∑ i : Fin (2 * m), ∑ j : Fin (2 * m), (X (σ i) (σ j)) ^ 2)
          = ∑ i : Fin (2 * m), ∑ j : Fin (2 * m), (X (σ i) j) ^ 2 := by
            apply Finset.sum_congr rfl
            intro i _
            exact hrow i
      _ = ∑ i : Fin (2 * m), ∑ j : Fin (2 * m), (X i j) ^ 2 := by
            exact Fintype.sum_bijective (fun i : Fin (2 * m) => σ i) σ.bijective
              (fun i => ∑ j : Fin (2 * m), (X (σ i) j) ^ 2)
              (fun i => ∑ j : Fin (2 * m), (X i j) ^ 2) (fun i => rfl)
  have hsum_le :
      (∑ i : Fin (2 * m), ∑ j : Fin (2 * m), (Y i j) ^ 2)
        ≤ ∑ i : Fin (2 * m), ∑ j : Fin (2 * m),
            (∑ σ ∈ blockAutoFinset m, (X (σ i) (σ j)) ^ 2) /
              ((blockAutoFinset m).card : ℝ) := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    exact hentry i j
  have havg_eq :
      (∑ i : Fin (2 * m), ∑ j : Fin (2 * m),
            (∑ σ ∈ blockAutoFinset m, (X (σ i) (σ j)) ^ 2) /
              ((blockAutoFinset m).card : ℝ))
        = ∑ i : Fin (2 * m), ∑ j : Fin (2 * m), (X i j) ^ 2 := by
    simp only [div_eq_mul_inv, Finset.sum_mul]
    calc
      (∑ i : Fin (2 * m), ∑ j : Fin (2 * m),
          ∑ σ ∈ blockAutoFinset m,
            X (σ i) (σ j) ^ 2 * (((blockAutoFinset m).card : ℝ)⁻¹))
          = ∑ i : Fin (2 * m), ∑ σ ∈ blockAutoFinset m,
              ∑ j : Fin (2 * m), X (σ i) (σ j) ^ 2 *
                (((blockAutoFinset m).card : ℝ)⁻¹) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_comm]
      _ = ∑ σ ∈ blockAutoFinset m, ∑ i : Fin (2 * m),
            ∑ j : Fin (2 * m), X (σ i) (σ j) ^ 2 *
              (((blockAutoFinset m).card : ℝ)⁻¹) := by
            rw [Finset.sum_comm]
      _ = ∑ σ ∈ blockAutoFinset m,
            (∑ i : Fin (2 * m), ∑ j : Fin (2 * m), X i j ^ 2) *
              (((blockAutoFinset m).card : ℝ)⁻¹) := by
            apply Finset.sum_congr rfl
            intro σ hσ
            calc
              (∑ i : Fin (2 * m), ∑ j : Fin (2 * m), X (σ i) (σ j) ^ 2 *
                  (((blockAutoFinset m).card : ℝ)⁻¹))
                  = ∑ i : Fin (2 * m),
                      (∑ j : Fin (2 * m), X (σ i) (σ j) ^ 2) *
                        (((blockAutoFinset m).card : ℝ)⁻¹) := by
                    apply Finset.sum_congr rfl
                    intro i _
                    rw [← Finset.sum_mul]
              _ = (∑ i : Fin (2 * m), ∑ j : Fin (2 * m), X (σ i) (σ j) ^ 2) *
                      (((blockAutoFinset m).card : ℝ)⁻¹) := by
                    rw [← Finset.sum_mul]
              _ = (∑ i : Fin (2 * m), ∑ j : Fin (2 * m), X i j ^ 2) *
                      (((blockAutoFinset m).card : ℝ)⁻¹) := by
                    rw [hperm_sum σ]
      _ = ∑ i : Fin (2 * m), ∑ j : Fin (2 * m), X i j ^ 2 := by
            rw [Finset.sum_const, nsmul_eq_mul]
            field_simp [hcard_ne]
  unfold frobeniusNorm
  apply Real.sqrt_le_sqrt
  exact le_trans hsum_le (le_of_eq havg_eq)

/-- **Design-side symmetry reduction (master export).** For every balanced design `D`,
its orbit average `orbitAvgDesign m D` over the full two-block automorphism group is the
witness: it is block-exchangeable, has the same zero one-point margins, and has a weakly
smaller objective. -/
lemma design_symmetrize (m : ℕ) (a b r kappa : ℝ)
    (hHom : TwoBlockHomophily m a b) (hk : 0 ≤ kappa)
    (D : FiniteDesign (Fin (2 * m) → Bool)) (hD : BalancedDesignClass m D) :
    orbitAvgDesign m D ∈ blockExchangeableDesignClass m ∧
      (∀ i, (orbitAvgDesign m D).E (fun z => signOf m z i) = 0) ∧
      designObjective m a b r kappa (assignmentSecondMoment m (orbitAvgDesign m D))
        ≤ designObjective m a b r kappa (assignmentSecondMoment m D) := by
  refine ⟨orbitAvgDesign_mem_class m D hD, ?_, ?_⟩
  · intro i
    exact balanced_zero_margin m (orbitAvgDesign m D) (orbitAvgDesign_balanced m D hD.balanced) i
  · exact designObjective_le_of_blockSums m a b r kappa hHom hk
      (assignmentSecondMoment m D)
      (assignmentSecondMoment m (orbitAvgDesign m D))
      (assignmentSecondMoment_symm m D)
      (assignmentSecondMoment_symm m (orbitAvgDesign m D))
      (assignmentSecondMoment_diag m D)
      (assignmentSecondMoment_diag m (orbitAvgDesign m D))
      (Ssame_orbitAvg m D)
      (Scross_orbitAvg m D)
      (frobeniusNorm_orbitAvg_le m D)

end CausalSmith.Experimentation.DesignPm1
