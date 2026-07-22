/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import CausalSmith.Experimentation.EXP_DesignPm1ExactnessBoundaryV1_Research.Helpers.ParitySliceForward

set_option linter.style.longLine false

/-! # Mixture designs and block-symmetry of second moments (backward-direction core)

Reusable primitives for the sufficiency direction:

* `uniformOnDesign` — the uniform law on a nonempty finset of assignments, with
  membership in the block-exchangeable class whenever the support is invariant
  under global negation and the two-block automorphism group;
* `mixtureDesign` — a finite convex mixture of designs, its expectation
  (`E`) linearity, its membership in the class, and the affine action on the
  block-symmetric second moment `X(u,v)`;
* `secondMoment_blockSym_of_exchangeable` — the second moment of any
  block-exchangeable design is block-symmetric (`= X(u,v)` for the reference-pair
  values `u,v`), proved by transporting pair expectations along block automorphisms.
-/

namespace CausalSmith.Experimentation.DesignPm1

open scoped BigOperators
open Causalean.Experimentation.DesignBased

/-! ## Reindexing a design by a two-block automorphism -/

/-- Reindex an assignment `z` by a permutation `σ`: `(R σ z) i = z (σ i)`. -/
def reindexBy (m : ℕ) (σ : Equiv.Perm (Fin (2 * m))) (z : Fin (2 * m) → Bool) :
    Fin (2 * m) → Bool := fun i => z (σ i)

/-- Change of variables: for a design invariant under the block-automorphism `σ`
(`D.p (reindexBy σ z) = D.p z`), expectation is invariant under precomposition by
`reindexBy σ`. -/
lemma E_reindex_invariant (m : ℕ) (D : FiniteDesign (Fin (2 * m) → Bool))
    (σ : Equiv.Perm (Fin (2 * m)))
    (hInv : ∀ z, D.p (reindexBy m σ z) = D.p z) (f : (Fin (2 * m) → Bool) → ℝ) :
    D.E (fun z => f (reindexBy m σ z)) = D.E f := by
  rw [FiniteDesign.E]
  have hbij : Function.Bijective (reindexBy m σ) := by
    refine ⟨?_, ?_⟩
    · intro z₁ z₂ h
      funext i
      have h' := congrFun h (σ.symm i)
      simpa [reindexBy] using h'
    · intro z
      refine ⟨reindexBy m σ.symm z, ?_⟩
      funext i
      simp [reindexBy]
  calc
    (∑ z, D.p z * f (reindexBy m σ z))
        = ∑ z, D.p (reindexBy m σ z) * f (reindexBy m σ z) := by
          apply Finset.sum_congr rfl
          intro z _
          rw [hInv z]
    _ = ∑ z, D.p z * f z := by
          exact hbij.sum_comp (fun z => D.p z * f z)

/-- The pointwise sign transports under reindexing: `signOf (R σ z) i = signOf z (σ i)`. -/
lemma signOf_reindex (m : ℕ) (σ : Equiv.Perm (Fin (2 * m)))
    (z : Fin (2 * m) → Bool) (i : Fin (2 * m)) :
    signOf m (reindexBy m σ z) i = signOf m z (σ i) := rfl

/-- Pair-expectation transport: if `D` is invariant under the block-automorphism `σ`
then `E[Z_{σ i} Z_{σ j}] = E[Z_i Z_j]`. -/
lemma E_pair_transport (m : ℕ) (D : FiniteDesign (Fin (2 * m) → Bool))
    (σ : Equiv.Perm (Fin (2 * m)))
    (hInv : ∀ z, D.p (reindexBy m σ z) = D.p z) (i j : Fin (2 * m)) :
    D.E (fun z => signOf m z (σ i) * signOf m z (σ j))
      = D.E (fun z => signOf m z i * signOf m z j) := by
  simpa [signOf_reindex] using
    (E_reindex_invariant m D σ hInv (fun z => signOf m z i * signOf m z j))

/-! ## Block automorphisms mapping a chosen pair to any other -/

/-- A within-block transposition (swap two indices of block `A`, fixing everything
else) is a two-block automorphism. -/
lemma isBlockAuto_swap_within (m : ℕ) {i j : Fin (2 * m)}
    (hi : i.val < m) (hj : j.val < m) : IsBlockAuto m (Equiv.swap i j) := by
  left
  intro k
  by_cases hki : k = i
  · subst k
    simp [hi, hj]
  · by_cases hkj : k = j
    · subst k
      simp [hi, hj]
    · simp [Equiv.swap_apply_of_ne_of_ne hki hkj]

private lemma isBlockAuto_swap_same (m : ℕ) {i j : Fin (2 * m)}
    (hij : (i.val < m ↔ j.val < m)) : IsBlockAuto m (Equiv.swap i j) := by
  left
  intro k
  by_cases hki : k = i
  · subst k
    simp [hij]
  · by_cases hkj : k = j
    · subst k
      simp [hij]
    · simp [Equiv.swap_apply_of_ne_of_ne hki hkj]

private lemma IsBlockAuto_comp (m : ℕ) {σ τ : Equiv.Perm (Fin (2 * m))}
    (hσ : IsBlockAuto m σ) (hτ : IsBlockAuto m τ) : IsBlockAuto m (σ * τ) := by
  rcases hσ with hσ | hσ <;> rcases hτ with hτ | hτ
  · left; intro i; exact (hσ (τ i)).trans (hτ i)
  · right; intro i; exact (hσ (τ i)).trans (hτ i)
  · right; intro i
    have h1 := hσ (τ i)
    have h2 := hτ i
    tauto
  · left; intro i
    have h1 := hσ (τ i)
    have h2 := hτ i
    tauto

private def blockFlipFun (m : ℕ) (i : Fin (2 * m)) : Fin (2 * m) :=
  if h : i.val < m then ⟨i.val + m, by omega⟩ else ⟨i.val - m, by omega⟩

private lemma blockFlipFun_val_lt (m : ℕ) (i : Fin (2 * m)) :
    (blockFlipFun m i).val < m ↔ ¬ i.val < m := by
  unfold blockFlipFun
  split_ifs with h
  · simp
    omega
  · simp
    omega

private lemma blockFlipFun_involutive (m : ℕ) (i : Fin (2 * m)) :
    blockFlipFun m (blockFlipFun m i) = i := by
  apply Fin.ext
  unfold blockFlipFun
  by_cases h : i.val < m
  · simp [h]
  · simp [h]
    have h1 : i.val - m < m := by omega
    simp [h1]
    omega

private def blockFlip (m : ℕ) : Equiv.Perm (Fin (2 * m)) where
  toFun := blockFlipFun m
  invFun := blockFlipFun m
  left_inv := blockFlipFun_involutive m
  right_inv := blockFlipFun_involutive m

private lemma blockFlip_auto (m : ℕ) : IsBlockAuto m (blockFlip m) := by
  right
  intro i
  exact blockFlipFun_val_lt m i

private lemma exists_blockAuto_pair_preserve (m : ℕ) {a b c d : Fin (2 * m)}
    (hab : a ≠ b) (hcd : c ≠ d)
    (hac : (a.val < m ↔ c.val < m)) (hbd : (b.val < m ↔ d.val < m)) :
    ∃ σ : Equiv.Perm (Fin (2 * m)), IsBlockAuto m σ ∧ σ a = c ∧ σ b = d := by
  let τ : Equiv.Perm (Fin (2 * m)) := Equiv.swap a c
  let b₁ : Fin (2 * m) := τ b
  let ρ : Equiv.Perm (Fin (2 * m)) := Equiv.swap b₁ d
  refine ⟨ρ * τ, ?_, ?_, ?_⟩
  · have hτ : IsBlockAuto m τ := isBlockAuto_swap_same m hac
    have hτpres : ∀ x, ((τ x).val < m ↔ x.val < m) := by
      rcases hτ with hτp | hτs
      · exact hτp
      · exfalso
        have h := hτs a
        simp [τ, hac] at h
        by_cases hc : c.val < m
        · have hmc : m ≤ c.val := h.mp hc
          omega
        · have hmc : m ≤ c.val := by omega
          exact hc (h.mpr hmc)
    have hb₁d : (b₁.val < m ↔ d.val < m) := (hτpres b).trans hbd
    have hρ : IsBlockAuto m ρ := isBlockAuto_swap_same m hb₁d
    exact IsBlockAuto_comp m hρ hτ
  · have hcb₁ : c ≠ b₁ := by
      intro hc
      have hb_eq_a : b = a := by
        have := congrArg τ hc.symm
        simpa [τ, b₁] using this
      exact hab hb_eq_a.symm
    change ρ (τ a) = c
    have hτa : τ a = c := by simp [τ]
    rw [hτa]
    exact Equiv.swap_apply_of_ne_of_ne hcb₁ hcd
  · simp [ρ, τ, b₁]

private lemma exists_blockAuto_pair (m : ℕ) {a b c d : Fin (2 * m)}
    (hab : a ≠ b) (hcd : c ≠ d)
    (hmem : ((a.val < m ↔ c.val < m) ∧ (b.val < m ↔ d.val < m)) ∨
      ((a.val < m ↔ ¬ c.val < m) ∧ (b.val < m ↔ ¬ d.val < m))) :
    ∃ σ : Equiv.Perm (Fin (2 * m)), IsBlockAuto m σ ∧ σ a = c ∧ σ b = d := by
  rcases hmem with hmem | hmem
  · exact exists_blockAuto_pair_preserve m hab hcd hmem.1 hmem.2
  · let φ : Equiv.Perm (Fin (2 * m)) := blockFlip m
    have hφa : ((φ a).val < m ↔ c.val < m) := by
      change (blockFlipFun m a).val < m ↔ c.val < m
      rw [blockFlipFun_val_lt]
      tauto
    have hφb : ((φ b).val < m ↔ d.val < m) := by
      change (blockFlipFun m b).val < m ↔ d.val < m
      rw [blockFlipFun_val_lt]
      tauto
    have hφab : φ a ≠ φ b := fun h => hab (φ.injective h)
    rcases exists_blockAuto_pair_preserve m hφab hcd hφa hφb with ⟨τ, hτ, hτa, hτb⟩
    refine ⟨τ * φ, IsBlockAuto_comp m hτ (blockFlip_auto m), ?_, ?_⟩
    · simpa [Equiv.Perm.mul_apply, φ] using hτa
    · simpa [Equiv.Perm.mul_apply, φ] using hτb

/-- The block-symmetry general lemma. For a block-exchangeable design `D`, its
second moment is block-symmetric: it equals `X(u,v)` with `u = E[Z_{i₀} Z_{j₀}]`
the within-block reference-pair value and `v = E[Z_{i₀} Z_{k₀}]` the cross-block
reference-pair value. -/
lemma secondMoment_blockSym_of_exchangeable (m : ℕ) (hm : 2 ≤ m)
    (D : FiniteDesign (Fin (2 * m) → Bool)) (hD : D ∈ blockExchangeableDesignClass m) :
    ∃ u v : ℝ, assignmentSecondMoment m D = blockSymMatrix m u v := by
  let i0 : Fin (2 * m) := ⟨0, by omega⟩
  let j0 : Fin (2 * m) := ⟨1, by omega⟩
  let k0 : Fin (2 * m) := ⟨m, by omega⟩
  let u : ℝ := D.E (fun z => signOf m z i0 * signOf m z j0)
  let v : ℝ := D.E (fun z => signOf m z i0 * signOf m z k0)
  refine ⟨u, v, ?_⟩
  rw [← Matrix.ext_iff]
  intro i j
  simp only [assignmentSecondMoment, Matrix.of_apply]
  by_cases hij : i = j
  · subst j
    calc
      D.E (fun z => signOf m z i * signOf m z i) = D.E (fun _ => (1 : ℝ)) := by
        apply D.E_congr
        intro z
        exact signOf_sq m z i
      _ = 1 := D.E_const 1
      _ = blockSymMatrix m u v i i := by simp [blockSymMatrix]
  · by_cases hsame : i.val < m ↔ j.val < m
    · have hi_cases : i.val < m ∨ ¬ i.val < m := em _
      rcases hi_cases with hi | hi
      · have hj : j.val < m := hsame.mp hi
        have hi0 : i0.val < m := by simp [i0]; omega
        have hj0 : j0.val < m := by simp [j0]; omega
        have hmem :
            ((i0.val < m ↔ i.val < m) ∧ (j0.val < m ↔ j.val < m)) ∨
              ((i0.val < m ↔ ¬ i.val < m) ∧ (j0.val < m ↔ ¬ j.val < m)) := by
          left
          constructor <;> simp [hi0, hj0, hi, hj]
        have hi0j0 : i0 ≠ j0 := by
          intro h
          have := congrArg Fin.val h
          simp [i0, j0] at this
        rcases exists_blockAuto_pair m hi0j0 hij hmem with ⟨σ, hσ, hσi, hσj⟩
        have hInv : ∀ z, D.p (reindexBy m σ z) = D.p z := by
          intro z
          exact hD.2 σ hσ z
        have ht := E_pair_transport m D σ hInv i0 j0
        have hval : D.E (fun z => signOf m z i * signOf m z j) = u := by
          simpa [u, hσi, hσj] using ht
        simpa [blockSymMatrix, hij, hsame] using hval
      · have hj : ¬ j.val < m := fun hj => hi (hsame.mpr hj)
        have hi0 : i0.val < m := by simp [i0]; omega
        have hj0 : j0.val < m := by simp [j0]; omega
        have hmem :
            ((i0.val < m ↔ i.val < m) ∧ (j0.val < m ↔ j.val < m)) ∨
              ((i0.val < m ↔ ¬ i.val < m) ∧ (j0.val < m ↔ ¬ j.val < m)) := by
          right
          constructor <;> simp [hi0, hj0, hi, hj]
        have hi0j0 : i0 ≠ j0 := by
          intro h
          have := congrArg Fin.val h
          simp [i0, j0] at this
        rcases exists_blockAuto_pair m hi0j0 hij hmem with ⟨σ, hσ, hσi, hσj⟩
        have hInv : ∀ z, D.p (reindexBy m σ z) = D.p z := by
          intro z
          exact hD.2 σ hσ z
        have ht := E_pair_transport m D σ hInv i0 j0
        have hval : D.E (fun z => signOf m z i * signOf m z j) = u := by
          simpa [u, hσi, hσj] using ht
        simpa [blockSymMatrix, hij, hsame] using hval
    · have hi_cases : i.val < m ∨ ¬ i.val < m := em _
      rcases hi_cases with hi | hi
      · have hj : ¬ j.val < m := fun hj => hsame ⟨fun _ => hj, fun _ => hi⟩
        have hi0 : i0.val < m := by simp [i0]; omega
        have hk0 : ¬ k0.val < m := by simp [k0]
        have hmem :
            ((i0.val < m ↔ i.val < m) ∧ (k0.val < m ↔ j.val < m)) ∨
              ((i0.val < m ↔ ¬ i.val < m) ∧ (k0.val < m ↔ ¬ j.val < m)) := by
          left
          constructor
          · simp [hi0, hi]
          · simp [hk0, hj]
        have hi0k0 : i0 ≠ k0 := by
          intro h
          have := congrArg Fin.val h
          simp [i0, k0] at this
          omega
        rcases exists_blockAuto_pair m hi0k0 hij hmem with ⟨σ, hσ, hσi, hσj⟩
        have hInv : ∀ z, D.p (reindexBy m σ z) = D.p z := by
          intro z
          exact hD.2 σ hσ z
        have ht := E_pair_transport m D σ hInv i0 k0
        have hval : D.E (fun z => signOf m z i * signOf m z j) = v := by
          simpa [v, hσi, hσj] using ht
        simpa [blockSymMatrix, hij, hsame] using hval
      · have hj : j.val < m := by
          by_contra hj
          exact hsame ⟨fun hi' => False.elim (hi hi'), fun hj' => False.elim (hj hj')⟩
        have hi0 : i0.val < m := by simp [i0]; omega
        have hk0 : ¬ k0.val < m := by simp [k0]
        have hmem :
            ((i0.val < m ↔ j.val < m) ∧ (k0.val < m ↔ i.val < m)) ∨
              ((i0.val < m ↔ ¬ j.val < m) ∧ (k0.val < m ↔ ¬ i.val < m)) := by
          left
          constructor
          · simp [hi0, hj]
          · simp [hk0, hi]
        have hi0k0 : i0 ≠ k0 := by
          intro h
          have := congrArg Fin.val h
          simp [i0, k0] at this
          omega
        have hji : j ≠ i := fun h => hij h.symm
        rcases exists_blockAuto_pair m hi0k0 hji hmem with ⟨σ, hσ, hσi, hσj⟩
        have hInv : ∀ z, D.p (reindexBy m σ z) = D.p z := by
          intro z
          exact hD.2 σ hσ z
        have ht := E_pair_transport m D σ hInv i0 k0
        have hvalji : D.E (fun z => signOf m z j * signOf m z i) = v := by
          simpa [v, hσi, hσj] using ht
        have hswap :
            D.E (fun z => signOf m z i * signOf m z j)
              = D.E (fun z => signOf m z j * signOf m z i) := by
          apply D.E_congr
          intro z
          ring
        have hval : D.E (fun z => signOf m z i * signOf m z j) = v := hswap.trans hvalji
        simpa [blockSymMatrix, hij, hsame] using hval

/-! ## Uniform design on a support -/

/-- The uniform law on a nonempty finset `S` of assignments. -/
noncomputable def uniformOnDesign (m : ℕ) (S : Finset (Fin (2 * m) → Bool))
    (hS : S.Nonempty) : FiniteDesign (Fin (2 * m) → Bool) where
  p := fun z => if z ∈ S then ((S.card : ℝ))⁻¹ else 0
  p_nonneg := fun z => by
    split
    · positivity
    · exact le_refl 0
  p_sum := by
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
    exact mul_inv_cancel₀ (by exact_mod_cast (Finset.card_ne_zero_of_mem hS.choose_spec))

/-- If the support `S` is invariant under global negation and under reindexing by
every two-block automorphism, the uniform design lies in the block-exchangeable
class. -/
lemma uniformOnDesign_mem (m : ℕ) (S : Finset (Fin (2 * m) → Bool)) (hS : S.Nonempty)
    (hNeg : ∀ z, (fun i => !z i) ∈ S ↔ z ∈ S)
    (hAuto : ∀ σ : Equiv.Perm (Fin (2 * m)), IsBlockAuto m σ →
      ∀ z, reindexBy m σ z ∈ S ↔ z ∈ S) :
    uniformOnDesign m S hS ∈ blockExchangeableDesignClass m := by
  refine ⟨⟨?_⟩, ?_⟩
  · intro z
    change (if z ∈ S then ((S.card : ℝ))⁻¹ else 0)
      = (if (fun i => !z i) ∈ S then ((S.card : ℝ))⁻¹ else 0)
    by_cases hz : z ∈ S
    · simp [hz, (hNeg z).2 hz]
    · have hnz : (fun i => !z i) ∉ S := fun h => hz ((hNeg z).1 h)
      simp [hz, hnz]
  · intro σ hσ z
    change (if reindexBy m σ z ∈ S then ((S.card : ℝ))⁻¹ else 0)
      = (if z ∈ S then ((S.card : ℝ))⁻¹ else 0)
    by_cases hz : z ∈ S
    · simp [hz, (hAuto σ hσ z).2 hz]
    · have hnz : reindexBy m σ z ∉ S := fun h => hz ((hAuto σ hσ z).1 h)
      simp [hz, hnz]

/-! ## Finite convex mixtures -/

/-- A finite convex mixture `∑ᵢ wᵢ Dᵢ` of designs. -/
noncomputable def mixtureDesign {k : ℕ} (m : ℕ) (w : Fin k → ℝ)
    (Ds : Fin k → FiniteDesign (Fin (2 * m) → Bool))
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) : FiniteDesign (Fin (2 * m) → Bool) where
  p := fun z => ∑ i, w i * (Ds i).p z
  p_nonneg := fun z => Finset.sum_nonneg (fun i _ => mul_nonneg (hw0 i) ((Ds i).p_nonneg z))
  p_sum := by
    rw [Finset.sum_comm]
    have : ∀ i : Fin k, ∑ z, w i * (Ds i).p z = w i := by
      intro i; rw [← Finset.mul_sum, (Ds i).p_sum, mul_one]
    simp_rw [this]; exact hw1

/-- Expectation of a mixture is the convex combination of expectations. -/
lemma mixtureDesign_E {k : ℕ} (m : ℕ) (w : Fin k → ℝ)
    (Ds : Fin k → FiniteDesign (Fin (2 * m) → Bool))
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (f : (Fin (2 * m) → Bool) → ℝ) :
    (mixtureDesign m w Ds hw0 hw1).E f = ∑ i, w i * (Ds i).E f := by
  simp only [FiniteDesign.E, mixtureDesign, Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1
  ext i
  rw [Finset.mul_sum]
  congr 1
  ext z
  ring

/-- A mixture of block-exchangeable designs is block-exchangeable. -/
lemma mixtureDesign_mem {k : ℕ} (m : ℕ) (w : Fin k → ℝ)
    (Ds : Fin k → FiniteDesign (Fin (2 * m) → Bool))
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (hDs : ∀ i, Ds i ∈ blockExchangeableDesignClass m) :
    mixtureDesign m w Ds hw0 hw1 ∈ blockExchangeableDesignClass m := by
  refine ⟨⟨?_⟩, ?_⟩
  · intro z
    simp only [mixtureDesign]
    apply Finset.sum_congr rfl
    intro i _
    rw [(hDs i).1.balanced z]
  · intro σ hσ z
    simp only [mixtureDesign]
    apply Finset.sum_congr rfl
    intro i _
    rw [(hDs i).2 σ hσ z]

/-- Averaging block-symmetric matrices with weights summing to `1`. -/
lemma sum_blockSymMatrix {k : ℕ} (m : ℕ) (w : Fin k → ℝ) (uu vv : Fin k → ℝ)
    (hw1 : ∑ i, w i = 1) :
    (∑ i, w i • blockSymMatrix m (uu i) (vv i))
      = blockSymMatrix m (∑ i, w i * uu i) (∑ i, w i * vv i) := by
  rw [← Matrix.ext_iff]
  intro a b
  have hsum :
      (∑ i, w i • blockSymMatrix m (uu i) (vv i)) a b
        = ∑ i, (w i • blockSymMatrix m (uu i) (vv i)) a b := by
    exact map_sum (Matrix.entryLinearMap ℝ ℝ a b)
      (fun i : Fin k => w i • blockSymMatrix m (uu i) (vv i)) Finset.univ
  rw [hsum]
  simp only [Matrix.smul_apply, smul_eq_mul]
  by_cases hab : a = b
  · simp [blockSymMatrix, hab, hw1]
  · by_cases hs : a.val < m ↔ b.val < m
    · simp [blockSymMatrix, hab, hs]
    · simp [blockSymMatrix, hab, hs]

/-- The second moment of a mixture whose components have block-symmetric second
moments `X(uᵢ,vᵢ)` is `X(∑ wᵢ uᵢ, ∑ wᵢ vᵢ)`. -/
lemma mixtureDesign_secondMoment {k : ℕ} (m : ℕ) (w : Fin k → ℝ)
    (Ds : Fin k → FiniteDesign (Fin (2 * m) → Bool))
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1) (uu vv : Fin k → ℝ)
    (hcomp : ∀ i, assignmentSecondMoment m (Ds i) = blockSymMatrix m (uu i) (vv i)) :
    assignmentSecondMoment m (mixtureDesign m w Ds hw0 hw1)
      = blockSymMatrix m (∑ i, w i * uu i) (∑ i, w i * vv i) := by
  rw [← sum_blockSymMatrix m w uu vv hw1]
  rw [← Matrix.ext_iff]
  intro i j
  have hsum :
      (∑ k, w k • blockSymMatrix m (uu k) (vv k)) i j
        = ∑ k, (w k • blockSymMatrix m (uu k) (vv k)) i j := by
    exact map_sum (Matrix.entryLinearMap ℝ ℝ i j)
      (fun k : Fin k => w k • blockSymMatrix m (uu k) (vv k)) Finset.univ
  rw [hsum]
  simp only [Matrix.smul_apply, smul_eq_mul, assignmentSecondMoment, Matrix.of_apply]
  rw [mixtureDesign_E]
  apply Finset.sum_congr rfl
  intro k _
  have hk := congrFun (congrFun (hcomp k) i) j
  simpa [assignmentSecondMoment] using congrArg (fun x => w k * x) hk

end CausalSmith.Experimentation.DesignPm1
