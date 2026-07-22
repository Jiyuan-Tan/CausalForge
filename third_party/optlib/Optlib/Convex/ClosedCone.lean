/-
Copyright (c) 2024 Shengyang Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengyang Xu
-/
import Optlib.Convex.ConicCaratheodory

/-!
# ClosedCone

## Main results

This file contains the following parts of closed cone.
* `quadrant'` : An equivalent definition of quadrant, in which V is of the form Fintype → ℝⁿ and
  can by represented by Matrix
* `cone'` : An equivalent definition of cone, in which V is of the form Fintype → ℝⁿ and
  can by represented
* proof of the closedness of a cone with linear independent basis
-/

section ClosedCone

open Finset Matrix

variable {n : ℕ} {s : Finset ℕ} {V : ℕ → (EuclideanSpace ℝ (Fin n))}
variable {x : EuclideanSpace ℝ (Fin n)}

/- An equivalent definition of cone and quadrant, in which V is of the form Fintype → ℝⁿ and
  can by represented by Matrix -/
def quadrant' (s : Finset ℕ) : Set (s → ℝ) := {x : s → ℝ | ∀ i : s, 0 ≤ x i}

/- An equivalent definition of cone, in which V is of the form Fintype → ℝⁿ and
  can by represented -/
def cone' (s : Finset ℕ) (V : s → (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n)) :=
  (fun x ↦ Finset.sum univ (fun i => x i • V i)) '' (quadrant' s)

/- The Proof of definition equivalence -/
lemma cone_trans (s : Finset ℕ) (V : ℕ → (EuclideanSpace ℝ (Fin n))) : cone' s (V ∘ coe s) = cone s V := by
  simp [cone', cone, quadrant, quadrant', coe]
  ext x; constructor
  · simp; intro t tnneg xdecompose
    let t' := fun i : ℕ ↦ if hs : i ∈ s then t ⟨i, hs⟩ else 0
    use t'; constructor
    · intro i; simp [t']
      by_cases hs : i ∈ s
      · simp [hs]; apply tnneg
      · simp [hs]
    · have eq : ∀ i : s, t i • V i = t' i.val • V i := by
        intro i; simp [t']
      have eq' : (Finset.sum (attach s) fun x ↦ t' x • V x) = (Finset.sum (attach s) fun x ↦ t x • V x) := by
        apply Finset.sum_congr; simp; simp [eq]
      rw [← xdecompose, ←eq', Finset.sum_attach s fun x ↦ t' x • V x]
  · simp; intro t tnneg xdecompose
    use t ∘ coe s; constructor
    · simp [tnneg]
    · simp [coe]; rw [← xdecompose, Finset.sum_attach s fun x ↦ t x • V x]

/- Cone V₁ is a subset of Cone V₂ if the basis of V₁ is a subset of the basis of V₂ -/
lemma cone_subset_of_idx_subset' (s τ : Finset ℕ) (hsub : τ ⊆ s) (V : ℕ → (EuclideanSpace ℝ (Fin n))) :
    cone τ V ⊆ cone s V := by
  simp only [cone]; rw [Set.subset_def]; simp [quadrant]
  intro t tnneg
  let t' := fun i : ℕ ↦ if i ∈ τ then t i else 0
  use t'; constructor
  · intro i; by_cases hi : i ∈ τ
    · simp [t', hi]; linarith [tnneg i]
    · simp [t', hi]
  · simp [t']; congr; simp [hsub]

/- Decompose a Cone into a Finset of Cones with linear independent basis -/
lemma cone_eq_finite_union (s : Finset ℕ) (V : ℕ → (EuclideanSpace ℝ (Fin n))):
    ∃ F : Finset (Set (EuclideanSpace ℝ (Fin n))),
    (cone s V = ⋃ C ∈ F, C) ∧
    (∀ C ∈ F, ∃ τ : Finset ℕ, C = cone τ V ∧ (LinearIndependent ℝ (V ∘ coe τ))) := by
  let idx_set := {τ : Finset ℕ | (τ ⊆ s) ∧ (LinearIndependent ℝ (V ∘ coe τ))}
  have finite_idx : idx_set.Finite := by
    have finite_ps : Finite s.powerset := by apply Finset.finite_toSet
    have idx_sub_ps : idx_set ⊆ s.powerset := by
      intro τ τin
      simp [idx_set] at τin
      apply Finset.mem_powerset.2 τin.1
    apply Set.Finite.subset _ idx_sub_ps
    apply finite_ps
  let idx_to_cone := fun τ : Finset ℕ ↦ cone τ V
  let F := idx_to_cone '' idx_set
  have finite_F : F.Finite := by apply Set.Finite.image; apply finite_idx
  use Set.Finite.toFinset finite_F
  constructor
  · ext x; constructor
    · intro xin
      let mem_x := conic_Caratheodory s V x xin
      rcases mem_x with ⟨τ, τsubs, xinτ, idpτ, _⟩
      simp [finite_F, F, idx_set, idx_to_cone]
      use τ
    · simp [finite_F, F, idx_set, idx_to_cone]
      intro τ τsubs _ xinτ
      apply cone_subset_of_idx_subset' s τ τsubs V xinτ
  · intro C Cin
    simp [finite_F, F] at Cin; rcases Cin with ⟨τ, τin, Ceq⟩
    use τ; constructor
    · rw [← Ceq]
    · simp [idx_set] at τin; exact τin.2

/- A Cone with linear independent basis is Closed -/
lemma closed_conic_idp (s : Finset ℕ) (V : s → (EuclideanSpace ℝ (Fin n)))
    (idp : LinearIndependent ℝ V) : IsClosed (cone' s V) := by
  simp [cone']
  let M : Matrix s (Fin n) ℝ := fun i ↦ V i
  let f := fun x : s → ℝ ↦ Finset.sum univ (fun i => x i • V i)
  let F := Matrix.mulVecLin Mᵀ
  -- `EuclideanSpace.equiv` bridges the `EuclideanSpace ℝ (Fin n)` / `Fin n → ℝ`
  -- wrapper that no longer unifies definitionally in the current mathlib; `e` is
  -- a homeomorphism, so it preserves closedness of the linear image below.
  let e := (EuclideanSpace.equiv (Fin n) ℝ).symm
  have eq2 : f = ⇑e ∘ ⇑F := by
      funext x
      ext j
      simp only [Function.comp_apply, f, F, Matrix.mulVecLin_apply]
      rw [show (e (Mᵀ.mulVec x)).ofLp = Mᵀ.mulVec x from rfl,
          show ((∑ i, x i • V i : EuclideanSpace ℝ (Fin n)).ofLp)
             = (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)) (∑ i, x i • V i) from rfl,
          map_sum]
      simp only [map_smul, WithLp.coe_linearEquiv, Matrix.mulVec, dotProduct,
        Matrix.transpose_apply, M, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  show IsClosed (f '' (quadrant' s))
  rw [eq2, Set.image_comp]
  apply e.toHomeomorph.isClosedMap
  have isclosed : IsClosedMap F := by
    have injF : Function.Injective F := by
      simp only [F]
      show Function.Injective Mᵀ.mulVec
      rw [Matrix.mulVec_injective_iff]
      -- `Mᵀ.col k = (V k).ofLp`; push `idp` through the `EuclideanSpace ≃ₗ Pi`
      -- wrapper that mathlib now inserts into `M`.
      have hcol : Mᵀ.col = ⇑(WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).toLinearMap ∘ V := by
        funext k; rfl
      rw [hcol]
      exact idp.map' _
        (LinearMap.ker_eq_bot.mpr (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).injective)
    have closeEmbF : Topology.IsClosedEmbedding F :=
      LinearMap.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr injF)
    exact closeEmbF.isClosedMap
  apply isclosed
  have domclosed : IsClosed (quadrant' s) := by
    let g := fun i : s ↦ {mu : s → ℝ | 0 ≤ mu i}
    have eqInter: (quadrant' s) = ⋂ (i : s), g i := by
      ext x; constructor
      intro h; simp [quadrant'] at h; simp [g]; exact h
      intro h; simp [quadrant']; simp [g] at h; exact h
    rw [eqInter]; apply isClosed_iInter
    intro i; simp [g]; apply isClosed_le
    apply continuous_const; apply continuous_apply
  apply domclosed

/- A finite generated Cone is Closed -/
theorem closed_conic (s : Finset ℕ) (V : ℕ → (EuclideanSpace ℝ (Fin n))) : IsClosed (cone s V) := by
  let decompose := cone_eq_finite_union s V
  rcases decompose with ⟨F, cone_eq, mem_prop⟩
  rw [cone_eq]; apply isClosed_biUnion_finset
  intro C Cin
  specialize mem_prop C Cin
  rcases mem_prop with ⟨τ, Ceq, τidp⟩; rw [Ceq]
  rw [← cone_trans]
  let V₀ := (V ∘ coe τ)
  show IsClosed (cone' τ V₀); apply closed_conic_idp
  simp [V₀]; apply τidp

end ClosedCone
