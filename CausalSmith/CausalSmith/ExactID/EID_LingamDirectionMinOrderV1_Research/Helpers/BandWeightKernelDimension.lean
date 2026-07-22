/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Dimension of the retained-band weight kernel
-/

import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.BandParameterCoordinates
import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.WeightSynthesisDimension

namespace CausalSmith.ExactID.EID_LingamDirectionMinOrderV1

open scoped BigOperators

noncomputable section

/-- The tangent space obtained by fixing every loading slope and allowing each
retained order's source weights to move in its synthesis kernel. -/
def bandWeightKernel (m L : ℕ) (s : Fin (m + 1) → ℂ) :
    Submodule ℂ (BandParamCoord m L → ℂ) where
  carrier := {x |
    x (Sum.inl ()) = 0 ∧
    (∀ i, x (Sum.inr (Sum.inl i)) = 0) ∧
    ∀ k : Fin (L - 1), endpointOrderSynthesis s (k.val + 2)
      (fun j => x (Sum.inr (Sum.inr (j, k)))) = 0}
  zero_mem' := by
    refine ⟨rfl, fun _ => rfl, ?_⟩
    intro k
    change endpointOrderSynthesis s (k.val + 2) 0 = 0
    exact (endpointOrderSynthesis s (k.val + 2)).map_zero
  add_mem' {x y} hx hy := by
    refine ⟨by simp [hx.1, hy.1], fun i => by simp [hx.2.1 i, hy.2.1 i], ?_⟩
    intro k
    change endpointOrderSynthesis s (k.val + 2)
      ((fun j => x (Sum.inr (Sum.inr (j, k)))) +
        fun j => y (Sum.inr (Sum.inr (j, k)))) = 0
    rw [map_add, hx.2.2 k, hy.2.2 k, add_zero]
  smul_mem' c x hx := by
    refine ⟨by simp [hx.1], fun i => by simp [hx.2.1 i], ?_⟩
    intro k
    change endpointOrderSynthesis s (k.val + 2)
      (c • fun j => x (Sum.inr (Sum.inr (j, k)))) = 0
    rw [map_smul, hx.2.2 k, smul_zero]

/-- The retained-band kernel is the product of its independent order blocks. -/
def bandWeightKernelEquiv (m L : ℕ) (s : Fin (m + 1) → ℂ) :
    bandWeightKernel m L s ≃ₗ[ℂ]
      (∀ k : Fin (L - 1), LinearMap.ker (endpointOrderSynthesis s (k.val + 2))) where
  toFun x k := ⟨fun j => x.1 (Sum.inr (Sum.inr (j, k))), x.2.2.2 k⟩
  invFun z := ⟨fun c =>
    match c with
    | Sum.inl _ => 0
    | Sum.inr (Sum.inl _) => 0
    | Sum.inr (Sum.inr jk) => (z jk.2).1 jk.1,
    by
      refine ⟨rfl, fun _ => rfl, ?_⟩
      intro k
      exact (z k).property⟩
  map_add' x y := by
    funext k
    apply Subtype.ext
    funext j
    rfl
  map_smul' c x := by
    funext k
    apply Subtype.ext
    funext j
    rfl
  left_inv x := by
    apply Subtype.ext
    funext c
    rcases c with _ | (i | ⟨j, k⟩)
    · exact x.2.1.symm
    · exact (x.2.2.1 i).symm
    · rfl
  right_inv z := by
    funext k
    apply Subtype.ext
    funext j
    rfl

/-- Establishes the stated dimension formula for band Weight Kernel. -/
lemma bandWeightKernel_finrank (m L : ℕ) (s : Fin (m + 1) → ℂ)
    (hs : Function.Injective s) :
    Module.finrank ℂ (bandWeightKernel m L s) =
      Finset.univ.sum (fun k : Fin (L - 1) => (m + 1) - (k.val + 2)) := by
  rw [(bandWeightKernelEquiv m L s).finrank_eq,
    Module.finrank_pi_fintype]
  apply Finset.sum_congr rfl
  intro k _
  exact endpointOrderSynthesis_ker_finrank s hs

/-- Proves the stated mathematical property of retained kernel sum. -/
lemma retained_kernel_sum (m : ℕ) (hm : 2 ≤ m) :
    Finset.univ.sum (fun k : Fin ((2 * m + 2) - 1) =>
      (m + 1) - (k.val + 2)) =
      m * (m - 1) / 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun k => (m + 1) - (k + 2))
    ((2 * m + 2) - 1)]
  have hsplit :
      (Finset.range ((2 * m + 2) - 1)).sum
          (fun k => (m + 1) - (k + 2)) =
        (Finset.range (m - 1)).sum (fun k => (m - 1) - k) := by
    calc
      _ = (Finset.range (m - 1)).sum
          (fun k => (m + 1) - (k + 2)) := by
        symm
        apply Finset.sum_subset
        · intro k hk
          simp only [Finset.mem_range] at hk ⊢
          omega
        · intro k hkall hksmall
          simp only [Finset.mem_range] at hkall hksmall
          omega
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k hk
        simp only [Finset.mem_range] at hk
        omega
  rw [hsplit]
  have hreflect :
      (Finset.range (m - 1)).sum (fun k => (m - 1) - k) =
        (Finset.range (m - 1)).sum (fun k => k + 1) := by
    calc
      _ = (Finset.range (m - 1)).sum
          (fun k => (m - 1 - 1 - k) + 1) := by
        apply Finset.sum_congr rfl
        intro k hk
        simp only [Finset.mem_range] at hk
        omega
      _ = _ := Finset.sum_range_reflect (fun k => k + 1) (m - 1)
  rw [hreflect]
  have hshift :
      (Finset.range (m - 1)).sum (fun k => k + 1) =
        (Finset.range m).sum (fun k => k) := by
    simpa [Nat.sub_add_cancel (by omega : 1 ≤ m)] using
      (Finset.sum_range_succ' (fun k : ℕ => k) (m - 1)).symm
  rw [hshift, Finset.sum_range_id]

/-- At the flagship retained order, the independent low-order weight kernels
have total dimension `m(m-1)/2`. -/
theorem bandWeightKernel_finrank_flagship (m : ℕ) (s : Fin (m + 1) → ℂ)
    (hs : Function.Injective s) (hm : 2 ≤ m) :
    Module.finrank ℂ (bandWeightKernel m (2 * m + 2) s) =
      m * (m - 1) / 2 := by
  rw [bandWeightKernel_finrank m (2 * m + 2) s hs,
    retained_kernel_sum m hm]

end

end CausalSmith.ExactID.EID_LingamDirectionMinOrderV1
