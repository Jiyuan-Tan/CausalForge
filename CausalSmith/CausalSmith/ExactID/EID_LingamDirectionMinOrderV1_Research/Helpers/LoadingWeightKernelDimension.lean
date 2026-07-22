/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Weight kernels for the two axis-conditioned loading families
-/

import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.BandWeightKernelDimension
import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.GenericSlopes

namespace CausalSmith.ExactID.EID_LingamDirectionMinOrderV1

open scoped BigOperators

noncomputable section

/-- The linear weight-synthesis map attached to an arbitrary loading family. -/
def loadingOrderSynthesis {n : ℕ} (u : Fin n → ℂ × ℂ) (r : ℕ) :
    (Fin n → ℂ) →ₗ[ℂ] (Fin (r + 1) → ℂ) where
  toFun z a := ∑ j, z j * (u j).1 ^ (r - a.val) * (u j).2 ^ a.val
  map_add' x y := by
    funext a
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c x := by
    funext a
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

/-- Fixing the loading coordinates leaves the product of the orderwise
loading-synthesis kernels. -/
def loadingBandWeightKernel (m L : ℕ) (u : Fin (m + 2) → ℂ × ℂ) :
    Submodule ℂ (BandParamCoord m L → ℂ) where
  carrier := {x |
    x (Sum.inl ()) = 0 ∧
    (∀ i, x (Sum.inr (Sum.inl i)) = 0) ∧
    ∀ k : Fin (L - 1), loadingOrderSynthesis u (k.val + 2)
      (fun j => x (Sum.inr (Sum.inr (j, k)))) = 0}
  zero_mem' := by
    refine ⟨rfl, fun _ => rfl, ?_⟩
    intro k
    change loadingOrderSynthesis u (k.val + 2) 0 = 0
    exact (loadingOrderSynthesis u (k.val + 2)).map_zero
  add_mem' {x y} hx hy := by
    refine ⟨by simp [hx.1, hy.1], fun i => by simp [hx.2.1 i, hy.2.1 i], ?_⟩
    intro k
    change loadingOrderSynthesis u (k.val + 2)
      ((fun j => x (Sum.inr (Sum.inr (j, k)))) +
        fun j => y (Sum.inr (Sum.inr (j, k)))) = 0
    rw [map_add, hx.2.2 k, hy.2.2 k, add_zero]
  smul_mem' c x hx := by
    refine ⟨by simp [hx.1], fun i => by simp [hx.2.1 i], ?_⟩
    intro k
    change loadingOrderSynthesis u (k.val + 2)
      (c • fun j => x (Sum.inr (Sum.inr (j, k)))) = 0
    rw [map_smul, hx.2.2 k, smul_zero]

private lemma forward_loadingOrderSynthesis_eq (m r : ℕ) (γ : ℂ) (ρ : Fin m → ℂ) :
    loadingOrderSynthesis (forwardLoading m γ ρ) r =
      endpointOrderSynthesis
        (fun j : Fin (m + 1) =>
          (forwardLoading m γ ρ j.castSucc).2) r := by
  apply LinearMap.ext
  intro z
  funext a
  simp only [loadingOrderSynthesis, endpointOrderSynthesis, LinearMap.coe_mk,
    AddHom.coe_mk]
  rw [Fin.sum_univ_castSucc]
  have hfinite : ∀ j : Fin (m + 1),
      (forwardLoading m γ ρ j.castSucc).1 = 1 := by
    intro j
    by_cases h0 : j.val = 0
    · simp [forwardLoading, h0]
    · have hlast : j.val ≠ m + 1 := by omega
      simp [forwardLoading, h0, hlast]
  rw [show forwardLoading m γ ρ (Fin.last (m + 1)) = (0, 1) by
    simp [forwardLoading]]
  simp only [hfinite, one_pow, mul_one, Prod.fst, Prod.snd, one_pow, mul_one]
  by_cases ha : a.val = r
  · simp [ha]
  · have hpos : 0 < r - a.val := Nat.sub_pos_of_lt (by omega)
    simp [ha, Nat.ne_of_gt hpos]

private lemma reverse_loadingOrderSynthesis_eq (m r : ℕ) (δ : ℂ) (σ : Fin m → ℂ)
    (z : Fin (m + 2) → ℂ) (a : Fin (r + 1)) :
    loadingOrderSynthesis (reverseLoading m δ σ) r z a =
      endpointOrderSynthesis
        (fun j : Fin (m + 1) => (reverseLoading m δ σ j.succ).1) r
        (Fin.lastCases (z 0) (fun j => z j.succ)) a.rev := by
  simp only [loadingOrderSynthesis, endpointOrderSynthesis, LinearMap.coe_mk,
    AddHom.coe_mk]
  rw [Fin.sum_univ_succ]
  have hfinite : ∀ j : Fin (m + 1),
      (reverseLoading m δ σ j.succ).2 = 1 := by
    intro j
    by_cases hlast : j.val = m
    · simp [reverseLoading, hlast]
    · simp [reverseLoading, hlast]
  rw [show reverseLoading m δ σ 0 = (1, 0) by simp [reverseLoading]]
  simp only [hfinite, one_pow, mul_one, Prod.fst, Prod.snd]
  have hsum : ∀ j : Fin (m + 1),
      (Fin.lastCases (z 0) (fun j => z j.succ) : Fin (m + 2) → ℂ) j.castSucc =
        z j.succ := by simp
  simp only [hsum]
  have harev : a.rev.val + a.val = r := a.rev_add_cast
  have hsub : r - a.val = a.rev.val := by omega
  rw [hsub]
  by_cases ha : a.val = 0
  · have harevlast : a.rev.val = r := by omega
    simp [ha, harevlast, add_comm]
  · have hpos : 0 < a.val := Nat.pos_of_ne_zero ha
    have harevne : a.rev.val ≠ r := by omega
    have hzpow : (0 : ℂ) ^ a.val = 0 := zero_pow (Nat.ne_of_gt hpos)
    rw [hzpow, mul_zero, zero_add, if_neg harevne, add_zero]

/-- Proves that the map or coordinate assignment called the forward loading Band Weight Kernel finrank of is injective. -/
theorem forward_loadingBandWeightKernel_finrank_of_injective (m : ℕ)
    (θ : ParamSpace ℂ m)
    (hs : Function.Injective (fun j : Fin (m + 1) =>
      (forwardLoading m θ.1 θ.2.1 j.castSucc).2)) (hm : 2 ≤ m) :
    Module.finrank ℂ
      (loadingBandWeightKernel m (2 * m + 2) (forwardLoading m θ.1 θ.2.1)) =
        m * (m - 1) / 2 := by
  let s := fun j : Fin (m + 1) =>
    (forwardLoading m θ.1 θ.2.1 j.castSucc).2
  have heq : loadingBandWeightKernel m (2 * m + 2)
      (forwardLoading m θ.1 θ.2.1) =
      bandWeightKernel m (2 * m + 2) s := by
    ext x
    simp only [loadingBandWeightKernel, bandWeightKernel, Submodule.mem_mk,
      Set.mem_setOf_eq]
    dsimp [s]
    constructor
    · rintro ⟨hzero, hslope, horder⟩
      refine ⟨hzero, hslope, ?_⟩
      intro k
      rw [← forward_loadingOrderSynthesis_eq]
      exact horder k
    · rintro ⟨hzero, hslope, horder⟩
      refine ⟨hzero, hslope, ?_⟩
      intro k
      rw [forward_loadingOrderSynthesis_eq]
      exact horder k
  rw [heq]
  exact bandWeightKernel_finrank_flagship m s hs hm

/-- Establishes the stated dimension formula for forward loading Band Weight Kernel. -/
theorem forward_loadingBandWeightKernel_finrank (m : ℕ) (θ : ParamSpace ℂ m)
    (hθ : θ ∈ genericParameterLocus m (2 * m + 2)) (hm : 2 ≤ m) :
    Module.finrank ℂ
      (loadingBandWeightKernel m (2 * m + 2) (forwardLoading m θ.1 θ.2.1)) =
        m * (m - 1) / 2 :=
  forward_loadingBandWeightKernel_finrank_of_injective m θ
    (forward_slopes_injective_of_generic hθ) hm

private def reverseLoadingKernelEquiv (m L : ℕ) (δ : ℂ) (σ : Fin m → ℂ) :
    loadingBandWeightKernel m L (reverseLoading m δ σ) ≃ₗ[ℂ]
      (∀ k : Fin (L - 1), LinearMap.ker (endpointOrderSynthesis
        (fun j : Fin (m + 1) => (reverseLoading m δ σ j.succ).1) (k.val + 2))) where
  toFun x k := ⟨Fin.lastCases
      (x.1 (Sum.inr (Sum.inr (0, k))))
      (fun j => x.1 (Sum.inr (Sum.inr (j.succ, k)))), by
    funext a
    calc
      _ = loadingOrderSynthesis (reverseLoading m δ σ) (k.val + 2)
          (fun j => x.1 (Sum.inr (Sum.inr (j, k)))) a.rev := by
        symm
        simpa using reverse_loadingOrderSynthesis_eq
          m (k.val + 2) δ σ (fun j => x.1 (Sum.inr (Sum.inr (j, k)))) a.rev
      _ = 0 := congrFun (x.2.2.2 k) a.rev⟩
  invFun z := ⟨fun c =>
    match c with
    | Sum.inl _ => 0
    | Sum.inr (Sum.inl _) => 0
    | Sum.inr (Sum.inr (j, k)) => Fin.cases ((z k).1 (Fin.last (m + 1)))
        (fun i => (z k).1 i.castSucc) j,
    by
      refine ⟨rfl, fun _ => rfl, ?_⟩
      intro k
      change loadingOrderSynthesis (reverseLoading m δ σ) (k.val + 2)
        (Fin.cases ((z k).1 (Fin.last (m + 1)))
          (fun i => (z k).1 i.castSucc)) = 0
      funext a
      rw [reverse_loadingOrderSynthesis_eq]
      have hv :
          (Fin.lastCases ((z k).1 (Fin.last (m + 1)))
            (fun i => (z k).1 i.castSucc) : Fin (m + 2) → ℂ) = (z k).1 := by
        funext j
        refine Fin.lastCases ?_ (fun i => ?_) j <;> simp
      have hcases :
          (Fin.lastCases
            (Fin.cases ((z k).1 (Fin.last (m + 1)))
              (fun i => (z k).1 i.castSucc) 0)
            (fun j => Fin.cases ((z k).1 (Fin.last (m + 1)))
              (fun i => (z k).1 i.castSucc) j.succ) : Fin (m + 2) → ℂ) =
            Fin.lastCases ((z k).1 (Fin.last (m + 1)))
              (fun i => (z k).1 i.castSucc) := by
        funext j
        refine Fin.lastCases ?_ (fun i => ?_) j <;> simp
      rw [hcases, hv]
      exact congrFun (z k).property a.rev⟩
  map_add' x y := by
    funext k
    apply Subtype.ext
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j <;> simp
  map_smul' c x := by
    funext k
    apply Subtype.ext
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j <;> simp
  left_inv x := by
    apply Subtype.ext
    funext c
    rcases c with _ | (i | ⟨j, k⟩)
    · exact x.2.1.symm
    · exact (x.2.2.1 i).symm
    · refine Fin.cases ?_ (fun q => ?_) j <;> simp
  right_inv z := by
    funext k
    apply Subtype.ext
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j <;> simp

/-- Proves that the map or coordinate assignment called the reverse loading Band Weight Kernel finrank of is injective. -/
theorem reverse_loadingBandWeightKernel_finrank_of_injective (m : ℕ)
    (η : ParamSpace ℂ m)
    (hs : Function.Injective (fun j : Fin (m + 1) =>
      (reverseLoading m η.1 η.2.1 j.succ).1)) (hm : 2 ≤ m) :
    Module.finrank ℂ
      (loadingBandWeightKernel m (2 * m + 2) (reverseLoading m η.1 η.2.1)) =
        m * (m - 1) / 2 := by
  let s := fun j : Fin (m + 1) =>
    (reverseLoading m η.1 η.2.1 j.succ).1
  rw [(reverseLoadingKernelEquiv m (2 * m + 2) η.1 η.2.1).finrank_eq,
    Module.finrank_pi_fintype]
  calc
    _ = Finset.univ.sum (fun k : Fin ((2 * m + 2) - 1) =>
        (m + 1) - (k.val + 2)) := by
      apply Finset.sum_congr rfl
      intro k _
      exact endpointOrderSynthesis_ker_finrank s hs
    _ = _ := retained_kernel_sum m hm

/-- Establishes the stated dimension formula for reverse loading Band Weight Kernel. -/
theorem reverse_loadingBandWeightKernel_finrank (m : ℕ) (η : ParamSpace ℂ m)
    (hη : η ∈ genericParameterLocus m (2 * m + 2)) (hm : 2 ≤ m) :
    Module.finrank ℂ
      (loadingBandWeightKernel m (2 * m + 2) (reverseLoading m η.1 η.2.1)) =
        m * (m - 1) / 2 :=
  reverse_loadingBandWeightKernel_finrank_of_injective m η
    (reverse_slopes_injective_of_generic hη) hm

end

end CausalSmith.ExactID.EID_LingamDirectionMinOrderV1
