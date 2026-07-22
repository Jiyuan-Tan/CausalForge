/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Direct/latent source-pair swaps

The source permutation omitted from the admissible `G_m` action.  These lemmas
construct the forward and reverse swaps, show that they preserve the complete
cumulant map and the generic retained-band locus, and separate them from the
admissible orbit.
-/

import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.GenericSlopes
import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.Varieties

namespace CausalSmith.ExactID.EID_LingamDirectionMinOrderV1

open scoped BigOperators

/-- The source index `i+1` belonging to the `i`-th latent loading. -/
def latentSourceIndex {m : ℕ} (i : Fin m) : Fin (m + 2) :=
  ⟨i + 1, by omega⟩

/-- `θ'` interchanges the complete forward direct-source pair with latent pair `i`. -/
def IsForwardDirectLatentSwap {m : ℕ} (i : Fin m)
    (θ θ' : ParamSpace ℂ m) : Prop :=
  θ'.1 = θ.2.1 i ∧
  θ'.2.1 = Function.update θ.2.1 i θ.1 ∧
  θ'.2.2 = Function.update
    (Function.update θ.2.2 (0 : Fin (m + 2)) (θ.2.2 (latentSourceIndex i)))
    (latentSourceIndex i) (θ.2.2 0)

/-- `η'` interchanges the complete reverse direct-source pair with latent pair `i`. -/
def IsReverseDirectLatentSwap {m : ℕ} (i : Fin m)
    (η η' : ParamSpace ℂ m) : Prop :=
  η'.1 = η.2.1 i ∧
  η'.2.1 = Function.update η.2.1 i η.1 ∧
  η'.2.2 = Function.update
    (Function.update η.2.2 (Fin.last (m + 1)) (η.2.2 (latentSourceIndex i)))
    (latentSourceIndex i) (η.2.2 (Fin.last (m + 1)))

/-- The unordered finite-slope part of either arrow support. -/
def loadingSlopeMultiset {m : ℕ} (θ : ParamSpace ℂ m) : Multiset ℂ :=
  θ.1 ::ₘ (Finset.univ.val.map (fun i => θ.2.1 i))

/-- The concrete forward direct/latent swap. -/
def forwardDirectLatentSwap {m : ℕ} (i : Fin m) (θ : ParamSpace ℂ m) :
    ParamSpace ℂ m :=
  (θ.2.1 i, Function.update θ.2.1 i θ.1,
    Function.update
      (Function.update θ.2.2 (0 : Fin (m + 2)) (θ.2.2 (latentSourceIndex i)))
      (latentSourceIndex i) (θ.2.2 0))

/-- The concrete reverse direct/latent swap. -/
def reverseDirectLatentSwap {m : ℕ} (i : Fin m) (η : ParamSpace ℂ m) :
    ParamSpace ℂ m :=
  (η.2.1 i, Function.update η.2.1 i η.1,
    Function.update
      (Function.update η.2.2 (Fin.last (m + 1)) (η.2.2 (latentSourceIndex i)))
      (latentSourceIndex i) (η.2.2 (Fin.last (m + 1))))

lemma forwardDirectLatentSwap_spec {m : ℕ} (i : Fin m) (θ : ParamSpace ℂ m) :
    IsForwardDirectLatentSwap i θ (forwardDirectLatentSwap i θ) := by
  exact ⟨rfl, rfl, rfl⟩

lemma reverseDirectLatentSwap_spec {m : ℕ} (i : Fin m) (η : ParamSpace ℂ m) :
    IsReverseDirectLatentSwap i η (reverseDirectLatentSwap i η) := by
  exact ⟨rfl, rfl, rfl⟩

private lemma latentSourceIndex_ne_zero {m : ℕ} (i : Fin m) :
    latentSourceIndex i ≠ (0 : Fin (m + 2)) := by
  intro h
  have := congrArg Fin.val h
  simp [latentSourceIndex] at this

private lemma latentSourceIndex_ne_last {m : ℕ} (i : Fin m) :
    latentSourceIndex i ≠ Fin.last (m + 1) := by
  intro h
  have := congrArg Fin.val h
  simp [latentSourceIndex] at this
  omega

private lemma generic_of_coordinates {m L : ℕ} {θ : ParamSpace ℂ m}
    (hband : θ ∈ bandSupportedParams m L)
    (hdirect : θ.1 ≠ 0)
    (hcross : ∀ i, θ.1 ≠ θ.2.1 i)
    (hinj : Function.Injective θ.2.1)
    (hweights : ∀ j : Fin (m + 2), ∀ r ∈ Finset.Icc 2 L, θ.2.2 j r ≠ 0) :
    θ ∈ genericParameterLocus m L := by
  refine ⟨hband, mul_ne_zero (mul_ne_zero (mul_ne_zero hdirect ?_) ?_) ?_⟩
  · exact Finset.prod_ne_zero_iff.mpr fun i _ => sub_ne_zero.mpr (hcross i)
  · apply Finset.prod_ne_zero_iff.mpr
    intro i _
    apply Finset.prod_ne_zero_iff.mpr
    intro i' _
    split
    · exact sub_ne_zero.mpr (hinj.ne (by omega))
    · exact one_ne_zero
  · apply Finset.prod_ne_zero_iff.mpr
    intro j _
    exact Finset.prod_ne_zero_iff.mpr (hweights j)

private lemma retained_weight_ne_zero_of_generic {m L : ℕ} {θ : ParamSpace ℂ m}
    (hθ : θ ∈ genericParameterLocus m L) :
    ∀ j : Fin (m + 2), ∀ r ∈ Finset.Icc 2 L, θ.2.2 j r ≠ 0 := by
  have hp := genericParameterLocus_prod_ne_zero hθ
  have hw : (∏ j : Fin (m + 2), ∏ r ∈ Finset.Icc 2 L, θ.2.2 j r) ≠ 0 :=
    (mul_ne_zero_iff.mp hp).2
  intro j r hr
  exact Finset.prod_ne_zero_iff.mp
    (Finset.prod_ne_zero_iff.mp hw j (Finset.mem_univ j)) r hr

/-- Proves the stated mathematical property of forward Direct Latent Swap generic. -/
lemma forwardDirectLatentSwap_generic {m L : ℕ} (i : Fin m) (θ : ParamSpace ℂ m)
    (hθ : θ ∈ genericParameterLocus m L) (hρi : θ.2.1 i ≠ 0) :
    forwardDirectLatentSwap i θ ∈ genericParameterLocus m L := by
  apply generic_of_coordinates
  · intro j r hr
    simp only [forwardDirectLatentSwap]
    by_cases hji : j = latentSourceIndex i
    · subst j
      simp [latentSourceIndex_ne_zero, genericParameterLocus_bandSupported hθ _ r hr]
    by_cases hj0 : j = 0
    · subst j
      simp [hji, latentSourceIndex_ne_zero,
        genericParameterLocus_bandSupported hθ (latentSourceIndex i) r hr]
    simp [hji, hj0, genericParameterLocus_bandSupported hθ j r hr]
  · exact hρi
  · intro j
    by_cases hji : j = i
    · subst j
      simpa [forwardDirectLatentSwap] using (gamma_ne_rho_of_generic hθ i).symm
    · simpa [forwardDirectLatentSwap, hji] using
        (rho_injective_of_generic hθ).ne (Ne.symm hji)
  · intro j k hjk
    by_cases hji : j = i
    · subst j
      by_cases hki : k = i
      · exact hki.symm
      · simp [forwardDirectLatentSwap, hki] at hjk
        exact ((gamma_ne_rho_of_generic hθ k) hjk).elim
    · by_cases hki : k = i
      · subst k
        simp [forwardDirectLatentSwap, hji] at hjk
        exact ((gamma_ne_rho_of_generic hθ j) hjk.symm).elim
      · simp [forwardDirectLatentSwap, hji, hki] at hjk
        exact (rho_injective_of_generic hθ) hjk
  · intro j r hr
    have hw := retained_weight_ne_zero_of_generic hθ
    simp only [forwardDirectLatentSwap]
    by_cases hji : j = latentSourceIndex i
    · subst j
      simpa [latentSourceIndex_ne_zero] using hw (0 : Fin (m + 2)) r hr
    by_cases hj0 : j = 0
    · subst j
      simpa [hji, latentSourceIndex_ne_zero] using hw (latentSourceIndex i) r hr
    simpa [hji, hj0] using hw j r hr

/-- Proves the stated mathematical property of reverse Direct Latent Swap generic. -/
lemma reverseDirectLatentSwap_generic {m L : ℕ} (i : Fin m) (η : ParamSpace ℂ m)
    (hη : η ∈ genericParameterLocus m L) (hσi : η.2.1 i ≠ 0) :
    reverseDirectLatentSwap i η ∈ genericParameterLocus m L := by
  apply generic_of_coordinates
  · intro j r hr
    simp only [reverseDirectLatentSwap]
    by_cases hji : j = latentSourceIndex i
    · subst j
      simp [latentSourceIndex_ne_last, genericParameterLocus_bandSupported hη _ r hr]
    by_cases hjl : j = Fin.last (m + 1)
    · subst j
      simp [hji, latentSourceIndex_ne_last,
        genericParameterLocus_bandSupported hη (latentSourceIndex i) r hr]
    simp [hji, hjl, genericParameterLocus_bandSupported hη j r hr]
  · exact hσi
  · intro j
    by_cases hji : j = i
    · subst j
      simpa [reverseDirectLatentSwap] using (gamma_ne_rho_of_generic hη i).symm
    · simpa [reverseDirectLatentSwap, hji] using
        (rho_injective_of_generic hη).ne (Ne.symm hji)
  · intro j k hjk
    by_cases hji : j = i
    · subst j
      by_cases hki : k = i
      · exact hki.symm
      · simp [reverseDirectLatentSwap, hki] at hjk
        exact ((gamma_ne_rho_of_generic hη k) hjk).elim
    · by_cases hki : k = i
      · subst k
        simp [reverseDirectLatentSwap, hji] at hjk
        exact ((gamma_ne_rho_of_generic hη j) hjk.symm).elim
      · simp [reverseDirectLatentSwap, hji, hki] at hjk
        exact (rho_injective_of_generic hη) hjk
  · intro j r hr
    have hw := retained_weight_ne_zero_of_generic hη
    simp only [reverseDirectLatentSwap]
    by_cases hji : j = latentSourceIndex i
    · subst j
      simpa [latentSourceIndex_ne_last] using hw (Fin.last (m + 1)) r hr
    by_cases hjl : j = Fin.last (m + 1)
    · subst j
      simpa [hji, latentSourceIndex_ne_last] using hw (latentSourceIndex i) r hr
    simpa [hji, hjl] using hw j r hr

private lemma forward_swap_weight {m : ℕ} (i : Fin m) (θ : ParamSpace ℂ m)
    (j : Fin (m + 2)) (r : ℕ) :
    (forwardDirectLatentSwap i θ).2.2 j r =
      θ.2.2 (Equiv.swap (0 : Fin (m + 2)) (latentSourceIndex i) j) r := by
  by_cases hj0 : j = 0
  · subst j
    simp [forwardDirectLatentSwap, Function.update, latentSourceIndex_ne_zero,
      (latentSourceIndex_ne_zero i).symm]
  by_cases hji : j = latentSourceIndex i
  · subst j
    simp [forwardDirectLatentSwap, Function.update, latentSourceIndex_ne_zero]
  have hs : Equiv.swap (0 : Fin (m + 2)) (latentSourceIndex i) j = j :=
    Equiv.swap_apply_of_ne_of_ne hj0 hji
  simp [forwardDirectLatentSwap, Function.update, hj0, hji, hs]

private lemma forward_swap_loading {m : ℕ} (i : Fin m) (θ : ParamSpace ℂ m)
    (j : Fin (m + 2)) :
    forwardLoading m (forwardDirectLatentSwap i θ).1
        (forwardDirectLatentSwap i θ).2.1 j =
      forwardLoading m θ.1 θ.2.1
        (Equiv.swap (0 : Fin (m + 2)) (latentSourceIndex i) j) := by
  by_cases hj0 : j = 0
  · subst j
    have hi : i.val ≠ m := Nat.ne_of_lt i.isLt
    simp [forwardDirectLatentSwap, forwardLoading, latentSourceIndex, hi]
  by_cases hji : j = latentSourceIndex i
  · subst j
    have hi : i.val ≠ m := Nat.ne_of_lt i.isLt
    simp [forwardDirectLatentSwap, forwardLoading, latentSourceIndex, hi]
  by_cases hjlast : j.val = m + 1
  · have hs : Equiv.swap (0 : Fin (m + 2)) (latentSourceIndex i) j = j :=
      Equiv.swap_apply_of_ne_of_ne hj0 hji
    rw [hs]
    simp [forwardLoading, hjlast]
  have hs : Equiv.swap (0 : Fin (m + 2)) (latentSourceIndex i) j = j :=
    Equiv.swap_apply_of_ne_of_ne hj0 hji
  have hjv0 : j.val ≠ 0 := by
    intro h
    exact hj0 (Fin.ext h)
  have hmidlt : j.val - 1 < m := by
    have := j.isLt
    omega
  have hidx : (⟨j.val - 1, hmidlt⟩ : Fin m) ≠ i := by
    intro h
    apply hji
    apply Fin.ext
    change j.val = i.val + 1
    have hv := congrArg Fin.val h
    change j.val - 1 = i.val at hv
    have hjpos : 0 < j.val := by
      apply Nat.pos_of_ne_zero
      intro hjv
      apply hj0
      exact Fin.ext hjv
    omega
  simp [forwardDirectLatentSwap, forwardLoading, hj0, hjlast, hs, hidx]

private lemma forward_swap_summand {m : ℕ} (i : Fin m) (θ : ParamSpace ℂ m)
    (j : Fin (m + 2)) (r a : ℕ) :
    (forwardDirectLatentSwap i θ).2.2 j r *
        (forwardLoading m (forwardDirectLatentSwap i θ).1
          (forwardDirectLatentSwap i θ).2.1 j).1 ^ (r - a) *
        (forwardLoading m (forwardDirectLatentSwap i θ).1
          (forwardDirectLatentSwap i θ).2.1 j).2 ^ a =
      θ.2.2 (Equiv.swap (0 : Fin (m + 2)) (latentSourceIndex i) j) r *
        (forwardLoading m θ.1 θ.2.1
          (Equiv.swap (0 : Fin (m + 2)) (latentSourceIndex i) j)).1 ^ (r - a) *
        (forwardLoading m θ.1 θ.2.1
          (Equiv.swap (0 : Fin (m + 2)) (latentSourceIndex i) j)).2 ^ a := by
  rw [forward_swap_weight, forward_swap_loading]

/-- Proves the stated mathematical property of forward Cumulant Map direct Latent Swap. -/
lemma forwardCumulantMap_directLatentSwap {m L : ℕ} (i : Fin m) (θ : ParamSpace ℂ m) :
    forwardCumulantMap m L (forwardDirectLatentSwap i θ) = forwardCumulantMap m L θ := by
  funext r a
  simp only [forwardCumulantMap]
  split
  · calc
      _ = ∑ j : Fin (m + 2),
          θ.2.2 (Equiv.swap (0 : Fin (m + 2)) (latentSourceIndex i) j) r *
            (forwardLoading m θ.1 θ.2.1
              (Equiv.swap (0 : Fin (m + 2)) (latentSourceIndex i) j)).1 ^ (r - a) *
            (forwardLoading m θ.1 θ.2.1
              (Equiv.swap (0 : Fin (m + 2)) (latentSourceIndex i) j)).2 ^ a := by
            apply Finset.sum_congr rfl
            intro j _
            exact forward_swap_summand i θ j r a
      _ = _ := Equiv.sum_comp (Equiv.swap (0 : Fin (m + 2)) (latentSourceIndex i))
        (fun j : Fin (m + 2) =>
          θ.2.2 j r * (forwardLoading m θ.1 θ.2.1 j).1 ^ (r - a) *
            (forwardLoading m θ.1 θ.2.1 j).2 ^ a)
  · rfl

private lemma reverse_swap_weight {m : ℕ} (i : Fin m) (η : ParamSpace ℂ m)
    (j : Fin (m + 2)) (r : ℕ) :
    (reverseDirectLatentSwap i η).2.2 j r =
      η.2.2 (Equiv.swap (Fin.last (m + 1)) (latentSourceIndex i) j) r := by
  by_cases hjl : j = Fin.last (m + 1)
  · subst j
    simp [reverseDirectLatentSwap, Function.update, latentSourceIndex_ne_last,
      (latentSourceIndex_ne_last i).symm]
  by_cases hji : j = latentSourceIndex i
  · subst j
    simp [reverseDirectLatentSwap, Function.update, latentSourceIndex_ne_last]
  have hs : Equiv.swap (Fin.last (m + 1)) (latentSourceIndex i) j = j :=
    Equiv.swap_apply_of_ne_of_ne hjl hji
  simp [reverseDirectLatentSwap, Function.update, hjl, hji, hs]

private lemma reverse_swap_loading {m : ℕ} (i : Fin m) (η : ParamSpace ℂ m)
    (j : Fin (m + 2)) :
    reverseLoading m (reverseDirectLatentSwap i η).1
        (reverseDirectLatentSwap i η).2.1 j =
      reverseLoading m η.1 η.2.1
        (Equiv.swap (Fin.last (m + 1)) (latentSourceIndex i) j) := by
  by_cases hjl : j = Fin.last (m + 1)
  · subst j
    have hi : i.val ≠ m := Nat.ne_of_lt i.isLt
    simp [reverseDirectLatentSwap, reverseLoading, latentSourceIndex, hi]
  by_cases hji : j = latentSourceIndex i
  · subst j
    have hi : i.val ≠ m := Nat.ne_of_lt i.isLt
    simp [reverseDirectLatentSwap, reverseLoading, latentSourceIndex, hi]
  by_cases hj0 : j = 0
  · subst j
    have hs : Equiv.swap (Fin.last (m + 1)) (latentSourceIndex i)
        (0 : Fin (m + 2)) = 0 :=
      Equiv.swap_apply_of_ne_of_ne hjl hji
    rw [hs]
    simp [reverseLoading]
  have hjlast : j.val ≠ m + 1 := by
    intro h
    exact hjl (Fin.ext h)
  have hs : Equiv.swap (Fin.last (m + 1)) (latentSourceIndex i) j = j :=
    Equiv.swap_apply_of_ne_of_ne hjl hji
  have hjv0 : j.val ≠ 0 := by
    intro h
    exact hj0 (Fin.ext h)
  have hmidlt : j.val - 1 < m := by
    have := j.isLt
    omega
  have hidx : (⟨j.val - 1, hmidlt⟩ : Fin m) ≠ i := by
    intro h
    apply hji
    apply Fin.ext
    change j.val = i.val + 1
    have hv := congrArg Fin.val h
    change j.val - 1 = i.val at hv
    have hjpos : 0 < j.val := by
      apply Nat.pos_of_ne_zero
      intro hjv
      apply hj0
      exact Fin.ext hjv
    omega
  simp [reverseDirectLatentSwap, reverseLoading, hj0, hjlast, hs, hidx]

-- The reverse calculation is the coordinate-reversed mirror of the forward one.
private lemma reverse_swap_summand {m : ℕ} (i : Fin m) (η : ParamSpace ℂ m)
    (j : Fin (m + 2)) (r a : ℕ) :
    (reverseDirectLatentSwap i η).2.2 j r *
        (reverseLoading m (reverseDirectLatentSwap i η).1
          (reverseDirectLatentSwap i η).2.1 j).1 ^ (r - a) *
        (reverseLoading m (reverseDirectLatentSwap i η).1
          (reverseDirectLatentSwap i η).2.1 j).2 ^ a =
      η.2.2 (Equiv.swap (Fin.last (m + 1)) (latentSourceIndex i) j) r *
        (reverseLoading m η.1 η.2.1
          (Equiv.swap (Fin.last (m + 1)) (latentSourceIndex i) j)).1 ^ (r - a) *
        (reverseLoading m η.1 η.2.1
          (Equiv.swap (Fin.last (m + 1)) (latentSourceIndex i) j)).2 ^ a := by
  rw [reverse_swap_weight, reverse_swap_loading]

/-- Proves the stated mathematical property of reverse Cumulant Map direct Latent Swap. -/
lemma reverseCumulantMap_directLatentSwap {m L : ℕ} (i : Fin m) (η : ParamSpace ℂ m) :
    reverseCumulantMap m L (reverseDirectLatentSwap i η) = reverseCumulantMap m L η := by
  funext r a
  simp only [reverseCumulantMap]
  split
  · calc
      _ = ∑ j : Fin (m + 2),
          η.2.2 (Equiv.swap (Fin.last (m + 1)) (latentSourceIndex i) j) r *
            (reverseLoading m η.1 η.2.1
              (Equiv.swap (Fin.last (m + 1)) (latentSourceIndex i) j)).1 ^ (r - a) *
            (reverseLoading m η.1 η.2.1
              (Equiv.swap (Fin.last (m + 1)) (latentSourceIndex i) j)).2 ^ a := by
            apply Finset.sum_congr rfl
            intro j _
            exact reverse_swap_summand i η j r a
      _ = _ := Equiv.sum_comp
        (Equiv.swap (Fin.last (m + 1)) (latentSourceIndex i))
        (fun j : Fin (m + 2) =>
          η.2.2 j r * (reverseLoading m η.1 η.2.1 j).1 ^ (r - a) *
            (reverseLoading m η.1 η.2.1 j).2 ^ a)
  · rfl

/-- Proves the stated set-containment or membership property for forward Direct Latent Swap not mem admissible Orbit. -/
lemma forwardDirectLatentSwap_not_mem_admissibleOrbit {m : ℕ} (i : Fin m)
    (θ : ParamSpace ℂ m) (hneq : θ.1 ≠ θ.2.1 i) :
    forwardDirectLatentSwap i θ ∉ admissibleOrbit θ := by
  rintro ⟨π, hπ⟩
  have := congrArg Prod.fst hπ
  exact hneq (by simpa [forwardDirectLatentSwap, admissibleSourceSwap] using this.symm)

/-- Proves the stated set-containment or membership property for reverse Direct Latent Swap not mem admissible Orbit. -/
lemma reverseDirectLatentSwap_not_mem_admissibleOrbit {m : ℕ} (i : Fin m)
    (η : ParamSpace ℂ m) (hneq : η.1 ≠ η.2.1 i) :
    reverseDirectLatentSwap i η ∉ admissibleOrbit η := by
  rintro ⟨π, hπ⟩
  have := congrArg Prod.fst hπ
  exact hneq (by simpa [reverseDirectLatentSwap, admissibleSourceSwap] using this.symm)

end CausalSmith.ExactID.EID_LingamDirectionMinOrderV1
