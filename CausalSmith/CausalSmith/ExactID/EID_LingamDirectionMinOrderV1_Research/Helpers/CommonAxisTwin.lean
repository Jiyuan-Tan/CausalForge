/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# The common-axis opposite-arrow twin
-/

import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.ArrowPolynomialGeometry
import CausalSmith.ExactID.EID_LingamDirectionMinOrderV1_Research.Helpers.GenericSlopes

namespace CausalSmith.ExactID.EID_LingamDirectionMinOrderV1

open scoped BigOperators

noncomputable section

/-- The generic forward parameter divisor on which the first latent direction
is the horizontal axis. -/
def forwardCommonAxisDivisor (m : ℕ) (hm : 1 ≤ m) : Set (ParamSpace ℂ m) :=
  {θ | θ ∈ genericParameterLocus m (2 * m + 2) ∧ θ.2.1 ⟨0, hm⟩ = 0}

private def commonAxisIndex (m : ℕ) (hm : 1 ≤ m) (j : Fin (m + 2)) : Fin (m + 2) :=
  if j.val = 0 then ⟨1, by omega⟩
  else if j.val = 1 then Fin.last (m + 1)
  else if j.val = m + 1 then 0
  else j

private def commonAxisIndexInv (m : ℕ) (hm : 1 ≤ m) (j : Fin (m + 2)) : Fin (m + 2) :=
  if j.val = 0 then Fin.last (m + 1)
  else if j.val = 1 then 0
  else if j.val = m + 1 then ⟨1, by omega⟩
  else j

private def commonAxisPermutation (m : ℕ) (hm : 1 ≤ m) : Equiv.Perm (Fin (m + 2)) where
  toFun := commonAxisIndex m hm
  invFun := commonAxisIndexInv m hm
  left_inv j := by
    have hm0 : m ≠ 0 := by omega
    by_cases h0 : j.val = 0 <;> by_cases h1 : j.val = 1 <;>
      by_cases hlast : j.val = m + 1 <;> apply Fin.ext <;>
      simp [commonAxisIndex, commonAxisIndexInv, h0, h1, hlast, Fin.last, hm0] <;> omega
  right_inv j := by
    have hm0 : m ≠ 0 := by omega
    by_cases h0 : j.val = 0 <;> by_cases h1 : j.val = 1 <;>
      by_cases hlast : j.val = m + 1 <;> apply Fin.ext <;>
      simp [commonAxisIndex, commonAxisIndexInv, h0, h1, hlast, Fin.last, hm0] <;> omega

private lemma commonAxisPermutation_apply (m : ℕ) (hm : 1 ≤ m)
    (j : Fin (m + 2)) :
    commonAxisPermutation m hm j = commonAxisIndex m hm j := rfl

@[simp] private lemma commonAxisIndex_zero (m : ℕ) (hm : 1 ≤ m) :
    commonAxisIndex m hm 0 = ⟨1, by omega⟩ := by
  simp [commonAxisIndex, commonAxisPermutation, Equiv.trans_apply, Equiv.swap_apply_def]

@[simp] private lemma commonAxisIndex_one (m : ℕ) (hm : 1 ≤ m) :
    commonAxisIndex m hm ⟨1, by omega⟩ = Fin.last (m + 1) := by
  have hm0 : m ≠ 0 := by omega
  apply Fin.ext
  simp [commonAxisIndex, Fin.last, hm0]

@[simp] private lemma commonAxisIndex_last (m : ℕ) (hm : 1 ≤ m) :
    commonAxisIndex m hm (Fin.last (m + 1)) = 0 := by
  have hm0 : m ≠ 0 := by omega
  apply Fin.ext
  simp [commonAxisIndex, Fin.last, hm0]

private lemma commonAxisIndex_mid {m : ℕ} (hm : 1 ≤ m) (j : Fin (m + 2))
    (h0 : j.val ≠ 0) (h1 : j.val ≠ 1) (hlast : j.val ≠ m + 1) :
    commonAxisIndex m hm j = j := by
  simp [commonAxisIndex, Fin.last, Fin.ext_iff, h0, h1, hlast]

/-- Reverse parameters obtained by reciprocating every nonzero finite forward
slope and cycling the two fixed axes with the zero latent direction. -/
def commonAxisReverseTwin (m : ℕ) (hm : 1 ≤ m) (θ : ParamSpace ℂ m) :
    ParamSpace ℂ m :=
  (θ.1⁻¹,
    (fun i => if i.val = 0 then 0 else (θ.2.1 i)⁻¹),
    fun j r =>
      let c := θ.2.2 (commonAxisIndex m hm j) r
      if hlast : j.val = m + 1 then c * θ.1 ^ r
      else if htwo : 2 ≤ j.val then c * θ.2.1 ⟨j.val - 1, by omega⟩ ^ r
      else c)

lemma commonAxisReverseTwin_bandSupported {m : ℕ} (hm : 1 ≤ m)
    {θ : ParamSpace ℂ m} (hθ : θ ∈ bandSupportedParams m (2 * m + 2)) :
    commonAxisReverseTwin m hm θ ∈ bandSupportedParams m (2 * m + 2) := by
  intro j r hr
  simp only [commonAxisReverseTwin]
  have hc : θ.2.2 (commonAxisIndex m hm j) r = 0 := hθ _ _ hr
  simp [commonAxisReverseTwin, hc]

private lemma retainedWeight_ne_zero_of_generic {m L : ℕ}
    {θ : ParamSpace ℂ m} (hθ : θ ∈ genericParameterLocus m L)
    (j : Fin (m + 2)) {r : ℕ} (hr : r ∈ Finset.Icc 2 L) :
    θ.2.2 j r ≠ 0 := by
  have hall := genericParameterLocus_prod_ne_zero hθ
  have hwprod : (∏ j : Fin (m + 2), ∏ r ∈ Finset.Icc 2 L,
      θ.2.2 j r) ≠ 0 := (mul_ne_zero_iff.mp hall).2
  exact (Finset.prod_ne_zero_iff.mp
    (Finset.prod_ne_zero_iff.mp hwprod j (Finset.mem_univ j))) r hr

/-- The reciprocal common-axis twin stays in the generic retained-band locus.
This is the parameter-level symmetry needed to transport the common-axis
closure through observable coordinate reversal. -/
lemma commonAxisReverseTwin_generic {m : ℕ} (hm : 1 ≤ m)
    {θ : ParamSpace ℂ m} (hθ : θ ∈ forwardCommonAxisDivisor m hm) :
    commonAxisReverseTwin m hm θ ∈ genericParameterLocus m (2 * m + 2) := by
  let L := 2 * m + 2
  let η := commonAxisReverseTwin m hm θ
  have hband : η ∈ bandSupportedParams m L :=
    commonAxisReverseTwin_bandSupported hm
      (genericParameterLocus_bandSupported hθ.1)
  have hγ : θ.1 ≠ 0 := gamma_ne_zero_of_generic hθ.1
  have hρinj : Function.Injective θ.2.1 := rho_injective_of_generic hθ.1
  have hρ : ∀ i : Fin m, i.val ≠ 0 → θ.2.1 i ≠ 0 := by
    intro i hi hzero
    have heq : i = ⟨0, hm⟩ := hρinj (hzero.trans hθ.2.symm)
    exact hi (congrArg Fin.val heq)
  have hηγ : η.1 ≠ 0 := by
    simp [η, commonAxisReverseTwin, hγ]
  have hηρzero : η.2.1 ⟨0, hm⟩ = 0 := by
    simp [η, commonAxisReverseTwin]
  have hηρnz : ∀ i : Fin m, i.val ≠ 0 → η.2.1 i ≠ 0 := by
    intro i hi
    simp [η, commonAxisReverseTwin, hi, hρ i hi]
  have hηρinj : Function.Injective η.2.1 := by
    intro i j hij
    by_cases hi : i.val = 0
    · have hi0 : i = ⟨0, hm⟩ := Fin.ext hi
      subst i
      by_contra hj
      have hjv : j.val ≠ 0 := fun h => hj (Fin.ext h.symm)
      exact hηρnz j hjv (hij ▸ hηρzero)
    · by_cases hj : j.val = 0
      · have hj0 : j = ⟨0, hm⟩ := Fin.ext hj
        subst j
        exact (hηρnz i hi (hij.trans hηρzero)).elim
      · apply hρinj
        have hinv := hij
        simp [η, commonAxisReverseTwin, hi, hj] at hinv
        exact hinv
  have hηγρ : ∀ i : Fin m, η.1 ≠ η.2.1 i := by
    intro i heq
    by_cases hi : i.val = 0
    · have hi0 : i = ⟨0, hm⟩ := Fin.ext hi
      subst i
      exact hηγ (heq.trans hηρzero)
    · have hinv : θ.1⁻¹ = (θ.2.1 i)⁻¹ := by
        simpa [η, commonAxisReverseTwin, hi] using heq
      exact gamma_ne_rho_of_generic hθ.1 i (inv_injective hinv)
  have hηw : ∀ (j : Fin (m + 2)) {r : ℕ}, r ∈ Finset.Icc 2 L →
      η.2.2 j r ≠ 0 := by
    intro j r hr
    have hc : θ.2.2 (commonAxisIndex m hm j) r ≠ 0 :=
      retainedWeight_ne_zero_of_generic hθ.1 _ hr
    by_cases hlast : j.val = m + 1
    · simp [η, commonAxisReverseTwin, hlast, hc, hγ]
    · by_cases htwo : 2 ≤ j.val
      · have hi : (⟨j.val - 1, by omega⟩ : Fin m).val ≠ 0 := by simp; omega
        simp [η, commonAxisReverseTwin, hlast, htwo, hc,
          hρ ⟨j.val - 1, by omega⟩ hi]
      · simp [η, commonAxisReverseTwin, hlast, htwo, hc]
  refine ⟨hband, ?_⟩
  apply mul_ne_zero
  · apply mul_ne_zero
    · exact mul_ne_zero hηγ
        (Finset.prod_ne_zero_iff.mpr (fun i _ => sub_ne_zero.mpr (hηγρ i)))
    · apply Finset.prod_ne_zero_iff.mpr
      intro i _
      apply Finset.prod_ne_zero_iff.mpr
      intro j _
      by_cases hij : i < j
      · simp only [hij, if_true]
        exact sub_ne_zero.mpr (fun h => (ne_of_lt hij) (hηρinj h))
      · simp [hij]
  · apply Finset.prod_ne_zero_iff.mpr
    intro j _
    apply Finset.prod_ne_zero_iff.mpr
    intro r hr
    exact hηw j hr

private lemma pow_mul_inv_pow_sub (x : ℂ) {r a : ℕ} (hx : x ≠ 0) (ha : a ≤ r) :
    x ^ r * x⁻¹ ^ (r - a) = x ^ a := by
  calc
    x ^ r * x⁻¹ ^ (r - a) =
        (x ^ a * x ^ (r - a)) * x⁻¹ ^ (r - a) := by
      rw [← pow_add, Nat.add_sub_of_le ha]
    _ = x ^ a * (x ^ (r - a) * x⁻¹ ^ (r - a)) := by ring
    _ = x ^ a := by
      rw [inv_pow, mul_inv_cancel₀ (pow_ne_zero _ hx), mul_one]

private lemma commonAxis_term_identity {m : ℕ} (hm : 1 ≤ m)
    {θ : ParamSpace ℂ m} (hzero : θ.2.1 ⟨0, hm⟩ = 0)
    (hγ : θ.1 ≠ 0)
    (hρ : ∀ i : Fin m, i.val ≠ 0 → θ.2.1 i ≠ 0)
    (r a : ℕ) (ha : a ≤ r) (j : Fin (m + 2)) :
    (commonAxisReverseTwin m hm θ).2.2 j r *
        (reverseLoading m (commonAxisReverseTwin m hm θ).1
          (commonAxisReverseTwin m hm θ).2.1 j).1 ^ (r - a) *
        (reverseLoading m (commonAxisReverseTwin m hm θ).1
          (commonAxisReverseTwin m hm θ).2.1 j).2 ^ a =
      θ.2.2 (commonAxisPermutation m hm j) r *
        (forwardLoading m θ.1 θ.2.1 (commonAxisPermutation m hm j)).1 ^ (r - a) *
        (forwardLoading m θ.1 θ.2.1 (commonAxisPermutation m hm j)).2 ^ a := by
  rw [commonAxisPermutation_apply]
  have hm0 : m ≠ 0 := by omega
  by_cases h0 : j.val = 0
  · have hj : j = 0 := Fin.ext h0
    rw [hj]
    simp [commonAxisReverseTwin, commonAxisIndex, reverseLoading, forwardLoading,
      hzero, hm0]
  · by_cases h1 : j.val = 1
    · have hj : j = ⟨1, by omega⟩ := Fin.ext h1
      rw [hj]
      simp [commonAxisReverseTwin, commonAxisIndex, reverseLoading, forwardLoading,
        Fin.last, hm0]
    · by_cases hlast : j.val = m + 1
      · have hj : j = Fin.last (m + 1) := Fin.ext hlast
        rw [hj]
        simp only [commonAxisReverseTwin, commonAxisIndex_last]
        simp [reverseLoading, forwardLoading, Fin.last, hm0]
        ring_nf
        rw [mul_assoc, pow_mul_inv_pow_sub θ.1 hγ ha]
      · have hj2 : 2 ≤ j.val := by omega
        have hmid : j.val < m + 1 := by omega
        have hidx0 : j.val - 1 ≠ 0 := by omega
        have hs : θ.2.1 ⟨j.val - 1, by omega⟩ ≠ 0 := hρ _ (by omega)
        rw [commonAxisIndex_mid hm j h0 h1 hlast]
        simp only [commonAxisReverseTwin]
        simp [reverseLoading, forwardLoading, h0, h1, hlast, hj2, hmid, hm0, hidx0]
        ring_nf
        rw [mul_assoc, pow_mul_inv_pow_sub _ hs ha]
        rw [commonAxisIndex_mid hm j h0 h1 hlast]
        ring

/-- Proves the stated equality or equivalence for common Axis Reverse Twin map eq. -/
lemma commonAxisReverseTwin_map_eq {m : ℕ} (hm : 1 ≤ m)
    {θ : ParamSpace ℂ m} (hzero : θ.2.1 ⟨0, hm⟩ = 0)
    (hγ : θ.1 ≠ 0)
    (hρ : ∀ i : Fin m, i.val ≠ 0 → θ.2.1 i ≠ 0) :
    reverseCumulantMap m (2 * m + 2) (commonAxisReverseTwin m hm θ) =
      forwardCumulantMap m (2 * m + 2) θ := by
  funext r a
  simp only [reverseCumulantMap, forwardCumulantMap]
  split
  · rw [← Equiv.sum_comp (commonAxisPermutation m hm)
      (fun j => θ.2.2 j r * (forwardLoading m θ.1 θ.2.1 j).1 ^ (r - a) *
        (forwardLoading m θ.1 θ.2.1 j).2 ^ a)]
    apply Finset.sum_congr rfl
    intro j _
    exact commonAxis_term_identity hm hzero hγ hρ r a (by omega) j
  · rfl

/-- Proves the stated set-containment or membership property for forward Common Axis image mem exceptional. -/
lemma forwardCommonAxis_image_mem_exceptional {m : ℕ} (hm : 1 ≤ m)
    {θ : ParamSpace ℂ m} (hθ : θ ∈ forwardCommonAxisDivisor m hm) :
    forwardCumulantMap m (2 * m + 2) θ ∈ genericFullFiberCompatibility m := by
  have hband := genericParameterLocus_bandSupported hθ.1
  have htwinband := commonAxisReverseTwin_bandSupported hm hband
  have hγ := gamma_ne_zero_of_generic hθ.1
  have hρ : ∀ i : Fin m, i.val ≠ 0 → θ.2.1 i ≠ 0 := by
    intro i hi hzeroi
    have heq : i = ⟨0, hm⟩ := rho_injective_of_generic hθ.1 (hzeroi.trans hθ.2.symm)
    exact hi (congrArg Fin.val heq)
  refine ⟨forwardCumulantMap_mem_bandSupportedCumulants m (2 * m + 2) θ,
    Or.inl ⟨⟨θ, mem_fiberCorrespondence_self hband, hθ.1⟩, ?_⟩⟩
  refine ⟨commonAxisReverseTwin m hm θ, htwinband, ?_⟩
  intro r a hr hrL ha
  exact congrFun (congrFun (commonAxisReverseTwin_map_eq hm hθ.2 hγ hρ) r) a

/-- Closure of the common-axis image divisor inside the forward arrow variety. -/
def forwardCommonAxisImageClosure (m : ℕ) (hm : 1 ≤ m) : Set (CumVec ℂ) :=
  zariskiClosure ((forwardCumulantMap m (2 * m + 2)) ''
    forwardCommonAxisDivisor m hm)

lemma forwardCommonAxisImageClosure_subset_exceptional {m : ℕ} (hm : 1 ≤ m) :
    forwardCommonAxisImageClosure m hm ⊆ genericCompatibilityClosure m := by
  apply zariskiClosure_mono
  rintro _ ⟨θ, hθ, rfl⟩
  exact forwardCommonAxis_image_mem_exceptional hm hθ

/-- The explicit common-axis image closure lies on the observable horizontal
contraction-minor hypersurface. -/
lemma forwardCommonAxisImageClosure_horizontalMinor_vanishes
    {m : ℕ} (hm : 1 ≤ m) {t : CumVec ℂ}
    (ht : t ∈ forwardCommonAxisImageClosure m hm) :
    MvPolynomial.eval (restrictCumBand (2 * m + 2) t)
      (horizontalContractionMinorPolynomial m) = 0 := by
  exact horizontalContractionMinorPolynomial_forwardCommonAxisClosure_vanishes hm ht

end

/-- The reverse twin constructed on the common-axis exceptional set is unchanged when equal
model orders, admissibility conditions, and parameter values are substituted. -/
add_decl_doc commonAxisReverseTwin.congr_simp

end CausalSmith.ExactID.EID_LingamDirectionMinOrderV1
