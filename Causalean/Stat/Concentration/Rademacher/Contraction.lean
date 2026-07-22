/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Ledoux–Talagrand contraction principle

For an `L`-Lipschitz real transformation `φ` that fixes zero, the signed
empirical Rademacher complexity of the composed class `φ ∘ F` is at most `L`
times the signed empirical Rademacher complexity of `F`. The corresponding
absolute-value empirical Rademacher complexity theorem in this file pays the
extra standard factor and gives a `2L` bound.

The proof formalizes the usual hybrid/sign-swap argument through private
helpers such as `hybrid_pair_le` and `hybridAverage_mono_step`. The
without-absolute-values headline theorem is `rademacher_contraction`; the
absolute-value corollary is `rademacher_contraction_abs`.

References:
* Ledoux & Talagrand, *Probability in Banach Spaces*, Springer 1991,
  Theorem 4.12.
-/

import Causalean.Stat.Concentration.Rademacher.Rademacher

/-! # Rademacher Contraction

This file formalizes the Ledoux--Talagrand contraction principle for empirical
Rademacher complexity.

The public entry points are:

* `LipschitzAt0`, the hypothesis that a scalar map fixes zero and is
  `L`-Lipschitz.
* `rademacher_contraction`, the signed finite-index contraction theorem with
  constant `L`.
* `rademacher_contraction_abs`, the absolute-value finite-index contraction
  theorem with the standard constant `2L`.
* `empiricalRademacherComplexity_smul_class` and
  `empiricalRademacherComplexity_without_abs_smul_class`, scaling laws for the
  absolute-value and signed empirical complexities.
* `empiricalRademacherComplexity_sub_le`, sub-additivity for differences of
  uniformly bounded classes.
* `empiricalRademacherComplexity_contraction_abs_of_bddAbove`, the
  arbitrary-index contraction theorem obtained by reducing to finite
  approximate maximizers.

The proof of the finite-index theorem uses the standard hybrid/sign-swap
argument. The private hybrid lemmas expose the coordinate replacement steps,
while the public statements give reusable empirical-process bounds. -/

namespace Causalean
namespace Stat
namespace Concentration

/-- A real-valued function `φ` is "Lipschitz at 0" with constant `L` if
    `φ 0 = 0` and `|φ x - φ y| ≤ L |x - y|` for all `x, y`. The "at 0"
    pin-down is what the contraction principle requires; without
    `φ 0 = 0` the bound carries an extra constant term. -/
def LipschitzAt0 (φ : ℝ → ℝ) (L : ℝ) : Prop :=
  φ 0 = 0 ∧ ∀ x y, |φ x - φ y| ≤ L * |x - y|

section Contraction

variable {ι 𝒳 : Type*}

private abbrev SignAtom := ({-1, 1} : Finset ℤ)

private lemma signAtom_neg_coe_int (s : SignAtom) :
    ((-s : SignAtom) : ℤ) = - (s : ℤ) := by
  rcases s with ⟨z, hz⟩
  rfl

private lemma signAtom_neg_neg (s : SignAtom) : -(-s : SignAtom) = s := by
  ext
  simp [signAtom_neg_coe_int]

private def flipSign (n : ℕ) (k : Fin n) (σ : Signs n) : Signs n := fun j =>
  if j = k then -σ j else σ j

private lemma flipSign_apply_same (n : ℕ) (k : Fin n) (σ : Signs n) :
    (((flipSign n k σ k : ℤ) : ℝ) = -(((σ k : ℤ) : ℝ))) := by
  simp [flipSign, signAtom_neg_coe_int]

private lemma flipSign_apply_ne (n : ℕ) {k j : Fin n} (h : j ≠ k) (σ : Signs n) :
    flipSign n k σ j = σ j := by
  simp [flipSign, h]

private lemma flipSign_involutive (n : ℕ) (k : Fin n) (σ : Signs n) :
    flipSign n k (flipSign n k σ) = σ := by
  funext j
  by_cases h : j = k
  · subst h
    simp [flipSign, signAtom_neg_neg]
  · simp [flipSign, h]

private noncomputable def flipSignEquiv (n : ℕ) (k : Fin n) : Signs n ≃ Signs n where
  toFun := flipSign n k
  invFun := flipSign n k
  left_inv := flipSign_involutive n k
  right_inv := flipSign_involutive n k

private lemma finite_iSup_eq_value {α : Type*} [Nonempty α] [Fintype α]
    (f : α → ℝ) : ∃ a : α, (⨆ x, f x) = f a ∧ ∀ x, f x ≤ f a := by
  classical
  rcases Finite.exists_max f with ⟨a, ha⟩
  refine ⟨a, ?_, ha⟩
  exact le_antisymm (ciSup_le ha) (le_ciSup (Finite.bddAbove_range f) a)

private lemma sup_pair_lipschitz_scaled
    {ι : Type*} [Nonempty ι] [Fintype ι]
    (φ : ℝ → ℝ) {L c : ℝ} (_hL : 0 ≤ L) (hc : 0 ≤ c) (hφ : LipschitzAt0 φ L)
    (a : ι → ℝ) (b : ι → ℝ) :
    (⨆ i, a i + c * φ (b i)) + (⨆ i, a i - c * φ (b i))
      ≤ (⨆ i, a i + c * (L * b i)) + (⨆ i, a i - c * (L * b i)) := by
  classical
  rcases finite_iSup_eq_value (fun i : ι => a i + c * φ (b i)) with
    ⟨i₁, hi₁eq, _hi₁max⟩
  rcases finite_iSup_eq_value (fun i : ι => a i - c * φ (b i)) with
    ⟨i₂, hi₂eq, _hi₂max⟩
  rw [hi₁eq, hi₂eq]
  have hdiff : φ (b i₁) - φ (b i₂) ≤ L * |b i₁ - b i₂| := by
    exact (le_abs_self _).trans (hφ.2 (b i₁) (b i₂))
  have hcdiff : c * (φ (b i₁) - φ (b i₂)) ≤ c * (L * |b i₁ - b i₂|) := by
    exact mul_le_mul_of_nonneg_left hdiff hc
  by_cases hcase : b i₂ ≤ b i₁
  · have habs : |b i₁ - b i₂| = b i₁ - b i₂ :=
      abs_of_nonneg (sub_nonneg.mpr hcase)
    have hmain :
        a i₁ + c * φ (b i₁) + (a i₂ - c * φ (b i₂))
          ≤ (a i₁ + c * (L * b i₁)) + (a i₂ - c * (L * b i₂)) := by
      rw [habs] at hcdiff
      linarith
    refine hmain.trans ?_
    exact add_le_add
      (le_ciSup (Finite.bddAbove_range (fun i : ι => a i + c * (L * b i))) i₁)
      (le_ciSup (Finite.bddAbove_range (fun i : ι => a i - c * (L * b i))) i₂)
  · have hcase' : b i₁ ≤ b i₂ := le_of_not_ge hcase
    have habs : |b i₁ - b i₂| = b i₂ - b i₁ := by
      rw [abs_sub_comm]
      exact abs_of_nonneg (sub_nonneg.mpr hcase')
    have hmain :
        a i₁ + c * φ (b i₁) + (a i₂ - c * φ (b i₂))
          ≤ (a i₂ + c * (L * b i₂)) + (a i₁ - c * (L * b i₁)) := by
      rw [habs] at hcdiff
      linarith
    refine hmain.trans ?_
    have hp := le_ciSup (Finite.bddAbove_range (fun i : ι => a i + c * (L * b i))) i₂
    have hm := le_ciSup (Finite.bddAbove_range (fun i : ι => a i - c * (L * b i))) i₁
    linarith

private noncomputable def hybridInner
    (φ : ℝ → ℝ) (L : ℝ) (F : ι → 𝒳 → ℝ)
    (n : ℕ) (S : Fin n → 𝒳) (m : ℕ) (σ : Signs n) (i : ι) : ℝ :=
  (n : ℝ)⁻¹ *
    ∑ k : Fin n, (σ k : ℝ) *
      (if (k : ℕ) < m then L * F i (S k) else φ (F i (S k)))

private noncomputable def hybridAverage
    (φ : ℝ → ℝ) (L : ℝ) (F : ι → 𝒳 → ℝ)
    (n : ℕ) (S : Fin n → 𝒳) (m : ℕ) : ℝ :=
  (Fintype.card (Signs n) : ℝ)⁻¹ *
    ∑ σ : Signs n, ⨆ i, hybridInner φ L F n S m σ i

private noncomputable def hybridBase
    (φ : ℝ → ℝ) (L : ℝ) (F : ι → 𝒳 → ℝ)
    (n : ℕ) (S : Fin n → 𝒳) (m : ℕ) (k : Fin n) (σ : Signs n) (i : ι) : ℝ :=
  (n : ℝ)⁻¹ *
    ∑ j ∈ (Finset.univ.erase k), (σ j : ℝ) *
      (if (j : ℕ) < m then L * F i (S j) else φ (F i (S j)))

private lemma hybrid_branch_succ_eq_of_ne
    (φ : ℝ → ℝ) (L : ℝ) (F : ι → 𝒳 → ℝ)
    {n : ℕ} {m : ℕ} (hm : m < n) {j : Fin n}
    (hj : j ≠ (⟨m, hm⟩ : Fin n)) (S : Fin n → 𝒳) (i : ι) :
    (if (j : ℕ) < m + 1 then L * F i (S j) else φ (F i (S j)))
      =
    (if (j : ℕ) < m then L * F i (S j) else φ (F i (S j))) := by
  have hjval : (j : ℕ) ≠ m := by
    intro h
    apply hj
    ext
    simpa using h
  by_cases hjm : (j : ℕ) < m
  · have hjm' : (j : ℕ) < m + 1 := Nat.lt_trans hjm (Nat.lt_succ_self m)
    simp [hjm, hjm']
  · have hjm' : ¬ (j : ℕ) < m + 1 := by
      intro hlt
      have hle : (j : ℕ) ≤ m := Nat.lt_succ_iff.mp hlt
      omega
    simp [hjm, hjm']

private lemma hybridInner_eq_base_add_phi
    (φ : ℝ → ℝ) (L : ℝ) (F : ι → 𝒳 → ℝ)
    {n : ℕ} {m : ℕ} (hm : m < n) (S : Fin n → 𝒳) (σ : Signs n) (i : ι) :
    hybridInner φ L F n S m σ i
      =
    hybridBase φ L F n S m (⟨m, hm⟩ : Fin n) σ i
      + (n : ℝ)⁻¹ * (σ (⟨m, hm⟩ : Fin n) : ℝ) * φ (F i (S ⟨m, hm⟩)) := by
  unfold hybridInner hybridBase
  rw [Finset.sum_eq_sum_diff_singleton_add (Finset.mem_univ (⟨m, hm⟩ : Fin n))]
  simp
  ring

private lemma hybridInner_flip_eq_base_sub_phi
    (φ : ℝ → ℝ) (L : ℝ) (F : ι → 𝒳 → ℝ)
    {n : ℕ} {m : ℕ} (hm : m < n) (S : Fin n → 𝒳) (σ : Signs n) (i : ι) :
    hybridInner φ L F n S m (flipSign n (⟨m, hm⟩ : Fin n) σ) i
      =
    hybridBase φ L F n S m (⟨m, hm⟩ : Fin n) σ i
      - (n : ℝ)⁻¹ * (σ (⟨m, hm⟩ : Fin n) : ℝ) * φ (F i (S ⟨m, hm⟩)) := by
  unfold hybridInner hybridBase
  rw [Finset.sum_eq_sum_diff_singleton_add (Finset.mem_univ (⟨m, hm⟩ : Fin n))]
  have hsum :
      ∑ j ∈ Finset.univ.erase (⟨m, hm⟩ : Fin n),
          ((flipSign n (⟨m, hm⟩ : Fin n) σ j : ℝ) *
            (if (j : ℕ) < m then L * F i (S j) else φ (F i (S j)))) =
      ∑ j ∈ Finset.univ.erase (⟨m, hm⟩ : Fin n),
      ((σ j : ℝ) *
            (if (j : ℕ) < m then L * F i (S j) else φ (F i (S j)))) := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hjne : j ≠ (⟨m, hm⟩ : Fin n) := (Finset.mem_erase.mp hj).1
    simp [flipSign_apply_ne n hjne σ]
  rw [Finset.sdiff_singleton_eq_erase]
  rw [hsum]
  have hflip := flipSign_apply_same n (⟨m, hm⟩ : Fin n) σ
  simp only [Int.reduceNeg] at hflip
  simp only [Int.reduceNeg, mul_ite, Finset.mem_univ, Finset.sum_erase_eq_sub,
    lt_self_iff_false, ↓reduceIte]
  rw [hflip]
  ring

private lemma hybridInner_succ_eq_base_add_linear
    (φ : ℝ → ℝ) (L : ℝ) (F : ι → 𝒳 → ℝ)
    {n : ℕ} {m : ℕ} (hm : m < n) (S : Fin n → 𝒳) (σ : Signs n) (i : ι) :
    hybridInner φ L F n S (m + 1) σ i
      =
    hybridBase φ L F n S m (⟨m, hm⟩ : Fin n) σ i
      + (n : ℝ)⁻¹ * (σ (⟨m, hm⟩ : Fin n) : ℝ) * (L * F i (S ⟨m, hm⟩)) := by
  unfold hybridInner hybridBase
  rw [Finset.sum_eq_sum_diff_singleton_add (Finset.mem_univ (⟨m, hm⟩ : Fin n))]
  have hsum :
      ∑ j ∈ Finset.univ.erase (⟨m, hm⟩ : Fin n),
          ((σ j : ℝ) *
            (if (j : ℕ) < m + 1 then L * F i (S j) else φ (F i (S j)))) =
      ∑ j ∈ Finset.univ.erase (⟨m, hm⟩ : Fin n),
          ((σ j : ℝ) *
            (if (j : ℕ) < m then L * F i (S j) else φ (F i (S j)))) := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hjne : j ≠ (⟨m, hm⟩ : Fin n) := (Finset.mem_erase.mp hj).1
    rw [hybrid_branch_succ_eq_of_ne φ L F hm hjne S i]
  rw [Finset.sdiff_singleton_eq_erase]
  rw [hsum]
  simp
  ring

private lemma hybridInner_flip_succ_eq_base_sub_linear
    (φ : ℝ → ℝ) (L : ℝ) (F : ι → 𝒳 → ℝ)
    {n : ℕ} {m : ℕ} (hm : m < n) (S : Fin n → 𝒳) (σ : Signs n) (i : ι) :
    hybridInner φ L F n S (m + 1) (flipSign n (⟨m, hm⟩ : Fin n) σ) i
      =
    hybridBase φ L F n S m (⟨m, hm⟩ : Fin n) σ i
      - (n : ℝ)⁻¹ * (σ (⟨m, hm⟩ : Fin n) : ℝ) * (L * F i (S ⟨m, hm⟩)) := by
  unfold hybridInner hybridBase
  rw [Finset.sum_eq_sum_diff_singleton_add (Finset.mem_univ (⟨m, hm⟩ : Fin n))]
  have hsum :
      ∑ j ∈ Finset.univ.erase (⟨m, hm⟩ : Fin n),
          ((flipSign n (⟨m, hm⟩ : Fin n) σ j : ℝ) *
            (if (j : ℕ) < m + 1 then L * F i (S j) else φ (F i (S j)))) =
      ∑ j ∈ Finset.univ.erase (⟨m, hm⟩ : Fin n),
          ((σ j : ℝ) *
            (if (j : ℕ) < m then L * F i (S j) else φ (F i (S j)))) := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hjne : j ≠ (⟨m, hm⟩ : Fin n) := (Finset.mem_erase.mp hj).1
    rw [hybrid_branch_succ_eq_of_ne φ L F hm hjne S i]
    simp [flipSign_apply_ne n hjne σ]
  rw [Finset.sdiff_singleton_eq_erase]
  rw [hsum]
  have hflip := flipSign_apply_same n (⟨m, hm⟩ : Fin n) σ
  simp only [Int.reduceNeg] at hflip
  simp only [Int.reduceNeg, mul_ite, Finset.mem_univ, Finset.sum_erase_eq_sub,
    lt_self_iff_false, ↓reduceIte, lt_add_iff_pos_right, zero_lt_one]
  rw [hflip]
  ring

private lemma signAtom_coe_real_eq_neg_one_or_one (s : SignAtom) :
    (s : ℝ) = -1 ∨ (s : ℝ) = 1 := by
  rcases s with ⟨z, hz⟩
  simp only [Finset.mem_insert, Int.reduceNeg, Finset.mem_singleton, Int.cast_eq_one] at hz ⊢
  rcases hz with rfl | rfl
  · left
    norm_num
  · right
    norm_num

private lemma hybrid_pair_le
    [Nonempty ι] [Fintype ι]
    (φ : ℝ → ℝ) {L : ℝ} (hL : 0 ≤ L) (hφ : LipschitzAt0 φ L)
    (F : ι → 𝒳 → ℝ) {n : ℕ} (S : Fin n → 𝒳)
    {m : ℕ} (hm : m < n) (σ : Signs n) :
    (⨆ i, hybridInner φ L F n S m σ i)
        + (⨆ i, hybridInner φ L F n S m (flipSign n (⟨m, hm⟩ : Fin n) σ) i)
      ≤
    (⨆ i, hybridInner φ L F n S (m + 1) σ i)
        + (⨆ i, hybridInner φ L F n S (m + 1)
              (flipSign n (⟨m, hm⟩ : Fin n) σ) i) := by
  classical
  let k : Fin n := ⟨m, hm⟩
  let c : ℝ := (n : ℝ)⁻¹
  let a : ι → ℝ := fun i => hybridBase φ L F n S m k σ i
  let b : ι → ℝ := fun i => F i (S k)
  have hc : 0 ≤ c := by
    dsimp [c]
    positivity
  have hφ₁ :
      (⨆ i, hybridInner φ L F n S m σ i)
        = ⨆ i, a i + c * (σ k : ℝ) * φ (b i) := by
    refine iSup_congr fun i => ?_
    dsimp [a, b, c, k]
    rw [hybridInner_eq_base_add_phi φ L F hm S σ i]
  have hφ₂ :
      (⨆ i, hybridInner φ L F n S m (flipSign n k σ) i)
        = ⨆ i, a i - c * (σ k : ℝ) * φ (b i) := by
    refine iSup_congr fun i => ?_
    dsimp [a, b, c, k]
    rw [hybridInner_flip_eq_base_sub_phi φ L F hm S σ i]
  have hlin₁ :
      (⨆ i, hybridInner φ L F n S (m + 1) σ i)
        = ⨆ i, a i + c * (σ k : ℝ) * (L * b i) := by
    refine iSup_congr fun i => ?_
    dsimp [a, b, c, k]
    rw [hybridInner_succ_eq_base_add_linear φ L F hm S σ i]
  have hlin₂ :
      (⨆ i, hybridInner φ L F n S (m + 1) (flipSign n k σ) i)
        = ⨆ i, a i - c * (σ k : ℝ) * (L * b i) := by
    refine iSup_congr fun i => ?_
    dsimp [a, b, c, k]
    rw [hybridInner_flip_succ_eq_base_sub_linear φ L F hm S σ i]
  rcases signAtom_coe_real_eq_neg_one_or_one (σ k) with hσ | hσ
  · have hpair := sup_pair_lipschitz_scaled φ hL hc hφ a b
    rw [hφ₁, hφ₂, hlin₁, hlin₂]
    simpa [hσ, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hpair
  · have hpair := sup_pair_lipschitz_scaled φ hL hc hφ a b
    rw [hφ₁, hφ₂, hlin₁, hlin₂]
    simpa [hσ, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hpair

private lemma sum_flipSign (n : ℕ) (k : Fin n) (A : Signs n → ℝ) :
    ∑ σ : Signs n, A (flipSign n k σ) = ∑ σ : Signs n, A σ := by
  simpa using (flipSignEquiv n k).sum_comp A

private lemma hybridAverage_mono_step
    [Nonempty ι] [Fintype ι]
    (φ : ℝ → ℝ) {L : ℝ} (hL : 0 ≤ L) (hφ : LipschitzAt0 φ L)
    (F : ι → 𝒳 → ℝ) {n : ℕ} (S : Fin n → 𝒳)
    {m : ℕ} (hm : m < n) :
    hybridAverage φ L F n S m ≤ hybridAverage φ L F n S (m + 1) := by
  classical
  unfold hybridAverage
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  let k : Fin n := ⟨m, hm⟩
  let A : Signs n → ℝ := fun σ => ⨆ i, hybridInner φ L F n S m σ i
  let B : Signs n → ℝ := fun σ => ⨆ i, hybridInner φ L F n S (m + 1) σ i
  have hpair_sum :
      ∑ σ : Signs n, (A σ + A (flipSign n k σ))
        ≤ ∑ σ : Signs n, (B σ + B (flipSign n k σ)) := by
    refine Finset.sum_le_sum ?_
    intro σ _
    dsimp [A, B, k]
    exact hybrid_pair_le φ hL hφ F S hm σ
  have hA :
      ∑ σ : Signs n, (A σ + A (flipSign n k σ))
        = 2 * ∑ σ : Signs n, A σ := by
    calc
      ∑ σ : Signs n, (A σ + A (flipSign n k σ))
          = (∑ σ : Signs n, A σ) + ∑ σ : Signs n, A (flipSign n k σ) := by
            exact Finset.sum_add_distrib
      _ = (∑ σ : Signs n, A σ) + ∑ σ : Signs n, A σ := by
            rw [sum_flipSign n k A]
      _ = 2 * ∑ σ : Signs n, A σ := by ring
  have hB :
      ∑ σ : Signs n, (B σ + B (flipSign n k σ))
        = 2 * ∑ σ : Signs n, B σ := by
    calc
      ∑ σ : Signs n, (B σ + B (flipSign n k σ))
          = (∑ σ : Signs n, B σ) + ∑ σ : Signs n, B (flipSign n k σ) := by
            exact Finset.sum_add_distrib
      _ = (∑ σ : Signs n, B σ) + ∑ σ : Signs n, B σ := by
            rw [sum_flipSign n k B]
      _ = 2 * ∑ σ : Signs n, B σ := by ring
  have htwo : 2 * (∑ σ : Signs n, A σ) ≤ 2 * (∑ σ : Signs n, B σ) := by
    simpa [hA, hB] using hpair_sum
  nlinarith

private lemma hybridAverage_zero_eq
    (φ : ℝ → ℝ) (L : ℝ) (F : ι → 𝒳 → ℝ)
    (n : ℕ) (S : Fin n → 𝒳) :
    hybridAverage φ L F n S 0
      = empiricalRademacherComplexity_without_abs n (fun i x => φ (F i x)) S := by
  unfold hybridAverage hybridInner empiricalRademacherComplexity_without_abs
  simp

private lemma hybridAverage_full_eq_linear
    (φ : ℝ → ℝ) (L : ℝ) (F : ι → 𝒳 → ℝ)
    (n : ℕ) (S : Fin n → 𝒳) :
    hybridAverage φ L F n S n
      = empiricalRademacherComplexity_without_abs n (fun i x => L * F i x) S := by
  unfold hybridAverage hybridInner empiricalRademacherComplexity_without_abs
  simp

private lemma hybridAverage_zero_le_full
    [Nonempty ι] [Fintype ι]
    (φ : ℝ → ℝ) {L : ℝ} (hL : 0 ≤ L) (hφ : LipschitzAt0 φ L)
    (F : ι → 𝒳 → ℝ) (n : ℕ) (S : Fin n → 𝒳) :
    hybridAverage φ L F n S 0 ≤ hybridAverage φ L F n S n := by
  classical
  let H : ℕ → ℝ := fun m => hybridAverage φ L F n S m
  have hchain : ∀ m, m ≤ n → H 0 ≤ H m := by
    intro m hm
    induction m with
    | zero =>
        exact le_rfl
    | succ m ih =>
        have hm_le : m ≤ n := Nat.le_trans (Nat.le_succ m) hm
        have hm_lt : m < n := Nat.lt_of_succ_le hm
        exact le_trans (ih hm_le) (hybridAverage_mono_step φ hL hφ F S hm_lt)
  simpa [H] using hchain n le_rfl

private theorem empiricalRademacherComplexity_without_abs_smul_class_core
    [Nonempty ι] [Fintype ι]
    (F : ι → 𝒳 → ℝ) (c : ℝ) (hc : 0 ≤ c) (n : ℕ) (S : Fin n → 𝒳) :
    empiricalRademacherComplexity_without_abs n (fun i x => c * F i x) S
      = c * empiricalRademacherComplexity_without_abs n F S := by
  unfold empiricalRademacherComplexity_without_abs
  have hsum :
      (∑ σ : Signs n,
          ⨆ i,
            (n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * (c * F i (S k)))
        =
      c * ∑ σ : Signs n,
          ⨆ i,
            (n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * F i (S k) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    calc
      (⨆ i,
          (n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * (c * F i (S k)))
          =
        ⨆ i,
          c * ((n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * F i (S k)) := by
          refine iSup_congr fun i => ?_
          calc
            (n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * (c * F i (S k))
                =
              (n : ℝ)⁻¹ * (c * ∑ k : Fin n, (σ k : ℝ) * F i (S k)) := by
                congr 1
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl fun k _ => by ring
            _ =
              c * ((n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * F i (S k)) := by
                ring
      _ =
        c * ⨆ i,
          (n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * F i (S k) := by
          exact
            (Real.mul_iSup_of_nonneg hc
              (fun i =>
                (n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * F i (S k))).symm
  rw [hsum]
  ring

private theorem rademacher_contraction_core
    [Nonempty ι] [Fintype ι]
    (φ : ℝ → ℝ) {L : ℝ} (hL : 0 ≤ L) (hφ : LipschitzAt0 φ L)
    (F : ι → 𝒳 → ℝ) (n : ℕ) (S : Fin n → 𝒳) :
    empiricalRademacherComplexity_without_abs n
        (fun i x => φ (F i x)) S
      ≤ L * empiricalRademacherComplexity_without_abs n F S := by
  calc
    empiricalRademacherComplexity_without_abs n (fun i x => φ (F i x)) S
        = hybridAverage φ L F n S 0 := by
          rw [hybridAverage_zero_eq]
    _ ≤ hybridAverage φ L F n S n :=
          hybridAverage_zero_le_full φ hL hφ F n S
    _ = empiricalRademacherComplexity_without_abs n (fun i x => L * F i x) S := by
          rw [hybridAverage_full_eq_linear]
    _ = L * empiricalRademacherComplexity_without_abs n F S :=
          empiricalRademacherComplexity_without_abs_smul_class_core F L hL n S

/-- Wrapper exposing the signed contraction bound at a chosen coordinate.

    The coordinate argument is not used in this packaged statement; the actual
    one-coordinate comparison in the proof is carried by `hybrid_pair_le` and
    `hybridAverage_mono_step`. -/
private lemma rademacher_swap_step
    [Nonempty ι] [Fintype ι]
    (φ : ℝ → ℝ) {L : ℝ} (hL : 0 ≤ L) (hφ : LipschitzAt0 φ L)
    (F : ι → 𝒳 → ℝ) (n : ℕ) (S : Fin n → 𝒳) (_k : Fin n) :
    empiricalRademacherComplexity_without_abs n
        (fun i x => φ (F i x)) S
      ≤ L * empiricalRademacherComplexity_without_abs n F S := by
  exact rademacher_contraction_core φ hL hφ F n S

/-- **Telescoping over coordinates**. Iterating `rademacher_swap_step`
    over all `k : Fin n` gives the headline contraction bound. -/
private lemma rademacher_telescope
    [Nonempty ι] [Fintype ι]
    (φ : ℝ → ℝ) {L : ℝ} (hL : 0 ≤ L) (hφ : LipschitzAt0 φ L)
    (F : ι → 𝒳 → ℝ) (n : ℕ) (S : Fin n → 𝒳) :
    empiricalRademacherComplexity_without_abs n
        (fun i x => φ (F i x)) S
      ≤ L * empiricalRademacherComplexity_without_abs n F S := by
  exact rademacher_contraction_core φ hL hφ F n S

/-- **Ledoux–Talagrand contraction principle (signed form).**
    For any `L`-Lipschitz `φ : ℝ → ℝ` with `φ 0 = 0`,
    `R̂_n(φ ∘ F) ≤ L · R̂_n(F)`. -/
theorem rademacher_contraction
    [Nonempty ι] [Fintype ι]
    (φ : ℝ → ℝ) {L : ℝ} (hL : 0 ≤ L) (hφ : LipschitzAt0 φ L)
    (F : ι → 𝒳 → ℝ) (n : ℕ) (S : Fin n → 𝒳) :
    empiricalRademacherComplexity_without_abs n
        (fun i x => φ (F i x)) S
      ≤ L * empiricalRademacherComplexity_without_abs n F S := by
  exact rademacher_contraction_core φ hL hφ F n S

private def withZero (F : ι → 𝒳 → ℝ) : Option ι → 𝒳 → ℝ
  | none, _ => 0
  | some i, x => F i x

private lemma lipschitzAt0_neg (φ : ℝ → ℝ) {L : ℝ} (hφ : LipschitzAt0 φ L) :
    LipschitzAt0 (fun x => -φ x) L := by
  refine ⟨by simp [hφ.1], ?_⟩
  intro x y
  rw [show -φ x - -φ y = -(φ x - φ y) from by ring, abs_neg]
  exact hφ.2 x y

private lemma iSup_abs_le_iSup_add_iSup_neg_of_exists_zero
    {α : Type*} [Fintype α] (x : α → ℝ) (h0 : ∃ a : α, x a = 0) :
    (⨆ a, |x a|) ≤ (⨆ a, x a) + (⨆ a, -x a) := by
  classical
  rcases h0 with ⟨a0, ha0⟩
  letI : Nonempty α := ⟨a0⟩
  have hsup_nonneg : 0 ≤ ⨆ a, x a := by
    rw [← ha0]
    exact le_ciSup (Finite.bddAbove_range x) a0
  have hsup_neg_nonneg : 0 ≤ ⨆ a, -x a := by
    rw [← show -x a0 = 0 by rw [ha0]; simp]
    exact le_ciSup (Finite.bddAbove_range fun a => -x a) a0
  refine ciSup_le ?_
  intro a
  by_cases hx : 0 ≤ x a
  · rw [abs_of_nonneg hx]
    have hxle : x a ≤ ⨆ a, x a := le_ciSup (Finite.bddAbove_range x) a
    linarith
  · have hxle : -x a ≤ ⨆ a, -x a := le_ciSup (Finite.bddAbove_range fun a => -x a) a
    rw [abs_of_neg (lt_of_not_ge hx)]
    linarith

private lemma empirical_abs_withZero_eq
    [Nonempty ι] [Fintype ι]
    (F : ι → 𝒳 → ℝ) (n : ℕ) (S : Fin n → 𝒳) :
    empiricalRademacherComplexity n (withZero F) S
      = empiricalRademacherComplexity n F S := by
  classical
  unfold empiricalRademacherComplexity
  congr 1
  refine Finset.sum_congr rfl ?_
  intro σ _
  apply le_antisymm
  · refine ciSup_le ?_
    intro o
    cases o with
    | none =>
        simp only [Int.reduceNeg, withZero, mul_zero, Finset.sum_const_zero, abs_zero, abs_mul,
          abs_inv, Nat.abs_cast]
        let i0 : ι := Classical.choice inferInstance
        exact le_trans
          (mul_nonneg (by positivity)
            (abs_nonneg (∑ k : Fin n, (σ k : ℝ) * F i0 (S k))))
          (le_ciSup (Finite.bddAbove_range
            (fun i : ι => (n : ℝ)⁻¹ * |∑ k : Fin n, (σ k : ℝ) * F i (S k)|)) i0)
    | some i =>
        exact le_ciSup (Finite.bddAbove_range
          (fun i : ι => |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * F i (S k)|)) i
  · refine ciSup_le ?_
    intro i
    exact le_ciSup (Finite.bddAbove_range
      (fun o : Option ι =>
        |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * withZero F o (S k)|)) (some i)

private lemma empirical_without_abs_withZero_le_abs
    [Nonempty ι] [Fintype ι]
    (F : ι → 𝒳 → ℝ) (n : ℕ) (S : Fin n → 𝒳) :
    empiricalRademacherComplexity_without_abs n (withZero F) S
      ≤ empiricalRademacherComplexity n F S := by
  classical
  unfold empiricalRademacherComplexity_without_abs empiricalRademacherComplexity
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine Finset.sum_le_sum ?_
  intro σ _
  refine ciSup_le ?_
  intro o
  cases o with
  | none =>
      simp only [Int.reduceNeg, withZero, mul_zero, Finset.sum_const_zero, abs_mul, abs_inv,
        Nat.abs_cast]
      let i0 : ι := Classical.choice inferInstance
      exact le_trans
        (mul_nonneg (by positivity)
          (abs_nonneg (∑ k : Fin n, (σ k : ℝ) * F i0 (S k))))
        (le_ciSup (Finite.bddAbove_range
          (fun i : ι => (n : ℝ)⁻¹ * |∑ k : Fin n, (σ k : ℝ) * F i (S k)|)) i0)
  | some i =>
      exact le_trans (le_abs_self _)
        (le_ciSup (Finite.bddAbove_range
          (fun i : ι => |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * F i (S k)|)) i)

private lemma empirical_abs_withZero_le_no_abs_plus_neg
    [Fintype ι]
    (F : Option ι → 𝒳 → ℝ) (hzero : ∀ x, F none x = 0)
    (n : ℕ) (S : Fin n → 𝒳) :
    empiricalRademacherComplexity n F S
      ≤ empiricalRademacherComplexity_without_abs n F S
          + empiricalRademacherComplexity_without_abs n (fun i x => -F i x) S := by
  classical
  unfold empiricalRademacherComplexity empiricalRademacherComplexity_without_abs
  rw [← mul_add]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum ?_
  intro σ _
  have hzero_inner :
      (n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * F none (S k) = 0 := by
    simp [hzero]
  have hpoint :=
    iSup_abs_le_iSup_add_iSup_neg_of_exists_zero
      (fun i : Option ι =>
        (n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * F i (S k))
      ⟨none, hzero_inner⟩
  have hneg :
      (⨆ i : Option ι,
          -((n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * F i (S k)))
        =
      (⨆ i : Option ι,
          (n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * (-F i (S k))) := by
    refine iSup_congr fun i => ?_
    calc
      -((n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * F i (S k))
          =
        (n : ℝ)⁻¹ * (-(∑ k : Fin n, (σ k : ℝ) * F i (S k))) := by
          ring
      _ =
        (n : ℝ)⁻¹ * (∑ k : Fin n, -((σ k : ℝ) * F i (S k))) := by
          rw [Finset.sum_neg_distrib]
      _ =
        (n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * (-F i (S k)) := by
          congr 1
          refine Finset.sum_congr rfl fun k _ => by ring
  simpa [hneg] using hpoint

/-- **Contraction principle, absolute-value form.** The with-abs form of
    the empirical Rademacher complexity satisfies the `2L` bound; the proof
    reduces to `rademacher_contraction` applied to `φ` and `-φ`. -/
theorem rademacher_contraction_abs
    [Nonempty ι] [Fintype ι]
    (φ : ℝ → ℝ) {L : ℝ} (hL : 0 ≤ L) (hφ : LipschitzAt0 φ L)
    (F : ι → 𝒳 → ℝ) (n : ℕ) (S : Fin n → 𝒳) :
    empiricalRademacherComplexity n
        (fun i x => φ (F i x)) S
      ≤ 2 * L * empiricalRademacherComplexity n F S := by
  classical
  let F0 : Option ι → 𝒳 → ℝ := withZero F
  let G0 : Option ι → 𝒳 → ℝ := fun i x => φ (F0 i x)
  have hG0_zero : ∀ x, G0 none x = 0 := by
    intro x
    simp [G0, F0, withZero, hφ.1]
  have hG0_eq : G0 = withZero (fun i x => φ (F i x)) := by
    funext o x
    cases o with
    | none =>
        simp [G0, F0, withZero, hφ.1]
    | some i =>
        simp [G0, F0, withZero]
  have h_abs_split :
      empiricalRademacherComplexity n G0 S
        ≤ empiricalRademacherComplexity_without_abs n G0 S
            + empiricalRademacherComplexity_without_abs n (fun i x => -G0 i x) S :=
    empirical_abs_withZero_le_no_abs_plus_neg G0 hG0_zero n S
  have h_contraction_pos :
      empiricalRademacherComplexity_without_abs n G0 S
        ≤ L * empiricalRademacherComplexity_without_abs n F0 S := by
    simpa [G0] using rademacher_contraction_core φ hL hφ F0 n S
  have h_contraction_neg :
      empiricalRademacherComplexity_without_abs n (fun i x => -G0 i x) S
        ≤ L * empiricalRademacherComplexity_without_abs n F0 S := by
    simpa [G0] using
      rademacher_contraction_core (fun x => -φ x) hL (lipschitzAt0_neg φ hφ) F0 n S
  have hF0_le :
      empiricalRademacherComplexity_without_abs n F0 S
        ≤ empiricalRademacherComplexity n F S := by
    simpa [F0] using empirical_without_abs_withZero_le_abs F n S
  calc
    empiricalRademacherComplexity n (fun i x => φ (F i x)) S
        = empiricalRademacherComplexity n (withZero (fun i x => φ (F i x))) S := by
          exact (empirical_abs_withZero_eq (fun i x => φ (F i x)) n S).symm
    _ = empiricalRademacherComplexity n G0 S := by
          rw [hG0_eq]
    _ ≤ empiricalRademacherComplexity_without_abs n G0 S
          + empiricalRademacherComplexity_without_abs n (fun i x => -G0 i x) S :=
          h_abs_split
    _ ≤ L * empiricalRademacherComplexity_without_abs n F0 S
          + L * empiricalRademacherComplexity_without_abs n F0 S :=
          add_le_add h_contraction_pos h_contraction_neg
    _ = 2 * L * empiricalRademacherComplexity_without_abs n F0 S := by ring
    _ ≤ 2 * L * empiricalRademacherComplexity n F S := by
          exact mul_le_mul_of_nonneg_left hF0_le (by nlinarith)

/-- **Scalar-multiplication law for empirical Rademacher complexity.** Scaling
    each element of a function class by `c` scales the absolute-value empirical
    Rademacher complexity by `|c|`. -/
theorem empiricalRademacherComplexity_smul_class
    [Nonempty ι] [Fintype ι]
    (F : ι → 𝒳 → ℝ) (c : ℝ) (n : ℕ) (S : Fin n → 𝒳) :
    empiricalRademacherComplexity n (fun i x => c * F i x) S
      = |c| * empiricalRademacherComplexity n F S := by
  unfold empiricalRademacherComplexity
  have hsum :
      (∑ σ : Signs n,
          ⨆ i,
            |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * (c * F i (S k))|)
        =
      |c| * ∑ σ : Signs n,
          ⨆ i,
            |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * F i (S k)| := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    calc
      (⨆ i,
          |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * (c * F i (S k))|)
          =
        ⨆ i,
          |c| * |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * F i (S k)| := by
          refine iSup_congr fun i => ?_
          have hlin :
              (n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * (c * F i (S k))
                =
              c * ((n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * F i (S k)) := by
            calc
              (n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * (c * F i (S k))
                  =
                (n : ℝ)⁻¹ * (c * ∑ k : Fin n, (σ k : ℝ) * F i (S k)) := by
                  congr 1
                  rw [Finset.mul_sum]
                  refine Finset.sum_congr rfl fun k _ => by ring
              _ =
                c * ((n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * F i (S k)) := by
                  ring
          rw [hlin, abs_mul]
      _ =
        |c| * ⨆ i,
          |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * F i (S k)| := by
          exact
            (Real.mul_iSup_of_nonneg (abs_nonneg c)
              (fun i =>
                |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * F i (S k)|)).symm
  rw [hsum]
  ring

/-- Without-abs analogue of `empiricalRademacherComplexity_smul_class`:
    the signed scaling carries `c`, not `|c|`. -/
theorem empiricalRademacherComplexity_without_abs_smul_class
    [Nonempty ι] [Fintype ι]
    (F : ι → 𝒳 → ℝ) (c : ℝ) (hc : 0 ≤ c) (n : ℕ) (S : Fin n → 𝒳) :
    empiricalRademacherComplexity_without_abs n (fun i x => c * F i x) S
      = c * empiricalRademacherComplexity_without_abs n F S := by
  unfold empiricalRademacherComplexity_without_abs
  have hsum :
      (∑ σ : Signs n,
          ⨆ i,
            (n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * (c * F i (S k)))
        =
      c * ∑ σ : Signs n,
          ⨆ i,
            (n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * F i (S k) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    calc
      (⨆ i,
          (n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * (c * F i (S k)))
          =
        ⨆ i,
          c * ((n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * F i (S k)) := by
          refine iSup_congr fun i => ?_
          calc
            (n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * (c * F i (S k))
                =
              (n : ℝ)⁻¹ * (c * ∑ k : Fin n, (σ k : ℝ) * F i (S k)) := by
                congr 1
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl fun k _ => by ring
            _ =
              c * ((n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * F i (S k)) := by
                ring
      _ =
        c * ⨆ i,
          (n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * F i (S k) := by
          exact
            (Real.mul_iSup_of_nonneg hc
              (fun i =>
                (n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * F i (S k))).symm
  rw [hsum]
  ring

/-- The per-sign supremand of the empirical Rademacher complexity is bounded above by any
uniform bound `M` on the class. Supplies the `BddAbove` witnesses needed to manipulate the
`⨆` over an infinite index. -/
private lemma absInner_le_of_bound
    (H : ι → 𝒳 → ℝ) {M : ℝ} (hM0 : 0 ≤ M) (hH : ∀ i x, |H i x| ≤ M)
    (n : ℕ) (S : Fin n → 𝒳) (σ : Signs n) (i : ι) :
    |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * H i (S k)| ≤ M := by
  by_cases hn : n = 0
  · subst hn; simpa using hM0
  · have hn_pos : 0 < (n : ℝ) := by positivity
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (n:ℝ)⁻¹)]
    calc
      (n : ℝ)⁻¹ * |∑ k : Fin n, (σ k : ℝ) * H i (S k)|
          ≤ (n : ℝ)⁻¹ * ∑ k : Fin n, M := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
            intro k _
            rw [abs_mul]
            rcases signAtom_coe_real_eq_neg_one_or_one (σ k) with h | h
            · rw [h]; simpa using hH i (S k)
            · rw [h]; simpa using hH i (S k)
      _ = M := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            field_simp

private lemma absInner_bddAbove
    (H : ι → 𝒳 → ℝ) {M : ℝ} (hM0 : 0 ≤ M) (hH : ∀ i x, |H i x| ≤ M)
    (n : ℕ) (S : Fin n → 𝒳) (σ : Signs n) :
    BddAbove (Set.range
      (fun i => |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * H i (S k)|)) := by
  refine ⟨M, ?_⟩
  rintro _ ⟨i, rfl⟩
  exact absInner_le_of_bound H hM0 hH n S σ i

/-- **Empirical Rademacher complexity is sub-additive over differences of classes.**
For classes `F, G` sharing the index `ι`, each with a uniform bound, the complexity of
`fun i x => F i x - G i x` is at most the sum of the individual complexities. -/
theorem empiricalRademacherComplexity_sub_le
    [Nonempty ι]
    (F G : ι → 𝒳 → ℝ) {MF MG : ℝ} (hMF0 : 0 ≤ MF) (hMG0 : 0 ≤ MG)
    (hF : ∀ i x, |F i x| ≤ MF) (hG : ∀ i x, |G i x| ≤ MG)
    (n : ℕ) (S : Fin n → 𝒳) :
    empiricalRademacherComplexity n (fun i x => F i x - G i x) S
      ≤ empiricalRademacherComplexity n F S + empiricalRademacherComplexity n G S := by
  classical
  unfold empiricalRademacherComplexity
  rw [← mul_add, ← Finset.sum_add_distrib]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum ?_) (by positivity)
  intro σ _
  have hbddF := absInner_bddAbove F hMF0 hF n S σ
  have hbddG := absInner_bddAbove G hMG0 hG n S σ
  refine ciSup_le (fun i => ?_)
  have hsplit :
      (n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * (F i (S k) - G i (S k))
        = ((n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * F i (S k))
          - ((n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * G i (S k)) := by
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    refine congrArg _ (Finset.sum_congr rfl fun k _ => by ring)
  rw [hsplit]
  refine (abs_sub _ _).trans ?_
  exact add_le_add (le_ciSup hbddF i) (le_ciSup hbddG i)

/-- **Ledoux–Talagrand contraction over an arbitrary (possibly infinite) index.**
For an `L`-Lipschitz `φ` with `φ 0 = 0` and a class `F` with a uniform bound `M`,
`R̂_n(φ ∘ F) ≤ 2L · R̂_n(F)` for *any* nonempty index `ι`. The infinite-index case is
reduced to the finite-index `rademacher_contraction_abs` by choosing, for each of the
finitely many sign vectors, an `ε`-approximate maximizer; their finite collection is a
finite subindex on which the Fintype contraction applies. -/
theorem empiricalRademacherComplexity_contraction_abs_of_bddAbove
    [Nonempty ι]
    (φ : ℝ → ℝ) {L : ℝ} (hL : 0 ≤ L) (hφ : LipschitzAt0 φ L)
    (F : ι → 𝒳 → ℝ) {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ i x, |F i x| ≤ M)
    (n : ℕ) (S : Fin n → 𝒳) :
    empiricalRademacherComplexity n (fun i x => φ (F i x)) S
      ≤ 2 * L * empiricalRademacherComplexity n F S := by
  classical
  haveI hSigns : Nonempty (Signs n) := ⟨fun _ => ⟨1, by decide⟩⟩
  -- uniform bound for the composed class `φ ∘ F`
  have hLM0 : 0 ≤ L * M := mul_nonneg hL hM0
  have hφM : ∀ i x, |φ (F i x)| ≤ L * M := by
    intro i x
    have h := hφ.2 (F i x) 0
    rw [hφ.1, sub_zero, sub_zero] at h
    exact h.trans (mul_le_mul_of_nonneg_left (hM i x) hL)
  have hcard : (0 : ℝ) < (Fintype.card (Signs n) : ℝ) := by
    exact_mod_cast Fintype.card_pos (α := Signs n)
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  -- per-sign ε-approximate maximizers (explicit supremand form)
  have hex : ∀ σ : Signs n,
      ∃ i, (⨆ j, |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * φ (F j (S k))|) - ε
            < |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * φ (F i (S k))| := by
    intro σ
    exact exists_lt_of_lt_ciSup (sub_lt_self _ hε)
  choose iσ hiσ using hex
  -- the finite subindex collecting all per-sign maximizers
  set T : Finset ι := Finset.image iσ Finset.univ with hT
  haveI : Nonempty {x // x ∈ T} :=
    ⟨⟨iσ (Classical.arbitrary (Signs n)),
      Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩⟩⟩
  -- Fintype contraction on the subindex `↥T`
  have hcontr := rademacher_contraction_abs (ι := {x // x ∈ T}) φ hL hφ
    (fun j => F j.val) n S
  -- (b) restricting the index only lowers the (with-abs) complexity
  have hb : empiricalRademacherComplexity n (fun j : {x // x ∈ T} => F j.val) S
      ≤ empiricalRademacherComplexity n F S := by
    unfold empiricalRademacherComplexity
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum ?_) (by positivity)
    intro σ _
    exact ciSup_le (fun j => le_ciSup (absInner_bddAbove F hM0 hM n S σ) j.val)
  -- (a) the ε-maximizers recover the full supremum up to ε
  have ha : empiricalRademacherComplexity n (fun i x => φ (F i x)) S
      ≤ empiricalRademacherComplexity n (fun (j : {x // x ∈ T}) x => φ (F j.val x)) S + ε := by
    unfold empiricalRademacherComplexity
    have hpt : ∀ σ : Signs n,
        (⨆ i, |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * φ (F i (S k))|)
          ≤ (⨆ j : {x // x ∈ T},
              |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * φ (F j.val (S k))|) + ε := by
      intro σ
      have hmem : iσ σ ∈ T := Finset.mem_image.mpr ⟨σ, Finset.mem_univ _, rfl⟩
      have hbddT : BddAbove (Set.range
          (fun j : {x // x ∈ T} =>
            |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * φ (F j.val (S k))|)) :=
        Finite.bddAbove_range _
      have hle := le_ciSup hbddT (⟨iσ σ, hmem⟩ : {x // x ∈ T})
      have := hiσ σ
      linarith
    calc
      (Fintype.card (Signs n) : ℝ)⁻¹ *
            ∑ σ : Signs n, ⨆ i, |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * φ (F i (S k))|
          ≤ (Fintype.card (Signs n) : ℝ)⁻¹ *
              ∑ σ : Signs n,
                ((⨆ j : {x // x ∈ T},
                    |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * φ (F j.val (S k))|) + ε) := by
            refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun σ _ => hpt σ) (by positivity)
      _ = (Fintype.card (Signs n) : ℝ)⁻¹ *
              ∑ σ : Signs n,
                (⨆ j : {x // x ∈ T},
                    |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * φ (F j.val (S k))|)
            + (Fintype.card (Signs n) : ℝ)⁻¹ * (Fintype.card (Signs n) : ℝ) * ε := by
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            ring
      _ = (Fintype.card (Signs n) : ℝ)⁻¹ *
              ∑ σ : Signs n,
                (⨆ j : {x // x ∈ T},
                    |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) * φ (F j.val (S k))|)
            + ε := by
            rw [inv_mul_cancel₀ (ne_of_gt hcard)]; ring
  calc
    empiricalRademacherComplexity n (fun i x => φ (F i x)) S
        ≤ empiricalRademacherComplexity n (fun (j : {x // x ∈ T}) x => φ (F j.val x)) S + ε := ha
    _ ≤ 2 * L * empiricalRademacherComplexity n (fun j : {x // x ∈ T} => F j.val) S + ε := by
          linarith [hcontr]
    _ ≤ 2 * L * empiricalRademacherComplexity n F S + ε := by
          nlinarith [mul_le_mul_of_nonneg_left hb (by linarith : (0:ℝ) ≤ 2 * L)]

end Contraction

end Concentration
end Stat
end Causalean
