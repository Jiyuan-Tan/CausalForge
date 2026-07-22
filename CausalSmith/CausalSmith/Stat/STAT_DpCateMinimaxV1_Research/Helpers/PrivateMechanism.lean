/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Explicit private armwise local-polynomial mechanism

This module constructs the finite monomial basis, uniform localization kernel,
flattened empirical Gram/moment query, and clipped projected release used by the
central-DP CATE upper-bound witness.
-/

import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.PrivateUpperBound
import Causalean.Stat.Privacy.LaplaceMechanism
import Causalean.Mathlib.Analysis.ConvexProjection
import Causalean.Mathlib.Analysis.MonomialGram
import Mathlib.Data.Fintype.EquivFin

namespace CausalSmith.Stat.DpCateMinimax

open MeasureTheory
open scoped BigOperators ENNReal
open Causalean.Mathlib.Analysis
open Causalean.Stat.Privacy

/-! ## The finite monomial basis -/

/-- The multi-indices in `d` variables having total degree at most `m`. -/
def degExpo (d m : ℕ) : Finset (Fin d → ℕ) :=
  (Fintype.piFinset fun _ => Finset.range (m + 1)).filter
    (fun e => ∑ j, e j ≤ m)

/-- The number of monomials in `d` variables having total degree at most `m`. -/
def pDim (d m : ℕ) : ℕ := (degExpo d m).card

/-- A fixed enumeration of all multi-indices of total degree at most `m`. -/
noncomputable def expoOf (d m : ℕ) : Fin (pDim d m) → (Fin d → ℕ) :=
  fun k => ((degExpo d m).equivFin.symm k).1

/-- The monomial enumeration has no duplicate exponent vectors. -/
theorem expoOf_injective (d m : ℕ) : Function.Injective (expoOf d m) := by
  intro k l h
  apply (degExpo d m).equivFin.symm.injective
  apply Subtype.ext
  exact h

/-- Every enumerated exponent vector has total degree at most `m`. -/
theorem expoOf_deg (d m : ℕ) (k : Fin (pDim d m)) :
    (∑ j, expoOf d m k j) ≤ m := by
  have hk : ((degExpo d m).equivFin.symm k).1 ∈ degExpo d m :=
    ((degExpo d m).equivFin.symm k).2
  exact (Finset.mem_filter.mp hk).2

private theorem mem_piFinset_of_sum_le {d m : ℕ} (e : Fin d → ℕ)
    (he : (∑ j, e j) ≤ m) :
    e ∈ Fintype.piFinset (fun _ : Fin d => Finset.range (m + 1)) := by
  rw [Fintype.mem_piFinset]
  intro j
  rw [Finset.mem_range]
  have hj : e j ≤ ∑ i, e i :=
    Finset.single_le_sum (fun i _ => Nat.zero_le (e i)) (Finset.mem_univ j)
  omega

/-- Every exponent vector of total degree at most `m` occurs in the enumeration. -/
theorem expoOf_surj (d m : ℕ) (e : Fin d → ℕ) (he : (∑ j, e j) ≤ m) :
    ∃ k, expoOf d m k = e := by
  have hemem : e ∈ degExpo d m := by
    exact Finset.mem_filter.mpr ⟨mem_piFinset_of_sum_le e he, he⟩
  let es : degExpo d m := ⟨e, hemem⟩
  refine ⟨(degExpo d m).equivFin es, ?_⟩
  exact congrArg Subtype.val ((degExpo d m).equivFin.symm_apply_apply es)

/-- The monomial basis is nonempty because it contains the zero multi-index. -/
theorem pDim_pos (d m : ℕ) : 0 < pDim d m := by
  rw [Nat.pos_iff_ne_zero]
  intro hzero
  have hempty : degExpo d m = ∅ := Finset.card_eq_zero.mp hzero
  have hz : (fun _ : Fin d => 0) ∈ degExpo d m := by
    apply Finset.mem_filter.mpr
    constructor
    · rw [Fintype.mem_piFinset]
      intro j
      simp
    · simp
  simp [hempty] at hz

/-- The coordinate of the constant monomial in the enumerated basis. -/
noncomputable def icptOf (d m : ℕ) : Fin (pDim d m) :=
  Classical.choose (expoOf_surj d m (fun _ => 0) (by simp))

/-- The intercept coordinate has the zero exponent vector. -/
theorem expoOf_icptOf (d m : ℕ) : expoOf d m (icptOf d m) = fun _ => 0 :=
  Classical.choose_spec (expoOf_surj d m (fun _ => 0) (by simp))

/-- The intercept feature is identically one. -/
theorem monomial_expoOf_icptOf (d m : ℕ) (u : Fin d → ℝ) :
    monomial (expoOf d m (icptOf d m)) u = 1 := by
  simp [expoOf_icptOf, monomial]

/-! ## Uniform kernel and features -/

/-- The indicator kernel of the closed unit cube in sup norm. -/
noncomputable def unifKernel (d : ℕ) (u : Fin d → ℝ) : ℝ :=
  if ∀ j, |u j| ≤ 1 then 1 else 0

/-- The uniform kernel is nonnegative. -/
theorem unifKernel_nonneg (d : ℕ) (u : Fin d → ℝ) : 0 ≤ unifKernel d u := by
  unfold unifKernel
  split <;> norm_num

/-- The uniform kernel is bounded above by one. -/
theorem unifKernel_le_one (d : ℕ) (u : Fin d → ℝ) : unifKernel d u ≤ 1 := by
  unfold unifKernel
  split <;> norm_num

/-- The uniform kernel vanishes outside the unit cube. -/
theorem unifKernel_eq_zero (d : ℕ) (u : Fin d → ℝ)
    (hu : ∃ j, 1 < |u j|) : unifKernel d u = 0 := by
  rw [unifKernel, if_neg]
  exact not_forall.mpr ⟨hu.choose, not_le_of_gt hu.choose_spec⟩

/-- The uniform kernel is at least one throughout the half-unit cube. -/
theorem one_le_unifKernel (d : ℕ) (u : Fin d → ℝ)
    (hu : ∀ j, |u j| ≤ (1 / 2 : ℝ)) : 1 ≤ unifKernel d u := by
  rw [unifKernel, if_pos (fun j =>
    (hu j).trans (by norm_num : (1 / 2 : ℝ) ≤ 1))]

/-- The uniform indicator kernel is Borel measurable. -/
theorem measurable_unifKernel (d : ℕ) : Measurable (unifKernel d) := by
  let S : Set (Fin d → ℝ) := {u | ∀ j, |u j| ≤ (1 : ℝ)}
  have hS : MeasurableSet S := by
    change MeasurableSet {u : Fin d → ℝ | ∀ j, |u j| ≤ (1 : ℝ)}
    have hi : MeasurableSet (⋂ j : Fin d,
        {u : Fin d → ℝ | |u j| ≤ (1 : ℝ)}) := MeasurableSet.iInter fun j =>
      measurableSet_le (continuous_abs.measurable.comp (measurable_pi_apply j)) measurable_const
    rw [show {u : Fin d → ℝ | ∀ j, |u j| ≤ (1 : ℝ)} =
        ⋂ j : Fin d, {u : Fin d → ℝ | |u j| ≤ (1 : ℝ)} by
      ext u
      simp]
    exact hi
  change Measurable fun u => if u ∈ S then (1 : ℝ) else 0
  exact Measurable.piecewise hS measurable_const measurable_const

/-- The enumerated monomial feature vector. -/
noncomputable def featOf (d m : ℕ) (u : Fin d → ℝ) (k : Fin (pDim d m)) : ℝ :=
  monomial (expoOf d m k) u

/-- The monomial feature vector is Borel measurable in its argument. -/
theorem measurable_featOf (d m : ℕ) : Measurable (featOf d m) := by
  rw [measurable_pi_iff]
  intro k
  unfold featOf monomial
  fun_prop

/-- Every feature coordinate is bounded by one on the unit cube. -/
theorem abs_featOf_le_one (d m : ℕ) (u : Fin d → ℝ) (k : Fin (pDim d m))
    (hu : ∀ j, |u j| ≤ 1) : |featOf d m u k| ≤ 1 := by
  rw [featOf, monomial, Finset.abs_prod]
  simp only [abs_pow]
  exact Finset.prod_le_one (fun _ _ => pow_nonneg (abs_nonneg _) _)
    (fun j _ => pow_le_one₀ (abs_nonneg _) (hu j))

/-! ## Flattened coordinate layout -/

/-- The total number of Gram and moment query coordinates. -/
def Nq (d m : ℕ) : ℕ := 2 * pDim d m * pDim d m + 2 * pDim d m

private theorem pairIdx_lt {p a k l : ℕ} (ha : a < 2) (hk : k < p) (hl : l < p) :
    (a * p + k) * p + l < 2 * p * p := by
  have hap : a * p + k < 2 * p := by
    calc
      a * p + k < a * p + p := Nat.add_lt_add_left hk _
      _ = (a + 1) * p := by ring
      _ ≤ 2 * p := Nat.mul_le_mul_right p (Nat.succ_le_iff.mpr ha)
  calc
    (a * p + k) * p + l < (a * p + k) * p + p := Nat.add_lt_add_left hl _
    _ = (a * p + k + 1) * p := by ring
    _ ≤ (2 * p) * p := Nat.mul_le_mul_right p (Nat.succ_le_iff.mpr hap)
    _ = 2 * p * p := by ring

/-- The flattened coordinate of an armwise Gram entry. -/
def gramIdxOf (d m : ℕ) (a : Fin 2) (k l : Fin (pDim d m)) : Fin (Nq d m) :=
  ⟨((a : ℕ) * pDim d m + k) * pDim d m + l, by
    have ha : (a : ℕ) < 2 := a.isLt
    have hk : (k : ℕ) < pDim d m := k.isLt
    have hl : (l : ℕ) < pDim d m := l.isLt
    simp only [Nq]
    exact (pairIdx_lt ha hk hl).trans_le (Nat.le_add_right _ _)⟩

/-- The flattened coordinate of an armwise moment entry. -/
def momIdxOf (d m : ℕ) (a : Fin 2) (k : Fin (pDim d m)) : Fin (Nq d m) :=
  ⟨2 * pDim d m * pDim d m + ((a : ℕ) * pDim d m + k), by
    have ha : (a : ℕ) < 2 := a.isLt
    have hk : (k : ℕ) < pDim d m := k.isLt
    simp only [Nq]
    nlinarith⟩

/-- The Gram-coordinate layout is injective. -/
theorem gramIdxOf_injective (d m : ℕ) :
    Function.Injective (fun q : Fin 2 × Fin (pDim d m) × Fin (pDim d m) =>
      gramIdxOf d m q.1 q.2.1 q.2.2) := by
  rintro ⟨a, k, l⟩ ⟨a', k', l'⟩ h
  simp only [Prod.mk.injEq]
  have hv := congrArg Fin.val h
  simp only [gramIdxOf] at hv
  have hp := pDim_pos d m
  have hl : l = l' := by
    apply Fin.ext
    have hm := congrArg (fun x : ℕ => x % pDim d m) hv
    simpa [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt l.isLt,
      Nat.mod_eq_of_lt l'.isLt] using hm
  subst l'
  have hbase : (a : ℕ) * pDim d m + k = (a' : ℕ) * pDim d m + k' := by
    apply Nat.mul_right_cancel hp
    exact Nat.add_right_cancel hv
  have hk : k = k' := by
    apply Fin.ext
    have hm := congrArg (fun x : ℕ => x % pDim d m) hbase
    simpa [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt k.isLt,
      Nat.mod_eq_of_lt k'.isLt] using hm
  subst k'
  have ha : a = a' := by
    apply Fin.ext
    apply Nat.mul_right_cancel hp
    exact Nat.add_right_cancel hbase
  subst a'
  simp

/-- The moment-coordinate layout is injective. -/
theorem momIdxOf_injective (d m : ℕ) :
    Function.Injective (fun q : Fin 2 × Fin (pDim d m) => momIdxOf d m q.1 q.2) := by
  rintro ⟨a, k⟩ ⟨a', k'⟩ h
  simp only [Prod.mk.injEq]
  have hv := congrArg Fin.val h
  simp only [momIdxOf] at hv
  have hp := pDim_pos d m
  have hbase : (a : ℕ) * pDim d m + k = (a' : ℕ) * pDim d m + k' :=
    Nat.add_left_cancel hv
  have hk : k = k' := by
    apply Fin.ext
    have hm := congrArg (fun x : ℕ => x % pDim d m) hbase
    simpa [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt k.isLt,
      Nat.mod_eq_of_lt k'.isLt] using hm
  subst k'
  have ha : a = a' := by
    apply Fin.ext
    apply Nat.mul_right_cancel hp
    exact Nat.add_right_cancel hbase
  subst a'
  simp

/-- Gram coordinates and moment coordinates are disjoint. -/
theorem gramIdxOf_ne_momIdxOf (d m : ℕ) (a : Fin 2) (k l : Fin (pDim d m))
    (a' : Fin 2) (k' : Fin (pDim d m)) :
    gramIdxOf d m a k l ≠ momIdxOf d m a' k' := by
  intro hEq
  have hv := congrArg Fin.val hEq
  simp only [gramIdxOf, momIdxOf] at hv
  have ha : (a : ℕ) < 2 := a.isLt
  have hk : (k : ℕ) < pDim d m := k.isLt
  have hl : (l : ℕ) < pDim d m := l.isLt
  have hgram : (((a : ℕ) * pDim d m + k) * pDim d m + l) <
      2 * pDim d m * pDim d m := pairIdx_lt ha hk hl
  omega

/-! ## Empirical query -/

/-- The armwise localized empirical Gram matrix. -/
noncomputable def empGram {d n : ℕ} (m : ℕ) (h : ℝ) (x0 : Fin d → ℝ)
    (a : Fin 2) (s : Fin n → CateObs d) : Matrix (Fin (pDim d m)) (Fin (pDim d m)) ℝ :=
  Matrix.of (fun k l : Fin (pDim d m) =>
    (n : ℝ)⁻¹ * ∑ i : Fin n,
      (if (s i).A = ((a : ℕ) : ℝ) then (1 : ℝ) else 0)
        * h ^ (-(d : ℝ)) * unifKernel d (fun j => ((s i).X j - x0 j) / h)
        * featOf d m (fun j => ((s i).X j - x0 j) / h) k
        * featOf d m (fun j => ((s i).X j - x0 j) / h) l)

/-- The armwise localized empirical moment vector, with outcomes clipped to `[-1,1]`. -/
noncomputable def empMom {d n : ℕ} (m : ℕ) (h : ℝ) (x0 : Fin d → ℝ)
    (a : Fin 2) (s : Fin n → CateObs d) : Fin (pDim d m) → ℝ :=
  fun k : Fin (pDim d m) =>
    (n : ℝ)⁻¹ * ∑ i : Fin n,
      (if (s i).A = ((a : ℕ) : ℝ) then (1 : ℝ) else 0)
        * h ^ (-(d : ℝ)) * unifKernel d (fun j => ((s i).X j - x0 j) / h)
        * max (-1) (min 1 (s i).Y)
        * featOf d m (fun j => ((s i).X j - x0 j) / h) k

/-- An explicit sensitivity numerator for the joint Gram/moment query. -/
def Cs (d m : ℕ) : ℝ := 4 * (pDim d m : ℝ) ^ 2 + 4 * (pDim d m : ℝ)

private noncomputable def gramSummand {d : ℕ} (m : ℕ) (h : ℝ) (x0 : Fin d → ℝ)
    (a : Fin 2) (O : CateObs d) (k l : Fin (pDim d m)) : ℝ :=
  (if O.A = ((a : ℕ) : ℝ) then (1 : ℝ) else 0)
    * h ^ (-(d : ℝ)) * unifKernel d (fun j => (O.X j - x0 j) / h)
    * featOf d m (fun j => (O.X j - x0 j) / h) k
    * featOf d m (fun j => (O.X j - x0 j) / h) l

private noncomputable def momSummand {d : ℕ} (m : ℕ) (h : ℝ) (x0 : Fin d → ℝ)
    (a : Fin 2) (O : CateObs d) (k : Fin (pDim d m)) : ℝ :=
  (if O.A = ((a : ℕ) : ℝ) then (1 : ℝ) else 0)
    * h ^ (-(d : ℝ)) * unifKernel d (fun j => (O.X j - x0 j) / h)
    * max (-1) (min 1 O.Y)
    * featOf d m (fun j => (O.X j - x0 j) / h) k

private theorem abs_armIndicator_le_one (A : ℝ) (a : Fin 2) :
    |if A = ((a : ℕ) : ℝ) then (1 : ℝ) else 0| ≤ 1 := by
  split <;> norm_num

private theorem abs_clip_one_le_one (y : ℝ) : |max (-1) (min 1 y)| ≤ 1 := by
  rw [abs_le]
  constructor
  · exact le_max_left _ _
  · exact (max_le (by norm_num) (min_le_left _ _))

private theorem abs_gramSummand_le {d : ℕ} (m : ℕ) {h : ℝ} (hh : 0 < h)
    (x0 : Fin d → ℝ) (a : Fin 2) (O : CateObs d) (k l : Fin (pDim d m)) :
    |gramSummand m h x0 a O k l| ≤ h ^ (-(d : ℝ)) := by
  let u : Fin d → ℝ := fun j => (O.X j - x0 j) / h
  by_cases hu : ∀ j, |u j| ≤ 1
  · have hR : 0 ≤ h ^ (-(d : ℝ)) := (Real.rpow_pos_of_pos hh _).le
    have hI := abs_armIndicator_le_one O.A a
    have hk := abs_featOf_le_one d m u k hu
    have hl := abs_featOf_le_one d m u l hu
    rw [gramSummand, show (fun j => (O.X j - x0 j) / h) = u from rfl,
      unifKernel, if_pos hu]
    simp only [abs_mul, mul_one]
    have hRabs : |h ^ (-(d : ℝ))| = h ^ (-(d : ℝ)) := abs_of_nonneg hR
    rw [hRabs]
    calc
      |if O.A = ((a : ℕ) : ℝ) then (1 : ℝ) else 0| * h ^ (-(d : ℝ)) *
          |featOf d m u k| * |featOf d m u l|
          ≤ 1 * h ^ (-(d : ℝ)) * 1 * 1 := by
            gcongr
      _ = h ^ (-(d : ℝ)) := by ring
  · rw [gramSummand, show (fun j => (O.X j - x0 j) / h) = u from rfl,
      unifKernel, if_neg hu]
    simp
    exact pow_nonneg (le_of_lt hh) d

private theorem abs_momSummand_le {d : ℕ} (m : ℕ) {h : ℝ} (hh : 0 < h)
    (x0 : Fin d → ℝ) (a : Fin 2) (O : CateObs d) (k : Fin (pDim d m)) :
    |momSummand m h x0 a O k| ≤ h ^ (-(d : ℝ)) := by
  let u : Fin d → ℝ := fun j => (O.X j - x0 j) / h
  by_cases hu : ∀ j, |u j| ≤ 1
  · have hR : 0 ≤ h ^ (-(d : ℝ)) := (Real.rpow_pos_of_pos hh _).le
    have hI := abs_armIndicator_le_one O.A a
    have hy := abs_clip_one_le_one O.Y
    have hk := abs_featOf_le_one d m u k hu
    rw [momSummand, show (fun j => (O.X j - x0 j) / h) = u from rfl,
      unifKernel, if_pos hu]
    simp only [abs_mul, mul_one]
    have hRabs : |h ^ (-(d : ℝ))| = h ^ (-(d : ℝ)) := abs_of_nonneg hR
    rw [hRabs]
    calc
      |if O.A = ((a : ℕ) : ℝ) then (1 : ℝ) else 0| * h ^ (-(d : ℝ)) *
          |max (-1) (min 1 O.Y)| * |featOf d m u k|
          ≤ 1 * h ^ (-(d : ℝ)) * 1 * 1 := by
            gcongr
      _ = h ^ (-(d : ℝ)) := by ring
  · rw [momSummand, show (fun j => (O.X j - x0 j) / h) = u from rfl,
      unifKernel, if_neg hu]
    simp
    exact pow_nonneg (le_of_lt hh) d

private theorem sum_sub_sum_eq_single {n : ℕ} (f g : Fin n → ℝ) (i : Fin n)
    (hfg : ∀ j, j ≠ i → f j = g j) :
    (∑ j, f j) - ∑ j, g j = f i - g i := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_eq_single i
  · intro j _ hji
    rw [hfg j hji]
    simp
  · simp

private theorem abs_empGram_sub_le {d n : ℕ} (m : ℕ) {h : ℝ} (hh : 0 < h)
    (x0 : Fin d → ℝ) (a : Fin 2) (s s' : Fin n → CateObs d) (i : Fin n)
    (hss : ∀ j, j ≠ i → s j = s' j) (k l : Fin (pDim d m)) :
    |empGram m h x0 a s k l - empGram m h x0 a s' k l| ≤
      2 * (n : ℝ)⁻¹ * h ^ (-(d : ℝ)) := by
  change |(n : ℝ)⁻¹ * (∑ j, gramSummand m h x0 a (s j) k l) -
      (n : ℝ)⁻¹ * (∑ j, gramSummand m h x0 a (s' j) k l)| ≤ _
  rw [← mul_sub, sum_sub_sum_eq_single _ _ i (fun j hji => by rw [hss j hji]), abs_mul]
  have hni : 0 ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg n)
  rw [abs_of_nonneg hni]
  calc
    (n : ℝ)⁻¹ * |gramSummand m h x0 a (s i) k l -
        gramSummand m h x0 a (s' i) k l|
        ≤ (n : ℝ)⁻¹ * (|gramSummand m h x0 a (s i) k l| +
          |gramSummand m h x0 a (s' i) k l|) := by
            gcongr
            exact abs_sub _ _
    _ ≤ (n : ℝ)⁻¹ * (h ^ (-(d : ℝ)) + h ^ (-(d : ℝ))) := by
      gcongr <;> exact abs_gramSummand_le m hh x0 a _ k l
    _ = 2 * (n : ℝ)⁻¹ * h ^ (-(d : ℝ)) := by ring

private theorem abs_empMom_sub_le {d n : ℕ} (m : ℕ) {h : ℝ} (hh : 0 < h)
    (x0 : Fin d → ℝ) (a : Fin 2) (s s' : Fin n → CateObs d) (i : Fin n)
    (hss : ∀ j, j ≠ i → s j = s' j) (k : Fin (pDim d m)) :
    |empMom m h x0 a s k - empMom m h x0 a s' k| ≤
      2 * (n : ℝ)⁻¹ * h ^ (-(d : ℝ)) := by
  change |(n : ℝ)⁻¹ * (∑ j, momSummand m h x0 a (s j) k) -
      (n : ℝ)⁻¹ * (∑ j, momSummand m h x0 a (s' j) k)| ≤ _
  rw [← mul_sub, sum_sub_sum_eq_single _ _ i (fun j hji => by rw [hss j hji]), abs_mul]
  have hni : 0 ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg n)
  rw [abs_of_nonneg hni]
  calc
    (n : ℝ)⁻¹ * |momSummand m h x0 a (s i) k - momSummand m h x0 a (s' i) k|
        ≤ (n : ℝ)⁻¹ * (|momSummand m h x0 a (s i) k| +
          |momSummand m h x0 a (s' i) k|) := by
            gcongr
            exact abs_sub _ _
    _ ≤ (n : ℝ)⁻¹ * (h ^ (-(d : ℝ)) + h ^ (-(d : ℝ))) := by
      gcongr <;> exact abs_momSummand_le m hh x0 a _ k
    _ = 2 * (n : ℝ)⁻¹ * h ^ (-(d : ℝ)) := by ring

/-- The joint armwise Gram/moment query has the stated global `ℓ¹` sensitivity. -/
theorem empQuery_sensitivity {d n : ℕ} (m : ℕ) (h : ℝ) (x0 : Fin d → ℝ)
    (hn : 0 < n) (hh : 0 < h) :
    ∀ s s' : Fin n → CateObs d, ReplacementAdjacent s s' →
      (∑ a : Fin 2, ∑ k, ∑ l,
          |empGram m h x0 a s k l - empGram m h x0 a s' k l|)
        + (∑ a : Fin 2, ∑ k,
          |empMom m h x0 a s k - empMom m h x0 a s' k|)
        ≤ Cs d m / ((n : ℝ) * h ^ (d : ℝ)) := by
  intro s s' hadj
  obtain ⟨i, hss⟩ := hadj
  have hG : (∑ a : Fin 2, ∑ k, ∑ l,
      |empGram m h x0 a s k l - empGram m h x0 a s' k l|) ≤
      (4 * (pDim d m : ℝ) ^ 2) * ((n : ℝ)⁻¹ * h ^ (-(d : ℝ))) := by
    calc
      _ ≤ ∑ _a : Fin 2, ∑ _k : Fin (pDim d m), ∑ _l : Fin (pDim d m),
          2 * (n : ℝ)⁻¹ * h ^ (-(d : ℝ)) := by
            exact Finset.sum_le_sum fun a _ =>
              Finset.sum_le_sum fun k _ =>
                Finset.sum_le_sum fun l _ => abs_empGram_sub_le m hh x0 a s s' i hss k l
      _ = _ := by simp [pow_two]; ring
  have hM : (∑ a : Fin 2, ∑ k,
      |empMom m h x0 a s k - empMom m h x0 a s' k|) ≤
      (4 * (pDim d m : ℝ)) * ((n : ℝ)⁻¹ * h ^ (-(d : ℝ))) := by
    calc
      _ ≤ ∑ _a : Fin 2, ∑ _k : Fin (pDim d m),
          2 * (n : ℝ)⁻¹ * h ^ (-(d : ℝ)) := by
            exact Finset.sum_le_sum fun a _ =>
              Finset.sum_le_sum fun k _ => abs_empMom_sub_le m hh x0 a s s' i hss k
      _ = _ := by simp; ring
  calc
    _ ≤ (4 * (pDim d m : ℝ) ^ 2) * ((n : ℝ)⁻¹ * h ^ (-(d : ℝ))) +
        (4 * (pDim d m : ℝ)) * ((n : ℝ)⁻¹ * h ^ (-(d : ℝ))) := add_le_add hG hM
    _ = Cs d m / ((n : ℝ) * h ^ (d : ℝ)) := by
      rw [Real.rpow_neg (le_of_lt hh)]
      unfold Cs
      field_simp

/-! ## Projected and clipped release -/

/-- The projected armwise local-polynomial solve, differenced and clipped to `[-2,2]`. -/
noncomputable def releaseOf {d n : ℕ} (m : ℕ) (h cstar Cstar : ℝ)
    (x0 : Fin d → ℝ) (s : Fin n → CateObs d) (w : Fin (Nq d m) → ℝ) : ℝ :=
  max (-2) (min 2
    ((((loewnerProj (pDim d m) cstar Cstar
          (Matrix.of (fun k l : Fin (pDim d m) =>
            empGram m h x0 1 s k l + w (gramIdxOf d m 1 k l))))⁻¹.mulVec
        (fun k : Fin (pDim d m) => empMom m h x0 1 s k + w (momIdxOf d m 1 k)))
      (icptOf d m)) -
    (((loewnerProj (pDim d m) cstar Cstar
          (Matrix.of (fun k l : Fin (pDim d m) =>
            empGram m h x0 0 s k l + w (gramIdxOf d m 0 k l))))⁻¹.mulVec
        (fun k : Fin (pDim d m) => empMom m h x0 0 s k + w (momIdxOf d m 0 k)))
      (icptOf d m))))

local instance matrixMeasurableSpace (p : ℕ) :
    MeasurableSpace (Matrix (Fin p) (Fin p) ℝ) :=
  MeasurableSpace.pi

local instance matrixBorelSpace (p : ℕ) :
    BorelSpace (Matrix (Fin p) (Fin p) ℝ) :=
  ⟨by
    change MeasurableSpace.pi = borel (Fin p → Fin p → ℝ)
    exact BorelSpace.measurable_eq⟩

private theorem measurable_matrix_iff {α : Type*} [MeasurableSpace α] {p : ℕ}
    (f : α → Matrix (Fin p) (Fin p) ℝ) :
    Measurable f ↔ ∀ i j, Measurable (fun x => f x i j) := by
  change (@Measurable α (Fin p → Fin p → ℝ) _ (matrixMeasurableSpace p) f) ↔
    ∀ i j, Measurable (fun x => f x i j)
  unfold matrixMeasurableSpace
  simp only [measurable_pi_iff]

/-- Matrix inversion is measurable on finite real matrices, with singular matrices
using Mathlib's nonsingular-inverse convention. -/
theorem measurable_matrix_inv (p : ℕ) :
    Measurable (fun G : Matrix (Fin p) (Fin p) ℝ => G⁻¹) := by
  rw [measurable_matrix_iff]
  intro i j
  simp only [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv]
  fun_prop

private theorem measurable_inv_mulVec_apply {α : Type*} [MeasurableSpace α] {p : ℕ}
    (G : α → Matrix (Fin p) (Fin p) ℝ) (v : α → Fin p → ℝ)
    (hG : Measurable G) (hv : Measurable v) (i : Fin p) :
    Measurable (fun x => (G x)⁻¹.mulVec (v x) i) := by
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.measurable_sum _ fun j _ =>
    ((((measurable_matrix_iff _).mp ((measurable_matrix_inv p).comp hG)) i j).mul
        (measurable_pi_iff.mp hv j))

private theorem measurable_gramSummand {d : ℕ} (m : ℕ) (h : ℝ)
    (x0 : Fin d → ℝ) (a : Fin 2) (k l : Fin (pDim d m)) :
    Measurable (fun O : CateObs d => gramSummand m h x0 a O k l) := by
  unfold gramSummand
  apply Measurable.mul
  · apply Measurable.mul
    · apply Measurable.mul
      · apply Measurable.mul
        · exact Measurable.ite (measurableSet_eq_fun measurable_CateObs_A measurable_const)
            measurable_const measurable_const
        · exact measurable_const
      · exact (measurable_unifKernel d).comp
          (measurable_pi_iff.mpr fun j =>
            ((measurable_pi_apply j).comp measurable_CateObs_X).sub measurable_const |>.div_const h)
    · exact (measurable_pi_iff.mp (measurable_featOf d m) k).comp
        (measurable_pi_iff.mpr fun j =>
          ((measurable_pi_apply j).comp measurable_CateObs_X).sub measurable_const |>.div_const h)
  · exact (measurable_pi_iff.mp (measurable_featOf d m) l).comp
      (measurable_pi_iff.mpr fun j =>
        ((measurable_pi_apply j).comp measurable_CateObs_X).sub measurable_const |>.div_const h)

private theorem measurable_momSummand {d : ℕ} (m : ℕ) (h : ℝ)
    (x0 : Fin d → ℝ) (a : Fin 2) (k : Fin (pDim d m)) :
    Measurable (fun O : CateObs d => momSummand m h x0 a O k) := by
  unfold momSummand
  apply Measurable.mul
  · apply Measurable.mul
    · apply Measurable.mul
      · apply Measurable.mul
        · exact Measurable.ite (measurableSet_eq_fun measurable_CateObs_A measurable_const)
            measurable_const measurable_const
        · exact measurable_const
      · exact (measurable_unifKernel d).comp
          (measurable_pi_iff.mpr fun j =>
            ((measurable_pi_apply j).comp measurable_CateObs_X).sub measurable_const |>.div_const h)
    · exact measurable_const.max (measurable_const.min measurable_CateObs_Y)
  · exact (measurable_pi_iff.mp (measurable_featOf d m) k).comp
      (measurable_pi_iff.mpr fun j =>
        ((measurable_pi_apply j).comp measurable_CateObs_X).sub measurable_const |>.div_const h)

/-- The empirical Gram query is jointly measurable in the dataset. -/
theorem measurable_empGram {d n : ℕ} (m : ℕ) (h : ℝ) (x0 : Fin d → ℝ) (a : Fin 2) :
    Measurable (empGram (n := n) m h x0 a) := by
  rw [measurable_matrix_iff]
  intro k l
  change Measurable fun s : Fin n → CateObs d =>
    (n : ℝ)⁻¹ * ∑ i, gramSummand m h x0 a (s i) k l
  exact measurable_const.mul (Finset.measurable_sum _ fun i _ =>
    (measurable_gramSummand m h x0 a k l).comp (measurable_pi_apply i))

/-- The empirical moment query is jointly measurable in the dataset. -/
theorem measurable_empMom {d n : ℕ} (m : ℕ) (h : ℝ) (x0 : Fin d → ℝ) (a : Fin 2) :
    Measurable (empMom (n := n) m h x0 a) := by
  rw [measurable_pi_iff]
  intro k
  change Measurable fun s : Fin n → CateObs d =>
    (n : ℝ)⁻¹ * ∑ i, momSummand m h x0 a (s i) k
  exact measurable_const.mul (Finset.measurable_sum _ fun i _ =>
    (measurable_momSummand m h x0 a k).comp (measurable_pi_apply i))

set_option maxHeartbeats 500000 in
/-- The release map is jointly measurable in the dataset and noise vector. -/
theorem measurable_releaseOf_joint {d n : ℕ} (m : ℕ) (h cstar Cstar : ℝ)
    (x0 : Fin d → ℝ) :
    Measurable (fun sw : (Fin n → CateObs d) × (Fin (Nq d m) → ℝ) =>
      releaseOf m h cstar Cstar x0 sw.1 sw.2) := by
  have hsolve (a : Fin 2) : Measurable (fun sw :
      (Fin n → CateObs d) × (Fin (Nq d m) → ℝ) =>
      ((loewnerProj (pDim d m) cstar Cstar
        (Matrix.of fun k l => empGram m h x0 a sw.1 k l + sw.2 (gramIdxOf d m a k l)))⁻¹.mulVec
          (fun k => empMom m h x0 a sw.1 k + sw.2 (momIdxOf d m a k))) (icptOf d m)) := by
    have hG : Measurable (fun sw : (Fin n → CateObs d) × (Fin (Nq d m) → ℝ) =>
        Matrix.of fun k l => empGram m h x0 a sw.1 k l + sw.2 (gramIdxOf d m a k l)) := by
      rw [measurable_matrix_iff]
      intro k l
      exact ((((measurable_matrix_iff _).mp (measurable_empGram m h x0 a)) k l).comp measurable_fst).add
            ((measurable_pi_apply (gramIdxOf d m a k l)).comp measurable_snd)
    have hv : Measurable (fun sw : (Fin n → CateObs d) × (Fin (Nq d m) → ℝ) =>
        fun k => empMom m h x0 a sw.1 k + sw.2 (momIdxOf d m a k)) := by
      rw [measurable_pi_iff]
      intro k
      exact ((measurable_pi_iff.mp (measurable_empMom m h x0 a) k).comp measurable_fst).add
        ((measurable_pi_apply (momIdxOf d m a k)).comp measurable_snd)
    exact measurable_inv_mulVec_apply _ _
      ((measurable_loewnerProj (pDim d m) cstar Cstar).comp hG) hv (icptOf d m)
  unfold releaseOf
  exact measurable_const.max (measurable_const.min ((hsolve 1).sub (hsolve 0)))

set_option maxHeartbeats 1000000 in
/-- For a fixed dataset, the release is measurable in its noise vector. -/
theorem measurable_releaseOf_noise {d n : ℕ} (m : ℕ) (h cstar Cstar : ℝ)
    (x0 : Fin d → ℝ) (s : Fin n → CateObs d) :
    Measurable (releaseOf m h cstar Cstar x0 s) := by
  change Measurable ((fun sw : (Fin n → CateObs d) × (Fin (Nq d m) → ℝ) =>
    releaseOf m h cstar Cstar x0 sw.1 sw.2) ∘ fun w => (s, w))
  exact (measurable_releaseOf_joint m h cstar Cstar x0).comp
    (measurable_const.prodMk measurable_id)

set_option maxHeartbeats 1000000 in
/-- For fixed noise, the release is measurable in the dataset. -/
theorem measurable_releaseOf_data {d n : ℕ} (m : ℕ) (h cstar Cstar : ℝ)
    (x0 : Fin d → ℝ) (w : Fin (Nq d m) → ℝ) :
    Measurable (fun s : Fin n → CateObs d => releaseOf m h cstar Cstar x0 s w) := by
  change Measurable ((fun sw : (Fin n → CateObs d) × (Fin (Nq d m) → ℝ) =>
    releaseOf m h cstar Cstar x0 sw.1 sw.2) ∘ fun s => (s, w))
  exact (measurable_releaseOf_joint m h cstar Cstar x0).comp
    (measurable_id.prodMk measurable_const)

/-- The explicit additive-Laplace projected local-polynomial mechanism. -/
noncomputable def mechOf {d n : ℕ} (m : ℕ) (h cstar Cstar epsN : ℝ)
    (x0 : Fin d → ℝ) (s : Fin n → CateObs d) : Measure ℝ :=
  (laplaceVecKernel (Nq d m)
    (((Cs d m) / ((n : ℝ) * h ^ (d : ℝ))) / epsN)).map
      (releaseOf m h cstar Cstar x0 s)

/-- Every output law of the explicit mechanism is supported on `[-2,2]`. -/
theorem mechOf_clipped {d n : ℕ} (m : ℕ) (h cstar Cstar epsN : ℝ)
    (x0 : Fin d → ℝ) :
    ∀ s : Fin n → CateObs d,
      (mechOf m h cstar Cstar epsN x0 s) (Set.Icc (-2 : ℝ) 2)ᶜ = 0 := by
  intro s
  rw [mechOf, Measure.map_apply (measurable_releaseOf_noise m h cstar Cstar x0 s)
    measurableSet_Icc.compl]
  have hempty : releaseOf m h cstar Cstar x0 s ⁻¹' (Set.Icc (-2 : ℝ) 2)ᶜ = ∅ := by
    ext w
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_Icc, Set.mem_empty_iff_false,
      iff_false, not_not]
    exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  rw [hempty, measure_empty]

set_option maxHeartbeats 1000000 in
/-- The explicit mechanism has exactly the armwise privatized local-polynomial
shape required by the structural upper-bound predicate. -/
theorem mechOf_isArmwise {d n : ℕ} (beta r0 epsN h cstar Cstar : ℝ)
    (x0 : Fin d → ℝ) (hbeta : 0 < beta) (hh : 0 < h) (hhr : h ≤ r0)
    (hcstar : 0 < cstar) (hcC : cstar ≤ Cstar) (hn : 0 < n) :
    IsArmwisePrivatizedLocalPoly n beta r0 epsN x0
      (mechOf (⌈beta⌉₊ - 1) h cstar Cstar epsN x0) := by
  let m : ℕ := ⌈beta⌉₊ - 1
  have hp : 0 < pDim d m := pDim_pos d m
  have hCs : 0 < Cs d m := by
    unfold Cs
    positivity
  have hm : m + 1 = ⌈beta⌉₊ := by
    dsimp [m]
    have hbceil : 0 < ⌈beta⌉₊ := Nat.ceil_pos.mpr hbeta
    omega
  refine ⟨h, Cs d m, 1, 1, (1 / 2 : ℝ), cstar, Cstar, m, pDim d m,
    Nq d m, icptOf d m, expoOf d m, unifKernel d, featOf d m,
    gramIdxOf d m, momIdxOf d m, empGram m h x0, empMom m h x0,
    loewnerProj (pDim d m) cstar Cstar, releaseOf m h cstar Cstar x0,
    hh, hhr, hCs, by norm_num, by norm_num, by norm_num, by norm_num,
    hcstar, hcC, hm, hp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · exact expoOf_deg d m
  · intro u k
    rfl
  · exact expoOf_surj d m
  · exact expoOf_icptOf d m
  · intro u
    exact monomial_expoOf_icptOf d m u
  · exact unifKernel_nonneg d
  · exact unifKernel_le_one d
  · exact unifKernel_eq_zero d
  · intro u hu
    exact one_le_unifKernel d u hu
  · intro a s
    constructor <;> rfl
  · exact gramIdxOf_injective d m
  · exact momIdxOf_injective d m
  · exact gramIdxOf_ne_momIdxOf d m
  · intro s s' hadj
    exact empQuery_sensitivity m h x0 hn hh s s' hadj
  · exact measurable_loewnerProj (pDim d m) cstar Cstar
  · intro G
    simpa [loewnerSet] using loewnerProj_mem hcstar hcC G
  · intro G hGlower hGupper
    exact loewnerProj_eq_self hcstar hcC G ⟨hGlower, hGupper⟩
  · intro G S hSlower hSupper
    exact loewnerProj_frobDist_le hcstar hcC G S ⟨hSlower, hSupper⟩
  · constructor
    · intro s w
      rfl
    · intro s
      rfl

/-! ## Flattened query and data-independent post-processing -/

private def queryCoordOf (d m : ℕ) :
    (Fin 2 × Fin (pDim d m) × Fin (pDim d m)) ⊕ (Fin 2 × Fin (pDim d m)) →
      Fin (Nq d m)
  | Sum.inl q => gramIdxOf d m q.1 q.2.1 q.2.2
  | Sum.inr q => momIdxOf d m q.1 q.2

private theorem queryCoordOf_injective (d m : ℕ) :
    Function.Injective (queryCoordOf d m) := by
  intro q q' h
  cases q with
  | inl q =>
      cases q' with
      | inl q' => exact congrArg Sum.inl (gramIdxOf_injective d m h)
      | inr q' => exact False.elim (gramIdxOf_ne_momIdxOf d m _ _ _ _ _ h)
  | inr q =>
      cases q' with
      | inl q' => exact False.elim (gramIdxOf_ne_momIdxOf d m _ _ _ _ _ h.symm)
      | inr q' => exact congrArg Sum.inr (momIdxOf_injective d m h)

private theorem queryCoordOf_bijective (d m : ℕ) :
    Function.Bijective (queryCoordOf d m) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · exact queryCoordOf_injective d m
  · simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    simp [Nq]
    ring

private noncomputable def queryCoordEquiv (d m : ℕ) :
    (Fin 2 × Fin (pDim d m) × Fin (pDim d m)) ⊕ (Fin 2 × Fin (pDim d m)) ≃
      Fin (Nq d m) :=
  Equiv.ofBijective (queryCoordOf d m) (queryCoordOf_bijective d m)

/-- The complete empirical Gram/moment query flattened into its explicit coordinate layout. -/
noncomputable def qOf {d n : ℕ} (m : ℕ) (h : ℝ) (x0 : Fin d → ℝ)
    (s : Fin n → CateObs d) (i : Fin (Nq d m)) : ℝ :=
  match (queryCoordEquiv d m).symm i with
  | Sum.inl q => empGram m h x0 q.1 s q.2.1 q.2.2
  | Sum.inr q => empMom m h x0 q.1 s q.2

/-- The flattened query recovers every Gram coordinate. -/
theorem qOf_gramIdxOf {d n : ℕ} (m : ℕ) (h : ℝ) (x0 : Fin d → ℝ)
    (s : Fin n → CateObs d) (a : Fin 2) (k l : Fin (pDim d m)) :
    qOf m h x0 s (gramIdxOf d m a k l) = empGram m h x0 a s k l := by
  change (match (queryCoordEquiv d m).symm
      (queryCoordEquiv d m (Sum.inl (a, k, l))) with
    | Sum.inl q => empGram m h x0 q.1 s q.2.1 q.2.2
    | Sum.inr q => empMom m h x0 q.1 s q.2) = _
  rw [(queryCoordEquiv d m).symm_apply_apply]

/-- The flattened query recovers every moment coordinate. -/
theorem qOf_momIdxOf {d n : ℕ} (m : ℕ) (h : ℝ) (x0 : Fin d → ℝ)
    (s : Fin n → CateObs d) (a : Fin 2) (k : Fin (pDim d m)) :
    qOf m h x0 s (momIdxOf d m a k) = empMom m h x0 a s k := by
  change (match (queryCoordEquiv d m).symm
      (queryCoordEquiv d m (Sum.inr (a, k))) with
    | Sum.inl q => empGram m h x0 q.1 s q.2.1 q.2.2
    | Sum.inr q => empMom m h x0 q.1 s q.2) = _
  rw [(queryCoordEquiv d m).symm_apply_apply]

/-- The flattened empirical query is measurable in the dataset. -/
theorem measurable_qOf {d n : ℕ} (m : ℕ) (h : ℝ) (x0 : Fin d → ℝ) :
    Measurable (qOf (n := n) m h x0) := by
  rw [measurable_pi_iff]
  intro i
  unfold qOf
  split
  · exact (measurable_pi_iff.mp (measurable_pi_iff.mp (measurable_empGram m h x0 _) _) _)
  · exact measurable_pi_iff.mp (measurable_empMom m h x0 _) _

/-- The flattened query inherits the joint `ℓ¹` sensitivity bound. -/
theorem qOf_sensitivity {d n : ℕ} (m : ℕ) (h : ℝ) (x0 : Fin d → ℝ)
    (hn : 0 < n) (hh : 0 < h) (s s' : Fin n → CateObs d)
    (hadj : ReplacementAdjacent s s') :
    ∑ i, |qOf m h x0 s i - qOf m h x0 s' i| ≤
      Cs d m / ((n : ℝ) * h ^ (d : ℝ)) := by
  rw [← (queryCoordEquiv d m).sum_comp
    (fun i => |qOf m h x0 s i - qOf m h x0 s' i|), Fintype.sum_sum_type]
  simpa [queryCoordEquiv, queryCoordOf, Fintype.sum_prod_type,
    qOf_gramIdxOf, qOf_momIdxOf] using empQuery_sensitivity m h x0 hn hh s s' hadj

/-- The data-independent projected solve applied to a noisy flattened query vector. -/
noncomputable def postprocessOf (d m : ℕ) (cstar Cstar : ℝ)
    (v : Fin (Nq d m) → ℝ) : ℝ :=
  max (-2) (min 2
    ((((loewnerProj (pDim d m) cstar Cstar
          (Matrix.of (fun k l : Fin (pDim d m) => v (gramIdxOf d m 1 k l))))⁻¹.mulVec
        (fun k : Fin (pDim d m) => v (momIdxOf d m 1 k))) (icptOf d m)) -
    (((loewnerProj (pDim d m) cstar Cstar
          (Matrix.of (fun k l : Fin (pDim d m) => v (gramIdxOf d m 0 k l))))⁻¹.mulVec
        (fun k : Fin (pDim d m) => v (momIdxOf d m 0 k))) (icptOf d m))))

/-- The data-independent projected solve is measurable. -/
theorem measurable_postprocessOf (d m : ℕ) (cstar Cstar : ℝ) :
    Measurable (postprocessOf d m cstar Cstar) := by
  have hsolve (a : Fin 2) : Measurable (fun v : Fin (Nq d m) → ℝ =>
      ((loewnerProj (pDim d m) cstar Cstar
        (Matrix.of fun k l => v (gramIdxOf d m a k l)))⁻¹.mulVec
          (fun k => v (momIdxOf d m a k))) (icptOf d m)) := by
    have hG : Measurable (fun v : Fin (Nq d m) → ℝ =>
        Matrix.of fun k l => v (gramIdxOf d m a k l)) := by
      rw [measurable_matrix_iff]
      intro k l
      exact measurable_pi_apply (gramIdxOf d m a k l)
    have hv : Measurable (fun v : Fin (Nq d m) → ℝ =>
        fun k => v (momIdxOf d m a k)) := by
      rw [measurable_pi_iff]
      intro k
      exact measurable_pi_apply (momIdxOf d m a k)
    exact measurable_inv_mulVec_apply _ _
      ((measurable_loewnerProj (pDim d m) cstar Cstar).comp hG) hv (icptOf d m)
  unfold postprocessOf
  exact measurable_const.max (measurable_const.min ((hsolve 1).sub (hsolve 0)))

/-- Adding noise before the data-independent solve agrees with the original release. -/
theorem releaseOf_eq_postprocessOf_add_qOf {d n : ℕ} (m : ℕ) (h cstar Cstar : ℝ)
    (x0 : Fin d → ℝ) (s : Fin n → CateObs d) (w : Fin (Nq d m) → ℝ) :
    releaseOf m h cstar Cstar x0 s w =
      postprocessOf d m cstar Cstar (w + qOf m h x0 s) := by
  unfold releaseOf postprocessOf
  simp only [Pi.add_apply, qOf_gramIdxOf, qOf_momIdxOf]
  simp only [add_comm]

/-! ## Laplace calibration and central privacy -/

/-- The upper-bound scaffold's scalar Laplace kernel agrees with the reusable
Laplace-mechanism library measure. -/
theorem laplaceKernel_eq_laplaceMeasure (b : ℝ) :
    laplaceKernel b = laplaceMeasure b := by
  unfold laplaceKernel laplaceMeasure laplacePDF
  congr 2
  funext w
  rw [neg_div]

/-- The upper-bound scaffold's vector noise kernel is the product measure used by
the reusable finite-dimensional Laplace mechanism. -/
theorem laplaceVecKernel_eq_pi_laplaceMeasure (N : ℕ) (b : ℝ) :
    laplaceVecKernel N b = Measure.pi (fun _ : Fin N => laplaceMeasure b) := by
  unfold laplaceVecKernel
  congr 1
  funext i
  exact laplaceKernel_eq_laplaceMeasure b

/-- The concrete mechanism is a measurable data-independent post-processing of
the standard additive vector Laplace mechanism. -/
theorem mechOf_eq_laplaceMechPi_map {d n : ℕ} (m : ℕ) (h cstar Cstar epsN : ℝ)
    (x0 : Fin d → ℝ) (s : Fin n → CateObs d) :
    mechOf m h cstar Cstar epsN x0 s =
      (laplaceMechPi (((Cs d m) / ((n : ℝ) * h ^ (d : ℝ))) / epsN)
        (qOf m h x0) s).map (postprocessOf d m cstar Cstar) := by
  rw [mechOf, laplaceVecKernel_eq_pi_laplaceMeasure, laplaceMechPi,
    MeasureTheory.Measure.map_map (measurable_postprocessOf d m cstar Cstar)]
  · congr 1
    funext w
    exact releaseOf_eq_postprocessOf_add_qOf m h cstar Cstar x0 s w
  · fun_prop

private theorem measurable_parametrized_map {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure β) [SFinite μ] (f : α × β → γ) (hf : Measurable f) :
    Measurable (fun a : α => μ.map (fun b => f (a, b))) := by
  apply MeasureTheory.Measure.measurable_of_measurable_coe
  intro B hB
  have heq : (fun a : α => (μ.map fun b => f (a, b)) B) =
      fun a => ∫⁻ b, B.indicator (fun _ => (1 : ENNReal)) (f (a, b)) ∂μ := by
    funext a
    have hfa : Measurable (fun b => f (a, b)) :=
      hf.comp (measurable_const.prodMk measurable_id)
    rw [Measure.map_apply hfa hB]
    exact (lintegral_indicator_one (hB.preimage hfa)).symm
  rw [heq]
  exact ((measurable_const.indicator hB).comp hf).lintegral_prod_right'

/-- The explicit output-law mechanism is measurable as a Giry-valued map. -/
theorem measurable_mechOf {d n : ℕ} (m : ℕ) (h cstar Cstar epsN : ℝ)
    (x0 : Fin d → ℝ) :
    Measurable (mechOf (n := n) m h cstar Cstar epsN x0) := by
  unfold mechOf
  letI : SFinite (laplaceVecKernel (Nq d m)
      (Cs d m / ((n : ℝ) * h ^ (d : ℝ)) / epsN)) := by
    unfold laplaceVecKernel laplaceKernel
    infer_instance
  exact measurable_parametrized_map _
    (fun sw : (Fin n → CateObs d) × (Fin (Nq d m) → ℝ) =>
      releaseOf m h cstar Cstar x0 sw.1 sw.2)
    (measurable_releaseOf_joint m h cstar Cstar x0)

/-- The explicit mechanism is centrally `(epsN,delN)`-differentially private. -/
theorem mechOf_centralDP {d n : ℕ} (m : ℕ) (h cstar Cstar epsN delN : ℝ)
    (x0 : Fin d → ℝ) (hn : 0 < n) (hh : 0 < h) (heps : 0 < epsN)
    (hdel : 0 ≤ delN) :
    CentralDP n epsN delN (mechOf m h cstar Cstar epsN x0) := by
  let Δ : ℝ := Cs d m / ((n : ℝ) * h ^ (d : ℝ))
  have hCs : 0 < Cs d m := by
    unfold Cs
    have hp := pDim_pos d m
    positivity
  have hden : 0 < (n : ℝ) * h ^ (d : ℝ) := by
    exact mul_pos (Nat.cast_pos.mpr hn) (Real.rpow_pos_of_pos hh _)
  have hΔ : 0 < Δ := div_pos hCs hden
  have hb : 0 < Δ / epsN := div_pos hΔ heps
  constructor
  · intro s
    rw [mechOf_eq_laplaceMechPi_map]
    letI : IsProbabilityMeasure (laplaceMechPi (Δ / epsN) (qOf m h x0) s) :=
      laplaceMechPi_isProbabilityMeasure (Δ / epsN) hb (qOf m h x0) s
    exact Measure.isProbabilityMeasure_map
      (measurable_postprocessOf d m cstar Cstar).aemeasurable
  constructor
  · exact measurable_mechOf m h cstar Cstar epsN x0
  · intro s s' _hdata _hdata' hadj B hB
    rw [mechOf_eq_laplaceMechPi_map, mechOf_eq_laplaceMechPi_map]
    apply pure_dp_implies_approx_dp _ s s' epsN delN _ hdel B hB
    apply pure_dp_postprocess _ s s' epsN _ _
      (measurable_postprocessOf d m cstar Cstar)
    exact laplaceMechPi_pure_dp ReplacementAdjacent (qOf m h x0) hΔ heps
      (fun t t' ht => qOf_sensitivity m h x0 hn hh t t' ht) s s' hadj

end CausalSmith.Stat.DpCateMinimax
