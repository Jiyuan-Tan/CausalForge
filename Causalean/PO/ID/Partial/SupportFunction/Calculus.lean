/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Support-function calculus

The algebraic rules for `supportFn` (`PartialID/SupportFunction/Basic.lean`).
These let a downstream sharpness proof *compute* the endpoints of a composite
feasible set (unions of nuisance regimes, Minkowski sums of independent
uncertainty, scaled/translated reweighting classes) by reducing to support
functions of the pieces, rather than re-running a `csSup` argument each time.

All statements carry the `Nonempty`/`BddAbove` side conditions that the real
`sSup` requires; over compact feasible sets these are automatic
(`linearImage_eq_Icc_of_isCompact` in `Interval.lean`).

## Main results

* `supportFn_singleton` — support function of a point is the functional value.
* `supportFn_nonneg_of_zero_mem` — `0 ∈ C` forces a nonnegative support value.
* `supportFn_smul_dir` — positive homogeneity in the direction.
* `supportFn_add_dir_le` — subadditivity in the direction (sublinearity).
* `supportFn_mono` — monotone in the set.
* `supportFn_union` — support function of a union is the `max`.
* `supportFn_inter_le` — support function of an intersection is `≤` the `min`.
* `supportFn_translate` — translating the set shifts the support value.
* `supportFn_smul_set` — scaling the set by `a ≥ 0` scales the support value.
* `supportFn_minkowski` — additive over Minkowski sums.
-/

import Causalean.PO.ID.Partial.SupportFunction.Basic

/-! # Support-function calculus

This file proves algebraic rules for support functions of convex identified
sets: singleton evaluation, homogeneity, subadditivity, monotonicity, unions,
intersections, translations, scaling, and Minkowski sums. These rules let
downstream partial-identification proofs compute robust interval endpoints
compositionally.
-/

open scoped RealInnerProductSpace Pointwise

namespace Causalean
namespace PartialID

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Cluster A — direction algebra -/

/-- Support function of a singleton is the functional value at the point. -/
theorem supportFn_singleton (d x₀ : E) : supportFn ({x₀} : Set E) d = ⟪d, x₀⟫ := by
  unfold supportFn
  rw [Set.image_singleton, csSup_singleton]

/-- If `0 ∈ C` then the support value is nonnegative (the functional value `0`
at the origin is a lower bound for the sup). -/
theorem supportFn_nonneg_of_zero_mem {C : Set E} {d : E} (h0 : (0 : E) ∈ C)
    (hbdd : BddAbove ((fun x => ⟪d, x⟫) '' C)) :
    0 ≤ supportFn C d := by
  have h := le_supportFn (C := C) (d := d) h0 hbdd
  simpa using h

/-- **Positive homogeneity in the direction.**  For `t ≥ 0`,
`supportFn C (t • d) = t * supportFn C d`. -/
theorem supportFn_smul_dir {C : Set E} {d : E} {t : ℝ} (ht : 0 ≤ t)
    (hne : C.Nonempty) (hbdd : BddAbove ((fun x => ⟪d, x⟫) '' C)) :
    supportFn C (t • d) = t * supportFn C d := by
  rcases eq_or_lt_of_le ht with rfl | htpos
  · simp only [zero_smul, zero_mul]
    apply le_antisymm
    · refine supportFn_le hne ?_
      intro x _
      simp
    · obtain ⟨x, hx⟩ := hne
      have := le_supportFn (C := C) (d := (0 : E)) hx ?_
      · simpa using this
      · refine ⟨0, ?_⟩
        rintro _ ⟨y, _, rfl⟩
        simp
  · apply le_antisymm
    · refine supportFn_le hne ?_
      intro x hx
      rw [real_inner_smul_left]
      have : ⟪d, x⟫ ≤ supportFn C d := le_supportFn hx hbdd
      exact mul_le_mul_of_nonneg_left this ht
    · rw [mul_comm, ← le_div_iff₀ htpos]
      refine supportFn_le hne ?_
      intro x hx
      rw [le_div_iff₀ htpos]
      have hle : ⟪t • d, x⟫ ≤ supportFn C (t • d) := by
        refine le_supportFn hx ?_
        obtain ⟨b, hb⟩ := hbdd
        refine ⟨t * b, ?_⟩
        rintro _ ⟨y, hy, rfl⟩
        simp only [real_inner_smul_left]
        exact mul_le_mul_of_nonneg_left (hb (Set.mem_image_of_mem _ hy)) ht
      rw [real_inner_smul_left] at hle
      linarith [hle]

/-- **Subadditivity in the direction** (sublinearity of the support function):
`supportFn C (d₁ + d₂) ≤ supportFn C d₁ + supportFn C d₂`. -/
theorem supportFn_add_dir_le {C : Set E} {d₁ d₂ : E} (hne : C.Nonempty)
    (hb₁ : BddAbove ((fun x => ⟪d₁, x⟫) '' C))
    (hb₂ : BddAbove ((fun x => ⟪d₂, x⟫) '' C)) :
    supportFn C (d₁ + d₂) ≤ supportFn C d₁ + supportFn C d₂ := by
  refine supportFn_le hne ?_
  intro x hx
  rw [inner_add_left]
  have h₁ : ⟪d₁, x⟫ ≤ supportFn C d₁ := le_supportFn hx hb₁
  have h₂ : ⟪d₂, x⟫ ≤ supportFn C d₂ := le_supportFn hx hb₂
  linarith

/-! ### Cluster B — set algebra -/

/-- **Monotone in the set.**  If `C ⊆ D` (with `C` nonempty and the functional
bounded above on `D`), then `supportFn C d ≤ supportFn D d`. -/
theorem supportFn_mono {C D : Set E} {d : E} (hCD : C ⊆ D) (hne : C.Nonempty)
    (hbdd : BddAbove ((fun x => ⟪d, x⟫) '' D)) :
    supportFn C d ≤ supportFn D d := by
  refine supportFn_le hne (fun x hx => ?_)
  exact le_supportFn (hCD hx) hbdd

/-- **Union rule.**  The support function of a union is the maximum of the parts. -/
theorem supportFn_union {C D : Set E} {d : E} (hC : C.Nonempty) (hD : D.Nonempty)
    (hbC : BddAbove ((fun x => ⟪d, x⟫) '' C))
    (hbD : BddAbove ((fun x => ⟪d, x⟫) '' D)) :
    supportFn (C ∪ D) d = max (supportFn C d) (supportFn D d) := by
  have hbU : BddAbove ((fun x => ⟪d, x⟫) '' (C ∪ D)) := by
    rw [Set.image_union]; exact hbC.union hbD
  refine le_antisymm ?_ ?_
  · refine supportFn_le (hC.inl) (fun x hx => ?_)
    rcases hx with hx | hx
    · exact le_trans (le_supportFn hx hbC) (le_max_left _ _)
    · exact le_trans (le_supportFn hx hbD) (le_max_right _ _)
  · rw [max_le_iff]
    exact ⟨supportFn_mono Set.subset_union_left hC hbU,
           supportFn_mono Set.subset_union_right hD hbU⟩

/-- **Intersection rule (one-sided).**  The support function of an intersection is
at most the minimum of the parts. -/
theorem supportFn_inter_le {C D : Set E} {d : E} (hne : (C ∩ D).Nonempty)
    (hbC : BddAbove ((fun x => ⟪d, x⟫) '' C))
    (hbD : BddAbove ((fun x => ⟪d, x⟫) '' D)) :
    supportFn (C ∩ D) d ≤ min (supportFn C d) (supportFn D d) := by
  refine le_min ?_ ?_
  · exact supportFn_mono Set.inter_subset_left hne hbC
  · exact supportFn_mono Set.inter_subset_right hne hbD

/-- **Translation rule.**  Translating the set by `x₀` shifts the support value
by `⟪d, x₀⟫`. -/
theorem supportFn_translate {C : Set E} {d : E} (x₀ : E) (hne : C.Nonempty)
    (hbdd : BddAbove ((fun x => ⟪d, x⟫) '' C)) :
    supportFn ((fun x => x₀ + x) '' C) d = ⟪d, x₀⟫ + supportFn C d := by
  have hneT : ((fun x => x₀ + x) '' C).Nonempty := hne.image _
  have hbT : BddAbove ((fun x => ⟪d, x⟫) '' ((fun x => x₀ + x) '' C)) := by
    obtain ⟨b, hb⟩ := hbdd
    refine ⟨⟪d, x₀⟫ + b, ?_⟩
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    simp only [inner_add_right]
    have hx' : ⟪d, x⟫ ≤ b := hb ⟨x, hx, rfl⟩
    linarith
  refine le_antisymm ?_ ?_
  · refine supportFn_le hneT (fun y hy => ?_)
    obtain ⟨x, hx, rfl⟩ := hy
    simp only [inner_add_right]
    have := le_supportFn hx hbdd
    linarith
  · have : supportFn C d ≤ supportFn ((fun x => x₀ + x) '' C) d - ⟪d, x₀⟫ := by
      refine supportFn_le hne (fun x hx => ?_)
      have hmem : x₀ + x ∈ (fun x => x₀ + x) '' C := ⟨x, hx, rfl⟩
      have := le_supportFn hmem hbT
      rw [inner_add_right] at this
      linarith
    linarith

/-- **Positive scaling rule.**  Scaling the set by `a ≥ 0` scales the support
value by `a`. -/
theorem supportFn_smul_set {C : Set E} {d : E} {a : ℝ} (ha : 0 ≤ a)
    (hne : C.Nonempty) (hbdd : BddAbove ((fun x => ⟪d, x⟫) '' C)) :
    supportFn (a • C) d = a * supportFn C d := by
  have hsmul : (a • C : Set E) = (fun x => a • x) '' C := rfl
  rcases eq_or_lt_of_le ha with hz | hpos
  · -- a = 0: a • C = {0} over nonempty C
    subst hz
    obtain ⟨c, hc⟩ := hne
    have hset : ((0 : ℝ) • C : Set E) = {0} := by
      rw [hsmul]
      ext y
      simp only [Set.mem_image, zero_smul, Set.mem_singleton_iff]
      constructor
      · rintro ⟨x, _, rfl⟩; rfl
      · rintro rfl; exact ⟨c, hc, rfl⟩
    rw [hset, zero_mul, supportFn_eq_iSup_image, Set.image_singleton,
      inner_zero_right, csSup_singleton]
  · -- 0 < a
    have hneS : (a • C : Set E).Nonempty := by
      rw [hsmul]; exact hne.image _
    have hbS : BddAbove ((fun x => ⟪d, x⟫) '' (a • C : Set E)) := by
      obtain ⟨b, hb⟩ := hbdd
      refine ⟨a * b, ?_⟩
      rw [hsmul]
      rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      simp only [real_inner_smul_right]
      have hx' : ⟪d, x⟫ ≤ b := hb ⟨x, hx, rfl⟩
      exact mul_le_mul_of_nonneg_left hx' ha
    refine le_antisymm ?_ ?_
    · refine supportFn_le hneS (fun y hy => ?_)
      rw [hsmul] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      simp only [real_inner_smul_right]
      exact mul_le_mul_of_nonneg_left (le_supportFn hx hbdd) ha
    · have : supportFn C d ≤ a⁻¹ * supportFn (a • C : Set E) d := by
        refine supportFn_le hne (fun x hx => ?_)
        have hmem : a • x ∈ (a • C : Set E) := by
          rw [hsmul]; exact ⟨x, hx, rfl⟩
        have h1 := le_supportFn hmem hbS
        rw [real_inner_smul_right] at h1
        have := mul_le_mul_of_nonneg_left h1 (le_of_lt (inv_pos.mpr hpos))
        rwa [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hpos), one_mul] at this
      have h2 := mul_le_mul_of_nonneg_left this ha
      rwa [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hpos), one_mul] at h2

/-- **Minkowski additivity.**  The support function is additive over Minkowski
sums: `supportFn (C + D) d = supportFn C d + supportFn D d`. -/
theorem supportFn_minkowski {C D : Set E} {d : E} (hC : C.Nonempty) (hD : D.Nonempty)
    (hbC : BddAbove ((fun x => ⟪d, x⟫) '' C))
    (hbD : BddAbove ((fun x => ⟪d, x⟫) '' D)) :
    supportFn (C + D) d = supportFn C d + supportFn D d := by
  have hneS : (C + D).Nonempty := hC.add hD
  have hbS : BddAbove ((fun x => ⟪d, x⟫) '' (C + D)) := by
    refine ⟨supportFn C d + supportFn D d, ?_⟩
    rintro _ ⟨_, hy, rfl⟩
    obtain ⟨c, hc, e, he, rfl⟩ := hy
    simp only [inner_add_right]
    exact add_le_add (le_supportFn hc hbC) (le_supportFn he hbD)
  refine le_antisymm ?_ ?_
  · refine supportFn_le hneS (fun y hy => ?_)
    obtain ⟨c, hc, e, he, rfl⟩ := hy
    simp only [inner_add_right]
    exact add_le_add (le_supportFn hc hbC) (le_supportFn he hbD)
  · -- ≥ : for each c, ⟪d,c⟫ + supportFn D d ≤ supportFn (C+D) d
    have key : ∀ c ∈ C, ⟪d, c⟫ + supportFn D d ≤ supportFn (C + D) d := by
      intro c hc
      have : supportFn D d ≤ supportFn (C + D) d - ⟪d, c⟫ := by
        refine supportFn_le hD (fun e he => ?_)
        have hmem : c + e ∈ C + D := ⟨c, hc, e, he, rfl⟩
        have h1 := le_supportFn hmem hbS
        rw [inner_add_right] at h1
        linarith
      linarith
    have : supportFn C d ≤ supportFn (C + D) d - supportFn D d := by
      refine supportFn_le hC (fun c hc => ?_)
      have := key c hc
      linarith
    linarith

end PartialID
end Causalean
