/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Star hull of a function class

The star hull of a function class `F : ι → 𝒳 → ℝ` around the origin is the
set of all rescalings `α • F i` with `α ∈ [0, 1]`. It is the standard
substrate for localized empirical-process arguments: the local Rademacher
complexity of `F` at radius `r` is dominated (up to a universal constant)
by the Rademacher complexity of `starHull F ∩ ball(0, r)`, which is
sub-root in `r`.

Reference:
* Bartlett, Bousquet, Mendelson, *Local Rademacher complexities*,
  Ann. Statist. 33 (2005) 1497–1537, Section 3.
-/

import Causalean.Stat.Concentration.Rademacher.Rademacher

/-! # Star Hulls of Function Classes

This file defines the star hull of a real-valued function class around the
origin and gives the parameterizations used in local empirical-process
arguments.

The set-level definition `starHull F` contains all functions `α • F i` with
`α ∈ [0, 1]`. Basic membership and congruence lemmas show that the original
class, the zero function, and every admissible rescaling lie in this hull.

For Rademacher-complexity arguments, `starHullParam ι` packages the rescaling
coefficient together with the original index, and `starHullEval F` evaluates
the associated function. The lemmas `starHullEval_mem_starHull`,
`starHullEval_one`, and `starHullEval_zero` connect this parameterized view
back to the set-level star hull. -/

namespace Causalean
namespace Stat
namespace Concentration

/-- The star hull of a function family `F : ι → 𝒳 → ℝ` around the origin.
    Each element is an `α`-rescaling of some `F i` for `α ∈ [0, 1]`. -/
def starHull {ι 𝒳 : Type*} (F : ι → 𝒳 → ℝ) : Set (𝒳 → ℝ) :=
  {f | ∃ (i : ι) (α : ℝ), 0 ≤ α ∧ α ≤ 1 ∧ f = α • F i}

/-- Each `F i` belongs to its own star hull (take `α = 1`). -/
lemma mem_starHull_self {ι 𝒳 : Type*} (F : ι → 𝒳 → ℝ) (i : ι) :
    F i ∈ starHull F := by
  refine ⟨i, 1, by norm_num, le_refl 1, ?_⟩
  simp

/-- The zero function belongs to the star hull of any nonempty family
    (take `α = 0`). -/
lemma zero_mem_starHull {ι 𝒳 : Type*} [Nonempty ι] (F : ι → 𝒳 → ℝ) :
    (fun _ : 𝒳 => (0 : ℝ)) ∈ starHull F := by
  refine ⟨Classical.arbitrary ι, 0, le_refl 0, by norm_num, ?_⟩
  ext x
  simp

/-- Pointwise-equal families have the same star hull. -/
lemma starHull_congr {ι 𝒳 : Type*} {F G : ι → 𝒳 → ℝ}
    (h : ∀ i x, F i x = G i x) : starHull F = starHull G := by
  have hFG : F = G := by
    funext i x
    exact h i x
  rw [hFG]

/-- An `α`-rescaling of `F i` with `α ∈ [0, 1]` lies in the star hull. -/
lemma starHull_smul_mem {ι 𝒳 : Type*} (F : ι → 𝒳 → ℝ) (i : ι)
    {α : ℝ} (h₀ : 0 ≤ α) (h₁ : α ≤ 1) :
    (α • F i) ∈ starHull F := by
  exact ⟨i, α, h₀, h₁, rfl⟩

/-- The star hull re-indexed as a `Type` (subtype carrier), suitable for
    the `ι`-parameter slot in `empiricalRademacherComplexity`,
    `rademacherComplexity`, etc.

    This older subtype index is retained for callers that work directly with
    the set-level hull. The `Type`-level parameterisation `starHullParam` (an
    `Icc (0:ℝ) 1 × ι` pair) is preferred for new local-complexity arguments
    because it keeps the original index explicit while adding a real rescaling
    parameter, and it admits clean monotonicity arguments through
    `starHullEval`. -/
noncomputable def starHullIndex {ι 𝒳 : Type*} (F : ι → 𝒳 → ℝ) : Type _ :=
  { f : 𝒳 → ℝ // f ∈ starHull F }

/-- **Star-hull parameter type.** A pair `(α, i)` with `α ∈ [0, 1]` and
    `i : ι` parameterises the star-hull element `α • F i`. This is the
    preferred index for downstream Rademacher-complexity arguments: it
    carries the multiplicative parameter explicitly, and monotonicity in
    `α` reduces to a per-coordinate scalar inequality. -/
def starHullParam (ι : Type*) : Type _ :=
  Set.Icc (0 : ℝ) 1 × ι

/-- The star-hull element associated to a parameter `(α, i)`: pointwise
    `α · F i x`. This is the "evaluation map" through which all
    star-hull arguments factor in the new `starHullParam` substrate. -/
def starHullEval {ι 𝒳 : Type*} (F : ι → 𝒳 → ℝ) :
    starHullParam ι → 𝒳 → ℝ :=
  fun p x => p.1.val * F p.2 x

/-- The evaluation map lands inside the (set-level) star hull. -/
lemma starHullEval_mem_starHull {ι 𝒳 : Type*} (F : ι → 𝒳 → ℝ)
    (p : starHullParam ι) : starHullEval F p ∈ starHull F := by
  refine ⟨p.2, p.1.val, p.1.property.1, p.1.property.2, ?_⟩
  funext x
  simp [starHullEval, smul_eq_mul]

/-- At parameter `(1, i)`, evaluation recovers `F i`. -/
lemma starHullEval_one {ι 𝒳 : Type*} (F : ι → 𝒳 → ℝ) (i : ι) :
    starHullEval F (⟨(1 : ℝ), by simp [Set.mem_Icc]⟩, i) = F i := by
  funext x
  simp [starHullEval]

/-- At parameter `(0, i)`, evaluation is the zero function. -/
lemma starHullEval_zero {ι 𝒳 : Type*} (F : ι → 𝒳 → ℝ) (i : ι) :
    starHullEval F (⟨(0 : ℝ), by simp [Set.mem_Icc]⟩, i) = fun _ => 0 := by
  funext x
  simp [starHullEval]

/-- `starHullParam` inherits `Nonempty` from its `ι` factor (the `[0,1]`
    factor is always nonempty). -/
instance starHullParam.instNonempty {ι : Type*} [Nonempty ι] :
    Nonempty (starHullParam ι) :=
  ⟨(⟨1, by simp [Set.mem_Icc]⟩, Classical.arbitrary ι)⟩

end Concentration
end Stat
end Causalean
