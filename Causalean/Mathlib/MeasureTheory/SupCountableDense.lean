/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Integrability of suprema over a countable-dense-skeletoned index class

A recurring pattern in localized empirical-process arguments is the need to show that a
supremum `ω ↦ sSup { F ω π : π ∈ S }` of a real process over an index class `S` is
measurable and integrable, when `S` carries a *countable dense skeleton* `D ⊆ S` (every
point of `S` is approached by a `D`-valued sequence along which the process converges) and
the process is uniformly bounded.

This file packages that pattern into a small, paper-agnostic API on an arbitrary measurable
space, so that individual empirical-process developments (policy-regret ERM suprema,
orthogonal-learning localized processes, set-valued support processes, …) reduce their
Bochner side conditions to a single invocation.

Main results:
* `sSup_image_eq_of_dense_tendsto` — for a real functional `F` bounded above on `S`, if
  every `x ∈ S` is reached by a `D`-valued sequence along which `F` converges to `F x`,
  then the supremum over `S` equals the supremum over the countable skeleton `D`.
* `measurable_sSup_image_of_countable_dense` — the pointwise supremum `ω ↦ sSup (F ω '' S)`
  is measurable, given a countable `D`, per-index measurability on `D`, and the skeleton
  supremum-equality for every `ω`.
* `integrable_sSup_image_of_countable_dense` — on a finite measure, the same supremum is
  integrable, given in addition a uniform bound `|F ω π| ≤ C` over `S`; the accompanying
  `bddAbove_image_of_bound` supplies the pointwise `BddAbove` fact for free.
-/

open MeasureTheory
open scoped BigOperators

namespace Causalean.Mathlib.MeasureTheory

/-- If `F` is bounded above on `S`, `D ⊆ S`, and every `x ∈ S` is the limit along a
`D`-valued sequence of `F`-values (`F (seq j) → F x`), then the supremum of `F` over `S`
coincides with the supremum over the countable skeleton `D`.  This is the density-side
input that turns a supremum over an uncountable class into a supremum over a countable
skeleton (used both for measurability and for evaluating the supremum). -/
theorem sSup_image_eq_of_dense_tendsto {ι : Type*} (F : ι → ℝ) (S D : Set ι)
    (hDS : D ⊆ S) (hbdd : BddAbove (F '' S))
    (hdense : ∀ x ∈ S, ∃ seq : ℕ → ι, (∀ j, seq j ∈ D) ∧
      Filter.Tendsto (fun j => F (seq j)) Filter.atTop (nhds (F x))) :
    sSup (F '' S) = sSup (F '' D) := by
  classical
  by_cases hS : S = ∅
  · have hD : D = ∅ := Set.eq_empty_of_subset_empty (by simpa [hS] using hDS)
    simp [hS, hD]
  · obtain ⟨x0, hx0⟩ := Set.nonempty_iff_ne_empty.mpr hS
    obtain ⟨seq, hseqD, _⟩ := hdense x0 hx0
    have hDne : D.Nonempty := ⟨seq 0, hseqD 0⟩
    have himageDne : (F '' D).Nonempty := hDne.image F
    have hbddD : BddAbove (F '' D) := hbdd.mono (Set.image_mono hDS)
    apply le_antisymm
    · refine csSup_le (Set.image_nonempty.mpr ⟨x0, hx0⟩) ?_
      rintro y ⟨x, hx, rfl⟩
      obtain ⟨seq, hseqD, htendsto⟩ := hdense x hx
      refine le_of_tendsto htendsto (Filter.Eventually.of_forall fun j => ?_)
      exact le_csSup hbddD ⟨seq j, hseqD j, rfl⟩
    · exact csSup_le_csSup hbdd himageDne (Set.image_mono hDS)

/-- The pointwise supremum `ω ↦ sSup ((F ω) '' S)` of a real process over an index class
`S` is measurable, provided `S` has a countable skeleton `D` on which the process is
measurable in `ω`, and the supremum over `S` agrees pointwise with the supremum over `D`.
Paper-agnostic generalization of the policy-class skeleton measurability step. -/
theorem measurable_sSup_image_of_countable_dense {Ω ι : Type*} [MeasurableSpace Ω]
    (S D : Set ι) (F : Ω → ι → ℝ)
    (hD : D.Countable)
    (hF : ∀ π ∈ D, Measurable (fun ω => F ω π))
    (heq : ∀ ω, sSup ((fun π => F ω π) '' S) = sSup ((fun π => F ω π) '' D)) :
    Measurable (fun ω => sSup ((fun π => F ω π) '' S)) := by
  classical
  letI : Countable D := hD.to_subtype
  have hsup :
      Measurable (fun ω : Ω => ⨆ π : D, F ω π.1) :=
    Measurable.iSup (fun π => hF π.1 π.2)
  convert hsup using 1
  ext ω
  rw [heq ω]
  have himage :
      ((fun π : ι => F ω π) '' D) =
        ((fun π : D => F ω π.1) '' Set.univ) := by
    ext y
    constructor
    · rintro ⟨π, hπ, rfl⟩
      exact ⟨⟨π, hπ⟩, Set.mem_univ _, rfl⟩
    · rintro ⟨π, _hπ, rfl⟩
      exact ⟨π.1, π.2, rfl⟩
  rw [himage]
  have huniv :
      ((fun π : D => F ω π.1) '' Set.univ) =
        Set.range (fun π : D => F ω π.1) := by
    ext y
    constructor
    · rintro ⟨π, _hπ, rfl⟩
      exact ⟨π, rfl⟩
    · rintro ⟨π, rfl⟩
      exact ⟨π, Set.mem_univ _, rfl⟩
  rw [huniv, sSup_range]

/-- A uniform absolute bound `|F ω π| ≤ C` over the index class `S` makes the image
`(F ω) '' S` bounded above (for every `ω`).  Companion `BddAbove` fact accompanying the
integrability lemma. -/
theorem bddAbove_image_of_bound {Ω ι : Type*} (S : Set ι) (F : Ω → ι → ℝ) (C : ℝ)
    (hbound : ∀ ω, ∀ π ∈ S, |F ω π| ≤ C) (ω : Ω) :
    BddAbove ((fun π => F ω π) '' S) := by
  exact bddAbove_def.mpr ⟨C, by
    rintro _ ⟨π, hπ, rfl⟩
    exact (le_abs_self _).trans (hbound ω π hπ)⟩

/-- On a finite measure, the pointwise supremum `ω ↦ sSup ((F ω) '' S)` over a
countable-dense-skeletoned index class is integrable, given per-index measurability on the
skeleton `D`, the skeleton supremum-equality, and a uniform bound `|F ω π| ≤ C` over `S`.
This is the entry point that discharges the Bochner side conditions of a localized
empirical-process supremum in one call. -/
theorem integrable_sSup_image_of_countable_dense {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (S D : Set ι) (F : Ω → ι → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hD : D.Countable)
    (hF : ∀ π ∈ D, Measurable (fun ω => F ω π))
    (heq : ∀ ω, sSup ((fun π => F ω π) '' S) = sSup ((fun π => F ω π) '' D))
    (hbound : ∀ ω, ∀ π ∈ S, |F ω π| ≤ C) :
    Integrable (fun ω => sSup ((fun π => F ω π) '' S)) μ := by
  have hmeas := measurable_sSup_image_of_countable_dense S D F hD hF heq
  refine Integrable.of_bound hmeas.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs]
  by_cases hne : ((fun π => F ω π) '' S).Nonempty
  · apply abs_le.mpr
    constructor
    · obtain ⟨y, hy⟩ := hne
      rcases hy with ⟨π, hπ, rfl⟩
      exact (abs_le.mp (hbound ω π hπ)).1.trans
        (le_csSup (bddAbove_image_of_bound S F C hbound ω) ⟨π, hπ, rfl⟩)
    · refine csSup_le hne fun y hy => ?_
      rcases hy with ⟨π, hπ, rfl⟩
      exact (abs_le.mp (hbound ω π hπ)).2
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, Real.sSup_empty]
    simpa using hC

end Causalean.Mathlib.MeasureTheory
