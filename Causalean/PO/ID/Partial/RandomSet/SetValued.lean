/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Compact-convex set-valued random variables and the Minkowski-mean support bridge

The general-`d` substrate for the Beresteanu–Molinari (2008) support-process CLT.
A set-valued random variable takes **body** values — nonempty compact convex
subsets of an inner-product space `E` (the class `𝒦ₖ(ℝᵈ)` of the paper).  On a
compact set the linear functional `⟪d, ·⟫` attains its supremum, so every support
function `supportFn (F ω) d` is well-defined.

The single load-bearing fact this file proves is the **Minkowski-mean support
bridge**

    supportFn ((1/|s|) • ∑_{i∈s} Fᵢ) d  =  (1/|s|) · ∑_{i∈s} supportFn (Fᵢ) d,

which turns the support value of an empirical Minkowski average `F̄ₙ` into an
ordinary sample mean of the scalar support values `s(p, Fᵢ)`.  This is exactly
what lets the multivariate CLT (`Stat/CLT`) fire on the support process — see
`SupportProcess.lean`.  Pure convex geometry: no probability, no atomlessness.

## Main definitions

* `IsBody C` — `C` is nonempty, compact and convex (the value type of an SVRV).
* `minkowskiMean s F` — the empirical Minkowski average `(1/|s|) • ∑_{i∈s} Fᵢ`.

## Main results

* `isBody_finsetSum` — a finite Minkowski sum of bodies is a body.
* `supportFn_finsetSum` — support function commutes with finite Minkowski sums.
* `supportFn_minkowskiMean` — **the keystone**: support of a Minkowski average is
  the average of supports.
-/

import Causalean.PO.ID.Partial.SupportFunction.Calculus
import Mathlib.Analysis.Convex.Topology

/-! # Set-Valued Random Variables and Minkowski Means

This file develops the convex-geometric substrate for random closed sets whose
values are nonempty compact convex subsets of an inner-product space. Its main
role in the library is to identify the support function of an empirical
Minkowski average with the ordinary average of scalar support functions.

Main declarations:
* `IsBody` records the nonempty compact convex value type for set-valued random
  variables.
* `isBody_finsetSum` shows that finite Minkowski sums preserve bodies.
* `supportFn_finsetSum` makes support functions commute with finite Minkowski
  sums.
* `minkowskiMean` and `supportFn_minkowskiMean` identify the support function
  of an empirical Minkowski average with the average of support functions.
-/

open scoped RealInnerProductSpace Pointwise

namespace Causalean.PartialID.RandomSet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A **body**: a nonempty, compact, convex subset of `E` — the value type
`𝒦ₖ(E)` of a Beresteanu–Molinari set-valued random variable.  Compactness makes
`supportFn C d` well-defined (the linear functional attains its sup); convexity is
what lets the support function characterise the set. -/
structure IsBody (C : Set E) : Prop where
  nonempty : C.Nonempty
  isCompact : IsCompact C
  convex : Convex ℝ C

/-- On a compact set the linear functional `⟪d, ·⟫` is bounded above. -/
lemma bddAbove_inner_image {C : Set E} (hC : IsCompact C) (d : E) :
    BddAbove ((fun x => ⟪d, x⟫) '' C) := by
  obtain ⟨R, hR⟩ := hC.isBounded.subset_closedBall (0 : E)
  refine ⟨‖d‖ * R, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hxR : ‖x‖ ≤ R := by simpa [Metric.mem_closedBall, dist_zero_right] using hR hx
  calc ⟪d, x⟫ ≤ ‖d‖ * ‖x‖ := real_inner_le_norm d x
    _ ≤ ‖d‖ * R := mul_le_mul_of_nonneg_left hxR (norm_nonneg d)

/-- The support function of a body is bounded above, hence meaningful. -/
lemma IsBody.bddAbove {C : Set E} (h : IsBody C) (d : E) :
    BddAbove ((fun x => ⟪d, x⟫) '' C) :=
  bddAbove_inner_image h.isCompact d

/-- A finite Minkowski sum of bodies is a body. -/
lemma isBody_finsetSum {ι : Type*} (s : Finset ι) (F : ι → Set E)
    (h : ∀ i ∈ s, IsBody (F i)) : IsBody (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction with
  | empty =>
      rw [Finset.sum_empty, ← Set.singleton_zero]
      exact ⟨Set.singleton_nonempty 0, isCompact_singleton, convex_singleton 0⟩
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      have ha := h a (Finset.mem_insert_self a s)
      have hr := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
      exact ⟨ha.nonempty.add hr.nonempty, ha.isCompact.add hr.isCompact,
        ha.convex.add hr.convex⟩

/-- **Support function commutes with finite Minkowski sums**:
`s(∑ᵢ Fᵢ, d) = ∑ᵢ s(Fᵢ, d)`. -/
theorem supportFn_finsetSum {ι : Type*} (s : Finset ι) (F : ι → Set E) (d : E)
    (h : ∀ i ∈ s, IsBody (F i)) :
    supportFn (∑ i ∈ s, F i) d = ∑ i ∈ s, supportFn (F i) d := by
  classical
  induction s using Finset.induction with
  | empty =>
      rw [Finset.sum_empty, Finset.sum_empty, ← Set.singleton_zero, supportFn,
        Set.image_singleton, inner_zero_right, csSup_singleton]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      have ha := h a (Finset.mem_insert_self a s)
      have hr := fun i hi => h i (Finset.mem_insert_of_mem hi)
      have hbody := isBody_finsetSum s F hr
      rw [supportFn_minkowski ha.nonempty hbody.nonempty (ha.bddAbove d)
        (hbody.bddAbove d), ih hr]

/-- The **empirical Minkowski average** `(1/|s|) • ∑_{i∈s} Fᵢ`. -/
noncomputable def minkowskiMean {ι : Type*} (s : Finset ι) (F : ι → Set E) : Set E :=
  (s.card : ℝ)⁻¹ • (∑ i ∈ s, F i)

/-- **Keystone — Minkowski-mean support bridge.**  The support function of an
empirical Minkowski average is the arithmetic average of the support functions:
`s(p, F̄ₙ) = (1/n) · ∑ᵢ s(p, Fᵢ)`.  This is the identity that turns the support
process into an ordinary sample mean, so the multivariate CLT applies. -/
theorem supportFn_minkowskiMean {ι : Type*} (s : Finset ι) (F : ι → Set E) (d : E)
    (h : ∀ i ∈ s, IsBody (F i)) :
    supportFn (minkowskiMean s F) d
      = (s.card : ℝ)⁻¹ * ∑ i ∈ s, supportFn (F i) d := by
  rw [minkowskiMean,
    supportFn_smul_set (by positivity) (isBody_finsetSum s F h).nonempty
      ((isBody_finsetSum s F h).bddAbove d),
    supportFn_finsetSum s F d h]

end Causalean.PartialID.RandomSet
