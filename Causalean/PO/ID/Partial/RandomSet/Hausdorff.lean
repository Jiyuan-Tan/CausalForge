/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Hausdorff distance and the support-function bridge (Beresteanu–Molinari keystone)

The inference theory of Beresteanu & Molinari (2008) rests on one geometric
identity (their equation (A.1), Hörmander's embedding): for compact convex sets
`A, B` in `ℝᵈ`,

    H(A, B) = sup_{‖p‖=1} | s(p, A) − s(p, B) |,

turning set distance into the sup-norm distance of support functions.  This file
builds the `d = 1` instance of that bridge — the only case the scalar
interval-data CLT (`IntervalCLT.lean`, Beresteanu–Molinari Theorems 3.1/3.2)
consumes — together with the underlying geometric fact

    H([a,b], [c,d]) = max(|a−c|, |b−d|),     dᴴ([a,b], [c,d]) = max((a−c)₊, (b−d)₊)?

(the directed version is recorded for the one-sided confidence regions).

## Main definitions

* `directedHausdorff A B` — the one-sided (directed) Hausdorff distance
  `sup_{a∈A} infDist a B`.
* `hausdorffDist A B` — the symmetric Hausdorff distance `max (dᴴ A B) (dᴴ B A)`.

## Main results

* `infDist_Icc` — distance from a point to an interval, `max 0 (max (c−x) (x−d))`.
* `directedHausdorff_Icc` — `dᴴ([a,b],[c,d]) = max 0 (max (c−a) (b−d))`.
* `hausdorffDist_Icc` — **the geometric keystone** `H([a,b],[c,d]) = max |a−c| |b−d|`.
-/

import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.InnerProductSpace.Basic

/-! # Hausdorff Distance for Intervals

This file develops the directed and symmetric Hausdorff distances needed for
scalar interval-valued identified sets. It proves the explicit formulas for
distances between compact real intervals that later connect interval inference
to support-function and central-limit-theorem arguments.

Main declarations:
* `directedHausdorff` and `hausdorffDist` define one-sided and symmetric
  Hausdorff distances in real-valued form.
* `infDist_Icc` computes the distance from a point to a closed real interval.
* `directedHausdorff_Icc` gives the directed interval formula.
* `hausdorffDist_Icc` gives the symmetric endpoint-gap formula
  `H([a,b],[c,d]) = max |a-c| |b-d|`.
-/

open Metric

namespace Causalean.PartialID.RandomSet

/-- **Directed (one-sided) Hausdorff distance** from `A` to `B`: the supremum over
points of `A` of their distance to `B`.  Real-valued (via `Metric.infDist`); on the
empty image `sSup` returns `0`. -/
noncomputable def directedHausdorff {α : Type*} [PseudoMetricSpace α]
    (A B : Set α) : ℝ :=
  sSup ((fun a => Metric.infDist a B) '' A)

/-- **Symmetric Hausdorff distance** `H(A,B) = max(dᴴ(A,B), dᴴ(B,A))`. -/
noncomputable def hausdorffDist {α : Type*} [PseudoMetricSpace α]
    (A B : Set α) : ℝ :=
  max (directedHausdorff A B) (directedHausdorff B A)

/-- **Distance from a real point to a closed interval.**  For `c ≤ d`,
`infDist x [c,d] = max 0 (max (c − x) (x − d))` — zero inside the interval, and the
signed gap to the nearer endpoint outside it. -/
theorem infDist_Icc {c d : ℝ} (hcd : c ≤ d) (x : ℝ) :
    Metric.infDist x (Set.Icc c d) = max 0 (max (c - x) (x - d)) := by
  refine le_antisymm ?_ ?_
  · -- the clamp point `p = max c (min x d) ∈ [c,d]` realises the upper bound
    set p : ℝ := max c (min x d) with hp
    have hpmem : p ∈ Set.Icc c d := by
      constructor
      · exact le_max_left _ _
      · exact max_le hcd (min_le_right _ _)
    have hle : Metric.infDist x (Set.Icc c d) ≤ dist x p :=
      Metric.infDist_le_dist_of_mem hpmem
    refine hle.trans ?_
    rw [Real.dist_eq]
    rcases le_total x c with hxc | hcx
    · -- x ≤ c ⇒ p = c, |x − c| = c − x
      have hmin : min x d = x := min_eq_left (hxc.trans hcd)
      have : p = c := by rw [hp, hmin]; exact max_eq_left hxc
      rw [this, abs_of_nonpos (by linarith)]
      have : c - x ≤ max (c - x) (x - d) := le_max_left _ _
      linarith [le_max_right (0 : ℝ) (max (c - x) (x - d))]
    · rcases le_total x d with hxd | hdx
      · -- c ≤ x ≤ d ⇒ p = x, distance 0
        have hmin : min x d = x := min_eq_left hxd
        have : p = x := by rw [hp, hmin]; exact max_eq_right hcx
        rw [this]; simp only [sub_self, abs_zero]
        exact le_max_left _ _
      · -- x ≥ d ⇒ p = d, |x − d| = x − d
        have hmin : min x d = d := min_eq_right hdx
        have : p = d := by rw [hp, hmin]; exact max_eq_right hcd
        rw [this, abs_of_nonneg (by linarith)]
        have : x - d ≤ max (c - x) (x - d) := le_max_right _ _
        linarith [le_max_right (0 : ℝ) (max (c - x) (x - d))]
  · -- lower bound: 0, c−x, x−d are each ≤ every point-to-point distance
    have hne_cd : (Set.Icc c d).Nonempty := ⟨c, ⟨le_rfl, hcd⟩⟩
    refine max_le (Metric.infDist_nonneg) (max_le ?_ ?_)
    · refine (Metric.le_infDist hne_cd).mpr ?_
      intro y hy
      rw [Real.dist_eq]
      have : c ≤ y := hy.1
      rcases le_total x y with h | h
      · rw [abs_of_nonpos (by linarith)]; linarith
      · rw [abs_of_nonneg (by linarith)]; linarith
    · refine (Metric.le_infDist hne_cd).mpr ?_
      intro y hy
      rw [Real.dist_eq]
      have : y ≤ d := hy.2
      rcases le_total x y with h | h
      · rw [abs_of_nonpos (by linarith)]; linarith
      · rw [abs_of_nonneg (by linarith)]; linarith

/-- The image whose `sSup` defines `directedHausdorff [a,b] [c,d]`, rewritten by
`infDist_Icc`. -/
private theorem image_infDist_Icc {a b c d : ℝ} (hcd : c ≤ d) :
    (fun x => Metric.infDist x (Set.Icc c d)) '' Set.Icc a b
      = (fun x => max 0 (max (c - x) (x - d))) '' Set.Icc a b := by
  apply Set.image_congr
  intro x _
  exact infDist_Icc hcd x

/-- **Directed Hausdorff distance between intervals.**
`dᴴ([a,b], [c,d]) = max 0 (max (c − a) (b − d))` (for `a ≤ b`, `c ≤ d`): the
worst over-reach of `[a,b]` beyond `[c,d]`, achieved at the endpoints. -/
theorem directedHausdorff_Icc {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    directedHausdorff (Set.Icc a b) (Set.Icc c d)
      = max 0 (max (c - a) (b - d)) := by
  unfold directedHausdorff
  rw [image_infDist_Icc hcd]
  set g : ℝ → ℝ := fun x => max 0 (max (c - x) (x - d)) with hg
  have hne : (g '' Set.Icc a b).Nonempty := ⟨g a, a, ⟨le_rfl, hab⟩, rfl⟩
  have hga : g a = max 0 (max (c - a) (a - d)) := rfl
  have hgb : g b = max 0 (max (c - b) (b - d)) := rfl
  -- upper bound on the image
  have hub : ∀ z ∈ g '' Set.Icc a b, z ≤ max 0 (max (c - a) (b - d)) := by
    rintro _ ⟨x, ⟨hax, hxb⟩, rfl⟩
    have h1 : c - x ≤ c - a := by linarith
    have h2 : x - d ≤ b - d := by linarith
    have hmax : max (c - x) (x - d) ≤ max (c - a) (b - d) := max_le_max h1 h2
    exact max_le_max (le_refl 0) hmax
  refine le_antisymm (csSup_le hne hub) ?_
  -- the target is ≤ sSup because it equals max (g a) (g b), both in the image
  have hbdd : BddAbove (g '' Set.Icc a b) := ⟨_, hub⟩
  have hsa : g a ≤ sSup (g '' Set.Icc a b) :=
    le_csSup hbdd ⟨a, ⟨le_rfl, hab⟩, rfl⟩
  have hsb : g b ≤ sSup (g '' Set.Icc a b) :=
    le_csSup hbdd ⟨b, ⟨hab, le_rfl⟩, rfl⟩
  -- max 0 (max (c−a) (b−d)) ≤ max (g a) (g b) ≤ sSup
  have h0a : (0 : ℝ) ≤ g a := by rw [hga]; exact le_max_left _ _
  have hca : c - a ≤ g a := by
    rw [hga]; exact le_trans (le_max_left _ _) (le_max_right 0 _)
  have hdb : b - d ≤ g b := by
    rw [hgb]; exact le_trans (le_max_right _ _) (le_max_right 0 _)
  have hmax_gg : max 0 (max (c - a) (b - d)) ≤ max (g a) (g b) := by
    refine max_le (le_trans h0a (le_max_left _ _)) (max_le ?_ ?_)
    · exact le_trans hca (le_max_left _ _)
    · exact le_trans hdb (le_max_right _ _)
  exact le_trans hmax_gg (max_le hsa hsb)

/-- **The geometric keystone (Beresteanu–Molinari eq. (A.1), `d = 1`).**  The
symmetric Hausdorff distance between two intervals is the larger of the endpoint
gaps: `H([a,b], [c,d]) = max(|a − c|, |b − d|)`. -/
theorem hausdorffDist_Icc {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    hausdorffDist (Set.Icc a b) (Set.Icc c d) = max |a - c| |b - d| := by
  unfold hausdorffDist
  rw [directedHausdorff_Icc hab hcd, directedHausdorff_Icc hcd hab]
  have hac1 : c - a ≤ |a - c| := by rw [abs_sub_comm]; exact le_abs_self _
  have hac2 : a - c ≤ |a - c| := le_abs_self _
  have hbd1 : b - d ≤ |b - d| := le_abs_self _
  have hbd2 : d - b ≤ |b - d| := by rw [abs_sub_comm]; exact le_abs_self _
  have h0ac : (0 : ℝ) ≤ |a - c| := abs_nonneg _
  have h0bd : (0 : ℝ) ≤ |b - d| := abs_nonneg _
  refine le_antisymm ?_ ?_
  · -- LHS ≤ RHS
    refine max_le
      (max_le (le_trans h0ac (le_max_left _ _))
        (max_le (le_trans hac1 (le_max_left _ _)) (le_trans hbd1 (le_max_right _ _))))
      (max_le (le_trans h0ac (le_max_left _ _))
        (max_le (le_trans hac2 (le_max_left _ _)) (le_trans hbd2 (le_max_right _ _))))
  · -- RHS ≤ LHS
    refine max_le ?_ ?_
    · -- |a − c| ≤ LHS
      rw [abs_le']
      refine ⟨?_, ?_⟩
      · exact le_trans (le_trans (le_max_left (a - c) (d - b)) (le_max_right 0 _))
          (le_max_right _ _)
      · rw [neg_sub]
        exact le_trans (le_trans (le_max_left (c - a) (b - d)) (le_max_right 0 _))
          (le_max_left _ _)
    · -- |b − d| ≤ LHS
      rw [abs_le']
      refine ⟨?_, ?_⟩
      · exact le_trans (le_trans (le_max_right (c - a) (b - d)) (le_max_right 0 _))
          (le_max_left _ _)
      · rw [neg_sub]
        exact le_trans (le_trans (le_max_right (a - c) (d - b)) (le_max_right 0 _))
          (le_max_right _ _)

end Causalean.PartialID.RandomSet
