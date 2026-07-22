/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Convexity of a reciprocal product of positive coordinates

On a convex subset `s` of the coordinate space `ι → ℝ` on which the coordinates indexed by a finite
set `S` stay positive, the map `p ↦ (∏ k ∈ S, p k)⁻¹` is convex (`prod_inv_convexOn`). The proof is
the standard log–sum–exp argument: write the reciprocal product as `exp (∑ k ∈ S, -log (p k))`,
note each `-log (p k)` is convex (concavity of `log` precomposed with the coordinate projection),
sum, and compose with the convex, monotone `exp`.

The `1 - p k` mirror (`prod_one_sub_inv_convexOn`, under the hypothesis `p k < 1` on `S`) is proved
the same way and is the form a two-sided design objective needs. These are the reusable core of the
"variance-envelope objective is convex on the feasible box" fact, with the concrete feasible box
replaced by an arbitrary convex set plus coordinate positivity.
-/

open scoped BigOperators

namespace Causalean.Mathlib

variable {ι : Type*}

/-- `-log (p k)` is convex on a convex set `s` whose `k`-th coordinate is positive throughout. -/
lemma neg_log_coord_convexOn {s : Set (ι → ℝ)} (hs : Convex ℝ s) (k : ι)
    (hk : ∀ p ∈ s, 0 < p k) :
    ConvexOn ℝ s (fun p : ι → ℝ => -Real.log (p k)) := by
  let eval : (ι → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun p => p k
      map_add' := by intro x y; rfl
      map_smul' := by intro a x; rfl }
  have hneglog : ConvexOn ℝ (Set.Ioi (0 : ℝ)) (fun x : ℝ => -Real.log x) :=
    strictConcaveOn_log_Ioi.concaveOn.neg
  have hcomp : ConvexOn ℝ (eval ⁻¹' Set.Ioi (0 : ℝ)) (fun p : ι → ℝ => -Real.log (p k)) := by
    simpa [eval] using hneglog.comp_linearMap eval
  exact hcomp.subset (fun p hp => hk p hp) hs

/-- `∑ k ∈ S, -log (p k)` is convex on a convex set `s` whose coordinates indexed by `S` are
positive throughout. -/
lemma neg_log_sum_convexOn {s : Set (ι → ℝ)} (hs : Convex ℝ s) (S : Finset ι)
    (hS : ∀ p ∈ s, ∀ k ∈ S, 0 < p k) :
    ConvexOn ℝ s (fun p : ι → ℝ => ∑ k ∈ S, -Real.log (p k)) := by
  classical
  induction S using Finset.induction with
  | empty => simpa using convexOn_const (0 : ℝ) hs
  | @insert k T hk ih =>
      have hkpos : ∀ p ∈ s, 0 < p k := fun p hp => hS p hp k (Finset.mem_insert_self k T)
      have hTpos : ∀ p ∈ s, ∀ j ∈ T, 0 < p j :=
        fun p hp j hj => hS p hp j (Finset.mem_insert_of_mem hj)
      have hkconv := neg_log_coord_convexOn hs k hkpos
      simpa [Finset.sum_insert hk] using hkconv.add (ih hTpos)

/-- **Convexity of a reciprocal product.** On a convex set `s` whose coordinates indexed by `S`
stay positive, `p ↦ (∏ k ∈ S, p k)⁻¹` is convex. -/
lemma prod_inv_convexOn {s : Set (ι → ℝ)} (hs : Convex ℝ s) (S : Finset ι)
    (hS : ∀ p ∈ s, ∀ k ∈ S, 0 < p k) :
    ConvexOn ℝ s (fun p : ι → ℝ => (∏ k ∈ S, p k)⁻¹) := by
  classical
  rw [convexOn_iff_forall_pos]
  refine ⟨hs, ?_⟩
  intro x hx y hy a b ha hb hab
  let F : (ι → ℝ) → ℝ := fun p => ∑ k ∈ S, -Real.log (p k)
  have hFconv := neg_log_sum_convexOn hs S hS
  rw [convexOn_iff_forall_pos] at hFconv
  have hFineq := hFconv.2 hx hy ha hb hab
  have hprod_exp : ∀ p ∈ s, (∏ k ∈ S, p k)⁻¹ = Real.exp (F p) := by
    intro p hp
    calc
      (∏ k ∈ S, p k)⁻¹ = ∏ k ∈ S, (p k)⁻¹ := by rw [Finset.prod_inv_distrib]
      _ = ∏ k ∈ S, Real.exp (-Real.log (p k)) := by
        refine Finset.prod_congr rfl ?_
        intro k hk
        rw [Real.exp_neg, Real.exp_log (hS p hp k hk)]
      _ = Real.exp (F p) := by
        dsimp [F]
        exact (Real.exp_sum S (fun k => -Real.log (p k))).symm
  have hxy : (a • x + b • y) ∈ s := hs hx hy ha.le hb.le hab
  rw [hprod_exp (a • x + b • y) hxy, hprod_exp x hx, hprod_exp y hy]
  have hmono : Real.exp (F (a • x + b • y)) ≤ Real.exp (a * F x + b * F y) :=
    Real.exp_le_exp.mpr hFineq
  have hexpineq : Real.exp (a * F x + b * F y) ≤ a * Real.exp (F x) + b * Real.exp (F y) := by
    have hc := convexOn_exp.2 (Set.mem_univ (F x)) (Set.mem_univ (F y)) ha.le hb.le hab
    simpa [smul_eq_mul] using hc
  exact le_trans hmono hexpineq

/-- `-log (1 - p k)` is convex on a convex set `s` where the `k`-th coordinate stays below `1`. -/
lemma neg_log_one_sub_coord_convexOn {s : Set (ι → ℝ)} (hs : Convex ℝ s) (k : ι)
    (hk : ∀ p ∈ s, p k < 1) :
    ConvexOn ℝ s (fun p : ι → ℝ => -Real.log (1 - p k)) := by
  classical
  rw [convexOn_iff_forall_pos]
  refine ⟨hs, ?_⟩
  intro x hx y hy a b ha hb hab
  have hxpos : 0 < 1 - x k := by linarith [hk x hx]
  have hypos : 0 < 1 - y k := by linarith [hk y hy]
  have hneglog : ConvexOn ℝ (Set.Ioi (0 : ℝ)) (fun z : ℝ => -Real.log z) :=
    strictConcaveOn_log_Ioi.concaveOn.neg
  have hmain :=
    hneglog.2 (show 1 - x k ∈ Set.Ioi (0 : ℝ) from hxpos)
      (show 1 - y k ∈ Set.Ioi (0 : ℝ) from hypos) ha.le hb.le hab
  convert hmain using 1
  · simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    congr 1
    linarith

/-- `∑ k ∈ S, -log (1 - p k)` is convex on a convex set `s` where the coordinates indexed by `S`
stay below `1`. -/
lemma neg_log_one_sub_sum_convexOn {s : Set (ι → ℝ)} (hs : Convex ℝ s) (S : Finset ι)
    (hS : ∀ p ∈ s, ∀ k ∈ S, p k < 1) :
    ConvexOn ℝ s (fun p : ι → ℝ => ∑ k ∈ S, -Real.log (1 - p k)) := by
  classical
  induction S using Finset.induction with
  | empty => simpa using convexOn_const (0 : ℝ) hs
  | @insert k T hk ih =>
      have hklt : ∀ p ∈ s, p k < 1 := fun p hp => hS p hp k (Finset.mem_insert_self k T)
      have hTlt : ∀ p ∈ s, ∀ j ∈ T, p j < 1 :=
        fun p hp j hj => hS p hp j (Finset.mem_insert_of_mem hj)
      have hkconv := neg_log_one_sub_coord_convexOn hs k hklt
      simpa [Finset.sum_insert hk] using hkconv.add (ih hTlt)

/-- **Convexity of a reciprocal product of complements.** On a convex set `s` whose coordinates
indexed by `S` stay below `1`, `p ↦ (∏ k ∈ S, (1 - p k))⁻¹` is convex. -/
lemma prod_one_sub_inv_convexOn {s : Set (ι → ℝ)} (hs : Convex ℝ s) (S : Finset ι)
    (hS : ∀ p ∈ s, ∀ k ∈ S, p k < 1) :
    ConvexOn ℝ s (fun p : ι → ℝ => (∏ k ∈ S, (1 - p k))⁻¹) := by
  classical
  rw [convexOn_iff_forall_pos]
  refine ⟨hs, ?_⟩
  intro x hx y hy a b ha hb hab
  let F : (ι → ℝ) → ℝ := fun p => ∑ k ∈ S, -Real.log (1 - p k)
  have hFconv := neg_log_one_sub_sum_convexOn hs S hS
  rw [convexOn_iff_forall_pos] at hFconv
  have hFineq := hFconv.2 hx hy ha hb hab
  have hprod_exp : ∀ p ∈ s, (∏ k ∈ S, (1 - p k))⁻¹ = Real.exp (F p) := by
    intro p hp
    calc
      (∏ k ∈ S, (1 - p k))⁻¹ = ∏ k ∈ S, (1 - p k)⁻¹ := by rw [Finset.prod_inv_distrib]
      _ = ∏ k ∈ S, Real.exp (-Real.log (1 - p k)) := by
        refine Finset.prod_congr rfl ?_
        intro k hk
        rw [Real.exp_neg, Real.exp_log (by linarith [hS p hp k hk])]
      _ = Real.exp (F p) := by
        dsimp [F]
        exact (Real.exp_sum S (fun k => -Real.log (1 - p k))).symm
  have hxy : (a • x + b • y) ∈ s := hs hx hy ha.le hb.le hab
  rw [hprod_exp (a • x + b • y) hxy, hprod_exp x hx, hprod_exp y hy]
  have hmono : Real.exp (F (a • x + b • y)) ≤ Real.exp (a * F x + b * F y) :=
    Real.exp_le_exp.mpr hFineq
  have hexpineq : Real.exp (a * F x + b * F y) ≤ a * Real.exp (F x) + b * Real.exp (F y) := by
    have hc := convexOn_exp.2 (Set.mem_univ (F x)) (Set.mem_univ (F y)) ha.le hb.le hab
    simpa [smul_eq_mul] using hc
  exact le_trans hmono hexpineq

end Causalean.Mathlib
