/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Basic
import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.Helpers.Witness.Core
import Mathlib.Analysis.Calculus.MeanValue

/-! # Uniform Hölder control of the localized CATE bump -/

namespace CausalSmith.Stat.DpCateMinimax

open MeasureTheory
open scoped Topology

noncomputable def causalCubeBump {d : ℕ} (u : Fin d → ℝ) : ℝ :=
  ∏ i : Fin d, CausalSmith.Stat.DoseResponseMinimax.doseBump (u i)

lemma causalCubeBump_contDiff {d : ℕ} :
    ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (causalCubeBump (d := d)) := by
  classical
  unfold causalCubeBump
  apply contDiff_prod
  intro i _
  have hb : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      CausalSmith.Stat.DoseResponseMinimax.doseBump := by
    simpa [CausalSmith.Stat.DoseResponseMinimax.doseBump] using
      CausalSmith.Stat.DoseResponseMinimax.doseContDiffBump.contDiff (n := ⊤)
  exact hb.comp (by fun_prop)

lemma causalCubeBump_zero {d : ℕ} : causalCubeBump (d := d) 0 = 1 := by
  classical
  simp [causalCubeBump, CausalSmith.Stat.DoseResponseMinimax.doseBump_zero]

lemma causalCubeBump_bounds {d : ℕ} (u : Fin d → ℝ) :
    0 ≤ causalCubeBump u ∧ causalCubeBump u ≤ 1 := by
  classical
  constructor
  · exact Finset.prod_nonneg fun i _ =>
      CausalSmith.Stat.DoseResponseMinimax.doseBump_nonneg (u i)
  · exact Finset.prod_le_one
      (fun i _ => CausalSmith.Stat.DoseResponseMinimax.doseBump_nonneg (u i))
      (fun i _ => CausalSmith.Stat.DoseResponseMinimax.doseBump_le_one (u i))

lemma causalCubeBump_support {d : ℕ} (u : Fin d → ℝ)
    (hu : ∃ j, 1 < |u j|) : causalCubeBump u = 0 := by
  classical
  rcases hu with ⟨j, hj⟩
  unfold causalCubeBump
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  exact CausalSmith.Stat.DoseResponseMinimax.doseBump_eq_zero_of_one_le_abs hj.le

lemma causalCubeBump_hasCompactSupport {d : ℕ} :
    HasCompactSupport (causalCubeBump (d := d)) := by
  let K : Set (Fin d → ℝ) := Set.Icc (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ))
  apply HasCompactSupport.intro (isCompact_Icc : IsCompact K)
  intro u hu
  have : ∃ j, 1 < |u j| := by
    by_contra h
    push_neg at h
    exact hu ⟨fun j => (abs_le.mp (h j)).1, fun j => (abs_le.mp (h j)).2⟩
  exact causalCubeBump_support u this

lemma causalCubeBump_deriv_bound {d : ℕ} (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : Fin d → ℝ,
      ‖iteratedFDeriv ℝ j (causalCubeBump (d := d)) u‖ ≤ C := by
  have hc : Continuous (iteratedFDeriv ℝ j (causalCubeBump (d := d))) :=
    ContDiff.continuous_iteratedFDeriv (WithTop.coe_le_coe.mpr le_top)
      (causalCubeBump_contDiff (d := d))
  rcases hc.bounded_above_of_compact_support
      ((causalCubeBump_hasCompactSupport (d := d)).iteratedFDeriv j) with ⟨C, hC⟩
  refine ⟨max C 0, le_max_right _ _, fun u => ?_⟩
  exact (hC u).trans (le_max_left _ _)

lemma causalCubeBump_deriv_holder {d : ℕ} (s : ℝ) (hs : 0 < s) :
    let k := ⌈s⌉₊ - 1
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u v : Fin d → ℝ,
      ‖iteratedFDeriv ℝ k (causalCubeBump (d := d)) u -
          iteratedFDeriv ℝ k causalCubeBump v‖ ≤ C * ‖u - v‖ ^ (s - (k : ℝ)) := by
  classical
  let k := ⌈s⌉₊ - 1
  have hceil : k + 1 = ⌈s⌉₊ := by
    dsimp [k]
    have : 0 < ⌈s⌉₊ := Nat.ceil_pos.mpr hs
    omega
  have hk_lt : (k : ℝ) < s := by
    rw [← Nat.lt_ceil]
    omega
  have hs_le : s ≤ (k : ℝ) + 1 := by
    calc
      s ≤ (⌈s⌉₊ : ℝ) := Nat.le_ceil s
      _ = (k : ℝ) + 1 := by rw [← hceil]; norm_num
  have hq0 : 0 ≤ s - (k : ℝ) := by linarith
  have hq1 : s - (k : ℝ) ≤ 1 := by linarith
  rcases causalCubeBump_deriv_bound (d := d) k with ⟨B0, hB0, h0⟩
  rcases causalCubeBump_deriv_bound (d := d) (k + 1) with ⟨B1, hB1, h1⟩
  let C := max B1 (2 * B0)
  refine ⟨C, hB1.trans (le_max_left _ _), ?_⟩
  intro u v
  have hlip : ‖iteratedFDeriv ℝ k causalCubeBump u -
        iteratedFDeriv ℝ k causalCubeBump v‖ ≤ B1 * ‖u - v‖ := by
    have hd : ∀ z ∈ (Set.univ : Set (Fin d → ℝ)),
        DifferentiableAt ℝ (iteratedFDeriv ℝ k (causalCubeBump (d := d))) z := by
      intro z _
      have hk0 : (k : ℕ∞) < (⊤ : ℕ∞) := WithTop.coe_lt_top k
      have hk : ((k : ℕ∞) : WithTop ℕ∞) <
          ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_lt_coe.mpr hk0
      exact (ContDiff.differentiable_iteratedFDeriv hk
        (causalCubeBump_contDiff (d := d))) z
    have hb : ∀ z ∈ (Set.univ : Set (Fin d → ℝ)),
        ‖fderiv ℝ (iteratedFDeriv ℝ k (causalCubeBump (d := d))) z‖ ≤ B1 := by
      intro z _
      rw [norm_fderiv_iteratedFDeriv]
      exact h1 z
    simpa [norm_sub_rev] using
      (convex_univ.norm_image_sub_le_of_norm_fderiv_le hd hb (Set.mem_univ v) (Set.mem_univ u))
  by_cases huv : ‖u - v‖ ≤ 1
  · calc
      ‖iteratedFDeriv ℝ k causalCubeBump u - iteratedFDeriv ℝ k causalCubeBump v‖
          ≤ B1 * ‖u - v‖ := hlip
      _ ≤ B1 * ‖u - v‖ ^ (s - (k : ℝ)) := by
        gcongr
        exact Real.self_le_rpow_of_le_one (norm_nonneg _) huv hq1
      _ ≤ C * ‖u - v‖ ^ (s - (k : ℝ)) := by
        gcongr
        exact le_max_left _ _
  · have huv1 : 1 ≤ ‖u - v‖ := le_of_not_ge huv
    calc
      ‖iteratedFDeriv ℝ k causalCubeBump u - iteratedFDeriv ℝ k causalCubeBump v‖
          ≤ 2 * B0 := by
            calc
              _ ≤ ‖iteratedFDeriv ℝ k causalCubeBump u‖ +
                    ‖iteratedFDeriv ℝ k causalCubeBump v‖ := norm_sub_le _ _
              _ ≤ B0 + B0 := add_le_add (h0 u) (h0 v)
              _ = 2 * B0 := by ring
      _ ≤ C := le_max_right _ _
      _ ≤ C * ‖u - v‖ ^ (s - (k : ℝ)) := by
        have := Real.one_le_rpow huv1 hq0
        nlinarith [hB1.trans (le_max_left B1 (2 * B0))]

end CausalSmith.Stat.DpCateMinimax
