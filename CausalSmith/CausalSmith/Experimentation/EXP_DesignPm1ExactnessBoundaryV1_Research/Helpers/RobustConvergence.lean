/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import CausalSmith.Experimentation.EXP_DesignPm1ExactnessBoundaryV1_Research.Helpers.RobustCorner
import CausalSmith.Experimentation.EXP_DesignPm1ExactnessBoundaryV1_Research.Helpers.SymRedMatrix
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

namespace CausalSmith.Experimentation.DesignPm1

open scoped BigOperators
open Filter Topology

-- @node: reduced_norm_sq_block_coords
/-- The reduced Frobenius square at `X(u,v)` is the identity square plus the two
off-diagonal block contributions. -/
lemma reduced_norm_sq_block_coords (m : ℕ) (u v : ℝ) :
    qParam m * (1 - u) ^ 2
        + (1 + ((m : ℝ) - 1) * u - (m : ℝ) * v) ^ 2
        + (1 + ((m : ℝ) - 1) * u + (m : ℝ) * v) ^ 2
      =
    (qParam m * 1 ^ 2 + 1 ^ 2 + 1 ^ 2)
        + NsameR m * u ^ 2 + NcrossR m * v ^ 2 := by
  unfold qParam NsameR NcrossR
  ring

-- @node: robust_minimizers_tendsto_identity_entries
/-- Any choice of relaxed minimizers converges entrywise to the identity as `κ → ∞`. -/
lemma robust_minimizers_tendsto_identity_entries (m : ℕ) (a b r : ℝ)
    (hHom : TwoBlockHomophily m a b) (hr0 : 0 ≤ r)
    (Xseq : ℝ → Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ)
    (hXseq : ∀ kappa : ℝ, 0 < kappa →
      Xseq kappa ∈ blockElliptope m a b ∧
        ∀ X ∈ blockElliptope m a b,
          designObjective m a b r kappa (Xseq kappa) ≤ designObjective m a b r kappa X) :
    ∀ i j, Tendsto (fun kappa => Xseq kappa i j) atTop
      (𝓝 ((1 : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ) i j)) := by
  classical
  rcases hHom with ⟨hm, hba, hb⟩
  have hHom' : TwoBlockHomophily m a b := ⟨hm, hba, hb⟩
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < (m : ℝ) := by nlinarith
  have hqpos : 0 < qParam m := by
    unfold qParam
    nlinarith
  have hcenterSq_pos : 0 < qParam m * 1 ^ 2 + (1 : ℝ) ^ 2 + (1 : ℝ) ^ 2 := by
    positivity
  have hqM : qParam m * 1 ^ 2 + (1 : ℝ) ^ 2 + (1 : ℝ) ^ 2 = 2 * (m : ℝ) := by
    unfold qParam
    ring
  have hsumpos : 0 < a + b := by nlinarith
  have hb2pos : 0 < 2 * b := by positivity
  have hcx_nonneg : 0 ≤ cX m a b r := by
    unfold cX
    have hrdiv : 0 ≤ r / (a + b) := div_nonneg hr0 (le_of_lt hsumpos)
    exact mul_nonneg (le_of_lt hqpos) (by nlinarith)
  have hcy_nonneg : 0 ≤ cY b r := by
    unfold cY
    have hrdiv : 0 ≤ r / (2 * b) := div_nonneg hr0 (le_of_lt hb2pos)
    nlinarith
  have hcz_nonneg : 0 ≤ cZ m := by
    unfold cZ
    nlinarith
  let centerSq : ℝ := qParam m * 1 ^ 2 + (1 : ℝ) ^ 2 + (1 : ℝ) ^ 2
  let centerNorm : ℝ := Real.sqrt centerSq
  let L : ℝ := cX m a b r + cY b r + cZ m
  have hIobj : ∀ kappa : ℝ,
      designObjective m a b r kappa (1 : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ)
        = L + kappa * centerNorm := by
    intro kappa
    calc
      designObjective m a b r kappa
          (1 : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ)
          = reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m)
              kappa 1 1 1 := identity_objective_eq_reduced_center m a b r kappa hHom'
      _ = L + kappa * centerNorm := by
            simp [reducedObjective, L, centerNorm, centerSq]
  intro i j
  by_cases hij : i = j
  · subst j
    rw [Metric.tendsto_nhds]
    intro ε hε
    refine Filter.eventually_atTop.2 ⟨(1 : ℝ), ?_⟩
    intro kappa hk
    have hkpos : 0 < kappa := by linarith
    rcases (hXseq kappa hkpos).1 with ⟨u, v, hXeq, _hmem⟩
    have hdist : dist (Xseq kappa i i)
        ((1 : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ) i i) = 0 := by
      simp [hXeq, blockSymMatrix]
    rw [hdist]
    exact hε
  · have hIentry : ((1 : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ) i j) = 0 := by
      simp [hij]
    by_cases hsame : decide (i.val < m) = decide (j.val < m)
    · rw [Metric.tendsto_nhds]
      intro ε hε
      let C : ℝ := NsameR m
      have hCpos : 0 < C := by
        dsimp [C, NsameR]
        nlinarith
      let δ : ℝ := Real.sqrt (centerSq + C * ε ^ 2) - centerNorm
      have hδpos : 0 < δ := by
        have hlt : centerSq < centerSq + C * ε ^ 2 := by
          have : 0 < C * ε ^ 2 := mul_pos hCpos (sq_pos_of_pos hε)
          linarith
        dsimp [δ, centerNorm]
        exact sub_pos.mpr (Real.sqrt_lt_sqrt (le_of_lt hcenterSq_pos) hlt)
      refine Filter.eventually_atTop.2 ⟨max (1 : ℝ) ((L + 1) / δ), ?_⟩
      intro kappa hklarge
      have hkpos : 0 < kappa := by
        have h1 : (1 : ℝ) ≤ kappa := le_trans (le_max_left _ _) hklarge
        linarith
      have hkδ_gt : L < kappa * δ := by
        have hkT : (L + 1) / δ ≤ kappa := le_trans (le_max_right _ _) hklarge
        have hmul := mul_le_mul_of_nonneg_right hkT (le_of_lt hδpos)
        have hdiv : ((L + 1) / δ) * δ = L + 1 := by
          field_simp [ne_of_gt hδpos]
        nlinarith
      by_contra hnotdist
      have habs : ε ≤ |Xseq kappa i j| := by
        have : ¬ |Xseq kappa i j| < ε := by
          simpa [Real.dist_eq, hIentry] using hnotdist
        exact le_of_not_gt this
      rcases (hXseq kappa hkpos).1 with ⟨u, v, hXeq, hmem⟩
      have hentry : Xseq kappa i j = u := by
        have hsameProp : i.val < m ↔ j.val < m := by
          simpa [decide_eq_decide] using hsame
        simp [hXeq, blockSymMatrix, hij, hsameProp]
      have hu_abs : ε ≤ |u| := by simpa [hentry] using habs
      have hu_sq : ε ^ 2 ≤ u ^ 2 := by
        exact (sq_le_sq.mpr (by simpa [abs_of_pos hε] using hu_abs))
      have hspec := block_spectral_coordinates m a b r kappa u v hHom'
      have htri : InReducedTriangle m (1 - u)
          (1 + ((m : ℝ) - 1) * u - (m : ℝ) * v)
          (1 + ((m : ℝ) - 1) * u + (m : ℝ) * v) :=
        hspec.1.mp ⟨u, v, rfl, hmem⟩
      rcases htri with ⟨hx, hy, hz, _hsum⟩
      have hlin_nonneg :
          0 ≤ cX m a b r * (1 - u)
            + cY b r * (1 + ((m : ℝ) - 1) * u - (m : ℝ) * v)
            + cZ m * (1 + ((m : ℝ) - 1) * u + (m : ℝ) * v) := by
        exact add_nonneg
          (add_nonneg (mul_nonneg hcx_nonneg hx) (mul_nonneg hcy_nonneg hy))
          (mul_nonneg hcz_nonneg hz)
      let normSq : ℝ := qParam m * (1 - u) ^ 2
        + (1 + ((m : ℝ) - 1) * u - (m : ℝ) * v) ^ 2
        + (1 + ((m : ℝ) - 1) * u + (m : ℝ) * v) ^ 2
      let normRed : ℝ := Real.sqrt normSq
      have hnormSq_eq :
          normSq = centerSq + NsameR m * u ^ 2 + NcrossR m * v ^ 2 := by
        simp [normSq, centerSq, reduced_norm_sq_block_coords]
      have hnorm_lower : centerNorm + δ ≤ normRed := by
        have hcross_nonneg : 0 ≤ NcrossR m * v ^ 2 := by
          dsimp [NcrossR]
          positivity
        have hsame_sq : C * ε ^ 2 ≤ NsameR m * u ^ 2 := by
          dsimp [C]
          exact mul_le_mul_of_nonneg_left hu_sq (le_of_lt hCpos)
        have hsq_le : centerSq + C * ε ^ 2 ≤ normSq := by
          rw [hnormSq_eq]
          dsimp [C] at hsame_sq ⊢
          linarith
        have hsqrt := Real.sqrt_le_sqrt hsq_le
        simpa [normRed, δ, centerNorm] using hsqrt
      have hobj_lower :
          kappa * normRed ≤ designObjective m a b r kappa (blockSymMatrix m u v) := by
        rw [hspec.2.1]
        change kappa * normRed ≤
          (cX m a b r * (1 - u)
            + cY b r * (1 + ((m : ℝ) - 1) * u - (m : ℝ) * v)
            + cZ m * (1 + ((m : ℝ) - 1) * u + (m : ℝ) * v)
            + kappa * normRed)
        exact le_add_of_nonneg_left hlin_nonneg
      have hleBlock : designObjective m a b r kappa (blockSymMatrix m u v)
          ≤ designObjective m a b r kappa
              (1 : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ) := by
        have hle := (hXseq kappa hkpos).2
          (1 : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ)
          (identity_mem_blockElliptope m a b hHom')
        rwa [hXeq] at hle
      have hmain : kappa * (centerNorm + δ) ≤ L + kappa * centerNorm := by
        calc
          kappa * (centerNorm + δ) ≤ kappa * normRed :=
            mul_le_mul_of_nonneg_left hnorm_lower (le_of_lt hkpos)
          _ ≤ designObjective m a b r kappa (blockSymMatrix m u v) := hobj_lower
          _ ≤ designObjective m a b r kappa
              (1 : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ) := hleBlock
          _ = L + kappa * centerNorm := hIobj kappa
      have hkδ_le : kappa * δ ≤ L := by
        have hmain' : kappa * centerNorm + kappa * δ ≤ L + kappa * centerNorm := by
          simpa [mul_add] using hmain
        linarith
      exact (not_lt_of_ge hkδ_le) hkδ_gt
    · rw [Metric.tendsto_nhds]
      intro ε hε
      let C : ℝ := NcrossR m
      have hCpos : 0 < C := by
        dsimp [C, NcrossR]
        nlinarith
      let δ : ℝ := Real.sqrt (centerSq + C * ε ^ 2) - centerNorm
      have hδpos : 0 < δ := by
        have hlt : centerSq < centerSq + C * ε ^ 2 := by
          have : 0 < C * ε ^ 2 := mul_pos hCpos (sq_pos_of_pos hε)
          linarith
        dsimp [δ, centerNorm]
        exact sub_pos.mpr (Real.sqrt_lt_sqrt (le_of_lt hcenterSq_pos) hlt)
      refine Filter.eventually_atTop.2 ⟨max (1 : ℝ) ((L + 1) / δ), ?_⟩
      intro kappa hklarge
      have hkpos : 0 < kappa := by
        have h1 : (1 : ℝ) ≤ kappa := le_trans (le_max_left _ _) hklarge
        linarith
      have hkδ_gt : L < kappa * δ := by
        have hkT : (L + 1) / δ ≤ kappa := le_trans (le_max_right _ _) hklarge
        have hmul := mul_le_mul_of_nonneg_right hkT (le_of_lt hδpos)
        have hdiv : ((L + 1) / δ) * δ = L + 1 := by
          field_simp [ne_of_gt hδpos]
        nlinarith
      by_contra hnotdist
      have habs : ε ≤ |Xseq kappa i j| := by
        have : ¬ |Xseq kappa i j| < ε := by
          simpa [Real.dist_eq, hIentry] using hnotdist
        exact le_of_not_gt this
      rcases (hXseq kappa hkpos).1 with ⟨u, v, hXeq, hmem⟩
      have hentry : Xseq kappa i j = v := by
        have hcrossProp : ¬ (i.val < m ↔ j.val < m) := by
          intro hprop
          exact hsame (by simpa [decide_eq_decide] using hprop)
        simp [hXeq, blockSymMatrix, hij, hcrossProp]
      have hv_abs : ε ≤ |v| := by simpa [hentry] using habs
      have hv_sq : ε ^ 2 ≤ v ^ 2 := by
        exact (sq_le_sq.mpr (by simpa [abs_of_pos hε] using hv_abs))
      have hspec := block_spectral_coordinates m a b r kappa u v hHom'
      have htri : InReducedTriangle m (1 - u)
          (1 + ((m : ℝ) - 1) * u - (m : ℝ) * v)
          (1 + ((m : ℝ) - 1) * u + (m : ℝ) * v) :=
        hspec.1.mp ⟨u, v, rfl, hmem⟩
      rcases htri with ⟨hx, hy, hz, _hsum⟩
      have hlin_nonneg :
          0 ≤ cX m a b r * (1 - u)
            + cY b r * (1 + ((m : ℝ) - 1) * u - (m : ℝ) * v)
            + cZ m * (1 + ((m : ℝ) - 1) * u + (m : ℝ) * v) := by
        exact add_nonneg
          (add_nonneg (mul_nonneg hcx_nonneg hx) (mul_nonneg hcy_nonneg hy))
          (mul_nonneg hcz_nonneg hz)
      let normSq : ℝ := qParam m * (1 - u) ^ 2
        + (1 + ((m : ℝ) - 1) * u - (m : ℝ) * v) ^ 2
        + (1 + ((m : ℝ) - 1) * u + (m : ℝ) * v) ^ 2
      let normRed : ℝ := Real.sqrt normSq
      have hnormSq_eq :
          normSq = centerSq + NsameR m * u ^ 2 + NcrossR m * v ^ 2 := by
        simp [normSq, centerSq, reduced_norm_sq_block_coords]
      have hnorm_lower : centerNorm + δ ≤ normRed := by
        have hsame_nonneg : 0 ≤ NsameR m * u ^ 2 := by
          have hNsame : 0 ≤ NsameR m := by
            dsimp [NsameR]
            nlinarith
          exact mul_nonneg hNsame (sq_nonneg u)
        have hcross_sq : C * ε ^ 2 ≤ NcrossR m * v ^ 2 := by
          dsimp [C]
          exact mul_le_mul_of_nonneg_left hv_sq (le_of_lt hCpos)
        have hsq_le : centerSq + C * ε ^ 2 ≤ normSq := by
          rw [hnormSq_eq]
          dsimp [C] at hcross_sq ⊢
          linarith
        have hsqrt := Real.sqrt_le_sqrt hsq_le
        simpa [normRed, δ, centerNorm] using hsqrt
      have hobj_lower :
          kappa * normRed ≤ designObjective m a b r kappa (blockSymMatrix m u v) := by
        rw [hspec.2.1]
        change kappa * normRed ≤
          (cX m a b r * (1 - u)
            + cY b r * (1 + ((m : ℝ) - 1) * u - (m : ℝ) * v)
            + cZ m * (1 + ((m : ℝ) - 1) * u + (m : ℝ) * v)
            + kappa * normRed)
        exact le_add_of_nonneg_left hlin_nonneg
      have hleBlock : designObjective m a b r kappa (blockSymMatrix m u v)
          ≤ designObjective m a b r kappa
              (1 : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ) := by
        have hle := (hXseq kappa hkpos).2
          (1 : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ)
          (identity_mem_blockElliptope m a b hHom')
        rwa [hXeq] at hle
      have hmain : kappa * (centerNorm + δ) ≤ L + kappa * centerNorm := by
        calc
          kappa * (centerNorm + δ) ≤ kappa * normRed :=
            mul_le_mul_of_nonneg_left hnorm_lower (le_of_lt hkpos)
          _ ≤ designObjective m a b r kappa (blockSymMatrix m u v) := hobj_lower
          _ ≤ designObjective m a b r kappa
              (1 : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ) := hleBlock
          _ = L + kappa * centerNorm := hIobj kappa
      have hkδ_le : kappa * δ ≤ L := by
        have hmain' : kappa * centerNorm + kappa * δ ≤ L + kappa * centerNorm := by
          simpa [mul_add] using hmain
        linarith
      exact (not_lt_of_ge hkδ_le) hkδ_gt

end CausalSmith.Experimentation.DesignPm1
