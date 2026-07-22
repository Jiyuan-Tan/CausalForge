/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Ehlich–Zeller mesh norming: substrate gate and its oversampled consumer

`lem:ehlich-zeller-chebyshev-lobatto-mesh` (SUBSTRATE-GATE, gate_class gated) and
`lem:oversampled-chebyshev-lobatto-norming` (conditional consumer).
-/

import CausalSmith.Experimentation.EXP_RolloutChebyshevMinimax_Research.Basic
import Causalean.Mathlib.Analysis.EhlichZellerMesh.Mesh
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open scoped BigOperators

namespace CausalSmith.Experimentation.RolloutChebyshev

-- @node: lem:ehlich-zeller-chebyshev-lobatto-mesh
/-- **SUBSTRATE-GATE (gate_class: gated).** The Ehlich–Zeller Chebyshev-Lobatto mesh/norming
inequality (Ehlich, H. and Zeller, K. (1964). *Schwankung von Polynomen zwischen Gitterpunkten*.
Mathematische Zeitschrift 86, 41–44): for a real polynomial `R` of degree ≤ β with `β < k`,
`sup_{[-1,1]} |R| ≤ sec(π β / (2k)) · max_{0≤j≤k} |R(-cos(π j / k))|`.

This is a classical external approximation-theory norming (Marcinkiewicz–Zygmund-type) result,
absent from Mathlib and genuinely hard to formalize. It is NOT original to this paper (the paper
claims no new polynomial extremal theorem — honest scope) and its source proof is a bare
citation. It is stated as a named `Prop` and threaded as visible substrate debt into its single
direct consumer `oversampled_chebyshev_lobatto_norming`; to be discharged 0-sorry before banking. -/
def EhlichZellerMesh : Prop :=
  ∀ (beta k : ℕ) (R : Polynomial ℝ), R.natDegree ≤ beta → beta < k →
    ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 →
      |R.eval x| ≤ (1 / Real.cos (Real.pi * (beta : ℝ) / (2 * (k : ℝ)))) *
        Finset.univ.sup' Finset.univ_nonempty
          (fun j : Fin (k + 1) => |R.eval (-Real.cos (Real.pi * (j : ℝ) / (k : ℝ)))|)

-- @node: ehlichZellerMesh
/-- The local gate proposition is discharged by the reusable substrate implementation. -/
lemma ehlichZellerMesh : EhlichZellerMesh := by
  intro beta k R hdeg hlt x hx
  let nodeVal : ℕ → ℝ := fun j =>
    |R.eval (-Real.cos (Real.pi * (j : ℝ) / (k : ℝ)))|
  let finNodeVal : Fin (k + 1) → ℝ := fun j =>
    |R.eval (-Real.cos (Real.pi * (j : ℝ) / (k : ℝ)))|
  have hmesh_le :
      Causalean.Mathlib.Analysis.EhlichZellerMesh.czMeshMax R k ≤
        Finset.univ.sup' Finset.univ_nonempty finNodeVal := by
    unfold Causalean.Mathlib.Analysis.EhlichZellerMesh.czMeshMax
      Causalean.Mathlib.Analysis.EhlichZellerMesh.czNode
    have hnonneg0 : sSup (∅ : Set ℝ) ≤ nodeVal 0 := by
      simp [nodeVal]
    have hmem :
        (⨆ j ∈ Finset.range (k + 1), nodeVal j) ∈
          Finset.image nodeVal (Finset.range (k + 1)) :=
      Finset.ciSup_mem_image nodeVal ⟨0, by simp, hnonneg0⟩
    rcases Finset.mem_image.mp hmem with ⟨j, hj, hj_eq⟩
    change (⨆ j ∈ Finset.range (k + 1), nodeVal j) ≤
      Finset.univ.sup' Finset.univ_nonempty finNodeVal
    rw [← hj_eq]
    let jf : Fin (k + 1) := ⟨j, by simpa using hj⟩
    exact Finset.le_sup' (s := Finset.univ) (f := finNodeVal) (Finset.mem_univ jf)
  have hcoef_nonneg : 0 ≤ 1 / Real.cos (Real.pi * (beta : ℝ) / (2 * (k : ℝ))) := by
    have hk_nat : 0 < k := by omega
    have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk_nat
    have hbeta_lt : (beta : ℝ) < (k : ℝ) := by exact_mod_cast hlt
    have hangle_lt : Real.pi * (beta : ℝ) / (2 * (k : ℝ)) < Real.pi / 2 := by
      field_simp [ne_of_gt hk_pos]
      nlinarith [Real.pi_pos, hbeta_lt]
    exact one_div_nonneg.mpr
      (le_of_lt (Real.cos_pos_of_mem_Ioo ⟨by
        have hangle_nonneg : 0 ≤ Real.pi * (beta : ℝ) / (2 * (k : ℝ)) := by
          positivity
        linarith [hangle_nonneg, Real.pi_pos]
      , hangle_lt⟩))
  have hbdd : BddAbove ((fun x => |R.eval x|) '' Set.Icc (-1 : ℝ) 1) := by
    refine ⟨Causalean.Mathlib.Analysis.EhlichZellerMesh.czSup R, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    let t := Real.arccos (-x)
    have ht : t ∈ Set.Icc (0 : ℝ) Real.pi :=
      ⟨Real.arccos_nonneg (-x), Real.arccos_le_pi (-x)⟩
    have hcos : -Real.cos t = x := by
      have hx₁ : -1 ≤ -x := by linarith [hx.2]
      have hx₂ : -x ≤ 1 := by linarith [hx.1]
      simp [t, Real.cos_arccos hx₁ hx₂]
    simpa [Causalean.Mathlib.Analysis.EhlichZellerMesh.czTrig, hcos] using
      Causalean.Mathlib.Analysis.EhlichZellerMesh.abs_czTrig_le_czSup R ht
  have hpoint :
      |R.eval x| ≤ sSup ((fun x => |R.eval x|) '' Set.Icc (-1 : ℝ) 1) :=
    le_csSup hbdd ⟨x, hx, rfl⟩
  have hbound :=
    Causalean.Mathlib.Analysis.EhlichZellerMesh.ehlichZeller_mesh_bound R beta k hdeg hlt
  exact hpoint.trans
    (hbound.trans (mul_le_mul_of_nonneg_left hmesh_le hcoef_nonneg))

-- @node: lem:oversampled-chebyshev-lobatto-norming
/-- Gate consumer: for `c > 1`, there is a finite constant `K(c)` (namely `sec(π/(2c))`) such
that for every `β ≥ 1`, every integer `k ≥ c·β`, and every degree-≤β polynomial `R`,
`sup_{[-1,1]} |R| ≤ K(c) · max_{0≤j≤k} |R(-cos(π j / k))|`. Its only hard step is the gated
Ehlich–Zeller mesh inequality (threaded as `hmesh`); the rest is `sec` monotonicity from
`β/k ≤ 1/c`. Proved conditional on the gate. -/
lemma oversampled_chebyshev_lobatto_norming (hmesh : EhlichZellerMesh) (c : ℝ) (hc : 1 < c) :
    ∃ K : ℝ, 0 < K ∧ ∀ (beta k : ℕ) (R : Polynomial ℝ), 1 ≤ beta → (k : ℝ) ≥ c * beta →
      R.natDegree ≤ beta →
      ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 →
        |R.eval x| ≤ K * Finset.univ.sup' Finset.univ_nonempty
          (fun j : Fin (k + 1) => |R.eval (-Real.cos (Real.pi * (j : ℝ) / (k : ℝ)))|) := by
  let K : ℝ := 1 / Real.cos (Real.pi / (2 * c))
  refine ⟨K, ?_, ?_⟩
  · have hcpos : 0 < c := lt_trans zero_lt_one hc
    have hangle_pos : 0 < Real.pi / (2 * c) :=
      div_pos Real.pi_pos (mul_pos (by norm_num) hcpos)
    have hangle_lt : Real.pi / (2 * c) < Real.pi / 2 := by
      exact div_lt_div_of_pos_left Real.pi_pos (by norm_num) (by nlinarith [hc])
    exact one_div_pos.mpr (Real.cos_pos_of_mem_Ioo ⟨by linarith, hangle_lt⟩)
  · intro beta k R hbeta hkR hdeg x hx
    have hbeta_pos_nat : 0 < beta := by omega
    have hbeta_pos : 0 < (beta : ℝ) := by exact_mod_cast hbeta_pos_nat
    have hcpos : 0 < c := lt_trans zero_lt_one hc
    have hkpos : 0 < (k : ℝ) := by
      have hcbeta_pos : 0 < c * (beta : ℝ) := mul_pos hcpos hbeta_pos
      exact lt_of_lt_of_le hcbeta_pos hkR
    have hbeta_lt_k : beta < k := by
      have hbeta_lt_cbeta : (beta : ℝ) < c * (beta : ℝ) := by nlinarith [hc, hbeta_pos]
      have hbeta_lt_k_real : (beta : ℝ) < (k : ℝ) := lt_of_lt_of_le hbeta_lt_cbeta hkR
      exact_mod_cast hbeta_lt_k_real
    have hmesh_bound := hmesh beta k R hdeg hbeta_lt_k x hx
    have hratio : (beta : ℝ) / (k : ℝ) ≤ 1 / c := by
      rw [div_le_iff₀ hkpos]
      field_simp [ne_of_gt hcpos]
      nlinarith [hkR]
    have hangle_le : Real.pi * (beta : ℝ) / (2 * (k : ℝ)) ≤ Real.pi / (2 * c) := by
      calc
        Real.pi * (beta : ℝ) / (2 * (k : ℝ))
            = (Real.pi / 2) * ((beta : ℝ) / (k : ℝ)) := by
              field_simp [ne_of_gt hkpos]
        _ ≤ (Real.pi / 2) * (1 / c) := by
              exact mul_le_mul_of_nonneg_left hratio (by positivity)
        _ = Real.pi / (2 * c) := by
              field_simp [ne_of_gt hcpos]
    have hangleA_nonneg : 0 ≤ Real.pi * (beta : ℝ) / (2 * (k : ℝ)) := by positivity
    have hangleB_le_pi : Real.pi / (2 * c) ≤ Real.pi := by
      rw [div_le_iff₀ (mul_pos (by norm_num) hcpos)]
      nlinarith [Real.pi_pos, hc]
    have hcos_le : Real.cos (Real.pi / (2 * c)) ≤
        Real.cos (Real.pi * (beta : ℝ) / (2 * (k : ℝ))) :=
      Real.cos_le_cos_of_nonneg_of_le_pi hangleA_nonneg hangleB_le_pi hangle_le
    have hangleB_lt : Real.pi / (2 * c) < Real.pi / 2 := by
      exact div_lt_div_of_pos_left Real.pi_pos (by norm_num) (by nlinarith [hc])
    have hangleB_pos : 0 < Real.pi / (2 * c) :=
      div_pos Real.pi_pos (mul_pos (by norm_num) hcpos)
    have hcosB_pos : 0 < Real.cos (Real.pi / (2 * c)) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith, hangleB_lt⟩
    have hcoef_le : 1 / Real.cos (Real.pi * (beta : ℝ) / (2 * (k : ℝ))) ≤ K := by
      dsimp [K]
      exact one_div_le_one_div_of_le hcosB_pos hcos_le
    have hsup_nonneg : 0 ≤ Finset.univ.sup' Finset.univ_nonempty
          (fun j : Fin (k + 1) => |R.eval (-Real.cos (Real.pi * (j : ℝ) / (k : ℝ)))|) := by
      let j0 : Fin (k + 1) := 0
      exact (abs_nonneg _).trans
        (Finset.le_sup' (s := Finset.univ)
          (f := fun j : Fin (k + 1) =>
            |R.eval (-Real.cos (Real.pi * (j : ℝ) / (k : ℝ)))|)
          (Finset.mem_univ j0))
    exact hmesh_bound.trans (mul_le_mul_of_nonneg_right hcoef_le hsup_nonneg)

end CausalSmith.Experimentation.RolloutChebyshev
