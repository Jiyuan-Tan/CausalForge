/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import CausalSmith.Experimentation.EXP_DesignPm1ExactnessBoundaryV1_Research.Basic
import CausalSmith.Experimentation.EXP_DesignPm1ExactnessBoundaryV1_Research.Helpers

/-! # Sharp cut-corner exactness (`thm:cut-corner-exactness`)

For `0 ≤ r < r_cut`, `X_cut = s_m s_mᵀ` is the unique minimizer of `F` over
`E_m^blk`, the implementability gap vanishes, and the cut design `P_cut ∈ P_m^sym`
attains the implementable optimum. -/

namespace CausalSmith.Experimentation.DesignPm1

open scoped BigOperators
open Causalean.Experimentation.DesignBased

-- @node: cutDesign_eq_cutVDesign
/-- The core `cutDesign` is the same two-point law as the vertex-design helper. -/
lemma cutDesign_eq_cutVDesign (m : ℕ) : cutDesign m = cutVDesign m := by
  unfold cutDesign cutVDesign uniformOnDesign
  congr
  funext z
  by_cases hsame : cutPlus m = cutMinus m
  · by_cases hz : z = cutMinus m
    · simp [hsame, hz]
      norm_num
    · simp [hsame, hz]
  · have hsame' : ¬ cutMinus m = cutPlus m := fun h => hsame h.symm
    by_cases hp : z = cutPlus m <;> by_cases hm : z = cutMinus m <;>
      simp [hp, hm, hsame, hsame']

-- @node: sInf_image_eq_of_minimizer
/-- If `x0` is a minimizer of `f` on `S`, then the infimum of the objective image is
`f x0`. -/
lemma sInf_image_eq_of_minimizer {α : Type*} (f : α → ℝ) (S : Set α) (x0 : α)
    (hx0 : x0 ∈ S) (hmin : ∀ x ∈ S, f x0 ≤ f x) :
    sInf (f '' S) = f x0 := by
  apply csInf_eq_of_forall_ge_of_forall_gt_exists_lt
  · exact ⟨f x0, ⟨x0, hx0, rfl⟩⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hmin x hx
  · intro w hw
    exact ⟨f x0, ⟨x0, hx0, rfl⟩, hw⟩

/-- The cut-exactness frontier
`r_cut(m,a,b,κ) = max 0 (min{2b(a+b)(1 − κ/(a−b)), 2b(2m−2b−κ)})`: the largest ratio up to
which `X_cut` stays optimal on the block-symmetric slice, taken as a nonnegative frontier
(`= 0` on the vacuous cells where the cut region is empty).
@realizes r_cut(m,a,b,kappa)(closed form min{2b(a+b)(1−κ/(a−b)), 2b(2m−2b−κ)}; the declared
[0,∞) space is PINNED BY CONSTRUCTION via the outer `max 0` clamp, so `r_cut ∈ [0,∞)` holds
unconditionally — not merely under the homophily regime. Given `0 ≤ r`, the consuming cut
region `r < r_cut` is equivalent to `r < min{…}`, so the clamp leaves `cut_corner_exactness`
unchanged in strength.)
@realizes kappa(carrier ℝ argument `kappa`; robustness weight entering both branches of the
cut frontier; range [0,∞) pinned by `0 ≤ kappa` on the consuming theorem `cut_corner_exactness`) -/
noncomputable def rCut (m : ℕ) (a b kappa : ℝ) : ℝ :=
  max 0 (min (2 * b * (a + b) * (1 - kappa / (a - b))) (2 * b * (2 * (m : ℝ) - 2 * b - kappa)))

/-- The low-robustness cut frontier `κ_cut(m,a,b) = max 0 (min{a−b, 2(m−b)})`: the largest
robustness weight below which the cut-exactness region `[0, r_cut(m,a,b,κ))` stays
nonempty, taken as a nonnegative frontier.
@realizes kappa_cut(m,a,b)(AUTHORITATIVE closed form min{a−b, 2(m−b)} clamped by an outer
`max 0`; the derived-phase [0,∞) space is PINNED BY CONSTRUCTION via that clamp, so
`κ_cut ∈ [0,∞)` holds unconditionally — `= 0` exactly on the vacuous cells where no
cut-exactness region persists (`a ≤ b` or `b ≥ m`), and `= min{a−b, 2(m−b)} > 0` under the
homophily regime with `b < m`. The range no longer depends on the regime holding.) -/
noncomputable def kappaCut (m : ℕ) (a b : ℝ) : ℝ := max 0 (min (a - b) (2 * ((m : ℝ) - b)))

-- @node: thm:cut-corner-exactness
/-- **Cut-corner exactness.** Under two-block homophily, for `0 ≤ r < r_cut(m,a,b,κ)`
the cut covariance `X_cut` is the unique minimizer of `F_{r,κ}` over `E_m^blk`; the
implementability gap is zero; `X_cut` is the unique minimizer over `C_m^pm`; and the
cut design `P_cut ∈ P_m^sym` realizes it with `X(P_cut) = X_cut`.
(The `ass:balanced-sign-design` atom is realized through membership in the
block-exchangeable class `C_m^pm`/`P_m^sym`, which bundles `BalancedDesignClass`.) -/
theorem cut_corner_exactness (m : ℕ) (a b r kappa : ℝ)
    (hHom : TwoBlockHomophily m a b)
    (hr0 : 0 ≤ r) -- @realizes r(range 0 ≤ r pins r ∈ [0,∞))
    (hk0 : 0 ≤ kappa) -- @realizes kappa(range 0 ≤ κ pins κ ∈ [0,∞), its definitional domain)
    (hr : r < rCut m a b kappa) : -- @realizes r_cut(m,a,b,kappa)(cut region r < r_cut)
    (cutCovariance m ∈ blockElliptope m a b ∧
      ∀ X ∈ blockElliptope m a b, X ≠ cutCovariance m →
        designObjective m a b r kappa (cutCovariance m) < designObjective m a b r kappa X) ∧
    implementabilityGap m a b r kappa = 0 ∧
    (cutCovariance m ∈ implementableCovarianceClass m ∧
      ∀ X ∈ implementableCovarianceClass m, X ≠ cutCovariance m →
        designObjective m a b r kappa (cutCovariance m) < designObjective m a b r kappa X) ∧
    cutDesign m ∈ blockExchangeableDesignClass m ∧
    assignmentSecondMoment m (cutDesign m) = cutCovariance m := by
  rcases hHom with ⟨hm, hba, hb⟩
  have hHom' : TwoBlockHomophily m a b := ⟨hm, hba, hb⟩
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < (m : ℝ) := by nlinarith
  have hm0 : (m : ℝ) ≠ 0 := ne_of_gt hmpos
  have hq : 0 < qParam m := by
    unfold qParam
    nlinarith
  have hdiff : 0 < a - b := by linarith
  have hsum : 0 < a + b := by linarith
  have hb2 : 0 < 2 * b := by positivity
  set A : ℝ := 2 * b * (a + b) * (1 - kappa / (a - b))
  set B : ℝ := 2 * b * (2 * (m : ℝ) - 2 * b - kappa)
  have hmin : r < min A B := by
    unfold rCut at hr
    by_cases hle : min A B ≤ 0
    · have hmax : max 0 (min A B) = 0 := max_eq_left hle
      linarith
    · have hmax : max 0 (min A B) = min A B :=
        max_eq_right (le_of_lt (lt_of_not_ge hle))
      simpa [A, B, hmax] using hr
  have hrA : r < A := lt_of_lt_of_le hmin (min_le_left A B)
  have hrB : r < B := lt_of_lt_of_le hmin (min_le_right A B)
  have h1 : cX m a b r / qParam m > cY b r + kappa := by
    unfold cX cY
    have hden : 0 < 2 * b * (a + b) := mul_pos hb2 hsum
    have hAdiv : r / (2 * b * (a + b)) < 1 - kappa / (a - b) := by
      rw [div_lt_iff₀ hden]
      nlinarith [hrA]
    have htarget' : kappa < (a - b) * (1 - r / (2 * b * (a + b))) := by
      have hmul := mul_lt_mul_of_pos_left hAdiv hdiff
      field_simp [ne_of_gt hdiff] at hmul ⊢
      nlinarith
    have hrepr : (a + b) + r / (a + b) - (2 * b + r / (2 * b) + kappa)
        = (a - b) * (1 - r / (2 * b * (a + b))) - kappa := by
      field_simp [ne_of_gt hb2, ne_of_gt hsum]
      ring
    have hcx : qParam m * (a + b + r / (a + b)) / qParam m
        = a + b + r / (a + b) := by
      field_simp [ne_of_gt hq]
    rw [hcx]
    nlinarith
  have h2 : cZ m > cY b r + kappa := by
    unfold cY cZ
    have hB' : r < 2 * b * (2 * (m : ℝ) - 2 * b - kappa) := by simpa [B] using hrB
    have htarget : 2 * b + r / (2 * b) + kappa < 2 * (m : ℝ) := by
      have hdiv : r / (2 * b) < 2 * (m : ℝ) - 2 * b - kappa := by
        rw [div_lt_iff₀ hb2]
        nlinarith [hB']
      nlinarith
    linarith
  have hcert := cut_vertex_certificate m (cX m a b r) (cY b r) (cZ m) kappa hq hk0 h1 h2
  have hspecCut := block_spectral_coordinates m a b r kappa 1 (-1) hHom'
  have hcutCoords := hspecCut.2.2.1.2
  have hxCut : (1 : ℝ) - 1 = 0 := congrArg Prod.fst hcutCoords
  have hyCut : 1 + ((m : ℝ) - 1) * (1 : ℝ) - (m : ℝ) * (-1 : ℝ) =
      2 * (m : ℝ) := congrArg (fun p : ℝ × ℝ × ℝ => p.2.1) hcutCoords
  have hzCut : 1 + ((m : ℝ) - 1) * (1 : ℝ) + (m : ℝ) * (-1 : ℝ) = 0 :=
    congrArg (fun p : ℝ × ℝ × ℝ => p.2.2) hcutCoords
  have hcutTriUV : InReducedTriangle m (1 - (1 : ℝ))
      (1 + ((m : ℝ) - 1) * (1 : ℝ) - (m : ℝ) * (-1 : ℝ))
      (1 + ((m : ℝ) - 1) * (1 : ℝ) + (m : ℝ) * (-1 : ℝ)) := by
    simpa [hxCut, hyCut, hzCut, two_mul] using hcert.1
  have hcutBlockMem : blockSymMatrix m 1 (-1) ∈ blockElliptope m a b := hspecCut.1.mpr hcutTriUV
  have hcutMem : cutCovariance m ∈ blockElliptope m a b := by
    rw [cutCovariance_eq_blockSym]
    exact hcutBlockMem
  have hcutObj : designObjective m a b r kappa (cutCovariance m) =
      reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa 0 (2 * (m : ℝ)) 0 := by
    rw [cutCovariance_eq_blockSym]
    simpa [hxCut, hyCut, hzCut, two_mul] using hspecCut.2.1
  have hrelStrict : ∀ X ∈ blockElliptope m a b, X ≠ cutCovariance m →
      designObjective m a b r kappa (cutCovariance m) < designObjective m a b r kappa X := by
    intro X hX hne
    rcases hX with ⟨u, v, rfl, hmem⟩
    have hspec := block_spectral_coordinates m a b r kappa u v hHom'
    have htri : InReducedTriangle m (1 - u)
        (1 + ((m : ℝ) - 1) * u - (m : ℝ) * v)
        (1 + ((m : ℝ) - 1) * u + (m : ℝ) * v) := by
      exact hspec.1.mp ⟨u, v, rfl, hmem⟩
    have hcoord_ne : ((1 - u,
        1 + ((m : ℝ) - 1) * u - (m : ℝ) * v,
        1 + ((m : ℝ) - 1) * u + (m : ℝ) * v) : ℝ × ℝ × ℝ) ≠
        (0, 2 * (m : ℝ), 0) := by
      intro hcoord
      have hx0 : 1 - u = 0 := congrArg Prod.fst hcoord
      have hz0 : 1 + ((m : ℝ) - 1) * u + (m : ℝ) * v = 0 :=
        congrArg (fun p : ℝ × ℝ × ℝ => p.2.2) hcoord
      have hu : u = 1 := by linarith
      have hv : v = -1 := by
        subst u
        have hmv : (m : ℝ) * (1 + v) = 0 := by nlinarith
        have hv1 : 1 + v = 0 := (mul_eq_zero.mp hmv).resolve_left hm0
        linarith
      apply hne
      rw [cutCovariance_eq_blockSym, hu, hv]
    calc
      designObjective m a b r kappa (cutCovariance m)
          = reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa
              0 (2 * (m : ℝ)) 0 := hcutObj
      _ < reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa
          (1 - u) (1 + ((m : ℝ) - 1) * u - (m : ℝ) * v)
          (1 + ((m : ℝ) - 1) * u + (m : ℝ) * v) := hcert.2 _ _ _ htri hcoord_ne
      _ = designObjective m a b r kappa (blockSymMatrix m u v) := hspec.2.1.symm
  have hcutD_eq : cutDesign m = cutVDesign m := cutDesign_eq_cutVDesign m
  have hcutDmem : cutDesign m ∈ blockExchangeableDesignClass m := by
    rw [hcutD_eq]
    exact cutVDesign_mem m
  have hcutSM : assignmentSecondMoment m (cutDesign m) = cutCovariance m := by
    rw [hcutD_eq, cutVDesign_secondMoment, ← cutCovariance_eq_blockSym]
  have hcutImp : cutCovariance m ∈ implementableCovarianceClass m :=
    ⟨cutDesign m, hcutDmem, hcutSM.symm⟩
  have himp_subset : implementableCovarianceClass m ⊆ blockElliptope m a b := by
    intro X hX
    rcases hX with ⟨D, hDmem, hXeq⟩
    rcases secondMoment_blockSym_of_exchangeable m hm D hDmem with ⟨u, v, hblock⟩
    rw [hXeq, hblock]
    have hslice := pm_slice_forward m hm u v D hblock
    have hspec := block_spectral_coordinates m a b r kappa u v hHom'
    exact hspec.1.mpr hslice.1
  have himpStrict : ∀ X ∈ implementableCovarianceClass m, X ≠ cutCovariance m →
      designObjective m a b r kappa (cutCovariance m) < designObjective m a b r kappa X := by
    intro X hX hne
    exact hrelStrict X (himp_subset hX) hne
  have hrelLe : ∀ X ∈ blockElliptope m a b,
      designObjective m a b r kappa (cutCovariance m) ≤ designObjective m a b r kappa X := by
    intro X hX
    by_cases hEq : X = cutCovariance m
    · subst X
      rfl
    · exact le_of_lt (hrelStrict X hX hEq)
  have himpLe : ∀ X ∈ implementableCovarianceClass m,
      designObjective m a b r kappa (cutCovariance m) ≤ designObjective m a b r kappa X := by
    intro X hX
    by_cases hEq : X = cutCovariance m
    · subst X
      rfl
    · exact le_of_lt (himpStrict X hX hEq)
  have hrelInf : sInf (designObjective m a b r kappa '' blockElliptope m a b) =
      designObjective m a b r kappa (cutCovariance m) :=
    sInf_image_eq_of_minimizer (designObjective m a b r kappa) (blockElliptope m a b)
      (cutCovariance m) hcutMem hrelLe
  have himpInf : sInf (designObjective m a b r kappa '' implementableCovarianceClass m) =
      designObjective m a b r kappa (cutCovariance m) :=
    sInf_image_eq_of_minimizer (designObjective m a b r kappa) (implementableCovarianceClass m)
      (cutCovariance m) hcutImp himpLe
  refine ⟨⟨hcutMem, hrelStrict⟩, ?_, ⟨⟨hcutImp, himpStrict⟩, hcutDmem, hcutSM⟩⟩
  unfold implementabilityGap
  rw [himpInf, hrelInf]
  ring

end CausalSmith.Experimentation.DesignPm1
