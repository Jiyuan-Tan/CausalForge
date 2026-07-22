/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Liu–Hudgens (2014), Proposition 5.1: the primitive asymptotic-normality theorem

This file assembles the fully-primitive Proposition 5.1.  Under the homogeneity + regularity bundle
`Homogeneous` of `CLTDischarge`, the studentized treatment-minus-control direct-effect contrast is
asymptotically standard normal, with the conditional central limit theorem supplied directly by the
independent-summands CLT `prodDesign_clt` and the selection-mixture lifted by homogeneity — no CLT
is taken as a black box.

It provides the conditional CLT for the reference selection `condCLT_ref` (the application of
`prodDesign_clt` to the homogeneity-reduced per-coordinate summands) and the headline
`directEffect_clt_homogeneous` (the tower bridge plus the support-restricted mixture-lifting lemma
`tendsto_E_of_uniformBound_ae`).
-/

import Causalean.Experimentation.TwoStageInterference.Asymptotic.CLTDischarge

/-! # Primitive direct-contrast CLT

The primitive Liu-Hudgens treatment-minus-control direct-effect CLT follows from the
independent-summands product-design CLT.

The lemma `condCLT_ref` applies `prodDesign_clt` to the homogeneity-reduced per-coordinate summands
at the reference first-stage selection. The theorem `directEffect_clt_homogeneous` then uses
selection homogeneity and the support-restricted mixture-lifting lemma to prove that the joint
studentized direct-effect CDF converges to `stdNormalCdf t`.
-/

open scoped BigOperators Topology
open Finset Filter

namespace Causalean
namespace Experimentation
namespace TwoStageInterference

open DesignBased

variable {Exp : ℕ → LHExperiment} {t δ M : ℝ} {v : ℕ → ℝ}
  {stud : ∀ n, (StratAssign (Exp n).ι × ∀ i, Fin ((Exp n).gsize i) → Bool) → ℝ}

/-- **Conditional CLT for the reference selection.** Applying the independent-summands CLT
`prodDesign_clt` to the per-coordinate summands `gₛ₀,ᵢ` over the conditional product design gives
the conditional studentized CDF at the reference selection `refSel Exp n` converging to `Φ(t)`. -/
lemma condCLT_ref (h : Homogeneous Exp t stud δ M v) :
    Tendsto (fun n => (condDesign (Exp n) (refSel Exp n)).Pr
        (fun w => stud n (refSel Exp n, w) ≤ t)) atTop (𝓝 (stdNormalCdf t)) := by
  classical
  set s₀ : ∀ n, StratAssign (Exp n).ι := fun n => refSel Exp n with hs₀
  -- Coordinate designs and per-coordinate summands.
  set D : ∀ n, ∀ i : (Exp n).ι, FiniteDesign (Fin ((Exp n).gsize i) → Bool) :=
    fun n i => if s₀ n i then (Exp n).ψ i else (Exp n).φ i with hD
  set g : ∀ n, ∀ i : (Exp n).ι, (Fin ((Exp n).gsize i) → Bool) → ℝ :=
    fun n i => cltSummand n δ v (s₀ n) i with hg
  set B : ℕ → ℝ := fun n => M / Real.sqrt ((Exp n).C * v n) with hBdef
  -- Positivity facts.
  have hCpos : ∀ n, 0 < (Exp n).C := by
    intro n
    have := nonempty_of_refSel h n
    rcases lt_or_gt_of_ne (Exp n).hC with h0 | h0
    · exfalso
      have hnn : (0 : ℝ) ≤ ∑ i, if s₀ n i then (1 : ℝ) else 0 :=
        Finset.sum_nonneg (fun i _ => by positivity)
      rw [h.hcount n (s₀ n) (refSel_mem Exp n)] at hnn; linarith
    · exact h0
  have hsqrt : ∀ n, 0 < Real.sqrt ((Exp n).C * v n) :=
    fun n => Real.sqrt_pos.mpr (mul_pos (hCpos n) (h.hvpos n))
  -- `0 ≤ B n`.
  have hB : ∀ n, 0 ≤ B n := by
    intro n
    have := nonempty_of_refSel h n
    exact div_nonneg (M_nonneg_of_homogeneous h n) (hsqrt n).le
  -- Uniform bound `|g n i a| ≤ B n`.
  have hbound : ∀ n i a, |g n i a| ≤ B n := by
    intro n i a
    rw [hg, hBdef]
    change |cltSummand n δ v (s₀ n) i a| ≤ M / Real.sqrt ((Exp n).C * v n)
    unfold cltSummand
    rw [abs_div, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [div_le_div_iff_of_pos_right (hsqrt n)]
    calc |if s₀ n i then (1:ℝ) else 0| * |groupDiff (Exp n) i a - δ|
        ≤ 1 * |groupDiff (Exp n) i a - δ| := by
          apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
          by_cases hh : s₀ n i = true <;> simp [hh]
      _ = |groupDiff (Exp n) i a - δ| := one_mul _
      _ ≤ M := h.hMbound n i a
  -- Mean-zero summands.
  have hmean : ∀ n i, (D n i).E (g n i) = 0 := by
    intro n i
    change (if s₀ n i then (Exp n).ψ i else (Exp n).φ i).E (cltSummand n δ v (s₀ n) i) = 0
    rw [show cltSummand n δ v (s₀ n) i
          = (fun a => ((if s₀ n i then (1:ℝ) else 0) / Real.sqrt ((Exp n).C * v n))
              * (groupDiff (Exp n) i a - δ)) from funext fun a => by
            unfold cltSummand; ring]
    rw [FiniteDesign.E_const_mul]
    by_cases hh : s₀ n i = true
    · rw [if_pos hh, if_pos hh]
      have : ((Exp n).ψ i).E (fun a => groupDiff (Exp n) i a - δ) = 0 := by
        rw [FiniteDesign.E_sub, FiniteDesign.E_const, E_groupDiff_eq_of_homogeneous h, sub_self]
      rw [this, mul_zero]
    · rw [if_neg hh]; ring
  -- Unit total variance.
  have hvar : ∀ n, (prodDesign (D n)).Var (fun w => ∑ i, g n i (w i)) = 1 := by
    intro n
    have := nonempty_of_refSel h n
    -- Write `g n i a = c i * gtil i a`.
    set c : (Exp n).ι → ℝ :=
      fun i => (if s₀ n i then (1:ℝ) else 0) / Real.sqrt ((Exp n).C * v n) with hc
    set gtil : ∀ i : (Exp n).ι, (Fin ((Exp n).gsize i) → Bool) → ℝ :=
      fun i a => groupDiff (Exp n) i a - δ with hgtil
    rw [show (fun w : ∀ i, Fin ((Exp n).gsize i) → Bool => ∑ i, g n i (w i))
          = (fun w => ∑ i, c i * gtil i (w i)) from funext fun w => by
            refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [hg, hc, hgtil]; simp only [cltSummand]; ring]
    rw [FiniteDesign.Var_prod_linear_comb]
    -- Each term: `(c i)² · Var(gtil i) = if s₀ᵢ then v/(C·v) else 0`.
    have hterm : ∀ i, (c i) ^ 2 * (D n i).Var (gtil i)
        = (if s₀ n i then (1:ℝ) else 0) * (v n / ((Exp n).C * v n)) := by
      intro i
      change ((if s₀ n i then (1:ℝ) else 0) / Real.sqrt ((Exp n).C * v n)) ^ 2
          * (if s₀ n i then (Exp n).ψ i else (Exp n).φ i).Var
              (fun a => groupDiff (Exp n) i a - δ)
          = (if s₀ n i then (1:ℝ) else 0) * (v n / ((Exp n).C * v n))
      by_cases hh : s₀ n i = true
      · rw [if_pos hh, if_pos hh, FiniteDesign.Var_sub_const, h.hv n i]
        rw [div_pow, one_pow, Real.sq_sqrt (mul_pos (hCpos n) (h.hvpos n)).le, one_mul,
          one_div, inv_mul_eq_div]
      · rw [if_neg hh, if_neg hh]; simp
    rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.sum_mul,
      h.hcount n (s₀ n) (refSel_mem Exp n)]
    rw [mul_div_assoc', div_eq_one_iff_eq
      (mul_ne_zero (ne_of_gt (hCpos n)) (ne_of_gt (h.hvpos n)))]
  -- Assemble `prodDesign_clt`.
  have hclt := DesignBased.prodDesign_clt D g B hB h.hB0 hbound h.hNB3 hmean hvar t
  -- Rewrite the prelimit to the conditional studentized CDF.
  refine hclt.congr (fun n => ?_)
  rw [condDesign]
  congr 1
  funext w
  rw [stud_eq_sum_of_homogeneous h n (s₀ n) (refSel_mem Exp n) w]

open Classical in
/-- **Proposition 5.1 (Liu–Hudgens 2014), fully primitive.** Under the homogeneity + regularity
bundle `Homogeneous`, the studentized treatment-minus-control direct-effect contrast is
asymptotically standard normal: its joint-design CDF at `t` converges to `Φ(t)`.  No CLT is
assumed: the conditional CLT for the reference selection is `condCLT_ref` (from the
independent-summands CLT `prodDesign_clt`), the homogeneity hypothesis `hhom` lifts the uniform
bound across the stage-1 support, and the support-restricted mixture-lifting lemma
`tendsto_E_of_uniformBound_ae` averages it. -/
theorem directEffect_clt_homogeneous (h : Homogeneous Exp t stud δ M v) :
    Tendsto (fun n => (Exp n).jointD.Pr (fun sw => stud n sw ≤ t)) atTop
      (𝓝 (stdNormalCdf t)) := by
  -- Reference-selection conditional CDF and its distance to `Φ(t)`.
  set F : ∀ n, StratAssign (Exp n).ι → ℝ :=
    fun n s => (condDesign (Exp n) s).Pr (fun w => stud n (s, w) ≤ t) with hF
  set B : ℕ → ℝ := fun n => |F n (refSel Exp n) - stdNormalCdf t| with hBdef
  -- `B n → 0` since the reference conditional CDF converges to `Φ(t)`.
  have hB : Tendsto B atTop (𝓝 0) := by
    have hc := condCLT_ref h
    rw [tendsto_iff_norm_sub_tendsto_zero] at hc
    simpa only [hBdef, hF, Real.norm_eq_abs] using hc
  -- Rewrite each joint CDF as the stage-1 average of conditional CDFs.
  have hrw : ∀ n, (Exp n).jointD.Pr (fun sw => stud n sw ≤ t) = (Exp n).D₁.E (F n) := by
    intro n
    rw [LHExperiment.jointD, jointDesign, FiniteDesign.Pr_compound_eq_E_condPr]
    apply (Exp n).D₁.E_congr
    intro s
    rw [hF]
    rfl
  simp_rw [hrw]
  -- Average via the support-restricted mixture-lifting lemma.
  refine FiniteDesign.tendsto_E_of_uniformBound_ae (fun n => (Exp n).D₁) F (stdNormalCdf t) B
    (fun n s hs => ?_) hB
  -- On the support, `hhom` identifies `F n s` with `F n (refSel)`.
  simp only [hBdef, hF]
  rw [h.hhom n s (refSel Exp n) hs (refSel_mem Exp n)]


end TwoStageInterference
end Experimentation
end Causalean
