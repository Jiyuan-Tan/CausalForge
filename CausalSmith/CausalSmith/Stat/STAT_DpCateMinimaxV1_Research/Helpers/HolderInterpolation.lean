/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Central-DP CATE minimax: Hölder pointwise → L¹ interpolation

Stage-2 scaffold. The gated kernel/Taylor moment-cancellation interpolation fact
`lem:holder_point_l1_interpolation`:
`∫_{C_*} |g| ≥ c_H · |g(x₀)|^{1 + d/γ}` for `g = τ_P - τ_Q` in the Hölder class,
in the STANDARD `⌈γ⌉-1` convention (degree `⌈γ⌉-1` Taylor polynomial with the
integer-order Lipschitz remainder). Direct analogue of the sibling
`DoseResponseMinimax.Helpers.Witness.{BumpHolder,HolderAux}` product-kernel
construction. It is registered substrate debt and therefore exposed as a `Prop`
definition to be supplied explicitly by each consumer.
-/

import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Causalean.Stat.Nonparametric.Approximation.HolderInterpolation

namespace CausalSmith.Stat.DpCateMinimax

open MeasureTheory

private lemma HolderBallStd_mono {d : ℕ} {f : (Fin d → ℝ) → ℝ}
    {order M : ℝ} {S T : Set (Fin d → ℝ)} (hST : S ⊆ T)
    (hf : HolderBallStd f order M T) : HolderBallStd f order M S := by
  refine ⟨hf.1.mono hST, ?_, ?_⟩
  · intro j hj x hx
    exact hf.2.1 j hj x (hST hx)
  · intro x hx y hy
    exact hf.2.2 x (hST hx) y (hST hy)

private lemma HolderBallStd_sub_open {d : ℕ} {f h : (Fin d → ℝ) → ℝ}
    {order L : ℝ} {S : Set (Fin d → ℝ)} (hS : IsOpen S)
    (hf : HolderBallStd f order L S) (hh : HolderBallStd h order L S) :
    HolderBallStd (fun x => f x - h x) order (2 * L) S := by
  refine ⟨hf.1.sub hh.1, ?_, ?_⟩
  · intro j hj x hx
    have hj' : (j : WithTop ℕ∞) ≤ (⌈order⌉₊ : WithTop ℕ∞) - 1 := by
      cases hq : ⌈order⌉₊ with
      | zero => simp_all
      | succ n =>
        have hjn : j ≤ n := by omega
        change ((j : ℕ∞) : WithTop ℕ∞) ≤
          ((n + 1 : ℕ∞) : WithTop ℕ∞) - ((1 : ℕ∞) : WithTop ℕ∞)
        rw [← WithTop.coe_sub]
        have henat : (n + 1 : ℕ∞) - 1 = n := by
          change (↑(n + 1) : ℕ∞) - ↑(1 : ℕ) = ↑n
          rw [← ENat.coe_sub]
          simp
        rw [henat]
        exact WithTop.coe_le_coe.mpr (ENat.coe_le_coe.mpr hjn)
    have hfa : ContDiffAt ℝ j f x :=
      (hf.1.of_le hj').contDiffAt (hS.mem_nhds hx)
    have hha : ContDiffAt ℝ j h x :=
      (hh.1.of_le hj').contDiffAt (hS.mem_nhds hx)
    change ‖iteratedFDeriv ℝ j (f - h) x‖ ≤ 2 * L
    rw [iteratedFDeriv_sub_apply hfa hha]
    calc
      ‖iteratedFDeriv ℝ j f x - iteratedFDeriv ℝ j h x‖
          ≤ ‖iteratedFDeriv ℝ j f x‖ + ‖iteratedFDeriv ℝ j h x‖ := norm_sub_le _ _
      _ ≤ L + L := add_le_add (hf.2.1 j hj x hx) (hh.2.1 j hj x hx)
      _ = 2 * L := by ring
  · intro x hx y hy
    let k := ⌈order⌉₊ - 1
    change ‖iteratedFDeriv ℝ k (f - h) x - iteratedFDeriv ℝ k (f - h) y‖ ≤
      (2 * L) * ‖x - y‖ ^ (order - ((k : ℕ) : ℝ))
    have hfx : ContDiffAt ℝ k f x := hf.1.contDiffAt (hS.mem_nhds hx)
    have hhx : ContDiffAt ℝ k h x := hh.1.contDiffAt (hS.mem_nhds hx)
    have hfy : ContDiffAt ℝ k f y := hf.1.contDiffAt (hS.mem_nhds hy)
    have hhy : ContDiffAt ℝ k h y := hh.1.contDiffAt (hS.mem_nhds hy)
    rw [iteratedFDeriv_sub_apply hfx hhx, iteratedFDeriv_sub_apply hfy hhy]
    calc
      ‖(iteratedFDeriv ℝ k f x - iteratedFDeriv ℝ k h x) -
          (iteratedFDeriv ℝ k f y - iteratedFDeriv ℝ k h y)‖ =
          ‖(iteratedFDeriv ℝ k f x - iteratedFDeriv ℝ k f y) -
            (iteratedFDeriv ℝ k h x - iteratedFDeriv ℝ k h y)‖ := by
              congr 1
              abel
      _ ≤ ‖iteratedFDeriv ℝ k f x - iteratedFDeriv ℝ k f y‖ +
          ‖iteratedFDeriv ℝ k h x - iteratedFDeriv ℝ k h y‖ := norm_sub_le _ _
      _ ≤ L * ‖x - y‖ ^ (order - ((k : ℕ) : ℝ)) +
          L * ‖x - y‖ ^ (order - ((k : ℕ) : ℝ)) :=
            add_le_add (hf.2.2 x hx y hy) (hh.2.2 x hx y hy)
      _ = (2 * L) * ‖x - y‖ ^ (order - (((⌈order⌉₊ - 1 : ℕ) : ℝ))) := by
            dsimp [k]
            ring

-- @node: lem:holder-point-l1-interpolation
/-- **Gated Hölder pointwise → L¹ interpolation input.** There is a constant `c_H > 0`
(depending only on the fixed regularity parameters `γ, d, L`, NOT on the pair
`P, Q`) such that for every pair of laws `P, Q` in the Hölder CATE class, writing
`g = τ_P - τ_Q` and `Δ = |g(x₀)|`, the L¹ mass of `g` on the interior cube
`C_* = {x : ‖x - x₀‖_∞ ≤ r_*}` satisfies
`∫_{C_*} |g(x)| dx ≥ c_H · Δ^{1 + d/γ}`. -/
def holder_point_l1_interpolation {d : ℕ}
    (alpha beta gamma L e0 f0 f1 r0 : ℝ) (x0 : Fin d → ℝ)
    (_hreg : RegimeConstants alpha beta gamma L e0 f0 f1 r0 x0) : Prop :=
    ∃ cH : ℝ, 0 < cH ∧ ∀ (P Q : CateLaw d),
      HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0 P →
      HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0 Q →
      cH * (|(P.mu1 x0 - P.mu0 x0) - (Q.mu1 x0 - Q.mu0 x0)|) ^ (1 + (d : ℝ) / gamma)
        ≤ ∫ x in supBall x0 (rStar r0 x0),
            |(P.mu1 x - P.mu0 x) - (Q.mu1 x - Q.mu0 x)|

/-- **Discharge of the Hölder pointwise → L¹ interpolation gate.** The gated `Prop`
`holder_point_l1_interpolation` is inhabited: it follows from the promoted generic
Tsybakov primitive `Causalean.Stat.Nonparametric.holder_point_l1_interpolation`.

The local `HolderBallStd`/`supBall` are byte-identical (definitionally equal) to the
Causalean ones, so the reduction is: (a) `supBall x0 (rStar r0 x0) ⊆ cube d` and a
strictly larger OPEN sub-cube `S'` with `supBall x0 (rStar r0 x0) ⊆ S' ⊆ cube d`;
(b) for `P, Q ∈ HolderCateClass`, `τ_P, τ_Q ∈ HolderBallStd γ L (cube d)`
(`.tauH`), so by monotonicity in the set they lie in `HolderBallStd γ L S'`, and on
the OPEN `S'` the global `iteratedFDeriv` agrees with `iteratedFDerivWithin S'`, so
`τ_P - τ_Q ∈ HolderBallStd γ (2L) S'`; (c) apply the promoted theorem with
`M = 2L`, `r = rStar r0 x0`, `S = S'`, and specialize its uniform constant `cH`. -/
theorem holder_point_l1_interpolation_holds {d : ℕ}
    (alpha beta gamma L e0 f0 f1 r0 : ℝ) (x0 : Fin d → ℝ)
    (hreg : RegimeConstants alpha beta gamma L e0 f0 f1 r0 x0) :
    holder_point_l1_interpolation alpha beta gamma L e0 f0 f1 r0 x0 hreg := by
  classical
  unfold holder_point_l1_interpolation
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · subst d
    refine ⟨1, by norm_num, ?_⟩
    intro P Q _ _
    have hball : supBall x0 (rStar r0 x0) = Set.univ := by
      ext x
      simp [supBall]
    rw [hball, setIntegral_univ, integral_unique]
    rw [Measure.volume_pi_eq_dirac (default : Fin 0 → ℝ)]
    simp [Real.rpow_one, Subsingleton.elim x0 default]
    have huniq (z : Fin 0 → ℝ) : z = x0 := Subsingleton.elim _ _
    simp only [huniq]
    exact le_refl
      (|P.mu1 x0 - P.mu0 x0 - (Q.mu1 x0 - Q.mu0 x0)| : ℝ)
  · rcases hreg with ⟨_halpha, _hbeta, hgamma, hL, _he0, _hf0,
        _hf01, hr0, hx0⟩
    let m : ℝ := ⨅ i : Fin d, min (x0 i) (1 - x0 i)
    let S : Set (Fin d → ℝ) :=
      {x | ∀ i, x i ∈ Set.Ioo (0 : ℝ) 1}
    haveI : Nonempty (Fin d) := ⟨⟨0, hdpos⟩⟩
    obtain ⟨imin, himin⟩ := Finite.exists_min
      (fun i : Fin d => min (x0 i) (1 - x0 i))
    have hm_eq : m = min (x0 imin) (1 - x0 imin) := by
      apply le_antisymm
      · exact ciInf_le (Finite.bddBelow_range _) imin
      · exact le_ciInf himin
    have hm_pos : 0 < m := by
      rw [hm_eq]
      exact lt_min (hx0 imin).1 (sub_pos.mpr (hx0 imin).2)
    have hrStar_pos : 0 < rStar r0 x0 := by
      rw [rStar]
      change 0 < (1 / 2 : ℝ) * min r0 m
      have hmin_pos : 0 < min r0 m := lt_min hr0.1 hm_pos
      positivity
    have hrStar_le (i : Fin d) :
        rStar r0 x0 ≤ (1 / 2 : ℝ) * min (x0 i) (1 - x0 i) := by
      have hm_le : m ≤ min (x0 i) (1 - x0 i) := by
        exact ciInf_le (Finite.bddBelow_range _) i
      rw [rStar]
      change (1 / 2 : ℝ) * min r0 m ≤
        (1 / 2 : ℝ) * min (x0 i) (1 - x0 i)
      exact mul_le_mul_of_nonneg_left ((min_le_right r0 m).trans hm_le) (by norm_num)
    have hSsub : supBall x0 (rStar r0 x0) ⊆ S := by
      intro x hx
      intro i
      have hm_i_pos : 0 < min (x0 i) (1 - x0 i) :=
        lt_min (hx0 i).1 (sub_pos.mpr (hx0 i).2)
      have hr_lt : rStar r0 x0 < min (x0 i) (1 - x0 i) := by
        have := hrStar_le i
        nlinarith
      have habs := abs_le.mp (hx i)
      constructor
      · have hri : rStar r0 x0 < x0 i :=
          hr_lt.trans_le (min_le_left _ _)
        linarith
      · have hri : rStar r0 x0 < 1 - x0 i :=
          hr_lt.trans_le (min_le_right _ _)
        linarith
    have hSopen : IsOpen S := by
      dsimp only [S]
      rw [show {x : Fin d → ℝ | ∀ i, x i ∈ Set.Ioo (0 : ℝ) 1} =
          ⋂ i : Fin d, (fun x : Fin d → ℝ => x i) ⁻¹' Set.Ioo 0 1 by
        ext x
        simp]
      exact isOpen_iInter_of_finite fun i =>
        (continuous_apply i).isOpen_preimage _ isOpen_Ioo
    obtain ⟨cH, hcH, hbound⟩ :=
      Causalean.Stat.Nonparametric.holder_point_l1_interpolation
        (γ := gamma) (M := 2 * L) (r := rStar r0 x0) (S := S)
        hgamma (by positivity) hrStar_pos hSsub
    refine ⟨cH, hcH, ?_⟩
    intro P Q hP hQ
    let tauP : (Fin d → ℝ) → ℝ := fun x => P.mu1 x - P.mu0 x
    let tauQ : (Fin d → ℝ) → ℝ := fun x => Q.mu1 x - Q.mu0 x
    let g : (Fin d → ℝ) → ℝ := fun x => tauP x - tauQ x
    have hScube : S ⊆ cube d := by
      intro x hx i
      exact ⟨(hx i).1.le, (hx i).2.le⟩
    have hP_S : HolderBallStd tauP gamma L S :=
      HolderBallStd_mono hScube hP.tauH
    have hQ_S : HolderBallStd tauQ gamma L S :=
      HolderBallStd_mono hScube hQ.tauH
    have hg : HolderBallStd g gamma (2 * L) S := by
      exact HolderBallStd_sub_open hSopen hP_S hQ_S
    exact hbound g hg

end CausalSmith.Stat.DpCateMinimax
