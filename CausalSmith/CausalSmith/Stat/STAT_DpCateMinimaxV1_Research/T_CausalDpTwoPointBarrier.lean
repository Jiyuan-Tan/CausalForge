/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Central-DP CATE minimax: the headline two-point / TV-contraction barrier

Stage-2 scaffold. The headline crux T-block
`thm:causal_dp_two_point_barrier` — the primary causal-privacy PROOF-METHOD
hardness result. Two parts: (i) an arbitrary-pair TV lower bound
`TV(P,Q) ≥ c_TV·|τ_P(x₀)-τ_Q(x₀)|^{1+d/γ}` over the frozen class (arm-disintegration
finite-measure inequality + `holder_point_l1_interpolation`); (ii) the DP two-point
obstruction via `dp_output_tv_contraction`: any two-point argument certifying
indistinguishability through `n{exp(ε_n)-1+δ_n}TV(P,Q) ≤ η < 1` forces
`Δ ≤ C_η(n ε_n)^{-γ/(γ+d)}` — so it cannot reach the larger formal `q = α+β` branch
when `q < γ` and `n ε_n > 1`.

This is a proof-METHOD hardness theorem about the ordinary two-point/TV-contraction
route ONLY; it is NOT an impossibility claim (for fuzzy mixtures, hypercubes, or
other private comparison inequalities) and NOT a minimax converse.
-/

import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Basic
import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.ArmDisintegrationTV
import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.DpContraction
import CausalSmith.Stat.STAT_DpCateMinimaxV1_Research.Helpers.HolderInterpolation
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace CausalSmith.Stat.DpCateMinimax

open MeasureTheory
open Causalean.Stat

private lemma separation_le_privacy_rate {d : ℕ}
    {gamma cTV eta neps b tv Delta : ℝ}
    (hgamma : 0 < gamma) (hcTV : 0 < cTV) (heta : 0 < eta)
    (hneps : 0 < neps) (hb : neps ≤ b)
    (hpoint : cTV * Delta ^ (1 + (d : ℝ) / gamma) ≤ tv)
    (hcert : b * tv ≤ eta) (hDelta : 0 ≤ Delta) :
    Delta ≤ (eta / cTV) ^ (gamma / (gamma + (d : ℝ))) *
      neps ^ (-(gamma / (gamma + (d : ℝ)))) := by
  have hd : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  have hgd : 0 < gamma + (d : ℝ) := add_pos_of_pos_of_nonneg hgamma hd
  have ha : 0 < gamma / (gamma + (d : ℝ)) := div_pos hgamma hgd
  have hp : 0 ≤ Delta ^ (1 + (d : ℝ) / gamma) := Real.rpow_nonneg hDelta _
  have hctvp : 0 ≤ cTV * Delta ^ (1 + (d : ℝ) / gamma) :=
    mul_nonneg hcTV.le hp
  have hb0 : 0 < b := lt_of_lt_of_le hneps hb
  have hsmall : b * (cTV * Delta ^ (1 + (d : ℝ) / gamma)) ≤ eta :=
    le_trans (mul_le_mul_of_nonneg_left hpoint hb0.le) hcert
  have hsmall' : neps * (cTV * Delta ^ (1 + (d : ℝ) / gamma)) ≤ eta :=
    le_trans (mul_le_mul_of_nonneg_right hb hctvp) hsmall
  have hden : 0 < cTV * neps := mul_pos hcTV hneps
  have hpow : Delta ^ (1 + (d : ℝ) / gamma) ≤ eta / (cTV * neps) := by
    apply (le_div_iff₀ hden).2
    nlinarith
  have hrpow := Real.rpow_le_rpow (Real.rpow_nonneg hDelta _) hpow ha.le
  have hexp : (1 + (d : ℝ) / gamma) * (gamma / (gamma + (d : ℝ))) = 1 := by
    field_simp
  calc
    Delta = (Delta ^ (1 + (d : ℝ) / gamma)) ^
        (gamma / (gamma + (d : ℝ))) := by
          rw [← Real.rpow_mul hDelta, hexp, Real.rpow_one]
    _ ≤ (eta / (cTV * neps)) ^ (gamma / (gamma + (d : ℝ))) := hrpow
    _ = (eta / cTV) ^ (gamma / (gamma + (d : ℝ))) *
        neps ^ (-(gamma / (gamma + (d : ℝ)))) := by
          rw [show eta / (cTV * neps) = (eta / cTV) / neps by field_simp]
          rw [Real.div_rpow (div_nonneg heta.le hcTV.le) hneps.le,
            Real.rpow_neg hneps.le]
          simp [div_eq_mul_inv]

-- @node: thm:causal-dp-two-point-barrier
/-- **Causal DP two-point / TV-contraction barrier (headline).**
Part (i): there is `c_TV > 0` such that for every pair `P, Q` in the frozen
observational Hölder CATE class, `TV(P,Q) ≥ c_TV·Δ^{1+d/γ}` with
`Δ = |τ_P(x₀) - τ_Q(x₀)|`.
Part (ii) (proof-method obstruction): for every `η ∈ (0,1)`, any central-DP causal
two-point lower-bound argument that certifies output indistinguishability through
`n{exp(ε_n)-1+δ_n}TV(P,Q) ≤ η` must have `Δ ≤ C_η(n ε_n)^{-γ/(γ+d)}`. Hence the
ordinary two-point/TV-contraction method cannot certify a lower bound of the larger
formal `q = α+β` order `(n ε_n)^{-q/(q+d)}` when `q < γ` and `n ε_n > 1`
(the two powers coincide at `n ε_n = 1`). This delimits that proof route only; it is
not an impossibility theorem for other private comparison methods. -/
theorem causal_dp_two_point_barrier {d : ℕ}
    (alpha beta gamma L e0 f0 f1 r0 : ℝ) (x0 : Fin d → ℝ) (eps del : ℕ → ℝ)
    (hreg : RegimeConstants alpha beta gamma L e0 f0 f1 r0 x0)
    (hbudget : PrivacyBudget eps del) :
    ∃ cTV : ℝ, 0 < cTV ∧
      (∀ P Q : CateLaw d,
          HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0 P →
          HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0 Q →
          IidSampling P → IidSampling Q →
          cTV * (|(P.mu1 x0 - P.mu0 x0) - (Q.mu1 x0 - Q.mu0 x0)|)
                ^ (1 + (d : ℝ) / gamma)
            ≤ tvDist P.dataMeasure Q.dataMeasure)
        ∧ (∀ η : ℝ, 0 < η → η < 1 → ∃ Cη : ℝ, 0 < Cη ∧
            ∀ n : ℕ, 1 ≤ n → ∀ P Q : CateLaw d,
              HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0 P →
              HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0 Q →
              IidSampling P → IidSampling Q →
              (n : ℝ) * (Real.exp (eps n) - 1 + del n)
                  * tvDist P.dataMeasure Q.dataMeasure ≤ η →
              |(P.mu1 x0 - P.mu0 x0) - (Q.mu1 x0 - Q.mu0 x0)|
                ≤ Cη * ((n : ℝ) * eps n) ^ (-(gamma / (gamma + (d : ℝ))))) := by
  have hinterp_all :=
    holder_point_l1_interpolation_holds alpha beta gamma L e0 f0 f1 r0 x0 hreg
  have hregC := hreg
  rcases hreg with ⟨halpha, hbeta, hgamma, hL, he0, hf0, hf01, hr0, hx0⟩
  obtain ⟨cH, hcH, hinterp⟩ := hinterp_all
  let c0 : ℝ := e0 * f0
  have hc0 : 0 < c0 := mul_pos he0.1 hf0
  let cTV : ℝ := c0 * cH / 4
  have hcTV : 0 < cTV := div_pos (mul_pos hc0 hcH) (by norm_num)
  have hpart : ∀ P Q : CateLaw d,
      HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0 P →
      HolderCateClass d alpha beta gamma L e0 f0 f1 r0 x0 Q →
      IidSampling P → IidSampling Q →
      cTV * (|(P.mu1 x0 - P.mu0 x0) - (Q.mu1 x0 - Q.mu0 x0)|) ^
          (1 + (d : ℝ) / gamma) ≤ tvDist P.dataMeasure Q.dataMeasure := by
    intro P Q hP hQ hIidP hIidQ
    have hTVlower :
        (c0 / 4) * ∫ x in supBall x0 (rStar r0 x0),
            |(P.mu1 x - P.mu0 x) - (Q.mu1 x - Q.mu0 x)|
          ≤ tvDist P.dataMeasure Q.dataMeasure :=
      arm_disintegration_tv_lower alpha beta gamma L e0 f0 f1 r0 x0 hregC
        P Q hP hQ hIidP hIidQ
    have hgate := hinterp P Q hP hQ
    dsimp [cTV]
    nlinarith
  refine ⟨cTV, hcTV, ?_, ?_⟩
  · exact hpart
  · intro eta heta heta1
    refine ⟨(eta / cTV) ^ (gamma / (gamma + (d : ℝ))),
      Real.rpow_pos_of_pos (div_pos heta hcTV) _, ?_⟩
    intro n hn P Q hP hQ hIidP hIidQ hcert
    have hpoint :
        cTV * (|(P.mu1 x0 - P.mu0 x0) - (Q.mu1 x0 - Q.mu0 x0)|) ^
            (1 + (d : ℝ) / gamma) ≤ tvDist P.dataMeasure Q.dataMeasure := by
      exact hpart P Q hP hQ hIidP hIidQ
    rcases hbudget n hn with ⟨hepsLower, hepsUpper, hdel, hdelUpper⟩
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hinvpos : 0 < (n : ℝ)⁻¹ := inv_pos.mpr hnpos
    have heps : 0 < eps n := lt_of_lt_of_le hinvpos hepsLower
    have hexpLower : eps n ≤ Real.exp (eps n) - 1 := by
      nlinarith [Real.add_one_le_exp (eps n)]
    have hbase : eps n ≤ Real.exp (eps n) - 1 + del n := by linarith
    have hb : (n : ℝ) * eps n ≤
        (n : ℝ) * (Real.exp (eps n) - 1 + del n) :=
      mul_le_mul_of_nonneg_left hbase hnpos.le
    apply separation_le_privacy_rate hgamma hcTV heta
      (mul_pos hnpos heps) hb hpoint
    · simpa [mul_assoc] using hcert
    · positivity

end CausalSmith.Stat.DpCateMinimax
