/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Structure-agnostic ATE lower bound: expected-risk (MSE) form (general center)

The general-constant-center analogue of `MSE.lean`.  The quantile bound
`minimax_lower_bound_gen` (`1/4 ≤ minimaxMiss …`, the paper's `γ = 3/4`
case) implies the weaker expected-risk floor: every measurable estimator has
mean-squared error at least `s²/4` (with `s = g₁β(α+β)/(2(g₁²−β²)) ≍ √(εg·εm)`) on
**some** DGP in the class, around any constant bounded-away center `(m₀, g₀, g₁)`.

The witness DGP is extracted from the two-point bound `1/4 ≤ max(…)` (Chebyshev
bridge `nMiss_sq_le_nMSE`): either the null estimate `(m̂, ĝ)` (ATE `g₁ − g₀`) or a
single Rademacher-perturbed DGP pulled out of the uniform mixture `QtrueG` by
`exists_real_ge_mixture`.
-/

import Causalean.Estimation.MinimaxATE.ConstCenterGeneral.LowerBound

/-! # General-Center MSE Bound

This file converts the general constant-center quantile lower bound into an expected
mean-squared-error lower bound. The theorem `minimax_lower_bound_mse_gen` uses
`minimax_lower_bound_gen` together with the Chebyshev bridge `nMiss_sq_le_nMSE` to extract an
in-class data-generating process on which any measurable estimator has squared-error risk at
least one quarter of the squared general-center separation.

The proof keeps the two possible witnesses explicit: the null law `QfalseG` with ATE `g₁ - g₀`,
or one perturbed law `QpertG` selected from the uniform mixture `QtrueG`. -/

namespace Causalean.Estimation.MinimaxATE

open MeasureTheory
open Causalean.Stat
open scoped ENNReal BigOperators

namespace GenConstr

/-- **Structure-agnostic minimax lower bound, expected-risk (MSE) form (general center).**
Under the hypotheses of `minimax_lower_bound_gen`, every measurable estimator
has mean-squared error at least `s²/4` (with `s = g₁β(α+β)/(2(g₁²−β²)) ≍ √(εg·εm)`) on
**some** DGP in the class — the weaker `(1−γ)`-factored (`γ = 3/4`) consequence of the
quantile bound, around any constant bounded-away center. -/
theorem minimax_lower_bound_mse_gen (P : GenConstr) {K n : ℕ} [NeZero K]
    {εg εm : ℝ}
    (hm : (P.m₀ * (P.β / P.g₁)) ^ 2 ≤ εm)
    (hg : P.g₁ ^ 2 * (P.α + P.β) ^ 2 / (P.g₁ - P.β) ^ 2 ≤ εg)
    (hεg : 0 ≤ εg) (hεm : 0 ≤ εm)
    (hΓ : P.Γ ≤ 1) (hreg : 2 * (n : ℝ) ^ 2 * (P.Γ / 2) ^ 2 ≤ (K : ℝ) * Real.log 2)
    {est : (Fin n → Obs (Fin K × Bool)) → ℝ} (hest : Measurable est) :
    ∃ p : InClassDGP (P.mhatG (K := K)) P.ghatG εg εm,
      (P.g₁ * P.β * (P.α + P.β) / (2 * (P.g₁ ^ 2 - P.β ^ 2))) ^ 2 / 4
        ≤ nMSE p.2.valid n est := by
  have hden : (0:ℝ) < P.g₁ ^ 2 - P.β ^ 2 := P.g1sq_sub_betasq_pos
  have hdenne : P.g₁ ^ 2 - P.β ^ 2 ≠ 0 := hden.ne'
  set gap := P.g₁ * P.β * (P.α + P.β) / (P.g₁ ^ 2 - P.β ^ 2) with hgap
  have hgap0 : 0 ≤ gap := by
    rw [hgap]; have := P.hβ; have := P.hα; have := P.hg₁0
    apply div_nonneg (by positivity) hden.le
  set s := P.g₁ * P.β * (P.α + P.β) / (2 * (P.g₁ ^ 2 - P.β ^ 2)) with hs
  have hs_gap : s = gap / 2 := by rw [hs, hgap]; field_simp
  have hs0 : 0 ≤ s := by rw [hs_gap]; linarith
  haveI : IsProbabilityMeasure (QfalseG P K n) := QfalseG_isProb P K n
  haveI : IsProbabilityMeasure (QtrueG P K n) := QtrueG_isProb P K n
  haveI : ∀ lam : Fin K → Bool, IsProbabilityMeasure (QpertG P K n lam) :=
    fun lam => QpertG_isProb P K n lam
  -- From `1/4 ≤ nMiss` on an in-class DGP (at its own ATE `θ`), Chebyshev gives MSE `≥ s²/4`.
  have hkey : ∀ {m : Fin K × Bool → ℝ} {g : Bool → Fin K × Bool → ℝ}
      (hin : InClass (P.mhatG (K := K)) P.ghatG εg εm m g) (θ : ℝ), ate g = θ →
      1 / 4 ≤ (productLaw hin.valid n).real {x | s ≤ |est x - θ|} →
      ∃ p : InClassDGP (P.mhatG (K := K)) P.ghatG εg εm, s ^ 2 / 4 ≤ nMSE p.2.valid n est := by
    intro m g hin θ hθ h14
    refine ⟨⟨(m, g), hin⟩, ?_⟩
    have hcheb : s ^ 2 * (productLaw hin.valid n).real {x | s ≤ |est x - θ|}
        ≤ nMSE hin.valid n est := by
      have h := nMiss_sq_le_nMSE hin.valid n (est := est) hs0
      unfold nMiss at h
      rwa [hθ] at h
    have h1 := mul_le_mul_of_nonneg_left h14 (sq_nonneg s)
    change s ^ 2 / 4 ≤ nMSE hin.valid n est
    calc s ^ 2 / 4 = s ^ 2 * (1 / 4) := by ring
      _ ≤ s ^ 2 * (productLaw hin.valid n).real {x | s ≤ |est x - θ|} := h1
      _ ≤ nMSE hin.valid n est := hcheb
  -- Two-point bound: `1/4 ≤ max(null miss, mixture miss)`.
  have htv := P.tvDist_QfalseG_QtrueG_le_half (K := K) (n := n) hΓ hreg
  have hsep : 2 * s ≤ |(P.g₁ - P.g₀) - ((P.g₁ - P.g₀) + gap)| := by
    rw [sub_add_cancel_left, abs_neg, abs_of_nonneg hgap0, hs_gap]; linarith
  have hmax := two_point_lower_bound_of_tvDist_le
    (P₀ := QfalseG P K n) (P₁ := QtrueG P K n) hest hsep htv
  rw [show (1 - (1 : ℝ) / 2) / 2 = 1 / 4 by norm_num] at hmax
  rcases le_max_iff.mp hmax with hleft | hright
  · -- null branch: `(m̂, ĝ)` is in class, `ate ĝ = g₁ − g₀`
    exact hkey (inClass_nullG P hεg hεm) (P.g₁ - P.g₀) P.ate_ghatG hleft
  · -- mixture branch: extract a single Rademacher-perturbed DGP
    obtain ⟨lam, hlam⟩ := exists_real_ge_mixture (signWeight K) (signWeight_sum K)
      (fun l => QpertG P K n l) {x | s ≤ |est x - ((P.g₁ - P.g₀) + gap)|}
    refine hkey (P.inClassG hm hg lam) ((P.g₁ - P.g₀) + gap) ?_ (le_trans hright hlam)
    rw [P.ate_gPertG lam]

end GenConstr

end Causalean.Estimation.MinimaxATE
