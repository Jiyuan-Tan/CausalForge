/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Mathlib.Probability.CondVar

/-!
# Unconditional (full-sample-law) bias / variance of a truncated estimator

Unconditional risk bounds for truncated local-polynomial estimators, lifting conditional-on-design
bias and variance estimates through good-design events.

The conditional-on-design capstones `localPoly_estimatorBias_window` and
`localPoly_estimatorStochL2` bound the bias / variance of the interior local-polynomial estimator
**given a non-degenerate design** (equivalently, on the high-probability good-design event of
`designMatrix_inv_concentration`). A full risk bound for the random-design estimator also needs
bounds on the bias `𝔼[est] − f(t)` and stochastic `L²` error `√Var(est)` under the **full** sample
law, where the design itself is random.

This module performs that high-probability-to-`L²` lift as a pair of generic probabilistic facts,
with no conditional-on-design caveat remaining:

* `estimatorBias_unconditional` — split `𝔼[est] = 𝔼[est·1_G] + 𝔼[est·1_{Gᶜ}]` through the design
  σ-algebra `m`: on the good design event `G` the conditional bias `|𝔼[est | m] − θ| ≤ B` holds,
  while off `G` the truncation `|est| ≤ M` controls the contribution by `2M·μ(Gᶜ)`. Yields
  `|𝔼[est] − θ| ≤ B + 2M·μ(Gᶜ)`.
* `estimatorVariance_unconditional` — via the **law of total variance**
  `Var(est) = 𝔼[Var(est | m)] + Var(𝔼[est | m])`: the first term is the within-design variance
  (`≤ Vrate` on `G`, `≤ M²` off it), the second is dominated by the squared conditional bias
  (`≤ Bsq` on `G`, `≤ 4M²` off it). Yields `Var(est) ≤ Vrate + Bsq + 5M²·μ(Gᶜ)`.
* `estimatorStochL2_unconditional` — the `√·` form of the variance bound.

Each carries an explicit `μ(Gᶜ)` tail; `designMatrix_inv_concentration` makes that tail tiny (and a
regime hypothesis absorbs it into the leading rate). The lift takes the *conditional* bias /
variance bounds as hypotheses — exactly the output of the conditional capstones — and is otherwise
self-contained: the conditional-expectation and law-of-total-variance machinery is
`MeasureTheory.condExp` / `ProbabilityTheory.condVar` from Mathlib.
-/

namespace Causalean.Stat.Nonparametric

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

variable {Ω : Type*} {m m0 : MeasurableSpace Ω} {μ : Measure[m0] Ω} [IsProbabilityMeasure μ]

/-- **Two-event integral split.** For an integrable `f` and a measurable set `G`, an a.e. bound
`f ≤ cG` on `G` and `f ≤ cGc` off `G` integrate to `∫ f ≤ cG·μ(G) + cGc·μ(Gᶜ)`. The workhorse
behind both the bias and the variance lift. -/
private lemma split_bound {f : Ω → ℝ} {G : Set Ω} {cG cGc : ℝ}
    (hf : Integrable f μ) (hGm : MeasurableSet[m0] G)
    (hcG : ∀ᵐ ω ∂μ, ω ∈ G → f ω ≤ cG)
    (hcGc : ∀ᵐ ω ∂μ, ω ∈ Gᶜ → f ω ≤ cGc) :
    ∫ ω, f ω ∂μ ≤ cG * (μ G).toReal + cGc * (μ Gᶜ).toReal := by
  have e1 : ∫ ω in G, f ω ∂μ ≤ cG * (μ G).toReal := by
    have h := setIntegral_mono_on_ae hf.integrableOn (integrable_const cG).integrableOn hGm hcG
    rw [setIntegral_const, smul_eq_mul, mul_comm] at h
    exact h
  have e2 : ∫ ω in Gᶜ, f ω ∂μ ≤ cGc * (μ Gᶜ).toReal := by
    have h := setIntegral_mono_on_ae hf.integrableOn (integrable_const cGc).integrableOn
      hGm.compl hcGc
    rw [setIntegral_const, smul_eq_mul, mul_comm] at h
    exact h
  rw [← integral_add_compl hGm hf]
  exact add_le_add e1 e2

/-- The conditional expectation of a `[-M, M]`-bounded statistic stays within `[-M, M]`. -/
private lemma abs_condExp_le_of_bound {est : Ω → ℝ} {M : ℝ} (hm : m ≤ m0)
    (hest : Integrable est μ) (hM : ∀ ω, |est ω| ≤ M) :
    ∀ᵐ ω ∂μ, |(μ[est | m]) ω| ≤ M := by
  have hub : μ[est | m] ≤ᵐ[μ] (fun _ => M) := by
    have h := condExp_mono (m := m) hest (integrable_const M)
      (Filter.Eventually.of_forall fun ω => (abs_le.1 (hM ω)).2)
    rwa [condExp_const hm] at h
  have hlb : (fun _ => (-M : ℝ)) ≤ᵐ[μ] μ[est | m] := by
    have h := condExp_mono (m := m) (integrable_const (-M)) hest
      (Filter.Eventually.of_forall fun ω => (abs_le.1 (hM ω)).1)
    rwa [condExp_const hm] at h
  filter_upwards [hub, hlb] with ω h1 h2 using abs_le.2 ⟨h2, h1⟩

/-- **Unconditional bias of a truncated estimator.** Let `est` be a `[-M, M]`-bounded integrable
estimator of a target `θ` with `|θ| ≤ M`, and let `G` (an `m`-measurable good-design event) be such
that the conditional bias `|𝔼[est | m] − θ| ≤ B` holds a.e. on `G`. Then the full-sample-law bias
obeys

`|𝔼[est] − θ| ≤ B + 2M·μ(Gᶜ)`,

the conditional bias `B` plus a truncation tail proportional to the bad-design probability. -/
theorem estimatorBias_unconditional {est : Ω → ℝ} {θ B M : ℝ} {G : Set Ω} (hm : m ≤ m0)
    (hest : Integrable est μ) (hM : ∀ ω, |est ω| ≤ M) (hθ : |θ| ≤ M) (hB : 0 ≤ B)
    (hG : MeasurableSet[m] G)
    (hcond : ∀ᵐ ω ∂μ, ω ∈ G → |(μ[est | m]) ω - θ| ≤ B) :
    |(∫ ω, est ω ∂μ) - θ| ≤ B + 2 * M * (μ Gᶜ).toReal := by
  have hGm0 : MeasurableSet[m0] G := hm _ hG
  have hcE_int : Integrable (μ[est | m]) μ := integrable_condExp
  have hg_int : Integrable (fun ω => (μ[est | m]) ω - θ) μ := hcE_int.sub (integrable_const θ)
  -- `∫ est = ∫ 𝔼[est | m]`, so the bias is the mean of `𝔼[est | m] − θ`.
  have hbias_eq : (∫ ω, est ω ∂μ) - θ = ∫ ω, ((μ[est | m]) ω - θ) ∂μ := by
    rw [integral_sub hcE_int (integrable_const θ), integral_const, integral_condExp hm,
      probReal_univ, one_smul]
  rw [hbias_eq]
  refine (abs_integral_le_integral_abs).trans ?_
  -- bad-side global a.e. bound `|𝔼[est | m] − θ| ≤ 2M`.
  have habsM := abs_condExp_le_of_bound hm hest hM
  have hθ' := abs_le.1 hθ
  have hbad : ∀ᵐ ω ∂μ, ω ∈ Gᶜ → |(μ[est | m]) ω - θ| ≤ 2 * M := by
    filter_upwards [habsM] with ω hω _
    have h1 := abs_le.1 hω
    rw [abs_le]; constructor <;> linarith [h1.1, h1.2, hθ'.1, hθ'.2]
  have hsplit := split_bound hg_int.abs hGm0 hcond hbad
  refine hsplit.trans ?_
  have hμG : (μ G).toReal ≤ 1 := by
    rw [← ENNReal.toReal_one]; exact ENNReal.toReal_mono (by simp) prob_le_one
  have hBG : B * (μ G).toReal ≤ B := by nlinarith [hB, hμG, ENNReal.toReal_nonneg (a := μ G)]
  linarith

/-- **Unconditional variance of a truncated estimator (law of total variance).** Let `est` be a
`[-M, M]`-bounded `L²` estimator of `θ` with `|θ| ≤ M`, and `G` an `m`-measurable good-design event
on which the conditional variance `Var[est | m] ≤ Vrate` and the squared conditional bias
`(𝔼[est | m] − θ)² ≤ Bsq` hold a.e. Then the full-sample-law variance obeys

`Var(est) ≤ Vrate + Bsq + 5M²·μ(Gᶜ)`,

the within-design variance rate `Vrate` plus the squared bias `Bsq` plus a truncation tail. -/
theorem estimatorVariance_unconditional {est : Ω → ℝ} {θ Bsq Vrate M : ℝ} {G : Set Ω}
    (hm : m ≤ m0) (hest : MemLp est 2 μ) (hM : ∀ ω, |est ω| ≤ M) (hθ : |θ| ≤ M)
    (hVr : 0 ≤ Vrate) (hBsq : 0 ≤ Bsq) (hG : MeasurableSet[m] G)
    (hVcond : ∀ᵐ ω ∂μ, ω ∈ G → (Var[est; μ | m]) ω ≤ Vrate)
    (hBcond : ∀ᵐ ω ∂μ, ω ∈ G → ((μ[est | m]) ω - θ) ^ 2 ≤ Bsq) :
    Var[est; μ] ≤ Vrate + Bsq + 5 * M ^ 2 * (μ Gᶜ).toReal := by
  have hMnn : 0 ≤ M := le_trans (abs_nonneg θ) hθ
  have hM2nn : 0 ≤ M ^ 2 := sq_nonneg M
  have hGm0 : MeasurableSet[m0] G := hm _ hG
  have hest_int : Integrable est μ := hest.integrable one_le_two
  have hμG : (μ G).toReal ≤ 1 := by
    rw [← ENNReal.toReal_one]; exact ENNReal.toReal_mono (by simp) prob_le_one
  have hμGcnn : (0 : ℝ) ≤ (μ Gᶜ).toReal := ENNReal.toReal_nonneg
  -- Law of total variance: `Var(est) = 𝔼[Var(est | m)] + Var(𝔼[est | m])`.
  have htot := integral_condVar_add_variance_condExp hm hest
  have hθ' := abs_le.1 hθ
  -- ===== Term 1: `𝔼[Var(est | m)] ≤ Vrate + M²·μ(Gᶜ)` =====
  have hcondVar_int : Integrable (Var[est; μ | m]) μ := integrable_condVar
  -- off-`G` bound on the conditional variance: `Var[est | m] ≤ 𝔼[est² | m] ≤ M²`.
  have hCV_le_sq : Var[est; μ | m] ≤ᵐ[μ] μ[fun ω => est ω ^ 2 | m] :=
    condVar_ae_le_condExp_sq hm hest
  have hsq_le_M2 : μ[fun ω => est ω ^ 2 | m] ≤ᵐ[μ] (fun _ => M ^ 2) := by
    have h := condExp_mono (m := m) hest.integrable_sq (integrable_const (M ^ 2))
      (Filter.Eventually.of_forall fun ω => by
        nlinarith [sq_abs (est ω), hM ω, abs_nonneg (est ω)])
    rwa [condExp_const hm] at h
  have hCV_bad : ∀ᵐ ω ∂μ, ω ∈ Gᶜ → (Var[est; μ | m]) ω ≤ M ^ 2 := by
    filter_upwards [hCV_le_sq, hsq_le_M2] with ω h1 h2 _ using le_trans h1 h2
  have hT1 : (∫ ω, (Var[est; μ | m]) ω ∂μ) ≤ Vrate + M ^ 2 * (μ Gᶜ).toReal := by
    refine (split_bound hcondVar_int hGm0 hVcond hCV_bad).trans ?_
    have hVG : Vrate * (μ G).toReal ≤ Vrate := by
      nlinarith [hVr, hμG, ENNReal.toReal_nonneg (a := μ G)]
    linarith
  -- ===== Term 2: `Var(𝔼[est | m]) ≤ Bsq + 4M²·μ(Gᶜ)` =====
  have hcE_memLp : MemLp (μ[est | m]) 2 μ := hest.condExp
  have hZ_memLp : MemLp (fun ω => (μ[est | m]) ω - θ) 2 μ := hcE_memLp.sub (memLp_const θ)
  have hZsq_int : Integrable (fun ω => ((μ[est | m]) ω - θ) ^ 2) μ := hZ_memLp.integrable_sq
  have habsM := abs_condExp_le_of_bound hm hest_int hM
  -- `Var(𝔼[est | m]) = Var(𝔼[est | m] − θ) ≤ 𝔼[(𝔼[est | m] − θ)²]`.
  have hVarcE_le : Var[μ[est | m]; μ] ≤ ∫ ω, ((μ[est | m]) ω - θ) ^ 2 ∂μ := by
    have hveq : Var[μ[est | m]; μ] = Var[fun ω => (μ[est | m]) ω - θ; μ] :=
      (variance_sub_const hcE_memLp.aestronglyMeasurable θ).symm
    rw [hveq]
    have h := variance_le_expectation_sq (μ := μ) hZ_memLp.aestronglyMeasurable
    simpa [pow_two, Pi.pow_apply] using h
  -- off-`G` bound on `(𝔼[est | m] − θ)²≤ (2M)² = 4M²`.
  have hZsq_bad : ∀ᵐ ω ∂μ, ω ∈ Gᶜ → ((μ[est | m]) ω - θ) ^ 2 ≤ 4 * M ^ 2 := by
    filter_upwards [habsM] with ω hω _
    have h1 := abs_le.1 hω
    have hlo : -(2 * M) ≤ (μ[est | m]) ω - θ := by linarith [h1.1, hθ'.2]
    have hhi : (μ[est | m]) ω - θ ≤ 2 * M := by linarith [h1.2, hθ'.1]
    nlinarith [hlo, hhi]
  have hT2 : Var[μ[est | m]; μ] ≤ Bsq + 4 * M ^ 2 * (μ Gᶜ).toReal := by
    refine hVarcE_le.trans ?_
    refine (split_bound hZsq_int hGm0 hBcond hZsq_bad).trans ?_
    have hBG : Bsq * (μ G).toReal ≤ Bsq := by
      nlinarith [hBsq, hμG, ENNReal.toReal_nonneg (a := μ G)]
    linarith
  -- ===== Assemble via the law of total variance =====
  rw [← htot]
  have heq : μ[Var[est; μ | m]] = ∫ ω, (Var[est; μ | m]) ω ∂μ := rfl
  rw [heq]
  exact (add_le_add hT1 hT2).trans_eq (by ring)

/-- **Unconditional stochastic `L²` error of a truncated estimator.** The `√·` form of
`estimatorVariance_unconditional`: under the same hypotheses,

`√Var(est) ≤ √(Vrate + Bsq + 5M²·μ(Gᶜ))`.

With `Vrate = Cvar²·(Nh)⁻¹`, `Bsq = Cbias²·h^{2β}` and a negligible truncation tail
(`5M²·μ(Gᶜ)` driven to `o((Nh)⁻¹)` by `designMatrix_inv_concentration`), this gives the
full-sample stochastic `L²` rate up to the bias and the negligible tail. -/
theorem estimatorStochL2_unconditional {est : Ω → ℝ} {θ Bsq Vrate M : ℝ} {G : Set Ω}
    (hm : m ≤ m0) (hest : MemLp est 2 μ) (hM : ∀ ω, |est ω| ≤ M) (hθ : |θ| ≤ M)
    (hVr : 0 ≤ Vrate) (hBsq : 0 ≤ Bsq) (hG : MeasurableSet[m] G)
    (hVcond : ∀ᵐ ω ∂μ, ω ∈ G → (Var[est; μ | m]) ω ≤ Vrate)
    (hBcond : ∀ᵐ ω ∂μ, ω ∈ G → ((μ[est | m]) ω - θ) ^ 2 ≤ Bsq) :
    Real.sqrt (Var[est; μ]) ≤ Real.sqrt (Vrate + Bsq + 5 * M ^ 2 * (μ Gᶜ).toReal) :=
  Real.sqrt_le_sqrt
    (estimatorVariance_unconditional hm hest hM hθ hVr hBsq hG hVcond hBcond)

end Causalean.Stat.Nonparametric
