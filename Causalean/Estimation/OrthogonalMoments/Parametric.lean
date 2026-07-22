/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Parametric (no-nuisance) specialisation of GeneralMoment

A `GeneralMoment` with `H = Unit` (no separate nuisance) reduces the DML
framework to the parametric one-step setting: the parameter `θ` enters the
moment directly and there is no "nuisance" to estimate flexibly.  This is
the abstract bridge from the semi-parametric layer to the classical
parametric Z-estimator.

OLS, IV-2SLS, and maximum-likelihood examples all instantiate this pattern by
supplying the appropriate score and scalar Jacobian.
-/

import Causalean.Estimation.OrthogonalMoments.DMLChernozhukov

/-! # Parametric Orthogonal Moments

This file shows how the orthogonal-moment machinery specializes to ordinary
parametric one-step estimators with no separate nuisance function, covering the
classical score-based template behind regression, instrumental variables, and
maximum likelihood examples. The definition `parametricMoment` encodes the
no-nuisance `GeneralMoment` with `H = Unit`, and
`parametric_asymptoticLinear` proves that the resulting Chernozhukov estimator
has an identically zero remainder after subtracting its influence-function
partial sum. -/

namespace Causalean
namespace Estimation
namespace OrthogonalMoments

open MeasureTheory Filter Topology Causalean.Stat

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
         {Z : Type*} [MeasurableSpace Z] {P_Z : MeasureTheory.Measure Z}

/-- Parametric moment: the moment depends only on `θ` (no nuisance).
`m_par θ z` is the user-supplied moment; `J₀ : ℝ` is its scalar Jacobian
at `θ₀`. -/
noncomputable def parametricMoment
    (m_par : ℝ → Z → ℝ) (θ₀ : ℝ) (J₀ : ℝ) (hJ : J₀ ≠ 0)
    (m_meas : ∀ θ, Measurable (m_par θ)) :
    GeneralMoment Ω μ Z P_Z Unit where
  m            := fun _ z θ => m_par θ z
  η₀           := ()
  θ₀           := θ₀
  H_ε          := Set.univ
  ρ₁           := fun _ _ => 0
  ρ₂           := fun _ _ => 0
  m_meas       := fun _ θ => m_meas θ
  η₀_mem       := Set.mem_univ _
  J₀           := J₀
  J₀_ne_zero   := hJ

/-- **Asymptotic linearity of the parametric one-step estimator.**

With `H = Unit`, the abstract `dmlChernozhukovEstimator` collapses to the
classical parametric one-step:

    θ̂_n := θ₀ − J₀⁻¹ · (1/|B(n)|) Σ_{i ∈ B(n)} m_par(θ₀, Z_i),

and the rescaled remainder
`√|B(n)|·(θ̂_n − θ₀) − (√|B(n)|)⁻¹ Σ ψ(Z_i)` with influence function
`ψ(z) := −J₀⁻¹ · m_par(θ₀, z)` is **identically zero** (algebraically — no
limit theorems needed).  The only non-trivial inputs are the population
mean-zero condition and the L² bound for `m_par(θ₀, ·)`.

For OLS, IV-2SLS, MLE: instantiate `m_par` with the score, identify `J₀`
with the Hessian/expected Jacobian, and the conclusion gives asymptotic
linearity at the rate dictated by `|B(n)|`. -/
theorem parametric_asymptoticLinear
    (m_par : ℝ → Z → ℝ) (θ₀ : ℝ) (J₀ : ℝ) (hJ : J₀ ≠ 0)
    (m_meas : ∀ θ, Measurable (m_par θ))
    (h_mean_zero : ∫ z, m_par θ₀ z ∂P_Z = 0)
    (h_finite_var : Integrable (fun z => (m_par θ₀ z) ^ 2) P_Z)
    (sample : IIDSample Ω Z μ P_Z)
    (split : OneShotSplit sample) :
    IsAsymLinear
      (dmlChernozhukovEstimator
        (parametricMoment (Ω := Ω) (μ := μ) (P_Z := P_Z) m_par θ₀ J₀ hJ m_meas)
        sample split (fun _ _ => ()))
      θ₀
      (fun z => -(J₀⁻¹) * m_par θ₀ z)
      sample
      split.foldB := by
  set M : GeneralMoment Ω μ Z P_Z Unit :=
    parametricMoment m_par θ₀ J₀ hJ m_meas with hM
  refine ⟨?_, ?_, ?_⟩
  · -- mean_zero
    rw [integral_const_mul, h_mean_zero, mul_zero]
  · -- finite_var
    refine (h_finite_var.const_mul (J₀⁻¹ ^ 2)).congr ?_
    filter_upwards with z
    ring
  · -- remainder: identically zero, since the parametric one-step exactly
    -- equals the influence-function partial sum.
    have h_pointwise : ∀ n ω,
        Real.sqrt ((split.foldB n).card : ℝ) *
            (dmlChernozhukovEstimator M sample split (fun _ _ => ()) n ω - θ₀)
          - (Real.sqrt ((split.foldB n).card : ℝ))⁻¹ *
              ∑ i ∈ split.foldB n, -(J₀⁻¹) * m_par θ₀ (sample.Z i ω) = 0 := by
      intro n ω
      set S : ℝ := ∑ i ∈ split.foldB n, m_par θ₀ (sample.Z i ω) with hS
      set c : ℝ := ((split.foldB n).card : ℝ) with hc
      have h_sum_eq : ∑ i ∈ split.foldB n, -(J₀⁻¹) * m_par θ₀ (sample.Z i ω)
          = -(J₀⁻¹) * S := by
        rw [hS, ← Finset.mul_sum]
      have h_est :
          dmlChernozhukovEstimator M sample split (fun _ _ => ()) n ω
            = θ₀ - J₀⁻¹ * (c⁻¹ * S) := by
        simp [dmlChernozhukovEstimator, M, parametricMoment,
          GeneralMoment.J₀_inv, hS, hc]
      rw [h_est, h_sum_eq]
      by_cases hc0 : c = 0
      · -- |B(n)| = 0: all sums vanish.
        have hcard : (split.foldB n).card = 0 := by
          have hcard_real : ((split.foldB n).card : ℝ) = 0 := by rw [← hc]; exact hc0
          exact_mod_cast hcard_real
        have hS0 : S = 0 := by
          rw [hS]
          exact Finset.sum_eq_zero
            (fun i hi => absurd (Finset.card_pos.mpr ⟨i, hi⟩)
              (by rw [hcard]; exact lt_irrefl 0))
        rw [hc0, hS0]
        simp
      · have hc_nn : 0 ≤ c := by rw [hc]; exact Nat.cast_nonneg _
        have hc_pos : 0 < c := lt_of_le_of_ne hc_nn (Ne.symm hc0)
        have hsqrt_pos : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc_pos
        have hsqrt_ne : Real.sqrt c ≠ 0 := ne_of_gt hsqrt_pos
        have h_sqrt_sq : Real.sqrt c * Real.sqrt c = c :=
          Real.mul_self_sqrt hc_nn
        have hsqrt_inv : Real.sqrt c * c⁻¹ = (Real.sqrt c)⁻¹ := by
          field_simp
          rw [sq, h_sqrt_sq]
        calc
          Real.sqrt c * (θ₀ - J₀⁻¹ * (c⁻¹ * S) - θ₀)
              - (Real.sqrt c)⁻¹ * (-(J₀⁻¹) * S)
              = -J₀⁻¹ * (Real.sqrt c * c⁻¹) * S + J₀⁻¹ * (Real.sqrt c)⁻¹ * S := by
                ring
          _ = -J₀⁻¹ * (Real.sqrt c)⁻¹ * S + J₀⁻¹ * (Real.sqrt c)⁻¹ * S := by
                rw [hsqrt_inv]
          _ = 0 := by ring
    -- The remainder function equals zero everywhere, so it is `o_p(1)`.
    intro ε hε
    have h_zero_set : ∀ n,
        {ω : Ω |
            ε * (fun _ => (1 : ℝ)) n <
              |Real.sqrt ((split.foldB n).card : ℝ) *
                  (dmlChernozhukovEstimator M sample split (fun _ _ => ()) n ω - θ₀)
                - (Real.sqrt ((split.foldB n).card : ℝ))⁻¹ *
                    ∑ i ∈ split.foldB n, -(J₀⁻¹) * m_par θ₀ (sample.Z i ω)|}
          = ∅ := by
      intro n
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      rw [h_pointwise n ω]
      simpa using le_of_lt hε
    have h_meas_zero : ∀ n,
        μ {ω : Ω |
            ε * (fun _ => (1 : ℝ)) n <
              |Real.sqrt ((split.foldB n).card : ℝ) *
                  (dmlChernozhukovEstimator M sample split (fun _ _ => ()) n ω - θ₀)
                - (Real.sqrt ((split.foldB n).card : ℝ))⁻¹ *
                    ∑ i ∈ split.foldB n, -(J₀⁻¹) * m_par θ₀ (sample.Z i ω)|} = 0 := by
      intro n
      rw [h_zero_set n]
      exact MeasureTheory.measure_empty
    simp_rw [h_meas_zero]
    exact tendsto_const_nhds

end OrthogonalMoments
end Estimation
end Causalean
