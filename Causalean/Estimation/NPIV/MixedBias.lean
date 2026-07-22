/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Mixed-bias / DR identity for linear inverse-problem functionals

First milestone of the NPIV / TRAE track.  This file states the
mixed-bias identity (`prop:est-trae-mixed-bias` in
`doc/basic_concepts/po/estimation/trae_inverse_problems.tex`):

    Θ(h, q) − θ₀ = E[(q₀(Z) − q(Z)) (h(X) − h₀(X))]

for every `h ∈ Hbar` and `q ∈ Qbar`, where `q₀` is a dual solution.  Two
direct corollaries record the doubly-robust cancellation at the truth:
`Θ(h₀, q) = θ₀` and `Θ(h, q₀) = θ₀`.

All three results are proved by integral linearity, the dual-solution
identity at direction `h − h₀`, and the primal moment identity at `q`.
-/

import Causalean.Estimation.NPIV.Setup

/-! # Mixed-Bias Identity for NPIV

This file proves the doubly robust mixed-bias identity for linear
inverse-problem functionals. It shows that, given a dual solution, the
functional error factors as the expectation of the product of the dual nuisance
error and the primal nuisance error, with immediate cancellation at either
truth. -/

namespace Causalean
namespace Estimation
namespace NPIV

open MeasureTheory

section MixedBias

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Mixed-bias / DR identity** — `prop:est-trae-mixed-bias`.

For every `h ∈ Hbar` and `q ∈ Qbar`, given a dual solution `q₀`,

    Θ(h, q) − θ₀ = E[(q₀(Z) − q(Z)) (h(X) − h₀(X))]. -/
theorem mixed_bias_identity
    (S : InverseProblemSystem Ω μ) {q₀ : S.𝒵 → ℝ}
    (hq₀ : S.DualSolution q₀)
    {h : S.𝒳 → ℝ} (hh : h ∈ S.Hbar)
    {q : S.𝒵 → ℝ} (hq : q ∈ S.Qbar) :
    S.Θ h q - S.θ₀
      = ∫ ω, (q₀ (S.Z ω) - q (S.Z ω)) * (h (S.X ω) - S.h₀ (S.X ω)) ∂μ := by
  -- Integrability witnesses for each piece appearing in the proof.
  have h_int_meh := S.integrable_m_e h hh
  have h_int_meh₀ := S.integrable_m_e S.h₀ S.h₀_mem
  have h_int_mq := S.integrable_m q hq
  have h_int_qh := S.integrable_qh h hh q hq
  have h_int_q₀h := S.integrable_qh h hh q₀ hq₀.mem
  have h_int_q₀h₀ := S.integrable_qh S.h₀ S.h₀_mem q₀ hq₀.mem
  have h_int_qh₀ := S.integrable_qh S.h₀ S.h₀_mem q hq
  -- Reordered version (the primal moment uses `h₀(X) · q(Z)` not `q(Z) · h₀(X)`).
  have h_int_h₀q : Integrable (fun ω =>
      S.h₀ (S.xOf (S.W ω)) * q (S.zOf (S.W ω))) μ := by
    have h := h_int_qh₀
    simpa [mul_comm] using h
  -- Step 1: distribute the LHS over its three summands.
  have hΘ_eq :
      S.Θ h q
        = (∫ ω, S.m_e (S.W ω) h ∂μ)
          + (∫ ω, S.m (S.W ω) q ∂μ)
          - (∫ ω, q (S.zOf (S.W ω)) * h (S.xOf (S.W ω)) ∂μ) := by
    unfold InverseProblemSystem.Θ InverseProblemSystem.phi InverseProblemSystem.phiVal
    calc
      ∫ ω, S.m_e (S.W ω) h + S.m (S.W ω) q
          - q (S.zOf (S.W ω)) * h (S.xOf (S.W ω)) ∂μ
          = (∫ ω, S.m_e (S.W ω) h + S.m (S.W ω) q ∂μ)
              - ∫ ω, q (S.zOf (S.W ω)) * h (S.xOf (S.W ω)) ∂μ :=
            integral_sub (h_int_meh.add h_int_mq) h_int_qh
      _ = (∫ ω, S.m_e (S.W ω) h ∂μ) + (∫ ω, S.m (S.W ω) q ∂μ)
            - ∫ ω, q (S.zOf (S.W ω)) * h (S.xOf (S.W ω)) ∂μ := by
            rw [integral_add h_int_meh h_int_mq]
  -- Step 2: dual identity applied at `h - h₀ ∈ Hbar` gives
  --   ∫ m_e(W; h) − ∫ m_e(W; h₀)
  --     = ∫ q₀(Z) · (h(X) − h₀(X)) ∂μ.
  have h_sub_mem : (fun x => h x - S.h₀ x) ∈ S.Hbar :=
    S.Hbar_sub h hh S.h₀ S.h₀_mem
  have h_dual := hq₀.identity (fun x => h x - S.h₀ x) h_sub_mem
  have h_me_sub_pw : ∀ ω,
      S.m_e (S.W ω) (fun x => h x - S.h₀ x)
        = S.m_e (S.W ω) h - S.m_e (S.W ω) S.h₀ := fun ω =>
    S.m_e_sub (S.W ω) h S.h₀
  have h_me_diff_eq :
      (∫ ω, S.m_e (S.W ω) h ∂μ) - (∫ ω, S.m_e (S.W ω) S.h₀ ∂μ)
        = ∫ ω, q₀ (S.zOf (S.W ω)) *
            (h (S.xOf (S.W ω)) - S.h₀ (S.xOf (S.W ω))) ∂μ := by
    rw [← integral_sub h_int_meh h_int_meh₀]
    have hcongr :
        (fun ω => S.m_e (S.W ω) h - S.m_e (S.W ω) S.h₀)
          = (fun ω => S.m_e (S.W ω) (fun x => h x - S.h₀ x)) := by
      funext ω
      exact (h_me_sub_pw ω).symm
    rw [hcongr, h_dual]
  -- Step 3: primal moment identity at `q`:
  --   ∫ m(W; q) ∂μ = ∫ h₀(X) · q(Z) ∂μ.
  have h_prim := S.primal_moment q hq
  -- Step 4: rewrite the RHS as a sum of three atomic integrals.
  have hRHS_eq :
      (∫ ω, (q₀ (S.Z ω) - q (S.Z ω))
          * (h (S.X ω) - S.h₀ (S.X ω)) ∂μ)
        = (∫ ω, q₀ (S.zOf (S.W ω))
              * (h (S.xOf (S.W ω)) - S.h₀ (S.xOf (S.W ω))) ∂μ)
          + (∫ ω, S.h₀ (S.xOf (S.W ω)) * q (S.zOf (S.W ω)) ∂μ)
          - (∫ ω, q (S.zOf (S.W ω)) * h (S.xOf (S.W ω)) ∂μ) := by
    -- Pointwise expansion: (q₀ − q)·(h − h₀) = q₀·(h − h₀) + h₀·q − q·h.
    have h_int_diff_q₀ :
        Integrable (fun ω =>
          q₀ (S.zOf (S.W ω))
            * (h (S.xOf (S.W ω)) - S.h₀ (S.xOf (S.W ω)))) μ := by
      have : (fun ω =>
              q₀ (S.zOf (S.W ω))
                * (h (S.xOf (S.W ω)) - S.h₀ (S.xOf (S.W ω))))
            = (fun ω => q₀ (S.zOf (S.W ω)) * h (S.xOf (S.W ω))
                - q₀ (S.zOf (S.W ω)) * S.h₀ (S.xOf (S.W ω))) := by
        funext ω; ring
      rw [this]; exact h_int_q₀h.sub h_int_q₀h₀
    -- ∫ (q₀ − q)·(h − h₀) = ∫ q₀·(h − h₀) + ∫ h₀·q − ∫ q·h
    have h_pw : ∀ ω,
        (q₀ (S.Z ω) - q (S.Z ω))
            * (h (S.X ω) - S.h₀ (S.X ω))
          = q₀ (S.zOf (S.W ω))
              * (h (S.xOf (S.W ω)) - S.h₀ (S.xOf (S.W ω)))
            + S.h₀ (S.xOf (S.W ω)) * q (S.zOf (S.W ω))
            - q (S.zOf (S.W ω)) * h (S.xOf (S.W ω)) := fun ω => by
      simp only [InverseProblemSystem.X, InverseProblemSystem.Z]
      ring
    have hcongr :
        (fun ω => (q₀ (S.Z ω) - q (S.Z ω)) * (h (S.X ω) - S.h₀ (S.X ω)))
          = (fun ω => q₀ (S.zOf (S.W ω))
                * (h (S.xOf (S.W ω)) - S.h₀ (S.xOf (S.W ω)))
              + S.h₀ (S.xOf (S.W ω)) * q (S.zOf (S.W ω))
              - q (S.zOf (S.W ω)) * h (S.xOf (S.W ω))) := by
      funext ω; exact h_pw ω
    rw [hcongr]
    calc
      ∫ ω, q₀ (S.zOf (S.W ω))
              * (h (S.xOf (S.W ω)) - S.h₀ (S.xOf (S.W ω)))
            + S.h₀ (S.xOf (S.W ω)) * q (S.zOf (S.W ω))
            - q (S.zOf (S.W ω)) * h (S.xOf (S.W ω)) ∂μ
          = (∫ ω, q₀ (S.zOf (S.W ω))
                  * (h (S.xOf (S.W ω)) - S.h₀ (S.xOf (S.W ω)))
                + S.h₀ (S.xOf (S.W ω)) * q (S.zOf (S.W ω)) ∂μ)
              - ∫ ω, q (S.zOf (S.W ω)) * h (S.xOf (S.W ω)) ∂μ :=
            integral_sub (h_int_diff_q₀.add h_int_h₀q) h_int_qh
      _ = (∫ ω, q₀ (S.zOf (S.W ω))
                * (h (S.xOf (S.W ω)) - S.h₀ (S.xOf (S.W ω))) ∂μ)
            + (∫ ω, S.h₀ (S.xOf (S.W ω)) * q (S.zOf (S.W ω)) ∂μ)
            - ∫ ω, q (S.zOf (S.W ω)) * h (S.xOf (S.W ω)) ∂μ := by
            rw [integral_add h_int_diff_q₀ h_int_h₀q]
  -- Step 5: combine.
  rw [hΘ_eq, hRHS_eq, ← h_me_diff_eq, ← h_prim]
  unfold InverseProblemSystem.θ₀
  ring

/-- DR cancellation at the truth on the primal side: `Θ(h₀, q) = θ₀` for
every `q ∈ Qbar`. -/
theorem Θ_h₀_eq_θ₀
    (S : InverseProblemSystem Ω μ) {q₀ : S.𝒵 → ℝ}
    (hq₀ : S.DualSolution q₀)
    {q : S.𝒵 → ℝ} (hq : q ∈ S.Qbar) :
    S.Θ S.h₀ q = S.θ₀ := by
  have hmb := mixed_bias_identity S hq₀ S.h₀_mem hq
  apply sub_eq_zero.mp
  rw [hmb]
  simp

/-- DR cancellation at the truth on the dual side: `Θ(h, q₀) = θ₀` for
every `h ∈ Hbar`. -/
theorem Θ_q₀_eq_θ₀
    (S : InverseProblemSystem Ω μ) {q₀ : S.𝒵 → ℝ}
    (hq₀ : S.DualSolution q₀)
    {h : S.𝒳 → ℝ} (hh : h ∈ S.Hbar) :
    S.Θ h q₀ = S.θ₀ := by
  have hmb := mixed_bias_identity S hq₀ hh hq₀.mem
  apply sub_eq_zero.mp
  rw [hmb]
  simp

end MixedBias

end NPIV
end Estimation
end Causalean
