/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Automatic debiasing — linear regression-functional core

This file develops the linear regression-functional core for
`doc/basic_concepts/po/estimation/automatic_debiasing.tex`:

* `LinRegFnSys` — linear regression-functional system (data, regression
  class `H_γ`, observation-level linear functional `m_lin`, truth `g₀`).
* `L_of_m S` — the population linear functional `γ ↦ ∫ m_lin(z, γ) dP_Z`.
* `linRieszScore` — alias of `rieszScore` from `Estimation.OrthogonalMoments.Riesz`.
* Three orthogonality lemmas: mean-zero plus two directional zeros.
* `linRieszLoss` — Riesz loss.
* `linRieszLoss_excess_eq_l2dist`, `linRieszLoss_FOC_iff_representer`
  — excess-risk and first-order-characterization facts.

Re-uses (does NOT redefine) `RieszRepresentation`, `rieszScore`,
`rieszScore_meanZero`, `rieszScore_bilinearRem` from
`Causalean.Estimation.OrthogonalMoments.Riesz`.
-/

import Causalean.Estimation.OrthogonalMoments.Riesz
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-! # Automatic Debiasing for Linear Regression Functionals

This file develops the linear core of automatic debiasing for regression-based
targets. It defines the regression-functional system, constructs the population
linear functional and Riesz score, and proves the mean-zero, orthogonality, and
Riesz-loss identities that underlie the debiased estimator. -/

namespace Causalean.Estimation.OrthogonalMoments.AutoDebias

open MeasureTheory

/-- **Linear regression-functional system.**

A bundle packaging:

* the observation space `Z` with law `P_Z`;
* the regression-argument space `X` with law `P_X = (proj_X)_* P_Z`;
* an abstract regression class `H_γ` (an `ℝ`-vector space) together with
  an evaluation `γ_target : H_γ → X → ℝ`;
* an observation-level functional `m_lin : Z → H_γ → ℝ` that is
  ℝ-linear in its second argument;
* the regression truth `g₀ : H_γ`.

The "regression equation" is encoded operationally: the residual
`Y_obs − γ_target g₀ ∘ proj_X` is `L²(P_Z)`-orthogonal to every
measurable integrable function of `proj_X`.

To keep universe parameters tame, every type, instance, and function is
declared as a field of the structure. -/
structure LinRegFnSys where
  Z : Type*
  [Z_meas : MeasurableSpace Z]
  P_Z : Measure Z
  [P_Z_prob : IsProbabilityMeasure P_Z]
  X : Type*
  [X_meas : MeasurableSpace X]
  P_X : Measure X
  H_γ : Type*
  [H_γ_addCommGroup : AddCommGroup H_γ]
  [H_γ_module : Module ℝ H_γ]
  proj_X : Z → X
  proj_X_meas : Measurable proj_X
  Y_obs : Z → ℝ
  Y_obs_meas : Measurable Y_obs
  γ_target : H_γ → X → ℝ
  γ_target_add : ∀ (γ₁ γ₂ : H_γ) (x : X),
    γ_target (γ₁ + γ₂) x = γ_target γ₁ x + γ_target γ₂ x
  γ_target_smul : ∀ (c : ℝ) (γ : H_γ) (x : X),
    γ_target (c • γ) x = c * γ_target γ x
  m_lin : Z → H_γ → ℝ
  m_lin_addLeft : ∀ z (γ₁ γ₂ : H_γ), m_lin z (γ₁ + γ₂) = m_lin z γ₁ + m_lin z γ₂
  m_lin_smulLeft : ∀ (c : ℝ) z (γ : H_γ), m_lin z (c • γ) = c * m_lin z γ
  m_lin_meas : ∀ γ : H_γ, Measurable (fun z => m_lin z γ)
  g₀ : H_γ
  pushforward : P_X = P_Z.map proj_X
  regression_resid_orthog :
    ∀ α : X → ℝ, Measurable α →
      Integrable (fun z => α (proj_X z) * (Y_obs z - γ_target g₀ (proj_X z))) P_Z →
      ∫ z, α (proj_X z) * (Y_obs z - γ_target g₀ (proj_X z)) ∂P_Z = 0

attribute [instance] LinRegFnSys.Z_meas LinRegFnSys.P_Z_prob
  LinRegFnSys.X_meas LinRegFnSys.H_γ_addCommGroup LinRegFnSys.H_γ_module

/-- **Population linear functional** `L(γ) := ∫ m_lin(z, γ) dP_Z`. -/
noncomputable def L_of_m (S : LinRegFnSys) : S.H_γ → ℝ :=
  fun γ => ∫ z, S.m_lin z γ ∂S.P_Z

/-- Additivity of `L_of_m` on integrable summands. -/
theorem L_of_m_add (S : LinRegFnSys) (γ₁ γ₂ : S.H_γ)
    (h₁ : Integrable (fun z => S.m_lin z γ₁) S.P_Z)
    (h₂ : Integrable (fun z => S.m_lin z γ₂) S.P_Z) :
    L_of_m S (γ₁ + γ₂) = L_of_m S γ₁ + L_of_m S γ₂ := by
  unfold L_of_m
  have hpoint : (fun z => S.m_lin z (γ₁ + γ₂)) = fun z => S.m_lin z γ₁ + S.m_lin z γ₂ := by
    funext z; exact S.m_lin_addLeft z γ₁ γ₂
  rw [hpoint]; exact integral_add h₁ h₂

/-- ℝ-homogeneity of `L_of_m`. -/
theorem L_of_m_smul (S : LinRegFnSys) (c : ℝ) (γ : S.H_γ) :
    L_of_m S (c • γ) = c * L_of_m S γ := by
  unfold L_of_m
  have hpoint : (fun z => S.m_lin z (c • γ)) = fun z => c * S.m_lin z γ := by
    funext z; exact S.m_lin_smulLeft c z γ
  rw [hpoint]; exact integral_const_mul c (fun z => S.m_lin z γ)

/-- **Linear Riesz score**: alias of the generic `rieszScore`
applied to the linear regression-functional system's data. -/
noncomputable def linRieszScore (S : LinRegFnSys)
    (γ : S.H_γ) (α : S.X → ℝ) (θ : ℝ) (z : S.Z) : ℝ :=
  Causalean.Estimation.OrthogonalMoments.rieszScore S.γ_target (L_of_m S) S.proj_X S.Y_obs γ α θ z

/-- **Mean-zero of the debiased linear score at the truth.** -/
theorem linRieszScore_meanZero (S : LinRegFnSys)
    (rep : Causalean.Estimation.OrthogonalMoments.RieszRepresentation
            S.H_γ S.γ_target (L_of_m S) S.P_X)
    (h_α₀_resid_int :
      Integrable
        (fun z => rep.α₀ (S.proj_X z) * (S.Y_obs z - S.γ_target S.g₀ (S.proj_X z)))
        S.P_Z) :
    ∫ z, linRieszScore S S.g₀ rep.α₀ (L_of_m S S.g₀) z ∂S.P_Z = 0 := by
  unfold linRieszScore
  exact Causalean.Estimation.OrthogonalMoments.rieszScore_meanZero rep S.g₀ S.proj_X S.Y_obs
    (S.regression_resid_orthog rep.α₀ rep.α₀_meas h_α₀_resid_int)

/-- **Directional zero in the regression direction.**

The Gateaux derivative of the population debiased moment in the
`g`-direction at the truth equals zero — equivalently, the representer
identity for the perturbation `ν_g`. -/
theorem linRieszScore_directional_g_zero (S : LinRegFnSys)
    (rep : Causalean.Estimation.OrthogonalMoments.RieszRepresentation
            S.H_γ S.γ_target (L_of_m S) S.P_X)
    (ν_g : S.H_γ) :
    (∫ z, S.m_lin z ν_g ∂S.P_Z)
        - ∫ x, rep.α₀ x * S.γ_target ν_g x ∂S.P_X = 0 := by
  have hrep := rep.representation ν_g; unfold L_of_m at hrep; linarith

/-- **Directional zero in the representer direction.**

For any measurable perturbation `ν_α : X → ℝ` with integrable residual
product, the directional derivative of the population debiased moment in
the `α`-direction at the truth vanishes. -/
theorem linRieszScore_directional_α_zero (S : LinRegFnSys)
    (ν_α : S.X → ℝ) (hν_α_meas : Measurable ν_α)
    (h_int :
      Integrable
        (fun z => ν_α (S.proj_X z) * (S.Y_obs z - S.γ_target S.g₀ (S.proj_X z)))
        S.P_Z) :
    ∫ z, ν_α (S.proj_X z) * (S.Y_obs z - S.γ_target S.g₀ (S.proj_X z)) ∂S.P_Z = 0 := by
  exact S.regression_resid_orthog ν_α hν_α_meas h_int

/-- **Linear Riesz loss**:

  `L_m(α) := ∫ (γ_target α x)² dP_X − 2 · L_of_m S α`.

When `γ_target α = α` (i.e. the regression class is just `L²(P_X)`), this
matches the textbook form `E[α(X)² − 2 m(Z;α)]`. -/
noncomputable def linRieszLoss (S : LinRegFnSys) (α : S.H_γ) : ℝ :=
  ∫ x, (S.γ_target α x) ^ 2 ∂S.P_X - 2 * L_of_m S α

/-- **Excess Riesz loss equals the squared L²(P_X) distance to the
representer.** -/
theorem linRieszLoss_excess_eq_l2dist (S : LinRegFnSys)
    (α α₀_idx : S.H_γ)
    (rep : Causalean.Estimation.OrthogonalMoments.RieszRepresentation
            S.H_γ S.γ_target (L_of_m S) S.P_X)
    (hRep_eq_idx : ∀ x, rep.α₀ x = S.γ_target α₀_idx x)
    (h_int_α2 : Integrable (fun x => (S.γ_target α x) ^ 2) S.P_X)
    (h_int_α₀2 : Integrable (fun x => (S.γ_target α₀_idx x) ^ 2) S.P_X)
    (h_int_αα₀ : Integrable (fun x => S.γ_target α x * S.γ_target α₀_idx x) S.P_X)
    (h_int_diff_sq :
      Integrable (fun x => (S.γ_target α x - S.γ_target α₀_idx x) ^ 2) S.P_X) :
    linRieszLoss S α - linRieszLoss S α₀_idx
      = ∫ x, (S.γ_target α x - S.γ_target α₀_idx x) ^ 2 ∂S.P_X := by
  have h_int_α₀α : Integrable (fun x => S.γ_target α₀_idx x * S.γ_target α x) S.P_X := by
    simpa [mul_comm] using h_int_αα₀
  have hL_α : L_of_m S α = ∫ x, S.γ_target α₀_idx x * S.γ_target α x ∂S.P_X := by
    rw [rep.representation α]; congr 1; funext x; rw [hRep_eq_idx x]
  have hL_α₀ : L_of_m S α₀_idx = ∫ x, (S.γ_target α₀_idx x) ^ 2 ∂S.P_X := by
    rw [rep.representation α₀_idx]; congr 1; funext x; rw [hRep_eq_idx x]; ring
  unfold linRieszLoss
  rw [hL_α, hL_α₀]
  have hInt_expand : (∫ x, (S.γ_target α x - S.γ_target α₀_idx x) ^ 2 ∂S.P_X) =
      ∫ x, (S.γ_target α x) ^ 2 - 2 * (S.γ_target α₀_idx x * S.γ_target α x) +
        (S.γ_target α₀_idx x) ^ 2 ∂S.P_X := by
    have _ := h_int_diff_sq; apply integral_congr_ae; filter_upwards with x; ring
  rw [hInt_expand]
  have hsplit : (∫ x, (S.γ_target α x) ^ 2 - 2 * (S.γ_target α₀_idx x * S.γ_target α x) +
        (S.γ_target α₀_idx x) ^ 2 ∂S.P_X) = (∫ x, (S.γ_target α x) ^ 2 ∂S.P_X) -
      2 * (∫ x, S.γ_target α₀_idx x * S.γ_target α x ∂S.P_X) +
        (∫ x, (S.γ_target α₀_idx x) ^ 2 ∂S.P_X) := by
    calc
      (∫ x, (S.γ_target α x) ^ 2 - 2 * (S.γ_target α₀_idx x * S.γ_target α x) +
          (S.γ_target α₀_idx x) ^ 2 ∂S.P_X) =
          ∫ x, ((S.γ_target α x) ^ 2 - 2 * (S.γ_target α₀_idx x * S.γ_target α x)) +
            (S.γ_target α₀_idx x) ^ 2 ∂S.P_X := by
            apply integral_congr_ae; filter_upwards with x; ring
      _ = (∫ x, (S.γ_target α x) ^ 2 - 2 * (S.γ_target α₀_idx x * S.γ_target α x) ∂S.P_X) +
            (∫ x, (S.γ_target α₀_idx x) ^ 2 ∂S.P_X) := by
            exact integral_add (h_int_α2.sub (h_int_α₀α.const_mul 2)) h_int_α₀2
      _ = ((∫ x, (S.γ_target α x) ^ 2 ∂S.P_X) -
            (∫ x, 2 * (S.γ_target α₀_idx x * S.γ_target α x) ∂S.P_X)) +
            (∫ x, (S.γ_target α₀_idx x) ^ 2 ∂S.P_X) := by
            rw [integral_sub h_int_α2 (h_int_α₀α.const_mul 2)]
      _ = (∫ x, (S.γ_target α x) ^ 2 ∂S.P_X) - 2 *
          (∫ x, S.γ_target α₀_idx x * S.γ_target α x ∂S.P_X) +
          (∫ x, (S.γ_target α₀_idx x) ^ 2 ∂S.P_X) := by
            rw [integral_const_mul]
  rw [hsplit]; ring

private lemma linear_coeff_eq_zero_of_quad_nonneg {a b : ℝ} (ha : 0 ≤ a)
    (h : ∀ t : ℝ, 0 ≤ 2 * t * b + t ^ 2 * a) : b = 0 := by
  by_cases hz : a = 0
  · have hpos := h 1; have hneg := h (-1); nlinarith
  · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm hz); have key := h (-b / a)
    have hane : a ≠ 0 := ne_of_gt hapos; field_simp [hane] at key; nlinarith [sq_nonneg b]

/-- **First-order condition for Riesz loss minimizers** (Prop 4, first half).

`α₀_idx` is a (directional) minimizer of the Riesz loss along every line
`α₀_idx + t • ν` if and only if it indexes a Riesz representer in the sense
that `L(ν) = ∫ γ_target α₀_idx · γ_target ν dP_X` for every `ν ∈ H_γ`. -/
theorem linRieszLoss_FOC_iff_representer (S : LinRegFnSys)
    (α₀_idx : S.H_γ)
    (h_int_quad :
      ∀ ν : S.H_γ, ∀ t : ℝ,
        Integrable (fun x => (S.γ_target (α₀_idx + t • ν) x) ^ 2) S.P_X)
    (h_int_L : ∀ ν : S.H_γ, Integrable (fun z => S.m_lin z ν) S.P_Z)
    (h_int_α₀ν_X :
      ∀ ν : S.H_γ,
        Integrable (fun x => S.γ_target α₀_idx x * S.γ_target ν x) S.P_X) :
    (∀ ν : S.H_γ, ∀ t : ℝ,
        linRieszLoss S α₀_idx ≤ linRieszLoss S (α₀_idx + t • ν))
      ↔ (∀ ν : S.H_γ,
          L_of_m S ν = ∫ x, S.γ_target α₀_idx x * S.γ_target ν x ∂S.P_X) := by
  have hloss : ∀ ν : S.H_γ, ∀ t : ℝ, linRieszLoss S (α₀_idx + t • ν) - linRieszLoss S α₀_idx =
      2 * t * ((∫ x, S.γ_target α₀_idx x * S.γ_target ν x ∂S.P_X) - L_of_m S ν) +
        t ^ 2 * (∫ x, (S.γ_target ν x) ^ 2 ∂S.P_X) := by
    intro ν t
    have hα₀2 : Integrable (fun x => (S.γ_target α₀_idx x) ^ 2) S.P_X := by
      simpa using h_int_quad ν 0
    have hν2 : Integrable (fun x => (S.γ_target ν x) ^ 2) S.P_X := by
      have hsum : Integrable (fun x => (S.γ_target α₀_idx x) ^ 2 +
          2 * (S.γ_target α₀_idx x * S.γ_target ν x) + (S.γ_target ν x) ^ 2) S.P_X := by
        refine (h_int_quad ν 1).congr ?_; filter_upwards with x
        rw [S.γ_target_add, S.γ_target_smul]; ring
      have hbase : Integrable (fun x => (S.γ_target α₀_idx x) ^ 2 +
          2 * (S.γ_target α₀_idx x * S.γ_target ν x)) S.P_X :=
        hα₀2.add ((h_int_α₀ν_X ν).const_mul 2)
      refine (hsum.sub hbase).congr ?_
      filter_upwards with x
      change ((S.γ_target α₀_idx x) ^ 2 + 2 * (S.γ_target α₀_idx x * S.γ_target ν x) +
          (S.γ_target ν x) ^ 2 - ((S.γ_target α₀_idx x) ^ 2 +
          2 * (S.γ_target α₀_idx x * S.γ_target ν x))) = (S.γ_target ν x) ^ 2
      ring
    have hsq : (∫ x, (S.γ_target (α₀_idx + t • ν) x) ^ 2 ∂S.P_X) =
        (∫ x, (S.γ_target α₀_idx x) ^ 2 ∂S.P_X) +
          2 * t * (∫ x, S.γ_target α₀_idx x * S.γ_target ν x ∂S.P_X) +
          t ^ 2 * (∫ x, (S.γ_target ν x) ^ 2 ∂S.P_X) := by
      have hpoint : (fun x => (S.γ_target (α₀_idx + t • ν) x) ^ 2) = fun x =>
          (S.γ_target α₀_idx x) ^ 2 + (2 * t) * (S.γ_target α₀_idx x * S.γ_target ν x) +
            t ^ 2 * (S.γ_target ν x) ^ 2 := by funext x; rw [S.γ_target_add, S.γ_target_smul]; ring
      rw [hpoint]
      calc
        (∫ x, (S.γ_target α₀_idx x) ^ 2 + (2 * t) * (S.γ_target α₀_idx x * S.γ_target ν x) +
              t ^ 2 * (S.γ_target ν x) ^ 2 ∂S.P_X) =
            (∫ x, ((S.γ_target α₀_idx x) ^ 2 + (2 * t) * (S.γ_target α₀_idx x * S.γ_target ν x)) +
              t ^ 2 * (S.γ_target ν x) ^ 2 ∂S.P_X) := by
              apply integral_congr_ae; filter_upwards with x; ring
        _ = (∫ x, (S.γ_target α₀_idx x) ^ 2 + (2 * t) *
              (S.γ_target α₀_idx x * S.γ_target ν x) ∂S.P_X) +
              (∫ x, t ^ 2 * (S.γ_target ν x) ^ 2 ∂S.P_X) := by
              exact integral_add (hα₀2.add ((h_int_α₀ν_X ν).const_mul (2 * t)))
                (hν2.const_mul (t ^ 2))
        _ = ((∫ x, (S.γ_target α₀_idx x) ^ 2 ∂S.P_X) +
              (∫ x, (2 * t) * (S.γ_target α₀_idx x * S.γ_target ν x) ∂S.P_X)) +
              (∫ x, t ^ 2 * (S.γ_target ν x) ^ 2 ∂S.P_X) := by
              rw [integral_add hα₀2 ((h_int_α₀ν_X ν).const_mul (2 * t))]
        _ = (∫ x, (S.γ_target α₀_idx x) ^ 2 ∂S.P_X) +
            2 * t * (∫ x, S.γ_target α₀_idx x * S.γ_target ν x ∂S.P_X) +
            t ^ 2 * (∫ x, (S.γ_target ν x) ^ 2 ∂S.P_X) := by
              rw [integral_const_mul, integral_const_mul]
    unfold linRieszLoss; rw [hsq]
    rw [L_of_m_add S α₀_idx (t • ν) (h_int_L α₀_idx) (h_int_L (t • ν)), L_of_m_smul S t ν]; ring
  constructor
  · intro hmin ν
    let b : ℝ := (∫ x, S.γ_target α₀_idx x * S.γ_target ν x ∂S.P_X) - L_of_m S ν
    let a : ℝ := ∫ x, (S.γ_target ν x) ^ 2 ∂S.P_X
    have ha : 0 ≤ a := by dsimp [a]; exact integral_nonneg (fun x => sq_nonneg (S.γ_target ν x))
    have hquad : ∀ t : ℝ, 0 ≤ 2 * t * b + t ^ 2 * a := by
      intro t; dsimp [a, b]; linarith [hmin ν t, hloss ν t]
    have hb := linear_coeff_eq_zero_of_quad_nonneg ha hquad; dsimp [b] at hb; linarith
  · intro hrep ν t
    have hb : (∫ x, S.γ_target α₀_idx x * S.γ_target ν x ∂S.P_X) - L_of_m S ν = 0 := by
      rw [← hrep ν]; simp
    rw [← sub_nonneg, hloss ν t, hb]
    simpa using mul_nonneg (sq_nonneg t) (integral_nonneg (fun x => sq_nonneg (S.γ_target ν x)))

end Causalean.Estimation.OrthogonalMoments.AutoDebias
