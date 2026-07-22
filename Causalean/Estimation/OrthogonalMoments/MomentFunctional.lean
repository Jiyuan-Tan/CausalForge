/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Abstract moment functional bundle for the general DML framework

This file defines the abstract `GeneralMoment` structure which packages a
moment functional `m : H → Z → ℝ → ℝ` together with the truth nuisance
`η₀ : H`, the target parameter `θ₀ : ℝ`, the perturbation set `H_ε ⊆ H`,
and the bilinear seminorm pair `(ρ₁, ρ₂)` used to express product-rate
remainders.

See `docs/superpowers/specs/2026-05-06-general-dml-framework-design.md` §4.1.
-/

import Causalean.Estimation.ATE.Setup
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Algebra.Module.Basic

/-! # Abstract Moment Functionals

This file defines the moment-functional interface used by the double machine
learning layer. The interface records the observed-data moment, the true
nuisance and scalar target, the local perturbation set, bilinear seminorms for
product-rate bounds, and the nonzero Jacobian of the population moment. Concrete
double-machine-learning instances reduce to filling this interface, which
centralizes the generic asymptotic-linearity machinery. -/

namespace Causalean
namespace Estimation
namespace OrthogonalMoments

open MeasureTheory

/-- A general moment records the score, truth, target, perturbation set,
bilinear seminorms, measurability, and nonzero population Jacobian needed by the
abstract double-machine-learning framework.

This is the Chernozhukov-form interface for scalar targets: the Jacobian is the
parameter derivative of the population moment at the truth, and its
nonsingularity makes the inverse Jacobian well-defined.

* `m η z θ`     — the moment functional, parametric in nuisance `η`, data `z`,
                  and parameter `θ`.
* `η₀`          — the truth nuisance.
* `θ₀`          — the truth parameter.
* `H_ε`         — perturbation set; nuisance estimates are required to live here.
* `ρ₁ η η'`     — first bilinear seminorm slot (e.g., outcome-regression L²).
* `ρ₂ η η'`     — second bilinear seminorm slot (e.g., propensity L²).
* `m_meas`      — joint measurability witness for `m η · θ`.
* `η₀_mem`      — `η₀ ∈ H_ε`.
* `J₀`          — Jacobian `∂_θ ∫ m(η₀, ·, θ) dP_Z |_{θ=θ₀}` of the population
                  moment in the parameter direction.  For AIPW (linear score
                  `m(η, z, θ) = ψ(η, z) − θ`), `J₀ = −1`.  This interface is
                  the scalar-target form of the orthogonal-moment framework.
* `J₀_ne_zero`  — non-singularity witness; `J₀⁻¹` is well-defined. -/
structure GeneralMoment
    (Ω : Type*) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (Z : Type*) [MeasurableSpace Z] (P_Z : MeasureTheory.Measure Z)
    (H : Type*) [AddCommGroup H] [Module ℝ H] where
  m : H → Z → ℝ → ℝ
  η₀ : H
  θ₀ : ℝ
  H_ε : Set H
  ρ₁ : H → H → NNReal
  ρ₂           : H → H → NNReal
  m_meas       : ∀ η θ, Measurable (fun z => m η z θ)
  η₀_mem       : η₀ ∈ H_ε
  J₀           : ℝ
  J₀_ne_zero   : J₀ ≠ 0

namespace GeneralMoment

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
         {Z : Type*} [MeasurableSpace Z] {P_Z : MeasureTheory.Measure Z}
         {H : Type*} [AddCommGroup H] [Module ℝ H]

/-- The inverse Jacobian is the reciprocal of the nonzero population Jacobian.

For the AIPW linear score, the Jacobian is minus one, so the inverse Jacobian is
also minus one. -/
noncomputable def J₀_inv (M : GeneralMoment Ω μ Z P_Z H) : ℝ := M.J₀⁻¹

/-- Multiplying the population Jacobian by its inverse gives one. -/
@[simp] lemma J₀_mul_J₀_inv (M : GeneralMoment Ω μ Z P_Z H) :
    M.J₀ * M.J₀_inv = 1 := by
  unfold J₀_inv
  exact mul_inv_cancel₀ M.J₀_ne_zero

end GeneralMoment

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
         {Z : Type*} [MeasurableSpace Z] {P_Z : MeasureTheory.Measure Z}
         {H : Type*} [AddCommGroup H] [Module ℝ H]

/-- The moment has zero population mean at the true nuisance and target. -/
def MeanZero (M : GeneralMoment Ω μ Z P_Z H) : Prop :=
  ∫ z, M.m M.η₀ z M.θ₀ ∂P_Z = 0

/-- The perturbation set is closed under line segments from the true nuisance to
any nuisance already in the set. -/
def H_ε_PerturbClosed (M : GeneralMoment Ω μ Z P_Z H) : Prop :=
  ∀ η ∈ M.H_ε, ∀ t ∈ Set.Icc (0 : ℝ) 1, M.η₀ + t • (η - M.η₀) ∈ M.H_ε

/-- A linear moment is a general moment whose score is affine in the scalar
target parameter.

It carries the coefficient and constant terms of the linear-score
decomposition, their measurability, and the consistency condition saying that
the Jacobian is the population mean of the coefficient at the truth. AIPW is the
canonical instance with constant coefficient minus one. -/
structure LinearMoment
    (Ω : Type*) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (Z : Type*) [MeasurableSpace Z] (P_Z : MeasureTheory.Measure Z)
    (H : Type*) [AddCommGroup H] [Module ℝ H]
    extends GeneralMoment Ω μ Z P_Z H where
  m_a : H → Z → ℝ
  m_b : H → Z → ℝ
  m_a_meas : ∀ η, Measurable (m_a η)
  m_b_meas : ∀ η, Measurable (m_b η)
  m_decomp : ∀ η z θ, m η z θ = m_a η z * θ + m_b η z
  /-- Jacobian field is consistent with the linear decomposition:
  `J₀ = ∫ m_a(η₀, z) dP_Z`. -/
  J₀_eq     : J₀ = ∫ z, m_a η₀ z ∂P_Z

end OrthogonalMoments
end Estimation
end Causalean
