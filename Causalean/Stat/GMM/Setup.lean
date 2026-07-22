/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# GMM problem setup: moment model, influence function, and efficiency

The statistical layer over `Causalean/Stat/GMM/VarianceAlgebra.lean`.  A
`GMMProblem` bundles a moment function `g : E → X → F` (parameter `θ : E`,
moment vector valued in `F`, `dim E ≤ dim F`) with the regularity needed for
the GMM asymptotic theory: population identification `∫ g(θ₀) dP = 0`, a
Jacobian `G = ∂_θ ∫ g(θ) dP |_{θ₀}`, the moment covariance `Cov` (the second
moment of `g(θ₀)`), a symmetric weighting `W`, and the inverse witnesses making
`Cov`, `GᵀWG`, `GᵀCov⁻¹G` invertible (full-rank / non-degeneracy assumptions,
exactly analogous to `ZEstimatorRegularity.J₀_inv`).

From this we read off:

* `gmmScore` — the combined estimating function `ψ(θ,x) = GᵀW g(θ,x)`, whose
  empirical zero is the (linearized) GMM estimator;
* `gmmIF` — the influence function `−(GᵀWG)⁻¹GᵀW g(θ₀,·)`;
* `GMMProblem.asympVar` — the sandwich asymptotic variance `gmmSandwich`;
* `GMMProblem.efficiency` — Hansen's optimal-weighting theorem in statistical
  terms: the sandwich variance dominates the efficient variance `(GᵀCov⁻¹G)⁻¹`
  in the Löwner order, with equality at `W = Cov⁻¹`.

Spec: Hansen (1982); Newey & McFadden (1994), §3.
-/

import Causalean.Stat.GMM.VarianceAlgebra
import Causalean.Stat.CLT.SecondMomentOperator
import Mathlib.Analysis.Calculus.FDeriv.Basic

/-! # Generalized Method of Moments Setup

This file packages the statistical data for generalized method of moments.  A
`GMMProblem` records the moment function `g`, target `θ₀`, weighting operator
`W`, Jacobian `G`, covariance operator `Cov`, and the two-sided inverse
witnesses needed for `Cov`, `GᵀWG`, and `GᵀCov⁻¹G`.

The public interface exposes `gmmScore`, `gmmIF`, and the bundled
`GMMProblem.score`, `GMMProblem.influence`, `GMMProblem.asympVar`, and
`GMMProblem.effVar`.  The main theorem `GMMProblem.efficiency` applies the
operator-algebra result from `Causalean.Stat.GMM.VarianceAlgebra` to show that
the sandwich variance for an arbitrary symmetric weighting dominates the
efficient inverse-covariance variance in the Loewner order. -/

namespace Causalean.Stat

open MeasureTheory ContinuousLinearMap
open scoped RealInnerProductSpace

variable {E F X : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  [MeasurableSpace X]

/-- The **combined GMM score** `ψ(θ,x) = GᵀW g(θ,x) : E`.  Setting its empirical
mean to zero is the first-order condition of the GMM criterion
`ḡ(θ)ᵀ W ḡ(θ)` (after fixing the Jacobian weight at its population value);
the GMM estimator is the resulting Z-estimator. -/
noncomputable def gmmScore (G : E →L[ℝ] F) (W : F →L[ℝ] F) (g : E → X → F) :
    E → X → E :=
  fun θ x => adjoint G (W (g θ x))

/-- The **GMM influence function** `−(GᵀWG)⁻¹ GᵀW g(θ₀,·)`. -/
noncomputable def gmmIF (G : E →L[ℝ] F) (W : F →L[ℝ] F) (breadInv : E →L[ℝ] E)
    (g : E → X → F) (θ₀ : E) : X → E :=
  fun x => -(breadInv (adjoint G (W (g θ₀ x))))

/-- **GMM problem.**  Moment model `g` with parameter truth `θ₀`, weighting `W`,
Jacobian `G`, covariance `Cov`, and the inverse witnesses for `Cov`, `GᵀWG`,
`GᵀCov⁻¹G`. -/
structure GMMProblem (P : Measure X) where
  /-- Moment function: `g θ x ∈ F`, with `θ` the parameter and `x` the datum. -/
  g : E → X → F
  /-- The parameter truth. -/
  θ₀ : E
  /-- Symmetric weighting operator on the moment space. -/
  W : F →L[ℝ] F
  /-- `W` is self-adjoint. -/
  hWsa : adjoint W = W
  /-- Jacobian `G = ∂_θ ∫ g(θ) dP |_{θ₀}` of the population moment. -/
  G : E →L[ℝ] F
  /-- Population identification: the moment vanishes at the truth. -/
  identification : ∫ x, g θ₀ x ∂P = 0
  /-- The moment vector at the truth is measurable. -/
  g_meas : Measurable (g θ₀)
  /-- The moment vector at the truth is square-integrable. -/
  finite_var : Integrable (fun x => ‖g θ₀ x‖ ^ 2) P
  /-- `G` is the Fréchet derivative of `θ ↦ ∫ g(θ) dP` at `θ₀`. -/
  jac_spec : HasFDerivAt (fun θ => ∫ x, g θ x ∂P) G θ₀
  /-- Moment covariance operator: the second moment of `g(θ₀)`. -/
  Cov : F →L[ℝ] F
  /-- `Cov` is the second-moment (covariance) operator of the moment vector. -/
  hCov : ∀ t s : F, ⟪Cov t, s⟫ = ∫ x, ⟪t, g θ₀ x⟫ * ⟪s, g θ₀ x⟫ ∂P
  /-- Inverse covariance `Cov⁻¹`. -/
  CovInv : F →L[ℝ] F
  CovInv_left : CovInv ∘L Cov = ContinuousLinearMap.id ℝ F
  CovInv_right : Cov ∘L CovInv = ContinuousLinearMap.id ℝ F
  /-- Inverse bread `(GᵀWG)⁻¹` (full-rank `G`, non-degenerate `W`). -/
  breadInv : E →L[ℝ] E
  breadInv_left : breadInv ∘L gmmBread G W = ContinuousLinearMap.id ℝ E
  breadInv_right : gmmBread G W ∘L breadInv = ContinuousLinearMap.id ℝ E
  /-- Inverse efficient bread `(GᵀCov⁻¹G)⁻¹`. -/
  effInv : E →L[ℝ] E
  effInv_left : effInv ∘L gmmBread G CovInv = ContinuousLinearMap.id ℝ E
  effInv_right : gmmBread G CovInv ∘L effInv = ContinuousLinearMap.id ℝ E

namespace GMMProblem

variable {P : Measure X} (prob : GMMProblem (E := E) (F := F) P)

/-- The combined score of the problem, `ψ(θ,x) = GᵀW g(θ,x)`. -/
noncomputable def score : E → X → E := gmmScore prob.G prob.W prob.g

/-- The influence function of the problem. -/
noncomputable def influence : X → E :=
  gmmIF prob.G prob.W prob.breadInv prob.g prob.θ₀

/-- The **sandwich asymptotic variance** `(GᵀWG)⁻¹ GᵀW Cov WG (GᵀWG)⁻¹`. -/
noncomputable def asympVar : E →L[ℝ] E :=
  gmmSandwich prob.G prob.W prob.Cov prob.breadInv

/-- The **efficient asymptotic variance** `(GᵀCov⁻¹G)⁻¹`. -/
noncomputable def effVar : E →L[ℝ] E := prob.effInv

/-- The covariance operator is positive — it is a second moment. -/
theorem cov_isPositive : prob.Cov.IsPositive := by
  refine ⟨fun t s => ?_, fun t => ?_⟩
  · -- symmetric: `⟪Cov t, s⟫ = ⟪Cov s, t⟫` (both `∫ ⟪t,g⟫⟪s,g⟫`), then flip.
    change ⟪prob.Cov t, s⟫ = ⟪t, prob.Cov s⟫
    have key : ⟪prob.Cov t, s⟫ = ⟪prob.Cov s, t⟫ := by
      rw [prob.hCov t s, prob.hCov s t]
      exact integral_congr_ae (ae_of_all _ fun x => by ring)
    exact key.trans (real_inner_comm t (prob.Cov s))
  · -- nonnegative quadratic form: `⟪Cov t, t⟫ = ∫ ⟪t,g⟫² ≥ 0`.
    rw [ContinuousLinearMap.reApplyInnerSelf_apply]
    have hre : RCLike.re ⟪prob.Cov t, t⟫ = ⟪prob.Cov t, t⟫ := rfl
    rw [hre, prob.hCov t t]
    exact integral_nonneg fun x => mul_self_nonneg _

/-- **GMM optimal-weighting theorem (Hansen 1982), statistical form.** The
sandwich asymptotic variance dominates the efficient variance `(GᵀCov⁻¹G)⁻¹` in
the Löwner order: `asympVar − effVar` is a positive operator. -/
theorem efficiency : (prob.asympVar - prob.effVar).IsPositive :=
  gmm_efficiency prob.G prob.W prob.Cov prob.CovInv prob.hWsa prob.cov_isPositive
    prob.CovInv_left prob.CovInv_right prob.breadInv prob.breadInv_left
    prob.breadInv_right prob.effInv prob.effInv_left prob.effInv_right

end GMMProblem

end Causalean.Stat
