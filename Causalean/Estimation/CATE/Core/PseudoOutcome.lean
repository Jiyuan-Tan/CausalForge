/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# DR pseudo-outcome for CATE estimation

This file defines Kennedy's uncentered AIPW pseudo-outcome `phi_eta` and
its truth specialization `phi_0`, as in
`def:est-cate-dr-pseudo-outcome` of
`doc/basic_concepts/po/estimation/dr_learner_cate.tex`:

    φ_η(z) = μ₁(x) − μ₀(x)
              + (a / π(x)) (y − μ₁(x))
              − ((1 − a) / (1 − π(x))) (y − μ₀(x)).

Algebraically `φ_η(z) = aipwMoment z η.μ_fn η.e_fn 0`, i.e. the AIPW moment
with the centering parameter `θ` set to zero.  We re-use the existing
`NuisanceVec γ` substrate from `Estimation/ATE/AIPWMoment.lean`.
-/

import Causalean.Estimation.CATE.Setup
import Causalean.Estimation.ATE.Score.AIPWMoment

/-!
Defines doubly robust pseudo-outcomes for conditional average treatment effect
estimation. The main definitions are `phi_eta`, the uncentered AIPW
pseudo-outcome at an arbitrary nuisance vector, and `phi₀`, its specialization
to the truth nuisance carried by a `CATEEstimationSystem`. The lemmas
`measurable_phi_eta` and `measurable_phi₀` provide the measurability facts used
by the conditional-mean, bias, and orthogonal-learning developments.
-/

namespace Causalean
namespace Estimation
namespace CATE

open MeasureTheory ProbabilityTheory Filter Topology Causalean.PO Causalean.Estimation.ATE

/-! ## DR pseudo-outcomes -/

variable {γ : Type*} [MeasurableSpace γ]

/-- Uncentered AIPW pseudo-outcome (Kennedy's `φ_η`):

    φ_η(z) := μ_fn 1 x − μ_fn 0 x
              + (a / e_fn x) (y − μ_fn 1 x)
              − ((1 − a) / (1 − e_fn x)) (y − μ_fn 0 x),

equivalently `aipwMoment z η.μ_fn η.e_fn 0`. -/
noncomputable def phi_eta (z : γ × Bool × ℝ) (η : NuisanceVec γ) : ℝ :=
  BackdoorEstimationSystem.aipwMoment z η.μ_fn η.e_fn 0

variable {P : POSystem} [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]

/-- True DR pseudo-outcome: `φ_0(z) := φ_{η_0}(z)` where `η_0` is the truth
nuisance vector carried by the back-door substrate of `S`. -/
noncomputable def phi₀ (S : CATEEstimationSystem P γ) (z : γ × Bool × ℝ) : ℝ :=
  phi_eta z S.toBackdoorEstimationSystem.η₀

/-! ## Measurability of the DR pseudo-outcomes -/

/-- The uncentered AIPW pseudo-outcome is measurable in the data argument.

Proof outline: mirror the proof of `measurable_ψ_AIPW` in
`Estimation/ATE/MeanZero.lean` lines 36–54, replacing `S.μ_val` with
`η.μ_fn` and `S.e_val` with `η.e_fn`, and noting that `aipwMoment` with
`θ = 0` differs from `ψ_AIPW` only by a constant subtraction that has
already been cleared. -/
lemma measurable_phi_eta (η : NuisanceVec γ) :
    Measurable (fun z : γ × Bool × ℝ => phi_eta z η) := by
  unfold phi_eta BackdoorEstimationSystem.aipwMoment BackdoorEstimationSystem.indA
    BackdoorEstimationSystem.projX BackdoorEstimationSystem.projA
    BackdoorEstimationSystem.projY
  have hx : Measurable (fun z : γ × Bool × ℝ => z.1) := measurable_fst
  have hy : Measurable (fun z : γ × Bool × ℝ => z.2.2) := by measurability
  have hμt : Measurable (fun z : γ × Bool × ℝ => η.μ_fn true z.1) :=
    (η.μ_meas true).comp hx
  have hμf : Measurable (fun z : γ × Bool × ℝ => η.μ_fn false z.1) :=
    (η.μ_meas false).comp hx
  have he : Measurable (fun z : γ × Bool × ℝ => η.e_fn z.1) :=
    η.e_meas.comp hx
  have hind : Measurable (fun z : γ × Bool × ℝ =>
      if z.2.1 = true then (1 : ℝ) else 0) := by
    have ha : Measurable (fun z : γ × Bool × ℝ => z.2.1) := by measurability
    exact (Measurable.of_discrete
      (f := fun b : Bool => if b = true then (1 : ℝ) else 0)).comp ha
  exact ((((hμt.sub hμf).add ((hind.div he).mul (hy.sub hμt))).sub
    (((measurable_const.sub hind).div (measurable_const.sub he)).mul
      (hy.sub hμf))).sub measurable_const)

/-- The true DR pseudo-outcome `φ_0` is measurable.

Proof outline: apply `measurable_phi_eta` at `η := S.toBackdoorEstimationSystem.η₀`. -/
lemma measurable_phi₀ (S : CATEEstimationSystem P γ) :
    Measurable (fun z : γ × Bool × ℝ => phi₀ S z) := by
  unfold phi₀
  exact measurable_phi_eta _

end CATE
end Estimation
end Causalean
