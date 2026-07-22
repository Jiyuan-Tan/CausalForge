/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# DR-Learner causal instantiation of the orthogonal statistical-learning framework

This file builds a `LearningSystem` whose data is the CATE observation triple
`(X, A, Y)`, whose loss is the AIPW pseudo-outcome
squared error

    ℓ_DR(z; θ, η) := (φ_η(z) − eval θ z.1)²,

and whose target `θ₀` is a witness to `eval θ₀ = τ_val` (the value-space
CATE) and minimizes the true-nuisance population risk over the target class.
We then state the headline orthogonality lemma
`prop:est-osl-dr-loss-orthogonal`: this loss is Neyman-orthogonal at
`(τ₀, h₀)` in the sense of `def:est-osl-neyman-loss`.

The target type `Θ` is left as a free `NormedAddCommGroup`/
`InnerProductSpace ℝ` parameter (mirroring the generic `LearningSystem`); the
candidate-evaluation map `eval : Θ → γ → ℝ` connects the abstract `Θ` to
the concrete CATE function class.  This way the file is reusable for both
the function-space view (`Θ := L²(P_X)`) and the finite-dimensional view
(`Θ := EuclideanSpace ℝ (Fin K)`).

The nuisance space `G := NuisanceVec γ` already carries `AddCommGroup`
and `Module ℝ` instances (see `Estimation/ATE/AIPWMoment.lean`), so the
typeclass requirements of `LearningSystem` are met without changing the generic
framework.

See `doc/basic_concepts/po/estimation/orthogonal_statistical_learning.tex`,
`prop:est-osl-dr-loss-orthogonal` (lines 143–160).
-/

import Causalean.Estimation.OrthogonalLearning.Population.NeymanOrthogonal
import Causalean.Estimation.CATE.Core.PseudoOutcome
import Causalean.Estimation.CATE.Core.PseudoOutcomeMean
import Causalean.Estimation.CATE.Core.ConditionalBias

/-!
Builds the DR-Learner orthogonal-learning system for CATE estimation. It
defines the bounded nuisance slice `BoundedNuisanceDirs`, target-minimization
predicates for the ordinary and clamped risks, and the `drLearningSystem`
instance. The theorem `drNeymanOrthog_witness` adapts abstract score-flatness
and dominated-convergence hypotheses into a `NeymanOrthogLoss` witness for the
DR-Learner squared loss.
-/

namespace Causalean
namespace Estimation
namespace OrthogonalLearning

open MeasureTheory ProbabilityTheory Filter Topology
  Causalean.PO Causalean.Estimation.ATE Causalean.Estimation.CATE

/-! ## DR-Learner orthogonal-learning system -/

/-- Bounded-direction nuisance slice anchored at `η₀`.

`BoundedNuisanceDirs η₀` is the set of `η : NuisanceVec γ` whose
deviation `η − η₀` has uniformly bounded outcome-regression and
propensity components.  This is the natural ambient slice for the
Neyman-orthogonality argument: `dr_scoreZero_of_bounded` (in
`Estimation/CATE/OrthogonalLearning/DRLearner/Analytic.lean`) discharges the integrated score-zero
obligation precisely on this set, so taking
`drLearningSystem.G_set := BoundedNuisanceDirs η₀` lets the abstract
`LearningSystem`-level orthogonality conclusion be hypothesis-free without
relying on integral-defaults-to-zero conventions for unbounded
directions.

The set is a vector subspace of `NuisanceVec γ` (closed under sums and
scalar multiples) and contains `η₀` itself (witnessed by `Cμ = Ce = 0`).
-/
def BoundedNuisanceDirs
    {γ : Type*} [MeasurableSpace γ] (η₀ : NuisanceVec γ) :
    Set (NuisanceVec γ) :=
  { η | (∃ Cμ : ℝ, ∀ b : Bool, ∀ x : γ, |(η - η₀).μ_fn b x| ≤ Cμ) ∧
        (∃ Ce : ℝ, ∀ x : γ, |(η - η₀).e_fn x| ≤ Ce) }

/-- The anchor `η₀` belongs to `BoundedNuisanceDirs η₀` (with `Cμ = Ce = 0`).
-/
lemma anchor_mem_boundedNuisanceDirs
    {γ : Type*} [MeasurableSpace γ] (η₀ : NuisanceVec γ) :
    η₀ ∈ BoundedNuisanceDirs η₀ := by
  refine ⟨⟨0, ?_⟩, ⟨0, ?_⟩⟩
  · intro b x
    have hμ : (η₀ - η₀).μ_fn b x = 0 := by
      change η₀.μ_fn b x - η₀.μ_fn b x = 0
      ring
    rw [hμ, abs_zero]
  · intro x
    have he : (η₀ - η₀).e_fn x = 0 := by
      change η₀.e_fn x - η₀.e_fn x = 0
      ring
    rw [he, abs_zero]

/-- The DR-Learner target `θ₀` minimizes the population squared-loss risk
against the true nuisance over the candidate target class.

This is the concrete CATE-side form of the `LearningSystem` target condition:
for every admissible target, the risk of the candidate whose evaluation equals
the value-space CATE is no larger than the risk of that target. -/
def DRThetaMinimizes
    {P : POSystem} {γ : Type*} [MeasurableSpace γ]
    [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
    (S : CATEEstimationSystem P γ)
    {Θ : Type*} (Θ_set : Set Θ) (θ₀ : Θ) (eval : Θ → γ → ℝ) : Prop :=
  ∀ θ ∈ Θ_set,
    ∫ z, (phi_eta z S.toBackdoorEstimationSystem.η₀ - eval θ₀ z.1)^2
        ∂S.toBackdoorEstimationSystem.P_Z
      ≤
    ∫ z, (phi_eta z S.toBackdoorEstimationSystem.η₀ - eval θ z.1)^2
        ∂S.toBackdoorEstimationSystem.P_Z

/-- The DR-Learner target `θ₀` minimizes the clamped true-nuisance squared
loss used by almost-everywhere empirical-process reductions.

For a clamp radius `b`, every admissible target has clamped true-nuisance
population risk at least as large as that of the target whose evaluation is the
value-space CATE. -/
def DRClampedThetaMinimizes
    {P : POSystem} {γ : Type*} [MeasurableSpace γ]
    [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
    (S : CATEEstimationSystem P γ)
    {Θ : Type*} (Θ_set : Set Θ) (θ₀ : Θ) (eval : Θ → γ → ℝ) (b : ℝ) : Prop :=
  ∀ θ ∈ Θ_set,
    ∫ z, max (-b)
          (min b ((phi_eta z S.toBackdoorEstimationSystem.η₀ - eval θ₀ z.1)^2))
        ∂S.toBackdoorEstimationSystem.P_Z
      ≤
    ∫ z, max (-b)
          (min b ((phi_eta z S.toBackdoorEstimationSystem.η₀ - eval θ z.1)^2))
        ∂S.toBackdoorEstimationSystem.P_Z

/-- The DR-Learner orthogonal-learning system: a `LearningSystem` whose data law is the CATE
observation triple's joint law `P_Z`, target space `Θ` is a
user-provided convex subset of an inner-product space (with a candidate
evaluation map `eval : Θ → γ → ℝ`), nuisance space `G := NuisanceVec γ`,
and loss

    ℓ z θ η := (phi_eta z η − eval θ z.1)².

The argument `eval_θ₀ : ∀ x, eval θ₀ x = S.τ_val x` is the truth-witness
identifying `θ₀` with the value-space CATE, and `θ₀_minimizes` states that
this candidate minimizes the true-nuisance population squared-loss risk over
`Θ_set`. The `G_set` is the bounded-direction slice `BoundedNuisanceDirs η₀`;
downstream callers can restrict further (e.g. to the strict-overlap slice
`H_ε`) if needed.

This is the orthogonal-learning-side analogue of `BackdoorEstimationSystem.aipwSystem`
in `Estimation/OrthogonalMoments/AIPWInstance.lean`. -/
noncomputable def drLearningSystem
    {P : POSystem} {γ : Type*} [MeasurableSpace γ]
    [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
    (S : CATEEstimationSystem P γ)
    (Θ : Type*) [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ]
    (Θ_set : Set Θ) (Θ_convex : Convex ℝ Θ_set)
    (θ₀ : Θ) (θ₀_mem : θ₀ ∈ Θ_set)
    (eval : Θ → γ → ℝ)
    (eval_meas : ∀ θ, Measurable (eval θ))
    (_eval_θ₀ : ∀ x, eval θ₀ x = S.τ_val x)
    (θ₀_minimizes : DRThetaMinimizes S Θ_set θ₀ eval) :
    LearningSystem P.Ω P.μ (γ × Bool × ℝ) S.toBackdoorEstimationSystem.P_Z
      Θ (NuisanceVec γ) where
  Θ_set    := Θ_set
  Θ_convex := Θ_convex
  θ₀       := θ₀
  θ₀_mem   := θ₀_mem
  G_set    := BoundedNuisanceDirs S.toBackdoorEstimationSystem.η₀
  g₀       := S.toBackdoorEstimationSystem.η₀
  g₀_mem   := anchor_mem_boundedNuisanceDirs _
  ℓ        := fun z θ η => (phi_eta z η - eval θ z.1)^2
  ℓ_meas   := by
    intro θ η
    have h1 : Measurable (fun z : γ × Bool × ℝ => phi_eta z η) :=
      measurable_phi_eta η
    have h2 : Measurable (fun z : γ × Bool × ℝ => eval θ z.1) :=
      (eval_meas θ).comp measurable_fst
    exact (h1.sub h2).pow_const 2
  θ₀_minimizes := θ₀_minimizes

/-! ## Headline orthogonality lemma -/

/-- **DR-Learner loss orthogonality** (`prop:est-osl-dr-loss-orthogonal`).

Under the back-door causal assumptions and strict overlap, the DR-Learner
squared loss is Neyman-orthogonal at the truth `(τ₀, η₀)`.

Mathematically, the proof follows the conditional Riesz cancellation
argument from the natural-language note:

* `D_θ L_DR(τ₀, η)[ν_θ] = -2 𝔼[(φ_η(Z) − τ₀(X)) · ν_θ(X)]`.
* Differentiate this in the nuisance directions `ν_η = (ν_μ, ν_e)`.
* The outcome-regression directions vanish via the conditional Riesz
  identity (proved in `Estimation/CATE/ConditionalBias.lean` as
  `cond_exp_residual_at_h` / `phi_eta_minus_phi₀_cond_exp`).
* The propensity direction vanishes via the conditional residual identity
  `cond_exp_residual_zero` from `Estimation/ATE/MeanZero.lean`.

In the abstract `LearningSystem` framework these analytic steps reduce to two
inputs that any concrete instantiation must supply:

* `hBridge : MixedScoreDCTBridge ... M` — the DCT swap that interchanges
  the limit defining the mixed directional derivative with the population
  integral.  In the DR setting this follows from strict overlap and the
  bounded-by-`ε⁻¹` envelopes already used in
  `phi_eta_minus_phi₀_cond_exp`.
* `hScoreFlat` — the *score-form* orthogonality: the integrated target
  directional derivative `g ↦ ∫ z, (M.Dθ_at g).dℓ_θ θ z ∂P_Z` has zero
  derivative at `g₀` for every admissible target direction `ν_θ`.  In the
  DR setting this is the closed-form statement that the conditional bias
  identity `phi_eta_minus_phi₀_cond_exp` produces a remainder bilinear in
  `(η.μ - η₀.μ, η.e - η₀.e)`, hence quadratic along any nuisance ray
  `η₀ + t • (η - η₀)`.

Given those two abstract inputs, orthogonality is a routine consequence of
`neymanOrthog_iff_score_deriv_zero`. The back-door and overlap assumptions are
carried for the DR-Learner interface but are ignored by this abstract adapter;
the theorem assumes the `hBridge` and `hScoreFlat` obligations directly. The
concrete analytic DR orthogonality result is `drNeymanOrthog`. -/
theorem drNeymanOrthog_witness
    {P : POSystem} {γ : Type*} [MeasurableSpace γ]
    [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
    (S : CATEEstimationSystem P γ)
    (_hA : S.toPOBackdoorSystem.Assumptions)
    (_hOverlap : ∃ ε > 0, S.toBackdoorEstimationSystem.StrictOverlap ε)
    (Θ : Type*) [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ]
    (Θ_set : Set Θ) (Θ_convex : Convex ℝ Θ_set)
    (θ₀ : Θ) (θ₀_mem : θ₀ ∈ Θ_set)
    (eval : Θ → γ → ℝ) (eval_meas : ∀ θ, Measurable (eval θ))
    (eval_θ₀ : ∀ x, eval θ₀ x = S.τ_val x)
    (θ₀_minimizes : DRThetaMinimizes S Θ_set θ₀ eval)
    (M : HasMixedDirDeriv
          (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes))
    (hBridge : MixedScoreDCTBridge
        (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes) M)
    (hScoreFlat :
      ∀ θ ∈ Θ_set,
        ∀ η ∈ BoundedNuisanceDirs S.toBackdoorEstimationSystem.η₀,
          Tendsto (fun t : ℝ =>
            ((∫ z, (M.Dθ_at
                (S.toBackdoorEstimationSystem.η₀ + t • (η -
                    S.toBackdoorEstimationSystem.η₀))).dℓ_θ θ z
                ∂S.toBackdoorEstimationSystem.P_Z)
              - (∫ z, (M.Dθ_at S.toBackdoorEstimationSystem.η₀).dℓ_θ θ z
                  ∂S.toBackdoorEstimationSystem.P_Z)) / t)
            (𝓝[≠] 0) (𝓝 0)) :
    NeymanOrthogLoss
      (drLearningSystem S Θ Θ_set Θ_convex θ₀ θ₀_mem eval eval_meas eval_θ₀ θ₀_minimizes) M :=
  (neymanOrthog_iff_score_deriv_zero _ M hBridge).mpr hScoreFlat

end OrthogonalLearning
end Estimation
end Causalean
