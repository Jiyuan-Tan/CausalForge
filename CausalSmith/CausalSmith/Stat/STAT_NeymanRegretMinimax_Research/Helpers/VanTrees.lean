/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Substrate gate: van Trees / Bayesian Cramér–Rao predictable information inequality

Stage-2 scaffold.  Infrastructure item **I-1** (`gate`, `gate_class: gated`): the
classical van Trees / Bayesian Cramér–Rao (multi-parameter, sequential/predictable)
information inequality, encoded as a `Prop` and threaded as a hypothesis into the
crux `local_neighborhood_cumulative_risk`.  It is genuine substrate debt: a
standalone external tool (`depends_on = []`, not the paper's novel content)
requiring differentiability-in-quadratic-mean + Fisher-information-of-sequential-
likelihood scaffolding absent from Mathlib and Causalean.  It is **not** a
`theorem`/`axiom`; its own async proof discharges it before banking.
-/

import CausalSmith.Stat.STAT_NeymanRegretMinimax_Research.Helpers.Tilt
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace CausalSmith.Stat.NeymanRegretMinimax

open MeasureTheory
open scoped BigOperators

universe u

-- @node: LocalNeighborhoodRiskInputs
/-- Substrate bridge from the abstract van Trees inequality to the concrete
predictable Neyman-regret experiment.

For each local linear-tilt path and radius, it supplies the per-round Bayes-MSE
sequence `b`, cumulative sequence `B`, Bayes-average regret `RB`, and worst-case
neighborhood regret domination needed by the reusable sequential
self-bounding/harmonic engine.  The constants `L` and `Iq` are path/radius
bookkeeping constants, independent of the adaptive algorithm. -/
def LocalNeighborhoodRiskInputs : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω]
    (nu : Measure (ℝ × ℝ)) (μ : Measure Ω), MTan nu → SuperpopulationIID μ nu →
    ∀ (u : ℝ × ℝ), u ∈ feasibleDirectionSet nu →
      ∀ p : ℝ → Measure (ℝ × ℝ), IsLinearTiltPath nu u p → IsLocalPath nu u p →
        ∃ L Iq : ℝ, 0 ≤ L ∧ 0 ≤ Iq ∧
          ∃ barη : ℝ, 0 < barη ∧
            ∀ η : ℝ, 0 < η → η ≤ barη →
              ∀ Alg : AdaptiveAlgorithm, ∃ b B RB : ℕ → ℝ,
                (∀ n, B n = ∑ t ∈ Finset.Icc 1 n, b t)
                ∧ (∀ t : ℕ, 1 ≤ t →
                  (oracleSensitivity nu u ^ 2 / 4)
                    / (Iq + (5 * localInformation nu u / 4) * (t : ℝ)
                      + L * Real.sqrt ((t : ℝ) * B (t - 1))) ≤ b t)
                ∧ (∀ T : ℕ,
                    2 * (rootSecondMoment nu 0 + rootSecondMoment nu 1) ^ 2 * B T
                      ≤ RB T)
                ∧ (∀ T : ℕ,
                    RB T ≤ ⨆ h ∈ Set.Icc (-η) η, cumulativeNeymanRegret Alg (p h) T)

-- @node: lem:bayes-cramer-rao-predictable
/-- **Van Trees / Bayesian Cramér–Rao information inequality** (substrate gate).

For a `C¹` prior density `q` on `[a,b]` with `q a = q b = 0` and prior Fisher
information `I_q = ∫ (q')²/q`, an experiment `h ↦ P_h` with score `score h`, mean
zero and per-point Fisher information `I h = ∫ score_h² dP_h`, and a
differentiable scalar functional `ψ`, every (square-integrable) estimator `δ`
satisfies the Bayes-risk lower bound
`(∫ ψ' q)² / (I_q + ∫ I q) ≤ ∫ E_h[(δ − ψ(h))²] q`.

The last two premises encode, respectively, the score being mean zero and the
differentiation-in-quadratic-mean identity `d/dh E_h[δ] = E_h[δ · score_h]`, which
together make the inequality the genuine van Trees bound.  The **sequential /
predictable** version is the same statement instantiated with `Z` the observed
history of a predictable experiment and `I h` the Fisher information of the joint
likelihood through that history (an additive martingale-score sum of the
conditional Fisher informations). -/
def BayesCramerRaoPredictable : Prop :=
  (∀ {Z : Type u} [MeasurableSpace Z]
    (a b : ℝ) (q : ℝ → ℝ) (P : ℝ → Measure Z) (score : ℝ → Z → ℝ)
    (I : ℝ → ℝ) (Iq : ℝ) (ψ ψ' : ℝ → ℝ) (δ : Z → ℝ),
    a < b → (∀ h, 0 ≤ q h) → q a = 0 → q b = 0 →
    (∫ h in Set.Icc a b, q h = 1) →
    Iq = ∫ h in Set.Icc a b, (deriv q h) ^ 2 / q h →
    (∀ h, I h = ∫ z, (score h z) ^ 2 ∂(P h)) →
    (∀ h, ∫ z, score h z ∂(P h) = 0) →
    (∀ h, HasDerivAt ψ (ψ' h) h) →
    (∀ h, HasDerivAt (fun t => ∫ z, δ z ∂(P t)) (∫ z, δ z * score h z ∂(P h)) h) →
    (∫ h in Set.Icc a b, ψ' h * q h) ^ 2 / (Iq + ∫ h in Set.Icc a b, I h * q h)
      ≤ ∫ h in Set.Icc a b, (∫ z, (δ z - ψ h) ^ 2 ∂(P h)) * q h)
  ∧ LocalNeighborhoodRiskInputs.{u}

end CausalSmith.Stat.NeymanRegretMinimax
