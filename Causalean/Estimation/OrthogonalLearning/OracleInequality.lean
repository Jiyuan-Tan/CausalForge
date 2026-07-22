/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Conservative oracle inequality for orthogonal sample-split plug-in ERM

`oracle_inequality_plugin_ERM` is the deterministic plug-in ERM oracle
inequality obtained from the AM–GM proof sketch for
`thm:est-osl-plugin-erm-oracle`. It tracks the conservative optimization-error
constant delivered by that proof. Hypotheses:

1. `LearningSystem` with convex `Θ_set` (carried by the system itself).
2. `σ`-strong convexity of `L(·, ĝ_n ω)` around `θ₀` w.r.t. `‖·‖`.
3. First-order inequality at the truth `(θ₀, g₀)`.
4. Sample-split plug-in ERM with optimisation slack `r_opt`.
5. Local empirical-process modulus `ρ` realised at the sample point `(n, ω)`
   for the realised nuisance `ĝ n ω`.

Conclusion:
`‖θhat n ω - θ₀‖² ≤ 4(1+σ)/σ² · (ρ n)² + (4/σ) · Bias_n + (4/σ) · r_opt n`.

(The note's `def:est-osl-plugin-erm-oracle` displays `(2/σ)·r_opt` but the
AM–GM proof sketched there only yields `(4/σ)·r_opt` because empirical
optimality of `θhat` against `θ₀` already injects the full `r_opt` into the
population excess-risk inequality.  We track the proof's own constant.)

The deterministic theorem takes the modulus inequality as a direct hypothesis
`hRho_holds` evaluated at the specific sample point `(n, ω)`, rather than
threading the `LocalEmpProcessModulus` event predicate. This keeps the signature
readable; `LocalEmpProcessModulus` is invoked by users by extracting an `ω` in
the modulus event before applying this theorem.

See `doc/basic_concepts/po/estimation/orthogonal_statistical_learning.tex`,
`thm:est-osl-plugin-erm-oracle`.
-/

import Causalean.Estimation.OrthogonalLearning.PluginERM
import Causalean.Estimation.OrthogonalLearning.Population.DirectionalDeriv
import Causalean.Estimation.OrthogonalLearning.Population.NeymanOrthogonal
import Causalean.Estimation.OrthogonalLearning.LocalEmpProcess.Local
import Causalean.Estimation.OrthogonalLearning.Population.SecondOrderBias

/-! # Orthogonal Statistical Learning Oracle Inequality

This file proves deterministic and high-probability conservative oracle
inequalities for sample-split plug-in empirical risk minimization with an
orthogonal loss. The bounds convert strong convexity, empirical optimality, a
local empirical-process modulus, and second-order bias into squared
target-space error control with the displayed `4/σ` optimization-slack
constant.

The deterministic theorem `oracle_inequality_plugin_ERM` consumes a realized
modulus inequality at one sample point. The high-probability theorem
`oracle_inequality_plugin_ERM_highProb` packages the same bound on the event
provided by `LocalEmpProcessModulus` for a fixed plug-in nuisance. -/

namespace Causalean
namespace Estimation
namespace OrthogonalLearning

open MeasureTheory ProbabilityTheory Filter Topology Causalean.Stat

variable {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
         {Z : Type*} [MeasurableSpace Z] {P_Z : MeasureTheory.Measure Z}
         {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ]
         {G : Type*} [AddCommGroup G] [Module ℝ G]

/-- **Conservative oracle inequality for the orthogonal sample-split plug-in ERM.**

Under strong convexity of the population risk in `θ` at the realised
nuisance, a first-order inequality at the truth, plug-in ERM optimality,
and a local empirical-process modulus realised at the sample point
`(n, ω)`, the squared estimation error of the plug-in target estimator is
controlled by

  `4(1+σ)/σ² · (ρ n)²  +  (4/σ) · Bias_n  +  (4/σ) · r_opt n`.

The proof is the AM–GM absorption sketched in the note's proof of
`thm:est-osl-plugin-erm-oracle`, with the conservative `4/σ` coefficient on
the optimization slack. -/
-- TODO(faithfulness): `thm:est-osl-plugin-erm-oracle` displays a `2/σ`
-- optimization-slack coefficient; deriving it from the current approximate-ERM
-- hypothesis needs an additional sharp basic inequality/slack convention.
theorem oracle_inequality_plugin_ERM
    (S : LearningSystem Ω μ Z P_Z Θ G)
    (S_iid : IIDSample Ω Z μ P_Z)
    (split : OneShotSplit S_iid)
    (Dθ_truth : HasDirDerivTheta S S.g₀)
    (ghat : ℕ → Ω → G)
    (Dθ_hat : ∀ n ω, HasDirDerivTheta S (ghat n ω))
    (θhat : ℕ → Ω → Θ)
    (r_opt : ℕ → ℝ)
    (hPluginERM : SampleSplitPluginERM S S_iid split θhat ghat r_opt)
    (σ : ℝ) (hσ : 0 < σ)
    -- σ-strong convexity of L(·, ghat n ω) around θ₀ w.r.t. ‖·‖.
    (hSC : ∀ n ω, ∀ θ ∈ S.Θ_set,
      S.L θ (ghat n ω) - S.L S.θ₀ (ghat n ω)
        ≥ (∫ z, (Dθ_hat n ω).dℓ_θ θ z ∂P_Z) + (σ / 2) * ‖θ - S.θ₀‖ ^ 2)
    -- First-order inequality at the truth (θ₀, g₀).
    (hFOI : FirstOrderInequality S Dθ_truth)
    (ρ : ℕ → ℝ)
    (n : ℕ) (ω : Ω)
    -- Modulus inequality realised at the sample point (n, ω) and the
    -- realised nuisance ghat n ω.  Equivalent (after instantiating the
    -- LocalEmpProcessModulus event) to the centred-process bound at the
    -- specific θhat n ω.
    (hRho_holds :
      (S.L (θhat n ω) (ghat n ω) - S.L S.θ₀ (ghat n ω))
        - (empRiskFoldB S S_iid split n ω (θhat n ω) (ghat n ω)
            - empRiskFoldB S S_iid split n ω S.θ₀ (ghat n ω))
        ≤ ρ n * ‖θhat n ω - S.θ₀‖ + (ρ n) ^ 2) :
    ‖θhat n ω - S.θ₀‖ ^ 2
      ≤ (4 * (1 + σ) / σ ^ 2) * (ρ n) ^ 2
        + (4 / σ) * Bias_n S Dθ_truth (Dθ_hat n ω) (θhat n ω)
        + (4 / σ) * r_opt n := by
  set e : ℝ := ‖θhat n ω - S.θ₀‖
  set rho : ℝ := ρ n
  set ropt : ℝ := r_opt n
  set B : ℝ := Bias_n S Dθ_truth (Dθ_hat n ω) (θhat n ω)
  set Dtruth : ℝ := ∫ z, Dθ_truth.dℓ_θ (θhat n ω) z ∂P_Z
  set Dhat : ℝ := ∫ z, (Dθ_hat n ω).dℓ_θ (θhat n ω) z ∂P_Z
  set Ldiff : ℝ :=
    S.L (θhat n ω) (ghat n ω) - S.L S.θ₀ (ghat n ω)
  set Empdiff : ℝ :=
    empRiskFoldB S S_iid split n ω (θhat n ω) (ghat n ω)
      - empRiskFoldB S S_iid split n ω S.θ₀ (ghat n ω)
  have hθ_mem : θhat n ω ∈ S.Θ_set := hPluginERM.mem_Θ_set n ω
  have hθ₀_mem : S.θ₀ ∈ S.Θ_set := S.θ₀_mem
  have hSC' : Ldiff ≥ Dhat + (σ / 2) * e ^ 2 := by
    simpa [Ldiff, Dhat, e] using hSC n ω (θhat n ω) hθ_mem
  have hStrong : (σ / 2) * e ^ 2 ≤ Ldiff - Dhat := by
    linarith
  have hFOI' : 0 ≤ Dtruth := by
    simpa [Dtruth] using hFOI (θhat n ω) hθ_mem
  have hEmp : Empdiff ≤ ropt := by
    have happrox := hPluginERM.approx_min n ω S.θ₀ hθ₀_mem
    simpa [Empdiff, ropt, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      sub_le_iff_le_add.mpr happrox
  have hMod : Ldiff - Empdiff ≤ rho * e + rho ^ 2 := by
    simpa [Ldiff, Empdiff, rho, e] using hRho_holds
  have hPop : Ldiff ≤ ropt + rho * e + rho ^ 2 := by
    linarith
  have hB : B = Dtruth - Dhat := by
    simp [B, Bias_n, Dtruth, Dhat]
  have hBasic : (σ / 2) * e ^ 2 ≤ ropt + rho * e + rho ^ 2 + B := by
    linarith
  have hYoung : rho * e ≤ (σ / 4) * e ^ 2 + (1 / σ) * rho ^ 2 := by
    have hσne : σ ≠ 0 := ne_of_gt hσ
    have hsquare : 0 ≤ (σ / 4) * (e - (2 / σ) * rho) ^ 2 := by
      exact mul_nonneg (by positivity) (sq_nonneg _)
    have hident :
        (σ / 4) * (e - (2 / σ) * rho) ^ 2
          = (σ / 4) * e ^ 2 + (1 / σ) * rho ^ 2 - rho * e := by
      field_simp [hσne]
      ring
    linarith
  have hAbsorb :
      (σ / 4) * e ^ 2 ≤ ropt + (1 / σ) * rho ^ 2 + rho ^ 2 + B := by
    linarith
  calc
    e ^ 2 = (4 / σ) * ((σ / 4) * e ^ 2) := by
      field_simp [ne_of_gt hσ]
    _ ≤ (4 / σ) * (ropt + (1 / σ) * rho ^ 2 + rho ^ 2 + B) := by
      exact mul_le_mul_of_nonneg_left hAbsorb (by positivity)
    _ = (4 * (1 + σ) / σ ^ 2) * rho ^ 2 + (4 / σ) * B + (4 / σ) * ropt := by
      field_simp [ne_of_gt hσ]
      ring

/-- **High-probability conservative oracle inequality for the orthogonal
sample-split plug-in ERM.**

This consumes a `LocalEmpProcessModulus` hypothesis at a fixed nuisance value
`g`, and concludes — with probability at least `1 − δ` over the ambient
sample — the same conservative squared estimation-error oracle bound.

This is the version downstream callers actually want once `LocalEmpProcessModulus`
has been discharged from concentration assumptions (e.g. by the global
Rademacher bridge in `LocalEmpProcess.Rademacher`).

Because the current bridge delivers `LocalEmpProcessModulus` at a single fixed
`g`, this theorem also pins the plug-in nuisance to a fixed `g`
(`ghat ≡ g`) — the realistic fold-A randomisation of the nuisance is handled
by a future fold-A/fold-B independence layer; threading it here would only
add quantifiers, not new mathematics, so we record it as a TODO. -/
theorem oracle_inequality_plugin_ERM_highProb
    (S : LearningSystem Ω μ Z P_Z Θ G)
    (S_iid : IIDSample Ω Z μ P_Z)
    (split : OneShotSplit S_iid)
    (Dθ_truth : HasDirDerivTheta S S.g₀)
    (g : G) (Dθ_at_g : HasDirDerivTheta S g)
    (θhat : ℕ → Ω → Θ)
    (r_opt : ℕ → ℝ)
    (hPluginERM : SampleSplitPluginERM S S_iid split θhat (fun _ _ => g) r_opt)
    (σ : ℝ) (hσ : 0 < σ)
    -- σ-strong convexity of `L(·, g)` around `θ₀` w.r.t. `‖·‖`.
    (hSC : ∀ θ ∈ S.Θ_set,
      S.L θ g - S.L S.θ₀ g
        ≥ (∫ z, Dθ_at_g.dℓ_θ θ z ∂P_Z) + (σ / 2) * ‖θ - S.θ₀‖ ^ 2)
    (hFOI : FirstOrderInequality S Dθ_truth)
    (ρ : ℕ → ℝ) (δ : ℝ)
    (hMod : LocalEmpProcessModulus S S_iid split ρ δ g) :
    ∀ n : ℕ, ∃ E : Set Ω, MeasurableSet E ∧
      μ E ≥ 1 - ENNReal.ofReal δ ∧
      ∀ ω ∈ E,
        ‖θhat n ω - S.θ₀‖ ^ 2
          ≤ (4 * (1 + σ) / σ ^ 2) * (ρ n) ^ 2
            + (4 / σ) * Bias_n S Dθ_truth Dθ_at_g (θhat n ω)
            + (4 / σ) * r_opt n := by
  intro n
  rcases hMod n with ⟨E, hE_meas, hE_ge, hE_uniform⟩
  refine ⟨E, hE_meas, hE_ge, ?_⟩
  intro ω hω
  have hθ_mem : θhat n ω ∈ S.Θ_set := hPluginERM.mem_Θ_set n ω
  have hRho_holds :
      (S.L (θhat n ω) ((fun _ _ => g) n ω)
          - S.L S.θ₀ ((fun _ _ => g) n ω))
        - (empRiskFoldB S S_iid split n ω (θhat n ω) ((fun _ _ => g) n ω)
            - empRiskFoldB S S_iid split n ω S.θ₀ ((fun _ _ => g) n ω))
        ≤ ρ n * ‖θhat n ω - S.θ₀‖ + (ρ n) ^ 2 := by
    simpa using hE_uniform ω hω (θhat n ω) hθ_mem
  exact
    oracle_inequality_plugin_ERM
      S S_iid split Dθ_truth (fun _ _ => g) (fun _ _ => Dθ_at_g)
      θhat r_opt hPluginERM σ hσ
      (fun _ _ θ hθ => hSC θ hθ) hFOI ρ n ω hRho_holds

end OrthogonalLearning
end Estimation
end Causalean
