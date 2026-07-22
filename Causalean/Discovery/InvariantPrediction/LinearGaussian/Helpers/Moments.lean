/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Discovery.InvariantPrediction.LinearGaussian.Model

/-!
# Invariant Causal Prediction — Gaussian-noise moments

The structural noises `εⱼ` of the observational SEM are centered Gaussian
(`hGauss`), hence integrable with mean `0`.  These two facts feed the mean-shift
integral computation in the completeness proof.

* `eps_integrable` — each `εⱼ` is `M.P`-integrable.
* `eps_integral_zero` — `E[εⱼ] = 0`.
-/

namespace Causalean.Discovery.InvariantPrediction.LinearGaussian

open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {p : ℕ}

/-- `εⱼ` is a.e.-measurable: by the structural-residual identity `hε` it agrees
a.e. with the measurable map `Xⱼ − Σ_{k≠j} βⱼₖ Xₖ`. -/
theorem eps_aemeasurable (M : ObsSEM p) (j : Fin (p + 1)) :
    AEMeasurable (fun ω => M.ε ω j) M.P := by
  have hmeasRHS : Measurable
      (fun ω => M.X ω j - ∑ k ∈ Finset.univ.erase j, M.β j k * M.X ω k) :=
    (M.hXmeas j).sub (Finset.measurable_sum _ (fun k _ => (M.hXmeas k).const_mul _))
  refine hmeasRHS.aemeasurable.congr ?_
  filter_upwards [M.hε] with ω hω using (hω j).symm

/-- The noise `εⱼ` is `M.P`-integrable (Gaussian marginal has a first moment). -/
theorem eps_integrable (M : ObsSEM p) (j : Fin (p + 1)) :
    Integrable (fun ω => M.ε ω j) M.P := by
  have hmeas : AEMeasurable (fun ω => M.ε ω j) M.P := eps_aemeasurable M j
  -- The identity map is integrable against the Gaussian law (`MemLp id 1`),
  -- and integrability transfers back through `integrable_map_measure`.
  have hid : Integrable (id : ℝ → ℝ) (M.P.map (fun ω => M.ε ω j)) := by
    rw [M.hGauss j]
    exact (memLp_id_gaussianReal 1).integrable (by norm_num)
  rw [M.hGauss j] at hid
  -- transfer
  have := (integrable_map_measure (μ := M.P)
    (f := fun ω => M.ε ω j) (g := (id : ℝ → ℝ)) ?_ hmeas).mp (by rwa [M.hGauss j])
  · simpa using this
  · rw [M.hGauss j]; exact (memLp_id_gaussianReal 1).aestronglyMeasurable

/-- The noise `εⱼ` is centered: `E[εⱼ] = 0`. -/
theorem eps_integral_zero (M : ObsSEM p) (j : Fin (p + 1)) :
    ∫ ω, M.ε ω j ∂M.P = 0 := by
  have hmeas : AEMeasurable (fun ω => M.ε ω j) M.P := eps_aemeasurable M j
  have hg : AEStronglyMeasurable (fun x : ℝ => x) (M.P.map (fun ω => M.ε ω j)) := by
    rw [M.hGauss j]; exact (memLp_id_gaussianReal 1).aestronglyMeasurable
  rw [← integral_map hmeas hg, M.hGauss j, integral_id_gaussianReal]

end Causalean.Discovery.InvariantPrediction.LinearGaussian
