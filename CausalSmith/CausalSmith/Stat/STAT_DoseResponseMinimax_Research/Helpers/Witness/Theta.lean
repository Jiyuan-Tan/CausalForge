/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Dose-response minimax lower bound: witness target values
-/

import CausalSmith.Stat.STAT_DoseResponseMinimax_Research.Helpers.Witness.Measure

namespace CausalSmith.Stat.DoseResponseMinimax

open MeasureTheory
open scoped ENNReal Topology

-- @node: dose-witness-theta
/-- For a normalized covariate density, the witness target value at the center
treatment equals the signed bump amplitude. -/
lemma doseWitness_theta {d : ℕ} (p0 : (Fin d → ℝ) → ℝ) (q0 : ℝ → ℝ)
    (B alpha t0 lambda h zeta : ℝ)
    (hp0_int : (∫ x in cube d, p0 x) = 1) :
    thetaFunctional (doseWitness (d := d) p0 q0 B alpha t0 lambda h zeta) t0 =
      zeta * lambda * h ^ alpha := by
  rw [thetaFunctional]
  change (∫ x in cube d,
      (zeta * lambda * h ^ alpha * doseBump ((t0 - t0) / h)) * p0 x) =
    zeta * lambda * h ^ alpha
  simp only [sub_self, zero_div, doseBump_zero, mul_one]
  rw [integral_const_mul, hp0_int, mul_one]

-- @node: dose-witness-theta-sep
/-- For a normalized covariate density, the separation between the positive and
negative witness target values is twice the bump amplitude without the sign. -/
lemma doseWitness_theta_sep {d : ℕ} (p0 : (Fin d → ℝ) → ℝ) (q0 : ℝ → ℝ)
    (B alpha t0 lambda h : ℝ)
    (hp0_int : (∫ x in cube d, p0 x) = 1) :
    thetaFunctional (doseWitness (d := d) p0 q0 B alpha t0 lambda h 1) t0 -
      thetaFunctional (doseWitness (d := d) p0 q0 B alpha t0 lambda h (-1)) t0 =
      2 * lambda * h ^ alpha := by
  rw [doseWitness_theta (d := d) p0 q0 B alpha t0 lambda h 1 hp0_int,
    doseWitness_theta (d := d) p0 q0 B alpha t0 lambda h (-1) hp0_int]
  ring

end CausalSmith.Stat.DoseResponseMinimax
