/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Local score-program definitions and closed-form arm solution

This file carries the arm score cost `J_{a,nu}`, the aggregate local information
objects built from it, and the closed-form score-program solution.
-/

import CausalSmith.Stat.STAT_NeymanRegretMinimax_Research.Helpers.ArmScoreSubstrate

namespace CausalSmith.Stat.NeymanRegretMinimax

open MeasureTheory
open scoped BigOperators Topology

-- @node: def:arm-score-costs
/-- Arm-wise information cost `J_{a,nu}(x) = inf { ∫ s² dnu_a : ∫ s dnu_a = 0,
∫ y s dnu_a = 0, ∫ y² s dnu_a = x }`: the least `L²(nu_a)` cost of a
moment-preserving score realizing the second-moment perturbation `x`.
@realizes J_{0,nu}(u_0), J_{1,nu}(u_1)(constrained L² score cost)
@realizes s_0, s_1(feasible scores s in the ∃) -/
noncomputable def armScoreCost (nu : Measure (ℝ × ℝ)) (a : Fin 2) (x : ℝ) : ℝ :=
  Causalean.Stat.MomentProblems.ScoreProgram.scoreCost (armMarginal nu a) x

-- @node: def:local-information
/-- Oracle-weighted local information cost
`J_nu(u) = π_nu* · J_{1,nu}(u₁) + (1 − π_nu*) · J_{0,nu}(u₀)`.
@realizes J_nu(u)(oracle-weighted arm score costs) -/
noncomputable def localInformation (nu : Measure (ℝ × ℝ)) (u : ℝ × ℝ) : ℝ :=
  oracleAllocation nu * armScoreCost nu 1 u.2
    + (1 - oracleAllocation nu) * armScoreCost nu 0 u.1

-- @node: def:feasible-direction-set
/-- Feasible-direction set `U_nu = {u : ℝ² : 0 < J_nu(u) < ∞ and π̇_nu(u) ≠ 0}`.
(In this `ℝ`-valued encoding `J_nu(u) < ∞` is automatic, so only the positivity
and the nonvanishing sensitivity are recorded.)
@realizes U_nu(feasible second-moment directions) -/
def feasibleDirectionSet (nu : Measure (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  {u | 0 < localInformation nu u ∧ oracleSensitivity nu u ≠ 0}

-- @node: def:local-complexity
/-- Local minimax complexity
`κ_nu = sup_{u ∈ U_nu} S_nu² · π̇_nu(u)² / J_nu(u)`, with `S_nu = m₀ + m₁`.
@realizes kappa_nu(S²-scaled Rayleigh sup over U_nu) -/
noncomputable def localComplexity (nu : Measure (ℝ × ℝ)) : ℝ :=
  sSup {v | ∃ u ∈ feasibleDirectionSet nu,
    v = (rootSecondMoment nu 0 + rootSecondMoment nu 1) ^ 2
      * oracleSensitivity nu u ^ 2 / localInformation nu u}

-- @node: def:testing-scale
/-- Local testing scale `h_T(nu,u) = (log T / (T · J_nu(u)))^{1/2}`.  (SYNC-BACK:
relocated from `Basic` to `Helpers/ScoreProgram` since it depends on
`localInformation`.)
@realizes h_T(nu,u)((log T/(T J_nu(u)))^{1/2}) -/
noncomputable def testingScale (nu : Measure (ℝ × ℝ)) (u : ℝ × ℝ) (T : ℕ) : ℝ :=
  Real.sqrt (Real.log (T : ℝ) / ((T : ℝ) * localInformation nu u))

-- @node: lem:arm-score-program-solution
/-- The arm score program solves in closed form, with the full note content: there
is an `L²(nu_a)` residual `e_a` of `y²` on `span{1,y}` — orthogonal to `1` and `y`
(`∫ e_a = 0`, `∫ y e_a = 0`) — whose residual identity `∫ y² e_a = ∫ e_a² =
r_{a,nu}` pins the tangent strength, with `r_{a,nu} > 0` and `e_a` bounded on
`[0,1]`.  For every `x` the cost is `J_{a,nu}(x) = x²/r_{a,nu}`, realized by the
EXPLICIT minimizing score `s_a^x = x·e_a/r_{a,nu}` (feasible for the three moment
constraints, with cost exactly `x²/r_{a,nu}`), itself bounded on `[0,1]`.
(Residual identity, explicit minimizers, and boundedness are STATED by the note,
not just the closed-form cost equality — added to the signature per the redirect.) -/
lemma arm_score_program_solution (nu : Measure (ℝ × ℝ)) (h : MTan nu) (a : Fin 2) :
    ∃ e : ℝ → ℝ,
      (∫ y, e y ∂(armMarginal nu a) = 0)
      ∧ (∫ y, y * e y ∂(armMarginal nu a) = 0)
      ∧ (∫ y, y ^ 2 * e y ∂(armMarginal nu a) = armTangentStrength nu a)
      ∧ armTangentStrength nu a = ∫ y, e y ^ 2 ∂(armMarginal nu a)
      ∧ 0 < armTangentStrength nu a
      ∧ (∃ C : ℝ, ∀ y ∈ Set.Icc (0 : ℝ) 1, |e y| ≤ C)
      ∧ ∀ x : ℝ,
          armScoreCost nu a x = x ^ 2 / armTangentStrength nu a
          ∧ (∫ y, x * e y / armTangentStrength nu a ∂(armMarginal nu a) = 0)
          ∧ (∫ y, y * (x * e y / armTangentStrength nu a) ∂(armMarginal nu a) = 0)
          ∧ (∫ y, y ^ 2 * (x * e y / armTangentStrength nu a) ∂(armMarginal nu a) = x)
          ∧ (∫ y, (x * e y / armTangentStrength nu a) ^ 2 ∂(armMarginal nu a)
              = x ^ 2 / armTangentStrength nu a)
          ∧ (∃ C : ℝ, ∀ y ∈ Set.Icc (0 : ℝ) 1,
              |x * e y / armTangentStrength nu a| ≤ C) := by
  let μ := armMarginal nu a
  let e := Causalean.Stat.MomentProblems.ResidualQuadratic.ProjectionResidual.projResidual μ
  haveI : IsProbabilityMeasure μ := armMarginal_isProbabilityMeasure nu h.toMInt a
  have hfin : Causalean.Stat.MomentProblems.ResidualQuadratic.MeasureBridge.FiniteMoment4 μ :=
    armMarginal_finiteMoment4 nu h.toMInt a
  have hnd :
      Causalean.Stat.MomentProblems.ResidualQuadratic.MeasureBridge.moment μ 1 ^ 2
        < Causalean.Stat.MomentProblems.ResidualQuadratic.MeasureBridge.moment μ 2 := by
    simpa [μ] using arm_variance_pos_of_tangent nu h a
  have hr_eq :
      armTangentStrength nu a
        = Causalean.Stat.MomentProblems.ResidualQuadratic.MeasureBridge.l2ResidualQuadratic μ := by
    simpa [μ] using armTangentStrength_eq_l2ResidualQuadratic nu h a
  have hr_l2 : 0 < Causalean.Stat.MomentProblems.ResidualQuadratic.MeasureBridge.l2ResidualQuadratic μ := by
    simpa [hr_eq] using h.tangent a
  refine ⟨e, ?_, ?_, ?_, ?_, h.tangent a, ?_, ?_⟩
  · simpa [e] using
      Causalean.Stat.MomentProblems.ResidualQuadratic.ProjectionResidual.integral_projResidual μ hfin hnd
  · simpa [e] using
      Causalean.Stat.MomentProblems.ResidualQuadratic.ProjectionResidual.integral_id_mul_projResidual μ hfin hnd
  · simpa [e, μ, hr_eq] using
      Causalean.Stat.MomentProblems.ResidualQuadratic.ProjectionResidual.integral_sq_mul_projResidual
        μ hfin hnd
  · simpa [e, μ, hr_eq] using
      (Causalean.Stat.MomentProblems.ResidualQuadratic.ProjectionResidual.integral_sq_projResidual
        μ hfin hnd).symm
  · simpa [e] using projResidual_bounded_Icc μ
  · intro x
    have hscore :=
      Causalean.Stat.MomentProblems.ScoreProgram.scoreCost_eq μ hfin hnd hr_l2 x
    have hfeas :=
      Causalean.Stat.MomentProblems.ScoreProgram.optScore_feasible
        μ hfin hnd hr_l2 x
    have hcost :=
      Causalean.Stat.MomentProblems.ScoreProgram.optScore_cost μ hfin hnd hr_l2 x
    have hfun :
        (fun y : ℝ => x * e y / armTangentStrength nu a)
          = Causalean.Stat.MomentProblems.ScoreProgram.optScore μ x := by
      funext y
      simp [e, Causalean.Stat.MomentProblems.ScoreProgram.optScore, hr_eq]
      ring
    constructor
    · simpa [armScoreCost, μ, hr_eq] using hscore
    constructor
    · rw [hfun]
      exact hfeas.mean_zero
    constructor
    · change ∫ y, y * ((fun y : ℝ => x * e y / armTangentStrength nu a) y) ∂μ = 0
      rw [hfun]
      exact hfeas.cov_id_zero
    constructor
    · change ∫ y, y ^ 2 * ((fun y : ℝ => x * e y / armTangentStrength nu a) y) ∂μ = x
      rw [hfun]
      exact hfeas.cov_sq
    constructor
    · change ∫ y, ((fun y : ℝ => x * e y / armTangentStrength nu a) y) ^ 2 ∂μ
          = x ^ 2 / armTangentStrength nu a
      rw [hfun]
      simpa [μ, hr_eq] using hcost
    · rcases projResidual_bounded_Icc μ with ⟨C, hC⟩
      refine ⟨|x| * C / armTangentStrength nu a, ?_⟩
      intro y hy
      have heC : |e y| ≤ C := by simpa [e] using hC y hy
      have hmul : |x| * |e y| ≤ |x| * C :=
        mul_le_mul_of_nonneg_left heC (abs_nonneg x)
      have hdiv := div_le_div_of_nonneg_right hmul (le_of_lt (h.tangent a))
      calc
        |x * e y / armTangentStrength nu a|
            = |x| * |e y| / armTangentStrength nu a := by
              rw [abs_div, abs_mul, abs_of_pos (h.tangent a)]
        _ ≤ |x| * C / armTangentStrength nu a := hdiv

end CausalSmith.Stat.NeymanRegretMinimax
