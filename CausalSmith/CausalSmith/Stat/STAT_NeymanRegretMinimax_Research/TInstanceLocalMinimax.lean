/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Instance-level local minimax converse — CONDITIONAL (not certified)

`thm:instance-local-minimax`: the kernel superpopulation Horvitz–Thompson converse
isolating the local curvature-information quotient that makes cumulative Neyman
regret unavoidable.

**BANKING STATUS: CONDITIONAL, NOT CERTIFIED.**  This theorem compiles sorry-free
and axiom-clean, but it takes the broad `LocalNeighborhoodRiskInputs` gate as an
explicit hypothesis (`hbridge`).  The F2.5 faithfulness reviewer correctly found
that this gate over-assumes content the source note DERIVES (the `b_t` recursion,
the `R_T^B ≥ 2S²·B_T` domination, and `sup ≥ R_T^B`).  It is therefore documented
as a conditional extension, NOT part of the certified bank.  The CERTIFIED core is
the gate-free machinery (`neyman_gap_identity`, `cumulative_risk_engine_uniform_threshold`,
`local_complexity_rayleigh`, `band_continuity_for_linear_tilts`).  See
`doc/research/SUBSTRATE_DEBT.md` and the writeup's Honest-scope section.
-/

import CausalSmith.Stat.STAT_NeymanRegretMinimax_Research.Helpers

namespace CausalSmith.Stat.NeymanRegretMinimax

open MeasureTheory
open scoped BigOperators Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

-- @node: thm:instance-local-minimax
/-- **Instance-level local minimax converse.**  For every `nu ∈ M_tan` and every
`ε > 0` there is a feasible direction `u_ε ∈ U_nu` with
`H_nu · π̇_nu(u_ε)² / J_nu(u_ε) ≥ κ_nu − ε`, its linear-tilt local path, and a
radius `η > 0`, such that every adaptive design `Alg` pays cumulative Neyman
regret at least `c₀ (κ_nu − ε) log T` somewhere in the `η`-neighborhood, for all
large `T` (`c₀ > 0` universal).

This is an honest CONDITIONAL theorem: it assumes `LocalNeighborhoodRiskInputs`,
the disclosed sequential van Trees / DQM Fisher-tensorization bridge from the
external substrate debt.  The i.i.d.-superpopulation sampling atom enters via
`SuperpopulationIID`. -/
-- @realizes epsilon(approximation margin ε ∈ (0,∞); binder `0 < ε`,
-- positive slack approximating the sup κ_nu = localComplexity nu)
-- @realizes nu_0, nu_1(arm marginals armMarginal nu a and armMarginal (p h) a are laws on
--   [0,1]: the base law's space is pinned by `MTan nu` (isLaw + bounded), and every
--   local-alternative `p h`'s space by `IsLocalPath nu uε p` (IsProbabilityMeasure (p h) +
--   BoundedOutcomes (p h)); the local alternatives are linear tilts, so no extremal
--   weight/support constraint is needed on this signature)
theorem instance_local_minimax
    (hbridge : LocalNeighborhoodRiskInputs.{u}) :
    ∃ c₀ : ℝ, 0 < c₀ ∧
      ∀ (nu : Measure (ℝ × ℝ)) (μ : Measure Ω), MTan nu → SuperpopulationIID μ nu →
        ∀ ε : ℝ, 0 < ε →
          ∃ uε : ℝ × ℝ, uε ∈ feasibleDirectionSet nu ∧
            localComplexity nu - ε
                ≤ lossCurvature nu * oracleSensitivity nu uε ^ 2 / localInformation nu uε ∧
            ∃ p : ℝ → Measure (ℝ × ℝ), IsLinearTiltPath nu uε p ∧ IsLocalPath nu uε p ∧
              ∃ η : ℝ, 0 < η ∧
                ∃ T₀ : ℕ, ∀ (Alg : AdaptiveAlgorithm) (T : ℕ), T₀ ≤ T →
                  c₀ * (localComplexity nu - ε) * Real.log (T : ℝ)
                    ≤ ⨆ h ∈ Set.Icc (-η) η, cumulativeNeymanRegret Alg (p h) T := by
  rcases local_neighborhood_cumulative_risk (Ω := Ω) hbridge with
    ⟨c₀, hc₀, hrisk_all⟩
  refine ⟨c₀, hc₀, ?_⟩
  intro nu μ hnu hiid ε hε
  let values : Set ℝ := {v | ∃ u ∈ feasibleDirectionSet nu,
    v = (rootSecondMoment nu 0 + rootSecondMoment nu 1) ^ 2
      * oracleSensitivity nu u ^ 2 / localInformation nu u}
  have hU : (feasibleDirectionSet nu).Nonempty :=
    (feasible_directions_nonempty nu hnu).1
  have hvalues_nonempty : values.Nonempty := by
    rcases hU with ⟨u0, hu0⟩
    exact ⟨_, ⟨u0, hu0, rfl⟩⟩
  have hklt : localComplexity nu - ε < localComplexity nu := sub_lt_self _ hε
  rw [localComplexity] at hklt
  change localComplexity nu - ε < sSup values at hklt
  rcases exists_lt_of_lt_csSup hvalues_nonempty hklt with ⟨_, hv, hvlt⟩
  rcases hv with ⟨uε, huε, rfl⟩
  have hquotS : localComplexity nu - ε ≤
      (rootSecondMoment nu 0 + rootSecondMoment nu 1) ^ 2
        * oracleSensitivity nu uε ^ 2 / localInformation nu uε :=
    le_of_lt hvlt
  have hJpos : 0 < localInformation nu uε := huε.1
  have hm0 : 0 < rootSecondMoment nu 0 := hnu.interiorMoments 0
  have hm1 : 0 < rootSecondMoment nu 1 := hnu.interiorMoments 1
  have hS_le_H :
      (rootSecondMoment nu 0 + rootSecondMoment nu 1) ^ 2 ≤ lossCurvature nu := by
    rw [lossCurvature]
    have hprod : 0 < rootSecondMoment nu 0 * rootSecondMoment nu 1 :=
      mul_pos hm0 hm1
    rw [le_div_iff₀ hprod]
    nlinarith [sq_nonneg (rootSecondMoment nu 0),
      sq_nonneg (rootSecondMoment nu 1), mul_nonneg hm0.le hm1.le]
  have hquotH : localComplexity nu - ε ≤
      lossCurvature nu * oracleSensitivity nu uε ^ 2 / localInformation nu uε := by
    refine hquotS.trans ?_
    have hmul :
        (rootSecondMoment nu 0 + rootSecondMoment nu 1) ^ 2
            * oracleSensitivity nu uε ^ 2
          ≤ lossCurvature nu * oracleSensitivity nu uε ^ 2 :=
      mul_le_mul_of_nonneg_right hS_le_H (sq_nonneg _)
    have hdiv := div_le_div_of_nonneg_right hmul (le_of_lt hJpos)
    simpa [mul_assoc] using hdiv
  rcases linear_tilt_path_valid nu hnu uε hJpos with ⟨p, hlin, hp⟩
  refine ⟨uε, huε, hquotH, p, hlin, hp, ?_⟩
  rcases hrisk_all nu μ hnu hiid uε huε p hlin hp with ⟨barη, hbarη, hriskη⟩
  refine ⟨barη, hbarη, ?_⟩
  rcases hriskη barη hbarη le_rfl with ⟨T₀, hT₀⟩
  refine ⟨max T₀ 1, ?_⟩
  intro Alg T hT
  have hT₀T : T₀ ≤ T := le_trans (Nat.le_max_left T₀ 1) hT
  have honeT : 1 ≤ T := le_trans (Nat.le_max_right T₀ 1) hT
  have hlog_nonneg : 0 ≤ Real.log (T : ℝ) := by
    exact Real.log_nonneg (by exact_mod_cast honeT)
  have hscale : c₀ * (localComplexity nu - ε) * Real.log (T : ℝ) ≤
      c₀ * (((rootSecondMoment nu 0 + rootSecondMoment nu 1) ^ 2
        * oracleSensitivity nu uε ^ 2 / localInformation nu uε)
        * Real.log (T : ℝ)) := by
    have hleft : c₀ * (localComplexity nu - ε) ≤
        c₀ * ((rootSecondMoment nu 0 + rootSecondMoment nu 1) ^ 2
          * oracleSensitivity nu uε ^ 2 / localInformation nu uε) :=
      mul_le_mul_of_nonneg_left hquotS (le_of_lt hc₀)
    have hright := mul_le_mul_of_nonneg_right hleft hlog_nonneg
    simpa [mul_assoc] using hright
  have hrisk := hT₀ Alg T hT₀T
  have hrisk' :
      c₀ * (((rootSecondMoment nu 0 + rootSecondMoment nu 1) ^ 2
        * oracleSensitivity nu uε ^ 2 / localInformation nu uε)
        * Real.log (T : ℝ))
        ≤ ⨆ h ∈ Set.Icc (-barη) barη, cumulativeNeymanRegret Alg (p h) T := by
    convert hrisk using 1
    ring
  exact hscale.trans hrisk'

end CausalSmith.Stat.NeymanRegretMinimax
