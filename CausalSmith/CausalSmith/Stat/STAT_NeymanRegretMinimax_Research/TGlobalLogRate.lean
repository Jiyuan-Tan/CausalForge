/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Global logarithmic minimax converse — CONDITIONAL (not certified)

`thm:global-log-rate`: the uniform `inf_Alg sup_nu 𝔯_T ≥ c log T` converse on a
compact tangent-regular band, ruling out any `o(log T)` claim.

**BANKING STATUS: CONDITIONAL, NOT CERTIFIED.**  Compiles sorry-free and axiom-clean,
but takes the broad `LocalNeighborhoodRiskInputs` gate (`hbridge`), which over-assumes
content the source note DERIVES (the `b_t` recursion, the domination, and the sup
bound) — flagged by the F2.5 faithfulness reviewer.  Documented as a conditional
extension, NOT certified.  The CERTIFIED core is the gate-free machinery; see
`SUBSTRATE_DEBT.md` and the writeup Honest-scope.  The tilt-band continuity it uses
IS certified (derived in `band_continuity_for_linear_tilts`).
-/

import CausalSmith.Stat.STAT_NeymanRegretMinimax_Research.TInstanceLocalMinimax

namespace CausalSmith.Stat.NeymanRegretMinimax

open MeasureTheory
open scoped BigOperators Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- **Closed-band class frontier** `K(underline_m, overline_m, underline_r)
= sup_{nu ∈ M(underline_m, overline_m, underline_r)} κ_nu`: the supremum of the
local complexity `κ_nu = localComplexity nu` over the closed regular band `MBand`.
This is the DEFINITIONAL realization of the core symbol `K` (a setup/environment
symbol bound in S1) — its space is `[0, ∞]` and it is carried by `sSup` over the
band membership predicate `MBand`.  The closed-FORM moment-envelope evaluation of
this sup is descoped (no ρ-envelope / three-point extremal cluster is scaffolded),
so ONLY the definitional sup is realized here.  It is a DISTINCT object from the
strict-interior sup `K^circ = sup_{nu ∈ M^circ} κ_nu` used as the constant in
`global_log_rate` below (the local tilt must stay strictly inside the closed band,
so the theorem uses the strict-interior sup, with `K^circ ≤ K`). -/
-- @realizes K(underline_m, overline_m, underline_r)(carrier sSup over MBand of
--   localComplexity = sup_{nu ∈ M(um,om,ur)} κ_nu; space [0,∞])
noncomputable def bandFrontier (um om ur : ℝ) : ℝ :=
  sSup {v | ∃ nu : Measure (ℝ × ℝ), MBand um om ur nu ∧ v = localComplexity nu}

-- @node: thm:global-log-rate
/-- **Global logarithmic minimax converse.**  For band radii `0 < um < om ≤ 1`,
`ur > 0` whose strict-interior subclass `M^circ` is nonempty, the minimax
cumulative Neyman regret over the closed band is at least
`c₀ · (K^circ − ε) · log T` for all large `T`, where `c₀ > 0` is a universal
numerical constant, `K^circ = sup_{nu ∈ M^circ} κ_nu` is the strict-interior
complexity supremum, and `ε > 0` is an arbitrary approximation slack for that
supremum (matching the `α`-slack in the local-to-global lift).  This restores the
`c ∝ sup_{M^circ} κ_nu` content the note states (a bare `∃ c > 0` would drop it).
This is an honest CONDITIONAL theorem: it assumes `LocalNeighborhoodRiskInputs`,
the disclosed sequential van Trees / DQM Fisher-tensorization bridge from the
external substrate debt.  The tilt band-functional continuity is NOT assumed here:
it is derived inside `band_continuity_for_linear_tilts` from the linear-tilt
construction. -/
-- @realizes epsilon(positive slack approximating K^circ = sup κ_nu)
-- @realizes underline_r(radius carrier ur : ℝ; space (0,∞) pinned here by hur : 0 < ur)
-- @realizes m_0, m_1(strict-interior band um < m_a < om, both arms; M^circ site)
-- @realizes r_{0,nu}, r_{1,nu}(strict tangent lower bound ur < r_{a,nu}, both arms; M^circ site)
-- @realizes pi_nu_star(range (0,1) via InteriorSecondMoments in MBand/MTan)
-- NOTE (constant is the strict-interior sup): the constant multiplying `log T` in
--   the conclusion below is the THEOREM-LOCAL strict-interior complexity supremum
--     K^circ = sSup {v | ∃ nu, MTan nu ∧ (um < m_a < om ∧ ur < r_{a,nu} both arms)
--                          ∧ v = localComplexity nu}
--            = sup_{nu ∈ M^circ} κ_nu,
--   which is EXACTLY the constant `thm:global-log-rate` states in core.json
--   (`c = universal const × sup_{nu ∈ M^circ} κ_nu`, on the STRICT interior — the local
--   tilt must stay strictly inside the closed band).  It is DELIBERATELY the strict-interior
--   sup and is a DISTINCT object from the closed-band class-frontier symbol
--   `K(underline_m, overline_m, underline_r) = sup_{nu ∈ M(um,om,ur)} κ_nu`, which is realized
--   DEFINITIONALLY by `bandFrontier um om ur` above (tagged `@realizes K`); the closed-FORM
--   moment-envelope evaluation of that frontier (the ρ-envelope cluster) stays descoped, but
--   the symbol `K` itself now carries its definitional realization.  We have `K^circ ≤ K`.
--   Each member value localComplexity nu = κ_nu ∈ [0,∞) is sup'd over the nonempty M^circ
--   (hstrict_nonempty).
theorem global_log_rate
    (hbridge : LocalNeighborhoodRiskInputs.{u}) :
    -- `c₀ > 0` is a SINGLE universal numerical constant, quantified OUTSIDE the band
    -- parameters (`∃ c₀, ∀ band, …`), so it does not depend on `um, om, ur`.  This
    -- matches the note's `c = (universal constant) × sup κ_nu` form and mirrors the
    -- structure of `instance_local_minimax`.
    ∃ c₀ : ℝ, 0 < c₀ ∧
      ∀ (um om ur : ℝ),
        -- @realizes underline_m, overline_m(joint hum ∧ humom ∧ hom = 0<um<om≤1)
        0 < um →     -- @realizes underline_m(space (0,1]: lower end 0 < um)
        um < om →    -- @realizes underline_m(um≤1 via om≤1) @realizes overline_m(0<om)
        om ≤ 1 →     -- @realizes overline_m(space (0,1]: upper end om ≤ 1)
        0 < ur →     -- @realizes underline_r
        (∃ nu : Measure (ℝ × ℝ), MTan nu ∧
          ∀ a : Fin 2, um < rootSecondMoment nu a ∧ rootSecondMoment nu a < om
            ∧ ur < armTangentStrength nu a) →
        (∀ nu : Measure (ℝ × ℝ), MTan nu →
          (∀ a : Fin 2, um < rootSecondMoment nu a ∧ rootSecondMoment nu a < om
            ∧ ur < armTangentStrength nu a) →
          ∃ μ : Measure Ω, SuperpopulationIID μ nu) →
        (∀ (Alg : AdaptiveAlgorithm) (T : ℕ),
          BddAbove (Set.range fun nu : {nu : Measure (ℝ × ℝ) // MBand um om ur nu} =>
            cumulativeNeymanRegret Alg nu.1 T)) →
        (∀ (Alg : AdaptiveAlgorithm) (T : ℕ),
          0 ≤ ⨆ nu : {nu : Measure (ℝ × ℝ) // MBand um om ur nu},
            cumulativeNeymanRegret Alg nu.1 T) →
        ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℕ, ∀ T : ℕ, T₀ ≤ T →
          c₀ * ((sSup {v | ∃ nu : Measure (ℝ × ℝ), MTan nu ∧
                    (∀ a : Fin 2, um < rootSecondMoment nu a
                      ∧ rootSecondMoment nu a < om
                      ∧ ur < armTangentStrength nu a)
                    ∧ v = localComplexity nu}) - ε)
              * Real.log (T : ℝ)
            ≤ ⨅ Alg : AdaptiveAlgorithm,
                ⨆ nu : {nu : Measure (ℝ × ℝ) // MBand um om ur nu},
                  cumulativeNeymanRegret Alg nu.1 T := by
  rcases local_neighborhood_cumulative_risk (Ω := Ω) hbridge with
    ⟨c₀, hc₀, hrisk_all⟩
  refine ⟨c₀, hc₀, ?_⟩
  intro um om ur hum humom hom hur hstrict_nonempty hIID hBandBdd hBandSupNonneg
    ε hε
  let strictValues : Set ℝ :=
    {v | ∃ nu : Measure (ℝ × ℝ), MTan nu ∧
      (∀ a : Fin 2, um < rootSecondMoment nu a ∧ rootSecondMoment nu a < om
        ∧ ur < armTangentStrength nu a)
      ∧ v = localComplexity nu}
  have hvalues_nonempty : strictValues.Nonempty := by
    rcases hstrict_nonempty with ⟨nu, hnu, hstrict⟩
    exact ⟨localComplexity nu, ⟨nu, hnu, hstrict, rfl⟩⟩
  have hKlt : sSup strictValues - ε < sSup strictValues := sub_lt_self _ hε
  rcases exists_lt_of_lt_csSup hvalues_nonempty hKlt with ⟨_, hv, hvlt⟩
  rcases hv with ⟨nu, hnu, hstrict, rfl⟩
  let δ : ℝ := localComplexity nu - (sSup strictValues - ε)
  have hδpos : 0 < δ := by
    dsimp [δ]
    linarith
  let rayValues : Set ℝ := {v | ∃ u ∈ feasibleDirectionSet nu,
    v = (rootSecondMoment nu 0 + rootSecondMoment nu 1) ^ 2
      * oracleSensitivity nu u ^ 2 / localInformation nu u}
  have hU : (feasibleDirectionSet nu).Nonempty :=
    (feasible_directions_nonempty nu hnu).1
  have hray_nonempty : rayValues.Nonempty := by
    rcases hU with ⟨u0, hu0⟩
    exact ⟨_, ⟨u0, hu0, rfl⟩⟩
  have hklt_local : localComplexity nu - δ < localComplexity nu := sub_lt_self _ hδpos
  rw [localComplexity] at hklt_local
  change localComplexity nu - δ < sSup rayValues at hklt_local
  rcases exists_lt_of_lt_csSup hray_nonempty hklt_local with ⟨_, huval, hu_lt⟩
  rcases huval with ⟨u, hu, rfl⟩
  have hquot_lower :
      sSup strictValues - ε ≤
        (rootSecondMoment nu 0 + rootSecondMoment nu 1) ^ 2
          * oracleSensitivity nu u ^ 2 / localInformation nu u := by
    have hδeq : localComplexity nu - δ = sSup strictValues - ε := by
      dsimp [δ]
      ring
    rw [← hδeq]
    exact le_of_lt hu_lt
  have hJpos : 0 < localInformation nu u := hu.1
  rcases linear_tilt_path_valid nu hnu u hJpos with ⟨p, hlin, hp⟩
  rcases hIID nu hnu hstrict with ⟨μ, hiid⟩
  rcases hrisk_all nu μ hnu hiid u hu p hlin hp with ⟨barη, hbarη, hriskη⟩
  rcases band_continuity_for_linear_tilts um om ur hum humom hom
      nu hnu hstrict u p hlin hp with
    ⟨ηband, hηband, hband⟩
  let η : ℝ := min barη ηband / 2
  have hηpos : 0 < η := by
    dsimp [η]
    exact half_pos (lt_min hbarη hηband)
  have hη_le_bar : η ≤ barη := by
    dsimp [η]
    exact (div_le_self (le_of_lt (lt_min hbarη hηband)) (by norm_num)).trans (min_le_left _ _)
  have hη_le_band : η ≤ ηband := by
    dsimp [η]
    exact (div_le_self (le_of_lt (lt_min hbarη hηband)) (by norm_num)).trans (min_le_right _ _)
  rcases hriskη η hηpos hη_le_bar with ⟨T₀, hT₀⟩
  refine ⟨max T₀ 1, ?_⟩
  intro T hT
  have hT₀T : T₀ ≤ T := le_trans (Nat.le_max_left T₀ 1) hT
  have honeT : 1 ≤ T := le_trans (Nat.le_max_right T₀ 1) hT
  have hlog_nonneg : 0 ≤ Real.log (T : ℝ) :=
    Real.log_nonneg (by exact_mod_cast honeT)
  letI : Nonempty AdaptiveAlgorithm :=
    ⟨{ policy := fun _ _ => (1 : ℝ) / 2
       predictable := by
        constructor
        · intro t
          exact measurable_const
        · intro t hist
          exact ⟨by norm_num, by norm_num⟩ }⟩
  refine le_ciInf ?_
  intro Alg
  have hscale :
      c₀ * (sSup strictValues - ε) * Real.log (T : ℝ) ≤
        c₀ * (((rootSecondMoment nu 0 + rootSecondMoment nu 1) ^ 2
          * oracleSensitivity nu u ^ 2 / localInformation nu u)
          * Real.log (T : ℝ)) := by
    have hleft : c₀ * (sSup strictValues - ε) ≤
        c₀ * ((rootSecondMoment nu 0 + rootSecondMoment nu 1) ^ 2
          * oracleSensitivity nu u ^ 2 / localInformation nu u) :=
      mul_le_mul_of_nonneg_left hquot_lower (le_of_lt hc₀)
    have hright := mul_le_mul_of_nonneg_right hleft hlog_nonneg
    simpa [mul_assoc] using hright
  have hrisk := hT₀ Alg T hT₀T
  have hrisk' :
      c₀ * (((rootSecondMoment nu 0 + rootSecondMoment nu 1) ^ 2
        * oracleSensitivity nu u ^ 2 / localInformation nu u)
        * Real.log (T : ℝ))
        ≤ ⨆ h ∈ Set.Icc (-η) η, cumulativeNeymanRegret Alg (p h) T := by
    convert hrisk using 1
    ring
  have hlocal_le_band :
      (⨆ h ∈ Set.Icc (-η) η, cumulativeNeymanRegret Alg (p h) T)
        ≤ ⨆ nu : {nu : Measure (ℝ × ℝ) // MBand um om ur nu},
            cumulativeNeymanRegret Alg nu.1 T := by
    refine ciSup_le ?_
    intro h
    by_cases hhmem : h ∈ Set.Icc (-η) η
    · haveI : Nonempty (h ∈ Set.Icc (-η) η) := ⟨hhmem⟩
      refine ciSup_le ?_
      intro hh
      have hh_abs : |h| ≤ η := abs_le.mpr hh
      have hh_band_radius : |h| ≤ ηband := le_trans hh_abs hη_le_band
      have hpband : MBand um om ur (p h) := hband h hh_band_radius
      exact le_ciSup (hBandBdd Alg T) ⟨p h, hpband⟩
    · haveI : IsEmpty (h ∈ Set.Icc (-η) η) := ⟨fun hh => hhmem hh⟩
      rw [Real.iSup_of_isEmpty]
      exact hBandSupNonneg Alg T
  exact hscale.trans (hrisk'.trans hlocal_le_band)

end CausalSmith.Stat.NeymanRegretMinimax
