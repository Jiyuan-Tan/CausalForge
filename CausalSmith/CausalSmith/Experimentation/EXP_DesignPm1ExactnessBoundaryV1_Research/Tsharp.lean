/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import CausalSmith.Experimentation.EXP_DesignPm1ExactnessBoundaryV1_Research.Basic
import CausalSmith.Experimentation.EXP_DesignPm1ExactnessBoundaryV1_Research.Helpers
import Mathlib.Data.Fin.VecNotation

/-! # Headline rounding-loss certificate (`thm:sharp-rho-star`)

The tight certificate `ρ_⋆ = Δ_m^±`, computed by the active-set SOCP over the
reduced triangle, with the exact zero-loss criterion `ρ_⋆ = 0` iff the relaxed
argmin meets the implementable slice `{y+z ≥ d_m}`. No exact `r_star` frontier is
asserted (honest open scope). -/

namespace CausalSmith.Experimentation.DesignPm1

open scoped BigOperators

/-- Reduced-coordinate active-set data `α = (c_x/q, c_y, c_z)` for the linear change
of variables `t = (q x, y, z)` that carries the reduced triangle `T_m` onto the scaled
simplex `Δ_M` (`M = 2m`) and `φ` onto `wsObj α β κ`. This is the `α` fed to
`lem:weighted-simplex-active-set` / `lem:weighted-simplex-truncation`. -/
noncomputable def sharpAlpha (m : ℕ) (a b r : ℝ) : Fin 3 → ℝ :=
  ![cX m a b r / qParam m, cY b r, cZ m]

/-- Reduced-coordinate weights `β = (1/q, 1, 1)` (so `β_y = β_z = 1`), the `β` fed to
`lem:weighted-simplex-active-set` / `lem:weighted-simplex-truncation` under the change of
variables `t = (q x, y, z)`. -/
noncomputable def sharpBeta (m : ℕ) : Fin 3 → ℝ :=
  ![1 / qParam m, 1, 1]

-- @node: thm:sharp-rho-star
/-- **Sharp `ρ_⋆` certificate.** Under two-block homophily, the rounding-loss
certificate equals the implementability gap (`ρ_⋆ = Δ_m^±`); the gap is nonnegative
(`Δ_m^± ≥ 0`, its definitional domain `[0,∞)`); `ρ_⋆ = 0` iff the relaxed argmin over
`T_m` meets the implementable slice `{y+z ≥ d_m}`; for `κ > 0` the relaxed minimizer
over `T_m` is *unique* (active-set uniqueness), and equivalently `ρ_⋆ = 0` iff that
unique minimizer satisfies `y+z ≥ d_m`; for `κ = 0` the relaxed argmin set is the
exposed face on the per-unit `α`-minimizing coordinates (`α = (c_x/q, c_y, c_z)`);
and for even `m` (`d_m = 0`) the certificate vanishes identically. No `r_star`
frontier is characterized.

The certificate is moreover computed by the finite active-set case split of the note:
under the change of variables `t = (q x, y, z)` (`α = sharpAlpha`, `β = sharpBeta`,
`M = 2m`), for `κ > 0` the unique relaxed minimizer is the active-set point of an
admissible support/multiplier `(S, λ)` (`lem:weighted-simplex-active-set`), with relaxed
value `M · λ`; and when the relaxed argmin misses the implementable slice `{y+z ≥ d_m}`,
the implementable value equals the objective on the truncation segment `{y+z = d_m}` at
the endpoint/interior selector `truncSelector` (`lem:weighted-simplex-truncation`). These
two clauses are the active-set / truncation computation the note displays.

This theorem does NOT realize `r_star`: it supplies only the zero-loss CRITERION
`ρ_⋆ = 0 ↔ relaxed argmin meets {y+z ≥ d_m}` (and, for `κ > 0`, its unique-minimizer
form), and asserts no `r_star` value, boundary, or sharp frontier. The `r_star` symbol's
`[0,∞)` space (the HONEST-OPEN cut-break frontier) is realized by its own dedicated
carrier `IsSharpExactnessBoundary` in `Basic.lean` — the `0 ≤ rStar` conjunct pins the
space and the zero-loss clause pins the separating role — not by this target block.

The probability-law symbol `P` enters this target block through `implementabilityGap`
(in the `ρ_⋆ = Δ_m^±` clause): `Δ_m^±` takes its implementable `sInf` over the second
moments `X(P)` of the laws `P ∈ P_m^sym`. That P realization is carried by the
authoritative cluster in `Basic.lean` — carrier `FiniteDesign (Fin (2*m) → Bool)` with
its `p_nonneg`/`p_sum` PMF fields, the design-class predicates
`BalancedDesignClass`/`blockExchangeableDesignClass`, and the consumers
`implementableCovarianceClass`/`implementabilityGap` (each `@realizes P`-tagged). -/
theorem sharp_rho_star (m : ℕ) (a b r kappa : ℝ) (hHom : TwoBlockHomophily m a b)
    (hr0 : 0 ≤ r) -- @realizes r(range 0 ≤ r pins r ∈ [0,∞))
    (hk : 0 ≤ kappa) : -- @realizes kappa(range 0 ≤ κ pins κ ∈ [0,∞), its definitional domain)
    roundingLossCertificate m a b r kappa = implementabilityGap m a b r kappa ∧
    -- @realizes rho_star(m,a,b,r,kappa)(standing range clause 0 ≤ ρ_⋆ pinning space [0,∞);
    -- discharged by the companion range lemma `roundingLossCertificate_nonneg` in Basic)
    0 ≤ roundingLossCertificate m a b r kappa ∧
    -- @realizes Delta_m^pm(r,kappa)(standing range clause 0 ≤ Δ_m^± pinning space [0,∞);
    -- discharged by the companion range lemma `implementabilityGap_nonneg` in Basic)
    0 ≤ implementabilityGap m a b r kappa ∧
    (roundingLossCertificate m a b r kappa = 0 ↔
      ∃ x y z, InReducedTriangle m x y z ∧
        (∀ x' y' z', InReducedTriangle m x' y' z' →
          reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa x y z
            ≤ reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa x' y' z') ∧
        parityThreshold m ≤ y + z) ∧
    (0 < kappa →
      (∃! t : ℝ × ℝ × ℝ, InReducedTriangle m t.1 t.2.1 t.2.2 ∧
        ∀ x' y' z', InReducedTriangle m x' y' z' →
          reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa t.1 t.2.1 t.2.2
            ≤ reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa x' y' z') ∧
      (roundingLossCertificate m a b r kappa = 0 ↔
        ∀ x y z, InReducedTriangle m x y z →
          (∀ x' y' z', InReducedTriangle m x' y' z' →
            reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa x y z
              ≤ reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa x' y' z') →
          parityThreshold m ≤ y + z)) ∧
    (kappa = 0 →
      ∀ x y z, InReducedTriangle m x y z →
        ((∀ x' y' z', InReducedTriangle m x' y' z' →
            reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa x y z
              ≤ reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa x' y' z')
          ↔ (x ≠ 0 → cX m a b r / qParam m ≤ cY b r ∧ cX m a b r / qParam m ≤ cZ m) ∧
            (y ≠ 0 → cY b r ≤ cX m a b r / qParam m ∧ cY b r ≤ cZ m) ∧
            (z ≠ 0 → cZ m ≤ cX m a b r / qParam m ∧ cZ m ≤ cY b r))) ∧
    -- Active-set computation of the relaxed minimizer (lem:weighted-simplex-active-set):
    -- for κ > 0 the unique relaxed argmin over `T_m` is the active-set point of an
    -- admissible support/multiplier `(S, λ)` under the change of variables `t = (q x, y, z)`
    -- (`α = sharpAlpha`, `β = sharpBeta`), with relaxed value `M · λ` (`M = 2m`).
    (0 < kappa →
      ∃ S : Finset (Fin 3), ∃ lam : ℝ,
        IsAdmissibleSupport (sharpAlpha m a b r) (sharpBeta m) kappa S lam ∧
        InReducedTriangle m
          (activeSetPoint (2 * (m : ℝ)) (sharpAlpha m a b r) (sharpBeta m) S lam 0 / qParam m)
          (activeSetPoint (2 * (m : ℝ)) (sharpAlpha m a b r) (sharpBeta m) S lam 1)
          (activeSetPoint (2 * (m : ℝ)) (sharpAlpha m a b r) (sharpBeta m) S lam 2) ∧
        (∀ x' y' z', InReducedTriangle m x' y' z' →
          reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa
              (activeSetPoint (2 * (m : ℝ)) (sharpAlpha m a b r) (sharpBeta m) S lam 0 / qParam m)
              (activeSetPoint (2 * (m : ℝ)) (sharpAlpha m a b r) (sharpBeta m) S lam 1)
              (activeSetPoint (2 * (m : ℝ)) (sharpAlpha m a b r) (sharpBeta m) S lam 2)
            ≤ reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa x' y' z') ∧
        relaxedReducedValue m a b r kappa = 2 * (m : ℝ) * lam) ∧
    -- Truncation correction (lem:weighted-simplex-truncation): when the relaxed argmin
    -- set is disjoint from the implementable slice `{y+z ≥ d_m}`, the implementable value
    -- is attained on the truncation segment `{y+z = d_m}` at the endpoint/interior selector
    -- `truncSelector`, so `Δ_m^±` is computed by this boundary-segment formula.
    ((¬ ∃ x y z, InReducedTriangle m x y z ∧
        (∀ x' y' z', InReducedTriangle m x' y' z' →
          reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa x y z
            ≤ reducedObjective (qParam m) (cX m a b r) (cY b r) (cZ m) kappa x' y' z') ∧
        parityThreshold m ≤ y + z) →
      implementableReducedValue m a b r kappa =
        wsObj (sharpAlpha m a b r) (sharpBeta m) kappa
          (truncSegPoint (2 * (m : ℝ)) (parityThreshold m)
            (truncSelector (2 * (m : ℝ)) (parityThreshold m)
              (sharpAlpha m a b r) (sharpBeta m) kappa))) ∧
    (Even m → roundingLossCertificate m a b r kappa = 0) := by
  have hGapEq :
      roundingLossCertificate m a b r kappa = implementabilityGap m a b r kappa := by
    rw [roundingLossCertificate, rounding_gap_reduction m a b r kappa hHom hk]
  refine ⟨hGapEq, roundingLossCertificate_nonneg m a b r kappa hHom hr0 hk,
    implementabilityGap_nonneg m a b r kappa hHom hr0 hk,
    sharp_roundingLoss_zero_iff_argmin_meets_slice m a b r kappa hHom hk, ?_, ?_, ?_, ?_, ?_⟩
  · intro hkpos
    have hAU := sharp_reduced_active_set_and_unique m a b r kappa hHom hk hkpos
    exact ⟨hAU.1,
      sharp_roundingLoss_zero_iff_unique_argmin_subset_slice m a b r kappa
        hHom hk hkpos hAU.1⟩
  · intro hk0 x y z hT
    exact sharp_kappa_zero_reduced_min_iff m a b r kappa x y z hHom hk0 hT
  · intro hkpos
    have hAU := sharp_reduced_active_set_and_unique m a b r kappa hHom hk hkpos
    simpa [sharpAlpha, sharpBeta] using hAU.2
  · intro hNoMeet
    simpa [sharpAlpha, sharpBeta] using
      sharp_truncation_value_of_no_reduced_argmin_in_slice m a b r kappa hHom hk hNoMeet
  · intro hEven
    exact sharp_roundingLoss_zero_of_even m a b r kappa hHom hk hEven

end CausalSmith.Experimentation.DesignPm1
