/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import CausalSmith.Experimentation.EXP_SaturationSkewThreshold_Research.Basic

namespace CausalSmith.Experimentation.SaturationSkew
open MeasureTheory
open scoped BigOperators

-- @node: lem:cai-randomized-saturation-moment-expansion
/-- SUBSTRATE-GATE (Cai–Pouget-Abadie–Airoldi 2022, Thm 9 + Cor. 12), realized as a
threaded `Prop` assumption (NOT a discharged lemma). The input `designVar n π`
DENOTES the design variance `Var_Z[ĥτ_DM]` of the difference-in-means estimator for
the `n`-th design at saturation vector `π` (named only via this docstring; not
separately formalized).

This gate now BINDS the scoped coefficient tuple `(V0,V1,V2,V3,V4)` to the Cai
specialization of the supplied homogeneous-linear-share working model `Yfull`: under
the isolated / anonymous / homogeneous-linear-share working model in the
leading-expansion domain, the design variance of every feasible vector expands as
`V0 + V1 μ₂ + V2 μ₂² + V3 μ₃ + V4 (μ₄ - μ₂²) + o(N⁻¹)` in the centered
treatment-proportion moments of the empirical law, and the isolated-cluster
simplification forces `V2 = 0`. Because the coefficients are now explicit arguments,
the consuming statements thread the SAME tuple they use to build `V`, so the
variance coefficients are bound to (not free of) the Cai specialization.

Consumers (`lem:variance-moment-reduction`, `prop:design-optimal-saturation`) take
this as an inline hypothesis. Visible substrate debt; excluded from the manifest. -/
def CaiRandomizedSaturationMomentExpansion {M m : ℕ}
    (Yfull : Fin M → Fin m → (Fin M → Fin m → Bool) → ℝ) (pbar : ℝ)
    (Mseq mseq : ℕ → ℕ)
    (Yseq : (n : ℕ) →
      Fin (Mseq n) → Fin (mseq n) → (Fin (Mseq n) → Fin (mseq n) → Bool) → ℝ)
    (designVar : (n : ℕ) → (Fin (Mseq n) → ℝ) → ℝ)
    (V0 V1 V2 V3 V4 : ℝ) : Prop :=
  IsolatedPartialInterference Yfull →
  AnonymousShareSpecialization Yfull →
  HomogeneousLinearShareWorkingModel pbar Yfull →
  CaiLeadingExpansionDomain pbar Mseq mseq Yseq →
    -- isolated-cluster simplification (Cor. 12): the quadratic-in-`μ₂` coefficient vanishes
    V2 = 0 ∧
    ∃ rem : ℕ → ℝ,
      Filter.Tendsto (fun n => rem n * ((Mseq n * mseq n : ℕ) : ℝ)) Filter.atTop (nhds 0) ∧
      ∀ (n : ℕ) (π : Fin (Mseq n) → ℝ), IsImplementable (Mseq n) (mseq n) pbar π →
        designVar n π
          = V0 + V1 * centeredMoment pbar 2 (empiricalLaw (Mseq n) π)
              + V2 * (centeredMoment pbar 2 (empiricalLaw (Mseq n) π)) ^ 2
              + V3 * centeredMoment pbar 3 (empiricalLaw (Mseq n) π)
              + V4 * (centeredMoment pbar 4 (empiricalLaw (Mseq n) π)
                  - (centeredMoment pbar 2 (empiricalLaw (Mseq n) π)) ^ 2)
              + rem n

end CausalSmith.Experimentation.SaturationSkew
