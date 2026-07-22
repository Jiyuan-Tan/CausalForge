/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import CausalSmith.Experimentation.EXP_SaturationSkewThreshold_Research.Basic
import CausalSmith.Experimentation.EXP_SaturationSkewThreshold_Research.Helpers

namespace CausalSmith.Experimentation.SaturationSkew

open MeasureTheory
open scoped BigOperators

-- @node: lem:variance-moment-reduction
theorem variance_moment_reduction {M m : ℕ}
    (Yfull : Fin M → Fin m → (Fin M → Fin m → Bool) → ℝ)
    (V0 V1 V2 V3 V4 pbar : ℝ) (Mseq mseq : ℕ → ℕ)
    (Yseq : (n : ℕ) →
      Fin (Mseq n) → Fin (mseq n) → (Fin (Mseq n) → Fin (mseq n) → Bool) → ℝ)
    (designVar : (n : ℕ) → (Fin (Mseq n) → ℝ) → ℝ)
    (hEq : EqualClusterSize M m (M * m))
    (hIso : IsolatedPartialInterference Yfull)
    (hAnon : AnonymousShareSpecialization Yfull)
    (hWork : HomogeneousLinearShareWorkingModel pbar Yfull)
    (hDom : CaiLeadingExpansionDomain pbar Mseq mseq Yseq)
    -- The Cai gate now binds the scoped coefficient tuple `(V0,V1,V2,V3,V4)` (with the
    -- isolated-cluster simplification `V2 = 0`) to `designVar`; the SAME tuple builds `V`.
    (hcai : CaiRandomizedSaturationMomentExpansion Yfull pbar Mseq mseq Yseq designVar V0 V1 V2 V3 V4)
    (hNz : ∀ n, ∃ z : ℤ, ((Mseq n * mseq n : ℕ) : ℝ) * pbar = z) :
    -- Finite leading-comparison equality: for every feasible saturation vector the
    -- `o(N⁻¹)`-free leading comparison (`designVar n π` minus the vanishing
    -- remainder `rem n`) is exactly `V(L_M(π))`.
    (∃ rem : ℕ → ℝ,
        Filter.Tendsto (fun n => rem n * ((Mseq n * mseq n : ℕ) : ℝ)) Filter.atTop (nhds 0) ∧
        ∀ (n : ℕ) (π : Fin (Mseq n) → ℝ), IsImplementable (Mseq n) (mseq n) pbar π →
          designVar n π
            = varianceFunctional V0 V1 V3 V4 pbar (empiricalLaw (Mseq n) π) + rem n) ∧
    (∀ (piseq : (n : ℕ) → Fin (Mseq n) → ℝ) (ν : Law),
        (∀ n, IsImplementable (Mseq n) (mseq n) pbar (piseq n)) →
        Filter.Tendsto (fun n => empiricalLaw (Mseq n) (piseq n)) Filter.atTop (nhds ν) →
        IsAdmissible pbar ν ∧
        Filter.Tendsto
          (fun n => varianceFunctional V0 V1 V3 V4 pbar (empiricalLaw (Mseq n) (piseq n)))
          Filter.atTop (nhds (varianceFunctional V0 V1 V3 V4 pbar ν))) ∧
      (∀ νstar : Law, IsMinimizer V0 V1 V3 V4 pbar νstar → cardSupportLe 3 νstar →
        ∃ piseq : (n : ℕ) → Fin (Mseq n) → ℝ,
          (∀ n, IsImplementable (Mseq n) (mseq n) pbar (piseq n)) ∧
          Filter.Tendsto
            (fun n => varianceFunctional V0 V1 V3 V4 pbar (empiricalLaw (Mseq n) (piseq n)))
            Filter.atTop (nhds (varianceFunctional V0 V1 V3 V4 pbar νstar))) ∧
      Filter.Tendsto
        (fun n => ⨅ π : {π : Fin (Mseq n) → ℝ // IsImplementable (Mseq n) (mseq n) pbar π},
            varianceFunctional V0 V1 V3 V4 pbar (empiricalLaw (Mseq n) π.1))
        Filter.atTop
        (nhds (⨅ ν : {ν : Law // IsAdmissible pbar ν},
            varianceFunctional V0 V1 V3 V4 pbar ν.1)) := by sorry

end CausalSmith.Experimentation.SaturationSkew
