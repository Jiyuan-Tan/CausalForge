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

-- @node: prop:design-optimal-saturation
theorem design_optimal_saturation {M m : ℕ}
    (Yfull : Fin M → Fin m → (Fin M → Fin m → Bool) → ℝ)
    (V0 V1 V2 V3 V4 pbar : ℝ) (Mseq mseq : ℕ → ℕ)
    (Yseq : (n : ℕ) →
      Fin (Mseq n) → Fin (mseq n) → (Fin (Mseq n) → Fin (mseq n) → Bool) → ℝ)
    (designVar : (n : ℕ) → (Fin (Mseq n) → ℝ) → ℝ)
    (hp0 : 0 ≤ pbar) (hp1 : pbar ≤ 1)
    (hEq : EqualClusterSize M m (M * m))
    (hIso : IsolatedPartialInterference Yfull)
    (hAnon : AnonymousShareSpecialization Yfull)
    (hWork : HomogeneousLinearShareWorkingModel pbar Yfull)
    (hDom : CaiLeadingExpansionDomain pbar Mseq mseq Yseq)
    -- Cai gate carried transitively from `variance_moment_reduction`: the bound tuple
    -- `(V0,V1,V2,V3,V4)` (with `V2 = 0`) is the same one used to build `V`.
    (hcai : CaiRandomizedSaturationMomentExpansion Yfull pbar Mseq mseq Yseq designVar V0 V1 V2 V3 V4)
    (hext : ExtremeMomentSliceSupport)
    (hNz : ∀ n, ∃ z : ℤ, ((Mseq n * mseq n : ℕ) : ℝ) * pbar = z) :
    (∀ (piseq : (n : ℕ) → Fin (Mseq n) → ℝ) (ν : Law),
        (∀ n, IsImplementable (Mseq n) (mseq n) pbar (piseq n)) →
        Filter.Tendsto (fun n => empiricalLaw (Mseq n) (piseq n)) Filter.atTop (nhds ν) →
        ∃ νmin : Law, IsMinimizer V0 V1 V3 V4 pbar νmin ∧
          varianceFunctional V0 V1 V3 V4 pbar νmin
            ≤ varianceFunctional V0 V1 V3 V4 pbar ν) ∧
      (∃ νstar : Law, IsMinimizer V0 V1 V3 V4 pbar νstar ∧ cardSupportLe 3 νstar ∧
        ∃ piseq : (n : ℕ) → Fin (Mseq n) → ℝ,
          (∀ n, IsImplementable (Mseq n) (mseq n) pbar (piseq n)) ∧
          Filter.Tendsto
            (fun n => varianceFunctional V0 V1 V3 V4 pbar (empiricalLaw (Mseq n) (piseq n)))
            Filter.atTop (nhds (varianceFunctional V0 V1 V3 V4 pbar νstar))) ∧
      (BudgetInterior pbar →
        (IsMinimizer V0 V1 V3 V4 pbar (diracLaw pbar)
          ↔ ∀ d ∈ centeredSupportDomain pbar, 0 ≤ V1 + V3 * d + V4 * d ^ 2)) ∧
      ((pbar = 0 ∨ pbar = 1) → ∀ ν : Law, IsAdmissible pbar ν ↔ ν = diracLaw pbar) ∧
      Filter.Tendsto
        (fun n => ⨅ π : {π : Fin (Mseq n) → ℝ // IsImplementable (Mseq n) (mseq n) pbar π},
            varianceFunctional V0 V1 V3 V4 pbar (empiricalLaw (Mseq n) π.1))
        Filter.atTop
        (nhds (⨅ ν : {ν : Law // IsAdmissible pbar ν},
            varianceFunctional V0 V1 V3 V4 pbar ν.1)) := by sorry

end CausalSmith.Experimentation.SaturationSkew
