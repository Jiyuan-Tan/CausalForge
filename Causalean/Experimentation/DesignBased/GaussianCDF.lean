/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Standard normal CDF facts (design-based presentation)

Thin adapter exposing the standard-normal cumulative distribution function to the design-based
interval theorems in the `.real (Iic t)` presentation they rely on definitionally.  The function
and every fact below are the canonical `Causalean.Mathlib.stdNormalCDF` from
`Causalean/Mathlib/Probability/StdNormalCDF.lean` — the single source of truth for the standard
normal CDF — re-exported under the `DesignBased.stdNormalCdf` name via `stdNormalCdf_eq`.  No proof
is duplicated here: nonnegativity, the upper bound, monotonicity, symmetry, and continuity all
delegate to the canonical lemmas.
-/

import Causalean.Mathlib.Probability.StdNormalCDF

/-! # Standard normal CDF adapter

The design-based standard-normal CDF is a namespace-local presentation of the canonical
Mathlib-facing CDF.

The definition `stdNormalCdf` uses the `.real (Iic t)` probability-measure presentation needed by
design-based interval and CLT statements, while `stdNormalCdf_eq` identifies it with
`Causalean.Mathlib.stdNormalCDF`. The remaining lemmas forward the reusable facts needed
downstream: nonnegativity, the upper bound by one, monotonicity, symmetry
`stdNormalCdf_neg`, and continuity `continuous_stdNormalCdf`.
-/

open MeasureTheory Set

namespace Causalean
namespace Experimentation
namespace DesignBased

/-- Standard normal cumulative distribution function `Φ(t) = P[Z ≤ t]`, `Z ∼ 𝒩(0,1)`, in the
`(gaussianReal 0 1).real (Iic t)` presentation used by the design-based interval theorems.
Definitionally the canonical `Causalean.Mathlib.stdNormalCDF` (see `stdNormalCdf_eq`). -/
noncomputable def stdNormalCdf (t : ℝ) : ℝ :=
  (ProbabilityTheory.gaussianReal 0 1).real (Set.Iic t)

/-- The design-based `.real (Iic)` presentation agrees with the canonical `stdNormalCDF`. -/
lemma stdNormalCdf_eq (t : ℝ) : stdNormalCdf t = Causalean.Mathlib.stdNormalCDF t := by
  rw [Causalean.Mathlib.stdNormalCDF_def]; exact (ProbabilityTheory.cdf_eq_real _ t).symm

/-- The standard-normal cumulative probability is nonnegative. -/
lemma stdNormalCdf_nonneg (t : ℝ) : 0 ≤ stdNormalCdf t := by
  rw [stdNormalCdf_eq]; exact Causalean.Mathlib.stdNormalCDF_nonneg t

/-- The standard-normal cumulative probability is at most one. -/
lemma stdNormalCdf_le_one (t : ℝ) : stdNormalCdf t ≤ 1 := by
  rw [stdNormalCdf_eq]; exact Causalean.Mathlib.stdNormalCDF_le_one t

/-- The standard-normal cumulative distribution function is monotone in its threshold. -/
lemma monotone_stdNormalCdf : Monotone stdNormalCdf := by
  rw [show stdNormalCdf = Causalean.Mathlib.stdNormalCDF from funext stdNormalCdf_eq]
  exact Causalean.Mathlib.stdNormalCDF_monotone

/-- **Symmetry of the standard normal CDF:** `Φ(−t) = 1 − Φ(t)`. -/
lemma stdNormalCdf_neg (t : ℝ) : stdNormalCdf (-t) = 1 - stdNormalCdf t := by
  rw [stdNormalCdf_eq, stdNormalCdf_eq]; exact Causalean.Mathlib.stdNormalCDF_neg t

/-- **Continuity of the standard normal CDF.** -/
lemma continuous_stdNormalCdf : Continuous stdNormalCdf := by
  rw [show stdNormalCdf = Causalean.Mathlib.stdNormalCDF from funext stdNormalCdf_eq]
  exact Causalean.Mathlib.stdNormalCDF_continuous

end DesignBased
end Experimentation
end Causalean
