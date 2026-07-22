/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Mathlib.Optimization.SimplexActiveSetDefs
import Mathlib.Data.Fin.VecNotation

/-! # Weighted-simplex truncation: shared definitions

The parity-truncated simplex `K_d`, its boundary segment `H_d` (`truncSegPoint`),
and the endpoint/interior selector `s⋆` (`truncSelector`). Split out of the main
truncation file so both the convexity/reduction helper and the 1-D slice helper can
reference them. -/

namespace Causalean.Mathlib.Optimization

open scoped BigOperators

/-- Membership in the parity-truncated simplex `K_d = {t ∈ Δ_M : t_y + t_z ≥ d}`. -/
def InTruncSimplex (M d : ℝ) (t : Fin 3 → ℝ) : Prop :=
  InSimplex M t ∧ d ≤ t 1 + t 2

/-- The boundary segment `H_d`: the point with `t_x = M − d`, `t_y = s`, `t_z = d − s`. -/
def truncSegPoint (M d s : ℝ) : Fin 3 → ℝ := ![M - d, s, d - s]

/-- The endpoint/interior selector `s⋆` on `H_d`, with `δ = α_y − α_z`
and `A = β_x (M − d)²`:
`s⋆ = 0` if `δ ≥ κ d / √(A + d²)`, `s⋆ = d` if `δ ≤ − κ d / √(A + d²)`, and
otherwise the interior root `s⋆ = (d − δ √((A + d²/2)/(κ² − δ²/2)))/2`.
At `κ = 0` the two guards collapse to `0 ≤ δ` and `δ ≤ 0`, recovering the
`κ = 0` endpoint rule `s⋆ = 0` if `δ ≥ 0`, `s⋆ = d` if `δ ≤ 0`. -/
noncomputable def truncSelector (M d : ℝ) (α β : Fin 3 → ℝ) (kappa : ℝ) : ℝ :=
  let δ := α 1 - α 2
  let A := β 0 * (M - d) ^ 2
  if kappa * d / Real.sqrt (A + d ^ 2) ≤ δ then 0
  else if δ ≤ -(kappa * d / Real.sqrt (A + d ^ 2)) then d
  else (d - δ * Real.sqrt ((A + d ^ 2 / 2) / (kappa ^ 2 - δ ^ 2 / 2))) / 2

end Causalean.Mathlib.Optimization
