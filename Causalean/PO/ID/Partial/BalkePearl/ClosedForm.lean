/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Balke-Pearl IV bounds: the closed-form LP endpoints

`Main.lean` states necessity abstractly, as membership in the *range* of the LP
objective over feasible latent tables, and `IntervalForm.lean` restates it as
membership in `[sInf, sSup]` of that range. Neither exhibits the endpoints as
formulas in the observed data — an analyst cannot compute either from a data set.

This file supplies the missing closed form. Balke and Pearl (1997) solve the
linear program explicitly: each endpoint is a maximum (resp. minimum) of eight
affine functions of the eight observed cell probabilities `p_{yd.z}`. The eight
expressions are the vertices of the dual feasible region, so each one is a
nonnegative combination of the feasibility constraints and is therefore a valid
bound; the maximum over the eight is the exact LP optimum.

## Main results

* `bpLowerTerm`, `bpUpperTerm` — the eight dual-vertex expressions per side.
* `bpLower`, `bpUpper` — the closed-form endpoints (max resp. min of the eight).
* `bpLower_le_BPObjective`, `BPObjective_le_bpUpper` — validity on feasible tables.
* `BPIdentifiedInterval_subset_Icc` — the identified interval sits inside
  `[bpLower, bpUpper]`.
* `ATE_mem_Icc_bpLower_bpUpper` — the analyst-facing bound on the true ATE.

## Scope

Only *validity* of the closed form is proved here. Attainment of the two
endpoints — which upgrades the containment to an equality, and is what makes the
Balke-Pearl bounds sharp — is not yet formalized; see the note at the end of the
file.
-/

import Causalean.PO.ID.Partial.BalkePearl.Main

/-! # Balke-Pearl bounds in closed form

This file gives the explicit Balke-Pearl formulas for the endpoints of the
identified interval for the average treatment effect under a binary instrument,
as a maximum and a minimum of eight affine functions of the observed cell
probabilities, and proves that they bound the true effect.
-/

namespace Causalean
namespace PO

open MeasureTheory

namespace POBalkePearlSystem

variable {P : POSystem} (S : POBalkePearlSystem P)

/-! ### The eight lower expressions

Writing `p y d z` for `cellProb y d z = P(Y = y, D = d | Z = z)`, the eight
expressions are the vertices of the dual of the minimization LP. The first four
are the "short" family `p 0 0 z + p 1 1 z' - 1` over the four instrument pairs;
the last four are the "long" vertices, in which one cell probability enters with
weight two. -/

/-- The `i`-th of the eight affine lower expressions in the Balke-Pearl closed
form for the average treatment effect. Each is a valid lower bound on the effect,
and their maximum is exactly the smallest effect compatible with the data. -/
noncomputable def bpLowerTerm (i : Fin 8) : ℝ :=
  let p := S.cellProb
  match i with
  | 0 => p false false false + p true true false - 1
  | 1 => p false false true + p true true true - 1
  | 2 => p true true false + p false false true - 1
  | 3 => p false false false + p true true true - 1
  | 4 => p false false false + 2 * p true true false
           - p true false true - p true true true - 1
  | 5 => 2 * p false false false + p true true false
           - p false false true - p false true true - 1
  | 6 => -p false false false - p false true false
           + 2 * p false false true + p true true true - 1
  | 7 => -p true false false - p true true false
           + p false false true + 2 * p true true true - 1

/-- The `i`-th of the eight affine upper expressions in the Balke-Pearl closed
form for the average treatment effect. Each is a valid upper bound on the effect,
and their minimum is exactly the largest effect compatible with the data. -/
noncomputable def bpUpperTerm (i : Fin 8) : ℝ :=
  let p := S.cellProb
  match i with
  | 0 => 1 - p true false false - p false true false
  | 1 => 1 - p true false true - p false true true
  | 2 => 1 - p true false false - p false true true
  | 3 => 1 - p false true false - p true false true
  | 4 => 1 - p true false false - 2 * p false true false
           + p false false true + p false true true
  | 5 => 1 + p true false false + p true true false
           - 2 * p true false true - p false true true
  | 6 => 1 - 2 * p true false false - p false true false
           + p true false true + p true true true
  | 7 => 1 + p false false false + p false true false
           - p true false true - 2 * p false true true

/-- The Balke-Pearl closed-form lower endpoint: the largest of the eight lower
expressions. This is the smallest average treatment effect compatible with the
observed distribution under a valid binary instrument. -/
noncomputable def bpLower : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty S.bpLowerTerm

/-- The Balke-Pearl closed-form upper endpoint: the smallest of the eight upper
expressions. This is the largest average treatment effect compatible with the
observed distribution under a valid binary instrument. -/
noncomputable def bpUpper : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty S.bpUpperTerm

/-! ### Validity of each expression

Each of the sixteen expressions is a nonnegative combination of the feasibility
constraints, so `linarith` discharges it from the eight marginal equations, the
normalization, and the sixteen nonnegativity facts. -/

/-- Every lower expression bounds the objective from below on feasible tables. -/
theorem bpLowerTerm_le_BPObjective (hA : S.BaseAssumptions)
    {π : Bool → Bool → Bool → Bool → ℝ} (hπ : BPFeasible S hA π) (i : Fin 8) :
    S.bpLowerTerm i ≤ BPObjective π := by
  have hs := hπ.sum_one
  have hn := hπ.nonneg
  have hm := hπ.marginal
  have e000 := hm false false false
  have e100 := hm true false false
  have e010 := hm false true false
  have e110 := hm true true false
  have e001 := hm false false true
  have e101 := hm true false true
  have e011 := hm false true true
  have e111 := hm true true true
  simp only [Fintype.sum_bool, dArm, yArm] at hs e000 e100 e010 e110 e001 e101 e011 e111
  norm_num at hs e000 e100 e010 e110 e001 e101 e011 e111
  fin_cases i <;>
    simp only [bpLowerTerm, BPObjective, Fintype.sum_bool, boolToReal] <;>
    simp only [e000, e100, e010, e110, e001, e101, e011, e111] <;>
    linarith [hn false false false false, hn false false false true,
      hn false false true false, hn false false true true,
      hn false true false false, hn false true false true,
      hn false true true false, hn false true true true,
      hn true false false false, hn true false false true,
      hn true false true false, hn true false true true,
      hn true true false false, hn true true false true,
      hn true true true false, hn true true true true]

/-- Every upper expression bounds the objective from above on feasible tables. -/
theorem BPObjective_le_bpUpperTerm (hA : S.BaseAssumptions)
    {π : Bool → Bool → Bool → Bool → ℝ} (hπ : BPFeasible S hA π) (i : Fin 8) :
    BPObjective π ≤ S.bpUpperTerm i := by
  have hs := hπ.sum_one
  have hn := hπ.nonneg
  have hm := hπ.marginal
  have e000 := hm false false false
  have e100 := hm true false false
  have e010 := hm false true false
  have e110 := hm true true false
  have e001 := hm false false true
  have e101 := hm true false true
  have e011 := hm false true true
  have e111 := hm true true true
  simp only [Fintype.sum_bool, dArm, yArm] at hs e000 e100 e010 e110 e001 e101 e011 e111
  norm_num at hs e000 e100 e010 e110 e001 e101 e011 e111
  fin_cases i <;>
    simp only [bpUpperTerm, BPObjective, Fintype.sum_bool, boolToReal] <;>
    simp only [e000, e100, e010, e110, e001, e101, e011, e111] <;>
    linarith [hn false false false false, hn false false false true,
      hn false false true false, hn false false true true,
      hn false true false false, hn false true false true,
      hn false true true false, hn false true true true,
      hn true false false false, hn true false false true,
      hn true false true false, hn true false true true,
      hn true true false false, hn true true false true,
      hn true true true false, hn true true true true]

/-! ### The closed-form bounds -/

/-- The closed-form lower endpoint bounds the objective on feasible tables. -/
theorem bpLower_le_BPObjective (hA : S.BaseAssumptions)
    {π : Bool → Bool → Bool → Bool → ℝ} (hπ : BPFeasible S hA π) :
    S.bpLower ≤ BPObjective π :=
  Finset.sup'_le _ _ (fun i _ => S.bpLowerTerm_le_BPObjective hA hπ i)

/-- The closed-form upper endpoint bounds the objective on feasible tables. -/
theorem BPObjective_le_bpUpper (hA : S.BaseAssumptions)
    {π : Bool → Bool → Bool → Bool → ℝ} (hπ : BPFeasible S hA π) :
    BPObjective π ≤ S.bpUpper :=
  Finset.le_inf' _ _ (fun i _ => S.BPObjective_le_bpUpperTerm hA hπ i)

/-- The identified interval is contained in the closed-form interval. -/
theorem BPIdentifiedInterval_subset_Icc (hA : S.BaseAssumptions) :
    S.BPIdentifiedInterval hA ⊆ Set.Icc S.bpLower S.bpUpper :=
  PartialID.identifiedInterval_subset_Icc
    (fun _ h => S.bpLower_le_BPObjective hA h)
    (fun _ h => S.BPObjective_le_bpUpper hA h)

/-- **The Balke-Pearl bound in closed form.** The true average treatment effect
lies between the largest of the eight lower expressions and the smallest of the
eight upper expressions, both computable directly from the observed cell
probabilities. -/
theorem ATE_mem_Icc_bpLower_bpUpper (hA : S.BaseAssumptions) :
    S.ATE ∈ Set.Icc S.bpLower S.bpUpper :=
  S.BPIdentifiedInterval_subset_Icc hA (S.ATE_mem_BPIdentifiedInterval hA)

/-! ### Sharpness

The containment above is an equality: the eight expressions are the dual vertices
of the LP, so the maximum of `bpLowerTerm` is attained by some feasible table,
and likewise for `bpUpper`. Proving this requires exhibiting, for each vertex, a
feasible table attaining it, then combining with
`PartialID.identifiedInterval_eq_Icc` (which additionally needs order-connectedness
of the identified interval, available from convexity of the feasible set).
That attainment argument is not yet formalized. -/

end POBalkePearlSystem

end PO
end Causalean
