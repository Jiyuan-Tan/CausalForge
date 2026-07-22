/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Liu–Hudgens (2014): large-sample setup for the direct-effect contrast

This file packages a single two-stage Hudgens–Halloran experiment into a self-contained
bundle `LHExperiment`, so that a *sequence* of such experiments (groups → ∞) can be studied for
large-sample inference following Liu & Hudgens (2014).  Each bundle carries the population of
groups `ι`, the per-group size `gsize i`, the two-stage design (stage-1 strategy design `D₁` and
the within-group strategy designs `ψ`/`φ`), the partial-interference potential outcomes `Y`, the
control/treatment unit counts `m0`/`m1`, the number `C` of ψ-selected groups, and — crucially —
the *known* design propensities (within-group control/treatment propensities `m0 i / nᵢ`,
`m1 i / nᵢ`, the stage-1 first-order propensity `C/N`, and the stage-1 pair propensity
`C(C−1)/(N(N−1))`) as carried regularity hypotheses.  These are exactly the hypotheses of the
unbiasedness theorem `E_estDirect` and the variance theorem `Var_estDirect`, so the bundle exposes
two reusable bridges, `E_estD` (the estimator is unbiased for the population average
treatment-minus-control direct-effect contrast) and `var_estD` (its design variance equals the
closed-form two-stage variance `directVar`), simply by feeding the carried hypotheses to those
theorems.
-/

import Causalean.Experimentation.TwoStageInterference.BetweenGroupEffect

/-! # Liu-Hudgens asymptotic setup

`LHExperiment` packages one Hudgens-Halloran two-stage experiment for Liu-Hudgens large-sample
inference on the treatment-minus-control direct-effect contrast.

The structure carries the group population, group sizes, stage-1 strategy design, within-group
strategies `ψ` and `φ`, partial-interference potential outcomes, fixed treated/control counts,
the number `C` of `ψ`-selected groups, and the known design propensities needed by the finite-sample
unbiasedness and variance theorems. Its namespace defines the joint two-stage design `jointD`, the
Horvitz-Thompson direct-effect estimator `estD`, the estimand `DEbar`, and the closed-form variance
`directVar`.

The main theorems are the reusable bridges `E_estD` and `var_estD`: they specialize the
finite-sample Hudgens-Halloran unbiasedness and variance results to each packaged experiment, so
later consistency, CLT, and Wald arguments can reason through `LHExperiment` alone.
-/

open scoped BigOperators
open Finset

namespace Causalean
namespace Experimentation
namespace TwoStageInterference

open DesignBased

/-- A single Liu–Hudgens (2014) two-stage experiment, packaged so that a sequence of them can be
studied for large-sample inference.  Carries the two-stage design (`D₁`, `ψ`, `φ`), the
partial-interference potential outcomes `Y`, the control/treatment unit counts `m0`/`m1`, the
number `C` of ψ-selected groups, and the *known* design propensities (`hprop0`, `hprop1`,
`hstage1`, `hstage1pair`) together with the nondegeneracy side conditions — exactly the hypothesis
lists of `E_estDirect` and `Var_estDirect`. -/
structure LHExperiment where
  /-- Finite population of groups. -/
  ι : Type
  [fι : Fintype ι]
  [dι : DecidableEq ι]
  /-- Size of each group. -/
  gsize : ι → ℕ
  /-- Stage-1 strategy-assignment design (which groups receive ψ vs. φ). -/
  D₁ : FiniteDesign (StratAssign ι)
  /-- Per-group treatment-allocation strategy ψ (the strategy of interest). -/
  ψ : ∀ i, FiniteDesign (Fin (gsize i) → Bool)
  /-- Per-group treatment-allocation strategy φ (the comparison strategy). -/
  φ : ∀ i, FiniteDesign (Fin (gsize i) → Bool)
  /-- Partial-interference potential outcomes: `Y i j w` is unit `(i,j)`'s outcome under the
  within-group assignment `w` of group `i`. -/
  Y : ∀ i, Fin (gsize i) → (Fin (gsize i) → Bool) → ℝ
  /-- Design-fixed number of control units per group. -/
  m0 : ι → ℝ
  /-- Design-fixed number of treated units per group. -/
  m1 : ι → ℝ
  /-- Number of groups selected for strategy ψ at stage 1. -/
  C : ℝ
  -- Carried regularity (exactly the `E_estDirect` / `Var_estDirect` hypotheses):
  /-- The ψ-selection count is nonzero. -/
  hC : C ≠ 0
  /-- Each group has a nonzero control count. -/
  hm0 : ∀ i, m0 i ≠ 0
  /-- Each group has a nonzero treated count. -/
  hm1 : ∀ i, m1 i ≠ 0
  /-- Each group is nonempty. -/
  hn  : ∀ i, (gsize i : ℝ) ≠ 0
  /-- There is at least one group. -/
  hN  : (Fintype.card ι : ℝ) ≠ 0
  /-- There are at least two groups (needed for the pair propensity). -/
  hN1 : (Fintype.card ι : ℝ) - 1 ≠ 0
  /-- Within-group control propensity of every unit is `m0 i / nᵢ`. -/
  hprop0 : ∀ i, ∀ j : Fin (gsize i), (ψ i).Pr (fun w => w j = false) = m0 i / (gsize i)
  /-- Within-group treatment propensity of every unit is `m1 i / nᵢ`. -/
  hprop1 : ∀ i, ∀ j : Fin (gsize i), (ψ i).Pr (fun w => w j = true) = m1 i / (gsize i)
  /-- Stage-1 first-order selection propensity of every group is `C/N`. -/
  hstage1 : ∀ i, D₁.Pr (fun s => s i = true) = C / (Fintype.card ι : ℝ)
  /-- Stage-1 second-order (pair) selection propensity is `C(C−1)/(N(N−1))`. -/
  hstage1pair : ∀ i j, i ≠ j →
    D₁.E (fun s => FiniteDesign.ind (fun s => s i = true) s
        * FiniteDesign.ind (fun s => s j = true) s)
      = (C * (C - 1)) / ((Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) - 1))

attribute [instance] LHExperiment.fι LHExperiment.dι

namespace LHExperiment

variable (E : LHExperiment)

/-- The joint two-stage design of the experiment. -/
noncomputable def jointD : FiniteDesign (StratAssign E.ι × ∀ i, Fin (E.gsize i) → Bool) :=
  jointDesign E.D₁ E.ψ E.φ

/-- The Horvitz-Thompson estimator of the experiment's treatment-minus-control direct-effect
contrast. -/
noncomputable def estD : (StratAssign E.ι × ∀ i, Fin (E.gsize i) → Bool) → ℝ :=
  estDirect E.Y E.m0 E.m1 E.C

/-- The population average treatment-minus-control direct-effect contrast: the treatment mean under
ψ minus the control mean under ψ. -/
noncomputable def DEbar : ℝ := CE_direct E.ψ E.Y

/-- The closed-form two-stage design variance of the treatment-minus-control direct-effect contrast
estimator (Theorem 6): a between-group SRS term over the group-level contrasts plus a within-group
term averaging the per-group contrast-estimator variances. -/
noncomputable def directVar : ℝ :=
  (1 - E.C / (Fintype.card E.ι : ℝ)) / E.C
      * SmuVar (fun i => groupMean E.ψ E.Y i true - groupMean E.ψ E.Y i false)
    + (1 / (E.C * (Fintype.card E.ι : ℝ)))
      * ∑ i, (E.ψ i).Var
          (fun w => groupEst E.Y i true (E.m1 i) w - groupEst E.Y i false (E.m0 i) w)

/-- **Unbiasedness bridge.** The estimator is unbiased for the population average
treatment-minus-control direct-effect contrast.  Immediate from `E_estDirect` and the carried
propensity hypotheses. -/
theorem E_estD : E.jointD.E E.estD = E.DEbar :=
  E_estDirect E.D₁ E.ψ E.φ E.Y E.m0 E.m1 E.C
    E.hC E.hm0 E.hm1 E.hn E.hprop0 E.hprop1 E.hstage1

/-- **Variance bridge.** The design variance of the treatment-minus-control direct-effect contrast
estimator equals the closed-form two-stage variance `directVar`.  Immediate from `Var_estDirect`
and the carried hypotheses. -/
theorem var_estD : E.jointD.Var E.estD = E.directVar :=
  Var_estDirect E.D₁ E.ψ E.φ E.Y E.m0 E.m1 E.C
    E.hC E.hN E.hN1 E.hm0 E.hm1 E.hn E.hprop0 E.hprop1 E.hstage1 E.hstage1pair

end LHExperiment

end TwoStageInterference
end Experimentation
end Causalean
