/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Sävje–Aronow–Hudgens (2021): consistency of Horvitz–Thompson for EATE under unknown interference

The flagship: along a sequence of Bernoulli experiments, the Horvitz–Thompson estimator is
**consistent** for the expected average treatment effect under *restricted interference*
(`d̄ = o(n)`), with no structural knowledge of the interference.  This is the conceptual heart of
the paper — standard estimators remain close to an average treatment effect even when units
interfere in unknown ways, as long as the average amount of interference grows slowly enough.

The argument is Chebyshev on the variance bound `Var(ĤT) ≤ k⁴·d̄/n` (`var_htEst_le`): since HT is
exactly unbiased for EATE (`htEst_unbiased`), `Pr(|ĤT − EATE| ≥ ε) ≤ (k⁴·d̄/n)/ε² → 0` whenever
`k⁴·d̄/n → 0`.  The same bound gives **root-n consistency** when `d̄` is bounded (`n·Var ≤ k⁴·C`).

The `SAHExperiment` bundle packages one Bernoulli experiment with its regularity constant `k`, so a
sequence `ℕ → SAHExperiment` is the paper's growing-sample regime.
-/

import Causalean.Experimentation.UnknownInterference.Unbiased
import Causalean.Experimentation.UnknownInterference.VarianceBound
import Causalean.Experimentation.DesignBased.Chebyshev
import Mathlib.Topology.Order.Bornology
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-! # Consistency under unknown interference

Horvitz-Thompson estimates the expected average treatment effect consistently when average
interference is sparse.

This file packages one Sävje-Aronow-Hudgens Bernoulli experiment as `SAHExperiment`, including
the finite unit type, treatment probabilities, potential outcomes, overlap bounds, moment bound,
and regularity constant.  The namespace-level bundle lemmas `D_E_htEst`, `D_Var_htEst_le`, and
`chebyshev_eate` restate exact unbiasedness, the finite-sample variance bound, and the resulting
Chebyshev tail inequality for the packaged experiment.  The main sequence theorem
`htEst_consistent_eate` proves convergence in probability when `k^4 * dbar / n -> 0`, and
`root_n_var` records the root-n variance scaling under bounded average interference.
-/

open scoped BigOperators Topology
open Filter

namespace Causalean
namespace Experimentation
namespace UnknownInterference

open DesignBased

/-- A single Sävje–Aronow–Hudgens Bernoulli experiment, packaged so that a sequence of them models
the growing-sample regime.  Carries the units `U`, treatment probabilities `p`, potential outcomes
`y`, and the regularity constant `k` together with the moment/overlap hypotheses of the variance
bound. -/
structure SAHExperiment where
  /-- Finite population of units. -/
  U : Type
  [fU : Fintype U]
  [dU : DecidableEq U]
  /-- Marginal treatment probabilities. -/
  p : U → ℝ
  /-- Potential outcomes `y i z` (unit `i`'s outcome under the full assignment `z`). -/
  y : U → (U → Bool) → ℝ
  /-- Regularity constant. -/
  k : ℝ
  /-- `1 ≤ k`. -/
  hk : 1 ≤ k
  /-- At least one unit. -/
  hcard : 1 ≤ Fintype.card U
  /-- Probabilities are in `[0,1]`. -/
  hp0 : ∀ i, 0 ≤ p i
  /-- Probabilities are in `[0,1]`. -/
  hp1 : ∀ i, p i ≤ 1
  /-- Lower overlap: `k⁻¹ ≤ p i`. -/
  hplo : ∀ i, k⁻¹ ≤ p i
  /-- Upper overlap: `p i ≤ 1 − k⁻¹`. -/
  hphi : ∀ i, p i ≤ 1 - k⁻¹
  /-- Second-moment bound: `E[Y_i²] ≤ k²`. -/
  hmom : ∀ i, (bernoulliDesign p hp0 hp1).E (fun z => (y i z) ^ 2) ≤ k ^ 2

attribute [instance] SAHExperiment.fU SAHExperiment.dU

namespace SAHExperiment

variable (E : SAHExperiment)

/-- The Bernoulli design of the experiment. -/
noncomputable def D : FiniteDesign (E.U → Bool) := bernoulliDesign E.p E.hp0 E.hp1

/-- The EATE estimand of the experiment. -/
noncomputable def eate : ℝ := EATE E.D E.y

/-- The treatment probabilities are nonzero (from lower overlap). -/
lemma p_ne_zero (i : E.U) : E.p i ≠ 0 := by
  have hkpos : (0 : ℝ) < E.k := lt_of_lt_of_le zero_lt_one E.hk
  have : (0 : ℝ) < E.p i := lt_of_lt_of_le (by positivity) (E.hplo i)
  exact ne_of_gt this

/-- One minus the treatment probability is nonzero (from upper overlap). -/
lemma one_sub_p_ne_zero (i : E.U) : (1 : ℝ) - E.p i ≠ 0 := by
  have hkpos : (0 : ℝ) < E.k := lt_of_lt_of_le zero_lt_one E.hk
  have hkinv : (0 : ℝ) < E.k⁻¹ := by positivity
  have : (0 : ℝ) < 1 - E.p i := by
    have := E.hphi i
    linarith
  exact ne_of_gt this

/-- **Unbiasedness (bundle form).** `E[ĤT] = EATE`. -/
theorem D_E_htEst : E.D.E (htEst E.p E.y) = E.eate := by
  change E.D.E (htEst E.p E.y) = EATE E.D E.y
  unfold SAHExperiment.D
  rw [htEst_unbiased E.p E.hp0 E.hp1 E.p_ne_zero E.one_sub_p_ne_zero E.y]

/-- **Variance bound (bundle form).** `Var(ĤT) ≤ k⁴·d̄/n`. -/
theorem D_Var_htEst_le :
    E.D.Var (htEst E.p E.y) ≤ E.k ^ 4 * dbar E.y / (Fintype.card E.U : ℝ) := by
  unfold SAHExperiment.D
  exact var_htEst_le E.p E.hp0 E.hp1 E.y E.k E.hk E.hcard E.hplo E.hphi E.hmom

/-- **Chebyshev tail bound.** `Pr(|ĤT − EATE| ≥ ε) ≤ (k⁴·d̄/n)/ε²`. -/
theorem chebyshev_eate {ε : ℝ} (hε : 0 < ε) :
    E.D.Pr (fun z => ε ≤ |htEst E.p E.y z - E.eate|)
      ≤ (E.k ^ 4 * dbar E.y / (Fintype.card E.U : ℝ)) / ε ^ 2 := by
  have hcheb := FiniteDesign.chebyshev E.D (htEst E.p E.y) hε
  rw [E.D_E_htEst] at hcheb
  have hε2 : (0 : ℝ) < ε ^ 2 := pow_pos hε 2
  refine le_trans hcheb ?_
  exact div_le_div_of_nonneg_right E.D_Var_htEst_le hε2.le

end SAHExperiment

/-- **Consistency of Horvitz–Thompson for EATE under unknown interference (Sävje–Aronow–Hudgens
2021).** Along a sequence of Bernoulli experiments with `k⁴·d̄/n → 0` (restricted interference with
controlled regularity), the HT estimator converges in probability to EATE: for every `ε > 0` the
tail probabilities vanish. -/
theorem htEst_consistent_eate (Exp : ℕ → SAHExperiment)
    (hrate : Tendsto (fun m => (Exp m).k ^ 4 * dbar (Exp m).y / (Fintype.card (Exp m).U : ℝ))
      atTop (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun m => (Exp m).D.Pr (fun z => ε ≤ |htEst (Exp m).p (Exp m).y z - (Exp m).eate|))
      atTop (𝓝 0) := by
  have hupper : Tendsto
      (fun m => (Exp m).k ^ 4 * dbar (Exp m).y / (Fintype.card (Exp m).U : ℝ) / ε ^ 2)
      atTop (𝓝 0) := by
    have := hrate.div_const (ε ^ 2)
    simpa using this
  refine squeeze_zero (fun m => ?_) (fun m => ?_) hupper
  · exact (Exp m).D.Pr_nonneg _
  · exact (Exp m).chebyshev_eate hε

/-- **Root-n variance scaling under bounded interference (Sävje–Aronow–Hudgens 2021).** If
`d̄ ≤ C` in one bundled experiment, then `n·Var(ĤT) ≤ k⁴·C`, the finite-sample variance inequality
that supports a root-n rate in bounded-interference sequences. -/
theorem root_n_var (E : SAHExperiment) (C : ℝ) (hC : dbar E.y ≤ C) :
    (Fintype.card E.U : ℝ) * E.D.Var (htEst E.p E.y) ≤ E.k ^ 4 * C := by
  have hn : (0 : ℝ) < (Fintype.card E.U : ℝ) := by
    have : (1 : ℝ) ≤ (Fintype.card E.U : ℝ) := by exact_mod_cast E.hcard
    linarith
  have hk4 : (0 : ℝ) ≤ E.k ^ 4 := by positivity
  have hvar := E.D_Var_htEst_le
  have hstep : (Fintype.card E.U : ℝ) * E.D.Var (htEst E.p E.y)
      ≤ (Fintype.card E.U : ℝ) * (E.k ^ 4 * dbar E.y / (Fintype.card E.U : ℝ)) :=
    mul_le_mul_of_nonneg_left hvar (le_of_lt hn)
  refine le_trans hstep ?_
  rw [mul_div_assoc']
  rw [mul_comm (Fintype.card E.U : ℝ) (E.k ^ 4 * dbar E.y), mul_div_assoc,
    div_self (ne_of_gt hn), mul_one]
  exact mul_le_mul_of_nonneg_left hC hk4

end UnknownInterference
end Experimentation
end Causalean
