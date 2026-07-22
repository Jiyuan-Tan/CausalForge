/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Bipartite minimax design: unbounded dispersion certificate

The first-order intervention-degree and surrogate-weight dispersion summaries do
not uniformly control the observable approximation ratio.  This file records the
resolved negative answer as a theorem scaffold.
-/

import CausalSmith.Experimentation.EXP_BipartiteMinimaxDesign_Research.Helpers.DispersionAsymptotics

set_option linter.style.longLine false

open scoped BigOperators
open Finset Filter

namespace CausalSmith.Experimentation.BipartiteMinimaxDesign

-- @node: thm:dispersion-certificate-unbounded
/-- For every admissible positivity floor, positive degree-dispersion constant,
and nonvacuous weight-ratio constant, there is a sequence of finite bipartite
experiments satisfying the positive-energy and first-order dispersion guards
whose observable surrogate approximation ratio tends to infinity. -/
theorem dispersionCertificateUnbounded :
    ∀ (ε : ℝ) -- @realizes epsilon(carrier ℝ; range (0,1/2) pinned by EpsilonAdmissible below)
      (cdisp : ℝ) -- @realizes c_disp(carrier ℝ; positive range pinned below)
      (Cdisp : ℝ), -- @realizes C_disp(carrier ℝ; declared positive range pinned below)
      EpsilonAdmissible ε → -- @realizes epsilon(domain ε ∈ (0,1/2))
      0 < cdisp → -- @realizes c_disp(domain c_disp ∈ (0,∞))
      1 ≤ Cdisp → -- @realizes C_disp(nonvacuous theorem regime C_disp ∈ [1,∞), which pins the declared positive domain)
      ∃ (I O : ℕ → Type)
        (_ : ∀ n, Fintype (I n))
        (_ : ∀ n, Fintype (O n))
        (_ : ∀ n, DecidableEq (I n))
        (E : ∀ n, BipartiteExperiment (I n) (O n))
        (B : ℕ → ℝ),
        (∀ n, BudgetAdmissible (I := I n) ε (B n)) ∧
        (∀ n, 0 < ∑ k, ((E n).sdeg k : ℝ) ^ 2) ∧
        (∀ᶠ n in atTop, ∀ k,
          ((E n).sdeg k : ℝ) ^ 2 ≤
            cdisp * ∑ l, ((E n).sdeg l : ℝ) ^ 2) ∧
        (∀ᶠ n in atTop, ∀ k l,
          0 < (E n).hWeight l → (E n).hWeight k ≤ Cdisp * (E n).hWeight l) ∧
        Tendsto (fun n ↦ approxRatio (E n) ε (B n)) atTop atTop := by
  intro ε cdisp Cdisp hε hcdisp hCdisp
  refine ⟨DispersionIntervention, DispersionOutcome, fun n ↦ inferInstance,
    fun n ↦ inferInstance, fun n ↦ inferInstance, dispersionExperiment,
    fun n ↦ dispersionBudget n ε, fun n ↦ dispersionBudget_admissible n hε,
    fun n ↦ dispersionExperiment_degree_energy_pos n, ?_, ?_,
    dispersionApproxRatio_tendsto_atTop hε⟩
  · have hdR : Tendsto (fun n ↦ (dispersionD n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp dispersionD_tendsto_atTop
    have hcd : ∀ᶠ n in atTop, 1 ≤ cdisp * (dispersionD n : ℝ) :=
      (hdR.const_mul_atTop hcdisp).eventually_ge_atTop 1
    filter_upwards [hcd] with n hn
    intro k
    have henergy := dispersionExperiment_degree_energy n
    have hd1 : (1 : ℝ) ≤ dispersionD n := by
      exact_mod_cast dispersionD_pos n
    have ht : (dispersionT n : ℝ) ^ 2 = dispersionD n := by
      simp [dispersionD]
    push_cast at henergy
    cases k with
    | inl k =>
      rw [dispersionExperiment_sdeg_core]
      rw [henergy]
      nlinarith [sq_nonneg (dispersionT n : ℝ)]
    | inr k =>
      rw [dispersionExperiment_sdeg_filler]
      rw [ht, henergy]
      nlinarith [sq_nonneg (dispersionD n : ℝ)]
  · filter_upwards [] with n
    intro k l hl
    rw [dispersionExperiment_hWeight_eq n k l]
    have hk := dispersionExperiment_hWeight_pos n l
    nlinarith

end CausalSmith.Experimentation.BipartiteMinimaxDesign
