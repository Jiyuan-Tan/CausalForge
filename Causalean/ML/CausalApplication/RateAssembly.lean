/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.ML.Core.Rate

/-! # Assembly: per-method rates ⇒ DML nuisance-rate conditions

The mechanism that consumes per-method L²-estimation rates (proven in the method
folders, expressed via `ML/Core/Rate`) and discharges the three nuisance-rate
hypotheses of `Estimation.ATE.dml_ATE_tendstoNormal`.

It is method-agnostic: ridge, OLS, logistic — once each proves an `o_p(n^{-1/4})`
L²-rate toward its population target (which the Step-1/2 bridge identifies with the
causal nuisance) — plug their error sequences in as `μErr` / `eErr`.  Instantiating
`μErr a n ω := (eLpNorm (fun x => μ̂ n ω a x − μ_val a x) 2 P_X).toReal` (and `eErr`
analogously) makes the three outputs *literally* DML's `h_mu_rate` / `h_e_rate` /
`h_product_rate`.
-/

namespace Causalean.ML.Causal

open MeasureTheory Causalean.Stat Causalean.ML

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The `n^{-1/4}` rate is bounded by `1` (so it weakens to the `o_p(1)` rate). -/
theorem rpow_quarter_le_one (n : ℕ) : (n : ℝ) ^ (-(1 / 4 : ℝ)) ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp [Real.rpow_def_of_pos]
  · have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    exact Real.rpow_le_one_of_one_le_of_nonpos h1 (by norm_num)

/-- **Assembly.** Per-nuisance `o_p(n^{-1/4})` L²-rates discharge DML's three
nuisance-rate conditions: each is `o_p(1)`, and each outcome×propensity product is
`o_p(n^{-1/2})`. -/
theorem dml_rate_conditions_of_quarter_rates
    {μErr : Bool → ℕ → Ω → ℝ} {eErr : ℕ → Ω → ℝ}
    (hμ : ∀ a, IsLittleOp (μErr a) (fun n => (n : ℝ) ^ (-(1 / 4 : ℝ))) μ)
    (he : IsLittleOp eErr (fun n => (n : ℝ) ^ (-(1 / 4 : ℝ))) μ) :
    (∀ a, IsLittleOp (μErr a) (fun _ => 1) μ) ∧
      IsLittleOp eErr (fun _ => 1) μ ∧
      (∀ a, IsLittleOp (fun n ω => μErr a n ω * eErr n ω)
        (fun n => (n : ℝ) ^ (-(1 / 2 : ℝ))) μ) :=
  ⟨fun a => isLittleOp_one_of_le_one rpow_quarter_le_one (hμ a),
   isLittleOp_one_of_le_one rpow_quarter_le_one he,
   fun a => isLittleOp_mul_quarter (hμ a) he⟩

end Causalean.ML.Causal
