/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# TWFE residualization closed forms for structured indicators

For `c : Cells I T` and an indicator array `A : I × T → ℝ` of a structured
predicate, this file collects closed-form expressions for the TWFE residual
`c.tildeX c.H_twfe A` on the observed cells.

The lemmas here are reusable substrate for staggered-adoption and event-study
panel regressions, and are stated generically against `Cells` plus an explicit
cohort-period weights construction (`cohortPeriodCells`). The construction is
defined locally to keep the dependency graph clean: `IndicatorClosedForms` does
not import any Q-instance file.

## Contents

### Trivial absorption (residual = 0; member of `H_twfe`)

* `tildeX_const` — constants.
* `tildeX_unit_indicator` — unit-only indicators `ind(i = i₀)`.
* `tildeX_period_indicator` — period-only indicators `ind(t = t₀)`.

These are independent of the weights: any `Cells I T`.

### Substantive closed forms (residual ≠ 0; not in `H_twfe`)

* `tildeX_product_indicator_balanced` — product `1_{S_I}(i) · 1_{S_T}(t)`
  under balanced weights factorizes into the product of demeaned indicators.
* `cohortPeriodCells` — generic `Cells` instance with all cohort-period cells
  observed and weights `π(g) / S`.
* `tildeX_cell_indicator_cohortPeriod` — cell `ind(g = g₀ ∧ t = t₀)`.
* `tildeX_diagonal_indicator_cohortPeriod` — staggered diagonal
  `ind(g.val = t.val)`.
* `tildeX_triangular_indicator_cohortPeriod` — staggered triangular
  `ind(g.val < t.val)`.

The substantive proofs all use the same pattern: exhibit the finite
unit-plus-period projection candidate, verify the two row/column normal
equations, and conclude by `proj_apply_eq_of_mem_orthogonal`.
-/

import Causalean.Panel.Cells
import Causalean.Panel.InnerProduct
import Causalean.Panel.Subspace
import Causalean.Panel.FixedEffect
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.NNReal.Basic

/-! # Indicator Residual Closed Forms

This file proves closed-form two-way fixed-effect residuals for structured
indicator arrays, including unit-only, period-only, rectangular, cohort-period,
diagonal, and triangular indicators. It also provides the exported
row-and-column orthogonality criterion `H_twfe_orthogonal_iff`, the finite
cohort law `CohortLaw`, and the generic cohort-period weighted panel
construction `cohortPeriodCells`, so downstream files can reuse the algebra
without importing a specialized regression instance. -/

open scoped BigOperators

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedSectionVars false

namespace Causalean
namespace Panel
namespace Cells

variable {I T : Type*}
variable [Fintype I] [Fintype T] [DecidableEq I] [DecidableEq T]

private lemma sum_indicator_mem_real {α : Type*} [Fintype α] [DecidableEq α]
    (S : Finset α) :
    (∑ x : α, (if x ∈ S then (1 : ℝ) else 0)) = (S.card : ℝ) := by
  rw [show (∑ x : α, (if x ∈ S then (1 : ℝ) else 0)) =
      ∑ x ∈ (Finset.univ : Finset α) ∩ S, (1 : ℝ) by
    simpa using
      (Finset.sum_ite_mem (s := (Finset.univ : Finset α)) (t := S)
        (f := fun _ : α => (1 : ℝ)))]
  simp

private lemma sum_centered_indicator_mem_real {α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α] (S : Finset α) :
    (∑ x : α,
      ((if x ∈ S then (1 : ℝ) else 0) - (S.card : ℝ) / (Fintype.card α : ℝ))) =
        0 := by
  rw [Finset.sum_sub_distrib, sum_indicator_mem_real]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : (Fintype.card α : ℝ) ≠ 0 := by
    have : 0 < Fintype.card α := Fintype.card_pos
    exact_mod_cast this.ne'
  field_simp [hcard]
  ring

private lemma sum_centered_eq_indicator_real {α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α] (a₀ : α) :
    (∑ x : α,
      ((if x = a₀ then (1 : ℝ) else 0) - 1 / (Fintype.card α : ℝ))) = 0 := by
  rw [Finset.sum_sub_distrib]
  rw [show (∑ x : α, (if x = a₀ then (1 : ℝ) else 0)) = (1 : ℝ) by
    simpa using (Fintype.sum_ite_eq (i := a₀) (f := fun _ : α => (1 : ℝ))).symm]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : (Fintype.card α : ℝ) ≠ 0 := by
    have : 0 < Fintype.card α := Fintype.card_pos
    exact_mod_cast this.ne'
  field_simp [hcard]
  ring

/-! ### `H_twfe`-orthogonality test against unit/period basis

To certify that an array `g : V I T` is `c.ip`-orthogonal to every member of
`H_twfe`, it suffices to test orthogonality against the spanning families
`e_{i₀}(i, t) := ind(i = i₀)` and `f_{t₀}(i, t) := ind(t = t₀)`.  This
helper is used throughout the indicator closed-form proofs and exported for
downstream residual arguments that need the same row/column reduction. -/

/-- An array is orthogonal to the full two-way fixed-effect subspace exactly
when it is orthogonal to every unit indicator and every period indicator. This
reduces `H_twfe` residual proofs to row and column normal equations. -/
lemma H_twfe_orthogonal_iff (c : Cells I T) (g : V I T) :
    (∀ h ∈ c.H_twfe, c.ip g h = 0) ↔
      ((∀ i₀ : I,
          c.ip g (fun r => if r.1 = i₀ then (1 : ℝ) else 0) = 0) ∧
       (∀ t₀ : T,
          c.ip g (fun r => if r.2 = t₀ then (1 : ℝ) else 0) = 0)) := by
  classical
  constructor
  · intro horth
    constructor
    · intro i₀
      exact horth (fun r => if r.1 = i₀ then (1 : ℝ) else 0)
        ⟨fun i => if i = i₀ then (1 : ℝ) else 0, fun _ => 0,
          by intro p; simp⟩
    · intro t₀
      exact horth (fun r => if r.2 = t₀ then (1 : ℝ) else 0)
        ⟨fun _ => 0, fun t => if t = t₀ then (1 : ℝ) else 0,
          by intro p; simp⟩
  · rintro ⟨hunit, hperiod⟩ h ⟨a, b, hh⟩
    have hA :
        c.ip g (fun r : I × T => a r.1) = 0 := by
      have hexp :
          c.ip g (fun r : I × T => a r.1) =
            ∑ i₀ : I, a i₀ *
              c.ip g (fun r : I × T => if r.1 = i₀ then (1 : ℝ) else 0) := by
        unfold ip
        rw [show
            (∑ i₀ : I, a i₀ *
                ∑ x ∈ c.observed,
                  c.weight x * g x * (if x.1 = i₀ then (1 : ℝ) else 0)) =
              ∑ x ∈ c.observed, c.weight x * g x * a x.1 by
          rw [show
              (∑ i₀ : I, a i₀ *
                  ∑ x ∈ c.observed,
                    c.weight x * g x * (if x.1 = i₀ then (1 : ℝ) else 0)) =
                ∑ i₀ : I, ∑ x ∈ c.observed,
                  a i₀ * (c.weight x * g x * (if x.1 = i₀ then (1 : ℝ) else 0)) by
            refine Finset.sum_congr rfl ?_
            intro i₀ _
            rw [Finset.mul_sum]]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl ?_
          intro x hx
          rw [show
              (∑ i₀ : I,
                a i₀ * (c.weight x * g x * (if x.1 = i₀ then (1 : ℝ) else 0))) =
                c.weight x * g x * a x.1 by
            rw [show
                (∑ i₀ : I,
                  a i₀ * (c.weight x * g x * (if x.1 = i₀ then (1 : ℝ) else 0))) =
                  (c.weight x * g x) *
                    ∑ i₀ : I, a i₀ * (if x.1 = i₀ then (1 : ℝ) else 0) by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro i₀ _
              ring]
            rw [show (∑ i₀ : I, a i₀ * (if x.1 = i₀ then (1 : ℝ) else 0)) =
                a x.1 by
              rw [Finset.sum_eq_single x.1]
              · simp
              · intro y _ hy
                simp [hy.symm]
              · intro hnot
                exact (hnot (Finset.mem_univ x.1)).elim]
            ]]
      rw [hexp]
      exact Finset.sum_eq_zero (fun i₀ _ => by rw [hunit i₀, mul_zero])
    have hB :
        c.ip g (fun r : I × T => b r.2) = 0 := by
      have hexp :
          c.ip g (fun r : I × T => b r.2) =
            ∑ t₀ : T, b t₀ *
              c.ip g (fun r : I × T => if r.2 = t₀ then (1 : ℝ) else 0) := by
        unfold ip
        rw [show
            (∑ t₀ : T, b t₀ *
                ∑ x ∈ c.observed,
                  c.weight x * g x * (if x.2 = t₀ then (1 : ℝ) else 0)) =
              ∑ x ∈ c.observed, c.weight x * g x * b x.2 by
          rw [show
              (∑ t₀ : T, b t₀ *
                  ∑ x ∈ c.observed,
                    c.weight x * g x * (if x.2 = t₀ then (1 : ℝ) else 0)) =
                ∑ t₀ : T, ∑ x ∈ c.observed,
                  b t₀ * (c.weight x * g x * (if x.2 = t₀ then (1 : ℝ) else 0)) by
            refine Finset.sum_congr rfl ?_
            intro t₀ _
            rw [Finset.mul_sum]]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl ?_
          intro x hx
          rw [show
              (∑ t₀ : T,
                b t₀ * (c.weight x * g x * (if x.2 = t₀ then (1 : ℝ) else 0))) =
                c.weight x * g x * b x.2 by
            rw [show
                (∑ t₀ : T,
                  b t₀ * (c.weight x * g x * (if x.2 = t₀ then (1 : ℝ) else 0))) =
                  (c.weight x * g x) *
                    ∑ t₀ : T, b t₀ * (if x.2 = t₀ then (1 : ℝ) else 0) by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro t₀ _
              ring]
            rw [show (∑ t₀ : T, b t₀ * (if x.2 = t₀ then (1 : ℝ) else 0)) =
                b x.2 by
              rw [Finset.sum_eq_single x.2]
              · simp
              · intro y _ hy
                simp [hy.symm]
              · intro hnot
                exact (hnot (Finset.mem_univ x.2)).elim]
            ]]
      rw [hexp]
      exact Finset.sum_eq_zero (fun t₀ _ => by rw [hperiod t₀, mul_zero])
    calc
      c.ip g h = c.ip g ((fun r : I × T => a r.1) + fun r : I × T => b r.2) := by
        congr 1
        ext p
        exact hh p
      _ = c.ip g (fun r : I × T => a r.1) +
          c.ip g (fun r : I × T => b r.2) := by
        rw [c.ip_add_right]
      _ = 0 := by rw [hA, hB]; ring

/-! ### Constants are absorbed by `H_twfe` -/

/-- The TWFE residual of a constant array vanishes on every observed cell. -/
theorem tildeX_const (c : Cells I T) (k : ℝ) (r : I × T) (hr : r ∈ c.observed) :
    c.tildeX c.H_twfe (fun _ : I × T => k) r = 0 := by
  -- PROOF: constants belong to `H_twfe` (`const_mem_H_twfe`), so by
  -- `residualize_self_of_mem` the residual vanishes on observed cells.
  exact c.residualize_self_of_mem c.H_twfe (c.const_mem_H_twfe k) r hr

/-! ### Unit-only and period-only indicators are absorbed by `H_twfe` -/

/-- Unit indicator is absorbed by `H_twfe`: `ind(i = i₀)` lies in `H_twfe`
(via `a(i) := ind(i = i₀)`, `b(t) := 0`), so its residual vanishes on every
observed cell.  Independent of the weights. -/
theorem tildeX_unit_indicator (c : Cells I T) (i₀ : I)
    (r : I × T) (hr : r ∈ c.observed) :
    c.tildeX c.H_twfe
        (fun s : I × T => if s.1 = i₀ then (1 : ℝ) else 0) r = 0 := by
  apply c.residualize_self_of_mem c.H_twfe ?_ r hr
  exact ⟨fun i => (if i = i₀ then 1 else 0 : ℝ), fun _ => 0,
    by intro p; simp⟩

/-- Period indicator is absorbed by `H_twfe`: `ind(t = t₀)` lies in `H_twfe`
(via `a := 0`, `b(t) := ind(t = t₀)`), so its residual vanishes on every
observed cell.  Independent of the weights. -/
theorem tildeX_period_indicator (c : Cells I T) (t₀ : T)
    (r : I × T) (hr : r ∈ c.observed) :
    c.tildeX c.H_twfe
        (fun s : I × T => if s.2 = t₀ then (1 : ℝ) else 0) r = 0 := by
  apply c.residualize_self_of_mem c.H_twfe ?_ r hr
  exact ⟨fun _ => 0, fun t => (if t = t₀ then 1 else 0 : ℝ),
    by intro p; simp⟩

/-! ### Product indicator under balanced weights -/

section Balanced

variable [Nonempty I] [Nonempty T]

private lemma balanced_centered_product_orth_unit (S_I : Finset I) (S_T : Finset T)
    (i₀ : I) :
    (balanced (I := I) (T := T)).ip
      (fun s : I × T =>
        ((if s.1 ∈ S_I then (1 : ℝ) else 0) -
            (S_I.card : ℝ) / (Fintype.card I : ℝ)) *
          ((if s.2 ∈ S_T then (1 : ℝ) else 0) -
            (S_T.card : ℝ) / (Fintype.card T : ℝ)))
      (fun r => if r.1 = i₀ then (1 : ℝ) else 0) = 0 := by
  unfold ip
  rw [balanced_observed]
  simp only [balanced_weight, ite_mul, one_mul, zero_mul, mul_ite, mul_one,
    mul_zero, ↓reduceIte]
  rw [Fintype.sum_prod_type]
  simp only
  rw [show (∑ x : I, ∑ x_1 : T,
        if x = i₀ then
          1 / ((Fintype.card I : ℝ) * (Fintype.card T : ℝ)) *
            (((if x ∈ S_I then 1 else 0) - (S_I.card : ℝ) / (Fintype.card I : ℝ)) *
              ((if x_1 ∈ S_T then 1 else 0) - (S_T.card : ℝ) / (Fintype.card T : ℝ)))
        else 0) =
      ∑ x_1 : T,
          1 / ((Fintype.card I : ℝ) * (Fintype.card T : ℝ)) *
            (((if i₀ ∈ S_I then 1 else 0) - (S_I.card : ℝ) / (Fintype.card I : ℝ)) *
              ((if x_1 ∈ S_T then 1 else 0) - (S_T.card : ℝ) / (Fintype.card T : ℝ))) by
    simpa [eq_comm] using (Fintype.sum_ite_eq (i := i₀)
      (f := fun x : I => ∑ x_1 : T,
            1 / ((Fintype.card I : ℝ) * (Fintype.card T : ℝ)) *
              (((if x ∈ S_I then 1 else 0) - (S_I.card : ℝ) / (Fintype.card I : ℝ)) *
                ((if x_1 ∈ S_T then 1 else 0) - (S_T.card : ℝ) / (Fintype.card T : ℝ)))))]
  rw [show (∑ x_1 : T,
          1 / ((Fintype.card I : ℝ) * (Fintype.card T : ℝ)) *
            (((if i₀ ∈ S_I then 1 else 0) - (S_I.card : ℝ) / (Fintype.card I : ℝ)) *
              ((if x_1 ∈ S_T then 1 else 0) - (S_T.card : ℝ) / (Fintype.card T : ℝ)))) =
      (1 / ((Fintype.card I : ℝ) * (Fintype.card T : ℝ)) *
        ((if i₀ ∈ S_I then 1 else 0) - (S_I.card : ℝ) / (Fintype.card I : ℝ))) *
        (∑ x_1 : T,
          ((if x_1 ∈ S_T then 1 else 0) - (S_T.card : ℝ) / (Fintype.card T : ℝ))) by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro x hx
    ring]
  rw [sum_centered_indicator_mem_real (S := S_T), mul_zero]

private lemma balanced_centered_product_orth_period (S_I : Finset I) (S_T : Finset T)
    (t₀ : T) :
    (balanced (I := I) (T := T)).ip
      (fun s : I × T =>
        ((if s.1 ∈ S_I then (1 : ℝ) else 0) -
            (S_I.card : ℝ) / (Fintype.card I : ℝ)) *
          ((if s.2 ∈ S_T then (1 : ℝ) else 0) -
            (S_T.card : ℝ) / (Fintype.card T : ℝ)))
      (fun r => if r.2 = t₀ then (1 : ℝ) else 0) = 0 := by
  unfold ip
  rw [balanced_observed]
  simp only [balanced_weight, ite_mul, one_mul, zero_mul, mul_ite, mul_one,
    mul_zero, ↓reduceIte]
  rw [Fintype.sum_prod_type]
  simp only
  rw [show (∑ x : I, ∑ x_1 : T,
        if x_1 = t₀ then
          1 / ((Fintype.card I : ℝ) * (Fintype.card T : ℝ)) *
            (((if x ∈ S_I then 1 else 0) - (S_I.card : ℝ) / (Fintype.card I : ℝ)) *
              ((if x_1 ∈ S_T then 1 else 0) - (S_T.card : ℝ) / (Fintype.card T : ℝ)))
        else 0) =
      ∑ x : I,
          1 / ((Fintype.card I : ℝ) * (Fintype.card T : ℝ)) *
            (((if x ∈ S_I then 1 else 0) - (S_I.card : ℝ) / (Fintype.card I : ℝ)) *
              ((if t₀ ∈ S_T then 1 else 0) - (S_T.card : ℝ) / (Fintype.card T : ℝ))) by
    refine Finset.sum_congr rfl ?_
    intro x hx
    simpa [eq_comm] using (Fintype.sum_ite_eq (i := t₀)
      (f := fun t : T =>
            1 / ((Fintype.card I : ℝ) * (Fintype.card T : ℝ)) *
              (((if x ∈ S_I then 1 else 0) - (S_I.card : ℝ) / (Fintype.card I : ℝ)) *
                ((if t ∈ S_T then 1 else 0) - (S_T.card : ℝ) / (Fintype.card T : ℝ)))))]
  rw [show (∑ x : I,
          1 / ((Fintype.card I : ℝ) * (Fintype.card T : ℝ)) *
            (((if x ∈ S_I then 1 else 0) - (S_I.card : ℝ) / (Fintype.card I : ℝ)) *
              ((if t₀ ∈ S_T then 1 else 0) - (S_T.card : ℝ) / (Fintype.card T : ℝ)))) =
      (1 / ((Fintype.card I : ℝ) * (Fintype.card T : ℝ)) *
        ((if t₀ ∈ S_T then 1 else 0) - (S_T.card : ℝ) / (Fintype.card T : ℝ))) *
        (∑ x : I,
          ((if x ∈ S_I then 1 else 0) - (S_I.card : ℝ) / (Fintype.card I : ℝ))) by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro x hx
    ring]
  rw [sum_centered_indicator_mem_real (S := S_I), mul_zero]

/-- Product indicator under balanced weights: the residual factorizes into a
product of centered indicators. -/
theorem tildeX_product_indicator_balanced (S_I : Finset I) (S_T : Finset T)
    (r : I × T) (hr : r ∈ (balanced (I := I) (T := T)).observed) :
    (balanced (I := I) (T := T)).tildeX
        ((balanced (I := I) (T := T)).H_twfe)
        (fun s : I × T =>
          (if s.1 ∈ S_I then (1 : ℝ) else 0) *
            (if s.2 ∈ S_T then (1 : ℝ) else 0)) r =
      ((if r.1 ∈ S_I then (1 : ℝ) else 0) -
          (S_I.card : ℝ) / (Fintype.card I : ℝ)) *
        ((if r.2 ∈ S_T then (1 : ℝ) else 0) -
          (S_T.card : ℝ) / (Fintype.card T : ℝ)) := by
  classical
  let c : Cells I T := balanced (I := I) (T := T)
  let X : V I T := fun s : I × T =>
    (if s.1 ∈ S_I then (1 : ℝ) else 0) *
      (if s.2 ∈ S_T then (1 : ℝ) else 0)
  let Y : V I T := fun s : I × T =>
    ((if s.1 ∈ S_I then (1 : ℝ) else 0) -
        (S_I.card : ℝ) / (Fintype.card I : ℝ)) *
      ((if s.2 ∈ S_T then (1 : ℝ) else 0) -
        (S_T.card : ℝ) / (Fintype.card T : ℝ))
  let G : V I T := X - Y
  have hG_mem : G ∈ c.H_twfe := by
    refine ⟨fun i =>
        ((S_T.card : ℝ) / (Fintype.card T : ℝ)) *
          (if i ∈ S_I then (1 : ℝ) else 0),
      fun t =>
        ((S_I.card : ℝ) / (Fintype.card I : ℝ)) *
          (if t ∈ S_T then (1 : ℝ) else 0) -
        ((S_I.card : ℝ) / (Fintype.card I : ℝ)) *
          ((S_T.card : ℝ) / (Fintype.card T : ℝ)), ?_⟩
    intro p
    by_cases hi : p.1 ∈ S_I <;> by_cases ht : p.2 ∈ S_T <;> simp [G, X, Y, hi, ht] <;>
      ring
  have hXsubG : X - G = Y := by
    ext s
    simp [G]
  have horth : ∀ h ∈ c.H_twfe, c.ip (X - G) h = 0 := by
    rw [H_twfe_orthogonal_iff]
    constructor
    · intro i₀
      rw [hXsubG]
      simpa [c, Y] using balanced_centered_product_orth_unit (S_I := S_I) (S_T := S_T) i₀
    · intro t₀
      rw [hXsubG]
      simpa [c, Y] using balanced_centered_product_orth_period (S_I := S_I) (S_T := S_T) t₀
  have hproj : c.proj c.H_twfe X r = G r :=
    c.proj_apply_eq_of_mem_orthogonal c.H_twfe X hG_mem horth r hr
  calc
    c.tildeX c.H_twfe X r = (X - c.proj c.H_twfe X) r := by simp [Cells.tildeX_eq]
    _ = Y r := by
      rw [Pi.sub_apply, hproj]
      exact congrFun hXsubG r
    _ = ((if r.1 ∈ S_I then (1 : ℝ) else 0) -
          (S_I.card : ℝ) / (Fintype.card I : ℝ)) *
        ((if r.2 ∈ S_T then (1 : ℝ) else 0) -
          (S_T.card : ℝ) / (Fintype.card T : ℝ)) := rfl

end Balanced

/-! ### Cohort-period cells (generic, weight `π(g) / S`)

This construction is kept generic and self-contained: every `(g, t)` cell is
observed, and the weight factors into the cohort mass `π(g)` times the uniform
period weight `1 / S`. -/

/-- Cohort law on a finite cohort index `Fin C`: probabilities `π(g) ≥ 0`
summing to one. -/
structure CohortLaw (C : ℕ) where
  /-- Cohort probabilities (nonnegative reals). -/
  pi : Fin C → NNReal
  /-- The probabilities sum to one. -/
  sumOne : (∑ g, (pi g : ℝ)) = 1

/-- Generic cohort-period `Cells` instance with positive cohort masses.
Every cell `(g, t) ∈ Fin C × Fin S` is observed and carries weight
`π(g) / S`. -/
noncomputable def cohortPeriodCells {C S : ℕ}
    [Nonempty (Fin C)] [Nonempty (Fin S)] (law : CohortLaw C)
    (hpi : ∀ g : Fin C, 0 < (law.pi g : ℝ)) :
    Cells (Fin C) (Fin S) where
  observed := Finset.univ
  observed_nonempty := Finset.univ_nonempty
  weight r := (law.pi r.1 : ℝ) / (Fintype.card (Fin S) : ℝ)
  weight_pos := by
    intro r _
    have hS : (0 : ℝ) < Fintype.card (Fin S) := by exact_mod_cast Fintype.card_pos
    exact div_pos (hpi r.1) hS
  weight_zero_off := by
    intro r hr
    exact (hr (Finset.mem_univ r)).elim
  weight_sum_one := by
    have hS : (Fintype.card (Fin S) : ℝ) ≠ 0 := by
      have : 0 < Fintype.card (Fin S) := Fintype.card_pos
      exact_mod_cast this.ne'
    rw [Fintype.sum_prod_type]
    calc
      ∑ x : Fin C, ∑ _y : Fin S, (law.pi x : ℝ) / (Fintype.card (Fin S) : ℝ)
          = ∑ x : Fin C, (law.pi x : ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro x _
            rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
            field_simp [hS]
      _ = 1 := law.sumOne

/-! ### Cohort-period indicator closed forms -/

section CohortPeriod

variable {C S : ℕ}
variable [Nonempty (Fin C)] [Nonempty (Fin S)]
variable (law : CohortLaw C) (hpi : ∀ g : Fin C, 0 < (law.pi g : ℝ))

private lemma cohort_sum_pi_centered_eq_zero (law : CohortLaw C) (g₀ : Fin C) :
    (∑ g : Fin C,
      (law.pi g : ℝ) * ((if g = g₀ then (1 : ℝ) else 0) - (law.pi g₀ : ℝ))) =
        0 := by
  rw [show (∑ g : Fin C,
      (law.pi g : ℝ) * ((if g = g₀ then (1 : ℝ) else 0) - (law.pi g₀ : ℝ))) =
      (∑ g : Fin C, (law.pi g : ℝ) * (if g = g₀ then (1 : ℝ) else 0)) -
        ∑ g : Fin C, (law.pi g : ℝ) * (law.pi g₀ : ℝ) by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro g hg
    ring]
  rw [show (∑ x : Fin C, (law.pi x : ℝ) * if x = g₀ then 1 else 0) =
      (law.pi g₀ : ℝ) by
    simpa [mul_comm] using
      (Fintype.sum_ite_eq (i := g₀) (f := fun g : Fin C => (law.pi g : ℝ))).symm]
  rw [show (∑ g : Fin C, (law.pi g : ℝ) * (law.pi g₀ : ℝ)) =
      (∑ g : Fin C, (law.pi g : ℝ)) * (law.pi g₀ : ℝ) by
    rw [Finset.sum_mul]]
  rw [law.sumOne]
  ring

private lemma cohort_cell_centered_orth_unit (law : CohortLaw C)
    (hpi : ∀ g : Fin C, 0 < (law.pi g : ℝ)) (g₀ g₁ : Fin C) (t₀ : Fin S) :
    (cohortPeriodCells law hpi).ip
      (fun s : Fin C × Fin S =>
        ((if s.1 = g₀ then (1 : ℝ) else 0) - (law.pi g₀ : ℝ)) *
          ((if s.2 = t₀ then (1 : ℝ) else 0) -
            1 / (Fintype.card (Fin S) : ℝ)))
      (fun r => if r.1 = g₁ then (1 : ℝ) else 0) = 0 := by
  unfold ip
  simp only [cohortPeriodCells, Finset.mem_univ, ite_mul, one_mul, zero_mul,
    mul_ite, mul_one, mul_zero, ↓reduceIte]
  rw [Fintype.sum_prod_type]
  simp only
  rw [show (∑ x : Fin C, ∑ x_1 : Fin S,
        if x = g₁ then
          (law.pi x : ℝ) / (Fintype.card (Fin S) : ℝ) *
            (((if x = g₀ then 1 else 0) - (law.pi g₀ : ℝ)) *
              ((if x_1 = t₀ then 1 else 0) - 1 / (Fintype.card (Fin S) : ℝ)))
        else 0) =
      ∑ x_1 : Fin S,
          (law.pi g₁ : ℝ) / (Fintype.card (Fin S) : ℝ) *
            (((if g₁ = g₀ then 1 else 0) - (law.pi g₀ : ℝ)) *
              ((if x_1 = t₀ then 1 else 0) - 1 / (Fintype.card (Fin S) : ℝ))) by
    simpa [eq_comm] using (Fintype.sum_ite_eq (i := g₁)
      (f := fun x : Fin C => ∑ x_1 : Fin S,
          (law.pi x : ℝ) / (Fintype.card (Fin S) : ℝ) *
            (((if x = g₀ then 1 else 0) - (law.pi g₀ : ℝ)) *
              ((if x_1 = t₀ then 1 else 0) - 1 / (Fintype.card (Fin S) : ℝ)))))]
  rw [show (∑ x_1 : Fin S,
          (law.pi g₁ : ℝ) / (Fintype.card (Fin S) : ℝ) *
            (((if g₁ = g₀ then 1 else 0) - (law.pi g₀ : ℝ)) *
              ((if x_1 = t₀ then 1 else 0) - 1 / (Fintype.card (Fin S) : ℝ)))) =
      ((law.pi g₁ : ℝ) / (Fintype.card (Fin S) : ℝ) *
        ((if g₁ = g₀ then 1 else 0) - (law.pi g₀ : ℝ))) *
        (∑ x_1 : Fin S,
          ((if x_1 = t₀ then 1 else 0) - 1 / (Fintype.card (Fin S) : ℝ))) by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro x hx
    ring]
  rw [sum_centered_eq_indicator_real (a₀ := t₀), mul_zero]

private lemma cohort_cell_centered_orth_period (law : CohortLaw C)
    (hpi : ∀ g : Fin C, 0 < (law.pi g : ℝ)) (g₀ : Fin C) (t₀ t₁ : Fin S) :
    (cohortPeriodCells law hpi).ip
      (fun s : Fin C × Fin S =>
        ((if s.1 = g₀ then (1 : ℝ) else 0) - (law.pi g₀ : ℝ)) *
          ((if s.2 = t₀ then (1 : ℝ) else 0) -
            1 / (Fintype.card (Fin S) : ℝ)))
      (fun r => if r.2 = t₁ then (1 : ℝ) else 0) = 0 := by
  unfold ip
  simp only [cohortPeriodCells, Finset.mem_univ, ite_mul, one_mul, zero_mul,
    mul_ite, mul_one, mul_zero, ↓reduceIte]
  rw [Fintype.sum_prod_type]
  simp only
  rw [show (∑ x : Fin C, ∑ x_1 : Fin S,
        if x_1 = t₁ then
          (law.pi x : ℝ) / (Fintype.card (Fin S) : ℝ) *
            (((if x = g₀ then 1 else 0) - (law.pi g₀ : ℝ)) *
              ((if x_1 = t₀ then 1 else 0) - 1 / (Fintype.card (Fin S) : ℝ)))
        else 0) =
      ∑ x : Fin C,
          (law.pi x : ℝ) / (Fintype.card (Fin S) : ℝ) *
            (((if x = g₀ then 1 else 0) - (law.pi g₀ : ℝ)) *
              ((if t₁ = t₀ then 1 else 0) - 1 / (Fintype.card (Fin S) : ℝ))) by
    refine Finset.sum_congr rfl ?_
    intro x hx
    simpa [eq_comm] using (Fintype.sum_ite_eq (i := t₁)
      (f := fun t : Fin S =>
          (law.pi x : ℝ) / (Fintype.card (Fin S) : ℝ) *
            (((if x = g₀ then 1 else 0) - (law.pi g₀ : ℝ)) *
              ((if t = t₀ then 1 else 0) - 1 / (Fintype.card (Fin S) : ℝ)))))]
  rw [show (∑ x : Fin C,
          (law.pi x : ℝ) / (Fintype.card (Fin S) : ℝ) *
            (((if x = g₀ then 1 else 0) - (law.pi g₀ : ℝ)) *
              ((if t₁ = t₀ then 1 else 0) - 1 / (Fintype.card (Fin S) : ℝ)))) =
      (((if t₁ = t₀ then 1 else 0) - 1 / (Fintype.card (Fin S) : ℝ)) /
        (Fintype.card (Fin S) : ℝ)) *
        (∑ x : Fin C,
          (law.pi x : ℝ) * ((if x = g₀ then 1 else 0) - (law.pi g₀ : ℝ))) by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro x hx
    ring]
  rw [cohort_sum_pi_centered_eq_zero (law := law) (g₀ := g₀), mul_zero]

/-- Cell indicator under cohort-period weights: the residual factorizes
into the product of centered cohort and period indicators (with cross terms
following the gauge fix `∑_t β(t) = π(g₀)`). -/
theorem tildeX_cell_indicator_cohortPeriod (g₀ : Fin C) (t₀ : Fin S)
    (r : Fin C × Fin S) (hr : r ∈ (cohortPeriodCells law hpi).observed) :
    (cohortPeriodCells law hpi).tildeX
        ((cohortPeriodCells law hpi).H_twfe)
        (fun s : Fin C × Fin S =>
          if s.1 = g₀ ∧ s.2 = t₀ then (1 : ℝ) else 0) r =
      (if r.1 = g₀ then (1 : ℝ) else 0) *
          (if r.2 = t₀ then (1 : ℝ) else 0)
        - (law.pi g₀ : ℝ) * (if r.2 = t₀ then (1 : ℝ) else 0)
        - (1 / (Fintype.card (Fin S) : ℝ)) *
            (if r.1 = g₀ then (1 : ℝ) else 0)
        + (law.pi g₀ : ℝ) / (Fintype.card (Fin S) : ℝ) := by
  classical
  let c : Cells (Fin C) (Fin S) := cohortPeriodCells law hpi
  let X : V (Fin C) (Fin S) := fun s : Fin C × Fin S =>
    if s.1 = g₀ ∧ s.2 = t₀ then (1 : ℝ) else 0
  let Y : V (Fin C) (Fin S) := fun s : Fin C × Fin S =>
    ((if s.1 = g₀ then (1 : ℝ) else 0) - (law.pi g₀ : ℝ)) *
      ((if s.2 = t₀ then (1 : ℝ) else 0) -
        1 / (Fintype.card (Fin S) : ℝ))
  let G : V (Fin C) (Fin S) := X - Y
  have hG_mem : G ∈ c.H_twfe := by
    refine ⟨fun g => (1 / (Fintype.card (Fin S) : ℝ)) *
        (if g = g₀ then (1 : ℝ) else 0),
      fun t => (law.pi g₀ : ℝ) * (if t = t₀ then (1 : ℝ) else 0) -
        (law.pi g₀ : ℝ) / (Fintype.card (Fin S) : ℝ), ?_⟩
    intro p
    by_cases hg : p.1 = g₀ <;> by_cases ht : p.2 = t₀ <;>
      simp [G, X, Y, hg, ht] <;> ring
  have hXsubG : X - G = Y := by
    ext s
    simp [G]
  have horth : ∀ h ∈ c.H_twfe, c.ip (X - G) h = 0 := by
    rw [H_twfe_orthogonal_iff]
    constructor
    · intro g₁
      rw [hXsubG]
      simpa [c, Y] using
        cohort_cell_centered_orth_unit (law := law) (hpi := hpi) (g₀ := g₀)
          (g₁ := g₁) (t₀ := t₀)
    · intro t₁
      rw [hXsubG]
      simpa [c, Y] using
        cohort_cell_centered_orth_period (law := law) (hpi := hpi) (g₀ := g₀)
          (t₀ := t₀) (t₁ := t₁)
  have hproj : c.proj c.H_twfe X r = G r :=
    c.proj_apply_eq_of_mem_orthogonal c.H_twfe X hG_mem horth r hr
  calc
    c.tildeX c.H_twfe X r = (X - c.proj c.H_twfe X) r := by simp [Cells.tildeX_eq]
    _ = Y r := by
      rw [Pi.sub_apply, hproj]
      exact congrFun hXsubG r
    _ = (if r.1 = g₀ then (1 : ℝ) else 0) *
          (if r.2 = t₀ then (1 : ℝ) else 0)
        - (law.pi g₀ : ℝ) * (if r.2 = t₀ then (1 : ℝ) else 0)
        - (1 / (Fintype.card (Fin S) : ℝ)) *
            (if r.1 = g₀ then (1 : ℝ) else 0)
        + (law.pi g₀ : ℝ) / (Fintype.card (Fin S) : ℝ) := by
          by_cases hg : r.1 = g₀ <;> by_cases ht : r.2 = t₀ <;>
            simp [Y, hg, ht] <;> ring

/-! ### Staggered indicators: diagonal and triangular -/

private lemma cohortPeriod_ip_unit_eq (law : CohortLaw C)
    (hpi : ∀ g : Fin C, 0 < (law.pi g : ℝ))
    (Y : V (Fin C) (Fin S)) (g₁ : Fin C) :
    (cohortPeriodCells law hpi).ip Y
      (fun r : Fin C × Fin S => if r.1 = g₁ then (1 : ℝ) else 0) =
        ((law.pi g₁ : ℝ) / (Fintype.card (Fin S) : ℝ)) *
          ∑ t : Fin S, Y (g₁, t) := by
  unfold ip
  simp only [cohortPeriodCells, Finset.mem_univ, ite_mul, one_mul, zero_mul,
    mul_ite, mul_one, mul_zero, ↓reduceIte]
  rw [Fintype.sum_prod_type]
  rw [show (∑ x : Fin C, ∑ t : Fin S,
      if x = g₁ then (law.pi x : ℝ) / (Fintype.card (Fin S) : ℝ) * Y (x, t) else 0) =
      ∑ t : Fin S, (law.pi g₁ : ℝ) / (Fintype.card (Fin S) : ℝ) * Y (g₁, t) by
    simpa [eq_comm] using (Fintype.sum_ite_eq (i := g₁)
      (f := fun x : Fin C =>
        ∑ t : Fin S, (law.pi x : ℝ) / (Fintype.card (Fin S) : ℝ) * Y (x, t))).symm]
  rw [Finset.mul_sum]

private lemma cohortPeriod_ip_period_eq (law : CohortLaw C)
    (hpi : ∀ g : Fin C, 0 < (law.pi g : ℝ))
    (Y : V (Fin C) (Fin S)) (t₁ : Fin S) :
    (cohortPeriodCells law hpi).ip Y
      (fun r : Fin C × Fin S => if r.2 = t₁ then (1 : ℝ) else 0) =
        (1 / (Fintype.card (Fin S) : ℝ)) *
          ∑ g : Fin C, (law.pi g : ℝ) * Y (g, t₁) := by
  unfold ip
  simp only [cohortPeriodCells, Finset.mem_univ, ite_mul, one_mul, zero_mul,
    mul_ite, mul_one, mul_zero, ↓reduceIte]
  rw [Fintype.sum_prod_type]
  rw [show (∑ g : Fin C, ∑ t : Fin S,
      if t = t₁ then (law.pi g : ℝ) / (Fintype.card (Fin S) : ℝ) * Y (g, t) else 0) =
      ∑ g : Fin C, (law.pi g : ℝ) / (Fintype.card (Fin S) : ℝ) * Y (g, t₁) by
    refine Finset.sum_congr rfl ?_
    intro g _
    simpa [eq_comm] using (Fintype.sum_ite_eq (i := t₁)
      (f := fun t : Fin S => (law.pi g : ℝ) / (Fintype.card (Fin S) : ℝ) * Y (g, t))).symm]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro g _
  ring

private noncomputable def diagRowMean {C S : ℕ} (g : Fin C) : ℝ :=
  if g.val < S then 1 / (Fintype.card (Fin S) : ℝ) else 0

private noncomputable def diagPeriodMean {C S : ℕ}
    (law : CohortLaw C) (t : Fin S) : ℝ :=
  if h : t.val < C then (law.pi ⟨t.val, h⟩ : ℝ) else 0

private noncomputable def diagGrandMean {C S : ℕ}
    (law : CohortLaw C) : ℝ :=
  (1 / (Fintype.card (Fin S) : ℝ)) *
    ∑ g : Fin C, (if g.val < S then (law.pi g : ℝ) else 0)

private noncomputable def diagX {C S : ℕ} : V (Fin C) (Fin S) :=
  fun s => if s.1.val = s.2.val then (1 : ℝ) else 0

private noncomputable def diagY {C S : ℕ} (law : CohortLaw C) :
    V (Fin C) (Fin S) :=
  fun s =>
    diagX s - diagRowMean (S := S) s.1 - diagPeriodMean law s.2 +
      diagGrandMean (S := S) law

private lemma diagonal_row_hit_sum (g : Fin C) :
    (∑ t : Fin S, (if g.val = t.val then (1 : ℝ) else 0)) =
      (if g.val < S then (1 : ℝ) else 0) := by
  by_cases hg : g.val < S
  · rw [show (∑ t : Fin S, (if g.val = t.val then (1 : ℝ) else 0)) =
        ∑ t : Fin S, (if t = ⟨g.val, hg⟩ then (1 : ℝ) else 0) by
      refine Finset.sum_congr rfl ?_
      intro t _
      by_cases hgt : g.val = t.val
      · have ht_eq : t = ⟨g.val, hg⟩ := by
          ext
          exact hgt.symm
        rw [if_pos hgt, if_pos ht_eq]
      · have ht_ne : t ≠ ⟨g.val, hg⟩ := by
          intro ht_eq
          apply hgt
          rw [ht_eq]
        rw [if_neg hgt, if_neg ht_ne]]
    rw [show (∑ t : Fin S, (if t = ⟨g.val, hg⟩ then (1 : ℝ) else 0)) = (1 : ℝ) by
      simpa using (Fintype.sum_ite_eq (i := ⟨g.val, hg⟩)
        (f := fun _ : Fin S => (1 : ℝ))).symm]
    simp [hg]
  · have hzero : ∀ t : Fin S, (if g.val = t.val then (1 : ℝ) else 0) = 0 := by
      intro t
      have hne : g.val ≠ t.val := by
        intro heq
        apply hg
        rw [heq]
        exact t.isLt
      rw [if_neg hne]
    rw [Finset.sum_eq_zero]
    · simp [hg]
    · intro t _
      exact hzero t

private lemma diagonal_col_hit_sum (law : CohortLaw C) (t : Fin S) :
    (∑ g : Fin C, (law.pi g : ℝ) * (if g.val = t.val then (1 : ℝ) else 0)) =
      diagPeriodMean law t := by
  unfold diagPeriodMean
  by_cases ht : t.val < C
  · rw [show (∑ g : Fin C, (law.pi g : ℝ) * (if g.val = t.val then (1 : ℝ) else 0)) =
        ∑ g : Fin C, (law.pi g : ℝ) * (if g = ⟨t.val, ht⟩ then (1 : ℝ) else 0) by
      refine Finset.sum_congr rfl ?_
      intro g _
      by_cases hgt : g.val = t.val
      · have hg_eq : g = ⟨t.val, ht⟩ := by
          ext
          exact hgt
        rw [if_pos hgt, if_pos hg_eq]
      · have hg_ne : g ≠ ⟨t.val, ht⟩ := by
          intro hg_eq
          apply hgt
          rw [hg_eq]
        rw [if_neg hgt, if_neg hg_ne]]
    rw [show (∑ g : Fin C, (law.pi g : ℝ) *
          (if g = ⟨t.val, ht⟩ then (1 : ℝ) else 0)) =
        (law.pi ⟨t.val, ht⟩ : ℝ) by
      simpa using (Fintype.sum_ite_eq (i := ⟨t.val, ht⟩)
        (f := fun g : Fin C => (law.pi g : ℝ))).symm]
    simp [ht]
  · have hzero :
        ∀ g : Fin C, (law.pi g : ℝ) * (if g.val = t.val then (1 : ℝ) else 0) = 0 := by
      intro g
      have hne : g.val ≠ t.val := by
        intro heq
        apply ht
        rw [← heq]
        exact g.isLt
      rw [if_neg hne]
      ring
    rw [Finset.sum_eq_zero]
    · simp [ht]
    · intro g _
      exact hzero g

private lemma diagonal_periodMean_sum_eq_grand_sum (law : CohortLaw C) :
    (∑ t : Fin S, diagPeriodMean law t) =
      ∑ g : Fin C, (if g.val < S then (law.pi g : ℝ) else 0) := by
  unfold diagPeriodMean
  rw [Finset.sum_fin_eq_sum_range]
  rw [Finset.sum_fin_eq_sum_range]
  simp only
  let f : ℕ → ℝ := fun x => if hC : x < C then (law.pi ⟨x, hC⟩ : ℝ) else 0
  let g : ℕ → ℝ := fun x => if hS : x < S then f x else 0
  have hL : (∑ x ∈ Finset.range S,
        if h : x < S then (if hC : x < C then (law.pi ⟨x, hC⟩ : ℝ) else 0) else 0) =
      ∑ x ∈ Finset.range S, f x := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    have hS : x < S := Finset.mem_range.mp hx
    simp [f, hS]
  have hR : (∑ x ∈ Finset.range C,
        if h : x < C then (if x < S then (law.pi ⟨x, h⟩ : ℝ) else 0) else 0) =
      ∑ x ∈ Finset.range C, g x := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    have hC : x < C := Finset.mem_range.mp hx
    by_cases hS : x < S <;> simp [f, g, hC, hS]
  rw [hL, hR]
  exact Finset.sum_congr_of_eq_on_inter
    (s₁ := Finset.range S) (s₂ := Finset.range C) (f := f) (g := g)
    (by
      intro x _ hxCnot
      have hnot : ¬ x < C := by simpa [Finset.mem_range] using hxCnot
      simp [f, hnot])
    (by
      intro x _ hxSnot
      have hnot : ¬ x < S := by simpa [Finset.mem_range] using hxSnot
      simp [g, hnot])
    (by
      intro x hxS _
      have hS : x < S := Finset.mem_range.mp hxS
      simp [g, hS])

private lemma diagonal_weighted_rowMean_eq_grand (law : CohortLaw C) :
    (∑ g : Fin C, (law.pi g : ℝ) * diagRowMean (S := S) g) =
      diagGrandMean (S := S) law := by
  unfold diagRowMean diagGrandMean
  rw [show (∑ g : Fin C,
        (law.pi g : ℝ) * (if g.val < S then 1 / (Fintype.card (Fin S) : ℝ) else 0)) =
      (1 / (Fintype.card (Fin S) : ℝ)) *
        ∑ g : Fin C, (if g.val < S then (law.pi g : ℝ) else 0) by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro g _
    by_cases hg : g.val < S
    · simp [hg]
      ring
    · simp [hg]]

private lemma diagonal_sum_Y_over_periods_eq_zero (law : CohortLaw C)
    (g₁ : Fin C) :
    (∑ t : Fin S, diagY (S := S) law (g₁, t)) = 0 := by
  unfold diagY diagX diagRowMean diagGrandMean
  simp only [Prod.fst, Prod.snd]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  rw [diagonal_row_hit_sum (S := S) (g := g₁)]
  rw [diagonal_periodMean_sum_eq_grand_sum (S := S) (law := law)]
  rw [show (∑ x : Fin S, (if g₁.val < S then 1 / (Fintype.card (Fin S) : ℝ) else 0)) =
      (Fintype.card (Fin S) : ℝ) *
        (if g₁.val < S then 1 / (Fintype.card (Fin S) : ℝ) else 0) by
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]]
  rw [show (∑ x : Fin S,
        1 / (Fintype.card (Fin S) : ℝ) *
          ∑ g : Fin C, (if g.val < S then (law.pi g : ℝ) else 0)) =
      (Fintype.card (Fin S) : ℝ) *
        (1 / (Fintype.card (Fin S) : ℝ) *
          ∑ g : Fin C, (if g.val < S then (law.pi g : ℝ) else 0)) by
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]]
  have hS0 : (Fintype.card (Fin S) : ℝ) ≠ 0 := by
    have : 0 < Fintype.card (Fin S) := Fintype.card_pos
    exact_mod_cast this.ne'
  have hSnz : (S : ℝ) ≠ 0 := by
    simpa [Fintype.card_fin] using hS0
  have hS_mul_inv : (S : ℝ) * (S : ℝ)⁻¹ = 1 := by
    field_simp [hSnz]
  by_cases hg : g₁.val < S
  · simp only [hg, if_true, Fintype.card_fin, one_div, mul_ite, mul_zero]
    rw [← mul_assoc, hS_mul_inv, one_mul]
    ring
  · simp only [hg, if_false, Fintype.card_fin, one_div, mul_ite, mul_zero]
    rw [← mul_assoc, hS_mul_inv, one_mul]
    ring

private lemma diagonal_weighted_sum_Y_over_cohorts_eq_zero (law : CohortLaw C)
    (t₁ : Fin S) :
    (∑ g : Fin C, (law.pi g : ℝ) * diagY (S := S) law (g, t₁)) = 0 := by
  unfold diagY diagX
  simp only [Prod.fst, Prod.snd]
  simp_rw [mul_add, mul_sub]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  rw [diagonal_col_hit_sum (law := law) (t := t₁)]
  rw [diagonal_weighted_rowMean_eq_grand (S := S) (law := law)]
  rw [show (∑ g : Fin C, (law.pi g : ℝ) * diagPeriodMean law t₁) =
      (∑ g : Fin C, (law.pi g : ℝ)) * diagPeriodMean law t₁ by
    rw [Finset.sum_mul]]
  rw [show (∑ g : Fin C, (law.pi g : ℝ) * diagGrandMean (S := S) law) =
      (∑ g : Fin C, (law.pi g : ℝ)) * diagGrandMean (S := S) law by
    rw [Finset.sum_mul]]
  rw [law.sumOne]
  ring

private lemma diagonal_centered_orth_unit (law : CohortLaw C)
    (hpi : ∀ g : Fin C, 0 < (law.pi g : ℝ)) (g₁ : Fin C) :
    (cohortPeriodCells law hpi).ip (diagY (S := S) law)
      (fun r : Fin C × Fin S => if r.1 = g₁ then (1 : ℝ) else 0) = 0 := by
  rw [cohortPeriod_ip_unit_eq (law := law) (hpi := hpi)]
  rw [diagonal_sum_Y_over_periods_eq_zero (S := S) (law := law) (g₁ := g₁)]
  ring

private lemma diagonal_centered_orth_period (law : CohortLaw C)
    (hpi : ∀ g : Fin C, 0 < (law.pi g : ℝ)) (t₁ : Fin S) :
    (cohortPeriodCells law hpi).ip (diagY (S := S) law)
      (fun r : Fin C × Fin S => if r.2 = t₁ then (1 : ℝ) else 0) = 0 := by
  rw [cohortPeriod_ip_period_eq (law := law) (hpi := hpi)]
  rw [diagonal_weighted_sum_Y_over_cohorts_eq_zero (S := S) (law := law) (t₁ := t₁)]
  ring

private noncomputable def triRowMean {C S : ℕ} (g : Fin C) : ℝ :=
  (∑ t : Fin S, (if g.val < t.val then (1 : ℝ) else 0)) /
    (Fintype.card (Fin S) : ℝ)

private noncomputable def triPeriodMean {C S : ℕ}
    (law : CohortLaw C) (t : Fin S) : ℝ :=
  ∑ g : Fin C, (if g.val < t.val then (1 : ℝ) else 0) * (law.pi g : ℝ)

private noncomputable def triGrandMean {C S : ℕ}
    (law : CohortLaw C) : ℝ :=
  (1 / (Fintype.card (Fin S) : ℝ)) *
    ∑ g : Fin C, ∑ t : Fin S,
      (if g.val < t.val then (law.pi g : ℝ) else 0)

private noncomputable def triX {C S : ℕ} : V (Fin C) (Fin S) :=
  fun s => if s.1.val < s.2.val then (1 : ℝ) else 0

private noncomputable def triY {C S : ℕ} (law : CohortLaw C) :
    V (Fin C) (Fin S) :=
  fun s =>
    triX s - triRowMean (S := S) s.1 - triPeriodMean law s.2 +
      triGrandMean (S := S) law

private lemma tri_sum_periodMean_eq_double (law : CohortLaw C) :
    (∑ t : Fin S, triPeriodMean law t) =
      ∑ g : Fin C, ∑ t : Fin S,
        (if g.val < t.val then (law.pi g : ℝ) else 0) := by
  unfold triPeriodMean
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro g _
  refine Finset.sum_congr rfl ?_
  intro t _
  by_cases h : g.val < t.val <;> simp [h]

private lemma tri_weighted_rowMean_eq_grand (law : CohortLaw C) :
    (∑ g : Fin C, (law.pi g : ℝ) * triRowMean (S := S) g) =
      triGrandMean (S := S) law := by
  unfold triRowMean triGrandMean
  rw [show (∑ g : Fin C,
        (law.pi g : ℝ) * ((∑ t : Fin S, if g.val < t.val then (1 : ℝ) else 0) /
          (Fintype.card (Fin S) : ℝ))) =
      (1 / (Fintype.card (Fin S) : ℝ)) *
        ∑ g : Fin C, (law.pi g : ℝ) *
          (∑ t : Fin S, if g.val < t.val then (1 : ℝ) else 0) by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro g _
    ring]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro g _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro t _
  by_cases h : g.val < t.val <;> simp [h]

private lemma tri_sum_Y_over_periods_eq_zero (law : CohortLaw C)
    (g₁ : Fin C) :
    (∑ t : Fin S, triY (S := S) law (g₁, t)) = 0 := by
  unfold triY triX triRowMean triGrandMean
  simp only [Prod.fst, Prod.snd]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  rw [tri_sum_periodMean_eq_double (S := S) (law := law)]
  rw [show (∑ x : Fin S,
        (∑ t : Fin S, if g₁.val < t.val then (1 : ℝ) else 0) /
          (Fintype.card (Fin S) : ℝ)) =
      (Fintype.card (Fin S) : ℝ) *
        ((∑ t : Fin S, if g₁.val < t.val then (1 : ℝ) else 0) /
          (Fintype.card (Fin S) : ℝ)) by
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]]
  rw [show (∑ x : Fin S,
        1 / (Fintype.card (Fin S) : ℝ) *
          ∑ g : Fin C, ∑ t : Fin S,
            (if g.val < t.val then (law.pi g : ℝ) else 0)) =
      (Fintype.card (Fin S) : ℝ) *
        (1 / (Fintype.card (Fin S) : ℝ) *
          ∑ g : Fin C, ∑ t : Fin S,
            (if g.val < t.val then (law.pi g : ℝ) else 0)) by
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]]
  have hS0 : (Fintype.card (Fin S) : ℝ) ≠ 0 := by
    have : 0 < Fintype.card (Fin S) := Fintype.card_pos
    exact_mod_cast this.ne'
  field_simp [hS0]
  ring_nf

private lemma tri_weighted_sum_Y_over_cohorts_eq_zero (law : CohortLaw C)
    (t₁ : Fin S) :
    (∑ g : Fin C, (law.pi g : ℝ) * triY (S := S) law (g, t₁)) = 0 := by
  unfold triY triX triPeriodMean
  simp only [Prod.fst, Prod.snd]
  simp_rw [mul_add, mul_sub]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  rw [tri_weighted_rowMean_eq_grand (S := S) (law := law)]
  rw [show (∑ g : Fin C, (law.pi g : ℝ) *
        (∑ g' : Fin C, (if g'.val < t₁.val then (1 : ℝ) else 0) * (law.pi g' : ℝ))) =
      (∑ g : Fin C, (law.pi g : ℝ)) *
        (∑ g' : Fin C, (if g'.val < t₁.val then (1 : ℝ) else 0) * (law.pi g' : ℝ)) by
    rw [Finset.sum_mul]]
  rw [show (∑ g : Fin C, (law.pi g : ℝ) * triGrandMean (S := S) law) =
      (∑ g : Fin C, (law.pi g : ℝ)) * triGrandMean (S := S) law by
    rw [Finset.sum_mul]]
  rw [law.sumOne]
  rw [show (∑ x : Fin C, (law.pi x : ℝ) * (if x.val < t₁.val then (1 : ℝ) else 0)) =
      ∑ x : Fin C, (if x.val < t₁.val then (1 : ℝ) else 0) * (law.pi x : ℝ) by
    refine Finset.sum_congr rfl ?_
    intro x _
    ring]
  ring_nf

private lemma tri_centered_orth_unit (law : CohortLaw C)
    (hpi : ∀ g : Fin C, 0 < (law.pi g : ℝ)) (g₁ : Fin C) :
    (cohortPeriodCells law hpi).ip (triY (S := S) law)
      (fun r : Fin C × Fin S => if r.1 = g₁ then (1 : ℝ) else 0) = 0 := by
  rw [cohortPeriod_ip_unit_eq (law := law) (hpi := hpi)]
  rw [tri_sum_Y_over_periods_eq_zero (S := S) (law := law) (g₁ := g₁)]
  ring

private lemma tri_centered_orth_period (law : CohortLaw C)
    (hpi : ∀ g : Fin C, 0 < (law.pi g : ℝ)) (t₁ : Fin S) :
    (cohortPeriodCells law hpi).ip (triY (S := S) law)
      (fun r : Fin C × Fin S => if r.2 = t₁ then (1 : ℝ) else 0) = 0 := by
  rw [cohortPeriod_ip_period_eq (law := law) (hpi := hpi)]
  rw [tri_weighted_sum_Y_over_cohorts_eq_zero (S := S) (law := law) (t₁ := t₁)]
  ring

/-- Diagonal (switch-on) indicator `ind(g.val = t.val)` under cohort-period
weights: the residual subtracts the cohort and period marginals plus a
grand-mean correction term.  In closed form

    tildeX R = ind(g.val = t.val)
              − E[R | g] − (E[R | t] − E[R])

with conditional means `E[R | g] = (1/S) · ind(g.val < S)`,
`E[R | t] = ind(t.val < C) · π(t.val)`, and grand mean
`E[R] = (1/S) · ∑_{g : g.val < S} π(g)`. -/
theorem tildeX_diagonal_indicator_cohortPeriod
    (r : Fin C × Fin S) (hr : r ∈ (cohortPeriodCells law hpi).observed) :
    (cohortPeriodCells law hpi).tildeX
        ((cohortPeriodCells law hpi).H_twfe)
        (fun s : Fin C × Fin S => if s.1.val = s.2.val then (1 : ℝ) else 0) r =
      (if r.1.val = r.2.val then (1 : ℝ) else 0)
        - (if r.1.val < S then 1 / (Fintype.card (Fin S) : ℝ) else 0)
        - (if h : r.2.val < C then (law.pi ⟨r.2.val, h⟩ : ℝ) else 0)
        + (1 / (Fintype.card (Fin S) : ℝ)) *
            ∑ g : Fin C, (if g.val < S then (law.pi g : ℝ) else 0) := by
  classical
  let c : Cells (Fin C) (Fin S) := cohortPeriodCells law hpi
  let X : V (Fin C) (Fin S) := diagX
  let Y : V (Fin C) (Fin S) := diagY law
  let G : V (Fin C) (Fin S) := X - Y
  have hG_mem : G ∈ c.H_twfe := by
    refine ⟨fun g => diagRowMean (S := S) g - diagGrandMean (S := S) law,
      fun t => diagPeriodMean law t, ?_⟩
    intro p
    simp [G, X, Y, diagY, diagX, diagRowMean, diagPeriodMean, diagGrandMean]
    ring
  have hXsubG : X - G = Y := by
    ext s
    simp [G]
  have horth : ∀ h ∈ c.H_twfe, c.ip (X - G) h = 0 := by
    rw [H_twfe_orthogonal_iff]
    constructor
    · intro g₁
      rw [hXsubG]
      exact diagonal_centered_orth_unit (S := S) (law := law) (hpi := hpi) (g₁ := g₁)
    · intro t₁
      rw [hXsubG]
      exact diagonal_centered_orth_period (S := S) (law := law) (hpi := hpi) (t₁ := t₁)
  have hproj : c.proj c.H_twfe X r = G r :=
    c.proj_apply_eq_of_mem_orthogonal c.H_twfe X hG_mem horth r hr
  calc
    c.tildeX c.H_twfe X r = (X - c.proj c.H_twfe X) r := by
      simp [Cells.tildeX_eq]
    _ = Y r := by
      rw [Pi.sub_apply, hproj]
      exact congrFun hXsubG r
    _ = (if r.1.val = r.2.val then (1 : ℝ) else 0)
        - (if r.1.val < S then 1 / (Fintype.card (Fin S) : ℝ) else 0)
        - (if h : r.2.val < C then (law.pi ⟨r.2.val, h⟩ : ℝ) else 0)
        + (1 / (Fintype.card (Fin S) : ℝ)) *
            ∑ g : Fin C, (if g.val < S then (law.pi g : ℝ) else 0) := rfl

/-- Triangular (continued-treatment) indicator `ind(g.val < t.val)` under
cohort-period weights: residual subtracts cohort and period marginals plus
the grand-mean correction.  In closed form

    tildeX J = ind(g.val < t.val)
              − E[J | g] − (E[J | t] − E[J])

with conditional means `E[J | g] = (1/S) · ∑_t ind(g.val < t.val)`,
`E[J | t] = ∑_{g'} π(g') ind(g'.val < t.val)`, and grand mean
`E[J] = (1/S) · ∑_{g, t} π(g) · ind(g.val < t.val)`. -/
theorem tildeX_triangular_indicator_cohortPeriod
    (r : Fin C × Fin S) (hr : r ∈ (cohortPeriodCells law hpi).observed) :
    (cohortPeriodCells law hpi).tildeX
        ((cohortPeriodCells law hpi).H_twfe)
        (fun s : Fin C × Fin S => if s.1.val < s.2.val then (1 : ℝ) else 0) r =
      (if r.1.val < r.2.val then (1 : ℝ) else 0)
        - (∑ s : Fin S, (if r.1.val < s.val then (1 : ℝ) else 0)) /
            (Fintype.card (Fin S) : ℝ)
        - (∑ g : Fin C,
            (if g.val < r.2.val then (1 : ℝ) else 0) * (law.pi g : ℝ))
        + (1 / (Fintype.card (Fin S) : ℝ)) *
            ∑ g : Fin C, ∑ s : Fin S,
              (if g.val < s.val then (law.pi g : ℝ) else 0) := by
  classical
  let c : Cells (Fin C) (Fin S) := cohortPeriodCells law hpi
  let X : V (Fin C) (Fin S) := triX
  let Y : V (Fin C) (Fin S) := triY law
  let G : V (Fin C) (Fin S) := X - Y
  have hG_mem : G ∈ c.H_twfe := by
    refine ⟨fun g => triRowMean (S := S) g - triGrandMean (S := S) law,
      fun t => triPeriodMean law t, ?_⟩
    intro p
    simp [G, X, Y, triY, triX, triRowMean, triPeriodMean, triGrandMean]
    ring
  have hXsubG : X - G = Y := by
    ext s
    simp [G]
  have horth : ∀ h ∈ c.H_twfe, c.ip (X - G) h = 0 := by
    rw [H_twfe_orthogonal_iff]
    constructor
    · intro g₁
      rw [hXsubG]
      exact tri_centered_orth_unit (S := S) (law := law) (hpi := hpi) (g₁ := g₁)
    · intro t₁
      rw [hXsubG]
      exact tri_centered_orth_period (S := S) (law := law) (hpi := hpi) (t₁ := t₁)
  have hproj : c.proj c.H_twfe X r = G r :=
    c.proj_apply_eq_of_mem_orthogonal c.H_twfe X hG_mem horth r hr
  calc
    c.tildeX c.H_twfe X r = (X - c.proj c.H_twfe X) r := by
      simp [Cells.tildeX_eq]
    _ = Y r := by
      rw [Pi.sub_apply, hproj]
      exact congrFun hXsubG r
    _ = (if r.1.val < r.2.val then (1 : ℝ) else 0)
        - (∑ s : Fin S, (if r.1.val < s.val then (1 : ℝ) else 0)) /
            (Fintype.card (Fin S) : ℝ)
        - (∑ g : Fin C,
            (if g.val < r.2.val then (1 : ℝ) else 0) * (law.pi g : ℝ))
        + (1 / (Fintype.card (Fin S) : ℝ)) *
            ∑ g : Fin C, ∑ s : Fin S,
              (if g.val < s.val then (law.pi g : ℝ) else 0) := rfl

end CohortPeriod

end Cells
end Panel
end Causalean
