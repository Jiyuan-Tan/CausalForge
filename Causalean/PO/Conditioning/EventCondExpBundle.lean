/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Bundle analogue of `POSystem.eventCondExp_of_consistency_IndepCF`

`PO/Conditioning/EventCondExp.lean` provides the single-period workhorse used in
`PO/ID/Exact/LATE.lean` and `HeckmanRoy/Wald.lean`:

  E[factualF | a = x]  =  ∫ h(B.jointValue) dμ

under unconditional `IndepCF a B` plus the consistency-on-event identity
`factualF = h ∘ B.jointValue` on `{a = x}`.

This file lifts the same identity to the *bundle conditional* setting used
by the Dynamic LATE bridges (def:po-dynamic-late-bridge).  Under
`P.CondIndepCFBundle a B C` (instrument `a` independent of `B` given the
σ-algebra of `C`) and the same consistency-on-event premise, the bundle
conditional expectation of the product `factualF · 1_{a=x}` factors:

  C.condExpGiven (factualF · 1_{a=x})
    =ᵐ C.condExpGiven (h ∘ B.jointValue) · C.condExpGiven (1_{a=x}).

The corresponding **ratio form** then collapses to the conditional mean of
`h ∘ B.jointValue` whenever the conditional probability of `{a=x}` is a.s.
positive.  This is the per-stage workhorse for the four bridge identities
in `PO/ID/Exact/DynamicLATE/Bridges.lean`.

Proof outline:
1.  Rewrite `factualF · 1_{a=x} =ᵐ (h ∘ B.jointValue) · 1_{a=x}` using `hF_eq`.
2.  Recognise `1_{a=x} = u ∘ a.factual` for `u y := if y = x then 1 else 0`,
    so the LHS integrand becomes `(u ∘ a.factual) · (h ∘ B.jointValue)`.
3.  Apply `Causalean.condExp_mul_of_condIndep` with `m := C.sigma`,
    `f := a.factual`, `g := B.jointValue`, exploiting
    `hCI.toCondIndepFun : CondIndepFun C.sigma C.sigma_le a.factual B.jointValue P.μ`
    (which holds because `(RegimedVar.ofFactual a).value = a.factual` by `rfl`).
4.  Rewrite the resulting product back into `condExpGiven` form via
    `POCFBundle.condExpGiven_congr_ae` and `hu_eq`.
-/

import Causalean.PO.Conditioning.Bundle
import Causalean.PO.Conditioning.EventCondExp

/-! # Bundle-Conditional Event Expectations

This file extends the event-level conditional-expectation workhorse to
conditioning on a finite bundle of potential-outcome variables. It provides the
product and ratio forms needed for dynamic local-average-treatment-effect bridge
arguments.

The theorem `POCFBundle.condExpGiven_mul_of_consistency_CondIndepCFBundle`
turns bundle-conditional independence and a consistency-on-event product
identity into a factorization of bundle conditional expectations.  The theorem
`POCFBundle.condExpRatio_of_consistency_CondIndepCFBundle` divides that
factorization by the conditional event probability under an a.e. nonzero
denominator assumption. -/

namespace Causalean
namespace PO

open MeasureTheory ProbabilityTheory

noncomputable section

namespace POCFBundle

variable {P : POSystem} (B C : POCFBundle P)

/-- **Bundle product-form workhorse** (analogue of
`POSystem.eventCondExp_of_consistency_IndepCF`).

Under bundle-conditional independence `a ⟂ B | C` and a consistency-on-event
premise expressed as the a.e. identity of products
`factualF · 1_{a=x} =ᵐ h(B.jointValue) · 1_{a=x}`, the bundle conditional
expectation factorises as

  C.condExpGiven (factualF · 1_{a=x})
    =ᵐ C.condExpGiven (h ∘ B.jointValue) · C.condExpGiven (1_{a=x}).

Used by dynamic-regime bridge arguments that condition on a history bundle. -/
theorem condExpGiven_mul_of_consistency_CondIndepCFBundle
    [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    {a : POVar P α}
    (hCI : P.CondIndepCFBundle (RegimedVar.ofFactual a) B C P.μ)
    {factualF : P.Ω → ℝ} (hF_meas : Measurable factualF)
    {h : (∀ i, B.type i) → ℝ} (hh_meas : Measurable h)
    (hh_int : Integrable (fun ω => h (B.jointValue ω)) P.μ)
    {x : α}
    (hF_eq : (fun ω => factualF ω * a.indicator x ω) =ᵐ[P.μ]
              fun ω => h (B.jointValue ω) * a.indicator x ω) :
    C.condExpGiven (fun ω => factualF ω * a.indicator x ω) P.μ
        =ᵐ[P.μ]
      fun ω => C.condExpGiven (fun ω' => h (B.jointValue ω')) P.μ ω
        * C.condExpGiven (a.indicator x) P.μ ω := by
  let u : α → ℝ := ({x} : Set α).indicator (fun _ => (1 : ℝ))
  have _ : Measurable (fun ω => factualF ω * a.indicator x ω) :=
    hF_meas.mul (a.measurable_indicator x)
  have hu_meas : Measurable u :=
    measurable_const.indicator (MeasurableSet.singleton x)
  have hu_eq : (fun ω => u (a.factual ω)) = a.indicator x := by
    funext ω
    unfold POVar.indicator
    by_cases hω : a.factual ω = x
    · have h1 : a.factual ω ∈ ({x} : Set α) := hω
      have h2 : ω ∈ a.event x := hω
      rw [show u (a.factual ω) = (1 : ℝ) from Set.indicator_of_mem h1 _,
          Set.indicator_of_mem h2]
    · have h1 : a.factual ω ∉ ({x} : Set α) := hω
      have h2 : ω ∉ a.event x := hω
      rw [show u (a.factual ω) = (0 : ℝ) from Set.indicator_of_notMem h1 _,
          Set.indicator_of_notMem h2]
  have huv_int : Integrable
      (fun ω => u (a.factual ω) * h (B.jointValue ω)) P.μ := by
    have hEq : (fun ω => u (a.factual ω) * h (B.jointValue ω)) =
        (fun ω => a.indicator x ω * h (B.jointValue ω)) := by
      funext ω
      rw [congr_fun hu_eq ω]
    rw [hEq]
    refine hh_int.mono
      ((a.measurable_indicator x).mul
        (hh_meas.comp B.measurable_jointValue)).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun ω => ?_)
    rcases a.indicator_eq_one_or_zero x ω with hω | hω <;> simp [hω]
  have hfact :
      P.μ[fun ω => u (a.factual ω) * h (B.jointValue ω) | C.sigma]
        =ᵐ[P.μ]
          P.μ[fun ω => u (a.factual ω) | C.sigma]
            * P.μ[fun ω => h (B.jointValue ω) | C.sigma] :=
    condExp_mul_of_condIndep (μ := P.μ)
        (m := C.sigma) C.sigma_le
        (f := a.factual) (g := B.jointValue)
        a.measurable_factual B.measurable_jointValue hCI.toCondIndepFun
        (u := u) (v := h) hu_meas hh_meas
        (by rw [hu_eq]; exact a.integrable_indicator x) hh_int huv_int
  have hfact' :
      C.condExpGiven (fun ω => h (B.jointValue ω) * a.indicator x ω) P.μ
        =ᵐ[P.μ]
          fun ω => C.condExpGiven (fun ω' => h (B.jointValue ω')) P.μ ω
            * C.condExpGiven (a.indicator x) P.μ ω := by
    unfold POCFBundle.condExpGiven
    have hprod_rw :
        (fun ω => u (a.factual ω) * h (B.jointValue ω)) =
          (fun ω => h (B.jointValue ω) * a.indicator x ω) := by
      funext ω
      rw [congr_fun hu_eq ω]
      ring
    rw [hprod_rw, hu_eq] at hfact
    filter_upwards [hfact] with ω hω
    simpa [Pi.mul_apply, mul_comm] using hω
  exact (C.condExpGiven_congr_ae hF_eq).trans hfact'

/-- **Bundle ratio-form workhorse**: ratio version of
`condExpGiven_mul_of_consistency_CondIndepCFBundle`.  Under the same
hypotheses plus an a.s.-positive denominator, the conditional ratio
`condExpRatio (factualF · 1_{a=x}) (1_{a=x})` collapses to the conditional
mean of `h ∘ B.jointValue`. -/
theorem condExpRatio_of_consistency_CondIndepCFBundle
    [StandardBorelSpace P.Ω] [IsFiniteMeasure P.μ]
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    {a : POVar P α}
    (hCI : P.CondIndepCFBundle (RegimedVar.ofFactual a) B C P.μ)
    {factualF : P.Ω → ℝ} (hF_meas : Measurable factualF)
    {h : (∀ i, B.type i) → ℝ} (hh_meas : Measurable h)
    (hh_int : Integrable (fun ω => h (B.jointValue ω)) P.μ)
    {x : α}
    (hF_eq : (fun ω => factualF ω * a.indicator x ω) =ᵐ[P.μ]
              fun ω => h (B.jointValue ω) * a.indicator x ω)
    (hOver : ∀ᵐ ω ∂P.μ, C.condExpGiven (a.indicator x) P.μ ω ≠ 0) :
    C.condExpRatio (fun ω => factualF ω * a.indicator x ω) (a.indicator x) P.μ
        =ᵐ[P.μ]
      C.condExpGiven (fun ω' => h (B.jointValue ω')) P.μ := by
  refine C.condExpRatio_eq_of_mul ?_ hOver
  filter_upwards [condExpGiven_mul_of_consistency_CondIndepCFBundle B C
    hCI hF_meas hh_meas hh_int hF_eq] with ω hω
  simpa [Pi.mul_apply, mul_comm] using hω

end POCFBundle

end

end PO
end Causalean
