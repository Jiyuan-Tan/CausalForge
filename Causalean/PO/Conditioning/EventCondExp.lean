/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Event-level conditional expectation wrapper

A thin wrapper around `∫ in A, g ∂μ / (μ A).toReal` suitable for the "conditioning
on a positive-probability event" idiom that appears throughout the
identification proofs (IV/LATE style).  Also provides a **drop-of-conditioning**
lemma: when the event-defining variable is jointly independent of a
counterfactual bundle `B`, conditioning on the event of the variable has no
effect on `∫ h ∘ B.jointValue`.

The drop-of-conditioning identity is stated in two forms:

* A **multiplied form** that mirrors `IndepFun.integral_restrict_preimage_eq_mul`
  and avoids division-by-zero edge cases.
* A **quotient form** using `eventCondExp`, which holds whenever
  `μ (rv.value ⁻¹' {x})` is neither `0` nor `∞`.
-/

import Causalean.PO.Core.Variable
import Causalean.PO.Assumptions.IndepCF
import Causalean.PO.Assumptions.ConsistencyLemmas
import Causalean.Mathlib.IndepIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Event-Level Conditional Expectations

This file packages conditioning on an event as a reusable event-level
conditional expectation and proves finite-partition and drop-of-conditioning
identities used throughout potential-outcome identification arguments.

The API starts with `eventCondExp`, its measure identity, finite-partition
decompositions, congruence, monotonicity, and algebra lemmas.  The main
potential-outcome workhorses are the `IndepCF` drop-of-conditioning theorems,
the consistency-on-event rewrite `POVar.eventCondExp_cfUnder_eq_factual_on_event`,
and `POSystem.eventCondExp_of_consistency_IndepCF`, which combines a supplied
event relabeling with independence. -/

namespace Causalean
namespace PO

open MeasureTheory ProbabilityTheory

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Event-level conditional expectation is the average of a real-valued
sample-space quantity over an event, computed as its integral over the event
divided by the event's real mass.

The definition is totalized: if the event has zero mass, the denominator is
`0` and identities such as `eventCondExp_mul_measure_toReal` keep track of the
corresponding zero-mass behavior. -/
def eventCondExp (μ : Measure Ω) (A : Set Ω) (g : Ω → ℝ) : ℝ :=
  (∫ ω in A, g ω ∂μ) / (μ A).toReal

/-! ### `eventCondExp` · measure identity and finite-partition total law

These two facts are domain-agnostic — they use only the definition of
`eventCondExp` and a finite-partition decomposition of the ambient space
— and are packaged here so every theorem file can share them. -/

/-- `eventCondExp μ A f · (μ A).toReal = ∫_A f`, including the zero-measure
case where both sides collapse to `0`. -/
lemma eventCondExp_mul_measure_toReal (μ : Measure Ω) [IsFiniteMeasure μ]
    (A : Set Ω) (f : Ω → ℝ) :
    eventCondExp μ A f * (μ A).toReal = ∫ ω in A, f ω ∂μ := by
  unfold eventCondExp
  by_cases h0 : (μ A).toReal = 0
  · rw [h0, mul_zero]
    have hμ0 : μ A = 0 := by
      rcases (ENNReal.toReal_eq_zero_iff _).mp h0 with h | h
      · exact h
      · exact absurd h (measure_ne_top _ _)
    exact (MeasureTheory.setIntegral_measure_zero f hμ0).symm
  · field_simp

/-- **Finite-partition total law.**  For any disjoint covering of `univ`
by a `Fintype`-indexed family of measurable sets,
`∫ f = ∑ i, (μ (A i)).toReal · eventCondExp μ (A i) f`.

Instantiating `ι := Bool` recovers the binary decomposition used in the
`Manski/{MTR,MTS}` proofs; instantiating `ι := α` for a discrete IV support
gives the tower-of-conditioning identity that unblocks the integrated MIV
bounds. -/
lemma integral_eq_sum_measure_mul_eventCondExp
    {ι : Type*} [Fintype ι] (μ : Measure Ω) [IsFiniteMeasure μ]
    (A : ι → Set Ω) (hmeas : ∀ i, MeasurableSet (A i))
    (hdisj : Pairwise (Function.onFun Disjoint A))
    (hcov : (⋃ i, A i) = Set.univ)
    (f : Ω → ℝ) (hf : Integrable f μ) :
    ∫ ω, f ω ∂μ
      = ∑ i, (μ (A i)).toReal * eventCondExp μ (A i) f := by
  have hsplit : ∫ ω in (⋃ i, A i), f ω ∂μ = ∑ i, ∫ ω in A i, f ω ∂μ :=
    MeasureTheory.integral_iUnion_fintype hmeas hdisj
      (fun _ => hf.integrableOn)
  have hcov' : ∫ ω, f ω ∂μ = ∑ i, ∫ ω in A i, f ω ∂μ := by
    rw [← hsplit, hcov, setIntegral_univ]
  rw [hcov']
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [mul_comm, eventCondExp_mul_measure_toReal]

/-- **Totalized finite-partition identity for event-level averages.**
Restricting the finite-partition decomposition to an event `A`, the
event-level average on `A` is the sum of the cell-level event averages weighted
by totalized event-mass ratios; when the conditioning event has positive
finite mass, these ratios are the usual conditional cell probabilities.

    event average on A =
      ∑ i, ((μ(A ∩ C i)).toReal / (μ A).toReal)
        · event average on A ∩ C i.

This is the measure-theoretic core of the finite→population bridge for
cell-indexed estimands: when `A = {G = g}`, the `C i` partition the covariate
space, and the event `A` has positive finite mass, the ratios become the
usual conditional probabilities `P(C = c | G = g)` and the cell-level event
averages become the corresponding within-cell conditional means. -/
lemma eventCondExp_eq_sum_condProb_mul_eventCondExp
    {ι : Type*} [Fintype ι] (μ : Measure Ω) [IsFiniteMeasure μ]
    (A : Set Ω) (C : ι → Set Ω) (hAmeas : MeasurableSet A)
    (hCmeas : ∀ i, MeasurableSet (C i))
    (hdisj : Pairwise (Function.onFun Disjoint C))
    (hcov : (⋃ i, C i) = Set.univ)
    (f : Ω → ℝ) (hf : Integrable f μ) :
    eventCondExp μ A f
      = ∑ i, (μ (A ∩ C i)).toReal / (μ A).toReal * eventCondExp μ (A ∩ C i) f := by
  -- The cells `A ∩ C i` are measurable, pairwise disjoint, and cover `A`.
  have hAC_meas : ∀ i, MeasurableSet (A ∩ C i) := fun i => hAmeas.inter (hCmeas i)
  have hAC_disj : Pairwise (Function.onFun Disjoint (fun i => A ∩ C i)) := by
    intro i j hij
    exact (hdisj hij).mono Set.inter_subset_right Set.inter_subset_right
  have hAC_cov : (⋃ i, A ∩ C i) = A := by
    rw [← Set.inter_iUnion, hcov, Set.inter_univ]
  -- Step 1: `∫_A f = ∑ i, ∫_{A ∩ C i} f`.
  have hsplit : ∫ ω in A, f ω ∂μ = ∑ i, ∫ ω in A ∩ C i, f ω ∂μ := by
    have h := MeasureTheory.integral_iUnion_fintype hAC_meas hAC_disj
      (fun _ => hf.integrableOn)
    rwa [hAC_cov] at h
  -- Step 2: each restricted integral is `μ(cell) · E[f | cell]`.
  have hcell : ∀ i, ∫ ω in A ∩ C i, f ω ∂μ
      = (μ (A ∩ C i)).toReal * eventCondExp μ (A ∩ C i) f := by
    intro i
    rw [mul_comm, eventCondExp_mul_measure_toReal]
  -- Assemble and divide through by `(μ A).toReal`.
  have hLHS : eventCondExp μ A f = (∫ ω in A, f ω ∂μ) / (μ A).toReal := rfl
  rw [hLHS, hsplit, Finset.sum_div]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hcell i, mul_div_right_comm]

/-! ### Congruence and monotonicity of `eventCondExp` -/

/-- a.e.-equal integrands have equal event-level conditional expectations. -/
lemma eventCondExp_congr_ae (μ : Measure Ω) (A : Set Ω) {f g : Ω → ℝ}
    (h : f =ᵐ[μ] g) :
    eventCondExp μ A f = eventCondExp μ A g := by
  unfold eventCondExp
  rw [MeasureTheory.integral_congr_ae (ae_restrict_of_ae h)]

/-- Equal-on-`A` integrands have equal event-level conditional expectations.
This specialises `eventCondExp_congr_ae` to a pointwise identity on a measurable
set `A`. -/
lemma eventCondExp_congr_on (μ : Measure Ω) {A : Set Ω} (hA : MeasurableSet A)
    {f g : Ω → ℝ} (h : ∀ ω ∈ A, f ω = g ω) :
    eventCondExp μ A f = eventCondExp μ A g := by
  unfold eventCondExp
  congr 1
  exact MeasureTheory.setIntegral_congr_fun hA h

/-- Monotonicity of `eventCondExp` under an a.e. inequality of integrable
functions. -/
lemma eventCondExp_mono_ae (μ : Measure Ω) {A : Set Ω} {f g : Ω → ℝ}
    (hf : IntegrableOn f A μ) (hg : IntegrableOn g A μ)
    (hfg : f ≤ᵐ[μ] g) :
    eventCondExp μ A f ≤ eventCondExp μ A g := by
  unfold eventCondExp
  have hint_le : ∫ ω in A, f ω ∂μ ≤ ∫ ω in A, g ω ∂μ :=
    MeasureTheory.setIntegral_mono_ae hf hg hfg
  have hnn : (0 : ℝ) ≤ (μ A).toReal := ENNReal.toReal_nonneg
  exact div_le_div_of_nonneg_right hint_le hnn

/-! ### Basic algebra of `eventCondExp` -/

/-- Event-level conditional expectation is additive for integrable summands on the event. -/
lemma eventCondExp_add (μ : Measure Ω) (A : Set Ω)
    {g₁ g₂ : Ω → ℝ}
    (h₁ : IntegrableOn g₁ A μ) (h₂ : IntegrableOn g₂ A μ) :
    eventCondExp μ A (g₁ + g₂) = eventCondExp μ A g₁ + eventCondExp μ A g₂ := by
  simp only [eventCondExp, Pi.add_apply, integral_add h₁ h₂, add_div]

/-- Event-level conditional expectation is additive over subtraction for
integrable functions on the event. -/
lemma eventCondExp_sub (μ : Measure Ω) (A : Set Ω)
    {g₁ g₂ : Ω → ℝ}
    (h₁ : IntegrableOn g₁ A μ) (h₂ : IntegrableOn g₂ A μ) :
    eventCondExp μ A (g₁ - g₂) = eventCondExp μ A g₁ - eventCondExp μ A g₂ := by
  simp only [eventCondExp, Pi.sub_apply, integral_sub h₁ h₂, sub_div]

/-- Event-level conditional expectation is homogeneous with respect to real
scalar multiplication. -/
lemma eventCondExp_smul (μ : Measure Ω) (A : Set Ω) (c : ℝ) (g : Ω → ℝ) :
    eventCondExp μ A (fun ω => c * g ω) = c * eventCondExp μ A g := by
  simp only [eventCondExp, MeasureTheory.integral_const_mul, mul_div_assoc]

/-! ### Generic drop-of-conditioning for `IndepFun` -/

/-- **Consistency + drop-of-conditioning for plain `IndepFun`.**  If `z` is
independent of a counterfactual bundle `B`, and a factual integrand agrees
with a measurable projection `h ∘ B` a.e. on the cell `{z = x}`, then its
event-level conditional expectation on that cell equals the unconditional
integral of the projection. -/
theorem eventCondExp_of_ae_eq_IndepFun
    {α β : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] {μ : Measure Ω}
    {z : Ω → α} {B : Ω → β}
    (hInd : IndepFun z B μ) (hz : Measurable z) (hB : Measurable B)
    {factualF : Ω → ℝ}
    {h : β → ℝ} (hh_meas : Measurable h) {x : α}
    (hF_eq : factualF =ᵐ[μ.restrict (z ⁻¹' {x})] fun ω => h (B ω))
    (hμA_pos : 0 < (μ (z ⁻¹' {x})).toReal) :
    eventCondExp μ (z ⁻¹' {x}) factualF = ∫ ω, h (B ω) ∂μ := by
  unfold eventCondExp
  rw [MeasureTheory.integral_congr_ae hF_eq]
  rw [hInd.integral_restrict_preimage_eq_mul hz hB (measurableSet_singleton x) hh_meas]
  have hpos : (μ (z ⁻¹' {x})).toReal ≠ 0 := ne_of_gt hμA_pos
  field_simp

/-! ### Drop-of-conditioning for `IndepCF`

The `IndepCF` shape gives us `IndepFun rv.value B.jointValue μ`, so the
generic `IndepFun.integral_restrict_preimage_eq_mul` applies directly with
`f := rv.value`, `g := B.jointValue`, `E := {x}`.  We phrase the main lemma
against a `RegimedVar` since that is the exact shape consumed by `IndepCF`. -/

variable {P : POSystem}

/-- **Drop-of-conditioning (multiplied form).**  If a regimed variable `rv` is
independent of the counterfactual bundle `B`, then the integral of
`h ∘ B.jointValue` over the preimage `rv.value ⁻¹' {x}` factors as
`(μ (rv.value ⁻¹' {x})).toReal * ∫ h ∘ B.jointValue ∂μ`.

This is the core identity; the quotient form below divides through by
`(μ (rv.value ⁻¹' {x})).toReal`, which is valid whenever the event has
finite positive measure. -/
theorem POSystem.integral_restrict_value_eq_mul_of_IndepCF
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    {rv : RegimedVar P α} {B : POCFBundle P}
    {μ : Measure P.Ω}
    (hInd : P.IndepCF rv B μ)
    {h : (∀ i : Fin B.n, B.type i) → ℝ}
    (hh_meas : Measurable h) (x : α) :
    ∫ ω in rv.value ⁻¹' {x}, h (B.jointValue ω) ∂μ
      = (μ (rv.value ⁻¹' {x})).toReal * ∫ ω, h (B.jointValue ω) ∂μ :=
  hInd.toIndepFun.integral_restrict_preimage_eq_mul
    rv.measurable_value B.measurable_jointValue (measurableSet_singleton x) hh_meas

/-- **Drop-of-conditioning for the factual event.**  Specialisation of
`POSystem.integral_restrict_value_eq_mul_of_IndepCF` to a factual `POVar`,
using `POVar.event` directly. -/
theorem POSystem.integral_event_eq_mul_of_IndepCF
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    {a : POVar P α} {B : POCFBundle P}
    {μ : Measure P.Ω}
    (hInd : P.IndepCF (RegimedVar.ofFactual a) B μ)
    {h : (∀ i : Fin B.n, B.type i) → ℝ}
    (hh_meas : Measurable h) (x : α) :
    ∫ ω in a.event x, h (B.jointValue ω) ∂μ
      = (μ (a.event x)).toReal * ∫ ω, h (B.jointValue ω) ∂μ := by
  -- `a.event x = (RegimedVar.ofFactual a).value ⁻¹' {x}` by definition, since
  -- `(ofFactual a).value = a.cf Regime.empty = a.factual` and
  -- `a.event x = a.factual ⁻¹' {x}`.
  have hev : a.event x = (RegimedVar.ofFactual a).value ⁻¹' {x} := by
    rfl
  rw [hev]
  simpa using
    (POSystem.integral_restrict_value_eq_mul_of_IndepCF hInd hh_meas x)

/-- **Drop-of-conditioning (quotient form).**  Under `IndepCF`, the event-level
conditional expectation `E[h ∘ B.jointValue | rv.value = x]` collapses to the
unconditional integral, provided the event has finite positive measure. -/
theorem POSystem.eventCondExp_eq_integral_of_IndepCF
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    {rv : RegimedVar P α} {B : POCFBundle P}
    {μ : Measure P.Ω}
    (hInd : P.IndepCF rv B μ)
    {h : (∀ i : Fin B.n, B.type i) → ℝ}
    (hh_meas : Measurable h) {x : α}
    (hμA_ne_zero : μ (rv.value ⁻¹' {x}) ≠ 0)
    (hμA_ne_top : μ (rv.value ⁻¹' {x}) ≠ ⊤) :
    eventCondExp μ (rv.value ⁻¹' {x}) (fun ω => h (B.jointValue ω))
      = ∫ ω, h (B.jointValue ω) ∂μ := by
  unfold eventCondExp
  rw [POSystem.integral_restrict_value_eq_mul_of_IndepCF hInd hh_meas x]
  have hpos : (μ (rv.value ⁻¹' {x})).toReal ≠ 0 := by
    rw [ENNReal.toReal_ne_zero]
    exact ⟨hμA_ne_zero, hμA_ne_top⟩
  field_simp

/-- **Drop-of-conditioning on factual events (quotient form).**  Specialisation
of the above to the factual event `a.event x`. -/
theorem POSystem.eventCondExp_event_eq_integral_of_IndepCF
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    {a : POVar P α} {B : POCFBundle P}
    {μ : Measure P.Ω}
    (hInd : P.IndepCF (RegimedVar.ofFactual a) B μ)
    {h : (∀ i : Fin B.n, B.type i) → ℝ}
    (hh_meas : Measurable h) {x : α}
    (hμA_ne_zero : μ (a.event x) ≠ 0)
    (hμA_ne_top : μ (a.event x) ≠ ⊤) :
    eventCondExp μ (a.event x) (fun ω => h (B.jointValue ω))
      = ∫ ω, h (B.jointValue ω) ∂μ := by
  have hev : a.event x = (RegimedVar.ofFactual a).value ⁻¹' {x} := rfl
  rw [hev] at hμA_ne_zero hμA_ne_top ⊢
  exact POSystem.eventCondExp_eq_integral_of_IndepCF
    hInd hh_meas hμA_ne_zero hμA_ne_top

/-- **Consistency-on-event for `eventCondExp`.**  Generic consumer of
`POVar.cf_eq_factual_on_event`: on the event `{a = a₀}`, the counterfactual
`y.cfUnder a a₀` agrees with `y.factual` pointwise, so their conditional
means on that event coincide.  This is the shared rewrite underlying
Manski `MTR`/`MTS` and (via the finite-partition total law) the
integrated MIV bounds. -/
theorem POVar.eventCondExp_cfUnder_eq_factual_on_event
    {P : POSystem} {β : Type*}
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (hC : P.Consistency)
    (y : POVar P ℝ) (a : POVar P β) (a₀ : β) (hvw : y.v ≠ a.v)
    (μ : Measure P.Ω) :
    eventCondExp μ (a.event a₀) (y.cfUnder a a₀)
      = eventCondExp μ (a.event a₀) y.factual := by
  unfold eventCondExp
  congr 1
  refine MeasureTheory.setIntegral_congr_fun (a.measurableSet_event a₀) ?_
  intro ω hω
  exact POVar.cf_eq_factual_on_event hC y a a₀ hvw hω

/-- **Drop-of-conditioning on an event, given a bundle relabeling of the
integrand.**  Takes as a HYPOTHESIS (`hF_eq`) that the factual integrand
`factualF` equals `h ∘ B.jointValue` on the event `{a = x}` — a *relabeling* of
`factualF` as a function of the bundle's joint counterfactual value — and
combines it with the `IndepCF` drop-of-conditioning identity to evaluate
`E[factualF | a = x] = ∫ h(B.jointValue) ∂μ`.

NOTE on the name: this lemma does NOT itself assume `P.Consistency`. The
`_of_consistency_` records where `hF_eq` usually comes from at the call site —
real consistency (`POVar.cf_eq_factual_on_event`) rewriting the factual into its
counterfactual/bundle form — but that derivation is the caller's, supplied here
purely as the premise `hF_eq`. The workhorse of LATE-style first-stage /
reduced-form proofs. -/
theorem POSystem.eventCondExp_of_consistency_IndepCF
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    {a : POVar P α} {B : POCFBundle P}
    {μ : Measure P.Ω}
    (hInd : P.IndepCF (RegimedVar.ofFactual a) B μ)
    {factualF : P.Ω → ℝ}
    {h : (∀ i : Fin B.n, B.type i) → ℝ} (hh_meas : Measurable h)
    {x : α}
    (hF_eq : ∀ ω ∈ a.event x, factualF ω = h (B.jointValue ω))
    (hμA_ne_zero : μ (a.event x) ≠ 0)
    (hμA_ne_top : μ (a.event x) ≠ ⊤) :
    eventCondExp μ (a.event x) factualF = ∫ ω, h (B.jointValue ω) ∂μ := by
  unfold eventCondExp
  rw [MeasureTheory.setIntegral_congr_fun (a.measurableSet_event x) hF_eq]
  rw [POSystem.integral_event_eq_mul_of_IndepCF hInd hh_meas x]
  have hpos : (μ (a.event x)).toReal ≠ 0 := by
    rw [ENNReal.toReal_ne_zero]
    exact ⟨hμA_ne_zero, hμA_ne_top⟩
  field_simp

end

end PO
end Causalean
