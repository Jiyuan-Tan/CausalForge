/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Multiple-instrument IV observed population bridge

Measure-backed bridge from the source population 2SLS moment ratio
`E[h(Z)Y] / E[h(Z)D]` to the finite response-type algebra.
-/

import Causalean.PO.ID.Exact.MultipleInstrumentIV.ResponseTypes
import Causalean.PO.Conditioning.EventCondExp
/-! # Multiple-Instrument IV Population Bridge

This file connects the observed population two-stage least squares moment
ratio for a finite instrument to the response-type finite algebra. It defines
the observed moments `observedReducedFormMoment`, `observedFirstStageMoment`,
and `observedBeta2SLS`; rewrites the first two as finite sums over instrument
cells; and packages the assumptions needed for the measure-backed bridge in
`ObservedBridge`.

The main results are `ObservedBridge.observedReducedFormMoment_eq_reducedFormMoment`,
`ObservedBridge.observedFirstStageMoment_eq_firstStageMoment`,
`ObservedBridge.observedBeta2SLS_eq_beta2SLSPopulationBridge`, and the
end-to-end theorem `ObservedBridge.observedBeta2SLS_eq_beta2SLSFiniteAlgebra`.
They show that the observable population ratio `E[h(Z)Y] / E[h(Z)D]` agrees
with the saturated response-type algebra once the observed conditional means
are linked to the finite response-type bridge. -/

namespace Causalean
namespace PO.ID.Exact
namespace MultipleInstrumentIV

open Finset MeasureTheory

noncomputable section

namespace ResponseTypeStats.PopulationBridge

variable {Ω : Type*} [MeasurableSpace Ω] {K : ℕ}

/-- Instrument cell `{ω | Z ω = k}`. -/
def zEvent (Z : Ω → Fin K) (k : Fin K) : Set Ω :=
  Z ⁻¹' ({k} : Set (Fin K))

/-- Observed reduced-form moment `E[h(Z)Y]`, where
`h(zᵏ) = dhat_k − Σ_l ρ_l dhat_l`. -/
noncomputable def observedReducedFormMoment
    (μ : Measure Ω) (Z : Ω → Fin K) (Y : Ω → ℝ) (I : FiniteIndex K) : ℝ :=
  ∫ ω, I.centeredIndex (Z ω) * Y ω ∂μ

/-- Observed first-stage moment `E[h(Z)D]`, with binary treatment coerced to
the real values `0` and `1`. -/
noncomputable def observedFirstStageMoment
    (μ : Measure Ω) (Z : Ω → Fin K) (D : Ω → Bool) (I : FiniteIndex K) : ℝ :=
  ∫ ω, I.centeredIndex (Z ω) * boolToReal (D ω) ∂μ

/-- Source population 2SLS ratio `E[h(Z)Y] / E[h(Z)D]`. -/
noncomputable def observedBeta2SLS
    (μ : Measure Ω) (Z : Ω → Fin K) (D : Ω → Bool) (Y : Ω → ℝ)
    (I : FiniteIndex K) : ℝ :=
  observedReducedFormMoment μ Z Y I / observedFirstStageMoment μ Z D I

private lemma zEvent_measurable (Z : Ω → Fin K) (hZ : Measurable Z) (k : Fin K) :
    MeasurableSet (zEvent Z k) :=
  hZ (measurableSet_singleton k)

omit [MeasurableSpace Ω] in
private lemma zEvent_pairwise_disjoint (Z : Ω → Fin K) :
    Pairwise (Function.onFun Disjoint (zEvent Z)) := by
  intro k l hkl
  rw [Function.onFun]
  refine Set.disjoint_left.mpr ?_
  intro ω hk hl
  exact hkl ((Set.mem_singleton_iff.mp hk).symm.trans (Set.mem_singleton_iff.mp hl))

omit [MeasurableSpace Ω] in
private lemma zEvent_iUnion (Z : Ω → Fin K) :
    (⋃ k : Fin K, zEvent Z k) = Set.univ := by
  ext ω
  simp [zEvent]

private lemma eventCondExp_centered_mul_eq
    (μ : Measure Ω) (Z : Ω → Fin K) (hZ : Measurable Z)
    (Y : Ω → ℝ) (I : FiniteIndex K) (k : Fin K) :
    PO.eventCondExp μ (zEvent Z k) (fun ω => I.centeredIndex (Z ω) * Y ω) =
      I.centeredIndex k * PO.eventCondExp μ (zEvent Z k) Y := by
  calc
    PO.eventCondExp μ (zEvent Z k) (fun ω => I.centeredIndex (Z ω) * Y ω) =
        PO.eventCondExp μ (zEvent Z k) (fun ω => I.centeredIndex k * Y ω) := by
      apply PO.eventCondExp_congr_on μ (zEvent_measurable Z hZ k)
      intro ω hω
      have hZω : Z ω = k := Set.mem_singleton_iff.mp hω
      simp [hZω]
    _ = I.centeredIndex k * PO.eventCondExp μ (zEvent Z k) Y := by
      exact PO.eventCondExp_smul μ (zEvent Z k) (I.centeredIndex k) Y

/-- Finite-support total-law rewrite of `E[h(Z)Y]` into instrument-cell
conditional expectations. -/
theorem observedReducedFormMoment_eq_sum_eventCondExp
    (μ : Measure Ω) [IsFiniteMeasure μ] (Z : Ω → Fin K) (hZ : Measurable Z)
    (Y : Ω → ℝ) (I : FiniteIndex K)
    (hInt : Integrable (fun ω => I.centeredIndex (Z ω) * Y ω) μ) :
    observedReducedFormMoment μ Z Y I =
      ∑ k : Fin K,
        (μ (zEvent Z k)).toReal * I.centeredIndex k *
          PO.eventCondExp μ (zEvent Z k) Y := by
  unfold observedReducedFormMoment
  rw [PO.integral_eq_sum_measure_mul_eventCondExp
    (μ := μ) (A := zEvent Z)
    (hmeas := zEvent_measurable Z hZ)
    (hdisj := zEvent_pairwise_disjoint Z)
    (hcov := zEvent_iUnion Z)
    (f := fun ω => I.centeredIndex (Z ω) * Y ω) hInt]
  refine Finset.sum_congr rfl ?_
  intro k _hk
  rw [eventCondExp_centered_mul_eq μ Z hZ Y I k]
  ring

/-- Finite-support total-law rewrite of `E[h(Z)D]` into instrument-cell
conditional expectations. -/
theorem observedFirstStageMoment_eq_sum_eventCondExp
    (μ : Measure Ω) [IsFiniteMeasure μ] (Z : Ω → Fin K) (hZ : Measurable Z)
    (D : Ω → Bool) (I : FiniteIndex K)
    (hInt : Integrable (fun ω => I.centeredIndex (Z ω) * boolToReal (D ω)) μ) :
    observedFirstStageMoment μ Z D I =
      ∑ k : Fin K,
        (μ (zEvent Z k)).toReal * I.centeredIndex k *
          PO.eventCondExp μ (zEvent Z k) (fun ω => boolToReal (D ω)) := by
  exact observedReducedFormMoment_eq_sum_eventCondExp
    (μ := μ) (Z := Z) hZ (Y := fun ω => boolToReal (D ω)) I hInt

/-- Assumptions connecting observed probability objects to the finite
response-type bridge.  The two conditional-expectation fields are the precise
place where consistency, exogeneity, and exclusion are used: for each
instrument cell, they replace the observed conditional mean by the
response-type expansion already consumed by the finite MTW algebra. -/
structure ObservedBridge (μ : Measure Ω) (Z : Ω → Fin K)
    (D : Ω → Bool) (Y : Ω → ℝ) (I : FiniteIndex K)
    (P : PopulationBridge K) where
  /-- The observed law is a probability measure, so the integrals below are
  population expectations. -/
  isProbability : IsProbabilityMeasure μ
  /-- The finite support masses in `I` are the probabilities of the observed
  instrument cells. -/
  rho_eq_zMass : ∀ k : Fin K, I.rho k = (μ (zEvent Z k)).toReal
  /-- Conditional outcome bridge after consistency, exogeneity, and exclusion:
  for each instrument cell Z = zᵏ, the observed conditional mean E[Y | Z = zᵏ]
  equals the response-type expansion `P.outcomeAtSupport k`.

  This is a *field* of the algebraic bridge, but it is no longer only an
  external hypothesis: `MultipleInstrumentIV/POBridge.lean` (`toObservedBridge`)
  *derives* it from a `POMultipleIVSystem` under consistency + instrument
  independence, discharging Gap G5 of the faithfulness audit
  (`doc/basic_concepts/po/estimand_characterization/audit/mtw.md`).  Callers may
  either supply it directly or obtain the whole bridge from the PO system. -/
  outcome_cell :
    ∀ k : Fin K,
      PO.eventCondExp μ (zEvent Z k) Y = P.outcomeAtSupport k
  /-- Baseline treatment mean, common across support cells after exogeneity.
  The centered first-stage score cancels this term in the first-stage moment. -/
  baseTreatment : ℝ
  /-- Conditional treatment bridge after consistency and exogeneity, stated in
  baseline-subtracted form: the adjacent telescoping term is the deviation from
  the baseline support point, not the raw treatment mean.

  Like `outcome_cell`, this field is *derived* (not merely assumed) from a
  `POMultipleIVSystem` under consistency + instrument independence in
  `MultipleInstrumentIV/POBridge.lean` (`toObservedBridge`), discharging Gap G5
  of the faithfulness audit. -/
  treatment_cell :
    ∀ k : Fin K,
      PO.eventCondExp μ (zEvent Z k) (fun ω => boolToReal (D ω)) =
        baseTreatment + P.treatmentAtSupport k

namespace ObservedBridge

variable {μ : Measure Ω} {Z : Ω → Fin K} {D : Ω → Bool} {Y : Ω → ℝ}
variable {I : FiniteIndex K} {P : PopulationBridge K}

/-- The observed reduced-form moment equals the finite response-type
reduced-form moment. -/
theorem observedReducedFormMoment_eq_reducedFormMoment
    (B : ObservedBridge μ Z D Y I P) [IsFiniteMeasure μ] (hZ : Measurable Z)
    (hInt : Integrable (fun ω => I.centeredIndex (Z ω) * Y ω) μ) :
    observedReducedFormMoment μ Z Y I = P.reducedFormMoment I := by
  rw [observedReducedFormMoment_eq_sum_eventCondExp μ Z hZ Y I hInt]
  unfold reducedFormMoment
  refine Finset.sum_congr rfl ?_
  intro k _hk
  rw [← B.rho_eq_zMass k, B.outcome_cell k]

/-- The observed first-stage moment equals the finite response-type
first-stage moment. -/
theorem observedFirstStageMoment_eq_firstStageMoment
    (B : ObservedBridge μ Z D Y I P) [IsFiniteMeasure μ] (hZ : Measurable Z)
    (hInt : Integrable (fun ω => I.centeredIndex (Z ω) * boolToReal (D ω)) μ) :
    observedFirstStageMoment μ Z D I = P.firstStageMoment I := by
  rw [observedFirstStageMoment_eq_sum_eventCondExp μ Z hZ D I hInt]
  unfold firstStageMoment
  calc
    (∑ k : Fin K,
        (μ (zEvent Z k)).toReal * I.centeredIndex k *
          PO.eventCondExp μ (zEvent Z k) (fun ω => boolToReal (D ω))) =
        ∑ k : Fin K,
          I.rho k * I.centeredIndex k *
            (B.baseTreatment + P.treatmentAtSupport k) := by
      refine Finset.sum_congr rfl ?_
      intro k _hk
      rw [← B.rho_eq_zMass k, B.treatment_cell k]
    _ = (∑ k : Fin K, I.rho k * I.centeredIndex k) * B.baseTreatment +
          ∑ k : Fin K, I.rho k * I.centeredIndex k * P.treatmentAtSupport k := by
      calc
        (∑ k : Fin K, I.rho k * I.centeredIndex k *
            (B.baseTreatment + P.treatmentAtSupport k)) =
            ∑ k : Fin K,
              (I.rho k * I.centeredIndex k * B.baseTreatment +
                I.rho k * I.centeredIndex k * P.treatmentAtSupport k) := by
          refine Finset.sum_congr rfl ?_
          intro k _hk
          ring
        _ = (∑ k : Fin K, I.rho k * I.centeredIndex k * B.baseTreatment) +
              ∑ k : Fin K, I.rho k * I.centeredIndex k * P.treatmentAtSupport k := by
          rw [Finset.sum_add_distrib]
        _ = (∑ k : Fin K, I.rho k * I.centeredIndex k) * B.baseTreatment +
              ∑ k : Fin K, I.rho k * I.centeredIndex k * P.treatmentAtSupport k := by
          rw [Finset.sum_mul]
    _ = ∑ k : Fin K, I.rho k * I.centeredIndex k * P.treatmentAtSupport k := by
      rw [I.centered_weight_sum_zero]
      simp

/-- Observed population 2SLS, written as `E[h(Z)Y]/E[h(Z)D]`, equals the
saturated finite-support population bridge ratio. -/
theorem observedBeta2SLS_eq_beta2SLSPopulationBridge
    (B : ObservedBridge μ Z D Y I P) [IsFiniteMeasure μ] (hZ : Measurable Z)
    (hYInt : Integrable (fun ω => I.centeredIndex (Z ω) * Y ω) μ)
    (hDInt : Integrable (fun ω => I.centeredIndex (Z ω) * boolToReal (D ω)) μ) :
    observedBeta2SLS μ Z D Y I = P.beta2SLSPopulationBridge I := by
  unfold observedBeta2SLS beta2SLSPopulationBridge
  rw [B.observedReducedFormMoment_eq_reducedFormMoment hZ hYInt,
    B.observedFirstStageMoment_eq_firstStageMoment hZ hDInt]

/-- End-to-end multiple-instrument IV bridge from the observed population 2SLS
ratio to the finite response-type algebra. -/
theorem observedBeta2SLS_eq_beta2SLSFiniteAlgebra
    (B : ObservedBridge μ Z D Y I P) [IsFiniteMeasure μ] (hZ : Measurable Z)
    (hYInt : Integrable (fun ω => I.centeredIndex (Z ω) * Y ω) μ)
    (hDInt : Integrable (fun ω => I.centeredIndex (Z ω) * boolToReal (D ω)) μ) :
    observedBeta2SLS μ Z D Y I = P.stats.beta2SLSFiniteAlgebra I := by
  rw [B.observedBeta2SLS_eq_beta2SLSPopulationBridge hZ hYInt hDInt,
    P.beta2SLSPopulationBridge_eq_beta2SLSFiniteAlgebra I]

end ObservedBridge

end ResponseTypeStats.PopulationBridge

end

end MultipleInstrumentIV
end PO.ID.Exact
end Causalean
