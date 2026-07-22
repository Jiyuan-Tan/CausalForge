/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Mogstad-Torgovitsky-Walters multiple-IV finite algebra

Public facade for the finite-support saturated/index algebra used by the MTW
multiple-IV characterization.  This module exports the ordered finite index,
the finite matrix first-stage construction, tail coefficients, the saturated
finite-support population bridge, the observed `E[h(Z)Y] / E[h(Z)D]` bridge,
response-type weights, and sign-alignment normalization facts.

NL artifact:
`doc/basic_concepts/po/estimand_characterization/mogstad_torgovitsky_walters_multiple_iv.md`.
-/

import Causalean.PO.ID.Exact.MultipleInstrumentIV.Population
/-! # Multiple-Instrument IV Main Facade

This file provides the public finite-support facade for the
Mogstad-Torgovitsky-Walters multiple-instrument characterization. It exposes
the signed adjacent ratio, the response-type weighted-sum form, positivity
under sign alignment, and the corresponding population bridge statements. -/

namespace Causalean
namespace PO.ID.Exact
namespace MultipleInstrumentIV

open Finset

namespace ResponseTypeStats

variable {K : ℕ} (I : FiniteIndex K) (R : ResponseTypeStats K)

/-- Signed adjacent reduced-form numerator in the finite response-type algebra:
`Σ_g λ_g Δ_g`.  This is the response-type counterpart of
`Σ_j B_j E[(Y(1)-Y(0)) Δ_jD]`. -/
noncomputable def signedAdjacentNumerator : ℝ :=
  ∑ g : ResponseType K, R.unnormTypeWeight I g * R.effect g

/-- Signed adjacent first-stage denominator in the finite response-type
algebra: `Σ_g λ_g`, corresponding to
`Σ_j B_j E[Δ_jD]`. -/
noncomputable def signedAdjacentDenominator : ℝ :=
  R.typeWeightDenom I

/-- The finite response-type ratio is the signed adjacent numerator divided by
the signed adjacent denominator.  The `PopulationBridge` facade below upgrades
this finite ratio to the saturated finite-support population 2SLS ratio. -/
theorem beta2SLSFiniteAlgebra_eq_signedAdjacentRatio
    (_hden : R.signedAdjacentDenominator I ≠ 0) :
    R.beta2SLSFiniteAlgebra I =
      R.signedAdjacentNumerator I / R.signedAdjacentDenominator I := by
  rfl

/-- Response-type weighted-sum form of the finite MTW algebra
(`prop:po-estimand-mtw-response-type-form`, finite algebra layer). -/
theorem beta2SLSFiniteAlgebra_eq_responseTypeWeightedSum'
    (hden : R.typeWeightDenom I ≠ 0) :
    R.beta2SLSFiniteAlgebra I = R.responseTypeEstimand I := by
  exact R.beta2SLSFiniteAlgebra_eq_responseTypeWeightedSum I hden

/-- Positive response-type average under MTW sign alignment and a positive
finite first-stage denominator (`prop:po-estimand-mtw-positive-weights`,
finite algebra layer). -/
theorem beta2SLSFiniteAlgebra_eq_positiveResponseTypeAverage'
    (hAlign : R.SignAligned I)
    (hden : 0 < R.typeWeightDenom I) :
    R.beta2SLSFiniteAlgebra I = R.responseTypeEstimand I ∧
      (∀ g : ResponseType K, 0 ≤ R.normalizedTypeWeight I g) ∧
      (∑ g : ResponseType K, R.normalizedTypeWeight I g = 1) := by
  exact R.beta2SLSFiniteAlgebra_eq_positiveResponseTypeAverage I hAlign hden

end ResponseTypeStats

namespace ResponseTypeStats.PopulationBridge

variable {K : ℕ} (I : FiniteIndex K) (P : ResponseTypeStats.PopulationBridge K)

/-- Population bridge version of the signed adjacent ratio theorem. -/
theorem beta2SLSPopulationBridge_eq_signedAdjacentRatio
    (hden : P.stats.signedAdjacentDenominator I ≠ 0) :
    P.beta2SLSPopulationBridge I =
      P.stats.signedAdjacentNumerator I / P.stats.signedAdjacentDenominator I := by
  rw [P.beta2SLSPopulationBridge_eq_beta2SLSFiniteAlgebra I]
  exact P.stats.beta2SLSFiniteAlgebra_eq_signedAdjacentRatio I hden

/-- Population bridge version of the response-type weighted-sum theorem. -/
theorem beta2SLSPopulationBridge_eq_responseTypeWeightedSum
    (hden : P.stats.typeWeightDenom I ≠ 0) :
    P.beta2SLSPopulationBridge I = P.stats.responseTypeEstimand I := by
  rw [P.beta2SLSPopulationBridge_eq_beta2SLSFiniteAlgebra I]
  exact P.stats.beta2SLSFiniteAlgebra_eq_responseTypeWeightedSum I hden

/-- Population bridge version of the positive response-type average theorem. -/
theorem beta2SLSPopulationBridge_eq_positiveResponseTypeAverage
    (hAlign : P.stats.SignAligned I)
    (hden : 0 < P.stats.typeWeightDenom I) :
    P.beta2SLSPopulationBridge I = P.stats.responseTypeEstimand I ∧
      (∀ g : ResponseType K, 0 ≤ P.stats.normalizedTypeWeight I g) ∧
      (∑ g : ResponseType K, P.stats.normalizedTypeWeight I g = 1) := by
  rw [P.beta2SLSPopulationBridge_eq_beta2SLSFiniteAlgebra I]
  exact P.stats.beta2SLSFiniteAlgebra_eq_positiveResponseTypeAverage I hAlign hden

end ResponseTypeStats.PopulationBridge

namespace ResponseTypeStats.PopulationBridge.ObservedBridge

open ResponseTypeStats.PopulationBridge

variable {Ω : Type*} [MeasurableSpace Ω] {K : ℕ}
variable {μ : MeasureTheory.Measure Ω} {Z : Ω → Fin K}
variable {D : Ω → Bool} {Y : Ω → ℝ}
variable {I : FiniteIndex K} {P : ResponseTypeStats.PopulationBridge K}

/-- End-to-end corollary (`prop:po-estimand-mtw-response-type-form`, observed
level): the observed population 2SLS ratio equals the response-type weighted
sum, stated directly at the observed-moment level with a single denominator
hypothesis `observedFirstStageMoment μ Z D I ≠ 0`.

This packages the full bridge chain:

    observedBeta2SLS = β₂SLS(finite algebra) = Σ_g ω_g Δ_g.

The hypothesis `hden` is the observable condition E[h(Z)D] ≠ 0 required by
`thm:po-estimand-mtw-signed-decomposition`.  Under `ObservedBridge` this
equals `typeWeightDenom I` (proved by `observedFirstStageMoment_eq_firstStageMoment`
+ `firstStageMoment_eq_typeWeightDenom`), so callers need not unfold the
bridge chain to locate the denominator condition. -/
theorem observedBeta2SLS_eq_responseTypeWeightedSum
    (B : ObservedBridge μ Z D Y I P) [MeasureTheory.IsFiniteMeasure μ]
    (hZ : Measurable Z)
    (hYInt : MeasureTheory.Integrable (fun ω => I.centeredIndex (Z ω) * Y ω) μ)
    (hDInt : MeasureTheory.Integrable
        (fun ω => I.centeredIndex (Z ω) * boolToReal (D ω)) μ)
    (hden : observedFirstStageMoment μ Z D I ≠ 0) :
    observedBeta2SLS μ Z D Y I = P.stats.responseTypeEstimand I := by
  -- Step 1: observed → finite algebra
  have h1 : observedBeta2SLS μ Z D Y I = P.stats.beta2SLSFiniteAlgebra I :=
    B.observedBeta2SLS_eq_beta2SLSFiniteAlgebra hZ hYInt hDInt
  -- Step 2: the observed denominator equals typeWeightDenom
  have hden' : P.stats.typeWeightDenom I ≠ 0 := by
    rwa [← P.firstStageMoment_eq_typeWeightDenom I,
      ← B.observedFirstStageMoment_eq_firstStageMoment hZ hDInt]
  -- Step 3: finite algebra → response-type weighted sum
  rw [h1]
  exact P.stats.beta2SLSFiniteAlgebra_eq_responseTypeWeightedSum I hden'

end ResponseTypeStats.PopulationBridge.ObservedBridge

end MultipleInstrumentIV
end PO.ID.Exact
end Causalean
