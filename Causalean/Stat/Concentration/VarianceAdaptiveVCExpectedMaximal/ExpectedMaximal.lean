import Causalean.Stat.Concentration.VarianceAdaptiveVCExpectedMaximal.Rademacher
import Causalean.Stat.Concentration.UniformDeviation.LocalizedEnvelopeExpectation

/-!
# Variance-adaptive expected maximal inequality for countable VC-type classes

This module proves the countable-class expected empirical-supremum bound from
the variance-adaptive Rademacher chaining estimate and symmetrization.  It
also provides an adapter for Causalean's existing uniform polynomial `L²`
covering certificate.
-/

namespace Causalean.Stat.Concentration

open MeasureTheory

universe u v

variable {𝒳 : Type u} [MeasurableSpace 𝒳] {ι : Type v}

/-- A countable measurable class bounded by `U`, with population `L²` radius
at most `σ` and empirical covering numbers at most `(A/ε)^v`, has expected
empirical supremum at most a universal constant times
`σ √(v log(AU/σ)/n) + v U log(AU/σ)/n`. -/
theorem varianceAdaptiveExpectedMaximal_le
    [Nonempty ι] [Countable ι]
    (P : Measure 𝒳) [IsProbabilityMeasure P]
    (F : ι → 𝒳 → ℝ) {U σ A v : ℝ}
    (hσ : 0 < σ) (hσU : σ < U) (hA : Real.exp 1 ≤ A) (hv : 1 ≤ v)
    (hmeas : ∀ i, Measurable (F i))
    (henvelope : ∀ i x, |F i x| ≤ U)
    (hL2 : ∀ i, measureL2Dist P (F i) (fun _ => 0) ≤ σ)
    (hcover : HasPolynomialEmpiricalL2Cover F U A v)
    (n : ℕ) (hn : 0 < n) :
    ∫ S : Fin n → 𝒳, countableEmpiricalSup P F S
        ∂Measure.pi (fun _ : Fin n => P) ≤
      varianceAdaptiveVCConstant * vcExpectedMaximalRate U σ A v n := by
  /-
  Apply countable-class symmetrization with the identity observation map,
  then substitute `varianceAdaptiveRademacherComplexity_le`.  The envelope
  hypotheses make every indexed function integrable, and countability makes
  the pointwise supremum measurable; no continuum-supremum measurability
  premise is needed.
  -/
  have hsymm :=
    uniform_deviation_expectation_le_two_smul_rademacher_complexity
      (μ := P) (f := F) hn id
      (fun i => by simpa [Function.comp_def] using hmeas i)
      (hσ.trans hσU).le henvelope
  have hrad := varianceAdaptiveRademacherComplexity_le
    P F hσ hσU hA hv hmeas henvelope hL2 hcover n hn
  calc
    ∫ S : Fin n → 𝒳, countableEmpiricalSup P F S
        ∂Measure.pi (fun _ : Fin n => P) ≤
        2 • rademacherComplexity n F P id := by
      simpa [countableEmpiricalSup, Function.comp_def] using hsymm
    _ ≤ 2 • ((varianceAdaptiveVCConstant / 2) *
        vcExpectedMaximalRate U σ A v n) := by
      have hmul := mul_le_mul_of_nonneg_left hrad (by norm_num : (0 : ℝ) ≤ 2)
      simp only [nsmul_eq_mul, Nat.cast_ofNat]
      exact hmul
    _ = varianceAdaptiveVCConstant * vcExpectedMaximalRate U σ A v n := by
      simp only [nsmul_eq_mul]
      ring

/-- An existing `HasPolynomialL2Cover` certificate yields some explicit
polynomial constants for which the countable class satisfies the
variance-adaptive expected maximal inequality at every positive sample size. -/
theorem HasPolynomialL2Cover.varianceAdaptiveExpectedMaximal_le
    [Nonempty ι] [Countable ι]
    (P : Measure 𝒳) [IsProbabilityMeasure P]
    (F : ι → 𝒳 → ℝ) {U σ : ℝ}
    (hF : HasPolynomialL2Cover F U)
    (hσ : 0 < σ) (hσU : σ < U)
    (hL2 : ∀ i, measureL2Dist P (F i) (fun _ => 0) ≤ σ) :
    ∃ A v : ℝ, Real.exp 1 ≤ A ∧ 1 ≤ v ∧
      ∀ n : ℕ, 0 < n →
        ∫ S : Fin n → 𝒳, countableEmpiricalSup P F S
            ∂Measure.pi (fun _ : Fin n => P) ≤
          varianceAdaptiveVCConstant * vcExpectedMaximalRate U σ A v n := by
  /-
  Obtain empirical constants from
  `HasPolynomialL2Cover.hasPolynomialEmpiricalL2Cover` and invoke the main
  theorem using the measurability and envelope fields of `hF`.
  -/
  obtain ⟨A, v, hA, hv, hcover⟩ := hF.hasPolynomialEmpiricalL2Cover
  refine ⟨A, v, hA, hv, ?_⟩
  intro n hn
  exact Causalean.Stat.Concentration.varianceAdaptiveExpectedMaximal_le P F hσ hσU hA hv
    hF.measurable hF.envelope hL2 hcover n hn

end Causalean.Stat.Concentration
